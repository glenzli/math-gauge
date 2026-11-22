"""Prepare, probe, or explicitly dispatch a private native research batch."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import queue
import re
import select
import signal
import socket
import stat
import subprocess
import sys
import threading
import time
import uuid

if sys.platform == "darwin":
    import fcntl

PUBLIC = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(PUBLIC))

from math_gauge import independent_research_execution as execution
from math_gauge import taste_v130 as flow
from scripts.isolated_cli import prepare as helper
from scripts.isolated_cli.probe import probe


SEATBELT = "/usr/bin/sandbox-exec"
PROFILE = execution.PERMISSION_PROFILE
LOCAL_MODEL_PROXY = ("127.0.0.1", 7897)


def source_hashes():
    paths = (Path(__file__), Path(execution.__file__), Path(helper.__file__), Path(sys.modules[probe.__module__].__file__))
    return {p.resolve().relative_to(PUBLIC).as_posix(): helper.sha256(p) for p in paths}


def identity(binary):
    selected = Path(binary).resolve(strict=True)
    version = subprocess.run([str(selected), "--version"], timeout=15, check=True, capture_output=True)
    with selected.open("rb") as stream:
        digest = hashlib.file_digest(stream, "sha256").hexdigest() if hasattr(hashlib, "file_digest") else helper.sha256(selected)
    return {"path": str(selected), "version": version.stdout.decode().strip(), "sha256": digest}


def runtime_installation(binary):
    binary = Path(binary)
    app_bundle = binary.parents[3] if len(binary.parents) > 3 else None
    install = app_bundle if app_bundle is not None and app_bundle.name == "codex-cli" else binary.parent
    host_directory = install / "bin" if install == app_bundle and install.name == "codex-cli" else install
    host = host_directory / "codex-code-mode-host"
    if not host.is_file() or host.is_symlink() or not os.access(host, os.X_OK):
        raise ValueError("The selected CLI installation lacks its local code-mode host")
    return install, {"path": str(host), "sha256": helper.sha256(host)}


def model_service_proxy():
    """Check the exact existing loopback service route without sending a request."""
    result = subprocess.run(["/usr/sbin/scutil", "--proxy"], capture_output=True, text=True, timeout=10, check=True)
    settings = dict(re.findall(r"^\s*(HTTPSEnable|HTTPSProxy|HTTPSPort)\s*:\s*(\S+)\s*$", result.stdout, re.M))
    if settings.get("HTTPSEnable") != "1":
        return None
    if (settings.get("HTTPSProxy"), settings.get("HTTPSPort")) != (LOCAL_MODEL_PROXY[0], str(LOCAL_MODEL_PROXY[1])):
        raise ValueError("Current HTTPS proxy differs from the supported existing model-service route")
    with socket.create_connection(LOCAL_MODEL_PROXY, timeout=2):
        pass
    return {"source": "macOS scutil --proxy and loopback TCP open", "host": LOCAL_MODEL_PROXY[0],
            "port": LOCAL_MODEL_PROXY[1], "scope": "native parent only"}


def mac_profile(read, write, protected, hidden_startup, installation_id, proxy):
    def restriction(operation, root, allowed):
        exceptions = [f"(require-not ({kind} {helper.sb_string(path)}))" for kind, path in allowed]
        return f'(deny {operation} (require-all (subpath {helper.sb_string(root)}) {" ".join(exceptions)}))'
    # Exact leaves are handled by the optional-file rules. Operation-specific
    # file-read-data denials would otherwise take precedence over file-read*.
    ordinary_read = [*read, *(("literal", path) for path in hidden_startup)]
    return "\n".join([
        "(version 1)", "(allow default)",
        *(restriction("file-read-data", root, ordinary_read) for root in protected),
        restriction("file-write*", "/", write),
        *(f'(deny file-read* (literal {helper.sb_string(path)}) (with errno ENOENT))' for path in hidden_startup),
        f'(allow file-write-data (literal {helper.sb_string(installation_id)}))',
        '(deny network-outbound (remote ip "localhost:*"))',
        *([f'(allow network-outbound (remote ip "localhost:{proxy["port"]}"))'] if proxy else []),
        # The trusted native command launcher applies a separate Seatbelt profile.
        '(allow process-exec (with no-sandbox) (literal "/usr/bin/sandbox-exec"))', "",
    ])


def positive_negative(work, negatives, positive):
    return {"positive": str(positive), "sha256": execution.sha256(positive.read_bytes()),
            "negative": [{"path": str(p), "category": category, "exists_before_run": True}
                         for category, p in negatives if p.is_file() and not p.is_relative_to(work)]}


def thread_params(work, model, rules):
    return {"cwd": str(work), "ephemeral": True, "model": model["model"], "modelProvider": "openai",
            "allowProviderModelFallback": False, "permissions": PROFILE, "approvalPolicy": "never",
            "config": {"model_reasoning_effort": model["effort"]}, "developerInstructions": rules}


def installation_identity(path):
    if path.is_symlink() or not path.is_file():
        raise ValueError("Native startup requires an existing regular installation identity")
    raw = path.read_bytes()  # This is a UUID, not an authentication credential.
    if stat.S_IMODE(path.stat().st_mode) != 0o644 or len(raw) != 36:
        raise ValueError("Native startup would need to change the existing installation identity")
    uuid.UUID(raw.decode("ascii"))
    return {"path": str(path), "sha256": execution.sha256(raw), "mode": "0644"}


def configure(binary_identity, runtime, work, control, negatives, positive):
    runtime.mkdir(mode=0o700)
    scratch = work / "scratch"
    scratch.mkdir(mode=0o700)
    binary = Path(binary_identity["path"])
    codex_home = Path(os.environ.get("CODEX_HOME", Path.home() / ".codex")).resolve()
    auth = codex_home / "auth.json"
    installation_id = codex_home / "installation_id"
    if auth.is_symlink() or installation_id.is_symlink():
        raise ValueError("Refusing a symlinked native startup location")
    installation = installation_identity(installation_id)
    install, code_mode_host = runtime_installation(binary)
    dependencies = [Path(p) for p in ("/usr/bin", "/usr/lib", "/usr/libexec", "/bin", "/sbin",
                    "/System/Library", "/private/etc", "/private/var/db/timezone",
                    "/private/var/db/dyld", "/opt/homebrew", "/Library/Frameworks/Python.framework")
                    if Path(p).exists()]
    read = [("subpath", path) for path in [*dependencies, install, runtime, work]]
    # Authentication is restricted to the native parent. Local tools must fail to open this path.
    if auth.is_file():
        read.append(("literal", auth))
    # The installed native program resolves its existing installation identity during startup.
    read.append(("literal", installation_id))
    read.append(("literal", Path(sys.executable).resolve()))
    profile = runtime / "outer.sb"
    protected = sorted({Path.home(), codex_home.parent, Path("/Users"), Path("/Volumes"),
                        Path("/private/tmp"), Path("/private/var/folders"), Path("/private/var/root"),
                        Path("/private/var/tmp")})
    global_config = codex_home / "config.toml"
    runtime_environments = codex_home / "environments.toml"
    user_rules = codex_home / "rules"
    user_instructions = [codex_home / name for name in ("AGENTS.md", "AGENTS.override.md")]
    hidden = [global_config, runtime_environments, user_rules, *user_instructions]
    proxy = model_service_proxy()
    execution.write_bytes(profile, mac_profile(read, [("subpath", runtime), ("subpath", scratch)],
                                             protected, hidden, installation_id, proxy).encode())
    negatives = [*negatives, ("global-config", global_config), ("global-environments", runtime_environments)]
    negatives.extend(("global-instructions", path) for path in user_instructions)
    outer_probes = positive_negative(work, negatives, positive)
    outer_probes["hidden_directories"] = [str(user_rules)] if user_rules.is_dir() else []
    inner_probes = positive_negative(work, [*negatives, ("authentication", auth),
                            ("installation-identity", installation_id)], positive)
    files = {":minimal": "read", str(work): "read", str(scratch): "write"}
    files.update({str(path): "read" for path in dependencies})
    denied = {*protected, control.parent, runtime.parent, auth, installation_id, *hidden}
    files.update({str(path): "deny" for path in sorted(denied)})
    settings = {"default_permissions": PROFILE, f"permissions.{PROFILE}.filesystem": files,
        f"permissions.{PROFILE}.network.enabled": False,
        "approval_policy": "never", "web_search": "disabled", "project_doc_max_bytes": 0,
        "skills.include_instructions": False, "features.network_proxy": False,
        "sqlite_home": str(runtime), "log_dir": str(runtime), "cli_auth_credentials_store": "file",
        "mcp_servers": {}, "shell_environment_policy.inherit": "none",
        "shell_environment_policy.set": {"PATH": "/opt/homebrew/bin:/usr/bin:/bin", "TMPDIR": str(scratch)},
        "features.skip_host_skill_discovery": True,
        **{"features." + name: False for name in helper.DISABLED_CODEX_FEATURES},
        "features.shell_tool": True, "features.unified_exec": True, "features.view_image": True,
        "features.code_mode_host": True}
    command = [SEATBELT, "-f", str(profile), str(binary), "app-server", "--stdio", "--strict-config"]
    for key, value in settings.items():
        command.extend(["--config", key + "=" + helper.toml(value)])
    environment = {k: os.environ[k] for k in ("HOME", "CODEX_HOME", "USER", "LOGNAME", "LANG") if k in os.environ}
    environment.update({"PATH": "/opt/homebrew/bin:/usr/bin:/bin", "TMPDIR": str(runtime)})
    execution.write_json(control / "sandbox-plan.json", {"argv": command, "settings": settings,
        "outer_probes": outer_probes, "tool_probes": inner_probes, "environment_keys": sorted(environment),
        "existing_installation_identity": installation,
        "local_code_mode_host": code_mode_host,
        "model_service_proxy": proxy,
        "outer_profile_sha256": execution.sha256(profile.read_bytes())})
    return command, environment, outer_probes, inner_probes, scratch


class AppServer:
    def __init__(self, command, environment, control, work):
        self.command, self.environment, self.control, self.work = command, environment, control, work
        self.messages = queue.Queue()
        self.stack = None

    def __enter__(self):
        from contextlib import ExitStack
        self.stack = ExitStack()
        try:
            self.stdin_log = self.stack.enter_context((self.control / "app-server.stdin.ndjson").open("xb", buffering=0))
            self.stdout_log = self.stack.enter_context((self.control / "app-server.stdout.ndjson").open("xb", buffering=0))
            stderr = self.stack.enter_context((self.control / "app-server.stderr.txt").open("xb"))
            self.proc = subprocess.Popen(self.command, cwd=self.work, env=self.environment,
                start_new_session=True, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=stderr)
        except BaseException:
            self.stack.close()
            raise
        self.reader = threading.Thread(target=self.collect, daemon=True)
        self.reader.start()
        return self

    def collect(self):
        try:
            for line in self.proc.stdout:
                tick = time.monotonic()
                at = execution.utc()
                self.stdout_log.write(line)
                self.messages.put((tick, at, line))
        finally:
            self.messages.put(None)

    def send(self, data, deadline=None):
        raw = execution.json_bytes(data)
        self.stdin_log.write(raw)
        fd = self.proc.stdin.fileno()
        if deadline is None:
            deadline = time.monotonic() + 10
        os.set_blocking(fd, False)
        while raw:
            remaining = max(0, deadline - time.monotonic())
            if not remaining or not select.select([], [fd], [], remaining)[1]:
                raise TimeoutError("Native stdin dispatch deadline")
            try:
                raw = raw[os.write(fd, raw):]
            except BlockingIOError:
                continue

    def receive(self, deadline):
        try:
            row = self.messages.get(timeout=max(0, deadline - time.monotonic()))
        except queue.Empty as error:
            raise TimeoutError("Native app-server response deadline") from error
        if row is None:
            raise RuntimeError("Native app-server closed stdout")
        if row[0] > deadline:
            raise TimeoutError("Native app-server response received after deadline")
        return row[1], row[2], json.loads(row[2])

    def rpc(self, id_, method, params):
        self.send({"id": id_, "method": method, "params": params})
        deadline = time.monotonic() + 35
        while True:
            _, raw, message = self.receive(deadline)
            if message.get("id") == id_ and "method" not in message:
                if "error" in message:
                    raise RuntimeError(f"Native {method} failed; see original wire output")
                return raw, message["result"]
            if "id" in message and "method" in message:
                raise RuntimeError("Unexpected native server request; no approval provided")

    def initialize(self):
        self.rpc(1, "initialize", {"clientInfo": {"name": "math-gauge", "version": "1.3.0"},
                                   "capabilities": {"experimentalApi": True}})
        self.send({"method": "initialized"})
        expected = json.loads((self.control / "sandbox-plan.json").read_bytes())["existing_installation_identity"]
        if installation_identity(Path(expected["path"])) != expected:
            raise RuntimeError("Native startup changed the installation identity")

    def tool_probe(self, manifest, scratch):
        # Only local TCP listeners are contacted, without transmitting data.
        proxy = json.loads((self.control / "sandbox-plan.json").read_bytes())["model_service_proxy"]
        source = """
import errno, hashlib, json, os, socket, sys
manifest, scratch, ports = json.loads(sys.argv[1]), sys.argv[2], json.loads(sys.argv[3])
checked = []
for row in manifest['negative']:
    try:
        fd = os.open(row['path'], os.O_RDONLY)
        os.close(fd)
        outcome = False
    except OSError as error:
        outcome = error.errno in {errno.EACCES, errno.EPERM}
    checked.append({'category': row['category'], 'passed': outcome})
with open(manifest['positive'], 'rb') as stream:
    positive = hashlib.sha256(stream.read()).hexdigest() == manifest['sha256']
try:
    fd = os.open(manifest['positive'], os.O_WRONLY)
    os.close(fd)
    readonly = False
except OSError as error:
    readonly = error.errno in {errno.EACCES, errno.EPERM}
target = os.path.join(scratch, '.controller-probe')
with open(target, 'xb') as stream:
    stream.write(b'synthetic scratch')
with open(target, 'rb') as stream:
    writable = stream.read() == b'synthetic scratch'
os.unlink(target)
network_denials = {}
for port in ports:
    with socket.socket() as client:
        client.settimeout(3)
        network_denials[str(port)] = client.connect_ex(('127.0.0.1', port)) in {errno.EACCES, errno.EPERM}
denied = all(network_denials.values())
proxy_variables = {name for name in os.environ if name.lower() in
    ('http_proxy','https_proxy','all_proxy','no_proxy','codex_network_proxy_brokered_credentials')}
print(json.dumps({'pid': os.getpid(), 'checks': checked, 'positive': positive, 'readonly': readonly,
    'scratch_read_write': writable, 'network_denied': denied, 'loopback_denials': network_denials, 'proxy_variables': sorted(proxy_variables),
    'passed': all(x['passed'] for x in checked) and positive and readonly and writable and denied and not proxy_variables}))
"""
        with socket.socket() as listener:
            listener.bind(("127.0.0.1", 0))
            listener.listen()
            ports = [listener.getsockname()[1], *([proxy["port"]] if proxy else [])]
            raw, result = self.rpc(3, "command/exec", {"command": [str(Path(sys.executable).resolve()), "-I", "-c",
                    source, json.dumps(manifest), str(scratch), json.dumps(ports)],
                "cwd": str(self.work), "permissionProfile": PROFILE, "timeoutMs": 10000})
        execution.write_bytes(self.control / "native-tool-probe.ndjson", raw)
        output = json.loads(result.get("stdout") or "{}")
        if result.get("exitCode") != 0 or output.get("passed") is not True:
            raise RuntimeError("Native command filesystem or network probe failed")
        return output

    def __exit__(self, *_):
        try:
            self.proc.stdin.close()
            self.stop_group()
            self.reader.join(timeout=5)
            self.proc.stdout.close()
            execution.write_json(self.control / "process-exit.json", {"pid": self.proc.pid,
                "returncode": self.proc.returncode, "finished_at": execution.utc()})
        finally:
            self.stack.close()

    def stop_group(self):
        for sig, grace in ((signal.SIGTERM, 5), (signal.SIGKILL, 5)):
            try:
                os.killpg(self.proc.pid, sig)
            except ProcessLookupError:
                pass
            try:
                self.proc.wait(timeout=grace)
                break
            except subprocess.TimeoutExpired:
                continue
        # A command still in this group must not survive a reaped server.
        try:
            os.killpg(self.proc.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass


def outer_probe(command, environment, manifest, work, control):
    # No private Python module import inside the actual file-open probe.
    source = Path(sys.modules[probe.__module__].__file__).read_text()
    script = source.split('if __name__ == "__main__":', 1)[0]
    script += """
manifest = json.loads(sys.argv[1])
result = probe(manifest)
for row in result['checks']:
    if row.get('category') in ('global-config', 'global-environments', 'global-instructions') and row.get('errno') == errno.ENOENT and row['exists_before_run']:
        row.update(passed=True, outcome='HIDDEN_BY_SEATBELT', expected='hidden-enoent')
for directory in manifest.get('hidden_directories', []):
    hidden = False
    try:
        with os.scandir(directory):
            pass
    except OSError as error:
        hidden = error.errno == errno.ENOENT
    result['checks'].append({'category': 'global-user-rules', 'path': directory, 'exists_before_run': True,
        'expected': 'hidden-enoent', 'passed': hidden})
result['passed'] = all(row['passed'] for row in result['checks'])
print(json.dumps(result))
"""
    result = subprocess.run([*command[:3], str(Path(sys.executable).resolve()), "-I", "-c", script,
                             json.dumps(manifest)], cwd=work, env=environment,
                            capture_output=True, timeout=15)
    execution.write_bytes(control / "outer-open.stdout.json", result.stdout)
    execution.write_bytes(control / "outer-open.stderr.txt", result.stderr)
    execution.write_json(control / "outer-open-command.json", {"exit_code": result.returncode})
    if result.returncode != 0 or json.loads(result.stdout).get("passed") is not True:
        raise RuntimeError("Actual outer Seatbelt file-open probe failed")


def _negative_inputs(root, prepared, registration):
    return [("private-registration", registration), ("public-baseline", Path(prepared["public_root"]) / "benchmark.json"),
            ("evaluator-plan", root / "control/plan.json"),
            ("other-runtime", root / "runtime/probe-evaluator-marker.md"),
            ("peer-workspace", root / "workspaces/preflight-peer/marker.md")]


def preflight(run_root, binary):
    root, prepared, plan, registration = execution.prepared(run_root)
    if prepared["fixture_only"]:
        raise ValueError("A synthetic queue cannot run native preflight")
    output = root / "control/preflight.json"
    if output.exists():
        raise ValueError("Keep the prior preflight; use a fresh root for changed conditions")
    control, runtime, work = (root / folder / "preflight" for folder in ("control", "runtime", "workspaces"))
    for new in (control, work):
        new.mkdir(mode=0o700)
    positive = work / "probe.md"
    execution.write_bytes(positive, b"Synthetic preflight only.\n")
    peer = root / "workspaces/preflight-peer"
    peer.mkdir(mode=0o700)
    execution.write_bytes(peer / "marker.md", b"Synthetic peer exclusion marker.\n")
    execution.write_bytes(root / "runtime/probe-evaluator-marker.md", b"Synthetic evaluator exclusion marker.\n")
    report = {"schema": "math-gauge.independent-research-runtime-preflight/v1", "status": "blocked",
              "plan_sha256": prepared["plan_sha256"], "binary": None, "candidate_dispatches": 0,
              "native_model_list_matches": False, "provider_admission_verified": False,
              "runner_sha256": source_hashes(), "started_at": execution.utc(), "probe_directory": "control/preflight"}
    try:
        if sys.platform != "darwin" or not Path(SEATBELT).is_file():
            raise RuntimeError("This runtime requires macOS Seatbelt")
        report["binary"] = identity(binary)
        args, env, outer, inner, scratch = configure(report["binary"], runtime, work, control,
                                                     _negative_inputs(root, prepared, registration), positive)
        setup = json.loads((control / "sandbox-plan.json").read_bytes())
        report["model_service_proxy"] = setup["model_service_proxy"]
        report["local_code_mode_host"] = setup["local_code_mode_host"]
        outer_probe(args, env, outer, work, control)
        with AppServer(args, env, control, work) as server:
            report["parent_pid"] = server.proc.pid
            server.initialize()
            pid = probe(outer, pid=server.proc.pid, role="parent")
            execution.write_json(control / "native-parent-pid.json", pid)
            if not pid["passed"]:
                raise RuntimeError("Actual native parent policy probe failed")
            server.tool_probe(inner, scratch)
            catalog, cursor = [], None
            for page in range(20):
                raw, result = server.rpc(10 + page, "model/list", {"includeHidden": True, "cursor": cursor})
                execution.write_bytes(control / f"model-list-{page}.ndjson", raw)
                catalog.extend(result["data"])
                cursor = result.get("nextCursor")
                if cursor is None:
                    break
            else:
                raise RuntimeError("Live model inventory pagination did not finish")
            listed = {(m["model"], e["reasoningEffort"]) for m in catalog for e in m["supportedReasoningEfforts"]}
            report["missing_configurations"] = [row["id"] for row in plan["cohort"]
                                                if (row["model"], row["effort"]) not in listed]
            if report["missing_configurations"]:
                raise RuntimeError("The native model list lacks a requested model or effort")
            report["native_model_list_matches"] = True
            threads = set()
            for index, model in enumerate(plan["cohort"]):
                request_id = 1000 + index
                raw, _ = server.rpc(request_id, "thread/start", thread_params(work, model, "Synthetic runtime probe only."))
                execution.write_bytes(control / f"empty-thread-{index}.ndjson", raw)
                thread = execution.thread_identity(json.loads(raw), model["model"], model["effort"], work, request_id=request_id)
                if thread in threads:
                    raise RuntimeError("Native server reused an empty preflight thread")
                threads.add(thread)
            report["empty_native_threads"] = len(threads)
        report["status"] = "passed"
    except (OSError, ValueError, RuntimeError, KeyError, TypeError, TimeoutError, subprocess.SubprocessError) as error:
        report["blocker"] = str(error)
    stderr = control / "app-server.stderr.txt"
    if stderr.exists() and b"failed to refresh available models" in stderr.read_bytes():
        report["catalog_remote_refresh"] = "observed-failure"
    else:
        report["catalog_remote_refresh"] = "not-established"
    report["finished_at"] = execution.utc()
    report["artifacts"] = [execution.descriptor(root, p) for p in sorted(control.iterdir()) if p.is_file()]
    execution.write_json(output, report)
    return report


def committed(root, path):
    path = path.resolve()
    rel = path.relative_to(root).as_posix()
    result = subprocess.run(["git", "show", "HEAD:" + rel], cwd=root, capture_output=True, timeout=15)
    if result.returncode or result.stdout != path.read_bytes():
        raise ValueError(f"Authorized commit must contain these execution bytes: {rel}")
    git = subprocess.run(["git", "rev-parse", "HEAD"], cwd=root, check=True, capture_output=True, timeout=15)
    return git.stdout.decode().strip()


def run_native(run_root, preflight_sha):
    root, prepared, plan, registration = execution.prepared(run_root)
    if prepared["fixture_only"] or sys.platform != "darwin":
        raise ValueError("Native execution requires the production plan and macOS")
    preflight_path = root / "control/preflight.json"
    ref = execution.descriptor(root, preflight_path)
    report = json.loads(preflight_path.read_bytes())
    if ref["sha256"] != preflight_sha or report["status"] != "passed" or not report["native_model_list_matches"]:
        raise ValueError("A passed, hash-selected native preflight is required")
    if (report["plan_sha256"] != prepared["plan_sha256"] or source_hashes() != report["runner_sha256"]
            or identity(report["binary"]["path"]) != report["binary"]
            or runtime_installation(report["binary"]["path"])[1] != report["local_code_mode_host"]
            or model_service_proxy() != report["model_service_proxy"]):
        raise ValueError("Plan, runner or CLI identity changed after native preflight")
    for item in report["artifacts"]:
        flow._read(root, item)
    private = flow._source_tree(registration)
    public_commit = committed(PUBLIC, Path(execution.__file__))
    for rel in report["runner_sha256"]:
        if committed(PUBLIC, PUBLIC / rel) != public_commit:
            raise ValueError("Public HEAD changed during dispatch freeze")
    for item in flow.load_case(registration)[2]["runner"]["files"]:
        committed(PUBLIC, PUBLIC / item["path"])
    private_commit = committed(private, Path(prepared["plan_path"]))
    committed(private, registration)
    freeze = {"preflight": ref, "public_head": public_commit, "private_head": private_commit,
              "binary": report["binary"], "budgets": execution.BUDGETS, "candidate_dispatches": 0,
              "frozen_at": execution.utc()}
    execution.write_json(root / "control/dispatch-freeze.json", freeze)

    def factory(model, control, work):
        return CandidateServer(root, prepared, registration, report["binary"], model, control, work)

    return execution.execute_queue(root, factory, preflight_ref=ref)


class CandidateServer(AppServer):
    def __init__(self, root, prepared, registration, cli, model, control, work):
        self.root, self.model = root, model
        self.outer, self.inner, self.scratch = None, None, None
        negatives = _negative_inputs(root, prepared, registration)
        negatives += [("peer-candidate", path) for path in (root / "workspaces").glob("*/rounds/R1.md")
                      if not path.is_relative_to(work)]
        args, env, self.outer, self.inner, self.scratch = configure(cli, root / "runtime" / model["id"],
            work, control, negatives, work / "packet/body.md")
        outer_probe(args, env, self.outer, work, control)
        super().__init__(args, env, control, work)

    def start(self):
        self.initialize()
        pid = probe(self.outer, pid=self.proc.pid, role="parent")
        execution.write_json(self.control / "native-parent-pid.json", pid)
        if not pid["passed"]:
            raise RuntimeError("Actual candidate parent policy check failed")
        local_tools = self.tool_probe(self.inner, self.scratch)
        rules = (self.work / "rules.md").read_bytes().decode("utf-8")
        raw, result = self.rpc(2, "thread/start", thread_params(self.work, self.model, rules))
        thread_path = self.control / "thread-start.ndjson"
        execution.write_bytes(thread_path, raw)
        thread = execution.thread_identity(json.loads(raw), self.model["model"], self.model["effort"], self.work)
        execution.write_json(self.control / "app-server.json", {"thread_id": thread, "parent_pid": self.proc.pid,
            "preflight_tool_pid": local_tools["pid"], "configured_model": result["model"],
            "configured_effort": result["reasoningEffort"], "thread_start_response": execution.descriptor(self.root, thread_path),
            "parent_pid_check": execution.descriptor(self.root, self.control / "native-parent-pid.json"),
            "tool_probe": execution.descriptor(self.root, self.control / "native-tool-probe.ndjson")})
        return thread

    def _children(self):
        ps = subprocess.run(["/bin/ps", "-axo", "pid=,ppid=,pgid=,stat=,comm="], capture_output=True,
                            text=True, check=True, timeout=5)
        rows = []
        for line in ps.stdout.splitlines():
            pid, parent, group, status, executable = line.split(None, 4)
            if not status.startswith("Z"):
                rows.append({"pid": int(pid), "ppid": int(parent), "pgid": int(group), "executable": executable})
        known = {self.proc.pid}
        while True:
            expanded = known | {item["pid"] for item in rows
                                if item["ppid"] in known or item["pgid"] == self.proc.pid}
            if expanded == known:
                return [item for item in rows if item["pid"] in known - {self.proc.pid}]
            known = expanded

    def turn(self, request, _rid):
        start = time.monotonic()
        sent = execution.utc()
        deadline = start + execution.BUDGETS["broker_seconds_per_round"]

        def stop_at_outer_deadline():
            if self.proc.poll() is None:
                try:
                    os.killpg(self.proc.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass

        watchdog = threading.Timer(execution.BUDGETS["outer_seconds_per_round"], stop_at_outer_deadline)
        watchdog.daemon = True
        watchdog.start()
        try:
            return self.capture_turn(request, sent, deadline)
        finally:
            watchdog.cancel()

    def capture_turn(self, request, sent, deadline):
        lines, times, boundary, failure = [], [], None, None
        try:
            self.send(request, deadline=deadline)
            while True:
                at, raw, message = self.receive(deadline)
                if execution._stamp(at) < execution._stamp(sent):
                    continue
                lines.append(raw)
                times.append(at)
                method, params = message.get("method"), message.get("params", {})
                if method == "turn/completed" and params.get("threadId") == request["params"]["threadId"]:
                    boundary, cutoff = at, "native-terminal"
                    break
                if method == "model/rerouted" or ("id" in message and (method or "error" in message)):
                    boundary, cutoff = at, "unavailable"
                    break
                if method in {"item/started", "item/completed"} and params["item"]["type"] in {
                    "webSearch", "mcpToolCall", "dynamicToolCall", "collabAgentToolCall", "subAgentActivity", "imageGeneration"
                }:
                    boundary, cutoff = at, "unavailable"
                    break
        except TimeoutError:
            boundary, cutoff = execution.utc(), "deadline"
        except (OSError, ValueError, RuntimeError, KeyError, TypeError) as error:
            boundary, cutoff, failure = execution.utc(), "unavailable", type(error).__name__
        workers = []
        try:
            workers = self._children()
            for item in reversed(workers):
                try:
                    os.kill(item["pid"], signal.SIGKILL)
                except ProcessLookupError:
                    continue
            if self._children():
                raise RuntimeError("A native worker remained live at the round boundary")
        except (OSError, ValueError, RuntimeError, subprocess.SubprocessError) as error:
            cutoff, failure = "unavailable", type(error).__name__
        if cutoff != "native-terminal":
            self.stop_group()
        return {"lines": lines, "received_at": times, "sent_at": sent, "boundary_at": boundary,
                "cutoff": cutoff, "pids": {"parent": self.proc.pid, "observed_workers_at_cutoff": workers,
                    "controller_error": failure}}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="mode", required=True)
    prep = sub.add_parser("prepare", help="Bind the plan and create a fresh private run root; no CLI session")
    prep.add_argument("--plan", required=True)
    prep.add_argument("--run-root", required=True)
    check = sub.add_parser("preflight", help="Use synthetic input to check OS isolation and a live model catalog; no turns")
    check.add_argument("--run-root", required=True)
    check.add_argument("--binary", required=True)
    run = sub.add_parser("execute", help="Start paid mathematical turns after the committed-plan and preflight gates")
    run.add_argument("--run-root", required=True)
    run.add_argument("--preflight-sha256", required=True)
    args = parser.parse_args(argv)
    try:
        if args.mode == "prepare":
            root = execution.prepare(args.plan, PUBLIC, args.run_root)
            print(json.dumps({"status": "prepared", "run_root": str(root), "candidate_dispatches": 0}))
            return 0
        root = flow._safe_absolute(args.run_root)
        if sys.platform != "darwin":
            raise ValueError("Native preflight and execution require macOS Seatbelt")
        with (root / "control/run.lock").open("a+b") as lock:
            fcntl.flock(lock.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
            if args.mode == "preflight":
                result = preflight(root, args.binary)
                print(json.dumps({"status": result["status"], "report": str(root / "control/preflight.json"),
                    "blocker": result.get("blocker"), "candidate_dispatches": 0}, ensure_ascii=False))
                return 0 if result["status"] == "passed" else 1
            result = run_native(root, args.preflight_sha256)
            print(json.dumps({"summary": str(root / "batch-summary.json"),
                              "outcomes": {r["model_id"]: r["outcome"] for r in result["cohort"]}}))
            return 0 if all(r["outcome"] == "normal-finals" for r in result["cohort"]) else 1
    except (OSError, ValueError, RuntimeError, KeyError, subprocess.SubprocessError) as error:
        print(f"independent-research: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
