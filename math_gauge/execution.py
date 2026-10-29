"""Execution ownership: adapter invocation and immutable attempt records; no grading."""

import hashlib
import json
import os
import signal
import subprocess
import re
import sys
import tempfile
import uuid
import time
from datetime import datetime, timezone
from pathlib import Path

from . import __version__
from .catalog import candidate_message, digest_bytes, read_json, relative_name, safe_file, write_json


def now():
    return datetime.now(timezone.utc).isoformat()


def runner_fingerprint():
    h = hashlib.sha256()
    for p in sorted(Path(__file__).parent.glob("*.py")):
        h.update(p.name.encode() + b"\0" + p.read_bytes())
    return h.hexdigest()


def invoke(command, request, cwd, timeout):
    if not command or not all(isinstance(x, str) for x in command):
        raise ValueError("Command must be a nonempty argv array")
    proc = subprocess.Popen(
        command,
        cwd=cwd,
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        start_new_session=(os.name == "posix"),
    )
    try:
        stdout, stderr = proc.communicate(
            json.dumps(request, ensure_ascii=False).encode("utf-8"), timeout=timeout
        )
        return (
            stdout,
            stderr,
            proc.returncode,
            "ok" if proc.returncode == 0 and stdout.strip() else "error",
        )
    except subprocess.TimeoutExpired:
        if os.name == "posix":
            os.killpg(proc.pid, signal.SIGKILL)
        else:
            proc.kill()
        stdout, stderr = proc.communicate()
        return stdout, stderr, proc.returncode, "timeout"


def run(
    suite, destination, ids=None, replay=None, command=None, model=None, timeout=120
):
    if (replay is None) == (command is None):
        raise ValueError("Choose exactly one of replay or command")
    if timeout <= 0:
        raise ValueError("Timeout must be positive")
    selected = suite.select(ids)
    if any(c["status"] == "retired" for c in selected):
        raise ValueError("Retired cases cannot be run")
    if command is not None and (
        not isinstance(command, list)
        or not command
        or not all(isinstance(x, str) for x in command)
    ):
        raise ValueError("Command must be a nonempty argv array")
    if command is not None and not model:
        raise ValueError("Command mode requires a model/adapter label")
    responses = read_json(replay) if replay else None
    if responses is not None:
        if not isinstance(responses, dict) or any(
            not isinstance(responses.get(c["id"]), str) for c in selected
        ):
            raise ValueError(
                "Replay requires a string response for every selected case"
            )
    dest = Path(destination).resolve()
    if dest.is_relative_to(suite.root):
        raise ValueError("Run directory must be outside the question suite")
    dest.mkdir(parents=True, exist_ok=False)
    metadata = {
        "schema": "math-gauge.run/v1",
        "run_id": uuid.uuid4().hex,
        "created_at": now(),
        "runner_version": __version__,
        "runner_sha256": runner_fingerprint(),
        "suite_id": suite.metadata["id"],
        "suite_version": suite.metadata["version"],
        "suite_sha256": suite.sha256,
        "visibility": suite.metadata["visibility"],
        "origin": "replay" if replay else "command",
        "model_label": "replay-fixture" if replay else model,
        "model_identity_verified": False,
        "timeout_seconds": timeout,
        "command": command,
        "cases": [],
    }
    for c in selected:
        metadata["cases"].append(
            {
                "id": c["id"],
                "version": c["version"],
                "track": c["track"],
                "task_kind": c.get("task_kind", "exploration"),
                "family_id": c.get("family_id", c["id"]),
                "candidate_message_sha256": digest_bytes(candidate_message(suite.request(c)).encode("utf-8")),
                "case_approved": c["status"] == "approved"
                and c["review"]["human"] == "approved",
            }
        )
    write_json(dest / "run.json", metadata)
    failures = 0
    for c in selected:
        case_dir = dest / c["id"]
        request = suite.prepare(c, case_dir / "solver")
        started = time.monotonic()
        if responses is not None:
            stdout, stderr, exit_code, status = responses[c["id"]], "", 0, "ok"
        else:
            try:
                stdout, stderr, exit_code, status = invoke(
                    command, request, case_dir / "solver", timeout
                )
            except OSError as error:
                stdout, stderr, exit_code, status = "", str(error), None, "error"
        failures += status != "ok"
        data = stdout.encode("utf-8") if isinstance(stdout, str) else stdout
        (case_dir / "response.md").write_bytes(data)
        (case_dir / "stderr.txt").write_bytes(stderr.encode("utf-8") if isinstance(stderr, str) else stderr)
        write_json(
            case_dir / "record.json",
            {
                "case_id": c["id"],
                "status": status,
                "exit_code": exit_code,
                "request_sha256": digest_bytes(
                    json.dumps(request, ensure_ascii=False, sort_keys=True).encode()
                ),
                "candidate_message_sha256": digest_bytes(candidate_message(request).encode("utf-8")),
                "response_sha256": digest_bytes(data),
                "elapsed_seconds": round(time.monotonic() - started, 6),
                "finished_at": now(),
            },
        )
    metadata["completed_at"] = now()
    metadata["execution_failures"] = failures
    write_json(dest / "run.json", metadata)
    return metadata


def check_lean(suite, ids=None, timeout=60):
    expected = suite.metadata["lean_toolchain"].split(":v")[-1]
    version = subprocess.run(
        ["lean", "--version"],
        cwd=suite.root,
        capture_output=True,
        text=True,
        timeout=10,
    )
    if version.returncode or f"version {expected}" not in version.stdout:
        raise ValueError(
            f"Lean {expected} required; got {version.stdout.strip()} {version.stderr.strip()}"
        )
    checks = []
    for case in suite.select(ids):
        for name in case["lean_checks"]:
            p = safe_file(suite.root, name)
            result = subprocess.run(
                ["lean", str(p)],
                cwd=suite.root,
                capture_output=True,
                text=True,
                timeout=timeout,
            )
            # This records kernel/compiler evidence for fixed audit files, not semantic agreement.
            checks.append(
                {
                    "case_id": case["id"],
                    "file": name,
                    "sha256": digest_bytes(p.read_bytes()),
                    "exit_code": result.returncode,
                    "output": result.stdout,
                    "stderr": result.stderr,
                }
            )
    return {
        "schema": "math-gauge.lean-check/v1",
        "created_at": now(),
        "suite_sha256": suite.sha256,
        "lean_version": version.stdout.strip(),
        "checks": checks,
        "all_compiled": bool(checks) and all(c["exit_code"] == 0 for c in checks),
        "semantic_alignment_inferred": False,
    }


def _lean_filename(name):
    if not isinstance(name, str) or not name.endswith('.lean'):
        raise ValueError(f"Unsafe or unsupported Lean filename: {name!r}")
    relative_name(name)
    if not all(x.rstrip("'").isidentifier() for x in name[:-5].split('/')):
        raise ValueError(f"Unsafe or unsupported Lean module filename: {name!r}")
    return name


def _candidate_imports(text, clean_lean):
    """Candidate module identifiers also allow ordinary Unicode Lean names."""
    imports = []
    for match in re.finditer(r'^\s*import\s+([^\r\n]+)', clean_lean(text), re.M):
        for name in match.group(1).split():
            if not all(x.rstrip("'").isidentifier() for x in name.split('.')):
                raise ValueError('Unsupported import syntax requires manual format review: ' + name)
            imports.append(name)
    return imports


def _override_extraction(response, override):
    """Reviewer may identify complete fenced bodies, never supply source text."""
    if (not isinstance(override, dict) or set(override) != {'reviewer', 'reviewer_kind', 'reason', 'files'}
            or override['reviewer_kind'] not in {'ai', 'human'}
            or not all(isinstance(override[k], str) and override[k].strip() for k in ('reviewer', 'reason'))
            or not isinstance(override['files'], list) or not override['files']):
        raise ValueError('Extraction override requires reviewer, reviewer_kind, reason and files')
    regions = set(); lines = response.splitlines(keepends=True); i = offset = 0
    while i < len(lines):
        opening = re.fullmatch(r' {0,3}(`{3,}|~{3,})[^\r\n]*\r?\n?', lines[i])
        offset += len(lines[i].encode()); i += 1
        if not opening:
            continue
        fence = opening.group(1); start = offset
        while i < len(lines):
            if re.fullmatch(r' {0,3}' + re.escape(fence[0]) + '{' + str(len(fence)) + r',}\s*', lines[i]):
                regions.add((start, offset))
                offset += len(lines[i].encode()); i += 1; break
            offset += len(lines[i].encode()); i += 1
    raw = response.encode(); files = []; names = set(); selected = set()
    for item in override['files']:
        if not isinstance(item, dict) or set(item) != {'name', 'start_byte', 'end_byte'}:
            raise ValueError('Override file must contain only name/start_byte/end_byte')
        name = _lean_filename(item['name']); span = (item['start_byte'], item['end_byte'])
        if (any(type(x) is not int for x in span) or span not in regions or span in selected
                or name.casefold() in names):
            raise ValueError('Override must select distinct complete fenced bodies with unique names')
        names.add(name.casefold()); selected.add(span)
        files.append(dict(item, content=raw[span[0]:span[1]].decode('utf-8')))
    return files


def extract_candidate_lean(response):
    """Extract complete named Lean fences without changing a source byte.

    Accept filename= in the fence or a filename on the preceding nonblank line.
    Ambiguous, duplicate, unnamed and unfinished Lean blocks fail closed.
    Source offsets refer to the UTF-8 bytes of the frozen response.
    """
    if not isinstance(response, str):
        raise ValueError("Response must be UTF-8 text")
    lines = response.splitlines(keepends=True)
    files, seen = [], set()
    i = offset = 0
    previous = ""
    while i < len(lines):
        line = lines[i]
        opening = re.fullmatch(r" {0,3}(`{3,}|~{3,})([^\r\n]*)\r?\n?", line)
        if not opening:
            if line.strip():
                previous = line.strip()
            offset += len(line.encode("utf-8")); i += 1
            continue
        fence, info = opening.groups()
        info = info.strip()
        is_lean = bool(re.match(r"lean(?:4)?(?:\s|$)", info, re.I))
        name = None
        if is_lean:
            tail = re.sub(r"^lean(?:4)?\b", "", info, flags=re.I).strip()
            if tail:
                match = re.fullmatch(r'(?:filename=)?["`]?([^"`\s]+)["`]?', tail)
            else:
                label = re.sub(r"^#{1,6}\s*", "", previous)
                label = re.sub(r"^(?:File|Filename|文件|文件名)\s*[:：]\s*", "", label, flags=re.I)
                match = re.fullmatch(r'[`*]*([^`*\s]+\.lean)[`*]*\s*[:：]?', label)
            if not match:
                raise ValueError("Every Lean block needs an unambiguous filename")
            name = _lean_filename(match.group(1))
            if name.casefold() in seen:
                raise ValueError("Duplicate Lean filename: " + name)
            seen.add(name.casefold())
        start = offset + len(line.encode("utf-8"))
        offset = start; i += 1; body = []
        while i < len(lines):
            closing = re.fullmatch(r" {0,3}" + re.escape(fence[0]) + "{" + str(len(fence)) + r",}\s*", lines[i])
            if closing:
                break
            body.append(lines[i]); offset += len(lines[i].encode("utf-8")); i += 1
        if i == len(lines):
            if is_lean:
                raise ValueError("Unclosed Lean code block: " + name)
            break
        if is_lean:
            files.append({"name": name, "content": "".join(body),
                          "start_byte": start, "end_byte": offset})
        offset += len(lines[i].encode("utf-8")); i += 1; previous = ""
    if not files:
        raise ValueError("No complete named Lean source files were delivered")
    return files


def _candidate_engine():
    # Reuse pinned dependency/import inspection, without changing the author
    # verifier's namespace policy, manifest contract or default behavior.
    path = Path(__file__).resolve().parents[1] / "scripts/formal/verify.py"
    namespace = {"__file__": str(path), "__name__": "candidate_formal_dependencies"}
    exec(compile(path.read_bytes(), str(path), "exec"), namespace)
    return namespace, path


def _candidate_sources(submitted, inputs, imports):
    """Submitted replacements plus only the input modules actually imported."""
    available = dict(inputs, **submitted)
    if len({name.casefold() for name in available}) != len(available):
        raise ValueError("Case-colliding input/submission filenames")
    by_module = {name[:-5].replace("/", "."): name for name in available}
    ordered, visiting, done = [], set(), set()
    external = set()

    def visit(name):
        if name in visiting:
            raise ValueError("Cyclic local imports: " + name)
        if name in done:
            return
        visiting.add(name)
        for module in imports(available[name]):
            if module in by_module:
                visit(by_module[module])
            else:
                external.add(module)
        visiting.remove(name); done.add(name); ordered.append(name)

    for name in submitted:
        visit(name)
    return [(name, available[name]) for name in ordered], external


def _candidate_policy(sources, build, scratch, dependency):
    """Default-deny macOS compiler policy; no network or process spawning."""
    quote = json.dumps
    reads = [str(sources), *dependency["search_paths"],
             str(Path(dependency["lean"]).parent.parent),
             "/System", "/usr/lib", "/usr/share", "/bin", "/usr/bin"]
    rules = ["(version 1)", "(deny default)", "(allow process-exec)",
             "(allow sysctl-read)", "(allow file-read-metadata)",
             '(allow file-read* (literal "/"))']
    rules += ["(allow file-read* (subpath " + quote(str(Path(p).resolve())) + "))" for p in reads]
    rules += ['(allow file-read* (literal "/dev/null") (literal "/dev/urandom") (literal "/dev/random"))']
    rules += ["(allow file-read* file-write* (subpath " + quote(str(p)) + "))" for p in (build, scratch)]
    return "\n".join(rules) + "\n"


def _candidate_process(argv, cwd, env, timeout):
    proc = subprocess.Popen(argv, cwd=cwd, env=env, stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE, text=True, encoding="utf-8",
                            errors="replace", start_new_session=True)
    try:
        stdout, stderr = proc.communicate(timeout=timeout)
        return proc.returncode, stdout, stderr, False
    except subprocess.TimeoutExpired:
        os.killpg(proc.pid, signal.SIGKILL)
        stdout, stderr = proc.communicate()
        return proc.returncode, stdout, stderr, True


def _missing_cached_source(module, dependency):
    relative = Path(*module.split(".")).with_suffix(".lean")
    for library in dependency["search_paths"]:
        library = Path(library)
        if library.parts[-4:] == (".lake", "build", "lib", "lean"):
            if (library.parents[3] / relative).is_file():
                return True
    return False


def verify_candidate_lean(case_dir, destination, *, dependency_root, lean=None,
                          timeout=120, required_files=(), extraction_override=None):
    """Freeze and compile a runner response in a fresh isolated workspace.

    No source repair, model invocation, grading, or author-reference imports.
    required_files may only encode filenames already required by the task.
    macOS sandbox-exec is mandatory; unsupported isolation fails closed.
    """
    case_dir, destination = Path(case_dir).resolve(), Path(destination).resolve()
    if destination.exists() or destination.is_relative_to(case_dir):
        raise ValueError("Candidate verification needs a new output outside the case directory")
    if timeout <= 0:
        raise ValueError("Timeout must be positive")
    destination.mkdir(parents=True)
    report_path = destination / "report.json"
    report = {"schema": "math-gauge.candidate-lean/v1", "status": "format_error",
              "started_at": now(), "report": str(report_path),
              "response_sha256": None, "files_sha256": {},
              "manifest": None, "manifest_sha256": None, "artifact_sha256": None,
              "engine_sha256": None,
              "semantic_alignment_inferred": False, "human_approval": False,
              "source_repaired": False, "modules": []}

    def finish(status, reason=None):
        report.update(status=status, finished_at=now())
        report['manual_extraction_needed'] = status == 'format_error'
        if reason:
            report["reason"] = reason
        write_json(report_path, report)
        return report

    try:
        response = (case_dir / "response.md").read_bytes()
        record = read_json(case_dir / "record.json")
        request = read_json(case_dir / "solver/request.json")
        report['case_id'] = request['case_id']
        if record.get('case_id', request['case_id']) != request['case_id']:
            return finish('infrastructure_error', 'Runner case identity differs from request')
        response_hash = digest_bytes(response)
        request_hash = digest_bytes(json.dumps(request, ensure_ascii=False, sort_keys=True).encode())
        if response_hash != record["response_sha256"] or request_hash != record["request_sha256"]:
            return finish("infrastructure_error", "Frozen runner request/response binding changed")
        report.update(response_sha256=response_hash, request_sha256=request_hash,
                      candidate_message_sha256=digest_bytes(candidate_message(request).encode()))
        (destination / "response.md").write_bytes(response)
        write_json(destination / "request.json", request)
        if extraction_override is not None:
            extracted = _override_extraction(response.decode('utf-8'), extraction_override)
            write_json(destination / 'extraction-override.json', extraction_override)
            report['extraction_override_sha256'] = digest_bytes((destination / 'extraction-override.json').read_bytes())
        else:
            extracted = extract_candidate_lean(response.decode("utf-8"))
        submitted = {item["name"]: item["content"] for item in extracted}
        absent = [name for name in required_files if _lean_filename(name) not in submitted]
        if absent:
            return finish("format_error", "Task-required files not delivered: " + ", ".join(absent))
        inputs = {}
        for item in request["files"]:
            if not item["name"].endswith(".lean"):
                continue
            name = _lean_filename(item["name"])
            if name.casefold() in {x.casefold() for x in inputs}:
                raise ValueError("Duplicate frozen input filename")
            inputs[name] = item["content"]
        for kind, files in (("submitted", submitted), ("inputs", inputs)):
            for name, content in files.items():
                path = destination / kind / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(content.encode("utf-8"))
        report["files_sha256"] = {name: digest_bytes(text.encode()) for name, text in submitted.items()}
        report["input_files_sha256"] = {name: digest_bytes(text.encode()) for name, text in inputs.items()}
        report["source_spans"] = [{k: v for k, v in item.items() if k != "content"} for item in extracted]
        report["replaced_inputs"] = sorted(set(inputs) & set(submitted))
        engine, engine_path = _candidate_engine()
        sources, external = _candidate_sources(submitted, inputs, lambda text: _candidate_imports(text, engine['clean_lean']))
        manifest = {"schema": "math-gauge.candidate-lean-manifest/v1",
                    "case_id": request['case_id'],
                    "response_sha256": response_hash, "request_sha256": request_hash,
                    "files_sha256": report["files_sha256"],
                    "input_files_sha256": report["input_files_sha256"],
                    "extraction_override_sha256": report.get('extraction_override_sha256'),
                    "ordered_sources": [{"name": name, "sha256": digest_bytes(text.encode()),
                                         "origin": "submitted" if name in submitted else "frozen-input"}
                                        for name, text in sources]}
        write_json(destination / "manifest.json", manifest)
        report["manifest"] = str(destination / "manifest.json")
        report["artifact_sha256"] = report["manifest_sha256"] = digest_bytes((destination / "manifest.json").read_bytes())
    except (ValueError, KeyError, TypeError, OSError) as error:
        return finish("format_error", str(error))
    template_path = engine_path.with_name("audit-candidate.lean.in")
    identity = {"execution": digest_bytes(Path(__file__).read_bytes()),
                "dependency_verifier": digest_bytes(engine_path.read_bytes()),
                "audit_template": digest_bytes(template_path.read_bytes())}
    report["engine_identity"] = identity
    report["engine_sha256"] = digest_bytes(json.dumps(identity, sort_keys=True).encode())
    if sys.platform != "darwin" or not Path("/usr/bin/sandbox-exec").is_file():
        return finish("infrastructure_error", "Required macOS compiler isolation is unavailable")
    try:
        dependency = engine["inspect_dependencies"](dependency_root, lean)
        report["dependency"] = dependency
        for module in external:
            try:
                engine["resolve_imports"]({module}, dependency)
            except engine["VerificationError"] as error:
                status = "infrastructure_error" if _missing_cached_source(module, dependency) else "compile_error"
                return finish(status, str(error))
        report["direct_external_imports"] = engine["resolve_imports"](external, dependency)
        with tempfile.TemporaryDirectory(prefix="math-gauge-candidate-") as temp:
            temp = Path(temp).resolve()
            stage, build, scratch = (temp / x for x in ("sources", "build", "scratch"))
            for path in (stage, build, scratch, destination / "logs", destination / "oleans"):
                path.mkdir()
            for name, content in sources:
                path = stage / name; path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(content.encode())
            module_names = [name[:-5].replace("/", ".") for name, _ in sources]
            audit_name = "GaugeCandidateAudit_" + uuid.uuid4().hex
            audit_text = template_path.read_text().replace("{{IMPORTS}}", "\n".join("import " + x for x in module_names)).replace(
                "{{MODULES}}", "#[" + ", ".join(json.dumps(x, ensure_ascii=False) for x in module_names) + "]")
            (stage / (audit_name + ".lean")).write_text(audit_text)
            (destination / "audit.lean").write_text(audit_text)
            policy = _candidate_policy(stage, build, scratch, dependency)
            policy_path = temp / "compiler.sb"; policy_path.write_text(policy)
            (destination / "compiler.sb").write_text(policy)
            env = {"PATH": "/usr/bin:/bin", "TMPDIR": str(scratch),
                   "LEAN_PATH": os.pathsep.join([str(build), *dependency["search_paths"]])}
            prefix = ["/usr/bin/sandbox-exec", "-f", str(policy_path)]
            positive = stage / "isolation-probe.txt"; positive.write_text("candidate-isolation-probe\n")
            probes = []
            for path, allowed in [(positive, True), (case_dir / "response.md", False), (engine_path, False)]:
                rc, out, err, timed = _candidate_process(prefix + ["/bin/cat", str(path)], stage, env, 10)
                passed = (rc == 0 and out == "candidate-isolation-probe\n") if allowed else (
                    rc != 0 and any(x in err for x in ("Operation not permitted", "Permission denied")))
                probes.append({"path": str(path), "expected": "allowed" if allowed else "denied",
                               "passed": passed and not timed, "exit_code": rc,
                               "stderr": err, "timeout": timed})
            report["isolation"] = {"policy_sha256": digest_bytes(policy.encode()), "probes": probes,
                                   "network": "denied", "process_fork": "denied"}
            if not all(p["passed"] for p in probes):
                return finish("infrastructure_error", "Compiler isolation probe failed; no candidate code executed")
            artifacts = {}
            for name in [*module_names, audit_name]:
                relative = Path(*name.split("."))
                source = stage / relative.with_suffix(".lean")
                target = build / relative.with_suffix(".olean"); target.parent.mkdir(parents=True, exist_ok=True)
                argv = prefix + [dependency["lean"], "--root=" + str(stage), "-o", str(target), str(source)]
                rc, out, err, timed = _candidate_process(argv, stage, env, timeout)
                log = destination / "logs" / (name.replace(".", "_") + ".log")
                log.write_text(out + err)
                item = {"module": name, "source_sha256": digest_bytes(source.read_bytes()),
                        "exit_code": rc, "timeout": timed, "argv": argv,
                        "log": str(log), "log_sha256": digest_bytes(log.read_bytes())}
                report["modules"].append(item)
                if name == audit_name:
                    summaries = [json.loads(x) for x in re.findall(r"CANDIDATE_AUDIT_SUMMARY (\{[^\r\n]*\})", out + err)]
                    declarations = [json.loads(x) for x in re.findall(r"CANDIDATE_DECL (\{[^\r\n]*\})", out + err)]
                    report["audit"] = {"summary": summaries[0] if len(summaries) == 1 else None,
                                       "declarations": declarations,
                                       "selection": "All constants originating in submitted or used frozen-input modules, regardless of namespace"}
                for previous, old_hash in artifacts.items():
                    if digest_bytes((build / previous).read_bytes()) != old_hash:
                        return finish("axiom_rejected", "Compiled dependency artifact changed during candidate execution")
                if rc or timed:
                    missing = re.findall(r"[A-Za-z0-9_./-]+\.olean", out + err)
                    cache_missing = any(not Path(x).is_file() and any(
                        str(Path(x)).startswith(base + "/") for base in dependency["search_paths"]) for x in missing)
                    status = "infrastructure_error" if cache_missing or name == audit_name else "compile_error"
                    if name == audit_name and "CANDIDATE_FORBIDDEN_AXIOMS" in out + err:
                        status = "axiom_rejected"
                    return finish(status, "timeout" if timed else "Lean failed; see frozen compilation log")
                data = target.read_bytes(); item["olean_sha256"] = digest_bytes(data)
                artifacts[str(relative.with_suffix(".olean"))] = item["olean_sha256"]
                saved = destination / "oleans" / relative.with_suffix(".olean")
                saved.parent.mkdir(parents=True, exist_ok=True); saved.write_bytes(data)
                if name == audit_name:
                    if len(summaries) != 1 or not summaries[0].get("passed") or not declarations:
                        return finish("axiom_rejected", "Missing or failed complete candidate module audit")
                    if (len(declarations) != summaries[0].get("declaration_count")
                            or len({x['name'] for x in declarations}) != len(declarations)
                            or any(x['module'] not in module_names for x in declarations)
                            or set(summaries[0].get('axiom_union', [])) - engine['ALLOWED_AXIOMS']):
                        return finish("axiom_rejected", "Candidate audit inventory or axiom union is inconsistent")
            for name, content in sources:
                if (stage / name).read_bytes() != content.encode():
                    return finish("axiom_rejected", "Source bytes changed during compilation")
    except (OSError, ValueError, KeyError, subprocess.SubprocessError, engine["VerificationError"]) as error:
        return finish("infrastructure_error", str(error))
    current_identity = {"execution": digest_bytes(Path(__file__).read_bytes()),
                        "dependency_verifier": digest_bytes(engine_path.read_bytes()),
                        "audit_template": digest_bytes(template_path.read_bytes())}
    if current_identity != identity:
        return finish("infrastructure_error", "Candidate verifier changed during execution")
    return finish("passed")
