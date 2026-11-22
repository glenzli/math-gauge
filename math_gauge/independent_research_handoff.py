"""Portable offline handoff for a three-round independent research task."""
from __future__ import annotations

import argparse
from contextlib import contextmanager
from datetime import datetime, timedelta, timezone
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import sys


EDITION = "1.3.0"
ROUNDS = ("R1", "R2", "R3")
ROUND_SECONDS = 2700
BUNDLE_SCHEMA = "math-gauge.independent-research-handoff/v1"
SESSION_SCHEMA = "math-gauge.independent-research-handoff-session/v1"
OBSERVATION_SCHEMA = "math-gauge.independent-research-handoff-observation/v1"
OUTCOMES = {"normal-final", "delivery-failed", "unresolved"}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def json_bytes(value):
    return (json.dumps(value, ensure_ascii=False, indent=2, allow_nan=False) + "\n").encode()


def _object(raw):
    def unique(pairs):
        result = dict(pairs)
        require(len(result) == len(pairs), "Repeated JSON key")
        return result

    def reject_constant(value):
        raise ValueError(f"Invalid JSON constant: {value}")

    value = json.loads(raw, object_pairs_hook=unique, parse_constant=reject_constant)
    require(isinstance(value, dict), "Expected a JSON object")
    return value


def descriptor(name, raw):
    return {"path": name, "bytes": len(raw), "sha256": hashlib.sha256(raw).hexdigest()}


def _absolute(path):
    target = Path(os.path.abspath(path))
    for part in (*reversed(target.parents), target):
        require(not part.is_symlink(), "Symlink in external path")
    return target


def _separate(*paths):
    for index, first in enumerate(paths):
        for second in paths[index + 1:]:
            require(not first.is_relative_to(second) and not second.is_relative_to(first),
                    "Operator bundle, state, release, capture and candidate files need separate trees")


def _relative(name):
    require(isinstance(name, str) and not set(name) & {"\\", ":", "\0"}
            and not any(char in name for char in "\r\n\t"), "Unsafe relative path")
    path = PurePosixPath(name)
    require(bool(path.parts) and not path.is_absolute() and path.as_posix() == name
            and all(part not in {".", ".."} for part in path.parts), "Unsafe relative path")
    return path.parts


def read_file(root, name):
    target = root
    for part in _relative(name):
        target = target / part
        require(not target.is_symlink(), "Symlink in file path")
    before = target.lstat()
    require(stat.S_ISREG(before.st_mode) and before.st_nlink == 1,
            "Expected a regular file with no hardlinks")
    flags = os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0) | getattr(os, "O_BINARY", 0)
    flags |= getattr(os, "O_NONBLOCK", 0)
    with os.fdopen(os.open(target, flags), "rb") as stream:
        opened = os.fstat(stream.fileno())
        require(os.path.samestat(before, opened) and opened.st_nlink == 1,
                "File changed during collection")
        raw = stream.read()
        after = os.fstat(stream.fileno())
    require(len(raw) == opened.st_size == after.st_size
            and opened.st_mtime_ns == after.st_mtime_ns
            and opened.st_ctime_ns == after.st_ctime_ns, "File changed during collection")
    return raw


def _read_ref(root, ref):
    require(isinstance(ref, dict) and set(ref) == {"path", "bytes", "sha256"}
            and type(ref["bytes"]) is int, "Invalid file descriptor")
    raw = read_file(root, ref["path"])
    require(descriptor(ref["path"], raw) == ref, "File hash or size changed")
    return raw


def _new(path, raw):
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | getattr(os, "O_BINARY", 0)
    with os.fdopen(os.open(path, flags, 0o600), "wb") as stream:
        stream.write(raw)


def _write_tree(root, files):
    root.mkdir(mode=0o700)
    for name, raw in files.items():
        path = root.joinpath(*_relative(name))
        path.parent.mkdir(mode=0o700, parents=True, exist_ok=True)
        _new(path, raw)


def bundle_files(root):
    """Check the precise distribution allowlist, including the shipped controller."""
    root = _absolute(root)
    raw = read_file(root, "manifest.json")
    manifest = _object(raw)
    require(set(manifest) == {"schema", "edition", "round_seconds", "files"}
            and manifest["schema"] == BUNDLE_SCHEMA and manifest["edition"] == EDITION
            and manifest["round_seconds"] == ROUND_SECONDS
            and isinstance(manifest["files"], list), "Invalid operator manifest")
    refs = {}
    for ref in manifest["files"]:
        require(isinstance(ref, dict) and isinstance(ref.get("path"), str), "Invalid bundle descriptor")
        name = ref["path"]
        require(name not in refs, "Repeated bundle file")
        refs[name] = ref
    fixed = {"README.md", "research_handoff.py", "control-inputs/rules.md",
             "control-inputs/packet/body.md", *(f"control-inputs/{round_id}.md" for round_id in ROUNDS)}
    figures = set(refs) - fixed
    require(fixed <= refs.keys() and len(figures) == 4 and all(
        re.fullmatch(r"control-inputs/packet/figures/[a-z0-9-]+\.png", name) for name in figures),
        "Unexpected operator bundle material")
    files = {name: _read_ref(root, ref) for name, ref in refs.items()}
    return descriptor("manifest.json", raw), files


def _current_files(files, round_id):
    current = {"task.md": files[f"control-inputs/{round_id}.md"]}
    if round_id == "R1":
        current["rules.md"] = files["control-inputs/rules.md"]
        for name, payload in files.items():
            if name.startswith("control-inputs/packet/"):
                current[name.removeprefix("control-inputs/")] = payload
    return current


def _stamp(value):
    require(isinstance(value, str), "Expected an ISO 8601 timestamp with a timezone")
    stamp = datetime.fromisoformat(value[:-1] + "+00:00" if value.endswith("Z") else value)
    require(stamp.tzinfo is not None, "Timestamp needs a timezone")
    return stamp


def _optional_stamp(value):
    return None if value is None else _stamp(value)


def _text(value):
    return isinstance(value, str) and bool(value.strip())


def _names(values):
    require(isinstance(values, list), "Expected an explicit file list")
    for name in values:
        _relative(name)
    require(len(values) == len({name.casefold() for name in values}), "Repeated file path")
    return values


def _validate_observation(obs, round_id, session):
    fields = {"schema", "round", "session_id", "kind", "request_id", "delivery",
              "dispatched_at", "boundary", "native_terminal", "cli_cleanup", "first_normal_final_at",
              "first_normal_final", "final", "attachments", "evidence_files", "evidence_gaps"}
    require(set(obs) == fields and obs["schema"] == OBSERVATION_SCHEMA
            and obs["round"] == round_id and obs["session_id"] == session["session_id"]
            and obs["kind"] == session["kind"] and _text(obs["request_id"])
            and obs["delivery"] in OUTCOMES, "Invalid round observation or session identity")
    boundary = obs["boundary"]
    require(isinstance(boundary, dict) and set(boundary) == {"kind", "at"}
            and boundary["kind"] in {"native-terminal", "first-normal-final", "deadline", "unavailable"},
            "Invalid round boundary")
    sent, cutoff = _optional_stamp(obs["dispatched_at"]), _optional_stamp(boundary["at"])
    limit = None if sent is None else sent + timedelta(seconds=ROUND_SECONDS)
    require(sent is None or cutoff is None or sent <= cutoff <= limit, "Boundary is outside round budget")
    terminal = obs["native_terminal"]
    terminal_at = None
    if terminal is not None:
        require(isinstance(terminal, dict) and set(terminal) == {"status", "classification", "at"}
                and _text(terminal["status"]) and terminal["classification"] in {"success", "failure", "unknown"},
                "Invalid native terminal observation")
        terminal_at = _optional_stamp(terminal["at"])
        require(sent is None or terminal_at is None or sent <= terminal_at, "Native terminal precedes dispatch")
    cleanup = obs["cli_cleanup"]
    if cleanup is not None:
        require(isinstance(cleanup, dict) and set(cleanup) == {"exit_code", "at"}
                and (cleanup["exit_code"] is None or type(cleanup["exit_code"]) is int), "Invalid CLI cleanup")
        cleanup_at = _optional_stamp(cleanup["at"])
        require(cutoff is None or cleanup_at is None or cutoff <= cleanup_at, "Cleanup precedes cutoff")
    if boundary["kind"] == "native-terminal":
        require(cutoff is not None and cutoff == terminal_at, "Cutoff must match the first native terminal")
    if boundary["kind"] == "deadline":
        require(limit is not None and cutoff == limit
                and (terminal_at is None or cutoff <= terminal_at), "Cutoff must match the fixed deadline")
    attachments, evidence = _names(obs["attachments"]), _names(obs["evidence_files"])
    require(all(PurePosixPath(name).suffix.lower() == ".md" and name.split("/", 1)[0].casefold()
                not in {"task.md", "rules.md", "packet", "rounds"} for name in attachments),
            "Only explicitly delivered Markdown attachments outside the supplied inputs are allowed")
    require("observation.json" not in {name.casefold() for name in evidence}, "Observation is stored separately")
    gaps = obs["evidence_gaps"]
    require(isinstance(gaps, list) and all(_text(gap) for gap in gaps), "Invalid evidence gaps")
    final = obs["final"]
    first_at = _optional_stamp(obs["first_normal_final_at"])
    if obs["delivery"] == "normal-final":
        require(obs["first_normal_final"] is True and _text(final) and sent is not None
                and first_at is not None and cutoff is not None and sent <= first_at <= cutoff,
                "Need the first normal final by the real cutoff")
        if terminal is None:
            require(boundary["kind"] == "first-normal-final" and cutoff == first_at and gaps,
                    "Explain absent native terminal evidence for an observed first normal final")
        else:
            require(boundary["kind"] == "native-terminal" and terminal["classification"] == "success"
                    and terminal["status"].strip().casefold() not in {"error", "failed", "failure", "timeout",
                        "cancelled", "canceled", "interrupted", "incomplete", "aborted"},
                    "A failed or unknown native terminal cannot become a normal final")
        _relative(final)
        require(final.casefold() != "observation.json" and final.casefold() not in {name.casefold() for name in evidence},
                "The native final must be a distinct capture file")
    else:
        require(final is None and not attachments and obs["first_normal_final"] is None and first_at is None
                and boundary["kind"] != "first-normal-final", "Nondelivery cannot contain a substitute final")
        if obs["delivery"] == "delivery-failed":
            require(boundary["kind"] in {"native-terminal", "deadline"}, "An unknown cutoff stays unresolved")


def _session(state, manifest):
    raw = read_file(state, "session.json")
    session = _object(raw)
    require(set(session) == {"schema", "bundle", "session_id", "kind", "round_seconds", "metadata"}
            and session["schema"] == SESSION_SCHEMA and session["bundle"] == manifest
            and _text(session["session_id"]) and session["kind"] in {"operator-attestation", "fixture"}
            and session["round_seconds"] == ROUND_SECONDS, "Invalid session or changed bundle")
    if session["metadata"] is not None:
        require(session["metadata"]["path"] == "metadata.json", "Invalid session metadata path")
        _object(_read_ref(state, session["metadata"]))
    return session, descriptor("session.json", raw)


def prepare(bundle, state, session_id, *, metadata=None, fixture=False):
    bundle, state = _absolute(bundle), _absolute(state)
    _separate(bundle, state)
    require(_text(session_id), "A declared session ID is required")
    manifest, _ = bundle_files(bundle)
    files = {}
    if metadata is not None:
        metadata = _absolute(metadata)
        _separate(bundle, state, metadata)
        files["metadata.json"] = read_file(metadata.parent, metadata.name)
        _object(files["metadata.json"])
    session = {"schema": SESSION_SCHEMA, "bundle": manifest, "session_id": session_id,
               "kind": "fixture" if fixture else "operator-attestation", "round_seconds": ROUND_SECONDS,
               "metadata": descriptor("metadata.json", files["metadata.json"]) if files else None}
    _write_tree(state, {**files, "session.json": json_bytes(session)})
    return session


def _issue_data(round_id, session_ref, previous, files):
    return {"round": round_id, "session": session_ref, "previous_seal": previous,
            "candidate_inputs": [descriptor(name, raw) for name, raw in sorted(files.items())]}


def _ledger(state, manifest, files):
    session, session_ref = _session(state, manifest)
    allowed = {"session.json", ".write-lock"}
    if session["metadata"] is not None:
        allowed.add("metadata.json")
    previous = None
    entries, request_ids = {}, set()
    next_round, open_issue = ROUNDS[0], None
    for index, round_id in enumerate(ROUNDS):
        issue_name = f"{round_id}.issue.json"
        issued, sealed = state / issue_name, state / round_id
        require(not issued.is_symlink() and not sealed.is_symlink(), "Symlink in round state")
        if not issued.exists():
            require(not sealed.exists(), "Frozen round was never issued")
            continue
        allowed.add(issue_name)
        require(next_round == round_id and open_issue is None, "Round was issued out of order")
        issue_raw = read_file(state, issue_name)
        require(_object(issue_raw) == _issue_data(round_id, session_ref, previous,
                    _current_files(files, round_id)), "Changed issue record")
        open_issue = descriptor(issue_name, issue_raw)
        if not sealed.exists():
            continue
        allowed.add(round_id)
        seal_name = f"{round_id}/seal.json"
        seal_raw = read_file(state, seal_name)
        seal = _object(seal_raw)
        require(set(seal) == {"round", "issued", "previous_seal", "delivery", "observation", "final",
                              "attachments", "evidence_files", "sealed_at"}
                and seal["round"] == round_id and seal["issued"] == open_issue
                and seal["previous_seal"] == previous, "Broken freeze chain")
        _stamp(seal["sealed_at"])
        require(seal["observation"]["path"] == f"{round_id}/observation.json", "Wrong frozen observation path")
        obs = _object(_read_ref(state, seal["observation"]))
        _validate_observation(obs, round_id, session)
        require(obs["request_id"] not in request_ids and obs["delivery"] == seal["delivery"],
                "Repeated physical request or changed outcome")
        request_ids.add(obs["request_id"])
        if obs["final"] is None:
            require(seal["final"] is None, "Unexpected frozen final")
        else:
            require(seal["final"]["path"] == f"{round_id}/first-final.md"
                    and _read_ref(state, seal["final"]).decode().strip(), "Wrong or empty frozen final")
        for key, prefix in [("attachments", "delivered"), ("evidence_files", "evidence")]:
            require([ref["path"] for ref in seal[key]] == [f"{round_id}/{prefix}/{name}" for name in obs[key]],
                    "Changed file allowlist")
            for ref in seal[key]:
                _read_ref(state, ref)
        names = {seal_name, seal["observation"]["path"],
                 *(ref["path"] for ref in seal["attachments"] + seal["evidence_files"])}
        if seal["final"] is not None:
            names.add(seal["final"]["path"])
        directories = {p.as_posix() for name in names for p in PurePosixPath(name).parents}
        require(all(not path.is_symlink() and path.relative_to(state).as_posix() in names | directories
                    for path in sealed.rglob("*")), "Unexpected file in frozen round")
        entries[round_id] = seal
        previous = descriptor(seal_name, seal_raw)
        next_round = ROUNDS[index + 1] if seal["delivery"] == "normal-final" and index + 1 < len(ROUNDS) else None
        open_issue = None
    require({path.name for path in state.iterdir()} <= allowed, "Unexpected file in operator state")
    return session, session_ref, entries, previous, next_round, open_issue, request_ids


@contextmanager
def _write_gate(state):
    require(state.is_dir(), "Prepare the operator state first")
    lock = state / ".write-lock"
    lock.mkdir(mode=0o700)
    try:
        yield
    finally:
        lock.rmdir()


def reveal(bundle, state, session_id, round_id, output):
    bundle, state, output = map(_absolute, (bundle, state, output))
    _separate(bundle, state, output)
    manifest, files = bundle_files(bundle)
    with _write_gate(state):
        session, session_ref, _, previous, next_round, issued, _ = _ledger(state, manifest, files)
        require(session["session_id"] == session_id and round_id in ROUNDS and next_round == round_id
                and issued is None, "Current round requires the same session and all preceding normal freezes")
        current = _current_files(files, round_id)
        require(output.parent.is_dir() and not output.exists(), "Release destination must be a fresh directory")
        issue_raw = json_bytes(_issue_data(round_id, session_ref, previous, current))
        pending = state / ".pending-release"
        _new(pending, issue_raw)
        _write_tree(output, current)
        _new(state / f"{round_id}.issue.json", issue_raw)
        pending.unlink()
    return [descriptor(name, raw) for name, raw in sorted(current.items())]


def new_observation(round_id, session_id, *, fixture=False):
    """Supply a blank declaration. Replace unknowns only with observed facts."""
    return {"schema": OBSERVATION_SCHEMA, "round": round_id, "session_id": session_id,
            "kind": "fixture" if fixture else "operator-attestation", "request_id": "",
            "delivery": "unresolved", "dispatched_at": None, "boundary": {"kind": "unavailable", "at": None},
            "native_terminal": None, "cli_cleanup": None, "first_normal_final_at": None,
            "first_normal_final": None, "final": None, "attachments": [], "evidence_files": [], "evidence_gaps": []}


def freeze(bundle, state, session_id, round_id, capture, *, candidate_files=None):
    bundle, state, capture = map(_absolute, (bundle, state, capture))
    candidates = [] if candidate_files is None else [_absolute(candidate_files)]
    _separate(bundle, state, capture, *candidates)
    manifest, files = bundle_files(bundle)
    with _write_gate(state):
        session, _, _, previous, next_round, issued, requests = _ledger(state, manifest, files)
        require(session["session_id"] == session_id and round_id in ROUNDS and next_round == round_id
                and issued is not None, "Only the active issued round may be frozen once")
        original = read_file(capture, "observation.json")
        obs = _object(original)
        _validate_observation(obs, round_id, session)
        require(obs["request_id"] not in requests, "Repeated physical request ID")
        frozen = {"observation.json": original}
        seal = {"round": round_id, "issued": issued, "previous_seal": previous, "delivery": obs["delivery"],
                "observation": descriptor(f"{round_id}/observation.json", original), "final": None,
                "attachments": [], "evidence_files": [], "sealed_at": datetime.now(timezone.utc).isoformat()}
        if obs["final"] is not None:
            final = read_file(capture, obs["final"])
            require(final.decode().strip(), "Empty first normal final")
            frozen["first-final.md"] = final
            seal["final"] = descriptor(f"{round_id}/first-final.md", final)
        require(not obs["attachments"] or candidates, "Supply the stopped candidate output tree for attachments")
        for key, prefix, root in (("attachments", "delivered", candidates[0] if candidates else None),
                                  ("evidence_files", "evidence", capture)):
            for name in obs[key]:
                raw = read_file(root, name)
                relative = f"{prefix}/{name}"
                frozen[relative] = raw
                seal[key].append(descriptor(f"{round_id}/{relative}", raw))
        # A partial freeze cannot be reopened as a fresh attempt. The seal marker is written last.
        _write_tree(state / round_id, {**frozen, "seal.json": json_bytes(seal)})
    return seal


def check(bundle, state=None):
    bundle = _absolute(bundle)
    manifest, files = bundle_files(bundle)
    result = {"edition": EDITION, "bundle": manifest, "round_seconds": ROUND_SECONDS,
              "rounds": list(ROUNDS), "candidate_calls": 0}
    if state is not None:
        state = _absolute(state)
        _separate(bundle, state)
        require(not (state / ".write-lock").exists() and not (state / ".write-lock").is_symlink(),
                "State is being modified or an earlier mutation was interrupted")
        session, _, entries, previous, next_round, issued, _ = _ledger(state, manifest, files)
        result.update(kind=session["kind"], sealed={key: entry["delivery"] for key, entry in entries.items()},
                      previous_seal=previous, open_round=next_round if issued else None,
                      next_round=next_round if issued is None else None)
    return result


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--bundle", type=Path, default=Path(__file__).resolve().parent)
    commands = parser.add_subparsers(dest="command", required=True)
    for name in ("prepare", "reveal", "freeze", "check", "observation-template"):
        command = commands.add_parser(name)
        if name != "observation-template":
            command.add_argument("--state", type=Path, required=name != "check")
        if name != "check":
            command.add_argument("--session-id", required=True)
        if name in {"reveal", "freeze", "observation-template"}:
            command.add_argument("--round", choices=ROUNDS, required=True)
        if name in {"reveal", "observation-template"}:
            command.add_argument("--output", type=Path, required=True)
        if name in {"prepare", "observation-template"}:
            command.add_argument("--fixture", action="store_true")
        if name == "prepare":
            command.add_argument("--metadata", type=Path)
        if name == "freeze":
            command.add_argument("--capture", type=Path, required=True)
            command.add_argument("--candidate-files", type=Path)
    args = parser.parse_args(argv)
    try:
        if args.command == "prepare":
            result = prepare(args.bundle, args.state, args.session_id, metadata=args.metadata, fixture=args.fixture)
        elif args.command == "reveal":
            result = reveal(args.bundle, args.state, args.session_id, args.round, args.output)
        elif args.command == "freeze":
            result = freeze(args.bundle, args.state, args.session_id, args.round, args.capture,
                            candidate_files=args.candidate_files)
        elif args.command == "observation-template":
            output = _absolute(args.output)
            _separate(_absolute(args.bundle), output)
            _new(output, json_bytes(new_observation(args.round, args.session_id, fixture=args.fixture)))
            result = {"observation": str(output)}
        else:
            result = check(args.bundle, args.state)
        print(json_bytes(result).decode(), end="")
        return 0
    except (OSError, ValueError, TypeError, KeyError, AttributeError) as error:
        print(f"research-handoff: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
