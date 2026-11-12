#!/usr/bin/env python3
"""Maintain evaluator evidence in local Git without changing its original contracts."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from math_gauge import evidence_retention as evidence


def relative(value):
    if not isinstance(value, str) or "\\" in value or "\0" in value:
        raise ValueError("Evidence paths must be safe repository-relative paths")
    path = PurePosixPath(value)
    if path.is_absolute() or not path.parts or any(x in {"", ".", ".."} for x in value.split("/")):
        raise ValueError("Evidence paths must be safe repository-relative paths")
    if path.parts[0] not in {"results", "studies", "verification"}:
        raise ValueError("Only evaluator evidence can enter the retention index")
    return value


def git(root, *args):
    env = os.environ.copy()
    for name in ("GIT_DIR", "GIT_WORK_TREE", "GIT_INDEX_FILE", "GIT_OBJECT_DIRECTORY",
                 "GIT_ALTERNATE_OBJECT_DIRECTORIES", "GIT_NAMESPACE"):
        env.pop(name, None)
    env.update(GIT_NO_LAZY_FETCH="1", GIT_NO_REPLACE_OBJECTS="1", GIT_TERMINAL_PROMPT="0",
               GIT_OPTIONAL_LOCKS="0")
    result = subprocess.run(["git", "--no-lazy-fetch", "--no-replace-objects", "-C", str(root),
                             *args], env=env, capture_output=True)
    if result.returncode:
        raise ValueError("Required evidence is not in local Git; no network recovery is allowed")
    return result.stdout


def source_tree(root, revision):
    if not isinstance(revision, str) or not re.fullmatch(r"[0-9a-f]{40}", revision):
        raise ValueError("Use the full, immutable source Git commit")
    result = {}
    for row in git(root, "ls-tree", "-r", "-z", "--full-tree", revision).split(b"\0"):
        if row:
            header, path = row.split(b"\t", 1)
            mode, kind, blob = header.decode("ascii").split()
            result[path.decode("utf-8")] = (mode, kind, blob)
    return result


def hash_hot(root, name):
    path = root / relative(name)
    for parent in reversed((path, *path.parents)):
        if parent == root or root in parent.parents:
            try:
                state = parent.lstat()
            except FileNotFoundError:
                raise ValueError(f"Original evidence is absent: {name}") from None
            if stat.S_ISLNK(state.st_mode):
                raise ValueError(f"Evidence cannot traverse a symlink: {name}")
    before = path.stat()
    if not stat.S_ISREG(before.st_mode):
        raise ValueError(f"Evidence must be a regular file: {name}")
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        while chunk := stream.read(1024 * 1024):
            digest.update(chunk)
    after = path.stat()
    if (before.st_ino, before.st_size, before.st_mtime_ns, before.st_ctime_ns) != (
            after.st_ino, after.st_size, after.st_mtime_ns, after.st_ctime_ns):
        raise ValueError(f"Evidence changed during verification: {name}")
    return digest.hexdigest(), after.st_size


def plan_entries(path, aliases=None):
    text = Path(path).read_text(encoding="utf-8")
    if Path(path).suffix == ".jsonl":
        rows = [json.loads(line) for line in text.splitlines() if line.strip()]
        entries = {row["path"]: row for row in rows}
        if len(entries) != len(rows):
            raise ValueError("Duplicate evidence path in retention plan")
    else:
        plan = json.loads(text)
        entries = dict(plan["files"])
        entries.update(plan.get("required_recovery_aliases", {}))
    if aliases:
        extra = json.loads(Path(aliases).read_text(encoding="utf-8"))["logical_files"]
        if entries.keys() & extra.keys():
            raise ValueError("Recovery aliases overlap the retention plan")
        entries.update(extra)
    return entries


def prepare(root, plan, revision, *, aliases=None):
    """Bind already-present original bytes to an immutable committed source."""
    root = Path(root).resolve()
    tree = source_tree(root, revision)
    entries = plan_entries(plan, aliases)
    files, objects = {}, {}
    for name, item in sorted(entries.items()):
        relative(name)
        if name.startswith("results/evidence-retention/"):
            raise ValueError("The retention index and canonical objects must stay hot")
        sha, size = hash_hot(root, name)
        if (sha, size) != (item["sha256"], item["bytes"]):
            raise ValueError(f"Original evidence differs from the reviewed plan: {name}")
        origin = relative(item.get("git_path") or item.get("preferred_git_path_after_recovery_commit") or name)
        source = tree.get(origin)
        if source is None or source[0] not in {"100644", "100755"} or source[1] != "blob":
            raise ValueError(f"Original evidence is not a committed regular blob: {name}")
        mode = item.get("mode")
        if mode not in {"100644", "100755"}:
            mode = source[0]
        previous = objects.get(sha)
        if previous is not None and previous["bytes"] != size:
            raise ValueError("Inconsistent size for one evidence digest")
        objects.setdefault(sha, {"bytes": size, "git_blob": source[2], "git_path": origin})
        files[name] = {"sha256": sha, "mode": mode, "reason": item["reason"]}
    data = {"schema": evidence.SCHEMA, "version": evidence.VERSION,
            "source_git_revision": revision, "objects": objects, "files": files}
    destination = root / evidence.INDEX_PATH
    if destination.exists():
        raise ValueError("Retention index already exists; review a new version instead of replacing it")
    destination.parent.mkdir(parents=True, exist_ok=True)
    raw = (json.dumps(data, ensure_ascii=False, indent=2, sort_keys=True) + "\n").encode()
    # The complete reader validation must pass before any original can be pruned.
    with tempfile.NamedTemporaryFile(dir=destination.parent, delete=False) as stream:
        stream.write(raw)
        temporary = Path(stream.name)
    try:
        os.replace(temporary, destination)
        return evidence.validate_repository(root, deep=True)
    except BaseException:
        destination.unlink(missing_ok=True)
        raise
    finally:
        temporary.unlink(missing_ok=True)


def prune(root):
    """Remove only exact tracked copies; ignored originals are never swept up."""
    root = Path(root).resolve()
    result = evidence.validate_repository(root, deep=True)
    if not result["present"]:
        raise ValueError("A verified retention index is required before pruning")
    registry = json.loads((root / evidence.INDEX_PATH).read_bytes())
    tracked = set(git(root, "ls-files", "-z").decode().split("\0"))
    pending = []
    for name, item in registry["files"].items():
        path = root / relative(name)
        if name not in tracked or not os.path.lexists(path):
            continue
        expected = registry["objects"][item["sha256"]]
        if hash_hot(root, name) != (item["sha256"], expected["bytes"]):
            raise ValueError(f"Refusing to prune modified evidence: {name}")
        pending.append((name, item["sha256"], expected["bytes"]))
    # Verify the whole set first. A damaged late file cannot cause a partial sweep.
    removed = 0
    for name, sha, size in pending:
        if hash_hot(root, name) != (sha, size):
            raise ValueError(f"Evidence changed before removal: {name}")
        (root / name).unlink()
        removed += size
    return {**result, "pruned_files": len(pending), "pruned_bytes": removed,
            "ignored_alias_originals_removed": False}


def restore(root, prefix, destination):
    """Write an explicit inspection copy; never mutate the evidence repository."""
    root = Path(root).resolve()
    prefix = relative(prefix)
    destination = Path(destination).absolute()
    if root == destination or root in destination.parents or destination.exists():
        raise ValueError("Restore to a new directory outside the evidence repository")
    for parent in destination.parents:
        if parent.is_symlink():
            raise ValueError("Restore destination cannot traverse a symlink")
    registry_path = root / evidence.INDEX_PATH
    registry = json.loads(registry_path.read_bytes()) if registry_path.exists() else {"files": {}}
    paths = list(evidence.iter_files(root / prefix))
    if not paths:
        raise ValueError("No retained evidence matches that prefix")
    # Verify all files before creating the destination; no source script is executed.
    for path in paths:
        evidence.read_bytes(path)
    destination.mkdir(parents=True)
    total = 0
    for path in paths:
        name = path.relative_to(root).as_posix()
        target = destination / path.relative_to(root / prefix)
        # A single-file prefix still receives a named file in the new directory.
        if target == destination:
            target = destination / path.name
        target.parent.mkdir(parents=True, exist_ok=True)
        raw = evidence.read_bytes(path)
        target.write_bytes(raw)
        mode = registry["files"].get(name, {}).get("mode")
        target.chmod(0o755 if mode == "100755" or mode is None and path.stat().st_mode & 0o111 else 0o644)
        total += len(raw)
    return {"restored_files": len(paths), "restored_bytes": total, "destination": str(destination)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("prepare", "check", "prune", "restore", "where"))
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--plan", type=Path)
    parser.add_argument("--source-revision")
    parser.add_argument("--aliases", type=Path)
    parser.add_argument("--deep", action="store_true")
    parser.add_argument("--prefix")
    parser.add_argument("--destination", type=Path)
    args = parser.parse_args()
    try:
        if args.action == "prepare":
            if args.plan is None or args.source_revision is None:
                raise ValueError("prepare needs --plan and --source-revision")
            result = prepare(args.root, args.plan, args.source_revision, aliases=args.aliases)
        elif args.action == "check":
            result = evidence.validate_repository(args.root, deep=args.deep)
        elif args.action == "prune":
            result = prune(args.root)
        elif args.action == "where":
            result = evidence.source_location(args.root / relative(args.prefix))
        else:
            if args.prefix is None or args.destination is None:
                raise ValueError("restore needs --prefix and --destination")
            result = restore(args.root, args.prefix, args.destination)
        print(json.dumps(result, ensure_ascii=False))
    except (KeyError, ValueError, OSError) as error:
        parser.exit(1, str(error) + "\n")


if __name__ == "__main__":
    main()
