"""Evaluator-only access to exact retained bytes stored in local Git history.

Hot files remain authoritative. A missing logical path may use only its explicit
retention entry; damaged files, symlinks and missing Git objects never trigger a
different source, a checkout, a fetch or execution of retained code.
"""
from collections import OrderedDict
from contextlib import contextmanager
import errno
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import subprocess
import tempfile
import threading
import unicodedata

INDEX_PATH = "results/evidence-retention/v0.1.0/index.json"
SCHEMA = "math-gauge.evidence-retention/v1"
VERSION = "0.1.0"
_SHA = re.compile(r"[0-9a-f]{64}")
_OID = re.compile(r"[0-9a-f]{40}")
_MODES = {"100644", "100755"}
_CACHE_BYTES = 32 * 1024 * 1024
_indexes = {}
_lock = threading.RLock()


def _require(value, message):
    if not value:
        raise ValueError(message)


def _relative(value):
    _require(isinstance(value, str) and value and "\\" not in value
             and not any(ord(c) < 32 or ord(c) == 127 for c in value),
             "Unsafe retained evidence path")
    p = PurePosixPath(value)
    _require(not p.is_absolute() and str(p) == value
             and p.parts[0] != ".git"
             and all(part not in {"", ".", ".."} and ":" not in part
                     for part in value.split("/")), "Unsafe retained evidence path")
    return value


def _unique_json(pairs):
    result = {}
    for key, value in pairs:
        _require(key not in result, "Duplicate retention index field")
        result[key] = value
    return result


def _location(path):
    """Normalize an OS root alias, never a symlink within the Git worktree."""
    path = Path(os.path.abspath(os.fspath(path)))
    for name in ("var", "tmp"):
        alias = Path("/") / name
        if (path.is_relative_to(alias) and alias.is_symlink()
                and alias.resolve() == Path("/private") / name):
            path = Path("/private") / name / path.relative_to(alias)
    for parent in (path, *path.parents):
        _require(not parent.is_symlink(), "Retained evidence cannot traverse a symlink")
    repositories = []
    for parent in (path, *path.parents):
        marker = parent / ".git"
        if os.path.lexists(marker):
            _require(not marker.is_symlink(), "Git metadata cannot be a symlink")
            mode = marker.lstat().st_mode
            _require(stat.S_ISDIR(mode) or stat.S_ISREG(mode), "Git metadata is not a safe file or directory")
            repositories.append(parent)
    if repositories:
        # Sealed payloads can contain their own historical .git directory. The
        # containing evaluator registry owns their explicit logical aliases.
        indexed = [parent for parent in repositories if os.path.lexists(parent / INDEX_PATH)]
        root = indexed[-1] if indexed else repositories[0]
        relative = path.relative_to(root)
        _require(not relative.parts or relative.parts[0] != ".git",
                 "The repository's live Git metadata is not retained evidence")
        return path, root
    # Ordinary standalone hot fixtures need neither Git nor a retention index.
    return path, None


def _hot_stat(path, root):
    anchor = root or path.parent
    relative = path.relative_to(anchor)
    current = anchor
    for index, part in enumerate(relative.parts):
        current = current / part
        try:
            info = current.lstat()
        except FileNotFoundError:
            return None
        _require(not stat.S_ISLNK(info.st_mode), "Retained evidence cannot traverse a symlink")
        if index + 1 < len(relative.parts):
            _require(stat.S_ISDIR(info.st_mode), "Retained evidence parent is not a directory")
    return info if relative.parts else anchor.stat()


def _hot_bytes(path, root):
    """Read a regular hot file with no-follow directory opens and a stable stat."""
    anchor = root or path.parent
    parts = path.relative_to(anchor).parts
    _require(parts, "Retained evidence must be a regular file")
    descriptors = []
    try:
        flags = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW
        descriptors.append(os.open(anchor, flags))
        for part in parts[:-1]:
            descriptors.append(os.open(part, flags, dir_fd=descriptors[-1]))
        fd = os.open(parts[-1], os.O_RDONLY | os.O_NOFOLLOW | getattr(os, "O_NONBLOCK", 0),
                     dir_fd=descriptors[-1])
        with os.fdopen(fd, "rb") as stream:
            before = os.fstat(stream.fileno())
            _require(stat.S_ISREG(before.st_mode), "Retained evidence must be a regular file")
            raw = stream.read()
            after = os.fstat(stream.fileno())
            identity = lambda s: (s.st_dev, s.st_ino, s.st_size, s.st_mtime_ns, s.st_ctime_ns)
            _require(identity(before) == identity(after), "Retained evidence changed during reading")
            return raw
    except FileNotFoundError:
        raise
    except OSError as error:
        if error.errno == errno.ELOOP:
            raise ValueError("Retained evidence cannot traverse a symlink") from error
        raise ValueError("Retained evidence is not a safe regular file") from error
    finally:
        for fd in reversed(descriptors):
            os.close(fd)


def _git(root, *arguments):
    env = os.environ.copy()
    for key in ("GIT_DIR", "GIT_WORK_TREE", "GIT_INDEX_FILE", "GIT_OBJECT_DIRECTORY",
                "GIT_ALTERNATE_OBJECT_DIRECTORIES", "GIT_NAMESPACE"):
        env.pop(key, None)
    env.update(GIT_NO_LAZY_FETCH="1", GIT_NO_REPLACE_OBJECTS="1",
               GIT_TERMINAL_PROMPT="0", GIT_OPTIONAL_LOCKS="0")
    try:
        result = subprocess.run(["git", "--no-lazy-fetch", "--no-replace-objects", "-C", str(root),
                                 *arguments], env=env, capture_output=True, check=False)
    except OSError as error:
        raise ValueError("Local Git evidence is unavailable; no network recovery is allowed") from error
    _require(result.returncode == 0,
             "Local Git evidence object is unavailable or invalid; no network recovery is allowed")
    return result.stdout


class _Index:
    def __init__(self, root, raw):
        data = json.loads(raw, object_pairs_hook=_unique_json)
        _require(isinstance(data, dict) and set(data) == {
            "schema", "version", "source_git_revision", "objects", "files"}
            and data["schema"] == SCHEMA and data["version"] == VERSION
            and isinstance(data["source_git_revision"], str)
            and _OID.fullmatch(data["source_git_revision"]), "Invalid retention index identity")
        _require(isinstance(data["objects"], dict) and isinstance(data["files"], dict),
                 "Retention index needs object and logical-file maps")
        self.root, self.revision = root, data["source_git_revision"]
        self.objects, self.files = data["objects"], data["files"]
        for sha, item in self.objects.items():
            _require(_SHA.fullmatch(sha) and isinstance(item, dict)
                     and set(item) == {"bytes", "git_blob", "git_path"}
                     and type(item["bytes"]) is int and item["bytes"] >= 0
                     and isinstance(item["git_blob"], str) and _OID.fullmatch(item["git_blob"]),
                     "Invalid retained Git object descriptor")
            _relative(item["git_path"])
        folded = {}
        for name, item in self.files.items():
            _relative(name)
            _require(name != INDEX_PATH and isinstance(item, dict)
                     and set(item) == {"sha256", "mode", "reason"}
                     and isinstance(item.get("sha256"), str) and item["sha256"] in self.objects
                     and isinstance(item.get("mode"), str) and item["mode"] in _MODES
                     and isinstance(item.get("reason"), str) and item["reason"].strip(),
                     "Invalid retained logical-file descriptor")
            alias = unicodedata.normalize("NFC", name).casefold()
            _require(alias not in folded, "Case or Unicode aliased retained evidence paths")
            folded[alias] = name
        self.tree = None
        self.sizes = {}
        self.cache, self.cache_bytes = OrderedDict(), 0
        self.lock = threading.RLock()

    def source(self, sha):
        item = self.objects[sha]
        if self.tree is None:
            _require(_git(self.root, "cat-file", "-t", self.revision).strip() == b"commit",
                     "Retained source Git revision must be a commit object")
            rows = _git(self.root, "ls-tree", "-r", "-z", "--full-tree", self.revision)
            wanted = {value["git_path"] for value in self.objects.values()}
            tree = {}
            for row in rows.split(b"\0"):
                if not row:
                    continue
                header, name = row.split(b"\t", 1)
                name = name.decode("utf-8")
                if name in wanted:
                    mode, kind, oid = header.decode("ascii").split()
                    tree[name] = (mode, kind, oid)
            self.tree = tree
        value = self.tree.get(item["git_path"])
        _require(value is not None and value[0] in _MODES and value[1:] == ("blob", item["git_blob"]),
                 "Retained Git path is not the bound regular blob at its source revision")
        return item

    def available(self, sha):
        with self.lock:
            item = self.source(sha)
            if sha not in self.sizes:
                size = _git(self.root, "cat-file", "-s", item["git_blob"]).strip()
                _require(size.isdigit() and int(size) == item["bytes"], "Retained Git object size changed")
                self.sizes[sha] = int(size)
            return True

    def read(self, sha, *, use_cache=True):
        with self.lock:
            item = self.source(sha)
            if use_cache and sha in self.cache:
                self.cache.move_to_end(sha)
                return self.cache[sha]
            raw = _git(self.root, "cat-file", "blob", item["git_blob"])
            _require(len(raw) == item["bytes"] and hashlib.sha256(raw).hexdigest() == sha,
                     "Retained Git evidence bytes changed")
            self.sizes[sha] = len(raw)
            if len(raw) <= 1024 * 1024:
                self.cache[sha] = raw
                self.cache_bytes += len(raw)
                while self.cache_bytes > _CACHE_BYTES:
                    _, removed = self.cache.popitem(last=False)
                    self.cache_bytes -= len(removed)
            return raw


def _index(root):
    if root is None:
        return None
    path = root / INDEX_PATH
    info = _hot_stat(path, root)
    if info is None:
        return None
    _require(stat.S_ISREG(info.st_mode), "Retention index must be a regular hot file")
    signature = (info.st_dev, info.st_ino, info.st_size, info.st_mtime_ns, info.st_ctime_ns)
    with _lock:
        cached = _indexes.get(root)
        if cached is None or cached[0] != signature:
            _indexes[root] = (signature, _Index(root, _hot_bytes(path, root)))
        return _indexes[root][1]


def read_bytes(path):
    path, root = _location(path)
    index = _index(root)
    name = path.relative_to(root).as_posix() if root is not None else None
    item = index.files.get(name) if index is not None else None
    _require(root is None or ".git" not in path.relative_to(root).parts or item is not None,
             "Nested Git payloads require an explicit retention entry")
    try:
        raw = _hot_bytes(path, root)
    except FileNotFoundError:
        if item is None:
            raise
        return index.read(item["sha256"])
    if item is not None:
        source = index.objects[item["sha256"]]
        _require(len(raw) == source["bytes"] and hashlib.sha256(raw).hexdigest() == item["sha256"],
                 "Retained hot evidence bytes changed; Git fallback is forbidden")
    return raw


def read_json(path):
    return json.loads(read_bytes(path))


def validate_repository(root, *, deep=False):
    """Validate the local retention registry without restoring any source path.

    Deep validation reads every unique object from Git, including objects whose
    logical files are still hot. It deliberately bypasses the byte cache.
    """
    path, repository = _location(root)
    _require(repository is not None and path == repository,
             "Retention validation needs the repository root")
    index = _index(repository)
    if index is None:
        return {"present": False, "files": 0, "unique_objects": 0,
                "logical_bytes": 0, "unique_bytes": 0, "deep": bool(deep)}
    with index.lock:
        index.tree = None
        index.sizes.clear()
        for sha in index.objects:
            if deep:
                index.read(sha, use_cache=False)
            else:
                index.available(sha)
    return {"present": True, "schema": SCHEMA, "version": VERSION,
            "source_git_revision": index.revision, "files": len(index.files),
            "unique_objects": len(index.objects),
            "logical_bytes": sum(index.objects[item["sha256"]]["bytes"]
                                 for item in index.files.values()),
            "unique_bytes": sum(item["bytes"] for item in index.objects.values()),
            "deep": bool(deep)}


def source_location(path):
    """Return the exact source identity used by an evaluator-facing file link."""
    path, root = _location(path)
    _require(root is not None, "Evidence source location needs a Git repository")
    index = _index(root)
    name = path.relative_to(root).as_posix()
    item = index.files.get(name) if index is not None else None
    raw = read_bytes(path)
    if item is not None:
        index.available(item["sha256"])
        source = index.objects[item["sha256"]]
        return {"repository_root": str(root), "revision": index.revision,
                "git_path": source["git_path"], "sha256": item["sha256"],
                "bytes": source["bytes"]}
    return {"repository_root": str(root), "revision": None, "git_path": name,
            "sha256": hashlib.sha256(raw).hexdigest(), "bytes": len(raw)}


def exists(path):
    path, root = _location(path)
    info = _hot_stat(path, root)
    if info is not None:
        return True
    index = _index(root)
    if index is None:
        return False
    name = path.relative_to(root).as_posix()
    if name in index.files:
        return index.available(index.files[name]["sha256"])
    return any(value.startswith(name.rstrip("/") + "/") for value in index.files)


def is_file(path):
    path, root = _location(path)
    info = _hot_stat(path, root)
    if info is not None:
        return stat.S_ISREG(info.st_mode)
    index = _index(root)
    name = path.relative_to(root).as_posix() if root is not None else None
    return bool(index is not None and name in index.files
                and index.available(index.files[name]["sha256"]))


def iter_files(prefix):
    """Enumerate regular logical files, including only explicitly retained cold paths."""
    requested = Path(prefix)
    prefix, root = _location(prefix)
    index = _index(root)
    paths = set()
    info = _hot_stat(prefix, root)
    if info is not None and stat.S_ISREG(info.st_mode):
        paths.add(prefix)
    elif info is not None:
        _require(stat.S_ISDIR(info.st_mode), "Retained evidence prefix is not a directory")
        for directory, dirs, files in os.walk(prefix, followlinks=False):
            dirs[:] = [name for name in dirs if name != ".git"]
            for name in (*dirs, *files):
                path = Path(directory) / name
                state = path.lstat()
                _require(not stat.S_ISLNK(state.st_mode), "Retained evidence cannot traverse a symlink")
                if name in files:
                    _require(stat.S_ISREG(state.st_mode), "Retained evidence must be a regular file")
                    if (root is None or ".git" not in path.relative_to(root).parts
                            or index is not None and path.relative_to(root).as_posix() in index.files):
                        paths.add(path)
    if index is not None:
        paths.update(root / name for name in index.files
                     if (root / name) == prefix or prefix in (root / name).parents)
    # Match Path.rglob's caller-visible spelling (for example macOS /var aliases).
    yield from (requested / path.relative_to(prefix) for path in sorted(paths))


@contextmanager
def materialize_tree(prefix):
    """Restore exact logical files only into a disposable evaluator directory."""
    prefix, root = _location(prefix)
    index = _index(root)
    with tempfile.TemporaryDirectory(prefix="math-gauge-evidence-") as temporary:
        target = Path(temporary).resolve()
        for source in iter_files(prefix):
            relative = source.relative_to(prefix)
            _require(relative.parts, "Materialized evidence prefix must be a directory")
            dest = target / relative
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.write_bytes(read_bytes(source))
            entry = index.files.get(source.relative_to(root).as_posix()) if index is not None else None
            mode = entry["mode"] if entry is not None else (
                "100755" if source.stat().st_mode & stat.S_IXUSR else "100644")
            dest.chmod(0o555 if mode == "100755" else 0o444)
        yield target
