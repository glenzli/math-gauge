"""Real file opens under the policy, or macOS policy checks for a live PID.

Copy this data-free file into the prepared run before denying the source repo.
No file contents, other than the positive task hash, are emitted.
"""

import argparse
import ctypes
import datetime
import errno
import hashlib
import json
import os
from pathlib import Path
import sys


def probe(manifest, pid=None, role=None):
    positive = manifest["positive"]
    expected = manifest["sha256"]
    checks = []
    if pid is None:
        digest = None
        try:
            digest = hashlib.sha256(Path(positive).read_bytes()).hexdigest()
            checks.append({"path": positive, "expected": "allowed", "passed": digest == expected,
                           "observed_sha256": digest})
        except OSError as error:
            checks.append({
                "path": positive, "expected": "allowed", "passed": False,
                "errno": error.errno, "observed_sha256": None,
            })
        for item in manifest["negative"]:
            check = {**item, "expected": "denied", "passed": False}
            try:
                with open(item["path"], "rb") as stream:
                    stream.read(1)
                check["outcome"] = "UNEXPECTED_ALLOWED"
            except OSError as error:
                check.update(
                    errno=error.errno,
                    outcome="DENIED" if error.errno in {errno.EPERM, errno.EACCES}
                    else "OTHER_ERROR",
                )
                check["passed"] = check["outcome"] == "DENIED" and item["exists_before_run"] is True
            checks.append(check)
        kind = "actual-file-open"
    else:
        if sys.platform != "darwin" or role not in {"parent", "worker"} or pid <= 0:
            raise ValueError("Live PID checks require macOS, a positive PID and parent/worker role")
        lib = ctypes.CDLL("/usr/lib/libsandbox.dylib", use_errno=True)
        flags = 1 | ctypes.c_uint.in_dll(lib, "SANDBOX_CHECK_NO_REPORT").value
        lib.sandbox_check.restype = ctypes.c_int
        lib.sandbox_check.argtypes = [ctypes.c_int, ctypes.c_char_p, ctypes.c_int]
        paths = [(positive, False)] + [(x["path"], True) for x in manifest["negative"]]
        for path, denied in paths:
            ctypes.set_errno(0)
            result = lib.sandbox_check(
                pid, b"file-read-data", flags, ctypes.c_char_p(path.encode())
            )
            checks.append({
                "path": path, "expected": "denied" if denied else "allowed",
                "result": result, "errno": ctypes.get_errno(),
                "passed": result > 0 if denied else result == 0,
            })
        kind = "live-pid-policy-query"
    return {
        "kind": kind, "role": role, "pid": os.getpid() if pid is None else pid,
        "probe_process_pid": os.getpid(),
        "utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "prompt_sha256": expected, "checks": checks,
        "passed": bool(checks) and all(x["passed"] for x in checks),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", required=True)
    parser.add_argument("--out", required=True)
    parser.add_argument("--pid", type=int)
    parser.add_argument("--role", choices=("parent", "worker"))
    args = parser.parse_args()
    try:
        manifest = json.loads(Path(args.manifest).read_text())
        result = probe(manifest, args.pid, args.role)
        with Path(args.out).open("x", encoding="utf-8") as stream:
            json.dump(result, stream, indent=2)
            stream.write("\n")
        return 0 if result["passed"] else 1
    except (OSError, ValueError, KeyError, TypeError) as error:
        print("isolation-probe: " + str(error), file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
