#!/usr/bin/env python3
"""Build the private independent-research operator ZIP without calling a model."""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import stat
import sys
from zipfile import ZIP_DEFLATED, ZipFile, ZipInfo


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from math_gauge import independent_research_handoff as handoff
from math_gauge import taste_v130


ARCHIVE_NAME = "independent-open-research-v1.3.0-operator.zip"


def build(registration, destination):
    """Copy exact candidate-role bytes from the shared case validator's allowlist."""
    registration, case, data = taste_v130.load_case(registration)
    destination = handoff._absolute(destination)
    handoff._separate(ROOT, taste_v130._source_tree(registration), destination)
    files = {
        "README.md": handoff.read_file(ROOT, "docs/independent-research-handoff.md"),
        "research_handoff.py": handoff.read_file(ROOT, "math_gauge/independent_research_handoff.py"),
    }
    allowlist = {
        **{f"control-inputs/{round_id}.md": data["rounds"][round_id] for round_id in handoff.ROUNDS},
        "control-inputs/rules.md": data["rules"],
        **{f"control-inputs/{ref['path']}": ref for ref in data["packet"]},
    }
    handoff.require(len(data["packet"]) == 5, "Expected the fixed body and four figures")
    contract = json.loads(taste_v130._read(case, data["review_contract"]))
    for name, ref in allowlist.items():
        raw = handoff._read_ref(case, ref)
        if name.endswith(".md"):
            text = raw.decode()
            handoff.require(not any(literal in text for literal in contract["packet_forbidden_literals"]),
                            "Candidate material contains an excluded marker")
        files[name] = raw
    manifest = {"schema": handoff.BUNDLE_SCHEMA, "edition": handoff.EDITION,
                "round_seconds": handoff.ROUND_SECONDS,
                "files": [handoff.descriptor(name, raw) for name, raw in sorted(files.items())]}
    files["manifest.json"] = handoff.json_bytes(manifest)
    receipt = {
        "schema": "math-gauge.independent-research-handoff-build/v1",
        "edition": handoff.EDITION,
        "distribution": "private-operator-only",
        "candidate_calls": 0,
        "source_registration": handoff.descriptor(registration.name, registration.read_bytes()),
        "source_case_material": list(allowlist.values()),
        "bundle_manifest": handoff.descriptor("manifest.json", files["manifest.json"]),
        "members": [handoff.descriptor(name, raw) for name, raw in sorted(files.items())],
    }
    destination.mkdir(mode=0o700)
    archive = destination / ARCHIVE_NAME
    with ZipFile(archive, "x") as zip_file:
        for name, raw in sorted(files.items()):
            member = ZipInfo(name)
            member.create_system = 3
            member.external_attr = (stat.S_IFREG | 0o600) << 16
            zip_file.writestr(member, raw, compress_type=ZIP_DEFLATED, compresslevel=9)
    archive.chmod(0o600)
    with ZipFile(archive) as zip_file:
        handoff.require(zip_file.namelist() == sorted(files) and zip_file.testzip() is None
                        and all(zip_file.read(name) == raw for name, raw in files.items()),
                        "ZIP member inventory or source bytes differ")
    receipt["archive"] = handoff.descriptor(archive.name, archive.read_bytes())
    handoff._new(destination / "build-receipt.json", handoff.json_bytes(receipt))
    return receipt


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--registration", required=True, type=Path)
    parser.add_argument("--out", required=True, type=Path, help="A fresh private local directory")
    args = parser.parse_args(argv)
    try:
        receipt = build(args.registration, args.out)
    except (OSError, ValueError, TypeError, KeyError) as error:
        parser.error(str(error))
    print(handoff.json_bytes({"directory": str(args.out.absolute()), "archive": receipt["archive"],
                             "members": len(receipt["members"]), "candidate_calls": 0}).decode(), end="")


if __name__ == "__main__":
    main()
