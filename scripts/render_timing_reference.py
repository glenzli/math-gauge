#!/usr/bin/env python3
"""Render the independent answer-time reference without scoring or model calls."""
import argparse
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from scripts.results_publication import prepare_publication, write_publication
from scripts.timing_reference import build_reference, render_panel


def write_reference(root, destination):
    data = build_reference(root)
    templates = Path(__file__).parent / "templates"
    page = ('<!doctype html><html lang="zh-CN"><head><meta charset="utf-8">'
            '<meta name="viewport" content="width=device-width,initial-scale=1">'
            '<title>答题耗时参考 · Math Gauge</title><link rel="stylesheet" href="assets/timing-reference.css">'
            '</head><body class="timing-page"><header><nav><a href="../index.html">Math Gauge</a>'
            '<a href="../index.html">能力榜 / Scores</a><div class="timing-languages">'
            '<button data-timing-language="zh" aria-pressed="true">中文</button>'
            '<button data-timing-language="en" aria-pressed="false">EN</button></div></nav></header><main>'
            + render_panel(data, link_prefix="../") + '</main><script src="assets/timing-reference.js"></script></body></html>')
    files = {"index.html": page, "data.json": json.dumps(data, ensure_ascii=False, indent=2) + "\n"}
    observations = Path(root) / "site/timings/observed-clocks.json"
    if observations.exists():
        files["observed-clocks.json"] = observations.read_bytes()
    for name in ("timing-reference.css", "timing-reference.js"):
        files["assets/" + name] = (templates / name).read_text()
    write_publication(destination, prepare_publication(files, root))
    return data


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--out", type=Path)
    args = parser.parse_args()
    data = write_reference(args.root, args.out or args.root / "site/timings")
    print(json.dumps({"status": "passed", "models": len(data["models"]), "sample_tasks": len(data["cases"]),
                      "new_candidate_calls": 0, "scores_modified": False}))


if __name__ == "__main__":
    main()
