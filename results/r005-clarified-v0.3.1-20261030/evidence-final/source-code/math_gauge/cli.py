import argparse
import json
import subprocess
import sys
from pathlib import Path

from .catalog import Suite, read_json, write_json
from .execution import check_lean, run
from .review import apply_reviews, report, templates


def parser():
    p = argparse.ArgumentParser(
        prog="math-gauge",
        description="Weak-structure mathematical evaluation, public or private question suite.",
    )
    sub = p.add_subparsers(dest="action", required=True)
    for name in ("validate", "list", "prepare", "run", "check-lean"):
        c = sub.add_parser(name)
        c.add_argument("--suite", default="cases/public")
        if name in {"run", "check-lean"}:
            c.add_argument("--case", action="append", dest="ids")
        if name == "prepare":
            c.add_argument("--case", required=True)
        if name in {"prepare", "run"}:
            c.add_argument("--out", required=True)
        if name == "run":
            g = c.add_mutually_exclusive_group(required=True)
            g.add_argument("--replay")
            g.add_argument(
                "--command-json",
                help="Explicit argv array. Receives one JSON request on stdin; stdout is the response.",
            )
            c.add_argument("--model")
            c.add_argument("--timeout", type=float, default=120)
        if name == "check-lean":
            c.add_argument("--out", required=True)
    for name in ("review-template", "review", "report"):
        c = sub.add_parser(name)
        c.add_argument("--run", required=True)
        if name == "review-template":
            c.add_argument("--out", required=True)
        if name == "review":
            c.add_argument("--input", required=True)
        if name == "report":
            c.add_argument(
                "--out",
                required=True,
                help="New output directory for report.json and report.md",
            )
    return p


def main(argv=None):
    args = parser().parse_args(argv)
    try:
        if args.action in {"validate", "list", "prepare", "run", "check-lean"}:
            suite = Suite.load(args.suite)
        if args.action == "validate":
            print(
                json.dumps(
                    {
                        "cases": len(suite.cases),
                        "suite_sha256": suite.sha256,
                        "human_approved": sum(
                            c["review"]["human"] == "approved"
                            for c in suite.cases.values()
                        ),
                    },
                    ensure_ascii=False,
                )
            )
        elif args.action == "list":
            for c in suite.cases.values():
                print(f"{c['id']}\t{c['track']}\t{c['title']}\t{c['status']}")
        elif args.action == "prepare":
            suite.prepare(suite.select([args.case])[0], args.out)
            print(args.out)
        elif args.action == "run":
            command = json.loads(args.command_json) if args.command_json else None
            if command is not None and (
                not isinstance(command, list)
                or not command
                or not all(isinstance(x, str) for x in command)
            ):
                raise ValueError("--command-json must be a nonempty argv array")
            result = run(
                suite,
                args.out,
                args.ids,
                args.replay,
                command,
                args.model,
                args.timeout,
            )
            print(args.out)
            return 1 if result["execution_failures"] else 0
        elif args.action == "check-lean":
            out = Path(args.out)
            if out.exists():
                raise ValueError("Output already exists")
            result = check_lean(suite, args.ids)
            write_json(out, result)
            print(
                f"{len(result['checks'])} files; all_compiled={result['all_compiled']}; semantic alignment is not inferred"
            )
            return 0 if result["all_compiled"] else 1
        elif args.action == "review-template":
            if Path(args.out).exists():
                raise ValueError("Output already exists")
            write_json(args.out, templates(args.run))
            print(args.out)
        elif args.action == "review":
            result = apply_reviews(args.run, read_json(args.input))
            print(f"{len(result)} recorded reviews")
        elif args.action == "report":
            data, md = report(args.run)
            out = Path(args.out)
            out.mkdir(parents=True, exist_ok=False)
            write_json(out / "report.json", data)
            (out / "report.md").write_text(md, encoding="utf-8")
            print(str(out / "report.md"))
        return 0
    except (
        ValueError,
        OSError,
        KeyError,
        TypeError,
        subprocess.SubprocessError,
    ) as error:
        print(f"math-gauge: {error}", file=sys.stderr)
        return 2
