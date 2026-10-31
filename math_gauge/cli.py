import argparse
import json
import subprocess
import sys
from pathlib import Path

from .catalog import Suite, read_json, write_json
from .benchmarks import BenchmarkProfile, build_plan, read_plan, write_plan
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
        c.add_argument("--suite", default="cases")
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
    c = sub.add_parser("benchmark-plan", help="Freeze a complete evaluator-only benchmark plan; no model calls.")
    c.add_argument("--suite", default="cases")
    c.add_argument("--profile", default="protocol/benchmark-profile.json")
    c.add_argument("--target", action="append", dest="targets")
    c.add_argument("--runtime", help="Predeclared model, budget and adapter identity JSON.")
    c.add_argument("--out", required=True)
    c = sub.add_parser("benchmark-run", help="Explicitly execute one frozen plan projection.")
    c.add_argument("--suite", default="cases")
    c.add_argument("--plan", required=True)
    c.add_argument("--out", required=True)
    c.add_argument("--target", action="append", dest="targets")
    c.add_argument("--reuse-run", action="append", dest="reuse_runs", default=[])
    g = c.add_mutually_exclusive_group(required=True)
    g.add_argument("--replay", help="Offline fixture responses; never model scores.")
    g.add_argument("--command-json", help="Frozen adapter argv array; receives only candidate messages.")
    c = sub.add_parser("benchmark-check", help="Read-only validation of a frozen plan or complete run evidence.")
    g = c.add_mutually_exclusive_group(required=True)
    g.add_argument("--plan")
    g.add_argument("--run")
    c.add_argument("--review-snapshot", type=int, help="Read a retained review version; default is the active snapshot.")
    c.add_argument("--audit-snapshot", help="Read a retained execution-audit SHA-256; historical selection is labeled.")
    c = sub.add_parser("benchmark-check-lean", help="Explicitly verify the original candidate Lean for one frozen slot.")
    c.add_argument("--run", required=True)
    c.add_argument("--slot", required=True)
    c.add_argument("--out", required=True)
    c.add_argument("--dependency-root", required=True)
    c.add_argument("--lean")
    for name in ("benchmark-review-template", "benchmark-review", "benchmark-collect"):
        c = sub.add_parser(name)
        c.add_argument("--run", required=True)
        if name == "benchmark-review":
            c.add_argument("--input", required=True)
            c.add_argument("--revise", action="store_true", help="Append a new review snapshot while retaining prior evidence.")
            c.add_argument("--expected-review-snapshot", help="Expected current review snapshot SHA-256.")
        else:
            c.add_argument("--out", required=True)
            if name == "benchmark-collect":
                c.add_argument("--review-snapshot", type=int)
                c.add_argument("--audit-snapshot")
    for name in ("benchmark-evidence-template", "benchmark-evidence-import", "benchmark-evidence-check"):
        c = sub.add_parser(name, help="Prepare, import or verify execution evidence without candidate calls.")
        c.add_argument("--run", required=True)
        if name == "benchmark-evidence-template":
            c.add_argument("--slot", help="Export one slot submission; default exports all slot forms.")
            c.add_argument("--out", required=True)
        elif name == "benchmark-evidence-import":
            c.add_argument("--slot", required=True)
            c.add_argument("--input", required=True, help="Submission JSON with explicit raw evidence paths.")
            c.add_argument("--revise", action="store_true", help="Append an audit revision; retain prior receipts.")
            c.add_argument("--expected-audit-snapshot", help="Expected current audit snapshot SHA-256.")
        else:
            c.add_argument("--audit-snapshot", help="Read a retained audit SHA-256; default verifies the current snapshot.")
            c.add_argument("--out", help="New JSON output file; default prints the verified evidence.")
    c = sub.add_parser("benchmark-report", help="Aggregate validated same-plan evidence with fixed denominators.")
    c.add_argument("--run", action="append", dest="runs", required=True)
    c.add_argument("--out", required=True)
    c.add_argument("--review-snapshot", type=int, help="Use this retained version in each supplied run.")
    g = c.add_mutually_exclusive_group()
    g.add_argument("--audit-snapshot", help="Retained audit SHA-256; requires exactly one --run.")
    g.add_argument("--audit-snapshots", help="JSON file mapping every resolved --run root to its retained audit SHA-256.")
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
        elif args.action == "benchmark-plan":
            suite = Suite.load(args.suite)
            profile = BenchmarkProfile.load(args.profile, suite)
            result = build_plan(profile, suite, args.targets,
                                runtime=read_json(args.runtime) if args.runtime else None)
            write_plan(args.out, result)
            print(json.dumps({"plan": args.out, "plan_sha256": result["plan_sha256"],
                              "planned": result["planned"], "candidate_calls": 0}))
        elif args.action == "benchmark-run":
            from .reliability import execute_reliability_run
            command = json.loads(args.command_json) if args.command_json else None
            if command is not None and (not isinstance(command, list) or not command
                                        or not all(isinstance(x, str) for x in command)):
                raise ValueError("--command-json must be a nonempty argv array")
            result = execute_reliability_run(read_plan(args.plan), Suite.load(args.suite),
                                             args.out, command=command, replay=args.replay,
                                             targets=args.targets, reuse_runs=args.reuse_runs)
            print(args.out)
            return 1 if result.get("execution_failures", 0) else 0
        elif args.action == "benchmark-check":
            if args.plan:
                result = read_plan(args.plan)
                summary = {"plan_sha256": result["plan_sha256"], "planned": result["planned"],
                           "runtime_frozen": result["runtime_frozen"], "candidate_calls": 0}
            else:
                from .reliability import inspect_reliability_run, reliability_score_inputs
                meta, records = inspect_reliability_run(args.run)
                collected = reliability_score_inputs(args.run, snapshot=args.review_snapshot,
                                                     audit_snapshot=args.audit_snapshot)
                summary = {"run": args.run, "plan_sha256": collected["plan"]["plan_sha256"],
                           "validated_slots": len(records), "run_id": meta.get("run_id"),
                           "audit_snapshot": collected.get("audit_snapshot"),
                           "execution_eligible_slots": sum(r["comparison_eligible"] for r in collected["slots"]),
                           "execution_eligibility": collected.get("execution_eligibility")}
            print(json.dumps(summary))
        elif args.action == "benchmark-check-lean":
            from .reliability_review import verify_reliability_candidate_lean
            result = verify_reliability_candidate_lean(
                args.run, args.slot, args.out,
                dependency_root=args.dependency_root, lean=args.lean)
            print(json.dumps({"slot_id": args.slot, "status": result["status"], "out": args.out}))
            return 0 if result["status"] == "passed" else 1
        elif args.action in {"benchmark-review-template", "benchmark-review", "benchmark-collect"}:
            from .reliability import (apply_reliability_reviews, reliability_review_templates,
                                      reliability_score_inputs)
            if args.action == "benchmark-review":
                result = apply_reliability_reviews(args.run, read_json(args.input),
                                                   revise=args.revise,
                                                   expected_snapshot=args.expected_review_snapshot)
                print(f"{len(result)} recorded benchmark reviews")
            else:
                if Path(args.out).exists():
                    raise ValueError("Output already exists")
                result = (reliability_review_templates(args.run)
                          if args.action == "benchmark-review-template"
                          else reliability_score_inputs(args.run, snapshot=args.review_snapshot,
                                                        audit_snapshot=args.audit_snapshot))
                write_json(args.out, result)
                print(args.out)
        elif args.action in {"benchmark-evidence-template", "benchmark-evidence-import", "benchmark-evidence-check"}:
            from .eligibility import (execution_eligibility_templates, import_execution_eligibility,
                                      verify_execution_eligibility)
            if args.action == "benchmark-evidence-import":
                result = import_execution_eligibility(
                    args.run, args.slot, args.input, revise=args.revise,
                    expected_snapshot=args.expected_audit_snapshot)
                print(json.dumps(result, ensure_ascii=False))
            else:
                if args.out and Path(args.out).exists():
                    raise ValueError("Output already exists")
                if args.action == "benchmark-evidence-template":
                    result = execution_eligibility_templates(args.run)
                    if args.slot:
                        selected = [item for item in result["slots"] if item["slot_id"] == args.slot]
                        if not selected:
                            raise ValueError("Unknown execution evidence slot")
                        result = selected[0]
                else:
                    result = verify_execution_eligibility(args.run, audit_snapshot=args.audit_snapshot)
                if args.out:
                    write_json(args.out, result)
                    print(args.out)
                else:
                    print(json.dumps(result, ensure_ascii=False))
                if args.action == "benchmark-evidence-check":
                    return 0 if result["slots"] and all(item["eligible"] for item in result["slots"].values()) else 1
        elif args.action == "benchmark-report":
            from .scoring import render_score, score_runs
            data = score_runs(args.runs, snapshot=args.review_snapshot, audit_snapshot=args.audit_snapshot,
                              audit_snapshots=read_json(args.audit_snapshots) if args.audit_snapshots else None)
            out = Path(args.out)
            out.mkdir(parents=True, exist_ok=False)
            write_json(out / "report.json", data)
            (out / "report.md").write_text(render_score(data), encoding="utf-8")
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
