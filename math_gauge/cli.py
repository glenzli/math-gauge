import argparse
import json
import subprocess
import sys
from pathlib import Path

from .catalog import Suite, read_json, write_json
from .benchmarks import BenchmarkProfile, build_plan, read_plan, write_plan
from .execution import check_lean, run
from .review import apply_reviews, report, templates


class _SuiteSources(argparse.Action):
    def __call__(self, parser, namespace, value, option_string=None):
        prior = getattr(namespace, self.dest, None)
        setattr(namespace, self.dest, [*(prior if isinstance(prior, list) else []), value])


def parser():
    p = argparse.ArgumentParser(
        prog="math-gauge",
        description="Weak-structure mathematical evaluation, public or private question suite.",
    )
    sub = p.add_subparsers(dest="action", required=True)
    c = sub.add_parser("suite-compose", help="Freeze evaluator-only identities of independently stored suites.")
    c.add_argument("--suite", action="append", required=True)
    c.add_argument("--id", required=True)
    c.add_argument("--version", required=True)
    c.add_argument("--out", required=True)
    for name in ("validate", "list", "prepare", "run", "check-lean"):
        c = sub.add_parser(name)
        c.add_argument("--suite", action=_SuiteSources, default="cases", help="Suite directory or manifest; repeat to compose independently rooted suites. Default: cases.")
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
    c.add_argument("--suite", action=_SuiteSources, default="cases")
    c.add_argument("--profile", default="protocol/benchmark-profile.json")
    c.add_argument("--target", action="append", dest="targets")
    c.add_argument("--runtime", help="Predeclared model, budget and adapter identity JSON.")
    c.add_argument("--out", required=True)
    c = sub.add_parser(
        "benchmark-export",
        help="Export a standalone external harness bundle and separate evaluator plan; no model calls.",
    )
    c.add_argument("--suite", action=_SuiteSources, default="cases")
    c.add_argument("--profile", help="Profile for a new plan; defaults to protocol/benchmark-profile.json.")
    c.add_argument("--target", action="append", dest="targets")
    g = c.add_mutually_exclusive_group()
    g.add_argument("--plan", help="Existing evaluator-only frozen plan.")
    g.add_argument("--runtime", help="Predeclared runtime JSON for a new plan; omitted means preparation only.")
    c.add_argument("--out", required=True, help="New standalone bundle directory.")
    c.add_argument("--evaluator-out", help="Separate new evaluator directory; defaults to <out>.evaluator.")
    c = sub.add_parser("benchmark-export-check", help="Read-only validation of an external harness bundle.")
    c.add_argument("--bundle", required=True)
    c.add_argument("--plan", help="Also bind the bundle to this evaluator-only plan.")
    c.add_argument("--suite", action=_SuiteSources, help="Bind to this suite; repeat for a composition.")
    c = sub.add_parser("benchmark-import", help="Import existing external responses into shared review evidence; no model calls.")
    c.add_argument("--bundle", help="Legacy immutable bundle/run directory; omit for a portable answers ZIP.")
    c.add_argument("--input", required=True, help="One portable answers ZIP, or legacy submission JSON with --bundle.")
    c.add_argument("--plan", required=True)
    c.add_argument("--suite", action=_SuiteSources, default="cases")
    c.add_argument("--out", required=True, help="New local run directory.")
    c = sub.add_parser("benchmark-run", help="Explicitly execute one frozen plan projection.")
    c.add_argument("--suite", action=_SuiteSources, default="cases")
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
    c.add_argument("--run", action="append", dest="runs", default=[],
                   help="Existing reliability source run; repeat as needed. Answer-review-only composition may omit this.")
    c.add_argument("--out", required=True)
    c.add_argument("--composition-plan", help="Explicit evaluator plan for a posthoc cross-plan development analysis; does not execute candidates.")
    c.add_argument("--model-aliases", help="Explicit source-label to target-label declarations for composition; does not verify backend identity.")
    c.add_argument("--composition-budget-policy", choices=("require_matching", "retain_source_budgets"), default="require_matching")
    c.add_argument("--frozen-source-reports", help="Explicit per-run trusted report and review-snapshot SHA-256 references for historical composition.")
    c.add_argument("--answer-review-sources", help="JSON array binding existing ordinary native answer runs to attributed post-observation dimension reviews.")
    c.add_argument("--suite", action=_SuiteSources, default="cases", help="Trusted target suite for answer-review rescoring; repeat to compose suites.")
    c.add_argument("--review-snapshot", type=int, help="Use this retained version in each supplied run.")
    g = c.add_mutually_exclusive_group()
    g.add_argument("--audit-snapshot", help="Retained audit SHA-256; requires exactly one --run.")
    g.add_argument("--audit-snapshots", help="JSON file mapping every resolved --run root to its retained audit SHA-256.")
    return p


def main(argv=None):
    args = parser().parse_args(argv)
    try:
        if args.action in {"validate", "list", "prepare", "run", "check-lean"}:
            suite = Suite.load(args.suite or ["cases"])
        if args.action == "suite-compose":
            import os
            suite = Suite.combine([Suite.load(path) for path in args.suite], suite_id=args.id, version=args.version)
            out = Path(args.out).resolve()
            out.parent.mkdir(parents=True, exist_ok=True)
            value = {"schema": "math-gauge.suite-composition/v1", "id": args.id, "version": args.version,
                     "suites": [{"path": os.path.relpath(member.manifest_path, out.parent),
                                 "id": member.metadata["id"], "version": member.metadata["version"],
                                 "sha256": member.sha256} for member in suite.members]}
            with out.open("x", encoding="utf-8") as stream:
                json.dump(value, stream, ensure_ascii=False, indent=2)
                stream.write("\n")
            print(json.dumps({"composition": str(out), "cases": len(suite.cases), "suite_sha256": suite.sha256}))
        elif args.action == "validate":
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
            suite = Suite.load(args.suite or ["cases"])
            profile = BenchmarkProfile.load(args.profile, suite)
            result = build_plan(profile, suite, args.targets,
                                runtime=read_json(args.runtime) if args.runtime else None)
            write_plan(args.out, result)
            print(json.dumps({"plan": args.out, "plan_sha256": result["plan_sha256"],
                              "planned": result["planned"], "candidate_calls": 0}))
        elif args.action == "benchmark-export":
            from .harness import export_harness_bundle
            if args.plan and args.profile:
                raise ValueError("--profile cannot change an existing --plan")
            suite = Suite.load(args.suite or ["cases"])
            plan = (read_plan(args.plan) if args.plan else build_plan(
                BenchmarkProfile.load(args.profile or "protocol/benchmark-profile.json", suite),
                suite, args.targets,
                runtime=read_json(args.runtime) if args.runtime else None))
            result = export_harness_bundle(
                plan, suite, args.out, evaluator_destination=args.evaluator_out,
                targets=args.targets)
            evaluator_root = Path(args.evaluator_out) if args.evaluator_out else Path(str(args.out) + ".evaluator")
            print(json.dumps({"bundle": args.out,
                              "evaluator_plan": str(evaluator_root / "plan.json"),
                              "bundle_sha256": result["bundle_sha256"],
                              "plan_sha256": result["plan_sha256"],
                              "planned": result["planned"],
                              "exported_slots": result["exported_slots"],
                              "runtime_frozen": result["runtime_frozen"],
                              "preparation_only": result["preparation_only"],
                              "candidate_calls": 0}))
        elif args.action == "benchmark-export-check":
            from .harness import DATASET_SCHEMA, SIMPLE_DATASET_SCHEMA, RUN_SCHEMA, inspect_harness_bundle
            result = inspect_harness_bundle(
                args.bundle, plan=read_plan(args.plan) if args.plan else None,
                suite=Suite.load(args.suite or ["cases"]) if args.suite else None)
            if result["schema"] in {DATASET_SCHEMA, SIMPLE_DATASET_SCHEMA, RUN_SCHEMA}:
                summary = {"bundle": args.bundle, "schema": result["schema"],
                           "dataset_sha256": result["dataset_sha256"],
                           "base_plan_sha256": result["base_plan_sha256"],
                           "planned": result["planned"], "candidate_calls": 0,
                           "runtime_frozen": result["schema"] == RUN_SCHEMA,
                           "preparation_only": result["schema"] in {DATASET_SCHEMA, SIMPLE_DATASET_SCHEMA}}
                if result["schema"] == RUN_SCHEMA:
                    summary["run_sha256"] = result["run_sha256"]
                    summary["runtime_sha256"] = result["runtime_sha256"]
                print(json.dumps(summary))
                return 0
            print(json.dumps({"bundle": args.bundle,
                              "bundle_sha256": result["bundle_sha256"],
                              "plan_sha256": result["plan_sha256"],
                              "planned": result["planned"],
                              "exported_slots": result["exported_slots"],
                              "runtime_frozen": result["runtime_frozen"],
                              "preparation_only": result["preparation_only"],
                              "candidate_calls": 0}))
        elif args.action == "benchmark-import":
            from .harness_import import import_answer_archive, import_harness_submission
            suite = Suite.load(args.suite or ["cases"])
            result = (import_harness_submission(args.bundle, args.input, read_plan(args.plan), suite, args.out)
                      if args.bundle else import_answer_archive(args.input, read_json(args.plan), suite, args.out))
            print(json.dumps({"run": args.out, "plan_sha256": result["plan_sha256"],
                              "candidate_calls": 0}))
        elif args.action == "benchmark-run":
            from .reliability import execute_reliability_run
            command = json.loads(args.command_json) if args.command_json else None
            if command is not None and (not isinstance(command, list) or not command
                                        or not all(isinstance(x, str) for x in command)):
                raise ValueError("--command-json must be a nonempty argv array")
            result = execute_reliability_run(read_plan(args.plan), Suite.load(args.suite or ["cases"]),
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
            from .scoring import render_score, score_composed_runs, score_runs
            if args.composition_plan:
                if args.audit_snapshot and len(args.runs) != 1:
                    raise ValueError("A single audit snapshot requires one source run")
                audits = read_json(args.audit_snapshots) if args.audit_snapshots else {}
                snapshots = {str(Path(root).resolve()): {
                    **({"snapshot": args.review_snapshot} if args.review_snapshot is not None else {}),
                    **({"audit_snapshot": audits.get(str(Path(root).resolve()), args.audit_snapshot)}
                       if audits.get(str(Path(root).resolve()), args.audit_snapshot) is not None else {})}
                    for root in args.runs}
                data = score_composed_runs(read_plan(args.composition_plan), args.runs, snapshots=snapshots,
                                          model_aliases=read_json(args.model_aliases) if args.model_aliases else None,
                                          budget_policy=args.composition_budget_policy,
                                          frozen_reports=read_json(args.frozen_source_reports) if args.frozen_source_reports else None,
                                          answer_review_sources=read_json(args.answer_review_sources) if args.answer_review_sources else (),
                                          suite=Suite.load(args.suite) if args.answer_review_sources else None)
            else:
                if args.model_aliases or args.frozen_source_reports or args.answer_review_sources:
                    raise ValueError("Model aliases and frozen score references require an explicit composition plan")
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
