#!/usr/bin/env python3
"""Verify current archive integrity and recompute all three classified score modes."""
import argparse
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from math_gauge.records import (load_assessment_results, load_retry_inputs, load_theorem_extension_inputs, load_background_check_inputs, load_written_argument_inputs, load_written_replacement_inputs, load_manuscript_completion_inputs, load_claim_review, project_assessment_score,
                                validate_record, load_public_task_scores, project_public_task_view,
                                selected_cli_records, selected_paper_records)
from math_gauge.scoring import score_assessment_record_inputs
from math_gauge.attempt_conditions import load_sources as load_attempt_sources
from math_gauge.paper_observations import SCHEMA as PAPER_SCHEMA, check_record as check_paper_record
from math_gauge import submission_evidence
from math_gauge.result_corrections import load_selected as load_correction, verify_private as verify_private_correction


def load(path):
    return json.loads(Path(path).read_bytes())


def check(root=ROOT, *, public_root=None):
    root = Path(root).resolve()
    archives = []
    scoring_version = None
    selection_root = Path(public_root).resolve() if public_root is not None else root
    selected = selected_cli_records(selection_root) + selected_paper_records(selection_root)
    paths = [root / folder.relative_to(selection_root) / "record.json" for _, folder in selected]
    for path in sorted(paths):
        folder, record = path.parent, load(path)
        if record.get('schema') == PAPER_SCHEMA:
            public = Path(public_root).resolve() / folder.relative_to(root) if public_root is not None else None
            archives.append(check_paper_record(folder, public_folder=public))
            scoring_version = load(folder / record['assessment_policy']['path'])['version']
            continue
        external = record.get("formalization_evidence_location") == "public_archive"
        if external and public_root is None:
            raise ValueError("Private archives require --public-root for shared evidence")
        public = Path(public_root).resolve() / folder.relative_to(root) if external else folder
        status = validate_record(folder, formalization_root=public if external else None)
        views = {mode: load_assessment_results(folder, record, mode=mode,
                    public_root=public if external else None) for mode in ("capability", "partial", "strict")}
        if any(value is None for value in views.values()):
            raise ValueError("Current archives require capability, reliable and Strict views")
        if external:
            inputs = load(folder / "scoring-inputs.json")
            retry = load_retry_inputs(folder, record, public_root=public)
            review_path = folder / "reviews/alignment.json"
            if not review_path.exists():
                review_path = folder / "alignment-review.json"
            review, source_policy = load(review_path), load(folder / "scoring-policy.json")
            assessment, strict = load(public / "assessment-policy.json"), load(public / "strict-scoring-policy.json")
            capability = load(public / "capability-scoring-policy.json")
            claim_policy = load(public / "claim-penalty-policy.json") if assessment.get("version") in {"0.8.0", "0.9.0"} else None
            research = load_theorem_extension_inputs(folder, record, policy=assessment.get("theorem_extension"))
            background = load_background_check_inputs(folder,record,policy=assessment.get("background_check"))
            written = load_written_argument_inputs(folder,record,policy=assessment.get("written_argument_additions"))
            replacement = load_written_replacement_inputs(folder,record,policy=assessment.get("written_argument_replacements"))
            manuscript = load_manuscript_completion_inputs(folder,record,policy=assessment.get("manuscript_completion"))
            engineering = load(public / "reviews/formalization.json")
            public_record = load(public / "record.json")
            public_tasks = load_public_task_scores(public, public_record)
            for mode, conditions in views.items():
                for condition, score in conditions.items():
                    selected_sources = load_attempt_sources(folder, record, condition, public_root=public)
                    selected = (selected_sources['inputs'] if selected_sources else
                                retry if condition == "nonlogical_retry_3" and retry is not None else inputs)
                    selected_review = selected_sources['alignment'] if selected_sources else review
                    selected_engineering = selected_sources['engineering'] if selected_sources else engineering
                    selected_manuscript = selected_sources['manuscript'] if selected_sources else manuscript
                    selected_research = selected_sources.get('theorem_extension_inputs', research) if selected_sources else research
                    selected_background = selected_sources.get('background_check_inputs', background) if selected_sources else background
                    claims = load_claim_review(folder, record, condition, public_root=public) if claim_policy else None
                    derived = score_assessment_record_inputs(selected, selected_review, source_policy,
                        formalization_review=selected_engineering, assessment_policy=assessment,
                        strict_policy=strict, mode=mode, theorem_extension_inputs=selected_research, background_check_inputs=selected_background, written_argument_inputs=written,
                        written_replacement_inputs=replacement, manuscript_completion_inputs=selected_manuscript,
                        claim_review=claims, claim_policy=claim_policy,
                        submission_review=submission_evidence.load_condition(folder,record,condition),
                        submission_policy=submission_evidence.load_policy(folder,record),
                        capability_policy=capability if mode == "capability" else None)
                    for key, value in derived.items():
                        if score.get(key) != value:
                            raise ValueError(f"Archived current score differs from source evidence: {mode}/{key}")
                    group = {"capability": "capability_results", "partial": "assessment_results", "strict": "strict_results"}[mode]
                    aggregate = load(public / public_record[group][condition]["path"])
                    projected = project_assessment_score(score)
                    projected["source_bindings"]["private_report_sha256"] = hashlib.sha256(
                        (folder / record[group][condition]["path"]).read_bytes()).hexdigest()
                    if aggregate != projected:
                        raise ValueError("Public current aggregate differs from the private shared-scorer result")
                    if public_tasks is not None:
                        task_view = project_public_task_view(score, public_tasks["public_case_ids"],
                            projected["source_bindings"]["private_report_sha256"])
                        if public_tasks["views"][mode][condition] != task_view:
                            raise ValueError("Public task judgments differ from the private shared-scorer result")
        original_earned = {mode: {condition: score["metrics"]["earned"]["exact"]
            for condition, score in conditions.items()} for mode, conditions in views.items()}
        model_id = folder.parent.name
        correction = load_correction(selection_root, model_id, public,
                                     record=public_record if external else record)
        if correction is not None:
            corrected = (verify_private_correction(root, selection_root, model_id, folder, correction)
                         if external else correction['_scores'])
            for mode, score in corrected.items():
                views[mode]['nonlogical_retry_3'] = score
            status['archived_earned'] = original_earned
            status['harness_source_correction'] = {
                'affected_cases': correction['affected_cases'], 'original_native_status': 'ERROR',
                'new_candidate_calls': 0, 'scoring_rules_changed': False}
        status["earned"] = {mode: {condition: score["metrics"]["earned"]["exact"]
            for condition, score in conditions.items()} for mode, conditions in views.items()}
        status["capacity"] = next(iter(views["partial"].values()))["capacity"]
        archives.append(status)
        scoring_version = next(iter(views['partial'].values()))['scoring_method_version']
    if not archives:
        raise ValueError("No current user-selected archives found")
    return {"passed": True, "benchmark_version": "0.6.0", "scoring_version": scoring_version,
            "strict_version": "0.2.0", "archives": archives, "candidate_calls": 0,
            "sealed_engineering_compilations": 0}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=["check"])
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--public-root", type=Path)
    args = parser.parse_args()
    try:
        print(json.dumps(check(args.root, public_root=args.public_root), ensure_ascii=False))
    except (ValueError, KeyError, OSError) as error:
        parser.exit(1, str(error) + "\n")


if __name__ == "__main__":
    main()
