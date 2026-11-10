#!/usr/bin/env python3
"""Recompute current classified scores from retained evidence, without model calls."""
import argparse
import copy
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from math_gauge.records import descriptor, evidence_bytes, load_retry_inputs, load_theorem_extension_inputs, load_background_check_inputs, load_written_argument_inputs, load_written_replacement_inputs, load_manuscript_completion_inputs, load_claim_review, project_assessment_score, project_public_task_view, public_assessment_case_ids, validate_record, selected_cli_records, selected_paper_records
from math_gauge.scoring import score_assessment_record_inputs
from math_gauge.attempt_conditions import load_sources as load_attempt_sources
from math_gauge.paper_observations import retain_scores as retain_paper_scores, check_record as check_paper_record
from math_gauge import submission_evidence
from math_gauge.records import rebind_content_rates


def load(path):
    return json.loads(Path(path).read_bytes())


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def write(path, value):
    Path(path).write_text(json.dumps(value, ensure_ascii=False, indent=2, allow_nan=False) + "\n", encoding="utf-8")


def retain(private_root, *, public_root=ROOT):
    public_root, private_root = Path(public_root).resolve(), Path(private_root).resolve()
    assessment = load(public_root / "protocol/scoring-policy.json")
    strict = load(public_root / "protocol/strict-scoring-policy.json")
    capability = load(public_root / "protocol/capability-scoring-policy.json")
    claim_policy = load(public_root / "protocol/claim-penalty-policy.json")
    for name in ("capability-scoring-policy.json", "score-modes.json", "claim-penalty-policy.json", "submission-scoring-policy.json"):
        (private_root / "protocol" / name).write_bytes((public_root / "protocol" / name).read_bytes())
    totals = {}
    for model, folder in selected_cli_records(public_root):
        relative = folder.relative_to(public_root)
        public, private = public_root / relative, private_root / relative
        validate_record(public, validate_scores=False)
        validate_record(private, formalization_root=public, validate_scores=False)
        record, private_record = load(public / "record.json"), load(private / "record.json")
        research = load_theorem_extension_inputs(private, private_record, policy=assessment.get("theorem_extension"))
        background = load_background_check_inputs(private,private_record,policy=assessment.get("background_check"))
        written = load_written_argument_inputs(private, private_record, policy=assessment.get("written_argument_additions"))
        replacement = load_written_replacement_inputs(private, private_record, policy=assessment.get("written_argument_replacements"))
        manuscript = load_manuscript_completion_inputs(private, private_record, policy=assessment.get("manuscript_completion"))
        original = load(private / "scoring-inputs.json")
        retry = load_retry_inputs(private, private_record, public_root=public, validate_results=False)
        old_retry = load(public / "retry-combined-aggregate.json") if (public / "retry-combined-aggregate.json").exists() else {}
        review_path = private / "reviews/alignment.json"
        if not review_path.exists():
            review_path = private / "alignment-review.json"
        review, source_policy = load(review_path), load(private / "scoring-policy.json")
        engineering = load(public / "reviews/formalization.json")
        for filename, source in (("assessment-policy.json", "scoring-policy.json"),
                                 ("strict-scoring-policy.json", "strict-scoring-policy.json"),
                                 ("capability-scoring-policy.json", "capability-scoring-policy.json"),
                                 ("claim-penalty-policy.json", "claim-penalty-policy.json"),
                                 ("submission-scoring-policy.json", "submission-scoring-policy.json"),
                                 ("score-modes.json", "score-modes.json")):
            (public / filename).write_bytes((public_root / "protocol" / source).read_bytes())
        for target in (record, private_record):
            target["assessment_policy"] = descriptor(public, public / "assessment-policy.json")
            target["strict_scoring_policy"] = descriptor(public, public / "strict-scoring-policy.json")
            target["capability_scoring_policy"] = descriptor(public, public / "capability-scoring-policy.json")
            target["score_mode_catalog"] = descriptor(public, public / "score-modes.json")
            target["default_score_mode"] = "partial"
            target["claim_penalty_policy"] = descriptor(public, public / "claim-penalty-policy.json")
            if assessment['version']=='0.9.0':
                target['submission_policy'] = descriptor(public,public/'submission-scoring-policy.json')
            for key in ("capability_results", "assessment_results", "strict_results"):
                target[key] = {}
        private_record["claim_review"] = descriptor(private, private / private_record.get("claim_review", {"path": "claim-review.json"})["path"])
        record["claim_review"] = descriptor(public, public / record.get("claim_review", {"path": "claim-review-public.json"})["path"])
        record["claim_review_source_sha256"] = private_record["claim_review"]["sha256"]
        totals[model] = {}
        for condition in ("single_attempt", "nonlogical_retry_3"):
            selected_sources = load_attempt_sources(private, private_record, condition, public_root=public)
            uses_retry = condition == "nonlogical_retry_3" and retry is not None
            inputs = selected_sources['inputs'] if selected_sources else retry if uses_retry else original
            selected_review = selected_sources['alignment'] if selected_sources else review
            selected_engineering = selected_sources['engineering'] if selected_sources else engineering
            selected_manuscript = selected_sources['manuscript'] if selected_sources else manuscript
            selected_research = selected_sources.get('theorem_extension_inputs', research) if selected_sources else research
            selected_background = selected_sources.get('background_check_inputs', background) if selected_sources else background
            selected_engineering_descriptor = (selected_sources['bindings']['formalization_review']
                                               if selected_sources else record['formalization_review'])
            claim_review = load_claim_review(private, private_record, condition, public_root=public)
            retry_summary = (copy.deepcopy(old_retry["retry_summary"]) if uses_retry else {
                "slots_with_reruns": 0, "source": "original_records_reused_no_new_retry_evidence",
                "all_original_attempts_independently_certified": False})
            if selected_sources:
                retry_summary = copy.deepcopy(old_retry.get('retry_summary', retry_summary))
            totals[model][condition] = {}
            for mode in ("capability", "partial", "strict"):
                score = score_assessment_record_inputs(inputs, selected_review, source_policy,
                    formalization_review=selected_engineering, assessment_policy=assessment, strict_policy=strict, mode=mode,
                    theorem_extension_inputs=selected_research, background_check_inputs=selected_background,
                    claim_review=claim_review, claim_policy=claim_policy,
                    capability_policy=capability if mode == "capability" else None, written_argument_inputs=written,
                    written_replacement_inputs=replacement, manuscript_completion_inputs=selected_manuscript,
                    submission_review=submission_evidence.load_condition(private,private_record,condition),
                    submission_policy=submission_evidence.load_policy(private,private_record))
                score.update(attempt_condition=condition, retry_summary=retry_summary,
                    scope="combined-evaluator", source_math_policy_version=source_policy["version"],
                    engineering_review_sha256=selected_engineering_descriptor['sha256'],
                    source_bindings={
                        "scoring_inputs_sha256": digest(private / ("retry-scoring-inputs.json" if uses_retry else "scoring-inputs.json")),
                        "source_math_policy_sha256": digest(private / "scoring-policy.json"),
                        "alignment_review_sha256": digest(review_path),
                        "engineering_review_sha256": selected_engineering_descriptor['sha256'],
                        "assessment_policy_sha256": digest(public / "assessment-policy.json"),
                        "strict_policy_sha256": digest(public / "strict-scoring-policy.json")})
                if selected_sources:
                    bundle = selected_sources['bindings']
                    score['source_bindings'].update(scoring_inputs_sha256=bundle['scoring_inputs']['sha256'],
                        alignment_review_sha256=bundle['alignment_review']['sha256'])
                score["source_bindings"].update(claim_review_sha256=private_record["claim_review"]["sha256"],
                    claim_penalty_policy_sha256=digest(public / "claim-penalty-policy.json"))
                if research is not None:
                    score["source_bindings"]["theorem_extension_inputs_sha256"] = (selected_sources['bindings']['theorem_extension_inputs']['sha256']
                        if selected_sources and 'theorem_extension_inputs' in selected_sources['bindings']
                        else digest(private / private_record["theorem_extension_inputs"]["path"]))
                if background is not None:
                    score["source_bindings"]["background_check_inputs_sha256"] = (selected_sources['bindings']['background_check_inputs']['sha256']
                        if selected_sources and 'background_check_inputs' in selected_sources['bindings']
                        else digest(private/private_record["background_check_inputs"]["path"]))
                if written is not None:
                    score["source_bindings"]["written_argument_inputs_sha256"] = private_record["written_argument_inputs"]["sha256"]
                elif original["plan"]["profile"]["data"].get("schema") == "math-gauge.benchmark-profile/v6":
                    score["source_bindings"]["current_written_scoring_inputs_sha256"] = digest(private / "scoring-inputs.json")
                if replacement is not None:
                    score["source_bindings"]["written_replacement_inputs_sha256"] = private_record["written_replacement_inputs"]["sha256"]
                elif (original["plan"]["profile"]["data"].get("schema") == "math-gauge.benchmark-profile/v6"
                      and record.get('written_replacement_evidence') is not None):
                    # Fresh v6 plans already contain PS001. Its public source
                    # projection binds those direct inputs, not a supplement.
                    projection=load(public/record['written_replacement_evidence']['path'])
                    direct_hash=digest(private/'scoring-inputs.json')
                    if projection['source_inputs_sha256']!=direct_hash:
                        raise ValueError('Direct written replacement lost its original source input')
                    score['source_bindings']['written_replacement_inputs_sha256']=direct_hash
                if selected_manuscript is not None:
                    score["source_bindings"]["manuscript_completion_inputs_sha256"] = (
                        selected_sources['bindings']['manuscript_completion_inputs']['sha256']
                        if selected_sources else private_record["manuscript_completion_inputs"]["sha256"])
                if mode == "capability":
                    score["source_bindings"]["capability_policy_sha256"] = digest(public / "capability-scoring-policy.json")
                if assessment['version']=='0.9.0':
                    score['source_bindings'].update(
                        submission_evidence_sha256=private_record['submission_evidence']['sha256'],
                        submission_policy_sha256=private_record['submission_policy']['sha256'])
                if uses_retry:
                    admission = load(public / record["retry_admission"]["path"])
                    score.update(retry_policy_sha256=admission["policy"]["sha256"],
                                 retry_admission_sha256=record["retry_admission"]["sha256"])
                is_retry = condition == "nonlogical_retry_3"
                private_name = {"capability": ("capability-result.json", "capability-retry-result.json"),
                    "partial": ("result.json", "retry-result.json"),
                    "strict": ("strict-result.json", "strict-retry-result.json")}[mode][is_retry]
                public_name = {"capability": ("capability-combined-aggregate.json", "capability-retry-combined-aggregate.json"),
                    "partial": ("combined-aggregate.json", "retry-combined-aggregate.json"),
                    "strict": ("strict-combined-aggregate.json", "strict-retry-combined-aggregate.json")}[mode][is_retry]
                write(private / private_name, score)
                aggregate = project_assessment_score(score)
                aggregate["source_bindings"]["private_report_sha256"] = digest(private / private_name)
                write(public / public_name, aggregate)
                key = {"capability": "capability_results", "partial": "assessment_results", "strict": "strict_results"}[mode]
                record[key][condition] = descriptor(public, public / public_name)
                private_record[key][condition] = descriptor(private, private / private_name)
                totals[model][condition][mode] = score["metrics"]["earned"].get("confirmed", score["metrics"]["earned"]["exact"])
        # Public-only score views are retired; original questions, answers,
        # engineering judgments and frozen execution inputs are untouched.
        for filename in ("result.json", "retry-result.json"):
            path = public / filename
            if path.exists():
                path.unlink()
        record.pop("retry_result", None)
        if record.get("retry_admission"):
            record["retry_combined_aggregate"] = descriptor(public, public / "retry-combined-aggregate.json")
            private_record["retry_result"] = descriptor(private, private / "retry-result.json")
        for folder, target in ((public, record), (private, private_record)):
            target["evidence"] = [descriptor(folder, folder / item["path"])
                if item["path"] in {"result.json", "combined-aggregate.json", "retry-result.json", "retry-combined-aggregate.json"}
                else item for item in target["evidence"]
                if not (folder == public and item["path"] in {"result.json", "retry-result.json"})]
            write(folder / "record.json", target)
    for model, public in selected_paper_records(public_root):
        private = private_root / public.relative_to(public_root)
        retained = retain_paper_scores(private, public)
        totals[model] = {condition: {mode: retained['earned'][mode][condition]
                                   for mode in ('capability', 'partial', 'strict')}
                         for condition in ('single_attempt', 'nonlogical_retry_3')}
    if assessment['version']=='0.9.0':
        totals.update(retain_native_scores(private_root,public_root=public_root)['totals'])
    export_public_tasks(private_root, public_root=public_root)
    if assessment['version']=='0.9.0':
        # The public task attachment is part of record.json. Bind auxiliary
        # observations only after that final record identity has been written.
        for _,public in selected_cli_records(public_root):
            rebind_content_rates(private_root/public.relative_to(public_root),public,
                                 private_root=private_root,public_root=public_root)
    active = sum(c["weight"] for c in assessment["subcategories"] if c["status"] == "active")
    return {"benchmark_version": "0.6.0", "scoring_version": assessment["version"], "strict_version": strict["version"],
            "capability_version": capability["version"], "default_score_mode": "partial",
            "capacity": {"active": active, "under_construction": 100-active, "total": 100}, "totals": totals,
            "candidate_calls": 0, "sealed_engineering_compilations": 0}


def export_public_tasks(private_root, *, public_root=ROOT):
    """Publish only selected public task judgments from the retained six reports."""
    public_root, private_root = Path(public_root), Path(private_root)
    published = []
    for model, folder in selected_cli_records(public_root):
        relative = folder.relative_to(public_root)
        public, private = public_root / relative, private_root / relative
        record, source_record = load(public / "record.json"), load(private / "record.json")
        policy = json.loads(evidence_bytes(public, record["assessment_policy"]))
        ids = public_assessment_case_ids(policy)
        data = {"schema": "math-gauge.public-task-scores/v1", "benchmark_version": "0.6.0",
                "model_label": record["model"]["requested_label"], "public_case_ids": ids,
                "human_review": "pending", "formal_comparison_eligible": False, "views": {}}
        for mode, key in (("capability", "capability_results"), ("partial", "assessment_results"), ("strict", "strict_results")):
            data["views"][mode] = {}
            for condition, item in source_record[key].items():
                raw = evidence_bytes(private, item)
                score = json.loads(raw)
                aggregate = json.loads(evidence_bytes(public, record[key][condition]))
                source_hash = hashlib.sha256(raw).hexdigest()
                if (aggregate["source_bindings"]["private_report_sha256"] != source_hash
                        or score["score_mode"] != mode or score["attempt_condition"] != condition):
                    raise ValueError("Public task projection needs matching retained reports")
                data["views"][mode][condition] = project_public_task_view(score, ids, source_hash)
        target = public / "public-task-scores.json"
        write(target, data)
        record["evidence"] = [r for r in record["evidence"] if r["path"] != target.name] + [descriptor(public, target)]
        write(public / "record.json", record)
        published.append({"model": model, "public_tasks": len(ids)})
    for model, public in selected_paper_records(public_root):
        check_paper_record(private_root / public.relative_to(public_root), public_folder=public)
        published.append({'model': model, 'public_tasks': 25})
    return {"published": published, "candidate_calls": 0, "scores_recomputed": False}


def retain_native_scores(private_root, *, public_root=ROOT):
    """Derive native views without converting their retained source into CLI evidence."""
    from math_gauge.native_observations import project_score
    from math_gauge.scoring import score_native_observation
    public_root,private_root=Path(public_root),Path(private_root)
    selected=[];totals={}
    for path in sorted((public_root/'results/v0.6.0').glob('*/*/native-observation.json')):
        public=path.parent;private=private_root/public.relative_to(public_root)
        record,source=load(path),load(private/'native-observation.json')
        data=load(private/source['mathematical_inputs']['path'])
        policies=[load(public_root/'protocol'/name) for name in ('scoring-policy.json',
            'strict-scoring-policy.json','capability-scoring-policy.json','claim-penalty-policy.json')]
        for filename,original in (('assessment-policy.json','scoring-policy.json'),
                ('strict-scoring-policy.json','strict-scoring-policy.json'),
                ('capability-scoring-policy.json','capability-scoring-policy.json'),
                ('claim-penalty-policy.json','claim-penalty-policy.json')):
            for folder in (public,private):
                (folder/filename).write_bytes((public_root/'protocol'/original).read_bytes())
        record['assessment_policy']=descriptor(public,public/'assessment-policy.json')
        totals[record['model_id']]={c:{} for c in ('single_attempt','nonlogical_retry_3')}
        task_views=dict(schema='math-gauge.public-task-scores/v1',benchmark_version='0.6.0',
            model_label=data['model_label'],public_case_ids=record['public_case_ids'],human_review='pending',
            formal_comparison_eligible=False,views={})
        for mode,field in (('capability','capability_results'),('partial','assessment_results'),('strict','strict_results')):
            task_views['views'][mode]={}
            for condition in ('single_attempt','nonlogical_retry_3'):
                full=score_native_observation(data,*policies,mode=mode,
                    submission_review=submission_evidence.load_condition(private,source,condition),
                    submission_policy=submission_evidence.load_policy(private,source))
                full.update(attempt_condition=condition,
                    retry_summary=dict(slots_with_reruns=0,effective_attempts=policies[0]['scope']['initial_slots']),
                    source_bindings=dict(mathematical_input_sha256=source['mathematical_inputs']['sha256'],
                        source_plan_sha256=source['plan']['sha256'],source_run_sha256=source['run']['sha256']))
                totals[record['model_id']][condition][mode]=full['metrics']['earned'].get('confirmed',full['metrics']['earned']['exact'])
                if source.get('source_supplements'):
                    full['source_bindings']['source_supplements_sha256']=source['source_supplements']['sha256']
                if policies[0]['version']=='0.9.0':
                    full['source_bindings'].update(submission_evidence_sha256=source['submission_evidence']['sha256'],
                        submission_policy_sha256=source['submission_policy']['sha256'])
                name=mode+('-retry' if condition=='nonlogical_retry_3' else '')+'-result.json'
                write(private/name,full)
                aggregate=project_score(full)
                aggregate['source_bindings']['private_report_sha256']=digest(private/name)
                target=public/record[field][condition]['path'];write(target,aggregate)
                record[field][condition]=descriptor(public,target)
                task_views['views'][mode][condition]=project_public_task_view(full,
                    record['public_case_ids'],digest(private/name))
        target=public/record['public_task_scores']['path'];write(target,task_views)
        record['public_task_scores']=descriptor(public,target)
        write(path,record)
        source['public_record_sha256']=digest(path)
        write(private/'native-observation.json',source)
        if policies[0]['version']=='0.9.0':
            rebind_content_rates(private,public,private_root=private_root,public_root=public_root)
        selected.append(record['model_id'])
    return dict(models=selected,totals=totals,candidate_calls=0)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--private-root", type=Path, required=True)
    parser.add_argument("--project-public-tasks-only", action="store_true", help="Project retained public task judgments without rescoring or changing private records.")
    args = parser.parse_args()
    result = export_public_tasks(args.private_root) if args.project_public_tasks_only else retain(args.private_root)
    print(json.dumps(result, ensure_ascii=False))


if __name__ == "__main__":
    main()
