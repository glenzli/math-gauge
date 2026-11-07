"""Source-bound final records: raw self-assessment evidence and finite trajectories.

This owner collects and validates records. Mathematical aggregation remains in
scoring.py; execution remains in execution.py and the existing harness.
"""

import hashlib
import json
import copy
from pathlib import Path, PurePosixPath

SCHEMA = "math-gauge.result-record/v1"
ASSESSMENTS = {"complete", "incomplete", "uncertain", "not_stated", "not_requested", "unresolved"}


def project_metrics(metrics):
    """Publish numeric aggregates and anonymous coverage, never slot diagnostics."""
    fields = ("exact", "lower", "upper", "complete", "coverage", "confirmed")
    return {name: {**{key: copy.deepcopy(value[key]) for key in fields if key in value},
                   "formal_comparison_eligible": False} for name, value in metrics.items()}


def apply_retry_selection(baseline, ledger, rows, policy):
    """Select the first delivery after bounded operational failures, never best-of.

    This is an admission projection; scoring.py still owns all arithmetic.
    The original plan, other slots and original record rows remain unchanged.
    """
    if (policy.get("schema") != "math-gauge.nonlogical-retry-policy/v1"
            or policy.get("maximum_total_attempts_per_slot") != 3
            or policy.get("selection") != "first_completed_delivery"
            or policy.get("retry_on_mathematical_error") is not False):
        raise ValueError("Unknown bounded retry policy")
    allowed = {"max_output_tokens", "service_error", "execution_interrupted"}
    if set(policy.get("eligible_failure_reasons", [])) != allowed:
        raise ValueError("Retry policy cannot admit mathematical failures")
    if (ledger.get("schema") != "math-gauge.retry-attempts/v1"
            or ledger.get("formal_comparison_eligible") is not False
            or ledger.get("human_review") != "pending"):
        raise ValueError("Retry evidence cannot promote execution or human qualification")
    result = copy.deepcopy(baseline)
    original = {r["slot_id"]: r for r in baseline["slots"]}
    selected = {r["slot_id"]: r for r in result["slots"]}
    indexed = {r["id"]: r for r in rows}
    seen = set()
    for slot in ledger.get("slots", []):
        sid = slot.get("slot_id")
        if sid in seen or sid not in original:
            raise ValueError("Retry ledger repeats or invents a planned slot")
        seen.add(sid)
        attempts = slot.get("attempts", [])
        if not 1 <= len(attempts) <= 3:
            raise ValueError("Retry cap is three total attempts including the first")
        delivered = None
        previous = None
        for number, attempt in enumerate(attempts, 1):
            rid = attempt.get("record_id")
            row = indexed.get(rid)
            if (type(attempt.get("attempt")) is not int or attempt.get("attempt") != number or row is None
                    or row.get("case_id") != original[sid]["case_id"]
                    or number == 1 and rid != sid
                    or number > 1 and (row.get("kind") != "nonlogical_retry"
                                      or row.get("parent_id") != previous)):
                raise ValueError("Retry attempts must be contiguous and source-bound to their slot")
            if delivered is not None:
                raise ValueError("Cannot retry a completed answer, even if mathematically wrong")
            if row.get("response") is not None:
                if (attempt.get("outcome") != "completed_delivery"
                        or attempt.get("failure_reason") is not None):
                    raise ValueError("A delivered answer cannot be relabeled as a retryable failure")
                delivered = rid
            elif (attempt.get("outcome") != "no_final_delivery"
                  or attempt.get("failure_reason") not in allowed
                  or attempt.get("final_answer_bytes") != 0):
                raise ValueError("A retry requires an eligible failure with no final delivery")
            previous = rid
        if slot.get("selected_record_id") != delivered:
            raise ValueError("Retry selection must be the first completed delivery")
        if slot.get("conditions_evidence") not in {"native_verified", "operator_declared_unverified_details"}:
            raise ValueError("Retry conditions need explicit evidence and uncertainty")
        if delivered is None:
            if original[sid].get("completion", {}).get("exact") != 0 or original[sid].get("strict_pass") is not False:
                raise ValueError("Exhausted retries must preserve zero delivery credit")
            continue
        row, target = indexed[delivered], selected[sid]
        evaluation = row["evaluation"]
        target.update({key: copy.deepcopy(evaluation[key]) for key in (
            "completion", "strict_pass", "whole_math", "focus_math", "focus_verdict",
            "group_diagnostic", "review_sha256")})
        target.update(status="response_received_execution_unverified",
                      execution_status="external_response_execution_unverified", reason=None,
                      response_sha256=row["response"]["sha256"],
                      whole_strict={"state": "C" if evaluation["strict_pass"] else "I",
                                    "adjudicated": True, "reasons": []},
                      comparison_eligible=False,
                      delivery_failure_does_not_adjudicate_theorem_truth=False)
        target["retry_selection"] = {"condition": "nonlogical_retry_3", "record_id": delivered,
                                     "attempt": len(attempts), "total_attempts": len(attempts)}
    return result


def load_retry_inputs(root, record, *, public_root=None, validate_results=True):
    """Validate optional retry evidence and its exact, separately retained input."""
    if record.get("retry_admission") is None:
        return None
    root = Path(root).resolve()
    location = record.get("retry_admission_location", "local")
    if location not in {"local", "public_archive"} or location == "public_archive" and public_root is None:
        raise ValueError("Retry admission needs its explicitly selected public archive")
    evidence_root = Path(public_root).resolve() if location == "public_archive" else root
    manifest = json.loads(evidence_bytes(evidence_root, record["retry_admission"]))
    if manifest.get("schema") != "math-gauge.retry-admission/v1":
        raise ValueError("Unknown retry admission manifest")
    policy = json.loads(evidence_bytes(evidence_root, manifest["policy"]))
    ledger = json.loads(evidence_bytes(evidence_root, manifest["ledger"]))
    for source in ledger.get("evidence", []):
        evidence_bytes(evidence_root, source)
    source_record = (json.loads((evidence_root / "record.json").read_bytes())
                     if location == "public_archive" else record)
    if location == "public_archive":
        validate_record(evidence_root, validate_scores=False)
    indexed = {r["id"]: r for r in source_record["records"]}
    for slot in ledger.get("slots", []):
        if slot.get("selected_record_id") is None:
            continue
        row = indexed[slot["selected_record_id"]]
        review = json.loads(evidence_bytes(evidence_root, row["review"]))
        evaluation = row["evaluation"]
        if (review.get("source_response") != row["response"]
                or evaluation.get("review_sha256") != row["review"]["sha256"]
                or review.get("strict_pass") != evaluation.get("strict_pass")
                or any(evaluation["completion"].get(key) != review["points"] / review["total"]
                       for key in ("lower", "upper", "exact"))):
            raise ValueError("Retry judgment differs from its bound answer review")
    baseline = json.loads((root / "scoring-inputs.json").read_bytes())
    projected = apply_retry_selection(baseline, ledger, source_record["records"], policy)
    retained = json.loads(evidence_bytes(root, record["retry_scoring_inputs"]))
    if projected != retained:
        raise ValueError("Retry inputs differ from their deterministic source selection")
    for name in (("retry_result", "retry_combined_aggregate") if validate_results else ()):
        if name in record:
            result = json.loads(evidence_bytes(root, record[name]))
            if (result.get("attempt_condition") != "nonlogical_retry_3"
                    or result.get("retry_policy_sha256") != manifest["policy"]["sha256"]
                    or result.get("formal_comparison_eligible") is not False
                    or result.get("human_review") != "pending"):
                raise ValueError("Retry result identity or review status changed")
    return retained


def project_assessment_score(score):
    """Publish the hierarchy and numeric results, excluding private task evidence."""
    fields = ("benchmark_version", "scoring_method_version", "strict_method_version", "score_mode",
              "capability_method_version", "capability_policy_sha256",
              "claim_penalty_method_version", "claim_penalty_policy_sha256", "claim_penalties",
              "primary_metric", "model_label", "capacity", "group_capacity", "coverage", "whole_task_counts", "profile",
              "alignment_selfcheck", "strict_alignment_selfcheck", "lean_formalization_breakdown",
              "initial_answers_replaced", "attempt_condition", "retry_summary", "source_bindings",
              "source_math_policy_version", "engineering_review_sha256",
              "retry_policy_sha256", "retry_admission_sha256")
    result = {key: copy.deepcopy(score[key]) for key in fields if key in score}
    result.update(schema="math-gauge.assessment-score-aggregate/v1", scope="combined-aggregate-only",
                  private_case_count=score.get("coverage", {}).get("private_tasks", 3), metrics=project_metrics(score["metrics"]),
                  contributions=project_metrics(score["contributions"]), human_review="pending",
                  formal_comparison_eligible=False, new_candidate_calls=0)
    return result


def _validate_research_tool_evidence(root, row, execution, policy):
    """Keep historical no-tools evidence distinct from native local-tool answers."""
    from .execution_policy import LOCAL_TOOLS_TRACK
    track = row.get("execution_track")
    if track != LOCAL_TOOLS_TRACK:
        if policy.get("local_tools_allowed") is True or track not in {None, "math-gauge.no-tools/v1"} or execution.get("tool_events") != []:
            raise ValueError("Research answer does not bind the selected local-tool condition")
        return
    plan = json.loads(evidence_bytes(root, row["execution_plan"]))
    settings = json.loads(evidence_bytes(root, row["native_tool_settings"]))
    control = json.loads(evidence_bytes(root, row["native_capability_control"]))
    if (plan.get("local_tool_policy") != LOCAL_TOOLS_TRACK
            or plan.get("tool_network_access") is not False or plan.get("search_allowed") is not False
            or execution.get("argv") != plan.get("argv") or execution.get("cwd") != plan.get("cwd")
            or execution.get("requested_model") != plan.get("model")
            or execution.get("requested_effort") != plan.get("effort")
            or control.get("passed") is not True or control.get("mathematical_requests") != 0
            or not any(c.get("passed") is True and c.get("requested_model") == plan.get("model")
                       and c.get("requested_effort") == plan.get("effort") for c in control.get("results", []))):
        raise ValueError("Research local-tool permission lacks matching native plan and capability evidence")
    if plan.get("client") == "codex":
        allowed = {"command_execution", "file_change"}
        if (settings.get("web_search") != "disabled"
                or settings.get("permissions.isolated-cli.network.enabled") is not False
                or settings.get("features.shell_tool") is not True):
            raise ValueError("Research native command settings differ from local-tools/no-network")
    elif plan.get("client") == "agy":
        allowed = {"finish", "manage_task", "run_command", "command_status", "send_command_input", "view_file",
                   "write_to_file", "replace_file_content", "multi_replace_file_content",
                   "list_dir", "grep_search", "find_by_name", "read_file", "write_file"}
        if (settings.get("enableTerminalSandbox") is not True
                or settings.get("toolPermission") != "proceed-in-sandbox"
                or not {"read_url(*)", "execute_url(*)", "mcp(*)", "unsandboxed(*)"}.issubset(
                    settings.get("permissions", {}).get("deny", []))
                or execution.get("permission_mode") != plan.get("expected_permission_mode")):
            raise ValueError("Research native AGY settings differ from local-tools/no-network")
    else:
        raise ValueError("Unsupported native research tool client")
    if any(event.get("name") not in allowed for event in execution.get("tool_events", [])):
        raise ValueError("Research answer used a tool outside the bound local capabilities")


def load_theorem_extension_inputs(root, record, *, policy=None):
    """Bind adopted A1 judgments to original final text and native evidence."""
    if record.get("theorem_extension_inputs") is None:
        return None
    from .theorem_extension import validate_inputs
    data = json.loads(evidence_bytes(root, record["theorem_extension_inputs"]))
    selected_policy = data.get("policy") if policy is None else policy
    if data.get("policy") != selected_policy:
        raise ValueError("Research answers bind a different selected scoring contract")
    validate_inputs(data, selected_policy)
    cases = {case["case_id"]: case for case in data["case_index"]}
    for row in data["slots"]:
        if row["status"] == "not_run":
            continue
        if row["status"] == "delivery_failed":
            execution = json.loads(evidence_bytes(root, row["execution"]))
            if execution.get("status") == "completed":
                raise ValueError("A completed research delivery cannot be relabeled as missing")
            continue
        raw = evidence_bytes(root, row["response"])
        task = evidence_bytes(root, row["original_input"])
        review = json.loads(evidence_bytes(root, row["review"]))
        execution = json.loads(evidence_bytes(root, row["execution"]))
        if (review.get("stage") != "A1" or review.get("B") != row["baseline_B"]
                or review.get("R") != row["research_R"]
                or review.get("answer_sha256") != hashlib.sha256(raw).hexdigest()
                or row.get("invited_answer_used") is not False
                or execution.get("kind") != "math" or execution.get("status") != "completed"
                or execution.get("exit_code") != 0 or execution.get("request_count") != 1
                or execution.get("tool_mismatch") is not None):
            raise ValueError("Research score differs from its original A1 review or execution")
        _validate_research_tool_evidence(root, row, execution, selected_policy)
        if (hashlib.sha256(task).hexdigest() != cases[row["case_id"]]["task_sha256"]
                or row.get("source_prompt_sha256") != cases[row["case_id"]]["task_sha256"]):
            raise ValueError("Research answer was submitted for a different original task")
        declaration = row.get("self_assessment", {})
        if declaration.get("origin") == "original_excerpt":
            start, end = declaration.get("utf8_start"), declaration.get("utf8_end")
            if (type(start) is not int or type(end) is not int or not 0 <= start < end <= len(raw)
                    or raw[start:end].decode("utf-8") != declaration.get("excerpt")):
                raise ValueError("Research self-assessment excerpt differs from the original response")
        for item in row.get("artifacts", []):
            evidence_bytes(root, item)
    return data


def validate_public_theorem_extension(root, record):
    """Check public A1 evidence without publishing companion case identities."""
    if record.get("theorem_extension_evidence") is None:
        return None
    from .theorem_extension import PUBLIC_CASE_IDS, POLICY_EDITIONS
    data = json.loads(evidence_bytes(root, record["theorem_extension_evidence"]))
    edition = POLICY_EDITIONS.get(data.get("research_policy_version", "0.1.0"))
    if (data.get("schema") != "math-gauge.theorem-extension-public-evidence/v1"
            or data.get("attempt_labels") != ["A1"] or data.get("research_invitation_included") is not False
            or edition is None or data.get("public_cases") != len(PUBLIC_CASE_IDS)
            or data.get("private_cases") != edition[0]
            or data.get("formal_comparison_eligible") is not False):
        raise ValueError("Invalid public theorem-extension evidence projection")
    rows = data.get("records", [])
    if len({r["case_id"] for r in rows}) != len(rows):
        raise ValueError("Repeated public research answer")
    for row in rows:
        if row.get("case_id") not in PUBLIC_CASE_IDS or row.get("attempt_label") != "A1":
            raise ValueError("Private case or invited answer entered public research records")
        raw = evidence_bytes(root, row["response"])
        review = json.loads(evidence_bytes(root, row["review"]))
        if (review.get("stage") != "A1" or review.get("B") != row.get("baseline_B")
                or review.get("R") != row.get("research_R")
                or review.get("answer_sha256") != hashlib.sha256(raw).hexdigest()):
            raise ValueError("Public research review is not bound to the original answer")
    return data



def load_background_check_inputs(root, record, *, policy=None):
    """Verify original answers, adopted diagnostic levels and native local-tool evidence."""
    if record.get('background_check_inputs') is None:
        return None
    from .background_check import validate_inputs
    data=json.loads(evidence_bytes(root,record['background_check_inputs']))
    selected=data['policy'] if policy is None else policy
    validate_inputs(data,selected)
    cases={c['case_id']:c for c in data['case_index']}
    for case in cases.values():
        for field,hash_key in [('original_task','task_sha256'),('contract','contract_sha256')]:
            if hashlib.sha256(evidence_bytes(root,case[field])).hexdigest()!=case[hash_key]:
                raise ValueError('Background retained task or contract bytes differ')
        evidence_bytes(root,case['source_rubric']);evidence_bytes(root,case['reference'])
    for row in data['slots']:
        if row['status']=='not_run': continue
        execution=json.loads(evidence_bytes(root,row['execution']))
        if row['status']=='delivery_failed':
            if execution.get('status')=='completed':
                raise ValueError('Completed background return cannot become missing delivery')
            continue
        raw=evidence_bytes(root,row['response'])
        review=json.loads(evidence_bytes(root,row['review']))
        source=json.loads(evidence_bytes(root,row['source_review']))
        task=evidence_bytes(root,row['original_input'])
        if (review.get('stage')!='A1' or review.get('background_R')!=row['background_R']
            or review.get('complete')!=row['complete'] or review.get('false_endorsement')!=row['false_endorsement']
            or review.get('answer_sha256')!=hashlib.sha256(raw).hexdigest()
            or review.get('source_review_sha256')!=row['source_review']['sha256']
            or source.get('source_rubric',{}).get('sha256')!=cases[row['case_id']]['source_rubric']['sha256']
            or source.get('reference',{}).get('sha256')!=cases[row['case_id']]['reference']['sha256']
            or source.get('answer',{}).get('sha256')!=hashlib.sha256(raw).hexdigest()
            or review.get('complete')!=source.get('all_substantive_requirements_verified')
            or review.get('false_endorsement')!=source.get('target_failure')
            or execution.get('status')!='completed' or execution.get('kind')!='math'
            or execution.get('request_count')!=1 or execution.get('exit_code')!=0
            or execution.get('tool_mismatch') is not None
            or hashlib.sha256(task).hexdigest()!=cases[row['case_id']]['task_sha256']
            or row.get('source_prompt_sha256')!=cases[row['case_id']]['task_sha256']):
            raise ValueError('Background judgment differs from its original source or execution')
        _validate_research_tool_evidence(root,row,execution,selected)
        original_control=evidence_bytes(root,row['original_capability_control'])
        control=json.loads(evidence_bytes(root,row['native_capability_control']))
        if control.get('source_control_sha256')!=hashlib.sha256(original_control).hexdigest():
            raise ValueError('Background native capability evidence lost its source binding')
        for q in source.get('quoted_evidence',[]):
            if raw[q['utf8_byte_start']:q['utf8_byte_end']]!=q['quote'].encode():
                raise ValueError('Background source quote differs from the exact answer')
        for item in row.get('artifacts',[]): evidence_bytes(root,item)
    return data


def validate_public_background_check(root,record):
    """Public source evidence contains only the two public families."""
    if record.get('background_check_evidence') is None: return None
    from .background_check import PUBLIC_CASE_IDS
    data=json.loads(evidence_bytes(root,record['background_check_evidence']))
    rows=data.get('records',[])
    if (data.get('schema')!='math-gauge.background-check-public-evidence/v1'
        or data.get('public_cases')!=2 or data.get('private_cases')!=2
        or len({x.get('case_id') for x in rows})!=len(rows)
        or data.get('formal_comparison_eligible') is not False):
        raise ValueError('Invalid public background evidence projection')
    for row in rows:
        if row.get('case_id') not in PUBLIC_CASE_IDS or row.get('attempt_label')!='A1':
            raise ValueError('Private background case entered public records')
        raw=evidence_bytes(root,row['response']);review=json.loads(evidence_bytes(root,row['review']))
        if (review.get('answer_sha256')!=hashlib.sha256(raw).hexdigest()
            or review.get('background_R')!=row.get('background_R')
            or review.get('complete')!=row.get('complete')):
            raise ValueError('Public background judgment lost its source answer')
    return data

def load_claim_review(root, record, condition, *, public_root=None):
    """Verify an appended claim audit without altering any source adjudication."""
    from .claim_penalties import validate_review
    root = Path(root).resolve()
    external = record.get("formalization_evidence_location") == "public_archive"
    public = Path(public_root).resolve() if public_root is not None else root
    raw = evidence_bytes(root, record["claim_review"])
    archive = json.loads(raw)
    expected_schema = ("math-gauge.claim-review-archive/v1" if external else
                       "math-gauge.claim-review-projection/v1")
    if (archive.get("schema") != expected_schema or archive.get("benchmark_version") != "0.6.0"
            or set(archive.get("conditions", {})) != {"single_attempt", "nonlogical_retry_3"}
            or archive.get("human_review") != "pending"):
        raise ValueError("Current archive needs a complete attributed claim review")
    if not external and archive.get("source_archive_sha256") != record.get("claim_review_source_sha256"):
        raise ValueError("Public claim projection binds a different private source audit")
    data = archive["conditions"][condition]
    rows = validate_review(data)
    assessment = json.loads(evidence_bytes(public, record["assessment_policy"]))
    public_ids = set(assessment["case_selection"]["public_case_ids"])
    public_ids.update(assessment["theorem_extension"]["public_case_ids"])
    public_ids.update(assessment["background_check"]["public_case_ids"])
    if (not external and set(rows) != public_ids
            or external and (not public_ids.issubset(rows) or len(rows) != assessment["scope"]["tasks"])):
        raise ValueError("Claim review changed the selected public/private task population")
    if archive.get("policy_sha256") != record["claim_penalty_policy"]["sha256"]:
        raise ValueError("Claim review binds a different penalty policy")
    if external:
        evidence_bytes(root, data["source_inputs"])
    checked_sources, parsed_sources = {}, {}
    for row in rows.values():
        if row["status"] in {"reviewed", "unresolved"} and not row["sources"]:
            raise ValueError("A claim review requires retained source evidence")
        texts = []
        for source in row["sources"]:
            if source.get("archive") not in {"public", "private"} or not external and source["archive"] != "public":
                raise ValueError("Claim evidence crossed its public/private projection boundary")
            base = public if source["archive"] == "public" else root
            key = (str(base), source["path"], source["sha256"])
            if key not in checked_sources:
                checked_sources[key] = evidence_bytes(base, source).decode("utf-8")
            texts.append(checked_sources[key])
        for finding in row["findings"]:
            for item in finding["evidence"]:
                number = item.get("source")
                if type(number) is not int or not 0 <= number < len(texts) or not item.get("quote"):
                    raise ValueError("Claim finding lost its specific source evidence")
                text = texts[number]
                if item.get("json_pointer") is not None:
                    if text not in parsed_sources:
                        parsed_sources[text] = json.loads(text)
                    value = parsed_sources[text]
                    for token in item["json_pointer"].strip("/").split("/"):
                        token = token.replace("~1", "/").replace("~0", "~")
                        value = value[int(token)] if isinstance(value, list) else value[token]
                    text = value if isinstance(value, str) else json.dumps(value, ensure_ascii=False)
                if item["quote"] not in text:
                    raise ValueError("Claim finding quotes different source bytes")
        embedded = row.get("embedded_reliability")
        if embedded is not None:
            item = embedded["source_score"]
            text = texts[item["source"]]
            if text not in parsed_sources:
                parsed_sources[text] = json.loads(text)
            value = parsed_sources[text]
            for token in item["json_pointer"].strip("/").split("/"):
                value = value[int(token)] if isinstance(value, list) else value[token]
            if value != embedded["awarded"]:
                raise ValueError("Embedded reliability credit differs from the original review")
    return data


def load_assessment_results(root, record, *, mode="partial", public_root=None):
    """Check current score-view bytes and policy/source identities in either archive."""
    if record.get("assessment_policy") is None:
        return None
    from .benchmarks import validate_assessment_policy, identity
    from .scoring import validate_strict_assessment_policy, validate_capability_policy
    root = Path(root).resolve()
    external = record.get("formalization_evidence_location") == "public_archive"
    if external and public_root is None:
        raise ValueError("Current assessment requires an explicit public evidence archive")
    evidence_root = Path(public_root).resolve() if external else root
    assessment_raw = evidence_bytes(evidence_root, record["assessment_policy"])
    strict_raw = evidence_bytes(evidence_root, record["strict_scoring_policy"])
    assessment = validate_assessment_policy(json.loads(assessment_raw))
    validate_strict_assessment_policy(json.loads(strict_raw))
    claim_raw = None
    if assessment["version"] == "0.8.0":
        from .claim_penalties import validate_policy
        claim_raw = evidence_bytes(evidence_root, record["claim_penalty_policy"])
        validate_policy(json.loads(claim_raw))
    keys = {"capability": "capability_results", "partial": "assessment_results", "strict": "strict_results"}
    if mode not in keys:
        raise ValueError("Unknown assessment score mode")
    capability_raw = None
    if mode == "capability":
        capability_raw = evidence_bytes(evidence_root, record["capability_scoring_policy"])
        validate_capability_policy(json.loads(capability_raw))
        catalog = json.loads(evidence_bytes(evidence_root, record["score_mode_catalog"]))
        if (record.get("default_score_mode") != "partial" or catalog.get("default") != "partial"
                or catalog.get("primary") != "partial"
                or [m.get("id") for m in catalog.get("modes", [])] != ["capability", "partial", "strict"]):
            raise ValueError("Current record must bind three score modes with reliable as default")
    sources = record.get(keys[mode], {})
    if set(sources) != {"single_attempt", "nonlogical_retry_3"}:
        raise ValueError("Current assessment needs both attempt conditions")
    scores = {}
    for condition, item in sources.items():
        score = json.loads(evidence_bytes(root, item))
        bindings = score.get("source_bindings", {})
        if (score.get("schema") != ("math-gauge.assessment-score/v1" if external else
                                    "math-gauge.assessment-score-aggregate/v1")
                or score.get("benchmark_version") != record["benchmark_version"]
                or score.get("scoring_method_version") != assessment["version"]
                or score.get("strict_method_version") != "0.2.0"
                or score.get("score_mode") != mode or score.get("primary_metric") != "earned"
                or score.get("attempt_condition") != condition
                or score.get("formal_comparison_eligible") is not False
                or score.get("human_review") != "pending"
                or bindings.get("assessment_policy_sha256") != hashlib.sha256(assessment_raw).hexdigest()
                or bindings.get("strict_policy_sha256") != hashlib.sha256(strict_raw).hexdigest()
                or bindings.get("engineering_review_sha256") != record["formalization_review"]["sha256"]):
            raise ValueError("Current score identity, condition or evidence binding changed")
        if mode == "capability" and (score.get("capability_method_version") != json.loads(capability_raw)["version"]
                or score.get("capability_policy_sha256") != identity(json.loads(capability_raw))
                or bindings.get("capability_policy_sha256") != hashlib.sha256(capability_raw).hexdigest()):
            raise ValueError("Capability score binds a different positive-contribution policy")
        if claim_raw is not None:
            load_claim_review(root, record, condition, public_root=evidence_root)
            source_sha = (record["claim_review"]["sha256"] if external else record["claim_review_source_sha256"])
            if (score.get("claim_penalty_method_version") != "0.1.0"
                    or score.get("claim_penalty_policy_sha256") != identity(json.loads(claim_raw))
                    or score.get("claim_penalties", {}).get("status") != "source_bound_review_applied"
                    or bindings.get("claim_penalty_policy_sha256") != hashlib.sha256(claim_raw).hexdigest()
                    or bindings.get("claim_review_sha256") != source_sha):
                raise ValueError("Current result lacks its source-bound claim penalty audit")
        if external:
            filename = ("retry-scoring-inputs.json" if condition == "nonlogical_retry_3"
                        and record.get("retry_admission") else "scoring-inputs.json")
            alignment = root / "reviews/alignment.json"
            if not alignment.exists():
                alignment = root / "alignment-review.json"
            expected = {"scoring_inputs_sha256": root / filename,
                        "source_math_policy_sha256": root / "scoring-policy.json",
                        "alignment_review_sha256": alignment}
            if record.get("theorem_extension_inputs") is not None:
                research = load_theorem_extension_inputs(root, record, policy=assessment.get("theorem_extension"))
                expected["theorem_extension_inputs_sha256"] = root / record["theorem_extension_inputs"]["path"]
            if record.get('background_check_inputs') is not None:
                load_background_check_inputs(root,record,policy=assessment.get('background_check'))
                expected['background_check_inputs_sha256']=root/record['background_check_inputs']['path']
            if any(bindings.get(key) != hashlib.sha256(path.read_bytes()).hexdigest()
                   for key, path in expected.items()):
                raise ValueError("Current score binds different source judgments")
        else:
            if score != project_assessment_score(score):
                raise ValueError("Current public score must contain only projected aggregates")
        scores[condition] = score
    return scores


def load_strict_results(root, record, *, public_root=None):
    return load_assessment_results(root, record, mode="strict", public_root=public_root)


def descriptor(root, path):
    root, path = Path(root).resolve(), Path(path).resolve()
    if not path.is_file() or not path.is_relative_to(root):
        raise ValueError("Record evidence must be a local regular file")
    raw = path.read_bytes()
    return {"path": str(path.relative_to(root)), "bytes": len(raw),
            "sha256": hashlib.sha256(raw).hexdigest()}


def evidence_bytes(root, item):
    name = item.get("path")
    if not isinstance(name, str) or "\\" in name:
        raise ValueError("Invalid record evidence path")
    relative = PurePosixPath(name)
    root = Path(root).resolve()
    if relative.is_absolute() or ".." in relative.parts or str(relative) != name:
        raise ValueError("Record evidence path escapes its archive")
    path = root / name
    if any(p.is_symlink() for p in [path, *path.parents] if p != root.parent):
        raise ValueError("Record evidence cannot traverse a symlink")
    if not path.is_file() or not path.resolve().is_relative_to(root):
        raise ValueError("Missing record evidence")
    raw = path.read_bytes()
    if len(raw) != item.get("bytes") or hashlib.sha256(raw).hexdigest() != item.get("sha256"):
        raise ValueError("Record evidence bytes changed")
    return raw


def validate_self_assessment(root, assessment):
    if assessment.get("value") not in ASSESSMENTS:
        raise ValueError("Unknown self-assessment value")
    origin = assessment.get("origin")
    if origin not in {"model_structured", "extracted_from_original", "not_available"}:
        raise ValueError("Unknown self-assessment origin")
    evidence = assessment.get("evidence", [])
    if origin in {"extracted_from_original", "model_structured"} and not evidence:
        raise ValueError("Self-assessment needs original evidence")
    if origin == "not_available" and assessment["value"] in {"complete", "incomplete", "uncertain"}:
        raise ValueError("A model judgment cannot be supplied without original evidence")
    for item in evidence:
        raw = evidence_bytes(root, item["source"])
        if item.get("kind") == "structured_alignment":
            data = json.loads(raw)
            items = data.get("items", [])
            if (len(items) != item.get("total")
                    or len({r.get("id") for r in items}) != len(items)
                    or sum(r.get("status") == "complete" for r in items) != item.get("reported_complete")):
                raise ValueError("Structured self-assessment differs from its original alignment")
            if "response_source" in item or "response_span" in item:
                response = evidence_bytes(root, item["response_source"])
                span = item["response_span"]
                start, end = span.get("start_byte"), span.get("end_byte")
                if (type(start) is not int or type(end) is not int
                        or not 0 <= start < end <= len(response)
                        or response[start:end] != raw
                        or span.get("sha256") != hashlib.sha256(raw).hexdigest()):
                    raise ValueError("Structured self-assessment differs from its original response")
            continue
        start, end = item.get("start_byte"), item.get("end_byte")
        if (type(start) is not int or type(end) is not int or not 0 <= start < end <= len(raw)
                or raw[start:end].decode("utf-8") != item.get("quote")):
            raise ValueError("Self-assessment quotation does not match original bytes")
    if origin == "not_available" and not assessment.get("reason"):
        raise ValueError("Missing self-assessment needs an explicit reason")


def trajectory(rounds, *, planned_rounds):
    """Describe only observed adjudicated states; never infer future convergence."""
    if type(planned_rounds) is not int or planned_rounds < 1 or len(rounds) > planned_rounds:
        raise ValueError("Invalid fixed trajectory denominator")
    values = [r.get("evaluation", {}).get("complete_count") for r in rounds]
    totals = [r.get("evaluation", {}).get("total") for r in rounds]
    verified = [type(v) is int and type(t) is int and t > 0 and v == t for v, t in zip(values, totals)]
    first_verified = next((i + 1 for i, v in enumerate(verified) if v), None)
    first_claimed = next((i + 1 for i, r in enumerate(rounds)
                          if r.get("self_assessment", {}).get("value") == "complete"
                          and r.get("self_assessment", {}).get("scope") == "full_task"), None)
    false_claims = [i + 1 for i, r in enumerate(rounds)
                    if r.get("evaluation", {}).get("false_complete_claim") is True]
    if not rounds or len(rounds) < planned_rounds:
        state = "interrupted"
    elif any(v is None or t is None for v, t in zip(values, totals)):
        state = "unresolved"
    elif verified[-1]:
        state = "verified_complete"
    elif (any(b < a for a, b in zip(values, values[1:]))
          or any(r.get("evaluation", {}).get("regressed", 0) not in (None, 0) for r in rounds)):
        state = "regressed"
    elif len(set(values)) == 1:
        state = "incomplete_stable"
    else:
        state = "incomplete_changed"
    held = 0
    if first_verified:
        for v in verified[first_verified:]:
            if not v:
                break
            held += 1
    return {"planned_rounds": planned_rounds, "recorded_rounds": len(rounds),
            "first_claimed_complete_round": first_claimed,
            "first_verified_complete_round": first_verified,
            "verified_maintenance_rounds_after_first_complete": held,
            "false_complete_claim_rounds": false_claims,
            "last_complete_count": values[-1] if values else None,
            "total": totals[-1] if totals else None, "state": state,
            "selection": "last_prescribed_round; no best-of or union",
            "stop_reason": "fixed_rounds_completed" if len(rounds) == planned_rounds else "missing_or_blocked_rounds"}


def validate_formalization_review(root, inputs, review):
    """Bind each mathematical judgment to the selected sealed files and kernel audit."""
    from .scoring import formalization_substitutions

    formalization_substitutions(inputs, review)
    frozen_cases = {case["case_id"]: case for case in inputs["plan"]["case_index"]}
    for case in review["cases"]:
        contract = evidence_bytes(root, case["case_contract"])
        if hashlib.sha256(contract).hexdigest() != frozen_cases[case["case_id"]]["group_contract_sha256"]:
            raise ValueError("Engineering evidence binds a different mathematical contract")
        if set(case.get("background_inputs", {})) != set(json.loads(contract)["immutable_input_files"]):
            raise ValueError("Engineering background inventory differs from the frozen contract")
        manifest = json.loads(evidence_bytes(root, case["source_manifest"]))
        if manifest.get("tree_sha256") != case.get("source_sha256"):
            raise ValueError("Engineering source differs from its original sealed manifest")
        selected = case.get("source_files", {})
        if set(selected) != set(case["compiled_sources"]):
            raise ValueError("Engineering evidence changed its compiled-file inventory")
        for name, item in selected.items():
            raw = evidence_bytes(root, item)
            actual = hashlib.sha256(raw).hexdigest()
            if (actual != case["compiled_sources"][name]
                    or manifest.get("files", {}).get(name, {}).get("sha256") != actual):
                raise ValueError("Compiled engineering source differs from the sealed original")
        kernel = json.loads(evidence_bytes(root, case["kernel_report"]))
        if (kernel.get("files_sha256") != case["compiled_sources"]
                or kernel.get("source_repaired") is not False):
            raise ValueError("Kernel evidence belongs to different or repaired source")
        audit = kernel.get("audit", {})
        modules = kernel.get("modules", [])
        background = {name[:-5].replace("/", "."): hashlib.sha256(evidence_bytes(root, item)).hexdigest()
                      for name, item in case.get("background_inputs", {}).items()}
        selected_modules = {name[:-5].replace("/", "."): case["compiled_sources"][name] for name in selected}
        compiled_modules = {row.get("module"): row.get("source_sha256") for row in modules}
        if any(compiled_modules.get(name) != digest for name, digest in selected_modules.items()):
            raise ValueError("Kernel module receipts differ from the selected engineering source")
        for module in modules:
            name = module.get("module", "")
            if name.startswith("formal_oet.") and name not in selected_modules:
                if background.get(name) != module.get("source_sha256"):
                    raise ValueError("Kernel audit used a different or unprovided frozen predecessor")
        passed = (bool(modules) and all(row.get("exit_code") == 0 and row.get("timeout") is not True
                                      for row in modules)
                  and audit.get("summary", {}).get("passed") is True
                  and not audit.get("summary", {}).get("unexpected_axioms"))
        if (case.get("kernel_status") == "passed") != passed:
            raise ValueError("Selected engineering kernel status differs from its actual report")
        inventory = {(row.get("module"), row.get("name")) for row in audit.get("declarations", [])}
        for item in case["obligations"]:
            if item["complete"] is True:
                for declaration in item["declarations"]:
                    filename, name = declaration.get("file"), declaration.get("name")
                    if (not isinstance(filename, str) or not filename.endswith(".lean")
                            or not isinstance(name, str)
                            or (filename[:-5].replace("/", "."), name) not in inventory):
                        raise ValueError("Completed obligation names a declaration absent from the kernel audit")
        for item in case.get("review_evidence", []):
            evidence_bytes(root, item)
    return {"cases": len(review["cases"]), "passed": True}


def validate_record(root, *, formalization_root=None, validate_scores=True):
    root = Path(root).resolve()
    record = json.loads((root / "record.json").read_bytes())
    if record.get("schema") != SCHEMA or record.get("benchmark_version") != "0.6.0":
        raise ValueError("Unsupported formal result record")
    if record.get("retention", {}).get("user_requested") is not True:
        raise ValueError("Formal retention requires an explicit user selection")
    rows = record.get("records", [])
    ids = [r.get("id") for r in rows]
    if len(ids) != len(set(ids)) or any(not isinstance(i, str) or not i for i in ids):
        raise ValueError("Repeated or invalid record IDs")
    known = set(ids)
    indexed = {r["id"]: r for r in rows}
    for row in rows:
        ancestors = {row["id"]}
        parent = row.get("parent_id")
        while parent is not None:
            if parent in ancestors or parent not in indexed:
                raise ValueError("Unknown or cyclic record parent")
            ancestors.add(parent)
            if indexed[parent]["case_id"] != row["case_id"]:
                raise ValueError("Record parent belongs to a different task")
            parent = indexed[parent].get("parent_id")
    for row in rows:
        if row.get("parent_id") is not None and row["parent_id"] not in known:
            raise ValueError("Unknown record parent")
        response = row.get("response")
        if response is not None:
            evidence_bytes(root, response)
            expected = row.get("source", {}).get("response_sha256")
            if expected is not None and expected != response["sha256"]:
                raise ValueError("Raw response differs from its execution source")
        elif not row.get("missing_response_reason"):
            raise ValueError("Missing raw response needs an explicit reason")
        validate_self_assessment(root, row["self_assessment"])
        for item in row.get("artifacts", []):
            evidence_bytes(root, item)
        evaluation = row.get("evaluation", {})
        n, total = evaluation.get("complete_count"), evaluation.get("total")
        if n is not None and (type(n) is not int or type(total) is not int or not 0 <= n <= total):
            raise ValueError("Invalid reviewed obligation counts")
    for item in record.get("evidence", []):
        evidence_bytes(root, item)
    load_theorem_extension_inputs(root, record)
    validate_public_theorem_extension(root, record)
    load_background_check_inputs(root, record)
    validate_public_background_check(root, record)
    if record.get("formalization_review") is not None:
        location = record.get("formalization_evidence_location", "local")
        if location not in {"local", "public_archive"}:
            raise ValueError("Unknown formalization evidence location")
        if location == "public_archive" and formalization_root is None:
            raise ValueError("Private record requires its explicitly selected public engineering archive")
        source_root = Path(formalization_root).resolve() if location == "public_archive" else root
        review = json.loads(evidence_bytes(source_root, record["formalization_review"]))
        inputs = json.loads((root / "scoring-inputs.json").read_bytes())
        validate_formalization_review(source_root, inputs, review)
        policy_raw = (root / "scoring-policy.json").read_bytes()
        policy = json.loads(policy_raw)
        alignment_path = root / "reviews/alignment.json"
        if not alignment_path.exists():
            alignment_path = root / "alignment-review.json"
        alignment = json.loads(alignment_path.read_bytes())
        if (review.get("policy_sha256") != hashlib.sha256(policy_raw).hexdigest()
                or alignment.get("policy_sha256") != review["policy_sha256"]
                or alignment.get("scoring_version") != policy.get("version")):
            raise ValueError("Engineering and alignment reviews bind different scoring policies")
        filenames = (("result.json",) if location == "public_archive" else ("combined-aggregate.json",)
                     if record.get("assessment_policy") else ("result.json", "combined-aggregate.json"))
        for filename in filenames:
            if filename == "combined-aggregate.json" and location == "public_archive":
                continue
            result = json.loads((root / filename).read_bytes())
            if (result.get("engineering_review_sha256") != record["formalization_review"]["sha256"]
                    or result.get("source_math_policy_version", result.get("scoring_method_version")) != policy["version"]):
                raise ValueError("Current result binds a different engineering review or scoring method")
    elif (root / "scoring-policy.json").is_file():
        if json.loads((root / "scoring-policy.json").read_bytes()).get("version") == "0.4.0":
            raise ValueError("Current engineering scoring requires all four source-bound reviews")
    if record.get("human_review") != "pending" or record.get("formal_comparison_eligible") is not False:
        raise ValueError("Record migration cannot promote human or execution qualification")
    load_retry_inputs(root, record, public_root=formalization_root, validate_results=validate_scores)
    if validate_scores:
        load_assessment_results(root, record, public_root=formalization_root)
        load_strict_results(root, record, public_root=formalization_root)
        if "capability_results" in record or "capability_scoring_policy" in record:
            load_assessment_results(root, record, mode="capability", public_root=formalization_root)
    return {"record_id": record["record_id"], "records": len(rows),
            "raw_responses": sum(r.get("response") is not None for r in rows),
            "candidate_calls_by_migration": record.get("candidate_calls_by_migration"), "passed": True}
