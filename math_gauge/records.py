"""Source-bound final records: raw self-assessment evidence and finite trajectories.

This owner collects and validates records. Mathematical aggregation remains in
scoring.py; execution remains in execution.py and the existing harness.
"""

import hashlib
import json
import copy
import re
from pathlib import Path, PurePosixPath

SCHEMA = "math-gauge.result-record/v1"
ASSESSMENTS = {"complete", "incomplete", "uncertain", "not_stated", "not_requested", "unresolved"}


def selected_cli_records(root):
    """Resolve user-selected CLI archives without guessing the newest result.

    Older editions had one retained record per selected model. An explicit
    record-id mapping can select among several user-retained snapshots.
    Native observations keep their separate record contract and loader.
    """
    root = Path(root).resolve()
    edition = json.loads((root / "benchmark.json").read_bytes())
    selected = edition["selected_result_models"]
    record_ids = edition.get("selected_result_record_ids", {})
    if len(selected) != len(set(selected)):
        raise ValueError("Selected result models must not repeat")
    result = []
    for model in selected:
        if (not isinstance(model, str) or not re.fullmatch(r"[a-z0-9][a-z0-9._-]*", model)):
            raise ValueError("Selected result model must be a safe model id")
        parent = root / "results" / ("v" + edition["version"]) / model
        record_id = record_ids.get(model)
        if record_id is not None:
            if not isinstance(record_id, str) or not re.fullmatch(r"[a-zA-Z0-9][a-zA-Z0-9._-]*", record_id):
                raise ValueError("Selected result record must be a safe record id")
            candidates = [parent / record_id / "record.json"]
        else:
            candidates = sorted(parent.glob("*/record.json"))
        if len(candidates) != 1 or not candidates[0].is_file():
            raise ValueError("Select exactly one retained result record for " + model)
        path = candidates[0].resolve()
        if not path.is_relative_to(root):
            raise ValueError("Selected result record cannot leave the public repository")
        result.append((model, path.parent))
    return result


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


def _native_research_completed(root, row, execution):
    """Admit an exact first native SUCCESS while preserving failed CLI cleanup.

    This narrow source adapter is not provider authentication. The legacy
    completed/exit0 path stays unchanged; readable ERROR and DONE never qualify.
    """
    if execution.get("status") == "completed" and execution.get("exit_code") == 0:
        return True
    item = row.get("native_delivery_receipt")
    if item is None:
        return False
    data = json.loads(evidence_bytes(root, item))
    plan = json.loads(evidence_bytes(root, row["execution_plan"]))
    answer = evidence_bytes(root, row["response"])
    events = [json.loads(line) for line in evidence_bytes(root, data["native_events"]).splitlines()]
    terminal = json.loads(evidence_bytes(root, data["native_terminal_event"]))
    seal = json.loads(evidence_bytes(root, data["native_terminal_seal"]))
    qualification = json.loads(evidence_bytes(root, data["collection_qualification"]))
    native = [event for event in events if event.get("event") == "result"]
    answer_hash = hashlib.sha256(answer).hexdigest()
    if (data.get("schema") != "math-gauge.native-success-cleanup-admission/v1"
            or data.get("post_observation") is not True or data.get("source_raw_bytes_rewritten") is not False
            or data.get("native_execution") != row.get("execution")
            or data.get("candidate_input") != row.get("original_input")
            or data.get("answer_sha256") != answer_hash
            or plan.get("client") != "agy" or execution.get("status") != "failed"
            or execution.get("exit_code") != -9 or execution.get("kind") != "math"
            or execution.get("request_count") != 1 or execution.get("tool_mismatch") is not None
            or (execution.get("failure") or {}).get("message") != "CLI failed or violated tools policy"
            or len(native) != 1 or native[0] != terminal or terminal.get("event") != "result"
            or terminal.get("result", {}).get("status") != "SUCCESS"
            or terminal.get("result", {}).get("response", "").encode("utf-8") != answer
            or seal.get("native_status") != "SUCCESS" or seal.get("normal_complete_delivery") is not True
            or seal.get("answer_sha256") != answer_hash
            or seal.get("raw_terminal_sha256") != data["native_terminal_event"].get("sha256")
            or qualification.get("collection_status") != "qualified"
            or qualification.get("answer_sha256") != answer_hash
            or any(qualification.get("checks", {}).get(key) is not True for key in
                   ("native_success", "first_native_terminal_exact", "native_final_text_exact_utf8",
                    "input_matches_frozen_candidate_message"))
            or execution.get("artifact_hashes", {}).get("input/task.md") != row["original_input"].get("sha256")
            or execution.get("artifact_hashes", {}).get("output/events.ndjson") != data["native_events"].get("sha256")):
        raise ValueError("Native research admission lacks its exact first SUCCESS and original cleanup evidence")
    return True


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
                or execution.get("kind") != "math" or not _native_research_completed(root, row, execution)
                or execution.get("request_count") != 1
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
            or not _native_research_completed(root,row,execution) or execution.get('kind')!='math'
            or execution.get('request_count')!=1
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

def _validate_manuscript_request_history(root, row, case, *, selected=None):
    """Retain submitted, uncertified requests without inventing a math zero.

    Unlike a pure-system exclusion, an authorized restart keeps the unresolved
    earlier request in the consumed physical/effective attempt history.
    """
    task = evidence_bytes(root, case["original_task"])
    ledger = json.loads(evidence_bytes(root, row["physical_request_ledger"]))
    attempts = ledger.get("attempts", [])
    if (ledger.get("schema") != "math-gauge.manuscript-request-history/v2"
            or ledger.get("selected_physical_request") != selected
            or not 1 <= len(attempts) <= 3
            or ledger.get("consumed_effective_attempts") != len(attempts)
            or [a.get("physical_request") for a in attempts] != list(range(1, len(attempts)+1))
            or selected is not None and selected != len(attempts)
            or ledger.get("mathematical_disposition") != ("ungraded_execution_authentication_failed"
                if selected is None else "first_complete_authorized_restart_delivery")):
        raise ValueError("Uncertified manuscript execution needs its complete, unselected request history")
    for number, attempt in enumerate(attempts, 1):
        execution = json.loads(evidence_bytes(root, attempt["execution"]))
        plan = json.loads(evidence_bytes(root, attempt["execution_plan"]))
        events = [json.loads(line) for line in evidence_bytes(root, attempt["native_events"]).splitlines()]
        request = evidence_bytes(root, attempt["native_request"])
        evidence_bytes(root, attempt["execution_result"])
        if (execution.get("request_count") != 1 or execution.get("kind") != "math"
                or execution.get("requested_model") != plan.get("model")
                or execution.get("requested_effort") != plan.get("effort")
                or plan.get("prompt_sha256") != case["task_sha256"]
                or plan.get("stdin_sha256") != hashlib.sha256(request).hexdigest()
                or execution.get("stdin_bytes_written") != len(request)
                or execution.get("stdin_write_calls") != 1
                or execution.get("artifact_hashes", {}).get("input/task.md") != case["task_sha256"]
                or execution.get("artifact_hashes", {}).get("output/events.ndjson") != attempt["native_events"]["sha256"]
                or plan.get("local_tool_policy") != "math-gauge.local-tools-no-search/v1"
                or plan.get("tool_network_access") is not False
                or evidence_bytes(root, attempt["candidate_input"]) != task
                or attempt.get("excluded_pure_system_failure") is not False
                or attempt.get("effective_model_attempt") != number):
            raise ValueError("Uncertified requests cannot be erased, relabeled pure-system or change the task")
        if plan.get("client") == "agy":
            if json.loads(request) != {"event": "user", "message": {"content": task.decode("utf-8")}}:
                raise ValueError("Uncertified manuscript request differs from its frozen question")
        elif plan.get("client") != "codex" or request != task:
            raise ValueError("Unsupported uncertified manuscript native input")
        delivered = (any(e.get("type") == "turn.completed" for e in events)
                or any(e.get("event") == "result" and e.get("result", {}).get("status") == "SUCCESS"
                    and e["result"].get("response", "").strip() for e in events))
        if delivered != (number == selected):
            raise ValueError("A normally delivered answer cannot be hidden as missing execution")
        if number > 1:
            authorization = json.loads(evidence_bytes(root, attempt["restart_authorization"]))
            kind = authorization.get("kind")
            if (kind not in {"user_authorized_independent_restart", "user_accepted_post_observation_trial_recovery"}
                    or authorization.get("physical_request") != number
                    or authorization.get("prior_request_excluded_as_pure_system") is not False
                    or not authorization.get("user_quote")):
                raise ValueError("Independent restart needs its explicit authorization and prior-request boundary")
            if kind == "user_accepted_post_observation_trial_recovery":
                if (authorization.get("post_observation") is not True
                        or authorization.get("case_id") != case["case_id"]
                        or authorization.get("task_sha256") != case["task_sha256"]
                        or authorization.get("accepted_source_response_sha256") != (row.get("response") or {}).get("sha256")
                        or authorization.get("adoption_does_not_change_original_execution") is not True):
                    raise ValueError("Post-observation acceptance must bind the actual retained task and answer")
                evidence_bytes(root, authorization["operator_recovery_source"])
    last = attempts[-1]
    if any(row.get(key) != last.get(key) for key in
            ("execution", "execution_plan", "execution_result", "native_events", "native_request", "candidate_input")):
        raise ValueError("Uncertified slot must point to the last retained operational attempt")
    if selected is not None and last.get("response") != row.get("response"):
        raise ValueError("Restart selection must retain the first delivered original answer")
    for item in row.get("artifacts", []):
        evidence_bytes(root, item)


def load_manuscript_completion_inputs(root, record, *, policy=None):
    """Bind an adopted manuscript judgment to exact original/native bytes.

    Native generation completion and intentional client cleanup are independent;
    these diagnostic sources never certify backend identity or formal eligibility.
    """
    if record.get("manuscript_completion_inputs") is None:
        return None
    from .manuscript_completion import validate_inputs, validate_system_exclusion
    data = json.loads(evidence_bytes(root, record["manuscript_completion_inputs"]))
    validate_inputs(data, data["policy"] if policy is None else policy)
    cases = {c["case_id"]: c for c in data["case_index"]}
    for case in cases.values():
        task = evidence_bytes(root, case["original_task"])
        contract_raw = evidence_bytes(root, case["contract"])
        contract = json.loads(contract_raw)
        rubric = json.loads(evidence_bytes(root, case["source_rubric"]))
        evidence_bytes(root, case["reference"])
        if (hashlib.sha256(task).hexdigest() != case["task_sha256"]
                or hashlib.sha256(contract_raw).hexdigest() != case["contract_sha256"]
                or contract.get("id") != case["case_id"] or contract.get("kind") != "research_exploration"
                or [{"criterion_id": r["id"], "points": r["points"]} for r in contract["dimensions"]] != case["criteria"]
                or [{"criterion_id": r["id"], "points": r["points"]} for r in rubric["criteria"]] != case["criteria"]
                or rubric.get("task_sha256") != case["task_sha256"] or rubric.get("post_observation") is not True):
            raise ValueError("Manuscript task, observed rubric or contract bytes changed")
        if case.get("fidelity_policy") is not None:
            if json.loads(evidence_bytes(root, case["fidelity_policy_source"])) != case["fidelity_policy"]:
                raise ValueError("Manuscript fidelity policy differs from its source bytes")
        if case.get("strict_completion_policy") is not None:
            if json.loads(evidence_bytes(root, case["strict_completion_policy_source"])) != case["strict_completion_policy"]:
                raise ValueError("Manuscript core completion policy differs from its source bytes")
    for row in data["slots"]:
        if row["status"] == "not_run":
            continue
        if row["status"] == "execution_authentication_failed":
            _validate_manuscript_request_history(root, row, cases[row["case_id"]])
            continue
        if any(not isinstance(row.get(k), dict) for k in (
                "native_request", "native_events", "candidate_input", "execution_result", "execution_plan",
                "native_capability_control", "physical_request_ledger")):
            raise ValueError("Manuscript delivery requires its original native input and complete request ledger")
        execution = json.loads(evidence_bytes(root, row["execution"]))
        case = cases[row["case_id"]]
        answer = evidence_bytes(root, row["response"])
        candidate = evidence_bytes(root, row["candidate_input"])
        task = evidence_bytes(root, case["original_task"])
        review = json.loads(evidence_bytes(root, row["review"]))
        result = json.loads(evidence_bytes(root, row["execution_result"]))
        plan = json.loads(evidence_bytes(root, row["execution_plan"]))
        events = [json.loads(b) for b in evidence_bytes(root, row["native_events"]).splitlines()]
        if plan.get("client") not in {"agy", "codex"}:
            raise ValueError("Unsupported manuscript native client")
        request_raw = evidence_bytes(root, row["native_request"])
        task_hash = hashlib.sha256(task).hexdigest()
        if (not isinstance(plan.get("stdin_file"), str) or not plan["stdin_file"]
                or not isinstance(plan.get("model"), str) or not plan["model"]
                or plan.get("prompt_sha256") != task_hash or plan.get("task_sha256", task_hash) != task_hash
                or plan.get("stdin_sha256") != hashlib.sha256(request_raw).hexdigest()
                or plan.get("stdin_file") != row.get("native_request_origin")
                or execution.get("stdin_bytes_written") != len(request_raw)
                or execution.get("stdin_write_calls") != 1
                or execution.get("artifact_hashes", {}).get("input/task.md") != task_hash
                or execution.get("artifact_hashes", {}).get("output/events.ndjson") != row["native_events"]["sha256"]
                or execution.get("requested_model") != plan.get("model")
                or execution.get("requested_effort") != plan.get("effort")):
            raise ValueError("Manuscript actual stdin differs from its sealed task or native plan")
        terminal = next((e for e in events if e.get("type", e.get("event")) in {"result", "turn.completed", "turn.failed"}), None)
        if terminal is None:
            raise ValueError("Manuscript needs an original native terminal")
        if plan.get("client") == "agy":
            native = terminal.get("result", {})
            text = native.get("response")
            delivered = terminal.get("event") == "result" and native.get("status") == "SUCCESS"
            request = json.loads(request_raw)
            if request != {"event": "user", "message": {"content": task.decode("utf-8")}}:
                raise ValueError("Manuscript native request changed its exact task")
        else:
            if request_raw != task:
                raise ValueError("Codex manuscript stdin must be the exact original task")
            messages = [e["item"].get("text") for e in events[:events.index(terminal)]
                if e.get("type") == "item.completed" and isinstance(e.get("item"), dict)
                and e["item"].get("type") == "agent_message"]
            text = messages[-1] if messages else None
            delivered = terminal.get("type") == "turn.completed"
            paired = json.loads(evidence_bytes(root, row["catalog_pair_check"]))
            if paired.get("passed") is not True or paired.get("pending") != {}:
                raise ValueError("Manuscript catalog events were not fully checked")
        seal = result.get("native_terminal_seal") or {}
        artifact_checks_passed = result.get("local_artifact_checks_passed") is True
        if result.get("schema") == "math-gauge.independent-idea-native-result/v1":
            seal = result.get("first_terminal") or {}
            artifact_checks_passed = (result.get("artifact_checks_passed") is True
                and result.get("normal_complete_delivery") is True
                and result.get("prompt_sha256") == task_hash)
        if (not delivered or not isinstance(text, str) or not text or text.encode("utf-8") != answer
                or candidate != task or execution.get("kind") != "math" or execution.get("request_count") != 1
                or execution.get("tool_mismatch") is not None or result.get("tool_mismatch") is not None
                or seal.get("answer_sha256") != row["response"]["sha256"]
                or not artifact_checks_passed
                or plan.get("local_tool_policy") != "math-gauge.local-tools-no-search/v1"
                or plan.get("tool_network_access") is not False
                or review.get("schema") != "math-gauge.manuscript-completion-review/v1"
                or review.get("case_id") != case["case_id"] or review.get("stage") != "A1"
                or review.get("reviewer_kind") != "ai" or review.get("human_review") != "pending"
                or review.get("formal_comparison_eligible") is not False
                or review.get("answer_sha256") != row["response"]["sha256"]
                or review.get("rubric_sha256") != case["source_rubric"]["sha256"]
                or review.get("score") != row["points"] or review.get("strict_pass") != row["complete"]):
            raise ValueError("Manuscript judgment lost its original input, answer or native execution")
        criteria = review.get("criteria", [])
        if ([{"criterion_id": c["id"], "points": c["max_points"]} for c in criteria] != case["criteria"]
                or any(type(c.get("points")) is not int or not 0 <= c["points"] <= c["max_points"] for c in criteria)
                or sum(c["points"] for c in criteria) != row["points"]):
            raise ValueError("Manuscript mathematical credit differs from its criterion review")
        manuscript = None
        if case.get("strict_completion_policy") is not None:
            strict_source = row.get("strict_completion_review_source")
            if (not isinstance(strict_source, dict)
                    or json.loads(evidence_bytes(root, strict_source)) != row.get("strict_completion_review")
                    or review.get("strict_completion_review_sha256") != strict_source.get("sha256")):
                raise ValueError("Manuscript core completion review lost its source judgment")
        if row.get("manuscript") is not None:
            manuscript = evidence_bytes(root, row["manuscript"])
            filename = Path(row["manuscript"]["path"]).name
            if (review.get("manuscript_sha256") != row["manuscript"]["sha256"]
                    or filename not in text
                    or not any(item.get("path") == filename
                        and item.get("sha256") == row["manuscript"]["sha256"]
                        and item.get("bytes") == len(manuscript) for item in seal.get("work", []))):
                raise ValueError("Delivered manuscript is not bound to the native final and sealed work")
        for criterion in criteria:
            for quote in criterion.get("evidence", []):
                document = quote.get("document", "answer")
                if document not in {"answer", "manuscript"}:
                    raise ValueError("Unsupported manuscript review document")
                raw = manuscript if document == "manuscript" else answer
                if raw is None or raw[quote["start"]:quote["end"]] != quote["quote"].encode("utf-8"):
                    raise ValueError("Manuscript review quotes different original bytes")
        fidelity = row.get("fidelity")
        if fidelity is not None:
            source = json.loads(evidence_bytes(root, fidelity["source"]))
            if (source.get("schema") != "math-gauge.manuscript-fidelity-review/v1"
                    or source.get("case_id") != case["case_id"]
                    or source.get("answer_sha256") != row["response"]["sha256"]
                    or source.get("rubric_sha256") != case["source_rubric"]["sha256"]
                    or source.get("policy_sha256") != case["fidelity_policy_source"]["sha256"]
                    or any(source.get(k) != fidelity[k] for k in
                        ("level", "adjustment_points", "passed", "reliable_acceptance", "root_cause"))
                    or source.get("reviewer_kind") != "ai" or source.get("human_review") != "pending"
                    or source.get("formal_comparison_eligible") is not False
                    or not source.get("evidence")):
                raise ValueError("Manuscript fidelity adjustment lost its source judgment")
            for quote in source["evidence"]:
                if answer[quote["start"]:quote["end"]] != quote["quote"].encode("utf-8"):
                    raise ValueError("Fidelity review quotes different original answer bytes")
        control = json.loads(evidence_bytes(root, row["native_capability_control"]))
        if (control.get("passed") is not True or control.get("math_requests") != 0
                or any(control.get("proof", {}).get(k) is not True
                    for k in ("local_read_write", "outside_denied", "network_denied"))):
            raise ValueError("Manuscript source lacks a real local-tool compatibility control")
        ledger = json.loads(evidence_bytes(root, row["physical_request_ledger"]))
        selected = row.get("selected_physical_request")
        if ledger.get("schema") == "math-gauge.manuscript-request-history/v2":
            if type(selected) is not int or selected <= 0:
                raise ValueError("A delivered authorized restart needs its exact selected request")
            _validate_manuscript_request_history(root, row, case, selected=selected)
            continue
        attempts = ledger.get("attempts", [])
        if (type(selected) is not int or selected <= 0 or not isinstance(attempts, list)
                or len(attempts) != selected or [a.get("physical_request") for a in attempts] != list(range(1, selected+1))
                or ledger.get("selected_physical_request") != selected
                or ledger.get("effective_model_attempt") != 1
                or ledger.get("first_complete_answer_selected") is not True
                or attempts[-1].get("execution") != row["execution"]
                or attempts[-1].get("native_events") != row["native_events"]
                or attempts[-1].get("response") != row["response"]):
            raise ValueError("Manuscript physical requests and effective A1 were conflated")
        for number, attempt in enumerate(attempts, 1):
            actual = json.loads(evidence_bytes(root, attempt["execution"]))
            original_events = [json.loads(b) for b in evidence_bytes(root, attempt["native_events"]).splitlines()]
            if actual.get("kind") != "math" or actual.get("request_count") != 1:
                raise ValueError("Manuscript ledger invented a physical mathematical request")
            text_available = False
            previous_text = None
            for event in original_events:
                if event.get("type") == "item.completed" and event.get("item", {}).get("type") == "agent_message":
                    previous_text = event["item"].get("text")
                if event.get("type") == "turn.completed":
                    text_available = bool(isinstance(previous_text, str) and previous_text.strip())
                    break
                if event.get("event") == "result":
                    native = event.get("result", {})
                    text_available = native.get("status") == "SUCCESS" and bool(native.get("response", "").strip())
                    break
            if attempt.get("response") is not None:
                evidence_bytes(root, attempt["response"])
            if number == selected:
                if (not text_available or attempt.get("first_complete_answer") is not True
                        or attempt.get("excluded_pure_system_failure") is not False
                        or attempt.get("effective_model_attempt") != 1):
                    raise ValueError("Selected manuscript request is not the first effective delivery")
            elif (text_available or attempt.get("first_complete_answer") is not False
                    or attempt.get("excluded_pure_system_failure") is not True
                    or attempt.get("effective_model_attempt") is not None
                    or attempt.get("exclusion_reason") not in {
                        "native_empty_reply_after_headless_permission_denial",
                        "controller_interruption_before_first_complete_answer",
                        "controller_local_edit_alias_false_positive"}):
                raise ValueError("Manuscript cannot exclude a normally delivered earlier answer")
            else:
                if not isinstance(attempt.get("stderr"), dict):
                    raise ValueError("A system exclusion needs its retained native error stream")
                validate_system_exclusion(actual, original_events, attempt["exclusion_reason"],
                    evidence_bytes(root, attempt["stderr"]).decode("utf-8"))
        for item in row.get("artifacts", []):
            evidence_bytes(root, item)
    return data


def validate_public_manuscript_completion(root, record):
    item = record.get("manuscript_completion_evidence")
    if item is None:
        return None
    data = json.loads(evidence_bytes(root, item))
    if (set(data) != {"schema", "private_cases", "source_inputs_sha256", "human_review", "formal_comparison_eligible"}
            or data.get("schema") != "math-gauge.manuscript-completion-public-evidence/v1"
            or type(data.get("private_cases")) is not int or data["private_cases"] not in {1, 2, 3, 4}
            or data.get("human_review") != "pending"
            or data.get("formal_comparison_eligible") is not False
            or not re.fullmatch(r"[0-9a-f]{64}", data.get("source_inputs_sha256", ""))):
        raise ValueError("Private manuscript evidence crossed its aggregate-only public boundary")
    return data


def load_written_argument_inputs(root, record, *, policy=None):
    """Bind added private written judgments to unchanged source tasks and A1 bytes."""
    if record.get("written_argument_inputs") is None:
        return None
    from .written_additions import validate_inputs
    data = json.loads(evidence_bytes(root, record["written_argument_inputs"]))
    selected = data["policy"] if policy is None else policy
    validate_inputs(data, selected)
    cases = {c["case_id"]: c for c in data["case_index"]}
    for case in cases.values():
        for field, hash_key in (("original_task", "task_sha256"), ("contract", "contract_sha256")):
            if hashlib.sha256(evidence_bytes(root, case[field])).hexdigest() != case[hash_key]:
                raise ValueError("Written addition retained different task or contract bytes")
        contract = json.loads(evidence_bytes(root, case["contract"]))
        rubric = json.loads(evidence_bytes(root, case["source_rubric"]))
        evidence_bytes(root, case["reference"])
        units = contract["criteria" if contract.get("kind") == "written_proof" else "dimensions"]
        weights = [{"criterion_id": c["id"], "points": c["points"]} for c in units]
        if (contract.get("id") != case["case_id"] or contract.get("kind") != case["contract_kind"]
                or weights != case["criteria"] or weights != [
                    {"criterion_id": c["id"], "points": c["points"]} for c in rubric["criteria"]]
                or rubric.get("total_points") != case["total_weight"]
                or rubric.get("task_sha256") != case["task_sha256"]):
            raise ValueError("Written addition changed its original criterion weights")
    for row in data["slots"]:
        if row["status"] == "not_run":
            continue
        execution = json.loads(evidence_bytes(root, row["execution"]))
        if row["status"] == "delivery_failed":
            if execution.get("status") == "completed":
                raise ValueError("Completed written return cannot become missing delivery")
            continue
        case = cases[row["case_id"]]
        raw = evidence_bytes(root, row["response"])
        source = json.loads(evidence_bytes(root, row["source_review"]))
        review = json.loads(evidence_bytes(root, row["review"]))
        statement = evidence_bytes(root, case["original_task"])
        candidate_input = evidence_bytes(root, row["candidate_input"])
        frozen = json.loads(evidence_bytes(root, row["original_test_plan"]))
        control_bytes = evidence_bytes(root, row["original_capability_control"])
        control = json.loads(control_bytes)
        native_control = json.loads(evidence_bytes(root, row["native_capability_control"]))
        if (review.get("schema") != "math-gauge.written-addition-review/v1"
                or review.get("case_id") != row["case_id"] or review.get("stage") != "A1"
                or review.get("points") != row["points"] or review.get("complete") != row["complete"]
                or review.get("answer_sha256") != row["response"]["sha256"]
                or review.get("source_review_sha256") != row["source_review"]["sha256"]
                or source.get("answer_sha256") != row["response"]["sha256"]
                or source.get("rubric_sha256") != case["source_rubric"]["sha256"]
                or source.get("score") != row["points"] or source.get("strict_pass") != row["complete"]
                or source.get("total_points") != case["total_weight"]
                or execution.get("status") != "completed" or execution.get("kind") != "math"
                or execution.get("request_count") != 1 or execution.get("exit_code") != 0
                or execution.get("tool_mismatch") is not None
                or execution.get("artifact_hashes", {}).get("output/response.md") != row["response"]["sha256"]
                or execution.get("artifact_hashes", {}).get("input/task.md") != row["candidate_input"]["sha256"]
                or frozen.get("statement_sha256") != case["task_sha256"]
                or frozen.get("input_sha256") != row["candidate_input"]["sha256"]
                or frozen.get("rubric_sha256") != case["source_rubric"]["sha256"]
                or frozen.get("reference_sha256") != case["reference"]["sha256"]
                or not candidate_input.endswith(statement)
                or "prefix_verbatim" in frozen and candidate_input != frozen["prefix_verbatim"].encode() + statement
                or control.get("passed") is not True or control.get("mathematical_calls") != 0
                or any(control.get("report", {}).get(key) is not True for key in (
                    "work_file_roundtrip", "protected_open_denied", "tool_network_denied"))
                or control.get("plan_sha256") != row["original_test_plan"]["sha256"]
                or native_control.get("source_control_sha256") != hashlib.sha256(control_bytes).hexdigest()):
            raise ValueError("Written addition judgment differs from its original answer, rubric or native execution")
        criteria = source.get("criteria", [])
        if (len(criteria) != len(case["criteria"])
                or [{"criterion_id": c["id"], "points": c["max_points"]} for c in criteria] != case["criteria"]
                or any(type(c.get("points")) is not int or not 0 <= c["points"] <= c["max_points"] for c in criteria)
                or sum(c["points"] for c in criteria) != row["points"]):
            raise ValueError("Written addition credit differs from the retained criterion review")
        for criterion in criteria:
            for quote in criterion.get("evidence", []):
                if raw[quote["start"]:quote["end"]] != quote["quote"].encode():
                    raise ValueError("Written addition review quotes different original answer bytes")
        _validate_research_tool_evidence(root, row, execution, selected)
        for item in row.get("artifacts", []):
            evidence_bytes(root, item)
    return data


def load_written_replacement_inputs(root, record, *, policy=None):
    """Bind selected public replacement math and native evidence without editing legacy inputs."""
    if record.get("written_replacement_inputs") is None:
        return None
    from .written_replacements import validate_inputs
    data = json.loads(evidence_bytes(root, record["written_replacement_inputs"]))
    validate_inputs(data, data["policy"] if policy is None else policy)
    case = data["case_index"][0]
    task = evidence_bytes(root, case["original_task"])
    contract_raw = evidence_bytes(root, case["contract"])
    contract = json.loads(contract_raw)
    rubric = json.loads(evidence_bytes(root, case["source_rubric"]))
    reference = evidence_bytes(root, case["reference"])
    weights = [{"criterion_id": c["id"], "points": c["points"]} for c in contract["criteria"]]
    if (hashlib.sha256(task).hexdigest() != case["task_sha256"]
            or hashlib.sha256(contract_raw).hexdigest() != case["contract_sha256"]
            or contract.get("id") != case["case_id"] or contract.get("kind") != "written_proof"
            or weights != case["criteria"]
            or weights != [{"criterion_id": c["id"], "points": c["points"]} for c in rubric["criteria"]]
            or rubric.get("scale") != case["total_weight"]):
        raise ValueError("Written replacement changed its original task or criterion weights")
    row = data["slots"][0]
    if row["status"] == "not_run":
        return data
    execution = json.loads(evidence_bytes(root, row["execution"]))
    if row["status"] == "delivery_failed":
        if execution.get("status") == "completed":
            raise ValueError("A completed replacement cannot become missing delivery")
        return data
    raw = evidence_bytes(root, row["response"])
    source = json.loads(evidence_bytes(root, row["source_review"]))
    review = json.loads(evidence_bytes(root, row["review"]))
    frozen = json.loads(evidence_bytes(root, row["original_test_plan"]))
    candidate = evidence_bytes(root, row["candidate_input"])
    control_raw = evidence_bytes(root, row["original_capability_control"])
    control = json.loads(control_raw)
    checks = json.loads(evidence_bytes(root, row["actual_path_checks"]))
    adapter = json.loads(evidence_bytes(root, row["native_capability_control"]))
    if (review.get("schema") != "math-gauge.written-replacement-review/v1"
            or review.get("case_id") != case["case_id"] or review.get("stage") != "A1"
            or review.get("points") != row["points"] or review.get("complete") != row["complete"]
            or review.get("answer_sha256") != row["response"]["sha256"]
            or review.get("source_review_sha256") != row["source_review"]["sha256"]
            or source.get("answer_sha256") != row["response"]["sha256"]
            or source.get("rubric_sha256") != case["source_rubric"]["sha256"]
            or source.get("score") != row["points"] or source.get("strict_pass") != row["complete"]
            or source.get("total_points") != case["total_weight"]
            or frozen.get("statement_sha256") != case["task_sha256"]
            or frozen.get("rubric_sha256") != case["source_rubric"]["sha256"]
            or frozen.get("reference_sha256") != hashlib.sha256(reference).hexdigest()
            or frozen.get("input_sha256") != row["candidate_input"]["sha256"]
            or candidate != frozen["prefix_verbatim"].encode() + task
            or execution.get("kind") != "math" or execution.get("status") != "completed"
            or execution.get("request_count") != 1 or execution.get("exit_code") != 0
            or execution.get("tool_mismatch") is not None
            or execution.get("artifact_hashes", {}).get("output/response.md") != row["response"]["sha256"]
            or execution.get("artifact_hashes", {}).get("input/task.md") != row["candidate_input"]["sha256"]
            or control.get("passed") is not True or control.get("mathematical_calls") != 0
            or control.get("source_bytes_read") != 0
            or control.get("work_file_roundtrip") is not True or control.get("tool_network_denied") is not True
            or control.get("plan_sha256") != row["original_test_plan"]["sha256"]
            or checks.get("all_target_checks_passed") is not True
            or checks.get("target_count") != control.get("target_count")
            or len(checks.get("checks", [])) != control.get("target_count")
            or any(c.get("passed") is not True or c.get("open_allowed") is not False
                   for c in checks.get("checks", []))
            or adapter.get("source_control_sha256") != hashlib.sha256(control_raw).hexdigest()):
        raise ValueError("Written replacement lost its original answer, review or local-tool evidence")
    criteria = source.get("criteria", [])
    if (len(criteria) != len(weights)
            or [{"criterion_id": c["id"], "points": c["max_points"]} for c in criteria] != weights
            or any(type(c.get("points")) is not int or not 0 <= c["points"] <= c["max_points"] for c in criteria)
            or sum(c["points"] for c in criteria) != row["points"]):
        raise ValueError("Written replacement credit differs from frozen criteria")
    for criterion in criteria:
        for quote in criterion.get("evidence", []):
            if raw[quote["start"]:quote["end"]] != quote["quote"].encode():
                raise ValueError("Written replacement review quotes different answer bytes")
    _validate_research_tool_evidence(root, row, execution, data["policy"])
    for item in row.get("artifacts", []):
        evidence_bytes(root, item)
    return data


def validate_public_written_replacements(root, record):
    """Only public task/answer/review bytes and an opaque private native-source hash are exposed."""
    item = record.get("written_replacement_evidence")
    if item is None:
        return None
    data = json.loads(evidence_bytes(root, item))
    if (set(data) != {"schema", "public_case_ids", "source_inputs_sha256", "human_review", "formal_comparison_eligible", "slots"}
            or data.get("schema") != "math-gauge.written-replacements-public-evidence/v1"
            or data.get("public_case_ids") != ["MG-PS001"]
            or data.get("human_review") != "pending" or data.get("formal_comparison_eligible") is not False
            or not re.fullmatch(r"[0-9a-f]{64}", data.get("source_inputs_sha256", ""))
            or len(data.get("slots", [])) != 1):
        raise ValueError("Invalid public replacement evidence projection")
    row = data["slots"][0]
    if (set(row) != {"case_id", "attempt_label", "status", "response", "source_review", "points", "complete"}
            or row.get("case_id") != "MG-PS001" or row.get("attempt_label") != "A1"):
        raise ValueError("Public replacement evidence changed its selected task")
    if row.get("status") == "not_run":
        if any(row.get(k) is not None for k in ("response", "source_review", "points", "complete")):
            raise ValueError("Public unrun replacement must remain unknown")
    elif row.get("status") == "response_received":
        raw = evidence_bytes(root, row["response"])
        review = json.loads(evidence_bytes(root, row["source_review"]))
        if (review.get("answer_sha256") != hashlib.sha256(raw).hexdigest()
                or review.get("score") != row.get("points") or review.get("strict_pass") != row.get("complete")):
            raise ValueError("Public replacement score lost its original answer")
    elif row.get("status") != "delivery_failed":
        raise ValueError("Unknown public replacement status")
    return data


def validate_public_written_additions(root, record):
    """Public records expose only the additional private population and opaque hash."""
    if record.get("written_argument_evidence") is None:
        return None
    data = json.loads(evidence_bytes(root, record["written_argument_evidence"]))
    if (set(data) != {"schema", "private_cases", "source_inputs_sha256", "human_review", "formal_comparison_eligible"}
            or data["schema"] != "math-gauge.written-additions-public-evidence/v1"
            or data["private_cases"] != 1 or data["human_review"] != "pending"
            or data["formal_comparison_eligible"] is not False
            or not re.fullmatch(r"[0-9a-f]{64}", data["source_inputs_sha256"])):
        raise ValueError("Private written evidence crossed its aggregate-only public boundary")
    return data


PUBLIC_TASK_FIELDS = ("case_id", "completion", "strict_pass", "response_sha256", "review_sha256")


def public_assessment_case_ids(policy):
    """Current public membership, without exposing the private case inventory."""
    selection = policy["case_selection"]
    return sorted(set(selection["public_case_ids"])
        | set(selection.get("public_replacement_case_ids", []))
        | set(policy["theorem_extension"]["public_case_ids"])
        | set(policy["background_check"]["public_case_ids"])
        | set(policy.get("manuscript_completion", {}).get("public_case_ids", [])))


def project_public_task_view(score, public_ids, source_report_sha256):
    """Copy public task judgments from the shared scorer; never recompute points."""
    rows = [r for r in score["tasks"] if r["case_id"] in set(public_ids)]
    if len(rows) != len(public_ids) or {r["case_id"] for r in rows} != set(public_ids):
        raise ValueError("Public task projection differs from current selected membership")
    return {"source_report_sha256": source_report_sha256,
            "tasks": [{k: copy.deepcopy(r[k]) for k in PUBLIC_TASK_FIELDS}
                      for r in sorted(rows, key=lambda r: r["case_id"])]}


def load_public_task_scores(root, record, *, policy=None):
    """Bind public per-task views to the same canonical reports as combined totals."""
    items = [r for r in record.get("evidence", []) if r.get("path") == "public-task-scores.json"]
    if not items:
        return None
    if len(items) != 1:
        raise ValueError("Duplicate public task projection")
    data = json.loads(evidence_bytes(root, items[0]))
    policy = policy or json.loads(evidence_bytes(root, record["assessment_policy"]))
    public_ids = public_assessment_case_ids(policy)
    if (set(data) != {"schema", "benchmark_version", "model_label", "public_case_ids", "views",
                      "human_review", "formal_comparison_eligible"}
            or data["schema"] != "math-gauge.public-task-scores/v1"
            or data["benchmark_version"] != "0.6.0"
            or data["model_label"] != record["model"]["requested_label"]
            or data["public_case_ids"] != public_ids
            or data["human_review"] != "pending" or data["formal_comparison_eligible"] is not False
            or set(data["views"]) != {"capability", "partial", "strict"}):
        raise ValueError("Invalid public task projection identity or privacy boundary")
    groups = {"capability": "capability_results", "partial": "assessment_results", "strict": "strict_results"}
    for mode, conditions in data["views"].items():
        if set(conditions) != {"single_attempt", "nonlogical_retry_3"}:
            raise ValueError("Public task projection changed the two retained conditions")
        for condition, view in conditions.items():
            aggregate = json.loads(evidence_bytes(root, record[groups[mode]][condition]))
            if (set(view) != {"source_report_sha256", "tasks"}
                    or view["source_report_sha256"] != aggregate["source_bindings"]["private_report_sha256"]
                    or [r.get("case_id") for r in view["tasks"]] != public_ids):
                raise ValueError("Public task view differs from the canonical combined source")
            for row in view["tasks"]:
                if (set(row) != set(PUBLIC_TASK_FIELDS)
                        or (row["strict_pass"] is not None and type(row["strict_pass"]) is not bool)
                        or set(row["completion"]) != {"lower", "upper", "exact"}
                        or any(v is not None and (type(v) not in (int, float) or not -1 <= v <= 1)
                               for v in row["completion"].values())
                        or any(v is not None and not re.fullmatch(r"[0-9a-f]{64}", v)
                               for v in (row["response_sha256"], row["review_sha256"]))):
                    raise ValueError("Public task view contains unsupported fields or judgments")
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
    public_ids = set(public_assessment_case_ids(assessment))
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


def validate_native_delivery_failure(root, row):
    """Verify operational zero from an original first native ERROR, not math text."""
    source = row.get("source", {})
    data = json.loads(evidence_bytes(root, row["delivery_failure"]))
    execution = json.loads(evidence_bytes(root, data["native_execution"]))
    events = [json.loads(line) for line in evidence_bytes(root, data["native_events"]).splitlines()]
    terminal = json.loads(evidence_bytes(root, data["native_terminal_event"]))
    seal = json.loads(evidence_bytes(root, data["native_terminal_seal"]))
    original = json.loads(evidence_bytes(root, source["slot_record"]))
    candidate = evidence_bytes(root, source["candidate_input"])
    transport = evidence_bytes(root, data["native_request"])
    user_events = [json.loads(line) for line in transport.splitlines()]
    plan = json.loads(evidence_bytes(root, data["native_plan"]))
    native = [event for event in events if event.get("event") == "result"]
    if (data.get("schema") != "math-gauge.native-delivery-failure-adjudication/v1"
            or data.get("case_id") != row.get("case_id") or data.get("slot_id") != row.get("id")
            or data.get("post_observation") is not True or data.get("outcome") != "delivery_failed"
            or data.get("mathematical_judgment") != "not_adjudicated"
            or data.get("additional_mathematical_penalty") != 0
            or data.get("source_raw_bytes_rewritten") is not False
            or row.get("response") is not None or row.get("review") is not None
            or data.get("candidate_input") != source.get("candidate_input")
            or data.get("slot_record") != source.get("slot_record")
            or original.get("slot_id") != row.get("id") or original.get("case_id") != row.get("case_id")
            or original.get("started") is not True or original.get("status") != "execution_error"
            or original.get("response_sha256") is not None or original.get("locked_attempt") is not None
            or execution.get("kind") != "math" or execution.get("request_count") != 1
            or execution.get("stdin_bytes_written") != len(transport) or execution.get("stdin_write_calls") != 1
            or plan.get("client") != "agy" or plan.get("stdin_sha256") != hashlib.sha256(transport).hexdigest()
            or plan.get("prompt_sha256") != hashlib.sha256(candidate).hexdigest()
            or len(user_events) != 1 or user_events[0].get("event") != "user"
            or user_events[0].get("message", {}).get("content") != candidate.decode("utf-8")
            or execution.get("artifact_hashes", {}).get("input/task.md") != hashlib.sha256(candidate).hexdigest()
            or execution.get("artifact_hashes", {}).get("output/events.ndjson") != data["native_events"].get("sha256")
            or len(native) != 1 or native[0] != terminal or terminal.get("result", {}).get("status") != "ERROR"
            or seal.get("native_status") != "ERROR" or seal.get("normal_complete_delivery") is not False
            or seal.get("raw_terminal_sha256") != data["native_terminal_event"].get("sha256")
            or row.get("evaluation", {}).get("completion") != {"lower": 0, "upper": 0, "exact": 0}
            or row.get("evaluation", {}).get("strict_pass") is not False):
        raise ValueError("Operational delivery failure lacks its source-bound first native ERROR")
    for item in data.get("retained_failed_physical_requests", []):
        evidence_bytes(root, item)
    return data


def validate_current_written_reviews(root, record, *, policy, external=False):
    """Verify direct current-plan written A1 sources, without legacy supplements.

    Reuse the retained scoring input and each record's source/review descriptors.
    This is a byte/criterion check, not a new mathematical review or execution
    certificate. Legacy plans must keep their original supplemental contracts.
    """
    from .benchmarks import identity, validate_plan
    from .catalog import assessment_weights, candidate_message, validate_group_contract
    from .reliability_review import _validate_entry
    from .reliability import compose_material

    root = Path(root).resolve()
    items = [item for item in record.get("evidence", []) if item.get("path") == "scoring-inputs.json"]
    if len(items) != 1:
        raise ValueError("Direct current written reviews need retained scoring-input bytes")
    inputs = json.loads(evidence_bytes(root, items[0]))
    plan = validate_plan(inputs["plan"])
    data = plan["profile"]["data"]
    if data.get("schema") != "math-gauge.benchmark-profile/v6":
        raise ValueError("Legacy written evidence still requires its source-bound supplements")
    if (plan.get("runtime_frozen") is not True
            or inputs.get("model_label") != plan.get("model_label")
            or identity(data.get("assessment_policy")) != identity(policy)):
        raise ValueError("Direct written sources bind a different current plan or policy")
    cases = {case["case_id"]: case for case in plan["case_index"]
             if case["component"] in {"proofs", "exploration"}}
    child = next(child for child in policy["subcategories"] if child["id"] == "written-argument")
    private = {cid for cid, case in cases.items() if case.get("source_visibility") == "private"}
    if (len(cases) != child["public_tasks"] + (child["private_tasks"] if external else 0)
            or len(private) != (child["private_tasks"] if external else 0)):
        raise ValueError("Direct written sources must cover every current written A1 in their archive")
    slots = {row["slot_id"]: row for row in inputs["slots"]}
    rows = {row["id"]: row for row in record["records"]}
    for cid, case in cases.items():
        sid = cid + ":A1"
        row, scored = rows.get(sid), slots.get(sid)
        if (row is None or scored is None or row.get("case_id") != cid
                or scored.get("case_id") != cid or row.get("kind") != "independent"
                or row.get("parent_id") is not None):
            raise ValueError("Direct written sources need their own independent A1 record")
        source = row.get("source", {})
        # Both private compositions and public projections have a scoring index.
        # The original group import/review plan is a separate byte-bound identity.
        source_plan = source.get("scoring_plan_sha256", source.get("execution_plan_sha256"))
        if source_plan != plan["plan_sha256"]:
            raise ValueError("Direct written record belongs to a different source plan")
        original_plan = plan
        import_descriptor = source.get("standard_import_plan")
        if import_descriptor is not None:
            if not isinstance(import_descriptor, dict):
                raise ValueError("Direct written import plan needs a retained descriptor")
            original_plan = validate_plan(json.loads(evidence_bytes(root, import_descriptor)))
        elif source.get("execution_plan_sha256") != plan["plan_sha256"]:
            raise ValueError("Composed written sources need their original import plan bytes")
        original_case = next((item for item in original_plan["case_index"]
                              if item["case_id"] == cid), None)
        original_slot = next((item for item in original_plan["slots"]
                              if item["slot_id"] == sid), None)
        compared = ("version", "track", "task_kind", "contract_kind", "component",
                    "request_sha256", "candidate_message_sha256", "group_contract_sha256",
                    "family_id", "parent_family_id", "assessment_unit", "stages", "criteria",
                    "dimensions", "total_weight")
        if (original_plan["plan_sha256"] != source.get("execution_plan_sha256")
                or original_plan.get("runtime_frozen") is not True
                or original_plan.get("model_label") != plan.get("model_label")
                or identity(original_plan["profile"]["data"].get("assessment_policy")) != identity(policy)
                or original_case is None or any(original_case.get(key) != case.get(key) for key in compared)
                or original_slot is None or original_slot.get("selected") is not True
                or original_slot.get("case_id") != cid or original_slot.get("kind") != "independent"
                or original_slot.get("attempt_label") != "A1" or original_slot.get("parent_slot") is not None):
            raise ValueError("Direct written import plan changes its source case or A1 contract")
        if any(not isinstance(source.get(key), dict) for key in (
                "candidate_request", "candidate_input", "case_contract")):
            raise ValueError("Direct written records need original task and contract descriptors")
        request = json.loads(evidence_bytes(root, source["candidate_request"]))
        message = evidence_bytes(root, source["candidate_input"])
        contract_raw = evidence_bytes(root, source["case_contract"])
        contract = validate_group_contract(json.loads(contract_raw))
        if (request.get("case_id") != cid or request.get("case_version") != case["version"]
                or hashlib.sha256(json.dumps(request, ensure_ascii=False, sort_keys=True).encode()).hexdigest()
                   != case["request_sha256"]
                or message != candidate_message(request).encode()
                or hashlib.sha256(message).hexdigest() != case["candidate_message_sha256"]
                or hashlib.sha256(contract_raw).hexdigest() != case["group_contract_sha256"]
                or contract.get("id") != cid or contract.get("kind") != case["contract_kind"]
                or any(case.get(key) != value for key, value in assessment_weights(contract).items())):
            raise ValueError("Direct written task text or criterion contract differs from its frozen plan")
        if row.get("response") is None:
            if row.get("delivery_failure") is not None:
                validate_native_delivery_failure(root, row)
                if (scored.get("response_sha256") is not None or scored.get("review_sha256") is not None
                        or scored.get("strict_pass") is not False
                        or scored.get("completion") != {"lower": 0, "upper": 0, "exact": 0}):
                    raise ValueError("Known written delivery failure must retain operational zero")
                continue
            if (scored.get("response_sha256") is not None or row.get("review") is not None
                    or scored.get("review_sha256") is not None
                    or scored.get("strict_pass") is not None
                    or scored.get("completion") != {"lower": 0, "upper": 1, "exact": None}
                    or not row.get("missing_response_reason")):
                raise ValueError("Unreviewed direct written evidence must stay unknown")
            continue
        raw = evidence_bytes(root, row["response"])
        answer_hash = hashlib.sha256(raw).hexdigest()
        if not isinstance(row.get("review"), dict) or not isinstance(source.get("slot_record"), dict):
            raise ValueError("Direct written answers need their original criterion review")
        review = json.loads(evidence_bytes(root, row["review"]))
        original_slot = json.loads(evidence_bytes(root, source["slot_record"]))
        review_hash = identity({key: value for key, value in review.items() if key != "review_sha256"})
        binding = review.get("binding", {})
        if (review.get("schema") != "math-gauge.reliability-review/v1"
                or review.get("reviewer_kind") != "ai" or review.get("case_id") != cid
                or review.get("slot_id") != sid or review.get("review_sha256") != review_hash
                or scored.get("review_sha256") != review_hash or review.get("binding") != scored.get("binding")
                or binding.get("plan_sha256") != source.get("execution_plan_sha256")
                or binding.get("slot_id") != sid or binding.get("parent_slot") is not None
                or binding.get("response_sha256") != answer_hash
                or binding.get("request_sha256") != case["request_sha256"]
                or binding.get("group_contract_sha256") != case["group_contract_sha256"]
                or scored.get("response_sha256") != answer_hash
                or source.get("response_sha256") != answer_hash
                or scored.get("slot_record_sha256") != source["slot_record"]["sha256"]
                or original_slot.get("case_id") != cid or original_slot.get("slot_id") != sid
                or original_slot.get("response_sha256") != answer_hash):
            raise ValueError("Direct written review is not bound to this original A1 answer")
        # Only the archive-relative response path is relocated for this read-only
        # replay; the retained source-slot bytes and their hash remain unchanged.
        parsed_material = compose_material(next(item for item in original_plan["slots"]
                                               if item["slot_id"] == sid), raw)[0]
        if (original_slot.get("material_sha256") != parsed_material["material_sha256"]
                or original_slot.get("material", parsed_material) != parsed_material):
            raise ValueError("Direct written original material differs from the bound A1 bytes")
        replay_slot = dict(original_slot, response_path=row["response"]["path"], material=parsed_material)
        meta = {"plan": original_plan, "plan_sha256": source["execution_plan_sha256"],
                "inputs": {cid: {"request": source["candidate_request"]["path"],
                                 "contract": source["case_contract"]["path"]}}}
        result = _validate_entry(root, meta, {sid: replay_slot}, review)
        if (any(result.get(key) != scored.get(key) for key in (
                    "group_diagnostic", "completion", "strict_pass", "whole_math", "whole_strict", "focus_math"))
                or row.get("evaluation", {}).get("completion") != scored.get("completion")
                or row.get("evaluation", {}).get("strict_pass") != scored.get("strict_pass")):
            raise ValueError("Direct written credit differs from the original criterion review")
    return set(cases)


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
    direct_written = set()
    needs_direct = (external and assessment.get("written_argument_additions") is not None
                    and record.get("written_argument_inputs") is None
                    or assessment.get("written_argument_replacements") is not None
                    and record.get("written_replacement_inputs" if external else "written_replacement_evidence") is None)
    if needs_direct:
        direct_written = validate_current_written_reviews(root, record, policy=assessment, external=external)
    if assessment.get("written_argument_additions") is not None:
        key = "written_argument_inputs" if external else "written_argument_evidence"
        if record.get(key) is None and not (external and direct_written):
            raise ValueError("Current written additions require their retained source evidence")
    if assessment.get("written_argument_replacements") is not None:
        key = "written_replacement_inputs" if external else "written_replacement_evidence"
        required = {pair["case_id"] for pair in assessment["written_argument_replacements"]["replacements"]}
        if record.get(key) is None and not required <= direct_written:
            raise ValueError("Current written replacement requires source-bound evidence")
    if assessment.get("manuscript_completion") is not None:
        key = "manuscript_completion_inputs" if external else "manuscript_completion_evidence"
        if record.get(key) is None:
            raise ValueError("Current manuscript component requires its source-bound evidence")
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
            if direct_written:
                expected["current_written_scoring_inputs_sha256"] = root / "scoring-inputs.json"
            if record.get("theorem_extension_inputs") is not None:
                research = load_theorem_extension_inputs(root, record, policy=assessment.get("theorem_extension"))
                expected["theorem_extension_inputs_sha256"] = root / record["theorem_extension_inputs"]["path"]
            if record.get('background_check_inputs') is not None:
                load_background_check_inputs(root,record,policy=assessment.get('background_check'))
                expected['background_check_inputs_sha256']=root/record['background_check_inputs']['path']
            if record.get("written_argument_inputs") is not None:
                load_written_argument_inputs(root, record, policy=assessment.get("written_argument_additions"))
                expected["written_argument_inputs_sha256"] = root / record["written_argument_inputs"]["path"]
            if record.get("written_replacement_inputs") is not None:
                load_written_replacement_inputs(root, record, policy=assessment.get("written_argument_replacements"))
                expected["written_replacement_inputs_sha256"] = root / record["written_replacement_inputs"]["path"]
            if record.get("manuscript_completion_inputs") is not None:
                load_manuscript_completion_inputs(root, record, policy=assessment.get("manuscript_completion"))
                expected["manuscript_completion_inputs_sha256"] = root / record["manuscript_completion_inputs"]["path"]
            if any(bindings.get(key) != hashlib.sha256(path.read_bytes()).hexdigest()
                   for key, path in expected.items()):
                raise ValueError("Current score binds different source judgments")
        else:
            if score != project_assessment_score(score):
                raise ValueError("Current public score must contain only projected aggregates")
            written = validate_public_written_additions(root, record)
            if (written is not None and bindings.get("current_written_scoring_inputs_sha256",
                                                    bindings.get("written_argument_inputs_sha256"))
                    != written["source_inputs_sha256"]):
                raise ValueError("Public written aggregate binds a different private input source")
            replacement = validate_public_written_replacements(root, record)
            if (replacement is not None and bindings.get("written_replacement_inputs_sha256")
                    != replacement["source_inputs_sha256"]):
                raise ValueError("Public written replacement binds a different source input")
            manuscript = validate_public_manuscript_completion(root, record)
            if (manuscript is not None and manuscript["private_cases"]
                    != assessment["manuscript_completion"]["private_cases"]):
                raise ValueError("Public manuscript evidence changed its fixed family population")
            if (manuscript is not None and bindings.get("manuscript_completion_inputs_sha256")
                    != manuscript["source_inputs_sha256"]):
                raise ValueError("Public manuscript aggregate binds a different private source")
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
        if case.get("source_kind") == "not_available":
            evidence = json.loads(evidence_bytes(root, case["unavailable_evidence"]))
            rows = {item["slot_id"]: item for item in inputs["slots"]}
            original = rows[case["slot_id"]]
            source_slot = json.loads(evidence_bytes(root, case["source_slot_record"]))
            failed = case.get("delivery_status") == "delivery_failed"
            if (evidence.get("schema") != "math-gauge.unavailable-engineering-evidence/v1"
                    or evidence.get("case_id") != case["case_id"]
                    or evidence.get("slot_id") != case["slot_id"]
                    or evidence.get("delivery_status") != case.get("delivery_status")
                    or evidence.get("slot_record_sha256") != original.get("slot_record_sha256")
                    or case["source_slot_record"].get("sha256") != original.get("slot_record_sha256")
                    or source_slot.get("case_id") != case["case_id"]
                    or source_slot.get("slot_id") != case["slot_id"]
                    or source_slot.get("started") is not failed
                    or source_slot.get("status") != ("execution_error" if failed else "not_run")
                    or source_slot.get("response_sha256") is not None or source_slot.get("locked_attempt") is not None
                    or (not failed and source_slot.get("attempts") != [])
                    or (failed and not source_slot.get("attempts"))
                    or evidence.get("original_response_sha256") is not None
                    or evidence.get("mathematical_judgment") != "not_adjudicated"
                    or case.get("source_manifest") is not None or case.get("kernel_report") is not None
                    or case.get("source_files") != {}):
                raise ValueError("Unavailable engineering evidence lost its original slot disposition")
            if failed:
                digest = evidence.get("native_failure_adjudication_sha256")
                if (not isinstance(digest, str) or len(digest) != 64
                        or any(char not in "0123456789abcdef" for char in digest)):
                    raise ValueError("Missing engineering delivery failure needs its private native ERROR adjudication")
            continue
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


def validate_unavailable_engineering_native_bindings(root, record, review, *, engineering_root):
    """Cross-bind public absence projections to private original slot/ERROR bytes."""
    rows = {row["id"]: row for row in record["records"]}
    for case in review["cases"]:
        if case.get("source_kind") != "not_available":
            continue
        row = rows.get(case["slot_id"], {})
        source = row.get("source", {})
        original = json.loads(evidence_bytes(root, source["slot_record"]))
        unavailable = json.loads(evidence_bytes(engineering_root, case["unavailable_evidence"]))
        failed = case.get("delivery_status") == "delivery_failed"
        if (row.get("delivery_status") != case.get("delivery_status") or row.get("response") is not None
                or source["slot_record"].get("sha256") != case["source_slot_record"].get("sha256")
                or original.get("started") is not failed
                or original.get("status") != ("execution_error" if failed else "not_run")
                or original.get("response_sha256") is not None or original.get("locked_attempt") is not None):
            raise ValueError("Unavailable engineering projection changed its private original slot")
        if failed:
            validate_native_delivery_failure(root, row)
            if unavailable.get("native_failure_adjudication_sha256") != row["delivery_failure"]["sha256"]:
                raise ValueError("Unavailable engineering projection binds another native ERROR adjudication")
        elif row.get("delivery_failure") is not None or original.get("attempts") != []:
            raise ValueError("Unrun engineering projection hid a native attempt")


def load_content_rates(root, record=None):
    """Read optional aggregate-only supplemental rates tied to this exact archive."""
    from .content_rates import validate_public_rates

    root = Path(root).resolve()
    path = root / 'content-rates.json'
    if not path.exists():
        return None
    record = record or json.loads((root / 'record.json').read_bytes())
    report = validate_public_rates(json.loads(path.read_bytes()))
    current = report['version'] == '0.2.0'
    source = record['assessment_results']['nonlogical_retry_3']
    expected = {
        'record_sha256': hashlib.sha256((root / 'record.json').read_bytes()).hexdigest(),
        'assessment_result_sha256': hashlib.sha256(evidence_bytes(root, source)).hexdigest(),
        'assessment_policy_sha256': hashlib.sha256(evidence_bytes(root, record['assessment_policy'])).hexdigest(),
        'method_policy_sha256': hashlib.sha256((root / ('goal-attainment-policy.json' if current
                                                       else 'content-rate-policy.json')).read_bytes()).hexdigest(),
    }
    if current:
        # Portable anonymous reports keep the original content review opaque;
        # source verification of its private bytes belongs to the evaluator run.
        expected.update(content_review_sha256=report['private_review_sha256'],
            content_method_policy_sha256=hashlib.sha256((root / 'content-rate-policy.json').read_bytes()).hexdigest())
    if report['source_bindings'] != expected or report['model_id'] != root.parent.name:
        raise ValueError('Content rates bind a different retained record, score or policy')
    return report


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
        if row.get("delivery_failure") is not None:
            validate_native_delivery_failure(root, row)
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
    load_written_argument_inputs(root, record)
    validate_public_written_additions(root, record)
    load_written_replacement_inputs(root, record)
    validate_public_written_replacements(root, record)
    load_manuscript_completion_inputs(root, record)
    validate_public_manuscript_completion(root, record)
    load_public_task_scores(root, record)
    if validate_scores:
        load_content_rates(root, record)
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
        if location == "public_archive":
            validate_unavailable_engineering_native_bindings(root, record, review, engineering_root=source_root)
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
