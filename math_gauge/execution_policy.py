"""Versioned execution conditions, separate from mathematical task requirements.

Omitting the opt-in preserves the historical no-tool context exactly. A tool
permission never adds a requirement to use it or changes a supplied Lean task.
This pure owner is embedded in portable controllers from the same source.
"""

import hashlib

NO_TOOLS_TRACK = "math-gauge.no-tools/v1"
LOCAL_TOOLS_TRACK = "math-gauge.local-tools-no-search/v1"
LOCAL_TOOL_IDS = ("exec_command", "write_stdin", "apply_patch")
FOLLOWUP_PROMPT_PROJECTION = "math-gauge.followup-permission-projection/v1"
SOURCE_FOLLOWUP_PERMISSION = "本轮不能调用工具或查询外部资料。"
LOCAL_FOLLOWUP_PERMISSION = "本轮不得访问网络或进行联网检索。"


def validate_case_execution_policy(data, case_components):
    """Only v5 opts into a declared mixed-condition development composition."""
    policy = data.get("case_execution_policy")
    if policy is None:
        return None
    if (data.get("schema") not in {"math-gauge.benchmark-profile/v5", "math-gauge.benchmark-profile/v6"}
            or not isinstance(policy, dict)
            or policy.get("schema") not in {"math-gauge.case-execution-policy/v1",
                                            "math-gauge.case-execution-policy/v2"}
            or policy.get("post_observation") is not True
            or policy.get("require_terminal_ok") is not True):
        raise ValueError("Mixed execution conditions require the explicit v5 development policy")
    fresh = {cid for cid, component in case_components.items()
             if component in {"lean-audit", "lean-formalization"}}
    retained = set(case_components) - fresh
    tracks = policy.get("case_tracks", {})
    if (not isinstance(tracks, dict) or set(tracks) != set(case_components)
            or any(track not in {NO_TOOLS_TRACK, LOCAL_TOOLS_TRACK} for track in tracks.values())
            or any(tracks[cid] != LOCAL_TOOLS_TRACK for cid in fresh)
            or set(policy.get("new_execution_case_ids", [])) != fresh
            or set(policy.get("retain_source_runtime_case_ids", [])) != retained
            or type(policy.get("new_turn_timeout_seconds")) is not int
            or policy["new_turn_timeout_seconds"] <= 0):
        raise ValueError("Case execution conditions must partition the fixed components without drift")
    overrides = policy.get("new_case_turn_timeout_seconds", {})
    if policy["schema"] == "math-gauge.case-execution-policy/v1":
        if "new_case_turn_timeout_seconds" in policy:
            raise ValueError("Per-case turn budgets require the explicit v2 execution policy")
    elif (policy["new_turn_timeout_seconds"] != 5400
          or not isinstance(overrides, dict)
          or set(overrides) != {"MG-C003"}
          or type(overrides["MG-C003"]) is not int
          or overrides["MG-C003"] != 10800
          or "MG-C003" not in fresh):
        raise ValueError("The v2 future budget changes only MG-C003 to 10800 seconds")
    return policy


def declared_case_timeout_seconds(data, cid):
    """Required new-turn budget; retained source conditions have no override.

    Read only the selected profile, never a process-global current policy. A
    frozen v1 profile therefore keeps its original 5400-second C003 budget.
    Native and broker limits must be set and evidenced by the actual adapter;
    this selector also supplies the outer runner/export compatibility check.
    """
    policy = data.get("case_execution_policy")
    if policy is None or cid not in policy["new_execution_case_ids"]:
        return None
    return policy.get("new_case_turn_timeout_seconds", {}).get(
        cid, policy["new_turn_timeout_seconds"])


def declared_case_context(data, cid, fallback):
    policy = data.get("case_execution_policy")
    if policy is None:
        return fallback
    track = policy["case_tracks"][cid]
    return execution_context({"execution_track": track}) if track == LOCAL_TOOLS_TRACK else execution_context()


def execution_context(runtime=None):
    if runtime is not None and not isinstance(runtime, dict):
        raise ValueError("Execution runtime must be an object")
    runtime = {} if runtime is None else runtime
    explicit = "execution_track" in runtime
    track = runtime.get("execution_track")
    if explicit and track not in {LOCAL_TOOLS_TRACK, "benchmark.local-tools-no-search/v1"}:
        raise ValueError("Unknown execution track")
    context = {"independent": "fresh", "followup": "branch-history-only",
               "external_correctness_feedback": False, "tools_allowed": []}
    if explicit:
        projection = ("benchmark.followup-permission-projection/v1"
                      if track.startswith("benchmark.") else FOLLOWUP_PROMPT_PROJECTION)
        context.update(execution_track=track, tools_allowed=list(LOCAL_TOOL_IDS),
                       tool_network_access=False, search_allowed=False,
                       local_tool_feedback_allowed=True,
                       followup_prompt_projection=projection)
    return context


def validate_context_policy(context):
    if not isinstance(context, dict):
        raise ValueError("Execution context policy must be an object")
    runtime = {"execution_track": context["execution_track"]} if "execution_track" in context else None
    expected = execution_context(runtime)
    if set(context) != set(expected) or any(
            type(context[key]) is not type(value) or context[key] != value for key, value in expected.items()):
        raise ValueError("Unexpected candidate context policy")
    return context


def execution_condition(context):
    validate_context_policy(context)
    if "execution_track" not in context:
        return {"track": NO_TOOLS_TRACK, "label": "No candidate tools"}
    return {"track": context["execution_track"],
            "label": "Local tools permitted; search and tool networking disabled; original task requirements unchanged",
            "followup_prompt_projection": context["followup_prompt_projection"]}


def project_followup_prompt(source, context):
    """Derive only the declared permission suffix; never mutate frozen source rows."""
    validate_context_policy(context)
    if not isinstance(source, dict) or not isinstance(source.get("content"), str):
        raise ValueError("Followup prompt source must contain text")
    content = source["content"]
    source_hash = hashlib.sha256(content.encode("utf-8")).hexdigest()
    if source.get("content_sha256") != source_hash:
        raise ValueError("Followup prompt source hash changed")
    result = dict(source)
    if "followup_prompt_projection" not in context:
        return result
    if {"source_content_sha256", "projection_version"} & set(source):
        raise ValueError("Followup prompt source is already projected")
    suffix = SOURCE_FOLLOWUP_PERMISSION + "\n"
    if content.count(SOURCE_FOLLOWUP_PERMISSION) != 1 or not content.endswith(suffix):
        raise ValueError("Unrecognized followup prompt permission suffix")
    projected = content[:-len(suffix)] + LOCAL_FOLLOWUP_PERMISSION + "\n"
    result.update(content=projected,
                  content_sha256=hashlib.sha256(projected.encode("utf-8")).hexdigest(),
                  source_content_sha256=source_hash,
                  projection_version=context["followup_prompt_projection"])
    return result
