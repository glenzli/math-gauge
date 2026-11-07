"""Current public/combined assessment projections shared by case adopters. No inference."""
import copy, hashlib, json, os, tempfile, sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from math_gauge.catalog import Suite
from math_gauge.theorem_extension import validate_policy

def load(path): return json.loads(Path(path).read_bytes())
def write(path,value):
    path=Path(path);path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(json.dumps(value,ensure_ascii=False,indent=2,allow_nan=False)+'\n')
def digest(path): return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def configure_current(private_root, config, public, private):
    """Refresh current projections; frozen historical inputs are not rewritten."""
    extension = validate_policy(load(ROOT / "protocol/theorem-extension-policy.json"))
    background_path=ROOT/"protocol/background-check-policy.json"
    background=load(background_path) if background_path.exists() else None
    written_path = ROOT / "protocol/written-additions-policy.json"
    written = load(written_path) if written_path.exists() else None
    public_count, private_count = len(public.cases), len(private.cases)
    total_count = public_count + private_count
    policy = load(ROOT / "protocol/scoring-policy.json")
    policy["version"] = "0.8.0"
    policy.update(score_modes=["capability", "partial", "strict"], default_score_mode="partial",
                  capability_policy_version="0.2.0", claim_penalty_policy_version="0.1.0", score_mode_catalog_version="0.1.0")
    policy["theorem_extension"] = extension
    if written is not None:
        from math_gauge.written_additions import validate_policy as validate_written_policy
        validate_written_policy(written)
        policy["written_argument_additions"] = written
        selection = load(ROOT / "protocol/case-selection.json")
        policy["case_selection"] = {key: selection[key] for key in policy["case_selection"]}
        next(c for c in policy["subcategories"] if c["id"] == "written-argument").update(
            private_tasks=3 + written["private_cases"], families=11 + written["families"])
    if background is not None:
        policy["background_check"]=background
        next(c for c in policy["subcategories"] if c["id"]=="background-check").update(
            source_components=["background-check"],public_tasks=2,private_tasks=2,families=4,status="active")
    leaf = next(c for c in policy["subcategories"] if c["id"] == "theorem-extension")
    leaf.update(source_components=["theorem-extension"], public_tasks=len(extension["public_case_ids"]),
                private_tasks=extension["private_cases"], families=extension["families"], status="active")
    policy["scope"].update(public_tasks=public_count, private_tasks=private_count, tasks=total_count,
                           parent_families=19 + extension["families"] + (4 if background else 0) + (written["families"] if written else 0),
                           initial_slots=total_count, public_initial_slots=public_count)
    write(ROOT / "protocol/scoring-policy.json", policy)
    profile = load(ROOT / "protocol/benchmark-profile.json")
    profile["suite"]["sha256"] = public.sha256
    profile["assessment_policy"] = policy
    extension_ids=list(extension["public_case_ids"])
    background_ids=[] if background is None else list(background["public_case_ids"])
    ids=extension_ids+background_ids
    profile["components"] = [row for row in profile["components"] if row["id"] not in {"theorem-extension","background-check"}]
    profile["components"].append({"id": "theorem-extension", "title": "命题拓展", "case_ids": extension_ids,
                                  "weight": 10, "aggregation": "family"})
    if background is not None:
        profile["components"].append({"id":"background-check","title":"背景核查",
            "case_ids":background_ids,"weight":10,"aggregation":"family"})
    execution = profile["case_execution_policy"]
    # Current formal tests share one permission policy; historical native evidence is immutable.
    for cid in public.cases:
        execution["case_tracks"][cid] = "math-gauge.local-tools-no-search/v1"
    for cid in ids:
        execution["case_tracks"][cid] = "math-gauge.local-tools-no-search/v1"
        if cid not in execution["retain_source_runtime_case_ids"]:
            execution["retain_source_runtime_case_ids"].append(cid)
        profile["attempt_schedule"][cid] = ["A1"]
    write(ROOT / "protocol/benchmark-profile.json", profile)
    edition = load(ROOT / "benchmark.json")
    edition["public"].update(suite_sha256=public.sha256, tasks=public_count, standard_slots=public_count)
    edition["private"].update(suite_sha256=private.sha256, tasks=private_count, standard_slots=private_count)
    edition["combined"].update(tasks=total_count, standard_slots=total_count)
    edition["profile"]["sha256"] = digest(ROOT / edition["profile"]["path"])
    edition["scoring_policy"].update(version=policy["version"], sha256=digest(ROOT / "protocol/scoring-policy.json"))
    edition["score_capacity"].update(active=90 if background else 80, under_construction=10 if background else 20)
    edition["theorem_extension_policy"] = {"path": "protocol/theorem-extension-policy.json", "version": extension["version"],
                                           "sha256": digest(ROOT / "protocol/theorem-extension-policy.json")}
    for key, filename in (("result_record_contract", "protocol/result-record.md"),
                          ("result_record_schema", "protocol/result-record.schema.json")):
        edition[key]["sha256"] = digest(ROOT / filename)
    if background is not None:
        edition["background_check_policy"]={"path":"protocol/background-check-policy.json",
            "version":background["version"],"sha256":digest(background_path)}
    if written is not None:
        edition["written_additions_policy"] = {"path": "protocol/written-additions-policy.json",
            "version": written["version"], "sha256": digest(written_path)}
        edition["case_selection"].update(version=selection["version"], sha256=digest(ROOT / "protocol/case-selection.json"))
    write(ROOT / "benchmark.json", edition)
    release_path = ROOT / "releases/v0.6.0/config.json"
    release = load(release_path)
    release.update(case_count=len(public.cases), slot_count=len(public.cases))
    write(release_path, release)
    private_edition = load(private_root / "benchmark.json")
    private_edition.update(benchmark_version="0.6.0", case_count=private_count, standard_slots=private_count,
                           combined_standard_slots=total_count, scoring_method_version=policy["version"])
    private_edition.pop("version", None)
    private_edition.pop("tasks", None)
    private_edition["theorem_extension"] = {"public_cases": len(extension["public_case_ids"]),
        "private_cases": extension["private_cases"], "policy_version": extension["version"],
        "formal_attempts": ["A1"], "research_invitation": False, "scoring_method": policy["version"]}
    private_edition["suite_sha256"] = private.sha256
    private_edition["score_capacity"].update(active=90 if background else 80, under_construction=10 if background else 20)
    private_edition["case_selection"]["source"] = (
        f"shared20-public/3-private frozen legacy selection plus{len(extension['public_case_ids'])}-public/"
        f"{extension['private_cases']}-private theorem extension, "
        f"{4 if background else 0} background checks and {written['private_cases'] if written else 0} added private written arguments")
    if written is not None:
        private_edition["case_selection"]["version"] = selection["version"]
        private_edition["written_argument_additions"] = {"private_cases": written["private_cases"],
            "policy_version": written["version"], "formal_attempts": ["A1"]}
    if background is not None:
        private_edition["background_check"]={"public_cases":2,"private_cases":2,"families":4,
            "policy_version":background["version"],"formal_attempts":["A1"]}
    write(private_root / "benchmark.json", private_edition)

    from scripts import catalog
    taxonomy = load(ROOT / "cases/taxonomy.json")
    for suite in taxonomy["source_suites"]:
        suite.update(suite_sha256=public.sha256, paper_count=len(public.cases))
    _, sources = catalog.load_sources(ROOT, taxonomy)
    taxonomy["scope"].update(paper_count=len(sources),
        written_proof_papers=sum(s["contract"]["kind"] == "written_proof" for s in sources.values()),
        proof_criteria=sum(len(s["contract"].get("criteria", [])) for s in sources.values()))
    taxonomy["paper_assignments"] = [a for a in taxonomy["paper_assignments"] if a["case_id"] not in ids]
    for cid in ids:
        source = sources[cid]
        focus_ids = ["F04", "F06", "F01"] if cid in background_ids else (["F06", "F01", "F04"] if cid == extension_ids[0] else ["F06", "F07", "F04"])
        criterion="complete-correction" if cid in background_ids else "complete-structure"
        taxonomy["paper_assignments"].append({"case_id": cid, "version": source["case"]["version"],
            "source_bindings": source["source_bindings"],
            "focus": [{"focus_id": fid, "role": "primary" if i == 0 else "secondary",
                "evidence": [{"criterion_id": criterion,
                    "note": "只按首答实际交付核验构造与结构、适用条件和严格结论；接受有效替代路线。",
                    "contract_pointer": "/criteria/2/required_evidence",
                    "task_locator": {"path": source["paths"]["task"], "line": 1,
                                      "applies_to": "whole-paper"}}]} for i, fid in enumerate(focus_ids)],
            "classification_review": {"status": "ai-reviewed", "human": "pending"}})
    write(ROOT / "cases/taxonomy.json", taxonomy)
    index, document = catalog.build(ROOT)
    write(ROOT / "cases/catalog.json", index)
    (ROOT / "cases/by-focus.md").write_text(document)
    (ROOT / "cases/README.md").write_text(catalog.render_index(index))

    packet = ROOT / "protocol/reliability"
    selection = load(packet / "selection.json")
    selection["source_suite_sha256"] = public.sha256
    write(packet / "selection.json", selection)
    schedule = load(packet / "schedule.json")
    for cid in ids:
        if not any(row["case_id"] == cid for row in schedule["slots"]):
            schedule["slots"].append({"ordinal_per_model": len(schedule["slots"]) + 1,
                "slot_id": cid + ":A1", "case_id": cid, "kind": "independent", "attempt_label": "A1",
                "context": "fresh", "parent_slot": None, "message_id": None,
                "status": "planned", "response_sha256": None, "grade": None})
    write(packet / "schedule.json", schedule)
    plan = load(packet / "plan.json")
    plan["planned_slots_per_model"] = public_count
    plan["assessment_method_version"] = policy["version"]
    plan["attempt_schedule"] = {cid: ["A1"] for cid in public.cases}
    from scripts.validate_protocol import check_candidate
    with tempfile.TemporaryDirectory(prefix="math-gauge-adoption-projection-") as temporary:
        plan["cases"] = [check_candidate(public, case, Path(temporary) / cid,
                                          selected_ids=plan["repeat_case_ids"])
                         for cid, case in public.cases.items()]
    for item in plan.get("suites", []):
        if "sha256" in item:
            item["sha256"] = public.sha256
        if "suite_sha256" in item:
            item["suite_sha256"] = public.sha256
        if "paper_count" in item:
            item["paper_count"] = public_count
        if isinstance(item.get("cases"), int):
            item["cases"] = public_count
    plan["design_bindings"]["schedule_sha256"] = digest(packet / "schedule.json")
    write(packet / "plan.json", plan)
    configure_combined(private_root, profile, public, private)


def configure_combined(private_root, public_profile, public, private):
    """Keep the companion's current profile bound to the complete A1 pool."""
    from math_gauge.benchmarks import BenchmarkProfile, build_plan
    protocol = private_root / "protocol"
    composition = {"schema": "math-gauge.suite-composition/v1", "id": "math-gauge-combined",
        "version": "0.6.0", "suites": [{"path": os.path.relpath(s.root, protocol),
            "id": s.metadata["id"], "version": s.metadata["version"], "sha256": s.sha256}
            for s in (public, private)]}
    write(protocol / "suite-composition.json", composition)
    suite = Suite.load(protocol / "suite-composition.json")
    profile = copy.deepcopy(public_profile)
    profile["id"] = "math-gauge-assessment-combined"
    profile["suite"] = {"id": suite.metadata["id"], "version": suite.metadata["version"], "sha256": suite.sha256}
    for cid, case in private.cases.items():
        component = next((name for name in ("theorem-extension", "background-check")
                          if private.case_manifest(cid).startswith(name + "/")), "proofs")
        next(c for c in profile["components"] if c["id"] == component)["case_ids"].append(cid)
        profile["attempt_schedule"][cid] = ["A1"]
        profile["case_execution_policy"]["case_tracks"][cid] = "math-gauge.local-tools-no-search/v1"
        profile["case_execution_policy"]["retain_source_runtime_case_ids"].append(cid)
    for name in ("lean-tool-budget-policy.json", "scoring-policy.json", "strict-scoring-policy.json"):
        (protocol / name).write_bytes((ROOT / "protocol" / name).read_bytes())
    packet = protocol / "reliability"
    packet.mkdir(exist_ok=True)
    selection = load(ROOT / "protocol/reliability/selection.json")
    selection["source_suite_sha256"] = suite.sha256
    write(packet / "selection.json", selection)
    write(packet / "prompts.json", load(ROOT / "protocol/reliability/prompts.json"))
    schedule = load(ROOT / "protocol/reliability/schedule.json")
    for cid in private.cases:
        schedule["slots"].append({"ordinal_per_model": len(schedule["slots"]) + 1,
            "slot_id": cid + ":A1", "case_id": cid, "kind": "independent", "attempt_label": "A1",
            "context": "fresh", "parent_slot": None, "message_id": None,
            "status": "planned", "response_sha256": None, "grade": None})
    write(packet / "schedule.json", schedule)
    write(protocol / "benchmark-profile.json", profile)
    loaded = BenchmarkProfile.load(protocol / "benchmark-profile.json", suite)
    plan = build_plan(loaded, suite)
    expected_slots = len(public.cases) + len(private.cases)
    if len(plan["slots"]) != expected_slots or any(row["attempt_label"] != "A1" for row in plan["slots"]):
        raise ValueError("The current combined profile must contain every selected independent A1 slot only")
    edition = load(private_root / "benchmark.json")
    edition["composition"] = {"path": "protocol/suite-composition.json", "suite_sha256": suite.sha256,
                               "tasks": expected_slots, "sha256": digest(protocol / "suite-composition.json")}
    edition["profile"] = {"path": "protocol/benchmark-profile.json",
                          "sha256": digest(protocol / "benchmark-profile.json"), "scope": "combined"}
    write(private_root / "benchmark.json", edition)

