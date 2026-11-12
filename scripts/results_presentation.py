"""Browser projections of retained display values; no scoring or evidence loading."""
import copy

SCHEMA = "math-gauge.browser-presentation/v1"


def pick(value, keys):
    return {key: copy.deepcopy(value[key]) for key in keys if key in (value or {})}


def result_view(result, *, model_page=False):
    metrics = ("earned", "overall", "lean-selfcheck") if model_page else ("earned",)
    view = {"metrics": pick(result["metrics"], metrics),
            "contributions": copy.deepcopy(result["contributions"])}
    if result.get('submission_summary') is not None:
        view['submission_summary'] = pick(result['submission_summary'],
            ('planned','active_final','forced_content','blank','pending','pending_original_record_review'))
    if model_page:
        view["claim_penalties"] = pick(result.get("claim_penalties"),
            ("findings_by_severity", "core_endorsement_tasks"))
        view["strict_alignment_selfcheck"] = pick(result.get("strict_alignment_selfcheck"), ("strict_pass",))
        if result.get('alignment_selfcheck') is not None:
            trajectory = result['alignment_selfcheck']
            view['alignment_selfcheck'] = {
                'rounds':[pick(row,('complete','submission_classification','delivery_verified')) for row in trajectory['rounds']],
                'major_false_complete_events':pick(trajectory['major_false_complete_events'],('count',))}
        if result.get('lean_formalization_breakdown') is not None:
            view['lean_formalization_breakdown'] = {'cases':[
                pick(row,('case_id','status','complete_count','total','submission_classification'))
                for row in result['lean_formalization_breakdown']['cases']]}
    return view


def model_view(model, *, model_page=False):
    view = pick(model, ("id", "label", "short_label", "theme", "logo", "harness_display_name",
                        "fully_evaluated", "answer_delivery", "evaluation_progress"))
    view["harness"] = pick(model.get("harness"), ("name",))
    view["combined"] = result_view(model["combined"], model_page=model_page)
    view["retry"] = {"combined": result_view(model["retry"]["combined"], model_page=model_page)}
    for mode in ("capability", "strict"):
        view[mode] = {condition: result_view(result, model_page=model_page)
                      for condition, result in model[mode].items()}
    if model.get('answer_delivery', {}).get('source_review_status') == 'complete':
        retained_views = [view['combined'], view['retry']['combined'],
                          *view['capability'].values(), *view['strict'].values()]
        for result in retained_views:
            if result.get('submission_summary') is not None:
                result['submission_summary']['pending_original_record_review'] = 0
    if model_page:
        alignment = model["alignment_selfcheck"]
        view["alignment_selfcheck"] = {
            "rounds": [pick(item, ("complete",)) for item in alignment["rounds"]],
            "major_false_complete_events": pick(alignment["major_false_complete_events"], ("count",))}
        view["trajectory"] = pick(model["trajectory"], ("state",))
        view["lean_formalization_breakdown"] = {"cases": [
            pick(item, ("case_id", "status", "complete_count", "total"))
            for item in model["lean_formalization_breakdown"]["cases"]]}
        view["public_claims"] = {condition: [
            {"case_id": claim["case_id"], "findings": [pick(finding, ("reason",))
             for finding in claim["findings"]]} for claim in claims]
            for condition, claims in model["public_claims"].items()}
    else:
        rates = model.get("content_rates")
        view["content_rates"] = None if rates is None else {"metrics": {
            "reliability": pick(rates["metrics"]["reliability"], ("observed",)),
            "attainment": pick(rates["metrics"].get("attainment"), ("confirmed",))}}
    return view


def project_payload(data):
    """Copy exactly the values consumed by each page's runtime, including unknown bounds."""
    shared = pick(data, ("schema", "benchmark_version", "default_score_mode", "score_modes",
                         "default_attempt_condition", "display_score_modes"))
    shared["source_schema"] = shared["schema"]
    shared["schema"] = SCHEMA
    shared["policy"] = {
        "groups": [pick(group, ("id", "title", "weight", "children"))
                   for group in data["policy"]["groups"]],
        "subcategories": [pick(item, ("id", "title", "weight", "status"))
                          for item in data["policy"]["subcategories"]]}
    if "case" in data:
        case = data["case"]
        shared["model"] = pick(data["model"], ("id", "label"))
        shared["case"] = {**pick(case, ("id", "title", "category")), "views": {
            mode: {condition: pick(view, ("completion", "strict_pass", "response_sha256", "review_sha256"))
                   for condition, view in views.items()} for mode, views in case["views"].items()}}
    elif "model" in data:
        shared["model"] = model_view(data["model"], model_page=True)
        shared["cases"] = [{**pick(item, ("id", "title", "category_title")), "views": {
            mode: {condition: pick(view, ("completion", "strict_pass"))
                   for condition, view in views.items()} for mode, views in item["views"].items()}}
            for item in data["cases"]]
    elif "models" in data:
        shared["models"] = [model_view(model) for model in data["models"]]
        shared["category_leaderboards"] = [pick(board, ("id", "views"))
                                            for board in data["category_leaderboards"]]
        shared["gap_diagnostics"] = {"tables": [{"id": table["id"], "rows": [
            pick(row, ("model_id", "value")) for row in table["rows"]]}
            for table in data["gap_diagnostics"]["tables"]]}
        shared["manuscript_observations"] = {"models": [{"id": model["id"], "observation": {
            "counts": pick(model["observation"]["counts"], ("total_groups",))}}
            for model in data["manuscript_observations"]["models"]]}
    return shared
