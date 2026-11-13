"""Join public total-cost observations with source-owned scores and sample clocks."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path

from math_gauge.costs import PUBLIC_SCHEMA, pareto_frontier
from math_gauge.editions import result_archive

DATA_PATH = "results/costs/v0.1.0/current.json"


def build_reference(root, *, display_data, timing_reference):
    edition = json.loads((Path(root) / "benchmark.json").read_bytes())
    path = Path(root) / DATA_PATH
    if not path.is_file():
        return None
    document = json.loads(path.read_text())
    if document.get("schema") != PUBLIC_SCHEMA or document.get("other_retries_included") is not False:
        raise ValueError("Cost display requires a selected-attempt public projection")
    costs = {row["model_id"]: row for row in document["models"]}
    if len(costs) != len(document["models"]):
        raise ValueError("Duplicate model cost reference")
    timings = {row["id"]: row for row in timing_reference["models"]}
    rows = []
    for model in display_data["models"]:
        row = costs.get(model["id"])
        if row is None:
            raise ValueError("Missing model in cost reference: " + model["id"])
        folder = Path(root) / result_archive(edition, model["id"]) / model["id"] / row["record_id"]
        source = folder / ("record.json" if (folder / "record.json").is_file() else "native-observation.json")
        if not source.is_file() or hashlib.sha256(source.read_bytes()).hexdigest() != row.get("record_sha256"):
            raise ValueError("Cost reference binds a different public model record")
        item = {key: row[key] for key in ("model_id", "record_id", "status", "total_usd", "known_usd",
                    "estimate_range_usd", "coverage", "pricing_basis")}
        item.update(label=model["label"], theme=model["theme"], logo=model["logo"], scores={},
                    seconds=timings[model["id"]]["summaries"]["daily"]["weighted_mean_seconds"])
        submission = (model["retry"]["combined"].get("submission_summary")
                      or model.get("answer_delivery") or {})
        normal_finals = submission.get("active_final")
        item["answer_delivery"] = {"planned": 39, "active_final": normal_finals,
                                   "complete": submission.get("planned") == 39 and normal_finals == 39}
        for mode in ("capability", "partial", "strict"):
            result = model["retry"]["combined"] if mode == "partial" else model[mode]["nonlogical_retry_3"]
            metrics = result["metrics"]
            item["scores"][mode] = {"value": metrics["earned"]["confirmed"],
                "complete": metrics.get("overall", {}).get("exact") is not None and
                            not model["evaluation_progress"]["nonlogical_retry_3"]["incomplete"]}
        rows.append(item)
    if set(costs) != {row["model_id"] for row in rows}:
        raise ValueError("Cost reference has a retired or duplicate model")
    frontiers = {}
    for mode in ("capability", "partial", "strict"):
        points = [{**row, "score": row["scores"][mode]["value"],
                   "score_complete": row["scores"][mode]["complete"]} for row in rows]
        frontiers[mode] = {axis: pareto_frontier(points, axis=axis) for axis in ("cost", "time")}
    return {"schema": "math-gauge.cost-presentation/v1", "version": "0.1.0", "currency": "USD",
            "as_of": document["as_of"], "models": rows, "frontiers": frontiers,
            "source": DATA_PATH, "source_evidence_sha256": document["private_source_sha256"],
            "prices": document["prices"]}


def render_panel(data):
    if data is None:
        return ""
    payload = json.dumps(data, ensure_ascii=False).replace("<", "\\u003c").replace("&", "\\u0026")
    template = (Path(__file__).parent / "templates/cost-reference.html").read_text()
    return template.replace("@@COST_DATA@@", payload)
