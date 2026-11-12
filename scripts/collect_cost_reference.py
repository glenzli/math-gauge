"""Read retained candidate usage into a separate cost observation, without model calls.

Supplement files may supply audited historical extractions and declared estimates.
Original archives, mathematical records and usage ledgers are read-only inputs.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import shutil
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from math_gauge.costs import (SCHEMA, VERSION, SUPPLEMENT_REFERENCE_SCHEMA, project_public,
                              source_descriptor, validate_private, verify_source)
from math_gauge.timings import record_context


def read(path):
    return json.loads(Path(path).read_bytes())


def digest(value):
    return hashlib.sha256(value.encode() if isinstance(value, str) else value).hexdigest()


def prices():
    values = []
    for name, label, rates, url in (
        ("terra-standard", "GPT-6.1 Terra · Standard", (1, .05, 1.25, 5), "https://developers.openai.com/api/docs/pricing"),
        ("sol-standard", "GPT-6.1 Sol · Standard", (2, .1, 2.5, 10), "https://developers.openai.com/api/docs/pricing"),
        ("astra-standard", "GPT-6 Astra · Standard", (10, 1, 12.5, 50), "https://developers.openai.com/api/docs/pricing"),
        ("flash-standard", "Gemini 3.8 Flash · Standard", (.75, .075, 0, 3.75), "https://ai.google.dev/gemini-api/docs/pricing"),
        ("argon-standard", "Gemini 4 Argon · introductory Standard", (2, .1, 0, 10), "https://cloud.google.com/gemini-enterprise-agent-platform/generative-ai/pricing"),
        ("carbon-standard", "Gemini 4 Carbon · introductory Global Standard through 2026-11-30", (2, .1, 0, 10), "https://cloud.google.com/model-garden/pricing"),
        ("opus-list", "Claude Opus 5.5 · native list cost", (4, .2, 5, 20), "https://platform.claude.com/docs/en/about-claude/pricing"),
        ("sonnet-list", "Claude Sonnet 5.5 · native list cost", (2, .1, 2.5, 10), "https://platform.claude.com/docs/en/about-claude/pricing"),
        ("kimi-standard", "Kimi K3.1 Pro · Standard", (2, .2, 2, 10), "https://platform.kimi.ai/"),
        ("glm-standard", "GLM-5.3 · Standard", (1.4, .26, 1.4, 4.4), "https://docs.z.ai/guides/overview/pricing"),
    ):
        values.append({"id": name, "label": label, "source_url": url,
                       "rates_per_million": dict(zip(("input", "cached_input", "cache_write", "output"), rates))})
    return values


def price_id(model):
    for prefix, price in (("terra-", "terra-standard"), ("sol-", "sol-standard"), ("astra-", "astra-standard"),
                           ("gemini-3.8", "flash-standard"), ("gemini-4-carbon", "carbon-standard"),
                           ("gemini-4-argon", "argon-standard"),
                           ("claude-opus", "opus-list"), ("claude-sonnet", "sonnet-list"),
                           ("kimi-", "kimi-standard"), ("glm-", "glm-standard")):
        if model.startswith(prefix):
            return price
    return None


def usage_projection(raw, kind):
    if type(raw.get("input_tokens")) is not int or type(raw.get("output_tokens")) is not int:
        raise ValueError("Native usage has no integer input/output")
    cache_key = "cache_read_input_tokens" if kind == "claude" else "cache_read_tokens" if kind == "agy" else "cached_input_tokens"
    if type(raw.get(cache_key)) is not int:
        raise ValueError("Native usage has no explicit cache count")
    return {"input_tokens": raw["input_tokens"], "output_tokens": raw["output_tokens"],
            "cached_input_tokens": raw[cache_key],
            "cache_write_input_tokens": raw.get("cache_creation_input_tokens", 0) if kind == "claude" else raw.get("cache_write_input_tokens", 0),
            "reasoning_output_tokens": raw.get("reasoning_output_tokens", raw.get("reasoning_tokens", raw.get("thinking_tokens", raw.get("output_tokens_details", {}).get("thinking_tokens"))))}


def agy_usage_gaps(updates, terminal_result=None):
    """A terminal aggregate does not fill unreported failed model generations."""
    steps = {(row.get("conversation_id"), row["step_index"]): row for row in updates
             if type(row.get("step_index")) is int}
    gaps = []
    for (conversation, index), row in sorted(steps.items(), key=lambda item: item[0][1]):
        if row.get("step_type") != "agent_response":
            continue
        usage = row.get("usage")
        following = steps.get((conversation, index + 1), {})
        if row.get("state") != "DONE":
            reason = "generation_unfinished_at_cutoff"
        elif not isinstance(usage, dict) or any(type(usage.get(key)) is not int
                for key in ("input_tokens", "output_tokens", "cache_read_tokens")):
            reason = "generation_usage_missing"
        elif (not any(usage[key] for key in ("input_tokens", "output_tokens", "cache_read_tokens"))
                and following.get("step_type") == "error_message"):
            reason = "zero_usage_generation_followed_by_error"
        else:
            continue
        gaps.append({"step_index": index, "state": row.get("state"), "reason": reason})
    terminal_result = terminal_result or {}
    error = terminal_result.get("error")
    if (not gaps and terminal_result.get("status") == "ERROR" and isinstance(error, str)
            and any(signal in error.lower() for signal in (
                "stream idle timeout", "stream was interrupted", "stream reading error", "request failed"))):
        # A failed provider stream may never emit an agent_response step. Its
        # absence cannot prove that the terminal's earlier counters are complete.
        gaps.append({"step_index": None, "state": "ERROR",
                     "reason": "native_stream_failure_usage_unresolved", "native_error": error})
    return gaps


class Collector:
    def __init__(self, public_root, private_root, out):
        self.public_root, self.private_root, self.out = public_root, private_root, out
        self.out.mkdir(parents=True, exist_ok=True)
        self.hash_cache = {}

    def upstream(self, path):
        path = Path(path)
        if path not in self.hash_cache:
            root = self.private_root if path.is_relative_to(self.private_root) else self.public_root
            self.hash_cache[path] = source_descriptor(path, root)
        return self.hash_cache[path]

    def extract(self, model, slot, body):
        safe = slot.replace(":", "-")
        path = self.out / "evidence" / model / (safe + ".json")
        path.parent.mkdir(parents=True, exist_ok=True)
        document = {"schema": "math-gauge.cost-usage-extract/v1", "extraction_only": True,
                    "not_a_new_native_receipt": True, "model_id": model, "slot_id": slot, **body}
        path.write_text(json.dumps(document, ensure_ascii=False, indent=2) + "\n")
        return source_descriptor(path, self.out)

    def recovered_failures(self, folder, record_file):
        """A later sealed failure supersedes an earlier failed attempt's counters."""
        path = folder / "review-completion-private.json"
        if not path.is_file():
            return {}
        document = read(path)
        if (document.get("schema") != "math-gauge.source-recovery-review/v1" or
                document.get("status") != "complete"):
            raise ValueError("Unknown recovered-failure selection evidence")
        verify_source(folder, document["record"])
        if (folder / document["record"]["path"]).resolve() != record_file.resolve():
            raise ValueError("Failure recovery binds a different retained record")
        recovered = {}
        for row in document["resolved_initials"]:
            if row.get("native_terminal_available") or row.get("classification") != "blank":
                raise ValueError("Recovered cost usage needs an explicit native extraction")
            for descriptor in row["evidence"]:
                verify_source(folder, descriptor)
            recovered[row["case_id"] + ":A1"] = {
                "physical_attempt": row["physical_attempt"],
                "upstream_files": [self.upstream(path)] +
                    [self.upstream(folder / source["path"]) for source in row["evidence"]]}
        return recovered

    def native(self, model, slot, meta_path, *, expected_answer):
        data = read(meta_path)
        attempt = digest(model + ":" + str(meta_path.relative_to(self.private_root)))
        identity_basis = "retained_archive_path"
        raw_units, provenance, complete = [], [self.upstream(meta_path)], False
        final_usage_present, coverage_gaps = False, []
        if meta_path.name == "execution.json":
            events = meta_path.parent.parent / "output/events.ndjson"
            if not events.is_file():
                return None
            expected = data.get("artifact_hashes", {}).get("output/events.ndjson")
            desc = self.upstream(events)
            if expected and desc["sha256"] != expected:
                raise ValueError("Native cost events changed: " + str(events))
            provenance.append(desc)
            terminal, native_ids, step_updates, native_results = [], set(), [], []
            for line in events.read_text().splitlines():
                try:
                    event = json.loads(line)
                except ValueError:
                    continue
                if event.get("type") == "turn.completed":
                    terminal.append(event.get("usage"))
                if event.get("type") == "thread.started" and event.get("thread_id"):
                    native_ids.add(("codex", event["thread_id"]))
                if event.get("event") == "init" and event.get("conversation_id"):
                    native_ids.add(("agy", event["conversation_id"]))
                if event.get("event") == "result":
                    terminal.append(event.get("result", {}).get("usage"))
                    native_results.append(event.get("result", {}))
                if event.get("event") == "step_update" and isinstance(event.get("step_update"), dict):
                    step_updates.append(event["step_update"])
            if len(native_ids) > 1:
                raise ValueError("A cost attempt contains multiple native outer identities")
            if native_ids:
                native_kind, native_id = next(iter(native_ids))
                request = data.get("request_utc", data.get("started_utc")) if native_kind == "agy" else ""
                if native_kind != "agy" or request:
                    attempt = digest(model + ":" + native_kind + ":" + native_id + ":" + str(request))
                    identity_basis = "native_thread" if native_kind == "codex" else "native_conversation_and_request_time"
            raw = data.get("usage")
            if isinstance(raw, dict) and raw in terminal:
                kind = "agy" if model.startswith("gemini-") else "codex"
                normalized = usage_projection(raw, kind)
                if not any(normalized[key] for key in ("input_tokens", "output_tokens", "cached_input_tokens")) and data.get("status") != "completed":
                    return None
                raw_units.append((normalized, raw, None))
                final_usage_present = True
                native_result = next((item for item in reversed(native_results) if item.get("usage") == raw), None)
                coverage_gaps = agy_usage_gaps(step_updates, native_result) if kind == "agy" else []
                complete = not coverage_gaps
        else:
            if data.get("session_id"):
                attempt = digest(model + ":claude:" + data["session_id"])
                identity_basis = "native_cli_session"
            stdout = meta_path.parent / "stdout.jsonl"
            result = None
            if stdout.is_file():
                provenance.append(self.upstream(stdout))
                for line in stdout.read_text().splitlines():
                    try:
                        event = json.loads(line)
                    except ValueError:
                        continue
                    if event.get("type") == "result":
                        result = event
            usage_path = meta_path.parent / "usage.json"
            if result is not None and usage_path.is_file():
                raw = read(usage_path)
                provenance.append(self.upstream(usage_path))
                native = result.get("usage", {})
                model_usage = result.get("modelUsage", {})
                if model_usage:
                    # CLI modelUsage is cumulative over every internal turn in
                    # the retained outer invocation. result.usage may be only
                    # the last turn; summing both would double charge it.
                    native = {key: sum(item.get(native_key, 0) for item in model_usage.values())
                              for key, native_key in (("input_tokens", "inputTokens"), ("output_tokens", "outputTokens"),
                                  ("cache_read_input_tokens", "cacheReadInputTokens"), ("cache_creation_input_tokens", "cacheCreationInputTokens"))}
                projected = usage_projection(raw, "claude")
                for key in ("input_tokens", "output_tokens", "cache_read_input_tokens", "cache_creation_input_tokens"):
                    if key in native and native[key] != raw[key]:
                        raise ValueError(f"Claude native usage differs from extraction: {model} {slot} {key}: {native[key]} != {raw[key]}")
                native_cost = None
                if model.startswith("claude-"):
                    if not all(item.get("costBasis") == "list" for item in result.get("modelUsage", {}).values()):
                        raise ValueError("Claude list cost has an unknown price basis")
                    native_cost = result.get("total_cost_usd")
                    if native_cost != raw.get("cost_usd_list_price"):
                        raise ValueError("Claude reported list costs disagree")
                raw_units.append((projected, raw, native_cost))
                complete = final_usage_present = True
            else:
                # A timed-out CLI may still retain completed provider-message usage.
                # Repeated streamed blocks for one provider message are one counter.
                unique = {}
                for path in sorted((meta_path.parent / "transcript").glob("*.jsonl")):
                    found = False
                    for line in path.read_text().splitlines():
                        try:
                            event = json.loads(line)
                        except ValueError:
                            continue
                        message = event.get("message", {})
                        if event.get("type") != "assistant" or not isinstance(message, dict):
                            continue
                        if event.get("sessionId") and event["sessionId"] != data.get("session_id"):
                            continue
                        raw, mid = message.get("usage"), message.get("id")
                        if not mid or not isinstance(raw, dict):
                            continue
                        normalized = usage_projection(raw, "claude")
                        before = unique.get(mid)
                        if before is not None:
                            if any(before[0][key] != normalized[key] for key in ("input_tokens", "cached_input_tokens", "cache_write_input_tokens")):
                                raise ValueError("Conflicting provider-message cache/input counters")
                            if before[0]["output_tokens"] > normalized["output_tokens"]:
                                continue
                        unique[mid] = (normalized, raw, None)
                        found = True
                    if found:
                        provenance.append(self.upstream(path))
                raw_units = list(unique.values())
        if not raw_units:
            return None
        kind = "agy" if model.startswith("gemini-") else "claude" if meta_path.name == "metadata.json" else "codex"
        units = []
        for index, (normalized, raw, native_cost) in enumerate(raw_units):
            unit = {"identity_sha256": digest(attempt + ":usage:" + str(index)), "attempt_identity_sha256": attempt,
                    "usage": normalized, "convention": "input_includes_cache" if kind == "codex" else "input_excludes_cache",
                    "price_id": price_id(model)}
            if native_cost is not None:
                unit.update(reported_list_cost_usd=native_cost, reported_cost_basis="list")
            units.append(unit)
        source = self.extract(model, slot, {"upstream_files": provenance, "raw_usage": [x[1] for x in raw_units],
            "answer_sha256": expected_answer, "native_final_usage_present": final_usage_present,
            "native_usage_coverage_gaps": coverage_gaps,
            "identity_basis": identity_basis, "attempt_identity_sha256": attempt,
            "partial_stream_message_deduplication": kind == "claude" and not final_usage_present})
        return {"id": slot, "state": "complete" if complete else "partial", "attempt_identity_sha256": attempt,
                "answer_sha256": expected_answer, "units": units, "sources": [source]}

    def model(self, model, record_id):
        public = self.public_root / "results/v0.6.0" / model / record_id
        private = self.private_root / "results/v0.6.0" / model / record_id
        context = record_context(public, private)
        record = context["private_record"]
        candidates = list(record.get("records", []))
        binding = record.get("attempt_condition_sources")
        if binding:
            conditions = read(private / binding["path"])
            desc = conditions["conditions"]["nonlogical_retry_3"].get("source_records")
            if desc:
                source = read(private / desc["path"])
                candidates = list(source.get("records", [])) + candidates
        by_id = {}
        for row in candidates:
            name = row.get("id", "").replace(":alignment:", ":R")
            if name not in by_id:
                by_id[name] = row
        record_file = private / context["name"]
        recovered = self.recovered_failures(private, record_file)
        slots = []
        for name, expected in context["expected"].items():
            row = by_id.get(name, {})
            raw_source = row.get("source", {})
            source = raw_source.get("native_execution") or raw_source.get("native_metadata")
            slot = None
            if name in recovered:
                if expected is not None:
                    raise ValueError("A recovered failure cannot replace a delivered answer")
                evidence = self.extract(model, name, {**recovered[name], "answer_sha256": None,
                    "missing_usage_reason": "The last retained attempt has no native usage; earlier failed-attempt counters are excluded"})
                slots.append({"id": name, "state": "missing", "selection": "last_retained_failure",
                              "answer_sha256": None, "units": [], "sources": [evidence]})
                continue
            if source:
                path = private / source["path"]
                if self.upstream(path)["sha256"] != source["sha256"]:
                    raise ValueError("Selected native cost source changed")
                slot = self.native(model, name, path, expected_answer=expected)
            selection = "fixed_round" if ":R" in name else "retained_final" if expected else "last_retained_failure"
            if slot is None:
                not_run = (raw_source.get("native_model_requests") == 0 or
                           raw_source.get("native_request_attempted") is False or row.get("status") == "not_run")
                source = self.extract(model, name, {"upstream_files": [self.upstream(record_file)],
                    "selection_evidence": raw_source, "answer_sha256": expected,
                    "missing_usage_reason": "No terminal usage or provider-message counters found in the retained source",
                    "not_run_explicit": not_run})
                slot = {"id": name, "state": "not_run" if not_run else "missing", "answer_sha256": expected,
                        "selection": "not_run" if not_run else selection, "units": [], "sources": [source]}
            else:
                slot["selection"] = selection
            slots.append(slot)
        return {"model_id": model, "record_id": record_id, "pricing_basis": "native_list" if model.startswith("claude-") else "standard_api_reference",
                "record_binding": self.upstream(record_file),
                "public_record_binding": self.upstream(public / context["name"]), "slots": slots}, context["expected"]

    def supplement(self, model, path):
        supplement = read(path)
        if supplement.get("schema") == SUPPLEMENT_REFERENCE_SCHEMA:
            if supplement.get("model_id") != model["model_id"] or supplement.get("record_id") != model["record_id"]:
                raise ValueError("Cost supplement reference belongs to a different selected record")
            verify_source(path.parent, supplement["inventory"])
            inventory = read(path.parent / supplement["inventory"]["path"])
            matches = [item for item in inventory["models"] if item["model_id"] == model["model_id"]]
            if inventory.get("schema") != SCHEMA or len(matches) != 1:
                raise ValueError("Cost supplement reference must select one frozen model inventory")
            supplement = matches[0]
        if supplement["record_id"] != model["record_id"]:
            raise ValueError("Cost supplement belongs to an old selected record")
        prefix = Path("evidence") / ("supplement-" + model["model_id"])
        def retain(source):
            verify_source(path.parent, source)
            target = self.out / prefix / source["path"]
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(path.parent / source["path"], target)
            return {**source, "path": (prefix / source["path"]).as_posix()}
        slots = {slot["id"]: slot for slot in model["slots"]}
        for row in supplement["slots"]:
            if row["id"] not in slots:
                raise ValueError("A cost supplement adds a retired slot")
            item = {**row, "sources": [retain(source) for source in row["sources"]]}
            slots[row["id"]] = item
        model["slots"] = list(slots.values())
        if supplement.get("estimate"):
            model["estimate"] = {**supplement["estimate"], "sources": [retain(s) for s in supplement["estimate"]["sources"]]}
        if supplement.get("cost_resolution"):
            resolution = supplement["cost_resolution"]
            model["cost_resolution"] = {**resolution, "sources": [retain(s) for s in resolution["sources"]]}
        if supplement.get("pricing_basis"):
            model["pricing_basis"] = supplement["pricing_basis"]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--private-root", type=Path, required=True)
    parser.add_argument("--out-dir", type=Path, required=True)
    parser.add_argument("--check", action="store_true", help="Verify an existing retained observation and its public projection")
    parser.add_argument("--supplement", type=Path, action="append", default=[])
    parser.add_argument("--extra-prices", type=Path, action="append", default=[])
    parser.add_argument("--as-of")
    args = parser.parse_args()
    collector = Collector(args.root, args.private_root, args.out_dir)
    edition = read(args.root / "benchmark.json")
    records = dict(edition["selected_result_record_ids"])
    records["dot-underlying-model-20261108"] = "20261108"
    if args.check:
        document = read(args.out_dir / "costs.json")
        expected = {}
        for model in document["models"]:
            name, rid = model["model_id"], model["record_id"]
            if records.get(name) != rid:
                raise ValueError("Cost observation refers to a different selected record")
            record_path = args.private_root / model["record_binding"]["path"]
            if collector.upstream(record_path) != model["record_binding"]:
                raise ValueError("The cost observation's source record changed")
            expected[name] = record_context(args.root / "results/v0.6.0" / name / rid,
                                             args.private_root / "results/v0.6.0" / name / rid)["expected"]
        raw = (args.out_dir / "costs.json").read_bytes()
        projected = project_public(document, source_sha256=digest(raw), root=args.out_dir,
                                   expected_answers=expected, benchmark_version=edition["version"])
        if projected != read(args.out_dir / "public.json"):
            raise ValueError("Public cost projection differs from its private sources")
        print(json.dumps({"status": "passed", "models": len(document["models"]), "new_candidate_calls": 0}))
        return
    if not args.as_of:
        parser.error("--as-of is required when collecting a new observation")
    supplements = {read(path)["model_id"]: path for path in args.supplement}
    models, expected = [], {}
    for model, record_id in records.items():
        row, selected = collector.model(model, record_id)
        if model in supplements:
            collector.supplement(row, supplements[model])
        models.append(row)
        expected[model] = selected
    tariffs = prices()
    for path in args.extra_prices:
        tariffs.extend(read(path))
    document = {"schema": SCHEMA, "version": VERSION, "benchmark_version": edition["version"], "as_of": args.as_of,
                "selection_rule": "one_retained_attempt_per_slot", "other_retries_included": False,
                "prices": tariffs, "models": models, "new_candidate_calls": 0, "scores_modified": False}
    rows = validate_private(document, root=args.out_dir, expected_answers=expected)
    raw = (json.dumps(document, ensure_ascii=False, indent=2) + "\n").encode()
    (args.out_dir / "costs.json").write_bytes(raw)
    public = project_public(document, source_sha256=digest(raw), root=args.out_dir,
                            expected_answers=expected, benchmark_version=edition["version"])
    (args.out_dir / "public.json").write_text(json.dumps(public, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps({"status": "passed", "models": [{key: row[key] for key in ("model_id", "status", "known_usd", "total_usd", "coverage")} for row in rows]}, ensure_ascii=False))


if __name__ == "__main__":
    main()
