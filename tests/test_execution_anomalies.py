"""Operational counting must preserve identities, unknowns and score separation."""
import copy
import hashlib
import json
from pathlib import Path
import tempfile
import unittest

from math_gauge.execution_anomalies import (
    CATEGORIES, SCHEMA, deduplicate_runs, load_public, project_public, validate_private, validate_public,
    verify_sources,
)
from scripts.results_anomalies import render_model_details, render_panel


def digest(value):
    return hashlib.sha256(value.encode()).hexdigest()


def fixture(*, history_complete=True):
    source = digest("original evidence")
    return {"schema": SCHEMA, "version": "0.1.0", "visibility": "private", "is_score": False,
            "unit": "physical_candidate_run", "as_of": "2026-11-15", "cutoff_utc": "2026-11-14T17:12:47Z",
            "sources": {source: {"root": "private", "path": "original.json", "bytes": 17, "sha256": source}},
            "groups": [{"id": "model-harness", "model_id": "public-model", "model_label": "Public Model",
                        "harness_label": "CLI", "route": "", "history_complete": history_complete,
                        "coverage": "complete" if history_complete else "partial", "sources": [source]}],
            "runs": []}


def run(document, identity, *, anomalies=(), scope="benchmark", disposition="normal_final", unknown=()):
    source = next(iter(document["sources"]))
    flags = {k: {"observed": None if k in unknown else k in anomalies} for k in CATEGORIES}
    for kind in anomalies:
        flags[kind].update(evidence=[source], reason="Original private task MG-PRIVATE-EXAMPLE at /private/source")
    return {"identity_sha256": digest(identity), "group_id": "model-harness", "scope": scope,
            "disposition": disposition, "observed_at": "2026-11-14T12:00:00Z", "sources": [source], "flags": flags}


def public(document):
    return project_public(document, private_sha256=digest(json.dumps(document, sort_keys=True)))


def causal_review(document, decision):
    return {"decision": decision, "reason": "Source-reviewed causal attribution",
            "evidence": [next(iter(document["sources"]))]}


class OperationalCountingTests(unittest.TestCase):
    def test_model_only_notes_bind_the_exact_review_and_never_enter_homepage(self):
        doc = fixture()
        doc['version'] = '0.3.0'
        doc['runs'] = [run(doc, 'pending', anomalies=('harness_environment',))]
        doc['runs'][0]['causal_review'] = {'harness_environment': causal_review(doc, 'unresolved')}
        projected = public(doc)
        note = {'unresolved_runs': 1, 'title': {'zh': '待确认原因', 'en': 'Unresolved cause'},
                'events': [{'runs': 1, 'zh': '<untrusted detail>', 'en': 'Transport interrupted'}],
                'explanation': {'zh': '不计入确认次数', 'en': 'Excluded from confirmed counts'}}
        notes = {'schema': 'math-gauge.operational-model-notes/v1',
                 'source_review_sha256': projected['source_review_sha256'],
                 'models': {'public-model': note}}
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / 'results/execution-anomalies/v0.3.0/model-notes.json'
            path.parent.mkdir(parents=True)
            path.write_text(json.dumps(notes))
            detail = render_model_details(projected, 'public-model', root=temporary)
            self.assertIn('&lt;untrusted detail&gt;', detail)
            self.assertNotIn('<untrusted detail>', detail)
            self.assertNotIn('Transport interrupted', render_panel(projected))
            self.assertEqual(projected['rows'][0]['anomalous_runs'], {'known': 0, 'exact': None})
            notes['source_review_sha256'] = digest('different review')
            path.write_text(json.dumps(notes))
            self.assertNotIn('Transport interrupted', render_model_details(projected, 'public-model', root=temporary))
            notes['source_review_sha256'] = projected['source_review_sha256']
            note['events'][0]['runs'] = 2
            path.write_text(json.dumps(notes))
            with self.assertRaisesRegex(ValueError, 'totals'):
                render_model_details(projected, 'public-model', root=temporary)

    def test_causal_review_excludes_tester_flags_but_retains_native_overlap_and_raw_flags(self):
        doc = fixture()
        doc["version"] = "0.3.0"
        tester = run(doc, "tester-only", anomalies=("timeout", "harness_environment"))
        tester["causal_review"] = {kind: causal_review(doc, "exclude")
                                   for kind in ("timeout", "harness_environment")}
        same_category = run(doc, "native-and-tester-runner", anomalies=("timeout", "harness_environment"))
        same_category["causal_review"] = {"timeout": causal_review(doc, "exclude"),
                                         "harness_environment": causal_review(doc, "count")}
        different_categories = run(doc, "native-server-and-tester", anomalies=("timeout", "http_429"))
        different_categories["causal_review"] = {"timeout": causal_review(doc, "exclude")}
        same_server = run(doc, "two-server-causes", anomalies=("service_stream_connection", "http_429"))
        same_server["causal_review"] = {"service_stream_connection": causal_review(doc, "exclude")}
        doc["runs"] = [tester, same_category, different_categories, same_server]
        original = copy.deepcopy(doc)
        result = public(doc)
        validate_public(result)
        row = result["rows"][0]
        self.assertEqual(row["reviewed_runs"], 4)
        self.assertEqual(row["excluded_runs"], 0)
        self.assertEqual(row["anomalous_runs"], {"known": 3, "exact": 3})
        self.assertEqual(row["categories"], {"server_errors": {"known": 2, "exact": 2},
                                             "context": {"known": 0, "exact": 0},
                                             "runner": {"known": 1, "exact": 1}})
        self.assertEqual(doc, original)
        self.assertNotIn("causal_review", json.dumps(result))

    def test_unresolved_cause_retains_unknown_unless_union_has_a_known_positive(self):
        for anomalies, reviewed_kind, category, expected_category, expected_union in (
                (("timeout",), "timeout", "runner", {"known": 0, "exact": None},
                 {"known": 0, "exact": None}),
                (("timeout", "http_429"), "timeout", "runner", {"known": 0, "exact": None},
                 {"known": 1, "exact": 1}),
                (("service_stream_connection", "http_429"), "service_stream_connection", "server_errors",
                 {"known": 1, "exact": 1}, {"known": 1, "exact": 1})):
            with self.subTest(anomalies=anomalies):
                doc = fixture()
                doc["version"] = "0.3.0"
                row = run(doc, "unresolved", anomalies=anomalies)
                row["causal_review"] = {reviewed_kind: causal_review(doc, "unresolved")}
                doc["runs"] = [row]
                result = public(doc)
                validate_public(result)
                self.assertEqual(result["rows"][0]["categories"][category], expected_category)
                self.assertEqual(result["rows"][0]["anomalous_runs"], expected_union)

    def test_group_category_exclusion_still_overrides_causal_review(self):
        doc = fixture()
        doc["version"] = "0.3.0"
        doc["groups"][0]["category_exclusions"] = {
            "server_errors": {"reason": "Operator-confirmed local forwarding configuration",
                              "evidence": [next(iter(doc["sources"]))]}}
        row = run(doc, "group-excluded", anomalies=("service_stream_connection", "http_429"))
        row["causal_review"] = {"service_stream_connection": causal_review(doc, "unresolved"),
                                "http_429": causal_review(doc, "count")}
        row["native_findings"] = {"service_stream_connection": causal_review(doc, "count")}
        doc["runs"] = [row]
        result = public(doc)["rows"][0]
        self.assertEqual(result["reviewed_runs"], 1)
        self.assertEqual(result["categories"]["server_errors"], {"known": 0, "exact": None})
        self.assertEqual(result["anomalous_runs"], {"known": 0, "exact": 0})

    def test_supplemental_native_finding_counts_provider_error_without_rewriting_raw_false(self):
        for decision, expected in (("count", {"known": 1, "exact": 1}),
                                   ("unresolved", {"known": 0, "exact": None})):
            with self.subTest(decision=decision):
                doc = fixture()
                doc["version"] = "0.3.0"
                row = run(doc, "tester-gateway-and-provider-502", anomalies=("harness_environment",))
                row["causal_review"] = {"harness_environment": causal_review(doc, "exclude")}
                row["native_findings"] = {"service_stream_connection": causal_review(doc, decision)}
                doc["runs"] = [row]
                original = copy.deepcopy(doc)
                result = public(doc)
                validate_public(result)
                projected = result["rows"][0]
                self.assertEqual(projected["reviewed_runs"], 1)
                self.assertEqual(projected["categories"]["runner"], {"known": 0, "exact": 0})
                self.assertEqual(projected["categories"]["server_errors"], expected)
                self.assertEqual(projected["anomalous_runs"], expected)
                self.assertFalse(row["flags"]["service_stream_connection"]["observed"])
                self.assertEqual(doc, original)
                self.assertNotIn("native_findings", json.dumps(result))

    def test_appended_reviews_require_supported_decisions_and_retained_evidence(self):
        doc = fixture()
        doc["version"] = "0.3.0"
        row = run(doc, "reviewed", anomalies=("timeout",), unknown=("http_429",))
        doc["runs"] = [row]
        review = causal_review(doc, "count")
        invalid = [
            {"server_errors": review},
            {"timeout": dict(review, decision="ignore")}, {"timeout": dict(review, decision=None)},
            {"timeout": dict(review, evidence=[])}, {"timeout": dict(review, evidence=[digest("missing")])},
            {"timeout": dict(review, evidence=review["evidence"][0])},
            {"timeout": dict(review, reason=" ")}, {"timeout": {"decision": "exclude"}},
            {"timeout": dict(review, unsupported=True)}, {"timeout": None}, None,
        ]
        for field in ("causal_review", "native_findings"):
            invalid_field = invalid + ([{"other": review}, {"http_429": review}] if field == "causal_review"
                                       else [{"timeout": dict(review, decision="exclude")}])
            for reviews in invalid_field:
                with self.subTest(field=field, reviews=reviews):
                    row[field] = reviews
                    with self.assertRaisesRegex(ValueError, field.replace("_", " ")):
                        validate_private(doc)
            row[field] = {"timeout": causal_review(doc, "count")}
            validate_private(doc)

    def test_aliases_merge_causal_review_without_order_dependence_and_reject_conflicts(self):
        doc = fixture()
        doc["version"] = "0.3.0"
        row = run(doc, "one-run", anomalies=("timeout", "http_429"))
        reviewed = copy.deepcopy(row)
        reviewed["causal_review"] = {"timeout": causal_review(doc, "exclude")}
        reviewed["native_findings"] = {"output_or_context_limit": causal_review(doc, "count")}
        for aliases in ([row, reviewed], [reviewed, row]):
            doc["runs"] = aliases
            result = public(doc)["rows"][0]
            self.assertEqual(result["reviewed_runs"], 1)
            self.assertEqual(result["categories"]["runner"], {"known": 0, "exact": 0})
            self.assertEqual(result["categories"]["context"], {"known": 1, "exact": 1})
            self.assertEqual(result["anomalous_runs"], {"known": 1, "exact": 1})
        conflict = copy.deepcopy(reviewed)
        conflict["causal_review"]["timeout"]["decision"] = "count"
        with self.assertRaisesRegex(ValueError, "causal reviews conflict"):
            deduplicate_runs([reviewed, conflict])

    def test_old_versions_reproduce_original_counts_and_reject_new_review_fields(self):
        for version in ("0.1.0", "0.2.0"):
            with self.subTest(version=version):
                doc = fixture()
                doc["version"] = version
                doc["runs"] = [run(doc, "benchmark", anomalies=("timeout",)),
                               run(doc, "diagnostic", scope="diagnostic_case", anomalies=("http_429",))]
                result = public(doc)
                validate_public(result)
                row = result["rows"][0]
                count = 2 if version == "0.1.0" else 1
                self.assertEqual(row["reviewed_runs"], count)
                self.assertEqual(row["anomalous_runs"], {"known": count, "exact": count})
                self.assertEqual(result["categories"], list(CATEGORIES) if version == "0.1.0"
                                 else ["server_errors", "context", "runner"])
                for field in ("causal_review", "native_findings"):
                    doc["runs"][0][field] = {}
                    with self.assertRaisesRegex(ValueError, "requires version 0.3.0"):
                        public(doc)
                    del doc["runs"][0][field]

    def test_load_public_prefers_new_causal_version_and_retains_both_fallbacks(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.assertIsNone(load_public(root))
            for version in ("0.1.0", "0.2.0", "0.3.0"):
                doc = fixture()
                doc["version"] = version
                doc["runs"] = [run(doc, "retained", anomalies=("timeout",))]
                projected = public(doc)
                path = root / f"results/execution-anomalies/v{version}/current.json"
                path.parent.mkdir(parents=True)
                path.write_text(json.dumps(projected))
                self.assertEqual(load_public(root), projected)

    def test_source_bound_category_exclusion_removes_only_its_union_contribution(self):
        doc = fixture()
        doc["version"] = "0.2.0"
        source = next(iter(doc["sources"]))
        doc["groups"][0]["category_exclusions"] = {
            "server_errors": {"reason": "Operator-confirmed local forwarding configuration", "evidence": [source]}}
        doc["runs"] = [run(doc, "proxy-only", anomalies=("service_stream_connection", "http_429")),
                       run(doc, "proxy-and-timeout", anomalies=("service_stream_connection", "timeout")),
                       run(doc, "output-limit", anomalies=("output_or_context_limit",))]
        original = copy.deepcopy(doc)
        result = public(doc)
        validate_public(result)
        row = result["rows"][0]
        self.assertEqual(row["reviewed_runs"], 3)
        self.assertEqual(row["anomalous_runs"], {"known": 2, "exact": 2})
        self.assertEqual(row["categories"]["server_errors"], {"known": 0, "exact": None})
        self.assertEqual(row["categories"]["context"]["known"], 1)
        self.assertEqual(row["categories"]["runner"]["known"], 1)
        self.assertEqual(doc, original)
        self.assertNotIn("forwarding", json.dumps(result))
        doc["groups"][0]["category_exclusions"]["server_errors"]["evidence"] = []
        with self.assertRaisesRegex(ValueError, "retained review"):
            validate_private(doc)

    def test_current_categories_count_unions_and_preserve_source_flags(self):
        doc = fixture()
        doc["version"] = "0.2.0"
        doc["runs"] = [run(doc, "one-run", anomalies=("service_stream_connection", "http_429", "timeout")),
                       run(doc, "limit", anomalies=("output_or_context_limit",))]
        original = copy.deepcopy(doc)
        result = public(doc)
        validate_public(result)
        self.assertEqual(result["categories"], ["server_errors", "context", "runner"])
        self.assertEqual(result["rows"][0]["anomalous_runs"], {"known": 2, "exact": 2})
        self.assertEqual(result["rows"][0]["categories"], {
            key: {"known": 1, "exact": 1} for key in ("server_errors", "context", "runner")})
        self.assertEqual(doc, original)

    def test_current_scope_excludes_diagnostic_trials_and_unselected_history(self):
        doc = fixture()
        doc["version"] = "0.2.0"
        doc["runs"] = [run(doc, "current-retry", anomalies=("timeout",)),
                       run(doc, "diagnostic", scope="diagnostic_case", anomalies=("timeout",)),
                       run(doc, "old-independent-repeat", scope="out_of_scope", anomalies=("http_429",))]
        result = public(doc)["rows"][0]
        self.assertEqual(result["reviewed_runs"], 1)
        self.assertEqual(result["excluded_runs"], 2)
        self.assertEqual(result["anomalous_runs"], {"known": 1, "exact": 1})
        # The retained old component still reproduces its broader original scope.
        doc["version"] = "0.1.0"
        self.assertEqual(public(doc)["rows"][0]["reviewed_runs"], 2)

    def test_grouped_known_positive_does_not_require_unknown_sibling(self):
        doc = fixture()
        doc["version"] = "0.2.0"
        doc["runs"] = [run(doc, "stream-with-unknown-429", anomalies=("service_stream_connection",),
                           unknown=("http_429",))]
        metric = public(doc)["rows"][0]["categories"]["server_errors"]
        self.assertEqual(metric, {"known": 1, "exact": 1})
        doc["runs"] = [run(doc, "no-stream-with-unknown-429", unknown=("http_429",))]
        metric = public(doc)["rows"][0]["categories"]["server_errors"]
        self.assertEqual(metric, {"known": 0, "exact": None})

    def test_aliases_and_overlapping_errors_count_one_recovered_run(self):
        doc = fixture()
        row = run(doc, "native-thread-and-dispatch", anomalies=("timeout", "service_stream_connection", "http_429"))
        doc["runs"] = [row, copy.deepcopy(row)]
        result = public(doc)["rows"][0]
        self.assertEqual(result["reviewed_runs"], 1)
        self.assertEqual(result["anomalous_runs"], {"known": 1, "exact": 1})
        self.assertEqual([result["categories"][k]["known"] for k in CATEGORIES[:3]], [1, 1, 1])

    def test_quota_cancellation_and_normal_continuation_do_not_create_errors(self):
        doc = fixture()
        doc["runs"] = [run(doc, "quota", disposition="quota_exhausted"),
                       run(doc, "cancel", disposition="cancelled"), run(doc, "normal-continuation"),
                       run(doc, "quota-with-independent-stream-error", disposition="quota_exhausted",
                           anomalies=("service_stream_connection",))]
        result = public(doc)["rows"][0]
        self.assertEqual(result["anomalous_runs"]["exact"], 1)
        self.assertEqual(result["quota_exhausted_runs"], 2)
        self.assertEqual(result["cancelled_runs"], 1)

    def test_controls_prototypes_open_and_late_runs_are_not_counted(self):
        doc = fixture()
        doc["runs"] = [run(doc, scope, scope=scope, anomalies=("other",)) for scope in
                       ("control", "prototype", "invited_study", "preparation", "open", "after_cutoff")]
        result = public(doc)["rows"][0]
        self.assertEqual(result["reviewed_runs"], 0)
        self.assertEqual(result["anomalous_runs"], {"known": 0, "exact": None})
        self.assertEqual(result["excluded_runs"], 6)

    def test_partial_history_does_not_turn_unseen_errors_into_zero(self):
        doc = fixture(history_complete=False)
        doc["runs"] = [run(doc, "fragment", anomalies=("timeout",), unknown=("http_429",))]
        result = public(doc)
        self.assertEqual(result["rows"][0]["anomalous_runs"], {"known": 1, "exact": None})
        page = render_panel(result)
        self.assertIn('<sup aria-describedby="anomaly-history-note">*</sup>', page)
        self.assertIn('class="anomaly-count positive anomaly-total">1</span>', page)
        self.assertIn('class="anomaly-count unknown">—', page)
        self.assertNotIn("MG-PRIVATE-EXAMPLE", json.dumps(result))
        self.assertNotIn("/private/source", page)

    def test_conflicting_alias_judgments_require_review(self):
        doc = fixture()
        row = run(doc, "same-native-run", anomalies=("timeout",))
        other = run(doc, "same-native-run")
        with self.assertRaisesRegex(ValueError, "conflict"):
            deduplicate_runs([row, other])

    def test_positive_anomaly_requires_original_source_and_cutoff(self):
        doc = fixture()
        row = run(doc, "unbound", anomalies=("other",))
        doc["runs"] = [row]
        row["flags"]["other"]["evidence"] = []
        with self.assertRaisesRegex(ValueError, "source-bound"):
            validate_private(doc)
        row["flags"]["other"]["evidence"] = row["sources"]
        row["observed_at"] = "2026-11-15T00:00:00Z"
        with self.assertRaisesRegex(ValueError, "cutoff"):
            validate_private(doc)

    def test_public_contract_rejects_private_inventory_and_false_precision(self):
        doc = fixture(history_complete=False)
        doc["runs"] = [run(doc, "fragment")]
        result = public(doc)
        validate_public(result)
        leaked = copy.deepcopy(result)
        leaked["sources"] = doc["sources"]
        with self.assertRaisesRegex(ValueError, "nonaggregate"):
            validate_public(leaked)
        bad = copy.deepcopy(result)
        bad["rows"][0]["anomalous_runs"]["known"] = 2
        with self.assertRaisesRegex(ValueError, "exceed"):
            validate_public(bad)

    def test_original_bytes_and_repository_boundary_are_checked(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            raw = b'{"status":"ERROR"}\n'
            (root / "original.json").write_bytes(raw)
            doc = fixture()
            key = next(iter(doc["sources"]))
            doc["sources"][key].update(bytes=len(raw), sha256=hashlib.sha256(raw).hexdigest())
            verify_sources(doc, {"private": root})
            (root / "original.json").write_bytes(b"changed")
            with self.assertRaisesRegex(ValueError, "changed"):
                verify_sources(doc, {"private": root})
            doc["sources"][key]["path"] = "../outside.json"
            with self.assertRaisesRegex(ValueError, "inside"):
                verify_sources(doc, {"private": root})


if __name__ == "__main__":
    unittest.main()
