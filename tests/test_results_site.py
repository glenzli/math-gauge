"""Current display consumes retained records without a parallel scoring method."""
import copy
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("current_results_site", ROOT / "scripts/render_results_site.py")
SITE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(SITE)


class CurrentSiteTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = SITE.build_data()

    def test_only_selected_current_models_and_scores_are_displayed(self):
        self.assertEqual(self.data["benchmark_version"], "0.6.0")
        self.assertEqual(len(self.data["models"]), 3)
        for model in self.data["models"]:
            path = ROOT / Path(model["source_record"]).parent
            for scope, name in [("public", "result.json"), ("combined", "combined-aggregate.json")]:
                original = json.loads((path / name).read_bytes())
                self.assertEqual(model[scope], original)
            self.assertFalse(model["combined"]["formal_comparison_eligible"])

    def test_public_display_has_no_private_task_identifiers_or_raw_inputs(self):
        for model in self.data["models"]:
            combined = model["combined"]
            self.assertEqual(combined["scope"], "combined-aggregate-only")
            self.assertNotIn("slot_evidence", combined)
            self.assertNotIn("records", combined)
            self.assertEqual(combined["private_case_count"], 3)
        text = json.dumps(self.data)
        self.assertNotIn("math-gauge-private/", text)
        self.assertNotIn("MG-X", text)

    def test_embedded_json_cannot_close_its_script_and_labels_are_escaped(self):
        data = copy.deepcopy(self.data)
        label = '</script><script>alert("fixture")</script>&'
        data["models"][0]["label"] = label
        page = SITE.render(data)
        self.assertNotIn(label, page)
        self.assertIn("\\u003c/script>", page)
        self.assertIn("&lt;/script&gt;", page)
        payload = page.split('<script type="application/json" id="data">', 1)[1].split("</script>", 1)[0]
        self.assertEqual(json.loads(payload), data)

    def test_outputs_are_deterministic_and_only_current_results_are_exported(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            SITE.write_site(root)
            before = {str(p.relative_to(root)): p.read_bytes() for p in root.rglob("*") if p.is_file()}
            SITE.write_site(root)
            self.assertEqual(before, {str(p.relative_to(root)): p.read_bytes() for p in root.rglob("*") if p.is_file()})
            self.assertEqual(len(before), 8)
            self.assertEqual(set(before), {"index.html", "data.json", *(
                "downloads/" + model["id"] + "-" + scope + ".json"
                for model in self.data["models"] for scope in ["public", "combined"])})

    def test_declared_components_and_finite_states_are_present(self):
        page = SITE.render(self.data)
        for value in ["verified_complete", "incomplete_stable", "regressed", "interrupted", "unresolved"]:
            self.assertIn(value, page)
        self.assertIn("textContent", page)
        self.assertNotIn("innerHTML", page)
        self.assertNotIn('<script src="http', page)
        for model in self.data["models"]:
            for scope in ["public", "combined"]:
                self.assertEqual(sum(c["weight"] for c in model[scope]["profile"]["components"]), 100)
                self.assertEqual(model[scope]["coverage"]["papers_planned"], 26 if scope == "public" else 29)

    def test_display_binds_the_unified_engineering_review_and_current_method(self):
        for model in self.data["models"]:
            path = ROOT / Path(model["source_record"]).parent
            record = json.loads((path / "record.json").read_bytes())
            for scope in ("public", "combined"):
                self.assertEqual(model[scope]["engineering_review_sha256"], record["formalization_review"]["sha256"])
                self.assertEqual(model[scope]["scoring_method_version"], self.data["policy"]["version"])
        gemini = next(model for model in self.data["models"] if model["id"].startswith("gemini"))
        case = next(case for case in gemini["public"]["lean_formalization_breakdown"]["cases"] if case["case_id"] == "HCH02")
        self.assertEqual((case["complete_count"], case["total"]), (38, 40))
        self.assertIn('href="../docs/formalization-audit.md"', SITE.render(self.data))


if __name__ == "__main__":
    unittest.main()
