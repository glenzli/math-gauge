"""Focused evidence for the release-only candidate identity projection."""

import copy
import json
from pathlib import Path
import re
import unittest

from math_gauge.catalog import Suite, candidate_message
from benchmark_fixtures import source_root
from math_gauge.release_projection import (
    CANDIDATE_PROJECTION, project_candidate_request, project_candidate_text,
)


ROOT = Path(__file__).resolve().parents[1]


class ReleaseProjectionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.suite = Suite.load(source_root() / "cases")

    def test_default_inputs_change_only_declared_identity_surfaces(self):
        changed = {"lean": 0, "ledger": 0, "attribution": 0}
        for case in self.suite.cases.values():
            request = self.suite.request(case)
            before = copy.deepcopy(request)
            projected = project_candidate_request(request)
            self.assertEqual(request, before)
            self.assertEqual(projected["task"], request["task"])
            self.assertEqual(projected["instruction"], request["instruction"])
            self.assertEqual({k: v for k, v in projected.items() if k != "files"},
                             {k: v for k, v in request.items() if k != "files"})
            self.assertEqual([f["name"] for f in projected["files"]],
                             [f["name"] for f in request["files"]])
            for original, result in zip(request["files"], projected["files"]):
                name, source, output = original["name"], original["content"], result["content"]
                if source == output:
                    continue
                if name.endswith(".lean"):
                    changed["lean"] += 1
                    self.assertNotIn("TaskInputs", source)
                    self.assertEqual(source.splitlines(keepends=True),
                                     output.replace("TaskInputs.", "MathGauge.").splitlines(keepends=True))
                    for line in source.splitlines():
                        if "MathGauge" in line:
                            self.assertRegex(line, r"^\s*(namespace|end) MathGauge\.F\d+$")
                elif name == "obligations.json":
                    changed["ledger"] += 1
                    old, new = json.loads(source), json.loads(output)
                    self.assertEqual(old.pop("schema"), "math-gauge.chapter-deliverables/v1")
                    self.assertEqual(new.pop("schema"), "task-inputs.chapter-deliverables/v1")
                    self.assertEqual(old, new)
                    self.assertEqual(output.replace("task-inputs.chapter-deliverables/v1",
                                                    "math-gauge.chapter-deliverables/v1"), source)
                elif name == "ATTRIBUTION.md":
                    changed["attribution"] += 1
                    self.assertEqual(output, source.replace(
                        "Public repository https://github.com/glenzli/oet-public at commit "
                        "539b40cec73184d98e06d54fbd10e4b4698bd6e7. ", ""
                    ).replace("new Math Gauge benchmark design material", "new task design material").replace(
                        " This is a draft task package; no generated solution has been evaluated or human-approved.",
                        "",
                    ))
                else:
                    self.fail("Unexpected projected input: " + name)
            self.assertIsNone(re.search(r"math[ _-]*gauge|https?://github\.com/",
                                        candidate_message(projected), re.IGNORECASE))
            self.assertEqual(project_candidate_request(projected), projected)
        self.assertEqual(changed["lean"], 0)
        self.assertEqual(changed["ledger"], 4)
        self.assertEqual(changed["attribution"], 3)

    def test_chapter_licenses_and_original_authorship_stay_exact(self):
        for cid in ("LCH02", "MG-C003"):
            request = self.suite.request(self.suite.cases[cid])
            original = {f["name"]: f["content"] for f in request["files"]}
            projected = {f["name"]: f["content"] for f in project_candidate_request(request)["files"]}
            self.assertEqual(projected["LICENSE"].encode("utf-8"), original["LICENSE"].encode("utf-8"))
            for credit in ("Zhe Li (Glen Li / glenzli)", "The Operator Evolution Theory",
                           "https://doi.org/10.5281/zenodo.21457931",
                           "https://creativecommons.org/licenses/by/4.0/"):
                self.assertIn(credit, projected["ATTRIBUTION.md"])
            self.assertNotIn("This is a draft task package", projected["ATTRIBUTION.md"])
            self.assertNotIn("human-approved", projected["ATTRIBUTION.md"])
            for name in original.keys() - {"ATTRIBUTION.md", "obligations.json"}:
                self.assertEqual(projected[name], original[name])

    def test_unknown_text_and_raw_response_metadata_are_not_rewritten(self):
        raw_answer = "MathGauge.F104\nhttps://github.com/example/raw-answer\n"
        request = {"schema": "math-gauge.request/v1", "task": "For every x, prove P x.",
                   "instruction": "", "files": [{"name": "Core.lean", "content":
                       "namespace MathGauge.F104\naxiom given : True\nend MathGauge.F104\n"}],
                   "raw_response": {"text": raw_answer}}
        before = copy.deepcopy(request)
        projected = project_candidate_request(request)
        self.assertEqual(projected["raw_response"]["text"], raw_answer)
        self.assertEqual(request, before)
        projected["raw_response"]["text"] = "separate copy"
        projected["files"][0]["content"] = "separate copy"
        self.assertEqual(request, before)
        self.assertEqual(project_candidate_text("notes.md", raw_answer), raw_answer)
        self.assertEqual(project_candidate_text("LICENSE", raw_answer), raw_answer)
        self.assertEqual(CANDIDATE_PROJECTION, "task-inputs.candidate-projection/v1")


if __name__ == "__main__":
    unittest.main()
