"""Synthetic frozen-report fixtures, never model executions or model evidence."""

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
import xml.etree.ElementTree as ET


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
try:
    import render_benchmark_comparison as comparison
    import render_benchmark_report as report_renderer
finally:
    sys.path.pop(0)


def synthetic_report(model="terra"):
    counts = {"proofs": 27, "lean-audit": 6, "lean-construction": 6,
              "chapters": 2, "exploration": 2, "answer-review": 3}
    components = [{"id": key, "weight": weight, "case_count": counts[key]}
                  for key, weight in (("proofs", 22.5), ("lean-audit", 18),
                                      ("lean-construction", 18), ("chapters", 18),
                                      ("exploration", 13.5), ("answer-review", 10))]
    metrics = {key: {"exact": 62.5, "coverage": {"planned": count}}
               for key, count in counts.items()}
    metrics.update({key: {"exact": 50.0, "coverage": {"planned": count}}
                    for key, count in (("repeat", 7), ("neutral", 14), ("stance", 28))})
    metrics.update({"core": {"exact": 60.25}, "overall": {"exact": 59.75}})
    records = [{"slot_id": cid + ":A1", "public_id": cid,
                "completion": {"exact": 0.5}, "strict_pass": False,
                "status": "reviewed", "human_status": "pending"}
               for cid in ("MG-C002", "MG-C003")]
    for index in range(3):
        records.append({"slot_id": f"SYNTHETIC-AR{index}:A1",
                        "public_id": f"SYNTHETIC-AR{index}",
                        "parent_family_id": f"SYNTHETIC-PARENT{index}",
                        "completion": {"exact": 0.5}, "major_error": False,
                        "strict_pass": False, "status": "reviewed",
                        "human_status": "pending", "dimensions": []})
    return {
        "schema": "math-gauge.public-composite-score/v1",
        "id": model + "-synthetic-only",
        "score_units": {"metrics": "percent", "completion": "fraction"},
        "profile": {"version": "0.5.0", "standard_version": "synthetic-standard-2",
                    "components": components,
                    "overall_weights": {"core": 75, "repeat": 5, "neutral": 10, "stance": 10}},
        "metrics": metrics, "slot_evidence": records,
        "coverage": {"a1_planned": 46, "parent_families": 43,
                     "slots_planned": 109, "slots_reviewed": 5},
        "strict_passes": {"core_A1": {"passed": 0, "total": 46},
                          "all_selected_slots": {"passed": 0, "total": 109}},
        "evidence_status": {"formal_comparison_eligible": False},
        "private_records": [{"public_id": "Private-Synthetic", "completion": {"exact": 0.5},
                             "status": "reviewed", "human_status": "pending"}],
        "methodology_revision": {"new_candidate_calls": 3},
        "default_public_profile": {"version": "0.5.0", "papers": 44,
                                   "parent_families": 41, "slots": 107},
    }


class BenchmarkRendererTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="math-gauge-offline-fixture-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)

    def write_pair(self, terra=None, gemini=None):
        paths = []
        for name, record in (("terra", terra if terra is not None else synthetic_report()),
                             ("gemini", gemini if gemini is not None else synthetic_report("gemini"))):
            path = self.root / (name + ".json")
            path.write_text(json.dumps(record, ensure_ascii=False), encoding="utf-8")
            paths.append(path)
        return paths

    def test_explicit_family_count_accepts_unseen_task_count(self):
        record = {"coverage": {"a1_planned": 501, "parent_families": 488}}
        self.assertEqual(report_renderer.family_count(record), 488)
        record["coverage"]["parent_families"] = None
        self.assertIsNone(report_renderer.family_count(record))

    def test_legacy_family_fallback_requires_complete_a1_inventory(self):
        record = {"coverage": {"a1_planned": 3}, "slot_evidence": [
            {"public_id": "MATH", "slot_id": "MATH:A1"},
            {"public_id": "AR", "slot_id": "AR:A1", "parent_family_id": "MATH"},
            {"public_id": "PRIVATE", "slot_id": "PRIVATE:A1"},
        ]}
        self.assertEqual(report_renderer.family_count(record), 2)
        record["slot_evidence"].pop()
        self.assertIsNone(report_renderer.family_count(record))

    def test_single_report_uses_frozen_versions_coverage_and_weights(self):
        record = synthetic_report()
        record["profile"]["overall_weights"]["core"] = 70
        record["profile"]["overall_weights"]["repeat"] = 10
        for content in (report_renderer.render_markdown(record, "synthetic-digest"),
                        report_renderer.render_html(record, "synthetic-digest")):
            self.assertIn("0.5.0", content)
            self.assertIn("synthetic-standard-2", content)
            self.assertIn("43", content)
            self.assertIn("109", content)
            self.assertIn("27", content)
            self.assertIn("70%能力分", content)
            self.assertIn("选定7题", content)
            self.assertIn("矩阵任务及两份加强题含新原生初答", content)
            self.assertIn("尚无作者Lean证据", content)
            self.assertIn("既有发布资产保持不可变", content)
            self.assertNotIn("0.4.0综合重算", content)
            self.assertNotIn("0.4.0题库与任务包版本一致", content)

    def test_comparison_uses_metric_plans_and_current_paths(self):
        first, second = synthetic_report(), synthetic_report("gemini")
        # A stale presentation hint must not override the metric's planned count.
        first["profile"]["components"][0]["case_count"] = 18
        second["profile"]["components"][0]["case_count"] = 18
        data = comparison.presentation(*self.write_pair(first, second))
        self.assertEqual(data["component_counts"]["proofs"], 27)
        self.assertEqual(data["coverage"], {"initial_tasks": 46, "parent_families": 43,
                                            "all_records": 109})
        charts = [comparison.main_svg(data), comparison.chapters_svg(data),
                  comparison.answer_review_svg(data)]
        for chart in charts:
            ET.fromstring(chart)
        self.assertIn("27份任务", charts[0])
        self.assertIn("0.5.0", charts[0])
        self.assertIn("3份审阅单位", charts[2])
        self.assertEqual(data["chapter_completion"]["MG-C003"]["terra"], 46)
        for content in (comparison.render_html(data, *charts), comparison.render_markdown(data)):
            self.assertIn("46份任务", content)
            self.assertIn("43个母题家族", content)
            self.assertIn("109份记录", content)
            self.assertIn("44份任务、41个母题家族、107份记录", content)
            self.assertIn("comparison-2026-11-03", content)
            self.assertIn("0.5.0", content)
            self.assertNotIn("当前统一展示0.4.0", content)

    def test_unknown_metrics_and_completion_are_never_zero_filled(self):
        records = [synthetic_report(), synthetic_report("gemini")]
        for record in records:
            for metric in record["metrics"].values():
                metric["exact"] = None
            for row in record["slot_evidence"]:
                row["completion"]["exact"] = None
                if "major_error" in row:
                    row["major_error"] = None
                    row["strict_pass"] = None
            record["private_records"][0]["completion"]["exact"] = None
        data = comparison.presentation(*self.write_pair(*records))
        charts = [comparison.main_svg(data), comparison.chapters_svg(data),
                  comparison.answer_review_svg(data)]
        outputs = [*charts, comparison.render_html(data, *charts), comparison.render_markdown(data),
                   report_renderer.render_html(records[0], "synthetic-digest"),
                   report_renderer.render_markdown(records[0], "synthetic-digest")]
        for content in outputs:
            self.assertIn("待完成", content)
            self.assertNotIn("None", content)
            self.assertNotIn("nan", content.lower())
        self.assertIsNone(data["chapter_completion"]["MG-C002"]["terra"])
        empty_pair = []
        comparison.pair(empty_pair, 200, {"terra": None, "gemini": None})
        self.assertNotIn("<rect", "".join(empty_pair))
        self.assertNotIn("<circle", "".join(empty_pair))

    def test_comparison_rejects_mismatched_frozen_versions_or_denominators(self):
        for change, expected in (("version", "versions differ"),
                                 ("direction", "direction coverage differs"),
                                 ("families", "parent-family coverage differs")):
            with self.subTest(change=change):
                first, second = synthetic_report(), synthetic_report("gemini")
                if change == "version":
                    second["profile"]["version"] = "different"
                elif change == "direction":
                    second["metrics"]["proofs"]["coverage"]["planned"] += 1
                else:
                    second["coverage"]["parent_families"] += 1
                with self.assertRaisesRegex(ValueError, expected):
                    comparison.presentation(*self.write_pair(first, second))

    def test_new_execution_note_can_come_from_composition_without_relabeling_legacy(self):
        record = synthetic_report()
        record["methodology_revision"]["new_candidate_calls"] = 0
        record["composition"] = {"new_candidate_calls": 3}
        self.assertIn("含新原生初答", report_renderer.method_note(record))
        record["composition"]["new_candidate_calls"] = 0
        self.assertNotIn("含新原生初答", report_renderer.method_note(record))
        self.assertIn("复用既有原答", report_renderer.method_note(record))

    def test_frozen_attempt_and_round_fields_drive_every_rendered_view(self):
        for labels, rounds, expected in ((["A1", "A2"], 1, "各两次严格完成"),
                                         (["A1", "A2", "A3"], 2, "各三次严格完成")):
            with self.subTest(labels=labels, rounds=rounds):
                first, second = synthetic_report(), synthetic_report("gemini")
                for record in (first, second):
                    record["profile"]["repeat_attempt_labels"] = labels
                    record["profile"]["self_check_rounds_per_arm"] = rounds
                data = comparison.presentation(*self.write_pair(first, second))
                charts = [comparison.main_svg(data), comparison.chapters_svg(data),
                          comparison.answer_review_svg(data)]
                outputs = [report_renderer.render_html(first, "synthetic-digest"),
                           report_renderer.render_markdown(first, "synthetic-digest"),
                           charts[0], comparison.render_html(data, *charts),
                           comparison.render_markdown(data)]
                for content in outputs:
                    self.assertIn(expected, content)
                    self.assertIn(f"每分支{rounds}轮", content)
                    if len(labels) == 2:
                        self.assertNotIn("各三次", content)

    def test_attempt_fallback_requires_a_complete_consistent_slot_inventory(self):
        record = synthetic_report()
        record["metrics"]["repeat"]["coverage"]["planned"] = 2
        for labels in (("A1", "A2", "A3"), ("A1", "A2")):
            record["slot_evidence"] = [{"slot_id": f"SYNTHETIC-{case}:{label}"}
                                       for case in range(2) for label in labels]
            record["coverage"].update(a1_planned=2, slots_planned=2 * len(labels))
            self.assertEqual(report_renderer.repeat_attempt_labels(record), list(labels))
        record["slot_evidence"].pop()
        self.assertIn("次数待确认", report_renderer.reliability_description(record, "repeat"))
        record["profile"]["repeat_attempt_labels"] = ["A1", "A2"]
        self.assertIn("各两次", report_renderer.reliability_description(record, "repeat"))
        record["profile"]["repeat_attempt_labels"] = ["A1", "A1"]
        with self.assertRaisesRegex(ValueError, "Invalid frozen repeat"):
            report_renderer.reliability_description(record, "repeat")

    def test_comparison_does_not_mix_attempt_or_round_contracts(self):
        for field, first_value, second_value in (
                ("repeat_attempt_labels", ["A1", "A2"], ["A1", "A2", "A3"]),
                ("self_check_rounds_per_arm", 1, 2)):
            with self.subTest(field=field):
                first, second = synthetic_report(), synthetic_report("gemini")
                first["profile"][field] = first_value
                second["profile"][field] = second_value
                with self.assertRaisesRegex(ValueError, "Frozen scoring configuration differs"):
                    comparison.presentation(*self.write_pair(first, second))

    def test_cli_writes_only_requested_temporary_reports_and_keeps_input_json(self):
        terra, gemini = self.write_pair()
        original = {path: path.read_bytes() for path in (terra, gemini)}
        readme = self.root / "README.md"
        readme.write_text("unchanged before\n## 最新综合结果\nold\n## 分项与总分\nunchanged after\n")
        out = self.root / "comparison-2026-11-03"
        markdown = self.root / "comparison.md"
        environment = {**os.environ, "PYTHONDONTWRITEBYTECODE": "1"}
        subprocess.run([sys.executable, str(ROOT / "scripts/render_benchmark_comparison.py"),
                        "--terra", str(terra), "--gemini", str(gemini), "--out", str(out),
                        "--markdown", str(markdown), "--readme", str(readme)],
                       check=True, capture_output=True, text=True, env=environment)
        single_html, single_md = self.root / "single.html", self.root / "single.md"
        subprocess.run([sys.executable, str(ROOT / "scripts/render_benchmark_report.py"),
                        "--input", str(terra), "--html", str(single_html), "--markdown", str(single_md)],
                       check=True, capture_output=True, text=True, env=environment)
        self.assertEqual({path.name for path in out.iterdir()},
                         {"index.html", "comparison.svg", "chapters.svg", "answer-review.svg"})
        self.assertTrue(single_html.is_file() and single_md.is_file() and markdown.is_file())
        for path, raw in original.items():
            self.assertEqual(path.read_bytes(), raw)
        updated = readme.read_text()
        self.assertTrue(updated.startswith("unchanged before\n"))
        self.assertTrue(updated.endswith("## 分项与总分\nunchanged after\n"))
        self.assertIn("0.5.0", updated)
        self.assertIn("46份任务", updated)
        self.assertIn("comparison-2026-11-03", updated)


    def test_new_public_layout_links_skip_readme_and_preserve_legacy_assets(self):
        # Offline fixtures only: no model, Lean or scoring invocation.
        records = [synthetic_report(), synthetic_report("gemini")]
        for record in records:
            record["profile"].update(version="0.6.0", standard_version="0.6.0",
                                     repeat_attempt_labels=["A1", "A2"],
                                     self_check_rounds_per_arm=1,
                                     reliability_population="written-only")
            definitions = (("proofs", 14, 14, 22.5), ("lean-audit", 4, 2, 22.5),
                           ("lean-formalization", 4, 2, 45), ("answer-review", 4, 4, 10))
            record["profile"]["components"] = [
                {"id": key, "case_count": cases, "family_count": families,
                 "aggregation": "parent_family" if key == "answer-review" else "family", "weight": weight}
                for key, cases, families, weight in definitions]
            record["metrics"] = {key: {"exact": None, "coverage": {"planned": families}}
                                 for key, _, families, _ in definitions}
            record["metrics"].update({key: {"exact": None, "coverage": {"planned": count}}
                                      for key, count in (("repeat", 4), ("neutral", 4), ("stance", 8))})
            record["metrics"].update(core={"exact": None}, overall={"exact": None})
            record["coverage"].update(a1_planned=26, parent_families=18,
                                      slots_planned=42, slots_reviewed=0)
            record["strict_passes"] = {"core_A1": {"passed": None, "total": 26}}
            record["private_records"] = []
            record["formalization_scope"] = {cid: {"obligations": total}
                for cid, total in (("LCH01", 8), ("LCH02", 20), ("HCH02", 40), ("MG-C003", 92))}
            record["slot_evidence"] = [
                {"slot_id": cid + ":A1", "public_id": cid, "completion": {"exact": None},
                 "strict_pass": None, "status": "missing", "human_status": "pending"}
                for cid in record["formalization_scope"]]
            record["slot_evidence"].append({"slot_id": "OFFLINE-AR:A1", "public_id": "OFFLINE-AR",
                "completion": {"exact": None}, "major_error": None, "strict_pass": None,
                "status": "missing", "human_status": "pending", "dimensions": []})
        paths = []
        for name, record in zip(("terra", "gemini"), records):
            path = self.root / f"docs/results/{name}-v0.6.0/result.json"
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(json.dumps(record), encoding="utf-8")
            paths.append(path)
        old = self.root / "docs/results/comparison-2026-11-03/index.html"
        old.parent.mkdir(parents=True)
        old.write_text("OFFLINE FIXTURE: preserved old asset")
        readme = self.root / "README.md"
        readme.write_text("OFFLINE FIXTURE: README has no legacy sections")
        preserved = {path: path.read_bytes() for path in [old, readme, *paths]}
        out = self.root / "docs/results/comparison-v0.6.0"
        markdown = self.root / "docs/comparison-rendered-v0.6.0.md"
        published_markdown = self.root / "docs/benchmark-comparison-v0.6.0.md"
        published_markdown.write_text("OFFLINE FIXTURE: preserve reviewed Chinese explanation")
        preserved[published_markdown] = published_markdown.read_bytes()
        reports = [self.root / f"docs/{name}-v0.6.0.md" for name in ("terra", "gemini")]
        environment = {**os.environ, "PYTHONDONTWRITEBYTECODE": "1"}
        subprocess.run([sys.executable, str(ROOT / "scripts/render_benchmark_comparison.py"),
            "--terra", str(paths[0]), "--gemini", str(paths[1]), "--out", str(out),
            "--markdown", str(markdown), "--markdown-link", str(published_markdown),
            "--readme", str(readme), "--skip-readme",
            "--terra-report", str(reports[0]), "--gemini-report", str(reports[1])],
            check=True, capture_output=True, text=True, env=environment)
        for source, target in zip(paths, reports):
            subprocess.run([sys.executable, str(ROOT / "scripts/render_benchmark_report.py"),
                "--input", str(source), "--html", str(source.with_name("index.html")),
                "--markdown", str(target), "--comparison", str(out / "index.html")],
                check=True, capture_output=True, text=True, env=environment)
        for path, original in preserved.items():
            self.assertEqual(path.read_bytes(), original)
        import re
        outputs = [out / "index.html", markdown, *reports,
                   *(path.with_name("index.html") for path in paths)]
        for path in outputs:
            content = path.read_text()
            links = re.findall(r'(?:href|src)="([^"]+)"|\]\(([^)]+)\)', content)
            self.assertTrue(links)
            self.assertFalse(any("2026-11-03" in (html_link or md_link)
                                 for html_link, md_link in links))
            self.assertIn("待完成", content)
            self.assertIn("待判", content)
            self.assertNotIn("Private-Synthetic", content)
        html = (out / "index.html").read_text()
        self.assertIn("../../benchmark-comparison-v0.6.0.md", html)
        self.assertIn("4个能力方向", html)
        self.assertIn("4份任务 / 2个家族", html)
        self.assertNotIn("六方向能力", html)
        self.assertNotIn("34/92项", html)
        chart = (out / "chapters.svg").read_text()
        for cid, total in (("LCH01", 8), ("LCH02", 20), ("HCH02", 40), ("C003", 92)):
            self.assertIn(cid, chart)
            self.assertIn(f"{total}项本章义务", chart)
        self.assertNotIn("0/92", chart)
        for filename in ("comparison.svg", "chapters.svg", "answer-review.svg"):
            ET.fromstring((out / filename).read_text())

    def test_current_formalization_scope_is_required_and_all_directions_render(self):
        records = [synthetic_report(), synthetic_report("gemini")]
        for record in records:
            record["profile"]["components"].append({"id": "lean-formalization", "weight": 0,
                "case_count": 4, "aggregation": "family", "family_count": 2})
            record["metrics"]["lean-formalization"] = {"exact": None, "coverage": {"planned": 2}}
        with self.assertRaisesRegex(ValueError, "requires explicit formalization_scope"):
            comparison.presentation(*self.write_pair(*records))
        for record in records:
            record["formalization_scope"] = {"MG-C003": {"obligations": 92}}
        data = comparison.presentation(*self.write_pair(*records))
        chart = comparison.main_svg(data)
        self.assertIn("7个能力方向", chart)
        self.assertIn("大Lean形式化", chart)
        self.assertIn("真实答卷审阅", chart)
        ET.fromstring(chart)


if __name__ == "__main__":
    unittest.main()
