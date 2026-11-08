"""Complete results are distinct from fine coverage and actual-content truth."""
import copy
import hashlib
import json
from pathlib import Path
import tempfile
import unittest

import test_content_rates
from math_gauge.content_rates import project_rates, validate_public_rates
from math_gauge.goal_attainment import definition_digest, validate_goal_review
from math_gauge.records import load_content_rates
from math_gauge.scoring import score_content_rates


class GoalAttainmentTests(unittest.TestCase):
    def fixture(self):
        content, policy = test_content_rates.ContentRateTests().fixture()
        goals = {key: copy.deepcopy(value) for key, value in content.items()
                 if key not in ('tasks', 'schema', 'version')}
        goals.update(schema='math-gauge.goal-attainment-review/v1', version='0.2.0',
                     post_observation=True, tasks=[])
        goals['source_bindings'].update(content_review_sha256='b' * 64,
                                        content_method_policy_sha256='a' * 64)
        for task in content['tasks']:
            row = {key: copy.deepcopy(value) for key, value in task.items() if key != 'units'}
            row['goals'] = [dict(id='complete-result', label='Complete original result',
                statement='The complete result requested by the original task',
                scope='All original hypotheses, quantifiers and boundary cases', weight=1,
                weight_origin='Original independent result', acceptance_conditions=[
                    'Correct, proved, aligned and actually delivered'], dependency_scope=[],
                required_goals=[], source_unit_ids=['goal'], passed=True,
                reason='Source result independently complete',
                definition_evidence=copy.deepcopy(task['units'][0]['evidence']),
                evidence=copy.deepcopy(task['units'][0]['evidence']))]
            goals['tasks'].append(row)
        self.freeze(goals)
        return content, goals, policy

    def freeze(self, goals):
        goals['goal_definition_sha256'] = definition_digest(goals['tasks'])

    def public(self, content, goals, policy):
        result = score_content_rates(content, policy, goals)
        result.update(private_review_sha256='b' * 64, private_goal_review_sha256='c' * 64)
        return project_rates(result)

    def test_fine_partial_coverage_does_not_deliver_complete_result(self):
        content, goals, policy = self.fixture()
        task = content['tasks'][0]
        task['units'].append(dict(copy.deepcopy(task['units'][0]), id='missing-proof',
                                  fulfillment='omitted', assertion='none'))
        goal = goals['tasks'][0]['goals'][0]
        goal.update(passed=False, reason='Necessary closure proof not delivered')
        goal['source_unit_ids'].append('missing-proof')
        self.freeze(goals)
        legacy = score_content_rates(content, policy)
        result = score_content_rates(content, policy, goals)
        self.assertEqual(result['metrics']['reliability'], legacy['metrics']['reliability'])
        self.assertLess(result['categories']['written-argument']['attainment']['confirmed'],
                        legacy['categories']['written-argument']['delivery']['confirmed'])
        self.assertEqual(result['metrics']['reliability']['exact'], 100)

    def test_independent_goal_survives_detachable_false_extra(self):
        content, goals, policy = self.fixture()
        task = content['tasks'][0]
        task['units'].append(dict(copy.deepcopy(task['units'][0]), id='false-extra',
                                  delivery_weight=0, assertion='incorrect'))
        result = score_content_rates(content, policy, goals)
        self.assertEqual(result['metrics']['attainment']['exact'], 100)
        self.assertLess(result['metrics']['reliability']['exact'], 100)
        # A mathematically valid result outside the original requested scope is
        # still reliable content, but cannot count as the original complete goal.
        goals['tasks'][0]['goals'][0].update(passed=False, reason='Wrong original scope')
        narrowed = score_content_rates(content, policy, goals)
        self.assertEqual(narrowed['metrics']['reliability'], result['metrics']['reliability'])
        self.assertLess(narrowed['metrics']['attainment']['confirmed'], 100)

    def test_retaining_old_correct_engineering_is_not_complete_repair(self):
        content, goals, policy = self.fixture()
        for task in goals['tasks']:
            if task['kind'] == 'selfcheck':
                task['goals'][0].update(passed=False,
                    reason='Retained earlier correct obligations; necessary repairs remain')
        result = score_content_rates(content, policy, goals)
        self.assertEqual(result['categories']['lean-selfcheck']['attainment']['exact'], 0)
        self.assertEqual(result['categories']['lean-selfcheck']['reliability']['exact'], 100)

    def test_multiple_results_can_partly_attain_without_accepting_whole_task(self):
        content, goals, policy = self.fixture()
        task = goals['tasks'][0]
        task['goals'].append(dict(copy.deepcopy(task['goals'][0]), id='second-result',
                                 passed=False, reason='Second independent result not delivered'))
        self.freeze(goals)
        result = score_content_rates(content, policy, goals)
        self.assertEqual(result['tasks'][0]['metrics']['attainment']['exact'], 50)

    def test_unknowns_keep_fixed_family_and_category_denominators(self):
        content, goals, policy = self.fixture()
        by_id = {task['id']: task for task in goals['tasks']}
        for task in content['tasks']:
            if task['subcategory'] in ('background-check', 'manuscript-completion', 'theorem-extension'):
                task['measured'] = False
                task['units'][0].update(fulfillment='unknown', assertion='unknown', aligned=None)
                by_id[task['id']]['measured'] = False
                by_id[task['id']]['goals'][0]['passed'] = None
        result = score_content_rates(content, policy, goals)
        self.assertEqual((result['metrics']['attainment']['confirmed'],
                          result['metrics']['attainment']['upper'],
                          result['metrics']['attainment']['exact']), (70, 100, None))
        self.assertEqual(result['metrics']['reliability']['observed'], 100)
        self.assertEqual(result['metrics']['reliability']['lower'], 70)

    def test_failed_dependency_and_silent_definition_change_are_rejected(self):
        content, goals, policy = self.fixture()
        task = goals['tasks'][0]
        task['goals'].append(dict(copy.deepcopy(task['goals'][0]), id='needed-object',
                                 passed=False, reason='Required object lacks representation bridge'))
        task['goals'][0]['required_goals'] = ['needed-object']
        self.freeze(goals)
        with self.assertRaisesRegex(ValueError, 'unmet necessary dependency'):
            validate_goal_review(goals, content, policy)
        task['goals'][0]['passed'] = False
        validate_goal_review(goals, content, policy)
        task['goals'][0]['weight'] = 9
        with self.assertRaisesRegex(ValueError, 'definition digest'):
            validate_goal_review(goals, content, policy)

    def test_v2_projection_never_relabels_legacy_coverage_or_leaks_goals(self):
        content, goals, policy = self.fixture()
        report = self.public(content, goals, policy)
        self.assertEqual(report['version'], '0.2.0')
        self.assertNotIn('delivery', report['metrics'])
        self.assertNotIn('tasks', report)
        self.assertNotIn('source_unit_ids', json.dumps(report))
        report['categories']['written-argument']['coverage']['private-goal-name'] = 1
        with self.assertRaises(ValueError):
            validate_public_rates(report)

    def test_v2_record_binds_both_method_versions_and_selected_source(self):
        content, goals, policy = self.fixture()
        report = self.public(content, goals, policy)
        with tempfile.TemporaryDirectory() as directory:
            folder = Path(directory) / report['model_id'] / 'record'
            folder.mkdir(parents=True)
            def write(name, value):
                path = folder / name
                path.write_text(json.dumps(value))
                return dict(path=name, bytes=path.stat().st_size,
                            sha256=hashlib.sha256(path.read_bytes()).hexdigest())
            score = write('score.json', {'unchanged': True})
            assessment = write('assessment.json', policy)
            legacy = write('content-rate-policy.json', {'version': '0.1.0'})
            method = write('goal-attainment-policy.json', {'version': '0.2.0'})
            record = {'assessment_results': {'nonlogical_retry_3': score}, 'assessment_policy': assessment}
            source = write('record.json', record)
            report['source_bindings'].update(record_sha256=source['sha256'],
                assessment_result_sha256=score['sha256'], assessment_policy_sha256=assessment['sha256'],
                method_policy_sha256=method['sha256'], content_method_policy_sha256=legacy['sha256'])
            report['assessment_policy_sha256'] = assessment['sha256']
            write('content-rates.json', report)
            self.assertEqual(load_content_rates(folder), report)
            write('content-rate-policy.json', {'version': 'changed'})
            with self.assertRaises(ValueError):
                load_content_rates(folder)


if __name__ == '__main__':
    unittest.main()
