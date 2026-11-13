"""Adopt source-bound harness errata without rewriting frozen result records.

This evaluator-only owner verifies selection, original bytes and public views.
All score arithmetic remains in scoring.py; native ERROR receipts stay ERROR.
"""
from copy import deepcopy
from datetime import datetime, timezone, timedelta
from fractions import Fraction
import base64
import hashlib
import json
from pathlib import Path

from .records import evidence_bytes, project_assessment_score
from .claim_penalties import assess, validate_review

SCHEMA = 'math-gauge.harness-result-correction/v1'
MODES = ('capability', 'partial', 'strict')
CONDITION = 'nonlogical_retry_3'


def require(value, message):
    if not value:
        raise ValueError(message)


def read(folder, descriptor):
    return json.loads(evidence_bytes(folder, descriptor))


def reconstruct_rate_reviews(folder, patch):
    """Reuse all unchanged review bytes and apply one explicitly bound source task."""
    require(patch.get('schema') == 'math-gauge.content-review-source-correction/v1'
            and patch.get('case_id') == 'HCH02' and patch.get('scoring_rules_changed') is False,
            'Unsupported content-review source correction')
    content = read(folder, patch['base_content_review'])
    goals = read(folder, patch['base_goal_review'])
    for review, key in ((content, 'content_task'), (goals, 'goal_task')):
        old = next(row for row in review['tasks'] if row['case_id'] == 'HCH02')
        replacement = patch[key]
        require(all(old[field] == replacement[field] for field in
                    ('id', 'case_id', 'subcategory', 'family_id', 'kind', 'measured')),
                'Review source correction changed task membership or measurement')
        review['tasks'] = [deepcopy(replacement) if row['case_id'] == 'HCH02' else row for row in review['tasks']]
        review['sources'].extend(deepcopy(patch['appended_sources']))
    content['source_bindings'] = deepcopy(patch['content_source_bindings'])
    goals['source_bindings'] = deepcopy(patch['goal_source_bindings'])
    for review, key in ((content, 'reconstructed_content_sha256'), (goals, 'reconstructed_goal_sha256')):
        raw = (json.dumps(review, ensure_ascii=False, indent=2) + '\n').encode()
        require(hashlib.sha256(raw).hexdigest() == patch[key], 'Reconstructed review differs from its bound bytes')
    from .goal_attainment import goal_contract
    original_goals = read(folder, patch['base_goal_review'])
    require(goal_contract(goals['tasks']) == goal_contract(original_goals['tasks']),
            'Harness correction changed complete-goal definitions or weights')
    original_content = read(folder, patch['base_content_review'])
    before = next(row for row in original_content['tasks'] if row['case_id'] == 'HCH02')['units']
    after = patch['content_task']['units']
    require([(u['id'], u['label'], u['delivery_weight'], u['claim_weight']) for u in before]
            == [(u['id'], u['label'], u['delivery_weight'], u['claim_weight']) for u in after],
            'Harness correction changed assertion units or weights')
    return content, goals


_MISSING = object()


def _field(raw, key, *, default=_MISSING):
    """Read a bounded protobuf field without loading native code or a database."""
    pos = 0

    def varint():
        nonlocal pos
        value = shift = 0
        while pos < len(raw) and shift <= 70:
            byte = raw[pos]
            pos += 1
            value |= (byte & 127) << shift
            if byte < 128:
                return value
            shift += 7
        raise ValueError('Invalid recovered native protobuf')

    found = []
    while pos < len(raw):
        tag = varint()
        number, wire = tag >> 3, tag & 7
        if wire == 0:
            value = varint()
        elif wire in (1, 5):
            length = 8 if wire == 1 else 4
            value = raw[pos:pos + length]
            pos += length
        elif wire == 2:
            length = varint()
            value = raw[pos:pos + length]
            pos += length
        else:
            raise ValueError('Unsupported recovered native protobuf field')
        require(pos <= len(raw), 'Truncated recovered native protobuf')
        if number == key:
            found.append(value)
    if not found and default is not _MISSING:
        return default
    require(len(found) == 1, 'Recovered native field is missing or ambiguous')
    return found[0]


def verify_native_recovery(folder, proof):
    """Bind visible reply20.1 and its original completion clock; no new receipt."""
    require(proof.get('post_observation') is True and proof.get('original_native_status') == 'ERROR'
            and proof.get('native_status_rewritten') is False
            and proof.get('new_candidate_calls') == 0,
            'Recovery must preserve its original native failure and observation timing')
    original = read(folder, proof['original_terminal_seal'])
    require(original.get('native_status') == 'ERROR'
            and original.get('normal_complete_delivery') is False,
            'Recovery cannot manufacture a native success')
    payload = evidence_bytes(folder, proof['step_payload'])
    response = evidence_bytes(folder, proof['response'])
    require(_field(_field(payload, 20), 1) == response,
            'Recovered answer must be the exact original visible reply, never hidden reasoning')
    witness = read(folder, proof['clock_witness'])
    require(witness.get('post_observation') is True
            and witness.get('not_an_execution_time_seal') is True
            and witness['conversation_id'] == proof['conversation_id']
            and sum(row['step_type'] == 14 for row in witness['rows']) == 1,
            'Recovered reply lost its single-context native identity')
    selected = [row for row in witness['rows'] if row['idx'] == proof['step_index']]
    require(len(selected) == 1 and selected[0]['step_type'] == 15
            and selected[0]['payload_sha256'] == hashlib.sha256(payload).hexdigest(),
            'Recovered reply differs from the original native step')
    metadata = base64.b64decode(selected[0]['original_metadata_b64'], validate=True)
    require(hashlib.sha256(metadata).hexdigest() == selected[0]['metadata_sha256'],
            'Recovered native metadata changed')
    stamp = _field(metadata, 8)
    nanos = _field(stamp, 2, default=0)
    require(isinstance(nanos, int) and 0 <= nanos < 1_000_000_000,
            'Invalid native completion clock')
    completed = datetime.fromtimestamp(_field(stamp, 1), timezone.utc) + timedelta(microseconds=nanos // 1000)
    started = datetime.fromisoformat(proof['started_at'])
    require(completed.isoformat() == proof['completed_at']
            and 0 <= (completed - started).total_seconds() <= proof['original_timeout_seconds']
            and completed <= datetime.fromisoformat(original['utc']),
            'Recovered reply was not complete before its original deadline')
    return {'response_sha256': hashlib.sha256(response).hexdigest(),
            'original_native_status': 'ERROR', 'completed_at': completed.isoformat()}


def load_selected(root, model_id, folder, *, record=None):
    """Only explicitly selected errata can replace current presentation views."""
    root, folder = Path(root), Path(folder)
    edition = json.loads((root / 'benchmark.json').read_bytes())
    selected = edition.get('result_corrections', {}).get(model_id)
    if selected is None:
        return None
    correction = read(root, selected)
    require(correction.get('schema') == SCHEMA and correction.get('version') == '0.1.0'
            and correction.get('visibility') == 'public-projection'
            and correction.get('benchmark_version') == edition['version']
            and correction.get('model_id') == model_id
            and correction.get('record_id') == folder.name
            and correction.get('new_candidate_calls') == 0
            and correction.get('scoring_rules_changed') is False
            and correction.get('native_status_rewritten') is False
            and correction.get('reviewer_kind') == 'ai'
            and correction.get('formal_comparison_eligible') is False
            and correction.get('affected_conditions') == [CONDITION]
            and correction.get('affected_cases') == ['HCH02'],
            'Invalid selected harness correction')
    original = read(folder, correction['base_record'])
    require(record is None or original == record, 'Harness correction binds a different original record')
    require(correction.get('user_adoption', {}).get('explicit') is True
            and correction['user_adoption'].get('post_observation') is True,
            'Harness recovery needs its separately recorded adoption')
    review = read(folder, correction['math_review'])
    answer = evidence_bytes(folder, correction['answer'])
    require(hashlib.sha256(answer).hexdigest() == correction['source_response_sha256']
            == review['source_response_sha256']
            and review.get('source_repaired') is False
            and review.get('new_candidate_calls') == 0
            and len(review.get('credit_units', [])) == 40,
            'Harness correction changed its original answer or mathematical inventory')
    claims = read(folder, correction['claim_review'])
    task_claim = claims['case']
    validate_review({'schema': 'math-gauge.claim-review-condition/v1', 'policy_version': '0.1.0',
        'reviewer_kind': 'ai', 'human_review': 'pending', 'formal_comparison_eligible': False,
        'cases': [task_claim]})
    require(task_claim['source_response_sha256'] == correction['source_response_sha256'],
            'Corrected commitment review belongs to another answer')
    units = review['credit_units']
    maximum = sum(Fraction(str(unit['maximum'])) for unit in units)
    value = sum((Fraction(str(unit['earned'])) for unit in units), Fraction()) / maximum
    expected = {}
    for mode in MODES:
        result, passed, _ = assess((value,) * 3, review['complete'], task_claim, mode=mode)
        expected[mode] = (Fraction(int(passed)),) * 3 if mode == 'strict' else result
    projection = read(folder, correction['public_tasks'])
    original_tasks = json.loads((folder / 'public-task-scores.json').read_bytes())
    require(projection['public_case_ids'] == original_tasks['public_case_ids']
            and set(projection['views']) == set(MODES), 'Harness correction changed public task membership')
    scores = {}
    keys = {'capability': 'capability_results', 'partial': 'assessment_results', 'strict': 'strict_results'}
    for mode in MODES:
        score = read(folder, correction['scores'][mode])
        base = read(folder, original[keys[mode]][CONDITION])
        require(project_assessment_score(score) == score
                and score['score_mode'] == mode and score['attempt_condition'] == CONDITION
                and all(score.get(key) == base.get(key) for key in
                        ('benchmark_version', 'scoring_method_version', 'strict_method_version',
                         'claim_penalty_policy_sha256', 'capacity', 'group_capacity')),
                'Harness correction changed scoring rules or the fixed benchmark frame')
        before = original_tasks['views'][mode]
        after = projection['views'][mode]
        require(after['single_attempt'] == before['single_attempt'], 'Harness correction changed first attempts')
        rows = after[CONDITION]['tasks']
        require([row['case_id'] for row in rows] == projection['public_case_ids'],
                'Harness correction repeated or omitted a public task')
        for old, new in zip(before[CONDITION]['tasks'], rows):
            if old['case_id'] != 'HCH02':
                require(old == new, 'Harness correction changed an unrelated answer')
            else:
                require(new['response_sha256'] == correction['source_response_sha256']
                        and new['review_sha256'] == review.get('private_review_sha256', correction['math_review']['sha256'])
                        and tuple(Fraction(str(new['completion'][key])) for key in ('lower', 'upper', 'exact'))
                        == expected[mode], 'Corrected task differs from its original unit and claim review')
        require(after[CONDITION]['source_report_sha256'] == score['source_bindings']['private_report_sha256'],
                'Corrected public tasks lost their shared scorer source')
        scores[mode] = score
    correction['_scores'] = scores
    correction['_tasks'] = projection
    correction['_claim'] = task_claim
    correction['_math_review'] = review
    correction['_selection'] = selected
    if correction.get('rates') is not None:
        from .content_rates import validate_public_rates
        rates = validate_public_rates(read(folder, correction['rates']))
        require(rates['source_bindings']['record_sha256'] == correction['base_record']['sha256']
                and rates['source_bindings']['assessment_result_sha256'] == correction['scores']['partial']['sha256'],
                'Corrected rates bind different original records or selected scores')
        correction['_rates'] = rates
    return correction


def verify_private(private_root, public_root, model_id, folder, public_correction):
    """Audit the private recovery witnesses and their exact public projections."""
    private_root, public_root, folder = map(Path, (private_root, public_root, folder))
    edition = json.loads((private_root / 'benchmark.json').read_bytes())
    selected = edition.get('result_corrections', {}).get(model_id)
    require(selected is not None and selected['sha256'] == public_correction['private_correction_sha256'],
            'Public and private harness correction selections differ')
    correction = read(private_root, selected)
    require(correction['visibility'] == 'private' and all(correction[key] == public_correction[key] for key in
            ('schema', 'version', 'benchmark_version', 'model_id', 'record_id', 'affected_cases',
             'affected_conditions', 'source_response_sha256', 'scoring_rules_changed',
             'native_status_rewritten', 'new_candidate_calls', 'user_adoption')),
            'Private harness recovery has a different adoption boundary')
    original = read(folder, correction['base_record'])
    verify_native_recovery(folder, read(folder, correction['native_proof']))
    review = read(folder, correction['math_review'])
    for descriptor in review['evidence']:
        evidence_bytes(folder, descriptor)
    claims = read(folder, correction['claim_condition'])
    validate_review(claims)
    require(correction['math_review']['sha256'] == public_correction['_math_review']['private_review_sha256'],
            'Public math review binds another private original')
    keys = {'capability': 'capability_results', 'partial': 'assessment_results', 'strict': 'strict_results'}
    reports = {}
    for mode in MODES:
        report = read(folder, correction['scores'][mode])
        projection = project_assessment_score(report)
        projection['source_bindings']['private_report_sha256'] = correction['scores'][mode]['sha256']
        require(projection == public_correction['_scores'][mode],
                'Corrected public score differs from its private shared scorer report')
        before = read(folder, original[keys[mode]][CONDITION])['tasks']
        after = report['tasks']
        require([r['case_id'] for r in before] == [r['case_id'] for r in after]
                and all(old == new for old, new in zip(before, after) if old['case_id'] != 'HCH02'),
                'Harness recovery changed unrelated private task judgments')
        binding = report['source_bindings']
        require(binding['harness_recovery_proof_sha256'] == correction['native_proof']['sha256']
                and binding['corrected_claim_condition_sha256'] == correction['claim_condition']['sha256']
                and binding['recovered_math_review_sha256'] == correction['math_review']['sha256'],
                'Corrected private score lost its recovery or review bindings')
        reports[mode] = report
    from .content_rates import project_rates, validate_review as validate_content, verify_sources
    from .goal_attainment import validate_goal_review
    from .scoring import score_content_rates
    content, goals = reconstruct_rate_reviews(folder, read(folder, correction['rate_patch']))
    assessment = json.loads((public_root / 'protocol/scoring-policy.json').read_bytes())
    validate_content(content, assessment, reports['partial'])
    validate_goal_review(goals, content, assessment, reports['partial'])
    for source_review in (content, goals):
        verify_sources(source_review, {'public': public_root, 'private': private_root})
    rates = score_content_rates(content, assessment, goals)
    patch = read(folder, correction['rate_patch'])
    rates.update(private_review_sha256=patch['reconstructed_content_sha256'],
                 private_goal_review_sha256=patch['reconstructed_goal_sha256'])
    require(rates == read(folder, correction['rates']) and project_rates(rates) == public_correction['_rates'],
            'Corrected rates differ from their original source review patch')
    return reports
