"""Prepare and adopt the source-bound HCH02 harness erratum; no model calls."""
from pathlib import Path
import argparse
import sqlite3
import shutil
import re
from copy import deepcopy
from fractions import Fraction
import hashlib
import json
import sys

ROOT = Path(__file__).resolve().parents[1]
PRIVATE = ROOT.parent / 'math-gauge-private'
HERE = None
CORRECTION_REL = Path('harness-corrections/20261113-HCH02')
FOLDER = PRIVATE / 'results/v0.6.0/gemini-4-argon/20261111'
PUBLIC = ROOT / 'results/v0.6.0/gemini-4-argon/20261111'
sys.path.insert(0, str(ROOT))
from math_gauge.evidence_retention import read_json
from math_gauge.records import (evidence_bytes, load_claim_review, load_written_argument_inputs,
                               load_written_replacement_inputs)
from math_gauge.attempt_conditions import load_sources
from math_gauge import submission_evidence
from math_gauge.scoring import (score_assessment_record_inputs, score_assessment_inputs,
    formalization_substitutions, score_record_inputs, strict_alignment_trajectory,
    _alignment_trajectory, submission_formalization_breakdown)
from math_gauge.records import project_assessment_score, project_public_task_view
from math_gauge.content_rates import project_rates
from math_gauge.scoring import score_content_rates
from math_gauge.result_corrections import (verify_native_recovery, load_selected, require,
                                         reconstruct_rate_reviews)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def desc(path, raw):
    return {'path': path, 'bytes': len(raw), 'sha256': sha(raw)}


def encoded(data):
    return (json.dumps(data, ensure_ascii=False, indent=2) + '\n').encode()


def bound(root, record, key):
    return json.loads(evidence_bytes(root, record[key]))


def main():
    condition = 'nonlogical_retry_3'
    record = read_json(FOLDER / 'record.json')
    sources = load_sources(FOLDER, record, condition, public_root=PUBLIC)
    source_policy = bound(PUBLIC, record, 'scoring_policy')
    assessment = bound(PUBLIC, record, 'assessment_policy')
    strict = bound(PUBLIC, record, 'strict_scoring_policy')
    capability = bound(PUBLIC, record, 'capability_scoring_policy')
    claim_policy = bound(PUBLIC, record, 'claim_penalty_policy')
    claims = load_claim_review(FOLDER, record, condition, public_root=PUBLIC)
    submission = submission_evidence.load_condition(FOLDER, record, condition)
    submission_policy = submission_evidence.load_policy(FOLDER, record)
    common = dict(assessment_policy=assessment, strict_policy=strict,
        theorem_extension_inputs=sources['theorem_extension_inputs'],
        background_check_inputs=sources['background_check_inputs'],
        capability_policy=capability, claim_review=claims, claim_policy=claim_policy,
        written_argument_inputs=load_written_argument_inputs(FOLDER, record, policy=assessment['written_argument_additions']),
        written_replacement_inputs=load_written_replacement_inputs(FOLDER, record, policy=assessment['written_argument_replacements']),
        manuscript_completion_inputs=sources['manuscript'], submission_review=submission,
        submission_policy=submission_policy)
    case = next(row for row in sources['inputs']['plan']['case_index'] if row['case_id'] == 'HCH02')
    raw_path = 'timing-corrections/20261113-agy-idle-tail/HCH02-backend-response.txt'
    raw = (FOLDER / raw_path).read_bytes()
    assert sha(raw) == '181d1ddd7dcf4e98ed83f433e7ae85f07384617f960c7c50a1fc2f1c2b84c2d4'
    source = desc(raw_path, raw)
    check_path = 'timing-corrections/20261113-agy-idle-tail/HCH02-recovered-check.json'
    log_path = 'timing-corrections/20261113-agy-idle-tail/HCH02-recovered-compile.log'
    check_raw, log_raw = (FOLDER / check_path).read_bytes(), (FOLDER / log_path).read_bytes()
    check = json.loads(check_raw)
    require(check['compile_log_sha256'] == sha(log_raw)
            and check['compile_exit_code'] == 1 and check['no_source_repair'] is True,
            'Original unchanged compilation evidence no longer matches')
    review_relative = (CORRECTION_REL / 'math-review.json').as_posix()
    units = [{'id': unit['stage_id'], 'maximum': unit.get('weight', 1), 'earned': 0,
              'reason': 'The only submitted target module fails unmodified kernel compilation. No required declaration can be accepted from that failed module by truncation, repair or substitution of a different workspace file.'}
             for unit in case['stages']]
    review = {
        'schema': 'math-gauge.normal-final-math-review/v1', 'version': '0.1.0',
        'case_id': 'HCH02', 'phase': 'A1', 'attempt_condition': condition,
        'case_contract_sha256': case['group_contract_sha256'],
        'reviewer_kind': 'ai', 'reviewer': 'Codex supplemental source review, current session',
        'human_review': 'pending', 'source_response_sha256': sha(raw),
        'source_repaired': False, 'new_candidate_calls': 0, 'candidate_scripts_executed': False,
        'original_final_existence_verified': True, 'complete': False, 'credit_units': units,
        'evidence': [source, desc(check_path, check_raw), desc(log_path, log_raw)],
        'compilation': {key: check[key] for key in ('lean_version', 'main_sha256', 'alignment_sha256',
            'no_source_repair', 'compile_exit_code', 'compile_log_sha256', 'source_is_original_reply_code_block')},
        'post_observation': True,
        'original_backend_reply_existence_only': True,
        'normal_cli_delivery_admitted': False, 'not_an_execution_receipt': True,
        'recovered_math_reply_adopted': True,
        'original_native_status': 'ERROR', 'observed_on': '2026-11-13',
        'finding': 'The original visible backend reply is recovered and adopted after a harness fault, but its Main.lean fails at line1120. This mathematical source correction does not promote native ERROR to success.'}
    review_bytes = encoded(review)
    review_descriptor = desc(review_relative, review_bytes)
    (HERE / 'HCH02-proposed-math-review.json').write_bytes(review_bytes)
    findings = [{
        'id': 'HCH02-recovered-final-false-verification',
        'root_cause': 'original-final-false-kernel-completion',
        'severity': 'critical', 'kind': 'false_verification', 'core_endorsement': True,
        'covered_by': 'none', 'strict_blocking': True,
        'reason': 'The submitted full target module fails in the pinned environment, while the original reply explicitly certifies complete kernel verification and all40 obligations. This matches the retained Gemini3.8Flash HCH02 precedent; the correct sealed workspace cannot replace the differing reply.',
        'evidence': [
            {'source': 0, 'quote': '完整完成与严格对齐'},
            {'source': 0, 'quote': '通过内核完整编译（0 错误、0 警告）'},
            {'source': 1, 'json_pointer': '/finding', 'quote': 'its Main.lean fails at line1120'}]}]
    for finding in findings:
        for item in finding['evidence']:
            haystack = raw.decode() if item['source'] == 0 else review['finding']
            assert item['quote'] in haystack, item
    proposed_inputs = deepcopy(sources['inputs'])
    target = next(row for row in proposed_inputs['slots'] if row['slot_id'] == 'HCH02:A1')
    target.update(response_sha256=sha(raw), review_sha256=review_descriptor['sha256'],
                  completion={'lower': 0, 'upper': 0, 'exact': 0}, strict_pass=False)
    proposed_claims = deepcopy(claims)
    claim = next(row for row in proposed_claims['cases'] if row['case_id'] == 'HCH02')
    claim.update(status='reviewed', source_response_sha256=sha(raw),
        source_review_sha256=review_descriptor['sha256'], sources=[source, review_descriptor], findings=findings,
        scope_note='Adopted source-bound review of the recovered original backend reply; the native CLI ERROR remains unchanged. This is not a new execution receipt.')
    proposed_submission = deepcopy(submission)
    delivery = next(row for row in proposed_submission['initials'] if row['case_id'] == 'HCH02')
    for key in ('work', 'work_review', 'mathematical_source'):
        delivery.pop(key, None)
    delivery.update(classification='active_final',
        reason='Original visible backend reply recovered and explicitly adopted after a harness delivery fault. Its original native ERROR receipt is unchanged.',
        source_response_sha256=sha(raw), normal_review=review_descriptor, normal_math=review)
    result = {'schema': 'math-gauge.supplemental-review-impact/v1', 'observed_on': '2026-11-13',
        'new_candidate_calls': 0, 'scores_modified': False, 'current_record_unchanged': True,
        'counterfactual_not_adopted': False, 'adopted_harness_correction': True, 'attempt_condition': condition,
        'only_case_changed': 'HCH02', 'case_review_sha256': sha(review_bytes), 'modes': {}}
    substitution = formalization_substitutions(sources['inputs'], sources['engineering'])
    for mode, result_key in [('capability', 'capability_results'), ('partial', 'assessment_results'), ('strict', 'strict_results')]:
        baseline = score_assessment_record_inputs(sources['inputs'], sources['alignment'], source_policy,
            formalization_review=sources['engineering'], mode=mode, **common)
        archived = bound(FOLDER, {result_key: record[result_key][condition]}, result_key)
        assert baseline['metrics'] == archived['metrics'], ('baseline metrics differ', mode)
        assert baseline['tasks'] == archived['tasks'], ('baseline task judgments differ', mode)
        old_source = score_record_inputs(sources['inputs'], sources['alignment'], source_policy,
                                        formalization_review=sources['engineering'])
        alignment = (_alignment_trajectory(sources['alignment'], source_policy, positive_only=True)[0]
                     if mode == 'capability' else old_source['alignment_selfcheck'])
        trajectory = strict_alignment_trajectory(sources['alignment'], source_policy)
        if submission.get('normal_alignment') is not None:
            selected = submission['normal_alignment']
            alignment = _alignment_trajectory(selected, source_policy, positive_only=mode == 'capability', allow_submission_sources=True)[0]
            trajectory = strict_alignment_trajectory(selected, source_policy, allow_submission_sources=True)
        preview_common = {**common, 'claim_review': proposed_claims, 'submission_review': proposed_submission}
        preview = score_assessment_inputs(proposed_inputs, mode=mode, mathematical_substitutions=substitution,
            alignment_summary=alignment, strict_trajectory=trajectory, **preview_common)
        retained = {**deepcopy(archived), **preview}
        retained['lean_formalization_breakdown'] = submission_formalization_breakdown(
            baseline['lean_formalization_breakdown'], proposed_submission)
        retained['source_bindings']['corrected_claim_condition_sha256'] = sha(encoded(proposed_claims))
        retained['source_bindings']['recovered_response_sha256'] = sha(raw)
        retained['source_bindings']['recovered_math_review_sha256'] = review_descriptor['sha256']
        retained['source_selection_correction'] = {
            'kind': 'harness_recovered_original_reply', 'case_id': 'HCH02',
            'original_native_status': 'ERROR', 'scoring_rules_changed': False,
            'user_adopted_after_observation': True, 'new_candidate_calls': 0}
        (HERE / ('HCH02-corrected-' + mode + '.json')).write_bytes(encoded(retained))
        before = next(row for row in baseline['tasks'] if row['case_id'] == 'HCH02')
        after = next(row for row in preview['tasks'] if row['case_id'] == 'HCH02')
        for row in baseline['tasks']:
            if row['case_id'] != 'HCH02':
                assert row == next(other for other in preview['tasks'] if other['case_id'] == row['case_id']), row['case_id']
        result['modes'][mode] = {
            'baseline_earned': baseline['metrics']['earned'], 'proposed_earned': preview['metrics']['earned'],
            'hch02_before': before, 'hch02_proposed': after,
            'other_task_rows_unchanged': True,
            'delta_confirmed': preview['metrics']['earned']['confirmed'] - baseline['metrics']['earned']['confirmed']}
    (HERE / 'HCH02-score-impact.json').write_bytes(encoded(result))
    (HERE / 'HCH02-corrected-claim-condition.json').write_bytes(encoded(proposed_claims))
    (HERE / 'HCH02-proposed-claim-findings.json').write_bytes(encoded({'findings': findings, 'sources': [source, review_descriptor]}))
    print(json.dumps({mode: {'before': row['baseline_earned']['confirmed'],
                            'after': row['proposed_earned']['confirmed'],
                            'delta': row['delta_confirmed'],
                            'hch02_completion': row['hch02_proposed']['completion']}
                      for mode, row in result['modes'].items()}, ensure_ascii=False))


def prepare_packages():
    """Write complete review artifacts before changing either selection pointer."""
    def put(side, name, data):
        raw = data if isinstance(data, bytes) else encoded(data)
        path = HERE / side / CORRECTION_REL / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(raw)
        return desc((CORRECTION_REL / name).as_posix(), raw)

    packet = FOLDER / 'timing-corrections/20261113-agy-idle-tail'
    recovered = read_json(packet / 'recovery.json')['cases']['HCH02']
    witness = read_json(FOLDER / recovered['clock_witness']['path'])
    database = Path(witness['database_path'])
    existing_payload = FOLDER / CORRECTION_REL / 'native-step116.pb'
    if existing_payload.exists():
        payload = existing_payload.read_bytes()
    else:
        require(sha(database.read_bytes()) == witness['database_sha256'], 'Original recovery database changed')
        with sqlite3.connect(database.resolve().as_uri() + '?mode=ro&immutable=1', uri=True) as connection:
            payload = connection.execute('SELECT step_payload FROM steps WHERE idx=116').fetchone()[0]
    payload_descriptor = put('private', 'native-step116.pb', payload)
    raw_path = 'timing-corrections/20261113-agy-idle-tail/HCH02-backend-response.txt'
    answer = evidence_bytes(FOLDER, desc(raw_path, (FOLDER / raw_path).read_bytes()))
    original_row = recovered['original_timing_row']
    proof = {
        'schema': 'math-gauge.recovered-agy-reply-proof/v1', 'post_observation': True,
        'new_candidate_calls': 0, 'original_native_status': 'ERROR', 'native_status_rewritten': False,
        'conversation_id': witness['conversation_id'], 'step_index': 116,
        'clock_witness': recovered['clock_witness'], 'step_payload': payload_descriptor,
        'response': desc(raw_path, answer), 'started_at': recovered['started_at'],
        'completed_at': recovered['boundary_at'], 'original_timeout_seconds': 5400,
        'original_terminal_seal': original_row['time_binding']['end']['source'],
        'original_execution': original_row['time_binding']['start']['source'],
        'observation_date': '2026-11-13', 'original_database_sha256': witness['database_sha256'],
    }
    proof_descriptor = put('private', 'native-recovery-proof.json', proof)
    math_private = json.loads((HERE / 'HCH02-proposed-math-review.json').read_bytes())
    math_descriptor = put('private', 'math-review.json', math_private)
    claims_full = json.loads((HERE / 'HCH02-corrected-claim-condition.json').read_bytes())
    claims_descriptor = put('private', 'claim-condition.json', claims_full)
    claim_case = next(row for row in claims_full['cases'] if row['case_id'] == 'HCH02')
    public_answer = put('public', 'answer.md', answer)
    math_public = deepcopy(math_private)
    math_public['evidence'] = [public_answer]
    math_public['private_review_sha256'] = math_descriptor['sha256']
    public_math = put('public', 'math-review.json', math_public)
    public_claim = deepcopy(claim_case)
    public_claim['sources'] = [public_answer, public_math]
    public_claim_descriptor = put('public', 'claim-review.json', {'case': public_claim})
    private_reports, public_reports = {}, {}
    projection = read_json(PUBLIC / 'public-task-scores.json')
    for mode in ('capability', 'partial', 'strict'):
        score = json.loads((HERE / ('HCH02-corrected-' + mode + '.json')).read_bytes())
        score['source_bindings'].update(harness_recovery_proof_sha256=proof_descriptor['sha256'],
                                        corrected_claim_condition_sha256=claims_descriptor['sha256'])
        private_reports[mode] = put('private', mode + '-retry.json', score)
        public_score = project_assessment_score(score)
        public_score['source_bindings']['private_report_sha256'] = private_reports[mode]['sha256']
        public_reports[mode] = put('public', mode + '-retry.json', public_score)
        projection['views'][mode]['nonlogical_retry_3'] = project_public_task_view(
            score, projection['public_case_ids'], private_reports[mode]['sha256'])
    tasks_descriptor = put('public', 'public-task-scores.json', projection)

    # Retain only changed rate tasks, not another copy of the unchanged ~2MB review.
    content = read_json(FOLDER / 'content-rate-review.json')
    goals = read_json(FOLDER / 'goal-attainment-review.json')
    target = next(task for task in content['tasks'] if task['case_id'] == 'HCH02')
    source_ref = {'repository': 'private', 'path': str(FOLDER.relative_to(PRIVATE) / math_descriptor['path']),
                  'sha256': math_descriptor['sha256'], 'pointer': '/finding'}
    reply_ref = {'repository': 'private', 'path': str(FOLDER.relative_to(PRIVATE) / raw_path),
                 'sha256': sha(answer), 'pointer': '/'}
    for unit in target['units']:
        unit.update(fulfillment='partial', aligned=None, assertion='incorrect',
            asserted_scope='本ID已完整形式化且通过内核核验：原答alignment逐项complete及整模块核验承诺',
            reason='本ID被原答逐项标为complete并纳入已通过内核核验的交付承诺，但唯一目标模块原样编译失败。沿用Flash同题判准，否定实作/核验承诺，不据此声称原数学命题为假；不增加断言单元。',
            evidence=[source_ref, reply_ref])
    goal_task = next(task for task in goals['tasks'] if task['case_id'] == 'HCH02')
    for goal in goal_task['goals']:
        goal.update(passed=False, reason='已恢复原答，但其必需目标模块未通过原样内核编译；不可借用不同的封卷文件完成本轮交付验收。', evidence=[source_ref, reply_ref])
    content['source_bindings']['assessment_result_sha256'] = public_reports['partial']['sha256']
    for reference in (source_ref, reply_ref):
        content['sources'].append({key: reference[key] for key in ('repository', 'path', 'sha256')})
        goals['sources'].append({key: reference[key] for key in ('repository', 'path', 'sha256')})
    content_sha = sha(encoded(content))
    goals['source_bindings'].update(assessment_result_sha256=public_reports['partial']['sha256'],
                                    content_review_sha256=content_sha)
    patch = {
        'schema': 'math-gauge.content-review-source-correction/v1', 'case_id': 'HCH02',
        'base_content_review': desc('content-rate-review.json', (FOLDER / 'content-rate-review.json').read_bytes()),
        'base_goal_review': desc('goal-attainment-review.json', (FOLDER / 'goal-attainment-review.json').read_bytes()),
        'content_task': target, 'goal_task': goal_task,
        'content_source_bindings': content['source_bindings'], 'goal_source_bindings': goals['source_bindings'],
        'appended_sources': [{key: ref[key] for key in ('repository', 'path', 'sha256')} for ref in (source_ref, reply_ref)],
        'reconstructed_content_sha256': content_sha, 'reconstructed_goal_sha256': sha(encoded(goals)),
        'scoring_rules_changed': False, 'goal_definition_sha256': goals['goal_definition_sha256'],
    }
    rate_patch = put('private', 'rate-review-patch.json', patch)
    assessment = json.loads((ROOT / 'protocol/scoring-policy.json').read_bytes())
    rates = score_content_rates(content, assessment, goals)
    rates.update(private_review_sha256=content_sha, private_goal_review_sha256=sha(encoded(goals)))
    rates_private = put('private', 'content-rates-report.json', rates)
    rates_public = put('public', 'content-rates.json', project_rates(rates))

    adoption = {'explicit': True, 'post_observation': True, 'observed_on': '2026-11-13',
                'reason': '排除harness bug，恢复原答并沿用既有判分规则；不是新评分标准或新模型作答。'}
    common = {
        'schema': 'math-gauge.harness-result-correction/v1', 'version': '0.1.0',
        'benchmark_version': '1.0.0', 'source_benchmark_version': '0.6.0',
        'model_id': 'gemini-4-argon', 'record_id': '20261111',
        'reviewer_kind': 'ai', 'human_review': 'pending', 'formal_comparison_eligible': False,
        'new_candidate_calls': 0, 'scoring_rules_changed': False, 'native_status_rewritten': False,
        'affected_conditions': ['nonlogical_retry_3'], 'affected_cases': ['HCH02'],
        'source_response_sha256': sha(answer), 'user_adoption': adoption,
        'original_native_status': 'ERROR',
    }
    private_manifest = {**common, 'visibility': 'private',
        'base_record': desc('record.json', (FOLDER / 'record.json').read_bytes()),
        'native_proof': proof_descriptor, 'math_review': math_descriptor,
        'claim_condition': claims_descriptor, 'scores': private_reports,
        'rate_patch': rate_patch, 'rates': rates_private}
    private_manifest_descriptor = put('private', 'private.json', private_manifest)
    public_manifest = {**common, 'visibility': 'public-projection',
        'base_record': desc('record.json', (PUBLIC / 'record.json').read_bytes()),
        'private_correction_sha256': private_manifest_descriptor['sha256'],
        'math_review': public_math, 'claim_review': public_claim_descriptor,
        'answer': public_answer, 'scores': public_reports, 'public_tasks': tasks_descriptor,
        'rates': rates_public, 'native_proof_sha256': proof_descriptor['sha256']}
    public_manifest_descriptor = put('public', 'public.json', public_manifest)
    impact = json.loads((HERE / 'HCH02-score-impact.json').read_bytes())
    rows = '\n'.join('| ' + mode + ' | %.2f | %.2f | %+.2f |' %
        (item['baseline_earned']['confirmed'], item['proposed_earned']['confirmed'], item['delta_confirmed'])
        for mode, item in impact['modes'].items())
    report = ('# HCH02 · harness故障更正\n\n'
        'Benchmark1.0.0及聚合0.9.0／MC0.3.0／SMC0.2.0不变。用户于2026-11-13明确接纳原生后端找回的原答；原CLI ERROR、旧记录和六视图保留。没有补跑，没有把ERROR改写为SUCCESS。\n\n'
        '恢复的是末次物理请求5的唯一可见回复，原截止前54分34.13秒生成。原答全文和源码代码块按原字节审核，不拼接其他尝试，不借用不同的封卷工程。\n\n'
        '原答Main.lean第1120行缩进改变Lean解析，原样编译失败。题面要求命名代码块全文交付，因此原封卷40/40不能转给这份回复。40项未取得模块验收信用，不等于40个原数学命题均为假。\n\n'
        '题内MC为0；编译失败本身不另扣罚。原答明确保证全工程已通过内核检查，沿用Gemini3.8Flash同题的critical false_verification判准，单一根因扣20%，RMC为−20/100，SMC为0。不是对40项各扣20。该题总榜权重2.5分，故MC减少2.50、RMC减少0.50。\n\n'
        '| 总榜指标 | 更正前 | 更正后 | 差值 |\n|---|---:|---:|---:|\n' + rows + '\n\n'
        '仅规则允许重试视图采用这份恢复原答；首次尝试不变。当前为38份主动／恢复交付、1项强收有内容；C003仍未正常交卷，固定三轮未执行。用量、成本和运行时钟来自同一物理请求，没有新增模型消耗。\n\n'
        '内容可靠率按同题既有标准审核逐项complete与核验承诺；目标达成率保留原固定目标和权重。原数学命题是否为真与核验承诺是否成立分开。\n')
    put('private', 'README.md', report.encode())
    put('public', 'README.md', report.encode())
    return public_manifest_descriptor, private_manifest_descriptor


def apply_packages(public_descriptor, private_descriptor):
    # Public selection changes last, after all original-byte witnesses exist.
    for side, destination in (('private', FOLDER), ('public', PUBLIC)):
        for source in sorted((HERE / side).rglob('*')):
            if source.is_file():
                target = destination / source.relative_to(HERE / side)
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(source, target)
    private_manifest = read_json(FOLDER / private_descriptor['path'])
    verify_native_recovery(FOLDER, read_json(FOLDER / private_manifest['native_proof']['path']))
    from math_gauge.content_rates import validate_review, verify_sources
    from math_gauge.goal_attainment import validate_goal_review
    content, goals = reconstruct_rate_reviews(FOLDER, read_json(FOLDER / private_manifest['rate_patch']['path']))
    assessment = read_json(ROOT / 'protocol/scoring-policy.json')
    current_score = read_json(FOLDER / private_manifest['scores']['partial']['path'])
    validate_review(content, assessment, current_score)
    validate_goal_review(goals, content, assessment, current_score)
    verify_sources(content, {'public': ROOT, 'private': PRIVATE})
    verify_sources(goals, {'public': ROOT, 'private': PRIVATE})
    recomputed = score_content_rates(content, assessment, goals)
    recomputed.update(private_review_sha256=sha(encoded(content)), private_goal_review_sha256=sha(encoded(goals)))
    require(recomputed == read_json(FOLDER / private_manifest['rates']['path']),
            'Corrected content rates differ from their source reviews')
    public_manifest = read_json(PUBLIC / public_descriptor['path'])
    require(project_rates(recomputed) == read_json(PUBLIC / public_manifest['rates']['path']),
            'Corrected rate projection differs from its private review')
    for mode in ('capability', 'partial', 'strict'):
        score = read_json(FOLDER / private_manifest['scores'][mode]['path'])
        projection = project_assessment_score(score)
        projection['source_bindings']['private_report_sha256'] = private_manifest['scores'][mode]['sha256']
        require(projection == read_json(PUBLIC / public_manifest['scores'][mode]['path']),
                'Corrected public score differs from the shared scorer report')
    for root, folder, item in ((PRIVATE, FOLDER, private_descriptor), (ROOT, PUBLIC, public_descriptor)):
        edition = read_json(root / 'benchmark.json')
        selection = {**item, 'path': str(folder.relative_to(root) / item['path'])}
        edition.setdefault('result_corrections', {})['gemini-4-argon'] = selection
        (root / 'benchmark.json').write_bytes(encoded(edition))
    load_selected(ROOT, 'gemini-4-argon', PUBLIC)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--private-root', type=Path, required=True)
    parser.add_argument('--stage', type=Path, required=True)
    parser.add_argument('--apply', action='store_true')
    args = parser.parse_args()
    PRIVATE = args.private_root.resolve()
    FOLDER = PRIVATE / PUBLIC.relative_to(ROOT)
    HERE = args.stage.resolve()
    HERE.mkdir(parents=True, exist_ok=True)
    main()
    public_descriptor, private_descriptor = prepare_packages()
    if args.apply:
        apply_packages(public_descriptor, private_descriptor)
    print(json.dumps({'prepared': True, 'adopted': args.apply, 'benchmark_version': '1.0.0',
                      'scoring_rules_changed': False, 'new_candidate_calls': 0}))



