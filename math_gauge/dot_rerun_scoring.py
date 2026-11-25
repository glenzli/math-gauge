"""Private scoring adapter. Acquisition and arithmetic are independently checked."""
import argparse
import hashlib
import json
from pathlib import Path

from . import dot_rerun_sources as run
from .dot_rerun_admission import LABEL, load_public
from .dot_rerun_independent import verify_review
from .dot_rerun_neutral import verify_replays
from .native_observations import _validate_math_inputs, project_score, require
from .neutral_revision import CONDITION, MODES, verify_pair
from .scoring import _score_observation_inputs, validate_assessment_policy
from .submission_evidence import validate_condition
from .theorem_extension_calibration import document, read

CONDITIONS = ('single_attempt', CONDITION)
POLICIES = {
    'assessment':'scoring-policy.json', 'strict':'strict-scoring-policy.json',
    'capability':'capability-scoring-policy.json', 'claim':'claim-penalty-policy.json',
    'submission':'submission-scoring-policy.json',
}
SUBMISSION = {
    'native_inline':'active_final', 'candidate_designated_file':'active_final',
    'observed_inline_bound_authored_file':'active_final',
    'observed_inline_bound_capture_projection':'active_final',
    'forced_content':'forced_content', 'nondelivery':'blank', 'unresolved_capture_loss':'not_run',
}


def compute_base(root, private_root, dataset, inputs):
    """Replay common math/submission arithmetic using the verified chosen physical data."""
    require(set(inputs) == {'schema','source','conditions','private_scores'}
            and inputs['schema'] == 'math-gauge.dot-native-rerun-score-inputs/v1'
            and set(inputs['conditions']) == set(CONDITIONS), 'Unknown Dot math input contract')
    contract = run.validate(private_root, dataset, document(private_root, inputs['source']),
                            include_evaluator_bindings=True)
    policy = {key:json.loads((Path(root)/'protocol'/name).read_bytes()) for key,name in POLICIES.items()}
    available, scores = validate_assessment_policy(policy['assessment']), {}
    for condition in CONDITIONS:
        bundle = inputs['conditions'][condition]
        require(set(bundle) == {'mathematical_review','submission_review'}, 'Unknown Dot score input fields')
        mathematical, submission = (document(private_root,bundle[k])
                                    for k in ('mathematical_review','submission_review'))
        chosen = contract['selected' if condition == CONDITION else 'first']
        source_hash = inputs['source']['sha256']
        _validate_math_inputs(mathematical, available, fresh_dot=True)
        require(mathematical['model_label'] == LABEL
                and mathematical['source_supplements_sha256'] == source_hash
                and submission['attempt_condition'] == condition
                and {t['slot_id'] for t in mathematical['tasks']} == set(chosen)-set(run.C003_ROUNDS),
                'Captured Math Gauge request population differs from native scoring input')
        initial = validate_condition(submission, model_label=LABEL,
            response_hashes={t['case_id']:(t.get('response') or {}).get('sha256') for t in mathematical['tasks']})
        require(set(initial) == {t['case_id'] for t in mathematical['tasks']},
                'Submission evidence must match every native task')
        for t in mathematical['tasks']:
            slot = chosen[t['slot_id']]
            row = initial[t['case_id']]
            bound = slot.get('response')
            require(t['response'] == bound and row['classification'] == SUBMISSION[slot['selection']],
                    'Changed selected response bytes or native/forced/nondelivery basis')
            primary = document(private_root,t['review'])
            require(primary.get('response_sha256') == (None if bound is None else bound['sha256'])
                    and primary.get('human_review') == 'pending'
                    and primary.get('case_id') == t['case_id']
                    and (slot['review'] is None or primary.get('source') == slot['review'])
                    and (bound is None or primary.get('source') is not None)
                    and primary.get('judgment') == {k:t[k] for k in t if k not in {'response','review'}},
                    'Normalized mathematics differs from its source-bound judgment')
            if primary.get('source') is not None:
                read(private_root,primary['source'])
            if row.get('work_review') is not None:
                require(document(private_root,row['work_review']) == row['work'],
                        'Inline forced-credit data differs from its original independently reviewed units')
            for ref in row['evidence']:
                if isinstance(ref,dict) and 'path' in ref:
                    read(private_root,ref)
        trajectory = mathematical['alignment_review']
        initial_c003 = chosen['MG-C003:A1']['response']
        require(trajectory['baseline']['source_sha256'] == initial_c003['sha256'],
                'Alignment evidence starts from another C003 baseline')
        raw_rounds = {r['round']:r for r in trajectory['rounds']}
        for row in submission['rounds']:
            i = row['round']
            slot = chosen[f'MG-C003:R{i}']
            require(row['classification'] == SUBMISSION[slot['selection']]
                    and row['mathematical_source_sha256'] == slot['response']['sha256']
                    and raw_rounds[i]['snapshot']['source_sha256'] == slot['response']['sha256'],
                    'C003 round changed its authorized source or delivery class')
            if condition == CONDITION:
                require(slot['review']['sha256'] in raw_rounds[i]['diagnosis']['review_evidence_sha256'],
                        'C003 diagnosis lost its independent original review')
        scores[condition] = {}
        for mode in MODES:
            report = _score_observation_inputs(mathematical, policy['assessment'], policy['strict'],
                policy['capability'],policy['claim'],mode=mode,record_kind='native_harness',
                submission_review=submission,submission_policy=policy['submission'])
            # The arithmetic helper is historical; acquisition and display edition
            # are projected separately for this new run only.
            report.update(benchmark_version='1.1.0',source_benchmark_version='1.0.0',
                attempt_condition=condition, source_bindings=dict(
                    dot_private_source_sha256=source_hash,
                    mathematical_input_sha256=bundle['mathematical_review']['sha256'],
                    submission_evidence_sha256=bundle['submission_review']['sha256']))
            scores[condition][mode] = report
    return scores, policy['assessment']


def verify_120(root, private_root, dataset, inputs, revised_private, *, public=None):
    """Verify public base and previously retained neutral addition against private replay."""
    public = load_public(root) if public is None else public
    require(public is not None, 'Dot additive public selection is not configured')
    base, assessment = compute_base(root, private_root, dataset, inputs)
    require(set(inputs['private_scores']) == set(CONDITIONS), 'Both condition reports must be byte-bound')
    for condition, reports in base.items():
        require(set(inputs['private_scores'][condition]) == set(MODES), 'All three modes must be retained')
        for mode, report in reports.items():
            saved = inputs['private_scores'][condition][mode]
            require(document(private_root,saved) == report, 'Private base report differs from common arithmetic')
            projection = project_score(report)
            projection['source_bindings']['private_report_sha256'] = saved['sha256']
            require(public['base'][mode][condition] == projection,
                    'Public base projection differs from the validated private report')
    pair = verify_pair(root,private_root,public['revised']['_selection'],revised_private,
                        base_reports=base[CONDITION],assessment_policy=assessment)
    data = pair['inputs'].for_score(base[CONDITION]['partial'],mode='partial')
    data['policy'] = pair['public']['policy']
    source = run.validate(private_root,dataset,document(private_root,inputs['source']),
                          include_evaluator_bindings=True)
    verify_replays(root,private_root,{'slots':source['effective_slots']},data)
    return {'status':'passed','benchmark_version':'1.2.0','source_benchmark_version':'1.0.0',
            'models':[run.MODEL],'new_candidate_calls':0}


def verify(root, private_root, dataset, base_inputs, revised_private, research_private, *, historical=False):
    public = load_public(root, historical=historical)
    require(public is not None, 'Dot additive public selection is not configured')
    inputs = document(private_root,base_inputs)
    verify_120(root,private_root,dataset,inputs,revised_private,public=public)
    require(verify_review(root,private_root,research_private) == public['research']['research'],
            'Public 1.3 item differs from original privately validated judgments')
    receipt = dict(schema='math-gauge.dot-paired-selection-validation/v1', model_id=run.MODEL,
        base_inputs_sha256=base_inputs['sha256'], neutral_private_sha256=revised_private['sha256'],
        research_private_sha256=research_private['sha256'], source_sha256=inputs['source']['sha256'],
        selected_neutral_public_sha256=public['revised']['_selection']['sha256'],
        selected_research_public_sha256=public['research_ref']['sha256'])
    encoded = json.dumps(receipt,sort_keys=True,separators=(',',':')).encode()
    require(hashlib.sha256(encoded).hexdigest() == public['paired_validation_sha256'],
            'Publication selection did not bind this exact paired verification')
    return dict(status='passed',editions=['1.2.0','1.3.0'],model_id=run.MODEL,new_candidate_calls=0)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--public-root',type=Path,required=True)
    parser.add_argument('--private-root',type=Path,required=True)
    parser.add_argument('--dataset',type=Path,required=True)
    parser.add_argument('inputs',type=Path)
    parser.add_argument('private_neutral_manifest_descriptor',type=Path)
    parser.add_argument('private_research_registration_descriptor',type=Path)
    args = parser.parse_args()
    print(json.dumps(verify(args.public_root,args.private_root,args.dataset,
        json.loads(args.inputs.read_bytes()),
        json.loads(args.private_neutral_manifest_descriptor.read_bytes()),
        json.loads(args.private_research_registration_descriptor.read_bytes()))))


if __name__ == '__main__':
    main()
