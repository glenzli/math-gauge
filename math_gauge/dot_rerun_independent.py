"""Project the original byte-quoted independent-research judgment privately."""
from fractions import Fraction
from pathlib import Path

from .independent_research_external import POLICY_PATHS, policy_bindings
from .independent_research_native import validate_public_model
from .independent_research_strict_credit import _bounds, _counts, _net_credit, _number
from .independent_research_value import DIMENSIONS, EXTENSION
from .theorem_extension_calibration import document, read, require

ROUNDS = ('R1','R2','R3')


def verify_review(root, private_root, ref):
    """Retain every actual review input and derive anonymously publishable components."""
    registration = document(private_root,ref)
    require(set(registration) == {'schema','case','context_id','source_root','review','review_manifest',
                                  'evidence_registry','extension_review','round_observations'}
            and registration['schema'] == 'math-gauge.dot-native-independent-trajectory/v1'
            and registration['case'] == 'MG-MT001'
            and isinstance(registration['context_id'],str) and registration['context_id'].strip(),
            'Research trajectory needs its actual, single native conversation')
    relative = registration['source_root']
    require(isinstance(relative,str) and all(part not in ('','.','..') for part in relative.split('/'))
            and '\\' not in relative, 'Unsafe private research source directory')
    source = Path(private_root)/relative
    manifest = document(source, registration['review_manifest'])
    research = document(source, registration['review'])
    registry = document(source,registration['evidence_registry'])
    def artifact(path):
        return read(source,dict(manifest[path],path=path))
    for path in manifest:
        artifact(path)
    paths = {f'{round}/answer.md':f'review-input/{round}/answer.md' for round in ROUNDS}
    bodies = {key:artifact(path) for key,path in paths.items()}
    seals = {round:manifest[paths[f'{round}/answer.md']]['sha256'] for round in ROUNDS}
    require(research['schema'] == 'math-gauge.source-bound-independent-review/v1'
            and research['case_id'] == registration['case']
            and research['status'] == 'ai-review-proposal-human-pending-not-admitted-not-published'
            and research['source_hashes'] == seals
            and research['capacity_aggregation'] == 'whole-three-round-trajectory-with-claim-status-tracking-not-unconditional-union'
            and research['item_weight'] == dict(taste=2,capacity=1,autonomy_included=False),
            'Independent research review did not grade this exact three-round trajectory')
    actual_policies = policy_bindings(root)
    for key in POLICY_PATHS:
        name = Path(POLICY_PATHS[key]).name
        require(manifest['review-policy-addendum/'+name]['sha256'] == actual_policies[key],
                'Research review policy differs from current published scoring policy')
    require(set(registration['round_observations']) == set(ROUNDS), 'One native delivery observation per round is required')
    previous = None
    for round in ROUNDS:
        row = document(source, registration['round_observations'][round])
        terminal = f'review-input/{round}/native-final.txt'
        task = f'review-input/candidate/{round}.md'
        require(row == dict(round=round,context_id=registration['context_id'],
                       native_final_sha256=manifest[terminal]['sha256'],
                       fixed_prompt_sha256=manifest[task]['sha256'],
                       answer_sha256=seals[round],previous_answer_sha256=previous,
                       declared_file=f'{round}/answer.md',source=row.get('source'))
                and f'`{round}/answer.md`' in artifact(terminal).decode('utf-8')
                and read(source,row['source']),
                'Research rounds must retain exact designated files from one uninterrupted context')
        previous = seals[round]
    require(registry['offset_convention'] == 'zero-based half-open UTF-8 byte ranges',
            'Research review quotes need exact byte offsets')
    refs = {}
    for ref_row in registry['evidence']:
        b = bodies[ref_row['source']]
        start,end = ref_row['utf8_bytes']
        require(ref_row['id'] not in refs and type(start) is int and type(end) is int and 0 <= start < end <= len(b)
                and ref_row['sha256'] == manifest[paths[ref_row['source']]]['sha256']
                and b[start:end] == ref_row['quote'].encode('utf-8'), 'Research judgment quote lost original bytes')
        refs[ref_row['id']] = ref_row
    def evidence(ids):
        require(isinstance(ids,list) and ids and all(i in refs for i in ids),
                'Reviewed judgment lacks exact evidence references')
    contract = document(source,dict(manifest['review-input/review-contract.json'],
                                    path='review-input/review-contract.json'))
    limits = {'taste':dict(zip(DIMENSIONS,(60,20,20))), 'capacity':{
        row['id']:20 for row in contract['gates']['capacity'] if row['required']}}
    axes, criteria, strict = {}, {}, {}
    # This exact review declares no accountable mathematical error roots.
    # Future runs with roots need their source-bound deduplication/allocation layer.
    require(research['error_roots'] == [] and research['total_error_deduction'] == 0,
            'Unsupported policy path for newly asserted research deductions')
    for axis,budget in limits.items():
        judged = research[axis]
        directions = judged['checkpoints']
        require(len(directions) == len(budget) and {d['id'] for d in directions} == set(budget),
                'Independent research checkpoint population differs from the contract')
        points, verdicts = {}, {}
        for row in directions:
            cid = row['id']
            evidence(row['evidence'])
            require(isinstance(row['reason'],str) and row['reason'].strip()
                    and row['max_credit'] == budget[cid] and _number(row['earned_mc'],budget[cid])
                    and row['error_deduction'] == 0 and row['earned_mc'] == row['earned_rmc']
                    and type(row['strict_pass']) is bool
                    and row['earned_smc'] == (row['earned_rmc'] if row['strict_pass'] else 0),
                    'Retain each original reviewed credit and strict verdict')
            points[cid],verdicts[cid] = row['earned_mc'],row['strict_pass']
        grade = dict(mc=judged['scores']['MC'],rmc=judged['scores']['RMC'])
        interval = _net_credit(points,{}, {},verdicts,grade,None)
        require(Fraction(str(judged['scores']['SMC'])) == interval[2]*100
                and judged['strict_pass'] is all(verdicts.values()),
                'Published research arithmetic differs from original review')
        axes[axis],criteria[axis],strict[axis] = dict(grade,strict=judged['strict_pass']),_counts(verdicts),_bounds(interval)
    extension = document(source,registration['extension_review'])
    detail = extension['extension']
    assignments = {name:manifest[f'review-input/candidate/{name}']['sha256']
                   for name in ('R1.md','R2.md','R3.md','rules.md')}
    require(extension['schema'] == 'math-gauge.dot-independent-extension-addendum/v1'
            and extension['item_id'] == registration['case']
            and extension['run_label'] == 'Dot (261125)'
            and extension['reviewer_kind'] == 'ai' and extension['human_review'] == 'pending'
            and extension['delivery_sha256'] == seals
            and extension['source_registry_sha256'] == registration['evidence_registry']['sha256']
            and extension['policy_sha256'] == actual_policies['value']
            and extension['candidate_assignment_sha256'] == assignments
            and extension['extension_scope'] == 'profile-initiative-only'
            and detail['level'] in EXTENSION
            and EXTENSION[detail['level']] == extension['historical_value_policy_fraction']
            and detail['assessed_rounds'] == list(ROUNDS)
            and all(isinstance(detail[k],str) and detail[k].strip() for k in
                    ('independent_question','outside_core','result_and_scope','value','reason')),
            'Separate policy-scoped E0–E3 judgment required; cannot infer extension from T/C')
    evidence(extension['source_registry_span_ids'])
    require(isinstance(detail['evidence'],list) and detail['evidence'],'Need exact extension evidence')
    for span in detail['evidence']:
        body = bodies[span['file']]
        require(span['file'] == span['round']+'/answer.md'
                and type(span['start']) is int and type(span['end']) is int
                and 0 <= span['start'] < span['end'] <= len(body)
                and body[span['start']:span['end']] == span['quote'].encode(),
                'Extension evidence lost exact retained source bytes')
    for opportunity in research['autonomy']['opportunities']:
        evidence(opportunity['evidence'])
    return validate_public_model(dict(status='reviewed',axes=axes,criteria=criteria,strict_credit=strict,
        extension_level=detail['level'],autonomy_score=research['autonomy']['RMC'],
        normal_rounds=3,round_dispatches=3,source_sha256=ref['sha256']))
