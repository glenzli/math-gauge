"""Post-observation first assessment of original normal native executions.

Acquisition freezes are retained unchanged. This provenance is neither portable
controller evidence nor a claim that a later standard existed before dispatch.
It validates source projections only; all score arithmetic stays elsewhere.
"""
import json
import re
from pathlib import PurePosixPath

SCHEMA = 'math-gauge.native-first-assessment-source/v1'
PUBLIC_SCHEMA = 'math-gauge.native-first-assessment-source-public/v1'
NEUTRAL_BRIDGE_SCHEMA = 'math-gauge.native-initial-neutral-parent-source-bridge/v1'


def require(value, message):
    if not value:
        raise ValueError(message)


def pointer(document, path):
    require(isinstance(path, str) and path.startswith('/'), 'Source binding needs an explicit JSON pointer')
    value = document
    for part in path.split('/')[1:]:
        part = part.replace('~1','/').replace('~0','~')
        value = value[int(part)] if isinstance(value, list) else value[part]
    return value


def validate(root, record, current):
    from .records import evidence_bytes
    return validate_sources(record, current, lambda item: evidence_bytes(root, item), root=root)


def validate_sources(record, current, read, *, root=None):
    from .benchmarks import validate_assessment_policy
    from .agy_evidence import validate_delivery
    from .agy_native_sources import SCHEMA as NATIVE, same

    def document(item):
        return json.loads(read(item))

    require(record.get('benchmark_version') == '1.0.0'
            and record.get('initial_assessment_edition') == '1.1.0'
            and record.get('score_history') is None and record.get('source_assessment_admission') is None
            and record.get('retention', {}).get('user_requested') is True,
            'Native first assessment must keep its actual edition and absence of formal score history')
    validate_assessment_policy(current)
    proof = document(record['first_assessment_source'])
    require(proof.get('schema') in {SCHEMA, PUBLIC_SCHEMA} and proof.get('version') == '0.1.0'
            and proof.get('model_id') == record.get('model_id')
            and proof.get('source_benchmark_version') == '1.0.0'
            and proof.get('initial_assessment_edition') == '1.1.0'
            and proof.get('assessment_method_version') == current.get('version') == '0.9.0'
            and proof.get('post_observation') is True and proof.get('new_candidate_calls') == 0
            and document(proof['first_assessment_policy']) == current,
            'Native first assessment lost its exact first policy or source edition')
    # Bind the current TX policy as a separate first-review source. It is not
    # inserted into any acquisition freeze or presented as an old score report.
    calibration = document(proof['calibration_policy'])
    require(calibration.get('schema') == 'math-gauge.theorem-extension-calibration-policy/v1'
            and calibration.get('source_benchmark_version') == '1.0.0'
            and calibration.get('target_benchmark_version') == '1.1.0',
            'Native first assessment needs the current TX policy')
    if proof['schema'] == PUBLIC_SCHEMA:
        require(record.get('scope') == 'public-answers-and-combined-aggregates'
                and record.get('formalization_evidence_location') is None
                and set(proof) == {'schema','version','model_id','source_benchmark_version',
                    'initial_assessment_edition','assessment_method_version','post_observation',
                    'new_candidate_calls','private_source_proof_sha256','first_assessment_policy',
                    'calibration_policy'}
                and isinstance(proof.get('private_source_proof_sha256'), str)
                and re.fullmatch(r'[0-9a-f]{64}', proof['private_source_proof_sha256'])
                and proof['private_source_proof_sha256'] == record.get('first_assessment_source_private_sha256'),
                'Public native provenance must be the opaque projection of its complete private proof')
        return current
    require(proof.get('kind') == 'native_post_observation_initial'
            and proof.get('source_raw_bytes_rewritten') is False
            and proof.get('acquisition_freezes_modified') is False
            and proof.get('prior_adopted_score_views_existed') is False
            and proof.get('prior_adopted_B') is None and 'prior_adopted_B' in proof
            and proof.get('prior_adopted_R') is None and 'prior_adopted_R' in proof
            and proof.get('prior_adopted_score_views') is None and 'prior_adopted_score_views' in proof
            and proof.get('portable_execution_claimed') is False,
            'Native first assessment cannot invent a pre-call freeze, portable run or adopted history')
    adoption = document(proof['user_adoption'])
    require(adoption.get('post_observation') is True and bool(adoption.get('user_quote'))
            and adoption.get('model_id') == record['model_id']
            and adoption.get('source_benchmark_version') == '1.0.0'
            and adoption.get('original_physical_effective_ordinals_preserved') is True
            and adoption.get('original_native_statuses_preserved') is True,
            'Native first assessment lacks its separate source-bound user adoption')
    rows = proof.get('normal_sources', [])
    require(isinstance(rows, list) and len(rows) == 42
            and len({r['id'] for r in rows}) == 42,
            'Complete native admission needs its selected39 A1 and three prescribed rounds')
    retained = {r['id']: r for r in record['records']}
    require(len(retained) == len(record['records']) == 42 and set(retained) == {r['id'] for r in rows},
            'First native provenance differs from the complete retained record population')
    initials, rounds, responses, by_id = set(), set(), set(), {}
    for row in rows:
        native = document(row['agy_native_evidence'])
        phase, cid = native.get('phase'), native.get('case_id')
        require(isinstance(cid, str) and phase in {'A1','R1','R2','R3'}
                and native.get('schema') == NATIVE and row['id'] == cid + ':' + phase
                and row.get('case_id') == cid and same(row.get('response'), native['response']),
                'Initial provenance selected another native case/phase/final')
        selected = retained[row['id']]
        require(selected.get('agy_native_evidence') == row['agy_native_evidence']
                and same(selected.get('response'), row['response'])
                and selected.get('source', {}).get('original_mathematical_review') == row['mathematical_review'],
                'First native provenance changed the adopted source or original AI review')
        actual = dict(case_id=cid, id=row['id'], response=row['response'],
                      agy_native_evidence=row['agy_native_evidence'])
        validate_delivery(root, actual, lambda _root, item: read(item))
        # Mathematical review contents are checked by their existing owners;
        # this file retains the actual source bytes rather than assigning credit.
        read(row['mathematical_review'])
        if phase == 'A1':
            require(cid not in initials, 'Repeated normal native initial')
            initials.add(cid)
        else:
            require(cid == 'MG-C003' and phase in {'R1','R2','R3'}, 'Unexpected prescribed round')
            rounds.add(phase)
        identity = (native['original_attempt'], native['physical_request'])
        require(identity not in responses, 'Native admission borrowed a physical delivery twice')
        responses.add(identity); by_id[row['id']] = row
    require(len(initials) == 39 and rounds == {'R1','R2','R3'}, 'Native first assessment lost fixed deliveries')
    tx = proof.get('first_tx_reviews', [])
    expected = {'MG-TX001','MG-TX002','MG-TXP001','MG-TXP002','MG-TXP003','MG-TXP004'}
    require(len(tx) == 6 and {r['case_id'] for r in tx} == expected,
            'Native first assessment requires the six actual first1.1 TX judgments')
    adopted_tx = document(record['theorem_extension_inputs'])
    adopted_tx = {r['case_id']:r for r in adopted_tx['slots']}
    require(set(adopted_tx) == expected, 'Initial TX provenance changed its six source families')
    for row in tx:
        actual = by_id[row['case_id'] + ':A1']
        original = document(actual['mathematical_review'])
        projection = document(row['review_projection'])
        adopted = adopted_tx[row['case_id']]
        fields = row['source_fields']
        require(original.get('first_formal_assessment') is True
                and all(k in original and original[k] is None for k in
                        ('old_adopted_B','old_adopted_R','old_score_views'))
                and projection.get('stage') == 'A1'
                and projection.get('B') == pointer(original, fields['baseline_B'])
                and projection.get('R') == pointer(original, fields['research_R'])
                and projection.get('answer_sha256') == pointer(original, fields['response_sha256'])
                    == actual['response']['sha256']
                and type(projection.get('B')) is int and projection['B'] in range(3)
                and type(projection.get('R')) is int and projection['R'] in range(4)
                and adopted.get('review') == row['review_projection']
                and same(adopted.get('response'), actual['response'])
                and adopted.get('baseline_B') == projection['B']
                and adopted.get('research_R') == projection['R']
                and pointer(original, fields['policy_sha256']) == proof['calibration_policy']['sha256']
                and projection.get('original_review') == actual['mathematical_review']
                and projection.get('metadata_projection_only') is True
                and projection.get('new_candidate_calls') == 0,
                'Initial TX metadata changed its original first mathematical judgment')
        standard = row['effective_standard']
        read(standard)
        standard_kind = 'standards' if row['case_id'] in {'MG-TX001','MG-TX002'} else 'private_standards'
        require(pointer(original, fields['standard_sha256']) == standard['sha256']
                == calibration[standard_kind]['sha256'],
                'First TX review lacks its actually bound effective standard')
    return current


def record_relative_reference(record_ref, item):
    """Resolve a source-record descriptor from its own archive, without fallback."""
    from .theorem_extension_calibration import _descriptor
    record_ref, item = _descriptor(record_ref), _descriptor(item)
    return dict(item, path=(PurePosixPath(record_ref['path']).parent / item['path']).as_posix())


def validate_neutral_parent_bridge(bridge, *, read, record_ref, record, first, adoption_row):
    """Bind a frozen unadopted parent to its later metadata-only formal baseline.

    This does not recompute weights or certify the new response/runtime. The
    neutral consumer already validates all baseline reports and their sources.
    """
    from .revision_harness import BUNDLE_SCHEMA, _identity
    from .agy_native_sources import SCHEMA as NATIVE, same
    from .manuscript_completion import criterion_total_matches
    # Frozen package descriptors use the adoption reader's root. Retained
    # answers, reviews and component inputs keep the source-record directory.
    def read_record(item):
        return read(record_relative_reference(record_ref, item))
    require(bridge.get('schema') == NEUTRAL_BRIDGE_SCHEMA and bridge.get('version') == '0.1.0'
            and bridge.get('created_after_freeze') is True and bridge.get('freeze_rewritten') is False
            and bridge.get('claims_formal_record_existed_at_freeze') is False
            and bridge.get('mathematical_values_changed') is False
            and bridge.get('source_record') == record_ref,
            'Neutral parent bridge cannot invent a pre-call formal record or changed mathematics')
    bundle = json.loads(read(bridge['frozen_bundle']))
    frozen = json.loads(read(bridge['frozen_selection']))
    preparation = json.loads(read(bridge['preparation_freeze']))
    require(bundle.get('schema') == BUNDLE_SCHEMA
            and bundle.get('bundle_sha256') == _identity({k:v for k,v in bundle.items() if k!='bundle_sha256'})
            and bundle.get('model_id') == frozen.get('model_id') == record.get('model_id'),
            'Neutral parent bridge changed the actual frozen bundle/selection/model')
    require(preparation.get('model_id') == record.get('model_id')
            and preparation.get('source_record') is None
            and any(same(item,bridge['frozen_bundle']) for item in preparation.get('files',[]))
            and any(same(item,bridge['frozen_selection']) for item in preparation.get('files',[])),
            'Neutral parent bridge substituted unfrozen packaging or selection metadata')
    tasks = [r for r in bundle['tasks'] if r['status']=='ready']
    chosen = frozen['selection']; links = bridge.get('rows', [])
    require(len(links) == len(tasks) == len(chosen)
            and preparation.get('selected_count') == len(tasks)
            and len({r['task_id'] for r in links}) == len(links)
            and [(r['task_id'],r['case_id']) for r in links] == [(r['task_id'],r['case_id']) for r in tasks]
            and [r['case_id'] for r in chosen] == [r['case_id'] for r in tasks],
            'Neutral parent bridge changed the complete original alias/case inventory')
    cid = adoption_row['case_id']
    pair = [(t,s,l) for t,s,l in zip(tasks,chosen,links) if t['case_id']==cid]
    require(len(pair)==1, 'Neutral parent has no unique original alias')
    task, selected, link = pair[0]
    source = task['source_selection']
    retained = next((r for r in record['records'] if r['id']==cid+':A1'), None)
    require(retained is not None and retained.get('kind')=='independent' and retained.get('parent_id') is None
            and link.get('raw_first_review') == retained.get('source',{}).get('original_mathematical_review')
            and link.get('formal_baseline_source_review') == retained.get('review')
            and same(retained.get('response'), adoption_row.get('original_answer'))
            and source.get('response_sha256') == selected.get('response_sha256')
                == retained['response']['sha256'] == first['response_sha256']
            and source.get('review_sha256') == selected.get('review_sha256')
                == link['raw_first_review']['sha256']
            and first['review_sha256'] == retained['review']['sha256']
            and all(selected.get(k)==first.get(k)==source.get(k) for k in ('family_id','subcategory'))
            and selected.get('first_scores') == first.get('first_scores')
            and selected.get('loss_modes') == first.get('loss_modes'),
            'Neutral parent changed frozen own-A1 answer/raw review, formal review or mathematical values')
    read_record(retained['response'])
    native = json.loads(read_record(retained['agy_native_evidence']))
    require(native.get('schema')==NATIVE and native.get('case_id')==cid and native.get('phase')=='A1'
            and same(native.get('response'),retained['response']),
            'Neutral parent metadata borrowed another normal native source')
    raw = json.loads(read_record(link['raw_first_review']))
    formal = json.loads(read_record(link['formal_baseline_source_review']))
    if link['raw_first_review']['sha256'] == link['formal_baseline_source_review']['sha256']:
        require(raw==formal and link.get('source_fields',{})=={}, 'Unchanged native review bridge has extra mappings')
        return True
    require(formal.get('original_review')==link['raw_first_review']
            and formal.get('metadata_projection_only') is True and formal.get('new_candidate_calls')==0
            and formal.get('case_id')==cid and formal.get('stage')=='A1'
            and formal.get('answer_sha256')==retained['response']['sha256'],
            'Changed review identity is not a source-bound metadata-only projection')
    fields = link['source_fields']
    schema = formal.get('schema')
    if schema == 'math-gauge.theorem-extension-first-assessment-review-projection/v1':
        require(set(fields)=={'B','R'} and all(pointer(raw,fields[k])==formal.get(k) for k in ('B','R')),
                'Neutral parent TX projection changed its original B/R judgment')
    elif schema == 'math-gauge.background-check-review/v1':
        keys={'background_R','complete','false_endorsement'}
        require(set(fields)==keys and all(pointer(raw,fields[k])==formal.get(k) for k in keys),
                'Neutral parent background projection changed its original substantive judgments')
    elif schema == 'math-gauge.manuscript-completion-review/v1':
        require(set(fields)=={'units','unit_id','unit_score','strict_pass'}
                and pointer(raw,fields['strict_pass']) is formal.get('strict_pass'),
                'Neutral parent manuscript projection changed its original Strict judgment')
        units=pointer(raw,fields['units']); require(isinstance(units,list), 'Manuscript source units are absent')
        originals={u[fields['unit_id']]:u for u in units}
        component=json.loads(read_record(record['manuscript_completion_inputs']))
        case=next(c for c in component['case_index'] if c['case_id']==cid)
        criteria=formal.get('criteria',[])
        require(len(originals)==len(units)==len(criteria)==len(case['criteria'])
                and [c['id'] for c in criteria]==[c['criterion_id'] for c in case['criteria']]
                and set(originals)=={c['id'] for c in criteria}
                and all(c['points']==originals[c['id']][fields['unit_score']]
                        and c['max_points']==expected['points'] for c,expected in zip(criteria,case['criteria']))
                and criterion_total_matches(criteria,formal.get('score')),
                'Neutral parent manuscript projection changed original criterion identities/credit')
    else:
        raise ValueError('Unsupported native first-review normalization schema')
    return True
