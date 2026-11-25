"""Source-bound initiative judgments on a fixed common set of opportunities.

This evaluator component selects original evidence and validates new behavioral
reviews. Interval composition uses the shared scoring helpers; no main score,
source policy, original answer or historical profile is rewritten.
"""
from copy import deepcopy
from fractions import Fraction
import hashlib
import json
from pathlib import Path, PurePosixPath

from .evidence_retention import read_bytes
from .mathematical_profile import source_bytes
from .scoring import _average, _bound, _interval, _percent

VERSION = '0.1.0'
EDITION = '1.3.0'
CONDITION = 'nonlogical_retry_3'
DIRECTORY = 'results/research-initiative/v' + VERSION
INDEX_PATH = DIRECTORY + '/index.json'
ADDITIONS = {'gemini-4-carbon-medium': DIRECTORY + '/additions/gemini-4-carbon-medium.json'}
POLICY_PATH = 'protocol/research-initiative.json'
CONTRACT_PATH = 'protocol/research-initiative/v' + VERSION + '/contracts-v2.json'
DELIVERY_SUPPLEMENTS = 'protocol/research-initiative/v' + VERSION + '/delivery-supplements.json'
BASE_INDEX = 'results/mathematical-profiles/v0.4.0/index.json'
MANUSCRIPT_INDEX = 'results/open-research/v0.1.0/index.json'
ELIGIBLE = {'written-argument', 'theorem-extension', 'background-check', 'manuscript-completion'}
BOUNDARIES = dict(reviewer_kind='ai', human_review='pending', post_observation=True,
                  formal_comparison_eligible=False, new_candidate_calls=0,
                  main_scores_modified=False, original_bytes_rewritten=False)


def encoded(value):
    return (json.dumps(value, ensure_ascii=False, indent=2, allow_nan=False) + '\n').encode()


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def _need(value, message):
    if not value:
        raise ValueError(message)


def _text(value):
    return isinstance(value, str) and bool(value.strip()) and '\0' not in value


def _hash(value):
    return isinstance(value, str) and len(value) == 64 and all(c in '0123456789abcdef' for c in value)


def reference(root, path, repository):
    path, root = Path(path), Path(root)
    raw = read_bytes(path)
    return dict(repository=repository, path=path.relative_to(root).as_posix(),
                bytes=len(raw), sha256=digest(raw))


def read_source(roots, ref):
    _need(isinstance(ref, dict) and ref.get('repository') in roots,
          'Initiative source needs a known repository')
    return source_bytes(roots[ref['repository']], ref)


def load_policy(root):
    raw = read_bytes(Path(root) / POLICY_PATH)
    policy = json.loads(raw)
    _need(policy.get('schema') == 'math-gauge.research-initiative-policy/v1'
          and policy.get('version') == VERSION and policy.get('edition') == EDITION
          and policy.get('condition') == CONDITION, 'Unsupported initiative policy')
    _need(all(policy.get(k) == v for k, v in BOUNDARIES.items()),
          'Initiative cannot change calls, main scores or approval status')
    _need(policy.get('planned_opportunities') == 28 and policy.get('legacy_opportunities') == 27
          and policy.get('independent_opportunities') == 1 and policy.get('weights') == 'equal-opportunity'
          and policy.get('extension_weight') == '1/28', 'Initiative must keep its fixed common opportunity set')
    _need(policy.get('grade_fractions') == {'0': '0', '1': '1/4', '2': '1/2', '3': '3/4', '4': '1'}
          and policy.get('extension_assessment') == 'common-independent-0-to4-review;no-original-E-conversion'
          and _hash(policy.get('private_contract_sha256')), 'Initiative needs its common independent behavior scale')
    source_bytes(root, policy['source_profile_policy'])
    return policy, digest(raw)


def load_contracts(public_root, private_root, policy):
    roots = {'public': Path(public_root), 'private': Path(private_root)}
    raw = read_bytes(roots['private'] / CONTRACT_PATH)
    _need(digest(raw) == policy['private_contract_sha256'], 'Initiative contracts changed after their freeze')
    contracts = json.loads(raw)
    _need(contracts.get('schema') == 'math-gauge.research-initiative-contracts/v1'
          and contracts.get('version') == VERSION and contracts.get('edition') == EDITION
          and contracts.get('planned') == 28, 'Unsupported initiative contracts')
    old = json.loads(read_source(roots, contracts['legacy_contract']))
    original = {r['case_id']: r for r in old['tasks'] if r['kind'] == 'initial'}
    rows = contracts['tasks']
    _need(len(rows) == len(original) and len({r['id'] for r in rows}) == len(rows)
          and {r['id'] for r in rows} == set(original), 'Initiative screening must cover the original A1 suite')
    chosen = []
    for row in rows:
        source = original[row['id']]
        _need(all(row[k] == source[k] for k in ('family_id', 'public', 'subcategory',
                                               'candidate_task', 'candidate_task_text'))
              and row['required_goals'] == source['goals'], 'An initiative opportunity changed the original task scope')
        read_source(roots, row['candidate_task'])
        _need(row['eligible'] is (row['subcategory'] in ELIGIBLE)
              and _text(row['eligibility_reason']) and _text(row['extension_boundary']),
              'Initiative opportunities must follow the frozen task-based screening')
        if row['eligible']:
            chosen.append(row)
    _need(len(chosen) == len({r['family_id'] for r in chosen}) == 27
          and contracts['legacy_opportunities'] == [r['id'] for r in chosen]
          and policy['public_cases'] == [r['id'] for r in chosen if r['public']]
          and policy['private_legacy_count'] == sum(not r['public'] for r in chosen),
          'Initiative cannot select opportunities from observed model success')
    _need(contracts['independent_opportunity']['id'] == 'independent-extension'
          and contracts['independent_opportunity']['planned'] == 1
          and len(set(contracts['cohort'])) == len(contracts['cohort']) and contracts['cohort'],
          'Invalid initiative cohort or independent opportunity')
    return contracts


def _legacy_materials(roots, model_id, contracts):
    """Resolve the same selected original A1 and admitted manuscript sources."""
    private, public = roots['private'], roots['public']
    index = json.loads(read_bytes(private / BASE_INDEX))
    base_ref = dict(repository='private', **index['models'][model_id]['source-bindings'])
    base = json.loads(read_source(roots, base_ref))
    from .current_results import selected_current_record_paths
    _need(base['model_id'] == model_id and base['condition'] == CONDITION
          and base['sources']['public_source_record']['path'] == selected_current_record_paths(public)[model_id],
          'Initiative baseline must be the model\'s selected original record')
    read_source(roots, base['sources']['public_source_record'])
    old_rows = {r['id']: r for r in base['tasks']}
    open_index = json.loads(read_bytes(private / MANUSCRIPT_INDEX))
    manuscript_ref = dict(repository='private', **open_index['models'][model_id]['source-bindings'])
    manuscripts = json.loads(read_source(roots, manuscript_ref))
    _need(manuscripts['model_id'] == model_id and manuscripts['condition'] == CONDITION
          and manuscripts['sources']['base_materials'] == base_ref,
          'Initiative manuscript evidence belongs to a different original answer')
    manuscript_rows = {r['case_id']: r for r in manuscripts['first']}
    supplement_ref, supplements = _delivery_supplements(roots, model_id, base)
    rows = []
    for case in (r for r in contracts['tasks'] if r['eligible']):
        cid = case['id']
        original = old_rows[cid + ':A1']
        state = original['selected_state']
        classification = (state.get('submission_assessment') or {}).get('classification',
                          state.get('submission_classification'))
        refs = {}
        if original.get('raw_answer'):
            refs['answer'] = original['raw_answer']
        if cid in manuscript_rows:
            manuscript = manuscript_rows[cid]
            classification = manuscript['classification']
            refs.update({key: ref for key, ref in manuscript['sources'].items()
                         if key.startswith(('answer:', 'manuscript:', 'nonfinal_work:'))})
        refs.update(supplements.get(cid, {}))
        sources, seen = {}, set()
        for name, ref in refs.items():
            if ref['sha256'] in seen:
                continue
            raw = read_source(roots, ref)
            sources[name] = dict(ref, bytes=len(raw))
            seen.add(ref['sha256'])
        available = any(ref['bytes'] for ref in sources.values())
        status = 'available' if available else 'settled_blank' if classification == 'blank' else 'unavailable'
        rows.append(dict(opportunity_id=cid, classification=classification, source_status=status, sources=sources))
    bindings = dict(base_materials=base_ref, manuscript_materials=manuscript_ref)
    if supplement_ref:
        bindings['delivery_supplements'] = supplement_ref
    return bindings, rows


def _delivery_supplements(roots, model_id, base):
    """Replay a reviewed inventory of explicit legacy normal-final attachments.

    Old collectors sometimes sealed the work directory without hashing a named
    output attachment. Preserve that limitation: the supplement binds the
    archived file and actual visible native delivery, and never invents a
    terminal content hash or admits an unsubmitted workspace.
    """
    path = roots['private'] / DELIVERY_SUPPLEMENTS
    if not path.exists():
        return None, {}
    ref = reference(roots['private'], path, 'private')
    data = json.loads(read_source(roots, ref))
    _need(data.get('schema') == 'math-gauge.research-initiative-delivery-supplements/v1'
          and data.get('version') == VERSION and data.get('reviewer_kind') == 'ai'
          and data.get('human_review') == 'pending' and data.get('post_observation') is True
          and data.get('new_candidate_calls') == 0, 'Invalid delivered-file inventory supplement')
    result, seen = {}, set()
    for row in data['rows']:
        key = row['model_id'], row['opportunity_id'], row['source_id']
        _need(key not in seen, 'Duplicate delivered-file supplement')
        seen.add(key)
        if row['model_id'] != model_id:
            continue
        _need(row['record'] == base['sources']['private_source_record']
              and row['answer'] == base['sources']['answer:' + row['opportunity_id'] + ':A1']
              and row.get('terminal_content_digest_observed') is False
              and row.get('archive_bytes_match_current') is True
              and _text(row.get('provenance'))
              and len(row.get('archive_git_revision', '')) == 40
              and len(row.get('archive_blob', '')) == 40,
              'A delivered-file supplement changed its original answer or evidence limits')
        record = json.loads(read_source(roots, row['record']))
        selected = next(r for r in record['records'] if r['id'] == row['opportunity_id'] + ':A1')
        source = selected['source']
        prefix = str(PurePosixPath(row['record']['path']).parent) + '/'
        for field, source_name in (('events', 'native_events'), ('collection', 'collection')):
            expected = dict(repository='private', **source[source_name])
            expected['path'] = prefix + expected['path']
            _need(row[field] == expected, 'Delivered-file native evidence belongs to a different attempt')
        collection = json.loads(read_source(roots, row['collection']))
        answer = read_source(roots, row['answer']).decode('utf-8')
        named = row['native_named_path']
        native_relative = 'sessions/' + named.split('/sessions/', 1)[-1]
        _need(collection.get('qualified_delivery') is True
              and collection.get('native_terminal_completed') is True
              and collection.get('response_sha256') == row['answer']['sha256']
              and named in answer and '/output/artifacts/' in named
              and row['artifact']['path'] == prefix + native_relative
              and row['artifact']['path'].endswith(named.split('/output/artifacts/', 1)[-1]),
              'The file was not explicitly delivered by the selected normal final')
        events = [json.loads(line) for line in read_source(roots, row['events']).decode('utf-8').splitlines()]
        terminal = next(i for i, event in enumerate(events) if event.get('type') == 'turn.completed')
        _need(terminal == row['first_terminal_event'] and row['completed_file_change_events'],
              'Delivered-file supplement lacks its first native terminal')
        for i in row['completed_file_change_events']:
            event = events[i] if isinstance(i, int) and 0 <= i < terminal else {}
            item = event.get('item', {})
            _need(event.get('type') == 'item.completed' and item.get('type') == 'file_change'
                  and item.get('status') == 'completed'
                  and any(change.get('path') == named for change in item.get('changes', [])),
                  'The named file lacks a completed preterminal native write')
        read_source(roots, row['artifact'])
        result.setdefault(row['opportunity_id'], {})[row['source_id']] = row['artifact']
    return ref if result else None, result


def _sealed_sources(state):
    """Include every explicitly sealed companion, never the loose workspace."""
    from .independent_research_value import flow
    files = {}
    for rid in ('R1', 'R2', 'R3'):
        seal = json.loads(read_bytes(state / (rid + '.seal.json')))
        _need(seal['delivery'] == 'normal-final', 'Initiative needs the selected normal-final trajectory')
        entries = [(rid, seal['raw']), *((ref['path'], ref) for ref in seal.get('files', []))]
        for sid, ref in entries:
            flow._read(state, ref)
            files[sid] = flow._contained(state, ref['path'])
    return files


def _independent_materials(roots):
    """Use the three existing source owners; no native stream or hidden-thought extraction."""
    from . import independent_research_value as value
    from . import independent_research_external as external
    from . import independent_research_native as native
    private, public = roots['private'], roots['public']
    area = private / 'research-previews/v1.3.0'
    found = {}

    def add(mid, files, selection, cohort_result):
        _need(mid not in found, 'Duplicate independent initiative source cohort')
        refs = {name: reference(private, path, 'private') for name, path in files.items()}
        found[mid] = dict(opportunity_id='independent-extension', classification='three-normal-finals',
                         source_status='available', sources=refs,
                         selection=reference(private, selection, 'private'),
                         adopted_source_sha256=cohort_result['models'][mid]['source_sha256'])

    replay, reviews = area / 'evidence/gpt-20261123/replay', area / 'value-review-v0.2.0/reviews'
    gpt = value.prepare(replay, reviews, public)
    _need(gpt == json.loads(read_bytes(public / value.PUBLIC_PATH)), 'Retained independent GPT sources do not replay')
    selection_path = replay / value.SELECTION_PATH
    selection = json.loads(read_bytes(selection_path))
    old_root = PurePosixPath(selection['run_root'])
    selected = {r['id']: r for r in selection['models']}
    for mid in gpt['models']:
        execution = json.loads(value._archived(replay, old_root, selected[mid]['execution']))
        state = replay / execution['state']
        add(mid, _sealed_sources(state), selection_path, gpt)

    selection_path = area / 'evidence/external-20261124/selection-kimi-reaudit-20261124.json'
    if selection_path.is_file():
        external_result = external.prepare(selection_path, public)
        _need(external_result == json.loads(read_bytes(public / external.PUBLIC_PATH)),
              'Retained external independent sources do not replay')
        selection = json.loads(read_bytes(selection_path))
        for item in selection['models']:
            state = Path(item['state'])
            checked = external.validate_state(state, selection['bundle'])
            add(item['id'], {name: state / name for name in checked['files']}, selection_path, external_result)

    selection_path = area / 'evidence/agy-20261124/adoption/selection-current.json'
    if selection_path.is_file():
        native_result = native.prepare(selection_path, public)
        _need(native_result == json.loads(read_bytes(public / native.PUBLIC_PATH)),
              'Retained native independent sources do not replay')
        for item in json.loads(read_bytes(selection_path))['models']:
            retention_path = Path(item['retention']['path'])
            retained = json.loads(read_bytes(retention_path))
            state = retention_path.parent / retained['retained_source_root'] / retained['selected_state_relative']
            add(item['id'], _sealed_sources(state), selection_path, native_result)
    return found


def prepare_materials(public_root, private_root, policy, policy_hash, contracts):
    roots = {'public': Path(public_root), 'private': Path(private_root)}
    independent = _independent_materials(roots)
    result = {}
    for mid in contracts['cohort']:
        sources, rows = _legacy_materials(roots, mid, contracts)
        extra = independent.get(mid, dict(opportunity_id='independent-extension',
            classification='independent-task-not-yet-adopted', source_status='unavailable', sources={}))
        rows.append(extra)
        result[mid] = dict(schema='math-gauge.research-initiative-materials/v1', version=VERSION,
            edition=EDITION, model_id=mid, condition=CONDITION, policy_sha256=policy_hash,
            private_contract_sha256=policy['private_contract_sha256'], sources=sources,
            rows=rows, new_candidate_calls=0)
    return result


def validate_review(review, materials, policy, policy_hash, roots):
    _need(review.get('schema') == 'math-gauge.research-initiative-review/v1'
          and review.get('version') == VERSION and review.get('edition') == EDITION
          and review.get('model_id') == materials['model_id']
          and review.get('condition') == CONDITION and review.get('policy_sha256') == policy_hash
          and review.get('private_contract_sha256') == policy['private_contract_sha256'],
          'Initiative review has a different policy, model or source scope')
    _need(review.get('reviewer_kind') == 'ai' and review.get('human_review') == 'pending'
          and review.get('new_candidate_calls') == 0 and _text(review.get('reviewer_context_id')),
          'Initiative review cannot invent calls or human approval')
    expected = {r['opportunity_id']: r for r in materials['rows']}
    rows = review.get('rows', [])
    _need(len(rows) == len(expected) == policy['planned_opportunities']
          and {r.get('opportunity_id') for r in rows} == set(expected),
          'Initiative requires every fixed opportunity exactly once')
    cache, primary_cache = {}, {}
    for row in rows:
        material = expected[row['opportunity_id']]
        grade = row.get('grade')
        status = row.get('assessment_status')
        _need(row.get('model_id') == materials['model_id']
              and (grade is None or type(grade) is int and 0 <= grade <= 4),
              'Invalid initiative grade or model')
        primary = row.get('primary_review')
        _need(isinstance(primary, dict) and type(primary.get('row')) is int
              and primary['row'] >= 0, 'Initiative must retain its actual fresh primary review')
        primary_key = tuple(primary['ref'].get(k) for k in ('repository', 'path', 'sha256'))
        if primary_key not in primary_cache:
            primary_cache[primary_key] = json.loads(read_source(roots, primary['ref']))
        proposal = primary_cache[primary_key]
        reviewer = proposal.get('reviewer') or {}
        _need(proposal.get('schema') == 'math-gauge.research-initiative-review-proposal/v1'
              and proposal.get('reviewer_kind') == 'ai' and proposal.get('human_review') == 'pending'
              and reviewer.get('requested_model') == 'gpt-6.1-sol' and reviewer.get('effort') == 'max'
              and _text(reviewer.get('context')) and primary['row'] < len(proposal.get('rows', [])),
              'Initiative primary reviewer attribution is unbound')
        original = proposal['rows'][primary['row']]
        _need(original.get('model_id') == row['model_id']
              and original.get('opportunity_id') == row['opportunity_id'],
              'Initiative borrowed another primary review row')
        if original.get('grade') != grade:
            adjustment = row.get('coordinator_adjustment') or {}
            _need(adjustment.get('reviewer_kind') == 'ai' and adjustment.get('human_review') == 'pending'
                  and _text(adjustment.get('reason')), 'A coordinator grade correction needs its named reason')
        if material['source_status'] == 'unavailable':
            _need(grade is None and status == 'unavailable' and _text(row.get('grade_reason')),
                  'Unavailable initiative evidence must remain unknown')
            continue
        if material['source_status'] == 'settled_blank':
            _need(grade == 0 and status == 'settled_blank' and not row.get('evidence'),
                  'A settled blank has zero observed initiative and no invented quote')
            continue
        _need(grade is not None and status == 'reviewed' and row.get('full_delivery_read') is True
              and all(_text(row.get(key)) for key in ('original_requirement_boundary',
                  'independent_question', 'mathematical_check', 'grade_reason')),
              'A reviewed opportunity needs an actual complete-source judgment')
        if grade:
            _need(row['independent_question'].strip().lower() not in ('none', '无', '没有', 'n/a'),
                  'Positive initiative needs a concrete independent question')
        refs = row.get('evidence', [])
        _need(isinstance(refs, list) and refs, 'Nonempty initiative answers need original quotations')
        for quote in refs:
            sid = quote.get('source_id')
            _need(sid in material['sources'], 'Initiative quote borrowed an unselected source')
            ref = material['sources'][sid]
            key = (ref['repository'], ref['path'], ref['sha256'])
            if key not in cache:
                cache[key] = read_source(roots, ref)
            raw = cache[key]
            start, end = quote.get('start'), quote.get('end')
            _need(type(start) is int and type(end) is int and 0 <= start < end <= len(raw)
                  and quote.get('sha256') == ref['sha256'] and _text(quote.get('quote'))
                  and raw[start:end] == quote['quote'].encode(), 'Initiative quotation differs from the original bytes')
    return review


def _metric(rows):
    values = [_interval(None) if row['grade'] is None else (Fraction(row['grade'], 4),) * 3 for row in rows]
    low, high, exact = _average(values, [1] * len(values))
    value = _percent(exact)
    return dict(lower=_bound(low, lower=True) if value is None else value,
                upper=_bound(high, lower=False) if value is None else value,
                exact=value, confirmed=_percent(low), unknown_weight=_percent(high-low),
                coverage=dict(unit='research_opportunity', planned=len(rows),
                              reviewed=sum(row['grade'] is not None for row in rows)))


def score_review(review):
    """Use one fixed average; the independent three-round task counts once."""
    rows = review['rows']
    legacy = [r for r in rows if r['opportunity_id'] != 'independent-extension']
    extra = [r for r in rows if r['opportunity_id'] == 'independent-extension']
    _need(len(rows) == 28 and len(legacy) == 27 and len(extra) == 1, 'Invalid fixed initiative denominator')
    return dict(metric=_metric(rows), legacy_metric=_metric(legacy), extension_metric=_metric(extra),
                legacy_weight='27/28', extension_weight='1/28')


def public_projection(review, materials, policy_hash):
    return dict(schema='math-gauge.research-initiative-profile/v1', version=VERSION,
                edition=EDITION, model_id=review['model_id'], condition=CONDITION,
                policy_sha256=policy_hash, private_review_sha256=digest(encoded(review)),
                private_materials_sha256=digest(encoded(materials)), **score_review(review), **BOUNDARIES)


def validate_public(report, policy, policy_hash):
    fields = {'schema', 'version', 'edition', 'model_id', 'condition', 'policy_sha256',
              'private_review_sha256', 'private_materials_sha256', 'metric', 'legacy_metric',
              'extension_metric', 'legacy_weight', 'extension_weight', *BOUNDARIES}
    _need(set(report) == fields and report['schema'] == 'math-gauge.research-initiative-profile/v1'
          and report['version'] == VERSION and report['edition'] == EDITION
          and report['condition'] == CONDITION and report['policy_sha256'] == policy_hash
          and report['legacy_weight'] == '27/28' and report['extension_weight'] == '1/28'
          and all(report[k] == v for k, v in BOUNDARIES.items())
          and all(_hash(report[k]) for k in ('private_review_sha256', 'private_materials_sha256')),
          'Invalid aggregate-only initiative projection')
    for key, planned in (('metric', 28), ('legacy_metric', 27), ('extension_metric', 1)):
        metric = report[key]
        _need(set(metric) == {'lower', 'upper', 'exact', 'confirmed', 'unknown_weight', 'coverage'}
              and all(type(metric[k]) in (int, float) and 0 <= metric[k] <= 100
                      for k in ('lower', 'upper', 'confirmed', 'unknown_weight'))
              and metric['lower'] <= metric['confirmed'] <= metric['upper']
              and (metric['exact'] is None or type(metric['exact']) in (int, float)
                   and metric['lower'] == metric['exact'] == metric['upper'])
              and metric['coverage'].get('unit') == 'research_opportunity'
              and metric['coverage'].get('planned') == planned
              and type(metric['coverage'].get('reviewed')) is int
              and 0 <= metric['coverage']['reviewed'] <= planned
              and (metric['exact'] is None) == (metric['coverage']['reviewed'] < planned),
              'Initiative must retain known zero, genuine unknowns and fixed opportunity coverage')
        _need(set(metric['coverage']) == {'unit', 'planned', 'reviewed'}
              and abs(metric['unknown_weight'] - (metric['upper'] - metric['lower'])) < 1e-8,
              'Initiative coverage and interval width must remain aggregate only')
    metric, legacy, extra = (report[k] for k in ('metric', 'legacy_metric', 'extension_metric'))
    _need(metric['coverage']['reviewed'] == legacy['coverage']['reviewed'] + extra['coverage']['reviewed'],
          'Initiative coverage must count the independent opportunity once')
    for key in ('lower', 'upper', 'confirmed'):
        combined = _average([(Fraction(str(part[key])) / 100,) * 3 for part in (legacy, extra)], [27, 1])[2]
        _need(abs(metric[key] - _percent(combined)) < 1e-8, 'Initiative published components do not share one mean')
    return report


def validate_addition(addition, original, original_ref, root, policy, policy_hash):
    """Admit one independently reviewed opportunity without rewriting the old index."""
    from . import independent_research_admitted_delivery as admitted
    from . import independent_research_external as external

    fields = {'schema', 'version', 'edition', 'model_id', 'condition', 'policy_sha256',
              'base_profile', 'admitted_results', 'admitted_selection_sha256',
              'independent_review', 'profile', *BOUNDARIES}
    _need(isinstance(addition, dict) and set(addition) == fields
          and addition['schema'] == 'math-gauge.research-initiative-addition/v1'
          and addition['version'] == VERSION and addition['edition'] == EDITION
          and addition['model_id'] in ADDITIONS and addition['model_id'] == original['model_id']
          and addition['condition'] == CONDITION and addition['policy_sha256'] == policy_hash
          and all(type(addition[k]) is type(v) and addition[k] == v for k, v in BOUNDARIES.items()),
          'Invalid aggregate-only initiative addition')
    _need(isinstance(original_ref, dict) and set(original_ref) == {'path', 'bytes', 'sha256'}
          and addition['base_profile'] == original_ref
          and json.loads(source_bytes(root, original_ref)) == original,
          'Initiative addition must bind the unchanged indexed profile')
    ref = addition['admitted_results']
    _need(isinstance(ref, dict) and set(ref) == {'path', 'bytes', 'sha256'}
          and ref['path'] == admitted.PUBLIC_PATH.as_posix()
          and type(ref['bytes']) is int and ref['bytes'] >= 0 and _hash(ref['sha256']),
          'Initiative addition requires its exact public admitted-delivery aggregate')
    delivered = admitted.validate_public(json.loads(source_bytes(root, ref)),
        policies=external.policy_bindings(root), model_ids=[addition['model_id']])
    _need(_hash(addition['admitted_selection_sha256'])
          and addition['admitted_selection_sha256'] == delivered['source_binding']['adoption_sha256'],
          'Initiative addition binds a different admitted selection')
    primary = addition['independent_review']
    _need(isinstance(primary, dict) and set(primary) == {'primary_ai_review_sha256',
              'coordinator_selection_sha256', 'normalization_sha256', 'grade_0_to_4'}
          and all(_hash(primary[k]) for k in ('primary_ai_review_sha256',
              'coordinator_selection_sha256', 'normalization_sha256'))
          and type(primary['grade_0_to_4']) is int and primary['grade_0_to_4'] == 0,
          'Initiative addition requires the independent zero-grade AI judgment, not an E conversion')
    report = validate_public(addition['profile'], policy, policy_hash)
    _need(report['model_id'] == original['model_id']
          and original['extension_metric'] == _metric([{'grade': None}])
          and report['extension_metric'] == _metric([{'grade': primary['grade_0_to_4']}])
          and report['legacy_metric'] == original['legacy_metric']
          and report['metric']['confirmed'] == original['metric']['confirmed']
          and report['metric']['coverage']['reviewed'] == original['metric']['coverage']['reviewed'] + 1
          and all(report[k] != original[k] for k in ('private_review_sha256', 'private_materials_sha256')),
          'Initiative addition may settle only the unknown independent opportunity; legacy judgments stay unchanged')
    return report


def load_public(root, *, benchmark_version):
    root = Path(root)
    if benchmark_version != EDITION or not (root / INDEX_PATH).is_file():
        return None
    policy, policy_hash = load_policy(root)
    raw = read_bytes(root / INDEX_PATH)
    index = json.loads(raw)
    _need(index.get('schema') == 'math-gauge.research-initiative-index/v1'
          and index.get('version') == VERSION and index.get('edition') == EDITION
          and index.get('condition') == CONDITION and isinstance(index.get('models'), dict)
          and len(index['models']) == 20
          and index.get('policy_sha256') == policy_hash and all(index.get(k) == v for k, v in BOUNDARIES.items()),
          'Invalid initiative index')
    models, additions = [], []
    for mid, ref in index['models'].items():
        report = validate_public(json.loads(source_bytes(root, ref)), policy, policy_hash)
        _need(report['model_id'] == mid, 'Initiative aggregate belongs to another model')
        addition_path = ADDITIONS.get(mid)
        if addition_path and (root / addition_path).is_file():
            addition_raw = read_bytes(root / addition_path)
            report = validate_addition(json.loads(addition_raw), report, ref, root, policy, policy_hash)
            additions.append(dict(path=addition_path, bytes=len(addition_raw), sha256=digest(addition_raw)))
        models.append(dict(id=mid, **{k: deepcopy(report[k]) for k in
                           ('metric', 'legacy_metric', 'extension_metric', 'legacy_weight', 'extension_weight')}))
    result = dict(schema='math-gauge.research-initiative/v1', version=VERSION,
                benchmark_version=EDITION, policy_sha256=policy_hash,
                source=dict(path=INDEX_PATH, bytes=len(raw), sha256=digest(raw)),
                models=models, **BOUNDARIES)
    if additions:
        result['additions'] = additions
    return result
