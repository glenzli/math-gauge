"""Authenticate an independent, common-opportunity research-capability axis.

The retained profile and execution owners supply exact deliveries. This owner
validates new mathematical judgments; only scoring.py performs aggregation.
"""
from copy import deepcopy
import hashlib
import io
import json
import math
from pathlib import Path
import tarfile

from .evidence_retention import read_bytes, is_file
from .mathematical_profile import _require, _text, _hash, _pointer, source_bytes

VERSION = '0.1.0'
EDITION = '1.2.0'
CONDITION = 'nonlogical_retry_3'
AXIS = 'open_research'
FAMILIES = 5
FACETS = ('formulation', 'mechanism', 'scope', 'closure')
POLICY_PATH = 'protocol/open-research.json'
DIRECTORY = 'results/open-research/v0.1.0'
INDEX_PATH = DIRECTORY + '/index.json'
NONFINAL_ADMISSION = DIRECTORY + '/review-source/nonfinal-source-admission-final.json'
BASE_INDEX = 'results/mathematical-profiles/v0.4.0/index.json'
REVISION_INDEX = 'results/mathematical-profile-revisions/v0.1.0/index.json'
CORE_STATES = {'established', 'local_gap', 'unresolved_core', 'refuted_core',
               'no_valid_progress', 'not_run', 'source_unresolved'}
STATUSES = {'reviewed', 'operational_zero', 'not_run', 'source_unresolved'}
BOUNDARIES = dict(reviewer_kind='ai', human_review='pending', post_observation=True,
                  formal_comparison_eligible=False, new_candidate_calls=0,
                  main_scores_modified=False, original_bytes_rewritten=False)


def encoded(value):
    return (json.dumps(value, ensure_ascii=False, indent=2) + '\n').encode()


def reference(path, raw, repository=None):
    result = dict(path=str(path), bytes=len(raw), sha256=hashlib.sha256(raw).hexdigest())
    if repository:
        result['repository'] = repository
    return result


def _read(roots, ref):
    _require(ref.get('repository') in roots, 'Unknown open-research source repository')
    return source_bytes(roots[ref['repository']], ref)


def validate_policy(policy):
    fixed = dict(schema='math-gauge.open-research-policy/v1', version=VERSION,
        benchmark_version=EDITION, condition=CONDITION, planned_families=FAMILIES,
        research_tasks_screened=15, not_elicited_tasks=10, public_families=1,
        private_families=4, facets=list(FACETS), grade_min=0, grade_max=4,
        family_weight='1/5', original_weight='4/5', revision_weight='1/5',
        grade_gate='essential-unproved-or-refuted-core-or-unbridged-scope-drift-caps-grade2',
        opportunity='explicitly-open-manuscript-tasks;no-unsolicited-extension-bonus',
        initiative='first-answer-only;separate-behavior;display-last', **BOUNDARIES)
    _require(all(type(policy.get(k)) is type(v) and policy[k] == v for k,v in fixed.items()),
             'Unsupported open-research policy or opportunity denominator')
    _require(set(policy) == set(fixed) | {'axis', 'anchors', 'private_contract_sha256'}
             and _hash(policy.get('private_contract_sha256')),
             'Open-research policy must bind its private contracts')
    axis = policy['axis']
    _require(set(axis) == {'id', 'label', 'description'} and axis['id'] == AXIS,
             'Open-research policy needs its independent axis')
    for field in ('label', 'description'):
        _require(set(axis[field]) == {'zh', 'en'} and all(_text(v) for v in axis[field].values()),
                 'Open-research axis needs bilingual copy')
    _require(policy['anchors']['path'] == 'protocol/open-research.md',
             'Open-research policy must bind its actual rubric')
    return policy


def load_policy(root):
    raw = read_bytes(Path(root) / POLICY_PATH)
    policy = validate_policy(json.loads(raw))
    source_bytes(root, policy['anchors'])
    return policy, hashlib.sha256(raw).hexdigest()


def validate_contracts(contracts, policy, roots):
    _require(contracts.get('schema') == 'math-gauge.open-research-contracts/v1'
             and contracts.get('version') == VERSION
             and contracts.get('benchmark_version') == EDITION,
             'Invalid open-research contracts')
    original = json.loads(_read(roots, contracts['source_profile_contracts']))
    opportunities = [r for r in original['tasks'] if r['kind'] == 'initial'
                     and r['subcategory'] in {'manuscript-completion', 'theorem-extension', 'background-check'}]
    by_id = {r['case_id']:r for r in opportunities}
    rows, audit = contracts['families'], contracts['opportunity_audit']
    _require(len(rows) == FAMILIES and len({r['case_id'] for r in rows}) == FAMILIES
             and sum(r['public'] for r in rows) == policy['public_families']
             and len(audit) == len(by_id) == policy['research_tasks_screened'],
             'Open-research common opportunity set differs')
    _require({r['case_id'] for r in rows} == {r['case_id'] for r in opportunities
                 if r['subcategory'] == 'manuscript-completion'},
             'Fixed proof/audit tasks cannot silently become open-capability failures')
    for row in rows:
        old = by_id[row['case_id']]
        _require(row['family_id'] == old['family_id'] and row['public'] == old['public']
                 and row['weight'] == policy['family_weight']
                 and row['candidate_task'] == old['candidate_task']
                 and set(row['core_anchors']) == set(FACETS)
                 and all(_text(v) for v in row['core_anchors'].values()),
                 'Open-research family must preserve its original task and explicit anchors')
        ref = row['candidate_task']
        task = _read(roots, ref).decode('utf-8')
        _require(row['request_quote'] in task, 'Open opportunity quote is not in the original task')
    _require({r['case_id'] for r in audit} == set(by_id), 'Opportunity audit misses a research task')
    for row in audit:
        old = by_id[row['case_id']]
        expected = 'explicit_open' if old['subcategory'] == 'manuscript-completion' else 'not_elicited'
        _require(row['classification'] == expected and _text(row['reason'])
                 and row['candidate_task'] == old['candidate_task'],
                 'Opportunity audit must use the original request, not observed model behavior')
        _require(row['request_quote'] in _read(roots, row['candidate_task']).decode('utf-8'),
                 'Opportunity audit quote differs from actual task bytes')
    return contracts


def _allowed_base_sources(base, original, contract):
    slot = original['id']
    names = {'answer:' + slot, 'content_review', 'goal_review', 'selected_report'}
    selected = {k:deepcopy(v) for k,v in base['sources'].items()
                if k in names or k.startswith('manuscript:' + slot + ':')}
    selected['task'] = deepcopy(contract['candidate_task'])
    return selected


def _nonfinal_sources(roots, model_id, original, admission):
    """Admit only previously selected cutoff mathematics, never a workspace union."""
    cid = original['id'].split(':')[0]
    matches = [r for r in [*admission['case_id_to_admission'].values(),
                           *admission['analogous_already_bound_sources']]
               if r['model_id'] == model_id and r['case_id'] == cid]
    if not matches:
        return {}, {}
    _require(len(matches) == 1, 'Duplicate nonfinal research source admission')
    row = matches[0]
    state = original['selected_state']['submission_assessment']
    _require(state['classification'] == row['classification'] == 'forced_content'
             and row['source_repaired'] is False and row['cross_attempt_union'] is False
             and row['work_review']['sha256'] == state['work_review_sha256'],
             'Nonfinal research must retain its exact condition-selected work review')
    work = json.loads(_read(roots, row['work_review']))
    _require(work['case_id'] == cid and work['attempt_condition'] == CONDITION
             and work['source_repaired'] is False and work['deadline_existence_verified'] is True
             and work['new_candidate_calls'] == 0,
             'Nonfinal research lacks its original cutoff and unrepaired-source boundary')
    sources = {'nonfinal_review':row['work_review']}
    prefixes = {}
    original_review = row.get('original_judgment_source', row.get('original_review'))
    if original_review:
        sources['nonfinal_original_review'] = original_review
        prefix = row.get('original_judgment_pointer')
        if prefix:
            prefixes['nonfinal_original_review'] = prefix.rsplit('/axes',1)[0]
    for i,item in enumerate(row['candidate_original_sources']):
        raw = _read(roots, item['ref'])
        seal = _read(roots, item['seal'])
        if item.get('seal_kind') == 'native_terminal_work_inventory':
            inventory = json.loads(seal)
            match = [r for r in inventory['work'] if r['path'] == item['member_name']]
            _require(len(match) == 1 and match[0]['sha256'] == item['ref']['sha256']
                     and match[0]['bytes'] == len(raw)
                     and inventory['normal_complete_delivery'] is False,
                     'Cutoff mathematics differs from its original native terminal inventory')
        else:
            with tarfile.open(fileobj=io.BytesIO(seal), mode='r:gz') as archive:
                member = archive.getmember(item['member_name'])
                _require(member.isfile() and member.size == len(raw)
                         and archive.extractfile(member).read() == raw,
                         'Nonfinal mathematics differs from the exact selected seal member')
        sources['nonfinal_work:' + str(i)] = item['ref']
    return sources, prefixes


def prepare_materials(public_root, private_root, model_id, policy, digest, contracts_ref, *, selected_sources=None):
    """Inventory exact retained sources only; this does not judge mathematics."""
    roots = dict(public=Path(public_root), private=Path(private_root))
    contracts = json.loads(_read(roots, contracts_ref))
    validate_contracts(contracts, policy, roots)
    base_index = json.loads(read_bytes(roots['private'] / BASE_INDEX))
    expected_base_ref = dict(repository='private', **base_index['models'][model_id]['source-bindings'])
    base_ref = selected_sources['base_materials'] if selected_sources is not None else expected_base_ref
    _require(base_ref == expected_base_ref, 'Research baseline is not the indexed selected answer source')
    base = json.loads(_read(roots, base_ref))
    _require(base['model_id'] == model_id and base['condition'] == CONDITION,
             'Open-research baseline is another model or attempt condition')
    originals = {r['id']:r for r in base['tasks']}
    report = json.loads(_read(roots, base['sources']['selected_report']))
    report_rows = {r['case_id']:i for i,r in enumerate(report['tasks'])}
    families = []
    admission_path = roots['private'] / NONFINAL_ADMISSION
    admission_raw = read_bytes(admission_path) if is_file(admission_path) else None
    admission = json.loads(admission_raw) if admission_raw is not None else None
    for contract in contracts['families']:
        cid, slot = contract['case_id'], contract['case_id'] + ':A1'
        old = originals[slot]
        classification = (old['selected_state'].get('submission_assessment') or {}).get(
            'classification', old['selected_state'].get('submission_classification'))
        bound = _allowed_base_sources(base, old, contract)
        extra, prefixes = _nonfinal_sources(roots, model_id, old, admission) if admission else ({},{})
        bound.update(extra)
        families.append(dict(case_id=cid, family_id=contract['family_id'],
            classification=classification, response_sha256=old['response_sha256'],
            content_index=old['content_index'], goal_index=old['goal_index'],
            report_index=report_rows[cid], evidence_prefixes=prefixes, sources=bound))
    sources = dict(contracts=contracts_ref, base_materials=base_ref)
    if any(any(k.startswith('nonfinal_') for k in r['sources']) for r in families):
        sources['nonfinal_admission'] = reference(NONFINAL_ADMISSION, admission_raw, 'private')
    revisions, available = [], False
    path = roots['private'] / REVISION_INDEX
    revision_index = json.loads(read_bytes(path)) if is_file(path) else {'models':{}}
    chosen_revision = (selected_sources.get('revision_materials') if selected_sources is not None
                       else dict(repository='private', **revision_index['models'][model_id]['source-bindings'])
                       if model_id in revision_index['models'] else None)
    if chosen_revision is not None:
        _require(model_id in revision_index['models'] and chosen_revision == dict(
            repository='private', **revision_index['models'][model_id]['source-bindings']),
            'Research continuation is not an indexed adopted-source snapshot')
        ref = chosen_revision
        materials = json.loads(_read(roots, ref))
        _require(materials['model_id'] == model_id and materials['condition'] == CONDITION,
                 'Open-research continuation belongs to another model or condition')
        sources['revision_materials'] = ref
        eligible = {r['case_id'] for r in contracts['families']}
        for row in materials['tasks']:
            if row['case_id'] in eligible:
                parent = next(r for r in families if r['case_id'] == row['case_id'])
                _require(row['revision_ref']['first_response_sha256'] == parent['response_sha256'],
                         'Research continuation is attached to a different first answer')
                revisions.append(dict(case_id=row['case_id'], sources=deepcopy(row['sources']),
                    status=row['revision_ref']['continuation']['status'],
                    first_response_sha256=row['revision_ref']['first_response_sha256']))
        available = True
    return dict(schema='math-gauge.open-research-materials/v1', version=VERSION,
        benchmark_version=EDITION, model_id=model_id, condition=CONDITION,
        policy_sha256=digest, sources=sources, first=families, revision=revisions,
        revision_available=available, new_candidate_calls=0)


def validate_judgment(row, material, *, stage, read_source):
    grade, status = row.get('grade'), row.get('assessment_status')
    _require(grade is None or type(grade) is int and 0 <= grade <= 4,
             'Research capability requires an independent integer0to4 grade or unknown')
    _require(status in STATUSES and (grade is None) == (status in {'not_run', 'source_unresolved'}),
             'Research evidence must distinguish actual zeros from unknowns')
    core, drift = row.get('core_status'), row.get('core_scope_failure')
    _require(core in CORE_STATES and _text(row.get('reason')),
             'Research judgment must state its actual core and mathematical reason')
    _require(grade is None or core not in {'not_run', 'source_unresolved'},
             'A known research grade cannot hide an unresolved source state')
    _require(drift is None if grade is None else type(drift) is bool,
             'Research scope gates need an explicit independent finding')
    _require(grade is None or grade <= 2 or core in {'established', 'local_gap'} and not drift,
             'Essential research core or scope failures cannot receive grade3or4')
    facets = row.get('facets', {})
    _require(set(facets) == set(FACETS) and all(v.get('status') in CORE_STATES and _text(v.get('reason'))
             for v in facets.values()), 'Research review needs all four evidence facets')
    if grade == 4:
        _require(core == 'established' and all(v['status'] == 'established' for v in facets.values()),
                 'Research grade4 requires all four requested-core facets to be established')
    if grade == 3:
        _require(all(v['status'] in {'established', 'local_gap'} for v in facets.values()),
                 'Research grade3 permits only a precise local gap requiring no new mechanism')
    if grade is None:
        _require(core == status and all(v['status'] == status for v in facets.values())
                 and _text(row.get('missing_evidence')),
                 'Unknown research capability must identify the missing actual evidence')
    state = material.get('classification') if stage == 'first' else material['status']
    if state == 'not_run':
        _require(grade is None and status == 'not_run', 'Unrun research cannot receive an invented grade')
    elif state == 'blank':
        _require((grade == 0 and status == 'operational_zero') or
                 (grade is None and status == 'source_unresolved'),
                 'Blank research must retain zero, or an explicit missing-original uncertainty')
    elif status == 'operational_zero':
        _require(grade == 0 and state in {'forced_content', 'delivery_failed'},
                 'Operational research zero needs a settled nondelivery')
    _require(isinstance(row.get('limitations'), list) and all(_text(v) for v in row['limitations'])
             and _text(row.get('optional_errors_disposition')),
             'Research review must preserve limitations and optional-error boundaries')
    entries, original_quote = row.get('evidence'), False
    _require(isinstance(entries, list) and entries, 'Every research judgment needs exact task-local evidence')
    for entry in entries:
        _require(set(entry) == {'source_id', 'pointer', 'quote'} and _text(entry['quote'])
                 and entry['source_id'] in material['sources'], 'Research evidence uses an unbound source')
        ident, pointer = entry['source_id'], entry['pointer']
        if ident in {'content_review', 'goal_review', 'selected_report'}:
            index = material[{'content_review':'content_index', 'goal_review':'goal_index',
                              'selected_report':'report_index'}[ident]]
            prefix = '/tasks/' + str(index)
            _require(pointer == prefix or pointer.startswith(prefix + '/'),
                     'Research evidence comes from another mathematical task')
        if ident in material.get('evidence_prefixes', {}):
            prefix = material['evidence_prefixes'][ident]
            _require(pointer == prefix or pointer.startswith(prefix + '/'),
                     'Nonfinal review evidence comes from another selected cutoff task')
        ref = material['sources'][ident]
        raw = read_source(ref)
        if ref['path'].endswith('.json'):
            value = _pointer(json.loads(raw), pointer)
            text = value if isinstance(value, str) else json.dumps(value, ensure_ascii=False)
        else:
            _require(pointer == '', 'Raw research evidence cannot contain a JSON pointer')
            text = raw.decode('utf-8')
        _require(entry['quote'] in text, 'Research quote is absent from the retained original source')
        original_quote |= ident in {'answer', 'cutoff_content'} or ident.startswith(
            ('answer:', 'manuscript:', 'attachment:', 'nonfinal_work:'))
    _require(not grade or original_quote, 'Positive research capacity needs actual delivered mathematics')
    return row


class ResearchInputs:
    """Authenticated independent judgments for the shared scoring owner."""
    def __init__(self, review, materials, *, public_root, private_root, policy, policy_sha256):
        validate_policy(policy)
        roots = dict(public=Path(public_root), private=Path(private_root))
        ref = materials['sources']['contracts']
        _require(ref['sha256'] == policy['private_contract_sha256'],
                 'Research review changed the frozen opportunity contracts')
        contracts = json.loads(_read(roots, ref))
        expected = prepare_materials(public_root, private_root, review['model_id'], policy,
                                     policy_sha256, ref, selected_sources=materials['sources'])
        _require(expected == materials, 'Research sources changed or use an unselected original/revision')
        fixed = dict(schema='math-gauge.open-research-review/v1', version=VERSION,
            benchmark_version=EDITION, condition=CONDITION, model_id=materials['model_id'],
            policy_sha256=policy_sha256, materials_sha256=hashlib.sha256(encoded(materials)).hexdigest(),
            **BOUNDARIES)
        _require(set(review) == set(fixed) | {'reviewer_id', 'tasks'}
                 and all(type(review.get(k)) is type(v) and review[k] == v for k,v in fixed.items())
                 and _text(review.get('reviewer_id')), 'Research review lost its actual identity or AI boundary')
        pairs = {(stage,r['case_id']):r for stage in ('first','revision') for r in materials[stage]}
        rows = review['tasks']
        _require(len(rows) == len(pairs) and {(r['stage'],r['case_id']) for r in rows} == set(pairs),
                 'Research review must cover each fixed family and every selected manuscript continuation')
        cache = {}
        def read(ref):
            key = (ref['repository'], ref['path'], ref['sha256'])
            if key not in cache:
                cache[key] = _read(roots, ref)
            return cache[key]
        for row in rows:
            _require(row.get('model_id') == materials['model_id'], 'Research judgment belongs to another model')
            validate_judgment(row, pairs[(row['stage'],row['case_id'])], stage=row['stage'], read_source=read)
        self.review, self.materials, self.contracts, self.policy = review, materials, contracts, policy


def project_public(score, *, policy, policy_sha256, review_sha256, materials_sha256):
    report = dict(schema='math-gauge.open-research-model/v1', version=VERSION,
        benchmark_version=EDITION, condition=CONDITION, model_id=score['model_id'],
        policy_sha256=policy_sha256, private_review_sha256=review_sha256,
        private_materials_sha256=materials_sha256, first=deepcopy(score['first']),
        revision=deepcopy(score['revision']), **BOUNDARIES)
    return validate_public(report, policy, policy_sha256)


def validate_public(report, policy, digest):
    fields = {'schema','version','benchmark_version','condition','model_id','policy_sha256',
              'private_review_sha256','private_materials_sha256','first','revision'} | set(BOUNDARIES)
    _require(set(report) == fields and report['schema'] == 'math-gauge.open-research-model/v1'
             and report['version'] == VERSION and report['benchmark_version'] == EDITION
             and report['condition'] == CONDITION and report['policy_sha256'] == digest
             and _text(report['model_id']) and _hash(report['private_review_sha256'])
             and _hash(report['private_materials_sha256'])
             and all(report[k] == v for k,v in BOUNDARIES.items()),
             'Unsafe or unsupported public research projection')
    for stage in ('first','revision'):
        metric = report[stage]
        if metric is None:
            _require(stage == 'revision', 'Every admitted model needs first-answer research evidence')
            continue
        _require(set(metric) == {'exact','confirmed','lower','upper','unknown_weight','coverage'}
                 and set(metric['coverage']) == {'unit','planned','reviewed'}
                 and metric['coverage']['unit'] == 'open_research_family'
                 and metric['coverage']['planned'] == FAMILIES
                 and type(metric['coverage']['reviewed']) is int
                 and 0 <= metric['coverage']['reviewed'] <= FAMILIES,
                 'Research coverage must retain the common five-family denominator')
        for key in ('confirmed','lower','upper','unknown_weight'):
            _require(type(metric[key]) in (int,float) and math.isfinite(metric[key])
                     and 0 <= metric[key] <= 100, 'Invalid research interval')
        exact = metric['exact']
        _require(metric['lower'] <= metric['confirmed'] <= metric['upper']
                 and abs(metric['upper']-metric['lower']-metric['unknown_weight']) < 1e-8
                 and ((exact is None and metric['unknown_weight'] > 0) or
                      type(exact) in (int,float) and metric['lower'] == exact == metric['upper']),
                 'Unknown research must not be rescaled or replaced with an exact score')
    return report


def pending_metric():
    """A missing independent review is an interval, not inherited capability."""
    return dict(exact=None, confirmed=0.0, lower=0.0, upper=100.0, unknown_weight=100.0,
                coverage=dict(unit='open_research_family', planned=FAMILIES, reviewed=0))


def load_public(root, *, benchmark_version):
    """Current1.2 only: historical profile policies and JSON stay untouched."""
    root = Path(root)
    if benchmark_version != EDITION or not is_file(root / INDEX_PATH):
        return None
    policy, digest = load_policy(root)
    raw = read_bytes(root / INDEX_PATH)
    index = json.loads(raw)
    _require(set(index) == {'schema','version','benchmark_version','condition','policy_sha256','models'}
                 | set(BOUNDARIES)
             and index['schema'] == 'math-gauge.open-research-index/v1'
             and index['version'] == VERSION and index['benchmark_version'] == EDITION
             and index['condition'] == CONDITION and index['policy_sha256'] == digest
             and all(index[k] == v for k,v in BOUNDARIES.items()),
             'Invalid research capability index')
    models = []
    for mid,ref in index['models'].items():
        report = validate_public(json.loads(source_bytes(root, ref)), policy, digest)
        _require(report['model_id'] == mid, 'Public research model source mismatch')
        models.append(dict(id=mid, first=report['first'], revision=report['revision']))
    return dict(schema='math-gauge.open-research/v1', version=VERSION,
        benchmark_version=EDITION, axis=deepcopy(policy['axis']), models=models,
        planned_families=FAMILIES, pending_metric=pending_metric(), policy_sha256=digest,
        source=reference(INDEX_PATH, raw), **BOUNDARIES)
