"""Independent current-edition structural-depth and open-research assessments.

Owns source selection, judgments and aggregate-only projections. Main scores,
legacy profile policies and mathematical answers are never modified here.
"""
from copy import deepcopy
from fractions import Fraction
import hashlib
import json
import re
from pathlib import Path, PurePosixPath

from .evidence_retention import read_bytes
from .mathematical_profile import source_bytes, _pointer

VERSION = '0.1.0'
EDITION = '1.3.0'
CONDITION = 'nonlogical_retry_3'
POLICY_PATH = 'protocol/profile-structure.json'
CONTRACT_PATH = 'protocol/profile-structure/v0.1.0/contracts.json'
DIRECTORY = 'results/profile-structure/v0.1.0'
INDEX_PATH = DIRECTORY + '/index.json'
AXES = ('depth', 'open_research')
PLANNED = dict(depth=28, open_research=6)
WEIGHTS = dict(depth=69, open_research=11)
FACETS = dict(depth=('mechanism', 'bridge', 'conditions', 'unification'),
              open_research=('formulation', 'mechanism', 'scope', 'closure'))
FACET_STATES = {'established', 'local_gap', 'essential_gap', 'refuted', 'unbridged_scope', 'unknown'}
STATUSES = {'reviewed', 'settled_blank', 'unrun', 'source_unresolved', 'review_pending'}
BOUNDARIES = dict(reviewer_kind='ai', human_review='pending', post_observation=True,
                  formal_comparison_eligible=False, new_candidate_calls=0,
                  main_scores_modified=False, original_bytes_rewritten=False)


def encoded(value):
    return (json.dumps(value, ensure_ascii=False, indent=2, allow_nan=False) + '\n').encode()


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def _need(condition, message):
    if not condition:
        raise ValueError(message)


def _text(value):
    return isinstance(value, str) and bool(value.strip()) and '\0' not in value


def _hash(value):
    return isinstance(value, str) and len(value) == 64 and all(c in '0123456789abcdef' for c in value)


def _read(roots, ref):
    _need(isinstance(ref, dict) and ref.get('repository') in roots,
          'Profile source requires an explicit public or private repository')
    return source_bytes(roots[ref['repository']], ref)


def _ref_key(ref):
    _need(isinstance(ref, dict), 'A source descriptor must be an object')
    return tuple(ref.get(k) for k in ('repository', 'path', 'sha256'))


def _boundary(value):
    return all(type(value.get(k)) is type(v) and value[k] == v for k, v in BOUNDARIES.items())


def load_policy(root):
    raw = read_bytes(Path(root) / POLICY_PATH)
    policy = json.loads(raw)
    _need(policy.get('schema') == 'math-gauge.profile-structure-policy/v1'
          and policy.get('version') == VERSION and policy.get('edition') == EDITION
          and policy.get('condition') == CONDITION and _boundary(policy),
          'Unsupported structural profile policy or assessment boundary')
    _need(policy.get('planned') == PLANNED and policy.get('weights') == WEIGHTS
          and policy.get('revision') == dict(original_weight='4/5', revision_weight='1/5')
          and _hash(policy.get('private_contract_sha256')),
          'Structural profiles must retain frozen opportunities, weights and revision blend')
    _need(policy.get('grade_scale') == dict(minimum=0, maximum=4, display_multiplier=25),
          'Structural profile must retain the independent0–4 grade scale')
    _need(set(policy.get('axes', {})) == set(AXES), 'Structural profile needs exactly its two axes')
    for axis in policy['axes'].values():
        _need(all(isinstance(axis.get(k), dict) and set(axis[k]) == {'zh', 'en'}
                  and all(_text(v) for v in axis[k].values()) for k in ('label', 'description')),
              'Structural profile axes require bilingual definitions')
    return policy, digest(raw)


def validate_contracts(contracts, policy):
    _need(contracts.get('schema') == 'math-gauge.profile-structure-contracts/v1'
          and contracts.get('version') == VERSION and contracts.get('edition') == EDITION
          and contracts.get('condition') == CONDITION,
          'Unsupported structural profile contracts')
    cohort = contracts.get('cohort', [])
    _need(len(cohort) == len(set(cohort)) == 20
          and all(isinstance(mid, str) and re.fullmatch(r'[a-z0-9][a-z0-9._-]*', mid) for mid in cohort),
          'Structural profile requires the selected twenty retained configurations')
    depth, research = contracts['depth'], contracts['open_research']
    families, bindings = depth['families'], depth['task_bindings']
    _need(depth['family_count'] == len(families) == 28 and depth['task_count'] == len(bindings) == 30
          and depth['weight_total'] == sum(f['weight'] for f in families) == policy['weights']['depth']
          and len({f['family_id'] for f in families}) == 28,
          'Structural depth must keep thirty tasks, twenty-eight families and weight sixty-nine')
    members = []
    for family in families:
        cases = family['case_ids']
        split = family['variant_split']
        _need(type(family['weight']) is int and family['weight'] in (1, 2, 3)
              and len(cases) == len(set(cases)) and cases
              and [s['case_id'] for s in split] == cases
              and all(Fraction(s['numerator'], s['denominator']) == Fraction(1, len(cases)) for s in split),
              'Depth variants must be equally combined within each frozen opportunity')
        members.extend(cases)
    _need(len(members) == len(set(members)) == 30
          and {r['case_id'] for r in bindings} == set(members),
          'Depth opportunity bindings are missing, duplicated or foreign')
    opportunities = research['opportunities']
    _need(research['opportunity_count'] == len(opportunities) == 6
          and research['weight_total'] == policy['weights']['open_research'] == 11
          and len({r['case_id'] for r in opportunities}) == 6
          and [r['opportunity_factor'] for r in opportunities] == [1, 2, 1, 2, 2, 3]
          and all(Fraction(r['weight']) == Fraction(r['opportunity_factor'], 11) for r in opportunities),
          'Open research must retain its six common opportunities and eleven fixed weight units')
    independent = [r for r in opportunities if r['stage_rule'].startswith('R3_actual_delivery')]
    _need(len(independent) == 1 and independent[0]['opportunity_factor'] == 3,
          'Only the prescribed final research delivery is the independent opportunity')
    return contracts


def validate_source_tree(value, roots, cache=None):
    """Hash every actual frozen candidate descriptor, including nested assets."""
    cache = {} if cache is None else cache
    if isinstance(value, dict):
        if {'repository', 'path', 'sha256'} <= set(value):
            key = _ref_key(value)
            if key not in cache:
                cache[key] = _read(roots, value)
            elif 'bytes' in value:
                _need(type(value['bytes']) is int and len(cache[key]) == value['bytes'],
                      'A repeated structural candidate descriptor changed its declared size')
        for item in value.values():
            validate_source_tree(item, roots, cache)
    elif isinstance(value, list):
        for item in value:
            validate_source_tree(item, roots, cache)
    return cache


def load_contracts(public_root, private_root, policy):
    raw = read_bytes(Path(private_root) / CONTRACT_PATH)
    _need(digest(raw) == policy['private_contract_sha256'], 'Structural profile contracts changed after freeze')
    contracts = validate_contracts(json.loads(raw), policy)
    roots = dict(public=Path(public_root), private=Path(private_root))
    validate_source_tree(contracts, roots)
    frozen = json.loads(_read(roots, contracts['design_sources']['depth-opportunities.json']))
    opened = json.loads(_read(roots, contracts['design_sources']['open-opportunities.json']))
    _need(contracts['depth']['families'] == frozen['families']
          and contracts['depth']['task_bindings'] == frozen['task_bindings']
          and contracts['open_research']['opportunities'] == opened['opportunities'],
          'Structural profile contracts changed their independently frozen task opportunities')
    return contracts


def independent_case(contracts):
    return next(r['case_id'] for r in contracts['open_research']['opportunities']
                if r['stage_rule'].startswith('R3_actual_delivery'))


def _case(cid, contracts):
    return independent_case(contracts) if cid == 'independent-research' else cid


def _key(row, contracts):
    return row['axis'], _case(row['case_id'], contracts), row['stage']


def _known_cases(contracts):
    return dict(depth={r['case_id'] for r in contracts['depth']['task_bindings']},
                open_research={r['case_id'] for r in contracts['open_research']['opportunities']})


def _verification_pointer(raw, pointer):
    _need(isinstance(pointer, str) and (pointer in ('', '/') or pointer.startswith('/')),
          'Retained mathematical verification needs an explicit JSON pointer')
    return raw if pointer in ('', '/') else _pointer(json.loads(raw), pointer)


def _verification_within(ref, pointer, allowed):
    if not isinstance(pointer, str):
        return False
    key = _ref_key(ref)
    return any(source == key and (parent in ('', '/') or pointer == parent or pointer.startswith(parent + '/'))
               for source, parent in allowed)


def _final_source(name):
    return name == 'R3' or name.startswith(('R3/', 'R3.'))


def _validate_intake(ref, packet, selected, roots):
    """Admit a named no-content correction from the existing continuation owner."""
    intake = json.loads(_read(roots, ref))
    _need(intake.get('schema') == 'math-gauge.profile-structure-source-intake/v1'
          and intake.get('version') == VERSION and intake.get('edition') == EDITION
          and intake.get('condition') == CONDITION and _boundary(intake)
          and intake.get('kind') in ('retained-continuation-no-content', 'retained-continuation-cutoff-content')
          and intake.get('model_id') == packet['model_id'] and intake.get('axis') == packet['axis']
          and intake.get('case_id') == packet['case_id'] and intake.get('stage') == packet['stage'] == 'revision'
          and intake.get('previous_source_status') == 'unavailable'
          and intake.get('source_status') == ('settled_blank' if intake.get('kind') == 'retained-continuation-no-content' else 'available')
          and _text(intake.get('reason'))
          and _ref_key(intake['source_material']) == _ref_key(packet['material_source']),
          'Invalid or foreign named no-content source intake')
    continuation = selected['revision_ref']['continuation']
    _need(continuation.get('status') == 'delivery_failed',
          'Source intake cannot turn a delivered mathematical answer into an empty failure')
    for name in ('failure_evidence', 'cutoff_review'):
        _need(name in selected['sources'] and name in continuation
              and _ref_key(intake[name]) == _ref_key(selected['sources'][name])
              and all(intake[name].get(k) == continuation[name].get(k) for k in ('path', 'sha256', 'bytes')),
              'Named no-content intake changed its existing continuation evidence')
    failure = json.loads(_read(roots, intake['failure_evidence']))
    cutoff = json.loads(_read(roots, intake['cutoff_review']))
    _need(all(value.get('model_id') == packet['model_id'] and value.get('case_id') == packet['case_id']
              for value in (failure, cutoff))
          and failure.get('status') == 'cutoff_without_final' and failure.get('normal_final_delivered') is False
          and failure.get('response_sha256') == digest(b'') and failure.get('delivered_attachments') == []
          and cutoff.get('failure_evidence_sha256') == intake['failure_evidence']['sha256']
          and cutoff.get('original_work_unmodified') is True and cutoff.get('no_normal_final') is True
          and cutoff.get('no_cross_attempt_union') is True,
          'Source intake lacks its retained cutoff and unrepaired-source verification')
    if intake['kind'] == 'retained-continuation-no-content':
        _need(cutoff.get('no_content') is True and cutoff.get('content_sha256') is None,
              'A named empty intake cannot discard retained original cutoff mathematics')
    else:
        _need('cutoff_content' in selected['sources'] and 'cutoff_content' in continuation
              and _ref_key(intake['cutoff_content']) == _ref_key(selected['sources']['cutoff_content'])
              and all(intake['cutoff_content'].get(k) == continuation['cutoff_content'].get(k) for k in ('path', 'sha256', 'bytes'))
              and cutoff.get('no_content') is False and cutoff.get('content_sha256') == intake['cutoff_content']['sha256']
              and bool(_read(roots, intake['cutoff_content']).strip()),
              'Cutoff intake must use the exact original content already admitted by the selected source owner')
    return intake


MATH_VERIFICATION_ROLES = {'original_mathematical_review', 'original_validation', 'original_claim_review',
                           'original_review_sha256', 'root_adjudication_sha256',
                           'complete_source_review', 'source_review_note'}


def _continuation_ref_keys(value, repository):
    result = set()
    if isinstance(value, dict):
        if {'path', 'sha256'} <= set(value):
            result.add((value.get('repository', repository), value['path'], value['sha256']))
        for item in value.values():
            result.update(_continuation_ref_keys(item, repository))
    elif isinstance(value, list):
        for item in value:
            result.update(_continuation_ref_keys(item, repository))
    return result


def _validate_verification_supplement(ref, packet, selected, roots, contracts):
    """Permit only mathematical files named by both this wrapper and this continuation."""
    manifest = json.loads(_read(roots, ref))
    _need(manifest.get('schema') == 'math-gauge.profile-structure-verification-supplements/v1'
          and manifest.get('version') == VERSION and manifest.get('edition') == EDITION
          and manifest.get('condition') == CONDITION and _boundary(manifest) and packet['stage'] == 'revision',
          'Invalid retained mathematical verification supplement')
    key = _key(packet, contracts)
    rows = [row for row in manifest.get('rows', []) if row.get('model_id') == packet['model_id'] and _key(row, contracts) == key]
    _need(len(rows) == 1, 'Verification supplement must select this model, task and actual continuation exactly once')
    row = rows[0]
    _need(_ref_key(row['source_material']) == _ref_key(packet['material_source'])
          and 'review' in selected['sources'] and _ref_key(row['wrapper']) == _ref_key(selected['sources']['review']),
          'Verification supplement substituted the selected continuation or thin review wrapper')
    wrapper = json.loads(_read(roots, row['wrapper']))
    admitted = _continuation_ref_keys(selected['revision_ref']['continuation'].get('sources', {}),
                                      packet['material_source']['repository'])
    verification = row.get('verification', [])
    _need(verification and len({(_ref_key(f['source']), f.get('pointer', '/')) for f in verification}) == len(verification),
          'Verification supplement has empty or duplicated mathematical facts')
    facts = []
    for fact in verification:
        role = fact.get('role')
        _need(role in MATH_VERIFICATION_ROLES and role in wrapper,
              'Old trait grades, hidden reasoning or unrelated files are not mathematical verification')
        declared = wrapper[role]
        expected_hash = declared.get('sha256') if isinstance(declared, dict) else declared
        source = fact['source']
        _need(_hash(expected_hash) and source.get('sha256') == expected_hash and _ref_key(source) in admitted,
              'Mathematical supplement is not explicitly hash-bound by its wrapper and original continuation sources')
        pointer = fact.get('pointer', '/')
        _verification_pointer(_read(roots, source), pointer)
        facts.append(dict(source=deepcopy(source), pointer=pointer))
    return facts


def _indexed_owner_references(roots, model_id):
    """Read each selected per-model entry; never bind a moving whole index hash."""
    paths = dict(first='results/mathematical-profiles/v0.4.0/index.json',
                 revision='results/mathematical-profile-revisions/v0.1.0/index.json',
                 initiative='results/research-initiative/v0.1.0/index.json',
                 open_research='results/open-research/v0.1.0/index.json')
    selected = {}
    for name, filename in paths.items():
        index = json.loads(read_bytes(Path(roots['private']) / filename))
        entry = index['models'].get(model_id)
        _need(entry is not None or name == 'revision', 'A retained model lacks its indexed source owner: ' + name)
        selected[name] = dict(repository='private', **entry['source-bindings']) if entry else None
    return selected


def _validate_owner_bindings(stage, bindings, selected):
    """A same-model lookalike JSON file is not an indexed source-owner receipt."""
    source_owner = 'initiative' if stage == 'independent' else stage
    expected = selected.get(source_owner)
    _need(expected is not None and _ref_key(bindings.get('material_source', {})) == _ref_key(expected),
          'Structural material is not the indexed selected ' + source_owner + ' source')
    for field, owner in (('initiative_material_source', 'initiative'), ('open_material_source', 'open_research')):
        _need(stage != 'first' or field in bindings, 'Original profile materials cannot omit a selected source-owner supplement')
        if field in bindings:
            _need(_ref_key(bindings[field]) == _ref_key(selected[owner]),
                  'Structural material substituted a same-model ' + owner + ' source-owner supplement')


def _select_current_open_owner(packet, selected, roots):
    """Upgrade a known pre-adoption packet only when indexed first sources are identical.

    Older preparation named the preserved first-only manuscript owner directly.
    Current adopted-neutral owners retain exactly that first array. This is a
    selection during preparation, never an acceptance bypass for persisted data.
    """
    if packet['stage'] != 'first' or _ref_key(packet.get('open_material_source', {})) == _ref_key(selected['open_research']):
        return packet
    mid = packet['model_id']
    name = 'results/open-research/v0.1.0/' + mid + '/source-bindings.json'
    raw = read_bytes(Path(roots['private']) / name)
    legacy_ref = dict(repository='private', path=name, bytes=len(raw), sha256=digest(raw))
    _need(_ref_key(packet.get('open_material_source', {})) == _ref_key(legacy_ref),
          'Preparation cannot replace an indexed owner with a same-model lookalike')
    old, current = json.loads(raw), json.loads(_read(roots, selected['open_research']))
    _need(old.get('model_id') == current.get('model_id') == mid
          and old.get('condition') == current.get('condition') == CONDITION
          and old['first'] == current['first']
          and old['sources']['base_materials'] == current['sources']['base_materials'],
          'Indexed manuscript owner changed original first-answer evidence')
    result = deepcopy(packet)
    result['open_material_source'] = deepcopy(selected['open_research'])
    return result


def _private_ref(original, roots):
    """Resolve a selected private path without borrowing an unrelated workspace."""
    name = original.get('path') if isinstance(original, dict) else original
    path = Path(name)
    _need(path.is_absolute(), 'Selected independent verification needs its exact absolute source identity')
    try:
        relative = path.relative_to(roots['private']).as_posix()
    except ValueError as error:
        raise ValueError('Independent verification is outside the selected private repository') from error
    raw = read_bytes(path)
    ref = dict(repository='private', path=relative, bytes=len(raw), sha256=digest(raw))
    if isinstance(original, dict):
        _need(all(ref[k] == original.get(k) for k in ('bytes', 'sha256')),
              'Independent verification differs from its selected original descriptor')
    return ref


def _admitted_independent(ref, packet, roots):
    """Replay the separate, explicit source owner; never relax a normal-final owner."""
    from . import independent_research_admitted_delivery as admitted
    intake = json.loads(_read(roots, ref))
    _need(intake.get('schema') == 'math-gauge.profile-structure-independent-addition/v1'
          and intake.get('version') == VERSION and intake.get('edition') == EDITION
          and intake.get('condition') == CONDITION and _boundary(intake)
          and intake.get('model_id') == packet['model_id'] == admitted.MODEL
          and intake.get('axis') == packet['axis'] == 'open_research'
          and intake.get('stage') == packet['stage'] == 'independent'
          and intake.get('case_id') in ('independent-research', 'MG-MT001')
          and intake.get('kind') == admitted.SOURCE_KIND
          and intake.get('source_status') == 'available'
          and intake.get('classification') == admitted.SOURCE_KIND and _text(intake.get('reason')),
          'Invalid or foreign independent-delivery profile addition')
    selection_ref, public_ref = intake['selection'], intake['public_adoption']
    selection_raw = _read(roots, selection_ref)
    selected = json.loads(selection_raw)
    _need(selected.get('schema') == admitted.FROZEN_SELECTION,
          'Independent profile addition requires its source-bound frozen-runner selection')
    _need(selection_ref['repository'] == 'private' and public_ref['repository'] == 'public'
          and public_ref['path'] == admitted.PUBLIC_PATH.as_posix(),
          'Independent profile addition must select its separate admitted-delivery owner')
    selection_path = Path(roots['private']) / selection_ref['path']
    projected = admitted.prepare(selection_path, roots['public'])
    _need(encoded(projected) == _read(roots, public_ref)
          and projected['source_binding']['adoption_sha256'] == digest(selection_raw)
          and projected['models'][admitted.MODEL]['source_sha256'] == intake['adopted_source_sha256'],
          'Independent profile addition differs from its adopted original source')
    _, _, registered = admitted.retained_case_reader(
        Path(selected['registration']['path']), Path(selected['frozen_runner']['path']), roots['public'])
    evidence = admitted.load_admission(Path(selected['admission']['path']), selected['registration']['sha256'],
                                       round_prompts=registered['rounds'])
    sources, actual_aliases, hashes = {}, {}, set()
    for row in evidence.original['rounds']:
        for index, document in enumerate(row['documents']):
            name = row['round'] if index == 0 else row['round'] + '.files/' + Path(document['source']['path']).name
            retained = evidence.archive.descriptor(document['source'])
            source = _private_ref(evidence.archive.root / retained['path'], roots)
            actual_aliases[name] = source
            if source['sha256'] not in hashes:
                sources[name] = source
                hashes.add(source['sha256'])
    _need(intake['sources'] == actual_aliases,
          'Independent profile addition omitted or substituted an admitted delivered document')
    return intake, sources


def _selected_independent_review(packet, roots):
    """Name factual reviews through the already selected trajectory, not an old grade."""
    selection = json.loads(_read(roots, packet['selection']))
    schema, mid = selection.get('schema'), packet['model_id']
    if schema == 'math-gauge.independent-research-admitted-selection/v2':
        return 'admitted_review', _private_ref(selection['review'], roots)
    selected = next((row for row in selection.get('models', []) if row.get('id') == mid), None)
    _need(selected is not None, 'Independent mathematical verification belongs to another configuration')
    if schema == 'math-gauge.independent-research-score-modes-selection/v1':
        original = selected['effective_review']
        old_root, name = PurePosixPath(selection['run_root']), PurePosixPath(original['path'])
        _need(name.as_posix() == original['path'] and '..' not in name.parts,
              'Noncanonical original independent mathematical review')
        replay = Path(roots['private']) / 'research-previews/v1.3.0/evidence/gpt-20261123/replay'
        if name.is_absolute():
            _need(name.is_relative_to(old_root), 'Independent review is outside its archived original run')
            path = replay / name.relative_to(old_root)
        else:
            path = Path(roots['private']) / Path(packet['selection']['path']).parent / name
        return 'effective_review', _private_ref(dict(original, path=str(path)), roots)
    _need(schema in ('math-gauge.independent-research-external-selection/v1',
                     'math-gauge.independent-research-native-selection/v1'),
          'Unknown independent mathematical source owner')
    if schema == 'math-gauge.independent-research-external-selection/v1' and selection.get('review_amendment'):
        amendment = json.loads(_read(roots, _private_ref(selection['review_amendment'], roots)))
        if amendment['model_id'] == mid:
            _need(_private_ref(selected['review'], roots) == _private_ref(amendment['after_review'], roots),
                  'Independent amended review is not the actually selected amended source')
            return 'amended_review', _private_ref(amendment['after_review'], roots)
    return 'review', _private_ref(selected['review'], roots)


def _independent_verifications(ref, packet, roots, contracts):
    manifest = json.loads(_read(roots, ref))
    _need(manifest.get('schema') == 'math-gauge.profile-structure-independent-verifications/v1'
          and manifest.get('version') == VERSION and manifest.get('edition') == EDITION
          and manifest.get('condition') == CONDITION and _boundary(manifest)
          and packet['stage'] == 'independent', 'Invalid independent mathematical verification manifest')
    rows = [r for r in manifest.get('rows', []) if r.get('model_id') == packet['model_id']
            and _key(r, contracts) == _key(packet, contracts)]
    _need(len(rows) == 1, 'Independent verification needs exactly this selected source opportunity')
    row = rows[0]
    _need(_ref_key(row['source_material']) == _ref_key(packet['material_source'])
          and row['selection'] == packet['selection'],
          'Independent verification changed its indexed original trajectory')
    role, selected = _selected_independent_review(packet, roots)
    allowed = ('/error_roots', '/axes/capacity', '/round_reviews/capacity/R3',
               '/round_diagnostics/R3', '/capacity/directions', '/capacity/deductions')
    facts = row.get('verification', [])
    _need(row.get('role') == role and facts
          and len({(_ref_key(f['source']), f.get('pointer')) for f in facts}) == len(facts),
          'Independent mathematical verification lost its selected reviewer role')
    result = []
    for fact in facts:
        pointer = fact.get('pointer')
        _need(_ref_key(fact['source']) == _ref_key(selected) and pointer in allowed,
              'Independent facts must name the selected original mathematical review subtree')
        _verification_pointer(_read(roots, fact['source']), pointer)
        result.append(dict(source=deepcopy(fact['source']), pointer=pointer))
    return result


def _authenticated_sources(packet, roots, contracts):
    """Resolve only already-selected source owners; never inspect a loose workspace."""
    cid, stage, mid = _case(packet['case_id'], contracts), packet['stage'], packet['model_id']
    if packet.get('contract_source'):
        frozen = json.loads(_read(roots, contracts['design_sources']['depth-opportunities.json']))
        _need(_ref_key(packet['contract_source']) == _ref_key(frozen['source_binding']['contracts']),
              'Structural source packet changed the frozen original task contracts')
    base = json.loads(_read(roots, packet['material_source']))
    _need(base.get('model_id') == mid and base.get('condition') == CONDITION,
          'A profile packet borrowed another model or attempt condition')
    allowed, facts, frozen_status = {}, set(), None
    if stage == 'independent':
        selected = next(r for r in base['rows'] if r['opportunity_id'] == 'independent-extension')
        if packet.get('independent_addition'):
            _need(selected['source_status'] == 'unavailable',
                  'A named independent addition cannot replace an already available trajectory')
            intake, actual = _admitted_independent(packet['independent_addition'], packet, roots)
            allowed.update(actual)
            frozen_status = 'available'
            _need(packet.get('selection') == intake['selection']
                  and packet.get('adopted_source_sha256') == intake['adopted_source_sha256']
                  and packet.get('classification') == intake['classification'],
                  'Independent profile addition changed its selected native source')
        else:
            allowed.update(selected['sources'])
            frozen_status = selected['source_status']
            _need(packet.get('selection') == selected.get('selection')
                  and packet.get('adopted_source_sha256') == selected.get('adopted_source_sha256')
                  and packet.get('classification') == selected.get('classification'),
                  'Independent profile source is not its selected retained trajectory')
        if packet.get('independent_verification'):
            supplemental = _independent_verifications(packet['independent_verification'], packet, roots, contracts)
            facts.update((_ref_key(item['source']), item['pointer']) for item in supplemental)
    elif stage == 'revision':
        selected = next(r for r in base['tasks'] if r['case_id'] == cid)
        allowed.update({k: v for k, v in selected['sources'].items()
                        if k in ('answer', 'task') or k.startswith('attachment:')})
        _need(packet.get('parent_response_sha256') == selected['revision_ref']['first_response_sha256'],
              'Continuation profile source changed its original parent answer')
        if selected['sources'].get('review'):
            facts.add((_ref_key(selected['sources']['review']), '/'))
        if selected['sources'].get('cutoff_review'):
            facts.add((_ref_key(selected['sources']['cutoff_review']), '/mathematical_review'))
    else:
        selected = next(r for r in base['tasks'] if r['id'] == cid + ':A1')
        if selected.get('raw_answer'):
            allowed['answer'] = selected['raw_answer']
        for field, index_key in (('content_review', 'content_index'), ('goal_review', 'goal_index')):
            if field in base['sources'] and index_key in selected:
                facts.add((_ref_key(base['sources'][field]), '/tasks/' + str(selected[index_key])))
        if packet.get('initiative_material_source'):
            initiative = json.loads(_read(roots, packet['initiative_material_source']))
            _need(initiative['model_id'] == mid and initiative['condition'] == CONDITION,
                  'Initiative supplement belongs to another profile source')
            chosen = next((r for r in initiative['rows'] if r['opportunity_id'] == cid), None)
            if chosen:
                allowed.update(chosen['sources'])
                frozen_status = chosen['source_status']
        if packet.get('open_material_source'):
            manuscript = json.loads(_read(roots, packet['open_material_source']))
            _need(manuscript['model_id'] == mid and manuscript['condition'] == CONDITION,
                  'Manuscript supplement belongs to another profile source')
            chosen = next((r for r in manuscript['first'] if r['case_id'] == cid), None)
            if chosen:
                allowed.update({k: v for k, v in chosen['sources'].items()
                                if k.startswith(('answer:', 'manuscript:', 'nonfinal_work:'))})
    intake = None
    if packet.get('intake_correction'):
        _need(stage == 'revision', 'A continuation intake cannot change an original or independent source')
        intake = _validate_intake(packet['intake_correction'], packet, selected, roots)
        if intake['kind'] == 'retained-continuation-cutoff-content':
            allowed['cutoff_content'] = intake['cutoff_content']
    if packet.get('verification_supplement'):
        supplemental = _validate_verification_supplement(packet['verification_supplement'], packet, selected, roots, contracts)
        facts.update((_ref_key(item['source']), item['pointer']) for item in supplemental)
    expected, hashes = {}, set()
    for name, ref in allowed.items():
        if ref['sha256'] not in hashes:
            expected[name] = ref
            hashes.add(ref['sha256'])
    _need(set(packet['sources']) == set(expected), 'Profile packet omitted or renamed an original delivered source')
    sources = {}
    for name, value in packet['sources'].items():
        ref = value['source']
        _need(_ref_key(ref) == _ref_key(expected[name]), 'A profile packet added an unselected answer or companion')
        raw = _read(roots, ref)
        _need(raw.decode('utf-8') == value['text'], 'Prepared packet text differs from its retained source bytes')
        sources[name] = deepcopy(ref)
    if frozen_status is None:
        frozen_status = 'available' if any(_read(roots, ref) for name, ref in sources.items() if name != 'task') else 'unavailable'
    if intake is not None:
        frozen_status = intake['source_status']
    if 'source_status' in packet:
        _need(packet['source_status'] == frozen_status, 'Profile source status differs from its retained source owner')
    verification = []
    for fact in packet.get('verified_math_facts', []):
        ref = fact['source']
        pointer = fact.get('pointer', '/')
        _need(_verification_within(ref, pointer, facts), 'Retained mathematical facts are not this task selected original verification')
        _verification_pointer(_read(roots, ref), pointer)
        verification.append(dict(source=deepcopy(ref), pointer=pointer))
    return sources, verification


def prepare_materials(public_root, private_root, packet_index, policy, policy_hash, contracts):
    """Remove temporary packet text/paths, authenticate and retain persistent references."""
    roots = dict(public=Path(public_root), private=Path(private_root))
    index = json.loads(read_bytes(packet_index))
    _need(index.get('schema') == 'math-gauge.profile-structure-review-packets/v1'
          and index.get('cohort') == contracts['cohort'], 'Reviewer packets use a different selected model cohort')
    result = {mid: dict(schema='math-gauge.profile-structure-materials/v1', version=VERSION,
        edition=EDITION, condition=CONDITION, model_id=mid, policy_sha256=policy_hash,
        private_contract_sha256=policy['private_contract_sha256'], rows=[], new_candidate_calls=0)
        for mid in contracts['cohort']}
    known = _known_cases(contracts)
    source_owners = {mid: _indexed_owner_references(roots, mid) for mid in contracts['cohort']}
    seen = set()
    for paths in index['groups'].values():
        for packet_path in paths:
            packet = json.loads(read_bytes(packet_path))
            mid, axis = packet['model_id'], packet['axis']
            key = _key(packet, contracts)
            _need(packet.get('schema') == 'math-gauge.profile-structure-review-packet/v1'
                  and mid in result and axis in AXES and key[1] in known[axis]
                  and key[2] in ('first', 'revision', 'independent') and (mid, *key) not in seen,
                  'Packet contains a missing, duplicate or foreign assessment slot')
            _need((key[2] == 'independent') == (key[1] == independent_case(contracts)),
                  'The independent research opportunity cannot become an A1 or extra round')
            seen.add((mid, *key))
            packet = _select_current_open_owner(packet, source_owners[mid], roots)
            _validate_owner_bindings(key[2], packet, source_owners[mid])
            sources, facts = _authenticated_sources(packet, roots, contracts)
            bindings = {name: deepcopy(packet[name]) for name in ('material_source', 'initiative_material_source',
                'open_material_source', 'contract_source', 'task_source', 'selection',
                'independent_addition', 'independent_verification') if packet.get(name)}
            for ref in bindings.values():
                _read(roots, ref)
            if packet.get('task_source') and 'task' in packet:
                _need(_read(roots, packet['task_source']).decode('utf-8') == packet['task'],
                      'Review packet changed the original mathematical task')
            row = dict(axis=axis, case_id=key[1], stage=key[2], source_status=packet['source_status'],
                classification=packet.get('classification'), sources=sources, bindings=bindings,
                verified_math_facts=facts)
            if packet.get('adopted_source_sha256'):
                row['adopted_source_sha256'] = packet['adopted_source_sha256']
            if packet.get('parent_response_sha256'):
                row['parent_response_sha256'] = packet['parent_response_sha256']
            row['evidence_source_ids'] = [name for name in sources if name != 'task'
                and (key[2] != 'independent' or _final_source(name))]
            if key[2] == 'independent' and row['source_status'] == 'available':
                _need(row['evidence_source_ids'], 'Independent research packet lacks the final prescribed delivery')
            result[mid]['rows'].append(row)
    for mid, materials in result.items():
        expected = {(axis, cid, 'first') for axis in AXES for cid in known[axis]
                    if cid != independent_case(contracts)}
        expected.add(('open_research', independent_case(contracts), 'independent'))
        actual = {_key(row, contracts) for row in materials['rows']}
        _need(expected <= actual, 'Structural profile is missing a fixed original opportunity')
        materials['rows'].sort(key=lambda row: _key(row, contracts))
        materials['revision_available'] = any(row['stage'] == 'revision' for row in materials['rows'])
    return result


def apply_intake_corrections(materials, correction_refs, *, public_root, private_root, policy, policy_hash, contracts):
    """Return a named source amendment; every other model retains identical bytes."""
    result = deepcopy(materials)
    roots = dict(public=Path(public_root), private=Path(private_root))
    changed = set()
    for ref in correction_refs:
        intake = json.loads(_read(roots, ref))
        mid = intake.get('model_id')
        _need(mid in result, 'Named source intake references an unselected model')
        key = _key(intake, contracts)
        matches = [row for row in result[mid]['rows'] if _key(row, contracts) == key]
        _need(len(matches) == 1, 'Named source intake references a missing or duplicate assessment slot')
        row = matches[0]
        previous = row['bindings'].get('intake_correction')
        _need(row['source_status'] == 'unavailable' and previous is None
              or row['source_status'] == intake['source_status'] and previous == ref,
              'Source intake cannot overwrite a different accepted source decision')
        row['bindings']['intake_correction'] = deepcopy(ref)
        row['source_status'] = intake['source_status']
        if intake['kind'] == 'retained-continuation-cutoff-content':
            row['sources']['cutoff_content'] = deepcopy(intake['cutoff_content'])
            if 'cutoff_content' not in row['evidence_source_ids']:
                row['evidence_source_ids'].append('cutoff_content')
            fact = dict(source=deepcopy(intake['cutoff_review']), pointer='/mathematical_review')
            if fact not in row['verified_math_facts']:
                row['verified_math_facts'].append(fact)
        changed.add(mid)
    for mid in changed:
        validate_materials(result[mid], policy, policy_hash, contracts, roots)
    return result


def apply_verification_supplements(materials, supplement_ref, *, public_root, private_root, policy, policy_hash, contracts):
    """Append source-bound verification without changing any candidate input or answer."""
    result = deepcopy(materials)
    roots = dict(public=Path(public_root), private=Path(private_root))
    manifest = json.loads(_read(roots, supplement_ref))
    _need(manifest.get('schema') == 'math-gauge.profile-structure-verification-supplements/v1'
          and manifest.get('version') == VERSION and manifest.get('edition') == EDITION
          and manifest.get('condition') == CONDITION and _boundary(manifest) and manifest.get('rows'),
          'Invalid retained mathematical verification supplement manifest')
    keys = [(row.get('model_id'), *_key(row, contracts)) for row in manifest['rows']]
    _need(len(keys) == len(set(keys)), 'Verification supplement contains duplicate assessment source slots')
    changed = set()
    for supplement in manifest.get('rows', []):
        mid = supplement.get('model_id')
        _need(mid in result, 'Verification supplement references an unselected model')
        key = _key(supplement, contracts)
        matches = [row for row in result[mid]['rows'] if _key(row, contracts) == key]
        _need(len(matches) == 1, 'Verification supplement references a missing assessment source slot')
        row = matches[0]
        previous = row['bindings'].get('verification_supplement')
        _need(previous is None or previous == supplement_ref, 'A different verification supplement needs a named amendment')
        base = json.loads(_read(roots, row['bindings']['material_source']))
        selected = next(r for r in base['tasks'] if r['case_id'] == row['case_id'])
        packet = dict(model_id=mid, axis=row['axis'], case_id=row['case_id'], stage=row['stage'], **row['bindings'])
        facts = _validate_verification_supplement(supplement_ref, packet, selected, roots, contracts)
        row['bindings']['verification_supplement'] = deepcopy(supplement_ref)
        for fact in facts:
            if fact not in row['verified_math_facts']:
                row['verified_math_facts'].append(fact)
        changed.add(mid)
    for mid in changed:
        validate_materials(result[mid], policy, policy_hash, contracts, roots)
    return result


def apply_independent_supplements(materials, *, addition_refs=(), verification_refs=(),
                                  public_root, private_root, policy, policy_hash, contracts):
    """Append named final-source decisions and factual audits without changing old owners."""
    result = deepcopy(materials)
    roots = dict(public=Path(public_root), private=Path(private_root))
    changed = set()

    def target(mid):
        _need(mid in result, 'Independent supplement references an unselected configuration')
        rows = [r for r in result[mid]['rows'] if r['stage'] == 'independent']
        _need(len(rows) == 1, 'Independent supplement lost its one prescribed opportunity')
        return rows[0]

    for ref in addition_refs:
        intake = json.loads(_read(roots, ref))
        mid = intake.get('model_id')
        row = target(mid)
        _need(row['source_status'] == 'unavailable' and not row['bindings'].get('independent_addition'),
              'Independent addition cannot replace an already selected available trajectory')
        row['bindings'].update(independent_addition=deepcopy(ref), selection=deepcopy(intake['selection']))
        row.update(source_status='available', classification=intake['classification'],
                   adopted_source_sha256=intake['adopted_source_sha256'])
        row['sources'], hashes = {}, set()
        for name, source in intake['sources'].items():
            if source['sha256'] not in hashes:
                row['sources'][name] = deepcopy(source)
                hashes.add(source['sha256'])
        row['evidence_source_ids'] = [name for name in row['sources'] if _final_source(name)]
        changed.add(mid)
    for ref in verification_refs:
        manifest = json.loads(_read(roots, ref))
        keys = [(r.get('model_id'), *_key(r, contracts)) for r in manifest.get('rows', [])]
        _need(keys and len(keys) == len(set(keys)), 'Independent verification has empty or duplicate source slots')
        for supplement in manifest['rows']:
            mid = supplement.get('model_id')
            row = target(mid)
            _need(_key(row, contracts) == _key(supplement, contracts),
                  'Independent verification selected a different mathematical source slot')
            previous = row['bindings'].get('independent_verification')
            _need(previous is None or previous == ref, 'Different independent facts need a named amendment')
            packet = dict(model_id=mid, axis=row['axis'], case_id=row['case_id'], stage='independent', **row['bindings'])
            facts = _independent_verifications(ref, packet, roots, contracts)
            row['bindings']['independent_verification'] = deepcopy(ref)
            for fact in facts:
                if fact not in row['verified_math_facts']:
                    row['verified_math_facts'].append(fact)
            changed.add(mid)
    for mid in changed:
        validate_materials(result[mid], policy, policy_hash, contracts, roots)
    return result


def _quote(quote, material, roots):
    name = quote.get('source_id')
    _need(name in material['evidence_source_ids'] and _text(quote.get('quote')),
          'Profile evidence borrowed an unselected source, task text or earlier manuscript')
    raw = _read(roots, material['sources'][name])
    needle = quote['quote'].encode('utf-8')
    if 'start' in quote or 'end' in quote:
        start, end = quote.get('start'), quote.get('end')
        _need(type(start) is int and type(end) is int and 0 <= start < end <= len(raw)
              and raw[start:end] == needle, 'Profile quote differs from exact UTF-8 source byte range')
    else:
        _need(needle in raw, 'Profile quote is absent from the selected original bytes')


def validate_judgment(row, material, contracts, roots):
    axis, cid, stage = _key(row, contracts)
    _need((axis, cid, stage) == _key(material, contracts), 'Profile judgment changed its selected opportunity or stage')
    grade, status = row.get('grade'), row.get('status')
    _need((grade is None or type(grade) is int and 0 <= grade <= 4) and status in STATUSES,
          'Profile grade must be an integer 0–4 or genuine unknown')
    _need(_text(row.get('reason')) and isinstance(row.get('evidence'), list),
          'Profile judgment needs its independent reason and exact source evidence')
    if material['source_status'] == 'unavailable':
        _need(grade is None and status in ('unrun', 'source_unresolved'), 'Unavailable profile evidence must remain unknown')
        return
    if material['source_status'] == 'settled_blank':
        _need(grade == 0 and status == 'settled_blank' and not row['evidence'],
              'Settled blank profile work is known zero without invented quotations')
        return
    if grade is None:
        _need(status in ('source_unresolved', 'review_pending'), 'An unadjudicated trait cannot be marked reviewed')
        for quote in row['evidence']:
            _quote(quote, material, roots)
        return
    _need(status == 'reviewed' and type(row.get('full_delivery_read')) is bool
          and row.get('review_scope') in ('full-delivery', 'trait-and-dependency-from-original-source',
                                         'trait-and-dependency-with-retained-math-verification'),
          'A nonempty profile assessment must preserve its actual review scope')
    _need(row['review_scope'] != 'full-delivery' or row['full_delivery_read'] is True,
          'A partial source read cannot be labeled a full-delivery audit')
    reuse = row.get('reused_verification', [])
    allowed = {(_ref_key(v['source']), v['pointer']) for v in material['verified_math_facts']}
    _need(isinstance(reuse, list), 'Retained mathematical verification must use explicit source references')
    for fact in reuse:
        _need(_verification_within(fact['source'], fact.get('pointer', '/'), allowed),
              'Reused mathematical verification differs from this selected source')
        _verification_pointer(_read(roots, fact['source']), fact.get('pointer', '/'))
    facets = row.get('facets', {})
    _need(set(facets) == set(FACETS[axis]) and all(v.get('state') in FACET_STATES
          and _text(v.get('reason')) for v in facets.values()), 'Profile facets need independent states and reasons')
    _need(type(row.get('core_scope_failure')) is bool and _text(row.get('next_tier_reason'))
          and row['evidence'], 'Profile review needs explicit scope failure, next-tier reason and original quotations')
    for quote in row['evidence']:
        _quote(quote, material, roots)
    deletions = row.get('optional_error_deletion', [])
    _need(isinstance(deletions, list), 'Optional error deletion requires an explicit itemized dependency check')
    for deletion in deletions:
        _need(_text(deletion.get('reason')) and all(deletion.get(k) is True for k in
              ('core_unchanged', 'dependencies_unchanged', 'scope_unchanged', 'no_source_repair')),
              'An optional error cannot be deleted by changing the core, dependencies, scope or source')
        _quote(dict(source_id=deletion.get('source_id'), quote=deletion.get('error_quote')), material, roots)
    if axis == 'depth' and grade >= 2:
        _need(facets['mechanism']['state'] == 'established', 'Depth grade2+ requires an established substantive mechanism')
    if grade >= 3:
        if axis == 'depth':
            _need(all(facets[k]['state'] == 'established' for k in ('mechanism', 'bridge', 'conditions')),
                  'Depth grade3+ requires its mechanism, bridge and verified conditions')
            _need(not row['core_scope_failure'] or grade == 3 and _text(row.get('independent_local_structure')),
                  'Failed depth core needs a separate established local structure and cannot earn grade4')
        else:
            _need(not row['core_scope_failure'] and all(v['state'] in ('established', 'local_gap') for v in facets.values()),
                  'Open-research grade3+ cannot retain a failed required core or essential scope gap')
            if grade == 3:
                _need(_text(row.get('g3_gap_witness')), 'Open-research grade3 needs its finite local-gap witness')
    if grade == 4:
        _need(not row['core_scope_failure'] and all(v['state'] == 'established' for v in facets.values())
              and _text(row.get('g4_closure_chain')), 'Profile grade4 requires its established complete structural chain')


def validate_review(review, materials, policy, policy_hash, contracts, roots):
    _need(review.get('schema') == 'math-gauge.profile-structure-review/v1'
          and review.get('version') == VERSION and review.get('edition') == EDITION
          and review.get('model_id') == materials['model_id'] and review.get('condition') == CONDITION
          and review.get('policy_sha256') == policy_hash
          and review.get('materials_sha256') == digest(encoded(materials)) and _boundary(review),
          'Structural review changed its source, policy, model or approval boundary')
    expected = {_key(r, contracts): r for r in materials['rows']}
    rows = review.get('rows', [])
    _need(len(rows) == len(expected) and {_key(r, contracts) for r in rows} == set(expected),
          'Structural review must retain each fixed source slot exactly once')
    proposals = {}
    for row in rows:
        _need(row.get('model_id') == materials['model_id'], 'Structural review borrowed another model judgment')
        primary = row.get('primary_review', {})
        ref = primary.get('source', {})
        key = _ref_key(ref)
        if key not in proposals:
            proposals[key] = json.loads(_read(roots, ref))
        proposal = proposals[key]
        attribution = proposal.get('reviewer', {})
        _need(proposal.get('schema') == 'math-gauge.profile-structure-review-proposal/v1'
              and proposal.get('reviewer_kind') == 'ai' and proposal.get('human_review') == 'pending'
              and attribution.get('requested_model') == 'gpt-6.1-sol' and attribution.get('effort') == 'max'
              and _text(attribution.get('context')) and type(primary.get('row')) is int
              and 0 <= primary['row'] < len(proposal.get('rows', [])),
              'Structural profile lost its actual source-bound primary reviewer')
        original = proposal['rows'][primary['row']]
        _need(original.get('model_id') == row['model_id'] and _key(original, contracts) == _key(row, contracts),
              'Structural profile primary row belongs to another model, task or stage')
        if original.get('grade') != row.get('grade'):
            correction = row.get('coordinator_adjustment', {})
            _need(correction.get('reviewer_kind') == 'ai' and correction.get('human_review') == 'pending'
                  and _text(correction.get('reason')), 'A changed primary grade needs its named coordinator adjustment')
        validate_judgment(row, expected[_key(row, contracts)], contracts, roots)
    return review


def validate_materials(materials, policy, policy_hash, contracts, roots):
    """Replay persistent references at acceptance; temporary packets grant no authority."""
    _need(materials.get('schema') == 'math-gauge.profile-structure-materials/v1'
          and materials.get('version') == VERSION and materials.get('edition') == EDITION
          and materials.get('condition') == CONDITION and materials.get('model_id') in contracts['cohort']
          and materials.get('policy_sha256') == policy_hash
          and materials.get('private_contract_sha256') == policy['private_contract_sha256']
          and type(materials.get('new_candidate_calls')) is int and materials['new_candidate_calls'] == 0,
          'Structural profile materials changed their source identity')
    known = _known_cases(contracts)
    expected = {(axis, cid, 'first') for axis in AXES for cid in known[axis]
                if cid != independent_case(contracts)}
    expected.add(('open_research', independent_case(contracts), 'independent'))
    rows = materials.get('rows', [])
    keys = [_key(row, contracts) for row in rows]
    _need(len(keys) == len(set(keys)) and expected <= set(keys)
          and all(axis in known and cid in known[axis] and stage in ('first', 'revision', 'independent')
                  for axis, cid, stage in keys), 'Persistent profile materials changed their fixed source slots')
    private = Path(roots['private'])
    owner_references = _indexed_owner_references(roots, materials['model_id'])
    selected_revision = None
    for stage in ('first', 'revision'):
        ref = owner_references[stage]
        chosen = [row for row in rows if row['stage'] == stage]
        if stage == 'first':
            _need(ref is not None and all(_ref_key(row['bindings']['material_source']) == _ref_key(ref) for row in chosen),
                  'Structural first answers are not the indexed selected original source')
        elif ref is not None:
            selected_revision = json.loads(_read(roots, ref))
            expected_revision = {r['case_id'] for r in selected_revision['tasks'] if any(r['case_id'] in ids for ids in known.values())}
            _need({r['case_id'] for r in chosen} == expected_revision
                  and all(_ref_key(row['bindings']['material_source']) == _ref_key(ref) for row in chosen),
                  'Structural material omitted or substituted an actually adopted continuation')
        else:
            _need(not chosen, 'A pending model cannot invent an adopted continuation')
    for row in rows:
        _validate_owner_bindings(row['stage'], row['bindings'], owner_references)
        packet = dict(model_id=materials['model_id'], axis=row['axis'], case_id=row['case_id'],
            stage=row['stage'], source_status=row['source_status'], classification=row.get('classification'),
            sources={name: dict(source=ref, text=_read(roots, ref).decode('utf-8'))
                                        for name, ref in row['sources'].items()},
            verified_math_facts=row['verified_math_facts'], **row['bindings'])
        for field in ('parent_response_sha256', 'adopted_source_sha256'):
            if field in row:
                packet[field] = row[field]
        sources, verification = _authenticated_sources(packet, roots, contracts)
        _need(sources == row['sources'] and verification == row['verified_math_facts'],
              'Persistent profile source or retained verification changed')
        for ref in row['bindings'].values():
            _read(roots, ref)
        allowed = [name for name in sources if name != 'task'
                   and (row['stage'] != 'independent' or _final_source(name))]
        _need(row['evidence_source_ids'] == allowed, 'Profile materials changed final-source evidence eligibility')
    _need(materials.get('revision_available') is (selected_revision is not None),
          'Profile materials changed their adopted continuation availability')
    return materials


class ProfileStructureInputs:
    """Authenticated source judgments accepted by the shared scoring owner."""
    def __init__(self, review, materials, *, public_root, private_root, policy, policy_sha256, contracts):
        actual_policy, actual_hash = load_policy(public_root)
        _need(policy == actual_policy and policy_sha256 == actual_hash,
              'Structural profile input did not use the actual selected policy bytes')
        _need(contracts == load_contracts(public_root, private_root, actual_policy),
              'Structural profile input substituted its frozen private contracts')
        _need(materials.get('schema') == 'math-gauge.profile-structure-materials/v1'
              and materials.get('policy_sha256') == policy_sha256
              and materials.get('private_contract_sha256') == policy['private_contract_sha256']
              and materials.get('edition') == EDITION and materials.get('condition') == CONDITION
              and materials.get('new_candidate_calls') == 0,
              'Structural profile materials changed their authenticated source identity')
        roots = dict(public=Path(public_root), private=Path(private_root))
        validate_materials(materials, policy, policy_sha256, contracts, roots)
        validate_review(review, materials, policy, policy_sha256, contracts, roots)
        self.review, self.materials = deepcopy(review), deepcopy(materials)
        self.policy, self.contracts = deepcopy(policy), deepcopy(contracts)
        frozen = json.loads(_read(roots, contracts['design_sources']['depth-opportunities.json']))
        original_tasks = json.loads(_read(roots, frozen['source_binding']['contracts']))['tasks']
        self.revision_eligible = {r['case_id'] for r in original_tasks
                                  if r['kind'] == 'initial' and r['subcategory'] not in ('lean-audit', 'lean-formalization')}


def _metric_valid(metric, axis):
    from math import isfinite
    fields = {'lower', 'upper', 'exact', 'confirmed', 'unknown_weight', 'coverage'}
    _need(isinstance(metric, dict) and set(metric) == fields, 'Structural metric must remain an aggregate-only interval')
    numeric = lambda value: type(value) in (int, float) and isfinite(value) and 0 <= value <= 100
    _need(all(numeric(metric[k]) for k in ('lower', 'upper', 'confirmed', 'unknown_weight'))
          and metric['lower'] <= metric['confirmed'] <= metric['upper']
          and (metric['exact'] is None or numeric(metric['exact'])
               and metric['lower'] == metric['exact'] == metric['upper'])
          and abs(metric['unknown_weight'] - (metric['upper'] - metric['lower'])) < 1e-8,
          'Structural metric changed known zero, unknown bounds or confirmed contribution')
    coverage = metric['coverage']
    expected_unit = 'depth_family' if axis == 'depth' else 'open_research_opportunity'
    _need(set(coverage) == {'unit', 'planned', 'reviewed', 'weight_planned', 'weight_reviewed'}
          and coverage['unit'] == expected_unit and coverage['planned'] == PLANNED[axis]
          and type(coverage['reviewed']) is int and 0 <= coverage['reviewed'] <= PLANNED[axis]
          and coverage['weight_planned'] == WEIGHTS[axis]
          and type(coverage['weight_reviewed']) is int and 0 <= coverage['weight_reviewed'] <= WEIGHTS[axis]
          and coverage['reviewed'] <= coverage['weight_reviewed'] <= 3 * coverage['reviewed']
          and coverage['planned'] - coverage['reviewed'] <= coverage['weight_planned'] - coverage['weight_reviewed']
              <= 3 * (coverage['planned'] - coverage['reviewed'])
          and (metric['exact'] is None) == (coverage['reviewed'] < coverage['planned'])
          and (coverage['reviewed'] == coverage['planned']) == (coverage['weight_reviewed'] == coverage['weight_planned']),
          'Structural metric must keep its fixed family/opportunity and weight coverage')
    return metric


def project_public(score, *, policy_hash, private_review_sha256, private_materials_sha256):
    return dict(schema='math-gauge.profile-structure-model/v1', version=VERSION, edition=EDITION,
        condition=CONDITION, model_id=score['model_id'], policy_sha256=policy_hash,
        private_review_sha256=private_review_sha256, private_materials_sha256=private_materials_sha256,
        first=deepcopy(score['first']), revision=deepcopy(score['revision']),
        revision_coverage=deepcopy(score['revision_coverage']),
        independent_delivery=deepcopy(score['independent_delivery']), **BOUNDARIES)


def validate_public(report, policy, policy_hash):
    fields = {'schema', 'version', 'edition', 'condition', 'model_id', 'policy_sha256',
              'private_review_sha256', 'private_materials_sha256', 'first', 'revision',
              'revision_coverage', 'independent_delivery', *BOUNDARIES}
    _need(set(report) == fields and report['schema'] == 'math-gauge.profile-structure-model/v1'
          and report['version'] == VERSION and report['edition'] == EDITION
          and report['condition'] == CONDITION and _text(report['model_id'])
          and report['policy_sha256'] == policy_hash and _boundary(report)
          and all(_hash(report[k]) for k in ('private_review_sha256', 'private_materials_sha256')),
          'Invalid aggregate-only structural profile report')
    for stage in ('first', 'revision'):
        _need(set(report[stage]) == set(AXES), 'Structural profile cannot supply or replace other axes')
        for axis in AXES:
            _metric_valid(report[stage][axis], axis)
    revisions = report['revision_coverage']
    _need(set(revisions) == {'status', 'selected', 'reviewed', 'unknown'}
          and revisions['status'] in ('adopted', 'not-adopted')
          and all(type(revisions[k]) is int and revisions[k] >= 0 for k in ('selected', 'reviewed', 'unknown'))
          and revisions['selected'] == revisions['reviewed'] + revisions['unknown']
          and revisions['selected'] <= 31,
          'Structural revision coverage must preserve selected and unresolved source slots')
    independent = report['independent_delivery']
    _need(set(independent) == {'source_status', 'classification', 'planned_rounds', 'last_round_selected'}
          and independent['source_status'] in ('available', 'settled_blank', 'unavailable')
          and independent['planned_rounds'] == 3 and type(independent['last_round_selected']) is bool
          and (independent['classification'] is None or _text(independent['classification']))
          and (independent['source_status'] != 'available' or independent['last_round_selected']),
          'Structural open-research coverage cannot invent a final manuscript or native delivery')
    return report


def load_public(root, *, benchmark_version):
    root = Path(root)
    if benchmark_version != EDITION or not (root / INDEX_PATH).is_file():
        return None
    _need((root / POLICY_PATH).is_file(), 'Adopted structural profile index is missing its selected policy')
    policy, policy_hash = load_policy(root)
    raw = read_bytes(root / INDEX_PATH)
    index = json.loads(raw)
    fields = {'schema', 'version', 'edition', 'condition', 'policy_sha256', 'cohort', 'models', *BOUNDARIES}
    _need(set(index) == fields and index['schema'] == 'math-gauge.profile-structure-index/v1'
          and index['version'] == VERSION and index['edition'] == EDITION and index['condition'] == CONDITION
          and index['policy_sha256'] == policy_hash and _boundary(index)
          and len(index['cohort']) == len(set(index['cohort'])) == 20
          and set(index['models']) == set(index['cohort']), 'Invalid structural profile index or retained cohort')
    models = []
    for mid in index['cohort']:
        report = validate_public(json.loads(source_bytes(root, index['models'][mid])), policy, policy_hash)
        _need(report['model_id'] == mid, 'Structural profile aggregate belongs to another configuration')
        models.append(dict(id=mid, **{k: deepcopy(report[k]) for k in
            ('first', 'revision', 'revision_coverage', 'independent_delivery')}))
    return dict(schema='math-gauge.profile-structure/v1', version=VERSION, benchmark_version=EDITION,
        condition=CONDITION, policy_sha256=policy_hash,
        source=dict(path=INDEX_PATH, bytes=len(raw), sha256=digest(raw)),
        axes=[dict(id=axis, **deepcopy(policy['axes'][axis])) for axis in AXES],
        planned=dict(PLANNED), weights=dict(WEIGHTS), models=models, **BOUNDARIES)
