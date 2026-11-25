"""Source-bound ordinal exploration orientation; no score aggregation or candidate calls."""
from copy import deepcopy
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
from .evidence_retention import read_bytes
VERSION = '0.1.0'
EDITION = '1.3.0'
POLICY_PATH = 'protocol/exploration-orientation.json'
PUBLIC_INDEX = 'results/exploration-orientation/v0.1.0/index.json'
PRIVATE_PREFIX = 'results/exploration-orientation/v0.1.0'
INTAKE_PREFIX = PRIVATE_PREFIX + '/source-intake'
POLICY_SHA256 = '3affe9a8ad2a7e3af36279bac65a04adec242a5453858a57f01f2e01455e4f7b'
INTAKE_SHA256 = 'fc658384d176dd30b30f2ba466972427a155c0ed3a2d21b9669bee911cf38d5a'
SUPPORT_SHA256 = '97e118db3867252f26919262a8bec681a2bb1056a43debba4906703faeac8adc'
TEMPLATE_SHA256 = '62f9e56cf521f33c7b3e41e6b79d37e19474448033527ad8256f42499a6becc5'
AXIS_IDS = ('horizontal_expansion', 'vertical_deepening', 'structural_reframing', 'boundary_probing', 'experimental_exploration')
ROUND_IDS = ('R1', 'R2', 'R3')
VERIFY_STATES = frozenset(('verified_result', 'verified_obstruction', 'substantive_attempt_unclosed', 'refuted_claim', 'invalid_operation', 'unresolved'))
EXECUTION_STATES = frozenset(('native_or_tool_receipt', 'reported_in_delivered_answer', 'checkable_manual_probe', 'execution_not_established'))
NULL_STATES = frozenset(('not_identifiable', 'missing_source', 'unsettled_source', 'incomplete_trajectory', 'unobservable_freedom', 'exposure_blocked', 'classification_unresolved', 'review_pending'))
PROMPT_STATES = frozenset(('self_chosen_within_open_invitation', 'elicited_expansion_or_deepening', 'elicited_self_audit_with_discretionary_action', 'unsolicited_beyond_legacy_required_core', 'required_or_routine', 'unresolved'))
STAGE_ROLES = frozenset(('new', 'developed', 'restructured', 'checked', 'corrected', 'retained_only', 'abandoned', 'stalled', 'unresolved'))
ROLE_GRADES = dict(incidental=1, local=2, mainline=3, central=4)
REVIEW_SCHEMA = 'math-gauge.exploration-orientation-review/v1'
MATERIAL_SCHEMA = 'math-gauge.exploration-orientation-materials/v1'
PUBLIC_SCHEMA = 'math-gauge.exploration-orientation-profile/v1'
INDEX_SCHEMA = 'math-gauge.exploration-orientation-index/v1'

def encoded(value):
    return (json.dumps(value, ensure_ascii=False, allow_nan=False, sort_keys=True, indent=2) + '\n').encode()

def digest(raw):
    return hashlib.sha256(raw).hexdigest()

def binding(raw):
    return dict(bytes=len(raw), sha256=digest(raw))

def reference(repository, path, raw):
    return dict(repository=repository, path=path, **binding(raw))

def _text(value):
    return isinstance(value, str) and bool(value.strip())

def _same_ref(a, b):
    return all((a.get(k) == b.get(k) for k in ('repository', 'path', 'bytes', 'sha256')))

def _need(condition, message):
    if not condition:
        raise ValueError(message)

def _object(raw):

    def pairs(entries):
        result = {}
        for key, value in entries:
            _need(key not in result, 'Duplicate JSON field')
            result[key] = value
        return result
    return json.loads(raw, object_pairs_hook=pairs)

def exact_source(roots, reference):
    """Read an existing hot/cold logical path without restoring it."""
    _need(isinstance(reference, dict) and reference.get('repository') in ('public', 'private'), 'Expected a public/private source owner')
    name = PurePosixPath(reference.get('path', ''))
    _need(bool(name.parts) and (not name.is_absolute()) and ('..' not in name.parts) and (name.as_posix() == reference['path']) and ('.git' not in name.parts), 'Expected a safe repository-relative source identity')
    _need(type(reference.get('bytes')) is int and reference['bytes'] >= 0 and isinstance(reference.get('sha256'), str) and (re.fullmatch('[0-9a-f]{64}', reference['sha256']) is not None), 'Need exact original source size and SHA256')
    root = Path(roots[reference['repository']]).resolve()
    path = root / reference['path']
    _need(path.resolve().is_relative_to(root), 'Source resolves outside its selected repository')
    raw = read_bytes(path)
    _need(len(raw) == reference['bytes'] and hashlib.sha256(raw).hexdigest() == reference['sha256'], 'Selected source bytes changed')
    return raw

def selected_round_sources(model, round_id):
    """Expose only actual selected delivery documents from the named round."""
    _need(round_id in ROUND_IDS, 'Need a prescribed original round')
    rows = [r for r in model.get('anchor', {}).get('rounds', []) if r.get('round') == round_id]
    _need(len(rows) == 1, 'Need one exact selected original round')
    result = {}
    for item in rows[0]['selected_documents']:
        sid = item['source_id']
        _need(isinstance(sid, str) and sid and (sid not in result), 'Duplicate or empty selected source ID')
        result[sid] = deepcopy(item['source'])
    return result

def selected_support_sources(model, case_id):
    """Expose a separately labeled A1 support slot, without a neutral revision."""
    rows = [r for r in model.get('a1_support_opportunities', []) if r.get('case_id') == case_id]
    _need(len(rows) == 1, 'Need one fixed common A1 support slot')
    return deepcopy(rows[0]['selected_documents'])

def read_exact_quote(evidence, allowed_sources, roots):
    """Resolve a verbatim UTF-8 byte quote through an explicit selected-source map.

    Callers select the round or common support slot before invoking this leaf.
    A quote cannot introduce a path, another round, a hidden thought or a loose
    file merely because those bytes happen to exist in a package.
    """
    _need(isinstance(evidence, dict) and set(evidence) == {'source_id', 'sha256', 'start', 'end', 'quote'}, 'Need an exact selected-source quote descriptor')
    sid = evidence['source_id']
    _need(isinstance(sid, str) and sid in allowed_sources, 'Quote source is not in this selected delivery')
    source = allowed_sources[sid]
    _need(evidence['sha256'] == source['sha256'], 'Quote hash differs from the selected source')
    raw = exact_source(roots, source)
    start, end, quote = (evidence['start'], evidence['end'], evidence['quote'])
    _need(type(start) is int and type(end) is int and (0 <= start < end <= len(raw)) and isinstance(quote, str) and bool(quote.strip()), 'Need a nonempty exact original byte span')
    quoted = quote.encode('utf-8')
    _need(raw[start:end] == quoted, 'Quote is not the exact selected original byte slice')
    try:
        raw.decode('utf-8')
        raw[:start].decode('utf-8')
        raw[:end].decode('utf-8')
    except UnicodeDecodeError as error:
        raise ValueError('Quote boundaries must align to original UTF-8 text') from error
    return quote

def load_policy(root):
    path = Path(root)
    path = path if path.suffix == '.json' else path / POLICY_PATH
    raw = read_bytes(path)
    policy = _object(raw)
    _need(digest(raw) == POLICY_SHA256 and policy.get('edition') == EDITION and (policy.get('version') == VERSION) and (policy.get('status') == 'frozen-before-new-orientation-coding') and (tuple(policy['publication']['axis_order']) == AXIS_IDS) and (policy['construct']['scale']['total'] is None) and (policy['main_scores_modified'] is False) and (policy['existing_ten_axes_modified'] is False), 'Need the exact frozen independent ordinal policy')
    return (policy, binding(raw))

def _verify_indexed_selection(model, roots):
    """Bind selection to actual existing owners, not a same-model lookalike file."""
    mid = model['model_id']
    owners = model['indexed_material_owners']
    if mid == 'dot-20261125':
        public_path = 'results/dot-native-profiles/v0.1.0/dot-20261125/index.json'
        index = _object(read_bytes(Path(roots['public']) / public_path))
        admission = _object(exact_source(roots, model['selected_source_admission']))
        _need(admission['source_admission'] == index['source_admission'], 'NewDot native source admission changed')
        for kind, owner in owners.items():
            expected = dict(repository='private', **admission['files'][owner['path']])
            _need(_same_ref(owner, expected), 'Native materials differ from the adopted exact owner')
    else:
        paths = dict(initiative='results/research-initiative/v0.1.0/index.json', structure='results/profile-structure/v0.1.0/index.json', baseline='results/mathematical-profiles/v0.4.0/index.json')
        for kind, path in paths.items():
            index = _object(read_bytes(Path(roots['private']) / path))
            expected = dict(repository='private', **index['models'][mid]['source-bindings'])
            _need(_same_ref(owners[kind], expected), 'A selected source owner was substituted')
    material = _object(exact_source(roots, owners['initiative']))
    _need(material['model_id'] == mid, 'Source owner names another model')
    actual = {r['opportunity_id']: r for r in material['rows']}
    for row in model['a1_support_opportunities']:
        selected = actual[row['case_id']]
        _need(set(row['selected_documents']) == set(selected['sources']) and all((_same_ref(value, selected['sources'][sid]) for sid, value in row['selected_documents'].items())), 'An A1 support document is not the exact selected first answer')
    permitted = actual['independent-extension']['sources']
    if mid == 'gemini-4-carbon-medium':
        structural = _object(exact_source(roots, owners['structure']))
        mt = next((r for r in structural['rows'] if r['stage'] == 'independent'))
        addition = _object(exact_source(roots, mt['bindings']['independent_addition']))
        permitted = addition['sources']
    chosen = [d['source'] for r in model['anchor']['rounds'] for d in r['selected_documents']]
    _need({(r['path'], r['sha256']) for r in chosen} == {(r['path'], r['sha256']) for r in permitted.values()}, 'A trajectory added or omitted a selected final/companion/cutoff document')

def prepare_materials(intake_root, *, public_root, private_root, policy_root, freeze_root):
    """Build exact source registries and unreviewed scaffolds; never infer grades."""
    roots = dict(public=Path(public_root), private=Path(private_root))
    policy, policy_binding = load_policy(policy_root)
    area = Path(freeze_root)
    freeze = _object(read_bytes(area / 'FREEZE.json'))
    template_raw, support_raw = (read_bytes(area / name) for name in ('review-template.json', 'support-contract.json'))
    _need(binding(template_raw) == freeze['template'] and digest(template_raw) == TEMPLATE_SHA256 and (binding(support_raw) == freeze['support_contract']) and (digest(support_raw) == SUPPORT_SHA256) and (policy_binding == freeze['policy']), 'Frozen template/support/policy bytes changed')
    template, support = (_object(template_raw), _object(support_raw))
    notes_raw = read_bytes(area / 'contract-notes.private.json')
    _need(binding(notes_raw) == policy['cross_task_corroboration']['private_contract_notes_binding'] == template['private_contract_notes_binding'], 'Private requiredness contract notes changed')
    source_root = Path(intake_root)
    inventory_raw = read_bytes(source_root / 'source-manifest.json')
    inventory = _object(inventory_raw)
    _need(binding(inventory_raw) == freeze['source_inventory'] and digest(inventory_raw) == INTAKE_SHA256 and (inventory['cohort'] == policy['cohort']['selected_configurations'] == support['cohort']), 'Need the frozen actual19-model intake and support screening')
    boundary = next((r for r in inventory['source_snapshot']['common_contracts'] if r['sha256'] == policy['source_inputs']['private_common_boundary_contract']['sha256']), None)
    _need(boundary is not None and binding(exact_source(roots, boundary)) == policy['source_inputs']['private_common_boundary_contract'], 'The exact common required-goal contract changed')
    materials, scaffolds = ({}, {})
    cohort_binding = dict(configuration_ids_sha256=digest(encoded(inventory['cohort'])), source_inventory=binding(inventory_raw))
    for item in inventory['models']:
        mid = item['model_id']
        raw = read_bytes(source_root / item['path'])
        _need(binding(raw) == {k: item[k] for k in ('bytes', 'sha256')}, 'Frozen per-model intake changed')
        model = _object(raw)
        _verify_indexed_selection(model, roots)
        model_ref = reference('private', INTAKE_PREFIX + '/' + item['path'], raw)
        registry = []

        def add(sid, rid, descriptor, selection, kind):
            exact_source(roots, descriptor)
            _need(sid not in {r['source_id'] for r in registry}, 'Duplicate selected registry source ID')
            registry.append(dict(source_id=sid, round=rid, descriptor=deepcopy(descriptor), selection_binding=deepcopy(selection), kind=kind))
        for source in model['anchor']['original_task_materials']['supplied_materials']:
            name = PurePosixPath(source['path']).name
            if name in ('R1.md', 'R2.md', 'R3.md'):
                rid = name[:2]
                _need(binding(exact_source(roots, source)) == policy['main_anchor']['prompt_bindings'][rid], 'The common invited task changed')
                sid, kind = ('prompt:' + rid, 'task-boundary')
            elif name == 'rules.md':
                rid, sid, kind = ('R1', 'rules', 'task-boundary')
                _need(binding(exact_source(roots, source)) == policy['main_anchor']['rule_binding'], 'Common rules changed')
            else:
                rid, sid, kind = ('R1', 'supplied:' + name, 'supplied-material')
            add(sid, rid, source, model_ref, kind)
        for row in model['anchor']['rounds']:
            for document in row['selected_documents']:
                add(document['source_id'], row['round'], document['source'], model_ref, 'anchor-delivery')
        support_rows = []
        for row in model['a1_support_opportunities']:
            cid = row['case_id']
            add('task:' + cid, 'A1', row['common_task_ref'], model_ref, 'support-task-boundary')
            aliases = {}
            for sid, source in row['selected_documents'].items():
                alias = 'a1:' + cid + ':' + sid
                add(alias, 'A1', source, model_ref, 'support-delivery')
                aliases[sid] = alias
            support_rows.append(dict(case_id=cid, family_id=row['family_id'], source_state=row['source_state'], aliases=aliases, task_source_id='task:' + cid, original_task=deepcopy(row['common_task_ref']), selected_a1_binding=dict(source=model_ref, pointer='/a1_support_opportunities/' + str(len(support_rows))), factual_review_pointers=[dict(source=row['existing_autonomous_mathematical_review']['source'], pointer=row['existing_autonomous_mathematical_review']['pointer'])] + row['other_existing_mathematical_facts']))
        material = dict(schema=MATERIAL_SCHEMA, version=VERSION, edition=EDITION, model_id=mid, policy_binding=policy_binding, cohort_binding=cohort_binding, selected_trajectory_manifest=model_ref, source_registry=registry, anchor_rounds=deepcopy(model['anchor']['rounds']), support_contract=binding(support_raw), support_opportunities=support_rows, existing_anchor_factual_reviews=deepcopy(model['anchor']['existing_mathematical_facts']) + ([] if model['anchor']['existing_autonomous_mathematical_review'].get('source_status') == 'stale-unavailable-before-explicit-admission' else [model['anchor']['existing_autonomous_mathematical_review']]), source_selection_receipts=deepcopy(model['anchor']['selected_source_adoption']), new_candidate_calls=0, main_scores_modified=False, existing_axes_modified=False)
        scaffold = deepcopy(template['review'])
        scaffold.update(model_id=mid, cohort_binding=cohort_binding, selected_trajectory_manifest=model_ref, policy_binding=policy_binding)
        scaffold['source_registry'] = [{k: deepcopy(v) for k, v in row.items() if k != 'kind'} | dict(read_scope='not_read') for row in registry]
        materials[mid], scaffolds[mid] = (material, scaffold)
    return (materials, scaffolds, policy, template)

def _registry(review, material, roots):
    expected = {r['source_id']: r for r in material['source_registry']}
    rows = review.get('source_registry')
    _need(isinstance(rows, list) and len(rows) == len(expected) and (len({r.get('source_id') for r in rows}) == len(rows)), 'Need the exact complete source registry')
    found = {}
    for row in rows:
        sid = row.get('source_id')
        _need(sid in expected and set(row) == {'source_id', 'round', 'descriptor', 'selection_binding', 'read_scope'} and (row['round'] == expected[sid]['round']) and (row['descriptor'] == expected[sid]['descriptor']) and (row['selection_binding'] == expected[sid]['selection_binding']) and (row['read_scope'] in ('full', 'partial', 'not_read', 'not_applicable')), 'Registry substituted a source, scope, round or selection binding')
        exact_source(roots, row['descriptor'])
        found[sid] = dict(row, kind=expected[sid]['kind'])
    return found

def validate_material_sources(material, *, public_root, private_root, intake_root=None):
    """Authenticate registry membership through the frozen inventory and current owners."""
    roots = dict(public=Path(public_root), private=Path(private_root))
    area = Path(intake_root) if intake_root is not None else roots['private'] / INTAKE_PREFIX
    inventory_raw = read_bytes(area / 'source-manifest.json')
    _need(digest(inventory_raw) == INTAKE_SHA256, 'The source intake is not the frozen selected inventory')
    inventory = _object(inventory_raw)
    mid = material.get('model_id')
    item = next((r for r in inventory['models'] if r['model_id'] == mid), None)
    _need(item is not None and material.get('schema') == MATERIAL_SCHEMA, 'Unknown selected material model')
    raw = read_bytes(area / item['path'])
    _need(binding(raw) == {k: item[k] for k in ('bytes', 'sha256')}, 'Frozen selected model material changed')
    selected = _object(raw)
    expected_ref = reference('private', INTAKE_PREFIX + '/' + item['path'], raw)
    _need(material['selected_trajectory_manifest'] == expected_ref and material['cohort_binding'] == dict(configuration_ids_sha256=digest(encoded(inventory['cohort'])), source_inventory=binding(inventory_raw)) and (material['policy_binding'] == dict(bytes=30589, sha256=POLICY_SHA256)) and (material['support_contract'] == dict(bytes=102239, sha256=SUPPORT_SHA256)), 'Material/source/policy/cohort selection changed')
    _verify_indexed_selection(selected, roots)
    expected = {}

    def add(sid, rid, source, kind):
        expected[sid] = (rid, source, kind)
    for source in selected['anchor']['original_task_materials']['supplied_materials']:
        name = PurePosixPath(source['path']).name
        if name in ('R1.md', 'R2.md', 'R3.md'):
            add('prompt:' + name[:2], name[:2], source, 'task-boundary')
        elif name == 'rules.md':
            add('rules', 'R1', source, 'task-boundary')
        else:
            add('supplied:' + name, 'R1', source, 'supplied-material')
    for row in selected['anchor']['rounds']:
        for doc in row['selected_documents']:
            add(doc['source_id'], row['round'], doc['source'], 'anchor-delivery')
    for row in selected['a1_support_opportunities']:
        cid = row['case_id']
        add('task:' + cid, 'A1', row['common_task_ref'], 'support-task-boundary')
        for sid, source in row['selected_documents'].items():
            add('a1:' + cid + ':' + sid, 'A1', source, 'support-delivery')
    registry = material['source_registry']
    _need(len(registry) == len(expected) and {r['source_id'] for r in registry} == set(expected), 'Material registry added or omitted a selected source')
    for row in registry:
        rid, source, kind = expected[row['source_id']]
        _need(row['round'] == rid and row['descriptor'] == source and (row['kind'] == kind) and (row['selection_binding'] == expected_ref), 'Material registry opened an unselected source')
    _need(material['anchor_rounds'] == selected['anchor']['rounds'], 'Selected original round statuses changed')
    anchor_facts = deepcopy(selected['anchor']['existing_mathematical_facts'])
    prior = selected['anchor']['existing_autonomous_mathematical_review']
    if prior.get('source_status') != 'stale-unavailable-before-explicit-admission':
        anchor_facts.append(prior)
    _need(material['existing_anchor_factual_reviews'] == anchor_facts and material['source_selection_receipts'] == selected['anchor']['selected_source_adoption'], 'Selected mathematical fact or source-admission receipts changed')
    _need(len(material['support_opportunities']) == 27, 'Need every fixed support opportunity')
    for index, row in enumerate(selected['a1_support_opportunities']):
        actual = material['support_opportunities'][index]
        _need(actual['case_id'] == row['case_id'] and actual['family_id'] == row['family_id'] and (actual['source_state'] == row['source_state']) and (actual['original_task'] == row['common_task_ref']) and (actual['aliases'] == {sid: 'a1:' + row['case_id'] + ':' + sid for sid in row['selected_documents']}) and (actual['factual_review_pointers'] == [dict(source=row['existing_autonomous_mathematical_review']['source'], pointer=row['existing_autonomous_mathematical_review']['pointer'])] + row['other_existing_mathematical_facts']), 'A support family, source status or alias changed')
    return selected

def _quotes(quotes, registry, roots, *, rounds=None, kinds=None, nonempty=True):
    _need(isinstance(quotes, list) and (bool(quotes) or not nonempty), 'Need exact source quotes')
    result = set()
    for quote in quotes:
        sid = quote.get('source_id')
        _need(sid in registry and (rounds is None or registry[sid]['round'] in rounds) and (kinds is None or registry[sid]['kind'] in kinds), 'Quote is outside the selected action context')
        read_exact_quote(quote, {sid: registry[sid]['descriptor']}, roots)
        result.add(sid)
    return result

def _factual_pointer(ref, allowed, roots):
    _need(isinstance(ref, dict) and isinstance(ref.get('source'), dict) and _text(ref.get('pointer')), 'Need a source-bound existing factual review pointer')
    _need(any((_same_ref(ref['source'], entry['source']) and (ref['pointer'] == entry['pointer'] or ref['pointer'].startswith(entry['pointer'] + '/')) for entry in allowed)), 'Unselected mathematical review cannot annotate verification')
    value = _object(exact_source(roots, ref['source']))
    for part in ref['pointer'].split('/')[1:]:
        part = part.replace('~1', '/').replace('~0', '~')
        value = value[int(part)] if isinstance(value, list) else value[part]

def _review_ref(ref, material, roots):
    allowed = []
    for row in material['support_opportunities']:
        allowed.extend(row['factual_review_pointers'])
    allowed.extend(material['existing_anchor_factual_reviews'])
    _factual_pointer(ref, allowed, roots)

def _eligible(action):
    return action['requiredness'] in ('discretionary_within_main_open_task', 'unsolicited_beyond_legacy_required_core') and action['prompt_relation'] not in ('required_or_routine', 'unresolved') and (action['stage_role'] != 'retained_only') and bool(action['axis_assignments'])

def _action(action, registry, material, roots):
    for field in ('action_id', 'episode_id', 'question_or_choice', 'concrete_operation', 'actual_observation_or_failure_location', 'requiredness_reason', 'independence_cluster'):
        _need(_text(action.get(field)), 'Action lacks its concrete question/operation/observation/boundary')
    rid, sid = (action.get('round'), action.get('source_id'))
    _need(rid in (*ROUND_IDS, 'A1') and sid in registry and (registry[sid]['round'] == rid) and (registry[sid]['kind'] in ('anchor-delivery', 'support-delivery')), 'An action must locate its actual selected delivery, not a prompt or other round')
    _need(action.get('prompt_relation') in PROMPT_STATES and action.get('stage_role') in STAGE_ROLES and (action.get('requiredness') in ('discretionary_within_main_open_task', 'unsolicited_beyond_legacy_required_core', 'required_or_routine', 'unresolved')) and (type(action.get('question_inferred_from_math')) is bool), 'Action elicitation/stage/requiredness is not explicit')
    if rid == 'A1':
        _need(registry[sid]['read_scope'] in ('partial', 'full'), 'An actual extra fragment must retain its truthful partial/full reading scope')
        _need(action['requiredness'] != 'discretionary_within_main_open_task', 'A1 support needs a genuine extra-core boundary')
        case = next((r for r in material['support_opportunities'] if sid in r['aliases'].values()), None)
        _need(case is not None, 'A1 action belongs to no selected common support slot')
        allowed = {s: entry for s, entry in registry.items() if s in case['aliases'].values() or s == case['task_source_id']}
    else:
        allowed = {s: entry for s, entry in registry.items() if entry['round'] in ROUND_IDS}
        _need(action['requiredness'] != 'unsolicited_beyond_legacy_required_core', 'An invited main-task action cannot be relabeled unsolicited A1 initiative')
    cited = _quotes(action.get('evidence'), allowed, roots, rounds={rid}, kinds={'anchor-delivery', 'support-delivery'})
    _need(sid in cited, 'The declared action source must occur in its actual evidence')
    boundaries = _quotes(action.get('task_boundary_evidence'), allowed, roots, kinds={'task-boundary', 'support-task-boundary'})
    if rid in ROUND_IDS:
        _need(all((registry[key]['round'] in ROUND_IDS and ROUND_IDS.index(registry[key]['round']) <= ROUND_IDS.index(rid) for key in boundaries)), 'An action cannot use a future invitation as its original requiredness boundary')
        elicitation = {'R1': 'self_chosen_within_open_invitation', 'R2': 'elicited_expansion_or_deepening', 'R3': 'elicited_self_audit_with_discretionary_action'}
        _need(action['prompt_relation'] in (elicitation[rid], 'required_or_routine', 'unresolved'), 'The actual R2/R3 invitation cannot become unsolicited or unprompted initiative')
    verification = action.get('verification', {})
    _need(verification.get('state') in VERIFY_STATES and verification.get('execution_support') in EXECUTION_STATES and _text(verification.get('mathematical_reason')) and _text(verification.get('claim_limits')), 'Every action needs a separate truthful verification state and limits')
    _quotes(verification.get('source_evidence'), allowed, roots, kinds={'anchor-delivery', 'support-delivery'})
    _need(isinstance(verification.get('reused_review_refs'), list), 'Existing verification refs must be explicit')
    for item in verification['reused_review_refs']:
        _review_ref(item, material, roots)
    assignments = action.get('axis_assignments')
    _need(isinstance(assignments, list) and len({r.get('axis_id') for r in assignments}) == len(assignments), 'Action axis assignments must be distinct')
    for assignment in assignments:
        _need(assignment.get('axis_id') in AXIS_IDS and assignment.get('organizing_role') in ROLE_GRADES and _text(assignment.get('trigger_reason')) and _text(assignment.get('role_reason')), 'Each overlapping axis requires its own actual trigger and organizing-role reason')
        _quotes(assignment.get('evidence'), allowed, roots, rounds={rid}, kinds={'anchor-delivery', 'support-delivery'})
        if assignment['axis_id'] == 'experimental_exploration' and _eligible(action):
            _need(verification['execution_support'] != 'execution_not_established' or verification['state'] in ('substantive_attempt_unclosed', 'invalid_operation', 'refuted_claim'), 'A design alone cannot establish an actually observed exploratory experiment')

def corroboration_summary(review, material):
    """Count already judged families; never infer an ordinal grade from counts."""
    observations = review['corroboration']['family_observations']
    result = {}
    for axis in AXIS_IDS:
        main = review['axes'][axis]['grade']
        complete = [r for r in observations if r['screening_complete'] is True]
        rows = [r['by_axis'][axis] for r in complete]
        fragment = sum((r['fragment_present'] is True for r in rows))
        reasons = {}
        for row in rows:
            if row['relation'] == 'insufficient':
                key = row.get('insufficient_reason', 'reviewed_no_fragment')
                reasons[key] = reasons.get(key, 0) + 1
        slot_states = {r['family_id']: r['source_state'] for r in material['support_opportunities']}
        missing = sum((slot_states[r['family_id']] == 'unknown-source' for r in complete))
        result[axis] = dict(main_grade=main, screened_families=len(complete), unreviewed_families=27 - len(complete), observed_fragment_families=fragment, source_missing_families=missing, support=None if main is None else sum((r['relation'] == 'support' for r in rows)), difference=None if main is None else sum((r['relation'] == 'difference' for r in rows)), insufficient=None if main is None else sum((r['relation'] == 'insufficient' for r in rows)), insufficient_reasons=reasons, relation_status='unanchored' if main is None else 'complete' if len(complete) == 27 else 'partial', observation_refs=[r['family_id'] for r in complete if r['by_axis'][axis]['fragment_present'] is True])
    return result

def validate_review(review, material, policy, *, public_root, private_root, allow_pending_support=False, intake_root=None):
    roots = dict(public=Path(public_root), private=Path(private_root))
    validate_material_sources(material, public_root=public_root, private_root=private_root, intake_root=intake_root)
    _need(review.get('schema') == REVIEW_SCHEMA and review.get('edition') == EDITION and (review.get('model_id') == material['model_id']) and _text(review.get('record_id')) and (review.get('policy_binding') == material['policy_binding']) and (review.get('cohort_binding') == material['cohort_binding']) and (review.get('selected_trajectory_manifest') == material['selected_trajectory_manifest']) and (review.get('new_candidate_calls') == 0) and (review.get('main_scores_modified') is False) and (review.get('existing_axes_modified') is False), 'Need an actual source/policy-bound review, never a template or score-changing record')
    reviewer = review.get('reviewer', {})
    _need(reviewer.get('kind') == 'ai' and reviewer.get('human_review') == 'pending' and (reviewer.get('post_observation') is True) and _text(reviewer.get('identity')) and _text(reviewer.get('context_id')), 'Preserve actual post-observation AI attribution and human-pending status')
    for key in ('primary_review_ref', 'coordinator_adjudication_ref'):
        if key in review:
            source = review[key]
            _need(isinstance(source, dict) and source.get('repository') == 'private' and source.get('path', '').startswith('reviews/exploration-orientation-20261125/'), 'Review provenance must remain in its explicitly retained private review archive')
            exact_source(roots, source)
    registry = _registry(review, material, roots)
    full = all((r['read_scope'] == 'full' for r in registry.values() if r['kind'] in ('anchor-delivery', 'task-boundary')))
    _need(type(review.get('sources_complete')) is bool and (not review['sources_complete'] or full), 'Source completion cannot be claimed without reading every prescribed final/companion/prompt')
    actions = review.get('actions')
    _need(isinstance(actions, list) and len({a.get('action_id') for a in actions}) == len(actions), 'Actions require unique actual identities')
    by_id = {a['action_id']: a for a in actions}
    for action in actions:
        _action(action, registry, material, roots)
        parent = action.get('parent_action_id')
        _need(parent is None or (parent in by_id and parent != action['action_id']), 'Unknown/self parent action')
        if parent:
            _need(by_id[parent]['round'] in ROUND_IDS and action['round'] in ROUND_IDS and (ROUND_IDS.index(by_id[parent]['round']) <= ROUND_IDS.index(action['round'])) or by_id[parent]['round'] == action['round'] == 'A1', 'An action cannot have a future-round parent')
        seen = {action['action_id']}
        while parent:
            _need(parent in by_id and parent not in seen, 'Action parent chain contains a missing link or cycle')
            seen.add(parent)
            parent = by_id[parent].get('parent_action_id')
    episodes = review.get('episodes')
    _need(isinstance(episodes, list) and len({e.get('episode_id') for e in episodes}) == len(episodes), 'Need distinct question/route episodes')
    episode_by = {e['episode_id']: e for e in episodes}
    for episode in episodes:
        refs = episode.get('action_refs')
        _need(_text(episode.get('question_or_route_family')) and _text(episode.get('deduplication_reason')) and _text(episode.get('independence_cluster')) and _text(episode.get('final_disposition')) and (episode.get('first_seen_round') in (*ROUND_IDS, 'A1')) and (episode.get('last_observed_round') in (*ROUND_IDS, 'A1')) and isinstance(refs, list) and refs and (len(refs) == len(set(refs))) and (set(refs) == {a['action_id'] for a in actions if a['episode_id'] == episode['episode_id']}), 'An episode must bind its actual linked actions without repeated-unit inflation')
    _need(all((a['episode_id'] in episode_by for a in actions)), 'An action lacks its deduplication episode')
    traces = review.get('stage_trace')
    _need(isinstance(traces, list), 'Need the actual stage trace')
    for trace in traces:
        action = by_id.get(trace.get('action_id'))
        _need(action is not None and trace.get('episode_id') == action['episode_id'] and (trace.get('round') in (*ROUND_IDS, 'A1')) and (trace.get('prompt_relation') in PROMPT_STATES) and (trace.get('stage_role') in STAGE_ROLES) and (trace.get('relation_to_previous_action') is None or _text(trace['relation_to_previous_action'])), 'Stage trace must retain actual action identity, prompting and later disposition')
        if trace['round'] == action['round']:
            _need(trace['prompt_relation'] == action['prompt_relation'] and trace['stage_role'] == action['stage_role'], 'First action stage differs from its typed action')
        else:
            _need(action['round'] in ROUND_IDS and trace['round'] in ROUND_IDS and (ROUND_IDS.index(trace['round']) > ROUND_IDS.index(action['round'])) and (trace['stage_role'] != 'new'), 'A later retained/corrected action is not a new independent action')
        _quotes(trace.get('evidence'), registry, roots, rounds={trace['round']}, kinds={'anchor-delivery', 'support-delivery'})
    _need({t['action_id'] for t in traces} == set(by_id), 'Every actual action needs a stage-trace entry')
    anchor_eligible = [a for a in actions if a['round'] in ROUND_IDS and _eligible(a)]
    axes = review.get('axes')
    _need(isinstance(axes, dict) and set(axes) == set(AXIS_IDS), 'Need exactly five independent organizing-role axes')
    for axis, row in axes.items():
        grade, state = (row.get('grade'), row.get('state'))
        _need(grade is None or (type(grade) is int and 0 <= grade <= 4), 'Ordinal grades must be integers0–4or null')
        _need(row.get('coding_confidence') in ('high', 'moderate', 'unresolved') and isinstance(row.get('exposure_constraints'), list), 'Need coding confidence and exposure constraints')
        _need(isinstance(row.get('action_refs'), list) and len(row['action_refs']) == len(set(row['action_refs'])) and all((aid in by_id and by_id[aid]['round'] in ROUND_IDS for aid in row['action_refs'])), 'The main radar may cite only selected anchor actions, never A1 support')
        if grade is None:
            _need(state in NULL_STATES and row.get('unknown_reason') == state, 'An unknown/identifiability state needs its actual reason, never a zero substitution')
        else:
            _need(review['sources_complete'] and anchor_eligible and _text(row.get('prompt_and_freedom_reason')) and (row['coding_confidence'] != 'unresolved') and all((row.get('source_coverage', {}).get(rid) == 'full' for rid in ROUND_IDS)) and (row['source_coverage'].get('attachments') in ('full', 'not_applicable')), 'A numeric axis needs complete read coverage, identifiable exploration and actual discretionary freedom')
            _need(_text(row.get('organizing_role_reason')) and _text(row.get('verification_summary')), 'A numeric organizational-role judgment needs its independent reason and truth limits')
            if grade == 0:
                _need(state == 'reviewed_absence' and _text(row.get('reviewed_absence_reason')) and (not row['action_refs']) and (not row['exposure_constraints']), 'Zero requires a full-scope observed absence with no observability blocker')
            else:
                _need(state == 'reviewed' and row['action_refs'] and all((_eligible(by_id[aid]) and any((a['axis_id'] == axis for a in by_id[aid]['axis_assignments'])) for aid in row['action_refs'])), 'Positive main axes require actual eligible actions and their axis-specific triggers')
                _quotes(row.get('whole_trajectory_evidence'), registry, roots, rounds=set(ROUND_IDS), kinds={'anchor-delivery'})
                if grade >= 3:
                    _need(_text(row.get('mainline_rationale')), 'Grade3/4requires a source-bound sustained mainline rationale')
                if grade == 4:
                    _need(_text(row.get('centrality_rationale')), 'Grade4requires an explicit agenda/path centrality rationale')
    if not anchor_eligible:
        _need(all((r['grade'] is None for r in axes.values())), 'No identifiable exploratory action cannot become five preference zeros')
    if review.get('profile_identifiability') == 'not_identifiable':
        _need(not anchor_eligible and all((r['state'] == 'not_identifiable' for r in axes.values())), 'Whole-profile nonidentifiability differs from a source gap or observed absence')
    else:
        _need(review.get('profile_identifiability') in ('identifiable', 'partially_identifiable', 'review_pending'), 'Need an explicit profile identifiability state')
    _validate_corroboration(review, material, registry, by_id, roots, allow_pending_support)
    return corroboration_summary(review, material)

def _validate_corroboration(review, material, registry, actions, roots, allow_pending):
    cor = review.get('corroboration', {})
    _need(cor.get('feeds_main_radar') is False and cor.get('planned_families') == 27, 'A1 corroboration must keep the fixed27families and cannot feed main grades')
    rows = cor.get('family_observations')
    _need(isinstance(rows, list) and len({r.get('family_id') for r in rows}) == len(rows), 'Count one common family once per axis, never units or variants')
    if allow_pending and (not rows) and (cor.get('status') == 'review_pending'):
        return
    slots = {r['family_id']: r for r in material['support_opportunities']}
    _need(all((r.get('family_id') in slots for r in rows)), 'Unknown support family')
    if not allow_pending:
        _need(len(rows) == 27 and all((r.get('screening_complete') is True for r in rows)), 'Publication needs completed screening of all27common families')
    for row in rows:
        slot = slots[row['family_id']]
        _need(row.get('selected_a1_binding') == slot['selected_a1_binding'] and row.get('task_and_required_boundary_binding') == slot['original_task'], 'Support changed its original answer or task boundary')
        _need(type(row.get('screening_complete')) is bool and set(row.get('by_axis', {})) == set(AXIS_IDS), 'Each support family needs an explicit five-axis screen')
        refs = row.get('eligible_extra_action_refs')
        _need(isinstance(refs, list) and all((aid in actions and actions[aid]['round'] == 'A1' and (actions[aid]['source_id'] in slot['aliases'].values()) and _eligible(actions[aid]) for aid in refs)), 'Support fragments must be genuinely extra actions in that selected A1 family')
        if row['screening_complete']:
            scope = row.get('read_scope')
            _need(scope in ('full', 'reused_full_review_and_exact_fragments') or slot['source_state'] in ('unknown-source', 'settled-blank'), 'A completed support screen must retain its actual full/reused reading scope')
            if scope == 'reused_full_review_and_exact_fragments':
                reused = row.get('reused_factual_review_refs')
                _need(isinstance(reused, list) and reused, 'Reused screening must bind this family original full-review facts')
                for item in reused:
                    _factual_pointer(item, slot['factual_review_pointers'], roots)
        for axis, item in row['by_axis'].items():
            if not row['screening_complete']:
                _need(item.get('fragment_present') is None and item.get('relation') == 'review_pending', 'An unread support slot cannot fabricate an observed absence')
                continue
            present = item.get('fragment_present')
            _need(type(present) is bool or (present is None and slot['source_state'] == 'unknown-source'), 'A support fragment needs an actual observed state')
            _need(_text(item.get('reason')), 'Keep each support absence/difference/insufficiency reason private')
            if present:
                eligible = [actions[aid] for aid in refs if any((a['axis_id'] == axis for a in actions[aid]['axis_assignments']))]
                _need(eligible and _text(item.get('substantive_and_autonomous_reason')), 'A support presence needs an independently substantive extra-core action')
                allowed = {sid: registry[sid] for sid in slot['aliases'].values()}
                _quotes(item.get('evidence'), allowed, roots, rounds={'A1'}, kinds={'support-delivery'})
                main = review['axes'][axis]['grade']
                expected = 'unanchored_observation' if main is None else 'support' if main > 0 else 'difference'
            else:
                expected = 'insufficient'
            _need(item.get('relation') == expected, 'Support/difference/null relation cannot change the main axis')
    derived = corroboration_summary(review, material)
    declared = cor.get('by_axis', {})
    _need(set(declared) == set(AXIS_IDS), 'Need five separate corroboration summaries')
    for axis, counts in derived.items():
        for key, value in counts.items():
            _need(declared[axis].get(key) == value, 'Corroboration counts must match actual unique-family judgments: ' + axis + '/' + key)

def with_derived_counts(review, material):
    """Return a new normalized review; retain the original proposal bytes separately."""
    result = deepcopy(review)
    result['corroboration']['by_axis'] = corroboration_summary(result, material)
    return result

def project_public(review, material, *, private_review_sha256):
    counts = corroboration_summary(review, material)
    actions = {a['action_id']: a for a in review['actions']}
    axes = {}
    for aid in AXIS_IDS:
        row = review['axes'][aid]
        states = sorted({actions[ref]['verification']['state'] for ref in row['action_refs']})
        axes[aid] = dict(grade=row['grade'], state=row['state'], coding_confidence=row['coding_confidence'], verification_states=states)
    eligible = [a for a in review['actions'] if a['round'] in ROUND_IDS and _eligible(a)]
    tags = []
    eligible_ids = {a['action_id'] for a in eligible}
    trace_roles = {r['stage_role'] for r in review['stage_trace'] if r['action_id'] in eligible_ids}
    if 'restructured' in trace_roles:
        tags.append('restructured_route')
    if 'abandoned' in trace_roles:
        tags.append('abandoned_route')
    if 'corrected' in trace_roles:
        tags.append('corrected_route')
    if any((a['verification']['state'] == 'substantive_attempt_unclosed' for a in eligible)):
        tags.append('unclosed_attempt')
    if any((a['verification']['state'] in ('refuted_claim', 'invalid_operation') for a in eligible)):
        tags.append('failed_attempt_observed')
    keys = ('support', 'difference', 'insufficient', 'observed_fragment_families', 'screened_families', 'unreviewed_families', 'source_missing_families', 'relation_status')
    return dict(schema=PUBLIC_SCHEMA, version=VERSION, edition=EDITION, model_id=review['model_id'], policy_sha256=material['policy_binding']['sha256'], private_materials_sha256=digest(encoded(material)), private_review_sha256=private_review_sha256, source_intake_sha256=INTAKE_SHA256, profile_identifiability=review['profile_identifiability'], axes=axes, tags=tags, corroboration={aid: {key: counts[aid][key] for key in keys} for aid in AXIS_IDS}, reviewer_kind='ai', human_review='pending', post_observation=True, formal_comparison_eligible=False, new_candidate_calls=0, main_scores_modified=False, existing_axes_modified=False, is_score=False, higher_is_better=None)

def validate_public(report, policy_binding):
    expected = {'schema', 'version', 'edition', 'model_id', 'policy_sha256', 'private_materials_sha256', 'private_review_sha256', 'source_intake_sha256', 'profile_identifiability', 'axes', 'tags', 'corroboration', 'reviewer_kind', 'human_review', 'post_observation', 'formal_comparison_eligible', 'new_candidate_calls', 'main_scores_modified', 'existing_axes_modified', 'is_score', 'higher_is_better'}
    _need(isinstance(report, dict) and set(report) == expected and (report['schema'] == PUBLIC_SCHEMA) and (report['version'] == VERSION) and (report['edition'] == EDITION) and (report['policy_sha256'] == policy_binding['sha256'] == POLICY_SHA256) and (report['source_intake_sha256'] == INTAKE_SHA256) and (report['reviewer_kind'] == 'ai') and (report['human_review'] == 'pending') and (report['post_observation'] is True) and (report['formal_comparison_eligible'] is False) and (report['new_candidate_calls'] == 0) and (report['main_scores_modified'] is False) and (report['existing_axes_modified'] is False) and (report['is_score'] is False) and (report['higher_is_better'] is None), 'Public projection must expose only the approved independent aggregate fields')
    for key in ('private_review_sha256', 'private_materials_sha256'):
        _need(isinstance(report[key], str) and re.fullmatch('[0-9a-f]{64}', report[key]) is not None, 'Public provenance uses opaque exact hashes')
    _need(set(report['axes']) == set(AXIS_IDS) and set(report['corroboration']) == set(AXIS_IDS), 'Public component needs five independent axes')
    _need(report['profile_identifiability'] in ('identifiable', 'partially_identifiable', 'not_identifiable', 'review_pending'), 'Unknown public profile state')
    for aid, row in report['axes'].items():
        _need(set(row) == {'grade', 'state', 'coding_confidence', 'verification_states'} and (row['grade'] is None and row['state'] in NULL_STATES or (type(row['grade']) is int and 0 <= row['grade'] <= 4 and (row['state'] == ('reviewed_absence' if row['grade'] == 0 else 'reviewed')))) and (row['coding_confidence'] in ('high', 'moderate', 'unresolved')) and isinstance(row['verification_states'], list) and (set(row['verification_states']) <= VERIFY_STATES), 'Invalid public ordinal/state/verification data')
        c = report['corroboration'][aid]
        _need(set(c) == {'support', 'difference', 'insufficient', 'observed_fragment_families', 'screened_families', 'unreviewed_families', 'source_missing_families', 'relation_status'}, 'Public corroboration must not expose private tasks or reasons')
        _need(all((v is None or (type(v) is int and 0 <= v <= 27) for k, v in c.items() if k != 'relation_status')) and c['screened_families'] + c['unreviewed_families'] == 27, 'Public support keeps its fixed27-family coverage')
        if row['grade'] is None:
            _need(c['support'] is c['difference'] is c['insufficient'] is None and c['relation_status'] == 'unanchored', 'Supplemental observations cannot fill a null main grade')
        else:
            _need(all((type(c[k]) is int for k in ('support', 'difference', 'insufficient'))) and c['support'] + c['difference'] + c['insufficient'] == c['screened_families'], 'Unique-family corroboration counts must retain their partition')
    _need(isinstance(report['tags'], list) and set(report['tags']) <= {'restructured_route', 'abandoned_route', 'corrected_route', 'unclosed_attempt', 'failed_attempt_observed'}, 'Public behavioral tags cannot expose topics or private material')
    return report

def stage(reviews, materials, policy, *, public_root, private_root, intake_root=None):
    """Produce public/private files in memory; callers explicitly install a reviewed result."""
    cohort = policy['cohort']['selected_configurations']
    _need(set(reviews) == set(materials) == set(cohort), 'Adoption must cover the exact frozen19configuration cohort')
    public_files, private_files, entries = ({}, {}, {})
    for mid in cohort:
        review = reviews[mid]
        validate_review(review, materials[mid], policy, public_root=public_root, private_root=private_root, intake_root=intake_root)
        review_raw, material_raw = (encoded(review), encoded(materials[mid]))
        report = project_public(review, materials[mid], private_review_sha256=digest(review_raw))
        validate_public(report, materials[mid]['policy_binding'])
        public_path = PRIVATE_PREFIX + '/' + mid + '/profile.json'
        public_raw = encoded(report)
        public_files[public_path] = public_raw
        entries[mid] = dict(path=public_path, **binding(public_raw))
        private_files[PRIVATE_PREFIX + '/' + mid + '/review.json'] = review_raw
        private_files[PRIVATE_PREFIX + '/' + mid + '/source-bindings.json'] = material_raw
        private_files[PRIVATE_PREFIX + '/' + mid + '/profile.json'] = public_raw
    policy_raw = encoded(policy)
    _need(digest(policy_raw) == POLICY_SHA256, 'Staging needs the frozen policy serialization')
    index = dict(schema=INDEX_SCHEMA, version=VERSION, edition=EDITION, cohort=cohort, axis_order=list(AXIS_IDS), policy=dict(path=POLICY_PATH, **binding(policy_raw)), source_intake_sha256=INTAKE_SHA256, models=entries, scale=[0, 4], human_review='pending', post_observation=True, new_candidate_calls=0, main_scores_modified=False, existing_axes_modified=False)
    public_files[PUBLIC_INDEX] = encoded(index)
    private_files[PRIVATE_PREFIX + '/index.json'] = encoded(dict(schema='math-gauge.exploration-orientation-private-index/v1', public_index=binding(public_files[PUBLIC_INDEX]), cohort=cohort, models={mid: dict(materials=binding(encoded(materials[mid])), review=binding(encoded(reviews[mid])), profile=entries[mid]) for mid in cohort}))
    return (public_files, private_files)

def load_public(root, *, cohort=None):
    root = Path(root)
    path = root / PUBLIC_INDEX
    if not path.is_file():
        return None
    policy, pb = load_policy(root)
    raw = read_bytes(path)
    index = _object(raw)
    expected = {'schema', 'version', 'edition', 'cohort', 'axis_order', 'policy', 'source_intake_sha256', 'models', 'scale', 'human_review', 'post_observation', 'new_candidate_calls', 'main_scores_modified', 'existing_axes_modified'}
    selected = policy['cohort']['selected_configurations']
    _need(set(index) == expected and index['schema'] == INDEX_SCHEMA and (index['version'] == VERSION) and (index['edition'] == EDITION) and (index['cohort'] == selected) and (set(index['models']) == set(selected)) and (index['axis_order'] == list(AXIS_IDS)) and (index['scale'] == [0, 4]) and (index['policy'] == dict(path=POLICY_PATH, **pb)) and (index['source_intake_sha256'] == INTAKE_SHA256) and (index['human_review'] == 'pending') and (index['post_observation'] is True) and (index['new_candidate_calls'] == 0) and (index['main_scores_modified'] is False) and (index['existing_axes_modified'] is False), 'Invalid selected public component index')
    _need(cohort is None or (len(cohort) == len(set(cohort)) == len(selected) and set(cohort) == set(selected)), 'Public orientation does not match the displayed settled cohort')
    reports = []
    for mid in selected:
        item = index['models'][mid]
        _need(item['path'] == PRIVATE_PREFIX + '/' + mid + '/profile.json', 'Unexpected public aggregate path')
        report = _object(exact_source(dict(public=root), dict(repository='public', **item)))
        validate_public(report, pb)
        _need(report['model_id'] == mid, 'Public report names a different model')
        reports.append(report)
    return dict(schema='math-gauge.exploration-orientation/v1', version=VERSION, edition=EDITION, policy_sha256=pb['sha256'], source_index=dict(path=PUBLIC_INDEX, **binding(raw)), axis_order=list(AXIS_IDS), scale=[0, 4], models=reports, human_review='pending', post_observation=True)

def attach_public(data, root):
    """Attach this one component after the current1.3cohort is finalized."""
    if data.get('benchmark_version') != EDITION:
        return data
    component = load_public(root, cohort=[m['id'] for m in data['models']])
    if component is not None:
        data['exploration_orientation'] = component
    return data

def validate_component(component):
    """Check the exact download envelope; raw private review objects cannot enter it."""
    fields = {'schema', 'version', 'edition', 'policy_sha256', 'source_index', 'axis_order', 'scale', 'models', 'human_review', 'post_observation'}
    _need(isinstance(component, dict) and set(component) == fields and (component['schema'] == 'math-gauge.exploration-orientation/v1') and (component['version'] == VERSION) and (component['edition'] == EDITION) and (component['policy_sha256'] == POLICY_SHA256) and (component['axis_order'] == list(AXIS_IDS)) and (component['scale'] == [0, 4]) and (component['human_review'] == 'pending') and (component['post_observation'] is True), 'Download accepts only the validated public aggregate envelope')
    source = component['source_index']
    _need(set(source) == {'path', 'bytes', 'sha256'} and source['path'] == PUBLIC_INDEX and (type(source['bytes']) is int) and (source['bytes'] > 0) and isinstance(source['sha256'], str) and (re.fullmatch('[0-9a-f]{64}', source['sha256']) is not None), 'Public download needs its exact aggregate index identity')
    _need(isinstance(component['models'], list) and len({r['model_id'] for r in component['models']}) == len(component['models']), 'Public download configurations must be unique')
    for report in component['models']:
        validate_public(report, dict(sha256=POLICY_SHA256))
    return component
