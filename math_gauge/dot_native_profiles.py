"""Additive profiles for one expressly selected 2026-11-25 native Dot run.

The original profile owners keep their historical source readers unchanged.
These subclasses authenticate the new native source contract, then give the
same validated judgments and immutable task weights to their shared scorers.
No candidate execution, source repair, main-score change or private projection.
"""
from copy import deepcopy
from pathlib import Path
import hashlib
import json

from . import mathematical_profile as base
from . import mathematical_profile_revision as revision
from . import open_research as research
from . import profile_structure as structure
from . import research_initiative as initiative
from . import legacy_taste as taste
from . import legacy_taste_strict as strict_taste
from .dot_rerun_admission import MODEL, load_public as load_admission
from .dot_rerun_sources import validate as validate_native
from .dot_rerun_scoring import verify as verify_pair
from .dot_rerun_neutral import verify_replays
from .dot_rerun_independent import verify_review as verify_independent
from .mathematical_profile import source_bytes, _require, _text, _hash, _pointer
from .theorem_extension_calibration import document

VERSION = '0.1.0'
DIRECTORY = 'results/dot-native-profiles/v0.1.0/dot-20261125'
INDEX_PATH = DIRECTORY + '/index.json'
EVIDENCE_PROFILE_PATH = DIRECTORY + '/evidence-replacement-v1/formalization-overlay.json'
SOURCE = DIRECTORY + '/source'
CONDITION = 'nonlogical_retry_3'
BOUNDARIES = dict(reviewer_kind='ai', human_review='pending', post_observation=True,
                  formal_comparison_eligible=False, new_candidate_calls=0,
                  main_scores_modified=False, original_bytes_rewritten=False)
CONTRACTS = dict(base='protocol/mathematical-profile/v0.4.0/contracts.json',
                 open='protocol/open-research/v0.1.0/contracts.json',
                 structure='protocol/profile-structure/v0.1.0/contracts.json',
                 initiative='protocol/research-initiative/v0.1.0/contracts-v2.json')


def encoded(value):
    return (json.dumps(value, ensure_ascii=False, sort_keys=True, indent=2, allow_nan=False) + '\n').encode()


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def reference(path, raw, repository=None):
    value = dict(path=str(path), bytes=len(raw), sha256=digest(raw))
    return value if repository is None else dict(value, repository=repository)


def _read(roots, ref):
    _require(isinstance(ref, dict) and ref.get('repository') in roots,
             'Native profile source needs an explicit repository')
    return source_bytes(roots[ref['repository']], ref)


def _source(ref):
    return dict(repository='private', path=SOURCE + '/' + ref['path'],
                bytes=ref['bytes'], sha256=ref['sha256'])


def _json(root, path):
    return json.loads((Path(root) / path).read_bytes())


def _fixed(review, schema, policy_sha256, materials):
    expected = dict(schema=schema, model_id=MODEL, condition=CONDITION,
                    policy_sha256=policy_sha256, materials_sha256=digest(encoded(materials)),
                    reviewer_kind='ai', human_review='pending', new_candidate_calls=0,
                    formal_comparison_eligible=False)
    _require(all(type(review.get(k)) is type(v) and review[k] == v for k, v in expected.items())
             and _text(review.get('reviewer_id')), 'Native profile review lost its exact source or attribution')


def _contract(public_root, private_root, kind, policy):
    path = CONTRACTS[kind]
    raw = (Path(private_root) / path).read_bytes()
    _require(digest(raw) == policy['private_contract_sha256'], 'Native profile changed the frozen common contract')
    value = json.loads(raw)
    if kind == 'base':
        base.validate_contracts(value, policy)
    elif kind == 'open':
        research.validate_contracts(value, policy, dict(public=Path(public_root), private=Path(private_root)))
    elif kind == 'structure':
        structure.validate_contracts(value, policy)
    elif kind == 'initiative':
        _require(initiative.load_contracts(public_root, private_root, policy) == value,
                 'Native initiative changed the frozen common task screening')
    return value, reference(path, raw, 'private')


def authenticate(public_root, private_root):
    """Reproduce the admitted native, mathematical, submission and replay chain."""
    public_root, private_root = Path(public_root), Path(private_root)
    admitted = load_admission(public_root, historical=True)
    _require(admitted is not None and admitted['public_source']['model_id'] == MODEL,
             'A native profile cannot select another or unadmitted Dot run')
    source = private_root / SOURCE
    ledger = _json(source, 'admission-build/inputs/native-source-ledger.json')
    ledger_raw = (source / 'admission-build/inputs/native-source-ledger.json').read_bytes()
    neutral_raw = (source / 'admission-build/neutral/private-inputs.json').read_bytes()
    neutral_manifest = (source / 'admission-build/neutral/private-manifest.json').read_bytes()
    _require(digest(ledger_raw) == admitted['public_source']['private_source_sha256']
             and digest(neutral_raw) == admitted['revised']['private_inputs_sha256']
             and digest(neutral_manifest) == admitted['revised']['private_manifest_sha256'],
             'Native profile raw intake differs from the public opaque bindings')
    base_ref = _json(source, 'admission-build/inputs/extracted-score-descriptor.json')
    neutral_ref = _json(source, 'admission-build/inputs/extracted-neutral-descriptor.json')
    independent_ref = _json(source, 'admission-build/research/registration-descriptor.json')
    _require(independent_ref['sha256'] == admitted['research']['private_research_sha256'],
             'Native profile independent trajectory belongs to another admission')
    verify_pair(public_root, source, source / 'dataset/benchmark-v1.0.0',
                base_ref, neutral_ref, independent_ref, historical=True)
    selected = validate_native(source, source / 'dataset/benchmark-v1.0.0', ledger,
                               include_evaluator_bindings=True)['selected']
    neutral = json.loads(neutral_raw)
    mathematics = _json(source, 'admission-build/inputs/nonlogical_retry_3-mathematics.json')
    submission = _json(source, 'admission-build/inputs/nonlogical_retry_3-submission.json')
    inputs = document(source, base_ref)
    strict_ref = inputs['private_scores'][CONDITION]['strict']
    strict_report = document(source, strict_ref)
    _require(strict_report['metrics'] == admitted['base']['strict'][CONDITION]['metrics'],
             'Native first-answer SMC does not match its public selection')
    return dict(roots=dict(public=public_root, private=private_root), native_root=source,
                admission=admitted, selected=selected, neutral=neutral, mathematics=mathematics,
                submission=submission, strict_report=strict_report, strict_ref=_source(strict_ref),
                ledger=ledger, independent_registration=document(source, independent_ref))


def _review_scopes(raw, case_id):
    """A shared review file is evidence only inside its explicitly named task."""
    try:
        data = json.loads(raw)
    except (ValueError, UnicodeDecodeError):
        return ['']
    identities = {case_id, case_id.removeprefix('MG-')}
    candidates = []
    escape = lambda key: str(key).replace('~', '~0').replace('/', '~1')
    def visit(value, pointer):
        if isinstance(value, dict):
            if any(value.get(k) in identities for k in ('case_id', 'case', 'id', 'task_id')
                   if isinstance(value.get(k), str)):
                candidates.append(pointer)
            for key, child in value.items():
                target = pointer + '/' + escape(key)
                if key in identities:
                    candidates.append(target)
                visit(child, target)
        elif isinstance(value, list):
            for index, child in enumerate(value):
                visit(child, pointer + '/' + str(index))
    visit(data, '')
    return sorted({p for p in candidates if not any(q != p and (p.startswith(q + '/') or q == '')
                                                      for q in candidates)})


def _task_sources(context, slot):
    binding = context['selected'][slot]
    refs = {'answer': _source(binding['response']), 'review': _source(binding['review'])}
    scopes = {'answer': ['']}
    scopes['review'] = _review_scopes(_read(context['roots'], refs['review']), slot.split(':')[0])
    return refs, scopes


def prepare_baseline(context):
    roots = context['roots']
    policy, policy_hash = base.load_policy(roots['public'])
    contracts, cref = _contract(roots['public'], roots['private'], 'base', policy)
    maths = {r['slot_id']: r for r in context['mathematics']['tasks']}
    submissions = {r['case_id']+':A1': r for r in context['submission']['initials']}
    submissions.update({'MG-C003:R'+str(r['round']): r for r in context['submission']['rounds']})
    tasks = []
    for contract in contracts['tasks']:
        slot = contract['id']
        refs, scopes = _task_sources(context, slot)
        state = dict(maths.get(slot, {}), case_id=contract['case_id'], family_id=contract['family_id'],
                     submission_assessment=submissions[slot])
        tasks.append(dict(id=slot, case_id=contract['case_id'], family_id=contract['family_id'],
                          contract=contract, raw_answer=refs['answer'], response_sha256=refs['answer']['sha256'],
                          selected_state=state, sources=refs, evidence_prefixes=scopes))
    materials = dict(schema='math-gauge.dot-native-profile-materials/v1', version=VERSION,
        model_id=MODEL, condition=CONDITION, policy_sha256=policy_hash,
        private_contract_sha256=policy['private_contract_sha256'], new_candidate_calls=0,
        admission=context['admission']['selection'], tasks=tasks,
        sources=dict(contracts=cref, selected_smc_report=context['strict_ref']))
    return materials, policy, policy_hash, contracts


def _evidence(entries, material, roots):
    _require(isinstance(entries, list) and entries, 'Every native profile judgment requires original evidence')
    for entry in entries:
        _require(set(entry) == {'source_id', 'pointer', 'quote'} and _text(entry['quote'])
                 and entry['source_id'] in material['sources'], 'Native profile quote borrowed an unselected source')
        name, pointer = entry['source_id'], entry['pointer']
        source = material['sources'][name]
        raw = _read(roots, source)
        _require(any(prefix == '' or pointer == prefix or pointer.startswith(prefix + '/')
                     for prefix in material['evidence_prefixes'].get(name, [''])),
                 'Native profile review evidence belongs to another mathematical task')
        if source['path'].endswith('.json'):
            value = _pointer(json.loads(raw), pointer)
            text = value if isinstance(value, str) else json.dumps(value, ensure_ascii=False)
        else:
            _require(pointer == '', 'A raw mathematical quote cannot contain a JSON pointer')
            text = raw.decode('utf-8')
        _require(entry['quote'] in text, 'Native profile quotation differs from selected source bytes')


def _validate_baseline_row(row, material, roots):
    _require(set(row.get('axes', {})) == base.BEHAVIOR, 'Native profile requires six independent judgments')
    base._validate_proof_core(row['axes']['proof'])
    base._validate_fidelity_core(row['axes']['fidelity'])
    for judgment in row['axes'].values():
        grade = judgment.get('grade')
        _require(grade is None or type(grade) is int and 0 <= grade <= 4,
                 'Native profile grade must be an independent integer0to4 or unknown')
        _require(_text(judgment.get('reason')), 'Native profile judgment needs its mathematical reason')
        _evidence(judgment.get('evidence'), material, roots)
        base._validate_assessment_status(judgment, grade, material, goal=False)
    goals, planned = row.get('goals', []), material['contract']['goals']
    _require(len(goals) == len(planned) and {g.get('id') for g in goals} == {g['id'] for g in planned},
             'Native profile changed its frozen original complete goals')
    for goal in goals:
        _require(goal.get('passed') is None or type(goal.get('passed')) is bool,
                 'Native goal must have an independent acceptance judgment')
        _require(_text(goal.get('reason')), 'Native goal needs its original acceptance reason')
        _evidence(goal.get('evidence'), material, roots)
        base._validate_assessment_status(goal, goal['passed'], material, goal=True)


class DotProfileInputs(base.ProfileInputs):
    """Original35-family input type with independently authenticated native sources."""
    def __init__(self, review, materials, *, public_root, private_root, context=None):
        context = authenticate(public_root, private_root) if context is None else context
        expected, policy, policy_hash, contracts = prepare_baseline(context)
        _require(materials == expected, 'Native first-answer profile substituted its selected materials')
        _fixed(review, 'math-gauge.dot-native-profile-review/v1', policy_hash, materials)
        by_id = {row['id']: row for row in materials['tasks']}
        rows = review.get('tasks', [])
        _require(len(rows) == len(by_id) == 42 and {r.get('id') for r in rows} == set(by_id),
                 'Native profile requires exactly39 initial and3 prescribed selfcheck deliveries')
        for row in rows:
            _validate_baseline_row(row, by_id[row['id']], context['roots'])
        self.review, self.policy, self.contracts, self.materials = map(deepcopy, (review, policy, contracts, materials))
        self.strict_report = deepcopy(context['strict_report'])


def prepare_revisions(context, baseline_review):
    roots = context['roots']
    policy, policy_hash = revision.load_policy(roots['public'])
    _, _, _, contracts = prepare_baseline(context)
    originals = {r['id']: r for r in baseline_review['tasks']}
    tasks = []
    for item in context['neutral']['rows']:
        slot = item['case_id'] + ':A1'
        continuation = item['continuation']
        sources = dict(answer=_source(continuation.get('answer') or continuation['cutoff_content']),
                       review=_source(continuation.get('review') or continuation['cutoff_review']))
        sources.update({'attachment:'+str(i): _source(ref) for i, ref in enumerate(continuation['attachments'])})
        contract = next(r for r in contracts['tasks'] if r['id'] == slot)
        tasks.append(dict(id=slot, case_id=item['case_id'], revision_ref=deepcopy(item),
                          revision_pointer='/rows/'+str(len(tasks)), contract=contract,
                          baseline_judgment=originals[slot], sources=sources))
    materials = dict(schema='math-gauge.dot-native-profile-revision-materials/v1', version=VERSION,
        model_id=MODEL, condition=CONDITION, policy_sha256=policy_hash, new_candidate_calls=0,
        admission=context['admission']['selection'], baseline_review_sha256=digest(encoded(baseline_review)), tasks=tasks)
    return materials, policy, policy_hash, contracts


class DotRevisionProfileInputs(revision.RevisionProfileInputs):
    """The same80/20 scorer, bound to this native run and its exact six revisions."""
    def __init__(self, review, materials, *, baseline, public_root, private_root, context=None):
        _require(isinstance(baseline, DotProfileInputs), 'Native revision needs its validated independent baseline')
        context = authenticate(public_root, private_root) if context is None else context
        expected, policy, policy_hash, contracts = prepare_revisions(context, baseline.review)
        _require(materials == expected, 'Native continuation materials changed the accepted original parent')
        _fixed(review, 'math-gauge.dot-native-profile-revision-review/v1', policy_hash, materials)
        by_id = {r['id']: r for r in materials['tasks']}
        rows = review.get('tasks', [])
        _require(len(rows) == len(by_id) == 6 and {r.get('id') for r in rows} == set(by_id),
                 'Native continuation profile must cover every and only adopted neutral task')
        for row in rows:
            revision.validate_task_review(row, by_id[row['id']], roots=context['roots'])
        from .scoring import score_mathematical_profile
        self.review, self.materials, self.policy, self.contracts = map(deepcopy, (review, materials, policy, contracts))
        self.base_score = score_mathematical_profile(baseline)
        self.base_profile = dict(metrics=deepcopy(self.base_score['metrics']))
        self.strict_report = deepcopy(context['admission']['final']['strict'])


def prepare_open(context):
    roots = context['roots']
    policy, policy_hash = research.load_policy(roots['public'])
    contracts, cref = _contract(roots['public'], roots['private'], 'open', policy)
    base_materials, _, _, _ = prepare_baseline(context)
    first = []
    for family in contracts['families']:
        original = next(r for r in base_materials['tasks'] if r['case_id'] == family['case_id'] and r['id'].endswith(':A1'))
        first.append(dict(case_id=family['case_id'], classification=base._delivery(original),
                          response_sha256=original['response_sha256'], sources=original['sources'],
                          native_evidence_prefixes=original['evidence_prefixes']))
    # No manuscript continuation was selected in this particular six-row loss set.
    _require(not any(r['subcategory'] == 'manuscript-completion' for r in context['neutral']['rows']),
             'New native manuscript revisions require an explicit source adapter')
    return (dict(schema='math-gauge.dot-native-open-research-materials/v1', model_id=MODEL,
        condition=CONDITION, policy_sha256=policy_hash, new_candidate_calls=0,
        admission=context['admission']['selection'], sources=dict(contracts=cref),
        first=first, revision=[], revision_available=True), policy, policy_hash, contracts)


class DotOpenResearchInputs(research.ResearchInputs):
    """Five manuscript outcomes on the original1.2 common-opportunity contract."""
    def __init__(self, review, materials, *, public_root, private_root, context=None):
        context = authenticate(public_root, private_root) if context is None else context
        expected, policy, policy_hash, contracts = prepare_open(context)
        _require(materials == expected, 'Native open-capability materials changed their actual deliveries')
        _fixed(review, 'math-gauge.dot-native-open-research-review/v1', policy_hash, materials)
        by_id = {('first', r['case_id']): r for r in materials['first']}
        rows = review.get('tasks', [])
        _require(len(rows) == len(by_id) == 5 and {(r.get('stage'), r.get('case_id')) for r in rows} == set(by_id),
                 'Native1.2 open capability requires its five original manuscript families')
        for row in rows:
            material = by_id[(row['stage'], row['case_id'])]
            _evidence(row.get('evidence'), dict(material,evidence_prefixes=material['native_evidence_prefixes']), context['roots'])
            research.validate_judgment(row, material, stage=row['stage'],
                                      read_source=lambda ref: _read(context['roots'], ref))
        self.review, self.materials, self.policy, self.contracts = map(deepcopy, (review, materials, policy, contracts))


def _independent_sources(context, *, trajectory=False):
    root = context['native_root']
    names = ('R1', 'R2', 'R3') if trajectory else ('R3',)
    refs = {}
    for name in names:
        path = name + '/answer.md'
        ref = reference(path, (root/'open-research'/path).read_bytes())
        refs[name + ':answer' if trajectory else 'answer'] = _source(dict(ref, path='open-research/'+path))
    return refs


def prepare_structure(context):
    roots = context['roots']
    policy, policy_hash = structure.load_policy(roots['public'])
    contracts, cref = _contract(roots['public'], roots['private'], 'structure', policy)
    base_materials, _, _, originals = prepare_baseline(context)
    by_case = {r['case_id']: r for r in base_materials['tasks'] if r['id'].endswith(':A1')}
    revision_materials = {}
    for item in context['neutral']['rows']:
        cont = item['continuation']
        revision_materials[item['case_id']] = dict(sources={
            'answer': _source(cont.get('answer') or cont['cutoff_content']),
            'review': _source(cont.get('review') or cont['cutoff_review'])},
            classification='active_final' if cont['status'] == 'reviewed' else 'forced_content')
    wanted = [('depth', r['case_id'], 'first') for r in contracts['depth']['task_bindings']]
    extra = structure.independent_case(contracts)
    wanted += [('open_research', r['case_id'], 'independent' if r['case_id'] == extra else 'first')
               for r in contracts['open_research']['opportunities']]
    wanted += [('depth', cid, 'revision') for cid in revision_materials
               if cid in {r['case_id'] for r in contracts['depth']['task_bindings']}]
    rows = []
    for axis, cid, stage in wanted:
        if stage == 'independent':
            sources = _independent_sources(context)
            classification = 'active_final'
            facts = []
            reg = context['independent_registration']
            review_ref = dict(reg['review'], path='admission-build/research/'+reg['review']['path'])
            facts.append(dict(source=_source(review_ref), pointer='/capacity', role='original_mathematical_review'))
        elif stage == 'revision':
            sources = revision_materials[cid]['sources']
            classification = revision_materials[cid]['classification']
            facts = [dict(source=sources['review'], pointer='', role='original_mathematical_review')]
        else:
            original = by_case[cid]
            sources = original['sources']
            classification = base._delivery(original)
            facts = [dict(source=sources['review'], pointer=p, role='original_mathematical_review')
                     for p in original['evidence_prefixes']['review']]
        # Only actual delivered mathematics is eligible for quotes. Original
        # reviews can be declared separately as retained verification facts.
        evidence_ids = [name for name in sources if name == 'answer' or name.startswith('attachment:')]
        rows.append(dict(axis=axis, case_id=cid, stage=stage, source_status='available',
                         classification=classification, sources=deepcopy(sources),
                         evidence_source_ids=evidence_ids, verified_math_facts=facts))
    materials = dict(schema='math-gauge.dot-native-structure-materials/v1', version=VERSION,
        model_id=MODEL, edition='1.3.0', condition=CONDITION, policy_sha256=policy_hash,
        private_contract_sha256=policy['private_contract_sha256'], new_candidate_calls=0,
        admission=context['admission']['selection'], contracts=cref, rows=rows, revision_available=True)
    return materials, policy, policy_hash, contracts, originals


class DotStructureInputs(structure.ProfileStructureInputs):
    """Current28/W69 and6/W11 contracts; native source intake only is additive."""
    def __init__(self, review, materials, *, public_root, private_root, context=None):
        context = authenticate(public_root, private_root) if context is None else context
        expected, policy, policy_hash, contracts, originals = prepare_structure(context)
        _require(materials == expected, 'Native structural profile substituted its task/final/verification sources')
        # The retained row validator enforces facets,2/3/4 gates, byte quotes,
        # actual primary attribution and itemized optional-error deletion.
        structure.validate_review(review, materials, policy, policy_hash, contracts, context['roots'])
        self.review, self.materials, self.policy, self.contracts = map(deepcopy, (review, materials, policy, contracts))
        self.revision_eligible = {r['case_id'] for r in originals['tasks'] if r['kind'] == 'initial'
                                  and r['subcategory'] not in ('lean-audit', 'lean-formalization')}


def prepare_initiative(context):
    roots = context['roots']
    policy, policy_hash = initiative.load_policy(roots['public'])
    contracts, cref = _contract(roots['public'], roots['private'], 'initiative', policy)
    baseline, _, _, _ = prepare_baseline(context)
    initial = {r['case_id']: r for r in baseline['tasks'] if r['id'].endswith(':A1')}
    rows = []
    for case in contracts['tasks']:
        if not case['eligible']:
            continue
        original = initial[case['id']]
        rows.append(dict(opportunity_id=case['id'], source_status='available',
            classification=base._delivery(original), sources=dict(answer=original['sources']['answer'])))
    rows.append(dict(opportunity_id='independent-extension', source_status='available',
                     classification='active_final', sources=_independent_sources(context, trajectory=True)))
    _require(len(rows) == 28, 'Native initiative must retain the28 common opportunities')
    return (dict(schema='math-gauge.dot-native-initiative-materials/v1', model_id=MODEL,
        condition=CONDITION, policy_sha256=policy_hash, contracts=cref,
        admission=context['admission']['selection'], new_candidate_calls=0, rows=rows), policy, policy_hash)


def score_initiative(review, materials, *, public_root, private_root, context=None):
    context = authenticate(public_root, private_root) if context is None else context
    expected, policy, policy_hash = prepare_initiative(context)
    _require(materials == expected, 'Native initiative substituted an opportunity or selected answer')
    initiative.validate_review(review, materials, policy, policy_hash, context['roots'])
    return initiative.score_review(review)


def prepare_taste(context):
    initial = {}
    revised = {}
    for slot, selected in context['selected'].items():
        cid = slot.removesuffix(':A1')
        if not cid.startswith(('MG-TX0', 'MG-TXP0')) or not slot.endswith(':A1'):
            continue
        refs, _ = _task_sources(context, slot)
        initial[cid] = dict(status='normal_final', response_sha256=refs['answer']['sha256'],
                            evidence=dict(answer=refs['answer']))
    for row in context['neutral']['rows']:
        if row['case_id'] in initial:
            continuation = row['continuation']
            _require(continuation['status'] == 'reviewed', 'A failed TX neutral needs its explicit unknown/zero source state')
            answer = _source(continuation['answer'])
            revised[row['case_id']] = dict(status='normal_final', response_sha256=answer['sha256'],
                evidence=dict(answer=answer), first_response_sha256=row['first_response_sha256'])
    _require(len(initial) == 6 and len(revised) == 5, 'Native taste must bind6 original and5 selected TX revisions')
    return dict(first=initial, revision=revised)


def score_taste(review, *, public_root, private_root, context=None):
    """Direct v0.2 proof-level judgments, existing six-family80/20 arithmetic."""
    context = authenticate(public_root, private_root) if context is None else context
    policy, policy_hash = strict_taste.load_policy(Path(public_root)/strict_taste.POLICY_PATH)
    scope_policy, _ = taste.load_policy(Path(public_root)/taste.POLICY_PATH)
    material = prepare_taste(context)
    _require(review.get('model_id') == MODEL and review.get('policy_sha256') == policy_hash
             and review.get('reviewer_kind') == 'ai' and review.get('human_review') == 'pending'
             and _text(review.get('reviewer_id')) and review.get('new_candidate_calls') == 0,
             'Native mathematical taste needs an explicit fresh proof-level review')
    rows = review.get('judgments', [])
    expected = {(stage, cid) for stage in ('first', 'revision') for cid in material[stage]}
    _require(len(rows) == len(expected) and {(r.get('stage'),r.get('case_id')) for r in rows} == expected,
             'Native taste review omitted or duplicated an adopted TX source')
    scores = {}
    for row in rows:
        stage, cid = row['stage'], row['case_id']
        source = material[stage][cid]
        _require(row.get('model_id') == MODEL, 'Native taste borrowed another model review')
        fields = {'model_id','stage','case_id','response_sha256','assessment_status','score',
                  'enough_evidence','reason','valid_scope','choice_value','condition_cost','evidence'}
        original = {key:row[key] for key in fields}
        taste._review_grade(original, source, context['roots'])
        checks, criteria = row.get('strict_checks'), row.get('criteria')
        _require(isinstance(checks, dict) and set(checks) == set(strict_taste.CHECKS)
                 and isinstance(criteria,dict) and set(criteria) == set(strict_taste.DIMENSIONS),
                 'Native taste must preserve each strict support/scope check')
        scored = row['score'] is not None
        if scored:
            _require(row.get('unresolved_kind') is None and all(type(v) is bool for v in checks.values())
                     and checks['no_silent_repair'] is True,
                     'Known native taste cannot depend on a silent repair or unresolved check')
        else:
            _require(row.get('unresolved_kind') in strict_taste.UNKNOWN_REASONS
                     and all(v is None or type(v) is bool for v in checks.values())
                     and any(checks[k] is None for k in strict_taste.CHECKS[:2]),
                     'Unknown native taste needs the actual missing source or unresolved proof')
        total = 0
        for axis, maximum in strict_taste.DIMENSIONS.items():
            judgment = criteria[axis]
            _require(set(judgment) == {'points','reason','evidence'} and _text(judgment['reason'])
                     and ((type(judgment['points']) is int and 0 <= judgment['points'] <= maximum)
                          if scored else judgment['points'] is None),
                     'Native taste dimensions lost their frozen40/30/30 budgets')
            taste._review_grade(dict(original,evidence=judgment['evidence']), source, context['roots'])
            total += judgment['points'] if scored else 0
        _require(not scored or (total == row['score'] and (total != 100 or all(checks.values()))
                 and (criteria['support']['points'] != 30 or checks['credited_work_closed'])),
                 'Native taste support or total was inferred instead of independently checked')
        scores[(MODEL, stage, cid)] = row['score']
    return taste._model_metrics(MODEL, material, scores, scope_policy)


def review_metadata(kind, materials, *, policy_sha256, reviewer_id):
    """Metadata only. Actual judgments and primary-review records remain explicit."""
    if kind == 'structure':
        return dict(schema='math-gauge.profile-structure-review/v1', version=structure.VERSION,
            edition=structure.EDITION, model_id=MODEL, condition=CONDITION,
            policy_sha256=policy_sha256, materials_sha256=structure.digest(structure.encoded(materials)),
            reviewer_id=reviewer_id, **structure.BOUNDARIES)
    schema = {'baseline':'math-gauge.dot-native-profile-review/v1',
              'revision':'math-gauge.dot-native-profile-revision-review/v1',
              'open':'math-gauge.dot-native-open-research-review/v1'}[kind]
    return dict(schema=schema, model_id=MODEL, condition=CONDITION,
                policy_sha256=policy_sha256, materials_sha256=digest(encoded(materials)),
                reviewer_id=reviewer_id, **BOUNDARIES)


def prepare_public_files(public_root, private_root, reviews):
    """Replay every source and judgment before returning additive file payloads."""
    from .scoring import (score_mathematical_profile, score_mathematical_profile_revisions,
                          score_open_research, score_profile_structure, profile_formalization_metric)
    from .formalization_profile import load_policy as formal_policy
    context = authenticate(public_root, private_root)
    _require(set(reviews) == {'baseline','revision','open','structure','initiative','taste'},
             'A complete Dot profile requires all six independent review components')
    materials, policy, ph, contracts = prepare_baseline(context)
    baseline = DotProfileInputs(reviews['baseline'], materials, public_root=public_root,
                               private_root=private_root, context=context)
    base_score = score_mathematical_profile(baseline)
    revised_materials, revised_policy, rh, _ = prepare_revisions(context, reviews['baseline'])
    revised = DotRevisionProfileInputs(reviews['revision'], revised_materials, baseline=baseline,
                       public_root=public_root, private_root=private_root, context=context)
    revision_score = score_mathematical_profile_revisions(revised)
    open_materials, open_policy, oh, _ = prepare_open(context)
    opened = DotOpenResearchInputs(reviews['open'], open_materials, public_root=public_root,
                                  private_root=private_root, context=context)
    open_score = score_open_research(opened)
    structural_materials, structural_policy, sh, _, _ = prepare_structure(context)
    structured = DotStructureInputs(reviews['structure'], structural_materials, public_root=public_root,
                                     private_root=private_root, context=context)
    structure_score = score_profile_structure(structured)
    initiative_materials, initiative_policy, ih = prepare_initiative(context)
    initiative_score = score_initiative(reviews['initiative'], initiative_materials,
        public_root=public_root, private_root=private_root, context=context)
    taste_score = score_taste(reviews['taste'], public_root=public_root, private_root=private_root, context=context)
    fp, fh = formal_policy(public_root)
    formalization = profile_formalization_metric(context['admission']['base']['strict'][CONDITION])
    _require(formalization == profile_formalization_metric(context['admission']['final']['strict']),
             'A non-Lean revision cannot change formalization or repair its original first answer')
    private = {}
    all_materials = dict(baseline=materials, revision=revised_materials, open=open_materials,
                         structure=structural_materials, initiative=initiative_materials,
                         taste=prepare_taste(context))
    all_scores = dict(baseline=base_score, revision=revision_score, open=open_score,
                      structure=structure_score, initiative=initiative_score, taste=taste_score)
    for kind in reviews:
        private[DIRECTORY+'/review/'+kind+'.json'] = encoded(reviews[kind])
        private[DIRECTORY+'/materials/'+kind+'.json'] = (structure.encoded(all_materials[kind])
                    if kind == 'structure' else initiative.encoded(all_materials[kind])
                    if kind == 'initiative' else encoded(all_materials[kind]))
        private[DIRECTORY+'/score/'+kind+'.json'] = encoded(all_scores[kind])
    def hashes(kind):
        return dict(private_review_sha256=digest(private[DIRECTORY+'/review/'+kind+'.json']),
                    private_materials_sha256=digest(private[DIRECTORY+'/materials/'+kind+'.json']))
    admission = context['admission']
    public = {}
    original = base.project_public(base_score, policy=policy, policy_sha256=ph, **hashes('baseline'),
        source_record=admission['revised']['source_record'], source_initial_assessment=admission['selection'])
    public[DIRECTORY+'/baseline.json'] = encoded(original)
    base_ref = reference(DIRECTORY+'/baseline.json', public[DIRECTORY+'/baseline.json'])
    continued = dict(schema='math-gauge.dot-native-profile-revision-model/v1', version=VERSION,
        model_id=MODEL, benchmark_version='1.2.0', condition=CONDITION,
        policy_sha256=rh, source_base_profile=base_ref, source_adoption=admission['revised']['_selection'],
        metrics=revision_score['metrics'], groups={}, revision_coverage=revision_score['revision_coverage'],
        **hashes('revision'), **BOUNDARIES)
    opened_report = research.project_public(open_score, policy=open_policy, policy_sha256=oh,
        review_sha256=hashes('open')['private_review_sha256'], materials_sha256=hashes('open')['private_materials_sha256'])
    structural_report = structure.project_public(structure_score, policy_hash=sh, **hashes('structure'))
    initiative_report = initiative.public_projection(reviews['initiative'], initiative_materials, ih)
    # Reconcile exact stored review bytes with the owner projection encoding.
    initiative_report.update(hashes('initiative'))
    taste_policy, th = strict_taste.load_policy(Path(public_root)/strict_taste.POLICY_PATH)
    taste_report = dict(schema='math-gauge.dot-native-taste-profile/v1', version=VERSION,
        edition='1.3.0', model_id=MODEL, condition=CONDITION, policy_sha256=th,
        metrics=taste_score, **hashes('taste'), **BOUNDARIES)
    formal_report = dict(schema='math-gauge.dot-native-formalization-profile/v1', version=VERSION,
        benchmark_version='1.2.0', model_id=MODEL, condition=CONDITION, policy_sha256=fh,
        source_report=admission['revised']['base_reports']['strict'][CONDITION],
        metric=formalization, **BOUNDARIES)
    for kind, value in dict(revision=continued, open=opened_report, structure=structural_report,
                            initiative=initiative_report, taste=taste_report, formalization=formal_report).items():
        public[DIRECTORY+'/'+kind+'.json'] = encoded(value)
    policies = dict(baseline=reference(base.POLICY_PATH, (Path(public_root)/base.POLICY_PATH).read_bytes()),
        revision=reference(revision.POLICY_PATH, (Path(public_root)/revision.POLICY_PATH).read_bytes()),
        open=reference(research.POLICY_PATH, (Path(public_root)/research.POLICY_PATH).read_bytes()),
        structure=reference(structure.POLICY_PATH, (Path(public_root)/structure.POLICY_PATH).read_bytes()),
        initiative=reference(initiative.POLICY_PATH, (Path(public_root)/initiative.POLICY_PATH).read_bytes()),
        taste=reference(strict_taste.POLICY_PATH, (Path(public_root)/strict_taste.POLICY_PATH).read_bytes()),
        formalization=reference('protocol/formalization-profile.json', (Path(public_root)/'protocol/formalization-profile.json').read_bytes()))
    public[INDEX_PATH] = encoded(dict(schema='math-gauge.dot-native-profile-index/v1', version=VERSION,
        model_id=MODEL, editions=['1.2.0','1.3.0'], source_admission=admission['selection'],
        policies=policies, profiles={name:reference(DIRECTORY+'/'+name+'.json', raw)
            for name, raw in [(Path(path).stem, raw) for path, raw in public.items()]}, **BOUNDARIES))
    private[DIRECTORY+'/adoption.json'] = encoded(dict(schema='math-gauge.dot-native-profile-adoption/v1',
        model_id=MODEL, public_index=reference(INDEX_PATH, public[INDEX_PATH]),
        source_admission=admission['selection'], policies=policies,
        source_closure=reference(DIRECTORY+'/source-closure.json',
            (Path(private_root)/DIRECTORY/'source-closure.json').read_bytes()),
        files={path:reference(path,raw) for path,raw in private.items()}, **BOUNDARIES))
    return public, private


def _validate_revision_public(report, policy, policy_hash, baseline_report, admission, ref, public_root):
    fixed = dict(schema='math-gauge.dot-native-profile-revision-model/v1', version=VERSION,
        model_id=MODEL, benchmark_version='1.2.0', condition=CONDITION, policy_sha256=policy_hash, **BOUNDARIES)
    _require(set(report) == set(fixed)|{'source_base_profile','source_adoption','metrics','groups',
             'revision_coverage','private_review_sha256','private_materials_sha256'}
        and all(type(report.get(k)) is type(v) and report[k] == v for k,v in fixed.items())
        and report['source_base_profile'] == ref
        and report['source_adoption'] == admission['revised']['_selection']
        and all(_hash(report[k]) for k in ('private_review_sha256','private_materials_sha256')),
        'Invalid additive native continuation profile')
    # Existing metric validation enforces original35-family/8-category coverage,
    # known zeros and exact-vs-unknown intervals, without claiming an old index.
    candidate = deepcopy(baseline_report)
    candidate['metrics'] = deepcopy(report['metrics'])
    base_policy, base_hash = base.load_policy(public_root)
    # The caller already authenticated this policy; keep support for test roots.
    base.validate_public(candidate, base_policy, policy_sha256=base_hash)
    counts = report['revision_coverage']
    _require(set(counts) == {'selected_tasks','reviewed_tasks','unknown_tasks'}
             and counts['selected_tasks'] == 6 and all(type(v) is int and v >= 0 for v in counts.values())
             and counts['reviewed_tasks'] + counts['unknown_tasks'] == 6,
             'Native continuation profile changed its fixed selected/unknown coverage')


def load_public(public_root):
    """Only explicitly installed additive files activate this one current Dot row."""
    root = Path(public_root)
    if not (root/INDEX_PATH).is_file():
        return None
    raw = (root/INDEX_PATH).read_bytes()
    index = json.loads(raw)
    active = load_admission(root)
    admission = (load_admission(root,historical=True) if active and active.get('prior_selection') else active)
    expected = dict(schema='math-gauge.dot-native-profile-index/v1', version=VERSION,
        model_id=MODEL, editions=['1.2.0','1.3.0'], **BOUNDARIES)
    _require(set(index) == set(expected)|{'source_admission','policies','profiles'}
             and all(type(index.get(k)) is type(v) and index[k] == v for k,v in expected.items())
             and admission is not None and index['source_admission'] == admission['selection'],
             'Dot profile selection belongs to another native run or historical edition')
    kinds = {'baseline','revision','open','structure','initiative','taste','formalization'}
    _require(set(index['profiles']) == set(index['policies']) == kinds,
             'Dot profile addition must supply the complete nine/ten-axis source set')
    policy_paths = dict(baseline=base.POLICY_PATH, revision=revision.POLICY_PATH,
        open=research.POLICY_PATH, structure=structure.POLICY_PATH, initiative=initiative.POLICY_PATH,
        taste=str(strict_taste.POLICY_PATH), formalization='protocol/formalization-profile.json')
    _require(all(index['policies'][kind] == reference(path,(root/path).read_bytes())
                 for kind,path in policy_paths.items()), 'Native profile policy references are not the actual common standards')
    reports = {}
    for kind, ref in index['profiles'].items():
        _require(set(ref) == {'path','bytes','sha256'} and type(ref['bytes']) is int and ref['bytes'] > 0
                 and _hash(ref['sha256']) and ref['path'] == DIRECTORY+'/'+kind+'.json',
                 'Dot profile source escaped its additive aggregate layer')
        reports[kind] = json.loads(source_bytes(root, ref))
        _require(reports[kind]['model_id'] == MODEL, 'Dot profile report borrowed another configuration')
        source_bytes(root, index['policies'][kind])
    bp, bh = base.load_policy(root)
    base.validate_public(reports['baseline'], bp, policy_sha256=bh)
    rp, rh = revision.load_policy(root)
    _validate_revision_public(reports['revision'], rp, rh, reports['baseline'], admission, index['profiles']['baseline'], root)
    op, oh = research.load_policy(root)
    research.validate_public(reports['open'], op, oh)
    sp, sh = structure.load_policy(root)
    structure.validate_public(reports['structure'], sp, sh)
    _require(reports['structure']['independent_delivery'] == dict(source_status='available',
        classification='active_final',planned_rounds=3,last_round_selected=True),
        'Native structural profile changed the actual final-manuscript delivery boundary')
    ip, ih = initiative.load_policy(root)
    initiative.validate_public(reports['initiative'], ip, ih)
    tp, th = strict_taste.load_policy(root/strict_taste.POLICY_PATH)
    taste_report = reports['taste']
    _require(set(taste_report) == {'schema','version','edition','model_id','condition','policy_sha256',
        'metrics','private_review_sha256','private_materials_sha256', *BOUNDARIES}
        and taste_report['schema'] == 'math-gauge.dot-native-taste-profile/v1'
        and taste_report['policy_sha256'] == th and set(taste_report['metrics']) == {'first','revision'}
        and all(taste_report[k] == v for k,v in BOUNDARIES.items()), 'Unsafe native taste aggregate')
    for metric in taste_report['metrics'].values():
        taste._validate_metric(metric)
    from .formalization_profile import load_policy as load_formal_policy
    from .scoring import profile_formalization_metric, profile_strict_completion_metric
    _, fh = load_formal_policy(root)
    formal = reports['formalization']
    _require(set(formal) == {'schema','version','benchmark_version','model_id','condition','policy_sha256',
        'source_report','metric', *BOUNDARIES} and formal['schema'] == 'math-gauge.dot-native-formalization-profile/v1'
        and formal['policy_sha256'] == fh and formal['source_report'] == admission['revised']['base_reports']['strict'][CONDITION]
        and formal['metric'] == profile_formalization_metric(admission['base']['strict'][CONDITION])
        and all(formal[k] == v for k,v in BOUNDARIES.items()), 'Native formalization must project the original whole Lean SMC')
    _require(reports['baseline']['metrics']['completion'] == profile_strict_completion_metric(admission['base']['strict'][CONDITION])
             and reports['revision']['metrics']['completion'] == profile_strict_completion_metric(admission['final']['strict']),
             'Native profiles changed the rule-selected official completion metric')
    source = reference(INDEX_PATH,raw)
    if active.get('prior_selection'):
        overlay = formalization_overlay(root, active, source, reports['formalization'])
        stored = (root/EVIDENCE_PROFILE_PATH).read_bytes()
        _require(json.loads(stored)==overlay,
                 'Replacement profile may project only authenticated Lean SMC and official completion')
        reports = deepcopy(reports)
        reports['formalization'].update(source_report=overlay['source_report'],metric=overlay['formalization'])
        for stage in ('baseline','revision'):
            reports[stage]['metrics']['completion'] = overlay['completion'][stage]
        return dict(index=index, source=reference(EVIDENCE_PROFILE_PATH,stored), reports=reports)
    return dict(index=index, source=source, reports=reports)


def formalization_overlay(root, active, original_index, original_report):
    from .scoring import profile_formalization_metric, profile_strict_completion_metric
    _require(active.get('prior_selection') is not None, 'Replacement profile needs a selected evidence revision')
    base=active['base']['strict'][CONDITION]
    revised=active['final']['strict']
    formal=profile_formalization_metric(base)
    _require(formal==profile_formalization_metric(revised), 'Neutral replay cannot change native Lean SMC')
    return dict(schema='math-gauge.dot-native-replacement-formalization/v1',model_id=MODEL,
        benchmark_version='1.2.0',condition=CONDITION,source_admission=active['selection'],
        original_profile_index=original_index,original_formalization_sha256=digest(encoded(original_report)),
        source_report=active['revised']['base_reports']['strict'][CONDITION],
        revised_report=active['revised']['scores']['strict'],formalization=formal,
        completion=dict(baseline=profile_strict_completion_metric(base),
                        revision=profile_strict_completion_metric(revised)),
        independent_reviews_changed=False,new_candidate_calls=0)


def _append(payload, entry, binding):
    _require(isinstance(payload, dict) and isinstance(payload.get('models'), list),
             'Native profile addition needs an authenticated existing public component')
    _require(not any(row['id'] == MODEL for row in payload['models']),
             'Native profile addition cannot replace an incumbent profile')
    payload['models'].append(deepcopy(entry))
    additions = payload.setdefault('additions', [])
    _require(binding not in additions, 'Duplicate native profile source binding')
    additions.append(deepcopy(binding))


def _append_base_profiles(data, selected):
    _require(any(row['id'] == MODEL for row in data['models']), 'A profile cannot admit its own leaderboard row')
    reports, binding = selected['reports'], selected['source']
    first = dict(id=MODEL, metrics=deepcopy(reports['baseline']['metrics']), groups={},
        review_status='ai-reviewed-human-pending', source=deepcopy(selected['index']['profiles']['baseline']))
    for field in ('mathematical_profile', 'mathematical_profile_baseline'):
        if data.get(field) is not None:
            _append(data[field], first, binding)
    revised = dict(id=MODEL, metrics=deepcopy(reports['revision']['metrics']), groups={},
        revision_coverage=deepcopy(reports['revision']['revision_coverage']),
        review_status='ai-reviewed-human-pending', source=deepcopy(selected['index']['profiles']['revision']))
    _append(data['mathematical_profile_revision'], revised, binding)
    _append(data['open_research'], dict(id=MODEL, first=reports['open']['first'], revision=reports['open']['revision']), binding)
    _append(data['formalization_profile'], dict(id=MODEL, metric=reports['formalization']['metric']), binding)
    if data.get('profile_models') is not None:
        model = next(row for row in data['models'] if row['id'] == MODEL)
        _require(not any(row['id'] == MODEL for row in data['profile_models']), 'Duplicate native profile selector')
        fields = ('id','label','short_label','theme','logo','presentation_eligibility',
                  'display_order','ranking_values','ranking_complete')
        data['profile_models'].append({key:deepcopy(model[key]) for key in fields if key in model})
    data.setdefault('sources', []).append(binding)


def append_edition_120(public_root, data):
    """Append only the new Dot metrics; preserve every retained row and source."""
    if data.get('benchmark_version') != '1.2.0':
        return
    selected = load_public(public_root)
    if selected is None:
        return
    _append_base_profiles(data, selected)


def append_edition_130(public_root, data):
    """Current structural/initiative overlays bind their own additive index."""
    if data.get('benchmark_version') != '1.3.0':
        return
    selected = load_public(public_root)
    if selected is None:
        return
    # The1.3 publisher reconstructs an unchanged retained baseline rather than
    # copying all current1.2 profiles. Append this native baseline explicitly.
    if not any(row['id'] == MODEL for row in data.get('mathematical_profile_revision', {}).get('models', [])):
        _append_base_profiles(data, selected)
    reports, binding = selected['reports'], selected['source']
    structural = dict(id=MODEL, **{key:deepcopy(reports['structure'][key]) for key in
                                 ('first','revision','revision_coverage','independent_delivery')})
    _append(data['profile_structure'], structural, binding)
    active = dict(id=MODEL, **{key:deepcopy(reports['initiative'][key]) for key in
                             ('metric','legacy_metric','extension_metric','legacy_weight','extension_weight')})
    _append(data['research_initiative'], active, binding)
    if binding not in data.setdefault('sources', []):
        data['sources'].append(binding)


def project_edition_130_abilities(public_root, result, policy, denominators):
    """Compose the existing1.3 axes with the new native baseline and strict TX taste."""
    from .research_profile import project_models
    selected = load_public(public_root)
    if selected is None:
        return project_models({}, {MODEL:result}, policy, denominators)[MODEL], None
    reports = selected['reports']
    data = dict(mathematical_profile_baseline=dict(schema='math-gauge.mathematical-profile-baseline/v1',
            benchmark_version='1.2.0', models=[dict(id=MODEL, metrics=reports['baseline']['metrics'])]),
        mathematical_profile_revision=dict(schema='math-gauge.mathematical-profile-revision/v1',
            benchmark_version='1.2.0', models=[dict(id=MODEL, metrics=reports['revision']['metrics'])]),
        open_research=dict(schema='math-gauge.open-research/v1', benchmark_version='1.2.0',
            models=[dict(id=MODEL, first=reports['open']['first'], revision=reports['open']['revision'])]))
    projected = project_models(data, {MODEL:result}, policy, denominators,
                               legacy_taste_strict={MODEL:reports['taste']['metrics']})[MODEL]
    return projected, selected['source']
