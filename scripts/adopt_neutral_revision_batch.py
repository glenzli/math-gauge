#!/usr/bin/env python3
"""Prepare or adopt a wholly reviewed neutral batch through the shared owners.

This command never calls models or grades mathematics. Preparation writes only a
disposable proposal; adoption accepts root-locked reviews and advances complete
models, leaving every existing adoption and source answer unchanged.
"""
from __future__ import annotations

import argparse
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from math_gauge.catalog import relative_name
from math_gauge.benchmarks import identity
from math_gauge.neutral_revision import (MODES, CONDITION, DIRECTORY, TARGET, SOURCE, VERSION,
    POLICY_PATH, TRANSITION_PATH, descriptor, document, read, require, load_policy,
    load_transition, load_model_selection, load_inputs, project_score, project_public_tasks, verify_pair,
    current_model_ids)
from math_gauge.records import public_assessment_case_ids
from math_gauge.scoring import score_neutral_revision_overlay
from scripts.results_revision_resources import (DATA_PATH, INDEX_PATH, build_batch_public,
    load_public as load_resources)

LOCK_SCHEMA = 'math-gauge.neutral-revision-final-review-selection/v1'


def encoded(value):
    return (json.dumps(value, ensure_ascii=False, indent=2, allow_nan=False) + '\n').encode()


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def ref(name, raw):
    relative_name(name)
    return dict(path=name, bytes=len(raw), sha256=sha(raw))


def external_bytes(item, *, base=None):
    require(isinstance(item, dict) and {'path','bytes','sha256'} <= set(item),
            'Expected an exact original-file descriptor')
    path = Path(item['path'])
    if not path.is_absolute():
        require(base is not None, 'Relative external source needs its stated root')
        path = Path(base) / path
    raw = path.read_bytes()
    require(len(raw) == item['bytes'] and sha(raw) == item['sha256'], 'Closed source bytes changed')
    return raw


def load_review_selection(path, runtime_path):
    """Only an explicit immutable root selection can promote an attachment."""
    if path is None or not Path(path).is_file():
        return None
    path = Path(path).resolve()
    value = json.loads(path.read_bytes())
    require(value.get('schema') == LOCK_SCHEMA and isinstance(value.get('rows'), dict),
            'Expected the root final-review selection contract')
    runtime = value.get('runtime_freeze')
    require(runtime is not None and external_bytes(runtime, base=path.parent) == Path(runtime_path).read_bytes(),
            'Final review selection binds a different immutable runtime freeze')
    for key, row in value['rows'].items():
        require(isinstance(key, str) and '--' in key and isinstance(row, dict)
                and 'review' in row and isinstance(row.get('attachments'), list)
                and isinstance(row.get('review_sources'), list),
                'Each locked review needs explicit attachment and review-source selections, including []')
    return value


def validate_locked_delivery(first, delivery, selected, *, lock_root):
    """Authenticate a final decision; no mathematical judgments are inferred."""
    review_raw = external_bytes(selected['review'], base=lock_root)
    review = json.loads(review_raw)
    require(review.get('reviewer_kind') == 'ai' and review.get('human_review') == 'pending'
            and review.get('mathematical_verdict_finalized') is True,
            'Preliminary or human-unapproved status cannot be rewritten at adoption')
    if delivery['normal_final_delivered']:
        require(review.get('response_sha256') == delivery['response']['sha256'],
                'Final review does not bind the complete actual final response')
        require(type(review.get('MC')) in {int,float} and 0 <= review['MC'] <= 100
                and type(review.get('RMC')) in {int,float} and -100 <= review['RMC'] <= 100
                and type(review.get('SMC')) is bool,
                'Final review requires exact MC/RMC/SMC source judgments')
    else:
        require(review.get('schema') == 'math-gauge.neutral-revision-cutoff-review/v1'
                and review.get('case_id') == first['case_id']
                and review.get('capability_completion', {}).get('exact') is not None,
                'A failed delivery remains unresolved until its actual cutoff MC is reviewed')
    # Newness of mathematical content belongs to the locked review. An explicit
    # resubmission may retain correct bytes; a mere mention is excluded by root's
    # authoritative attachment list rather than by a byte-change heuristic.
    allowed = {row['source']['sha256']: row for row in delivery.get('named_sealed_files', [])}
    answer = external_bytes(delivery['response']) if delivery.get('response') else b''
    attachments, names = [], set()
    for item in selected['attachments']:
        raw = external_bytes(item, base=lock_root)
        name = Path(item['path']).name
        require(name not in names and item['sha256'] in allowed and name.encode() in answer,
                'An attachment must be explicitly selected, named by the final, and terminal-bound')
        require(allowed[item['sha256']]['source']['bytes'] == len(raw), 'Selected attachment differs from sealed bytes')
        names.add(name)
        attachments.append((name, raw))
    if 'delivered_attachments' in review:
        require({row['sha256'] for row in review['delivered_attachments']}
                == {row['sha256'] for row in selected['attachments']},
                'Final selection and review disagree about delivered attachments')
    return review, review_raw, attachments


class Proposal:
    def __init__(self, public_root, private_root):
        self.roots = dict(public=Path(public_root), private=Path(private_root))
        self.new = dict(public={}, private={})
        self.context = dict(public={}, private={})

    def add(self, scope, name, value):
        raw = value if isinstance(value, bytes) else encoded(value)
        relative_name(name)
        old = self.new[scope].get(name)
        require(old is None or old == raw, 'Conflicting staged artifact')
        self.new[scope][name] = raw
        return ref(name, raw)

    def bind(self, scope, item):
        item = {key:item[key] for key in ('path','bytes','sha256')}
        self.context[scope][item['path']] = read(self.roots[scope], item)
        return item

    def materialize(self, destination):
        destination = Path(destination)
        for scope in ('public', 'private'):
            for name, raw in {**self.context[scope], **self.new[scope]}.items():
                path = destination / scope / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(raw)


def _guard_existing(public_root, private_root, transition):
    """Retain exact old adoption/resource bytes across an additive transaction."""
    result = {}
    for scope, root in (('public', Path(public_root)), ('private', Path(private_root))):
        for item in transition['adoptions'].values():
            folder = root / Path(item['path']).parent
            for path in folder.rglob('*'):
                if path.is_file():
                    result[(scope, path.relative_to(root).as_posix())] = sha(path.read_bytes())
    result[('public', DATA_PATH)] = sha((Path(public_root) / DATA_PATH).read_bytes())
    return result


def _put_model(proposal, public_root, private_root, run_root, source, deliveries, locked, lock_path, lock_raw, frozen_cells):
    mid = source['model_id']
    destination = Path(DIRECTORY) / mid / source['record_id']
    base = destination.as_posix()
    public_root, private_root = Path(public_root), Path(private_root)
    lookup = {row['case_id']:row for row in deliveries}
    rows = []

    def copied(name, raw):
        return proposal.add('private', base + '/' + name, raw)

    study_sources = []
    for name in ('pre-run-freeze.json','runtime-freeze.json','packet-index-evaluator-only.json','model-source-identities.json'):
        study_sources.append(copied('batch-source/' + name, (Path(run_root) / name).read_bytes()))
    for path in sorted((Path(run_root) / 'operational-attribution').glob(mid + '--*.json')):
        study_sources.append(copied('batch-source/operational-attribution/' + path.name, path.read_bytes()))
    study_sources.append(copied('batch-source/final-review-selection.json', lock_raw))
    for first in source['selection']:
        cid = first['case_id']
        delivery = lookup[cid]
        frozen = frozen_cells[mid + '--' + cid]
        require(delivery['id'] == frozen['id'] and delivery['original_input']['sha256'] == frozen['input_sha256'],
                'Closed answer input differs from its actual pre-call freeze')
        request_raw = external_bytes(frozen['portable_request'])
        request = json.loads(request_raw)
        request_hash = request.pop('request_sha256')
        require(request_hash == frozen['portable_request_sha256'] == identity(request)
                and len(request['messages']) == 1
                and request['messages'][0]['content'].encode() == external_bytes(delivery['original_input'])
                and request['source_response_sha256'] == first['response_sha256'],
                'Continuation request substituted the frozen original input or parent answer')
        execution = json.loads(external_bytes(delivery['native_execution']))
        require(execution.get('requested_model') == frozen['requested_model']
                and execution.get('requested_effort') == frozen['effort'],
                'Continuation changed the actual frozen requested model or effort')
        selected = locked['rows'][mid + '--' + cid]
        review, review_raw, attached = validate_locked_delivery(first, delivery, selected, lock_root=Path(lock_path).parent)
        prefix = 'continuations/' + cid + '/'
        input_ref = copied(prefix + 'input.md', external_bytes(delivery['original_input']))
        review_ref = copied(prefix + 'review.json', review_raw)
        collection_ref = copied(prefix + 'collection.json', external_bytes(delivery['collection']))
        sources = [copied(prefix + 'portable-request.json', request_raw)]
        if delivery.get('recovery_supplement'):
            supplement_raw = external_bytes(delivery['recovery_supplement'])
            supplement = json.loads(supplement_raw)
            require(supplement.get('schema') == 'math-gauge.neutral-revision-capacity-recovery/v1'
                    and supplement.get('logical_id') == delivery['id']
                    and supplement.get('selected_physical_attempt') == 2
                    and supplement.get('original_failure_not_pure_system_excluded') is True
                    and supplement.get('original_effective_attempt_retained') is True
                    and supplement.get('maximum_additional_attempts') == 1
                    and supplement.get('additional_attempts') == 1
                    and supplement['attempts'][1]['collection']['sha256'] == delivery['collection']['sha256']
                    and supplement['original_runtime_freeze']['sha256'] == sha((Path(run_root)/'runtime-freeze.json').read_bytes()),
                    'Recovery selection lacks its exact bounded post-observation supplement')
            sources.append(copied(prefix + 'recovery/recovery-supplement.json', supplement_raw))
            for key in ('authorization','recovery_plan','recovery_runtime_freeze','dispatch_gate'):
                sources.append(copied(prefix + 'recovery/' + key + '.json', external_bytes(supplement[key])))
            for ordinal, prior in enumerate(delivery.get('prior_attempts', []), 1):
                mapping = []
                for key in ('collection','native_execution','seal','native_events','original_input','initial_work','response','terminal_output_observation'):
                    if prior.get(key) is not None:
                        original = prior[key]
                        retained = copied(prefix + f'recovery/prior-{ordinal}/' + key + '-' + Path(original['path']).name,
                            external_bytes(original))
                        sources.append(retained)
                        mapping.append(dict(original=original, retained=retained))
                sources.append(copied(prefix + f'recovery/prior-{ordinal}/source-map.json', dict(
                    physical_attempt_number=ordinal, effective_attempt_retained=True,
                    selected_as_current_delivery=False, sources=mapping)))
        review_map = []
        for number, source_review in enumerate(selected['review_sources'], 1):
            raw = external_bytes(source_review, base=Path(lock_path).parent)
            name = Path(source_review['path']).name
            retained = copied(prefix + f'review-sources/{number:02d}-' + source_review['sha256'][:12] + '-' + name, raw)
            sources.append(retained)
            review_map.append(dict(original_source=source_review, retained_source=retained))
        sources.append(copied(prefix + 'review-sources/source-map.json', dict(
            schema='math-gauge.neutral-revision-retained-review-sources/v1',
            original_review_bytes_rewritten=False, sources=review_map)))
        for key, name in (('native_execution','execution.json'),('seal','seal.json'),
                          ('native_events','events.ndjson'),('initial_work','initial-work-materials.json'),
                          ('terminal_output_observation','terminal-output-observation.json')):
            if delivery.get(key):
                sources.append(copied(prefix + name, external_bytes(delivery[key])))
        session = Path(delivery['collection']['path']).parents[1]
        for name in ('plan.json','attempt-ledger.json','cli-identity.json'):
            sources.append(copied(prefix + name, (session / 'runtime' / name).read_bytes()))
        attachments = [copied(prefix + 'attachments/' + name, raw) for name, raw in attached]
        if delivery['normal_final_delivered']:
            answer_ref = copied(prefix + 'answer.md', external_bytes(delivery['response']))
            continuation = dict(status='reviewed', input=input_ref, answer=answer_ref, review=review_ref,
                collection=collection_ref, attachments=attachments, sources=sources, reused=False,
                scores=dict(capability=review['MC']/100, partial=review['RMC']/100, strict=int(review['SMC'])))
        else:
            if delivery.get('response') is not None:
                sources.append(copied(prefix + 'original-cutoff-response.md', external_bytes(delivery['response'])))
            content = selected.get('cutoff_content')
            cutoff_ref = None if content is None else copied(prefix + 'cutoff-content', external_bytes(content, base=Path(lock_path).parent))
            continuation = dict(status='delivery_failed', input=input_ref, scores=None, failure_evidence=collection_ref,
                cutoff_review=review_ref, cutoff_content=cutoff_ref, sources=sources, reused=False)
        originals = {}
        for target, key in (('original_task','source_case'),('original_answer','original_answer'),('original_review','original_review')):
            item = first.get(key)
            if item is not None:
                proposal.bind(item['scope'], item)
            originals[target] = item
        rows.append(dict(case_id=cid, family_id=first['family_id'], subcategory=first['subcategory'],
            first_response_sha256=first['response_sha256'], first_review_sha256=first['review_sha256'],
            **originals, source_component=None, continuation=continuation))
    companion, resource_sources = build_batch_public(public_root, private_root, run_root, mid, source, deliveries)
    resource_ref = proposal.add('public', 'results/continuation-resources/v0.1.0/batches/gpt-20261120/' + mid + '/resources.json', companion)
    study_sources.append(copied('batch-source/resource-sources.json', encoded(resource_sources)))
    policy = load_policy(public_root)
    policy_ref = proposal.bind('public', descriptor(public_root, public_root / POLICY_PATH))
    for name in ('standards','invitation','protocol'):
        proposal.bind('public', policy[name])
    catalog = public_root / 'cases/catalog.json'
    proposal.bind('public', descriptor(public_root, catalog))
    for item in source['base_reports'].values():
        proposal.bind('private', item)
    for conditions in source['public_base_reports'].values():
        for item in conditions.values():
            proposal.bind('public', item)
    private_record = proposal.bind('private', descriptor(private_root, private_root / source['source_record']['path']))
    proposal.bind('public', source['source_record'])
    inputs = dict(schema='math-gauge.neutral-revision-inputs/v1', version=VERSION,
        benchmark_version=TARGET, source_scoring_edition=SOURCE, attempt_condition=CONDITION,
        model_id=mid, record_id=source['record_id'], model_label=source['reports']['partial']['model_label'],
        source_record=private_record, policy=policy_ref, base_reports=source['base_reports'], rows=rows,
        study_sources=study_sources, post_observation=True, original_bytes_rewritten=False,
        reviewer_kind='ai', human_review='pending', formal_comparison_eligible=False, adoption_new_candidate_calls=0)
    inputs_ref = proposal.add('private', base + '/inputs.json', inputs)
    return dict(model_id=mid, destination=base, source=source, inputs_ref=inputs_ref,
                resource_ref=resource_ref, rows=rows, policy_ref=policy_ref,
                physical_requests=companion['models'][0]['revision']['physical_requests'])


def prepare(public_root, private_root, run_root, destination, *, reviews=None, models=None):
    public_root, private_root, run_root, destination = (Path(path).resolve() for path in
        (public_root, private_root, run_root, destination))
    require(not destination.exists() and not destination.is_relative_to(public_root)
            and not destination.is_relative_to(private_root), 'Preparation needs a new disposable directory outside both repositories')
    runtime = json.loads((run_root / 'runtime-freeze.json').read_bytes())
    cells = runtime['cells']
    known_models = sorted({row['model_id'] for row in cells})
    transition = load_transition(public_root)
    require(transition is not None, 'Batch adoption extends the existing source-bound 1.2 transition')
    selected_ids = current_model_ids(transition)
    models = sorted(set(known_models) & selected_ids) if models is None else list(models)
    require(set(models) <= selected_ids, 'Model is outside the selected assessment edition')
    require(len(models) == len(set(models)) and set(models) <= set(known_models), 'Model is outside the frozen batch')
    sealed = json.loads((run_root / 'sealed-deliveries.json').read_bytes())
    require(external_bytes(sealed['runtime_freeze']) == (run_root / 'runtime-freeze.json').read_bytes(),
            'Sealed discovery index binds another runtime')
    locked = load_review_selection(reviews, run_root / 'runtime-freeze.json')
    lock_raw = None if locked is None else Path(reviews).read_bytes()
    require(locked is None or json.loads(lock_raw) == locked, 'Final review selection changed while reading')
    lock_ref = None if locked is None else dict(path=str(Path(reviews).resolve()), bytes=len(lock_raw), sha256=sha(lock_raw))
    selected = {} if locked is None else locked['rows']
    proposal = Proposal(public_root, private_root)
    proposal.bind('public', transition['source_edition'])
    report = dict(schema='math-gauge.neutral-revision-batch-proposal/v1', candidate_calls=0,
        prepared_only=True, run_root=str(run_root), runtime_sha256=sha((run_root / 'runtime-freeze.json').read_bytes()),
        benchmark_before_sha256=sha((public_root / 'benchmark.json').read_bytes()),
        resources_index_before_sha256=sha((public_root / INDEX_PATH).read_bytes()) if (public_root / INDEX_PATH).exists() else None,
        models=[], protected_originals=[dict(scope=scope, path=name, sha256=value)
            for (scope,name),value in _guard_existing(public_root, private_root, transition).items()])
    prepared = []
    for mid in models:
        source = load_model_selection(public_root, private_root, mid)
        expected = {row['case_id'] for row in source['selection']}
        frozen = {row['case_id'] for row in cells if row['model_id'] == mid}
        require(expected == frozen, 'Frozen batch differs from the unchanged source selection')
        finals = [row for row in sealed['normal_finals'] + sealed['operational_failures'] if row['model_id'] == mid]
        require(len({row['case_id'] for row in finals}) == len(finals), 'Duplicate closed cell')
        missing_delivery = sorted(expected - {row['case_id'] for row in finals})
        missing_review = sorted(cid for cid in expected if mid + '--' + cid not in selected)
        if mid in transition['adoptions']:
            report['models'].append(dict(model_id=mid, status='already_adopted', selected=len(expected)))
        elif missing_delivery or missing_review:
            report['models'].append(dict(model_id=mid, status='pending', selected=len(expected),
                missing_delivery=missing_delivery, missing_final_review=missing_review))
        else:
            prepared.append(_put_model(proposal, public_root, private_root, run_root, source, finals,
                locked, reviews, lock_raw, {row['id']:row for row in cells}))
            report['models'].append(dict(model_id=mid, status='ready', selected=len(expected)))
    destination.mkdir(parents=True)
    proposal.materialize(destination)
    assessment = json.loads((public_root / 'protocol/scoring-policy.json').read_bytes())
    public_ids = public_assessment_case_ids(assessment)
    new_adoptions, resources = {}, []
    for item in prepared:
        source, base, mid = item['source'], item['destination'], item['model_id']
        validated = load_inputs(destination / 'private', item['inputs_ref'], public_root=destination / 'public', base_reports=source['reports'])
        private_scores, public_scores, full = {}, {}, {}
        for mode in MODES:
            score = score_neutral_revision_overlay(source['reports'][mode], assessment, revision=validated, mode=mode)
            full[mode] = score
            private_scores[mode] = proposal.add('private', base + '/' + mode + '-' + CONDITION + '.json', score)
            projected = project_score(score)
            projected['source_bindings']['private_report_sha256'] = private_scores[mode]['sha256']
            public_scores[mode] = proposal.add('public', base + '/' + mode + '-' + CONDITION + '.json', projected)
        private_ref = proposal.add('private', base + '/private.json', dict(schema='math-gauge.neutral-revision-private/v1',
            version=VERSION, benchmark_version=TARGET, model_id=mid, record_id=source['record_id'],
            inputs=item['inputs_ref'], scores=private_scores))
        tasks = proposal.add('public', base + '/public-tasks.json', project_public_tasks(full, public_ids,
            {mode:private_scores[mode]['sha256'] for mode in MODES}))
        continuations = []
        private_ids = {row['case_id'] for row in source['reports']['partial']['tasks']} - set(public_ids)

        def public_original(name, original):
            raw = proposal.new['private'][original['path']]
            require(not any(cid.encode() in raw for cid in private_ids),
                    'Private task identifiers cannot enter a public continuation original')
            return proposal.add('public', name, raw)

        for row in item['rows']:
            if row['case_id'] not in public_ids or row['continuation']['status'] != 'reviewed':
                continue
            case = dict(case_id=row['case_id'], attachments=[])
            for key, name in (('input','input.md'),('answer','answer.md'),('review','review.json')):
                original = row['continuation'][key]
                case[key] = public_original(base + '/public-continuations/' + row['case_id'] + '/' + name, original)
            for attached in row['continuation']['attachments']:
                case['attachments'].append(public_original(base + '/public-continuations/' + row['case_id'] + '/' + Path(attached['path']).name, attached))
            continuations.append(case)
        public_ref = proposal.add('public', base + '/public.json', dict(schema='math-gauge.neutral-revision-public/v1',
            version=VERSION, benchmark_version=TARGET, source_scoring_edition=SOURCE, attempt_condition=CONDITION,
            model_id=mid, record_id=source['record_id'], source_record=source['source_record'], policy=item['policy_ref'],
            base_reports=source['public_base_reports'], scores=public_scores, public_tasks=tasks,
            public_continuations=continuations, private_inputs_sha256=item['inputs_ref']['sha256'],
            private_manifest_sha256=private_ref['sha256'], revision_resources=item['resource_ref'],
            revision_counts=dict(selected=len(item['rows']), reviewed=sum(row['continuation']['status']=='reviewed' for row in item['rows']),
                delivery_failed=sum(row['continuation']['status']=='delivery_failed' for row in item['rows']), pending=0,
                source_new_calls=item['physical_requests'], reused_neutral_calls=0), post_observation=True,
            reviewer_kind='ai', human_review='pending', formal_comparison_eligible=False, adoption_new_candidate_calls=0))
        proposal.materialize(destination)
        verify_pair(destination / 'public', destination / 'private', public_ref, private_ref,
                    base_reports=source['reports'], assessment_policy=assessment)
        new_adoptions[mid] = public_ref
        resources.append(item['resource_ref'])
        next(row for row in report['models'] if row['model_id']==mid)['scores'] = {
            mode:full[mode]['metrics']['earned']['confirmed'] for mode in MODES}
    if prepared:
        if (public_root / INDEX_PATH).exists():
            resource_index = json.loads((public_root / INDEX_PATH).read_bytes())
        else:
            resource_index = dict(schema='math-gauge.neutral-revision-resources-index/v1', version='0.1.0',
                benchmark_version=TARGET, sources=[descriptor(public_root, public_root / DATA_PATH)])
        for source in resource_index['sources']:
            proposal.bind('public', source)
        resource_index['sources'].extend(resources)
        proposal.add('public', INDEX_PATH, resource_index)
        updated = {key:deepcopy(value) for key,value in transition.items() if not key.startswith('_')}
        updated['adoptions'].update(new_adoptions)
        updated['pending_models'] = sorted(set(updated['pending_models']) - set(new_adoptions))
        transition_ref = proposal.add('public', TRANSITION_PATH, updated)
        edition = json.loads((public_root / 'benchmark.json').read_bytes())
        edition['neutral_revision_transition'] = transition_ref
        proposal.add('public', 'benchmark.json', edition)
        proposal.materialize(destination)
        load_resources(destination / 'public')
    report['artifacts'] = {scope:[ref(name,raw) for name,raw in sorted(proposal.new[scope].items())]
                           for scope in ('public','private')}
    report['new_models'] = sorted(new_adoptions)
    if lock_ref is not None:
        require(external_bytes(lock_ref) == lock_raw, 'Final review selection changed during preparation; prepare again')
    report['review_selection'] = lock_ref
    (destination / 'proposal.json').write_bytes(encoded(report))
    return report


def adopt(public_root, private_root, proposal_root):
    """Publish a verified proposal locally, with the edition pointer written last."""
    public_root, private_root, proposal_root = (Path(path).resolve() for path in
        (public_root, private_root, proposal_root))
    report = json.loads((proposal_root / 'proposal.json').read_bytes())
    require(report.get('schema') == 'math-gauge.neutral-revision-batch-proposal/v1'
            and report.get('candidate_calls') == 0 and report.get('prepared_only') is True,
            'Expected a validated prepare-only proposal')
    require(sha((public_root / 'benchmark.json').read_bytes()) == report['benchmark_before_sha256'],
            'Current adoption state changed; prepare again without model calls')
    current_index = sha((public_root / INDEX_PATH).read_bytes()) if (public_root / INDEX_PATH).exists() else None
    require(current_index == report['resources_index_before_sha256'], 'Resource index changed after preparation')
    if not report['new_models']:
        return dict(adopted_models=[], candidate_calls=0, status='no_complete_reviewed_models')
    require(report['review_selection'] is not None, 'Adoption requires the actual final review lock')
    external_bytes(report['review_selection'])
    roots = dict(public=public_root, private=private_root)
    for old in report['protected_originals']:
        require(sha((roots[old['scope']] / old['path']).read_bytes()) == old['sha256'],
                'An existing adoption or original resource companion changed')
    # Reuse the owning consumers at the write boundary before advancing state.
    proposed_transition = json.loads((proposal_root / 'public' / TRANSITION_PATH).read_bytes())
    current_transition = load_transition(public_root)
    require(set(report['new_models']) <= current_model_ids(current_transition)
            and proposed_transition.get('withdrawn_models', []) == current_transition.get('withdrawn_models', []),
            'Adoption must preserve the explicitly selected assessment model set')
    load_transition(proposal_root / 'public')
    assessment = json.loads((public_root / 'protocol/scoring-policy.json').read_bytes())
    load_review_selection(report['review_selection']['path'], Path(report['run_root']) / 'runtime-freeze.json')
    for mid in report['new_models']:
        source = load_model_selection(public_root, private_root, mid)
        public_ref = proposed_transition['adoptions'][mid]
        private_ref = descriptor(proposal_root / 'private',
            proposal_root / 'private' / Path(public_ref['path']).parent / 'private.json')
        verify_pair(proposal_root / 'public', proposal_root / 'private', public_ref, private_ref,
                    base_reports=source['reports'], assessment_policy=assessment)
    load_resources(proposal_root / 'public')
    mutables = {INDEX_PATH, TRANSITION_PATH, 'benchmark.json'}
    for scope in ('private','public'):
        for item in report['artifacts'][scope]:
            raw = read(proposal_root / scope, item)
            if scope == 'public' and item['path'] in mutables:
                continue
            target = roots[scope] / item['path']
            require(not target.exists() or target.read_bytes() == raw, 'Existing immutable adoption output differs')
            target.parent.mkdir(parents=True, exist_ok=True)
            if not target.exists():
                target.write_bytes(raw)
    for name in (INDEX_PATH, TRANSITION_PATH, 'benchmark.json'):
        item = next(item for item in report['artifacts']['public'] if item['path']==name)
        raw = read(proposal_root / 'public', item)
        target = public_root / name
        temporary = target.with_suffix(target.suffix + '.new')
        temporary.parent.mkdir(parents=True, exist_ok=True)
        temporary.write_bytes(raw)
        temporary.replace(target)
    current = load_transition(public_root)
    for mid in report['new_models']:
        public_ref = current['adoptions'][mid]
        private_ref = descriptor(private_root, private_root / Path(public_ref['path']).parent / 'private.json')
        source = load_model_selection(public_root, private_root, mid)
        verify_pair(public_root, private_root, public_ref, private_ref,
                    base_reports=source['reports'], assessment_policy=assessment)
    load_resources(public_root)
    for old in report['protected_originals']:
        require(sha((roots[old['scope']] / old['path']).read_bytes()) == old['sha256'],
                'An original adoption/resource file was modified')
    return dict(adopted_models=report['new_models'], candidate_calls=0, status='adopted_locally')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action', choices=('prepare','adopt'))
    parser.add_argument('--public-root', type=Path, default=ROOT)
    parser.add_argument('--private-root', type=Path, required=True)
    parser.add_argument('--run-root', type=Path)
    parser.add_argument('--reviews', type=Path)
    parser.add_argument('--out', type=Path, required=True, help='Disposable proposal directory, or prepared directory for adopt')
    parser.add_argument('--model', action='append')
    args = parser.parse_args()
    try:
        if args.action == 'prepare':
            require(args.run_root is not None, 'prepare requires --run-root')
            result = prepare(args.public_root, args.private_root, args.run_root, args.out,
                             reviews=args.reviews, models=args.model)
        else:
            result = adopt(args.public_root, args.private_root, args.out)
    except (ValueError, OSError, KeyError) as error:
        parser.error(str(error))
    print(json.dumps(result, ensure_ascii=False, indent=2))


if __name__ == '__main__':
    main()
