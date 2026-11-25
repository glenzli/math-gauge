"""Reuse explicitly accepted Carbon strict-taste leaves under their own parent.

Original reviews, catalog, policy and old aggregate remain immutable. This
adapter authenticates a separately audited source addition, translates only the
recorded neutral-revision stage name, and uses the existing six-family scorer.
"""
import json
from pathlib import Path

from . import independent_research_admitted_delivery as admitted
from . import legacy_taste as legacy
from . import legacy_taste_strict as strict
from .mathematical_profile import source_bytes

SCHEMA = 'math-gauge.legacy-taste-source-addition/v1'
MODEL = admitted.MODEL
PUBLIC_PATH = admitted.PUBLIC_PATH.with_name('gemini-4-carbon-medium-legacy-taste.json')
REUSE_AUDIT_SHA256 = '16d1a66bdf1adc273bdaa733020628b518ee6668ea39e8f154402ee3f2cfbdde'
_BASE_FIELDS = ('model_id', 'stage', 'case_id', 'response_sha256', 'assessment_status', 'score', 'enough_evidence',
                'reason', 'valid_scope', 'choice_value', 'condition_cost', 'evidence')
_need, _fields, digest, encoded = admitted._need, admitted._fields, admitted.digest, admitted.encoded


def _pointer(document, pointer):
    for part in pointer.strip('/').split('/'):
        part = part.replace('~1', '/').replace('~0', '~')
        document = document[int(part)] if isinstance(document, list) else document[part]
    return document


def _leaf(row, criteria, checks, material, roots, *, stage):
    """Reuse the original judgment and existing quote validator; no regrading."""
    base = {key: row[key] for key in _BASE_FIELDS}
    _need(base['model_id'] == MODEL and base['stage'] == stage,
          'Taste source addition changed the original model or recorded stage')
    legacy._review_grade(base, material, roots)
    _need(_fields(criteria, strict.DIMENSIONS) and _fields(checks, strict.CHECKS)
          and row.get('unresolved_kind') is None and checks['no_silent_repair'] is True,
          'Accepted strict-taste credit cannot use a repaired or unresolved source')
    points = {}
    for name, maximum in strict.DIMENSIONS.items():
        part = criteria[name]
        _need(_fields(part, ('points', 'reason', 'evidence')) and admitted.modes._text(part['reason'])
              and type(part['points']) is int and 0 <= part['points'] <= maximum,
              'Original strict taste dimension lost its fixed point limit')
        legacy._review_grade(dict(base, evidence=part['evidence']), material, roots)
        points[name] = part['points']
    _need(sum(points.values()) == row['score'] and all(type(v) is bool for v in checks.values())
          and (row['score'] != 100 or all(checks.values()))
          and (points['support'] != 30 or checks['credited_work_closed']),
          'Original strict taste dimensions or proof-level checks do not reconcile')
    return row['score'], points


def prepare(reuse_audit_path, public_root, private_root, parent):
    audit_path = admitted.flow._safe_absolute(reuse_audit_path)
    public_root, private_root = map(admitted.flow._safe_absolute, (public_root, private_root))
    audit_raw = audit_path.read_bytes()
    audit = json.loads(audit_raw)
    _need(digest(audit_raw) == REUSE_AUDIT_SHA256
          and audit['schema'] == 'math-gauge.carbon-legacy-strict-taste-reuse-audit/v1'
          and audit['status'] == 'audit-consistent-reuse-original-proposals-no-new-grades'
          and audit['model_id'] == MODEL and audit['edition'] == '1.3.0'
          and audit['condition'] == legacy.CONDITION and audit['human_review'] == 'pending'
          and audit['fixed_families'] == 6 and len(audit['actual_revisions']) == 4
          and audit['new_taste_grades_created'] == audit['new_candidate_calls'] == 0
          and all(audit[k] is True for k in ('current_catalog_reproduced_by_existing_owner',
              'original_first_sources_unchanged', 'original_revision_null_not_overwritten')),
          'Need the exact independently checked, Root-accepted four-proposal reuse audit')
    roots = dict(public=public_root, private=private_root, temporary=audit_path.parent)
    def read(ref):
        _need(ref['repository'] in roots, 'Unknown original taste source repository')
        return source_bytes(roots[ref['repository']], ref)
    parent_raw, _ = admitted.baseline(public_root, parent)
    _need(digest(parent_raw) == audit['new_baseline']['sha256'], 'Taste addition requires its exact actual1.2 parent')
    base_policy, base_sha = legacy.load_policy(public_root/legacy.POLICY_PATH)
    policy, policy_sha = strict.load_policy(public_root/strict.POLICY_PATH)
    _need(policy_sha == audit['policy']['sha256'] and base_sha == audit['base_scope_policy']['sha256']
          and policy['private_standard_sha256'] == audit['private_standard']['sha256'],
          'Taste reuse changed its actual strict criterion')
    for key in ('policy', 'private_standard', 'base_scope_policy', 'private_scope', 'adopted_neutral_inputs'):
        read(audit[key])
    catalog_raw = read(audit['current_source_catalog'])
    catalog = json.loads(catalog_raw)
    # Rebuild through the existing selected-source owner. A saved catalog alone
    # is never enough to make an older answer follow a new parent.
    rebuilt = legacy.build_source_catalog(public_root, private_root, read(audit['private_scope']), base_policy, parent_raw)
    _need(rebuilt == catalog and digest(catalog_raw) == audit['current_source_catalog']['sha256'],
          'Current selected taste sources differ from the original reuse audit')
    old_catalog = json.loads(read(audit['retained_original_source_catalog']))
    model = catalog['models'][MODEL]
    _need(model['first'] == old_catalog['models'][MODEL]['first']
          and all(value == catalog['models'].get(mid) for mid, value in old_catalog['models'].items() if mid != MODEL),
          'A model addition cannot change retained first answers or other model catalogs')
    scores = {}
    for point in audit['retained_first_judgment_pointers']:
        source = json.loads(read(point['review']))
        row = _pointer(source, point['judgment_pointer'])
        _need(row['case_id'] == point['case_id'] and row['response_sha256'] == point['response_sha256'],
              'Changed original first-answer strict-taste source')
        score, _ = _leaf(row, row['criteria'], row['strict_checks'], model['first'][row['case_id']], roots, stage='first')
        scores[(MODEL, 'first', row['case_id'])] = score
    _need(len(scores) == 6, 'Retain all six first-answer families')
    proposals = []
    for point in audit['actual_revisions']:
        original_raw, root_raw = read(point['original_proposal']), read(point['root_adjudication'])
        original, root = json.loads(original_raw), json.loads(root_raw)
        _need(all(original[k] == v for k, v in legacy.REVIEWER.items())
              and original['policy_sha256'] == policy_sha
              and original['private_standard_sha256'] == policy['private_standard_sha256']
              and original['reviewer_id'] == point['original_reviewer_id']
              and point['root_explicitly_accepted_taste_separately_from_profile'] is True,
              'Original proposal or actual independent AI attribution changed')
        row = _pointer(original, point['original_judgment_pointer'])
        criteria = _pointer(original, point['criteria_pointer'])
        checks = _pointer(original, point['strict_checks_pointer'])
        material = model['revision'][point['case_id']]
        _need(row['case_id'] == point['case_id'] and point['target_model_id'] == MODEL
              and point['target_stage'] == 'revision' and point['first_response_sha256'] == material['first_response_sha256']
              and point['answer'] == material['evidence']['answer'], 'Taste proposal has a different adopted same-parent final')
        score, dimensions = _leaf(row, criteria, checks, material, roots, stage=point['original_stage'])
        accepted = _pointer(root, point['root_taste_pointer'])
        _need(accepted == dict(score=score,criteria=dimensions,checks=checks)
              and score == point['original_score'], 'Root acceptance did not independently select the exact taste leaf')
        key = (MODEL, 'revision', point['case_id'])
        _need(key not in scores, 'Duplicate adopted taste revision')
        scores[key] = score
        proposals.append(digest(original_raw))
    metrics = legacy._model_metrics(MODEL, model, scores, base_policy)
    original_index_raw = read(audit['retained_original_public_strict_source'])
    original_index = json.loads(original_index_raw)
    _need(metrics['first'] == original_index['models'][MODEL]['first'] == audit['original_first_metric_preserved'],
          'New taste lineage changed the retained first-answer metric')
    _need(audit_path.read_bytes() == audit_raw, 'Reuse audit changed during verification')
    result = dict(schema=SCHEMA,version='0.1.0',edition='1.3.0',condition=legacy.CONDITION,
        source_binding=dict(base_edition='1.2.0',baseline=parent,reuse_audit_sha256=digest(audit_raw),
            source_catalog_sha256=digest(catalog_raw),original_index_sha256=digest(original_index_raw),
            accepted_proposals_sha256=proposals),policy_sha256=policy_sha,base_scope_policy_sha256=base_sha,
        cohort=[MODEL],models={MODEL:metrics},reused_revision_families=4,reviewer_kind='ai',human_review='pending',
        post_observation=True,new_candidate_calls=0,new_mathematical_judgments=0)
    return validate_public(result,parent=parent,policy_sha256=policy_sha)


def validate_public(document, *, parent=None, policy_sha256=None):
    _need(_fields(document, ('schema','version','edition','condition','source_binding','policy_sha256',
          'base_scope_policy_sha256','cohort','models','reused_revision_families','reviewer_kind','human_review',
          'post_observation','new_candidate_calls','new_mathematical_judgments'))
          and document['schema'] == SCHEMA and document['version'] == '0.1.0'
          and document['edition'] == '1.3.0' and document['condition'] == legacy.CONDITION
          and document['cohort'] == [MODEL] and _fields(document['models'], (MODEL,))
          and document['reused_revision_families'] == 4 and document['reviewer_kind'] == 'ai'
          and document['human_review'] == 'pending' and document['post_observation'] is True
          and type(document['new_candidate_calls']) is type(document['new_mathematical_judgments']) is int
          and document['new_candidate_calls'] == document['new_mathematical_judgments'] == 0,
          'Invalid public taste addition or private inventory')
    binding = document['source_binding']
    _need(_fields(binding, ('base_edition','baseline','reuse_audit_sha256','source_catalog_sha256',
          'original_index_sha256','accepted_proposals_sha256')) and binding['base_edition'] == '1.2.0'
          and binding['reuse_audit_sha256'] == REUSE_AUDIT_SHA256
          and (parent is None or binding['baseline'] == parent)
          and all(adoption_hash(v) for v in (document['policy_sha256'],document['base_scope_policy_sha256'],
              binding['source_catalog_sha256'],binding['original_index_sha256']))
          and isinstance(binding['accepted_proposals_sha256'], list) and len(binding['accepted_proposals_sha256']) == 4
          and len(set(binding['accepted_proposals_sha256'])) == 4
          and all(adoption_hash(v) for v in binding['accepted_proposals_sha256'])
          and (policy_sha256 is None or document['policy_sha256'] == policy_sha256),
          'Taste addition lost its exact own-source lineage')
    baseline = binding['baseline']
    _need(_fields(baseline, ('path','bytes','sha256')) and adoption_hash(baseline['sha256'])
          and type(baseline['bytes']) is int and baseline['bytes'] >= 0
          and baseline['path'] == f'results/independent-research-baselines/v0.1.0/{baseline["sha256"]}/data.json',
          'Taste addition parent must be a public immutable aggregate source')
    row = document['models'][MODEL]
    _need(_fields(row, ('first','revision')) and row['revision'] is not None, 'Taste addition needs its own selected revision stage')
    for metric in row.values(): legacy._validate_metric(metric)
    return document


adoption_hash = admitted.adoption._is_hash
