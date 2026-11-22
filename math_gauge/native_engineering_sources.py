"""Explicit post-observation engineering inputs for original native deliveries.

The mathematical input projection is not a CLI execution freeze or old grade.
Private inputs stay private; existing kernel/alignment/scoring owners retain
all judgments and arithmetic. The record owner only composes this source gate.
"""
import copy
import hashlib
import json
import re

SCHEMA = 'math-gauge.native-engineering-assessment-sources/v1'
PUBLIC_SCHEMA = 'math-gauge.native-engineering-assessment-sources-public/v1'
MODES = {'capability':'capability_results','partial':'assessment_results','strict':'strict_results'}
CONDITIONS = {'single_attempt','nonlogical_retry_3'}


def require(value, message):
    if not value:
        raise ValueError(message)


def _hash(value):
    return isinstance(value,str) and re.fullmatch(r'[0-9a-f]{64}',value) is not None


def validate(root, record, *, engineering_root=None):
    from .records import evidence_bytes
    source = json.loads(evidence_bytes(root,record['native_engineering_sources']))
    return validate_sources(root,record,source,engineering_root=engineering_root,evidence=evidence_bytes)


def validate_sources(root, record, source, *, engineering_root=None, evidence=None):
    from .records import evidence_bytes
    from .native_assessment_sources import SCHEMA as FIRST, PUBLIC_SCHEMA as PUBLIC_FIRST
    evidence = evidence or evidence_bytes
    document = lambda ref:json.loads(evidence(root,ref))
    common = {'schema','version','model_id','model_label','source_benchmark_version',
        'mathematical_inputs_kind','post_observation','execution_freeze_claimed',
        'mathematical_judgments_changed','reviewer_kind','human_review',
        'formal_comparison_eligible','new_candidate_calls','engineering_review','reports'}
    require(source.get('schema') in {SCHEMA,PUBLIC_SCHEMA}
            and source.get('version')=='0.1.0' and source.get('model_id')==record.get('model_id')
            and source.get('model_label')==record.get('model',{}).get('requested_label')
            and source.get('source_benchmark_version')==record.get('benchmark_version')=='1.0.0'
            and source.get('mathematical_inputs_kind')=='post_observation_evaluator_projection'
            and source.get('post_observation') is True and source.get('execution_freeze_claimed') is False
            and source.get('mathematical_judgments_changed') is False
            and source.get('reviewer_kind')=='ai' and source.get('human_review')=='pending'
            and source.get('formal_comparison_eligible') is False and source.get('new_candidate_calls')==0
            and source.get('engineering_review')==record.get('formalization_review'),
            'Native engineering sources changed their actual model, scope or observation identity')
    first = document(record['first_assessment_source'])
    public = source['schema']==PUBLIC_SCHEMA
    require(first.get('schema')==(PUBLIC_FIRST if public else FIRST)
            and first.get('model_id')==record.get('model_id'),
            'Native engineering sources require their explicit native first-assessment provenance')
    require(set(source.get('reports',{}))==CONDITIONS and all(
            set(source['reports'][c])==set(MODES) and all(source['reports'][c][m]==record[f][c]
                for m,f in MODES.items()) for c in CONDITIONS),
            'Native engineering sources changed their two-condition three-mode reports')
    if public:
        require(set(source)==common|{'private_source_sha256','scoring_inputs_sha256',
            'source_math_policy_sha256','alignment_review_sha256','selected_alignment_review_sha256',
            'private_report_sha256'}
            and record.get('scope')=='public-answers-and-combined-aggregates'
            and record.get('formalization_evidence_location') is None
            and source.get('private_source_sha256')==record.get('native_engineering_sources_private_sha256')
            and all(_hash(source.get(k)) for k in ('private_source_sha256','scoring_inputs_sha256',
                'source_math_policy_sha256','alignment_review_sha256'))
            and set(source.get('selected_alignment_review_sha256',{}))==CONDITIONS
            and all(_hash(v) for v in source['selected_alignment_review_sha256'].values())
            and set(source.get('private_report_sha256',{}))==CONDITIONS,
            'Public native engineering must retain only opaque private mathematical inputs')
        review=document(source['engineering_review'])
        require(review.get('model_label')==source['model_label']
                and review.get('policy_sha256')==source['source_math_policy_sha256'],
                'Public engineering review changed its source policy/model')
        for c in CONDITIONS:
            require(set(source['private_report_sha256'][c])==set(MODES),
                    'Public native engineering lost one of its private report hashes')
            for m in MODES:
                report=document(source['reports'][c][m]);b=report.get('source_bindings',{})
                require(_hash(source['private_report_sha256'][c][m])
                        and b.get('private_report_sha256')==source['private_report_sha256'][c][m]
                        and b.get('engineering_review_sha256')==source['engineering_review']['sha256']
                        and all(b.get(k)==source[k] for k in ('scoring_inputs_sha256',
                            'source_math_policy_sha256','alignment_review_sha256')),
                        'Public native engineering report lost its opaque source bindings')
        return dict(public_projection=True,private_validation_required=True,report_views=6)
    require(set(source)==common|{'scoring_inputs','source_math_policy','alignment_review',
            'selected_alignment_reviews'} and record.get('scope')!='public-answers-and-combined-aggregates',
            'Full native engineering mathematical inputs belong to the private source archive')
    from . import records,scoring,submission_evidence,agy_evidence
    location=record.get('formalization_evidence_location','local')
    require(location in {'local','public_archive'},'Unknown native engineering source location')
    require(location!='public_archive' or engineering_root is not None,
            'Native private engineering needs its explicitly selected public source root')
    eroot=engineering_root if location=='public_archive' else root
    inputs=document(source['scoring_inputs']);policy=document(source['source_math_policy'])
    alignment=document(source['alignment_review'])
    engineering=json.loads(evidence(eroot,source['engineering_review']))
    require(inputs.get('model_label')==source['model_label']
            and policy.get('version')=='0.4.0'
            and alignment.get('scoring_version')==policy['version']
            and alignment.get('model_label')==engineering.get('model_label')==source['model_label']
            and alignment.get('policy_sha256')==engineering.get('policy_sha256')==source['source_math_policy']['sha256'],
            'Native engineering inputs/alignment/review changed their mathematical source policy')
    compiled=records.validate_formalization_review(eroot,inputs,engineering)
    substitutions=scoring.formalization_substitutions(inputs,engineering)
    retained={r['id']:r for r in record['records']}
    for case in engineering['cases']:
        row=retained.get(case['slot_id'])
        require(row is not None and row.get('case_id')==case['case_id']
                and row.get('kind')=='independent' and row.get('parent_id') is None
                and (row.get('response') or {}).get('sha256')==case.get('original_response_sha256')
                and row.get('agy_native_evidence') is not None,
                'Native engineering borrowed an engineering answer from another case or round')
        native=document(row['agy_native_evidence'])
        from .agy_native_sources import SCHEMA as NATIVE
        require(native.get('schema')==NATIVE and native.get('phase')=='A1'
                and native.get('case_id')==case['case_id']
                and agy_evidence.validate_delivery(root,row,evidence).get('delivered') is True,
                'Native engineering requires the actual normal own-A1 sealed delivery')
    assessment=document(record['assessment_policy']);strict=document(record['strict_scoring_policy'])
    capability=document(record['capability_scoring_policy']);claimpolicy=document(record['claim_penalty_policy'])
    tx=records.load_theorem_extension_inputs(root,record,policy=assessment.get('theorem_extension'))
    bg=records.load_background_check_inputs(root,record,policy=assessment.get('background_check'))
    mc=records.load_manuscript_completion_inputs(root,record,policy=assessment.get('manuscript_completion'))
    archive=document(record['submission_evidence'])
    require(set(source.get('selected_alignment_reviews',{}))==CONDITIONS,
            'Native engineering needs both source-selected alignment reviews')
    for condition in CONDITIONS:
        require(source['selected_alignment_reviews'][condition]==archive['conditions'][condition]['normal_alignment_review'],
                'Native engineering selected alignment from another condition')
        evidence(root,source['selected_alignment_reviews'][condition])
        observed=submission_evidence.load_condition(root,record,condition)
        claims=records.load_claim_review(root,record,condition,public_root=eroot)
        for mode in MODES:
            report=document(source['reports'][condition][mode]);b=report.get('source_bindings',{})
            require(b.get('engineering_review_sha256')==source['engineering_review']['sha256']
                    and all(b.get(k)==source[v]['sha256'] for k,v in (
                        ('scoring_inputs_sha256','scoring_inputs'),
                        ('source_math_policy_sha256','source_math_policy'),
                        ('alignment_review_sha256','alignment_review'))),
                    'Native engineering report changed its actual mathematical input bindings')
            trajectory,_=scoring._alignment_trajectory(observed['normal_alignment'],policy,
                positive_only=mode=='capability',allow_submission_sources=True)
            strict_trajectory=scoring.strict_alignment_trajectory(observed['normal_alignment'],policy,
                allow_submission_sources=True)
            expected=scoring.score_assessment_inputs(inputs,assessment,strict,mode=mode,
                mathematical_substitutions=substitutions,alignment_summary=trajectory,
                strict_trajectory=strict_trajectory,capability_policy=capability,
                claim_review=claims,claim_policy=claimpolicy,
                submission_review=observed,submission_policy=submission_evidence.load_policy(root,record),
                theorem_extension_inputs=tx,background_check_inputs=bg,manuscript_completion_inputs=mc)
            require(all(report.get(k)==v for k,v in expected.items())
                    and report.get('attempt_condition')==condition,
                    'Native engineering report differs from the existing shared scorer')
    return dict(public_projection=False,engineering_cases=compiled['cases'],report_views=6,
                original_sources_repaired=False,mathematical_inputs_kind=source['mathematical_inputs_kind'])


def validate_public_pair(public_root, private_root, public_record, private_record):
    """Use explicit source roots; do not publish or infer complete private inputs."""
    from .records import evidence_bytes,project_assessment_score
    private=json.loads(evidence_bytes(private_root,private_record['native_engineering_sources']))
    public=json.loads(evidence_bytes(public_root,public_record['native_engineering_sources']))
    require(public.get('private_source_sha256')==private_record['native_engineering_sources']['sha256']
            ==public_record.get('native_engineering_sources_private_sha256')
            and public.get('engineering_review')==private.get('engineering_review')
            and all(public.get(k+'_sha256')==private[k]['sha256'] for k in
                    ('scoring_inputs','source_math_policy','alignment_review'))
            and public.get('selected_alignment_review_sha256')=={
                c:private['selected_alignment_reviews'][c]['sha256'] for c in CONDITIONS},
            'Native engineering public projection belongs to different private sources')
    validate_sources(public_root,public_record,public)
    result=validate_sources(private_root,private_record,private,engineering_root=public_root)
    for c in CONDITIONS:
        for m,f in MODES.items():
            raw=json.loads(evidence_bytes(private_root,private_record[f][c]))
            expected=project_assessment_score(raw)
            expected.setdefault('source_bindings',{})['private_report_sha256']=private_record[f][c]['sha256']
            require(json.loads(evidence_bytes(public_root,public_record[f][c]))==expected,
                    'Native engineering public report changed its complete private projection')
    return result
