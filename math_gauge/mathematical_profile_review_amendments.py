"""Independent TX source-review corrections to current profile traits.

No research tier is converted into a profile grade. Retained task judgments,
the common profile contract and the exact original answer authenticate the
separately adjudicated grades before scoring.py recomputes either stage.
"""
from copy import deepcopy
import hashlib
import json
from pathlib import Path

from .mathematical_profile_corrections import BaselineCorrectionInputs
from .mathematical_profile import source_bytes, load_policy
from .theorem_extension_calibration import require

DIRECTORY='results/mathematical-profile-review-amendments/v0.1.0'
INDEX_PATH=DIRECTORY+'/index.json'
MODEL='astra-6.2-xhigh'
SLOT='MG-TX002:A1'


def read(roots,ref):
    require(ref.get('repository') in roots,'Unknown profile-review correction source scope')
    return source_bytes(roots[ref['repository']],ref)


class ProfileReviewAmendmentInputs(BaselineCorrectionInputs):
    corrected_axes=frozenset({'depth','initiative'})

    def __init__(self,raw,*,roots):
        roots={key:Path(value).resolve() for key,value in roots.items()}
        data=json.loads(raw)
        require(data.get('schema')=='math-gauge.mathematical-profile-review-amendment/v1'
                and data.get('version')=='0.1.0' and data.get('model_id')==MODEL
                and data.get('slot_id')==SLOT and data.get('new_candidate_calls')==0
                and data.get('reviewer_kind')=='ai' and data.get('human_review')=='pending'
                and data.get('independent_profile_assessment') is True
                and data.get('original_bytes_rewritten') is False,
                'Invalid independent profile review amendment')
        policy,digest=load_policy(roots['public'])
        sources=data['sources']
        require(sources['policy']['sha256']==digest,'Profile amendment changed the scoring rubric')
        loaded={key:json.loads(read(roots,ref)) for key,ref in sources.items()}
        base_index=json.loads((Path(roots['private'])/'results/mathematical-profiles/v0.4.0/index.json').read_bytes())
        revision_index=json.loads((Path(roots['private'])/'results/mathematical-profile-revisions/v0.1.0/index.json').read_bytes())
        for alias,key in [('base_review','review'),('base_bindings','source-bindings'),('base_score','score')]:
            require({k:sources[alias][k] for k in ('path','bytes','sha256')}==base_index['models'][MODEL][key],
                    'Profile amendment changed its selected first-answer source')
        for alias,key in [('revision_review','review'),('revision_bindings','source-bindings')]:
            require({k:sources[alias][k] for k in ('path','bytes','sha256')}==revision_index['models'][MODEL][key],
                    'Profile amendment changed its adopted revision review')
        require(sources['contracts']['sha256']==policy['private_contract_sha256'],
                'Profile amendment changed its common task weights')
        original=next(r for r in loaded['base_review']['tasks'] if r['id']==SLOT)
        require(loaded['base_review']['model_id']==MODEL and loaded['base_score']['model_id']==MODEL,
                'Profile amendment borrowed another model review')
        audit=loaded['audit']
        target=next(r for r in audit['rows'] if r['model_id']==MODEL and r['case_id']=='MG-TX002')
        require(target['profile_review']['sha256']==sources['base_review']['sha256']
                and target['read_complete_original'] is True,
                'Profile amendment audit changed its original assessment')
        answer=target['original_answer']
        retained=loaded['base_bindings']['sources']['answer:'+SLOT]
        require(answer['sha256']==retained['sha256'],'Profile amendment changed the actual original answer')
        answer_raw=source_bytes(roots[retained['repository']],retained)
        for quote in target['original_citations']:
            require(answer_raw[quote['start_byte']:quote['end_byte']]==quote['quote'].encode(),
                    'Profile amendment quote does not bind its original answer')
        require({r['model_id'] for r in audit['comparators']}==
                {'astra-6.2-max','astra-6-max','terra-6.1-max','terra-6.1-xhigh'},
                'Profile amendment lost the independently reviewed comparison set')
        for comparator in audit['comparators']:
            ref=dict(comparator['profile_review'])
            ref['path']=Path(ref['path']).relative_to(roots['private']).as_posix()
            require(ref==base_index['models'][comparator['model_id']]['review'],
                    'Profile amendment comparator is not its selected original profile')
            reviewed=json.loads(source_bytes(roots['private'],ref))
            row=next(r for r in reviewed['tasks'] if r['id']==SLOT)
            require(reviewed['model_id']==comparator['model_id'] and comparator['read_complete_original'] is True
                    and all(row['axes'][a]['grade']==4 for a in self.corrected_axes),
                    'Profile amendment comparator does not support the stated common scale')
        axes=data['axes']
        require(set(axes)==self.corrected_axes,'Profile amendment changed unreviewed traits')
        for axis,before in [('depth',2),('initiative',0)]:
            require(axes[axis]['from']==original['axes'][axis]['grade']==before
                    and axes[axis]['to']==4 and isinstance(axes[axis].get('reason'),str)
                    and axes[axis]['reason'].strip(),
                    'Profile amendment does not match its independently accepted judgment')
        self.rows=[dict(model_id=MODEL,id=SLOT,axes=deepcopy(axes))]
        self.contracts=loaded['contracts']
        self.data=deepcopy(data)
        self.sha256=hashlib.sha256(raw).hexdigest()


def apply_public(root,data):
    """Select source-bound corrected traits only for the current 1.2 display."""
    root=Path(root)
    if data.get('benchmark_version')!='1.2.0' or not (root/INDEX_PATH).is_file():
        return
    index=json.loads((root/INDEX_PATH).read_bytes())
    fields={'schema','version','benchmark_version','model_id','reviewer_kind','human_review',
        'independent_profile_assessment','new_candidate_calls','main_scores_modified','source_first_profile',
        'source_revision_profile','private_adoption_sha256','private_score_sha256','metrics'}
    require(set(index)==fields and index.get('schema')=='math-gauge.mathematical-profile-review-amendment-public/v1'
            and index.get('model_id')==MODEL and index.get('new_candidate_calls')==0
            and index.get('benchmark_version')=='1.2.0' and index.get('main_scores_modified') is False
            and index.get('human_review')=='pending' and index.get('independent_profile_assessment') is True,
            'Invalid public profile-review correction')
    for key in ('source_first_profile','source_revision_profile'):
        source_bytes(root,index[key])
    for kind,key in [('mathematical-profiles/v0.4.0','source_first_profile'),
                     ('mathematical-profile-revisions/v0.1.0','source_revision_profile')]:
        parent=json.loads((root/'results'/kind/'index.json').read_bytes())
        require(parent['models'][MODEL]==index[key],'Profile correction changed its selected source profile')
    require(set(index['metrics'])=={'first','revision'} and all(
        set(index['metrics'][s])==ProfileReviewAmendmentInputs.corrected_axes for s in ('first','revision')),
        'Profile correction changed an unreviewed axis')
    for axis in ProfileReviewAmendmentInputs.corrected_axes:
        for stage in ('first','revision'):
            metric=index['metrics'][stage][axis]
            require(set(metric)=={'exact','confirmed','lower','upper','unknown_weight','coverage'}
                    and metric['coverage']==dict(unit='mathematical_family',planned=35,reviewed=35)
                    and metric['lower']<=metric['confirmed']<=metric['upper']
                    and metric['exact']==metric['confirmed'] and 0<=metric['exact']<=100,
                    'Profile correction changed its scale or coverage')
    require(index['metrics']['first']['initiative']==index['metrics']['revision']['initiative'],
            'Research initiative must remain first-answer-only')
    ref=dict(path=INDEX_PATH,bytes=(root/INDEX_PATH).stat().st_size,
        sha256=hashlib.sha256((root/INDEX_PATH).read_bytes()).hexdigest())
    for key,stage in [('mathematical_profile','first'),('mathematical_profile_baseline','first'),
                      ('mathematical_profile_revision','revision')]:
        profile=data.get(key)
        if profile is None:
            continue
        row=next((r for r in profile['models'] if r['id']==MODEL),None)
        if row is not None:
            for axis in ProfileReviewAmendmentInputs.corrected_axes:
                row['metrics'][axis]=deepcopy(index['metrics'][stage][axis])
            row['profile_review_amendment']=ref
    data['sources'].append(ref)
