#!/usr/bin/env python3
"""Adopt/check a separately adjudicated profile correction without candidate calls."""
from pathlib import Path
import argparse,hashlib,json,sys

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from math_gauge.mathematical_profile_review_amendments import (
    DIRECTORY,INDEX_PATH,MODEL,ProfileReviewAmendmentInputs,
)
from math_gauge.mathematical_profile import source_bytes
from math_gauge.mathematical_profile_revision import RevisionProfileInputs,load_policy
from math_gauge.scoring import score_mathematical_profile_baseline_corrections,score_mathematical_profile_revisions
from math_gauge.neutral_revision import descriptor,document,read,require


def write(root,path,value):
    raw=value if isinstance(value,bytes) else (json.dumps(value,ensure_ascii=False,indent=2)+'\n').encode()
    target=Path(root)/path
    require(not target.exists() or target.read_bytes()==raw,'Refusing to replace profile correction evidence')
    target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(raw)
    return descriptor(root,target)


def derive(p,q,raw):
    roots=dict(public=Path(p),private=Path(q))
    correction=ProfileReviewAmendmentInputs(raw,roots=roots)
    source=correction.data['sources']
    first=score_mathematical_profile_baseline_corrections(
        json.loads(source_bytes(q,source['base_score'])),correction,model_id=MODEL)
    review=json.loads(source_bytes(q,source['revision_review']))
    material_raw=source_bytes(q,source['revision_bindings']);materials=json.loads(material_raw)
    policy,digest=load_policy(p)
    revision=RevisionProfileInputs(review,materials,roots=roots,policy=policy,policy_sha256=digest,
        materials_sha256=hashlib.sha256(material_raw).hexdigest(),corrections=correction)
    revised=score_mathematical_profile_revisions(revision)
    return correction,first,revised


def prepare(p,q,adoption):
    raw=Path(adoption).read_bytes();c,first,revised=derive(p,q,raw)
    adopted=write(q,DIRECTORY+'/adoption.json',raw)
    full={stage:write(q,DIRECTORY+'/'+stage+'.json',score) for stage,score in [('first',first),('revision',revised)]}
    source=c.data['sources']
    public=dict(schema='math-gauge.mathematical-profile-review-amendment-public/v1',version='0.1.0',
        benchmark_version='1.2.0',model_id=MODEL,reviewer_kind='ai',human_review='pending',
        independent_profile_assessment=True,new_candidate_calls=0,main_scores_modified=False,
        source_first_profile={k:source['base_public_profile'][k] for k in ('path','bytes','sha256')},
        source_revision_profile={k:source['revision_public_profile'][k] for k in ('path','bytes','sha256')},
        private_adoption_sha256=adopted['sha256'],private_score_sha256={k:v['sha256'] for k,v in full.items()},
        metrics={stage:{axis:score['metrics'][axis] for axis in c.corrected_axes}
            for stage,score in [('first',first),('revision',revised)]})
    write(p,INDEX_PATH,public)
    write(q,INDEX_PATH,dict(schema='math-gauge.mathematical-profile-review-amendment-private/v1',
        adoption=adopted,scores=full,public_projection=descriptor(p,Path(p)/INDEX_PATH)))
    return check(p,q)


def check(p,q):
    private=json.loads((Path(q)/INDEX_PATH).read_bytes());public=document(p,private['public_projection'])
    raw=read(q,private['adoption']);c,first,revised=derive(p,q,raw)
    require(private['adoption']['sha256']==public['private_adoption_sha256'],'Profile amendment adoption differs')
    for stage,score in [('first',first),('revision',revised)]:
        require(document(q,private['scores'][stage])==score
                and private['scores'][stage]['sha256']==public['private_score_sha256'][stage]
                and public['metrics'][stage]=={a:score['metrics'][a] for a in c.corrected_axes},
                'Profile amendment differs from its shared source scorer')
    return dict(model_id=MODEL,corrected_tasks=1,corrected_axis_judgments=2,new_candidate_calls=0)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action',choices=['prepare','check']);parser.add_argument('--private-root',type=Path,required=True)
    parser.add_argument('--adoption',type=Path)
    args=parser.parse_args()
    print(json.dumps(prepare(ROOT,args.private_root,args.adoption) if args.action=='prepare'
                     else check(ROOT,args.private_root),ensure_ascii=False))


if __name__=='__main__':main()
