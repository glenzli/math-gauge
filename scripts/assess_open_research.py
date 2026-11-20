#!/usr/bin/env python3
"""Prepare/check independently reviewed open research capability, without calls."""
import argparse
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from math_gauge.evidence_retention import read_bytes
from math_gauge.open_research import (
    VERSION, EDITION, CONDITION, DIRECTORY, INDEX_PATH, BASE_INDEX, BOUNDARIES,
    ResearchInputs, encoded, reference, load_policy, prepare_materials, project_public,
    load_public, source_bytes,
)


def prepare(root, private_root, reviews):
    from math_gauge.scoring import score_open_research
    root, private_root = Path(root), Path(private_root)
    policy, digest = load_policy(root)
    rel = 'protocol/open-research/v0.1.0/contracts.json'
    contracts_ref = reference(rel, read_bytes(private_root / rel), 'private')
    models = json.loads(read_bytes(root / BASE_INDEX))['models']
    by_model = {}
    for row in reviews:
        by_model.setdefault(row['model_id'], []).append(row)
    if set(by_model) != set(models):
        raise ValueError('Open research must review exactly the current admitted profile cohort')
    public_files, private_files, public_models, private_models = {}, {}, {}, {}
    slot_count = 0
    for mid in models:
        materials = prepare_materials(root, private_root, mid, policy, digest, contracts_ref)
        material_raw = encoded(materials)
        review = dict(schema='math-gauge.open-research-review/v1', version=VERSION,
            benchmark_version=EDITION, condition=CONDITION, model_id=mid,
            policy_sha256=digest, materials_sha256=hashlib.sha256(material_raw).hexdigest(),
            reviewer_id='Fresh gpt-6.1-sol/max independent primary reviewers; root coordinator final source-bound acceptance',
            tasks=sorted(by_model[mid], key=lambda r:(r['stage'],r['case_id'])), **BOUNDARIES)
        review_raw = encoded(review)
        inputs = ResearchInputs(review, materials, public_root=root, private_root=private_root,
                                policy=policy, policy_sha256=digest)
        score = score_open_research(inputs)
        public = project_public(score, policy=policy, policy_sha256=digest,
            review_sha256=hashlib.sha256(review_raw).hexdigest(),
            materials_sha256=hashlib.sha256(material_raw).hexdigest())
        folder = DIRECTORY + '/' + mid
        private_models[mid] = {}
        for name,raw in [('review.json',review_raw),('source-bindings.json',material_raw),
                         ('score.json',encoded(score))]:
            path = folder + '/' + name
            private_files[path] = raw
            private_models[mid][name.removesuffix('.json')] = reference(path,raw)
        path,raw = folder + '/profile.json',encoded(public)
        public_files[path] = raw
        public_models[mid] = reference(path,raw)
        private_models[mid]['public_projection'] = reference(path,raw)
        slot_count += len(review['tasks'])
    common = dict(version=VERSION, benchmark_version=EDITION, condition=CONDITION,
                  policy_sha256=digest, **BOUNDARIES)
    public_files[INDEX_PATH] = encoded(dict(schema='math-gauge.open-research-index/v1',
        models=public_models, **common))
    private_files[INDEX_PATH] = encoded(dict(schema='math-gauge.private-open-research-index/v1',
        models=private_models, **common))
    return public_files, private_files, dict(status='passed',models=len(models),
        independently_reviewed_deliveries=slot_count,new_candidate_calls=0,main_scores_modified=False)


def install(root, private_root, reviews):
    public, private, receipt = prepare(root, private_root, reviews)
    # All sources, mathematics contracts and public projections validate before
    # any file is installed. Existing reviewed payloads are immutable.
    for base,files in [(Path(private_root),private),(Path(root),public)]:
        for name,raw in files.items():
            path=base/name
            if path.exists() and path.read_bytes()!=raw:
                raise ValueError('Refusing to rewrite an adopted research review: '+name)
    for base,files in [(Path(private_root),private),(Path(root),public)]:
        for name,raw in files.items():
            path=base/name
            path.parent.mkdir(parents=True,exist_ok=True)
            if not path.exists():
                path.write_bytes(raw)
    return receipt


def check(root, private_root):
    root,private_root=Path(root),Path(private_root)
    from math_gauge.scoring import score_open_research
    policy,digest=load_policy(root)
    index=json.loads(read_bytes(private_root/INDEX_PATH))
    pub=json.loads(read_bytes(root/INDEX_PATH))
    expected=json.loads(read_bytes(root/BASE_INDEX))['models']
    if set(index['models'])!=set(pub['models']) or set(pub['models'])!=set(expected):
        raise ValueError('Research capability indices differ from the common admitted cohort')
    tasks=0
    for mid,refs in index['models'].items():
        review=json.loads(source_bytes(private_root,refs['review']))
        material_raw=source_bytes(private_root,refs['source-bindings'])
        materials=json.loads(material_raw)
        inputs=ResearchInputs(review,materials,public_root=root,private_root=private_root,
                              policy=policy,policy_sha256=digest)
        score=score_open_research(inputs)
        if score!=json.loads(source_bytes(private_root,refs['score'])):
            raise ValueError('Research capability no longer reproduces from independent reviews')
        projected=project_public(score,policy=policy,policy_sha256=digest,
            review_sha256=refs['review']['sha256'],materials_sha256=refs['source-bindings']['sha256'])
        if projected!=json.loads(source_bytes(root,pub['models'][mid])):
            raise ValueError('Public research capability is not the exact private projection')
        if refs['public_projection']!=pub['models'][mid]:
            raise ValueError('Paired research projection references differ')
        tasks+=len(review['tasks'])
    load_public(root,benchmark_version=EDITION)
    if load_public(root,benchmark_version='1.1.0') is not None:
        raise ValueError('Archived profile cannot inherit a new research axis')
    return dict(status='passed',models=len(expected),independently_reviewed_deliveries=tasks,
                new_candidate_calls=0,main_scores_modified=False)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root',type=Path,default=ROOT)
    parser.add_argument('--private-root',type=Path,default=ROOT.parent/'math-gauge-private')
    parser.add_argument('--reviews',type=Path)
    parser.add_argument('--write',action='store_true')
    args=parser.parse_args()
    if args.reviews:
        rows=json.loads(args.reviews.read_text())
        result=(install(args.root,args.private_root,rows) if args.write else
                prepare(args.root,args.private_root,rows)[2])
    else:
        if args.write:
            parser.error('--write requires exact independently reviewed --reviews')
        result=check(args.root,args.private_root)
    print(json.dumps(result,ensure_ascii=False,indent=2))


if __name__=='__main__':
    main()
