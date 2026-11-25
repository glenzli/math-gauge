#!/usr/bin/env python3
"""Prepare/replay this explicitly admitted native Dot profile; never call models."""
from pathlib import Path
import argparse
import json
import sys

sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from math_gauge import dot_native_profiles as owner


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action',choices=('prepare','check','stage'))
    parser.add_argument('--public-root',type=Path,default=Path(__file__).resolve().parents[1])
    parser.add_argument('--private-root',type=Path,required=True)
    parser.add_argument('--reviews-dir',type=Path)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    if args.action=='prepare':
        parser.error('prepare needs --output') if args.output is None else None
        context=owner.authenticate(args.public_root,args.private_root)
        payloads={}
        payloads['baseline'],_,_,_=owner.prepare_baseline(context)
        payloads['open'],_,_,_=owner.prepare_open(context)
        payloads['structure'],_,_,_,_=owner.prepare_structure(context)
        payloads['initiative'],_,_=owner.prepare_initiative(context)
        payloads['taste']=owner.prepare_taste(context)
        args.output.mkdir(parents=True,exist_ok=True)
        for name,value in payloads.items():
            path=args.output/(name+'-materials.json')
            raw=owner.encoded(value)
            if path.exists() and path.read_bytes()!=raw:
                raise ValueError('Refusing to replace a different prepared source packet: '+str(path))
            path.write_bytes(raw)
        print(json.dumps(dict(status='prepared',model_id=owner.MODEL,new_candidate_calls=0,output=str(args.output))))
        return
    parser.error('check/stage needs --reviews-dir') if args.reviews_dir is None else None
    reviews={kind:json.loads((args.reviews_dir/(kind+'.json')).read_bytes())
             for kind in ('baseline','revision','open','structure','initiative','taste')}
    public,private=owner.prepare_public_files(args.public_root,args.private_root,reviews)
    if args.action=='check':
        # Check every installed projection byte, without changing any file.
        for root,files in ((args.public_root,public),(args.private_root,private)):
            for relative,raw in files.items():
                if (root/relative).read_bytes()!=raw:
                    raise ValueError('Installed Dot profile differs from its exact source replay: '+relative)
        owner.load_public(args.public_root)
    else:
        parser.error('stage needs --output') if args.output is None else None
        for name,files in (('public',public),('private',private)):
            for relative,raw in files.items():
                path=args.output/name/relative;path.parent.mkdir(parents=True,exist_ok=True)
                if path.exists() and path.read_bytes()!=raw:
                    raise ValueError('Refusing to overwrite another staged Dot adoption: '+str(path))
                path.write_bytes(raw)
    print(json.dumps(dict(status='passed'if args.action=='check'else'staged',model_id=owner.MODEL,
                         public_files=len(public),private_files=len(private),new_candidate_calls=0)))


if __name__=='__main__':main()
