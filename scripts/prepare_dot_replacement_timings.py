"""Evaluate the exact replacement timing capture; never initiate candidate runs."""
import argparse
from pathlib import Path
import json

from math_gauge import dot_evidence_timing as current, dot_rerun_timings as older
from math_gauge.dot_rerun_admission import load_public
from math_gauge.dot_rerun_sources import validate


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--public-root',type=Path,required=True)
    parser.add_argument('--private-source-root',type=Path,required=True)
    parser.add_argument('--written',type=Path,required=True)
    parser.add_argument('--lean',type=Path,required=True)
    parser.add_argument('--out',type=Path,required=True)
    parser.add_argument('--private-receipt',type=Path,required=True)
    args=parser.parse_args()
    private=args.private_source_root
    raw=(private/'admission-build/evidence-replacement-v1/native-source-ledger.json').read_bytes()
    admission=load_public(args.public_root)
    sha=current._sha(raw)
    if sha!=admission['public_source']['private_source_sha256']:
        raise ValueError('Use the exact adopted private score source')
    validated=validate(private,private/'dataset/benchmark-v1.0.0',json.loads(raw),include_evaluator_bindings=True)
    written=args.written; lean=args.lean
    subjects={}
    for slot in sorted(current.SLOTS):
        case,phase=slot.removeprefix('MG-').split(':')
        is_chapter=case=='C003'
        folder=(lean/(case if phase=='A1' else case+'-'+phase)) if is_chapter else written/case
        log_root=lean if is_chapter else written
        log_case=case+'-'+phase if is_chapter else case
        answer=(folder/'answer.md').read_bytes()
        original_request=(folder/'request.json').read_bytes()
        expected=validated['selected'][slot]
        physical=validated['effective_slots'][slot]['physical_calls'][-1]
        if phase=='A1' and current._sha(original_request)!=physical['request']['sha256']:
            raise ValueError(f'{slot}: timing and selected physical request disagree')
        selected=older.read(private,expected['response'])
        if selected!=answer:
            # Admission may select a byte-verified readable projection; a
            # chapter KEEP may also have a specifically declared effective
            # parent. Always keep the actual original timed artifact binding.
            projection=folder/'recovered-answer.md'
            if not projection.is_file() or projection.read_bytes()!=selected:
                raise ValueError(f'{slot}: selected response differs from raw and captured projection')
        sealed=folder/'sealed.json'
        subjects[slot]=current.read_receipt(slot,log_case,(log_root/'timing-events.jsonl').read_bytes(),
            sealed.read_bytes() if sealed.is_file() else None, original_request, selected,
            prior_capture=answer if answer!=selected else None)
    receipt=dict(private_ledger_sha256=sha,
                 authorization_sha256=current._sha((written/'user-authorizations.json').read_bytes()),
                 subjects=subjects)
    for rel,data in current.prepare(args.public_root,admission,receipt).items():
        path=args.out/rel
        path.parent.mkdir(parents=True,exist_ok=True)
        path.write_bytes(data)
    args.private_receipt.write_bytes(older.encoded(receipt))


if __name__=='__main__':main()
