"""Preserve two reviews and apply a root-adjudicated verdict; no model calls."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import sys

BASE = Path(__file__).resolve().parent
sys.path.insert(0, str(BASE.parents[2]))
from math_gauge.review import apply_reviews


def main():
    p = argparse.ArgumentParser()
    p.add_argument('packet')
    p.add_argument('--primary', type=Path, required=True)
    p.add_argument('--secondary', type=Path, required=True)
    p.add_argument('--verdict', type=Path, required=True)
    a = p.parse_args()
    mapping = {x['packet_id']: x for x in json.loads((BASE / 'packet-map.json').read_text())}
    row = mapping[a.packet]
    entries = [json.loads(path.read_text()) for path in (a.primary, a.secondary, a.verdict)]
    for entry in entries:
        assert entry['packet_id'] == a.packet and entry['case_id'] == row['case_id']
        assert entry['response_sha256'] == row['response_sha256']
        assert entry['reviewer_kind'] == 'ai'
    assert entries[0]['reviewer'] != entries[1]['reviewer'], 'Require distinct reviewers'
    verdict = entries[2]
    assert verdict['reviewer'] == '/root' and verdict['needs_second_review'] is False
    assert verdict['primary_review_sha256'] == hashlib.sha256(a.primary.read_bytes()).hexdigest()
    assert verdict['secondary_review_sha256'] == hashlib.sha256(a.secondary.read_bytes()).hexdigest()
    assert not (Path(row['run_dir']) / 'reviews.json').exists(), 'Never overwrite an applied review'
    targets = [(BASE / kind / (a.packet + '.json'), source)
               for kind, source in [('primary', a.primary), ('secondary', a.secondary), ('adjudication', a.verdict)]]
    assert all(not target.exists() for target, _ in targets), 'Keep original reviews immutable'
    for target, source in targets:
        target.parent.mkdir(exist_ok=True)
        shutil.copyfile(source, target)
    apply_reviews(row['run_dir'], [verdict])
    print(json.dumps({'packet':a.packet, 'case_id':row['case_id'], 'decision':verdict['decision']}))


if __name__ == '__main__':
    main()
