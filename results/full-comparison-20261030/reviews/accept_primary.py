"""Root-selected provisional pass reviews, applied by the unchanged shared runner."""
import argparse
import json
from pathlib import Path
import shutil
import sys

BASE = Path(__file__).resolve().parent
sys.path.insert(0, str(BASE.parents[2]))
from math_gauge.review import apply_reviews


def main():
    p = argparse.ArgumentParser()
    p.add_argument('packets', nargs='+')
    p.add_argument('--source-root', type=Path, default=Path('/private/tmp/math-gauge-review-r'))
    a = p.parse_args()
    mapping = {x['packet_id']: x for x in json.loads((BASE / 'packet-map.json').read_text())}
    for pid in a.packets:
        row = mapping[pid]
        source = a.source_root / (pid + '.json')
        entry = json.loads(source.read_text())
        assert entry['packet_id'] == pid and entry['case_id'] == row['case_id']
        assert entry['response_sha256'] == row['response_sha256']
        assert entry['reviewer_kind'] == 'ai' and entry['decision'] == 'pass'
        assert entry['needs_second_review'] is False
        destination = BASE / 'primary' / source.name
        destination.parent.mkdir(exist_ok=True)
        assert not destination.exists(), 'Keep each original primary review immutable'
        assert not (Path(row['run_dir']) / 'reviews.json').exists(), 'Never overwrite an applied review'
        shutil.copyfile(source, destination)
        apply_reviews(row['run_dir'], [entry])
        print(json.dumps({'packet':pid,'case_id':entry['case_id'],'decision':entry['decision']}))


if __name__ == '__main__':
    main()
