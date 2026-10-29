"""Project exact frozen answers for review; never run or modify a candidate."""
import hashlib
import json
from pathlib import Path
import uuid

ROOT = Path('/private/tmp/math-gauge-full-comparison-20261030')
DEST = Path(__file__).resolve().parent


def read(p):
    return json.loads(p.read_text())


def sha(data):
    return hashlib.sha256(data).hexdigest()


def main():
    path = DEST / 'packet-map.json'
    mapping = read(path) if path.exists() else []
    seen = {(r['model_label'], r['case_id']) for r in mapping}
    freeze = read(ROOT / 'runtime/freeze.json')
    cases = {c['case_id']: c for c in freeze['cases']}
    index_path = ROOT / 'runtime/model-runs.json'
    if not index_path.exists():
        print('No completed records yet.')
        return
    added = []
    for label, runs in read(index_path)['model_runs'].items():
        for directory in runs:
            run = Path(directory)
            meta = read(run / 'run.json')
            cid = meta['cases'][0]['id']
            if (label, cid) in seen:
                continue
            record = read(run / cid / 'record.json')
            receipt = read(run / cid / 'execution-assessment.json')
            if record['status'] != 'ok' or receipt['valid_for_comparison'] is not True:
                continue
            response = (run / cid / 'response.md').read_bytes()
            assert sha(response) == record['response_sha256'] == receipt['response_sha256']
            assert receipt['run_id'] == meta['run_id'] and receipt['model_label'] == label
            item = cases[cid]
            suite = Path(item['suite_root'])
            manifest = next(read(suite / name) for name in read(suite / 'suite.json')['cases'] if read(suite / name)['id'] == cid)
            packet_id = uuid.uuid4().hex[:12]
            packet = DEST / 'packets' / packet_id
            packet.mkdir(parents=True, exist_ok=False)
            (packet / 'response.md').write_bytes(response)
            (packet / 'request.json').write_bytes((run / cid / 'solver/request.json').read_bytes())
            (packet / 'solver').mkdir()
            (packet / 'solver/request.json').write_bytes((run / cid / 'solver/request.json').read_bytes())
            (packet / 'record.json').write_bytes((run / cid / 'record.json').read_bytes())
            for key, name in [('task', 'task.md'), ('reference', 'reference.md'), ('rubric', 'rubric.json')]:
                (packet / name).write_bytes((suite / manifest[key]).read_bytes())
            evidence = {'packet_id': packet_id, 'case_id': cid, 'task_kind': item['task_kind'],
                        'response_sha256': sha(response), 'request_sha256': item['request_sha256'],
                        'rubric_sha256': item['rubric_sha256'],
                        'blinding_limit': 'Model labels omitted; phase timing may still be inferable.'}
            (packet / 'packet.json').write_text(json.dumps(evidence, ensure_ascii=False, indent=2) + '\n')
            row = dict(evidence, model_label=label, run_dir=str(run), packet_dir=str(packet))
            mapping.append(row)
            added.append({'packet_id': packet_id, 'case_id': cid})
    path.write_text(json.dumps(mapping, ensure_ascii=False, indent=2) + '\n')
    print(json.dumps({'new_packets': added, 'total': len(mapping)}, ensure_ascii=False))


if __name__ == '__main__':
    main()
