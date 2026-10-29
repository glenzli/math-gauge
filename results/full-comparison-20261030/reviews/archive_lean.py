"""Preserve original candidate verification artifacts and bind their existing hashes."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil

BASE = Path(__file__).resolve().parent


def load(path):
    return json.loads(path.read_text())


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('packets', nargs='+')
    parser.add_argument('--source-root', type=Path, default=Path('/private/tmp/math-gauge-review-f'))
    args = parser.parse_args()
    mapping = {r['packet_id']: r for r in load(BASE / 'packet-map.json')}
    map_path = BASE / 'lean-report-map.json'
    reports = load(map_path) if map_path.exists() else {}
    allowed = {'report.json', 'request.json', 'response.md', 'manifest.json', 'compiler.sb', 'audit.lean', 'extraction-override.json'}
    for pid in args.packets:
        row = mapping[pid]; review = load(args.source_root / (pid + '.json'))
        report_path = Path(review['candidate_lean_report_path'])
        report = load(report_path)
        assert digest(report_path) == review['candidate_lean_report_sha256']
        assert report['case_id'] == row['case_id'] and report['response_sha256'] == row['response_sha256']
        assert report['request_sha256'] == row['request_sha256']
        target = BASE.parent / 'answers' / pid / 'lean'
        assert not target.exists(), 'Keep verification attempts immutable'
        sources = []
        for source in sorted(report_path.parent.rglob('*')):
            assert not source.is_symlink(), 'Do not archive symlink targets'
            if not source.is_file():
                continue
            rel = source.relative_to(report_path.parent)
            assert (len(rel.parts) == 1 and rel.name in allowed) or rel.parts[0] in {'submitted','inputs','logs','oleans'}, str(rel)
            sources.append((source, rel, digest(source)))
        target.mkdir(parents=True)
        manifest = []
        for source, rel, expected in sources:
            dest = target / rel; dest.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(source, dest)
            assert digest(source) == digest(dest) == expected
            manifest.append({'source':str(source),'archived':str(dest),'sha256':expected})
        (target.parent / 'archive-manifest.json').write_text(json.dumps(manifest, ensure_ascii=False, indent=2) + '\n')
        reports.setdefault(row['model_label'], {})[row['case_id']] = str(target / 'report.json')
        print(json.dumps({'packet':pid,'case_id':row['case_id'],'status':report['status'],'files':len(manifest)}))
    map_path.write_text(json.dumps(reports, ensure_ascii=False, indent=2) + '\n')


if __name__ == '__main__':
    main()
