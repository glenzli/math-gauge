"""Prepare, validate and stage the independently reviewed exploration profile.

No command executes candidates, calculates benchmark scores or installs a site.
"""
import argparse
import json
from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from math_gauge import exploration_orientation as owner

def write_files(root, files):
    root = Path(root)
    for name, raw in files.items():
        target = root / name
        if not target.resolve().is_relative_to(root.resolve()):
            raise ValueError('Output path escapes the reviewed artifact directory')
        if target.exists() and target.read_bytes() != raw:
            raise ValueError('Output already contains different bytes: ' + name)
    for name, raw in files.items():
        target = root / name
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(raw)

def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action', choices=('prepare', 'check', 'stage'))
    parser.add_argument('--public-root', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--private-root', type=Path, required=True)
    parser.add_argument('--intake-root', type=Path)
    parser.add_argument('--freeze-root', type=Path)
    parser.add_argument('--policy', type=Path)
    parser.add_argument('--review-index', type=Path)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args(argv)
    intake = args.intake_root or args.private_root / owner.INTAKE_PREFIX
    freeze = args.freeze_root or args.private_root / 'protocol/exploration-orientation/v0.1.0'
    policy_path = args.policy or args.public_root / owner.POLICY_PATH
    materials, scaffolds, policy, _ = owner.prepare_materials(intake, public_root=args.public_root, private_root=args.private_root, policy_root=policy_path, freeze_root=freeze)
    if args.action == 'prepare':
        if args.output is None:
            parser.error('prepare requires --output')
        files = {mid + '/source-bindings.json': owner.encoded(value) for mid, value in materials.items()}
        files.update({mid + '/review-scaffold.json': owner.encoded(value) for mid, value in scaffolds.items()})
        write_files(args.output, files)
        print(json.dumps(dict(action='prepare', models=len(materials), new_candidate_calls=0, output=str(args.output))))
        return 0
    if args.review_index is None:
        parser.error('check/stage requires --review-index')
    selected = owner._object(args.review_index.read_bytes())
    if set(selected) != set(materials):
        raise ValueError('Need exactly the frozen19final review paths')
    reviews = {mid: owner._object((args.review_index.parent / name).read_bytes()) for mid, name in selected.items()}
    public, private = owner.stage(reviews, materials, policy, public_root=args.public_root, private_root=args.private_root, intake_root=intake)
    if args.action == 'check':
        for root, files in ((args.public_root, public), (args.private_root, private)):
            for name, expected in files.items():
                if owner.read_bytes(root / name) != expected:
                    raise ValueError('Adopted component does not exactly replay: ' + name)
        loaded = owner.load_public(args.public_root, cohort=policy['cohort']['selected_configurations'])
        if loaded is None:
            raise ValueError('Adopted public component is missing')
    if args.action == 'stage':
        if args.output is None:
            parser.error('stage requires --output')
        public[owner.POLICY_PATH] = policy_path.read_bytes()
        private[owner.INTAKE_PREFIX + '/source-manifest.json'] = (intake / 'source-manifest.json').read_bytes()
        manifest = json.loads(private[owner.INTAKE_PREFIX + '/source-manifest.json'])
        for model in manifest['models']:
            private[owner.INTAKE_PREFIX + '/' + model['path']] = (intake / model['path']).read_bytes()
        for name in ('FREEZE.json', 'review-template.json', 'support-contract.json', 'contract-notes.private.json'):
            private['protocol/exploration-orientation/v0.1.0/' + name] = (freeze / name).read_bytes()
        write_files(args.output / 'public', public)
        write_files(args.output / 'private', private)
    print(json.dumps(dict(action=args.action, models=len(materials), public_files=len(public), private_files=len(private), public_index=owner.binding(public[owner.PUBLIC_INDEX]), new_candidate_calls=0, main_scores_modified=False)))
    return 0
if __name__ == '__main__':
    raise SystemExit(main())
