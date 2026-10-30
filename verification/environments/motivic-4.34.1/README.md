# Fixed actual-transfer author environment

The optional author profile `lean-4.34.1-motivic` imports actual finite
correspondences, presheaves with transfers and the literal A1 projection maps.
It fixes Lean 4.34.1 and all eleven dependency revisions in
[lake-manifest.json](lake-manifest.json):

| Dependency | Fixed identity |
| --- | --- |
| Lean | `leanprover/lean4:v4.34.1` |
| Motivic | `a6805c4a87cdfd7717dd7a94039246a167f15380` |
| Aglib | `2c34f185fa859e862661f939cd216b07bcccfb26` |
| Mathlib | `d13f23b723b8a846827a245b89c10fc7d3f11612` |
| Complete environment lock | SHA-256 `2f9cab228ffc375abbe1a4783c1e3908aef990b4c1e97626e8cf3f0476f31253` |

The other eight packages are fixed by name and revision in the same lock and
verifier whitelist. Exact lockfile bytes are required; do not run `lake update`
on an accepted environment. [Third-party notices](THIRD_PARTY_NOTICES.md) and
both complete upstream Apache license files are retained beside this README.
The libraries and their compiled caches stay external to Math Gauge.

## Prepare a separate dependency project

Use a new directory and an installed Lean 4.34.1 toolchain. The following runs
from the Math Gauge repository root; replace the example absolute directory.
It refuses an existing destination and creates independent fixed Git checkouts.
The dependency project's own build output is excluded from author verification.

```sh
export MG_MOTIVIC_DEPS=/absolute/path/new-math-gauge-motivic-dependencies
python3 - "$MG_MOTIVIC_DEPS" <<'PY'
from pathlib import Path
import json, shutil, subprocess, sys
source = Path('verification/environments/motivic-4.34.1').resolve()
root = Path(sys.argv[1]).resolve()
root.mkdir(parents=True, exist_ok=False)
for name in ('lean-toolchain', 'lakefile.toml', 'lake-manifest.json'):
    shutil.copyfile(source / name, root / name)
packages = root / '.lake/packages'
packages.mkdir(parents=True)
for package in json.loads((root / 'lake-manifest.json').read_text())['packages']:
    target = packages / package['name']
    subprocess.run(['git', 'clone', '--filter=blob:none', '--no-checkout',
                    package['url'], str(target)], check=True)
    subprocess.run(['git', '-C', str(target), 'checkout', '--detach',
                    package['rev']], check=True)
PY
```

Existing caches are reusable only for matching toolchain, source and dependency
identities. Cached outputs do not replace a fresh GP003 case compilation. For a
new environment, Mathlib's cache command provides its compiled dependency cache;
then build only the external module roots declared by the current GP003 manifest.
The second command computes those roots from the explicit case projection and
excludes local modules and Lean's standard library. It does not build all Motivic.

```sh
(cd "$MG_MOTIVIC_DEPS" && lake --no-cache exe cache get)
python3 - "$MG_MOTIVIC_DEPS" <<'PY'
from pathlib import Path
import json, subprocess, sys
root = Path(sys.argv[1]).resolve()
manifest = json.loads(Path('cases/proofs/MG-GP003/formal/manifest.json').read_text())
local = {row['module'] for row in manifest['modules']}
external = sorted({name for row in manifest['modules'] for name in row['imports']
                   if name not in local and name.split('.')[0] not in ('Lean', 'Std', 'Init')})
subprocess.run(['lake', '--no-cache', 'build', *('+' + name for name in external)],
               cwd=root, check=True)
PY
```

The explicit author manifest must already list the final GP003 sources before
acquiring its complete external closure. Prepare it with
`prepare_author.py --profile lean-4.34.1-motivic` and the complete, dependency-ordered
module list, keeping `Main` last. This step binds sources and existing alignment;
it does not decide which S5 obligations have been proved.

Public upstream compiled archives can reduce setup time. The fixed Motivic
[cache release](https://github.com/kangxyz/motivic/releases/tag/lean-native-a6805c4a87cdfd7717dd7a94039246a167f15380)
records its source commit; cache filenames and CI success alone are insufficient.
The original-source environment and source build above remain authoritative.
When reusing output from a different upstream commit, first check equality of
every required transitive source blob, all dependency pins and the compiler
identity. Record the archive origin and file hashes; preserve the fixed checkout.
A cache mismatch requires acquiring or building the affected closure, not
changing the profile or mixing Lean 4.29.1 outputs into it.

## Inspect identities and verify only GP003

The author verifier checks the lockfile bytes, all eleven independent Git roots,
actual HEADs, clean tracked sources, compiler version and compiler binary hash.
Only explicit case sources, that standard library and the declared package
caches enter `LEAN_PATH`; ambient paths and sibling case outputs are excluded.
Use the exact compiler path for the installed toolchain.

```sh
python3 scripts/formal/verify.py \
  --manifest cases/proofs/MG-GP003/formal/manifest.json \
  --dependency-root "$MG_MOTIVIC_DEPS" \
  --lean /absolute/path/to/lean-4.34.1/bin/lean \
  --out /absolute/path/to/new-gp003-verification
```

The output directory must be new. This invocation compiles only GP003 and its
current explicit local modules; it does not invoke a candidate model, rebuild
external packages, or compile other benchmark cases.

The resulting `MG-GP003/report.json` binds:

- `dependency`: exact package revisions, tracked-source state, compiler and lock identity;
- `direct_external_imports`: each directly imported compiled module and its SHA-256;
- `external_source_closure`: every reachable external module, tracked Git blob,
  source SHA-256, import edges, and olean/private/server/IR/signature part hashes;
- `modules` and `audit`: fresh case source/output/log identities and the inventory
  and axiom union of all declarations from the explicit local source closure.

The external closure is recomputed after compilation. The offline evidence
checker rejects a missing closure, inconsistent row count or digest, duplicate
modules, omitted direct/transitive imports, mixed package revisions, and compiled
parts inconsistent with the module identity. It verifies saved evidence without
requiring the original cache machine.

A successful compilation and allowed-axiom audit establish the recorded Lean
result. Assumption fidelity, prose-to-Lean correspondence, complete S5 coverage,
AI semantic review and human approval remain separate evidence. The profile does
not change candidate-facing material, the default Lean 4.29.1 profile, other
cases, or review status. All original GP003 modules and all added actual geometry,
site and assembly modules must participate in its final fresh verification.
