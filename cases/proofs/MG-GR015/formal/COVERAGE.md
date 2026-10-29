# MG-GR015 author Lean coverage

All six stages are formalized. The exact declarations, assumptions, quantifiers, domains, representation choices and frozen input hashes are in `alignment.json`. Human review remains pending; no candidate model was run.

| Stage | Mathematical coverage |
|---|---|
| S1 | Actual compatible quotient completion, explicit retraction from the given section, completed linear product decomposition, short exactness, all lifts with a unique parameter, and the change under replacing the section. No finite generation or freeness is added. |
| S2 | Actual PowerSeries-valued restricted product: each observation level has finite surviving support. Coefficient extraction and finite polynomial truncation records are proved inverse. The map is a k[t]-linear equivalence; the target is an actual k[[t]] submodule with componentwise operations and proved scalar closure. |
| S3 | Actual bounded diagonal and cokernel, all bounds including zero. The quotient is killed by t^M. Completed kernel coordinates are divisible by their diagonal powers, and division preserves restricted support by shifting n to n+M. Completed injectivity, surjectivity, exactness and the complete unique coordinate parameterization of each lift fiber are proved. |
| S4 | The exact parent unbounded diagonal counterexample on actual countable free modules. Its finite partial sums form a compatible completed kernel record; any completed preimage would force a finite representative at level one to have infinitely many nonzero constant coefficients. |
| S5 | The actual canonical map is injective and not surjective. The same explicit record has an original representative at every level but no single original finite-support vector. |
| S6 | The actual principal-ideal powers equal t-power images. The original quotient completion and native adic completion are linked by a linear equivalence commuting with transitions, evaluations and canonical maps. The nth evaluation kernel is actually t^n Mhat; the actual canonical map to the second completion is bijective and underlies the constructed linear equivalence. |

## Proof routes and evidence

S3 obtains the first lift from the proved general surjectivity theorem for the actual induced completion map, using the explicit native-adic bridge. Classical choice then selects one lift, and the coordinate theorem describes every lift uniquely. This is a complete alternative to selecting the reference's finite polynomial lift; neither existence nor completed exactness is an input assumption.

S6 uses the pinned mathlib finitely-generated-ideal completion theorems after proving all representation identities and supplying finite generation of the principal ideal. It never assumes finite generation of the original module or relies merely on a name containing “completion”.

`CompletionFailure.lean` is copied byte-for-byte from `cases/public/MG-R015/formal/CompletionFailure.lean`; its exact source hash and base commit are recorded. The other six modules are new. The shared v2 verifier compiles every local module in a fresh output directory with Lean 4.29.1 and pinned mathlib, then audits all local declarations, including private declarations. Compilation, independent semantic review and human approval remain separate evidence.
