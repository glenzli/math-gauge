# MG-GR016 author Lean coverage

All six stages are represented by actual module constructions and theorems. `alignment.json` records every stage and exact frozen source identities. Human review remains pending; no candidate model was run.

| Stage | Actual proof coverage |
|---|---|
| S1 | Quotient lift rbar↦r(1−e)b, independence of representative, right inverse, and a genuine LinearEquiv ker(q)×C≃B with its inverse. |
| S2 | Derive finite presentation of R/I from I.FG; apply the pinned library local splitting theorem at every maximal ideal (supplied from all primes). The split finite-free surjection makes R/I projective. Split R→R/I and explicitly prove I=(1−s(1bar))R with an idempotent generator. This is a valid alternative to the reference determinant proof, as allowed by the contract; it adds no hypothesis. |
| S3 | Actual kernel equivalence, split product isomorphism, section difference parameters, mutually inverse classifications of all sections and all compatible isomorphisms, and change-of-origin formula. |
| S4 | The complete original counterexample is copied byte-for-byte: infinite Boolean product, finite-support ideal, actual short exact sequence, finite-free middle term and cyclic quotient, all-prime local and tensor sections, and exclusion of every global section. |
| S5 | The same actual ideal satisfies I²=I, its quotient is nonzero, and no section exists. No finite generation is silently added. |
| S6 | Actual overlaps R_(f_i f_j), denominator clearing and a finite unit-ideal identity produce the unique glued element. Gluing every original source element gives a linear map. The whole localized map agrees with every supplied section and q∘s=id. An explicit equivalence relates equality of the common-localization maps to the elementwise compatibility used in the construction. No Hom-localization commutation or presentation hypothesis is used. |

## Closure and evidence

`LocalSplitting.lean` is an exact copy of `cases/public/MG-R016/formal/LocalSplitting.lean`; its SHA256 and repository base commit are in `alignment.json`. The other four modules are newly authored for this group. Modules compile in the order recorded by the v2 manifest against Lean 4.29.1 and the pinned mathlib revision. The shared verifier compiles this closure in a fresh isolated directory and dynamically audits every local declaration, including private declarations. A successful compiler check and this author mapping are distinct from independent semantic review and human approval.
