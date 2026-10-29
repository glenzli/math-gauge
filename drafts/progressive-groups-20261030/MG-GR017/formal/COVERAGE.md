# MG-GR017 author formal coverage

All six stages are implemented, with complete quantifier/domain mappings in `alignment.json`.

| Stage | Formal coverage |
|---|---|
| S1 | Discrete lifting, actual coproduct lifting, finite coproduct profiniteness, empty cases |
| S2 | Actual continuous retraction inheritance; product with discrete factor lifting and finite factor profiniteness |
| S3 | Actual Stone ultrafilter projectivity, continuous surjective counit, continuous section iff projectivity |
| S4 | Both projective factors and concrete continuous surjective product cover having no continuous section |
| S5 | Actual finite-range continuous lift through any surjection; finite-range topology provides continuity |
| S6 | Full continuous lift ↔ all continuous fiber maps; finite-fiber specialization ↔ all labelled clopen partitions |

`ProductLifting.lean` is a byte-identical public MG-R017 author source copy with frozen provenance. New obligations are proved in `ProgressiveLifting.lean`. Compactness is explicitly proved for finite coproducts and finite discrete product factors; the stronger unrestricted discrete lifting lemmas do not claim infinite discrete spaces are compact. The counit section implication produces full lifting diagrams in arbitrary target universes.

S6 defines actual original continuous maps and actual source/target fibers, with explicit restriction, gluing, both inverse laws and a proof of glued continuity along the finite open fiber cover. Its clopen partition type only assumes the actual partition axioms, allows empty labelled blocks and constructs the corresponding continuous map. No continuity or lift existence is hidden in a certificate.

Fresh isolated compilation and whole-module dynamic axiom audit use the shared verifier. Human review remains pending; no candidate model execution.
