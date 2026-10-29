# MG-GR019 author formal coverage

All six stages are implemented in actual topological spaces and ultrafilter algebras. Compilation is author proof evidence; human approval and candidate model performance remain pending/not run.

| Stage | Formal content |
|---|---|
| S1 | Literal clopen-characteristic observation image, profiniteness, continuous surjection, universal property and exact connected-component fibers |
| S2 | Equality of product components, homeomorphism of actual observation images, natural pointwise formula |
| S3 | Actual preimage of every component is a component under connected-fiber surjection; induced observation homeomorphism |
| S4 | Exact two-law algebra constructor, unique compact Hausdorff topology, both round trips, all morphisms, profinite reflection and all finite-observation criteria |
| S5 | Product algebra with both laws, equality of reconstructed/product topologies, natural product observation quotient |
| S6 | Square fold from the real interval [−1,1] onto [0,1], actual induced quotient homeomorphism and disconnected fiber over 1 |

S1 uses Bool for {0,1}; its universal property is proved for all Hausdorff totally disconnected targets and therefore includes all finite discrete targets. Compact Hausdorff component/quasicomponent equality is used with its hypotheses. S5 does not identify the ultrafilters of a product with the product of ultrafilter sets: it uses actual coordinate pushforwards and proves multiplication naturality from the membership formula. The product quotient is expressed in the ordinary product topology, proved equal to the reconstructed topology by `product_topology`. S6 verifies the induced map, not merely the existence of an unrelated homeomorphism between the quotients.

`UltrafilterAlgebras.lean` and `ProfiniteReflection.lean` are byte-identical copies of the public MG-R019 author sources, recorded with exact provenance hashes in alignment.json. New modules and the complete closure are freshly compiled and dynamically audited by the shared verifier. No assumed-goal certificate, placeholder, new axiom or candidate execution is used.
