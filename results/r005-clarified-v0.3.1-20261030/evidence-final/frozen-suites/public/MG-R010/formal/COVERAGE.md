# MG-R010 semantic coverage

Scope: the full frozen task, all conclusions in its reference, both boundary examples, fixed carrier universe, and the larger presheaf value universe. The canonical task/reference/rubric were not edited. The main proof is direct and does not assume Cartesian closedness as a certificate.

All names below are in `MathGauge.Mapping`. Source carrier universe is `u`; `v` is the ambient value-universe lift. A type in universe `u` and its `ULift` into the ambient universe are canonically equivalent; `lift_nat_equiv` proves that no additional natural transformations are lost by working first with the small Hom sets.

| Frozen semantic assertion | Lean declaration(s), actual scope |
|---|---|
| Same-carrier topology determined by all U-small compact Hausdorff probes | `Kify`, `kify_isOpen_iff` |
| The topology is finer than the original; original probes lift and map back | `continuous_kdown`, `continuous_kprobe` |
| Every compact Hausdorff space has a U-small profinite cover | `compact_cover` is `Profinite.of (Ultrafilter S)`; its compact, Hausdorff and totally disconnected structures are actual mathlib instances, not hypotheses on an abstract cover |
| Ultrafilter limit map is continuous, surjective, and a quotient | `compact_cover_map`, `compact_cover_surjective`, `compact_cover_quotient`; principal ultrafilters are the surjectivity witnesses |
| Profinite and compact Hausdorff probes give identical detection | `compact_profinite_detection`, `kify_isOpen_iff_profinite`, `continuous_from_kify_profinite` |
| Hausdorff property preserved | `instT2SpaceKify`, using the injective continuous carrier identity |
| kX is compactly generated; k(kX)=kX up to the literal carrier identity homeomorphism | `instUCompactlyGeneratedSpaceKify`, `kify_homeo (Kify X)` |
| Compact Hausdorff objects fixed | `kify_homeo S` for `S : CompHaus`; the required compact generation instance is supplied by mathlib for these actual spaces |
| Lift from arbitrary compactly generated source, with same underlying map | `continuous_into_kify` |
| Functorial kification and identity/composition | `kmap`, `kmap_id`, `kmap_comp` |
| Probe presheaf is unchanged naturally | `probe_kify_iso` |
| Singleton extraction and naturality determine every component pointwise | `probe_point`, `probe_naturality_point` |
| All Nat(hX,hY) correspond to C(kX,kY), in both directions | `probe_map_equiv`; `probe_to_map` proves continuity from actual probes; `map_to_probe` constructs each component |
| Identity/composition preserved | `map_to_probe_id`, `map_to_probe_comp` |
| Correct compactly generated product | `kprod`, `kpair`, `kfst`, `ksnd`, `kprod_equiv` |
| Probe product and ordinary product correspondence | `probe_product_iso`, with pointwise pairing/projections |
| k(Z×X)=k(kZ×kX), on the same pairs | `kify_product_homeo` |
| Mapping carrier and topology | `KMap A B = Kify C(A,B)`; `Realization X Y = KMap (Kify X) (Kify Y)`; `C(A,B)` carries mathlib's actual compact-open topology |
| Mapping space Hausdorff and U-small | `instT2SpaceKMap`, `realization_hausdorff`, `realization_small` |
| Currying continuous into compact-open, then its kification | `continuous_kcurry_co`, `kcurry`; each compact subset of A is treated as a compact Hausdorff subtype |
| Uncurrying continuous on k-product without local compactness of A | `continuous_kuncurry`, `kuncurry`; for a compact probe S, restriction is by its actual second coordinate S→A, so ordinary evaluation is used only on compact S |
| Full exponential bijection and explicit evaluation | `exponential_equiv`, `keval`, `eval_exponential`, `kcurry_apply`, `kuncurry_apply` |
| Every profinite parameter represented naturally | `realization_equiv`, `realization_natural`; in the larger universe, `realization_equivV` and the actual presheaf isomorphism `realization_isoV` |
| Every Hausdorff parameter Z, including non-CG Z | `all_parameter_equiv`, `all_parameter_equivV`; these actually prove the result for all topological Z |
| Required evaluation operation is the displayed bijection | `evaluation`, `evaluation_apply`, `evaluation_induces_equiv`, `evaluation_bijective`; ambient-universe versions `evaluationV`, `evaluationV_induces_equiv`, `evaluationV_bijective` |
| Parameter naturality, including arbitrary probe natural transformations | `all_parameter_natural`, `realization_natural` |
| Continuous maps in X and Y and their identities/compositions | `realization_map`, `realization_map_apply`, `realization_map_id`, `realization_map_comp`, `family_record_natural_XY`, `realization_natural_XY`, `all_parameter_natural_XY` |
| Larger-universe Nat sets are U-small | `lift_nat_equiv`, `lift_product_nat_equiv`, `records_small` |
| Correct uniqueness: arbitrary realizations become homeomorphic after kification | `probe_iso_homeo`, `realization_unique_after_kify`; no original-topology uniqueness is claimed |
| Empty source gives singleton mapping space | `realization_empty_source : Unique (Realization X Y)` for `[IsEmpty X]` |
| Nonempty source and empty target give empty mapping space | `realization_empty_target`; empty parameters are included in all unrestricted equivalences |
| Boundary 1 actual one-point cocountable topology | `Fortissimo`, `fortissimo_isOpen`, `instT2SpaceFortissimo`, `fortissimo_not_open_infty`, `fortissimo_not_discrete` |
| Boundary 1 every compact subset finite | `fortissimo_compact_finite`, proved using a countably infinite closed discrete subset if a compact set were infinite |
| Boundary 1 discrete kification and extra probe maps | `instDiscreteTopologyKifyFortissimo`, `fortissimo_not_continuous_to_kify`, `fortissimo_extra_probe_map` |
| Boundary 1 concrete D=P(N), rather than an uninstantiated uncountability premise | `powerset_nat_uncountable`, `powerset_nat_extra_probe_map`, via Cantor's theorem |
| Boundary 2 Q is compactly generated and has no compact neighborhood | `rational_compactly_generated`, `rational_not_locally_compact`, `rational_compact_not_mem_nhds` |
| Boundary 2 ordinary compact-open evaluation fails at (0,0) | `rational_evaluation_not_continuousAt`, `rational_evaluation_not_continuous` |

The second boundary proof uses a Urysohn separator for the closed compact set and the point outside it, scaled to value 2. This proves the same finite-neighborhood obstruction as the reference's explicit distance quotient. Its proof that Q has no compact neighborhood uses local compactness of a topological group implying completeness, then the dense rational embedding in R; it does not assume the non-local-compactness conclusion. These are alternative complete proofs of the same assertions, not strengthened hypotheses.

Validation: every mathematical source compiled with Lean 4.29.1 and mathlib `5e932f97dd25535344f80f9dd8da3aab83df0fe6`. `R010Audit.lean` enumerates all namespace declarations in the environment, including generated helpers and instances, and rejects every foundational dependency other than `propext`, `Classical.choice`, and `Quot.sound`. Its complete output is `R010Audit.compile.log`. The current source fingerprints and frozen-input fingerprints are in `R010-evidence.json`.

Remaining limitation: Lean uses a universe hierarchy rather than set-theoretic Grothendieck universe membership. This is the standard faithful universe-level formulation: all constructed topological carriers stay in `Type u`, while the profinite category and natural transformation sets live in the explicitly enlarged universe. No topology, finiteness, countability, Hausdorff condition, or quantified parameter was removed from the mathematical target.
