# MG-R009: complete semantic coverage ledger

This formalization uses actual set-valued presheaves, actual Grothendieck-topology sheaves, the pointwise orbit quotient, and mathlib's concrete two-plus sheafification. No quotient, comparison isomorphism, or descent conclusion is supplied as an input certificate. The frozen task, reference, and rubric are unchanged.

## Universes and actual input

The general site has object universe `u`, morphism universe `v`, and values `Type (max u v w)` for independent arbitrary `w`. `SheafUniverseLocal.lean` proves the four concrete plus/sheafification local-surjectivity and local-injectivity lemmas in this full value universe; they do not assume those conclusions. The profinite instantiation is `ProfSheaf.{u,w} = Sheaf (coherentTopology Profinite.{u}) (Type (max (u+1) w))`. Thus arbitrary larger-universe sheaves and arbitrary bases are retained. `SpaceAction.classification` explicitly quantifies this larger value universe.

`SpaceAction` contains actual homeomorphisms and their pointwise identity/composition laws, an unpacked presentation of the given homomorphism into the homeomorphism group. `SpaceAction.probe_action` acts on the actual lifted continuous-map presheaf. `PAction` similarly records natural group-action maps and their two group laws; `PAction.actIso` derives their invertibility.

## Coverage map

| Frozen mathematical obligation | Lean declaration(s) and actual content |
| --- | --- |
| Profinite finite jointly surjective coverage, including empty families | `prof_cover_iff`; identifies the actual coherent topology with finite jointly surjective families using `Profinite.effectiveEpiFamily_tfae`. The library's profinite limits and coherent topology implement fibre products and cover composition. |
| Actual representable/probe sheaf | `prof_probe_sheaf`; its objects are `ULift C(S,X)`, with precomposition restrictions. Sheafhood is proved by the compact-Hausdorff quotient-map sheaf theorem, then exact universe lifting. |
| Arbitrary sheaf group action | `PAction`, `EquivariantOver`, `PAction.actIso`. No freeness or stabilizer condition is built into the object type. |
| Pointwise orbit presheaf | `PAction.orbit_setoid`, `orbit_presheaf`, `orbit_projection`; actual `Quotient` and descended restriction maps. |
| Orbit equivalence relation and restriction stability | `orbit_setoid.iseqv`, `restrict_act`, `orbit_projection_eq`; identity, inverse, multiplication and naturality prove the obligations. |
| Actual sheaf quotient | `PAction.quotient_sheaf`, `quotient_projection`; the underlying presheaf is `J.sheafify orbit_presheaf`, i.e. two concrete plus constructions. |
| Local representatives | `quotient_locally_surjective`; global orbit representatives and local representatives in plus construction give the actual image covering sieve. |
| Exact local orbit equality | `quotient_eq_iff_local_orbit`, `quotient_eq_iff_finite_cover`; equality is on a covering sieve and, on Prof, on a finite jointly surjective family with possibly different labels. |
| Invariant universal property and naturality | `quotient_lift`, `quotient_lift_fac`, `quotient_hom_ext`, `quotient_universal`, `quotient_universal_natural`; explicit factorization, uniqueness, equivalence, and postcomposition naturality. |
| Effective local-orbit kernel pair | `quotient_kernel_condition`, actual `fibre_sheaf q q`, and `quotient_kernel_universal`; every map equalizing its two projections uniquely factors through the quotient. |
| Actual fibre-product sheaf | `fibre_presheaf`, `fibre_isSheaf`, `fibre_sheaf`, `fibre_universal`; sectionwise pairs with equal images and a coordinatewise sheaf gluing proof. |
| Canonical realization from E | `EquivariantOver.quotient_to_base`, `comparison`, `comparison_apply`; actual `e ↦ (π(e),[e])`. |
| Comparison always locally onto | `comparison_locally_surjective`; successive local lifts and local orbit labels, without global representatives. |
| All-test stabilizer criterion | `StabilizerTrivial`; quantifies every site object, every section, and every group element. |
| Sufficiency | `comparison_injective`, `comparison_isIso`; local orbit equality plus stabilizer triviality and sheaf separation prove injectivity, then actual locally bijective sheaf isomorphism. |
| Necessity and all three equivalent conditions | `realizable_iff_stabilizer_trivial`, `comparison_isIso_iff`; actual arbitrary equivariant realization and actual comparison isomorphism. |
| Locally varying labels | `EquivariantOver.local_stabilizer`; proves the stronger statement for arbitrary covering-local labels, hence covers locally constant finite-image labels. |
| Pullback object satisfies criterion | `pullback_action`, `pullback_equivariant`, `pullback_stabilizer_trivial`; only the first coordinate is acted on. |
| Quotient of H×Q D is D | `pullback_snd_locally_surjective`, `pullback_snd_local_orbits`, `pullback_quotient_iso`, `pullback_quotient_fac`; actual quotient lift, local kernel and surjectivity proofs. |
| All equivariant maps descend | `EquivariantOver.Hom.quotient_map`, `quotient_map_fac`, `quotient_map_over`; actual map on orbit quotients. |
| Complete realization Hom correspondence | `descend_pullback_hom`, `descend_pullback_fac`, `descend_pullback_over`, `pullback_descend`, `descend_pullback`, `realization_hom_equiv`; both inverses and base compatibility. |
| Identity/composition preservation | `Hom.quotient_map_id`, `Hom.quotient_map_comp`, `pullback_hom_id`, `pullback_hom_comp`; used in actual functors. |
| Actual categorical equivalence | `equivariantCategory`, `StableEquivariant`, `realizationFunctor`, `quotientFunctor`, `descent_equivalence`; full, faithful and essentially surjective proofs use the established maps. |
| Unique realization with chosen identifications | `realization_iso_unique`; existence and uniqueness of the slice isomorphism compatible with both specified identifications. No automorphism triviality is claimed. |
| Arbitrary sheaf base B and its quotient | `pullback_quotient_iso A B b`, `basechange_equivalence`; applies to every large-universe sheaf B, without representability. |
| Actual base change of equivariant records | `basechange_record`, `basechange_stabilizer_trivial`; action on E-coordinate and projection to H×Q B. |
| Realization/base-change coordinate isomorphism | `basechange_fibre_iso`, its first/second-coordinate formulas, `basechange_realization_iso`; actual natural sheaf isomorphism preserving projection and action. |
| Naturality of base change | `fibre_map`, `fibre_map_id`, `basechange_fibre_natural`; explicit maps in both D and B and equality of the actual squares. |
| Quotient of base-changed realization | `basechange_realization_quotient_iso`; the quotient is the actual fibre sheaf D×Q B, proved using local surjectivity and local orbit kernel of the right projection. |
| Empty test, empty T, empty base | All generic declarations allow them, and `prof_cover_iff` allows the empty finite index set. Probe sheafhood includes empty finite products. No nonempty assumption appears in the classification. |

## Reference boundary conclusions, proved by complete alternative routes

1. `prof_point_cover_id`, `prof_point_locally_surjective`, `quotient_point_eq_iff`, and `quotient_point_equiv` prove that sheafification of this orbit presheaf really leaves singleton sections equal to the global orbit set. This is derived from finite jointly surjective covers of the singleton.
2. `padic_integer_translation` is the actual integer translation action on mathlib's compact Hausdorff totally disconnected 2-adic integers. `padic_two_uncountable` uses Baire's theorem and the fact that an infinite compact topological group cannot be discrete, replacing the reference's binary-sequence parameterization. `padic_orbit_point_nontrivial` proves there is more than one integer orbit. `padic_invariant_continuous_constant` uses the actual theorem `PadicInt.denseRange_intCast`. `padic_quotient_not_hausdorff_probe` proves that this quotient is not the probe sheaf of any Hausdorff space, using an explicit Yoneda calculation. The optional inverse-limit coordinates are not substituted for an unproved topological action.
3. `real_translation` is the actual constant-translation action on the real continuous-map sheaf. `real_orbit_point_subsingleton` proves its quotient has only one singleton section. `cantor_real` is the canonical Cantor embedding supplied by the proved ternary Cantor homeomorphism; using this continuous injection replaces the particular half-sized ternary series in the reference. `real_q_eq_finite_difference` proves equality of quotient records forces finite image of the difference. Consequently `cantor_q_ne_zero` and `cantor_q_neg_ne` are proved. `real_orbit_neg_involution`, `involution_action`, and `invisible_record` construct the actual C₂ action directly; `invisible_record_pointwise_trivial` and `invisible_record_not_realizable` establish the full counterexample. This proof does not need to package all addition operations into a separate abelian-group-valued sheaf.

## Validation

Every listed declaration is kernel-checked with Lean 4.29.1 and mathlib `5e932f97dd25535344f80f9dd8da3aab83df0fe6`. `R009Audit.lean` imports all modules and enumerates every `MathGauge.Descent` declaration, including generated declarations and instances; it rejects every axiom except `propext`, `Classical.choice`, and `Quot.sound`. Exact source/log hashes and audit declaration count are recorded in `R009-evidence.json`.

No theorem is marked complete solely because a module exists. The complete compiled declarations above are the evidence; neither repository documentation nor source claims replace those proofs.
