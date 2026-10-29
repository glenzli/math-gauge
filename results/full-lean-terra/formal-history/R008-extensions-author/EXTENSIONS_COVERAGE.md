# Current R008 reference-extension coverage

**This current addendum supersedes exactly the four R008 reference gaps listed in the frozen `COVERAGE.md`: the finite-stage idempotent criterion, preservation of finite limits for arbitrary towers, the multiplier-two example, and the rank-two projection example. All four are now proved and compiled.** The original coverage ledger and core artifacts remain byte-for-byte unchanged so their previous evidence receipts remain valid. The candidate response's separate additional results retain their previously stated mathematical-review status.

## Exact correspondence

| Reference conclusion | Actual compiled declaration | Coverage |
|---|---|---|
| Finitely many records admit one common stage | `MathGauge.Tower.FreeTower.finite_records_common_stage` | Proved for dependent arbitrary target modules |
| Finitely many record equalities admit one common later witness | `MathGauge.Tower.FreeTower.finite_equalities_common_stage` | Proved, including empty finite families |
| A map from a finite free module to a record module lifts to a finite stage | `MathGauge.Tower.FreeTower.finite_free_map_lifts` | Actual lift constructed on a chosen finite basis |
| Equality of maps from a finite free module can be witnessed at one stage | `MathGauge.Tower.FreeTower.finite_free_maps_eventually_equal` | Proved from the common-witness lemma and basis extensionality |
| Finite generation of M iff some stage dual surjects onto M | `MathGauge.Tower.FreeTower.finite_invariant_iff_stage_surjective` | Proved in both directions |
| Exact reference criterion on the original P_n: existence of n and d²=d, and for every m≥n existence of u_m and r≥m with u_m d=u_m, ρ_nm u_m=d, u_mρ_nr=ρ_mr | `MathGauge.Tower.FreeTower.FiniteStageCriterion` | Exact quantified definition; no coherence of the separately selected u_m is imposed |
| The original-stage criterion is equivalent to its dual formulation | `MathGauge.Tower.FreeTower.finiteStage_iff_dualStage` | Proved by actual finite-free bidual equivalences; `transposeDual` is constructed, with pairing and composition formulas |
| M finite generated implies the criterion | `MathGauge.Tower.FreeTower.finite_invariant_implies_dualStage` and `finiteStage_iff_dualStage` | The stage, splitting j, idempotent, retractions and later witnesses are constructed; no certificate assumption |
| Criterion implies M finite generated | `MathGauge.Tower.FreeTower.dualStage_implies_finite_invariant` | Proved by surjectivity of the finite stage. This is a complete alternative to the reference's image-isomorphism proof |
| Finite-stage criterion iff finite generation, hence iff representability | `MathGauge.Tower.FreeTower.finiteStage_iff_finite_invariant`, `finiteStage_iff_representable` | Proved under the original tower hypotheses |
| Every tower preserves finite limits | `MathGauge.Tower.FreeTower.preserves_every_finite_limit` | Standard `CategoryTheory.Limits.PreservesLimit`, for every U-small category with finitely many objects and total arrows, with no finite-generation assumption on M |
| This is the canonical finite-limit comparison | `recordComparison`, `recordComparison_injective`, `recordComparison_surjective`, `finiteRecordConeIsLimit` | The map is induced by actual limit projections; its inverse is constructed by moving representatives and compatibility equations to common stages. Empty diagrams included |
| The rank-two tower has step (a,b)↦(a,0) | `MathGauge.Tower.Examples.projectionTower` | Concrete constant ℤ×ℤ stages and the actual projection map |
| This tower satisfies the finite-stage criterion | `MathGauge.Tower.Examples.projection_finite_stage_criterion` | Explicit witness n=0, d=projection, u_m=projection, r=m+1 |
| Its invariant is ℤ and its record functor is represented by ℤ | `MathGauge.Tower.Examples.projectionInvariantEquiv`, `projectionRepresentation` | Actual linear equivalence and actual natural isomorphism with Hom(ℤ,-) |
| No step is an isomorphism, so eventual isomorphisms are not necessary | `MathGauge.Tower.Examples.projection_step_not_injective`, `projection_never_eventually_isomorphisms` | Proved using the nonzero second-coordinate kernel |
| The multiplier-two tower | `MathGauge.Tower.Examples.doublingTower` | Concrete ℤ stages and multiplication by two |
| Its invariant is ℤ[1/2] | `MathGauge.Tower.Examples.doublingInvariantEquivDyadic` | Actual linear equivalence with `dyadicIntegers`, the submodule `{q : ℚ | ∃ n : ℕ, ∃ z : ℤ, q = z / 2^n}` |
| The direct-limit-to-fraction map is legitimate and injective | `dyadicStageMap_compatible`, `doublingToRat`, `doublingToRat_injective`, `doublingToDyadic_bijective` | All transition compatibility, injectivity, range and surjectivity proved |
| Finite denominators do not generate all dyadic integers | `doubling_stage_not_surjective`, `doubling_invariant_not_finite`, `dyadicIntegers_not_finitely_generated` | The next denominator is excluded from every stage image; the finite-stage-surjectivity criterion then rules out finite generation |
| The multiplier-two record functor is not representable and fails countable-limit preservation | `doubling_not_representable`, `doubling_not_preserves_countable_limits` | Deduced from the previously compiled main classification on this concrete tower |

There is no remaining unencoded conclusion among these requested reference extensions. Alternate intermediate proof routes (for example the reference's explicit isomorphism `im e ≅ M`) are not claimed as separately encoded; their stated final conclusions are proved by the complete alternatives above. No benchmark statement or reference was changed.

## Build order and audit

Use the frozen `check.py` with these **new files only**, after the already-built core dependencies:

1. `TowerStageTools.lean`
2. `TowerFiniteLimits.lean`
3. `TowerFiniteStage.lean`
4. `TowerProjectionExample.lean`
5. `TowerDoublingExample.lean`
6. `TowerExtrasAudit.lean`

`TowerExtrasAudit.lean` enumerates declarations by their **actual originating module in the compiled Lean environment**, including generated private declarations, and recursively audits their axiom dependencies. It rejects project axioms and every dependency other than `propext`, `Classical.choice`, and `Quot.sound`. Exact counts and source/log/object hashes appear in `EXTENSIONS_MANIFEST.json` and `TowerExtrasAudit.compile.log`.

The base manifest SHA-256 is `92ddee66356758bae308b8502dc2977fb96c14a536f33cf08c81f41229925bf6`. All source files, compiled objects, logs and support files recorded by that manifest are checked unchanged before the extension manifest is written. The extensions use the same Lean 4.29.1 and mathlib `5e932f97dd25535344f80f9dd8da3aab83df0fe6` environment.
