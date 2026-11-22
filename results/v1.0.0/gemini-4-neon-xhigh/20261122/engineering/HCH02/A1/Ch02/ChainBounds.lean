import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space
import Ch02.MatrixCore
import Ch02.MatrixBounds

/-!
# Chapter 2 Finite-Chain Bounds and Path-Based Zero/Positivity Criteria

Formalizes the finite-composition local matrix bounds (Corollary `#h-c80171fa685dc795`),
the zero-step identity certificates (Remark `#h-11006ddd8c43bfec`), and the path-based
zero/positivity criteria for finite matrix products (Proposition `#h-e4154c34e95d3c23`)
from `source/02-operator-bounds.md` (`HC02-D05`, `HC02-P12`–`HC02-P17`).
-/

namespace OetCh02

open formal_oet.vol_01.ch_01_foundations

/-! ### 1. Stepwise Chain Data Structures (HC02-D05) -/

/-- Stepwise data for a finite operator chain `cₖ = ϕₖ ∘ … ∘ ϕ₁` equipped with local
Lipschitz matrix certificates `L^{(m)} ∈ ℒ(ϕₘ)|_{Uₘ}` on the actual recursive domains
`U₁ ⊆ dom(cₖ)`, `U_{m+1} = ϕₘ(Uₘ)`. Contains only step-level data (never the composite bound). -/
structure LipChainData {X I : Type} (bot : X) [Fintype I]
    (d : I → X → X → ENNReal) (k : ℕ) where
  ops : Fin k → Operator X bot
  startDomain : Set X
  startDomain_subset : startDomain ⊆ dom (finChainOp ops)
  stepMatrices : Fin k → GaugeMatrix I
  step_valid : ∀ m : Fin k,
    stepMatrices m ∈ RestrictedLipSet d (ops m) (chainDomain ops startDomain m.castSucc)

/-- Stepwise data for a finite operator chain `cₖ = ϕₖ ∘ … ∘ ϕ₁` equipped with local
co-Lipschitz matrix certificates `K^{(m)} ∈ 𝒦(ϕₘ)|_{Uₘ}` on the actual recursive domains
`U₁ ⊆ dom(cₖ)`, `U_{m+1} = ϕₘ(Uₘ)`. Each `step_valid m` includes nonemptiness of `Uₘ`.
Contains only step-level data (never the composite bound). -/
structure CoLipChainData {X I : Type} (bot : X) [Fintype I]
    (d : I → X → X → ENNReal) (k : ℕ) where
  ops : Fin k → Operator X bot
  startDomain : Set X
  startDomain_subset : startDomain ⊆ dom (finChainOp ops)
  stepMatrices : Fin k → GaugeMatrix I
  step_valid : ∀ m : Fin k,
    stepMatrices m ∈ CoLipSet d (ops m) (chainDomain ops startDomain m.castSucc)

/-- Dropping the final step of a length `k + 1` Lipschitz chain yields a valid prefix chain. -/
def LipChainData.prefix {X I : Type} {bot : X} [Fintype I]
    {d : I → X → X → ENNReal} {k : ℕ} (chain : LipChainData bot d (k + 1)) :
    LipChainData bot d k where
  ops := fun t => chain.ops t.castSucc
  startDomain := chain.startDomain
  startDomain_subset := by
    have hcomp : finChainOp chain.ops =
        compOp (chain.ops (Fin.last k)) (finChainOp (fun t : Fin k => chain.ops t.castSucc)) :=
      finChainOp_succ_last chain.ops
    exact Set.Subset.trans chain.startDomain_subset
      (hcomp ▸ dom_compOp_subset_left _ _)
  stepMatrices := fun t => chain.stepMatrices t.castSucc
  step_valid := fun m => by
    rw [chainDomain_prefix chain.ops chain.startDomain m.castSucc]
    exact chain.step_valid m.castSucc

/-- Dropping the final step of a length `k + 1` co-Lipschitz chain yields a valid prefix chain. -/
def CoLipChainData.prefix {X I : Type} {bot : X} [Fintype I]
    {d : I → X → X → ENNReal} {k : ℕ} (chain : CoLipChainData bot d (k + 1)) :
    CoLipChainData bot d k where
  ops := fun t => chain.ops t.castSucc
  startDomain := chain.startDomain
  startDomain_subset := by
    have hcomp : finChainOp chain.ops =
        compOp (chain.ops (Fin.last k)) (finChainOp (fun t : Fin k => chain.ops t.castSucc)) :=
      finChainOp_succ_last chain.ops
    exact Set.Subset.trans chain.startDomain_subset
      (hcomp ▸ dom_compOp_subset_left _ _)
  stepMatrices := fun t => chain.stepMatrices t.castSucc
  step_valid := fun m => by
    rw [chainDomain_prefix chain.ops chain.startDomain m.castSucc]
    exact chain.step_valid m.castSucc

/-! ### 2. Finite-Chain Local Matrix Bounds (HC02-P12, HC02-P13) -/

/--
OET anchor: h-c80171fa685dc795 (i) (`HC02-P12`)
**Corollary (Local Lip matrix bound for finite compositions)**:
For `k ≥ 1`, if each step has a valid local Lip matrix `L^{(m)} ∈ ℒ(ϕₘ)|_{Uₘ}` on the
actual intermediate domain `Uₘ`, then `L^{(k)} · … · L^{(1)} ∈ ℒ(cₖ)|_{U₁}`.
-/
theorem finChain_lip_bound {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) :
    ∀ (k : ℕ), 1 ≤ k → ∀ (chain : LipChainData bot d k),
      finMatProd chain.stepMatrices ∈
        RestrictedLipSet d (finChainOp chain.ops) chain.startDomain
  | 0, hk, _ => absurd hk (by decide)
  | 1, _, chain => by
      rw [finMatProd_one, finChainOp_one]
      exact chain.step_valid 0
  | k + 2, _, chain => by
      have hk : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
      have h_pref := finChain_lip_bound d (k + 1) hk chain.prefix
      have h_last_dom :
          chainDomain chain.ops chain.startDomain (Fin.last (k + 1)).castSucc =
            operator_image (finChainOp chain.prefix.ops) chain.startDomain := by
        rw [← chainDomain_prefix chain.ops chain.startDomain (Fin.last (k + 1))]
        exact chainDomain_last_eq_operator_image chain.prefix.ops chain.startDomain
      have h_last :
          chain.stepMatrices (Fin.last (k + 1)) ∈
            RestrictedLipSet d (chain.ops (Fin.last (k + 1)))
              (operator_image (finChainOp chain.prefix.ops) chain.startDomain) := by
        rw [← h_last_dom]
        exact chain.step_valid (Fin.last (k + 1))
      rw [finMatProd_succ_last, finChainOp_succ_last]
      have hU1 : chain.startDomain ⊆
          dom (compOp (chain.ops (Fin.last (k + 1))) (finChainOp chain.prefix.ops)) := by
        simpa [LipChainData.prefix, finChainOp_succ_last] using chain.startDomain_subset
      exact restrictedLipSet_comp d (finChainOp chain.prefix.ops)
        (chain.ops (Fin.last (k + 1))) chain.startDomain hU1 h_pref h_last

/-- Unpacked version of `HC02-P12` taking the step operators and matrices directly. -/
theorem finChain_lip_bound_unpacked {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (k : ℕ) (hk : 1 ≤ k)
    (ϕ : Fin k → Operator X bot) (U1 : Set X) (hU1 : U1 ⊆ dom (finChainOp ϕ))
    (L : Fin k → GaugeMatrix I)
    (hL : ∀ m : Fin k, L m ∈ RestrictedLipSet d (ϕ m) (chainDomain ϕ U1 m.castSucc)) :
    finMatProd L ∈ RestrictedLipSet d (finChainOp ϕ) U1 :=
  finChain_lip_bound d k hk ⟨ϕ, U1, hU1, L, hL⟩

/--
OET anchor: h-c80171fa685dc795 (ii) (`HC02-P13`)
**Corollary (Local co-Lip matrix bound for finite compositions)**:
For `k ≥ 1`, if each step has a valid local co-Lip matrix `K^{(m)} ∈ 𝒦(ϕₘ)|_{Uₘ}` on the
actual intermediate domain `Uₘ` (each carrying nonemptiness of `Uₘ`), then
`K^{(k)} · … · K^{(1)} ∈ 𝒦(cₖ)|_{U₁}`.
-/
theorem finChain_coLip_bound {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) :
    ∀ (k : ℕ), 1 ≤ k → ∀ (chain : CoLipChainData bot d k),
      finMatProd chain.stepMatrices ∈
        CoLipSet d (finChainOp chain.ops) chain.startDomain
  | 0, hk, _ => absurd hk (by decide)
  | 1, _, chain => by
      rw [finMatProd_one, finChainOp_one]
      exact chain.step_valid 0
  | k + 2, _, chain => by
      have hk : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
      have h_pref := finChain_coLip_bound d (k + 1) hk chain.prefix
      have h_last_dom :
          chainDomain chain.ops chain.startDomain (Fin.last (k + 1)).castSucc =
            operator_image (finChainOp chain.prefix.ops) chain.startDomain := by
        rw [← chainDomain_prefix chain.ops chain.startDomain (Fin.last (k + 1))]
        exact chainDomain_last_eq_operator_image chain.prefix.ops chain.startDomain
      have h_last :
          chain.stepMatrices (Fin.last (k + 1)) ∈
            CoLipSet d (chain.ops (Fin.last (k + 1)))
              (operator_image (finChainOp chain.prefix.ops) chain.startDomain) := by
        rw [← h_last_dom]
        exact chain.step_valid (Fin.last (k + 1))
      rw [finMatProd_succ_last, finChainOp_succ_last]
      have hU1 : chain.startDomain ⊆
          dom (compOp (chain.ops (Fin.last (k + 1))) (finChainOp chain.prefix.ops)) := by
        simpa [CoLipChainData.prefix, finChainOp_succ_last] using chain.startDomain_subset
      exact coLipSet_comp d (finChainOp chain.prefix.ops)
        (chain.ops (Fin.last (k + 1))) chain.startDomain hU1 h_pref h_last

/-- Unpacked version of `HC02-P13` taking the step operators and matrices directly. -/
theorem finChain_coLip_bound_unpacked {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (k : ℕ) (hk : 1 ≤ k)
    (ϕ : Fin k → Operator X bot) (U1 : Set X) (hU1 : U1 ⊆ dom (finChainOp ϕ))
    (K : Fin k → GaugeMatrix I)
    (hK : ∀ m : Fin k, K m ∈ CoLipSet d (ϕ m) (chainDomain ϕ U1 m.castSucc)) :
    finMatProd K ∈ CoLipSet d (finChainOp ϕ) U1 :=
  finChain_coLip_bound d k hk ⟨ϕ, U1, hU1, K, hK⟩

/-! ### 3. Zero-Step Identity Certificates (HC02-P14, HC02-P15) -/

/-- Exact identity-matrix summation formula: `∑ i, I_{i → j} * d_i(x, y) = d_j(x, y)`. -/
theorem idMatrix_sum_eq_dist {X I : Type} [Fintype I]
    (d : I → X → X → ENNReal) (x y : X) (j : I) :
    (∑ i : I, idMatrix i j * d i x y) = d j x y := by
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    rw [idMatrix_apply_ne hij, zero_mul]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/--
OET anchor: h-11006ddd8c43bfec (`HC02-P14`)
For any `U ⊆ dom(id_X)`, the identity matrix `I` is a valid restricted Lip matrix for `id_X`.
-/
theorem idMatrix_mem_restrictedLipSet {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) {U : Set X} (hU : U ⊆ dom (idOp (bot := bot))) :
    idMatrix ∈ RestrictedLipSet d (idOp (bot := bot)) U := by
  refine ⟨hU, ?_⟩
  intro x _ y _ j
  simp [idMatrix_sum_eq_dist]

/-- Zero-step (`k = 0`) boundary formulation of `HC02-P14`:
for `c₀ = id_X`, empty product `= I`, and nonempty `U ⊆ dom(c₀)`, `I ∈ ℒ(c₀)|_U`. -/
theorem zeroStep_lip_bound {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal)
    (ϕ : Fin 0 → Operator X bot) (L : Fin 0 → GaugeMatrix I)
    {U : Set X} (_hU_ne : U.Nonempty) (hU : U ⊆ dom (finChainOp ϕ)) :
    finMatProd L ∈ RestrictedLipSet d (finChainOp ϕ) U := by
  rw [finMatProd_zero, finChainOp_zero]
  exact idMatrix_mem_restrictedLipSet d (by simpa [finChainOp_zero] using hU)

/--
OET anchor: h-11006ddd8c43bfec (`HC02-P15`)
For any nonempty `U ⊆ dom(id_X)`, the identity matrix `I` is a valid restricted co-Lip
matrix for `id_X`.
-/
theorem idMatrix_mem_coLipSet {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) {U : Set X}
    (hU_ne : U.Nonempty) (hU : U ⊆ dom (idOp (bot := bot))) :
    idMatrix ∈ CoLipSet d (idOp (bot := bot)) U := by
  refine ⟨hU_ne, hU, ?_⟩
  intro x _ y _ j
  simp [idMatrix_sum_eq_dist]

/-- Zero-step (`k = 0`) boundary formulation of `HC02-P15`:
for `c₀ = id_X`, empty product `= I`, and nonempty `U ⊆ dom(c₀)`, `I ∈ 𝒦(c₀)|_U`. -/
theorem zeroStep_coLip_bound {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal)
    (ϕ : Fin 0 → Operator X bot) (K : Fin 0 → GaugeMatrix I)
    {U : Set X} (hU_ne : U.Nonempty) (hU : U ⊆ dom (finChainOp ϕ)) :
    finMatProd K ∈ CoLipSet d (finChainOp ϕ) U := by
  rw [finMatProd_zero, finChainOp_zero]
  exact idMatrix_mem_coLipSet d hU_ne (by simpa [finChainOp_zero] using hU)

/-- Combined intersection form of Remark `#h-11006ddd8c43bfec`:
`I ∈ ℒ(id_X)|_U ∩ 𝒦(id_X)|_U` for any nonempty `U ⊆ dom(id_X)`. -/
theorem idMatrix_mem_restrictedLipSet_inter_coLipSet {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) {U : Set X}
    (hU_ne : U.Nonempty) (hU : U ⊆ dom (idOp (bot := bot))) :
    idMatrix ∈ RestrictedLipSet d (idOp (bot := bot)) U ∩ CoLipSet d (idOp (bot := bot)) U :=
  ⟨idMatrix_mem_restrictedLipSet d hU, idMatrix_mem_coLipSet d hU_ne hU⟩

/-! ### 4. Zero and Positivity Criteria for Finite Matrix Products (HC02-P16, HC02-P17) -/

/-- General algebraic zero criterion for finite `ENNReal` matrix products (`n ≥ 1`):
`(M^{(n)} · … · M^{(1)})_{i → j} = 0` iff every intermediate index sequence has at least
one zero step entry. -/
theorem finMatProd_apply_eq_zero_iff {I : Type} [Fintype I]
    (n : ℕ) (hn : 1 ≤ n) (M : Fin n → GaugeMatrix I) (i j : I) :
    finMatProd M i j = 0 ↔ ∀ mid : MidIndexSeq I n, PathHasZero n M i j mid := by
  rw [finMatProd_apply_eq_sum_paths n hn M i j, Finset.sum_eq_zero_iff]
  simp [pathWeight_eq_zero_iff]

/-- General algebraic positivity criterion for finite `ENNReal` matrix products (`n ≥ 1`):
`(M^{(n)} · … · M^{(1)})_{i → j} > 0` iff there exists at least one intermediate index
sequence whose step entries are all strictly positive. -/
theorem finMatProd_apply_pos_iff {I : Type} [Fintype I]
    (n : ℕ) (hn : 1 ≤ n) (M : Fin n → GaugeMatrix I) (i j : I) :
    0 < finMatProd M i j ↔ ∃ mid : MidIndexSeq I n, PathAllPos n M i j mid := by
  rw [pos_iff_ne_zero, ne_eq, finMatProd_apply_eq_zero_iff n hn M i j]
  push Not
  constructor
  · rintro ⟨mid, hmid⟩
    refine ⟨mid, ?_⟩
    rw [← pathWeight_pos_iff, pos_iff_ne_zero, ne_eq, pathWeight_eq_zero_iff]
    exact hmid
  · rintro ⟨mid, hmid⟩
    refine ⟨mid, ?_⟩
    rw [← pathWeight_eq_zero_iff, ← ne_eq, ← pos_iff_ne_zero, pathWeight_pos_iff]
    exact hmid

/--
OET anchor: h-e4154c34e95d3c23 (i) (`HC02-P16`)
**Proposition (Zero criterion for finite Lip matrix product entries)**:
Along a finite operator chain (`n ≥ 1`) with local Lip certificates `L^{(m)} ∈ ℒ(ϕₘ)|_{Uₘ}`,
`[L^{(n)} · … · L^{(1)}]_{i → j} = 0` iff every intermediate index sequence `(k₁, …, k_{n-1})`
contains at least one layer `m` with `[L^{(m)}]_{k_{m-1} → k_m} = 0`.
-/
theorem lipChain_prod_entry_eq_zero_iff {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (n : ℕ) (hn : 1 ≤ n)
    (chain : LipChainData bot d n) (i j : I) :
    finMatProd chain.stepMatrices i j = 0 ↔
      ∀ mid : MidIndexSeq I n, PathHasZero n chain.stepMatrices i j mid :=
  finMatProd_apply_eq_zero_iff n hn chain.stepMatrices i j

/-- `n = 1` degeneration of `HC02-P16`: the unique empty intermediate sequence reduces
the path criterion directly to `[L^{(1)}]_{i → j} = 0`. -/
theorem lipChain_prod_entry_eq_zero_one {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (chain : LipChainData bot d 1) (i j : I) :
    (∀ mid : MidIndexSeq I 1, PathHasZero 1 chain.stepMatrices i j mid) ↔
      chain.stepMatrices 0 i j = 0 := by
  rw [← lipChain_prod_entry_eq_zero_iff d 1 le_rfl chain i j, finMatProd_one]

/--
OET anchor: h-e4154c34e95d3c23 (ii) (`HC02-P17`)
**Proposition (Positivity criterion for finite co-Lip matrix product entries)**:
Along a finite operator chain (`n ≥ 1`) with local co-Lip certificates `K^{(m)} ∈ 𝒦(ϕₘ)|_{Uₘ}`,
`[K^{(n)} · … · K^{(1)}]_{i → j} > 0` iff there exists at least one intermediate index sequence
`(k₁, …, k_{n-1})` along which every step entry `[K^{(m)}]_{k_{m-1} → k_m} > 0`.
-/
theorem coLipChain_prod_entry_pos_iff {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (n : ℕ) (hn : 1 ≤ n)
    (chain : CoLipChainData bot d n) (i j : I) :
    0 < finMatProd chain.stepMatrices i j ↔
      ∃ mid : MidIndexSeq I n, PathAllPos n chain.stepMatrices i j mid :=
  finMatProd_apply_pos_iff n hn chain.stepMatrices i j

/-- `n = 1` degeneration of `HC02-P17`: the unique empty intermediate sequence reduces
the path criterion directly to `[K^{(1)}]_{i → j} > 0`. -/
theorem coLipChain_prod_entry_pos_one {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (chain : CoLipChainData bot d 1) (i j : I) :
    (∃ mid : MidIndexSeq I 1, PathAllPos 1 chain.stepMatrices i j mid) ↔
      0 < chain.stepMatrices 0 i j := by
  rw [← coLipChain_prod_entry_pos_iff d 1 le_rfl chain i j, finMatProd_one]

end OetCh02
