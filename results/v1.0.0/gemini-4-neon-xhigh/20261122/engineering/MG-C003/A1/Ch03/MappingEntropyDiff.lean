/-
Formalization of Chapter 3 (Section 3.6: Mapping Entropy Difference)
of "The Operator Evolution Theory, Volume I" by Zhe Li (Glen Li / glenzli), CC BY 4.0.
-/
import Ch03.ScaleAndCovering

namespace Ch03

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set

/-! ### Section 3.6: Mapping Entropy Difference (CH03-D08) -/

/-- Well-definedness premise for the mapping entropy difference `ΔE_{ε, J_in, J_out}(ϕ | U)`:
at least one of the input or output covering numbers is finite (excluding `∞ - ∞`). -/
def MappingEntropyDiffWellDefined {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (J_in J_out : Set I) (ε : ENNReal)
    (ϕ : Operator X bot) (U : Set X) : Prop :=
  subfamily_covering_number d J_in ε U < ⊤ ∨
    subfamily_covering_number d J_out ε (operator_image ϕ U) < ⊤

/-- Mapping entropy difference `ΔE_{ε, J_in, J_out}(ϕ | U) := E_{ε, J_in}(U) - E_{ε, J_out}(ϕ(U))`,
defined only under the well-definedness premise `MappingEntropyDiffWellDefined`. -/
noncomputable def mappingEntropyDiff {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (J_in J_out : Set I) (ε : ENNReal)
    (ϕ : Operator X bot) (U : Set X)
    (_hwd : MappingEntropyDiffWellDefined d J_in J_out ε ϕ U) : EReal :=
  subfamily_metric_entropy d J_in ε U -
    subfamily_metric_entropy d J_out ε (operator_image ϕ U)

/-- Same-subfamily abbreviation `ΔE_{ε, J}(ϕ | U)`. -/
noncomputable def mappingEntropyDiffSame {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (J : Set I) (ε : ENNReal)
    (ϕ : Operator X bot) (U : Set X)
    (hwd : MappingEntropyDiffWellDefined d J J ε ϕ U) : EReal :=
  mappingEntropyDiff d J J ε ϕ U hwd

/-- Single-component channel abbreviation `ΔE_{ε, i, j}(ϕ | U)`. -/
noncomputable def mappingEntropyDiffComp {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (i j : I) (ε : ENNReal)
    (ϕ : Operator X bot) (U : Set X)
    (hwd : MappingEntropyDiffWellDefined d ({i} : Set I) ({j} : Set I) ε ϕ U) : EReal :=
  mappingEntropyDiff d ({i} : Set I) ({j} : Set I) ε ϕ U hwd

/-- Same single-component abbreviation `ΔE_{ε, j}(ϕ | U)`. -/
noncomputable def mappingEntropyDiffCompSame {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (j : I) (ε : ENNReal)
    (ϕ : Operator X bot) (U : Set X)
    (hwd : MappingEntropyDiffWellDefined d ({j} : Set I) ({j} : Set I) ε ϕ U) : EReal :=
  mappingEntropyDiff d ({j} : Set I) ({j} : Set I) ε ϕ U hwd

theorem mappingEntropyDiffWellDefined_comp_iff {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (i j : I) (ε : ENNReal)
    (ϕ : Operator X bot) (U : Set X) :
    MappingEntropyDiffWellDefined d ({i} : Set I) ({j} : Set I) ε ϕ U ↔
      covering_number (d i) ε U < ⊤ ∨
        covering_number (d j) ε (operator_image ϕ U) < ⊤ := by
  simp [MappingEntropyDiffWellDefined, subfamily_covering_number_singleton]

theorem mappingEntropyDiffComp_eq {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (i j : I) (ε : ENNReal)
    (ϕ : Operator X bot) (U : Set X)
    (hwd : MappingEntropyDiffWellDefined d ({i} : Set I) ({j} : Set I) ε ϕ U) :
    mappingEntropyDiffComp d i j ε ϕ U hwd =
      metric_entropy (d i) ε U - metric_entropy (d j) ε (operator_image ϕ U) := by
  simp [mappingEntropyDiffComp, mappingEntropyDiff, subfamily_metric_entropy_singleton]

/-- Explicit case evaluation of `mappingEntropyDiff` in all three well-defined regimes. -/
theorem mappingEntropyDiff_cases {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (J_in J_out : Set I) (ε : ENNReal)
    (ϕ : Operator X bot) (U : Set X) (hU : U.Nonempty) :
    (subfamily_covering_number d J_in ε U < ⊤ →
      subfamily_covering_number d J_out ε (operator_image ϕ U) < ⊤ →
      ∀ hwd : MappingEntropyDiffWellDefined d J_in J_out ε ϕ U,
      mappingEntropyDiff d J_in J_out ε ϕ U hwd =
        ↑(Real.logb 2 (subfamily_covering_number d J_in ε U).toReal -
          Real.logb 2 (subfamily_covering_number d J_out ε (operator_image ϕ U)).toReal)) ∧
    (subfamily_covering_number d J_in ε U = ⊤ →
      subfamily_covering_number d J_out ε (operator_image ϕ U) < ⊤ →
      ∀ hwd : MappingEntropyDiffWellDefined d J_in J_out ε ϕ U,
      mappingEntropyDiff d J_in J_out ε ϕ U hwd = ⊤) ∧
    (subfamily_covering_number d J_in ε U < ⊤ →
      subfamily_covering_number d J_out ε (operator_image ϕ U) = ⊤ →
      ∀ hwd : MappingEntropyDiffWellDefined d J_in J_out ε ϕ U,
      mappingEntropyDiff d J_in J_out ε ϕ U hwd = ⊥) := by
  have himg_ne : (operator_image ϕ U).Nonempty := hU.image ϕ.func
  refine ⟨?_, ?_, ?_⟩
  · intro h1 h2 hwd
    unfold mappingEntropyDiff
    rw [subfamily_metric_entropy_eq_metric_entropy, subfamily_metric_entropy_eq_metric_entropy]
    rw [metric_entropy_eq_coe_of_nonempty_of_lt_top hU h1,
        metric_entropy_eq_coe_of_nonempty_of_lt_top himg_ne h2]
    rfl
  · intro h1 h2 hwd
    unfold mappingEntropyDiff
    rw [subfamily_metric_entropy_eq_metric_entropy, subfamily_metric_entropy_eq_metric_entropy]
    rw [(metric_entropy_eq_top_iff _ _ _).mpr h1,
        metric_entropy_eq_coe_of_nonempty_of_lt_top himg_ne h2]
    simp
  · intro h1 h2 hwd
    unfold mappingEntropyDiff
    rw [subfamily_metric_entropy_eq_metric_entropy, subfamily_metric_entropy_eq_metric_entropy]
    rw [metric_entropy_eq_coe_of_nonempty_of_lt_top hU h1,
        (metric_entropy_eq_top_iff _ _ _).mpr h2]
    simp

/-! ### Remark: Well-Definedness on Nonempty Finite Sets (CH03-P22-01) -/

/-- Helper: A finite set is covered by itself at any positive radius `ε`. -/
theorem covering_number_le_card_of_finite {X : Type} {bot : X}
    {d : X → X → ENNReal} (hd : ExtendedPseudoMetric X bot d)
    {ε : ENNReal} (hε_pos : 0 < ε) {S : Set X} (hS : S.Finite) :
    covering_number d ε S ≤ (hS.toFinset.card : ENNReal) := by
  have hnet : InternalEpsilonNet d ε S hS.toFinset := by
    constructor
    · intro c hc
      simpa using hc
    · intro x hx
      refine ⟨x, hS.mem_toFinset.mpr hx, ?_⟩
      rw [hd.dist_self x]
      exact hε_pos
  exact covering_number_le_of_net hnet

/-- Remark (CH03-P22-01): If `U ⊆ dom ϕ` is nonempty and finite, then for any nonempty
subfamilies `J_in, J_out` and any finite positive `ε`, both covering numbers are positive and
finite, both metric entropies are finite reals, and `ΔE` is well-defined. -/
theorem remark_finite_mapping_entropy_diff_well_defined {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ k : I, ExtendedPseudoMetric X bot (d k))
    (ϕ : Operator X bot) (U : Set X) (J_in J_out : Set I) (ε : ENNReal)
    (hUne : U.Nonempty) (hUfin : U.Finite) (_hUdom : U ⊆ dom ϕ)
    (hJin : J_in.Nonempty) (hJout : J_out.Nonempty)
    (hε_pos : 0 < ε) (_hε_fin : ε < ⊤) :
    (1 ≤ subfamily_covering_number d J_in ε U ∧
      subfamily_covering_number d J_in ε U < ⊤) ∧
    (1 ≤ subfamily_covering_number d J_out ε (operator_image ϕ U) ∧
      subfamily_covering_number d J_out ε (operator_image ϕ U) < ⊤) ∧
    (∃ r₁ : ℝ, subfamily_metric_entropy d J_in ε U = ↑r₁) ∧
    (∃ r₂ : ℝ, subfamily_metric_entropy d J_out ε (operator_image ϕ U) = ↑r₂) ∧
    MappingEntropyDiffWellDefined d J_in J_out ε ϕ U := by
  have hd_in := subfamily_pseudometric_is_extended d J_in hJin hd
  have hd_out := subfamily_pseudometric_is_extended d J_out hJout hd
  have himg_ne : (operator_image ϕ U).Nonempty := hUne.image ϕ.func
  have himg_fin : (operator_image ϕ U).Finite := hUfin.image ϕ.func
  have h1_in : 1 ≤ subfamily_covering_number d J_in ε U :=
    one_le_covering_number_of_nonempty _ ε U hUne
  have hfin_in : subfamily_covering_number d J_in ε U < ⊤ :=
    lt_of_le_of_lt (covering_number_le_card_of_finite hd_in hε_pos hUfin)
      (ENNReal.natCast_lt_top _)
  have h1_out : 1 ≤ subfamily_covering_number d J_out ε (operator_image ϕ U) :=
    one_le_covering_number_of_nonempty _ ε (operator_image ϕ U) himg_ne
  have hfin_out : subfamily_covering_number d J_out ε (operator_image ϕ U) < ⊤ :=
    lt_of_le_of_lt (covering_number_le_card_of_finite hd_out hε_pos himg_fin)
      (ENNReal.natCast_lt_top _)
  refine ⟨⟨h1_in, hfin_in⟩, ⟨h1_out, hfin_out⟩, ?_, ?_, Or.inl hfin_in⟩
  · exact ⟨Real.logb 2 (subfamily_covering_number d J_in ε U).toReal,
      metric_entropy_eq_coe_of_nonempty_of_lt_top hUne hfin_in⟩
  · exact ⟨Real.logb 2 (subfamily_covering_number d J_out ε (operator_image ϕ U)).toReal,
      metric_entropy_eq_coe_of_nonempty_of_lt_top himg_ne hfin_out⟩

/-! ### Proposition 3.18: Component Partition and Mapping Entropy Difference (CH03-P23-01..03) -/

/-- Proposition 3.18(i): If `j ∈ I_const(ϕ | U)`, then `N_j(ε, ϕ(U)) = 1`, `E_{ε, j}(ϕ(U)) = 0`,
`ΔE_{ε, j}(ϕ | U)` is well-defined (even if input entropy is `+∞`), and equals `E_{ε, j}(U)`. -/
theorem prop_3_18_i {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (ε : ENNReal) (j : I)
    (hUne : U.Nonempty) (_hUdom : U ⊆ dom ϕ)
    (hε_pos : 0 < ε) (_hε_fin : ε < ⊤) (hj : j ∈ I_const d ϕ U) :
    covering_number (d j) ε (operator_image ϕ U) = 1 ∧
    metric_entropy (d j) ε (operator_image ϕ U) = 0 ∧
    MappingEntropyDiffWellDefined d ({j} : Set I) ({j} : Set I) ε ϕ U ∧
    ∀ hwd : MappingEntropyDiffWellDefined d ({j} : Set I) ({j} : Set I) ε ϕ U,
      mappingEntropyDiffCompSame d j ε ϕ U hwd = metric_entropy (d j) ε U := by
  rcases hUne with ⟨x₀, hx₀⟩
  have himg_ne : (operator_image ϕ U).Nonempty := ⟨ϕ.func x₀, ⟨x₀, hx₀, rfl⟩⟩
  have hcov : covering_number (d j) ε (operator_image ϕ U) = 1 := by
    apply le_antisymm
    · have hnet : InternalEpsilonNet (d j) ε (operator_image ϕ U) {ϕ.func x₀} := by
        constructor
        · intro c hc
          simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hc
          subst hc
          exact ⟨x₀, hx₀, rfl⟩
        · rintro y ⟨x, hxU, rfl⟩
          refine ⟨ϕ.func x₀, Finset.mem_singleton_self _, ?_⟩
          rw [hj x hxU x₀ hx₀]
          exact hε_pos
      simpa using covering_number_le_of_net hnet
    · exact one_le_covering_number_of_nonempty (d j) ε (operator_image ϕ U) himg_ne
  have hent : metric_entropy (d j) ε (operator_image ϕ U) = 0 := by
    rw [metric_entropy, hcov, log2_ereal_one]
  have hwd : MappingEntropyDiffWellDefined d ({j} : Set I) ({j} : Set I) ε ϕ U := by
    rw [mappingEntropyDiffWellDefined_comp_iff]
    right
    rw [hcov]
    exact ENNReal.one_lt_top
  refine ⟨hcov, hent, hwd, ?_⟩
  intro hwd'
  change mappingEntropyDiffComp d j j ε ϕ U hwd' = metric_entropy (d j) ε U
  rw [mappingEntropyDiffComp_eq, hent, sub_zero]

/-- Proposition 3.18(ii-a): If `j ∈ I_id(ϕ | U)`, then `N_j(ε, ϕ(U)) = N_j(ε, U)` and
`E_{ε, j}(ϕ(U)) = E_{ε, j}(U)`. -/
theorem prop_3_18_ii_a {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ k : I, ExtendedPseudoMetric X bot (d k))
    (ϕ : Operator X bot) (U : Set X) (ε : ENNReal) (j : I)
    (_hUne : U.Nonempty) (hUdom : U ⊆ dom ϕ)
    (_hε_pos : 0 < ε) (_hε_fin : ε < ⊤) (hj : j ∈ I_id d ϕ U) :
    covering_number (d j) ε (operator_image ϕ U) = covering_number (d j) ε U ∧
    metric_entropy (d j) ε (operator_image ϕ U) = metric_entropy (d j) ε U := by
  classical
  have hiso := prop_3_1_iii d ϕ U j (hd j) hUdom hj
  have hcov : covering_number (d j) ε (operator_image ϕ U) = covering_number (d j) ε U := by
    apply le_antisymm
    · rw [le_covering_number_iff]
      intro S hS
      have hnet : InternalEpsilonNet (d j) ε (operator_image ϕ U) (S.image ϕ.func) := by
        constructor
        · intro y hy
          rcases Finset.mem_image.mp (by simpa using hy) with ⟨s, hs, rfl⟩
          exact ⟨s, hS.1 hs, rfl⟩
        · rintro y ⟨x, hxU, rfl⟩
          rcases hS.2 x hxU with ⟨s, hs, hdist⟩
          refine ⟨ϕ.func s, Finset.mem_image_of_mem ϕ.func hs, ?_⟩
          rw [hiso x hxU s (hS.1 hs)]
          exact hdist
      calc
        covering_number (d j) ε (operator_image ϕ U)
            ≤ ((S.image ϕ.func).card : ENNReal) := covering_number_le_of_net hnet
        _ ≤ (S.card : ENNReal) := by exact_mod_cast Finset.card_image_le
    · rw [le_covering_number_iff]
      intro T hT
      let pick : X → X := fun t => if h : t ∈ operator_image ϕ U then Classical.choose h else bot
      have hnet : InternalEpsilonNet (d j) ε U (T.image pick) := by
        constructor
        · intro c hc
          rcases Finset.mem_image.mp (by simpa using hc) with ⟨t, ht, rfl⟩
          have htimg : t ∈ operator_image ϕ U := hT.1 ht
          simp only [pick, dif_pos htimg]
          exact (Classical.choose_spec htimg).1
        · intro x hxU
          rcases hT.2 (ϕ.func x) ⟨x, hxU, rfl⟩ with ⟨t, ht, hdist⟩
          have htimg : t ∈ operator_image ϕ U := hT.1 ht
          refine ⟨pick t, Finset.mem_image_of_mem pick ht, ?_⟩
          have hpick_mem : pick t ∈ U := by
            simp only [pick, dif_pos htimg]
            exact (Classical.choose_spec htimg).1
          have hpick_eq : ϕ.func (pick t) = t := by
            simp only [pick, dif_pos htimg]
            exact (Classical.choose_spec htimg).2
          rw [← hiso x hxU (pick t) hpick_mem, hpick_eq]
          exact hdist
      calc
        covering_number (d j) ε U
            ≤ ((T.image pick).card : ENNReal) := covering_number_le_of_net hnet
        _ ≤ (T.card : ENNReal) := by exact_mod_cast Finset.card_image_le
  exact ⟨hcov, by simp [metric_entropy, hcov]⟩

/-- Proposition 3.18(ii-b): If `j ∈ I_id(ϕ | U)` and `ΔE_{ε, j}(ϕ | U)` is well-defined
(excluding `∞ - ∞`), then `ΔE_{ε, j}(ϕ | U) = 0`. -/
theorem prop_3_18_ii_b {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ k : I, ExtendedPseudoMetric X bot (d k))
    (ϕ : Operator X bot) (U : Set X) (ε : ENNReal) (j : I)
    (hUne : U.Nonempty) (hUdom : U ⊆ dom ϕ)
    (hε_pos : 0 < ε) (hε_fin : ε < ⊤) (hj : j ∈ I_id d ϕ U)
    (hwd : MappingEntropyDiffWellDefined d ({j} : Set I) ({j} : Set I) ε ϕ U) :
    mappingEntropyDiffCompSame d j ε ϕ U hwd = 0 := by
  have heq := prop_3_18_ii_a d hd ϕ U ε j hUne hUdom hε_pos hε_fin hj
  have hfin : covering_number (d j) ε U < ⊤ := by
    rw [mappingEntropyDiffWellDefined_comp_iff] at hwd
    rcases hwd with h1 | h2
    · exact h1
    · rwa [heq.1] at h2
  change mappingEntropyDiffComp d j j ε ϕ U hwd = 0
  rw [mappingEntropyDiffComp_eq, heq.2]
  rw [metric_entropy_eq_coe_of_nonempty_of_lt_top hUne hfin]
  exact_mod_cast sub_self (Real.logb 2 (covering_number (d j) ε U).toReal)

/-! ### Proposition 3.19: Single-Channel Lip Upper Bound and Entropy Difference Lower Bound (CH03-P24-01..02) -/

/-- Proposition 3.19 (net pushforward): A finite positive single-channel Lip constant `L` pushes
any internal `(ε / L)`-net of `U` to an internal `ε`-net of `ϕ(U)` without increasing cardinality. -/
theorem prop_3_19_net_pushforward {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i j : I)
    (ε L : ENNReal) (_hε_pos : 0 < ε) (_hε_fin : ε < ⊤) (_hL_pos : 0 < L) (_hL_fin : L < ⊤)
    (hLip : ∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ L * d i x y)
    {S : Finset X} (hS : InternalEpsilonNet (d i) (ε / L) U S) :
    letI := Classical.decEq X
    InternalEpsilonNet (d j) ε (operator_image ϕ U) (S.image ϕ.func) ∧
      (S.image ϕ.func).card ≤ S.card := by
  classical
  refine ⟨⟨?_, ?_⟩, Finset.card_image_le⟩
  · intro y hy
    rcases Finset.mem_image.mp (by simpa using hy) with ⟨s, hs, rfl⟩
    exact ⟨s, hS.1 hs, rfl⟩
  · rintro y ⟨x, hxU, rfl⟩
    rcases hS.2 x hxU with ⟨c, hc, hdist⟩
    refine ⟨ϕ.func c, Finset.mem_image_of_mem ϕ.func hc, ?_⟩
    have hmul : L * d i x c < ε := by
      rw [mul_comm]
      exact ENNReal.mul_lt_of_lt_div hdist
    exact lt_of_le_of_lt (hLip x hxU c (hS.1 hc)) hmul

/-- Proposition 3.19 (covering number upper bound): `N_j(ε, ϕ(U)) ≤ N_i(ε / L, U)`. -/
theorem prop_3_19_covering_le {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i j : I)
    (ε L : ENNReal) (hε_pos : 0 < ε) (hε_fin : ε < ⊤) (hL_pos : 0 < L) (hL_fin : L < ⊤)
    (hLip : ∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ L * d i x y) :
    covering_number (d j) ε (operator_image ϕ U) ≤ covering_number (d i) (ε / L) U := by
  classical
  rw [le_covering_number_iff]
  intro S hS
  have hpush := prop_3_19_net_pushforward d ϕ U i j ε L hε_pos hε_fin hL_pos hL_fin hLip hS
  calc
    covering_number (d j) ε (operator_image ϕ U)
        ≤ ((S.image ϕ.func).card : ENNReal) := covering_number_le_of_net hpush.1
    _ ≤ (S.card : ENNReal) := by exact_mod_cast hpush.2

/-- Proposition 3.19 (entropy difference lower bound): When `U` is totally bounded in `d_i`,
both covering numbers are finite, `ΔE_{ε, i, j}(ϕ | U)` is well-defined, and
`ΔE_{ε, i, j}(ϕ | U) ≥ E_{ε, i}(U) - E_{ε / L, i}(U)`. -/
theorem prop_3_19_entropy_diff_ge {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i j : I)
    (ε L : ENNReal)
    (hUne : U.Nonempty) (_hUdom : U ⊆ dom ϕ)
    (hTB : IsTotallyBounded (d i) U)
    (hε_pos : 0 < ε) (hε_fin : ε < ⊤) (hL_pos : 0 < L) (hL_fin : L < ⊤)
    (hLip : ∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ L * d i x y) :
    covering_number (d i) ε U < ⊤ ∧
    covering_number (d j) ε (operator_image ϕ U) < ⊤ ∧
    MappingEntropyDiffWellDefined d ({i} : Set I) ({j} : Set I) ε ϕ U ∧
    ∀ hwd : MappingEntropyDiffWellDefined d ({i} : Set I) ({j} : Set I) ε ϕ U,
      metric_entropy (d i) ε U - metric_entropy (d i) (ε / L) U ≤
        mappingEntropyDiffComp d i j ε ϕ U hwd := by
  have hcov_le := prop_3_19_covering_le d ϕ U i j ε L hε_pos hε_fin hL_pos hL_fin hLip
  have hεL_pos : 0 < ε / L := ENNReal.div_pos (ne_of_gt hε_pos) (ne_of_lt hL_fin)
  have hεL_fin : ε / L < ⊤ := ENNReal.div_lt_top (ne_of_lt hε_fin) (ne_of_gt hL_pos)
  have hfin_in : covering_number (d i) ε U < ⊤ := hTB ε hε_pos hε_fin
  have hfin_inL : covering_number (d i) (ε / L) U < ⊤ := hTB (ε / L) hεL_pos hεL_fin
  have hfin_out : covering_number (d j) ε (operator_image ϕ U) < ⊤ :=
    lt_of_le_of_lt hcov_le hfin_inL
  have himg_ne : (operator_image ϕ U).Nonempty := hUne.image ϕ.func
  have hwd : MappingEntropyDiffWellDefined d ({i} : Set I) ({j} : Set I) ε ϕ U := by
    rw [mappingEntropyDiffWellDefined_comp_iff]
    exact Or.inl hfin_in
  refine ⟨hfin_in, hfin_out, hwd, ?_⟩
  intro hwd'
  rw [mappingEntropyDiffComp_eq]
  have hent_le : metric_entropy (d j) ε (operator_image ϕ U) ≤ metric_entropy (d i) (ε / L) U :=
    metric_entropy_mono_of_covering_number_le hcov_le
  rw [metric_entropy_eq_coe_of_nonempty_of_lt_top hUne hfin_inL,
      metric_entropy_eq_coe_of_nonempty_of_lt_top himg_ne hfin_out] at hent_le ⊢
  rw [metric_entropy_eq_coe_of_nonempty_of_lt_top hUne hfin_in]
  have hreal_le : Real.logb 2 (covering_number (d j) ε (operator_image ϕ U)).toReal ≤
      Real.logb 2 (covering_number (d i) (ε / L) U).toReal :=
    EReal.coe_le_coe_iff.mp hent_le
  change ((Real.logb 2 (covering_number (d i) ε U).toReal -
      Real.logb 2 (covering_number (d i) (ε / L) U).toReal : ℝ) : EReal) ≤
    ((Real.logb 2 (covering_number (d i) ε U).toReal -
      Real.logb 2 (covering_number (d j) ε (operator_image ϕ U)).toReal : ℝ) : EReal)
  exact EReal.coe_le_coe_iff.mpr (sub_le_sub_left hreal_le _)

/-! ### Proposition 3.20: co-Lip Constant and Entropy Difference Upper Bound (CH03-P25-01..02) -/

/-- Proposition 3.20 (net pullback): A finite positive co-Lip entry `K_{i → j}` pulls back any
internal `ε`-net `T` of `ϕ(U)` to an internal `(ε / K_{i → j})`-net `S` of `U` with `|S| ≤ |T|`. -/
theorem prop_3_20_net_pullback {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i j : I)
    (ε : ENNReal) (K : I → I → ENNReal)
    (_hε_pos : 0 < ε) (_hε_fin : ε < ⊤)
    (hK : IsCoLipMatrix d ϕ U K) (hK_pos : 0 < K i j) (hK_fin : K i j < ⊤)
    {T : Finset X} (hT : InternalEpsilonNet (d j) ε (operator_image ϕ U) T) :
    ∃ S : Finset X, InternalEpsilonNet (d i) (ε / K i j) U S ∧ S.card ≤ T.card := by
  classical
  let pick : X → X := fun t => if h : t ∈ operator_image ϕ U then Classical.choose h else bot
  refine ⟨T.image pick, ⟨?_, ?_⟩, Finset.card_image_le⟩
  · intro c hc
    rcases Finset.mem_image.mp (by simpa using hc) with ⟨t, ht, rfl⟩
    have htimg : t ∈ operator_image ϕ U := hT.1 ht
    simp only [pick, dif_pos htimg]
    exact (Classical.choose_spec htimg).1
  · intro x hxU
    rcases hT.2 (ϕ.func x) ⟨x, hxU, rfl⟩ with ⟨t, ht, hdist⟩
    have htimg : t ∈ operator_image ϕ U := hT.1 ht
    refine ⟨pick t, Finset.mem_image_of_mem pick ht, ?_⟩
    have hpick_mem : pick t ∈ U := by
      simp only [pick, dif_pos htimg]
      exact (Classical.choose_spec htimg).1
    have hpick_eq : ϕ.func (pick t) = t := by
      simp only [pick, dif_pos htimg]
      exact (Classical.choose_spec htimg).2
    have hcolip : K i j * d i x (pick t) ≤ d j (ϕ.func x) (ϕ.func (pick t)) := by
      calc
        K i j * d i x (pick t)
            ≤ ∑ k : I, K k j * d k x (pick t) :=
              Finset.single_le_sum (f := fun k => K k j * d k x (pick t))
                (fun _ _ => zero_le _) (Finset.mem_univ i)
        _ ≤ d j (ϕ.func x) (ϕ.func (pick t)) := hK.2.2 x hxU (pick t) hpick_mem j
    have hlt : d i x (pick t) * K i j < ε := by
      rw [mul_comm]
      exact lt_of_le_of_lt hcolip (by rw [hpick_eq]; exact hdist)
    exact (ENNReal.lt_div_iff_mul_lt (Or.inl (ne_of_gt hK_pos)) (Or.inl (ne_of_lt hK_fin))).mpr hlt

/-- Proposition 3.20 (covering number lower bound): `N_i(ε / K_{i → j}, U) ≤ N_j(ε, ϕ(U))`. -/
theorem prop_3_20_covering_ge {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i j : I)
    (ε : ENNReal) (K : I → I → ENNReal)
    (hε_pos : 0 < ε) (hε_fin : ε < ⊤)
    (hK : IsCoLipMatrix d ϕ U K) (hK_pos : 0 < K i j) (hK_fin : K i j < ⊤) :
    covering_number (d i) (ε / K i j) U ≤ covering_number (d j) ε (operator_image ϕ U) := by
  rw [le_covering_number_iff]
  intro T hT
  rcases prop_3_20_net_pullback d ϕ U i j ε K hε_pos hε_fin hK hK_pos hK_fin hT with
    ⟨S, hSnet, hScard⟩
  calc
    covering_number (d i) (ε / K i j) U
        ≤ (S.card : ENNReal) := covering_number_le_of_net hSnet
    _ ≤ (T.card : ENNReal) := by exact_mod_cast hScard

/-- Proposition 3.20 (entropy difference upper bound): When `U` is totally bounded in `d_i`
(allowing output entropy to be `+∞`), `ΔE_{ε, i, j}(ϕ | U)` is well-defined and satisfies
`ΔE_{ε, i, j}(ϕ | U) ≤ E_{ε, i}(U) - E_{ε / K_{i → j}, i}(U)`. -/
theorem prop_3_20_entropy_diff_le {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i j : I)
    (ε : ENNReal) (K : I → I → ENNReal)
    (hUne : U.Nonempty) (_hUdom : U ⊆ dom ϕ)
    (hTB : IsTotallyBounded (d i) U)
    (hε_pos : 0 < ε) (hε_fin : ε < ⊤)
    (hK : IsCoLipMatrix d ϕ U K) (hK_pos : 0 < K i j) (hK_fin : K i j < ⊤) :
    MappingEntropyDiffWellDefined d ({i} : Set I) ({j} : Set I) ε ϕ U ∧
    ∀ hwd : MappingEntropyDiffWellDefined d ({i} : Set I) ({j} : Set I) ε ϕ U,
      mappingEntropyDiffComp d i j ε ϕ U hwd ≤
        metric_entropy (d i) ε U - metric_entropy (d i) (ε / K i j) U := by
  have hcov_ge := prop_3_20_covering_ge d ϕ U i j ε K hε_pos hε_fin hK hK_pos hK_fin
  have hεK_pos : 0 < ε / K i j := ENNReal.div_pos (ne_of_gt hε_pos) (ne_of_lt hK_fin)
  have hεK_fin : ε / K i j < ⊤ := ENNReal.div_lt_top (ne_of_lt hε_fin) (ne_of_gt hK_pos)
  have hfin_in : covering_number (d i) ε U < ⊤ := hTB ε hε_pos hε_fin
  have hfin_inK : covering_number (d i) (ε / K i j) U < ⊤ := hTB (ε / K i j) hεK_pos hεK_fin
  have himg_ne : (operator_image ϕ U).Nonempty := hUne.image ϕ.func
  have hwd : MappingEntropyDiffWellDefined d ({i} : Set I) ({j} : Set I) ε ϕ U := by
    rw [mappingEntropyDiffWellDefined_comp_iff]
    exact Or.inl hfin_in
  refine ⟨hwd, ?_⟩
  intro hwd'
  rw [mappingEntropyDiffComp_eq]
  by_cases htop : covering_number (d j) ε (operator_image ϕ U) = ⊤
  · rw [(metric_entropy_eq_top_iff _ _ _).mpr htop,
        metric_entropy_eq_coe_of_nonempty_of_lt_top hUne hfin_in]
    simp
  · have hfin_out : covering_number (d j) ε (operator_image ϕ U) < ⊤ :=
      lt_top_iff_ne_top.mpr htop
    have hent_le : metric_entropy (d i) (ε / K i j) U ≤
        metric_entropy (d j) ε (operator_image ϕ U) :=
      metric_entropy_mono_of_covering_number_le hcov_ge
    rw [metric_entropy_eq_coe_of_nonempty_of_lt_top hUne hfin_inK,
        metric_entropy_eq_coe_of_nonempty_of_lt_top himg_ne hfin_out] at hent_le ⊢
    rw [metric_entropy_eq_coe_of_nonempty_of_lt_top hUne hfin_in]
    have hreal_le : Real.logb 2 (covering_number (d i) (ε / K i j) U).toReal ≤
        Real.logb 2 (covering_number (d j) ε (operator_image ϕ U)).toReal :=
      EReal.coe_le_coe_iff.mp hent_le
    change ((Real.logb 2 (covering_number (d i) ε U).toReal -
        Real.logb 2 (covering_number (d j) ε (operator_image ϕ U)).toReal : ℝ) : EReal) ≤
      ((Real.logb 2 (covering_number (d i) ε U).toReal -
        Real.logb 2 (covering_number (d i) (ε / K i j) U).toReal : ℝ) : EReal)
    exact EReal.coe_le_coe_iff.mpr (sub_le_sub_left hreal_le _)

end Ch03
