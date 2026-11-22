/-
Formalization of Chapter 3 (Section 3.2: Computational Fibers and Image Factorization)
of "The Operator Evolution Theory, Volume I" by Zhe Li (Glen Li / glenzli), CC BY 4.0.
-/
import Ch03.ComponentPartition
import formal_oet.vol_01.ch_01_foundations.metric_entropy

namespace Ch03

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set

/-! ### Section 3.2: Computational Fibers (CH03-D02) -/

/-- Computational fiber of target `y` under `ϕ` on restricted domain `U` with respect to
subfamily pseudometric `d_J`. -/
def compFiber {X I : Type} {bot : X} (d : I → X → X → ENNReal)
    (ϕ : Operator X bot) (J : Set I) (U : Set X) (y : X) : Set X :=
  { x ∈ U | subfamily_pseudometric d J (ϕ.func x) y = 0 }

/-- Single-component computational fiber `Fib_{ϕ, j}(y | U)`. -/
def compFiberSingle {X I : Type} {bot : X} (d : I → X → X → ENNReal)
    (ϕ : Operator X bot) (j : I) (U : Set X) (y : X) : Set X :=
  { x ∈ U | d j (ϕ.func x) y = 0 }

/-- Global computational fiber `Fib_{ϕ, J}(y) = Fib_{ϕ, J}(y | dom ϕ)`. -/
def compFiberGlobal {X I : Type} {bot : X} (d : I → X → X → ENNReal)
    (ϕ : Operator X bot) (J : Set I) (y : X) : Set X :=
  compFiber d ϕ J (dom ϕ) y

/-- Deduplicated family of computational fibers over image targets `y ∈ ϕ(U)`. -/
def compFiberFamily {X I : Type} {bot : X} (d : I → X → X → ENNReal)
    (ϕ : Operator X bot) (J : Set I) (U : Set X) : Set (Set X) :=
  (fun y => compFiber d ϕ J U y) '' (operator_image ϕ U)

theorem compFiber_singleton_eq_single {X I : Type} {bot : X} (d : I → X → X → ENNReal)
    (ϕ : Operator X bot) (j : I) (U : Set X) (y : X) :
    compFiber d ϕ ({j} : Set I) U y = compFiberSingle d ϕ j U y := by
  ext x
  simp [compFiber, compFiberSingle, subfamily_pseudometric_singleton]

/-- Subfamily pseudometric vanishes iff every component in the subfamily vanishes. -/
theorem subfamily_pseudometric_eq_zero_iff {X I : Type} (d : I → X → X → ENNReal)
    (J : Set I) (x y : X) :
    subfamily_pseudometric d J x y = 0 ↔ ∀ j ∈ J, d j x y = 0 := by
  constructor
  · intro h j hj
    have hle : d j x y ≤ subfamily_pseudometric d J x y :=
      le_iSup (fun k : {k // k ∈ J} => d k.1 x y) ⟨j, hj⟩
    rw [h] at hle
    exact le_antisymm hle (zero_le _)
  · intro h
    apply le_antisymm _ (zero_le _)
    dsimp [subfamily_pseudometric]
    apply iSup_le
    intro j
    rw [h j.1 j.2]

/-- For a finite nonempty subfamily `J ⊆ I`, `subfamily_pseudometric d J` coincides with the
finite maximum `max_{j ∈ J} d_j(x, y)`. -/
theorem subfamily_pseudometric_eq_finset_sup' {X I : Type} [Fintype I]
    (d : I → X → X → ENNReal) (J : Set I) (hJ : J.Nonempty) (x y : X) :
    subfamily_pseudometric d J x y =
      J.toFinite.toFinset.sup' (by simpa [Set.Finite.toFinset_nonempty] using hJ)
        (fun j => d j x y) := by
  apply le_antisymm
  · dsimp [subfamily_pseudometric]
    apply iSup_le
    intro j
    exact Finset.le_sup' (f := fun k => d k x y) (J.toFinite.mem_toFinset.mpr j.2)
  · rw [Finset.sup'_le_iff]
    intro j hj
    exact le_iSup (fun k : {k // k ∈ J} => d k.1 x y) ⟨j, J.toFinite.mem_toFinset.mp hj⟩

/-! ### Point-Equality Relation, Zero-Distance Relation, Image Quotient, Fiber Preorder (CH03-D03) -/

/-- Point-equality pair relation `R_=(ϕ | U)`. -/
def pointEqRel {X : Type} {bot : X} (ϕ : Operator X bot) (U : Set X) : Set (X × X) :=
  { p | p.1 ∈ U ∧ p.2 ∈ U ∧ ϕ.func p.1 = ϕ.func p.2 }

/-- Full-gauge zero-distance pair relation `R_~(ϕ | U)`. -/
def zeroDistRel {X I : Type} {bot : X} (d : I → X → X → ENNReal)
    (ϕ : Operator X bot) (U : Set X) : Set (X × X) :=
  { p | p.1 ∈ U ∧ p.2 ∈ U ∧ GaugeZeroRelated d (ϕ.func p.1) (ϕ.func p.2) }

/-- Correspondence between `R_~(ϕ | U)` and full-family computational fibers `Fib_{ϕ, I}(ϕ(x) | U)`. -/
theorem mem_zeroDistRel_iff_mem_compFiber {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ : Operator X bot) (U : Set X) {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    (x, y) ∈ zeroDistRel d ϕ U ↔ y ∈ compFiber d ϕ Set.univ U (ϕ.func x) := by
  simp only [zeroDistRel, compFiber, Set.mem_setOf_eq, GaugeZeroRelated,
    subfamily_pseudometric_eq_zero_iff, Set.mem_univ, forall_true_left, hx, hy, true_and]
  constructor
  · intro h i
    rw [(hd i).symm]
    exact h i
  · intro h i
    rw [(hd i).symm]
    exact h i

/-- Setoid induced by the gauge zero-distance relation `~_G` restricted to `ϕ(U)`. -/
def imageZeroSetoid {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ : Operator X bot) (U : Set X) : Setoid { z : X // z ∈ operator_image ϕ U } where
  r a b := GaugeZeroRelated d a.1 b.1
  iseqv := by
    have heq := gauge_zero_related_equivalence d
      (fun i x => (hd i).dist_self x)
      (fun i x y => (hd i).symm x y)
      (fun i x y z => (hd i).triangle x y z)
    exact ⟨fun a => heq.refl a.1, fun h => heq.symm h, fun h1 h2 => heq.trans h1 h2⟩

/-- Image quotient `ϕ(U) / ~_G`. -/
def ImageQuot {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ : Operator X bot) (U : Set X) : Type :=
  Quotient (imageZeroSetoid d hd ϕ U)

/-- Canonical class `[ϕ(x)] ∈ ϕ(U) / ~_G` for `x ∈ U`. -/
def imageQuotMk {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ : Operator X bot) (U : Set X) (x : X) (hx : x ∈ U) : ImageQuot d hd ϕ U :=
  Quotient.mk (imageZeroSetoid d hd ϕ U) ⟨ϕ.func x, ⟨x, hx, rfl⟩⟩

theorem imageQuotMk_eq_iff {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ : Operator X bot) (U : Set X) {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    imageQuotMk d hd ϕ U x hx = imageQuotMk d hd ϕ U y hy ↔
      GaugeZeroRelated d (ϕ.func x) (ϕ.func y) := by
  exact Quotient.eq (r := imageZeroSetoid d hd ϕ U)

/-- Zero-distance fiber preorder `ϕ_A ⪰_{fiber, U} ϕ_B`, defined by `R_~(ϕ_A | U) ⊆ R_~(ϕ_B | U)`. -/
def FiberPreorder {X I : Type} {bot : X} (d : I → X → X → ENNReal)
    (U : Set X) (ϕA ϕB : Operator X bot) : Prop :=
  zeroDistRel d ϕA U ⊆ zeroDistRel d ϕB U

/-- Separating property of a gauge family restricted to a subset `S`. -/
def IsSeparatingOn {X I : Type} (d : I → X → X → ENNReal) (S : Set X) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, GaugeZeroRelated d x y → x = y

/-! ### Proposition 3.5: Basic Properties of Computational Fibers (CH03-P06-01..08) -/

/-- Proposition 3.5(i): Target zero-distance invariance. -/
theorem prop_3_5_i {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ : Operator X bot) (J : Set I) (U : Set X) (y y' : X)
    (_hU : U ⊆ dom ϕ) (_hJ : J.Nonempty)
    (hyy' : subfamily_pseudometric d J y y' = 0) :
    compFiber d ϕ J U y = compFiber d ϕ J U y' := by
  have hzero := (subfamily_pseudometric_eq_zero_iff d J y y').mp hyy'
  ext x
  simp only [compFiber, Set.mem_setOf_eq, subfamily_pseudometric_eq_zero_iff]
  constructor
  · rintro ⟨hx, hxy⟩
    refine ⟨hx, fun j hj => le_antisymm ?_ (zero_le _)⟩
    calc
      d j (ϕ.func x) y' ≤ d j (ϕ.func x) y + d j y y' := (hd j).triangle _ _ _
      _ = 0 := by rw [hxy j hj, hzero j hj, zero_add]
  · rintro ⟨hx, hxy'⟩
    refine ⟨hx, fun j hj => le_antisymm ?_ (zero_le _)⟩
    calc
      d j (ϕ.func x) y ≤ d j (ϕ.func x) y' + d j y' y := (hd j).triangle _ _ _
      _ = 0 := by rw [hxy' j hj, (hd j).symm y' y, hzero j hj, zero_add]

/-- Proposition 3.5(ii-a): Every image-target fiber is nonempty and these fibers cover `U`. -/
theorem prop_3_5_ii_a {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ : Operator X bot) (J : Set I) (U : Set X)
    (_hU : U ⊆ dom ϕ) (_hJ : J.Nonempty) :
    (∀ y ∈ operator_image ϕ U, (compFiber d ϕ J U y).Nonempty) ∧
    (⋃ y ∈ operator_image ϕ U, compFiber d ϕ J U y) = U ∧
    ⋃₀ compFiberFamily d ϕ J U = U := by
  have hnonempty : ∀ y ∈ operator_image ϕ U, (compFiber d ϕ J U y).Nonempty := by
    rintro y ⟨x, hx, rfl⟩
    refine ⟨x, hx, ?_⟩
    rw [subfamily_pseudometric_eq_zero_iff]
    intro j _
    exact (hd j).dist_self (ϕ.func x)
  have hunion : (⋃ y ∈ operator_image ϕ U, compFiber d ϕ J U y) = U := by
    ext x
    simp only [Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨y, _, hx, _⟩
      exact hx
    · intro hx
      refine ⟨ϕ.func x, ⟨x, hx, rfl⟩, hx, ?_⟩
      rw [subfamily_pseudometric_eq_zero_iff]
      intro j _
      exact (hd j).dist_self (ϕ.func x)
  have hsUnion : ⋃₀ compFiberFamily d ϕ J U = U := by
    rw [compFiberFamily, Set.sUnion_image]
    exact hunion
  exact ⟨hnonempty, hunion, hsUnion⟩

/-- Proposition 3.5(ii-b): Image-target fibers are either equal or disjoint; after deduplication
`compFiberFamily` forms a partition of `U`. -/
theorem prop_3_5_ii_b {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ : Operator X bot) (J : Set I) (U : Set X)
    (hU : U ⊆ dom ϕ) (hJ : J.Nonempty) :
    (∀ y₁ ∈ operator_image ϕ U, ∀ y₂ ∈ operator_image ϕ U,
      compFiber d ϕ J U y₁ = compFiber d ϕ J U y₂ ∨
      Disjoint (compFiber d ϕ J U y₁) (compFiber d ϕ J U y₂)) ∧
    (compFiberFamily d ϕ J U).PairwiseDisjoint id ∧
    (∀ F ∈ compFiberFamily d ϕ J U, F.Nonempty ∧ F ⊆ U) ∧
    ⋃₀ compFiberFamily d ϕ J U = U := by
  have hdisj : ∀ y₁ ∈ operator_image ϕ U, ∀ y₂ ∈ operator_image ϕ U,
      compFiber d ϕ J U y₁ = compFiber d ϕ J U y₂ ∨
      Disjoint (compFiber d ϕ J U y₁) (compFiber d ϕ J U y₂) := by
    intro y₁ _ y₂ _
    by_cases hinter : (compFiber d ϕ J U y₁ ∩ compFiber d ϕ J U y₂).Nonempty
    · left
      rcases hinter with ⟨x, hx1, hx2⟩
      apply prop_3_5_i d hd ϕ J U y₁ y₂ hU hJ
      rw [subfamily_pseudometric_eq_zero_iff]
      have h1 := (subfamily_pseudometric_eq_zero_iff d J (ϕ.func x) y₁).mp hx1.2
      have h2 := (subfamily_pseudometric_eq_zero_iff d J (ϕ.func x) y₂).mp hx2.2
      intro j hj
      apply le_antisymm _ (zero_le _)
      calc
        d j y₁ y₂ ≤ d j y₁ (ϕ.func x) + d j (ϕ.func x) y₂ := (hd j).triangle _ _ _
        _ = 0 := by rw [(hd j).symm y₁ (ϕ.func x), h1 j hj, h2 j hj, zero_add]
    · right
      rw [Set.disjoint_iff_inter_eq_empty]
      exact Set.not_nonempty_iff_eq_empty.mp hinter
  have hpair : (compFiberFamily d ϕ J U).PairwiseDisjoint id := by
    rintro F₁ ⟨y₁, hy₁, rfl⟩ F₂ ⟨y₂, hy₂, rfl⟩ hne
    rcases hdisj y₁ hy₁ y₂ hy₂ with heq | hdis
    · exact (hne heq).elim
    · exact hdis
  have hmem : ∀ F ∈ compFiberFamily d ϕ J U, F.Nonempty ∧ F ⊆ U := by
    rintro F ⟨y, hy, rfl⟩
    refine ⟨(prop_3_5_ii_a d hd ϕ J U hU hJ).1 y hy, fun x hx => hx.1⟩
  exact ⟨hdisj, hpair, hmem, (prop_3_5_ii_a d hd ϕ J U hU hJ).2.2⟩

/-- Proposition 3.5(iii): Component intersection law for any nonempty subfamily `J`. -/
theorem prop_3_5_iii {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (J : Set I) (U : Set X) (y : X)
    (_hU : U ⊆ dom ϕ) (hJ : J.Nonempty) :
    compFiber d ϕ J U y = ⋂ j ∈ J, compFiberSingle d ϕ j U y := by
  ext x
  simp only [compFiber, compFiberSingle, Set.mem_setOf_eq, Set.mem_iInter,
    subfamily_pseudometric_eq_zero_iff]
  constructor
  · rintro ⟨hx, h⟩ j hj
    exact ⟨hx, h j hj⟩
  · intro h
    rcases hJ with ⟨j₀, hj₀⟩
    exact ⟨(h j₀ hj₀).1, fun j hj => (h j hj).2⟩

/-- Proposition 3.5(iv): Subfamily antitone inclusion `J ⊆ K → Fib_K ⊆ Fib_J`. -/
theorem prop_3_5_iv {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (J K : Set I) (U : Set X) (y : X)
    (_hU : U ⊆ dom ϕ) (_hJ : J.Nonempty) (_hK : K.Nonempty) (hJK : J ⊆ K) :
    compFiber d ϕ K U y ⊆ compFiber d ϕ J U y := by
  intro x hx
  refine ⟨hx.1, ?_⟩
  rw [subfamily_pseudometric_eq_zero_iff]
  intro j hj
  exact (subfamily_pseudometric_eq_zero_iff d K (ϕ.func x) y).mp hx.2 j (hJK hj)

/-- Proposition 3.5(v): Subfamily boundaries (`J = {i}` and `J = I`). -/
theorem prop_3_5_v {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (y : X)
    (_hU : U ⊆ dom ϕ) :
    (∀ i : I, compFiber d ϕ ({i} : Set I) U y = compFiberSingle d ϕ i U y) ∧
    (∀ i : I, compFiber d ϕ Set.univ U y ⊆ compFiberSingle d ϕ i U y) := by
  constructor
  · intro i
    exact compFiber_singleton_eq_single d ϕ i U y
  · intro i x hx
    refine ⟨hx.1, ?_⟩
    exact (subfamily_pseudometric_eq_zero_iff d Set.univ (ϕ.func x) y).mp hx.2 i trivial

/-- Proposition 3.5(vi-a): Identity component fiber equals the input zero-distance class. -/
theorem prop_3_5_vi_a {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ : Operator X bot) (U : Set X) (j : I) (y : X)
    (_hU : U ⊆ dom ϕ) (hj : j ∈ I_id d ϕ U) :
    compFiberSingle d ϕ j U y = { x ∈ U | d j x y = 0 } := by
  ext x
  simp only [compFiberSingle, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hx, hxy⟩
    refine ⟨hx, le_antisymm ?_ (zero_le _)⟩
    calc
      d j x y ≤ d j x (ϕ.func x) + d j (ϕ.func x) y := (hd j).triangle _ _ _
      _ = 0 := by rw [(hd j).symm x (ϕ.func x), hj.2 x hx, hxy, zero_add]
  · rintro ⟨hx, hxy⟩
    refine ⟨hx, le_antisymm ?_ (zero_le _)⟩
    calc
      d j (ϕ.func x) y ≤ d j (ϕ.func x) x + d j x y := (hd j).triangle _ _ _
      _ = 0 := by rw [hj.2 x hx, hxy, zero_add]

/-- Proposition 3.5(vi-b): Constant component fiber equals `U` at any image target `y₀ ∈ ϕ(U)`,
and equals `∅` at any target `y` with `d_j(y, y₀) > 0`. -/
theorem prop_3_5_vi_b {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ : Operator X bot) (U : Set X) (j : I)
    (_hU : U ⊆ dom ϕ) (hj : j ∈ I_const d ϕ U) :
    ∀ y₀ ∈ operator_image ϕ U,
      compFiberSingle d ϕ j U y₀ = U ∧
      (∀ y : X, 0 < d j y y₀ → compFiberSingle d ϕ j U y = ∅) := by
  rintro y₀ ⟨x₀, hx₀, rfl⟩
  constructor
  · ext x
    simp only [compFiberSingle, Set.mem_setOf_eq, and_iff_left_iff_imp]
    intro hx
    exact hj x hx x₀ hx₀
  · intro y hypos
    ext x
    simp only [compFiberSingle, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨hx, hxy⟩
    have hzero : d j y (ϕ.func x₀) = 0 := by
      apply le_antisymm _ (zero_le _)
      calc
        d j y (ϕ.func x₀)
            ≤ d j y (ϕ.func x) + d j (ϕ.func x) (ϕ.func x₀) := (hd j).triangle _ _ _
        _ = 0 := by rw [(hd j).symm y (ϕ.func x), hxy, hj x hx x₀ hx₀, zero_add]
    exact (ne_of_gt hypos) hzero

/-! ### Proposition 3.6: Point-Value Image Factorization and Scalar Lip Bound (CH03-P07-01..04) -/

/-- Proposition 3.6(i-necessary): Existence of a point-value factor map `T : ϕ_A(U) → X`
implies `R_=(ϕ_A | U) ⊆ R_=(ϕ_B | U)`. -/
theorem prop_3_6_i_nec {X : Type} {bot : X}
    (ϕA ϕB : Operator X bot) (U : Set X)
    (_hUA : U ⊆ dom ϕA) (_hUB : U ⊆ dom ϕB)
    (hT : ∃ T : { z : X // z ∈ operator_image ϕA U } → X,
      ∀ x (hx : x ∈ U), T ⟨ϕA.func x, ⟨x, hx, rfl⟩⟩ = ϕB.func x) :
    pointEqRel ϕA U ⊆ pointEqRel ϕB U := by
  rcases hT with ⟨T, hT⟩
  rintro ⟨x, y⟩ ⟨hx, hy, hxy⟩
  refine ⟨hx, hy, ?_⟩
  have h1 := hT x hx
  have h2 := hT y hy
  have harg : (⟨ϕA.func x, ⟨x, hx, rfl⟩⟩ : { z : X // z ∈ operator_image ϕA U }) =
      ⟨ϕA.func y, ⟨y, hy, rfl⟩⟩ := Subtype.ext hxy
  rw [← h1, ← h2, harg]

/-- Proposition 3.6(i-sufficient): `R_=(ϕ_A | U) ⊆ R_=(ϕ_B | U)` constructs a well-defined map
`T : ϕ_A(U) → X` satisfying `T ∘ ϕ_A = ϕ_B` on `U` (including when `U = ∅`). -/
theorem prop_3_6_i_suff {X : Type} {bot : X}
    (ϕA ϕB : Operator X bot) (U : Set X)
    (_hUA : U ⊆ dom ϕA) (_hUB : U ⊆ dom ϕB)
    (hsub : pointEqRel ϕA U ⊆ pointEqRel ϕB U) :
    ∃ T : { z : X // z ∈ operator_image ϕA U } → X,
      ∀ x (hx : x ∈ U), T ⟨ϕA.func x, ⟨x, hx, rfl⟩⟩ = ϕB.func x := by
  classical
  refine ⟨fun z => ϕB.func (Classical.choose z.2), ?_⟩
  intro x hx
  let z : { z : X // z ∈ operator_image ϕA U } := ⟨ϕA.func x, ⟨x, hx, rfl⟩⟩
  have hspec := Classical.choose_spec z.2
  have hrel : (Classical.choose z.2, x) ∈ pointEqRel ϕA U := ⟨hspec.1, hx, hspec.2⟩
  exact (hsub hrel).2.2

/-- Proposition 3.6(i): Full equivalence for unidirectional point-value factorization. -/
theorem prop_3_6_i {X : Type} {bot : X}
    (ϕA ϕB : Operator X bot) (U : Set X)
    (hUA : U ⊆ dom ϕA) (hUB : U ⊆ dom ϕB) :
    (∃ T : { z : X // z ∈ operator_image ϕA U } → X,
      ∀ x (hx : x ∈ U), T ⟨ϕA.func x, ⟨x, hx, rfl⟩⟩ = ϕB.func x) ↔
      pointEqRel ϕA U ⊆ pointEqRel ϕB U :=
  ⟨prop_3_6_i_nec ϕA ϕB U hUA hUB, prop_3_6_i_suff ϕA ϕB U hUA hUB⟩

/-- Proposition 3.6(ii): Bidirectional point-value factorization exists iff
`R_=(ϕ_A | U) = R_=(ϕ_B | U)`. -/
theorem prop_3_6_ii {X : Type} {bot : X}
    (ϕA ϕB : Operator X bot) (U : Set X)
    (hUA : U ⊆ dom ϕA) (hUB : U ⊆ dom ϕB) :
    ((∃ T_AB : { z : X // z ∈ operator_image ϕA U } → X,
        ∀ x (hx : x ∈ U), T_AB ⟨ϕA.func x, ⟨x, hx, rfl⟩⟩ = ϕB.func x) ∧
     (∃ T_BA : { z : X // z ∈ operator_image ϕB U } → X,
        ∀ x (hx : x ∈ U), T_BA ⟨ϕB.func x, ⟨x, hx, rfl⟩⟩ = ϕA.func x)) ↔
      pointEqRel ϕA U = pointEqRel ϕB U := by
  rw [prop_3_6_i ϕA ϕB U hUA hUB, prop_3_6_i ϕB ϕA U hUB hUA, Set.Subset.antisymm_iff]

/-- Proposition 3.6(iii): In the single-component setting, if `T : ϕ_A(U) → X` satisfies
`T ∘ ϕ_A = ϕ_B` on `U`, `ϕ_A` is `K_A`-co-Lip (`0 < K_A < ∞`), and `ϕ_B` is `L_B`-Lip (`L_B < ∞`),
then `T` is `(L_B / K_A)`-Lip on `ϕ_A(U)`. -/
theorem prop_3_6_iii {X : Type} {bot : X}
    (d : X → X → ENNReal) (ϕA ϕB : Operator X bot) (U : Set X)
    (_hUA : U ⊆ dom ϕA) (_hUB : U ⊆ dom ϕB)
    (T : { z : X // z ∈ operator_image ϕA U } → X)
    (hT : ∀ x (hx : x ∈ U), T ⟨ϕA.func x, ⟨x, hx, rfl⟩⟩ = ϕB.func x)
    (K_A L_B : ENNReal) (hK_pos : 0 < K_A) (hK_fin : K_A < ⊤) (_hL_fin : L_B < ⊤)
    (hcoLip : ∀ x ∈ U, ∀ x' ∈ U, K_A * d x x' ≤ d (ϕA.func x) (ϕA.func x'))
    (hLip : ∀ x ∈ U, ∀ x' ∈ U, d (ϕB.func x) (ϕB.func x') ≤ L_B * d x x') :
    ∀ y y' : { z : X // z ∈ operator_image ϕA U },
      d (T y) (T y') ≤ (L_B / K_A) * d y.1 y'.1 := by
  intro y y'
  rcases y with ⟨yval, x, hx, rfl⟩
  rcases y' with ⟨y'val, x', hx', rfl⟩
  rw [hT x hx, hT x' hx']
  have hK_ne0 : K_A ≠ 0 := ne_of_gt hK_pos
  have hK_netop : K_A ≠ ⊤ := ne_of_lt hK_fin
  have hdx : d x x' ≤ K_A⁻¹ * d (ϕA.func x) (ϕA.func x') := by
    calc
      d x x' = K_A⁻¹ * (K_A * d x x') := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hK_ne0 hK_netop, one_mul]
      _ ≤ K_A⁻¹ * d (ϕA.func x) (ϕA.func x') :=
        mul_le_mul_right (hcoLip x hx x' hx') K_A⁻¹
  calc
    d (ϕB.func x) (ϕB.func x') ≤ L_B * d x x' := hLip x hx x' hx'
    _ ≤ L_B * (K_A⁻¹ * d (ϕA.func x) (ϕA.func x')) := mul_le_mul_right hdx L_B
    _ = (L_B / K_A) * d (ϕA.func x) (ϕA.func x') := by rw [div_eq_mul_inv, mul_assoc]

/-- Proposition 3.6(iii) matrix specialization for single-component gauge spaces (`[Subsingleton I]`). -/
theorem prop_3_6_iii_subsingleton {X I : Type} {bot : X} [Fintype I] [Subsingleton I]
    (d : I → X → X → ENNReal) (i : I) (ϕA ϕB : Operator X bot) (U : Set X)
    (T : { z : X // z ∈ operator_image ϕA U } → X)
    (hT : ∀ x (hx : x ∈ U), T ⟨ϕA.func x, ⟨x, hx, rfl⟩⟩ = ϕB.func x)
    (K L : I → I → ENNReal)
    (hK : IsCoLipMatrix d ϕA U K) (hL : IsLipMatrix d ϕB U L)
    (hK_pos : 0 < K i i) (hK_fin : K i i < ⊤) (hL_fin : L i i < ⊤) :
    ∀ y y' : { z : X // z ∈ operator_image ϕA U },
      d i (T y) (T y') ≤ (L i i / K i i) * d i y.1 y'.1 := by
  apply prop_3_6_iii (d i) ϕA ϕB U hK.2.1 hL.1 T hT (K i i) (L i i) hK_pos hK_fin hL_fin
  · intro x hx x' hx'
    have h := hK.2.2 x hx x' hx' i
    have hsum : (∑ k : I, K k i * d k x x') = K i i * d i x x' := by
      apply Finset.sum_eq_single i
      · intro k _ hk; exact (hk (Subsingleton.elim k i)).elim
      · intro hi; exact (hi (Finset.mem_univ i)).elim
    simpa [hsum] using h
  · exact single_component_lip_matrix_ineq d ϕB U L i hL

/-! ### Proposition 3.7: Image Factorization on the Zero-Distance Quotient (CH03-P08-01..03) -/

/-- Proposition 3.7 (unidirectional): A quotient map `Tbar : ϕ_A(U)/~_G → ϕ_B(U)/~_G` satisfying
`Tbar([ϕ_A(x)]) = [ϕ_B(x)]` exists iff `R_~(ϕ_A | U) ⊆ R_~(ϕ_B | U)`. -/
theorem prop_3_7_one_way {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕA ϕB : Operator X bot) (U : Set X)
    (_hUA : U ⊆ dom ϕA) (_hUB : U ⊆ dom ϕB) :
    (∃ Tbar : ImageQuot d hd ϕA U → ImageQuot d hd ϕB U,
      ∀ x (hx : x ∈ U), Tbar (imageQuotMk d hd ϕA U x hx) = imageQuotMk d hd ϕB U x hx) ↔
      zeroDistRel d ϕA U ⊆ zeroDistRel d ϕB U := by
  classical
  constructor
  · rintro ⟨Tbar, hTbar⟩ ⟨x, y⟩ ⟨hx, hy, hxy⟩
    refine ⟨hx, hy, ?_⟩
    have hqA : imageQuotMk d hd ϕA U x hx = imageQuotMk d hd ϕA U y hy :=
      (imageQuotMk_eq_iff d hd ϕA U hx hy).mpr hxy
    have hqB : imageQuotMk d hd ϕB U x hx = imageQuotMk d hd ϕB U y hy := by
      rw [← hTbar x hx, ← hTbar y hy, hqA]
    exact (imageQuotMk_eq_iff d hd ϕB U hx hy).mp hqB
  · intro hsub
    let f : { z : X // z ∈ operator_image ϕA U } → ImageQuot d hd ϕB U :=
      fun z => imageQuotMk d hd ϕB U (Classical.choose z.2) (Classical.choose_spec z.2).1
    have hresp : ∀ a b : { z : X // z ∈ operator_image ϕA U },
        (imageZeroSetoid d hd ϕA U).r a b → f a = f b := by
      intro a b hab
      have ha := Classical.choose_spec a.2
      have hb := Classical.choose_spec b.2
      have hrelA : (Classical.choose a.2, Classical.choose b.2) ∈ zeroDistRel d ϕA U := by
        refine ⟨ha.1, hb.1, ?_⟩
        simpa [ha.2, hb.2] using hab
      have hrelB := hsub hrelA
      exact (imageQuotMk_eq_iff d hd ϕB U ha.1 hb.1).mpr hrelB.2.2
    refine ⟨Quotient.lift f hresp, ?_⟩
    intro x hx
    change f ⟨ϕA.func x, ⟨x, hx, rfl⟩⟩ = imageQuotMk d hd ϕB U x hx
    dsimp [f]
    have hspec := Classical.choose_spec (⟨x, hx, rfl⟩ : ϕA.func x ∈ operator_image ϕA U)
    have hrelA : (Classical.choose (⟨x, hx, rfl⟩ : ϕA.func x ∈ operator_image ϕA U), x) ∈
        zeroDistRel d ϕA U := by
      refine ⟨hspec.1, hx, ?_⟩
      intro i
      rw [hspec.2]
      exact (hd i).dist_self (ϕA.func x)
    exact (imageQuotMk_eq_iff d hd ϕB U hspec.1 hx).mpr (hsub hrelA).2.2

/-- Proposition 3.7 (bidirectional): Quotient maps in both directions exist iff
`R_~(ϕ_A | U) = R_~(ϕ_B | U)`. -/
theorem prop_3_7_two_way {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕA ϕB : Operator X bot) (U : Set X)
    (hUA : U ⊆ dom ϕA) (hUB : U ⊆ dom ϕB) :
    ((∃ Tbar_AB : ImageQuot d hd ϕA U → ImageQuot d hd ϕB U,
        ∀ x (hx : x ∈ U), Tbar_AB (imageQuotMk d hd ϕA U x hx) = imageQuotMk d hd ϕB U x hx) ∧
     (∃ Tbar_BA : ImageQuot d hd ϕB U → ImageQuot d hd ϕA U,
        ∀ x (hx : x ∈ U), Tbar_BA (imageQuotMk d hd ϕB U x hx) = imageQuotMk d hd ϕA U x hx)) ↔
      zeroDistRel d ϕA U = zeroDistRel d ϕB U := by
  rw [prop_3_7_one_way d hd ϕA ϕB U hUA hUB, prop_3_7_one_way d hd ϕB ϕA U hUB hUA,
    Set.Subset.antisymm_iff]

/-- Helper: when the gauge family separates an operator's actual image `ϕ(U)`,
`R_=(ϕ | U) = R_~(ϕ | U)`. -/
theorem pointEqRel_eq_zeroDistRel_of_separatingOn {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ : Operator X bot) (U : Set X)
    (hsep : IsSeparatingOn d (operator_image ϕ U)) :
    pointEqRel ϕ U = zeroDistRel d ϕ U := by
  ext ⟨x, y⟩
  simp only [pointEqRel, zeroDistRel, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hx, hy, hxy⟩
    exact ⟨hx, hy, fun i => by rw [hxy]; exact (hd i).dist_self _⟩
  · rintro ⟨hx, hy, hxy⟩
    exact ⟨hx, hy, hsep (ϕ.func x) ⟨x, hx, rfl⟩ (ϕ.func y) ⟨y, hy, rfl⟩ hxy⟩

/-- Proposition 3.7 (image-separating specialization): If the gauge family separates each of the
two actual images `ϕ_A(U)` and `ϕ_B(U)`, then `R_= = R_~` on each side, and both the unidirectional
and bidirectional point-value criteria coincide with the quotient criteria. -/
theorem prop_3_7_image_separating {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕA ϕB : Operator X bot) (U : Set X)
    (hUA : U ⊆ dom ϕA) (hUB : U ⊆ dom ϕB)
    (hsepA : IsSeparatingOn d (operator_image ϕA U))
    (hsepB : IsSeparatingOn d (operator_image ϕB U)) :
    pointEqRel ϕA U = zeroDistRel d ϕA U ∧
    pointEqRel ϕB U = zeroDistRel d ϕB U ∧
    ((∃ T : { z : X // z ∈ operator_image ϕA U } → X,
        ∀ x (hx : x ∈ U), T ⟨ϕA.func x, ⟨x, hx, rfl⟩⟩ = ϕB.func x) ↔
     (∃ Tbar : ImageQuot d hd ϕA U → ImageQuot d hd ϕB U,
        ∀ x (hx : x ∈ U), Tbar (imageQuotMk d hd ϕA U x hx) = imageQuotMk d hd ϕB U x hx)) ∧
    (((∃ T_AB : { z : X // z ∈ operator_image ϕA U } → X,
        ∀ x (hx : x ∈ U), T_AB ⟨ϕA.func x, ⟨x, hx, rfl⟩⟩ = ϕB.func x) ∧
      (∃ T_BA : { z : X // z ∈ operator_image ϕB U } → X,
        ∀ x (hx : x ∈ U), T_BA ⟨ϕB.func x, ⟨x, hx, rfl⟩⟩ = ϕA.func x)) ↔
     ((∃ Tbar_AB : ImageQuot d hd ϕA U → ImageQuot d hd ϕB U,
        ∀ x (hx : x ∈ U), Tbar_AB (imageQuotMk d hd ϕA U x hx) = imageQuotMk d hd ϕB U x hx) ∧
      (∃ Tbar_BA : ImageQuot d hd ϕB U → ImageQuot d hd ϕA U,
        ∀ x (hx : x ∈ U), Tbar_BA (imageQuotMk d hd ϕB U x hx) = imageQuotMk d hd ϕA U x hx))) := by
  have hA := pointEqRel_eq_zeroDistRel_of_separatingOn d hd ϕA U hsepA
  have hB := pointEqRel_eq_zeroDistRel_of_separatingOn d hd ϕB U hsepB
  refine ⟨hA, hB, ?_, ?_⟩
  · rw [prop_3_6_i ϕA ϕB U hUA hUB, prop_3_7_one_way d hd ϕA ϕB U hUA hUB, hA, hB]
  · rw [prop_3_6_ii ϕA ϕB U hUA hUB, prop_3_7_two_way d hd ϕA ϕB U hUA hUB, hA, hB]

/-! ### Remark: Transitivity of Fiber Inclusion (CH03-P09-01..03) -/

/-- Remark (CH03-P09-01): `FiberPreorder d U` is reflexive and transitive. -/
theorem remark_fiber_preorder_refl_trans {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (U : Set X) :
    (∀ ϕ : Operator X bot, FiberPreorder d U ϕ ϕ) ∧
    (∀ ϕ₁ ϕ₂ ϕ₃ : Operator X bot,
      FiberPreorder d U ϕ₁ ϕ₂ → FiberPreorder d U ϕ₂ ϕ₃ → FiberPreorder d U ϕ₁ ϕ₃) := by
  exact ⟨fun _ => Set.Subset.rfl, fun _ _ _ h12 h23 => h12.trans h23⟩

/-- Remark (CH03-P09-02): Along any finite chain `ϕ₀, …, ϕₘ` with stepwise `ϕ_{r-1} ⪰ ϕ_r`,
we have `ϕ_a ⪰ ϕ_b` for every `0 ≤ a ≤ b ≤ m` (in particular `a < b`). -/
theorem remark_fiber_chain_trans {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (U : Set X) {m : ℕ}
    (ϕ : Fin (m + 1) → Operator X bot)
    (_hdom : ∀ k : Fin (m + 1), U ⊆ dom (ϕ k))
    (hstep : ∀ r : Fin m, FiberPreorder d U (ϕ r.castSucc) (ϕ r.succ)) :
    ∀ a b : Fin (m + 1), a ≤ b → FiberPreorder d U (ϕ a) (ϕ b) := by
  have hnat : ∀ (a b : ℕ) (ha : a < m + 1) (hb : b < m + 1), a ≤ b →
      FiberPreorder d U (ϕ ⟨a, ha⟩) (ϕ ⟨b, hb⟩) := by
    intro a b ha hb hab
    induction b with
    | zero =>
        have ha0 : a = 0 := Nat.eq_zero_of_le_zero hab
        subst ha0
        exact Set.Subset.rfl
    | succ b ih =>
        by_cases hEq : a = b + 1
        · subst hEq
          exact Set.Subset.rfl
        · have hle : a ≤ b := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne hab hEq)
          have hb' : b < m := Nat.lt_of_succ_lt_succ hb
          have hprev := ih (Nat.lt_trans hb' (Nat.lt_succ_self m)) hle
          have hlast : FiberPreorder d U (ϕ ⟨b, Nat.lt_trans hb' (Nat.lt_succ_self m)⟩)
              (ϕ ⟨b + 1, hb⟩) := hstep ⟨b, hb'⟩
          exact hprev.trans hlast
  intro a b hab
  exact hnat a.1 b.1 a.2 b.2 hab

/-- Remark (CH03-P09-03): If some step in the chain is a strict inclusion, then the endpoints
satisfy strict inclusion `R_~(ϕ₀ | U) ⊂ R_~(ϕₘ | U)` with an explicit difference witness. -/
theorem remark_fiber_chain_strict {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (U : Set X) {m : ℕ}
    (ϕ : Fin (m + 1) → Operator X bot)
    (hdom : ∀ k : Fin (m + 1), U ⊆ dom (ϕ k))
    (hstep : ∀ r : Fin m, FiberPreorder d U (ϕ r.castSucc) (ϕ r.succ))
    (hstrict : ∃ r : Fin m, zeroDistRel d (ϕ r.castSucc) U ⊂ zeroDistRel d (ϕ r.succ) U) :
    zeroDistRel d (ϕ 0) U ⊂ zeroDistRel d (ϕ (Fin.last m)) U ∧
    ∃ p : X × X, p ∈ zeroDistRel d (ϕ (Fin.last m)) U \ zeroDistRel d (ϕ 0) U := by
  have htrans := remark_fiber_chain_trans d U ϕ hdom hstep
  have h0m : zeroDistRel d (ϕ 0) U ⊆ zeroDistRel d (ϕ (Fin.last m)) U :=
    htrans 0 (Fin.last m) (Fin.zero_le _)
  rcases hstrict with ⟨r, hr_sub, hr_not_sub⟩
  have hex : ∃ p, p ∈ zeroDistRel d (ϕ r.succ) U ∧ p ∉ zeroDistRel d (ϕ r.castSucc) U := by
    by_contra hall
    push Not at hall
    exact hr_not_sub hall
  rcases hex with ⟨p, hp_succ, hp_not_prev⟩
  have h0_prev : zeroDistRel d (ϕ 0) U ⊆ zeroDistRel d (ϕ r.castSucc) U :=
    htrans 0 r.castSucc (Fin.zero_le _)
  have hsucc_m : zeroDistRel d (ϕ r.succ) U ⊆ zeroDistRel d (ϕ (Fin.last m)) U :=
    htrans r.succ (Fin.last m) (Fin.le_last _)
  have hp_in_m : p ∈ zeroDistRel d (ϕ (Fin.last m)) U := hsucc_m hp_succ
  have hp_not_0 : p ∉ zeroDistRel d (ϕ 0) U := fun hp0 => hp_not_prev (h0_prev hp0)
  refine ⟨⟨h0m, fun hm0 => hp_not_0 (hm0 hp_in_m)⟩, ⟨p, hp_in_m, hp_not_0⟩⟩

end Ch03
