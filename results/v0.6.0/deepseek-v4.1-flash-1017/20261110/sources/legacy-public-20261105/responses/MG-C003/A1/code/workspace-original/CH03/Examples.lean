import CH03.Core6

namespace formal_oet.vol_01.ch_03_operator_local_degeneracy
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set

set_option maxHeartbeats 4000000

/-! ## Counterexample 3.1 for Proposition 3.2 (two-point swap) -/

def dSwap (x y : Fin 3) : ENNReal :=
  if x = 0 then (if y = 0 then 0 else ⊤)
  else if y = 0 then ⊤
  else if x = y then 0 else 1

theorem dSwap_extended : ExtendedPseudoMetric (Fin 3) 0 dSwap where
  nonabsorbing := ⟨1, by decide⟩
  dist_self := by intro x; fin_cases x <;> simp [dSwap]
  symm := by intro x y; fin_cases x <;> fin_cases y <;> simp [dSwap]
  triangle := by
    intro x y z
    fin_cases x <;> fin_cases y <;> fin_cases z <;> simp [dSwap]
  isolate_bot := by
    intro x hx
    fin_cases x <;> simp [dSwap] at hx ⊢

def dSwapFamily : Unit → Fin 3 → Fin 3 → ENNReal := fun _ => dSwap

def dSwapFamily_extended : ∀ i : Unit, ExtendedPseudoMetric (Fin 3) 0 (dSwapFamily i) :=
  fun _ => dSwap_extended

def swapAB : Operator (Fin 3) 0 where
  func x := if x = 1 then 2 else if x = 2 then 1 else 0
  preserves_bot := by simp

def swapU : Set (Fin 3) := {1, 2}

theorem swap_const_empty : Iconst dSwapFamily swapAB swapU = ∅ := by
  ext i
  fin_cases i
  simp only [Set.mem_empty_iff_false, iff_false]
  intro h
  have h12 := h 1 (by simp [swapU]) 2 (by simp [swapU])
  simp [dSwapFamily, dSwap, swapAB] at h12

theorem swap_id_empty : Iid dSwapFamily swapAB swapU = ∅ := by
  ext i
  fin_cases i
  simp only [Set.mem_empty_iff_false, iff_false]
  intro h
  have hz := h.2 1 (by simp [swapU])
  change dSwap (swapAB.func 1) 1 = 0 at hz
  simp [swapAB, dSwap] at hz

theorem swap_active_univ : Iact dSwapFamily swapAB swapU = Set.univ := by
  ext i
  fin_cases i
  simp [Iact, swap_const_empty, swap_id_empty]

theorem swap_comp_eq_id : swapAB * swapAB = (1 : Operator (Fin 3) 0) := by
  apply Operator.ext
  funext x
  change swapAB.func (swapAB.func x) = x
  fin_cases x <;> simp [swapAB]

theorem swap_comp_id_univ : Iid dSwapFamily (swapAB * swapAB) swapU = Set.univ := by
  rw [swap_comp_eq_id]
  ext i
  fin_cases i
  constructor
  · intro _
    simp
  · intro _
    refine ⟨?_, ?_⟩
    · intro h
      have h12 := h 1 (by simp [swapU]) 2 (by simp [swapU])
      change dSwap 1 2 = 0 at h12
      simp [dSwap] at h12
    · intro x hx
      change dSwap x x = 0
      fin_cases x <;> simp [dSwap]

theorem swap_comp_active_empty :
    Iact dSwapFamily (swapAB * swapAB) swapU = ∅ := by
  ext i
  fin_cases i
  simp only [Set.mem_empty_iff_false, iff_false]
  intro h
  exact h.2 (by
    rw [swap_comp_id_univ]
    simp)

theorem swap_reverse_inclusions_fail :
    (¬ Iact dSwapFamily swapAB swapU ⊆
        Iact dSwapFamily (swapAB * swapAB) swapU) ∧
      (¬ Iid dSwapFamily (swapAB * swapAB) swapU ⊆
        Iid dSwapFamily swapAB swapU) := by
  constructor
  · intro h
    have : () ∈ Iact dSwapFamily (swapAB * swapAB) swapU := h (by rw [swap_active_univ]; simp)
    rw [swap_comp_active_empty] at this
    simp at this
  · intro h
    have : () ∈ Iid dSwapFamily swapAB swapU := h (by rw [swap_comp_id_univ]; simp)
    rw [swap_id_empty] at this
    simp at this

/-! ## Seven-point two-component counterexample (Proposition 3.3(ii)) -/

def dSeven (k : Fin 2) (x y : Fin 7) : ENNReal :=
  if x = 0 then (if y = 0 then 0 else ⊤)
  else if y = 0 then ⊤
  else if x = y then 0
  else if k = 0 ∧ ((x = 3 ∧ y = 4) ∨ (x = 4 ∧ y = 3)) then 0
  else 1

theorem dSeven_extended (k : Fin 2) : ExtendedPseudoMetric (Fin 7) 0 (dSeven k) where
  nonabsorbing := ⟨1, by decide⟩
  dist_self := by intro x; fin_cases x <;> simp [dSeven]
  symm := by
    intro x y
    fin_cases x <;> fin_cases y <;> fin_cases k <;> simp [dSeven]
  triangle := by
    intro x y z
    fin_cases x <;> fin_cases y <;> fin_cases z <;> fin_cases k <;> simp [dSeven]
  isolate_bot := by
    intro x hx
    fin_cases x <;> simp [dSeven] at hx ⊢

def sevenFamily : Fin 2 → Fin 7 → Fin 7 → ENNReal := dSeven

def phiPQ : Operator (Fin 7) 0 where
  func x := if x = 1 then 3 else if x = 2 then 4 else 0
  preserves_bot := by simp

def psiRS : Operator (Fin 7) 0 where
  func x := if x = 3 then 5 else if x = 4 then 6 else 0
  preserves_bot := by simp

def sevenU : Set (Fin 7) := {1, 2}

theorem seven_inner_const : (0 : Fin 2) ∈ Iconst sevenFamily phiPQ sevenU := by
  intro x hx y hy
  simp [sevenU] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
    simp [sevenFamily, dSeven, phiPQ]

theorem seven_composite_not_const :
    (0 : Fin 2) ∉ Iconst sevenFamily (psiRS * phiPQ) sevenU := by
  intro h
  have h12 := h 1 (by simp [sevenU]) 2 (by simp [sevenU])
  change dSeven 0 (psiRS.func (phiPQ.func 1)) (psiRS.func (phiPQ.func 2)) = 0 at h12
  simp [phiPQ, psiRS, dSeven] at h12

theorem seven_point_counterexample :
    (∀ k : Fin 2, ExtendedPseudoMetric (Fin 7) 0 (sevenFamily k)) ∧
      (0 : Fin 2) ∈ Iconst sevenFamily phiPQ sevenU ∧
      (0 : Fin 2) ∉ Iconst sevenFamily (psiRS * phiPQ) sevenU :=
  ⟨dSeven_extended, seven_inner_const, seven_composite_not_const⟩

/-! ## Counterexample for Proposition 3.8(ii) -/

def dTopOnly (x y : Fin 3) : ENNReal :=
  if x = 0 then (if y = 0 then 0 else ⊤)
  else if y = 0 then ⊤
  else if x = y then 0 else ⊤

theorem dTopOnly_extended : ExtendedPseudoMetric (Fin 3) 0 dTopOnly where
  nonabsorbing := ⟨1, by decide⟩
  dist_self := by intro x; fin_cases x <;> simp [dTopOnly]
  symm := by intro x y; fin_cases x <;> fin_cases y <;> simp [dTopOnly]
  triangle := by
    intro x y z
    fin_cases x <;> fin_cases y <;> fin_cases z <;> simp [dTopOnly]
  isolate_bot := by
    intro x hx
    fin_cases x <;> simp [dTopOnly] at hx ⊢

def dOne (x y : Fin 3) : ENNReal :=
  if x = 0 then (if y = 0 then 0 else ⊤)
  else if y = 0 then ⊤
  else if x = y then 0 else 1

theorem dOne_extended : ExtendedPseudoMetric (Fin 3) 0 dOne where
  nonabsorbing := ⟨1, by decide⟩
  dist_self := by intro x; fin_cases x <;> simp [dOne]
  symm := by intro x y; fin_cases x <;> fin_cases y <;> simp [dOne]
  triangle := by
    intro x y z
    fin_cases x <;> fin_cases y <;> fin_cases z <;> simp [dOne]
  isolate_bot := by
    intro x hx
    fin_cases x <;> simp [dOne] at hx ⊢

def dTwo (k : Fin 2) (x y : Fin 3) : ENNReal :=
  if k = 0 then dTopOnly x y else dOne x y

theorem dTwo_extended (k : Fin 2) : ExtendedPseudoMetric (Fin 3) 0 (dTwo k) := by
  fin_cases k
  · simpa [dTwo] using dTopOnly_extended
  · simpa [dTwo] using dOne_extended

def idThree : Operator (Fin 3) 0 where
  func x := x
  preserves_bot := rfl

def threeU : Set (Fin 3) := {1, 2}

theorem pointwise_top_radius (y : Fin 3) (hy : y ∈ threeU) :
    pointwiseZeroRadius (fun _ : Unit => dTopOnly) idThree () () y threeU = ⊤ := by
  rw [pointwiseZeroRadius, pointwiseRadius_eq_top_iff]
  intro r hr0 hrtop
  refine ⟨hr0, hrtop, ?_⟩
  intro x hx hlt
  change dTopOnly (idThree.func x) (idThree.func y) = 0
  simp only [idThree]
  have hx12 : x = 1 ∨ x = 2 := by simpa [threeU] using hx
  have hy12 : y = 1 ∨ y = 2 := by simpa [threeU] using hy
  rcases hx12 with rfl | rfl <;> rcases hy12 with rfl | rfl
  · rfl
  · exfalso
    have : dTopOnly (1 : Fin 3) 2 = ⊤ := by simp [dTopOnly]
    rw [this] at hlt
    exact not_top_lt hlt
  · exfalso
    have : dTopOnly (2 : Fin 3) 1 = ⊤ := by simp [dTopOnly]
    rw [this] at hlt
    exact not_top_lt hlt
  · rfl

theorem unified_top_radius :
    zeroingMatrix (fun _ : Unit => dTopOnly) idThree threeU () () = ⊤ := by
  unfold zeroingMatrix unifiedRadius
  apply le_antisymm le_top
  apply le_iInf
  intro y
  change ⊤ ≤ pointwiseZeroRadius (fun _ : Unit => dTopOnly) idThree () () y.1 threeU
  exact top_le_iff.mpr (pointwise_top_radius y.1 y.2)

theorem identity_not_const_top : (() : Unit) ∉ Iconst (fun _ : Unit => dTopOnly) idThree threeU := by
  intro h
  have h12 := h 1 (by simp [threeU]) 2 (by simp [threeU])
  change dTopOnly 1 2 = 0 at h12
  simp [dTopOnly] at h12

theorem zeroing_infinite_not_const_same_channel :
    zeroingMatrix (fun _ : Unit => dTopOnly) idThree threeU () () = ⊤ ∧
      (() : Unit) ∉ Iconst (fun _ : Unit => dTopOnly) idThree threeU :=
  ⟨unified_top_radius, identity_not_const_top⟩

theorem pointwise_top_radius_two (y : Fin 3) (hy : y ∈ threeU) :
    pointwiseZeroRadius dTwo idThree 0 1 y threeU = ⊤ := by
  rw [pointwiseZeroRadius, pointwiseRadius_eq_top_iff]
  intro r hr0 hrtop
  refine ⟨hr0, hrtop, ?_⟩
  intro x hx hlt
  change dTwo 1 (idThree.func x) (idThree.func y) = 0
  simp only [idThree]
  change dOne x y = 0
  have hx12 : x = 1 ∨ x = 2 := by simpa [threeU] using hx
  have hy12 : y = 1 ∨ y = 2 := by simpa [threeU] using hy
  rcases hx12 with rfl | rfl <;> rcases hy12 with rfl | rfl
  · rfl
  · exfalso
    have : dTwo 0 (1 : Fin 3) 2 = ⊤ := by simp [dTwo, dTopOnly]
    rw [this] at hlt
    exact not_top_lt hlt
  · exfalso
    have : dTwo 0 (2 : Fin 3) 1 = ⊤ := by simp [dTwo, dTopOnly]
    rw [this] at hlt
    exact not_top_lt hlt
  · rfl

theorem unified_top_radius_two :
    zeroingMatrix (dTwo) idThree threeU 1 0 = ⊤ := by
  unfold zeroingMatrix unifiedRadius
  apply le_antisymm le_top
  apply le_iInf
  intro y
  change ⊤ ≤ pointwiseZeroRadius dTwo idThree 0 1 y.1 threeU
  exact top_le_iff.mpr (pointwise_top_radius_two y.1 y.2)

theorem identity_not_const_two : (1 : Fin 2) ∉ Iconst dTwo idThree threeU := by
  intro h
  have h12 := h 1 (by simp [threeU]) 2 (by simp [threeU])
  change dOne 1 2 = 0 at h12
  simp [dOne] at h12

theorem zeroing_infinite_not_const_distinct_channel :
    zeroingMatrix dTwo idThree threeU 1 0 = ⊤ ∧
      (1 : Fin 2) ∉ Iconst dTwo idThree threeU :=
  ⟨unified_top_radius_two, identity_not_const_two⟩

/-! ## Diameter-scale reverse failure (Proposition 3.14(iii)) -/

def dFin2 (x y : Fin 2) : ENNReal := if x = y then 0 else 1

noncomputable def fin2DiameterScale : InputScaleFamily (Fin 2) Unit where
  scale := fun _ => diameterScale (fun _ : Unit => dFin2) ()
  mono := by
    intro _ A B hAB
    exact diameterScale_mono (fun _ : Unit => dFin2) () hAB

theorem fin2_diameter_univ :
    fin2DiameterScale.scale () (Set.univ : Set (Fin 2)) = 1 := by
  unfold fin2DiameterScale
  simp only
  unfold diameterScale
  apply le_antisymm
  · apply iSup_le
    intro x
    apply iSup_le
    intro y
    rcases x with ⟨x, hx⟩
    rcases y with ⟨y, hy⟩
    fin_cases x <;> fin_cases y <;> simp [dFin2]
  · exact le_iSup_of_le (⟨0, by simp⟩ : {x : Fin 2 // x ∈ (Set.univ : Set (Fin 2))})
      (le_iSup_of_le (⟨1, by simp⟩ : {y : Fin 2 // y ∈ (Set.univ : Set (Fin 2))})
        (by simp [dFin2]))

theorem fin2_diameter_singleton :
    fin2DiameterScale.scale () ({0} : Set (Fin 2)) = 0 := by
  unfold fin2DiameterScale
  simp only
  unfold diameterScale
  apply le_antisymm
  · apply iSup_le
    intro x
    apply iSup_le
    intro y
    rcases x with ⟨x, hx⟩
    rcases y with ⟨y, hy⟩
    simp only [Set.mem_singleton_iff] at hx hy
    subst x
    subst y
    simp [dFin2]
  · exact zero_le _

theorem diameter_scale_reverse_failure :
    ∃ (d : Unit → Fin 2 → Fin 2 → ENNReal) (σ : InputScaleFamily (Fin 2) Unit)
      (A B : Set (Fin 2)) (τ : ENNReal),
      B ⊆ A ∧ σ.scale () B < τ ∧ ¬ σ.scale () A < τ := by
  refine ⟨fun _ => dFin2, fin2DiameterScale, Set.univ, ({0} : Set (Fin 2)),
    (1/2 : ENNReal), ?_, ?_, ?_⟩
  · intro x _; simp
  · rw [fin2_diameter_singleton]
    norm_num
  · rw [fin2_diameter_univ]
    norm_num

end formal_oet.vol_01.ch_03_operator_local_degeneracy
