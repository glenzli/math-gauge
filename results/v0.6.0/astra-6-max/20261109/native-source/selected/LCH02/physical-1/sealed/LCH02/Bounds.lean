import LCH02.Matrix

open scoped BigOperators Classical Matrix
open formal_oet.vol_01.ch_01_foundations

namespace LCH02

variable {X I : Type} {bot : X} [Fintype I]

/-- Domain legality is part of the restricted predicate. -/
def IsLipOn (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) (L : Mat I) : Prop :=
  U ⊆ dom φ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j,
    d j (φ.func x) (φ.func y) ≤ ∑ i, L j i * d i x y

def IsLip (d : I → X → X → ENNReal) (φ : Operator X bot) (L : Mat I) : Prop :=
  IsLipOn d φ (dom φ) L

def LipMatricesOn (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) : Set (Mat I) := {L | IsLipOn d φ U L}

def LipMatrices (d : I → X → X → ENNReal) (φ : Operator X bot) : Set (Mat I) :=
  {L | IsLip d φ L}

/-- In particular, no co-Lip certificate exists on the empty set. -/
def IsCoLipOn (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) (K : Mat I) : Prop :=
  U.Nonempty ∧ U ⊆ dom φ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j,
    (∑ i, K j i * d i x y) ≤ d j (φ.func x) (φ.func y)

def CoLipMatricesOn (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) : Set (Mat I) := {K | IsCoLipOn d φ U K}

theorem composite_domain (φ ψ : Operator X bot) {U : Set X}
    (hU : U ⊆ dom (ψ * φ)) :
    U ⊆ dom φ ∧ φ.func '' U ⊆ dom ψ := by
  constructor
  · intro x hx hbot
    have h := hU hx
    change ψ.func (φ.func x) ≠ bot at h
    exact h (by rw [hbot, ψ.preserves_bot])
  · rintro _ ⟨x, hx, rfl⟩
    exact hU hx

section Gauge
variable [Nonempty I] {d : I → X → X → ENNReal}
variable (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
include hd
set_option linter.unusedSectionVars false

theorem singleton_lip [Subsingleton I] (i : I) {φ : Operator X bot} {L : Mat I}
    (hL : IsLip d φ L) (x y : X) (hx : x ∈ dom φ) (hy : y ∈ dom φ) :
    d i (φ.func x) (φ.func y) ≤ L i i * d i x y := by
  have hs : (∑ k, L i k * d k x y) = L i i * d i x y := by
    apply Finset.sum_eq_single i
    · intro k _ hki
      exact (hki (Subsingleton.elim _ _)).elim
    · simp
  simpa only [hs] using hL.2 x hx y hy i

theorem lip_antitone {φ : Operator X bot} {U V : Set X}
    (hUV : U ⊆ V) (_hV : V ⊆ dom φ) :
    LipMatricesOn d φ V ⊆ LipMatricesOn d φ U := by
  intro L hL
  exact ⟨hUV.trans hL.1, fun x hx y hy j => hL.2 x (hUV hx) y (hUV hy) j⟩

theorem lip_restrict {φ : Operator X bot} {U : Set X} (hU : U ⊆ dom φ) :
    LipMatrices d φ ⊆ LipMatricesOn d φ U :=
  lip_antitone hd hU (Set.Subset.refl _)

theorem colip_antitone {φ : Operator X bot} {U V : Set X}
    (hne : U.Nonempty) (hUV : U ⊆ V) (_hV : V ⊆ dom φ) :
    CoLipMatricesOn d φ V ⊆ CoLipMatricesOn d φ U := by
  intro K hK
  exact ⟨hne, hUV.trans hK.2.1,
    fun x hx y hy j => hK.2.2 x (hUV hx) y (hUV hy) j⟩

theorem colip_restrict {φ : Operator X bot} {U : Set X}
    (hne : U.Nonempty) (hU : U ⊆ dom φ) :
    CoLipMatricesOn d φ (dom φ) ⊆ CoLipMatricesOn d φ U :=
  colip_antitone hd hne hU (Set.Subset.refl _)

theorem lip_comp {φ ψ : Operator X bot} {U : Set X} {L₁ L₂ : Mat I}
    (hU : U ⊆ dom (ψ * φ)) (h₁ : IsLipOn d φ U L₁)
    (h₂ : IsLipOn d ψ (φ.func '' U) L₂) :
    IsLipOn d (ψ * φ) U (L₂ * L₁) := by
  refine ⟨hU, ?_⟩
  intro x hx y hy j
  change d j (ψ.func (φ.func x)) (ψ.func (φ.func y)) ≤ _
  calc
    _ ≤ (L₂ *ᵥ (fun k => d k (φ.func x) (φ.func y))) j :=
      h₂.2 _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ j
    _ ≤ (L₂ *ᵥ (L₁ *ᵥ (fun i => d i x y))) j :=
      mulVec_mono L₂ (h₁.2 x hx y hy) j
    _ = _ := congrFun (Matrix.mulVec_mulVec (fun i => d i x y) L₂ L₁) j

theorem colip_comp {φ ψ : Operator X bot} {U : Set X} {K₁ K₂ : Mat I}
    (hU : U ⊆ dom (ψ * φ)) (h₁ : IsCoLipOn d φ U K₁)
    (h₂ : IsCoLipOn d ψ (φ.func '' U) K₂) :
    IsCoLipOn d (ψ * φ) U (K₂ * K₁) := by
  refine ⟨h₁.1, hU, ?_⟩
  intro x hx y hy j
  change _ ≤ d j (ψ.func (φ.func x)) (ψ.func (φ.func y))
  calc
    _ = (K₂ *ᵥ (K₁ *ᵥ (fun i => d i x y))) j :=
      (congrFun (Matrix.mulVec_mulVec (fun i => d i x y) K₂ K₁) j).symm
    _ ≤ (K₂ *ᵥ (fun k => d k (φ.func x) (φ.func y))) j :=
      mulVec_mono K₂ (h₁.2.2 x hx y hy) j
    _ ≤ _ := h₂.2.2 _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ j

theorem colip_entry_zero {φ : Operator X bot} {K : Mat I}
    (hK : IsCoLipOn d φ (dom φ) K) {x y : X}
    (hx : x ∈ dom φ) (hy : y ∈ dom φ) {i j : I}
    (hout : d j (φ.func x) (φ.func y) = 0) (hin : 0 < d i x y) :
    K j i = 0 := by
  have hterm : K j i * d i x y ≤ 0 := by
    calc
      _ ≤ ∑ k, K j k * d k x y := Finset.single_le_sum (fun k _ => zero_le _) (Finset.mem_univ i)
      _ ≤ d j (φ.func x) (φ.func y) := hK.2.2 x hx y hy j
      _ = 0 := hout
  exact (mul_eq_zero.mp (le_antisymm hterm (zero_le _))).resolve_right (ne_of_gt hin)

theorem identity_lip {U : Set X} (hU : U ⊆ dom (1 : Operator X bot)) :
    IsLipOn d (1 : Operator X bot) U (1 : Mat I) := by
  refine ⟨hU, ?_⟩
  intro x hx y hy j
  change d j x y ≤ ((1 : Mat I) *ᵥ (fun i => d i x y)) j
  simp

theorem identity_colip {U : Set X} (hne : U.Nonempty)
    (hU : U ⊆ dom (1 : Operator X bot)) :
    IsCoLipOn d (1 : Operator X bot) U (1 : Mat I) := by
  refine ⟨hne, hU, ?_⟩
  intro x hx y hy j
  change ((1 : Mat I) *ᵥ (fun i => d i x y)) j ≤ d j x y
  simp

end Gauge
end LCH02
