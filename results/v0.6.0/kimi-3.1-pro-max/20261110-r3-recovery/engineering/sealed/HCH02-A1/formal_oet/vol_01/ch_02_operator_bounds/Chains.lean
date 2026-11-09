import formal_oet.vol_01.ch_02_operator_bounds.Bounds

namespace formal_oet.vol_01.ch_02_operator_bounds

open scoped BigOperators ENNReal Classical
open formal_oet.vol_01.ch_01_foundations

/-- A legal pair composite has a legal first stage. -/
theorem dom_of_chain_two_left {X : Type} {bot : X}
    (ϕ₁ ϕ₂ : Operator X bot) (U : Set X)
    (h : U ⊆ dom (OperatorChain [ϕ₂, ϕ₁])) : U ⊆ dom ϕ₁ := by
  intro x hx hfirst
  have hcomp := h hx
  apply hcomp
  change ϕ₂.func (ϕ₁.func x) = bot
  rw [hfirst, ϕ₂.preserves_bot]

/-- A legal pair composite has a legal second stage on the actual image. -/
theorem image_sub_dom_chain_two_right {X : Type} {bot : X}
    (ϕ₁ ϕ₂ : Operator X bot) (U : Set X)
    (h : U ⊆ dom (OperatorChain [ϕ₂, ϕ₁])) : ϕ₁.func '' U ⊆ dom ϕ₂ := by
  intro z hz
  rcases hz with ⟨x, hx, rfl⟩
  exact h hx

/-- HC02-D05.  The image of the whole composite is exactly the recursively
computed actual domain. -/
theorem operatorChain_image {X : Type} {bot : X} (U : Set X)
    (ϕ : ℕ → Operator X bot) (n : ℕ) :
    (operatorChain ϕ n).func '' U = actualDomain U ϕ n := by
  induction n with
  | zero =>
      simp [operatorChain, actualDomain, OperatorChain]
  | succ n ih =>
      calc
        (operatorChain ϕ (n + 1)).func '' U =
            ((ϕ n).func ∘ (operatorChain ϕ n).func) '' U := rfl
        _ = (ϕ n).func '' ((operatorChain ϕ n).func '' U) := Set.image_comp _ _ _
        _ = actualDomain U ϕ (n + 1) := by rw [ih]; rfl

/-- HC02-D05.  Iterated images are nonempty exactly when the initial set is. -/
theorem actualDomain_nonempty_iff {X : Type} {bot : X} (U : Set X)
    (ϕ : ℕ → Operator X bot) (n : ℕ) :
    (actualDomain U ϕ n).Nonempty ↔ U.Nonempty := by
  induction n with
  | zero => rfl
  | succ n ih => simp [actualDomain, ih]

/-- HC02-D05.  Legality of the full composite implies legality of every
individual step on its actual input domain. -/
theorem actualDomain_subset_dom {X : Type} {bot : X} (U : Set X)
    (ϕ : ℕ → Operator X bot) {n m : ℕ} (hm : m < n)
    (hdom : U ⊆ dom (operatorChain ϕ n)) :
    actualDomain U ϕ m ⊆ dom (ϕ m) := by
  induction n generalizing m with
  | zero => omega
  | succ n ih =>
      by_cases hmn : m = n
      · subst m
        rw [← operatorChain_image]
        exact image_sub_dom_chain_two_right (operatorChain ϕ n) (ϕ n) U hdom
      · apply ih (m := m) (by omega)
        exact dom_of_chain_two_left (operatorChain ϕ n) (ϕ n) U hdom

/-- HC02-D05.  Extract any one local Lip certificate from the recursively
specified chain data. -/
theorem LipChainValid.step {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (U : Set X) (ϕ : ℕ → Operator X bot)
    (L : ℕ → BoundMatrix I) {n m : ℕ} (hm : m < n)
    (hvalid : LipChainValid d U ϕ L n) :
    L m ∈ restrictedLipCertificates d (ϕ m) (actualDomain U ϕ m) := by
  induction n generalizing m with
  | zero => omega
  | succ n ih =>
      by_cases hmn : m = n
      · subst m
        exact hvalid.2
      · exact ih (m := m) (by omega) hvalid.1

/-- HC02-D05.  Extract any one local co-Lip certificate from the recursively
specified chain data. -/
theorem CoLipChainValid.step {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (U : Set X) (ϕ : ℕ → Operator X bot)
    (K : ℕ → BoundMatrix I) {n m : ℕ} (hm : m < n)
    (hvalid : CoLipChainValid d U ϕ K n) :
    K m ∈ restrictedCoLipCertificates d (ϕ m) (actualDomain U ϕ m) := by
  induction n generalizing m with
  | zero => omega
  | succ n ih =>
      by_cases hmn : m = n
      · subst m
        exact hvalid.2
      · exact ih (m := m) (by omega) hvalid.1

/-- HC02-P12.  The specified ordered product of local Lip certificates is a
certificate for the full finite chain. -/
theorem lip_orderedProduct_chain {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (U : Set X) (ϕ : ℕ → Operator X bot)
    (L : ℕ → BoundMatrix I) (n : ℕ)
    (hdom : U ⊆ dom (operatorChain ϕ n))
    (hvalid : LipChainValid d U ϕ L n) :
    orderedProduct L n ∈ restrictedLipCertificates d (operatorChain ϕ n) U := by
  induction n with
  | zero => exact identity_lip d U hdom
  | succ n ih =>
      have hprefix : U ⊆ dom (operatorChain ϕ n) :=
        dom_of_chain_two_left (operatorChain ϕ n) (ϕ n) U hdom
      have hproduct := ih hprefix hvalid.1
      have hlast : L n ∈ restrictedLipCertificates d (ϕ n)
          ((operatorChain ϕ n).func '' U) := by
        rw [operatorChain_image]
        exact hvalid.2
      exact lip_comp_two d (operatorChain ϕ n) (ϕ n) U
        (orderedProduct L n) (L n) hdom hproduct hlast

/-- The co-Lip chain induction with an explicit nonempty initial domain. -/
theorem coLip_orderedProduct_chain_aux {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (U : Set X) (ϕ : ℕ → Operator X bot)
    (K : ℕ → BoundMatrix I) (hU : U.Nonempty) (n : ℕ)
    (hdom : U ⊆ dom (operatorChain ϕ n))
    (hvalid : CoLipChainValid d U ϕ K n) :
    orderedProduct K n ∈ restrictedCoLipCertificates d (operatorChain ϕ n) U := by
  induction n with
  | zero => exact identity_coLip d U hU hdom
  | succ n ih =>
      have hprefix : U ⊆ dom (operatorChain ϕ n) :=
        dom_of_chain_two_left (operatorChain ϕ n) (ϕ n) U hdom
      have hproduct := ih hprefix hvalid.1
      have hlast : K n ∈ restrictedCoLipCertificates d (ϕ n)
          ((operatorChain ϕ n).func '' U) := by
        rw [operatorChain_image]
        exact hvalid.2
      exact coLip_comp_two d (operatorChain ϕ n) (ϕ n) U
        (orderedProduct K n) (K n) hdom hproduct hlast

/-- HC02-P13.  Positive-length co-Lip chain.  Nonemptiness of `U` is derived
from the final local certificate, not added as an extra hypothesis. -/
theorem coLip_orderedProduct_chain_succ {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (U : Set X) (ϕ : ℕ → Operator X bot)
    (K : ℕ → BoundMatrix I) (n : ℕ)
    (hdom : U ⊆ dom (operatorChain ϕ (n + 1)))
    (hvalid : CoLipChainValid d U ϕ K (n + 1)) :
    orderedProduct K (n + 1) ∈ restrictedCoLipCertificates d (operatorChain ϕ (n + 1)) U := by
  apply coLip_orderedProduct_chain_aux d U ϕ K _ (n + 1) hdom hvalid
  have himage : (actualDomain U ϕ n).Nonempty := hvalid.2.1
  exact (actualDomain_nonempty_iff U ϕ n).mp himage

/-- HC02-P14.  Zero-step unit Lip certificate in ordered-product notation. -/
theorem zero_step_unit_lip {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (U : Set X) (ϕ : ℕ → Operator X bot)
    (L : ℕ → BoundMatrix I) (hU : U ⊆ dom (operatorChain ϕ 0)) :
    orderedProduct L 0 ∈ restrictedLipCertificates d (operatorChain ϕ 0) U := by
  exact identity_lip d U hU

/-- HC02-P15.  Zero-step unit co-Lip certificate in ordered-product notation. -/
theorem zero_step_unit_coLip {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (U : Set X) (ϕ : ℕ → Operator X bot)
    (K : ℕ → BoundMatrix I) (hUne : U.Nonempty)
    (hU : U ⊆ dom (operatorChain ϕ 0)) :
    orderedProduct K 0 ∈ restrictedCoLipCertificates d (operatorChain ϕ 0) U := by
  exact identity_coLip d U hUne hU

end formal_oet.vol_01.ch_02_operator_bounds
