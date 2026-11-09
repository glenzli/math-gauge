import LCH02.Chains

/- The target statements with the textbook's full gauge-space context. -/
noncomputable section

-- These hypotheses deliberately retain the full textbook context.
set_option linter.unusedSectionVars false

namespace LCH02.Textbook

open formal_oet.vol_01.ch_01_foundations

section Gauge

variable {X I : Type} {bot : X}
    [fi : Fintype I] [ni : Nonempty I] [di : DecidableEq I]
    (d : I → X → X → ENNReal) (hd : ∀ i, ExtendedPseudoMetric X bot (d i))

include hd ni di

theorem scalar_lip [Unique I] (φ : Operator X bot) (L : Mat I) :
    Lip d φ L ↔ ∀ x ∈ dom φ, ∀ y ∈ dom φ,
      d (default : I) (φ.func x) (φ.func y) ≤
        L default default * d default x y :=
  lip_singleton L

theorem lip_antitone (φ : Operator X bot) (U V : Set X)
    (hUV : U ⊆ V) (hV : V ⊆ dom φ) :
    lipFamilyOn d φ V ⊆ lipFamilyOn d φ U :=
  lipFamilyOn_antitone hUV hV

theorem global_lip_restrict (φ : Operator X bot) (U : Set X) (hU : U ⊆ dom φ) :
    lipFamily d φ ⊆ lipFamilyOn d φ U := lip_restrict hU

theorem two_step_lip (φ₁ φ₂ : Operator X bot) (U : Set X) (A B : Mat I)
    (hU : U ⊆ dom (φ₂ * φ₁))
    (h₁ : LipOn d φ₁ U A) (h₂ : LipOn d φ₂ (φ₁.func '' U) B) :
    LipOn d (φ₂ * φ₁) U (B * A) := lip_comp hU h₁ h₂

theorem coLip_antitone (φ : Operator X bot) (U V : Set X)
    (hne : U.Nonempty) (hUV : U ⊆ V) (hV : V ⊆ dom φ) :
    coLipFamilyOn d φ V ⊆ coLipFamilyOn d φ U :=
  coLipFamilyOn_antitone hne hUV hV

theorem global_coLip_restrict (φ : Operator X bot) (U : Set X)
    (hne : U.Nonempty) (hU : U ⊆ dom φ) :
    coLipFamilyOn d φ (dom φ) ⊆ coLipFamilyOn d φ U := coLip_restrict hne hU

theorem forced_zero_entry (φ : Operator X bot) (K : Mat I)
    (hK : CoLipOn d φ (dom φ) K) (x y : X) (hx : x ∈ dom φ) (hy : y ∈ dom φ)
    (i j : I) (hout : d j (φ.func x) (φ.func y) = 0) (hin : 0 < d i x y) :
    entry K i j = 0 := coLip_entry_zero hK hx hy hout hin

theorem two_step_coLip (φ₁ φ₂ : Operator X bot) (U : Set X) (A B : Mat I)
    (hU : U ⊆ dom (φ₂ * φ₁))
    (h₁ : CoLipOn d φ₁ U A) (h₂ : CoLipOn d φ₂ (φ₁.func '' U) B) :
    CoLipOn d (φ₂ * φ₁) U (B * A) := coLip_comp hU h₁ h₂

theorem finite_lip_bound (φ : ℕ → Operator X bot) (L : ℕ → Mat I)
    (U : Set X) (n : ℕ) (hn : 0 < n) (hU : U ⊆ dom (chain φ n))
    (hs : ∀ m < n, LipOn d (φ m) (inputDomain φ U m) (L m)) :
    LipOn d (chain φ n) U (matrixProduct L n) := finite_lip φ L U n hn hU hs

theorem finite_coLip_bound (φ : ℕ → Operator X bot) (K : ℕ → Mat I)
    (U : Set X) (n : ℕ) (hn : 0 < n) (hU : U ⊆ dom (chain φ n))
    (hs : ∀ m < n, CoLipOn d (φ m) (inputDomain φ U m) (K m)) :
    CoLipOn d (chain φ n) U (matrixProduct K n) := finite_coLip φ K U n hn hU hs

theorem unit_lip (U : Set X) (_hne : U.Nonempty)
    (hU : U ⊆ dom (1 : Operator X bot)) :
    LipOn d (1 : Operator X bot) U (1 : Mat I) := identity_lip hU

theorem unit_coLip (U : Set X) (hne : U.Nonempty)
    (hU : U ⊆ dom (1 : Operator X bot)) :
    CoLipOn d (1 : Operator X bot) U (1 : Mat I) := identity_coLip hne hU

end Gauge

section Matrices

variable {I : Type} [Fintype I] [ni : Nonempty I] [DecidableEq I]
include ni

theorem product_positive (M : ℕ → Mat I) (n : ℕ) (_hn : 0 < n) (i j : I) :
    0 < entry (matrixProduct M n) i j ↔
      ∃ p : IndexPath I n i j,
        ∀ m : Fin n, 0 < entry (M m) (p.edge m).1 (p.edge m).2 := by
  rw [matrixProduct_pos_iff]
  exact exists_congr fun p => p.allPositive_iff_edges M

theorem product_zero (M : ℕ → Mat I) (n : ℕ) (_hn : 0 < n) (i j : I) :
    entry (matrixProduct M n) i j = 0 ↔
      ∀ p : IndexPath I n i j,
        ∃ m : Fin n, entry (M m) (p.edge m).1 (p.edge m).2 = 0 := by
  rw [matrixProduct_zero_iff]
  exact forall_congr' fun p => p.hasZero_iff_edges M

end Matrices

end LCH02.Textbook
