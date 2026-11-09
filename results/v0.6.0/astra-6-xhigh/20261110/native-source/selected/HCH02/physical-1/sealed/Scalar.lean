import Bounds
import Mathlib.Data.ENNReal.Inv

noncomputable section
open scoped Classical
open formal_oet.vol_01.ch_01_foundations
namespace HCH02
variable {X I : Type} {bot : X}

def ScalarSet (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) (i j : I) : Set ENNReal :=
  {a | ∀ x ∈ U, ∀ y ∈ U, d j (φ.func x) (φ.func y) ≤ a * d i x y}

def channelInf (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) (i j : I) : ENNReal := sInf (ScalarSet d φ U i j)

variable {d : I → X → X → ENNReal} {φ : Operator X bot} {U : Set X} {i j : I}
  {a b : ENNReal}

theorem scalar_upward (ha : a ∈ ScalarSet d φ U i j) (hab : a ≤ b) :
    b ∈ ScalarSet d φ U i j :=
  fun x hx y hy => (ha x hx y hy).trans (mul_le_mul_left hab _)

theorem above_inf_feasible (h : channelInf d φ U i j < b) : b ∈ ScalarSet d φ U i j := by
  obtain ⟨a, ha, hab⟩ := sInf_lt_iff.mp h
  exact scalar_upward ha hab.le

theorem zero_inf_positive (h : channelInf d φ U i j = 0) (hb : 0 < b) :
    b ∈ ScalarSet d φ U i j := above_inf_feasible (h ▸ hb)

theorem finite_inf_iff : channelInf d φ U i j < ⊤ ↔
    ∃ a < ⊤, a ∈ ScalarSet d φ U i j := by
  constructor
  · intro h
    obtain ⟨a, ha, hat⟩ := sInf_lt_iff.mp h
    exact ⟨a, hat, ha⟩
  · rintro ⟨a, hat, ha⟩
    exact (sInf_le ha).trans_lt hat

theorem scalar_empty_of_zero_input {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    (hin : d i x y = 0) (hout : 0 < d j (φ.func x) (φ.func y)) :
    ScalarSet d φ U i j = ∅ ∧ channelInf d φ U i j = ⊤ := by
  have he : ScalarSet d φ U i j = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro a ha
    have h := ha x hx y hy
    rw [hin, mul_zero] at h
    exact (not_le_of_gt hout) h
  exact ⟨he, by simp [channelInf, he]⟩

theorem positive_finite_inf_attained (hpos : 0 < channelInf d φ U i j)
    (hfin : channelInf d φ U i j < ⊤) :
    channelInf d φ U i j ∈ ScalarSet d φ U i j := by
  intro x hx y hy
  by_cases hzero : d i x y = 0
  · obtain ⟨b, hb, _⟩ := sInf_lt_iff.mp hfin
    simpa [hzero] using hb x hx y hy
  · by_cases htop : d i x y = ⊤
    · rw [htop, ENNReal.mul_top (ne_of_gt hpos)]
      exact le_top
    · change d j (φ.func x) (φ.func y) ≤ sInf (ScalarSet d φ U i j) * d i x y
      rw [sInf_eq_iInf, ENNReal.iInf_mul_of_ne hzero htop]
      apply le_iInf
      intro b
      rw [ENNReal.iInf_mul_of_ne hzero htop]
      exact le_iInf fun hb => hb x hx y hy

/- A genuine gauge-space counterexample: component false has infinite
   distance between distinct points; component true has distance one
   between the two nonabsorbing points. -/
def counterDist (j : Bool) (x y : Fin 3) : ENNReal :=
  if x = y then 0 else if x = 0 ∨ y = 0 then ⊤ else if j then 1 else ⊤

theorem counterMetric (j : Bool) : ExtendedPseudoMetric (Fin 3) 0 (counterDist j) := by
  refine ⟨⟨1, by decide⟩, ?_, ?_, ?_, ?_⟩
  · intro x
    simp [counterDist]
  · intro x y
    simp only [counterDist, eq_comm, or_comm]
  · intro x y z
    fin_cases x <;> fin_cases y <;> fin_cases z <;> cases j <;>
      norm_num [counterDist]
  · intro x hx
    simp [counterDist, hx]

def counterU : Set (Fin 3) := {x | x ≠ 0}

theorem counter_domain : counterU.Nonempty ∧ counterU ⊆ dom (ident : Operator (Fin 3) 0) := by
  exact ⟨⟨1, by change (1 : Fin 3) ≠ 0; decide⟩, fun _ hx => hx⟩

theorem counter_positive_feasible (a : ENNReal) (ha : 0 < a) :
    a ∈ ScalarSet counterDist (ident : Operator (Fin 3) 0) counterU false true := by
  intro x hx y hy
  change x ≠ 0 at hx
  change y ≠ 0 at hy
  by_cases hxy : x = y
  · simp [ident, counterDist, hxy]
  · simp [ident, counterDist, hxy, hx, hy, ENNReal.mul_top (ne_of_gt ha)]

theorem counter_inf_zero :
    channelInf counterDist (ident : Operator (Fin 3) 0) counterU false true = 0 := by
  apply le_antisymm _ (zero_le _)
  apply le_of_forall_gt
  intro b hb
  obtain ⟨a, ha, hab⟩ := exists_between hb
  exact (sInf_le (counter_positive_feasible a ha)).trans_lt hab

theorem counter_zero_not_feasible :
    0 ∉ ScalarSet counterDist (ident : Operator (Fin 3) 0) counterU false true := by
  intro h
  have h12 := h 1 (by change (1 : Fin 3) ≠ 0; decide)
    2 (by change (2 : Fin 3) ≠ 0; decide)
  norm_num [ident, counterDist, show (1 : Fin 3) ≠ 2 by decide,
    show (1 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 0 by decide] at h12

theorem zero_inf_counterexample :
    (∀ j : Bool, ExtendedPseudoMetric (Fin 3) 0 (counterDist j)) ∧
    counterU.Nonempty ∧ counterU ⊆ dom (ident : Operator (Fin 3) 0) ∧
    channelInf counterDist (ident : Operator (Fin 3) 0) counterU false true = 0 ∧
    0 ∉ ScalarSet counterDist (ident : Operator (Fin 3) 0) counterU false true :=
  ⟨counterMetric, counter_domain.1, counter_domain.2, counter_inf_zero, counter_zero_not_feasible⟩

end HCH02
