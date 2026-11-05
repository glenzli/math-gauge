import formal_oet.vol_01.ch_02_operator_bounds.decoupling
import formal_oet.vol_01.ch_02_operator_bounds.single_channel
import formal_oet.vol_01.ch_01_foundations.metric_entropy
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.EReal.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

namespace formal_oet.vol_01.ch_03_operator_local_degeneracy

open formal_oet.vol_01.ch_01_foundations
open Set

variable {X : Type} {I : Type} {bot : X}

/-! ## Component partition (D01) -/

/-- Constant components of `φ` on `U`. -/
def Iconst (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) : Set I :=
  {i | ∀ x ∈ U, ∀ y ∈ U, d i (φ.func x) (φ.func y) = 0}

/-- Identity components of `φ` on `U`, with constant priority. -/
def Iid (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) : Set I :=
  {i | i ∉ Iconst d φ U ∧ ∀ x ∈ U, d i (φ.func x) x = 0}

/-- Active components of `φ` on `U`. -/
def Iact (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) : Set I :=
  {i | i ∉ Iconst d φ U ∧ i ∉ Iid d φ U}

@[simp] theorem mem_Iconst {d : I → X → X → ENNReal} {φ : Operator X bot}
    {U : Set X} {i : I} :
    i ∈ Iconst d φ U ↔ ∀ x ∈ U, ∀ y ∈ U, d i (φ.func x) (φ.func y) = 0 := Iff.rfl

@[simp] theorem mem_Iid {d : I → X → X → ENNReal} {φ : Operator X bot}
    {U : Set X} {i : I} :
    i ∈ Iid d φ U ↔ i ∉ Iconst d φ U ∧ ∀ x ∈ U, d i (φ.func x) x = 0 := Iff.rfl

@[simp] theorem mem_Iact {d : I → X → X → ENNReal} {φ : Operator X bot}
    {U : Set X} {i : I} :
    i ∈ Iact d φ U ↔ i ∉ Iconst d φ U ∧ i ∉ Iid d φ U := Iff.rfl

theorem not_active_iff (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X)
    (i : I) :
    i ∉ Iact d φ U ↔ i ∈ Iconst d φ U ∨ i ∈ Iid d φ U := by
  constructor
  · intro h
    by_cases hc : i ∈ Iconst d φ U
    · exact Or.inl hc
    · by_cases hi : i ∈ Iid d φ U
      · exact Or.inr hi
      · exact False.elim (h ⟨hc, hi⟩)
  · rintro (hc | hi)
    · intro h; exact h.1 hc
    · intro h; exact h.2 hi

/-! ## Fibers and relations (D02, D03) -/

/-- The computational fiber, represented by simultaneous vanishing on `J`. -/
def Fiber (d : I → X → X → ENNReal) (φ : Operator X bot) (J : Set I)
    (y : X) (U : Set X) : Set X :=
  {x | x ∈ U ∧ ∀ j ∈ J, d j (φ.func x) y = 0}

@[simp] theorem mem_Fiber {d : I → X → X → ENNReal} {φ : Operator X bot}
    {J : Set I} {y : X} {U : Set X} {x : X} :
    x ∈ Fiber d φ J y U ↔ x ∈ U ∧ ∀ j ∈ J, d j (φ.func x) y = 0 := Iff.rfl

/-- Point-value relation on `U`. -/
def REq (φ : Operator X bot) (U : Set X) : Set (X × X) :=
  {p | p.1 ∈ U ∧ p.2 ∈ U ∧ φ.func p.1 = φ.func p.2}

/-- Zero-distance relation on `U`. -/
def RSim (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) : Set (X × X) :=
  {p | p.1 ∈ U ∧ p.2 ∈ U ∧ GaugeZeroRelated d (φ.func p.1) (φ.func p.2)}

@[simp] theorem mem_REq {φ : Operator X bot} {U : Set X} {x y : X} :
    (x, y) ∈ REq φ U ↔ x ∈ U ∧ y ∈ U ∧ φ.func x = φ.func y := Iff.rfl

@[simp] theorem mem_RSim {d : I → X → X → ENNReal} {φ : Operator X bot}
    {U : Set X} {x y : X} :
    (x, y) ∈ RSim d φ U ↔ x ∈ U ∧ y ∈ U ∧ GaugeZeroRelated d (φ.func x) (φ.func y) :=
  Iff.rfl

/-- Separation on a subset, for the full gauge family. -/
def SeparatesOn (d : I → X → X → ENNReal) (S : Set X) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, GaugeZeroRelated d x y → x = y

/-- The zero relation is an equivalence when every component is an extended pseudometric. -/
theorem gaugeZeroRelated_equivalence {d : I → X → X → ENNReal}
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)) :
    Equivalence (GaugeZeroRelated d) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x i; exact (hd i).dist_self x
  · intro x y hxy i
    rw [(hd i).symm]
    exact hxy i
  · intro x y z hxy hyz i
    apply le_antisymm
    · calc
        d i x z ≤ d i x y + d i y z := (hd i).triangle x y z
        _ = 0 := by rw [hxy i, hyz i, zero_add]
    · exact zero_le _

/-- Setoid on an image subset induced by the full zero relation. -/
def imageSetoid (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (U : Set X) : Setoid {y : X // y ∈ φ.func '' U} where
  r p q := GaugeZeroRelated d p.1 q.1
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro p; exact (gaugeZeroRelated_equivalence hd).refl p.1
    · intro p q hpq; exact (gaugeZeroRelated_equivalence hd).symm hpq
    · intro p q r hpq hqr; exact (gaugeZeroRelated_equivalence hd).trans hpq hqr

/-- The quotient of the actual image set by the zero relation. -/
abbrev ImageQuot (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (U : Set X) := Quotient (imageSetoid d hd φ U)

/-- The quotient class of an input point. -/
def imageQuotMk (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (U : Set X) (x : X) (hx : x ∈ U) : ImageQuot d hd φ U :=
  Quotient.mk _ ⟨φ.func x, ⟨x, hx, rfl⟩⟩

/-- Existence of a point-value image factor. -/
def PointFactorExists (φA φB : Operator X bot) (U : Set X) : Prop :=
  ∃ T : {y : X // y ∈ φA.func '' U} → X,
    ∀ (x : X) (hx : x ∈ U),
      T ⟨φA.func x, ⟨x, hx, rfl⟩⟩ = φB.func x

/-- Existence of a quotient image factor. -/
def QuotientFactorExists (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φA φB : Operator X bot) (U : Set X) : Prop :=
  ∃ T : ImageQuot d hd φA U → ImageQuot d hd φB U,
    ∀ (x : X) (hx : x ∈ U),
      T (imageQuotMk d hd φA U x hx) = imageQuotMk d hd φB U x hx

/-- The fiber preorder associated to zero-distance relations. -/
def FiberPreorder (d : I → X → X → ENNReal) (φA φB : Operator X bot) (U : Set X) : Prop :=
  RSim d φA U ⊆ RSim d φB U

/-! ## Zeroing radii (D04, D05) -/

/-- A finite positive radius satisfying the local zeroing condition. -/
def LegalRadius (din : X → X → ENNReal) (P : X → X → Prop)
    (φ : Operator X bot) (y : X) (U : Set X) (r : ENNReal) : Prop :=
  0 < r ∧ r ≠ ⊤ ∧ ∀ x ∈ U, din x y < r → P (φ.func x) (φ.func y)

/-- Pointwise zeroing radius, as the supremum of legal finite positive radii. -/
noncomputable def pointwiseRadius (din : X → X → ENNReal) (P : X → X → Prop)
    (φ : Operator X bot) (y : X) (U : Set X) : ENNReal :=
  ⨆ r : {r : ENNReal // LegalRadius din P φ y U r}, r.1

/-- Pointwise zeroing radius for a single output component. -/
noncomputable def pointwiseZeroRadius (d : I → X → X → ENNReal)
    (φ : Operator X bot) (i j : I) (y : X) (U : Set X) : ENNReal :=
  pointwiseRadius (d i) (fun a b => d j a b = 0) φ y U

/-- Pointwise zeroing radius for an output subfamily. -/
noncomputable def pointwiseZeroRadiusJ (d : I → X → X → ENNReal)
    (φ : Operator X bot) (i : I) (J : Set I) (y : X) (U : Set X) : ENNReal :=
  pointwiseRadius (d i) (fun a b => ∀ j ∈ J, d j a b = 0) φ y U

/-- Unified zeroing radius over a nonempty base set `A`, evaluated on `U`. -/
noncomputable def unifiedRadius (din : X → X → ENNReal) (P : X → X → Prop)
    (φ : Operator X bot) (A : Set X) (U : Set X) : ENNReal :=
  ⨅ y : {y : X // y ∈ A}, pointwiseRadius din P φ y U

/-- Unified zeroing radius for one input component and an output subfamily. -/
noncomputable def unifiedZeroRadiusJ (d : I → X → X → ENNReal)
    (φ : Operator X bot) (i : I) (J : Set I) (A : Set X) : ENNReal :=
  unifiedRadius (d i) (fun a b => ∀ j ∈ J, d j a b = 0) φ A A

/-- The zeroing matrix entry in row `j`, column `i`. -/
noncomputable def zeroingMatrix (d : I → X → X → ENNReal)
    (φ : Operator X bot) (U : Set X) (j i : I) : ENNReal :=
  unifiedRadius (d i) (fun a b => d j a b = 0) φ U U

/-! ## Basic radius lemmas -/

theorem legalRadius_mono {din : X → X → ENNReal} {P : X → X → Prop}
    {φ : Operator X bot} {y : X} {U : Set X} {r r' : ENNReal}
    (hr' : 0 < r') (hrr' : r' ≤ r) (hr : LegalRadius din P φ y U r) :
    LegalRadius din P φ y U r' := by
  refine ⟨hr', ne_top_of_le_ne_top hr.2.1 hrr', ?_⟩
  intro x hx hlt
  exact hr.2.2 x hx (lt_of_lt_of_le hlt hrr')

theorem le_pointwiseRadius_of_legal {din : X → X → ENNReal} {P : X → X → Prop}
    {φ : Operator X bot} {y : X} {U : Set X} {r : ENNReal}
    (hr : LegalRadius din P φ y U r) :
    r ≤ pointwiseRadius din P φ y U :=
  le_iSup (fun s : {s : ENNReal // LegalRadius din P φ y U s} => s.1) ⟨r, hr⟩

theorem pointwiseRadius_eq_top_iff {din : X → X → ENNReal} {P : X → X → Prop}
    {φ : Operator X bot} {y : X} {U : Set X} :
    pointwiseRadius din P φ y U = ⊤ ↔
      ∀ r : ENNReal, 0 < r → r ≠ ⊤ → LegalRadius din P φ y U r := by
  constructor
  · intro htop r hr0 hrtop
    by_contra hnot
    have hbound : ∀ s : {s : ENNReal // LegalRadius din P φ y U s}, s.1 ≤ r := by
      intro s
      by_contra hs
      have hrs : r < s.1 := lt_of_not_ge hs
      exact hnot (legalRadius_mono hr0 (le_of_lt hrs) s.2)
    have hsup : pointwiseRadius din P φ y U ≤ r := iSup_le hbound
    rw [htop] at hsup
    have : r = ⊤ := top_le_iff.mp hsup
    exact hrtop this
  · intro hall
    apply le_antisymm le_top
    by_contra hnot
    have hne : pointwiseRadius din P φ y U ≠ ⊤ := by
      intro h
      exact hnot (h ▸ le_rfl)
    have hlt : pointwiseRadius din P φ y U < ⊤ := lt_top_iff_ne_top.mpr hne
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hne
    have hnpos : 0 < (n : ENNReal) := by
      rcases Nat.eq_zero_or_pos n with rfl | h
      · simp at hn
      · exact_mod_cast h
    have hnne : (n : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top n
    have hleg : LegalRadius din P φ y U (n : ENNReal) := hall _ hnpos hnne
    exact (not_lt_of_ge (le_pointwiseRadius_of_legal hleg)) hn

end formal_oet.vol_01.ch_03_operator_local_degeneracy
