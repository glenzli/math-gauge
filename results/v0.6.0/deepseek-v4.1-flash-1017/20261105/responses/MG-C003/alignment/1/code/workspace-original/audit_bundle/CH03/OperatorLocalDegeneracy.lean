import formal_oet.vol_01.ch_02_operator_bounds.decoupling
import formal_oet.vol_01.ch_02_operator_bounds.single_channel
import formal_oet.vol_01.ch_01_foundations.metric_entropy
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.EReal.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

namespace formal_oet.vol_01.ch_03_operator_local_degeneracy

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
open formal_oet.vol_01.ch_01_foundations
open Set
variable {X : Type} {I : Type} {bot : X}
def Iconst (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) : Set I :=
  {i | ∀ x ∈ U, ∀ y ∈ U, d i (φ.func x) (φ.func y) = 0}
def Iid (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) : Set I :=
  {i | i ∉ Iconst d φ U ∧ ∀ x ∈ U, d i (φ.func x) x = 0}
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
def Fiber (d : I → X → X → ENNReal) (φ : Operator X bot) (J : Set I)
    (y : X) (U : Set X) : Set X :=
  {x | x ∈ U ∧ ∀ j ∈ J, d j (φ.func x) y = 0}
@[simp] theorem mem_Fiber {d : I → X → X → ENNReal} {φ : Operator X bot}
    {J : Set I} {y : X} {U : Set X} {x : X} :
    x ∈ Fiber d φ J y U ↔ x ∈ U ∧ ∀ j ∈ J, d j (φ.func x) y = 0 := Iff.rfl
def REq (φ : Operator X bot) (U : Set X) : Set (X × X) :=
  {p | p.1 ∈ U ∧ p.2 ∈ U ∧ φ.func p.1 = φ.func p.2}
def RSim (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) : Set (X × X) :=
  {p | p.1 ∈ U ∧ p.2 ∈ U ∧ GaugeZeroRelated d (φ.func p.1) (φ.func p.2)}
@[simp] theorem mem_REq {φ : Operator X bot} {U : Set X} {x y : X} :
    (x, y) ∈ REq φ U ↔ x ∈ U ∧ y ∈ U ∧ φ.func x = φ.func y := Iff.rfl
@[simp] theorem mem_RSim {d : I → X → X → ENNReal} {φ : Operator X bot}
    {U : Set X} {x y : X} :
    (x, y) ∈ RSim d φ U ↔ x ∈ U ∧ y ∈ U ∧ GaugeZeroRelated d (φ.func x) (φ.func y) :=
  Iff.rfl
def SeparatesOn (d : I → X → X → ENNReal) (S : Set X) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, GaugeZeroRelated d x y → x = y
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
def imageSetoid (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (U : Set X) : Setoid {y : X // y ∈ φ.func '' U} where
  r p q := GaugeZeroRelated d p.1 q.1
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro p; exact (gaugeZeroRelated_equivalence hd).refl p.1
    · intro p q hpq; exact (gaugeZeroRelated_equivalence hd).symm hpq
    · intro p q r hpq hqr; exact (gaugeZeroRelated_equivalence hd).trans hpq hqr
abbrev ImageQuot (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (U : Set X) := Quotient (imageSetoid d hd φ U)
def imageQuotMk (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (U : Set X) (x : X) (hx : x ∈ U) : ImageQuot d hd φ U :=
  Quotient.mk _ ⟨φ.func x, ⟨x, hx, rfl⟩⟩
def PointFactorExists (φA φB : Operator X bot) (U : Set X) : Prop :=
  ∃ T : {y : X // y ∈ φA.func '' U} → X,
    ∀ (x : X) (hx : x ∈ U),
      T ⟨φA.func x, ⟨x, hx, rfl⟩⟩ = φB.func x
def QuotientFactorExists (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φA φB : Operator X bot) (U : Set X) : Prop :=
  ∃ T : ImageQuot d hd φA U → ImageQuot d hd φB U,
    ∀ (x : X) (hx : x ∈ U),
      T (imageQuotMk d hd φA U x hx) = imageQuotMk d hd φB U x hx
def FiberPreorder (d : I → X → X → ENNReal) (φA φB : Operator X bot) (U : Set X) : Prop :=
  RSim d φA U ⊆ RSim d φB U
def LegalRadius (din : X → X → ENNReal) (P : X → X → Prop)
    (φ : Operator X bot) (y : X) (U : Set X) (r : ENNReal) : Prop :=
  0 < r ∧ r ≠ ⊤ ∧ ∀ x ∈ U, din x y < r → P (φ.func x) (φ.func y)
noncomputable def pointwiseRadius (din : X → X → ENNReal) (P : X → X → Prop)
    (φ : Operator X bot) (y : X) (U : Set X) : ENNReal :=
  ⨆ r : {r : ENNReal // LegalRadius din P φ y U r}, r.1
noncomputable def pointwiseZeroRadius (d : I → X → X → ENNReal)
    (φ : Operator X bot) (i j : I) (y : X) (U : Set X) : ENNReal :=
  pointwiseRadius (d i) (fun a b => d j a b = 0) φ y U
noncomputable def pointwiseZeroRadiusJ (d : I → X → X → ENNReal)
    (φ : Operator X bot) (i : I) (J : Set I) (y : X) (U : Set X) : ENNReal :=
  pointwiseRadius (d i) (fun a b => ∀ j ∈ J, d j a b = 0) φ y U
noncomputable def unifiedRadius (din : X → X → ENNReal) (P : X → X → Prop)
    (φ : Operator X bot) (A : Set X) (U : Set X) : ENNReal :=
  ⨅ y : {y : X // y ∈ A}, pointwiseRadius din P φ y U
noncomputable def unifiedZeroRadiusJ (d : I → X → X → ENNReal)
    (φ : Operator X bot) (i : I) (J : Set I) (A : Set X) : ENNReal :=
  unifiedRadius (d i) (fun a b => ∀ j ∈ J, d j a b = 0) φ A A
noncomputable def zeroingMatrix (d : I → X → X → ENNReal)
    (φ : Operator X bot) (U : Set X) (j i : I) : ENNReal :=
  unifiedRadius (d i) (fun a b => d j a b = 0) φ U U
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
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set
variable {X : Type} {I : Type} {bot : X}
theorem const_component_zero_row_bound [Fintype I]
    (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) (i : I)
    (hi : i ∈ Iconst d φ U) :
    ∀ x ∈ U, ∀ y ∈ U,
      d i (φ.func x) (φ.func y) ≤ ∑ k : I, (0 : ENNReal) * d k x y := by
  intro x hx y hy
  rw [hi x hx y hy]
  simp
theorem const_component_colip_entry_zero
    [Fintype I] (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X)
    (K : I → I → ENNReal) (i k : I)
    (hK : IsCoLipMatrix d φ U K) (hi : i ∈ Iconst d φ U)
    (hpos : ∃ x ∈ U, ∃ y ∈ U, 0 < d k x y) :
    K k i = 0 := by
  rcases hpos with ⟨x, hx, y, hy, hxy⟩
  have hconst : d i (φ.func x) (φ.func y) = 0 := hi x hx y hy
  have hineq := hK.2.2 x hx y hy i
  rw [hconst] at hineq
  have hsingle :
      K k i * d k x y ≤ ∑ l : I, K l i * d l x y := by
    exact Finset.single_le_sum (fun l _ => (zero_le (K l i * d l x y) : (0 : ENNReal) ≤ _)) (Finset.mem_univ k)
  have hterm : K k i * d k x y = 0 :=
    le_antisymm (le_trans hsingle hineq) (zero_le (K k i * d k x y))
  rcases mul_eq_zero.mp hterm with h | h
  · exact h
  · exact False.elim ((ne_of_gt hxy) h)
theorem id_component_isometry
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (U : Set X) (i : I) (hi : i ∈ Iid d φ U) :
    ∀ x ∈ U, ∀ y ∈ U, d i (φ.func x) (φ.func y) = d i x y := by
  rcases hi with ⟨_, hzero⟩
  intro x hx y hy
  apply le_antisymm
  · calc
      d i (φ.func x) (φ.func y)
          ≤ d i (φ.func x) x + d i x (φ.func y) := (hd i).triangle _ _ _
      _ ≤ d i (φ.func x) x + (d i x y + d i y (φ.func y)) := by
        gcongr
        exact (hd i).triangle _ _ _
      _ = d i x y := by
        rw [hzero x hx, ← (hd i).symm (φ.func y) y, hzero y hy]
        simp
  · calc
      d i x y
          ≤ d i x (φ.func x) + d i (φ.func x) y := (hd i).triangle _ _ _
      _ ≤ d i x (φ.func x) + (d i (φ.func x) (φ.func y) + d i (φ.func y) y) := by
        gcongr
        exact (hd i).triangle _ _ _
      _ = d i (φ.func x) (φ.func y) := by
        rw [← (hd i).symm (φ.func x) x, hzero x hx, hzero y hy]
        simp
theorem active_composite_of_not_active_steps
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ1 φ2 : Operator X bot) (U : Set X) (i : I)
    (h1 : i ∉ Iact d φ1 U) (h2 : i ∉ Iact d φ2 (φ1.func '' U)) :
    i ∉ Iact d (φ2 * φ1) U := by
  have h1c := (not_active_iff d φ1 U i).mp h1
  have h2c := (not_active_iff d φ2 (φ1.func '' U) i).mp h2
  have hcomp_notconst_or_id :
      i ∈ Iconst d (φ2 * φ1) U ∨ i ∈ Iid d (φ2 * φ1) U := by
    rcases h1c with h1const | h1id
    · rcases h2c with h2const | h2id
      · left
        intro x hx y hy
        exact h2const (φ1.func x) ⟨x, hx, rfl⟩ (φ1.func y) ⟨y, hy, rfl⟩
      · rcases h2id with ⟨_, h2zero⟩
        left
        intro x hx y hy
        have hφx : φ1.func x ∈ φ1.func '' U := ⟨x, hx, rfl⟩
        have hφy : φ1.func y ∈ φ1.func '' U := ⟨y, hy, rfl⟩
        have hmid : d i (φ1.func x) (φ1.func y) = 0 := h1const x hx y hy
        apply le_antisymm
        · calc
            d i ((φ2 * φ1).func x) ((φ2 * φ1).func y)
                = d i (φ2.func (φ1.func x)) (φ2.func (φ1.func y)) := rfl
            _ ≤ d i (φ2.func (φ1.func x)) (φ1.func x) +
                  d i (φ1.func x) (φ2.func (φ1.func y)) := (hd i).triangle _ _ _
            _ ≤ d i (φ2.func (φ1.func x)) (φ1.func x) +
                  (d i (φ1.func x) (φ1.func y) +
                    d i (φ1.func y) (φ2.func (φ1.func y))) := by
              gcongr
              exact (hd i).triangle _ _ _
            _ = 0 := by
              rw [h2zero (φ1.func x) hφx, hmid,
                ← (hd i).symm (φ2.func (φ1.func y)) (φ1.func y),
                h2zero (φ1.func y) hφy]
              simp
        · exact zero_le _
    · rcases h2c with h2const | h2id
      · left
        intro x hx y hy
        exact h2const (φ1.func x) ⟨x, hx, rfl⟩ (φ1.func y) ⟨y, hy, rfl⟩
      · rcases h1id with ⟨h1nc, h1zero⟩
        rcases h2id with ⟨h2nc', h2zero⟩
        right
        refine ⟨?_, ?_⟩
        · intro hcompconst
          apply h1nc
          intro x hx y hy
          have hout := hcompconst x hx y hy
          change d i (φ2.func (φ1.func x)) (φ2.func (φ1.func y)) = 0 at hout
          have hiso := id_component_isometry d hd φ2 (φ1.func '' U) i
            ⟨h2nc', h2zero⟩ (φ1.func x) ⟨x, hx, rfl⟩ (φ1.func y) ⟨y, hy, rfl⟩
          rw [hiso] at hout
          exact hout
        · intro x hx
          have hφx : φ1.func x ∈ φ1.func '' U := ⟨x, hx, rfl⟩
          apply le_antisymm
          · calc
              d i ((φ2 * φ1).func x) x
                  = d i (φ2.func (φ1.func x)) x := rfl
              _ ≤ d i (φ2.func (φ1.func x)) (φ1.func x) + d i (φ1.func x) x :=
                  (hd i).triangle _ _ _
              _ = 0 := by rw [h2zero (φ1.func x) hφx, h1zero x hx]; simp
          · exact zero_le _
  exact (not_active_iff d (φ2 * φ1) U i).mpr hcomp_notconst_or_id
theorem active_subset_two_step
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ1 φ2 : Operator X bot) (U : Set X) :
    Iact d (φ2 * φ1) U ⊆
      Iact d φ1 U ∪ Iact d φ2 (φ1.func '' U) := by
  intro i hi
  by_contra hnot
  have h1 : i ∉ Iact d φ1 U := fun h => hnot (Or.inl h)
  have h2 : i ∉ Iact d φ2 (φ1.func '' U) := fun h => hnot (Or.inr h)
  exact (active_composite_of_not_active_steps d hd φ1 φ2 U i h1 h2) hi
theorem id_subset_composite_id
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ1 φ2 : Operator X bot) (U : Set X) :
    Iid d φ1 U ∩ Iid d φ2 (φ1.func '' U) ⊆ Iid d (φ2 * φ1) U := by
  intro i hi
  rcases hi with ⟨h1id, h2id⟩
  rcases h1id with ⟨h1nc, h1zero⟩
  rcases h2id with ⟨h2nc, h2zero⟩
  refine ⟨?_, ?_⟩
  · intro hcompconst
    apply h1nc
    intro x hx y hy
    have hout := hcompconst x hx y hy
    change d i (φ2.func (φ1.func x)) (φ2.func (φ1.func y)) = 0 at hout
    have hiso := id_component_isometry d hd φ2 (φ1.func '' U) i
      ⟨h2nc, h2zero⟩ (φ1.func x) ⟨x, hx, rfl⟩ (φ1.func y) ⟨y, hy, rfl⟩
    rw [hiso] at hout
    exact hout
  · intro x hx
    have hφx : φ1.func x ∈ φ1.func '' U := ⟨x, hx, rfl⟩
    apply le_antisymm
    · calc
        d i ((φ2 * φ1).func x) x
            = d i (φ2.func (φ1.func x)) x := rfl
        _ ≤ d i (φ2.func (φ1.func x)) (φ1.func x) + d i (φ1.func x) x :=
            (hd i).triangle _ _ _
        _ = 0 := by rw [h2zero (φ1.func x) hφx, h1zero x hx]; simp
    · exact zero_le _
def listCompose : List (Operator X bot) → Operator X bot
  | [] => 1
  | φ :: rest => listCompose rest * φ
@[simp] theorem listCompose_nil : listCompose ([] : List (Operator X bot)) = 1 := rfl
@[simp] theorem listCompose_cons (φ : Operator X bot) (rest : List (Operator X bot)) :
    listCompose (φ :: rest) = listCompose rest * φ := rfl
def imageChain : List (Operator X bot) → Set X → List (Set X)
  | [], U => [U]
  | φ :: rest, U => U :: imageChain rest (φ.func '' U)
def activeChain (d : I → X → X → ENNReal) :
    List (Operator X bot) → Set X → List (Set I)
  | [], _ => []
  | φ :: rest, U => Iact d φ U :: activeChain d rest (φ.func '' U)
def listUnion {α : Type} : List (Set α) → Set α
  | [] => ∅
  | s :: ss => s ∪ listUnion ss
theorem active_identity_eq_empty
    (d : I → X → X → ENNReal) (hself : ∀ i x, d i x x = 0) (U : Set X) :
    Iact d (1 : Operator X bot) U = ∅ := by
  ext i
  constructor
  · intro hi
    by_cases hc : i ∈ Iconst d (1 : Operator X bot) U
    · exact (hi.1 hc).elim
    · have hiid : i ∈ Iid d (1 : Operator X bot) U := by
        refine ⟨hc, ?_⟩
        intro x hx
        change d i x x = 0
        exact hself i x
      exact (hi.2 hiid).elim
  · intro hi; simp at hi
/-- The active components of an arbitrary finite chain are contained in the
union of the active components at the actual successive image domains. -/
theorem active_subset_union_chain
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φs : List (Operator X bot)) (U : Set X)
    (hdom : U ⊆ dom (listCompose φs)) :
    Iact d (listCompose φs) U ⊆ listUnion (activeChain d φs U) := by
  induction φs generalizing U with
  | nil =>
      change Iact d (1 : Operator X bot) U ⊆ listUnion (activeChain d [] U)
      rw [active_identity_eq_empty d (fun i x => (hd i).dist_self x)]
      simp [listUnion, activeChain]
  | cons φ rest ih =>
      rw [listCompose_cons]
      have hdomφ : U ⊆ dom φ := by
        intro x hx
        by_contra hxbot
        have hxval : φ.func x = bot := by simpa [dom] using hxbot
        have hcomp : (listCompose rest * φ).func x = bot := by
          change (listCompose rest).func (φ.func x) = bot
          rw [hxval, (listCompose rest).preserves_bot]
        exact hdom hx (by simpa [dom] using hcomp)
      have hdomRest : φ.func '' U ⊆ dom (listCompose rest) := by
        intro y hy
        rcases hy with ⟨x, hx, rfl⟩
        have hxne : (listCompose rest).func (φ.func x) ≠ bot := by
          intro hb
          exact hdom hx (by simpa [dom, listCompose_cons] using hb)
        simpa [dom] using hxne
      intro i hi
      have hstep := active_subset_two_step d hd φ (listCompose rest) U hi
      rcases hstep with hleft | hright
      · exact Or.inl hleft
      · have hrec := ih (φ.func '' U) hdomRest hright
        exact Or.inr hrec
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set
variable {X : Type} {I : Type} {bot : X}
theorem outer_const_composite_const
    (d : I → X → X → ENNReal) (φ ψ : Operator X bot) (U : Set X) (i : I)
    (hi : i ∈ Iconst d ψ (φ.func '' U)) :
    i ∈ Iconst d (ψ * φ) U := by
  intro x hx y hy
  exact hi (φ.func x) ⟨x, hx, rfl⟩ (φ.func y) ⟨y, hy, rfl⟩
theorem inner_const_preserved_of_zero_row
    [Fintype I] (d : I → X → X → ENNReal) (φ ψ : Operator X bot)
    (U : Set X) (j : I) (L : I → I → ENNReal)
    (hj : j ∈ Iconst d φ U)
    (hL : IsLipMatrix d ψ (φ.func '' U) L)
    (hrow : ∀ k : I, k ≠ j → L k j = 0) :
    j ∈ Iconst d (ψ * φ) U := by
  intro x hx y hy
  have hx' : φ.func x ∈ φ.func '' U := ⟨x, hx, rfl⟩
  have hy' : φ.func y ∈ φ.func '' U := ⟨y, hy, rfl⟩
  have hbound' := hL.2 (φ.func x) hx' (φ.func y) hy' j
  have hsum : (∑ k : I, L k j * d k (φ.func x) (φ.func y)) =
      L j j * d j (φ.func x) (φ.func y) := by
    apply Finset.sum_eq_single j
    · intro k _ hk
      rw [hrow k hk, zero_mul]
    · intro hjmem
      exact (hjmem (Finset.mem_univ j)).elim
  have hconst : d j (φ.func x) (φ.func y) = 0 := hj x hx y hy
  rw [hsum] at hbound'
  have : d j ((ψ * φ).func x) ((ψ * φ).func y) ≤ 0 := by
    simpa [hconst] using hbound'
  exact le_antisymm this (zero_le _)
theorem fiber_target_zero_eq
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (J : Set I) (U : Set X) {y y' : X}
    (hy : ∀ j ∈ J, d j y y' = 0) :
    Fiber d φ J y U = Fiber d φ J y' U := by
  ext x
  constructor
  · rintro ⟨hx, hxzero⟩
    refine ⟨hx, fun j hj => ?_⟩
    have hle : d j (φ.func x) y' ≤ 0 := by
      calc
        d j (φ.func x) y' ≤ d j (φ.func x) y + d j y y' := (hd j).triangle _ _ _
        _ = 0 := by rw [hxzero j hj, hy j hj]; simp
    exact le_antisymm hle (zero_le _)
  · rintro ⟨hx, hxzero⟩
    refine ⟨hx, fun j hj => ?_⟩
    have hyx : d j y' y = 0 := by
      rw [(hd j).symm]
      exact hy j hj
    have hle : d j (φ.func x) y ≤ 0 := by
      calc
        d j (φ.func x) y ≤ d j (φ.func x) y' + d j y' y := (hd j).triangle _ _ _
        _ = 0 := by rw [hxzero j hj, hyx]; simp
    exact le_antisymm hle (zero_le _)
theorem fiber_self_mem
    (d : I → X → X → ENNReal) (hself : ∀ i x, d i x x = 0)
    (φ : Operator X bot) (J : Set I) (U : Set X) {x : X} (hx : x ∈ U) :
    x ∈ Fiber d φ J (φ.func x) U :=
  ⟨hx, fun j _ => hself j (φ.func x)⟩
theorem fiber_image_nonempty
    (d : I → X → X → ENNReal) (hself : ∀ i x, d i x x = 0)
    (φ : Operator X bot) (J : Set I) (U : Set X) {y : X}
    (hy : y ∈ φ.func '' U) : (Fiber d φ J y U).Nonempty := by
  rcases hy with ⟨x, hx, rfl⟩
  exact ⟨x, fiber_self_mem d hself φ J U hx⟩
theorem fiber_cover
    (d : I → X → X → ENNReal) (hself : ∀ i x, d i x x = 0)
    (φ : Operator X bot) (J : Set I) (U : Set X) :
    ∀ x : X, x ∈ U ↔ ∃ y : X, y ∈ φ.func '' U ∧ x ∈ Fiber d φ J y U := by
  intro x
  constructor
  · intro hx
    exact ⟨φ.func x, ⟨x, hx, rfl⟩, fiber_self_mem d hself φ J U hx⟩
  · rintro ⟨y, _, hx, _⟩
    exact hx
theorem fiber_eq_or_disjoint
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (J : Set I) (U : Set X) :
    ∀ y1 : X, y1 ∈ φ.func '' U → ∀ y2 : X, y2 ∈ φ.func '' U →
      Fiber d φ J y1 U = Fiber d φ J y2 U ∨
        Disjoint (Fiber d φ J y1 U) (Fiber d φ J y2 U) := by
  intro y1 hy1 y2 hy2
  by_cases hinter : (Fiber d φ J y1 U ∩ Fiber d φ J y2 U).Nonempty
  · left
    rcases hinter with ⟨x, hx1, hx2⟩
    have hzero : ∀ j ∈ J, d j y1 y2 = 0 := by
      intro j hj
      have hx1j : d j (φ.func x) y1 = 0 := hx1.2 j hj
      have hx2j : d j (φ.func x) y2 = 0 := hx2.2 j hj
      have hle : d j y1 y2 ≤ 0 := by
        calc
          d j y1 y2 ≤ d j y1 (φ.func x) + d j (φ.func x) y2 := (hd j).triangle _ _ _
          _ = 0 := by
            rw [← (hd j).symm, hx1j, hx2j]; simp
      exact le_antisymm hle (zero_le _)
    exact fiber_target_zero_eq d hd φ J U hzero
  · right
    rw [Set.disjoint_left]
    intro x hx1 hx2
    exact hinter ⟨x, hx1, hx2⟩
theorem fiber_partition
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (J : Set I) (U : Set X) :
    (∀ x : X, x ∈ U ↔ ∃ y : X, y ∈ φ.func '' U ∧ x ∈ Fiber d φ J y U) ∧
    (∀ y1 : X, y1 ∈ φ.func '' U → ∀ y2 : X, y2 ∈ φ.func '' U →
      Fiber d φ J y1 U = Fiber d φ J y2 U ∨
        Disjoint (Fiber d φ J y1 U) (Fiber d φ J y2 U)) ∧
    (∀ y : X, y ∈ φ.func '' U → (Fiber d φ J y U).Nonempty) := by
  refine ⟨fiber_cover d (fun i x => (hd i).dist_self x) φ J U, ?_, ?_⟩
  · exact fiber_eq_or_disjoint d hd φ J U
  · intro y hy
    exact fiber_image_nonempty d (fun i x => (hd i).dist_self x) φ J U hy
theorem fiber_inter
    (d : I → X → X → ENNReal) (φ : Operator X bot) (J : Set I)
    (hJ : J.Nonempty) (U : Set X) (y : X) :
    Fiber d φ J y U = ⋂ j ∈ J, Fiber d φ ({j} : Set I) y U := by
  ext x
  constructor
  · rintro ⟨hx, hxzero⟩
    simp only [Set.mem_iInter]
    intro j hj
    exact ⟨hx, by simpa using hxzero j hj⟩
  · intro hx
    simp only [Set.mem_iInter] at hx
    rcases hJ with ⟨j0, hj0⟩
    have hx0 := hx j0 hj0
    refine ⟨hx0.1, ?_⟩
    intro j hj
    exact (hx j hj).2 j (by simp)
theorem fiber_antitone_subfamily
    (d : I → X → X → ENNReal) (φ : Operator X bot) {J K : Set I}
    (hJK : J ⊆ K) (U : Set X) (y : X) :
    Fiber d φ K y U ⊆ Fiber d φ J y U := by
  intro x hx
  exact ⟨hx.1, fun j hj => hx.2 j (hJK hj)⟩
theorem fiber_singleton_eq
    (d : I → X → X → ENNReal) (φ : Operator X bot) (i : I) (U : Set X) (y : X) :
    Fiber d φ ({i} : Set I) y U = {x | x ∈ U ∧ d i (φ.func x) y = 0} := by
  ext x
  simp [Fiber]
theorem fiber_full_subset_singleton
    (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) (y : X) (i : I) :
    Fiber d φ (Set.univ : Set I) y U ⊆ Fiber d φ ({i} : Set I) y U :=
  fiber_antitone_subfamily d φ (by intro j _; simp) U y
theorem fiber_id_component
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (U : Set X) (y : X) (hy : y ∈ U) (j : I)
    (hj : j ∈ Iid d φ U) :
    Fiber d φ ({j} : Set I) (φ.func y) U = {x | x ∈ U ∧ d j x y = 0} := by
  ext x
  constructor
  · rintro ⟨hx, hxzero⟩
    refine ⟨hx, ?_⟩
    have hiso := id_component_isometry d hd φ U j hj x hx y hy
    have hout : d j (φ.func x) (φ.func y) = 0 := by
      exact hxzero j (by simp)
    rwa [hiso] at hout
  · rintro ⟨hx, hxy⟩
    refine ⟨hx, ?_⟩
    have hiso := id_component_isometry d hd φ U j hj x hx y hy
    intro k hk
    simp only [Set.mem_singleton_iff] at hk
    subst k
    rw [hiso, hxy]
theorem fiber_const_component_image
    (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) (j : I)
    (hj : j ∈ Iconst d φ U) {y0 : X} (hy0 : y0 ∈ φ.func '' U) :
    Fiber d φ ({j} : Set I) y0 U = U := by
  rcases hy0 with ⟨z, hz, rfl⟩
  ext x
  constructor
  · intro hx; exact hx.1
  · intro hx
    refine ⟨hx, ?_⟩
    intro k hk
    simp only [Set.mem_singleton_iff] at hk
    subst k
    exact hj x hx z hz
theorem fiber_const_component_empty
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (U : Set X) (j : I)
    (hj : j ∈ Iconst d φ U) {y0 y : X}
    (hy0 : y0 ∈ φ.func '' U) (hpos : 0 < d j y y0) :
    Fiber d φ ({j} : Set I) y U = ∅ := by
  ext x
  constructor
  · intro hx
    exfalso
    have hxy : d j (φ.func x) y = 0 := hx.2 j (by simp)
    rcases hy0 with ⟨z, hz, rfl⟩
    have hxz : d j (φ.func x) (φ.func z) = 0 := hj x hx.1 z hz
    have hle : d j (φ.func z) y ≤ 0 := by
      calc
        d j (φ.func z) y ≤ d j (φ.func z) (φ.func x) + d j (φ.func x) y :=
          (hd j).triangle _ _ _
        _ = 0 := by rw [← (hd j).symm, hxz, hxy]; simp
    have hthis : d j (φ.func z) y = 0 := le_antisymm hle (zero_le _)
    rw [(hd j).symm] at hthis
    exact (ne_of_gt hpos) hthis
  · intro hx; simp at hx
theorem point_factor_necessary
    (φA φB : Operator X bot) (U : Set X)
    (hT : PointFactorExists φA φB U) :
    REq φA U ⊆ REq φB U := by
  rcases hT with ⟨T, hT⟩
  intro p hp
  rcases p with ⟨x, y⟩
  rcases hp with ⟨hx, hy, hxy⟩
  refine ⟨hx, hy, ?_⟩
  have hsub : (⟨φA.func x, ⟨x, hx, rfl⟩⟩ : {z : X // z ∈ φA.func '' U}) =
      ⟨φA.func y, ⟨y, hy, rfl⟩⟩ := Subtype.ext hxy
  have h := congrArg T hsub
  simpa [hT x hx, hT y hy] using h
theorem point_factor_sufficient
    (φA φB : Operator X bot) (U : Set X)
    (h : REq φA U ⊆ REq φB U) :
    PointFactorExists φA φB U := by
  classical
  let rep : {y : X // y ∈ φA.func '' U} → X := fun y => Classical.choose y.2
  have hrepU : ∀ y, rep y ∈ U := fun y => (Classical.choose_spec y.2).1
  have hrepval : ∀ y, φA.func (rep y) = y.1 := fun y => (Classical.choose_spec y.2).2
  refine ⟨fun y => φB.func (rep y), ?_⟩
  intro x hx
  have hpair : (rep ⟨φA.func x, ⟨x, hx, rfl⟩⟩, x) ∈ REq φA U := by
    refine ⟨hrepU _, hx, ?_⟩
    rw [hrepval]
  exact (h hpair).2.2
theorem point_factor_iff
    (φA φB : Operator X bot) (U : Set X) :
    PointFactorExists φA φB U ↔ REq φA U ⊆ REq φB U :=
  ⟨point_factor_necessary φA φB U, point_factor_sufficient φA φB U⟩
theorem point_factor_both_iff
    (φA φB : Operator X bot) (U : Set X) :
    (PointFactorExists φA φB U ∧ PointFactorExists φB φA U) ↔
      REq φA U = REq φB U := by
  constructor
  · rintro ⟨hAB, hBA⟩
    exact le_antisymm (point_factor_necessary φA φB U hAB)
      (point_factor_necessary φB φA U hBA)
  · intro hEq
    constructor
    · exact point_factor_sufficient φA φB U (le_of_eq hEq)
    · exact point_factor_sufficient φB φA U (le_of_eq hEq.symm)
def ScalarLip (d : X → X → ENNReal) (φ : Operator X bot) (U : Set X) (L : ENNReal) : Prop :=
  U ⊆ dom φ ∧ ∀ x ∈ U, ∀ y ∈ U, d (φ.func x) (φ.func y) ≤ L * d x y
def ScalarCoLip (d : X → X → ENNReal) (φ : Operator X bot) (U : Set X) (K : ENNReal) : Prop :=
  U.Nonempty ∧ U ⊆ dom φ ∧ ∀ x ∈ U, ∀ y ∈ U, K * d x y ≤ d (φ.func x) (φ.func y)
theorem point_factor_scalar_lip
    (d : X → X → ENNReal) (φA φB : Operator X bot) (U : Set X)
    (T : {y : X // y ∈ φA.func '' U} → X)
    (hT : ∀ (x : X) (hx : x ∈ U),
      T ⟨φA.func x, ⟨x, hx, rfl⟩⟩ = φB.func x)
    (K L : ENNReal)
    (hK : ScalarCoLip d φA U K) (hL : ScalarLip d φB U L)
    (hKpos : 0 < K) (hKtop : K ≠ ⊤) :
    ∀ y : {y : X // y ∈ φA.func '' U}, ∀ y' : {y : X // y ∈ φA.func '' U},
      d (T y) (T y') ≤ (L / K) * d y.1 y'.1 := by
  classical
  let rep : {y : X // y ∈ φA.func '' U} → X := fun y => Classical.choose y.2
  have hrepU : ∀ y, rep y ∈ U := fun y => (Classical.choose_spec y.2).1
  have hrepval : ∀ y, φA.func (rep y) = y.1 := fun y => (Classical.choose_spec y.2).2
  have hTy : ∀ y, T y = φB.func (rep y) := by
    intro y
    have hsub : (⟨φA.func (rep y), ⟨rep y, hrepU y, rfl⟩⟩ :
        {z : X // z ∈ φA.func '' U}) = y := Subtype.ext (hrepval y)
    calc
      T y = T ⟨φA.func (rep y), ⟨rep y, hrepU y, rfl⟩⟩ := congrArg T hsub.symm
      _ = φB.func (rep y) := hT (rep y) (hrepU y)
  intro y y'
  rw [hTy y, hTy y']
  have hco := hK.2.2 (rep y) (hrepU y) (rep y') (hrepU y')
  have hco' : K * d (rep y) (rep y') ≤ d y.1 y'.1 := by
    simpa [hrepval y, hrepval y'] using hco
  have hlip := hL.2 (rep y) (hrepU y) (rep y') (hrepU y')
  have hstep : d (rep y) (rep y') ≤ d y.1 y'.1 / K := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl (ne_of_gt hKpos)) (Or.inl hKtop)]
    rwa [mul_comm]
  calc
    d (φB.func (rep y)) (φB.func (rep y'))
        ≤ L * d (rep y) (rep y') := hlip
    _ ≤ L * (d y.1 y'.1 / K) := by gcongr
    _ = (L / K) * d y.1 y'.1 := by
      rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
      ac_rfl
theorem quotient_factor_sufficient
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φA φB : Operator X bot) (U : Set X)
    (h : RSim d φA U ⊆ RSim d φB U) :
    QuotientFactorExists d hd φA φB U := by
  classical
  let repA : {y : X // y ∈ φA.func '' U} → X := fun y => Classical.choose y.2
  have hrepAU : ∀ y, repA y ∈ U := fun y => (Classical.choose_spec y.2).1
  have hrepAval : ∀ y, φA.func (repA y) = y.1 := fun y => (Classical.choose_spec y.2).2
  let f : {y : X // y ∈ φA.func '' U} → ImageQuot d hd φB U :=
    fun y => imageQuotMk d hd φB U (repA y) (hrepAU y)
  have hf : ∀ p q : {y : X // y ∈ φA.func '' U},
      GaugeZeroRelated d p.1 q.1 → f p = f q := by
    intro p q hpq
    apply Quotient.sound
    have hA : GaugeZeroRelated d (φA.func (repA p)) (φA.func (repA q)) := by
      simpa [hrepAval] using hpq
    have hR : (repA p, repA q) ∈ RSim d φA U :=
      ⟨hrepAU p, hrepAU q, hA⟩
    exact (h hR).2.2
  let T : ImageQuot d hd φA U → ImageQuot d hd φB U := Quotient.lift f hf
  refine ⟨T, ?_⟩
  intro x hx
  change T (Quotient.mk _ ⟨φA.func x, ⟨x, hx, rfl⟩⟩) = imageQuotMk d hd φB U x hx
  change f ⟨φA.func x, ⟨x, hx, rfl⟩⟩ = imageQuotMk d hd φB U x hx
  apply Quotient.sound
  have hA : GaugeZeroRelated d (φA.func (repA ⟨φA.func x, ⟨x, hx, rfl⟩⟩))
      (φA.func x) := by
    have hval := hrepAval ⟨φA.func x, ⟨x, hx, rfl⟩⟩
    intro i
    rw [hval]
    exact (hd i).dist_self _
  have hR : (repA ⟨φA.func x, ⟨x, hx, rfl⟩⟩, x) ∈ RSim d φA U :=
    ⟨hrepAU _, hx, hA⟩
  exact (h hR).2.2
theorem quotient_factor_necessary
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φA φB : Operator X bot) (U : Set X)
    (hT : QuotientFactorExists d hd φA φB U) :
    RSim d φA U ⊆ RSim d φB U := by
  rcases hT with ⟨T, hT⟩
  intro p hp
  rcases p with ⟨x, y⟩
  rcases hp with ⟨hx, hy, hxy⟩
  refine ⟨hx, hy, ?_⟩
  have hq : imageQuotMk d hd φA U x hx = imageQuotMk d hd φA U y hy :=
    Quotient.sound hxy
  have h := congrArg T hq
  rw [hT x hx, hT y hy] at h
  exact Quotient.exact h
theorem quotient_factor_iff
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φA φB : Operator X bot) (U : Set X) :
    QuotientFactorExists d hd φA φB U ↔ RSim d φA U ⊆ RSim d φB U :=
  ⟨quotient_factor_necessary d hd φA φB U,
    quotient_factor_sufficient d hd φA φB U⟩
theorem quotient_factor_both_iff
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φA φB : Operator X bot) (U : Set X) :
    (QuotientFactorExists d hd φA φB U ∧
      QuotientFactorExists d hd φB φA U) ↔
      RSim d φA U = RSim d φB U := by
  constructor
  · rintro ⟨hAB, hBA⟩
    exact le_antisymm (quotient_factor_necessary d hd φA φB U hAB)
      (quotient_factor_necessary d hd φB φA U hBA)
  · intro hEq
    exact ⟨quotient_factor_sufficient d hd φA φB U (le_of_eq hEq),
      quotient_factor_sufficient d hd φB φA U (le_of_eq hEq.symm)⟩
theorem req_subset_rsim
    (d : I → X → X → ENNReal) (hself : ∀ i x, d i x x = 0)
    (φ : Operator X bot) (U : Set X) :
    REq φ U ⊆ RSim d φ U := by
  intro p hp
  rcases p with ⟨x, y⟩
  rcases hp with ⟨hx, hy, hxy⟩
  refine ⟨hx, hy, ?_⟩
  intro i
  rw [hxy]
  exact hself i (φ.func y)
theorem rsim_subset_req_of_separates
    (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X)
    (hsep : SeparatesOn d (φ.func '' U)) :
    RSim d φ U ⊆ REq φ U := by
  intro p hp
  rcases p with ⟨x, y⟩
  rcases hp with ⟨hx, hy, hzero⟩
  exact ⟨hx, hy, hsep (φ.func x) ⟨x, hx, rfl⟩ (φ.func y) ⟨y, hy, rfl⟩ hzero⟩
theorem quotient_point_factor_iff_of_separating
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φA φB : Operator X bot) (U : Set X)
    (hsepA : SeparatesOn d (φA.func '' U))
    (hsepB : SeparatesOn d (φB.func '' U)) :
    QuotientFactorExists d hd φA φB U ↔ PointFactorExists φA φB U := by
  constructor
  · intro hq
    apply point_factor_sufficient
    intro p hp
    have hR : RSim d φA U ⊆ RSim d φB U :=
      (quotient_factor_iff d hd φA φB U).mp hq
    have hzA : GaugeZeroRelated d (φA.func p.1) (φA.func p.2) := by
      rw [hp.2.2]
      intro i; exact (hd i).dist_self _
    have hzB := hR ⟨hp.1, hp.2.1, hzA⟩
    exact ⟨hp.1, hp.2.1,
      hsepB (φB.func p.1) ⟨p.1, hp.1, rfl⟩ (φB.func p.2) ⟨p.2, hp.2.1, rfl⟩ hzB.2.2⟩
  · intro hp
    apply (quotient_factor_iff d hd φA φB U).mpr
    intro q hq
    have hEq : REq φA U ⊆ REq φB U := (point_factor_iff φA φB U).mp hp
    have hzA : GaugeZeroRelated d (φA.func q.1) (φA.func q.2) := hq.2.2
    have heqA := hsepA (φA.func q.1) ⟨q.1, hq.1, rfl⟩
      (φA.func q.2) ⟨q.2, hq.2.1, rfl⟩ hzA
    have hpA : (q.1, q.2) ∈ REq φA U := ⟨hq.1, hq.2.1, heqA⟩
    have heqB := hEq hpA
    refine ⟨hq.1, hq.2.1, ?_⟩
    intro i
    rw [heqB.2.2]
    exact (hd i).dist_self _
theorem quotient_point_factor_both_iff_of_separating
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φA φB : Operator X bot) (U : Set X)
    (hsepA : SeparatesOn d (φA.func '' U))
    (hsepB : SeparatesOn d (φB.func '' U)) :
    (QuotientFactorExists d hd φA φB U ∧
      QuotientFactorExists d hd φB φA U) ↔
    (PointFactorExists φA φB U ∧ PointFactorExists φB φA U) := by
  constructor
  · rintro ⟨hAB, hBA⟩
    exact ⟨(quotient_point_factor_iff_of_separating d hd φA φB U hsepA hsepB).mp hAB,
      (quotient_point_factor_iff_of_separating d hd φB φA U hsepB hsepA).mp hBA⟩
  · rintro ⟨hAB, hBA⟩
    exact ⟨(quotient_point_factor_iff_of_separating d hd φA φB U hsepA hsepB).mpr hAB,
      (quotient_point_factor_iff_of_separating d hd φB φA U hsepB hsepA).mpr hBA⟩
theorem fiberPreorder_refl
    (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) :
    FiberPreorder d φ φ U := fun _ h => h
theorem fiberPreorder_trans
    (d : I → X → X → ENNReal) {φA φB φC : Operator X bot} {U : Set X}
    (hAB : FiberPreorder d φA φB U) (hBC : FiberPreorder d φB φC U) :
    FiberPreorder d φA φC U := fun p hp => hBC (hAB hp)
theorem fiberPreorder_chain
    (d : I → X → X → ENNReal) (φ : ℕ → Operator X bot) (U : Set X) (m : ℕ)
    (hstep : ∀ r < m, FiberPreorder d (φ r) (φ (r + 1)) U) :
    ∀ a b : ℕ, a ≤ b → b ≤ m → FiberPreorder d (φ a) (φ b) U := by
  intro a b hab
  induction b with
  | zero =>
      intro hb
      have : a = 0 := Nat.eq_zero_of_le_zero hab
      subst a
      exact fun _ hp => hp
  | succ b ih =>
      intro hb
      rcases Nat.eq_or_lt_of_le hab with rfl | hlt
      · exact fun _ hp => hp
      · have hab' : a ≤ b := Nat.le_of_lt_succ hlt
        have hb' : b ≤ m := Nat.le_of_succ_le hb
        have hbm : b < m := Nat.lt_of_succ_le hb
        exact fiberPreorder_trans d (ih hab' hb') (hstep b hbm)
theorem fiberPreorder_chain_strict
    (d : I → X → X → ENNReal) (φ : ℕ → Operator X bot) (U : Set X) (m r : ℕ)
    (hstep : ∀ k < m, FiberPreorder d (φ k) (φ (k + 1)) U)
    (hr : r < m)
    (hstrict : ¬ RSim d (φ (r + 1)) U ⊆ RSim d (φ r) U) :
    RSim d (φ 0) U ⊆ RSim d (φ m) U ∧
      ¬ RSim d (φ m) U ⊆ RSim d (φ 0) U ∧
      ∃ p : X × X, p ∈ RSim d (φ m) U ∧ p ∉ RSim d (φ 0) U := by
  have h0m : FiberPreorder d (φ 0) (φ m) U :=
    fiberPreorder_chain d φ U m hstep 0 m (Nat.zero_le m) (Nat.le_refl m)
  have hr1m : FiberPreorder d (φ (r + 1)) (φ m) U :=
    fiberPreorder_chain d φ U m hstep (r + 1) m (Nat.succ_le_of_lt hr) (Nat.le_refl m)
  have h0r : FiberPreorder d (φ 0) (φ r) U :=
    fiberPreorder_chain d φ U m hstep 0 r (Nat.zero_le r) (Nat.le_of_lt hr)
  have hnot : ¬ RSim d (φ m) U ⊆ RSim d (φ 0) U := by
    intro hrev
    apply hstrict
    intro p hp
    exact h0r (hrev (hr1m hp))
  rcases Set.not_subset.mp hnot with ⟨p, hpm, hp0⟩
  exact ⟨h0m, hnot, p, hpm, hp0⟩
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set
variable {X : Type} {I : Type} {bot : X}
theorem fiber_eq_U_of_subset_const
    (d : I → X → X → ENNReal) (φ : Operator X bot) (J : Set I) (U : Set X)
    (hJ : J ⊆ Iconst d φ U) {y : X} (hy : y ∈ U) :
    Fiber d φ J (φ.func y) U = U := by
  ext x
  constructor
  · intro hx; exact hx.1
  · intro hx
    refine ⟨hx, ?_⟩
    intro j hj
    exact hJ hj x hx y hy
theorem pointwiseZeroRadiusJ_eq_top_of_const
    (d : I → X → X → ENNReal) (φ : Operator X bot) (i : I) (J : Set I)
    (U : Set X) (hJ : J ⊆ Iconst d φ U) {y : X} (hy : y ∈ U) :
    pointwiseZeroRadiusJ d φ i J y U = ⊤ := by
  rw [pointwiseZeroRadiusJ, pointwiseRadius_eq_top_iff]
  intro r hr0 hrtop
  refine ⟨hr0, hrtop, ?_⟩
  intro x hx _
  intro j hj
  exact hJ hj x hx y hy
theorem unifiedZeroRadiusJ_eq_top_of_const
    (d : I → X → X → ENNReal) (φ : Operator X bot) (i : I) (J : Set I)
    (U : Set X) (hU : U.Nonempty) (hJ : J ⊆ Iconst d φ U) :
    unifiedZeroRadiusJ d φ i J U = ⊤ := by
  apply le_antisymm le_top
  apply le_iInf
  intro y
  change ⊤ ≤ pointwiseZeroRadiusJ d φ i J y.1 U
  rw [pointwiseZeroRadiusJ_eq_top_of_const d φ i J U hJ y.2]
theorem fiber_id_component_target
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (U : Set X) (y : X) (hy : y ∈ U) (i : I)
    (hi : i ∈ Iid d φ U) :
    Fiber d φ ({i} : Set I) (φ.func y) U = {x | x ∈ U ∧ d i x y = 0} :=
  fiber_id_component d hd φ U y hy i hi
theorem pointwiseRadius_ge_of_ball_subset
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (U : Set X) (y : X) (hy : y ∈ U) (i : I)
    (hi : i ∈ Iid d φ U) {r0 : ENNReal}
    (hr0pos : 0 < r0) (hr0top : r0 ≠ ⊤)
    (hball : ∀ x ∈ U, d i x y < r0 → d i x y = 0) :
    r0 ≤ pointwiseZeroRadius d φ i i y U := by
  apply le_pointwiseRadius_of_legal
  refine ⟨hr0pos, hr0top, ?_⟩
  intro x hx hlt
  have hxy : d i x y = 0 := hball x hx hlt
  have hiso := id_component_isometry d hd φ U i hi x hx y hy
  rw [hiso, hxy]
theorem pointwiseZeroRadiusJ_eq_finset_inf
    [Fintype I] (d : I → X → X → ENNReal) (φ : Operator X bot) (i : I)
    (J : Finset I) (hJ : J.Nonempty) (y : X) (U : Set X) :
    pointwiseZeroRadiusJ d φ i (J : Set I) y U =
      J.inf' hJ (fun j => pointwiseZeroRadius d φ i j y U) := by
  apply le_antisymm
  · apply Finset.le_inf' hJ
    intro j hj
    apply iSup_le
    intro r
    apply le_pointwiseRadius_of_legal
    refine ⟨r.2.1, r.2.2.1, ?_⟩
    intro x hx hlt
    exact r.2.2.2 x hx hlt j hj
  · apply le_of_forall_lt
    intro c hc
    have hmpos : 0 < J.inf' hJ (fun j => pointwiseZeroRadius d φ i j y U) :=
      lt_of_le_of_lt (zero_le c) hc
    obtain ⟨dmid, hcd, hdm⟩ := exists_between hc
    have hdpos : 0 < dmid := lt_of_le_of_lt (zero_le c) hcd
    have hlegal : LegalRadius (d i) (fun a b => ∀ j ∈ (J : Set I), d j a b = 0)
        φ y U dmid := by
      refine ⟨hdpos, ?_, ?_⟩
      · by_contra htop
        have : (⊤ : ENNReal) < J.inf' hJ (fun j => pointwiseZeroRadius d φ i j y U) := by
          simpa [htop] using hdm
        exact not_top_lt this
      · intro x hx hlt
        intro j hj
        have hltj : dmid < pointwiseZeroRadius d φ i j y U :=
          lt_of_lt_of_le hdm (Finset.inf'_le (fun j => pointwiseZeroRadius d φ i j y U) hj)
        rcases (lt_iSup_iff.mp hltj) with ⟨s, hslt⟩
        have hslegal : LegalRadius (d i) (fun a b => d j a b = 0) φ y U s.1 := s.2
        have hmidlegal : LegalRadius (d i) (fun a b => d j a b = 0) φ y U dmid :=
          legalRadius_mono hdpos (le_of_lt hslt) hslegal
        exact hmidlegal.2.2 x hx hlt
    have hle : dmid ≤ pointwiseZeroRadiusJ d φ i (J : Set I) y U :=
      le_pointwiseRadius_of_legal hlegal
    exact lt_of_lt_of_le hcd hle
theorem unifiedZeroRadiusJ_eq_finset_inf
    [Fintype I] (d : I → X → X → ENNReal) (φ : Operator X bot) (i : I)
    (J : Finset I) (hJ : J.Nonempty) (U : Set X) (hU : U.Nonempty) :
    unifiedZeroRadiusJ d φ i (J : Set I) U =
      J.inf' hJ (fun j => zeroingMatrix d φ U j i) := by
  unfold unifiedZeroRadiusJ zeroingMatrix unifiedRadius
  apply le_antisymm
  · apply Finset.le_inf' hJ
    intro j hj
    apply le_iInf
    intro y
    calc
      (⨅ y : {y : X // y ∈ U},
          pointwiseRadius (d i) (fun a b => ∀ j ∈ (J : Set I), d j a b = 0) φ y.1 U)
          ≤ pointwiseRadius (d i) (fun a b => ∀ j ∈ (J : Set I), d j a b = 0) φ y.1 U :=
            iInf_le _ y
      _ = J.inf' hJ (fun j => pointwiseZeroRadius d φ i j y.1 U) := by
            exact pointwiseZeroRadiusJ_eq_finset_inf d φ i J hJ y.1 U
      _ ≤ pointwiseZeroRadius d φ i j y.1 U :=
            Finset.inf'_le (fun j => pointwiseZeroRadius d φ i j y.1 U) hj
  · apply le_iInf
    intro y
    change (J.inf' hJ (fun j =>
        ⨅ y : {y : X // y ∈ U}, pointwiseZeroRadius d φ i j y.1 U)) ≤
      pointwiseZeroRadiusJ d φ i (J : Set I) y.1 U
    rw [pointwiseZeroRadiusJ_eq_finset_inf d φ i J hJ y.1 U]
    apply Finset.le_inf' hJ
    intro j hj
    calc
      (J.inf' hJ (fun j =>
          ⨅ y : {y : X // y ∈ U}, pointwiseZeroRadius d φ i j y.1 U))
          ≤ (⨅ y : {y : X // y ∈ U}, pointwiseZeroRadius d φ i j y.1 U) :=
            Finset.inf'_le (fun j =>
              ⨅ y : {y : X // y ∈ U}, pointwiseZeroRadius d φ i j y.1 U) hj
      _ ≤ pointwiseZeroRadius d φ i j y.1 U := iInf_le _ y
theorem unifiedZeroRadiusJ_antitone_output
    (d : I → X → X → ENNReal) (φ : Operator X bot) (i : I)
    {J K : Set I} (hJK : J ⊆ K) (A : Set X) :
    unifiedZeroRadiusJ d φ i K A ≤ unifiedZeroRadiusJ d φ i J A := by
  unfold unifiedZeroRadiusJ unifiedRadius
  apply iInf_mono
  intro y
  apply iSup_le
  intro r
  apply le_pointwiseRadius_of_legal
  exact ⟨r.2.1, r.2.2.1, fun x hx hlt j hj => r.2.2.2 x hx hlt j (hJK hj)⟩
theorem fiber_member_output_zero
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (U : Set X) (i j : I) {y y' : X}
    (hy' : y' ∈ Fiber d φ ({j} : Set I) (φ.func y) U) :
    d j (φ.func y) (φ.func y') = 0 := by
  have h := hy'.2 j (by simp)
  rw [(hd j).symm]
  exact h
theorem pointwise_radius_truncation
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (U : Set X) (i j : I) {y y' : X}
    (hy' : y' ∈ U)
    (hlt : d i y y' < pointwiseZeroRadius d φ i j y U) :
    d j (φ.func y) (φ.func y') = 0 := by
  unfold pointwiseZeroRadius pointwiseRadius at hlt
  rcases lt_iSup_iff.mp hlt with ⟨r, hrlt⟩
  have hsym : d i y' y < r.1 := by
    rwa [(hd i).symm] at hrlt
  have hout := r.2.2.2 y' hy' hsym
  change d j (φ.func y') (φ.func y) = 0 at hout
  rwa [(hd j).symm] at hout
theorem composite_fiber_truncation
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ1 φ2 : Operator X bot) (U : Set X) (i j : I) {x x' : X}
    (hx : φ1.func x ∈ U) (hx' : φ1.func x' ∈ U)
    (hmem : φ1.func x' ∈ Fiber d φ2 ({j} : Set I) (φ2.func (φ1.func x)) U) :
    d j ((φ2 * φ1).func x) ((φ2 * φ1).func x') = 0 := by
  exact fiber_member_output_zero d hd φ2 U i j hmem
theorem unified_comp_radius_preserve
    (d : I → X → X → ENNReal) (φ1 φ2 : Operator X bot) (i j l : I) (U : Set X)
    (hpres : ∀ y ∈ φ1.func '' U, ∀ y' ∈ φ1.func '' U,
      d l y y' = 0 → d j (φ2.func y) (φ2.func y') = 0) :
    unifiedRadius (d i) (fun a b => d l a b = 0) φ1 U U ≤
      unifiedRadius (d i) (fun a b => d j a b = 0) (φ2 * φ1) U U := by
  unfold unifiedRadius
  apply le_iInf
  intro y
  refine le_trans (iInf_le (fun y : {y : X // y ∈ U} =>
    pointwiseRadius (d i) (fun a b => d l a b = 0) φ1 y.1 U) y) ?_
  apply iSup_le
  intro r
  apply le_pointwiseRadius_of_legal
  refine ⟨r.2.1, r.2.2.1, ?_⟩
  intro x hx hlt
  have hφx : φ1.func x ∈ φ1.func '' U := ⟨x, hx, rfl⟩
  have hφy : φ1.func y.1 ∈ φ1.func '' U := ⟨y.1, y.2, rfl⟩
  have hz : d l (φ1.func x) (φ1.func y.1) = 0 := r.2.2.2 x hx hlt
  exact hpres _ hφx _ hφy hz
theorem unified_comp_radius_lip_pullback
    (d : I → X → X → ENNReal) (φ1 φ2 : Operator X bot) (i j l : I) (U : Set X)
    (L : ENNReal) (hLpos : 0 < L) (hLtop : L ≠ ⊤)
    (hLip : ∀ x ∈ U, ∀ y ∈ U,
      d l (φ1.func x) (φ1.func y) ≤ L * d i x y) :
    unifiedRadius (d l) (fun a b => d j a b = 0) φ2 (φ1.func '' U) (φ1.func '' U) / L ≤
      unifiedRadius (d i) (fun a b => d j a b = 0) (φ2 * φ1) U U := by
  unfold unifiedRadius
  let p2 : X → ENNReal := fun z =>
    pointwiseRadius (d l) (fun a b => d j a b = 0) φ2 z (φ1.func '' U)
  let pc : X → ENNReal := fun y =>
    pointwiseRadius (d i) (fun a b => d j a b = 0) (φ2 * φ1) y U
  have hpoint : ∀ y ∈ U, p2 (φ1.func y) / L ≤ pc y := by
    intro y hy
    rw [ENNReal.div_le_iff (ne_of_gt hLpos) hLtop]
    apply iSup_le
    intro r
    have hrlegal : LegalRadius (d i) (fun a b => d j a b = 0) (φ2 * φ1) y U (r.1 / L) := by
      refine ⟨ENNReal.div_pos (ne_of_gt r.2.1) hLtop,
        ENNReal.div_ne_top r.2.2.1 (ne_of_gt hLpos), ?_⟩
      intro x hx hlt
      have hLx : L * d i x y < r.1 := by
        have := (ENNReal.mul_lt_of_lt_div hlt : d i x y * L < r.1)
        rwa [mul_comm] at this
      have hstep : d l (φ1.func x) (φ1.func y) < r.1 :=
        lt_of_le_of_lt (hLip x hx y hy) hLx
      exact r.2.2.2 (φ1.func x) ⟨x, hx, rfl⟩ hstep
    have hle : r.1 / L ≤ pc y := le_pointwiseRadius_of_legal hrlegal
    calc
      r.1 = (r.1 / L) * L := by rw [ENNReal.div_mul_cancel (ne_of_gt hLpos) hLtop]
      _ ≤ pc y * L := by gcongr
  have h1 : (⨅ z : {z : X // z ∈ φ1.func '' U}, p2 z.1) / L ≤
      (⨅ y : {y : X // y ∈ U}, p2 (φ1.func y.1) / L) := by
    apply le_iInf
    intro y
    exact ENNReal.div_le_div_right
      (iInf_le (fun z : {z : X // z ∈ φ1.func '' U} => p2 z.1)
        ⟨φ1.func y.1, ⟨y.1, y.2, rfl⟩⟩) L
  have h2 : (⨅ y : {y : X // y ∈ U}, p2 (φ1.func y.1) / L) ≤
      (⨅ y : {y : X // y ∈ U}, pc y.1) := by
    apply iInf_mono
    intro y
    exact hpoint y.1 y.2
  exact le_trans h1 h2
structure InputScaleFamily (X : Type) (I : Type) where
  scale : I → Set X → ENNReal
  mono : ∀ i : I, ∀ {A B : Set X}, A ⊆ B → scale i A ≤ scale i B
noncomputable def diameterScale (d : I → X → X → ENNReal) (i : I) (A : Set X) : ENNReal :=
  ⨆ x : {x : X // x ∈ A}, ⨆ y : {y : X // y ∈ A}, d i x.1 y.1
theorem diameterScale_mono (d : I → X → X → ENNReal) (i : I) {A B : Set X}
    (hAB : A ⊆ B) :
    diameterScale d i A ≤ diameterScale d i B := by
  apply iSup_le
  intro x
  apply iSup_le
  intro y
  exact le_iSup_of_le ⟨x.1, hAB x.2⟩ (le_iSup_of_le ⟨y.1, hAB y.2⟩ le_rfl)
theorem inputScaleFamily_mono {σ : InputScaleFamily X I} (i : I) {A B : Set X}
    (hAB : A ⊆ B) : σ.scale i A ≤ σ.scale i B := σ.mono i hAB
noncomputable def thresholdType (σ : InputScaleFamily X I) (τσ τN : ENNReal)
    (d : I → X → X → ENNReal) (φ : Operator X bot) (A : Set X) (i j : I) :
    Bool × Bool :=
  (decide (σ.scale i A < τσ), decide (τN ≤ zeroingMatrix d φ A j i))
theorem thresholdType_exhaustive (σ : InputScaleFamily X I) (τσ τN : ENNReal)
    (d : I → X → X → ENNReal) (φ : Operator X bot) (A : Set X) (i j : I) :
    thresholdType σ τσ τN d φ A i j = (true, true) ∨
    thresholdType σ τσ τN d φ A i j = (true, false) ∨
    thresholdType σ τσ τN d φ A i j = (false, true) ∨
    thresholdType σ τσ τN d φ A i j = (false, false) := by
  unfold thresholdType
  by_cases h1 : σ.scale i A < τσ <;> by_cases h2 : τN ≤ zeroingMatrix d φ A j i <;>
    simp [h1, h2]
theorem thresholdType_fst_mono (σ : InputScaleFamily X I)
    {τσ τσ' τN : ENNReal} (hτ : τσ ≤ τσ')
    (d : I → X → X → ENNReal) (φ : Operator X bot) (A : Set X) (i j : I)
    (h : (thresholdType σ τσ τN d φ A i j).1 = true) :
    (thresholdType σ τσ' τN d φ A i j).1 = true := by
  unfold thresholdType at h ⊢
  simp only [Prod.fst] at h ⊢
  rw [decide_eq_true_eq] at h ⊢
  exact lt_of_lt_of_le h hτ
theorem thresholdType_snd_antitone (σ : InputScaleFamily X I)
    {τN τN' τσ : ENNReal} (hτ : τN ≤ τN')
    (d : I → X → X → ENNReal) (φ : Operator X bot) (A : Set X) (i j : I)
    (h : (thresholdType σ τσ τN' d φ A i j).2 = true) :
    (thresholdType σ τσ τN d φ A i j).2 = true := by
  unfold thresholdType at h ⊢
  simp only [Prod.snd] at h ⊢
  rw [decide_eq_true_eq] at h ⊢
  exact le_trans hτ h
theorem scale_threshold_domain_mono (σ : InputScaleFamily X I) (i : I)
    {B A : Set X} (hBA : B ⊆ A) {τσ : ENNReal}
    (h : σ.scale i A < τσ) : σ.scale i B < τσ :=
  lt_of_le_of_lt (inputScaleFamily_mono i hBA) h
theorem pointwiseRadius_domain_antitone
    (din : X → X → ENNReal) (P : X → X → Prop) (φ : Operator X bot)
    {B A : Set X} (hBA : B ⊆ A) {y : X} (hy : y ∈ B) :
    pointwiseRadius din P φ y A ≤ pointwiseRadius din P φ y B := by
  apply iSup_le
  intro r
  apply le_pointwiseRadius_of_legal
  refine ⟨r.2.1, r.2.2.1, ?_⟩
  intro x hx hlt
  exact r.2.2.2 x (hBA hx) hlt
theorem unifiedRadius_domain_antitone
    (din : X → X → ENNReal) (P : X → X → Prop) (φ : Operator X bot)
    {B A : Set X} (hBA : B ⊆ A) (hB : B.Nonempty) :
    unifiedRadius din P φ A A ≤ unifiedRadius din P φ B B := by
  unfold unifiedRadius
  have h1 : (⨅ y : {y : X // y ∈ A}, pointwiseRadius din P φ y.1 A) ≤
      (⨅ y : {y : X // y ∈ B}, pointwiseRadius din P φ y.1 A) := by
    apply le_iInf
    intro y
    exact iInf_le _ (⟨y.1, hBA y.2⟩ : {y : X // y ∈ A})
  have h2 : (⨅ y : {y : X // y ∈ B}, pointwiseRadius din P φ y.1 A) ≤
      (⨅ y : {y : X // y ∈ B}, pointwiseRadius din P φ y.1 B) := by
    apply iInf_mono
    intro y
    exact pointwiseRadius_domain_antitone din P φ hBA y.2
  exact le_trans h1 h2
theorem below_unified_radius_output_zero
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (A : Set X) (i j : I) {x y : X}
    (hx : x ∈ A) (hy : y ∈ A)
    (hlt : d i x y < zeroingMatrix d φ A j i) :
    d j (φ.func x) (φ.func y) = 0 := by
  unfold zeroingMatrix unifiedRadius at hlt
  have hltp : d i x y < pointwiseRadius (d i) (fun a b => d j a b = 0) φ x A :=
    lt_of_lt_of_le hlt (iInf_le _ (⟨x, hx⟩ : {x : X // x ∈ A}))
  unfold pointwiseRadius at hltp
  rcases lt_iSup_iff.mp hltp with ⟨r, hrlt⟩
  have hsym : d i y x < r.1 := by
    rwa [(hd i).symm] at hrlt
  have hout := r.2.2.2 y hy hsym
  change d j (φ.func y) (φ.func x) = 0 at hout
  rwa [(hd j).symm] at hout
theorem output_positive_input_ge_unified_radius
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (A : Set X) (i j : I) {x y : X}
    (hx : x ∈ A) (hy : y ∈ A)
    (hpos : 0 < d j (φ.func x) (φ.func y)) :
    zeroingMatrix d φ A j i ≤ d i x y := by
  by_contra hnot
  have hlt : d i x y < zeroingMatrix d φ A j i := lt_of_not_ge hnot
  have hzero := below_unified_radius_output_zero d hd φ A i j hx hy hlt
  exact (ne_of_gt hpos) hzero
theorem unified_radius_deficiency_witness
    (d : I → X → X → ENNReal) (φ : Operator X bot) (A : Set X) (i j : I)
    {τN α : ENNReal} (hbelow : zeroingMatrix d φ A j i < τN)
    (hα : zeroingMatrix d φ A j i < α) (hατ : α < τN) :
    ∃ x ∈ A, ∃ y ∈ A, d i x y < α ∧
      ∃ ε : ENNReal, 0 < ε ∧ ε ≠ ⊤ ∧ ε ≤ d j (φ.func x) (φ.func y) := by
  unfold zeroingMatrix unifiedRadius at hα
  rcases iInf_lt_iff.mp hα with ⟨y, hy⟩
  have hαpos : 0 < α := lt_of_le_of_lt (zero_le _) hα
  have hαtop : α ≠ ⊤ := ne_top_of_lt hατ
  have hnotball : ¬ ∀ x ∈ A, d i x y.1 < α →
      d j (φ.func x) (φ.func y.1) = 0 := by
    intro hall
    have hlegal : LegalRadius (d i) (fun a b => d j a b = 0) φ y.1 A α :=
      ⟨hαpos, hαtop, hall⟩
    exact (not_lt_of_ge (le_pointwiseRadius_of_legal hlegal)) hy
  push Not at hnotball
  rcases hnotball with ⟨x, hxA, hdist, hout⟩
  refine ⟨x, hxA, y.1, y.2, hdist, ?_⟩
  have houtpos : 0 < d j (φ.func x) (φ.func y.1) :=
    lt_of_le_of_ne (zero_le _) (Ne.symm hout)
  by_cases htop : d j (φ.func x) (φ.func y.1) = ⊤
  · exact ⟨1, zero_lt_one, ENNReal.one_ne_top, by simp [htop]⟩
  · exact ⟨d j (φ.func x) (φ.func y.1), houtpos, htop, le_rfl⟩
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set
variable {X : Type} {I : Type} {bot : X}
/-- Total boundedness on a set: every finite positive precision admits a finite
internal cover. -/
def TotallyBoundedOn (d : X → X → ENNReal) (U : Set X) : Prop :=
  ∀ ε : ENNReal, 0 < ε → ε ≠ ⊤ → covering_number d ε U ≠ ⊤
theorem covering_number_le_card_of_net {d : X → X → ENNReal} {ε : ENNReal}
    {U : Set X} {S : Finset X} (hS : InternalEpsilonNet d ε U S) :
    covering_number d ε U ≤ (S.card : ENNReal) := by
  unfold covering_number
  exact iInf_le_of_le S (iInf_le_of_le hS le_rfl)
theorem log2_ereal_mono {a b : ENNReal} (h : a ≤ b) :
    log2_ereal a ≤ log2_ereal b := by
  by_cases ha0 : a = 0
  · simp [log2_ereal, ha0]
  · by_cases hb0 : b = 0
    · have hab : a ≤ 0 := by simpa [hb0] using h
      exact False.elim (ha0 (le_antisymm hab (zero_le _)))
    · by_cases hbt : b = ⊤
      · simp [log2_ereal, ha0, hb0, hbt]
      · have hat : a ≠ ⊤ := ne_top_of_le_ne_top hbt h
        simp only [log2_ereal, if_neg ha0, if_neg hat, if_neg hb0, if_neg hbt]
        exact EReal.coe_le_coe
          (Real.logb_le_logb_of_le one_lt_two
            (ENNReal.toReal_pos ha0 hat) (ENNReal.toReal_mono hbt h))
theorem covering_number_eq_one_of_forall_zero
    (d : X → X → ENNReal) (U : Set X) (hU : U.Nonempty) (ε : ENNReal)
    (hε : 0 < ε) (hzero : ∀ x ∈ U, ∀ y ∈ U, d x y = 0) :
    covering_number d ε U = 1 := by
  apply le_antisymm
  · rcases hU with ⟨x0, hx0⟩
    have hnet : InternalEpsilonNet d ε U {x0} := by
      constructor
      · intro x hx
        have hx' : x = x0 := by simpa using hx
        simpa [hx'] using hx0
      · intro x hx
        refine ⟨x0, by simp, ?_⟩
        rw [hzero x hx x0 hx0]
        exact hε
    calc
      covering_number d ε U ≤ (({x0} : Finset X).card : ENNReal) :=
        covering_number_le_card_of_net hnet
      _ = 1 := by simp
  · exact one_le_covering_number_of_nonempty d ε U hU
theorem threshold_ball_subset_fiber
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (A : Set X) (i j : I) {τN : ENNReal}
    (hth : τN ≤ zeroingMatrix d φ A j i) :
    ∀ x ∈ A, ∀ y ∈ A, d i y x < τN →
      y ∈ Fiber d φ ({j} : Set I) (φ.func x) A := by
  intro x hx y hya hy
  refine ⟨hya, ?_⟩
  intro k hk
  simp only [Set.mem_singleton_iff] at hk
  subst k
  apply below_unified_radius_output_zero d hd φ A i j hya hx
  exact lt_of_lt_of_le hy hth
theorem covering_number_image_le_of_threshold
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (A : Set X) (i j : I) {τN : ENNReal}
    (hτpos : 0 < τN) (hth : τN ≤ zeroingMatrix d φ A j i)
    (B : Set X) (hBA : B ⊆ A) (ε : ENNReal) (hε : 0 < ε) :
    covering_number (d j) ε (φ.func '' B) ≤ covering_number (d i) τN B := by
  classical
  by_cases hfin : ∃ S : Finset X, InternalEpsilonNet (d i) τN B S
  · obtain ⟨S, hS, hcover, hmin⟩ :=
      covering_number_attained (d i) τN B hfin
    have hSimg : InternalEpsilonNet (d j) ε (φ.func '' B) (S.image φ.func) := by
      constructor
      · intro z hz
        rcases Finset.mem_image.mp hz with ⟨s, hs, rfl⟩
        exact ⟨s, hS.1 hs, rfl⟩
      · intro z hz
        rcases hz with ⟨a, ha, rfl⟩
        rcases hS.2 a ha with ⟨s, hs, hdist⟩
        refine ⟨φ.func s, Finset.mem_image.mpr ⟨s, hs, rfl⟩, ?_⟩
        have hsA : s ∈ A := hBA (hS.1 hs)
        have haA : a ∈ A := hBA ha
        have hfib := threshold_ball_subset_fiber d hd φ A i j hth s hsA a haA hdist
        have hout := hfib.2 j (by simp)
        exact lt_of_le_of_lt (le_of_eq hout) hε
    calc
      covering_number (d j) ε (φ.func '' B)
          ≤ ((S.image φ.func).card : ENNReal) := covering_number_le_card_of_net hSimg
      _ ≤ (S.card : ENNReal) := by exact_mod_cast Finset.card_image_le
      _ = covering_number (d i) τN B := hcover.symm
  · have htop : covering_number (d i) τN B = ⊤ :=
      (covering_number_eq_top_iff (d i) τN B).mpr hfin
    rw [htop]
    exact le_top
theorem entropy_image_le_of_threshold
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (A : Set X) (i j : I) {τN : ENNReal}
    (hτpos : 0 < τN) (hτtop : τN ≠ ⊤)
    (hth : τN ≤ zeroingMatrix d φ A j i)
    (B : Set X) (hBA : B ⊆ A) (hB : B.Nonempty) (ε : ENNReal) (hε : 0 < ε) :
    metric_entropy (d j) ε (φ.func '' B) ≤ metric_entropy (d i) τN B := by
  unfold metric_entropy
  exact log2_ereal_mono
    (covering_number_image_le_of_threshold d hd φ A i j hτpos hth B hBA ε hε)
theorem small_domain_zeroing_iff
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (A : Set X) (i j : I) {τσ τN : ENNReal}
    (hA : A.Nonempty) (hτpos : 0 < τN) (hτtop : τN ≠ ⊤)
    (hdiam : diameterScale d i A < τσ) (hτ : τσ ≤ τN) :
    τN ≤ zeroingMatrix d φ A j i ↔
      ∀ x ∈ A, ∀ y ∈ A, d j (φ.func x) (φ.func y) = 0 := by
  constructor
  · intro hth x hx y hy
    have hdiamxy : d i x y ≤ diameterScale d i A := by
      exact le_iSup_of_le (⟨x, hx⟩ : {x : X // x ∈ A})
        (le_iSup_of_le (⟨y, hy⟩ : {y : X // y ∈ A}) le_rfl)
    have hlt : d i x y < zeroingMatrix d φ A j i :=
      lt_of_le_of_lt hdiamxy (lt_of_lt_of_le hdiam (le_trans hτ hth))
    exact below_unified_radius_output_zero d hd φ A i j hx hy hlt
  · intro hzero
    have hmat_top : zeroingMatrix d φ A j i = ⊤ := by
      apply le_antisymm le_top
      apply le_iInf
      intro x
      change ⊤ ≤ pointwiseRadius (d i) (fun a b => d j a b = 0) φ x.1 A
      exact top_le_iff.mpr (pointwiseRadius_eq_top_iff.mpr (by
        intro r hr0 hrtop
        refine ⟨hr0, hrtop, ?_⟩
        intro y hy _
        exact hzero y hy x.1 x.2))
    rw [hmat_top]
    exact le_top
theorem small_domain_image_covering_eq_one
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (A : Set X) (i j : I) {τσ τN ε : ENNReal}
    (hA : A.Nonempty) (hτpos : 0 < τN) (hτtop : τN ≠ ⊤)
    (hdiam : diameterScale d i A < τσ) (hτ : τσ ≤ τN)
    (hth : τN ≤ zeroingMatrix d φ A j i) (hε : 0 < ε) :
    covering_number (d j) ε (φ.func '' A) = 1 := by
  have hzero : ∀ x ∈ A, ∀ y ∈ A, d j (φ.func x) (φ.func y) = 0 :=
    (small_domain_zeroing_iff d hd φ A i j hA hτpos hτtop hdiam hτ).mp hth
  apply covering_number_eq_one_of_forall_zero (d j) (φ.func '' A)
  · rcases hA with ⟨x, hx⟩
    exact ⟨φ.func x, ⟨x, hx, rfl⟩⟩
  · exact hε
  · intro u hu v hv
    rcases hu with ⟨x, hx, rfl⟩
    rcases hv with ⟨y, hy, rfl⟩
    exact hzero x hx y hy
theorem finite_set_covering_ne_top
    (d : X → X → ENNReal) (hself : ∀ x, d x x = 0)
    (U : Set X) (hUfin : U.Finite) {ε : ENNReal} (hε : 0 < ε) :
    covering_number d ε U ≠ ⊤ := by
  intro htop
  have hnet : InternalEpsilonNet d ε U hUfin.toFinset := by
    constructor
    · intro x hx
      exact hUfin.mem_toFinset.mp hx
    · intro x hx
      refine ⟨x, hUfin.mem_toFinset.mpr hx, ?_⟩
      rw [hself x]
      exact hε
  have hle := covering_number_le_card_of_net hnet
  rw [htop] at hle
  exact ENNReal.natCast_ne_top hUfin.toFinset.card (top_le_iff.mp hle)
theorem finite_set_metric_entropy_ne_top
    (d : X → X → ENNReal) (hself : ∀ x, d x x = 0)
    (U : Set X) (hUfin : U.Finite) {ε : ENNReal} (hε : 0 < ε) :
    metric_entropy d ε U ≠ ⊤ := by
  have htop := finite_set_covering_ne_top d hself U hUfin hε
  unfold metric_entropy
  by_cases h0 : covering_number d ε U = 0
  · simp [log2_ereal, h0]
  · simp [log2_ereal, h0, htop]
theorem metric_entropy_ne_bot_of_nonempty
    (d : X → X → ENNReal) (U : Set X) (hU : U.Nonempty) (ε : ENNReal) :
    metric_entropy d ε U ≠ ⊥ := by
  have hnonneg := metric_entropy_nonneg d ε U hU
  intro hbot
  have h : (0 : EReal) ≤ ⊥ := by simpa [hbot] using hnonneg
  exact (not_le_of_gt (EReal.bot_lt_coe 0)) h
noncomputable def erealSub (a b : EReal) : EReal :=
  if a = ⊤ then (if b = ⊤ then 0 else ⊤)
  else if a = ⊥ then (if b = ⊥ then 0 else ⊥)
  else if b = ⊤ then ⊥
  else if b = ⊥ then ⊤
  else ↑(a.toReal - b.toReal)
theorem erealSub_coe_coe (x y : ℝ) : erealSub ↑x ↑y = ↑(x - y) := by
  simp [erealSub]
theorem erealSub_self (a : EReal) : erealSub a a = 0 := by
  by_cases htop : a = ⊤
  · simp [erealSub, htop]
  · by_cases hbot : a = ⊥
    · simp [erealSub, hbot]
    · have hcoe : a = ↑a.toReal := (EReal.coe_toReal htop hbot).symm
      rw [hcoe]
      simp [erealSub]
theorem erealSub_eq_self_of_right_zero {a : EReal} (hbot : a ≠ ⊥) :
    erealSub a 0 = a := by
  by_cases htop : a = ⊤
  · simp [erealSub, htop]
  · have hcoe : a = ↑a.toReal := (EReal.coe_toReal htop hbot).symm
    rw [hcoe]
    norm_num [erealSub]
noncomputable def mappingEntropyDiff
    (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X)
    (Jin Jout : Set I) (ε : ENNReal) : EReal :=
  erealSub (subfamily_metric_entropy d Jin ε U)
    (subfamily_metric_entropy d Jout ε (φ.func '' U))
def MappingEntropyDiffWellDefined
    (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X)
    (Jin Jout : Set I) (ε : ENNReal) : Prop :=
  subfamily_metric_entropy d Jin ε U ≠ ⊤ ∨
    subfamily_metric_entropy d Jout ε (φ.func '' U) ≠ ⊤
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set
variable {X : Type} {I : Type} {bot : X}
theorem subfamily_pseudometric_eq_zero_of_const
    (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X)
    (J : Set I) (hJ : J ⊆ Iconst d φ U) :
    ∀ x ∈ φ.func '' U, ∀ y ∈ φ.func '' U,
      subfamily_pseudometric d J x y = 0 := by
  rintro x ⟨a, ha, rfl⟩ y ⟨b, hb, rfl⟩
  rw [subfamily_pseudometric, ENNReal.iSup_eq_zero]
  intro j
  exact hJ j.2 a ha b hb
theorem subfamily_metric_entropy_const
    (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X)
    (J : Set I) (hJne : J.Nonempty) (hJ : J ⊆ Iconst d φ U)
    (hU : U.Nonempty) (ε : ENNReal) (hε : 0 < ε) :
    covering_number (subfamily_pseudometric d J) ε (φ.func '' U) = 1 ∧
      subfamily_metric_entropy d J ε (φ.func '' U) = 0 := by
  have hne : (φ.func '' U).Nonempty := by
    rcases hU with ⟨x, hx⟩
    exact ⟨φ.func x, ⟨x, hx, rfl⟩⟩
  have hcover : covering_number (subfamily_pseudometric d J) ε (φ.func '' U) = 1 :=
    covering_number_eq_one_of_forall_zero _ _ hne ε hε
      (subfamily_pseudometric_eq_zero_of_const d φ U J hJ)
  refine ⟨hcover, ?_⟩
  unfold subfamily_metric_entropy
  simp [hcover, log2_ereal]
theorem const_channel_entropy_diff
    (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X)
    (Jin Jout : Set I) (hJoutne : Jout.Nonempty)
    (hJout : Jout ⊆ Iconst d φ U) (hU : U.Nonempty)
    (ε : ENNReal) (hε : 0 < ε) :
    covering_number (subfamily_pseudometric d Jout) ε (φ.func '' U) = 1 ∧
      subfamily_metric_entropy d Jout ε (φ.func '' U) = 0 ∧
      mappingEntropyDiff d φ U Jin Jout ε =
        subfamily_metric_entropy d Jin ε U := by
  obtain ⟨hc, he⟩ := subfamily_metric_entropy_const d φ U Jout hJoutne hJout hU ε hε
  refine ⟨hc, he, ?_⟩
  have hnonbot : subfamily_metric_entropy d Jin ε U ≠ ⊥ :=
    metric_entropy_ne_bot_of_nonempty (subfamily_pseudometric d Jin) U hU ε
  unfold mappingEntropyDiff
  rw [he]
  exact erealSub_eq_self_of_right_zero hnonbot
theorem image_net_of_isometry [DecidableEq X]
    (d : X → X → ENNReal) (φ : Operator X bot) (U : Set X) {ε : ENNReal}
    (hiso : ∀ x ∈ U, ∀ y ∈ U, d (φ.func x) (φ.func y) = d x y)
    {S : Finset X} (hS : InternalEpsilonNet d ε U S) :
    InternalEpsilonNet d ε (φ.func '' U) (S.image φ.func) := by
  classical
  constructor
  · intro z hz
    rcases Finset.mem_image.mp hz with ⟨s, hs, rfl⟩
    exact ⟨s, hS.1 hs, rfl⟩
  · intro z hz
    rcases hz with ⟨x, hx, rfl⟩
    rcases hS.2 x hx with ⟨s, hs, hdist⟩
    refine ⟨φ.func s, Finset.mem_image.mpr ⟨s, hs, rfl⟩, ?_⟩
    rwa [hiso x hx s (hS.1 hs)]
theorem preimage_net_of_isometry
    (d : X → X → ENNReal) (φ : Operator X bot) (U : Set X) {ε : ENNReal}
    (hiso : ∀ x ∈ U, ∀ y ∈ U, d (φ.func x) (φ.func y) = d x y)
    {T : Finset X} (hT : InternalEpsilonNet d ε (φ.func '' U) T) :
    ∃ S : Finset X, InternalEpsilonNet d ε U S ∧ S.card ≤ T.card := by
  classical
  let rep : {t : X // t ∈ T} → X := fun t =>
    Classical.choose (hT.1 t.2)
  have hrepU : ∀ t : {t : X // t ∈ T}, rep t ∈ U := fun t =>
    (Classical.choose_spec (hT.1 t.2)).1
  have hrepval : ∀ t : {t : X // t ∈ T}, φ.func (rep t) = t.1 := fun t =>
    (Classical.choose_spec (hT.1 t.2)).2
  let S : Finset X := T.attach.image rep
  refine ⟨S, ?_, ?_⟩
  · constructor
    · intro x hx
      rcases Finset.mem_image.mp hx with ⟨t, _, rfl⟩
      exact hrepU t
    · intro x hx
      rcases hT.2 (φ.func x) ⟨x, hx, rfl⟩ with ⟨t, ht, hdist⟩
      refine ⟨rep ⟨t, ht⟩, ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨⟨t, ht⟩, Finset.mem_attach _ _, rfl⟩
      · have hval : φ.func (rep ⟨t, ht⟩) = t := hrepval ⟨t, ht⟩
        have hdist' : d (φ.func x) (φ.func (rep ⟨t, ht⟩)) < ε := by
          simpa [hval] using hdist
        simpa [hiso x hx (rep ⟨t, ht⟩) (hrepU ⟨t, ht⟩)] using hdist' 
  · calc
      S.card ≤ T.attach.card := Finset.card_image_le
      _ = T.card := Finset.card_attach
theorem covering_number_image_eq_of_isometry
    (d : X → X → ENNReal) (φ : Operator X bot) (U : Set X) (ε : ENNReal)
    (hiso : ∀ x ∈ U, ∀ y ∈ U, d (φ.func x) (φ.func y) = d x y) :
    covering_number d ε (φ.func '' U) = covering_number d ε U := by
  classical
  apply le_antisymm
  · by_cases hfin : ∃ S : Finset X, InternalEpsilonNet d ε U S
    · obtain ⟨S, hS, hcover, _⟩ := covering_number_attained d ε U hfin
      calc
        covering_number d ε (φ.func '' U) ≤ (S.image φ.func).card :=
          covering_number_le_card_of_net (image_net_of_isometry d φ U hiso hS)
        _ ≤ (S.card : ENNReal) := by exact_mod_cast Finset.card_image_le
        _ = covering_number d ε U := hcover.symm
    · rw [(covering_number_eq_top_iff d ε U).mpr hfin]
      exact le_top
  · by_cases hfin : ∃ T : Finset X, InternalEpsilonNet d ε (φ.func '' U) T
    · obtain ⟨T, hT, hcover, _⟩ := covering_number_attained d ε (φ.func '' U) hfin
      obtain ⟨S, hS, hcard⟩ := preimage_net_of_isometry d φ U hiso hT
      calc
        covering_number d ε U ≤ S.card := covering_number_le_card_of_net hS
        _ ≤ (T.card : ENNReal) := by exact_mod_cast hcard
        _ = covering_number d ε (φ.func '' U) := hcover.symm
    · rw [(covering_number_eq_top_iff d ε (φ.func '' U)).mpr hfin]
      exact le_top
theorem id_channel_covering_eq
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (U : Set X) (j : I) (hj : j ∈ Iid d φ U)
    (ε : ENNReal) :
    covering_number (d j) ε (φ.func '' U) = covering_number (d j) ε U := by
  classical
  exact covering_number_image_eq_of_isometry (d j) φ U ε
    (id_component_isometry d hd φ U j hj)
theorem id_channel_entropy_eq
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (U : Set X) (j : I) (hj : j ∈ Iid d φ U)
    (ε : ENNReal) :
    subfamily_metric_entropy d ({j} : Set I) ε (φ.func '' U) =
      subfamily_metric_entropy d ({j} : Set I) ε U := by
  rw [subfamily_metric_entropy_singleton, subfamily_metric_entropy_singleton]
  unfold metric_entropy
  rw [id_channel_covering_eq d hd φ U j hj ε]
theorem id_channel_entropy_diff_zero
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (U : Set X) (j : I) (hj : j ∈ Iid d φ U)
    (ε : ENNReal) (hdef : MappingEntropyDiffWellDefined d φ U {j} {j} ε) :
    mappingEntropyDiff d φ U {j} {j} ε = 0 := by
  unfold mappingEntropyDiff
  rw [id_channel_entropy_eq d hd φ U j hj ε]
  exact erealSub_self _
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set
variable {X : Type} {I : Type} {bot : X}
theorem metric_entropy_eq_coe_of_cover_finite
    (d : X → X → ENNReal) (ε : ENNReal) (U : Set X)
    (h0 : covering_number d ε U ≠ 0) (htop : covering_number d ε U ≠ ⊤) :
    metric_entropy d ε U =
      ↑(Real.logb 2 (covering_number d ε U).toReal) := by
  unfold metric_entropy
  simp [log2_ereal, h0, htop]
theorem covering_number_pos_of_nonempty
    (d : X → X → ENNReal) (ε : ENNReal) (U : Set X) (hU : U.Nonempty) :
    covering_number d ε U ≠ 0 := by
  exact ne_of_gt (lt_of_lt_of_le zero_lt_one
    (one_le_covering_number_of_nonempty d ε U hU))
theorem image_nonempty_of_nonempty (φ : Operator X bot) {U : Set X} (hU : U.Nonempty) :
    (φ.func '' U).Nonempty := by
  rcases hU with ⟨x, hx⟩
  exact ⟨φ.func x, ⟨x, hx, rfl⟩⟩
theorem image_net_of_lip [DecidableEq X]
    (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) (i j : I)
    (L : ENNReal) (hLpos : 0 < L) (hLip : ∀ x ∈ U, ∀ y ∈ U,
      d j (φ.func x) (φ.func y) ≤ L * d i x y)
    {ε : ENNReal} {S : Finset X}
    (hS : InternalEpsilonNet (d i) (ε / L) U S) :
    InternalEpsilonNet (d j) ε (φ.func '' U) (S.image φ.func) := by
  classical
  constructor
  · intro z hz
    rcases Finset.mem_image.mp hz with ⟨s, hs, rfl⟩
    exact ⟨s, hS.1 hs, rfl⟩
  · intro z hz
    rcases hz with ⟨x, hx, rfl⟩
    rcases hS.2 x hx with ⟨s, hs, hdist⟩
    refine ⟨φ.func s, Finset.mem_image.mpr ⟨s, hs, rfl⟩, ?_⟩
    have hmul : L * d i x s < ε := by
      have := (ENNReal.mul_lt_of_lt_div hdist : d i x s * L < ε)
      rwa [mul_comm] at this
    exact lt_of_le_of_lt (hLip x hx s (hS.1 hs)) hmul
theorem covering_number_image_le_of_lip
    (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) (i j : I)
    (L : ENNReal) (hLpos : 0 < L)
    (hLip : ∀ x ∈ U, ∀ y ∈ U,
      d j (φ.func x) (φ.func y) ≤ L * d i x y)
    (ε : ENNReal) :
    covering_number (d j) ε (φ.func '' U) ≤ covering_number (d i) (ε / L) U := by
  classical
  by_cases hfin : ∃ S : Finset X, InternalEpsilonNet (d i) (ε / L) U S
  · obtain ⟨S, hS, hcover, _⟩ := covering_number_attained (d i) (ε / L) U hfin
    calc
      covering_number (d j) ε (φ.func '' U)
          ≤ ((S.image φ.func).card : ENNReal) :=
            covering_number_le_card_of_net (image_net_of_lip d φ U i j L hLpos hLip hS)
      _ ≤ (S.card : ENNReal) := by exact_mod_cast Finset.card_image_le
      _ = covering_number (d i) (ε / L) U := hcover.symm
  · rw [(covering_number_eq_top_iff (d i) (ε / L) U).mpr hfin]
    exact le_top
theorem lip_entropy_diff_lower
    (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X)
    (i j : I) (L ε : ENNReal)
    (hU : U.Nonempty) (hLpos : 0 < L) (hLtop : L ≠ ⊤)
    (hεpos : 0 < ε) (hεtop : ε ≠ ⊤)
    (hTB : TotallyBoundedOn (d i) U)
    (hLip : ∀ x ∈ U, ∀ y ∈ U,
      d j (φ.func x) (φ.func y) ≤ L * d i x y) :
    erealSub (subfamily_metric_entropy d ({i} : Set I) ε U)
        (subfamily_metric_entropy d ({i} : Set I) (ε / L) U) ≤
      mappingEntropyDiff d φ U {i} {j} ε := by
  classical
  have hdivpos : 0 < ε / L := ENNReal.div_pos (ne_of_gt hεpos) hLtop
  have hdivtop : ε / L ≠ ⊤ := ENNReal.div_ne_top hεtop (ne_of_gt hLpos)
  have hNin_top : covering_number (d i) ε U ≠ ⊤ := hTB ε hεpos hεtop
  have hNin2_top : covering_number (d i) (ε / L) U ≠ ⊤ := hTB (ε / L) hdivpos hdivtop
  have hNin0 : covering_number (d i) ε U ≠ 0 :=
    covering_number_pos_of_nonempty (d i) ε U hU
  have hNin20 : covering_number (d i) (ε / L) U ≠ 0 :=
    covering_number_pos_of_nonempty (d i) (ε / L) U hU
  have hcover := covering_number_image_le_of_lip d φ U i j L hLpos hLip ε
  have hNout_top : covering_number (d j) ε (φ.func '' U) ≠ ⊤ :=
    ne_top_of_le_ne_top hNin2_top hcover
  have hNout0 : covering_number (d j) ε (φ.func '' U) ≠ 0 :=
    covering_number_pos_of_nonempty (d j) ε (φ.func '' U)
      (image_nonempty_of_nonempty φ hU)
  have hEin : metric_entropy (d i) ε U =
      ↑(Real.logb 2 (covering_number (d i) ε U).toReal) :=
    metric_entropy_eq_coe_of_cover_finite (d i) ε U hNin0 hNin_top
  have hEin2 : metric_entropy (d i) (ε / L) U =
      ↑(Real.logb 2 (covering_number (d i) (ε / L) U).toReal) :=
    metric_entropy_eq_coe_of_cover_finite (d i) (ε / L) U hNin20 hNin2_top
  have hEout : metric_entropy (d j) ε (φ.func '' U) =
      ↑(Real.logb 2 (covering_number (d j) ε (φ.func '' U)).toReal) :=
    metric_entropy_eq_coe_of_cover_finite (d j) ε (φ.func '' U) hNout0 hNout_top
  have hlog : Real.logb 2 (covering_number (d j) ε (φ.func '' U)).toReal ≤
      Real.logb 2 (covering_number (d i) (ε / L) U).toReal := by
    apply Real.logb_le_logb_of_le one_lt_two
    · exact ENNReal.toReal_pos hNout0 hNout_top
    · exact ENNReal.toReal_mono hNin2_top hcover
  unfold mappingEntropyDiff
  rw [subfamily_metric_entropy_singleton d i ε U,
    subfamily_metric_entropy_singleton d i (ε / L) U,
    subfamily_metric_entropy_singleton d j ε (φ.func '' U)]
  rw [hEin, hEin2, hEout, erealSub_coe_coe, erealSub_coe_coe]
  apply EReal.coe_le_coe
  linarith
theorem preimage_net_of_colip
    (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) (i j : I)
    (K : ENNReal) (hKpos : 0 < K) (hKtop : K ≠ ⊤)
    (hco : ∀ x ∈ U, ∀ y ∈ U, K * d i x y ≤ d j (φ.func x) (φ.func y))
    {ε : ENNReal} {T : Finset X}
    (hT : InternalEpsilonNet (d j) ε (φ.func '' U) T) :
    ∃ S : Finset X, InternalEpsilonNet (d i) (ε / K) U S ∧ S.card ≤ T.card := by
  classical
  let rep : {t : X // t ∈ T} → X := fun t =>
    Classical.choose (hT.1 t.2)
  have hrepU : ∀ t : {t : X // t ∈ T}, rep t ∈ U := fun t =>
    (Classical.choose_spec (hT.1 t.2)).1
  have hrepval : ∀ t : {t : X // t ∈ T}, φ.func (rep t) = t.1 := fun t =>
    (Classical.choose_spec (hT.1 t.2)).2
  let S : Finset X := T.attach.image rep
  refine ⟨S, ?_, ?_⟩
  · constructor
    · intro x hx
      rcases Finset.mem_image.mp hx with ⟨t, _, rfl⟩
      exact hrepU t
    · intro x hx
      rcases hT.2 (φ.func x) ⟨x, hx, rfl⟩ with ⟨t, ht, hdist⟩
      refine ⟨rep ⟨t, ht⟩, ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨⟨t, ht⟩, Finset.mem_attach _ _, rfl⟩
      · have hval : φ.func (rep ⟨t, ht⟩) = t := hrepval ⟨t, ht⟩
        have hcoin : K * d i x (rep ⟨t, ht⟩) < ε := by
          calc
            K * d i x (rep ⟨t, ht⟩) ≤
                d j (φ.func x) (φ.func (rep ⟨t, ht⟩)) :=
              hco x hx (rep ⟨t, ht⟩) (hrepU ⟨t, ht⟩)
            _ = d j (φ.func x) t := by rw [hval]
            _ < ε := hdist
        rw [ENNReal.lt_div_iff_mul_lt (Or.inl (ne_of_gt hKpos)) (Or.inl hKtop)]
        rwa [mul_comm]
  · calc
      S.card ≤ T.attach.card := Finset.card_image_le
      _ = T.card := Finset.card_attach
theorem covering_number_le_image_of_colip
    (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) (i j : I)
    (K : ENNReal) (hKpos : 0 < K) (hKtop : K ≠ ⊤)
    (hco : ∀ x ∈ U, ∀ y ∈ U, K * d i x y ≤ d j (φ.func x) (φ.func y))
    (ε : ENNReal) :
    covering_number (d i) (ε / K) U ≤ covering_number (d j) ε (φ.func '' U) := by
  classical
  by_cases hfin : ∃ T : Finset X, InternalEpsilonNet (d j) ε (φ.func '' U) T
  · obtain ⟨T, hT, hcover, _⟩ :=
      covering_number_attained (d j) ε (φ.func '' U) hfin
    obtain ⟨S, hS, hcard⟩ := preimage_net_of_colip d φ U i j K hKpos hKtop hco hT
    calc
      covering_number (d i) (ε / K) U ≤ (S.card : ENNReal) :=
        covering_number_le_card_of_net hS
      _ ≤ (T.card : ENNReal) := by exact_mod_cast hcard
      _ = covering_number (d j) ε (φ.func '' U) := hcover.symm
  · rw [(covering_number_eq_top_iff (d j) ε (φ.func '' U)).mpr hfin]
    exact le_top
theorem erealSub_coe_top (x : ℝ) : erealSub (↑x : EReal) ⊤ = ⊥ := by
  simp [erealSub]
theorem erealSub_coe_coe_le_coe_coe {a b c d : ℝ} (h : a - c ≤ b - d) :
    (erealSub (↑a : EReal) (↑c : EReal)) ≤ erealSub (↑b : EReal) (↑d : EReal) := by
  rw [erealSub_coe_coe, erealSub_coe_coe]
  exact EReal.coe_le_coe h
theorem colip_entropy_diff_upper
    (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X)
    (i j : I) (K ε : ENNReal)
    (hU : U.Nonempty) (hKpos : 0 < K) (hKtop : K ≠ ⊤)
    (hεpos : 0 < ε) (hεtop : ε ≠ ⊤)
    (hTB : TotallyBoundedOn (d i) U)
    (hco : ∀ x ∈ U, ∀ y ∈ U, K * d i x y ≤ d j (φ.func x) (φ.func y)) :
    mappingEntropyDiff d φ U {i} {j} ε ≤
      erealSub (subfamily_metric_entropy d ({i} : Set I) ε U)
        (subfamily_metric_entropy d ({i} : Set I) (ε / K) U) := by
  classical
  have hdivpos : 0 < ε / K := ENNReal.div_pos (ne_of_gt hεpos) hKtop
  have hdivtop : ε / K ≠ ⊤ := ENNReal.div_ne_top hεtop (ne_of_gt hKpos)
  have hNin_top : covering_number (d i) ε U ≠ ⊤ := hTB ε hεpos hεtop
  have hNin2_top : covering_number (d i) (ε / K) U ≠ ⊤ := hTB (ε / K) hdivpos hdivtop
  have hNin0 : covering_number (d i) ε U ≠ 0 :=
    covering_number_pos_of_nonempty (d i) ε U hU
  have hNin20 : covering_number (d i) (ε / K) U ≠ 0 :=
    covering_number_pos_of_nonempty (d i) (ε / K) U hU
  have hEin : metric_entropy (d i) ε U =
      ↑(Real.logb 2 (covering_number (d i) ε U).toReal) :=
    metric_entropy_eq_coe_of_cover_finite (d i) ε U hNin0 hNin_top
  have hEin2 : metric_entropy (d i) (ε / K) U =
      ↑(Real.logb 2 (covering_number (d i) (ε / K) U).toReal) :=
    metric_entropy_eq_coe_of_cover_finite (d i) (ε / K) U hNin20 hNin2_top
  have hcover := covering_number_le_image_of_colip d φ U i j K hKpos hKtop hco ε
  by_cases houttop : covering_number (d j) ε (φ.func '' U) = ⊤
  · have hEout_top : metric_entropy (d j) ε (φ.func '' U) = ⊤ := by
      unfold metric_entropy
      simp [log2_ereal, houttop]
    unfold mappingEntropyDiff
    rw [subfamily_metric_entropy_singleton d i ε U,
      subfamily_metric_entropy_singleton d i (ε / K) U,
      subfamily_metric_entropy_singleton d j ε (φ.func '' U)]
    rw [hEin, hEin2, hEout_top, erealSub_coe_top, erealSub_coe_coe]
    exact bot_le
  · have hNout0 : covering_number (d j) ε (φ.func '' U) ≠ 0 :=
      covering_number_pos_of_nonempty (d j) ε (φ.func '' U)
        (image_nonempty_of_nonempty φ hU)
    have hEout : metric_entropy (d j) ε (φ.func '' U) =
        ↑(Real.logb 2 (covering_number (d j) ε (φ.func '' U)).toReal) :=
      metric_entropy_eq_coe_of_cover_finite (d j) ε (φ.func '' U) hNout0 houttop
    have hlog : Real.logb 2 (covering_number (d i) (ε / K) U).toReal ≤
        Real.logb 2 (covering_number (d j) ε (φ.func '' U)).toReal := by
      apply Real.logb_le_logb_of_le one_lt_two
      · exact ENNReal.toReal_pos hNin20 hNin2_top
      · exact ENNReal.toReal_mono houttop hcover
    unfold mappingEntropyDiff
    rw [subfamily_metric_entropy_singleton d i ε U,
      subfamily_metric_entropy_singleton d i (ε / K) U,
      subfamily_metric_entropy_singleton d j ε (φ.func '' U)]
    rw [hEin, hEin2, hEout, erealSub_coe_coe, erealSub_coe_coe]
    apply EReal.coe_le_coe
    linarith
theorem subfamily_pseudometric_self_zero
    (d : I → X → X → ENNReal) (hself : ∀ i x, d i x x = 0)
    (J : Set I) (x : X) :
    subfamily_pseudometric d J x x = 0 := by
  rw [subfamily_pseudometric, ENNReal.iSup_eq_zero]
  intro j
  exact hself j.1 x
theorem finite_mapping_entropy_diff_wellDefined
    (d : I → X → X → ENNReal) (hself : ∀ i x, d i x x = 0)
    (φ : Operator X bot) (U : Set X) (hUfin : U.Finite)
    (Jin Jout : Set I) (ε : ENNReal) (hε : 0 < ε) (hεtop : ε ≠ ⊤) :
    MappingEntropyDiffWellDefined d φ U Jin Jout ε := by
  left
  exact finite_set_metric_entropy_ne_top (subfamily_pseudometric d Jin)
    (subfamily_pseudometric_self_zero d hself Jin) U hUfin hε
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set
set_option maxHeartbeats 4000000
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
open formal_oet.vol_01.ch_01_foundations
open Set
set_option maxHeartbeats 4000000
def lineDist : Option ℝ → Option ℝ → ENNReal
  | none, none => 0
  | some x, some y => ENNReal.ofReal |x - y|
  | none, some _ => ⊤
  | some _, none => ⊤
@[simp] theorem lineDist_none_none : lineDist none none = 0 := rfl
@[simp] theorem lineDist_some_some (x y : ℝ) :
    lineDist (some x) (some y) = ENNReal.ofReal |x - y| := rfl
@[simp] theorem lineDist_none_some (y : ℝ) : lineDist none (some y) = ⊤ := rfl
@[simp] theorem lineDist_some_none (x : ℝ) : lineDist (some x) none = ⊤ := rfl
theorem lineDist_extended : ExtendedPseudoMetric (Option ℝ) none lineDist where
  nonabsorbing := ⟨some 0, by simp⟩
  dist_self := by
    intro x
    rcases x with _ | x <;> simp
  symm := by
    intro x y
    rcases x with _ | x <;> rcases y with _ | y <;> simp [lineDist, abs_sub_comm]
  triangle := by
    intro x y z
    rcases x with _ | x <;> rcases y with _ | y <;> rcases z with _ | z <;> simp [lineDist]
    rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (abs_sub_le x y z)
  isolate_bot := by
    intro x hx
    rcases x with _ | x
    · exact (hx rfl).elim
    · simp
noncomputable def stepFun : Option ℝ → Option ℝ
  | none => none
  | some x => some (if x < 0 then 0 else 1)
@[simp] theorem stepFun_none : stepFun none = none := rfl
@[simp] theorem stepFun_some (x : ℝ) :
    stepFun (some x) = some (if x < 0 then 0 else 1) := rfl
theorem stepFun_preserves_bot : stepFun none = none := rfl
noncomputable def stepOp : Operator (Option ℝ) none where
  func := stepFun
  preserves_bot := stepFun_preserves_bot
def stepU : Set (Option ℝ) :=
  some '' (Set.Ico (-1 : ℝ) 0 ∪ Set.Ioc (0 : ℝ) 1)
theorem mem_stepU {x : Option ℝ} :
    x ∈ stepU ↔ ∃ r : ℝ, x = some r ∧ ((-1 ≤ r ∧ r < 0) ∨ (0 < r ∧ r ≤ 1)) := by
  unfold stepU
  constructor
  · rintro ⟨r, hr, rfl⟩
    rcases hr with hr | hr
    · exact ⟨r, rfl, Or.inl ⟨hr.1, hr.2⟩⟩
    · exact ⟨r, rfl, Or.inr ⟨hr.1, hr.2⟩⟩
  · rintro ⟨r, rfl, hr⟩
    refine ⟨r, ?_, rfl⟩
    rcases hr with hr | hr
    · exact Or.inl ⟨hr.1, hr.2⟩
    · exact Or.inr ⟨hr.1, hr.2⟩
theorem stepU_some_ne_zero {y : ℝ} (hy : some y ∈ stepU) : y ≠ 0 := by
  rcases (mem_stepU.mp hy) with ⟨r, hsr, hr⟩
  injection hsr with hry
  subst r
  rcases hr with hr | hr <;> linarith
theorem abs_pos_of_mem_stepU {y : ℝ} (hy : some y ∈ stepU) : 0 < |y| :=
  abs_pos.mpr (stepU_some_ne_zero hy)
theorem step_same_neg {x y : ℝ} (hx : x < 0) (hy : y < 0) :
    stepFun (some x) = stepFun (some y) := by
  simp [stepFun, hx, hy]
theorem step_same_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    stepFun (some x) = stepFun (some y) := by
  simp [stepFun, not_lt.mpr (le_of_lt hx), not_lt.mpr (le_of_lt hy)]
theorem step_neg_pos {x y : ℝ} (hx : x < 0) (hy : 0 < y) :
    lineDist (stepFun (some x)) (stepFun (some y)) = 1 := by
  simp [stepFun, hx, not_lt.mpr (le_of_lt hy)]
theorem step_pos_neg {x y : ℝ} (hx : 0 < x) (hy : y < 0) :
    lineDist (stepFun (some x)) (stepFun (some y)) = 1 := by
  simp [stepFun, not_lt.mpr (le_of_lt hx), hy]
theorem lineDist_step_same_sign {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : (x < 0 ∧ y < 0) ∨ (0 < x ∧ 0 < y)) :
    lineDist (stepFun (some x)) (stepFun (some y)) = 0 := by
  rcases h with ⟨hxneg, hyneg⟩ | ⟨hxpos, hypos⟩
  · rw [step_same_neg hxneg hyneg]; simp
  · rw [step_same_pos hxpos hypos]; simp
theorem opposite_sign_abs_gt {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : ¬ ((x < 0 ∧ y < 0) ∨ (0 < x ∧ 0 < y))) :
    |y| < |x - y| := by
  rcases lt_or_gt_of_ne hx with hxneg | hxpos <;>
    rcases lt_or_gt_of_ne hy with hyneg | hypos
  · exact False.elim (h (Or.inl ⟨hxneg, hyneg⟩))
  · rw [abs_of_pos hypos, abs_of_neg (sub_neg.mpr (by linarith))]
    linarith
  · rw [abs_of_neg hyneg, abs_of_pos (sub_pos.mpr (by linarith))]
    linarith
  · exact False.elim (h (Or.inr ⟨hxpos, hypos⟩))
theorem ofReal_abs_y_legal {y : ℝ} (hy : some y ∈ stepU) :
    LegalRadius lineDist (fun a b => lineDist a b = 0) stepOp (some y) stepU
      (ENNReal.ofReal |y|) := by
  refine ⟨ENNReal.ofReal_pos.mpr (abs_pos_of_mem_stepU hy), ENNReal.ofReal_ne_top, ?_⟩
  intro x hx hlt
  rcases (mem_stepU.mp hx) with ⟨xr, hxs, hxrU⟩
  subst x
  rcases (mem_stepU.mp hy) with ⟨yr, hys, hyrU⟩
  injection hys with hyr
  subst y
  have hxrne : xr ≠ 0 := by
    rcases hxrU with hxrU | hxrU <;> linarith
  have hyrne : yr ≠ 0 := by
    rcases hyrU with hyrU | hyrU <;> linarith
  have hltreal : |xr - yr| < |yr| := by
    rw [lineDist_some_some] at hlt
    rwa [ENNReal.ofReal_lt_ofReal_iff (abs_pos_of_mem_stepU hy)] at hlt
  have hsame : (xr < 0 ∧ yr < 0) ∨ (0 < xr ∧ 0 < yr) := by
    by_contra hnot
    have hgt := opposite_sign_abs_gt hxrne hyrne hnot
    linarith
  change lineDist (stepFun (some xr)) (stepFun (some yr)) = 0
  exact lineDist_step_same_sign hxrne hyrne hsame
/-- Every legal radius is at most `|y|`; the proof constructs a point of the
opposite sign inside the ball when the radius is larger. -/
theorem legal_radius_le_abs {y : ℝ} (hy : some y ∈ stepU) {r : ENNReal}
    (hr : LegalRadius lineDist (fun a b => lineDist a b = 0) stepOp (some y) stepU r) :
    r ≤ ENNReal.ofReal |y| := by
  by_contra hle
  have hlt : ENNReal.ofReal |y| < r := lt_of_not_ge hle
  have hrtop : r ≠ ⊤ := hr.2.1
  have hreal : |y| < r.toReal := by
    have := (ENNReal.ofReal_lt_iff_lt_toReal (abs_nonneg y) hrtop).mp hlt
    simpa using this
  let δ : ℝ := r.toReal - |y|
  have hδ : 0 < δ := by dsimp [δ]; linarith
  let a : ℝ := min (1/2 : ℝ) (δ / 2)
  have hapos : 0 < a := by
    dsimp [a]
    exact lt_min (by norm_num) (by linarith)
  have hahalf : a ≤ 1/2 := by dsimp [a]; exact min_le_left _ _
  have hadelta : a ≤ δ / 2 := by dsimp [a]; exact min_le_right _ _
  by_cases hypos : 0 < y
  · let x : ℝ := -a
    have hxneg : x < 0 := by dsimp [x]; linarith
    have hxU : some x ∈ stepU := by
      rw [mem_stepU]
      refine ⟨x, rfl, Or.inl ⟨?_, hxneg⟩⟩
      dsimp [x]; linarith
    have hdist : |x - y| < r.toReal := by
      have habs : |x - y| = y + a := by
        rw [abs_of_neg (sub_neg.mpr (by dsimp [x]; linarith))]
        dsimp [x]; ring
      rw [habs]
      dsimp [δ] at hadelta
      rw [abs_of_pos hypos] at hreal hadelta
      linarith
    have hltline : lineDist (some x) (some y) < r := by
      rw [lineDist_some_some]
      exact (ENNReal.ofReal_lt_iff_lt_toReal (abs_nonneg _) hrtop).mpr hdist
    have hzero := hr.2.2 (some x) hxU hltline
    change lineDist (stepFun (some x)) (stepFun (some y)) = 0 at hzero
    have hone : lineDist (stepFun (some x)) (stepFun (some y)) = 1 :=
      step_neg_pos hxneg hypos
    rw [hone] at hzero
    norm_num at hzero
  · have hyneg : y < 0 := by
      rcases (mem_stepU.mp hy) with ⟨yr, hsy, hyrU⟩
      injection hsy with hry
      subst yr
      rcases hyrU with hyrU | hyrU
      · exact hyrU.2
      · exact False.elim (hypos hyrU.1)
    let x : ℝ := a
    have hxpos : 0 < x := by dsimp [x]; exact hapos
    have hxU : some x ∈ stepU := by
      rw [mem_stepU]
      refine ⟨x, rfl, Or.inr ⟨hxpos, ?_⟩⟩
      dsimp [x]; linarith
    have hdist : |x - y| < r.toReal := by
      have habs : |x - y| = a + (-y) := by
        rw [abs_of_pos (sub_pos.mpr (by dsimp [x]; linarith))]
        dsimp [x]; ring
      rw [habs]
      have habs_y : |y| = -y := abs_of_neg hyneg
      dsimp [δ] at hadelta
      rw [habs_y] at hreal hadelta
      linarith
    have hltline : lineDist (some x) (some y) < r := by
      rw [lineDist_some_some]
      exact (ENNReal.ofReal_lt_iff_lt_toReal (abs_nonneg _) hrtop).mpr hdist
    have hzero := hr.2.2 (some x) hxU hltline
    change lineDist (stepFun (some x)) (stepFun (some y)) = 0 at hzero
    have hone : lineDist (stepFun (some x)) (stepFun (some y)) = 1 :=
      step_pos_neg hxpos hyneg
    rw [hone] at hzero
    norm_num at hzero
theorem pointwise_radius_eq_abs {y : ℝ} (hy : some y ∈ stepU) :
    pointwiseRadius lineDist (fun a b => lineDist a b = 0) stepOp (some y) stepU =
      ENNReal.ofReal |y| := by
  apply le_antisymm
  · unfold pointwiseRadius
    apply iSup_le
    intro r
    exact legal_radius_le_abs hy r.2
  · exact le_pointwiseRadius_of_legal (ofReal_abs_y_legal hy)
theorem unified_radius_step_eq_zero :
    unifiedRadius lineDist (fun a b => lineDist a b = 0) stepOp stepU stepU = 0 := by
  unfold unifiedRadius
  apply le_antisymm
  · have h : (⨅ y : {y : Option ℝ // y ∈ stepU},
        pointwiseRadius lineDist (fun a b => lineDist a b = 0) stepOp y.1 stepU) = ⊥ := by
      apply (iInf_eq_bot _).mpr
      intro b hb
      by_cases hbtop : b = ⊤
      · refine ⟨⟨some (1/2), ?_⟩, ?_⟩
        · rw [mem_stepU]
          exact ⟨1/2, rfl, Or.inr ⟨by norm_num, by norm_num⟩⟩
        · rw [pointwise_radius_eq_abs (by
            rw [mem_stepU]
            exact ⟨1/2, rfl, Or.inr ⟨by norm_num, by norm_num⟩⟩)]
          simp [hbtop]
      · have hbpos : 0 < b.toReal := ENNReal.toReal_pos (ne_of_gt hb) hbtop
        let ε : ℝ := min (1/2 : ℝ) (b.toReal / 2)
        have hεpos : 0 < ε := lt_min (by norm_num) (by linarith)
        have hεle : ε ≤ 1/2 := min_le_left _ _
        have hεb : ε < b.toReal := lt_of_le_of_lt (min_le_right _ _) (by linarith)
        refine ⟨⟨some ε, ?_⟩, ?_⟩
        · rw [mem_stepU]
          exact ⟨ε, rfl, Or.inr ⟨hεpos, by linarith⟩⟩
        · rw [pointwise_radius_eq_abs (by
            rw [mem_stepU]
            exact ⟨ε, rfl, Or.inr ⟨hεpos, by linarith⟩⟩)]
          rw [ENNReal.ofReal_lt_iff_lt_toReal (abs_nonneg _) hbtop]
          simpa [abs_of_pos hεpos] using hεb
    simpa using le_of_eq h
  · exact zero_le _
theorem stepU_subset_dom : stepU ⊆ dom stepOp := by
  intro x hx
  rcases (mem_stepU.mp hx) with ⟨r, rfl, hr⟩
  rw [dom]
  simp [stepOp, stepFun]
theorem legal_radius_iff_abs {y : ℝ} (hy : some y ∈ stepU) {r : ENNReal}
    (hr0 : 0 < r) :
    LegalRadius lineDist (fun a b => lineDist a b = 0) stepOp (some y) stepU r ↔
      r ≤ ENNReal.ofReal |y| := by
  constructor
  · exact legal_radius_le_abs hy
  · intro hle
    exact legalRadius_mono hr0 hle (ofReal_abs_y_legal hy)
theorem counterexample_3_1_structure :
    ExtendedPseudoMetric (Option ℝ) none lineDist ∧
      (∀ x ∈ stepU, stepOp.func x ≠ none) ∧
      (∀ y : ℝ, some y ∈ stepU → 0 < pointwiseRadius lineDist
        (fun a b => lineDist a b = 0) stepOp (some y) stepU) := by
  refine ⟨lineDist_extended, ?_, ?_⟩
  · intro x hx
    have hx' := stepU_subset_dom hx
    simpa [dom] using hx'
  · intro y hy
    rw [pointwise_radius_eq_abs hy]
    exact ENNReal.ofReal_pos.mpr (abs_pos_of_mem_stepU hy)
open formal_oet.vol_01.ch_01_foundations
open Set
set_option maxHeartbeats 4000000
def stepB (a : ℝ) : Set (Option ℝ) := {some (-a), some a}
theorem stepB_nonempty (a : ℝ) : (stepB a).Nonempty := by
  refine ⟨some a, ?_⟩
  simp [stepB]
theorem stepB_input_cover_one {a : ℝ} {τ : ENNReal} (ha : 0 < a) (ha1 : a ≤ 1)
    (h2a : ENNReal.ofReal (2 * a) < τ)
    (hτpos : 0 < τ) :
    covering_number lineDist τ (stepB a) = 1 := by
  have hnet : InternalEpsilonNet lineDist τ (stepB a) ({some (-a)} : Finset (Option ℝ)) := by
    constructor
    · intro x hx
      simp at hx
      subst x
      simp [stepB]
    · intro x hx
      refine ⟨some (-a), by simp, ?_⟩
      simp only [stepB, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · simp [hτpos]
      · rw [lineDist_some_some]
        have habs : |a - (-a)| = 2 * a := by
          rw [show a - (-a) = 2 * a by ring, abs_of_pos (by linarith)]
        rw [habs]
        exact h2a
  apply le_antisymm
  · calc
      covering_number lineDist τ (stepB a) ≤ (({some (-a)} : Finset (Option ℝ)).card : ENNReal) :=
        covering_number_le_card_of_net hnet
      _ = 1 := by simp
  · exact one_le_covering_number_of_nonempty lineDist τ (stepB a) (stepB_nonempty a)
theorem step_image_B {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    stepOp.func '' stepB a = ({some (0 : ℝ), some 1} : Set (Option ℝ)) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp only [stepB, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · have hneg : -a < 0 := by linarith
      simp [stepOp, stepFun, hneg]
    · have hnonneg : ¬a < 0 := not_lt.mpr (le_of_lt ha)
      simp [stepOp, stepFun, hnonneg]
  · intro hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · refine ⟨some (-a), ?_, ?_⟩
      · simp [stepB]
      · have hneg : -a < 0 := by linarith
        simp [stepOp, stepFun, hneg]
    · refine ⟨some a, ?_, ?_⟩
      · simp [stepB]
      · have hnonneg : ¬a < 0 := not_lt.mpr (le_of_lt ha)
        simp [stepOp, stepFun, hnonneg]
theorem out_two_cover_le :
    covering_number lineDist (1/2 : ENNReal) ({some (0 : ℝ), some 1} : Set (Option ℝ)) ≤ 2 := by
  have hnet : InternalEpsilonNet lineDist (1/2 : ENNReal)
      ({some (0 : ℝ), some 1} : Set (Option ℝ)) ({some 0, some 1} : Finset (Option ℝ)) := by
    constructor
    · intro x hx
      simp at hx
      rcases hx with rfl | rfl <;> simp
    · intro x hx
      refine ⟨x, ?_, ?_⟩
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl <;> simp
      · have hd : lineDist x x = 0 := by
          rcases x with _ | x <;> simp
        rw [hd]
        norm_num
  calc
    covering_number lineDist (1/2 : ENNReal) ({some (0 : ℝ), some 1} : Set (Option ℝ))
        ≤ (({some 0, some 1} : Finset (Option ℝ)).card : ENNReal) :=
          covering_number_le_card_of_net hnet
    _ = 2 := by norm_num
theorem no_one_center_covers_out :
    ¬ ∃ c ∈ ({some (0 : ℝ), some 1} : Set (Option ℝ)),
      lineDist (some 0) c < (1/2 : ENNReal) ∧ lineDist (some 1) c < (1/2 : ENNReal) := by
  rintro ⟨c, hc, h0, h1⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
  rcases hc with rfl | rfl
  · rw [lineDist_some_some] at h1
    norm_num at h1
  · rw [lineDist_some_some] at h0
    norm_num at h0
theorem out_two_cover_ge :
    (2 : ENNReal) ≤ covering_number lineDist (1/2 : ENNReal)
      ({some (0 : ℝ), some 1} : Set (Option ℝ)) := by
  have hfin : ∃ S : Finset (Option ℝ), InternalEpsilonNet lineDist (1/2 : ENNReal)
      ({some (0 : ℝ), some 1} : Set (Option ℝ)) S := by
    refine ⟨{some 0, some 1}, ?_⟩
    constructor
    · intro x hx
      simp at hx
      rcases hx with rfl | rfl <;> simp
    · intro x hx
      refine ⟨x, ?_, ?_⟩
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl <;> simp
      · rcases x with _ | x
        · norm_num [lineDist]
        · norm_num [lineDist]
  obtain ⟨S, hS, hcover, hmin⟩ :=
    covering_number_attained lineDist (1/2 : ENNReal)
      ({some (0 : ℝ), some 1} : Set (Option ℝ)) hfin
  have hcard : 2 ≤ S.card := by
    by_contra hnot
    have hle : S.card ≤ 1 := by omega
    have hall := Finset.card_le_one.mp hle
    rcases hS.2 (some 0) (by simp) with ⟨c0, hc0, hdist0⟩
    rcases hS.2 (some 1) (by simp) with ⟨c1, hc1, hdist1⟩
    have hc01 : c0 = c1 := hall c0 hc0 c1 hc1
    have hc0set : c0 ∈ ({some (0 : ℝ), some 1} : Set (Option ℝ)) := hS.1 hc0
    have hboth : lineDist (some 0) c0 < (1/2 : ENNReal) ∧
        lineDist (some 1) c0 < (1/2 : ENNReal) := by
      constructor
      · exact hdist0
      · simpa [hc01] using hdist1
    exact no_one_center_covers_out ⟨c0, hc0set, hboth.1, hboth.2⟩
  rw [hcover]
  exact_mod_cast hcard
theorem out_two_cover_eq :
    covering_number lineDist (1/2 : ENNReal)
      ({some (0 : ℝ), some 1} : Set (Option ℝ)) = 2 := by
  exact le_antisymm out_two_cover_le out_two_cover_ge
theorem step_two_point_cover_counterexample (τ : ENNReal) (hτpos : 0 < τ) (hτtop : τ ≠ ⊤) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧ ENNReal.ofReal (2 * a) < τ ∧
      covering_number lineDist τ (stepB a) = 1 ∧
      covering_number lineDist (1/2 : ENNReal) (stepOp.func '' stepB a) = 2 := by
  let a : ℝ := min (1/2 : ℝ) (τ.toReal / 4)
  have hτreal : 0 < τ.toReal := ENNReal.toReal_pos (ne_of_gt hτpos) hτtop
  have hapos : 0 < a := lt_min (by norm_num) (by positivity)
  have ha1 : a ≤ 1 := le_trans (min_le_left _ _) (by norm_num)
  have haτ : 2 * a < τ.toReal := by
    have hle : a ≤ τ.toReal / 4 := min_le_right _ _
    nlinarith
  have h2a : ENNReal.ofReal (2 * a) < τ :=
    (ENNReal.ofReal_lt_iff_lt_toReal (by positivity) hτtop).mpr haτ
  refine ⟨a, hapos, ha1, h2a, ?_, ?_⟩
  · exact stepB_input_cover_one hapos ha1 h2a hτpos
  · rw [step_image_B hapos ha1, out_two_cover_eq]
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set
set_option maxHeartbeats 5000000
def absLineDist : Option ℝ → Option ℝ → ENNReal
  | none, none => 0
  | some x, some y => ENNReal.ofReal (abs (abs x - abs y))
  | none, some _ => ⊤
  | some _, none => ⊤
@[simp] theorem absLineDist_none_none : absLineDist none none = 0 := rfl
@[simp] theorem absLineDist_some_some (x y : ℝ) :
    absLineDist (some x) (some y) = ENNReal.ofReal (abs (abs x - abs y)) := rfl
@[simp] theorem absLineDist_none_some (y : ℝ) : absLineDist none (some y) = ⊤ := rfl
@[simp] theorem absLineDist_some_none (x : ℝ) : absLineDist (some x) none = ⊤ := rfl
theorem absLineDist_self (x : Option ℝ) : absLineDist x x = 0 := by
  rcases x with _ | x <;> simp [absLineDist]
theorem absLineDist_extended : ExtendedPseudoMetric (Option ℝ) none absLineDist where
  nonabsorbing := ⟨some 0, by simp⟩
  dist_self := by intro x; rcases x with _ | x <;> simp
  symm := by
    intro x y
    rcases x with _ | x <;> rcases y with _ | y <;> simp [absLineDist, abs_sub_comm]
  triangle := by
    intro x y z
    rcases x with _ | x <;> rcases y with _ | y <;> rcases z with _ | z <;> simp [absLineDist]
    rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (abs_sub_le |x| |y| |z|)
  isolate_bot := by
    intro x hx
    rcases x with _ | x
    · exact (hx rfl).elim
    · simp
def absLineFam : Unit → Option ℝ → Option ℝ → ENNReal := fun _ => absLineDist
theorem absLineFam_extended :
    ∀ i : Unit, ExtendedPseudoMetric (Option ℝ) none (absLineFam i) :=
  fun _ => absLineDist_extended
def phi31 : Operator (Option ℝ) none where
  func
    | none => none
    | some x => some (2 * x - 1)
  preserves_bot := rfl
@[simp] theorem operator_mul_func {X : Type} {bot : X} (φ ψ : Operator X bot) (x : X) :
    (φ * ψ).func x = φ.func (ψ.func x) := rfl
@[simp] theorem operator_one_func {X : Type} {bot : X} (x : X) :
    ((1 : Operator X bot).func x) = x := rfl
def phi31sq : Operator (Option ℝ) none := phi31 * phi31
def U31 : Set (Option ℝ) := {some (0 : ℝ), some 1}
theorem ex31_phi_const : (() : Unit) ∈ Iconst absLineFam phi31 U31 := by
  intro x hx y hy
  simp only [U31, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
    norm_num [absLineFam, absLineDist, phi31]
theorem ex31_phi_fiber :
    Fiber absLineFam phi31 ({()} : Set Unit) (some (-1 : ℝ)) U31 = U31 := by
  ext x
  constructor
  · intro hx; exact hx.1
  · intro hx
    refine ⟨hx, ?_⟩
    intro k hk
    cases k
    simp only [U31, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;> norm_num [absLineFam, absLineDist, phi31]
theorem ex31_phi2_not_const : (() : Unit) ∉ Iconst absLineFam phi31sq U31 := by
  intro h
  have h01 := h (some 0) (by simp [U31]) (some 1) (by simp [U31])
  change absLineDist (phi31sq.func (some 0)) (phi31sq.func (some 1)) = 0 at h01
  norm_num [phi31sq, phi31, absLineFam, absLineDist] at h01
theorem ex31_phi2_not_id : (() : Unit) ∉ Iid absLineFam phi31sq U31 := by
  intro h
  have hz := h.2 (some 0) (by simp [U31])
  change absLineDist (phi31sq.func (some 0)) (some 0) = 0 at hz
  norm_num [phi31sq, phi31, absLineFam, absLineDist] at hz
theorem ex31_phi2_active : (() : Unit) ∈ Iact absLineFam phi31sq U31 :=
  ⟨ex31_phi2_not_const, ex31_phi2_not_id⟩
theorem ex31_phi2_fiber :
    Fiber absLineFam phi31sq ({()} : Set Unit) (some (-3 : ℝ)) U31 = {some 0} := by
  ext x
  constructor
  · intro hx
    simp only [U31, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx.1 with hx0 | hx1
    · simp [hx0]
    · exfalso
      subst x
      have hz := hx.2 () (by simp)
      norm_num [phi31sq, phi31, absLineFam, absLineDist] at hz
  · intro hx
    simp only [Set.mem_singleton_iff] at hx
    subst x
    refine ⟨by simp [U31], ?_⟩
    intro k hk
    cases k
    norm_num [phi31sq, phi31, absLineFam, absLineDist]
theorem ex31_constant_self_comp_no_distinguish
    (ψ : Operator (Option ℝ) none) {c : Option ℝ}
    (hconst : ∀ x ∈ U31, ψ.func x = c) :
    some (0 : ℝ) ∈ Fiber absLineFam (ψ * ψ) ({()} : Set Unit) ((ψ * ψ).func (some 0)) U31 ∧
      some (1 : ℝ) ∈ Fiber absLineFam (ψ * ψ) ({()} : Set Unit) ((ψ * ψ).func (some 0)) U31 := by
  have h0 : (ψ * ψ).func (some (0:ℝ)) = ψ.func c := by
    change ψ.func (ψ.func (some 0)) = ψ.func c
    rw [hconst (some 0) (by simp [U31])]
  have h1 : (ψ * ψ).func (some (1:ℝ)) = ψ.func c := by
    change ψ.func (ψ.func (some 1)) = ψ.func c
    rw [hconst (some 1) (by simp [U31])]
  constructor
  · refine ⟨by simp [U31], ?_⟩
    intro k hk
    cases k
    exact absLineDist_self _
  · refine ⟨by simp [U31], ?_⟩
    intro k hk
    cases k
    rw [h1, ← h0]
    exact absLineDist_self _
theorem colip_positive_pointwise_radius_gap
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (U : Set X) (i j : I) (K : ENNReal)
    (hco : ∀ x ∈ U, ∀ y ∈ U, K * d i x y ≤ d j (φ.func x) (φ.func y))
    (hKpos : 0 < K) (y : X) (hy : y ∈ U)
    (hrpos : 0 < pointwiseZeroRadius d φ i j y U) :
    ∀ x ∈ U, ¬ (0 < d i x y ∧ d i x y < pointwiseZeroRadius d φ i j y U) := by
  intro x hx hlt
  have hsym : d i y x < pointwiseZeroRadius d φ i j y U := by
    rw [(hd i).symm]
    exact hlt.2
  have hzero : d j (φ.func y) (φ.func x) = 0 :=
    pointwise_radius_truncation d hd φ U i j hx hsym
  have hcoxy := hco x hx y hy
  have hposmul : 0 < K * d i x y := ENNReal.mul_pos (ne_of_gt hKpos) (ne_of_gt hlt.1)
  have hle : K * d i x y ≤ 0 := by
    calc
      K * d i x y ≤ d j (φ.func x) (φ.func y) := hcoxy
      _ = d j (φ.func y) (φ.func x) := (hd j).symm _ _
      _ = 0 := hzero
  exact (not_lt_of_ge hle) hposmul
theorem colip_positive_unified_radius_gap
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (U : Set X) (i j : I) (K : ENNReal)
    (hco : ∀ x ∈ U, ∀ y ∈ U, K * d i x y ≤ d j (φ.func x) (φ.func y))
    (hKpos : 0 < K) (hrpos : 0 < zeroingMatrix d φ U j i) :
    ∀ x ∈ U, ∀ y ∈ U,
      d i x y = 0 ∨ zeroingMatrix d φ U j i ≤ d i x y := by
  intro x hx y hy
  by_cases hzero : d i x y = 0
  · exact Or.inl hzero
  · right
    by_contra hnot
    have hlt : d i x y < zeroingMatrix d φ U j i := lt_of_not_ge hnot
    have hpos : 0 < d i x y := lt_of_le_of_ne (zero_le _) (Ne.symm hzero)
    unfold zeroingMatrix unifiedRadius at hlt
    have hltp : d i x y < pointwiseZeroRadius d φ i j x U :=
      lt_of_lt_of_le hlt (iInf_le _ (⟨x, hx⟩ : {x : X // x ∈ U}))
    have hout : d j (φ.func x) (φ.func y) = 0 :=
      pointwise_radius_truncation d hd φ U i j hy hltp
    have hcop := hco x hx y hy
    have hposmul : 0 < K * d i x y := ENNReal.mul_pos (ne_of_gt hKpos) (ne_of_gt hpos)
    have hle : K * d i x y ≤ 0 := by
      calc
        K * d i x y ≤ d j (φ.func x) (φ.func y) := hcop
        _ = 0 := hout
    exact (not_lt_of_ge hle) hposmul
noncomputable abbrev threeHalves : ENNReal := (3/2 : ENNReal)
theorem threeHalves_eq : threeHalves = ((3/2 : NNReal) : ENNReal) := by
  norm_num [threeHalves, ENNReal.coe_div]
theorem one_lt_threeHalves : (1 : ENNReal) < threeHalves := by
  rw [threeHalves_eq]
  exact_mod_cast (by norm_num : (1 : NNReal) < 3/2)
theorem threeHalves_le_two : threeHalves ≤ (2 : ENNReal) := by
  rw [threeHalves_eq]
  change ((3/2 : NNReal) : ENNReal) ≤ ((2 : NNReal) : ENNReal)
  exact_mod_cast (by
    rw [div_le_iff₀ (by norm_num : (0 : NNReal) < 2)]
    norm_num : (3/2 : NNReal) ≤ 2)
theorem threeHalves_lt_three : threeHalves < (3 : ENNReal) := by
  rw [threeHalves_eq]
  exact_mod_cast (by norm_num : (3/2 : NNReal) < 3)
theorem zero_lt_threeHalves : (0 : ENNReal) < threeHalves := lt_trans zero_lt_one one_lt_threeHalves
theorem absLineDist_one_lt (x y : ℝ) (h : abs (abs x - abs y) = 1) :
    absLineDist (some x) (some y) < threeHalves := by
  rw [absLineDist_some_some, h]
  simpa using one_lt_threeHalves
theorem absLineDist_zero_lt (x y : ℝ) (h : abs (abs x - abs y) = 0) :
    absLineDist (some x) (some y) < threeHalves := by
  rw [absLineDist_some_some, h]
  simpa using zero_lt_threeHalves
def U33 : Set (Option ℝ) := {some (-3), some (-2), some 0, some 2}
def shift33 : Operator (Option ℝ) none where
  func
    | none => none
    | some x => some (x + 1)
  preserves_bot := rfl
def identityOp : Operator (Option ℝ) none := 1
theorem identity_fiber_neg3 :
    Fiber absLineFam identityOp ({()} : Set Unit) (some (-3 : ℝ)) U33 = {some (-3)} := by
  ext x
  constructor
  · intro hx
    simp only [U33, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx.1 with rfl | rfl | rfl | rfl
    · simp
    · exfalso
      have hz := hx.2 () (by simp)
      norm_num [absLineFam, absLineDist, identityOp, operator_one_func] at hz
    · exfalso
      have hz := hx.2 () (by simp)
      norm_num [absLineFam, absLineDist, identityOp, operator_one_func] at hz
    · exfalso
      have hz := hx.2 () (by simp)
      norm_num [absLineFam, absLineDist, identityOp, operator_one_func] at hz
  · intro hx
    simp only [Set.mem_singleton_iff] at hx
    subst x
    refine ⟨by simp [U33], ?_⟩
    intro k hk
    cases k
    exact absLineDist_self _
theorem identity_fiber_neg2 :
    Fiber absLineFam identityOp ({()} : Set Unit) (some (-2 : ℝ)) U33 =
      {some (-2), some 2} := by
  ext x
  constructor
  · intro hx
    simp only [U33, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx.1 with rfl | rfl | rfl | rfl
    · exfalso
      have hz := hx.2 () (by simp)
      norm_num [absLineFam, absLineDist, identityOp, operator_one_func] at hz
    · simp
    · exfalso
      have hz := hx.2 () (by simp)
      norm_num [absLineFam, absLineDist, identityOp, operator_one_func] at hz
    · simp
  · intro hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · refine ⟨by simp [U33], ?_⟩
      intro k hk; cases k; exact absLineDist_self _
    · refine ⟨by simp [U33], ?_⟩
      intro k hk; cases k
      norm_num [absLineFam, absLineDist, identityOp, operator_one_func]
theorem identity_fiber_zero :
    Fiber absLineFam identityOp ({()} : Set Unit) (some 0 : Option ℝ) U33 = {some 0} := by
  ext x
  constructor
  · intro hx
    simp only [U33, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx.1 with rfl | rfl | rfl | rfl
    · exfalso
      have hz := hx.2 () (by simp)
      norm_num [absLineFam, absLineDist, identityOp, operator_one_func] at hz
    · exfalso
      have hz := hx.2 () (by simp)
      norm_num [absLineFam, absLineDist, identityOp, operator_one_func] at hz
    · simp
    · exfalso
      have hz := hx.2 () (by simp)
      norm_num [absLineFam, absLineDist, identityOp, operator_one_func] at hz
  · intro hx
    simp only [Set.mem_singleton_iff] at hx
    subst x
    refine ⟨by simp [U33], ?_⟩
    intro k hk; cases k; exact absLineDist_self _
theorem identity_fiber_two :
    Fiber absLineFam identityOp ({()} : Set Unit) (some 2 : Option ℝ) U33 =
      {some (-2), some 2} := by
  rw [show (some (2:ℝ)) = (some 2) by rfl]
  ext x
  constructor
  · intro hx
    simp only [U33, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx.1 with rfl | rfl | rfl | rfl
    · exfalso
      have hz := hx.2 () (by simp)
      norm_num [absLineFam, absLineDist, identityOp, operator_one_func] at hz
    · simp
    · exfalso
      have hz := hx.2 () (by simp)
      norm_num [absLineFam, absLineDist, identityOp, operator_one_func] at hz
    · simp
  · intro hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · refine ⟨by simp [U33], ?_⟩
      intro k hk; cases k
      norm_num [absLineFam, absLineDist, identityOp, operator_one_func]
    · refine ⟨by simp [U33], ?_⟩
      intro k hk; cases k; exact absLineDist_self _
theorem shift_fiber_neg2 :
    Fiber absLineFam shift33 ({()} : Set Unit) (some (-2 : ℝ)) U33 = {some (-3)} := by
  ext x
  constructor
  · intro hx
    simp only [U33, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx.1 with rfl | rfl | rfl | rfl
    · simp
    · exfalso
      have hz := hx.2 () (by simp)
      norm_num [absLineFam, absLineDist, shift33] at hz
    · exfalso
      have hz := hx.2 () (by simp)
      norm_num [absLineFam, absLineDist, shift33] at hz
    · exfalso
      have hz := hx.2 () (by simp)
      norm_num [absLineFam, absLineDist, shift33] at hz
  · intro hx
    simp only [Set.mem_singleton_iff] at hx
    subst x
    refine ⟨by simp [U33], ?_⟩
    intro k hk; cases k
    norm_num [absLineFam, absLineDist, shift33]
theorem shift_fiber_neg1 :
    Fiber absLineFam shift33 ({()} : Set Unit) (some (-1 : ℝ)) U33 =
      {some (-2), some 0} := by
  ext x
  constructor
  · intro hx
    simp only [U33, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx.1 with rfl | rfl | rfl | rfl
    · exfalso
      have hz := hx.2 () (by simp)
      norm_num [absLineFam, absLineDist, shift33] at hz
    · simp
    · simp
    · exfalso
      have hz := hx.2 () (by simp)
      norm_num [absLineFam, absLineDist, shift33] at hz
  · intro hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · refine ⟨by simp [U33], ?_⟩
      intro k hk; cases k
      norm_num [absLineFam, absLineDist, shift33]
    · refine ⟨by simp [U33], ?_⟩
      intro k hk; cases k
      norm_num [absLineFam, absLineDist, shift33]
theorem shift_fiber_one :
    Fiber absLineFam shift33 ({()} : Set Unit) (some (1 : ℝ)) U33 =
      {some (-2), some 0} := by
  ext x
  constructor
  · intro hx
    simp only [U33, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx.1 with rfl | rfl | rfl | rfl
    · exfalso
      have hz := hx.2 () (by simp)
      norm_num [absLineFam, absLineDist, shift33] at hz
    · simp
    · simp
    · exfalso
      have hz := hx.2 () (by simp)
      norm_num [absLineFam, absLineDist, shift33] at hz
  · intro hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · refine ⟨by simp [U33], ?_⟩
      intro k hk; cases k
      norm_num [absLineFam, absLineDist, shift33]
    · refine ⟨by simp [U33], ?_⟩
      intro k hk; cases k
      norm_num [absLineFam, absLineDist, shift33]
theorem shift_fiber_three :
    Fiber absLineFam shift33 ({()} : Set Unit) (some (3 : ℝ)) U33 = {some 2} := by
  ext x
  constructor
  · intro hx
    simp only [U33, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx.1 with rfl | rfl | rfl | rfl
    · exfalso
      have hz := hx.2 () (by simp)
      norm_num [absLineFam, absLineDist, shift33] at hz
    · exfalso
      have hz := hx.2 () (by simp)
      norm_num [absLineFam, absLineDist, shift33] at hz
    · exfalso
      have hz := hx.2 () (by simp)
      norm_num [absLineFam, absLineDist, shift33] at hz
    · simp
  · intro hx
    simp only [Set.mem_singleton_iff] at hx
    subst x
    refine ⟨by simp [U33], ?_⟩
    intro k hk; cases k
    norm_num [absLineFam, absLineDist, shift33]
theorem U33_no_single_center :
    ¬ ∃ c ∈ U33, ∀ x ∈ U33, absLineDist x c < threeHalves := by
  rintro ⟨c, hc, hcov⟩
  simp only [U33, Set.mem_insert_iff, Set.mem_singleton_iff] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · have h := hcov (some 0) (by simp [U33])
    norm_num [absLineDist] at h
    exact (not_lt_of_ge threeHalves_lt_three.le) h
  · have h := hcov (some 0) (by simp [U33])
    norm_num [absLineDist] at h
    exact (not_lt_of_ge threeHalves_le_two) h
  · have h := hcov (some 2) (by simp [U33])
    norm_num [absLineDist] at h
    exact (not_lt_of_ge threeHalves_le_two) h
  · have h := hcov (some 0) (by simp [U33])
    norm_num [absLineDist] at h
    exact (not_lt_of_ge threeHalves_le_two) h
theorem U33_cover_le :
    covering_number absLineDist threeHalves U33 ≤ 2 := by
  have hnet : InternalEpsilonNet absLineDist threeHalves U33
      ({some (-2), some 0} : Finset (Option ℝ)) := by
    constructor
    · intro x hx
      simp at hx
      rcases hx with rfl | rfl <;> simp [U33]
    · intro x hx
      simp only [U33, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact ⟨some (-2), by simp, absLineDist_one_lt _ _ (by norm_num)⟩
      · exact ⟨some (-2), by simp, absLineDist_zero_lt _ _ (by norm_num)⟩
      · exact ⟨some 0, by simp, absLineDist_zero_lt _ _ (by norm_num)⟩
      · exact ⟨some (-2), by simp, absLineDist_zero_lt _ _ (by norm_num)⟩
  calc
    covering_number absLineDist threeHalves U33
        ≤ (({some (-2), some 0} : Finset (Option ℝ)).card : ENNReal) :=
          covering_number_le_card_of_net hnet
    _ = 2 := by norm_num
theorem U33_cover_ge :
    (2 : ENNReal) ≤ covering_number absLineDist threeHalves U33 := by
  have hfin : ∃ S : Finset (Option ℝ), InternalEpsilonNet absLineDist threeHalves U33 S :=
    ⟨{some (-2), some 0}, by
      constructor
      · intro x hx; simp at hx
        rcases hx with rfl | rfl <;> simp [U33]
      · intro x hx
        simp only [U33, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl | rfl
        · exact ⟨some (-2), by simp, absLineDist_one_lt _ _ (by norm_num)⟩
        · exact ⟨some (-2), by simp, absLineDist_zero_lt _ _ (by norm_num)⟩
        · exact ⟨some 0, by simp, absLineDist_zero_lt _ _ (by norm_num)⟩
        · exact ⟨some (-2), by simp, absLineDist_zero_lt _ _ (by norm_num)⟩⟩
  obtain ⟨S, hS, hcover, hmin⟩ := covering_number_attained absLineDist threeHalves U33 hfin
  have hcard : 2 ≤ S.card := by
    by_contra hnot
    have hle : S.card ≤ 1 := by omega
    have hall := Finset.card_le_one.mp hle
    rcases hS.2 (some 0) (by simp [U33]) with ⟨c0, hc0, h0⟩
    have hc0U : c0 ∈ U33 := hS.1 hc0
    have hcov : ∀ x ∈ U33, absLineDist x c0 < threeHalves := by
      intro x hx
      rcases hS.2 x hx with ⟨c, hc, hdist⟩
      have hcc0 : c = c0 := hall c hc c0 hc0
      simpa [hcc0] using hdist
    exact U33_no_single_center ⟨c0, hc0U, hcov⟩
  rw [hcover]
  exact_mod_cast hcard
theorem U33_cover_eq : covering_number absLineDist threeHalves U33 = 2 :=
  le_antisymm U33_cover_le U33_cover_ge
theorem shift_image_U33 : shift33.func '' U33 =
    ({some (-2), some (-1), some 1, some 3} : Set (Option ℝ)) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp only [U33, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> norm_num [shift33]
  · intro hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact ⟨some (-3), by simp [U33], by norm_num [shift33]⟩
    · exact ⟨some (-2), by simp [U33], by norm_num [shift33]⟩
    · exact ⟨some 0, by simp [U33], by norm_num [shift33]⟩
    · exact ⟨some 2, by simp [U33], by norm_num [shift33]⟩
theorem shift_image_cover_le :
    covering_number absLineDist threeHalves (shift33.func '' U33) ≤ 1 := by
  rw [shift_image_U33]
  have hnet : InternalEpsilonNet absLineDist threeHalves
      ({some (-2), some (-1), some 1, some 3} : Set (Option ℝ))
      ({some (-2)} : Finset (Option ℝ)) := by
    constructor
    · intro x hx; simp at hx; subst x; simp
    · intro x hx
      simp at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact ⟨some (-2), by simp, absLineDist_zero_lt _ _ (by norm_num)⟩
      · exact ⟨some (-2), by simp, absLineDist_one_lt _ _ (by norm_num)⟩
      · exact ⟨some (-2), by simp, absLineDist_one_lt _ _ (by norm_num)⟩
      · exact ⟨some (-2), by simp, absLineDist_one_lt _ _ (by norm_num)⟩
  calc
    covering_number absLineDist threeHalves
        ({some (-2), some (-1), some 1, some 3} : Set (Option ℝ))
        ≤ (({some (-2)} : Finset (Option ℝ)).card : ENNReal) :=
          covering_number_le_card_of_net hnet
    _ = 1 := by simp
theorem shift_image_cover_eq :
    covering_number absLineDist threeHalves (shift33.func '' U33) = 1 := by
  apply le_antisymm shift_image_cover_le
  exact one_le_covering_number_of_nonempty absLineDist threeHalves
    (shift33.func '' U33) (image_nonempty_of_nonempty shift33 ⟨some (-3), by simp [U33]⟩)
theorem ex33_entropy_diff :
    mappingEntropyDiff absLineFam shift33 U33 {()} {()} threeHalves = 1 := by
  unfold mappingEntropyDiff
  rw [subfamily_metric_entropy_singleton absLineFam () threeHalves U33,
    subfamily_metric_entropy_singleton absLineFam () threeHalves (shift33.func '' U33)]
  change erealSub (metric_entropy absLineDist threeHalves U33)
    (metric_entropy absLineDist threeHalves (shift33.func '' U33)) = 1
  have hU0 : covering_number absLineDist threeHalves U33 ≠ 0 :=
    covering_number_pos_of_nonempty absLineDist threeHalves U33
      ⟨some (-3), by simp [U33]⟩
  have hUtop : covering_number absLineDist threeHalves U33 ≠ ⊤ := by
    rw [U33_cover_eq]; exact ENNReal.natCast_ne_top 2
  have hI0 : covering_number absLineDist threeHalves (shift33.func '' U33) ≠ 0 :=
    covering_number_pos_of_nonempty absLineDist threeHalves (shift33.func '' U33)
      (image_nonempty_of_nonempty shift33 ⟨some (-3), by simp [U33]⟩)
  have hItop : covering_number absLineDist threeHalves (shift33.func '' U33) ≠ ⊤ := by
    rw [shift_image_cover_eq]; simp
  rw [metric_entropy_eq_coe_of_cover_finite absLineDist threeHalves U33 hU0 hUtop,
    metric_entropy_eq_coe_of_cover_finite absLineDist threeHalves (shift33.func '' U33) hI0 hItop,
    U33_cover_eq, shift_image_cover_eq, erealSub_coe_coe]
  norm_num [Real.logb]
open formal_oet.vol_01.ch_01_foundations
open Set
set_option maxHeartbeats 5000000
noncomputable def floorOp : Operator (Option ℝ) none where
  func
    | none => none
    | some x => some (if x < 1 then 0 else if x < 2 then 1 else 2)
  preserves_bot := rfl
def D1 : Set (Option ℝ) := some '' Set.Icc (0 : ℝ) (1/2)
def D2 : Set (Option ℝ) := some '' Set.Icc (9/10 : ℝ) (11/10)
def D3 : Set (Option ℝ) := {some (0 : ℝ), some 2}
def D4 : Set (Option ℝ) := some '' Set.Icc (0 : ℝ) 2
theorem mem_D1 {x : Option ℝ} :
    x ∈ D1 ↔ ∃ r : ℝ, x = some r ∧ 0 ≤ r ∧ r ≤ 1/2 := by
  unfold D1
  constructor
  · rintro ⟨r, hr, hxr⟩
    exact ⟨r, hxr.symm, hr.1, hr.2⟩
  · rintro ⟨r, rfl, hr0, hr1⟩
    exact ⟨r, ⟨hr0, hr1⟩, rfl⟩
theorem mem_D2 {x : Option ℝ} :
    x ∈ D2 ↔ ∃ r : ℝ, x = some r ∧ 9/10 ≤ r ∧ r ≤ 11/10 := by
  unfold D2
  constructor
  · rintro ⟨r, hr, hxr⟩
    exact ⟨r, hxr.symm, hr.1, hr.2⟩
  · rintro ⟨r, rfl, hr0, hr1⟩
    exact ⟨r, ⟨hr0, hr1⟩, rfl⟩
theorem mem_D3 {x : Option ℝ} :
    x ∈ D3 ↔ x = some (0 : ℝ) ∨ x = some 2 := by
  simp [D3]
theorem mem_D4 {x : Option ℝ} :
    x ∈ D4 ↔ ∃ r : ℝ, x = some r ∧ 0 ≤ r ∧ r ≤ 2 := by
  unfold D4
  constructor
  · rintro ⟨r, hr, hxr⟩
    exact ⟨r, hxr.symm, hr.1, hr.2⟩
  · rintro ⟨r, rfl, hr0, hr1⟩
    exact ⟨r, ⟨hr0, hr1⟩, rfl⟩
theorem diameter_some_Icc (a b : ℝ) (hab : a ≤ b) :
    diameterScale (fun _ : Unit => lineDist) () (some '' Set.Icc a b) =
      ENNReal.ofReal (b - a) := by
  apply le_antisymm
  · apply iSup_le
    intro x
    apply iSup_le
    intro y
    rcases x with ⟨x, hx⟩
    rcases y with ⟨y, hy⟩
    rcases hx with ⟨xr, hxr, hvalx⟩
    rcases hy with ⟨yr, hyr, hvaly⟩
    subst x
    subst y
    change lineDist (some xr) (some yr) ≤ ENNReal.ofReal (b - a)
    rw [lineDist_some_some]
    apply ENNReal.ofReal_le_ofReal
    rw [abs_sub_le_iff]
    exact ⟨by linarith [hxr.2, hyr.1], by linarith [hxr.1, hyr.2]⟩
  · have hx : some a ∈ some '' Set.Icc a b := ⟨a, ⟨le_rfl, hab⟩, rfl⟩
    have hy : some b ∈ some '' Set.Icc a b := ⟨b, ⟨hab, le_rfl⟩, rfl⟩
    calc
      ENNReal.ofReal (b - a) = lineDist (some a) (some b) := by
        rw [lineDist_some_some, abs_of_nonpos (by linarith)]
        ring_nf
      _ ≤ diameterScale (fun _ : Unit => lineDist) () (some '' Set.Icc a b) := by
        exact le_iSup_of_le (⟨some a, hx⟩ : {x : Option ℝ // x ∈ some '' Set.Icc a b})
          (le_iSup_of_le (⟨some b, hy⟩ : {x : Option ℝ // x ∈ some '' Set.Icc a b}) le_rfl)
theorem diameter_D1 : diameterScale (fun _ : Unit => lineDist) () D1 = ENNReal.ofReal (1/2 : ℝ) := by
  rw [D1, diameter_some_Icc 0 (1/2) (by norm_num)]
  ring_nf
theorem diameter_D2 : diameterScale (fun _ : Unit => lineDist) () D2 = ENNReal.ofReal (1/5 : ℝ) := by
  rw [D2, diameter_some_Icc (9/10) (11/10) (by norm_num)]
  ring_nf
theorem diameter_D4 : diameterScale (fun _ : Unit => lineDist) () D4 = (2 : ENNReal) := by
  rw [D4, diameter_some_Icc 0 2 (by norm_num)]
  norm_num
theorem diameter_D3 : diameterScale (fun _ : Unit => lineDist) () D3 = (2 : ENNReal) := by
  apply le_antisymm
  · apply iSup_le
    intro x
    apply iSup_le
    intro y
    rcases x with ⟨x, hx⟩
    rcases y with ⟨y, hy⟩
    simp only [D3, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> norm_num [lineDist]
  · exact le_iSup_of_le (⟨some 0, by simp [D3]⟩ : {x : Option ℝ // x ∈ D3})
      (le_iSup_of_le (⟨some 2, by simp [D3]⟩ : {y : Option ℝ // y ∈ D3}) (by norm_num [lineDist]))
open formal_oet.vol_01.ch_01_foundations
open Set
theorem floorOp_zero : floorOp.func (some (0:ℝ)) = some 0 := by norm_num [floorOp]
theorem floorOp_one : floorOp.func (some (1:ℝ)) = some 1 := by norm_num [floorOp]
theorem floorOp_two : floorOp.func (some (2:ℝ)) = some 2 := by norm_num [floorOp]
theorem floorOp_of_nonneg_lt_one {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) :
    floorOp.func (some x) = some 0 := by
  simp [floorOp, h1]
theorem pointwiseRadius_eq_zero_of_no_legal
    (y : Option ℝ) (U : Set (Option ℝ))
    (h : ∀ r : ENNReal, LegalRadius lineDist (fun a b => lineDist a b = 0)
      floorOp y U r → False) :
    pointwiseRadius lineDist (fun a b => lineDist a b = 0) floorOp y U = 0 := by
  apply le_antisymm
  · unfold pointwiseRadius
    apply iSup_le
    intro r
    exact False.elim (h r r.2)
  · exact zero_le _
theorem pointwise_D2_one_zero :
    pointwiseRadius lineDist (fun a b => lineDist a b = 0) floorOp (some 1) D2 = 0 := by
  apply pointwiseRadius_eq_zero_of_no_legal
  intro r hr
  have hrrealpos : 0 < r.toReal := ENNReal.toReal_pos (ne_of_gt hr.1) hr.2.1
  let a : ℝ := min (r.toReal / 2) (1/10)
  have hapos : 0 < a := lt_min (by linarith) (by norm_num)
  have hahalf : a ≤ 1/10 := min_le_right _ _
  have har : a < r.toReal := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  let x : ℝ := 1 - a
  have hxU : some x ∈ D2 := by
    rw [mem_D2]
    refine ⟨x, rfl, ?_, ?_⟩ <;> dsimp [x] <;> linarith
  have hxl : x < 1 := by dsimp [x]; linarith
  have hx0 : 0 ≤ x := by dsimp [x]; linarith
  have hdist : lineDist (some x) (some 1) < r := by
    rw [lineDist_some_some]
    apply (ENNReal.ofReal_lt_iff_lt_toReal (abs_nonneg _) hr.2.1).mpr
    have : |x - 1| = a := by
      rw [abs_of_neg]
      · dsimp [x]; ring
      · dsimp [x]; linarith
    rw [this]
    exact har
  have hzero := hr.2.2 (some x) hxU hdist
  change lineDist (floorOp.func (some x)) (floorOp.func (some 1)) = 0 at hzero
  rw [floorOp_of_nonneg_lt_one hx0 hxl, floorOp_one] at hzero
  have hone : lineDist (some (0:ℝ)) (some 1) = 1 := by norm_num [lineDist]
  rw [hone] at hzero
  norm_num at hzero
theorem pointwise_D4_one_zero :
    pointwiseRadius lineDist (fun a b => lineDist a b = 0) floorOp (some 1) D4 = 0 := by
  apply pointwiseRadius_eq_zero_of_no_legal
  intro r hr
  have hrrealpos : 0 < r.toReal := ENNReal.toReal_pos (ne_of_gt hr.1) hr.2.1
  let a : ℝ := min (r.toReal / 2) (1/2)
  have hapos : 0 < a := lt_min (by linarith) (by norm_num)
  have hahalf : a ≤ 1/2 := min_le_right _ _
  have har : a < r.toReal := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  let x : ℝ := 1 - a
  have hxU : some x ∈ D4 := by
    rw [mem_D4]
    refine ⟨x, rfl, ?_, ?_⟩ <;> dsimp [x] <;> linarith
  have hxl : x < 1 := by dsimp [x]; linarith
  have hx0 : 0 ≤ x := by dsimp [x]; linarith
  have hdist : lineDist (some x) (some 1) < r := by
    rw [lineDist_some_some]
    apply (ENNReal.ofReal_lt_iff_lt_toReal (abs_nonneg _) hr.2.1).mpr
    have : |x - 1| = a := by
      rw [abs_of_neg]
      · dsimp [x]; ring
      · dsimp [x]; linarith
    rw [this]
    exact har
  have hzero := hr.2.2 (some x) hxU hdist
  change lineDist (floorOp.func (some x)) (floorOp.func (some 1)) = 0 at hzero
  rw [floorOp_of_nonneg_lt_one hx0 hxl, floorOp_one] at hzero
  have hone : lineDist (some (0:ℝ)) (some 1) = 1 := by norm_num [lineDist]
  rw [hone] at hzero
  norm_num at hzero
open formal_oet.vol_01.ch_01_foundations
open Set
theorem pointwise_D3_zero :
    pointwiseRadius lineDist (fun a b => lineDist a b = 0) floorOp (some 0) D3 = 2 := by
  apply le_antisymm
  · unfold pointwiseRadius
    apply iSup_le
    intro rsub
    rcases rsub with ⟨r, hlegal⟩
    rcases hlegal with ⟨hr0, hrtop, hall⟩
    by_contra hnot
    have hlt : (2 : ENNReal) < r := lt_of_not_ge hnot
    have hx : some (2:ℝ) ∈ D3 := by simp [D3]
    have hdist : lineDist (some 2) (some 0) < r := by norm_num [lineDist]; exact hlt
    have hzero := hall (some 2) hx hdist
    change lineDist (floorOp.func (some 2)) (floorOp.func (some 0)) = 0 at hzero
    rw [floorOp_two, floorOp_zero] at hzero
    have htwo : lineDist (some (2:ℝ)) (some 0) = 2 := by norm_num [lineDist]
    rw [htwo] at hzero
    norm_num at hzero
  · apply le_pointwiseRadius_of_legal
    refine ⟨by norm_num, by norm_num, ?_⟩
    intro x hx hlt
    simp only [D3, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · rw [floorOp_zero]
      norm_num [lineDist]
    · exfalso
      norm_num [lineDist] at hlt
theorem pointwise_D3_two :
    pointwiseRadius lineDist (fun a b => lineDist a b = 0) floorOp (some 2) D3 = 2 := by
  apply le_antisymm
  · unfold pointwiseRadius
    apply iSup_le
    intro rsub
    rcases rsub with ⟨r, hlegal⟩
    rcases hlegal with ⟨hr0, hrtop, hall⟩
    by_contra hnot
    have hlt : (2 : ENNReal) < r := lt_of_not_ge hnot
    have hx : some (0:ℝ) ∈ D3 := by simp [D3]
    have hdist : lineDist (some 0) (some 2) < r := by norm_num [lineDist]; exact hlt
    have hzero := hall (some 0) hx hdist
    change lineDist (floorOp.func (some 0)) (floorOp.func (some 2)) = 0 at hzero
    rw [floorOp_zero, floorOp_two] at hzero
    have htwo : lineDist (some (0:ℝ)) (some 2) = 2 := by norm_num [lineDist]
    rw [htwo] at hzero
    norm_num at hzero
  · apply le_pointwiseRadius_of_legal
    refine ⟨by norm_num, by norm_num, ?_⟩
    intro x hx hlt
    simp only [D3, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exfalso
      norm_num [lineDist] at hlt
    · rw [floorOp_two]
      norm_num [lineDist]
theorem zeroing_D3 : zeroingMatrix (fun _ : Unit => lineDist) floorOp D3 () () = 2 := by
  unfold zeroingMatrix unifiedRadius
  apply le_antisymm
  · calc
      (⨅ y : {y : Option ℝ // y ∈ D3},
          pointwiseRadius lineDist (fun a b => lineDist a b = 0) floorOp y.1 D3)
          ≤ pointwiseRadius lineDist (fun a b => lineDist a b = 0) floorOp (some 0) D3 :=
            iInf_le _ (⟨some 0, by simp [D3]⟩ : {y : Option ℝ // y ∈ D3})
      _ = 2 := pointwise_D3_zero
  · apply le_iInf
    intro y
    have hy : y.1 = some (0:ℝ) ∨ y.1 = some 2 := by
      simpa only [D3, Set.mem_insert_iff, Set.mem_singleton_iff] using y.2
    rcases hy with h | h
    · rw [h]; exact pointwise_D3_zero.ge
    · rw [h]; exact pointwise_D3_two.ge
theorem zeroing_D2_zero : zeroingMatrix (fun _ : Unit => lineDist) floorOp D2 () () = 0 := by
  apply le_antisymm
  · calc
      zeroingMatrix (fun _ : Unit => lineDist) floorOp D2 () ()
          ≤ pointwiseRadius lineDist (fun a b => lineDist a b = 0) floorOp (some 1) D2 := by
            unfold zeroingMatrix unifiedRadius
            exact iInf_le _ (⟨some 1, by rw [mem_D2]; exact ⟨1, rfl, by norm_num, by norm_num⟩⟩ : {y : Option ℝ // y ∈ D2})
      _ = 0 := pointwise_D2_one_zero
  · exact zero_le _
theorem zeroing_D4_zero : zeroingMatrix (fun _ : Unit => lineDist) floorOp D4 () () = 0 := by
  apply le_antisymm
  · calc
      zeroingMatrix (fun _ : Unit => lineDist) floorOp D4 () ()
          ≤ pointwiseRadius lineDist (fun a b => lineDist a b = 0) floorOp (some 1) D4 := by
            unfold zeroingMatrix unifiedRadius
            exact iInf_le _ (⟨some 1, by rw [mem_D4]; exact ⟨1, rfl, by norm_num, by norm_num⟩⟩ : {y : Option ℝ // y ∈ D4})
      _ = 0 := pointwise_D4_one_zero
  · exact zero_le _
theorem zeroing_D1_top : zeroingMatrix (fun _ : Unit => lineDist) floorOp D1 () () = ⊤ := by
  apply le_antisymm le_top
  apply le_iInf
  intro y
  change ⊤ ≤ pointwiseRadius lineDist (fun a b => lineDist a b = 0) floorOp y.1 D1
  exact top_le_iff.mpr (pointwiseRadius_eq_top_iff.mpr (by
  intro r hr0 hrtop
  refine ⟨hr0, hrtop, ?_⟩
  intro x hx _
  change lineDist (floorOp.func x) (floorOp.func y.1) = 0
  rcases mem_D1.mp hx with ⟨xr, rfl, hx0, hx1⟩
  rcases mem_D1.mp y.2 with ⟨yr, hys, hy0, hy1⟩
  have hyr : y.1 = some yr := hys
  rw [hyr]
  rw [floorOp_of_nonneg_lt_one hx0 (by linarith),
    floorOp_of_nonneg_lt_one hy0 (by linarith)]
  norm_num [lineDist]))
open formal_oet.vol_01.ch_01_foundations
open Set
noncomputable def diameterScaleFamily : InputScaleFamily (Option ℝ) Unit where
  scale := fun _ => diameterScale (fun _ : Unit => lineDist) ()
  mono := by
    intro _ A B hAB
    exact diameterScale_mono (fun _ : Unit => lineDist) () hAB
theorem ofReal_half_lt_one : ENNReal.ofReal (1/2 : ℝ) < (1 : ENNReal) := by
  rw [show (1:ENNReal) = ENNReal.ofReal (1:ℝ) by simp]
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0:ℝ)<1)).mpr (by norm_num)
theorem ofReal_fifth_lt_one : ENNReal.ofReal (1/5 : ℝ) < (1 : ENNReal) := by
  rw [show (1:ENNReal) = ENNReal.ofReal (1:ℝ) by simp]
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0:ℝ)<1)).mpr (by norm_num)
theorem type_D1 :
    thresholdType diameterScaleFamily 1 1 (fun _ : Unit => lineDist) floorOp D1 () () = (true, true) := by
  have h1 : diameterScaleFamily.scale () D1 < (1 : ENNReal) := by
    change diameterScale (fun _ : Unit => lineDist) () D1 < 1
    rw [diameter_D1]
    exact ofReal_half_lt_one
  have h2 : (1 : ENNReal) ≤ zeroingMatrix (fun _ : Unit => lineDist) floorOp D1 () () := by
    rw [zeroing_D1_top]; exact le_top
  simp [thresholdType, h1, h2]
theorem type_D2 :
    thresholdType diameterScaleFamily 1 1 (fun _ : Unit => lineDist) floorOp D2 () () = (true, false) := by
  have h1 : diameterScaleFamily.scale () D2 < (1 : ENNReal) := by
    change diameterScale (fun _ : Unit => lineDist) () D2 < 1
    rw [diameter_D2]
    exact ofReal_fifth_lt_one
  have h2 : ¬ (1 : ENNReal) ≤ zeroingMatrix (fun _ : Unit => lineDist) floorOp D2 () () := by
    rw [zeroing_D2_zero]
    norm_num
  simp [thresholdType, h1, h2]
theorem type_D3 :
    thresholdType diameterScaleFamily 1 1 (fun _ : Unit => lineDist) floorOp D3 () () = (false, true) := by
  have h1 : ¬ diameterScaleFamily.scale () D3 < (1 : ENNReal) := by
    change ¬ diameterScale (fun _ : Unit => lineDist) () D3 < 1
    rw [diameter_D3]
    norm_num
  have h2 : (1 : ENNReal) ≤ zeroingMatrix (fun _ : Unit => lineDist) floorOp D3 () () := by
    rw [zeroing_D3]
    norm_num
  simp [thresholdType, h1, h2]
theorem type_D4 :
    thresholdType diameterScaleFamily 1 1 (fun _ : Unit => lineDist) floorOp D4 () () = (false, false) := by
  have h1 : ¬ diameterScaleFamily.scale () D4 < (1 : ENNReal) := by
    change ¬ diameterScale (fun _ : Unit => lineDist) () D4 < 1
    rw [diameter_D4]
    norm_num
  have h2 : ¬ (1 : ENNReal) ≤ zeroingMatrix (fun _ : Unit => lineDist) floorOp D4 () () := by
    rw [zeroing_D4_zero]
    norm_num
  simp [thresholdType, h1, h2]
theorem radius_D3_ge_one : (1 : ENNReal) ≤ zeroingMatrix (fun _ : Unit => lineDist) floorOp D3 () () := by
  rw [zeroing_D3]; norm_num
theorem D3_radius_not_forall_zero :
    (1 : ENNReal) ≤ zeroingMatrix (fun _ : Unit => lineDist) floorOp D3 () () ∧
      ¬ (∀ x ∈ D3, ∀ y ∈ D3,
        lineDist (floorOp.func x) (floorOp.func y) = 0) := by
  constructor
  · exact radius_D3_ge_one
  · intro h
    have h02 := h (some 0) (by simp [D3]) (some 2) (by simp [D3])
    rw [floorOp_zero, floorOp_two] at h02
    have htwo : lineDist (some (0:ℝ)) (some 2) = 2 := by norm_num [lineDist]
    rw [htwo] at h02
    norm_num at h02
open formal_oet.vol_01.ch_01_foundations
open Set
theorem floorOp_eq_floor_D1 {x : ℝ} (hx : some x ∈ D1) :
    floorOp.func (some x) = some (Int.floor x : ℝ) := by
  rcases mem_D1.mp hx with ⟨r, hxr, h0, h1⟩
  injection hxr with hxr
  subst r
  have hxlt : x < 1 := by linarith
  have hfloor : Int.floor x = (0:ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num <;> linarith
  rw [floorOp_of_nonneg_lt_one h0 hxlt, hfloor]
  norm_num
theorem floorOp_eq_floor_D2 {x : ℝ} (hx : some x ∈ D2) :
    floorOp.func (some x) = some (Int.floor x : ℝ) := by
  rcases mem_D2.mp hx with ⟨r, hxr, h0, h1⟩
  injection hxr with hxr
  subst r
  by_cases hx1 : x < 1
  · have hfloor : Int.floor x = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num <;> linarith
    rw [floorOp_of_nonneg_lt_one (by linarith) hx1, hfloor]
    norm_num
  · have hxge : 1 ≤ x := le_of_not_gt hx1
    have hxlt2 : x < 2 := by linarith
    have hfloor : Int.floor x = (1:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num <;> linarith
    simp [floorOp, hx1, hxlt2, hfloor]
theorem floorOp_eq_floor_D3 {x : ℝ} (hx : some x ∈ D3) :
    floorOp.func (some x) = some (Int.floor x : ℝ) := by
  rcases mem_D3.mp hx with hx0 | hx2
  · injection hx0 with hx0
    subst x
    norm_num [floorOp]
  · injection hx2 with hx2
    subst x
    norm_num [floorOp]
theorem floorOp_eq_floor_D4 {x : ℝ} (hx : some x ∈ D4) :
    floorOp.func (some x) = some (Int.floor x : ℝ) := by
  rcases mem_D4.mp hx with ⟨r, hxr, h0, h1⟩
  injection hxr with hxr
  subst r
  by_cases hx1 : x < 1
  · have hfloor : Int.floor x = (0:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num <;> linarith
    rw [floorOp_of_nonneg_lt_one h0 hx1, hfloor]
    norm_num
  · have hxge : 1 ≤ x := le_of_not_gt hx1
    by_cases hx2 : x < 2
    · have hfloor : Int.floor x = (1:ℤ) := by
        apply Int.floor_eq_iff.mpr
        constructor <;> norm_num <;> linarith
      simp [floorOp, hx1, hx2, hfloor]
    · have hxeq : x = 2 := by linarith
      subst x
      norm_num [floorOp]
open formal_oet.vol_01.ch_01_foundations
open Set
set_option maxHeartbeats 8000000
def d4 (x y : Fin 4) : ENNReal :=
  ((if x.val ≤ y.val then y.val - x.val else x.val - y.val : ℕ) : ENNReal)
theorem d4_symm (x y : Fin 4) : d4 x y = d4 y x := by
  fin_cases x <;> fin_cases y <;> norm_num [d4]
theorem d4_triangle (x y z : Fin 4) : d4 x z ≤ d4 x y + d4 y z := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;> norm_num [d4]
def f4 (x : Fin 4) : Fin 4 := x
def g4 (x : Fin 4) : Fin 4 := ![0, 3, 1, 2] x
def U4 : Set (Fin 4) := Set.univ
@[simp] theorem mem_U4 (x : Fin 4) : x ∈ U4 := by simp [U4]
theorem d4_lt_one_eq {x y : Fin 4} (h : d4 x y < (1 : ENNReal)) : x = y := by
  fin_cases x <;> fin_cases y <;> simp [d4] at h ⊢
  all_goals exact (not_lt_of_ge (by norm_num : (2 : ENNReal) ≤ 3)) h <;> omega
theorem d4_lt_two_eq_or {x y : Fin 4} (h : d4 x y < (2 : ENNReal)) :
    d4 x y = 0 ∨ d4 x y = 1 := by
  fin_cases x <;> fin_cases y <;> simp [d4] at h ⊢
  all_goals exact (not_lt_of_ge (by norm_num : (2 : ENNReal) ≤ 3)) h
theorem U4_cover_four {ε : ENNReal} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    covering_number d4 ε U4 = 4 := by
  have hnet : InternalEpsilonNet d4 ε U4 (Finset.univ : Finset (Fin 4)) := by
    constructor
    · intro x hx; simp
    · intro x hx
      refine ⟨x, by simp, ?_⟩
      have : d4 x x = 0 := by simp [d4]
      rw [this]
      exact hε0
  apply le_antisymm
  · calc
      covering_number d4 ε U4 ≤ ((Finset.univ : Finset (Fin 4)).card : ENNReal) :=
        covering_number_le_card_of_net hnet
      _ = 4 := by simp
  · by_contra hnot
    have hlt : covering_number d4 ε U4 < (4 : ENNReal) := lt_of_not_ge hnot
    have hfin : ∃ S : Finset (Fin 4), InternalEpsilonNet d4 ε U4 S :=
      ⟨Finset.univ, hnet⟩
    obtain ⟨S, hS, hcover, hmin⟩ := covering_number_attained d4 ε U4 hfin
    have hsub : (Finset.univ : Finset (Fin 4)) ⊆ S := by
      intro x _
      rcases hS.2 x (by simp) with ⟨c, hc, hdist⟩
      have hcx : c = x := by
        symm
        exact d4_lt_one_eq (lt_of_lt_of_le hdist hε1)
      simpa [hcx] using hc
    have hcard : (4 : ℕ) ≤ S.card := by
      simpa using Finset.card_le_card hsub
    have : (4 : ENNReal) ≤ covering_number d4 ε U4 := by
      rw [hcover]
      exact_mod_cast hcard
    exact (not_lt_of_ge this) hlt
theorem no_single_cover_two (c : Fin 4) :
    ∃ x : Fin 4, ¬ d4 x c < (2 : ENNReal) := by
  fin_cases c
  · exact ⟨3, by norm_num [d4]⟩
  · exact ⟨3, by norm_num [d4]⟩
  · exact ⟨0, by norm_num [d4]⟩
  · exact ⟨0, by norm_num [d4]⟩
theorem U4_cover_two {ε : ENNReal} (hε0 : 0 < ε) (hε1 : 1 < ε) (hε2 : ε ≤ 2) :
    covering_number d4 ε U4 = 2 := by
  have hnet : InternalEpsilonNet d4 ε U4 ({1, 3} : Finset (Fin 4)) := by
    constructor
    · intro x hx
      simp at hx
      rcases hx with rfl | rfl <;> simp
    · intro x hx
      fin_cases x
      · refine ⟨1, by simp, ?_⟩
        norm_num [d4]
        exact hε1
      · refine ⟨1, by simp, ?_⟩
        norm_num [d4]
        exact hε0
      · refine ⟨1, by simp, ?_⟩
        norm_num [d4]
        exact hε1
      · refine ⟨3, by simp, ?_⟩
        norm_num [d4]
        exact hε0
  apply le_antisymm
  · calc
      covering_number d4 ε U4 ≤ (({1, 3} : Finset (Fin 4)).card : ENNReal) :=
        covering_number_le_card_of_net hnet
      _ = 2 := by simp
  · by_contra hnot
    have hlt : covering_number d4 ε U4 < (2 : ENNReal) := lt_of_not_ge hnot
    have hfin : ∃ S : Finset (Fin 4), InternalEpsilonNet d4 ε U4 S :=
      ⟨{1, 3}, hnet⟩
    obtain ⟨S, hS, hcover, hmin⟩ := covering_number_attained d4 ε U4 hfin
    have hcardlt : S.card < 2 := by
      have : (S.card : ENNReal) < (2 : ENNReal) := by
        rw [← hcover]; exact hlt
      exact_mod_cast this
    have hle : S.card ≤ 1 := by omega
    have hall := Finset.card_le_one.mp hle
    rcases hS.2 0 (by simp) with ⟨c0, hc0, _⟩
    have hcov : ∀ x : Fin 4, d4 x c0 < ε := by
      intro x
      rcases hS.2 x (by simp) with ⟨c, hc, hdist⟩
      have hcc0 : c = c0 := hall c hc c0 hc0
      simpa [hcc0] using hdist
    rcases no_single_cover_two c0 with ⟨x, hnotlt⟩
    exact hnotlt (lt_of_lt_of_le (hcov x) hε2)
theorem U4_cover_one {ε : ENNReal} (hε2 : 2 < ε) :
    covering_number d4 ε U4 = 1 := by
  have hnet : InternalEpsilonNet d4 ε U4 ({1} : Finset (Fin 4)) := by
    constructor
    · intro x hx; simp at hx; subst x; simp
    · intro x hx
      fin_cases x
      · refine ⟨1, by simp, ?_⟩
        norm_num [d4]
        exact lt_trans (by norm_num : (1:ENNReal) < 2) hε2
      · refine ⟨1, by simp, ?_⟩
        norm_num [d4]
        exact lt_trans (by norm_num : (0:ENNReal) < 2) hε2
      · refine ⟨1, by simp, ?_⟩
        norm_num [d4]
        exact lt_trans (by norm_num : (1:ENNReal) < 2) hε2
      · refine ⟨1, by simp, ?_⟩
        norm_num [d4]
        exact hε2
  apply le_antisymm
  · calc
      covering_number d4 ε U4 ≤ (({1} : Finset (Fin 4)).card : ENNReal) :=
        covering_number_le_card_of_net hnet
      _ = 1 := by simp
  · exact one_le_covering_number_of_nonempty d4 ε U4 ⟨0, by simp⟩
theorem f4_image : f4 '' U4 = U4 := by
  ext x; simp [f4, U4]
theorem g4_image : g4 '' U4 = U4 := by
  ext x
  constructor
  · rintro ⟨y, -, rfl⟩
    fin_cases y <;> simp [g4]
  · intro hx
    fin_cases x
    · refine ⟨0, by simp, ?_⟩; decide
    · refine ⟨2, by simp, ?_⟩; decide
    · refine ⟨3, by simp, ?_⟩; decide
    · refine ⟨1, by simp, ?_⟩; decide
noncomputable def sevenQuarters : ENNReal := ((7/4 : NNReal) : ENNReal)
noncomputable def sevenTwelfths : ENNReal := ((7/12 : NNReal) : ENNReal)
theorem one_lt_sevenQuarters : (1 : ENNReal) < sevenQuarters := by
  unfold sevenQuarters
  exact_mod_cast (by norm_num : (1 : NNReal) < 7/4)
theorem sevenQuarters_le_two : sevenQuarters ≤ (2 : ENNReal) := by
  unfold sevenQuarters
  change ((7/4 : NNReal) : ENNReal) ≤ ((2 : NNReal) : ENNReal)
  exact_mod_cast (by
    rw [div_le_iff₀ (by norm_num : (0 : NNReal) < 4)]
    norm_num : (7/4 : NNReal) ≤ 2)
theorem sevenTwelfths_le_one : sevenTwelfths ≤ (1 : ENNReal) := by
  unfold sevenTwelfths
  change ((7/12 : NNReal) : ENNReal) ≤ ((1 : NNReal) : ENNReal)
  exact_mod_cast (by
    rw [div_le_iff₀ (by norm_num : (0 : NNReal) < 12)]
    norm_num : (7/12 : NNReal) ≤ 1)
theorem zero_lt_sevenTwelfths : (0 : ENNReal) < sevenTwelfths := by
  unfold sevenTwelfths
  exact_mod_cast (by norm_num : (0 : NNReal) < 7/12)
theorem U4_cover_sevenQuarters : covering_number d4 sevenQuarters U4 = 2 := by
  apply U4_cover_two
  · exact lt_trans zero_lt_one one_lt_sevenQuarters
  · exact one_lt_sevenQuarters
  · exact sevenQuarters_le_two
theorem f4_cover_sevenQuarters : covering_number d4 sevenQuarters (f4 '' U4) = 2 := by
  rw [f4_image]; exact U4_cover_sevenQuarters
theorem g4_cover_sevenQuarters : covering_number d4 sevenQuarters (g4 '' U4) = 2 := by
  rw [g4_image]; exact U4_cover_sevenQuarters
def FuncLip (d : X → X → ENNReal) (f : X → X) (U : Set X) (L : ENNReal) : Prop :=
  ∀ x ∈ U, ∀ y ∈ U, d (f x) (f y) ≤ L * d x y
theorem f4_lip_one : FuncLip d4 f4 U4 1 := by
  intro x hx y hy
  simp [f4]
theorem g4_lip_three : FuncLip d4 g4 U4 3 := by
  intro x hx y hy
  fin_cases x <;> fin_cases y <;> norm_num [d4, g4]
theorem f4_lip_min : ∀ L : ENNReal, FuncLip d4 f4 U4 L → (1 : ENNReal) ≤ L := by
  intro L hL
  have h := hL 0 (by simp) 1 (by simp)
  simpa [d4, f4] using h
theorem g4_lip_min : ∀ L : ENNReal, FuncLip d4 g4 U4 L → (3 : ENNReal) ≤ L := by
  intro L hL
  have h := hL 0 (by simp) 1 (by simp)
  simpa [d4, g4] using h
theorem U4_cover_sevenTwelfths : covering_number d4 sevenTwelfths U4 = 4 := by
  exact U4_cover_four zero_lt_sevenTwelfths sevenTwelfths_le_one
noncomputable def FuncEntropyDiff (d : X → X → ENNReal) (f : X → X)
    (U : Set X) (ε : ENNReal) : EReal :=
  erealSub (metric_entropy d ε U) (metric_entropy d ε (f '' U))
theorem f4_entropy_diff_zero : FuncEntropyDiff d4 f4 U4 sevenQuarters = 0 := by
  unfold FuncEntropyDiff
  rw [f4_image]
  exact erealSub_self _
theorem g4_entropy_diff_zero : FuncEntropyDiff d4 g4 U4 sevenQuarters = 0 := by
  unfold FuncEntropyDiff
  rw [g4_image]
  exact erealSub_self _
theorem ex35_lip_cover_comparison :
    covering_number d4 sevenQuarters (f4 '' U4) ≤
        covering_number d4 sevenQuarters U4 ∧
      covering_number d4 sevenQuarters (g4 '' U4) ≤
        covering_number d4 sevenTwelfths U4 ∧
      covering_number d4 sevenQuarters (f4 '' U4) = 2 ∧
      covering_number d4 sevenQuarters (g4 '' U4) = 2 ∧
      covering_number d4 sevenTwelfths U4 = 4 := by
  refine ⟨?_, ?_, f4_cover_sevenQuarters, g4_cover_sevenQuarters, U4_cover_sevenTwelfths⟩
  · rw [f4_cover_sevenQuarters, U4_cover_sevenQuarters]
  · rw [g4_cover_sevenQuarters, U4_cover_sevenTwelfths]
    norm_num
open formal_oet.vol_01.ch_01_foundations
open Set
def e35 (i : Fin 4) : Option ℝ := some (i.val : ℝ)
def realU35 : Set (Option ℝ) := {some (0:ℝ), some 1, some 2, some 3}
def fReal35 : Option ℝ → Option ℝ := id
noncomputable def gReal35 : Option ℝ → Option ℝ
  | none => none
  | some x =>
      if x = 0 then some 0
      else if x = 1 then some 3
      else if x = 2 then some 1
      else if x = 3 then some 2
      else none
theorem e35_injective : Function.Injective e35 := by
  intro x y h
  have hv : (x.val : ℝ) = y.val := by
    simpa [e35] using Option.some.inj h
  apply Fin.ext
  exact_mod_cast hv
theorem e35_image : e35 '' (Set.univ : Set (Fin 4)) = realU35 := by
  ext z
  constructor
  · rintro ⟨i, -, rfl⟩
    fin_cases i <;> simp [e35, realU35]
  · intro hz
    simp only [realU35, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact ⟨0, by simp, by simp [e35]⟩
    · exact ⟨1, by simp, by simp [e35]⟩
    · exact ⟨2, by simp, by simp [e35]⟩
    · exact ⟨3, by simp, by simp [e35]⟩
theorem e35_isometry (x y : Fin 4) :
    lineDist (e35 x) (e35 y) = d4 x y := by
  fin_cases x <;> fin_cases y <;> norm_num [e35, lineDist, d4]
theorem e35_comm_f : ∀ x : Fin 4, e35 (f4 x) = fReal35 (e35 x) := by
  intro x; simp [f4, fReal35, e35]
theorem e35_comm_g : ∀ x : Fin 4, e35 (g4 x) = gReal35 (e35 x) := by
  intro x
  fin_cases x <;> simp [g4, gReal35, e35]
theorem three_halves_not_in_realU35 :
    some ((3/2 : ℝ)) ∉ realU35 := by
  simp [realU35]
  norm_num
theorem ex35_finite_model_alignment :
    Function.Injective e35 ∧
      e35 '' (Set.univ : Set (Fin 4)) = realU35 ∧
      (∀ x y : Fin 4, lineDist (e35 x) (e35 y) = d4 x y) ∧
      (∀ x : Fin 4, e35 (f4 x) = fReal35 (e35 x)) ∧
      (∀ x : Fin 4, e35 (g4 x) = gReal35 (e35 x)) ∧
      some ((3/2 : ℝ)) ∉ realU35 :=
  ⟨e35_injective, e35_image, e35_isometry, e35_comm_f, e35_comm_g,
    three_halves_not_in_realU35⟩

end formal_oet.vol_01.ch_03_operator_local_degeneracy
