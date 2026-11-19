import Chapter.Cover

open formal_oet.vol_01.ch_01_foundations
open scoped ENNReal
namespace Chapter

variable {Y Z : Type}

def extendDistance (D : Y → Y → ℝ≥0∞) : Option Y → Option Y → ℝ≥0∞
  | none, none => 0
  | some x, some y => D x y
  | _, _ => ⊤

theorem extend_legal [Nonempty Y] {D : Y → Y → ℝ≥0∞}
    (hs : ∀ x, D x x = 0) (hm : ∀ x y, D x y = D y x)
    (ht : ∀ x y z, D x z ≤ D x y + D y z) :
    ExtendedPseudoMetric (Option Y) none (extendDistance D) where
  nonabsorbing := Nonempty.elim inferInstance fun y : Y => ⟨some y, Option.some_ne_none _⟩
  dist_self x := by cases x <;> simp [extendDistance, hs]
  symm x y := by cases x <;> cases y <;> simp [extendDistance, hm]
  triangle x y z := by
    cases x <;> cases y <;> cases z <;> simp [extendDistance, ht]
  isolate_bot x hx := by cases x <;> simp_all [extendDistance]

noncomputable def discreteReadout [DecidableEq Z] (q : Y → Z) (a : ℝ≥0∞) (x y : Y) :
    ℝ≥0∞ := if q x = q y then 0 else a

theorem discrete_legal [Nonempty Y] [DecidableEq Z] (q : Y → Z) (a : ℝ≥0∞) :
    ExtendedPseudoMetric (Option Y) none (extendDistance (discreteReadout q a)) := by
  apply extend_legal
  · simp [discreteReadout]
  · intro x y
    simp [discreteReadout, eq_comm]
  · intro x y z
    by_cases h : q x = q y
    · simp [discreteReadout, h]
    · simpa only [discreteReadout, if_neg h] using
        (le_add_right (show (if q x = q z then 0 else a) ≤ a by split <;> simp) :
          (if q x = q z then 0 else a) ≤ a + (if q y = q z then 0 else a))

def liftRealMap (F : ℝ → ℝ) : Operator (Option ℝ) none :=
  ⟨Option.map F, rfl⟩

theorem liftReal_domain (F : ℝ → ℝ) :
    dom (liftRealMap F) = Set.range (some : ℝ → Option ℝ) := by
  ext x
  cases x <;> simp [dom, liftRealMap]

noncomputable def readDistance (q : ℝ → ℝ) : Option ℝ → Option ℝ → ℝ≥0∞ :=
  extendDistance fun x y => ENNReal.ofReal |q x - q y|

@[simp] theorem read_some (q : ℝ → ℝ) (x y : ℝ) :
    readDistance q (some x) (some y) = ENNReal.ofReal |q x - q y| := rfl

theorem read_legal (q : ℝ → ℝ) : ExtendedPseudoMetric (Option ℝ) none (readDistance q) := by
  apply extend_legal
  · simp
  · intro x y
    rw [abs_sub_comm]
  · intro x y z
    rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (abs_sub_le _ _ _)

@[simp] theorem read_zero_iff (q : ℝ → ℝ) (x y : ℝ) :
    readDistance q (some x) (some y) = 0 ↔ q x = q y := by
  rw [read_some, ENNReal.ofReal_eq_zero]
  exact ⟨fun h => sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h (abs_nonneg _))),
    fun h => by simp [h]⟩

noncomputable def realDist := readDistance id
noncomputable def absDist := readDistance abs

@[simp] theorem real_some (x y : ℝ) : realDist (some x) (some y) = ENNReal.ofReal |x-y| := rfl

@[simp] theorem real_zero (x y : ℝ) : realDist (some x) (some y) = 0 ↔ x = y :=
  read_zero_iff id x y

@[simp] theorem abs_zero (x y : ℝ) : absDist (some x) (some y) = 0 ↔ |x| = |y| :=
  read_zero_iff abs x y

@[simp] theorem liftReal_some (F : ℝ → ℝ) (x : ℝ) :
    (liftRealMap F).func (some x) = some (F x) := rfl

def realSet (S : Set ℝ) : Set (Option ℝ) := some '' S

theorem realSet_domain (F : ℝ → ℝ) (S : Set ℝ) : realSet S ⊆ dom (liftRealMap F) := by
  rintro _ ⟨x, hx, rfl⟩
  exact Option.some_ne_none _

@[simp] theorem mem_realSet (S : Set ℝ) (x : ℝ) :
    some x ∈ realSet S ↔ x ∈ S := by simp [realSet]

theorem realSet_diameter (a b : ℝ) (hab : a ≤ b) {S : Set ℝ}
    (ha : a ∈ S) (hb : b ∈ S) (hS : S ⊆ Set.Icc a b) :
    diameter realDist (realSet S) = ENNReal.ofReal (b - a) := by
  apply le_antisymm
  · refine iSup_le fun x : realSet S => iSup_le fun y : realSet S => ?_
    obtain ⟨x',hx,hex⟩ := x.2
    obtain ⟨y',hy,hey⟩ := y.2
    rw [← hex, ← hey, real_some]
    apply ENNReal.ofReal_le_ofReal
    have hx' := hS hx
    have hy' := hS hy
    exact abs_le.mpr ⟨by linarith [hx'.1,hy'.2], by linarith [hx'.2,hy'.1]⟩
  · simpa [abs_of_nonneg (sub_nonneg.mpr hab)] using
      (le_diameter (P := realDist) ((mem_realSet S b).mpr hb) ((mem_realSet S a).mpr ha))

namespace Swap

def U : Set (Option Bool) := {some false, some true}
noncomputable def d : Unit → Option Bool → Option Bool → ℝ≥0∞ :=
  fun _ => extendDistance (discreteReadout id 1)
def f : Operator (Option Bool) none := ⟨Option.map not, rfl⟩

theorem gauge (i : Unit) : ExtendedPseudoMetric _ none (d i) := discrete_legal id 1

theorem calculations :
    U ⊆ dom f ∧ U ⊆ dom (f*f) ∧ f.func '' U = U ∧
    Active d f U = {()} ∧ Ident d f U = ∅ ∧ Ident d (f*f) U = {()} ∧
    Active d (f*f) U = ∅ := by
  have mem (x : Option Bool) : x ∈ U ↔ x ≠ none := by
    cases x with
    | none => simp [U]
    | some b => cases b <;> simp [U]
  have dom1 : U ⊆ dom f := by
    rintro (_ | x) h
    · simp [U] at h
    · exact Option.some_ne_none _
  have dom2 : U ⊆ dom (f*f) := by
    rintro (_ | x) h
    · simp [U] at h
    · exact Option.some_ne_none _
  have hi : f.func '' U = U := by
    ext x
    constructor
    · rintro ⟨y, hy,rfl⟩
      exact (mem _).mpr (dom1 hy)
    · intro hx
      cases x with
      | none => simp [U] at hx
      | some b => exact ⟨some (!b), (mem _).mpr (Option.some_ne_none _), by simp [f]⟩
  have hc : () ∉ Const d f U := by
    intro h
    have h' := h (some false) (by simp [U]) (some true) (by simp [U])
    norm_num [d, f, extendDistance, discreteReadout] at h'
  have hn : () ∉ Ident d f U := by
    intro h
    have h' := h.2 (some false) (by simp [U])
    norm_num [d, f, extendDistance, discreteReadout] at h'
  have hc2 : () ∉ Const d (f*f) U := by
    intro h
    have h' := h (some false) (by simp [U]) (some true) (by simp [U])
    norm_num [d, f, extendDistance, discreteReadout] at h'
  have hi2 : () ∈ Ident d (f*f) U := by
    refine ⟨hc2, fun x _ => ?_⟩
    have hx : (f*f).func x = x := by cases x <;> simp [f]
    rw [hx]
    exact (gauge ()).dist_self _
  refine ⟨dom1, dom2, hi, ?_, ?_, ?_, ?_⟩ <;> ext i <;> cases i
  · simp [Active, hc, hn]
  · simp [hn]
  · simp [hi2]
  · simp [Active, hi2]

theorem reverse_failures :
    ¬ (Active d f U ∪ Active d f (f.func '' U) ⊆ Active d (f*f) U) ∧
    ¬ (Ident d (f*f) U ⊆ Ident d f U ∩ Ident d f (f.func '' U)) := by
  obtain ⟨_,_,hi,ha,hid,hid2,ha2⟩ := calculations
  rw [hi, ha, hid, hid2, ha2, Set.union_self, Set.inter_self]
  simp

end Swap

namespace Inner

inductive Pt | a | b | p | q | r | s deriving DecidableEq
open Pt

def q : Pt → Pt | Pt.q => p | x => x
noncomputable def d (i : Bool) : Option Pt → Option Pt → ℝ≥0∞ :=
  extendDistance (discreteReadout (if i then id else q) 1)
def f : Operator (Option Pt) none :=
  ⟨fun | some a => some p | some b => some Pt.q | _ => none, rfl⟩
def g : Operator (Option Pt) none :=
  ⟨fun | some p => some r | some Pt.q => some s | _ => none, rfl⟩
def U : Set (Option Pt) := {some a, some b}

theorem gauge (i : Bool) : ExtendedPseudoMetric _ none (d i) := by
  haveI : Nonempty Pt := ⟨a⟩
  exact discrete_legal _ _

theorem counterexample : U ⊆ dom (g*f) ∧ f.func '' U = {some p, some Pt.q} ∧
    false ∈ Const d f U ∧ false ∉ Const d (g*f) U ∧ d true (some p) (some Pt.q) = 1 ∧
    d false ((g*f).func (some a)) ((g*f).func (some b)) = 1 := by
  have mem (x : Option Pt) : x ∈ U ↔ x = some a ∨ x = some b := by simp [U]
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro x hx
    rcases (mem x).mp hx with rfl | rfl <;> exact Option.some_ne_none _
  · ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      rcases (mem y).mp hy with rfl | rfl <;> simp [f]
    · intro hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact ⟨some a,by simp [U],rfl⟩
      · exact ⟨some b,by simp [U],rfl⟩
  · intro x hx y hy
    rcases (mem x).mp hx with rfl | rfl <;> rcases (mem y).mp hy with rfl | rfl <;>
      simp [d, f, q, extendDistance, discreteReadout]
  · intro h
    have he := h (some a) (by simp [U]) (some b) (by simp [U])
    norm_num [d, f, g, q, extendDistance, discreteReadout] at he
    cases he
  · simp [d, extendDistance, discreteReadout]
  · simp [d, f, g, q, extendDistance, discreteReadout]

end Inner

namespace InfiniteGap

noncomputable def d {I : Type} [DecidableEq I] (i k : I) : Option Bool → Option Bool → ℝ≥0∞ :=
  extendDistance (discreteReadout id (if k = i then ⊤ else 1))

theorem gauge {I : Type} [DecidableEq I] (i k : I) :
    ExtendedPseudoMetric _ none (d i k) := discrete_legal _ _

theorem counterexample {I : Type} [Fintype I] [DecidableEq I] (i j : I) :
    let U := Swap.U
    let f : Operator (Option Bool) none := 1
    U.Nonempty ∧ U ⊆ dom f ∧ nullMatrix (d i) f U j i = ⊤ ∧
      j ∉ Const (d i) f U ∧ d i i (some false) (some true) = ⊤ ∧
      (i = j → d i j (some false) (some true) = ⊤) ∧
      (i ≠ j → d i j (some false) (some true) = 1) := by
  dsimp
  have mem (x : Option Bool) : x ∈ Swap.U ↔ x = some false ∨ x = some true := by simp [Swap.U]
  refine ⟨⟨some false,by simp [Swap.U]⟩,?_,?_,?_,?_,?_,?_⟩
  · intro x hx
    rcases (mem x).mp hx with rfl | rfl <;> exact Option.some_ne_none _
  · apply top_unique
    apply le_uniform_iff.mpr
    intro y hy x hx h
    rcases (mem y).mp hy with rfl | rfl <;> rcases (mem x).mp hx with rfl | rfl
    · exact (gauge i j).dist_self _
    · simp [d, extendDistance, discreteReadout] at h
    · simp [d, extendDistance, discreteReadout] at h
    · exact (gauge i j).dist_self _
  · intro h
    have he := h (some false) (by simp [Swap.U]) (some true) (by simp [Swap.U])
    change d i j (some false) (some true) = 0 at he
    by_cases hji : j = i <;> norm_num [d, extendDistance, discreteReadout, hji] at he
  · simp [d, extendDistance, discreteReadout]
  · rintro rfl
    simp [d, extendDistance, discreteReadout]
  · intro h
    simp [d, extendDistance, discreteReadout, Ne.symm h]

end InfiniteGap

theorem diameter_counterexample :
    let A := realSet ({0,1} : Set ℝ)
    let B := realSet ({0} : Set ℝ)
    B.Nonempty ∧ B ⊆ A ∧ A ⊆ dom (1 : Operator (Option ℝ) none) ∧
    diameter realDist B = 0 ∧ diameter realDist A = 1 ∧
    diameter realDist B < ENNReal.ofReal (1/2) ∧
    ENNReal.ofReal (1/2) ≤ diameter realDist A := by
  have ha : diameter realDist (realSet ({0,1} : Set ℝ)) = 1 := by
    rw [realSet_diameter 0 1 (by norm_num) (by simp) (by simp) (by
      intro x hx
      simp at hx
      rcases hx with rfl | rfl <;> exact ⟨by norm_num,by norm_num⟩)]
    norm_num
  have hb : diameter realDist (realSet ({0} : Set ℝ)) = 0 := by
    rw [realSet_diameter 0 0 le_rfl (by simp) (by simp) (by simp)]
    simp
  refine ⟨⟨some 0,by simp⟩,Set.image_mono (by simp),?_,hb,ha,?_,?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact Option.some_ne_none _
  · rw [hb]
    simp
  · rw [ha, ENNReal.ofReal_le_one]
    norm_num

end Chapter
