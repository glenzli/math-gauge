import Chapter3.Entropy
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Data.Finset.Powerset

namespace Chapter3
open formal_oet.vol_01.ch_01_foundations
open Set
noncomputable section

@[simp] theorem op_mul_apply {A : Type} {b : A} (f g : Operator A b) (x : A) :
    (g*f).func x = g.func (f.func x) := rfl
@[simp] theorem op_one_apply {A : Type} {b : A} (x : A) :
    (1 : Operator A b).func x = x := rfl

def pointedDist {A : Type} (d : A → A → ENNReal) : Option A → Option A → ENNReal
  | none, none => 0
  | some a, some b => d a b
  | _, _ => ⊤
def pointedOp {A : Type} (f : A → A) : Operator (Option A) none :=
  ⟨Option.map f, rfl⟩

theorem pointed_metric {A : Type} [Nonempty A] (d : A → A → ENNReal)
    (hs : ∀ x, d x x = 0) (hy : ∀ x y, d x y = d y x)
    (ht : ∀ x y z, d x z ≤ d x y + d y z) :
    ExtendedPseudoMetric (Option A) none (pointedDist d) := by
  refine ⟨⟨some (Classical.arbitrary A), by simp⟩, ?_, ?_, ?_, ?_⟩
  · intro x; cases x <;> simp [pointedDist,hs]
  · intro x y; cases x <;> cases y <;> simp [pointedDist,hy]
  · intro x y z; cases x <;> cases y <;> cases z <;> simp [pointedDist,ht]
  · intro x hx; cases x <;> simp_all [pointedDist]

def realReadout (q : ℝ → ℝ) : Option ℝ → Option ℝ → ENNReal :=
  pointedDist (fun x y => edist (q x) (q y))
def realDistance := realReadout id
def absDistance := realReadout (fun x => |x|)

theorem realReadout_metric (q : ℝ → ℝ) :
    ExtendedPseudoMetric (Option ℝ) none (realReadout q) :=
  pointed_metric _ (fun _ => edist_self _) (fun _ _ => edist_comm _ _) (fun _ _ _ => edist_triangle _ _ _)
theorem realDistance_metric : ExtendedPseudoMetric (Option ℝ) none realDistance := realReadout_metric id
theorem absDistance_metric : ExtendedPseudoMetric (Option ℝ) none absDistance := realReadout_metric _

@[simp] theorem realReadout_some (q : ℝ → ℝ) (x y : ℝ) :
    realReadout q (some x) (some y) = ENNReal.ofReal |q x-q y| := by
  exact edist_dist _ _
@[simp] theorem realDistance_some (x y : ℝ) :
    realDistance (some x) (some y) = ENNReal.ofReal |x-y| := realReadout_some _ _ _
@[simp] theorem absDistance_some (x y : ℝ) :
    absDistance (some x) (some y) = ENNReal.ofReal (abs (abs x-abs y)) := realReadout_some _ _ _
@[simp] theorem pointedOp_some (f : ℝ → ℝ) (x : ℝ) :
    (pointedOp f).func (some x) = some (f x) := rfl
@[simp] theorem realDistance_zero (x y : ℝ) : realDistance (some x) (some y) = 0 ↔ x = y := by
  change edist x y = 0 ↔ x = y
  exact edist_eq_zero

theorem real_domain (f : ℝ → ℝ) : dom (pointedOp f) = range some := by
  ext x; cases x <;> simp [dom,pointedOp]

theorem diameter_pair (d : Option ℝ → Option ℝ → ENNReal)
    (hd : ExtendedPseudoMetric (Option ℝ) none d) (x y : ℝ) :
    diameter d ({some x, some y} : Set (Option ℝ)) = d (some x) (some y) := by
  apply le_antisymm
  · apply iSup_le
    intro a
    apply iSup_le
    intro ha
    apply iSup_le
    intro b
    apply iSup_le
    intro hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
      simp [hd.dist_self,hd.symm]
  · exact dist_le_diameter d (by simp) (by simp)

theorem diameter_real_interval {a b : ℝ} (hab : a ≤ b) :
    diameter realDistance (some '' Icc a b) = ENNReal.ofReal (b-a) := by
  apply le_antisymm
  · apply iSup_le
    rintro _
    apply iSup_le
    rintro ⟨x,hx,rfl⟩
    apply iSup_le
    rintro _
    apply iSup_le
    rintro ⟨y,hy,rfl⟩
    rw [realDistance_some]
    apply ENNReal.ofReal_le_ofReal
    exact abs_le.mpr ⟨by linarith [hx.1,hx.2,hy.1,hy.2], by linarith [hx.1,hx.2,hy.1,hy.2]⟩
  · have h := dist_le_diameter realDistance
      (mem_image_of_mem some (show a ∈ Icc a b from ⟨le_rfl,hab⟩))
      (mem_image_of_mem some (show b ∈ Icc a b from ⟨hab,le_rfl⟩))
    simpa [realDistance_some,abs_of_nonpos (sub_nonpos.mpr hab)] using h

theorem cover_finset_lower {X : Type} (d : X → X → ENNReal) (eps : ENNReal)
    (S : Finset X) (n : ℕ)
    (h : ∀ T ∈ S.powerset, InternalEpsilonNet d eps (↑S) T → n ≤ T.card) :
    (n : ENNReal) ≤ covering_number d eps (↑S : Set X) := by
  classical
  apply le_iInf
  intro T
  apply le_iInf
  intro hT
  exact_mod_cast h T (Finset.mem_powerset.mpr (fun _ ht => hT.1 ht)) hT

theorem cover_le_net {X : Type} (d : X → X → ENNReal) (eps : ENNReal)
    (U : Set X) (S : Finset X) (h : InternalEpsilonNet d eps U S) :
    covering_number d eps U ≤ (S.card : ENNReal) :=
  iInf_le_of_le S (iInf_le_of_le h le_rfl)

theorem cover_separated {X : Type} (d : X → X → ENNReal) (eps : ENNReal)
    (S : Finset X) (he : 0 < eps) (hself : ∀ x, d x x = 0)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, d x y < eps → x=y) :
    covering_number d eps (↑S : Set X) = (S.card : ENNReal) := by
  classical
  apply le_antisymm
  · apply cover_le_net
    exact ⟨subset_rfl,fun x hx => ⟨x,hx,by rwa [hself]⟩⟩
  · apply le_iInf
    intro T
    apply le_iInf
    intro hT
    have hsub : S ⊆ T := by
      intro x hx
      obtain ⟨c,hc,hd⟩ := hT.2 x hx
      have hh := hsep x hx c (hT.1 hc) hd
      rwa [← hh] at hc
    exact_mod_cast Finset.card_le_card hsub

theorem cover_two_lower {X : Type} (d : X → X → ENNReal) (eps : ENNReal)
    (U : Set X) (hne : U.Nonempty)
    (hfar : ∀ c ∈ U, ∃ x ∈ U, eps ≤ d x c) : (2 : ENNReal) ≤ covering_number d eps U := by
  classical
  apply le_iInf
  intro S
  apply le_iInf
  intro hS
  have hn : S.Nonempty := by
    obtain ⟨x,hx⟩ := hne
    obtain ⟨c,hc,_⟩ := hS.2 x hx
    exact ⟨c,hc⟩
  obtain ⟨c,hc⟩ := hn
  obtain ⟨x,hx,hd⟩ := hfar c (hS.1 hc)
  obtain ⟨a,ha,hda⟩ := hS.2 x hx
  have hneac : a ≠ c := fun he => not_lt_of_ge hd (he ▸ hda)
  have hcard : 2 ≤ S.card := by
    have hsub : ({a,c} : Finset X) ⊆ S := by
      intro z hz
      simp only [Finset.mem_insert,Finset.mem_singleton] at hz
      rcases hz with hz | hz <;> subst z <;> assumption
    have hh := Finset.card_le_card hsub
    simpa [hneac] using hh
  exact_mod_cast hcard

theorem cover_pair {X : Type} (d : X → X → ENNReal)
    (hs : ∀ x, d x x = 0) (hy : ∀ x y, d x y = d y x)
    {a b : X} (hab : a ≠ b) {eps : ENNReal} (he : 0 < eps) :
    covering_number d eps ({a,b} : Set X) = if d a b < eps then 1 else 2 := by
  classical
  by_cases h : d a b < eps
  · rw [if_pos h]
    apply le_antisymm _ (one_le_covering_number_of_nonempty _ _ _ ⟨a,by simp⟩)
    have hn : InternalEpsilonNet d eps ({a,b} : Set X) {a} := by
      refine ⟨by simp,?_⟩
      intro x hx
      rcases hx with hx | hx
      · subst x; exact ⟨a,by simp,by rwa [hs]⟩
      · subst x; exact ⟨a,by simp,by rwa [hy]⟩
    simpa using cover_le_net d eps ({a,b} : Set X) {a} hn
  · rw [if_neg h]
    apply le_antisymm
    · have hn : InternalEpsilonNet d eps ({a,b} : Set X) {a,b} := by
        refine ⟨by simp,fun x hx => ⟨x,by simpa using hx,by rwa [hs]⟩⟩
      simpa [hab] using cover_le_net d eps ({a,b} : Set X) {a,b} hn
    · apply cover_two_lower _ _ _ ⟨a,by simp⟩
      intro c hc
      rcases hc with hc | hc
      · subst c; exact ⟨b,by simp,by rw [hy]; exact le_of_not_gt h⟩
      · subst c; exact ⟨a,by simp,le_of_not_gt h⟩

def discreteReadout {A B : Type} (q : A → B) (x y : A) : ENNReal :=
  by classical exact if q x = q y then 0 else 1
theorem discreteReadout_metric {A B : Type} [Nonempty A] (q : A → B) :
    ExtendedPseudoMetric (Option A) none (pointedDist (discreteReadout q)) := by
  classical
  apply pointed_metric
  · intro x; simp [discreteReadout]
  · intro x y; simp [discreteReadout,eq_comm]
  · intro x y z
    by_cases hxy : q x = q y <;> by_cases hyz : q y = q z <;>
      by_cases hxz : q x = q z <;> simp_all [discreteReadout]

namespace Swap
abbrev X := Option Bool
def d : Unit → X → X → ENNReal := fun _ => pointedDist (discreteReadout id)
def U : Set X := {some false, some true}
def f : Operator X none := pointedOp Bool.not
theorem legal : ExtendedPseudoMetric X none (d ()) := discreteReadout_metric id
theorem image : f.func '' U = U := by
  ext x
  simp [U,f,pointedOp,Set.image_insert_eq,Set.image_singleton]
  tauto
theorem types :
    constComponents d f U = ∅ ∧ idComponents d f U = ∅ ∧ actComponents d f U = univ ∧
    idComponents d (f*f) U = univ ∧ actComponents d (f*f) U = ∅ := by
  have hc : constComponents d f U = ∅ := by
    ext i; cases i
    norm_num [constComponents,U,d,f,pointedOp,pointedDist,discreteReadout]
  have hi : idComponents d f U = ∅ := by
    ext i; cases i
    norm_num [idComponents,constComponents,U,d,f,pointedOp,pointedDist,discreteReadout]
  refine ⟨hc,hi,by simp [actComponents,hc,hi],?_,?_⟩
  · ext i; cases i
    norm_num [idComponents,constComponents,U,d,f,pointedOp,pointedDist,discreteReadout,
      operator_monoid,operator_compose]
  · ext i; cases i
    norm_num [actComponents,idComponents,constComponents,U,d,f,pointedOp,pointedDist,discreteReadout,
      operator_monoid,operator_compose]
theorem reverse_failures :
    ¬ (actComponents d f U ∪ actComponents d f (f.func '' U) ⊆ actComponents d (f*f) U) ∧
    ¬ (idComponents d (f*f) U ⊆ idComponents d f U ∩ idComponents d f (f.func '' U)) := by
  simp [image,types.1,types.2.1,types.2.2.1,types.2.2.2.1,types.2.2.2.2]
end Swap

namespace Inner
inductive A | a | b | p | q | r | s deriving DecidableEq, Fintype, Inhabited
open A
def read : A → A | q => p | x => x
def d (i : Bool) : Option A → Option A → ENNReal :=
  pointedDist (discreteReadout (if i then id else read))
def f : Operator (Option A) none := ⟨fun x => match x with
  | some a => some p | some b => some q | _ => none, rfl⟩
def g : Operator (Option A) none := ⟨fun x => match x with
  | some p => some r | some q => some s | _ => none, rfl⟩
def U : Set (Option A) := {some a,some b}
theorem legal : ∀ i, ExtendedPseudoMetric (Option A) none (d i) :=
  fun i => discreteReadout_metric _
theorem domain : U ⊆ dom (g*f) := by
  intro x hx
  rcases hx with rfl | rfl <;> simp [dom,g,f,operator_monoid,operator_compose]
theorem calculation :
    false ∈ constComponents d f U ∧ false ∉ constComponents d (g*f) U ∧
    d true (some p) (some q) = 1 ∧ d false (some r) (some s) = 1 := by
  norm_num [constComponents,U,d,f,g,pointedDist,discreteReadout,read,
    operator_monoid,operator_compose,show p ≠ q by decide,show r ≠ s by decide]
end Inner

namespace Infinite
def d (i : Bool) : Option Bool → Option Bool → ENNReal :=
  if i then pointedDist (discreteReadout id) else
    pointedDist (fun x y => if x = y then 0 else ⊤)
def U : Set (Option Bool) := Swap.U
theorem legal : ∀ i, ExtendedPseudoMetric (Option Bool) none (d i) := by
  intro i
  cases i
  · apply pointed_metric
    · intro x; simp
    · intro x y; simp [eq_comm]
    · intro x y z
      by_cases hxy : x=y <;> by_cases hyz : y=z <;> by_cases hxz : x=z <;> simp_all
  · exact discreteReadout_metric id
theorem radii (j : Bool) :
    uniformRadius (d false) (d j) (1 : Operator (Option Bool) none) U U = ⊤ ∧
    j ∉ constComponents d (1 : Operator (Option Bool) none) U := by
  constructor
  · apply top_unique
    apply le_iInf
    intro y
    apply le_iInf
    intro hy
    apply (le_radius_iff _ _ _ _ _ _).mpr
    intro x hx hxy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
      cases j <;> norm_num [d,pointedDist,discreteReadout] at *
  · intro hc
    have hh := hc (some false) (by simp [U,Swap.U]) (some true) (by simp [U,Swap.U])
    cases j <;> norm_num [d,pointedDist,discreteReadout] at hh
end Infinite

end
end Chapter3
