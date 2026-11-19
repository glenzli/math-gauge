import Ch3.Scale

namespace MG
open Set formal_oet.vol_01.ch_01_foundations
noncomputable section
variable {D E : Type}

def extend (p : Dist D) : Dist (Option D)
  | none, none => 0
  | some x, some y => p x y
  | _, _ => ⊤

theorem extended [Nonempty D] (p : Dist D) (hs : ∀ x, p x x = 0)
    (hc : ∀ x y, p x y = p y x) (ht : ∀ x y z, p x z ≤ p x y + p y z) :
    ExtendedPseudoMetric (Option D) none (extend p) where
  nonabsorbing := ⟨some (Classical.arbitrary D),by simp⟩
  dist_self := by rintro (_|x) <;> simp [extend,hs]
  symm := by rintro (_|x) (_|y) <;> simp [extend,hc]
  triangle := by rintro (_|x) (_|y) (_|z) <;> simp [extend,ht]
  isolate_bot := by rintro (_|x) hx <;> simp_all [extend]

def liftOp (a : D → D) : Op (none : Option D) := ⟨Option.map a,rfl⟩
@[simp] theorem lift_some (a : D → D) (x : D) : (liftOp a).func (some x) = some (a x) := rfl
@[simp] theorem mul_apply {X : Type} {b : X} (f g : Op b) (x : X) : (g*f).func x = g.func (f.func x) := rfl
@[simp] theorem one_apply {X : Type} {b : X} (x : X) : (1 : Op b).func x = x := rfl
@[simp] theorem lift_dom (a : D → D) : dom (liftOp a) = range some := by
  ext x
  cases x <;> simp [dom,liftOp]

def discreteRead [DecidableEq E] (a : D → E) (w : ENNReal) :=
  extend fun x y => if a x = a y then 0 else w

theorem discreteMetric [Nonempty D] [DecidableEq E] (a : D → E) (w : ENNReal) :
    ExtendedPseudoMetric (Option D) none (discreteRead a w) := by
  apply extended
  · simp
  · intro x y
    by_cases h : a x = a y <;> simp [h,eq_comm]
  · intro x y z
    by_cases h : a x = a y <;> by_cases k : a y = a z <;> by_cases l : a x = a z <;> simp_all

abbrev pt := @Option.some ℝ
abbrev Line := Option ℝ
def readDist (a : ℝ → ℝ) : Dist Line := extend fun x y => edist (a x) (a y)
abbrev usual := readDist id
abbrev absolute := readDist abs

theorem readMetric (a : ℝ → ℝ) : ExtendedPseudoMetric Line none (readDist a) :=
  extended _ (fun _ => edist_self _) (fun _ _ => edist_comm _ _) (fun _ _ _ => edist_triangle _ _ _)

@[simp] theorem read_points (a : ℝ → ℝ) (x y : ℝ) :
    readDist a (pt x) (pt y) = ENNReal.ofReal |a x - a y| := by
  change edist (a x) (a y) = _
  rw [edist_dist,Real.dist_eq]

def realSet (A : Set ℝ) : Set Line := pt '' A
theorem realDom (a : ℝ → ℝ) (A : Set ℝ) : realSet A ⊆ dom (liftOp a) := by
  rintro _ ⟨x,_,rfl⟩
  exact Option.some_ne_none _
theorem realNonempty {A : Set ℝ} (hA : A.Nonempty) : (realSet A).Nonempty := hA.image _
@[simp] theorem mem_realSet {x : ℝ} {A : Set ℝ} : pt x ∈ realSet A ↔ x ∈ A := by simp [realSet,pt]

namespace Swap
abbrev a := some false
abbrev c := some true
def U : Set (Option Bool) := {a,c}
def d := discreteRead (id : Bool → Bool) 1
def f := liftOp Bool.not

theorem model : ExtendedPseudoMetric _ none d := discreteMetric _ _
theorem domain : U ⊆ dom f := by intro x hx; rcases hx with h|h <;> rw [h] <;> exact Option.some_ne_none _
theorem image_eq : f.func '' U = U := by
  ext x
  simp [U, f, a,c,or_comm,eq_comm]

theorem components : Active d f U ∧ ¬ Ident d f U ∧ Ident d (f*f) U ∧ ¬ Active d (f*f) U := by
  have ha : a ∈ U := Or.inl rfl
  have hc : c ∈ U := Or.inr rfl
  have hn : ¬ Const d f U := fun h => one_ne_zero (h _ ha _ hc)
  have hi : ¬ Ident d f U := fun h => one_ne_zero (h.2 _ ha)
  have hj : Ident d (f*f) U := ⟨fun h => one_ne_zero (h _ ha _ hc),by
    intro x hx
    rcases hx with h|h <;> rw [h] <;> rfl⟩
  exact ⟨⟨hn,hi⟩,hi,hj,fun h => h.2 hj⟩

theorem strictInclusions :
    ({_i : Unit | Active d (f*f) U} ⊂ {_i : Unit | Active d f U} ∪ {_i : Unit | Active d f (f.func '' U)}) ∧
    ({_i : Unit | Ident d f U} ∩ {_i : Unit | Ident d f (f.func '' U)} ⊂ {_i : Unit | Ident d (f*f) U}) := by
  rw [image_eq,union_self,inter_self]
  obtain ⟨ha,hi,hj,hn⟩ := components
  exact ⟨⟨fun _ _ => ha,fun h => hn (h (a := ()) ha)⟩,⟨fun _ _ => hj,fun h => hi (h (a := ()) hj)⟩⟩

def channels (j : Bool) : Dist (Option Bool) := discreteRead (id : Bool → Bool) (if j then 1 else ⊤)
theorem channelsMetric (j : Bool) : ExtendedPseudoMetric _ none (channels j) := discreteMetric _ _
theorem infiniteInput (j : Bool) :
    (∀ y ∈ U, radius (channels false) (channels j) (1 : Op (none : Option Bool)) U y = ⊤) ∧
    matrix channels (1 : Op (none : Option Bool)) U j false = ⊤ ∧ ¬ Const (channels j) (1 : Op (none : Option Bool)) U := by
  have bound : ∀ y ∈ U, ∀ x ∈ U, channels false x y < ⊤ →
      channels j ((1 : Op (none : Option Bool)).func x) ((1 : Op (none : Option Bool)).func y) = 0 := by
    intro y hy x hx
    rcases hx with h|h <;> rcases hy with k|k <;> rw [h,k] <;> simp [channels,a,c,discreteRead,extend]
  refine ⟨fun y hy => top_unique (radiusBound.2 (bound y hy)),top_unique (uniformBound.2 bound),?_⟩
  intro h
  have H := h a (Or.inl rfl) c (Or.inr rfl)
  cases j <;> simp [channels,discreteRead,extend,a,c] at H
end Swap

namespace Seven
inductive P | a | b | p | q | r | s deriving DecidableEq, Inhabited, Fintype
open P

theorem cardinality : Fintype.card (Option P) = 7 := by decide

def key : P → P | q => p | x => x
def d (k : Bool) := discreteRead (if k then id else key) 1
def first : Op (none : Option P) := ⟨fun x => match x with
  | some .a => some .p | some .b => some .q | _ => none,rfl⟩
def lastOp : Op (none : Option P) := ⟨fun x => match x with
  | some .p => some .r | some .q => some .s | _ => none,rfl⟩
def U : Set (Option P) := {some a,some b}
theorem model (k : Bool) : ExtendedPseudoMetric _ none (d k) := discreteMetric _ _
theorem exampleData : U ⊆ dom (lastOp*first) ∧ first.func '' U = {some p,some q} ∧
    Const (d false) first U ∧ d true (some p) (some q) = 1 ∧
    d false ((lastOp*first).func (some a)) ((lastOp*first).func (some b)) = 1 ∧
    ¬ Const (d false) (lastOp*first) U := by
  refine ⟨?_,?_,?_,rfl,rfl,fun h => one_ne_zero (h _ (Or.inl rfl) _ (Or.inr rfl))⟩
  · intro x hx
    rcases hx with h|h <;> rw [h] <;> exact Option.some_ne_none _
  · rw [U,Set.image_insert_eq,Set.image_singleton]; rfl
  · intro x hx y hy
    rcases hx with h|h <;> rcases hy with k|k <;> rw [h,k] <;> rfl
end Seven
end
end MG
