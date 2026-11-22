import Entropy
open formal_oet.vol_01.ch_01_foundations formal_oet.vol_01.ch_02_operator_bounds
open Set
namespace C3
noncomputable section
open scoped Classical
variable {X I : Type} {b : X}

def liftDist (p : D X) : D (Option X)
  | some x, some y => p x y
  | none, none => 0
  | _, _ => ⊤

theorem lift_metric [Nonempty X] {p : D X} (hr : ∀ x, p x x = 0)
    (hs : ∀ x y, p x y = p y x) (ht : ∀ x y z, p x z ≤ p x y + p y z) :
    ExtendedPseudoMetric (Option X) none (liftDist p) where
  nonabsorbing := ⟨some (Classical.arbitrary X), Option.some_ne_none _⟩
  dist_self x := by cases x <;> simp [liftDist,hr]
  symm x y := by cases x <;> cases y <;> simp [liftDist,hs]
  triangle x y z := by cases x <;> cases y <;> cases z <;> simp [liftDist,ht]
  isolate_bot x hx := by cases x <;> simp_all [liftDist]

def discrete {Y : Type} (v : X → Y) (c : ENNReal) (x y : X) : ENNReal :=
  if v x = v y then 0 else c

theorem discrete_metric [Nonempty X] {Y : Type} (v : X → Y) (c : ENNReal) :
    ExtendedPseudoMetric (Option X) none (liftDist (discrete v c)) := by
  apply lift_metric
  · simp [discrete]
  · intro x y
    simp [discrete,eq_comm]
  · intro x y z
    by_cases h : v x = v y <;> by_cases k : v y = v z <;> simp_all [discrete]
    split <;> simp

def run (f : X → X) : Op (none : Option X) := ⟨Option.map f,rfl⟩
def area (S : Set X) := some '' S
@[simp] theorem some_area {S : Set X} {x : X} : some x ∈ area S ↔ x ∈ S := by simp [area]
theorem area_dom (f : X → X) (S : Set X) : area S ⊆ dom (run f) := by
  rintro _ ⟨x,_,rfl⟩
  exact Option.some_ne_none _
theorem area_image (f : X → X) (S : Set X) : (run f).func '' area S = area (f '' S) := by
  simp [area,run,image_image]

def realDist (v : ℝ → ℝ) (x y : ℝ) := ENNReal.ofReal |v x - v y|
abbrev line (v : ℝ → ℝ) := liftDist (realDist v)
theorem line_metric (v : ℝ → ℝ) : ExtendedPseudoMetric (Option ℝ) none (line v) := by
  apply lift_metric
  · simp [realDist]
  · intro x y
    rw [realDist,abs_sub_comm,realDist]
  · intro x y z
    rw [realDist,realDist,realDist,← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (abs_sub_le _ _ _)

@[simp] theorem line_some (v : ℝ → ℝ) (x y : ℝ) :
    line v (some x) (some y) = ENNReal.ofReal |v x-v y| := rfl
@[simp] theorem run_some (f : X → X) (x : X) : (run f).func (some x) = some (f x) := rfl

theorem area_diam {p : D X} {S : Set X} : diameter (liftDist p) (area S) = diameter p S := by
  apply le_antisymm
  · apply diameter_le.mpr
    rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
    exact le_diameter hx hy
  · exact diameter_le.mpr fun x hx y hy => le_diameter (some_area.mpr hx) (some_area.mpr hy)

theorem area_rad {p q : D X} {f : X → X} {S : Set X} {y : X} :
    rad (liftDist p) (liftDist q) (run f).func (area S) (some y) = rad p q f S y := by
  apply le_antisymm
  · exact le_rad.mpr fun x hx hh => below_rad (p := liftDist p) (q := liftDist q) (f := (run f).func) (y := some y) (some_area.mpr hx) hh
  · apply le_rad.mpr
    rintro _ ⟨x,hx,rfl⟩ hh
    exact below_rad (p := p) (q := q) (f := f) (y := y) hx hh

theorem area_uniform {p q : D X} {f : X → X} {S : Set X} :
    uniform (liftDist p) (liftDist q) (run f).func (area S) (area S) = uniform p q f S S := by
  apply le_antisymm
  · apply le_uniform.mpr
    intro y hy x hx hp
    exact uniform_zero (p := liftDist p) (q := liftDist q) (f := (run f).func) (some_area.mpr hx) (some_area.mpr hy) hp
  · apply le_uniform.mpr
    rintro _ ⟨y,hy,rfl⟩ _ ⟨x,hx,rfl⟩ hp
    exact uniform_zero (p := p) (q := q) (f := f) hx hy hp

namespace Swap
abbrev p := liftDist (discrete (id : Bool → Bool) 1)
def F := run Bool.not
def U := area (univ : Set Bool)
theorem model : ExtendedPseudoMetric _ none p := discrete_metric _ _
theorem image_dom : U ⊆ dom F ∧ F.func '' U = U := by
  refine ⟨area_dom _ _,?_⟩
  have hh : Function.Surjective Bool.not := fun x => ⟨!x,by simp⟩
  rw [U,F,area_image,Set.image_univ,Set.range_eq_univ.mpr hh]

theorem calc_swap : Active p F.func U ∧ ¬ Ident p F.func U ∧
    Ident p (F * F).func U ∧ ¬ Active p (F * F).func U := by
  have mem (x : Bool) : some x ∈ U := some_area.mpr trivial
  have hn : ¬ Const p F.func U := by
    intro h
    simpa [p,F,liftDist,discrete] using h _ (mem true) _ (mem false)
  have hi : ¬ Ident p F.func U := by
    intro h
    simpa [p,F,liftDist,discrete] using h.2 _ (mem true)
  have hid : Ident p (F * F).func U := by
    refine ⟨?_,?_⟩
    · intro h
      have hh := h _ (mem true) _ (mem false)
      change p (some true) (some false) = 0 at hh
      simp [p,liftDist,discrete] at hh
    · rintro _ ⟨x,_,rfl⟩
      cases x <;> exact (model.dist_self _)
  exact ⟨⟨hn,hi⟩,hi,hid,fun h => h.2 hid⟩
end Swap

namespace Seven
abbrev Pt := Fin 6
def readout (x : Pt) := if x = 3 then 2 else x
def p (j : Bool) := liftDist (discrete (if j then id else readout) 1)
def F : Op (none : Option Pt) :=
  ⟨fun x => if x = some 0 then some 2 else if x = some 1 then some 3 else none,by simp⟩
def G : Op (none : Option Pt) :=
  ⟨fun x => if x = some 2 then some 4 else if x = some 3 then some 5 else none,by simp⟩
def U : Set (Option Pt) := {some 0,some 1}
theorem model (j : Bool) : ExtendedPseudoMetric _ none (p j) := discrete_metric _ _
theorem example_seven : U ⊆ dom (G * F) ∧ Const (p false) F.func U ∧
    ¬ Const (p false) (G * F).func U ∧ p true (F.func (some 0)) (F.func (some 1)) = 1 := by
  have hf0 : F.func (some 0) = some 2 := by simp [F]
  have hf1 : F.func (some 1) = some 3 := by norm_num [F,Fin.ext_iff]
  have hg2 : G.func (some 2) = some 4 := by simp [G]
  have hg3 : G.func (some 3) = some 5 := by norm_num [G,Fin.ext_iff]
  have eval (x) : (G * F).func x = G.func (F.func x) := rfl
  simp only [U, Const, Set.mem_insert_iff,Set.mem_singleton_iff,
    forall_eq_or_imp,forall_eq] at *
  norm_num [Set.subset_def,dom,eval,hf0,hf1,hg2,hg3,p,liftDist,discrete,readout,Fin.ext_iff]
  simp

end Seven

namespace InfiniteInput
def d (j : Bool) := liftDist (discrete (id : Bool → Bool) (if j then 1 else ⊤))
theorem model (j : Bool) : ExtendedPseudoMetric _ none (d j) := discrete_metric _ _
theorem both (j : Bool) : N d (run id).func Swap.U j false = ⊤ ∧ ¬ Const (d j) (run id).func Swap.U := by
  constructor
  · apply top_unique
    apply le_uniform.mpr
    rintro _ ⟨y,_,rfl⟩ _ ⟨x,_,rfl⟩ hh
    by_cases he : x = y
    · subst x; exact (model j).dist_self _
    · simp [d,liftDist,discrete,he] at hh
  · intro hc
    have hh := hc (some true) (some_area.mpr trivial) (some false) (some_area.mpr trivial)
    cases j <;> simp [d,liftDist,discrete] at hh
end InfiniteInput

end
end C3
