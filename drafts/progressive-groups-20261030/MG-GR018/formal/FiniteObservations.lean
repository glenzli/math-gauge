import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

noncomputable section
open Set Filter Function
attribute [local instance] Classical.propDecidable
namespace MathGauge.FiniteObservations
universe u v w

/-- Natural coherent choices for every map into a finite test set. -/
structure Record (X : Type u) where
  choose : (A : Type) → [Fintype A] → (X → A) → A
  natural : ∀ (A B : Type) [Fintype A] [Fintype B] (f : X → A) (g : A → B),
    g (choose A f) = choose B (g ∘ f)

@[ext] theorem Record.ext {X : Type u} {r s : Record X}
    (h : ∀ (A : Type) [Fintype A] (f : X → A), r.choose A f = s.choose A f) : r = s := by
  cases r with | mk rc rn =>
    cases s with | mk sc sn =>
      congr
      funext A inst f
      exact h A f

namespace Record
variable {X : Type u} {Y : Type v} {Z : Type w}

theorem choose_const (r : Record X) (A : Type) [Fintype A] (a : A) :
    r.choose A (fun _ => a) = a := by
  simpa only [comp_def] using (r.natural PUnit A (fun _ => PUnit.unit) (fun _ => a)).symm

theorem choose_pair (r : Record X) (A B : Type) [Fintype A] [Fintype B]
    (f : X → A) (g : X → B) :
    r.choose (A × B) (fun x => (f x,g x)) = (r.choose A f,r.choose B g) := by
  apply Prod.ext
  · exact r.natural (A × B) A (fun x => (f x,g x)) Prod.fst
  · exact r.natural (A × B) B (fun x => (f x,g x)) Prod.snd

def map (f : X → Y) (r : Record X) : Record Y where
  choose A _ g := r.choose A (g ∘ f)
  natural A B _ _ g h := by simpa only [comp_assoc] using r.natural A B (g ∘ f) h

def point (x : X) : Record X where
  choose _ _ f := f x
  natural _ _ _ _ _ _ := rfl

def flatten (R : Record (Record X)) : Record X where
  choose A _ f := R.choose A (fun r => r.choose A f)
  natural A B _ _ f g := by
    rw [R.natural A B (fun r => r.choose A f) g]
    congr 1
    funext r
    exact r.natural A B f g

@[simp] theorem map_id (r : Record X) : map id r = r := by ext; rfl
@[simp] theorem map_comp (f : X → Y) (g : Y → Z) (r : Record X) :
    map g (map f r) = map (g ∘ f) r := by ext; rfl
@[simp] theorem map_point (f : X → Y) (x : X) : map f (point x) = point (f x) := by ext; rfl
@[simp] theorem flatten_point (r : Record X) : flatten (point r) = r := by ext; rfl
@[simp] theorem flatten_map_point (r : Record X) : flatten (map point r) = r := by ext; rfl
@[simp] theorem flatten_assoc (R : Record (Record (Record X))) :
    flatten (flatten R) = flatten (map flatten R) := by ext; rfl
@[simp] theorem flatten_natural (f : X → Y) (R : Record (Record X)) :
    map f (flatten R) = flatten (map (map f) R) := by ext; rfl

end Record

private def characteristic {X : Type u} (s : Set X) : X → Bool := fun x => decide (x ∈ s)

def accepted {X : Type u} (r : Record X) (s : Set X) : Prop :=
  r.choose Bool (characteristic s) = true

private theorem characteristic_compl {X : Type u} (s : Set X) :
    characteristic sᶜ = Bool.not ∘ characteristic s := by
  funext x
  simp [characteristic]

private theorem characteristic_inter {X : Type u} (s t : Set X) :
    characteristic (s ∩ t) = (fun p : Bool × Bool => p.1 && p.2) ∘
      (fun x => (characteristic s x, characteristic t x)) := by
  funext x
  simp [characteristic]

@[simp] theorem accepted_univ {X : Type u} (r : Record X) : accepted r univ := by
  have h : characteristic (univ : Set X) = (fun _ => true) := by
    funext x
    simp [characteristic]
  change r.choose Bool (characteristic univ) = true
  rw [h]
  exact r.choose_const Bool true

@[simp] theorem accepted_inter {X : Type u} (r : Record X) (s t : Set X) :
    accepted r (s ∩ t) ↔ accepted r s ∧ accepted r t := by
  unfold accepted
  rw [characteristic_inter, ← r.natural, r.choose_pair]
  simp

@[simp] theorem accepted_compl {X : Type u} (r : Record X) (s : Set X) :
    accepted r sᶜ ↔ ¬ accepted r s := by
  unfold accepted
  rw [characteristic_compl, ← r.natural]
  simp

def toFilter {X : Type u} (r : Record X) : Filter X where
  sets := {s | accepted r s}
  univ_sets := accepted_univ r
  sets_of_superset := by
    intro s t hs hst
    have hst' : s ∩ t = s := inter_eq_self_of_subset_left hst
    have hacc : accepted r (s ∩ t) := by simpa only [hst'] using hs
    have := (accepted_inter r s t).mp hacc
    exact this.2
  inter_sets := fun hs ht => (accepted_inter r _ _).mpr ⟨hs,ht⟩

def toUltrafilter {X : Type u} (r : Record X) : Ultrafilter X :=
  Ultrafilter.ofComplNotMemIff (toFilter r) (by
    intro s
    change (¬ accepted r sᶜ) ↔ accepted r s
    rw [accepted_compl, not_not])

@[simp] theorem mem_toUltrafilter {X : Type u} (r : Record X) (s : Set X) :
    s ∈ toUltrafilter r ↔ accepted r s := Iff.rfl

/-- The selected finite fibre is exactly the fibre belonging to the ultrafilter. -/
theorem choose_fibre {X : Type u} (r : Record X) (A : Type) [Fintype A]
    (f : X → A) (a : A) :
    f ⁻¹' {a} ∈ toUltrafilter r ↔ r.choose A f = a := by
  classical
  rw [mem_toUltrafilter]
  unfold accepted
  have h : characteristic (f ⁻¹' {a}) = (fun z : A => decide (z = a)) ∘ f := rfl
  rw [h, ← r.natural]
  simp

def selected {X : Type u} (U : Ultrafilter X) (A : Type) [Fintype A] (f : X → A) : A :=
  (Ultrafilter.eq_pure_of_finite (U.map f)).choose

theorem selected_spec {X : Type u} (U : Ultrafilter X) (A : Type) [Fintype A] (f : X → A) :
    U.map f = pure (selected U A f) := (Ultrafilter.eq_pure_of_finite (U.map f)).choose_spec

theorem selected_fibre {X : Type u} (U : Ultrafilter X) (A : Type) [Fintype A]
    (f : X → A) (a : A) : f ⁻¹' {a} ∈ U ↔ selected U A f = a := by
  have h := selected_spec U A f
  have he : ({a} : Set A) ∈ U.map f ↔ selected U A f ∈ ({a} : Set A) := by rw [h]; rfl
  exact he

def ofUltrafilter {X : Type u} (U : Ultrafilter X) : Record X where
  choose := selected U
  natural A B _ _ f g := by
    have h : U.map (g ∘ f) = pure (g (selected U A f)) := by
      rw [← Ultrafilter.map_map, selected_spec U A f, Ultrafilter.map_pure]
    exact Ultrafilter.pure_injective ((selected_spec U B (g ∘ f)).symm.trans h) |>.symm

@[simp] theorem to_of {X : Type u} (U : Ultrafilter X) : toUltrafilter (ofUltrafilter U) = U := by
  classical
  ext s
  change selected U Bool (characteristic s) = true ↔ s ∈ U
  have h := (selected_fibre U Bool (characteristic s) true).symm
  convert h using 2
  ext x
  simp [characteristic]

@[simp] theorem of_to {X : Type u} (r : Record X) : ofUltrafilter (toUltrafilter r) = r := by
  ext A inst f
  apply (selected_fibre (toUltrafilter r) A f (r.choose A f)).mp
  exact (choose_fibre r A f (r.choose A f)).mpr rfl

def classification (X : Type u) : Record X ≃ Ultrafilter X where
  toFun := toUltrafilter
  invFun := ofUltrafilter
  left_inv := of_to
  right_inv := to_of

@[simp] theorem to_point {X : Type u} (x : X) : toUltrafilter (Record.point x) = pure x := by
  ext s
  simp [accepted, characteristic, Record.point]

@[simp] theorem to_map {X : Type u} {Y : Type v} (f : X → Y) (r : Record X) :
    toUltrafilter (Record.map f r) = (toUltrafilter r).map f := by
  ext s
  rfl

@[simp] theorem to_flatten {X : Type u} (R : Record (Record X)) :
    toUltrafilter (Record.flatten R) = (toUltrafilter R).bind toUltrafilter := by
  classical
  ext s
  change R.choose Bool (fun r => r.choose Bool (characteristic s)) = true ↔
    R.choose Bool (characteristic {r | accepted r s}) = true
  have hfun : (fun r : Record X => r.choose Bool (characteristic s)) =
      characteristic {r | accepted r s} := by
    funext r
    simp only [characteristic, accepted, mem_setOf_eq, Bool.decide_eq_true]
  rw [hfun]


/-- Multiplication compatibility in the usual join-and-pushforward notation. -/
theorem to_flatten_join {X : Type u} (R : Record (Record X)) :
    toUltrafilter (Record.flatten R) = joinM ((toUltrafilter R).map toUltrafilter) := by
  rw [to_flatten]
  rfl

/-- Every finite test type in any universe is recovered from a finite skeleton. -/
def Record.evalFinite {X : Type u} (r : Record X) (A : Type v) [Fintype A] (f : X → A) : A :=
  (Fintype.equivFin A).symm (r.choose (Fin (Fintype.card A)) (Fintype.equivFin A ∘ f))

theorem evalFinite_natural {X : Type u} (r : Record X)
    (A : Type v) (B : Type w) [Fintype A] [Fintype B] (f : X → A) (g : A → B) :
    g (r.evalFinite A f) = r.evalFinite B (g ∘ f) := by
  apply (Fintype.equivFin B).injective
  simp only [Record.evalFinite, Equiv.apply_symm_apply]
  have h := r.natural (Fin (Fintype.card A)) (Fin (Fintype.card B))
    (Fintype.equivFin A ∘ f) (Fintype.equivFin B ∘ g ∘ (Fintype.equivFin A).symm)
  simpa only [comp_def, Equiv.symm_apply_apply] using h



/-- Extension agrees with every original test, not just the finite skeleton. -/
theorem evalFinite_agrees {X : Type u} (r : Record X) (A : Type) [Fintype A] (f : X → A) :
    r.evalFinite A f = r.choose A f := by
  apply (Fintype.equivFin A).injective
  simp only [Record.evalFinite, Equiv.apply_symm_apply]
  exact (r.natural A (Fin (Fintype.card A)) f (Fintype.equivFin A)).symm

/-- The transported value satisfies every map to a skeletal finite test. -/
theorem evalFinite_tests {X : Type u} (r : Record X) (A : Type v) [Fintype A]
    (f : X → A) (n : ℕ) (g : A → Fin n) :
    g (r.evalFinite A f) = r.choose (Fin n) (g ∘ f) := by
  exact (evalFinite_natural r A (Fin n) f g).trans (evalFinite_agrees r (Fin n) (g ∘ f))

/-- These naturality requirements uniquely determine the extension to any finite universe. -/
theorem evalFinite_unique {X : Type u} (r : Record X) (A : Type v) [Fintype A]
    (f : X → A) (a : A)
    (h : ∀ (n : ℕ) (g : A → Fin n), g a = r.choose (Fin n) (g ∘ f)) :
    a = r.evalFinite A f := by
  apply (Fintype.equivFin A).injective
  simp only [Record.evalFinite, Equiv.apply_symm_apply]
  exact h (Fintype.card A) (Fintype.equivFin A)

/-- Point records are never identified. -/
theorem point_injective (X : Type u) : Injective (Record.point : X → Record X) := by
  intro x y h
  apply Ultrafilter.pure_injective
  simpa only [to_point] using congrArg toUltrafilter h

/-- A record from a free ultrafilter is not evaluation at any point. -/
theorem free_record_not_point (X : Type u) [Infinite X] (x : X) :
    ofUltrafilter (hyperfilter X) ≠ Record.point x := by
  intro h
  have hU : hyperfilter X = pure x := by simpa using congrArg toUltrafilter h
  have hm : ({x} : Set X) ∈ hyperfilter X := by rw [hU]; simp
  exact (Set.finite_singleton x).notMem_hyperfilter hm

/-- Exact finite/infinite boundary, including the empty set. -/
theorem point_surjective_iff_finite (X : Type u) :
    Surjective (Record.point : X → Record X) ↔ Finite X := by
  constructor
  · intro h
    by_contra hfin
    letI : Infinite X := not_finite_iff_infinite.mp hfin
    obtain ⟨x,hx⟩ := h (ofUltrafilter (hyperfilter X))
    exact free_record_not_point X x hx.symm
  · intro hfin
    letI : Finite X := hfin
    intro r
    obtain ⟨x,hx⟩ := Ultrafilter.eq_pure_of_finite (toUltrafilter r)
    refine ⟨x,(classification X).injective ?_⟩
    change toUltrafilter (Record.point x) = toUltrafilter r
    rw [to_point]
    exact hx.symm

end MathGauge.FiniteObservations
