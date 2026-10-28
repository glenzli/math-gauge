import Std

/-!
A compiler-unchecked Lean 4.29.1 standard-library candidate.

The code does not assume a concrete extended-real implementation.  `view`
represents static observational equivalence; `Envelope` represents the
monotone action of upper-bound certificates on a preorder of gauge vectors.
The correspondence with the original metric and matrix data is described in
round-3.md.
-/

universe uA uX uO uY uI uC uV

namespace GaugeCore

structure System (A : Type uA) (X : Type uX) (O : Type uO) where
  bottom : X
  step : A → X → X
  step_bottom : ∀ a, step a bottom = bottom
  view : X → O
  view_bottom : ∀ x, view x = view bottom → x = bottom

namespace System

variable {A : Type uA} {X : Type uX} {O : Type uO}

/-- Words are executed from left to right. -/
def run (S : System A X O) : List A → X → X
  | [], x => x
  | a :: w, x => run S w (S.step a x)

theorem run_append (S : System A X O) :
    ∀ (u v : List A) (x : X),
      S.run (u ++ v) x = S.run v (S.run u x) := by
  intro u
  induction u with
  | nil =>
      intro v x
      rfl
  | cons a u ih =>
      intro v x
      change S.run (u ++ v) (S.step a x) =
        S.run v (S.run u (S.step a x))
      exact ih v (S.step a x)

theorem run_bottom (S : System A X O) (w : List A) :
    S.run w S.bottom = S.bottom := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      change S.run w (S.step a S.bottom) = S.bottom
      rw [S.step_bottom a]
      exact ih

/-- Equality of all finite future static observations. -/
def TraceEq (S : System A X O) (x y : X) : Prop :=
  ∀ w : List A, S.view (S.run w x) = S.view (S.run w y)

theorem trace_head (S : System A X O) (x y : X)
    (h : S.TraceEq x y) : S.view x = S.view y := by
  exact h []

theorem trace_step (S : System A X O) (a : A) (x y : X)
    (h : S.TraceEq x y) : S.TraceEq (S.step a x) (S.step a y) := by
  intro w
  exact h (a :: w)

def traceSetoid (S : System A X O) : Setoid X where
  r := S.TraceEq
  iseqv := by
    constructor
    · intro x w
      rfl
    · intro x y h w
      exact (h w).symm
    · intro x y z hxy hyz w
      exact (hxy w).trans (hyz w)

def State (S : System A X O) : Type uX := Quotient S.traceSetoid

def pack (S : System A X O) (x : X) : S.State :=
  Quotient.mk S.traceSetoid x

theorem pack_eq_of_trace (S : System A X O) (x y : X)
    (h : S.TraceEq x y) : S.pack x = S.pack y := by
  exact Quotient.sound h

theorem trace_of_pack_eq (S : System A X O) (x y : X)
    (h : S.pack x = S.pack y) : S.TraceEq x y := by
  exact Quotient.exact h

def qstep (S : System A X O) (a : A) : S.State → S.State :=
  Quotient.lift (fun x : X => S.pack (S.step a x)) (by
    intro x y h
    exact Quotient.sound (S.trace_step a x y h))

@[simp] theorem qstep_pack (S : System A X O) (a : A) (x : X) :
    S.qstep a (S.pack x) = S.pack (S.step a x) := by
  rfl

def qrun (S : System A X O) : List A → S.State → S.State
  | [], p => p
  | a :: w, p => qrun S w (S.qstep a p)

theorem qrun_append (S : System A X O) :
    ∀ (u v : List A) (p : S.State),
      S.qrun (u ++ v) p = S.qrun v (S.qrun u p) := by
  intro u
  induction u with
  | nil =>
      intro v p
      rfl
  | cons a u ih =>
      intro v p
      change S.qrun (u ++ v) (S.qstep a p) =
        S.qrun v (S.qrun u (S.qstep a p))
      exact ih v (S.qstep a p)

theorem qrun_pack (S : System A X O) :
    ∀ (w : List A) (x : X),
      S.qrun w (S.pack x) = S.pack (S.run w x) := by
  intro w
  induction w with
  | nil =>
      intro x
      rfl
  | cons a w ih =>
      intro x
      change S.qrun w (S.pack (S.step a x)) =
        S.pack (S.run w (S.step a x))
      exact ih (S.step a x)

def qbottom (S : System A X O) : S.State := S.pack S.bottom

theorem pack_bottom_iff (S : System A X O) (x : X) :
    S.pack x = S.qbottom ↔ x = S.bottom := by
  constructor
  · intro h
    have ht : S.TraceEq x S.bottom := Quotient.exact h
    exact S.view_bottom x (ht [])
  · intro h
    change S.pack x = S.pack S.bottom
    rw [h]

theorem qrun_bottom (S : System A X O) (w : List A) :
    S.qrun w S.qbottom = S.qbottom := by
  calc
    S.qrun w S.qbottom = S.pack (S.run w S.bottom) :=
      S.qrun_pack w S.bottom
    _ = S.pack S.bottom := congrArg S.pack (S.run_bottom w)
    _ = S.qbottom := rfl

def Defined (S : System A X O) (w : List A) (x : X) : Prop :=
  S.run w x ≠ S.bottom

def QDefined (S : System A X O) (w : List A) (p : S.State) : Prop :=
  S.qrun w p ≠ S.qbottom

theorem defined_iff_qdefined (S : System A X O) (w : List A) (x : X) :
    S.QDefined w (S.pack x) ↔ S.Defined w x := by
  unfold QDefined Defined
  rw [S.qrun_pack w x]
  constructor
  · intro hn hx
    exact hn (congrArg S.pack hx)
  · intro hn hp
    exact hn ((S.pack_bottom_iff (S.run w x)).mp hp)

/-- A single static observation descends to the trajectory quotient. -/
def qview (S : System A X O) : S.State → O :=
  Quotient.lift S.view (by
    intro x y h
    exact h [])

@[simp] theorem qview_pack (S : System A X O) (x : X) :
    S.qview (S.pack x) = S.view x := by
  rfl

/-- All future quotient views separate quotient states. -/
theorem state_ext (S : System A X O) (p q : S.State)
    (h : ∀ w : List A, S.qview (S.qrun w p) = S.qview (S.qrun w q)) :
    p = q := by
  revert h
  refine Quotient.inductionOn p ?_
  intro x
  refine Quotient.inductionOn q ?_
  intro y h
  apply Quotient.sound
  intro w
  have hw := h w
  rw [S.qrun_pack w x, S.qrun_pack w y] at hw
  change S.view (S.run w x) = S.view (S.run w y) at hw
  exact hw

/-- Any pairwise reading defined on the static observations is preserved. -/
def qread {I : Type uI} {V : Type uV} (S : System A X O)
    (read : I → O → O → V) (i : I) (p q : S.State) : V :=
  read i (S.qview p) (S.qview q)

theorem qread_run {I : Type uI} {V : Type uV} (S : System A X O)
    (read : I → O → O → V) (i : I) (w : List A) (x y : X) :
    S.qread read i (S.qrun w (S.pack x)) (S.qrun w (S.pack y)) =
      read i (S.view (S.run w x)) (S.view (S.run w y)) := by
  unfold qread
  rw [S.qrun_pack w x, S.qrun_pack w y]
  rfl

/-- A step-invariant relation remains invariant under every word. -/
theorem relation_run (S : System A X O) (R : X → X → Prop)
    (hstep : ∀ (a : A) (x y : X), R x y → R (S.step a x) (S.step a y)) :
    ∀ (w : List A) (x y : X), R x y → R (S.run w x) (S.run w y) := by
  intro w
  induction w with
  | nil =>
      intro x y h
      exact h
  | cons a w ih =>
      intro x y h
      exact ih (S.step a x) (S.step a y) (hstep a x y h)

/-- Any step-invariant relation refining static observations refines TraceEq. -/
theorem trace_greatest (S : System A X O) (R : X → X → Prop)
    (hobs : ∀ x y, R x y → S.view x = S.view y)
    (hstep : ∀ (a : A) (x y : X), R x y → R (S.step a x) (S.step a y))
    (x y : X) (h : R x y) : S.TraceEq x y := by
  intro w
  exact hobs (S.run w x) (S.run w y) (S.relation_run R hstep w x y h)

/-- The kernel of another realization. -/
def kernelSetoid {Y : Type uY} (p : X → Y) : Setoid X where
  r := fun x y => p x = p y
  iseqv := by
    constructor
    · intro x
      rfl
    · intro x y h
      exact h.symm
    · intro x y z hxy hyz
      exact hxy.trans hyz

/-- The trajectory quotient factors through any observationally sound realization. -/
def factorKernel {Y : Type uY} (S : System A X O) (p : X → Y)
    (g : A → Y → Y)
    (hobs : ∀ x y, p x = p y → S.view x = S.view y)
    (hstep : ∀ (a : A) (x : X), p (S.step a x) = g a (p x)) :
    Quotient (kernelSetoid p) → S.State :=
  Quotient.lift S.pack (by
    intro x y h
    have stable : ∀ (a : A) (x y : X),
        p x = p y → p (S.step a x) = p (S.step a y) := by
      intro a x y hxy
      calc
        p (S.step a x) = g a (p x) := hstep a x
        _ = g a (p y) := congrArg (g a) hxy
        _ = p (S.step a y) := (hstep a y).symm
    exact Quotient.sound
      (S.trace_greatest (fun x y => p x = p y) hobs stable x y h))

theorem factorKernel_mk {Y : Type uY} (S : System A X O) (p : X → Y)
    (g : A → Y → Y)
    (hobs : ∀ x y, p x = p y → S.view x = S.view y)
    (hstep : ∀ (a : A) (x : X), p (S.step a x) = g a (p x))
    (x : X) :
    S.factorKernel p g hobs hstep (Quotient.mk (kernelSetoid p) x) =
      S.pack x := by
  rfl

/-- A component is a projection of the static observation. -/
def qCompTrace {I : Type uI} {C : I → Type uC} (S : System A X O)
    (project : (i : I) → O → C i) (i : I) (p q : S.State) : Prop :=
  ∀ w : List A,
    project i (S.qview (S.qrun w p)) = project i (S.qview (S.qrun w q))

def qCompKernel {I : Type uI} {C : I → Type uC} (S : System A X O)
    (project : (i : I) → O → C i) (i : I) (w : List A)
    (p q : S.State) : Prop :=
  S.qCompTrace project i (S.qrun w p) (S.qrun w q)

theorem qCompKernel_equivalence {I : Type uI} {C : I → Type uC}
    (S : System A X O) (project : (i : I) → O → C i)
    (i : I) (w : List A) :
    Equivalence (fun p q : S.State => S.qCompKernel project i w p q) := by
  constructor
  · intro p v
    rfl
  · intro p q h v
    exact (h v).symm
  · intro p q r hpq hqr v
    exact (hpq v).trans (hqr v)

theorem qCompKernel_prefix {I : Type uI} {C : I → Type uC}
    (S : System A X O) (project : (i : I) → O → C i)
    (i : I) (u v : List A) (p q : S.State)
    (h : S.qCompKernel project i u p q) :
    S.qCompKernel project i (u ++ v) p q := by
  unfold qCompKernel qCompTrace at h ⊢
  intro t
  have ht := h (v ++ t)
  rw [S.qrun_append v t (S.qrun u p), S.qrun_append v t (S.qrun u q)] at ht
  rw [S.qrun_append u v p, S.qrun_append u v q]
  exact ht

theorem all_components_iff_kernel {I : Type uI} {C : I → Type uC}
    (S : System A X O) (project : (i : I) → O → C i)
    (separates : ∀ o₁ o₂ : O, (∀ i, project i o₁ = project i o₂) → o₁ = o₂)
    (w : List A) (p q : S.State) :
    (∀ i, S.qCompKernel project i w p q) ↔ S.qrun w p = S.qrun w q := by
  constructor
  · intro h
    apply S.state_ext
    intro v
    apply separates
    intro i
    exact h i v
  · intro h i v
    exact congrArg (fun z => project i (S.qview (S.qrun v z))) h

/-- Abstract upper-bound propagation; no concrete matrix arithmetic is assumed. -/
structure Envelope (S : System A X O) (V : Type uV) where
  rel : V → V → Prop
  rel_refl : ∀ v, rel v v
  rel_trans : ∀ u v w, rel u v → rel v w → rel u w
  gauge : X → X → V
  transfer : A → V → V
  transfer_mono : ∀ a u v, rel u v → rel (transfer a u) (transfer a v)
  step_bound : ∀ a x y,
    S.step a x ≠ S.bottom → S.step a y ≠ S.bottom →
    rel (gauge (S.step a x) (S.step a y)) (transfer a (gauge x y))

namespace Envelope

variable {V : Type uV} {S : System A X O}

def wordMap (E : Envelope S V) : List A → V → V
  | [], v => v
  | a :: w, v => wordMap E w (E.transfer a v)

theorem wordMap_mono (E : Envelope S V) :
    ∀ (w : List A) (u v : V),
      E.rel u v → E.rel (E.wordMap w u) (E.wordMap w v) := by
  intro w
  induction w with
  | nil =>
      intro u v h
      exact h
  | cons a w ih =>
      intro u v h
      exact ih (E.transfer a u) (E.transfer a v) (E.transfer_mono a u v h)

/-- A final successful pair permits all intermediate bounds to be composed. -/
theorem word_bound (E : Envelope S V) :
    ∀ (w : List A) (x y : X),
      S.run w x ≠ S.bottom → S.run w y ≠ S.bottom →
      E.rel (E.gauge (S.run w x) (S.run w y))
        (E.wordMap w (E.gauge x y)) := by
  intro w
  induction w with
  | nil =>
      intro x y hx hy
      exact E.rel_refl (E.gauge x y)
  | cons a w ih =>
      intro x y hx hy
      have hxTail : S.run w (S.step a x) ≠ S.bottom := hx
      have hyTail : S.run w (S.step a y) ≠ S.bottom := hy
      have hxStep : S.step a x ≠ S.bottom := by
        intro h
        apply hxTail
        calc
          S.run w (S.step a x) = S.run w S.bottom := congrArg (S.run w) h
          _ = S.bottom := S.run_bottom w
      have hyStep : S.step a y ≠ S.bottom := by
        intro h
        apply hyTail
        calc
          S.run w (S.step a y) = S.run w S.bottom := congrArg (S.run w) h
          _ = S.bottom := S.run_bottom w
      have tailBound := ih (S.step a x) (S.step a y) hxTail hyTail
      have liftedBound := E.wordMap_mono w
        (E.gauge (S.step a x) (S.step a y))
        (E.transfer a (E.gauge x y))
        (E.step_bound a x y hxStep hyStep)
      exact E.rel_trans _ _ _ tailBound liftedBound

end Envelope
end System

/-! A small example where static observations agree but future behavior differs. -/
namespace Example

inductive Toy where
  | bot
  | p
  | q
  deriving DecidableEq

def toyView : Toy → Bool
  | .bot => false
  | .p => true
  | .q => true

def toyStep : Unit → Toy → Toy
  | _, .bot => .bot
  | _, .p => .p
  | _, .q => .bot

def toy : System Unit Toy Bool where
  bottom := .bot
  step := toyStep
  step_bottom := by
    intro a
    rfl
  view := toyView
  view_bottom := by
    intro x h
    cases x with
    | bot => rfl
    | p => cases h
    | q => cases h

theorem static_same : toy.view Toy.p = toy.view Toy.q := by
  rfl

theorem future_distinct : toy.pack Toy.p ≠ toy.pack Toy.q := by
  intro h
  have ht : toy.TraceEq Toy.p Toy.q := Quotient.exact h
  have h1 := ht [()]
  change true = false at h1
  cases h1

end Example
end GaugeCore
