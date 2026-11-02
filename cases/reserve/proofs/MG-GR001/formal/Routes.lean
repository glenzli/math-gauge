import Partial

noncomputable section
namespace MathGauge.RecursiveClosure.System
variable {Y V E I : Type} [Fintype I] {g : Gauge Y I}

/-- A finite sequence of actual calls, storing the return composition in execution order. -/
inductive Calls (s : System Y V E I g) :
    ℕ → (v : V) → s.Input v → (w : V) → s.Input w → (Y → Y) → Prop
  | zero (v) (x : s.Input v) : Calls s 0 v x v x id
  | step {v x e z n w y f}
      (hs : s.step v x = Sum.inr ⟨e,z⟩)
      (tail : Calls s n (s.dst e) z w y f) :
      Calls s (n+1) v x w y (s.ret e ∘ f)

theorem calls_unfold (s : System Y V E I g) (H : s.Family)
    {n v x w y f} (h : s.Calls n v x w y f) :
    s.transform^[n] H v x = f (H w y) := by
  induction h with
  | zero => rfl
  | step hs tail ih => rw [s.iterate_call H hs,ih]; rfl

theorem calls_then_stop (s : System Y V E I g) (H : s.Family)
    {n v x w y f z} (h : s.Calls n v x w y f)
    (hs : s.step w y = Sum.inl z) (k : ℕ) :
    s.transform^[n+(k+1)] H v x = f z := by
  rw [Function.iterate_add_apply]
  rw [s.calls_unfold _ h,s.iterate_stop H hs k]

end MathGauge.RecursiveClosure.System
