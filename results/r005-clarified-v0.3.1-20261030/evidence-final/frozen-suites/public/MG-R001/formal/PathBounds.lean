import Routes
import Bounds

noncomputable section
open scoped BigOperators ENNReal
open Matrix
namespace MathGauge.RecursiveClosure.System
variable {Y V E I : Type} [Fintype I] [DecidableEq I] {g : Gauge Y I}

/-- The actual return composition, in call order, and actual product of local matrices. -/
def pathReturn (s : System Y V E I g) : List E → Y → Y
  | [] => id
  | e::es => s.ret e ∘ s.pathReturn es

def pathMatrix (s : System Y V E I g) : List E → Matrix I I ℝ≥0∞
  | [] => 1
  | e::es => (show Matrix I I ℝ≥0∞ from fun i j => (s.L e i j : ℝ≥0∞)) * s.pathMatrix es

theorem path_lipschitz (s : System Y V E I g) (es : List E) (x y : Y) :
    (fun i => g.d i (s.pathReturn es x) (s.pathReturn es y)) ≤
      s.pathMatrix es *ᵥ (fun i => g.d i x y) := by
  induction es with
  | nil => simp [pathReturn,pathMatrix]
  | cons e es ih =>
    intro i
    change g.d i (s.ret e (s.pathReturn es x)) (s.ret e (s.pathReturn es y)) ≤ _
    calc
      _ ≤ ∑ j, (s.L e i j : ℝ≥0∞) * g.d j (s.pathReturn es x) (s.pathReturn es y) := s.lip e i _ _
      _ ≤ ∑ j, (s.L e i j : ℝ≥0∞) * (s.pathMatrix es *ᵥ fun k => g.d k x y) j :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_right (ih j) _)
      _ = _ := by rw [pathMatrix,← Matrix.mulVec_mulVec]; rfl

/-- This path records only actual selected call branches, not an arbitrary graph path. -/
inductive CallPath (s : System Y V E I g) :
    List E → (v : V) → s.Input v → (w : V) → s.Input w → Prop
  | nil (v x) : CallPath s [] v x v x
  | cons {es v x e z w y} (h : s.step v x=Sum.inr ⟨e,z⟩)
      (tail : CallPath s es (s.dst e) z w y) : CallPath s (e::es) v x w y

theorem CallPath.toCalls {s : System Y V E I g} {es v x w y}
    (h : s.CallPath es v x w y) : s.Calls es.length v x w y (s.pathReturn es) := by
  induction h with
  | nil v x => exact Calls.zero v x
  | cons h tail ih => exact Calls.step h ih

theorem call_path_matrix_bound (s : System Y V E I g) {es v x w y}
    (h : s.CallPath es v x w y) (F G : s.Family) :
    (fun i => g.d i (s.transform^[es.length] F v x) (s.transform^[es.length] G v x)) ≤
      s.pathMatrix es *ᵥ (fun i => g.d i (F w y) (G w y)) := by
  rw [s.calls_unfold F h.toCalls,s.calls_unfold G h.toCalls]
  exact s.path_lipschitz es _ _

end MathGauge.RecursiveClosure.System
