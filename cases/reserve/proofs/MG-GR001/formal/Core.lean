import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Tactic

noncomputable section
open scoped BigOperators ENNReal NNReal Matrix.Norms.Operator
open Matrix

namespace MathGauge.RecursiveClosure

/-- The nonabsorbing part of the stated finite gauge. No separation is assumed. -/
structure Gauge (Y I : Type) where
  d : I → Y → Y → ℝ≥0∞
  self : ∀ i x, d i x x = 0
  symm : ∀ i x y, d i x y = d i y x
  triangle : ∀ i x y z, d i x z ≤ d i x y + d i y z

/-- Add the isolated absorbing point to any nonabsorbing gauge. -/
def liftDistance {Y I : Type} (g : Gauge Y I) (i : I) : Option Y → Option Y → ℝ≥0∞
  | none, none => 0
  | some x, some y => g.d i x y
  | _, _ => ⊤

theorem lift_self {Y I : Type} (g : Gauge Y I) (i : I) (x : Option Y) :
    liftDistance g i x x = 0 := by
  cases x <;> simp [liftDistance, g.self]

theorem lift_symm {Y I : Type} (g : Gauge Y I) (i : I) (x y : Option Y) :
    liftDistance g i x y = liftDistance g i y x := by
  cases x <;> cases y <;> simp [liftDistance, g.symm]

theorem lift_triangle {Y I : Type} (g : Gauge Y I) (i : I) (x y z : Option Y) :
    liftDistance g i x z ≤ liftDistance g i x y + liftDistance g i y z := by
  cases x <;> cases y <;> cases z <;> simp [liftDistance, g.triangle]

theorem lift_bottom_isolated {Y I : Type} (g : Gauge Y I) (i : I) (x : Y) :
    liftDistance g i (some x) none = ⊤ := rfl

/-- A typed encoding of the disjoint stop/call partition. `step` stores only
the given terminal output or the given edge and routed input, never a solution. -/
structure System (Y V E I : Type) [Fintype I] (g : Gauge Y I) where
  Input : V → Type
  src : E → V
  dst : E → V
  step : (v : V) → Input v → Y ⊕ ((e : E) × Input (dst e))
  step_src : ∀ v x e z, step v x = Sum.inr ⟨e,z⟩ → src e = v
  ret : E → Y → Y
  L : E → I → I → ℝ≥0
  lip : ∀ e i x y, g.d i (ret e x) (ret e y) ≤ ∑ j, (L e i j : ℝ≥0∞) * g.d j x y

namespace System
variable {Y V E I : Type} [Fintype I] {g : Gauge Y I}

abbrev Family (s : System Y V E I g) := (v : V) → s.Input v → Y
abbrev PartialFamily (s : System Y V E I g) := (v : V) → s.Input v → Option Y

def transform (s : System Y V E I g) (F : s.Family) : s.Family := fun v x =>
  match s.step v x with
  | Sum.inl y => y
  | Sum.inr ⟨e,z⟩ => s.ret e (F (s.dst e) z)

def partialTransform (s : System Y V E I g) (F : s.PartialFamily) : s.PartialFamily :=
  fun v x => match s.step v x with
  | Sum.inl y => some y
  | Sum.inr ⟨e,z⟩ => (F (s.dst e) z).map (s.ret e)

theorem transform_some (s : System Y V E I g) (F : s.Family) :
    s.partialTransform (fun v x => some (F v x)) = fun v x => some (s.transform F v x) := by
  funext v x
  cases h : s.step v x with
  | inl y => simp [partialTransform,transform,h]
  | inr ez => rcases ez with ⟨e,z⟩; simp [partialTransform,transform,h]

def delta (s : System Y V E I g) (F G : s.Family) (vi : V × I) : ℝ≥0∞ :=
  ⨆ x : s.Input vi.1, g.d vi.2 (F vi.1 x) (G vi.1 x)

theorem point_le_delta (s : System Y V E I g) (F G : s.Family) (v : V) (i : I)
    (x : s.Input v) : g.d i (F v x) (G v x) ≤ s.delta F G (v,i) :=
  le_iSup (fun x => g.d i (F v x) (G v x)) x

def gainAction [Fintype E] [DecidableEq V] (s : System Y V E I g)
    (u : V × I → ℝ≥0∞) (vi : V × I) : ℝ≥0∞ :=
  ∑ e, if s.src e = vi.1 then ∑ j, (s.L e vi.2 j : ℝ≥0∞) * u (s.dst e,j) else 0

theorem gainAction_mono [Fintype E] [DecidableEq V] (s : System Y V E I g)
    {u w : V × I → ℝ≥0∞} (h : u ≤ w) : s.gainAction u ≤ s.gainAction w := by
  intro vi
  apply Finset.sum_le_sum
  intro e he
  split_ifs
  · exact Finset.sum_le_sum fun j _ => mul_le_mul_left' (h _) _
  · rfl

theorem delta_transform [Fintype E] [DecidableEq V] (s : System Y V E I g)
    (F G : s.Family) : s.delta (s.transform F) (s.transform G) ≤ s.gainAction (s.delta F G) := by
  rintro ⟨v,i⟩
  apply iSup_le
  intro x
  cases h : s.step v x with
  | inl y => simp [transform, h, g.self]
  | inr ez =>
    rcases ez with ⟨e,z⟩
    have hsrc := s.step_src v x e z h
    calc
      g.d i (s.transform F v x) (s.transform G v x)
          = g.d i (s.ret e (F (s.dst e) z)) (s.ret e (G (s.dst e) z)) := by simp [transform,h]
      _ ≤ ∑ j, (s.L e i j : ℝ≥0∞) * g.d j (F (s.dst e) z) (G (s.dst e) z) := s.lip _ _ _ _
      _ ≤ ∑ j, (s.L e i j : ℝ≥0∞) * s.delta F G (s.dst e,j) :=
        Finset.sum_le_sum fun j _ => mul_le_mul_left' (s.point_le_delta F G _ j z) _
      _ ≤ s.gainAction (s.delta F G) (v,i) := by
        have hh := Finset.single_le_sum (f := fun e' =>
          if s.src e' = v then ∑ j, (s.L e' i j : ℝ≥0∞) * s.delta F G (s.dst e',j) else 0)
          (fun e' _ => bot_le) (Finset.mem_univ e)
        simpa [gainAction,hsrc] using hh

theorem delta_iterate [Fintype E] [DecidableEq V] (s : System Y V E I g)
    (F G : s.Family) (n : ℕ) :
    s.delta (s.transform^[n] F) (s.transform^[n] G) ≤ s.gainAction^[n] (s.delta F G) := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    simp only [Function.iterate_succ_apply']
    exact (s.delta_transform _ _).trans (s.gainAction_mono ih)

end System

namespace Counterexample

abbrev Y := ℝ × ℝ
def coordinate (i : Fin 2) (x : Y) : ℝ := if i = 0 then x.1 else x.2

def gauge : Gauge Y (Fin 2) where
  d i x y := ENNReal.ofReal |coordinate i x - coordinate i y|
  self := by intros; simp
  symm := by intros; rw [abs_sub_comm]
  triangle := by
    intro i x y z
    rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (abs_sub_le _ _ _)

theorem gauge_separates (x y : Y) (h : ∀ i, gauge.d i x y = 0) : x = y := by
  have h0 := h 0
  have h1 := h 1
  simp [gauge,coordinate, ENNReal.ofReal_eq_zero, abs_nonpos_iff] at h0 h1
  exact Prod.ext (sub_eq_zero.mp h0) (sub_eq_zero.mp h1)

/-- The underlying nonabsorbing output space really is complete R². -/
theorem output_complete : CompleteSpace Y := inferInstance

def ret : Bool → Y → Y
  | false, x => (x.2 / 2, 0)
  | true, x => (0, x.1 / 2)

def L : Bool → Fin 2 → Fin 2 → ℝ≥0
  | false => !![0, 1/2; 0, 0]
  | true => !![0, 0; 1/2, 0]

theorem half_abs (a b : ℝ) :
    ENNReal.ofReal |a/2-b/2| = (2:ℝ≥0∞)⁻¹ * ENNReal.ofReal |a-b| := by
  rw [← sub_div, abs_div]
  norm_num
  rw [div_eq_mul_inv, ENNReal.ofReal_mul (abs_nonneg _)]
  rw [ENNReal.ofReal_inv_of_pos (by norm_num)]
  norm_num [mul_comm]

theorem ret_lip (e : Bool) (i : Fin 2) (x y : Y) :
    gauge.d i (ret e x) (ret e y) ≤ ∑ j, (L e i j : ℝ≥0∞) * gauge.d j x y := by
  cases e <;> fin_cases i <;>
    simp [gauge,coordinate,ret,L,Fin.sum_univ_two,half_abs]

abbrev sys : System Y Bool Bool (Fin 2) gauge where
  Input _ := ℤ
  src := id
  dst := Bool.not
  step v n := if n ≤ 0 then Sum.inl (0,0)
    else Sum.inr ⟨v, if v then n+1 else n⟩
  step_src := by
    intro v n e z h
    dsimp only [id] at h ⊢
    by_cases hn : n ≤ 0
    · simp [hn] at h
    · simp only [hn,if_false] at h
      cases h; rfl
  ret := ret
  L := L
  lip := ret_lip

/-- The integer input is a faithful parametrization of the actual subset {(n,0)}. -/
def inputEmbedding (n : ℤ) : Y := (n,0)
theorem inputEmbedding_injective : Function.Injective inputEmbedding := by
  intro a b h
  have hc := congrArg Prod.fst h
  change (a:ℝ) = (b:ℝ) at hc
  exact_mod_cast hc

def solution (c : ℝ) : sys.Family := fun v n =>
  if n ≤ 0 then (0,0)
  else if v then (0, 2*c*4^n) else (c*4^n,0)

theorem solution_fixed (c : ℝ) : sys.transform (solution c) = solution c := by
  funext v n
  change ℤ at n
  by_cases hn : n ≤ 0
  · simp [System.transform,sys,solution,hn]
  · have hn' : ¬ n+1 ≤ 0 := by omega
    have hp : (4:ℝ)^(n+1) = (4:ℝ)^n * 4 := by rw [zpow_add₀ (by norm_num)]; simp
    cases v <;> simp [System.transform,sys,solution,hn,hn',ret,hp] <;> ring

theorem solution_injective : Function.Injective solution := by
  intro c d h
  have hx := congrArg (fun F : sys.Family => (F false 1).1) h
  simp [solution] at hx
  linarith

theorem not_unique_fixed : ¬ ∃! F : sys.Family, sys.transform F = F := by
  rintro ⟨F,hF,huniq⟩
  have h := (huniq _ (solution_fixed 0)).trans (huniq _ (solution_fixed 1)).symm
  have : (0:ℝ) = 1 := solution_injective h
  norm_num at this

def M : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0,0,0,1/2; 0,0,0,0; 0,0,0,0; 1/2,0,0,0]

theorem matrix_norm : ‖M‖₊ = (1/2 : ℝ≥0) := by
  rw [Matrix.linfty_opNNNorm_def]
  simp [M, show (Finset.univ : Finset (Fin 4)) = {0,1,2,3} by decide]

theorem matrix_spectral_lt_one : spectralRadius ℂ M < 1 := by
  calc
    spectralRadius ℂ M ≤ (↑‖M‖₊ : ℝ≥0∞) := spectrum.spectralRadius_le_nnnorm M
    _ < 1 := by rw [matrix_norm]; norm_num

end Counterexample
end MathGauge.RecursiveClosure
