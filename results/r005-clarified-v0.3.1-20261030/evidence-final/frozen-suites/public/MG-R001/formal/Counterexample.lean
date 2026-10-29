import Bounds
import Partial
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Analysis.SpecificLimits.Normed

noncomputable section
open scoped BigOperators ENNReal NNReal Matrix.Norms.Operator
open Matrix Filter Topology
namespace MathGauge.RecursiveClosure.Counterexample

def ix : Fin 4 → Bool × Fin 2 := ![(false,0),(false,1),(true,0),(true,1)]

theorem ix_bijective : Function.Bijective ix := by
  constructor
  · intro a b h; fin_cases a <;> fin_cases b <;> simpa [ix] using h
  · rintro ⟨v,i⟩; cases v <;> fin_cases i
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩
    · exact ⟨3,rfl⟩

/-- The spectral matrix is the actual block aggregation of the given local bounds. -/
theorem M_is_aggregate (a b : Fin 4) :
    M a b = ((sys.coeff (ix a) (ix b) : ℝ≥0) : ℂ) := by
  fin_cases a <;> fin_cases b <;>
    norm_num [M,System.coeff,sys,ix,L,Fintype.sum_bool]

theorem half_in_spectrum : (1/2 : ℂ) ∈ spectrum ℂ M := by
  let v : Fin 4 → ℂ := ![1,0,0,1]
  have he : Matrix.toLinAlgEquiv' M v = (1/2 : ℂ) • v := by
    ext i; fin_cases i <;> norm_num [Matrix.toLinAlgEquiv'_apply,Matrix.mulVec,dotProduct,M,v,Fin.sum_univ_succ]
  have hn : v ≠ 0 := by intro h; have := congrFun h 0; norm_num [v] at this
  have hvec : Module.End.HasEigenvector (Matrix.toLinAlgEquiv' M) (1/2 : ℂ) v :=
    ⟨(Module.End.mem_eigenspace_iff).2 he,hn⟩
  have hh := (Module.End.hasEigenvalue_of_hasEigenvector hvec).mem_spectrum
  simpa only [AlgEquiv.spectrum_eq] using hh

theorem matrix_spectral_eq_half : spectralRadius ℂ M = (1/2 : ℝ≥0∞) := by
  apply le_antisymm
  · calc
      spectralRadius ℂ M ≤ (↑‖M‖₊ : ℝ≥0∞) := spectrum.spectralRadius_le_nnnorm M
      _ = 1/2 := by rw [matrix_norm]; norm_num
  · have hh : (↑‖(1/2 : ℂ)‖₊ : ℝ≥0∞) ≤ spectralRadius ℂ M :=
      le_iSup_of_le (1/2 : ℂ) (le_iSup_of_le half_in_spectrum le_rfl)
    simpa using hh

theorem fixed_families_infinite : Set.Infinite {F : sys.Family | sys.transform F = F} := by
  have hr : Set.range solution ⊆ {F : sys.Family | sys.transform F = F} := by
    rintro F ⟨c,rfl⟩; exact solution_fixed c
  exact (Set.infinite_range_of_injective solution_injective).mono hr

def initial : sys.Family := fun _ n => ((n:ℝ),0)

def stateAfter (k : ℕ) : Bool → ℤ → Y :=
  if k = 0 then initial else sys.transform^[k] initial

theorem unfold_one (H : sys.Family) (n : ℤ) (hn : 0 < n) :
    sys.transform H false n = ret false (H true n) ∧
    sys.transform H true n = ret true (H false (n+1)) := by
  simp [System.transform,sys,not_le.mpr hn,Bool.not]

theorem unfold_formulas (k : ℕ) (n : ℤ) (hn : 0 < n) :
    (sys.transform^[2*k] initial false n = (((n:ℝ)+(k:ℝ)) / 4^k,0)) ∧
    (sys.transform^[2*k+1] initial true n = (0,((n:ℝ)+(k:ℝ)+1) / (2*4^k))) ∧
    (sys.transform^[2*k+1] initial false n = (0,0)) := by
  induction k generalizing n with
  | zero =>
    simp [initial,Function.iterate_one,unfold_one initial n hn,ret]
  | succ k ih =>
    have hn1 : 0 < n+1 := by omega
    have h2 : sys.transform^[2*(k+1)] initial false n =
        ret false (sys.transform^[2*k+1] initial true n) := by
      rw [show 2*(k+1) = (2*k+1)+1 by omega,Function.iterate_succ_apply']
      exact (unfold_one _ n hn).1
    have h3 : sys.transform^[2*(k+1)+1] initial true n =
        ret true (ret false (sys.transform^[2*k+1] initial true (n+1))) := by
      rw [Function.iterate_succ_apply']
      rw [(unfold_one _ n hn).2]
      rw [show 2*(k+1) = (2*k+1)+1 by omega,Function.iterate_succ_apply']
      rw [(unfold_one _ (n+1) hn1).1]
    have hz : sys.transform^[2*(k+1)+1] initial false n = (0,0) := by
      rw [Function.iterate_succ_apply']
      rw [(unfold_one _ n hn).1]
      rw [show 2*(k+1) = (2*k+1)+1 by omega,Function.iterate_succ_apply']
      rw [(unfold_one _ n hn).2, (ih (n+1) hn1).2.2]
      norm_num [ret]
    rw [h2,h3,(ih n hn).2.1,(ih (n+1) hn1).2.1]
    simp only [ret,Prod.mk.injEq,and_true,true_and,Nat.cast_add,Nat.cast_one,Int.cast_add,Int.cast_one,pow_succ]
    refine ⟨?_,?_,hz⟩ <;> ring

theorem no_uniform_even_bound (k : ℕ) (C : ℝ) :
    ∃ n : ℤ, 0 < n ∧ C < (sys.transform^[2*k] initial false n).1 := by
  obtain ⟨n,hn⟩ := exists_nat_gt (max 0 (C*4^k))
  have hn0 : 0 < (n:ℤ) := by
    have : (0:ℝ) < n := lt_of_le_of_lt (le_max_left _ _) hn
    exact_mod_cast this
  refine ⟨n,hn0,?_⟩
  rw [(unfold_formulas k n hn0).1]
  simp only
  apply (lt_div_iff₀ (by positivity : (0:ℝ) < 4^k)).2
  have hcn : C*4^k < (n:ℝ) := lt_of_le_of_lt (le_max_right _ _) hn
  norm_num only [Int.cast_natCast]
  exact lt_of_lt_of_le hcn (le_add_of_nonneg_right (Nat.cast_nonneg _))

theorem no_uniform_odd_bound (k : ℕ) (C : ℝ) :
    ∃ n : ℤ, 0 < n ∧ C < (sys.transform^[2*k+1] initial true n).2 := by
  obtain ⟨n,hn⟩ := exists_nat_gt (max 0 (C*(2*4^k)))
  have hn0 : 0 < (n:ℤ) := by
    have : (0:ℝ) < n := lt_of_le_of_lt (le_max_left _ _) hn
    exact_mod_cast this
  refine ⟨n,hn0,?_⟩
  rw [(unfold_formulas k n hn0).2.1]
  simp only
  apply (lt_div_iff₀ (by positivity : (0:ℝ) < 2*4^k)).2
  have hcn : C*(2*4^k) < (n:ℝ) := lt_of_le_of_lt (le_max_right _ _) hn
  norm_num only [Int.cast_natCast]
  linarith [Nat.cast_nonneg (α := ℝ) k]

theorem even_error_top (k : ℕ) :
    sys.delta (sys.transform^[2*k] initial) (solution 0) (false,0) = ⊤ := by
  apply ENNReal.eq_top_of_forall_nnreal_le
  intro C
  obtain ⟨n,hn,hC⟩ := no_uniform_even_bound k C
  apply le_trans _ (sys.point_le_delta _ _ false 0 n)
  have hnonneg : 0 ≤ (sys.transform^[2*k] initial false n).1 := le_of_lt (lt_of_le_of_lt C.2 hC)
  have hx : gauge.d 0 (sys.transform^[2*k] initial false n) (solution 0 false n) =
      ENNReal.ofReal (sys.transform^[2*k] initial false n).1 := by
    change ENNReal.ofReal |(sys.transform^[2*k] initial false n).1 - (solution 0 false n).1| = _
    rw [show (solution 0 false n).1 = 0 by simp [solution],sub_zero,abs_of_nonneg hnonneg]
  rw [hx]
  simpa using ENNReal.ofReal_le_ofReal hC.le

theorem odd_error_top (k : ℕ) :
    sys.delta (sys.transform^[2*k+1] initial) (solution 0) (true,1) = ⊤ := by
  apply ENNReal.eq_top_of_forall_nnreal_le
  intro C
  obtain ⟨n,hn,hC⟩ := no_uniform_odd_bound k C
  apply le_trans _ (sys.point_le_delta _ _ true 1 n)
  have hnonneg : 0 ≤ (sys.transform^[2*k+1] initial true n).2 := le_of_lt (lt_of_le_of_lt C.2 hC)
  have hx : gauge.d 1 (sys.transform^[2*k+1] initial true n) (solution 0 true n) =
      ENNReal.ofReal (sys.transform^[2*k+1] initial true n).2 := by
    change ENNReal.ofReal |(sys.transform^[2*k+1] initial true n).2 - (solution 0 true n).2| = _
    rw [show (solution 0 true n).2 = 0 by simp [solution],sub_zero,abs_of_nonneg hnonneg]
  rw [hx]
  simpa using ENNReal.ofReal_le_ofReal hC.le

theorem error_top_every_depth (n : ℕ) :
    ∃ vi, sys.delta (sys.transform^[n] initial) (solution 0) vi = ⊤ := by
  rcases Nat.even_or_odd n with ⟨k,hk⟩|⟨k,hk⟩
  · refine ⟨(false,0),?_⟩
    have he : n = 2*k := by omega
    rw [he]
    exact even_error_top k
  · refine ⟨(true,1),?_⟩
    have he : n = 2*k+1 := by omega
    rw [he]
    exact odd_error_top k

/-- A component that is constant after one return can depend on the original input again. -/
theorem component_restoration (u v : ℝ) :
    (ret false (u,v)).2 = 0 ∧ ret true (ret false (u,v)) = (0,v/4) := by
  simp [ret]; ring

end MathGauge.RecursiveClosure.Counterexample
