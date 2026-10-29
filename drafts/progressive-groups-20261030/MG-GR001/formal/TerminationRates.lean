import ScalarExamples

noncomputable section
open scoped BigOperators ENNReal NNReal Matrix.Norms.Operator
open Filter Topology
namespace MathGauge.RecursiveClosure
namespace System
variable {Y V E I : Type} [Fintype I] {g : Gauge Y I}

/-- A bound K on the number of calls means evaluation depth K+1. Every
initial family has then been completely discarded. -/
theorem uniform_termination_exact (s : System Y V E I g) (K : ℕ)
    (hK : ∀ v x, ∃ y, s.eval (K+1) v x = some y)
    (H G : s.Family) (n : ℕ) (hn : K+1 ≤ n) :
    s.transform^[n] H = s.transform^[K+1] G := by
  funext v x
  obtain ⟨y,hy⟩ := hK v x
  exact (s.finite_stop_stable H hy hn).trans (s.eval_forces_unfold G hy).symm

theorem uniform_termination_fixed (s : System Y V E I g) (K : ℕ)
    (hK : ∀ v x, ∃ y, s.eval (K+1) v x = some y) (H : s.Family) :
    s.transform (s.transform^[K+1] H) = s.transform^[K+1] H := by
  simpa only [Function.iterate_succ_apply'] using
    s.uniform_termination_exact K hK H H (K+2) (by omega)
end System

namespace ScalarExamples

abbrev countdown : System ℝ Unit Unit Unit gauge where
  Input _ := ℕ
  src _ := ()
  dst _ := ()
  step _ n := match n with
    | 0 => .inl 0
    | n+1 => .inr ⟨(),n⟩
  step_src := by intros; rfl
  ret _ y := y/2
  L _ _ _ := 1/2
  lip := by intros; simpa [gauge] using half_lip _ _

def exponentialInitial : countdown.Family := fun _ n => 2^n

theorem countdown_halts (n : ℕ) : countdown.Halts () n := by
  induction n with
  | zero => exact System.Halts.stop rfl
  | succ n ih => exact System.Halts.call rfl ih

theorem countdown_zero_fixed : countdown.transform (fun _ _ => 0) = (fun _ _ => 0) := by
  funext v n
  cases n <;> simp [System.transform,countdown]

theorem countdown_tail (k n : ℕ) (h : k ≤ n) :
    countdown.transform^[k] exponentialInitial () n = 2^n / 4^k := by
  induction k generalizing n with
  | zero => simp [exponentialInitial]
  | succ k ih =>
    cases n with
    | zero => omega
    | succ n =>
      rw [Function.iterate_succ_apply']
      change (countdown.transform^[k] exponentialInitial () n)/2 = _
      rw [ih n (by omega),pow_succ,pow_succ]
      ring

theorem countdown_error_top (k : ℕ) :
    countdown.delta (countdown.transform^[k] exponentialInitial) (fun _ _ => 0) ((),()) = ⊤ := by
  apply ENNReal.eq_top_of_forall_nnreal_le
  intro C
  obtain ⟨j,hj⟩ := exists_nat_gt ((C : ℝ)*4^k)
  let n := j+k
  have hn : k ≤ n := by dsimp [n]; omega
  have hp : (n : ℝ) ≤ 2^n := by
    have hh := one_add_mul_le_pow (by norm_num : (-2:ℝ) ≤ 1) n
    norm_num at hh
    linarith
  have hbound : (C : ℝ) ≤ 2^n / 4^k := by
    apply (le_div_iff₀ (by positivity : (0:ℝ) < 4^k)).mpr
    have hjn : (j:ℝ) ≤ n := by exact_mod_cast (show j ≤ n by dsimp [n]; omega)
    linarith
  apply le_trans _ (countdown.point_le_delta _ _ () () n)
  change (C:ℝ≥0∞) ≤ edist (countdown.transform^[k] exponentialInitial () n) 0
  rw [edist_dist,Real.dist_eq,countdown_tail k n hn,sub_zero,abs_of_nonneg (by positivity)]
  simpa using ENNReal.ofReal_le_ofReal hbound

theorem countdown_spectral : spectralRadius ℂ (complexMatrix countdown.coeff) < 1 := by
  convert shift_spectral using 1

/-- A uniformly terminating depth-one system. Input (false,j) represents
the terminal even number 2j, and (true,j) its calling odd partner 2j+1. -/
abbrev depthOne : System ℝ Unit Unit Unit gauge where
  Input _ := Bool × ℕ
  src _ := ()
  dst _ := ()
  step _ x := if x.1 then .inr ⟨(),(false,x.2)⟩ else .inl 0
  step_src := by intros; rfl
  ret _ y := y/2
  L _ _ _ := 1/2
  lip := by intros; simpa [gauge] using half_lip _ _

def parityInput (x : Bool × ℕ) : ℝ := if x.1 then 2*(x.2:ℝ)+1 else 2*x.2

theorem parityInput_injective : Function.Injective parityInput := by
  rintro ⟨b,n⟩ ⟨c,m⟩ h
  cases b <;> cases c <;> simp only [parityInput,Bool.false_eq_true,if_false,if_true] at h
  · have : n=m := by exact_mod_cast (show (n:ℝ) = m by linarith)
    cases this; rfl
  · have hi : 2*n = 2*m+1 := by exact_mod_cast h
    omega
  · have hi : 2*n+1 = 2*m := by exact_mod_cast h
    omega
  · have : n=m := by exact_mod_cast (show (n:ℝ) = m by linarith)
    cases this; rfl

def badInitial : depthOne.Family := fun _ x => if x.1 then 0 else x.2

theorem depthOne_eval_two (x : Bool × ℕ) : depthOne.eval 2 () x = some 0 := by
  rcases x with ⟨b,n⟩
  cases b <;> simp [System.eval,System.partialTransform,depthOne]

theorem depthOne_exact (H : depthOne.Family) (n : ℕ) (hn : 2 ≤ n) :
    depthOne.transform^[n] H = (fun _ _ => 0) := by
  funext v x
  cases v
  exact depthOne.finite_stop_stable H (depthOne_eval_two x) hn

theorem depthOne_first_unbounded :
    depthOne.delta (depthOne.transform badInitial) (fun _ _ => 0) ((),()) = ⊤ := by
  apply ENNReal.eq_top_of_forall_nnreal_le
  intro C
  obtain ⟨j,hj⟩ := exists_nat_gt (2*(C:ℝ))
  have hb : (C:ℝ) ≤ (j:ℝ)/2 := by linarith
  apply le_trans _ (depthOne.point_le_delta _ _ () () (true,j))
  simp only [System.transform,depthOne,badInitial,if_true,Bool.false_eq_true,if_false,gauge,
    edist_dist,Real.dist_eq,sub_zero]
  rw [abs_of_nonneg (by positivity)]
  simpa using ENNReal.ofReal_le_ofReal hb

theorem depthOne_no_finite_geometric : ¬∃ q C : ℝ≥0, ∀ n : ℕ, 1 ≤ n →
    depthOne.delta (depthOne.transform^[n] badInitial) (fun _ _ => 0) ((),()) ≤
      (C : ℝ≥0∞) * (q : ℝ≥0∞)^n := by
  rintro ⟨q,C,h⟩
  have hh := h 1 le_rfl
  simp only [Function.iterate_one,depthOne_first_unbounded,pow_one] at hh
  exact (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top) (top_le_iff.mp hh)

theorem depthOne_spectral : spectralRadius ℂ (complexMatrix depthOne.coeff) < 1 := by
  convert shift_spectral using 1

end ScalarExamples
end MathGauge.RecursiveClosure
