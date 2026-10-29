import Partial
import Spectral
import Bounds

noncomputable section
namespace MathGauge.RecursiveClosure.TerminationBoundary

def gauge : Gauge ℕ Unit where
  d _ _ _ := 0
  self := by intros; rfl
  symm := by intros; rfl
  triangle := by intros; simp

def sys : System ℕ Unit Unit Unit gauge where
  Input _ := ℕ
  src _ := ()
  dst _ := ()
  step _ n := match n with
    | 0 => Sum.inl 0
    | n+1 => Sum.inr ⟨(),n⟩
  step_src := by intros; rfl
  ret _ := id
  L _ _ _ := 0
  lip := by intros; simp [gauge]

theorem all_inputs_halt (n : ℕ) : sys.Halts () n := by
  induction n with
  | zero => exact System.Halts.stop rfl
  | succ n ih => exact System.Halts.call rfl ih

theorem eval_eq_none_iff (n m : ℕ) : sys.eval m () n=none ↔ m≤n := by
  induction m generalizing n with
  | zero => simp [System.eval]
  | succ m ih =>
    cases n with
    | zero => simp [System.eval,System.partialTransform,sys]
    | succ n =>
      simpa [System.eval,System.partialTransform,sys] using ih n

/-- The finite graph and pointwise termination admit no common finite unfolding depth. -/
theorem no_uniform_depth : ¬∃ m, ∀ n, sys.eval m () n ≠ none := by
  rintro ⟨m,hm⟩
  exact hm m ((eval_eq_none_iff m m).2 le_rfl)

theorem spectral_zero : spectralRadius ℂ (complexMatrix sys.coeff)=0 := by
  have hm : complexMatrix sys.coeff=0 := by ext a b; simp [complexMatrix,System.coeff,sys]
  rw [hm,spectrum.spectralRadius_zero]

end MathGauge.RecursiveClosure.TerminationBoundary
