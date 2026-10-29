import Core
import Bounds
import Spectral

noncomputable section
open scoped BigOperators ENNReal NNReal Matrix.Norms.Operator
open Matrix
namespace MathGauge.RecursiveClosure.Obstructions

abbrev Positive := {x : ℝ // 0 < x}
def positiveGauge : Gauge Positive Unit where
  d _ x y := ENNReal.ofReal |x.val-y.val|
  self := by intros; simp
  symm := by intros; rw [abs_sub_comm]
  triangle := by
    intro i x y z
    rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (abs_sub_le _ _ _)

def half (x : Positive) : Positive := ⟨x.val/2,div_pos x.property (by norm_num)⟩

abbrev positiveSystem : System Positive Unit Unit Unit positiveGauge where
  Input _ := Unit
  src _ := ()
  dst _ := ()
  step _ _ := Sum.inr ⟨(),()⟩
  step_src := by intros; rfl
  ret _ := half
  L _ _ _ := 1/2
  lip := by
    intro e i x y
    simp [positiveGauge,half,Counterexample.half_abs]

theorem positive_no_fixed : ¬ ∃ F : positiveSystem.Family, positiveSystem.transform F = F := by
  rintro ⟨F,hF⟩
  have h := congrArg (fun G : positiveSystem.Family => (G () ()).val) hF
  change (F () ()).val/2 = (F () ()).val at h
  linarith [(F () ()).property]

def zeroGauge : Gauge Bool Unit where
  d _ _ _ := 0
  self := by intros; rfl
  symm := by intros; rfl
  triangle := by intros; simp

abbrev swapSystem : System Bool Unit Unit Unit zeroGauge where
  Input _ := Unit
  src _ := ()
  dst _ := ()
  step _ _ := Sum.inr ⟨(),()⟩
  step_src := by intros; rfl
  ret _ := Bool.not
  L _ _ _ := 1/2
  lip := by intros; simp [zeroGauge]

theorem swap_no_fixed : ¬ ∃ F : swapSystem.Family, swapSystem.transform F = F := by
  rintro ⟨F,hF⟩
  have h := congrArg (fun G : swapSystem.Family => G () ()) hF
  change Bool.not (F () ()) = F () () at h
  have hn := Bool.not_ne_self (F () ())
  exact hn h

theorem single_loop_spectral_lt_one :
    spectralRadius ℂ (complexMatrix positiveSystem.coeff) < 1 ∧
    spectralRadius ℂ (complexMatrix swapSystem.coeff) < 1 := by
  have h1 : ‖complexMatrix positiveSystem.coeff‖₊ = (1/2:ℝ≥0) := by
    simp [Matrix.linfty_opNNNorm_def,complexMatrix,System.coeff,positiveSystem,show (Finset.univ : Finset (Unit × Unit)) = {((),())} by decide]
  have h2 : ‖complexMatrix swapSystem.coeff‖₊ = (1/2:ℝ≥0) := by
    simp [Matrix.linfty_opNNNorm_def,complexMatrix,System.coeff,swapSystem,show (Finset.univ : Finset (Unit × Unit)) = {((),())} by decide]
  constructor
  · exact lt_of_le_of_lt (spectrum.spectralRadius_le_nnnorm _) (by rw [h1]; norm_num)
  · exact lt_of_le_of_lt (spectrum.spectralRadius_le_nnnorm _) (by rw [h2]; norm_num)

def totalSetoid : Setoid Bool where
  r _ _ := True
  iseqv := ⟨by simp,by simp,by simp⟩

theorem zero_quotient_subsingleton : Subsingleton (Quotient totalSetoid) := by
  constructor
  intro a b
  induction a using Quotient.inductionOn with | _ a =>
    induction b using Quotient.inductionOn with | _ b =>
      exact Quotient.sound True.intro

end MathGauge.RecursiveClosure.Obstructions
