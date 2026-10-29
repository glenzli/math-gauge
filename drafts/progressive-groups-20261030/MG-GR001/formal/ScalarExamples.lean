import CompleteFamilies
import Partial

noncomputable section
open scoped BigOperators ENNReal NNReal Matrix.Norms.Operator
open Filter Topology
namespace MathGauge.RecursiveClosure.ScalarExamples

def gauge : Gauge ℝ Unit where
  d _ x y := edist x y
  self := by intros; exact edist_self _
  symm := by intros; exact edist_comm _ _
  triangle := by intros; exact edist_triangle _ _ _

theorem real_output_complete : CompleteSpace ℝ := inferInstance

theorem gauge_matches_metric (x y : ℝ) : edist x y = ⨆ i, gauge.d i x y := by
  simp [gauge]

theorem half_lip (x y : ℝ) :
    edist (x/2) (y/2) ≤ ((1/2 : ℝ≥0) : ℝ≥0∞) * edist x y := by
  rw [edist_dist,Real.dist_eq,edist_dist,Real.dist_eq,← sub_div,abs_div]
  norm_num
  rw [div_eq_mul_inv,ENNReal.ofReal_mul (abs_nonneg _)]
  rw [ENNReal.ofReal_inv_of_pos (by norm_num)]
  norm_num [mul_comm]

/-- Index n represents the actual positive integer n+1 in the stated input subset. -/
def positiveInput (n : ℕ) : ℝ := n+1
theorem positiveInput_injective : Function.Injective positiveInput := by
  intro n m h
  dsimp [positiveInput] at h
  exact_mod_cast (add_right_cancel h : (n : ℝ) = (m : ℝ))

abbrev shift : System ℝ Unit Unit Unit gauge where
  Input _ := ℕ
  src _ := ()
  dst _ := ()
  step _ n := .inr ⟨(),n+1⟩
  step_src := by intros; rfl
  ret _ y := y/2
  L _ _ _ := 1/2
  lip := by intros; simpa [gauge] using half_lip _ _

def fixed (c : ℝ) : shift.Family := fun _ n => c*2^(n+1)
def linearInitial : shift.Family := fun _ (n : ℕ) => (n:ℝ)+1

theorem fixed_is_fixed (c : ℝ) : shift.transform (fixed c) = fixed c := by
  funext v n
  simp [System.transform,shift,fixed,pow_succ]
  ring

theorem fixed_classification (F : shift.Family) :
    shift.transform F = F ↔ ∃ c : ℝ, F = fixed c := by
  constructor
  · intro h
    refine ⟨F () 0 / 2,?_⟩
    funext v n
    cases v
    induction n with
    | zero => simp [fixed]
    | succ n ih =>
      have he := congrArg (fun H : shift.Family => H () n) h
      change F () (n+1)/2 = F () n at he
      rw [ih] at he
      dsimp [fixed] at he ⊢
      rw [pow_succ]
      linarith
  · rintro ⟨c,rfl⟩
    exact fixed_is_fixed c

theorem fixed_injective : Function.Injective fixed := by
  intro c d h
  have hh := congrArg (fun F : shift.Family => F () 0) h
  simp [fixed] at hh
  linarith

theorem not_unique : ¬∃! F : shift.Family, shift.transform F = F := by
  rintro ⟨F,hF,hu⟩
  have h := (hu _ (fixed_is_fixed 0)).trans (hu _ (fixed_is_fixed 1)).symm
  have := fixed_injective h
  norm_num at this

theorem shift_iterate (H : shift.Family) (k n : ℕ) :
    shift.transform^[k] H () n = H () (n+k) / 2^k := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    change (shift.transform^[k] H () (n+1))/2 = _
    rw [ih,pow_succ]
    simp [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,div_div]

theorem linear_iterate (k n : ℕ) :
    shift.transform^[k] linearInitial () n = ((n : ℝ)+k+1)/2^k := by
  simp [shift_iterate,linearInitial]

theorem linear_pointwise (n : ℕ) :
    Tendsto (fun k => shift.transform^[k] linearInitial () n) atTop (𝓝 0) := by
  have hp : Tendsto (fun k : ℕ => (1/2 : ℝ)^k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by norm_num)
  have hk := tendsto_self_mul_const_pow_of_lt_one (r := (1/2:ℝ)) (by norm_num) (by norm_num)
  have hh := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (n:ℝ)+1) atTop
    (𝓝 ((n:ℝ)+1))).mul hp).add hk
  convert hh using 1
  · funext k
    simp only [linear_iterate,div_eq_mul_inv,one_div,one_mul,inv_pow]
    ring
  · simp

theorem linear_error_top (k : ℕ) :
    shift.delta (shift.transform^[k] linearInitial) (fixed 0) ((),()) = ⊤ := by
  apply ENNReal.eq_top_of_forall_nnreal_le
  intro C
  obtain ⟨n,hn⟩ := exists_nat_gt ((C : ℝ)*2^k)
  have hp : (0 : ℝ) < 2^k := by positivity
  have hb : (C : ℝ) ≤ ((n : ℝ)+k+1)/2^k := by
    apply (le_div_iff₀ hp).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  apply le_trans _ (shift.point_le_delta _ _ () () n)
  change (C:ℝ≥0∞) ≤ edist (shift.transform^[k] linearInitial () n) (0*2^(n+1))
  rw [zero_mul,edist_dist,Real.dist_eq,linear_iterate,sub_zero,abs_of_nonneg (by positivity)]
  simpa using ENNReal.ofReal_le_ofReal hb

theorem different_fixed_distance_top (c d : ℝ) (hcd : c ≠ d) :
    shift.delta (fixed c) (fixed d) ((),()) = ⊤ := by
  apply ENNReal.eq_top_of_forall_nnreal_le
  intro C
  have ha : 0 < |c-d| := abs_pos.mpr (sub_ne_zero.mpr hcd)
  obtain ⟨n,hn⟩ := exists_nat_gt ((C:ℝ)/|c-d|)
  have hp : (n:ℝ) ≤ 2^n := by
    have hh := one_add_mul_le_pow (by norm_num : (-2:ℝ) ≤ 1) n
    norm_num at hh
    linarith
  have hb : (C : ℝ) ≤ |c-d| * 2^(n+1) := by
    have hh := (div_lt_iff₀ ha).mp hn
    rw [pow_succ]
    nlinarith
  apply le_trans _ (shift.point_le_delta _ _ () () n)
  change (C:ℝ≥0∞) ≤ edist (c*2^(n+1)) (d*2^(n+1))
  rw [edist_dist,Real.dist_eq,← sub_mul,abs_mul,abs_of_nonneg (by positivity : (0:ℝ) ≤ 2^(n+1))]
  simpa using ENNReal.ofReal_le_ofReal hb

theorem different_branches (c d : ℝ) (hcd : c ≠ d) :
    shift.weighted (fun _ => 1) (fixed c) (fixed d) = ⊤ ∧
    shift.weighted (fun _ => 1) (shift.transform (fixed c)) (fixed c) = 0 := by
  constructor
  · change (⨆ a, shift.delta (fixed c) (fixed d) a / (1:ℝ≥0∞)) = ⊤
    apply top_le_iff.mp
    calc
      ⊤ = shift.delta (fixed c) (fixed d) ((),()) / (1:ℝ≥0∞) := by
        rw [different_fixed_distance_top c d hcd,div_one]
      _ ≤ _ := le_iSup (fun a : Unit × Unit => shift.delta (fixed c) (fixed d) a / (1:ℝ≥0∞)) ((),())
  · rw [fixed_is_fixed]
    exact shift.weighted_self _ _

theorem shift_spectral : spectralRadius ℂ (complexMatrix shift.coeff) < 1 := by
  have hm : complexMatrix shift.coeff = (1/2 : ℂ) • (1 : Matrix (Unit × Unit) (Unit × Unit) ℂ) := by
    ext ⟨⟨⟩,⟨⟩⟩ ⟨⟨⟩,⟨⟩⟩
    norm_num [complexMatrix,System.coeff,shift]
  rw [hm]
  calc
    spectralRadius ℂ _ ≤ (↑‖(1/2 : ℂ) • (1 : Matrix (Unit × Unit) (Unit × Unit) ℂ)‖₊ : ℝ≥0∞) :=
      spectrum.spectralRadius_le_nnnorm _
    _ < 1 := by norm_num [nnnorm_smul]

end MathGauge.RecursiveClosure.ScalarExamples
