import GreenPerturbation

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Filter Topology
namespace MathGauge.HilbertRegular
open HilbertCriteria HilbertPerturbation
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def Positive (L : E →L[ℂ] E) : Prop := ∀ x, 0 ≤ Complex.re (inner ℂ (L x) x)

def shifted (L : E →L[ℂ] E) (ε : ℝ) : E →L[ℂ] E := L+(ε:ℂ) • 1

theorem shifted_energy (L : E →L[ℂ] E) (ε : ℝ) (x : E) :
    Complex.re (inner ℂ (shifted L ε x) x) = Complex.re (inner ℂ (L x) x)+ε*‖x‖^2 := by
  simp only [shifted,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply,inner_add_left,Complex.add_re]
  congr 1
  rw [inner_smul_left]
  simp [← Complex.ofReal_pow]

theorem shifted_coercive (L : E →L[ℂ] E) (hL : Positive L) (ε : ℝ) :
    ∀ x, ε*‖x‖^2 ≤ Complex.re (inner ℂ (shifted L ε x) x) := by
  intro x
  rw [shifted_energy]
  linarith [hL x]

def regularGreen (L : E →L[ℂ] E) (hL : Positive L) (ε : ℝ) : E →L[ℂ] E :=
  if hε : 0<ε then Green (shifted L ε) hε (shifted_coercive L hL ε) else 0

theorem regular_right (L : E →L[ℂ] E) (hL : Positive L) {ε : ℝ} (hε : 0<ε) :
    (shifted L ε).comp (regularGreen L hL ε) = 1 := by
  rw [regularGreen,dif_pos hε]
  exact Green_right _ hε _

theorem regular_left (L : E →L[ℂ] E) (hL : Positive L) {ε : ℝ} (hε : 0<ε) :
    (regularGreen L hL ε).comp (shifted L ε) = 1 := by
  rw [regularGreen,dif_pos hε]
  exact Green_left _ hε _

theorem regular_norm (L : E →L[ℂ] E) (hL : Positive L) {ε : ℝ} (hε : 0<ε) :
    ‖regularGreen L hL ε‖ ≤ ε⁻¹ := by
  rw [regularGreen,dif_pos hε]
  exact Green_norm _ hε _

def regularError (L : E →L[ℂ] E) (hL : Positive L) (ε : ℝ) : E →L[ℂ] E :=
  (ε:ℂ) • regularGreen L hL ε

theorem regularError_bound (L : E →L[ℂ] E) (hL : Positive L) (ε : ℝ) :
    ‖regularError L hL ε‖ ≤ 1 := by
  by_cases he : 0<ε
  · rw [regularError,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos he]
    exact (mul_le_mul_of_nonneg_left (regular_norm L hL he) he.le).trans_eq (mul_inv_cancel₀ he.ne')
  · simp [regularError,regularGreen,dif_neg he]

theorem regular_error_identity (L : E →L[ℂ] E) (hL : Positive L) {ε : ℝ} (hε : 0<ε) :
    L.comp (regularGreen L hL ε) = 1-regularError L hL ε := by
  have he := regular_right L hL hε
  simp only [shifted,ContinuousLinearMap.add_comp,ContinuousLinearMap.smul_comp,
    show (1 : E →L[ℂ] E) = ContinuousLinearMap.id ℂ E from rfl,
    ContinuousLinearMap.id_comp] at he
  exact eq_sub_iff_add_eq.mpr he

theorem error_range_identity (L : E →L[ℂ] E) (hL : Positive L) {ε : ℝ} (hε : 0<ε) (y : E) :
    regularError L hL ε (L y) = (ε:ℂ) • y-(ε:ℂ) • regularError L hL ε y := by
  have he := congrArg (fun U : E →L[ℂ] E => U y) (regular_left L hL hε)
  change regularGreen L hL ε (L y+(ε:ℂ) • y)=y at he
  rw [map_add,map_smul] at he
  change (ε:ℂ) • regularGreen L hL ε (L y) = (ε:ℂ) • y-(ε:ℂ) • ((ε:ℂ) • regularGreen L hL ε y)
  have ht := congrArg (fun z : E => (ε:ℂ) • z) he
  simp only [smul_add] at ht
  exact eq_sub_iff_add_eq.mpr ht

theorem error_range_bound (L : E →L[ℂ] E) (hL : Positive L) {ε : ℝ} (hε : 0<ε) (y : E) :
    ‖regularError L hL ε (L y)‖ ≤ 2*ε*‖y‖ := by
  rw [error_range_identity L hL hε]
  have hn : ‖regularError L hL ε y‖ ≤ ‖y‖ :=
    ((regularError L hL ε).le_opNorm y).trans (by simpa using mul_le_mul_of_nonneg_right (regularError_bound L hL ε) (norm_nonneg y))
  have hs := norm_sub_le ((ε:ℂ) • y) ((ε:ℂ) • regularError L hL ε y)
  simp only [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hε] at hs
  nlinarith

theorem error_range_tendsto (L : E →L[ℂ] E) (hL : Positive L) (y : E) :
    Tendsto (fun ε => regularError L hL ε (L y)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have ht : Tendsto (fun ε : ℝ => 2*ε*‖y‖) (𝓝[>] 0) (𝓝 0) := by
    have he : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) := continuous_id.continuousWithinAt
    simpa using (he.const_mul 2).mul_const ‖y‖
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ ht
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact error_range_bound L hL hε y

theorem regularError_norm_tendsto_of_right_inverse (L : E →L[ℂ] E) (hL : Positive L)
    (U : E →L[ℂ] E) (hU : L.comp U=1) :
    Tendsto (fun ε => ‖regularError L hL ε‖) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hb : ∀ᶠ ε : ℝ in 𝓝[>] 0, ‖regularError L hL ε‖ ≤ 2*ε*‖U‖ := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    change 0<ε at hε
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro x
    have hx : L (U x)=x := congrArg (fun V : E →L[ℂ] E => V x) hU
    calc
      _ = ‖regularError L hL ε (L (U x))‖ := by rw [hx]
      _ ≤ 2*ε*‖U x‖ := error_range_bound L hL hε _
      _ ≤ (2*ε*‖U‖)*‖x‖ := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (U.le_opNorm x) (by positivity : 0≤2*ε)
  have he : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) := continuous_id.continuousWithinAt
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hb
  simpa using (he.const_mul 2).mul_const ‖U‖

theorem right_inverse_of_regularError_small (L : E →L[ℂ] E) (hL : Positive L)
    {ε : ℝ} (hε : 0<ε) (hsmall : ‖regularError L hL ε‖<1) :
    ∃ U : E →L[ℂ] E, L.comp U=1 := by
  let V : E →L[ℂ] E := ∑' n : ℕ, regularError L hL ε^n
  have hi : (1-regularError L hL ε)*V=1 :=
    (summable_geometric_of_norm_lt_one hsmall).one_sub_mul_tsum_pow
  refine ⟨(regularGreen L hL ε).comp V,?_⟩
  rw [← ContinuousLinearMap.comp_assoc,regular_error_identity L hL hε]
  exact hi

theorem regularError_norm_iff_right_inverse (L : E →L[ℂ] E) (hL : Positive L) :
    Tendsto (fun ε => ‖regularError L hL ε‖) (𝓝[>] (0:ℝ)) (𝓝 0) ↔
      ∃ U : E →L[ℂ] E, L.comp U=1 := by
  constructor
  · intro ht
    have hp : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0<ε := self_mem_nhdsWithin
    obtain ⟨ε,hε,he⟩ := (hp.and
      (ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1)))).exists
    exact right_inverse_of_regularError_small L hL hε he
  · rintro ⟨U,hU⟩
    exact regularError_norm_tendsto_of_right_inverse L hL U hU

end MathGauge.HilbertRegular
