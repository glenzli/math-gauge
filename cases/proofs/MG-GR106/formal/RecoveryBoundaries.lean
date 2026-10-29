import DenseRecovery
import Mathlib.Topology.MetricSpace.Contracting

noncomputable section
open UniformSpace Topology Filter Set
open scoped NNReal
open MathGauge.R106

namespace MathGauge.GR106

variable {I X Y Z : Type*} [MetricSpace X] [MetricSpace Y] [MetricSpace Z]

/-- S1: arbitrary proper filters, with no sequential replacement. -/
theorem compact_recovery [CompactSpace X] [CompleteSpace Y]
    (L : Filter I) [L.NeBot] (K : ℝ≥0) (f : I → X → Y)
    (hLip : ∀ i, LipschitzWith K (f i))
    (hC : ∀ x, Cauchy (Filter.map (fun i => f i x) L)) :
    ∃ g : X → Y, LipschitzWith K g ∧ TendstoUniformly f g L := by
  obtain ⟨g, hgl, hg⟩ := exists_lipschitz_limit L K f hLip univ dense_univ
    (fun x _ => hC x)
  exact ⟨g, hgl, tendstoUniformlyOn_univ.mp
    (compact_uniform_limit L K f g hLip hg univ isCompact_univ)⟩

theorem fixed_exists_unique [Nonempty X] [CompleteSpace X]
    (q : ℝ≥0) (hq : q < 1) (f : X → X) (hf : LipschitzWith q f) :
    ∃! x, f x = x := by
  let h : ContractingWith q f := ⟨hq, hf⟩
  exact ⟨h.fixedPoint f, h.fixedPoint_isFixedPt,
    fun _ hx => h.fixedPoint_unique hx⟩

/-- S2: the uniform error is the actual supremum, finite by compactness. -/
theorem fixed_sup_error [CompactSpace X] [Nonempty X]
    (q : ℝ≥0) (hq : q < 1) (f g : X → X)
    (hf : LipschitzWith q f) (hg : LipschitzWith q g)
    {x y : X} (hx : f x = x) (hy : g y = y) :
    dist x y ≤ sSup (Set.range (fun z => dist (f z) (g z))) / (1 - (q : ℝ)) := by
  have hb : BddAbove (Set.range (fun z => dist (f z) (g z))) := by
    simpa only [image_univ] using
      isCompact_univ.bddAbove_image (hf.continuous.dist hg.continuous).continuousOn
  exact (show ContractingWith q f from ⟨hq, hf⟩).dist_fixedPoint_fixedPoint_of_dist_le'
    g hx hy (fun z => le_csSup hb (mem_range_self z))

theorem fixed_points_tendsto [CompleteSpace X]
    (L : Filter I) (q : ℝ≥0) (hq : q < 1) (f : I → X → X) (g : X → X)
    (hl : ∀ i, LipschitzWith q (f i))
    (hlim : ∀ x, Tendsto (fun i => f i x) L (𝓝 (g x)))
    (x : I → X) (a : X) (hx : ∀ i, f i (x i) = x i) (ha : g a = a) :
    Tendsto x L (𝓝 a) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hd : Tendsto (fun i => dist a (f i a)) L (𝓝 0) := by
    simpa only [ha, dist_self] using (tendsto_const_nhds (x := a)).dist (hlim a)
  have hb : Tendsto (fun i => dist a (f i a) / (1 - (q : ℝ))) L (𝓝 0) := by
    simpa using hd.div_const (1 - (q : ℝ))
  apply squeeze_zero (fun _ => dist_nonneg) (fun i => ?_) hb
  simpa only [dist_comm (x i) a] using
    (show ContractingWith q (f i) from ⟨hq, hl i⟩).dist_le_of_fixedPoint a (hx i)

/-- S3: uniform error bounds compose without substituting a moving point into a pointwise limit. -/
theorem composition_error (c : ℝ≥0) (f f' : X → Y) (g g' : Y → Z)
    (hg : LipschitzWith c g) (a b : ℝ)
    (hferr : ∀ x, dist (f x) (f' x) ≤ a)
    (hgerr : ∀ y, dist (g y) (g' y) ≤ b) (x : X) :
    dist (g (f x)) (g' (f' x)) ≤ (c : ℝ) * a + b := by
  exact (dist_triangle _ (g (f' x)) _).trans
    (add_le_add ((hg.dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left (hferr x) c.coe_nonneg))
      (hgerr (f' x)))

theorem compact_composition_recovery [CompactSpace X] [CompactSpace Y] [CompleteSpace Z]
    (L : Filter I) [L.NeBot] (K M : ℝ≥0) (f : I → X → Y) (g : I → Y → Z)
    (hf : ∀ i, LipschitzWith K (f i)) (hg : ∀ i, LipschitzWith M (g i))
    (hfc : ∀ x, Cauchy (Filter.map (fun i => f i x) L))
    (hgc : ∀ y, Cauchy (Filter.map (fun i => g i y) L)) :
    ∃ a : X → Y, ∃ b : Y → Z, LipschitzWith K a ∧ LipschitzWith M b ∧
      TendstoUniformly f a L ∧ TendstoUniformly g b L ∧
      TendstoUniformly (fun i x => g i (f i x)) (fun x => b (a x)) L := by
  obtain ⟨a, ha, hfa⟩ := compact_recovery L K f hf hfc
  obtain ⟨b, hb, hgb⟩ := compact_recovery L M g hg hgc
  refine ⟨a, b, ha, hb, hfa, hgb, tendstoUniformlyOn_univ.mp ?_⟩
  apply compact_uniform_limit L (M * K) (fun i x => g i (f i x)) (fun x => b (a x))
    (fun i => (hg i).comp (hf i)) _ univ isCompact_univ
  intro x
  exact moving_input_limit L M g b hg (fun y => hgb.tendsto_at y)
    (fun i => f i x) (a x) (hfa.tendsto_at x)

/-- S5: a translated tent on R, using D=R (an allowed dense subset). -/
def tent (n : ℕ) (x : ℝ) : ℝ := max 0 (1 - dist x (n : ℝ))

theorem tent_lipschitz (n : ℕ) : LipschitzWith 1 (tent n) := by
  apply LipschitzWith.of_le_add
  intro x y
  apply max_le
  · exact add_nonneg (le_max_left _ _) dist_nonneg
  · have h := dist_triangle y x (n : ℝ)
    rw [dist_comm y x] at h
    have hh := le_max_right (0 : ℝ) (1 - dist y (n : ℝ))
    dsimp [tent]
    linarith

theorem tent_eventually_zero (x : ℝ) : ∀ᶠ n : ℕ in atTop, tent n x = 0 := by
  obtain ⟨N, hN⟩ := exists_nat_gt (x + 1)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hdist : 1 ≤ dist x (n : ℝ) := by
    rw [Real.dist_eq]
    have h := neg_le_abs (x - (n : ℝ))
    linarith
  exact max_eq_left (by linarith)

theorem tent_pointwise (x : ℝ) : Tendsto (fun n => tent n x) atTop (𝓝 0) :=
  tendsto_const_nhds.congr' (by
    filter_upwards [tent_eventually_zero x] with n hn
    exact hn.symm)

theorem tent_cauchy (x : ℝ) : Cauchy (Filter.map (fun n => tent n x) atTop) :=
  cauchy_map_iff_exists_tendsto.mpr ⟨0, tent_pointwise x⟩

theorem tent_peak (n : ℕ) : tent n n = 1 := by simp [tent]

theorem tent_extensions_not_uniform :
    ¬ TendstoUniformly (extensions tent) (fun _ : Completion ℝ => 0) atTop := by
  intro h
  obtain ⟨n, hn⟩ := ((Metric.tendstoUniformly_iff.mp h) (1 / 2) (by norm_num)).exists
  have hh := hn ((n : ℝ) : Completion ℝ)
  rw [extensions_coe 1 tent tent_lipschitz, tent_peak] at hh
  norm_num at hh

/-- Identify the actual recovered function as zero, also on completion points. -/
theorem tent_recovery_zero {g : Completion ℝ → ℝ} (hg : Continuous g)
    (hdata : ∀ x : ℝ, Tendsto (fun n => tent n x) atTop (𝓝 (g x))) :
    g = fun _ => 0 :=
  unique_from_dense_data atTop tent univ dense_univ hg continuous_const
    (fun x _ => hdata x) (fun x _ => tent_pointwise x)

/-- S6: a totally bounded set need not itself be closed; its closure in the completion is compact. -/
theorem totally_bounded_uniform [CompleteSpace X] [CompleteSpace Y]
    (L : Filter I) (K : ℝ≥0) (f : I → X → Y) (g : X → Y)
    (hl : ∀ i, LipschitzWith K (f i))
    (hlim : ∀ x, Tendsto (fun i => f i x) L (𝓝 (g x)))
    (A : Set X) (hA : TotallyBounded A) : TendstoUniformlyOn f g L A := by
  exact (compact_uniform_limit L K f g hl hlim (closure A)
    (hA.closure.isCompact_of_isClosed isClosed_closure)).mono subset_closure

end MathGauge.GR106
