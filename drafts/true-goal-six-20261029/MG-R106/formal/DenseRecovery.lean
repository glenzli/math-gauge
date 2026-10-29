import Mathlib.Topology.MetricSpace.Completion
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Tactic

noncomputable section

open UniformSpace Topology Filter Set
open scoped NNReal

namespace MathGauge.R106

variable {I X Y : Type*} [MetricSpace X] [MetricSpace Y]

/-- A shared Lipschitz bound transfers Cauchy data from a dense subset without countability. -/
theorem cauchy_on_dense (L : Filter I) [L.NeBot] (K : ℝ≥0) (f : I → X → Y)
    (hLip : ∀ i, LipschitzWith K (f i)) (D : Set X) (hD : Dense D)
    (hC : ∀ d ∈ D, Cauchy (Filter.map (fun i => f i d) L)) (x : X) :
    Cauchy (Filter.map (fun i => f i x) L) := by
  rw [Metric.cauchy_iff]
  refine ⟨inferInstance, ?_⟩
  intro ε hε
  have hK : 0 < (K : ℝ) + 1 := by positivity
  obtain ⟨d, hd, hxd⟩ := hD.exists_dist_lt x (show 0 < ε / (4 * ((K : ℝ) + 1)) by positivity)
  have hn : (K : ℝ) * dist x d < ε / 4 := by
    have ht : 4 * ((K : ℝ) + 1) * dist x d < ε := by
      nlinarith [(lt_div_iff₀ (show 0 < 4 * ((K : ℝ) + 1) by positivity)).mp hxd]
    nlinarith [dist_nonneg (x := x) (y := d)]
  obtain ⟨t, ht, hp⟩ := (Metric.cauchy_iff.mp (hC d hd)).2 (ε / 2) (by positivity)
  let s : Set I := (fun i => f i d) ⁻¹' t
  refine ⟨(fun i => f i x) '' s, ?_, ?_⟩
  · exact Filter.mem_map_iff_exists_image.mpr ⟨s, ht, subset_rfl⟩
  · rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
    have hmid := hp (f i d) hi (f j d) hj
    have hi' := (hLip i).dist_le_mul x d
    have hj' := (hLip j).dist_le_mul d x
    rw [dist_comm d x] at hj'
    have htri := dist_triangle (f i x) (f i d) (f j x)
    have htri' := dist_triangle (f i d) (f j d) (f j x)
    linarith

variable [CompleteSpace Y]

/-- Pointwise limits exist globally and retain the same Lipschitz constant. -/
theorem exists_lipschitz_limit (L : Filter I) [L.NeBot] (K : ℝ≥0) (f : I → X → Y)
    (hLip : ∀ i, LipschitzWith K (f i)) (D : Set X) (hD : Dense D)
    (hC : ∀ d ∈ D, Cauchy (Filter.map (fun i => f i d) L)) :
    ∃ g : X → Y, LipschitzWith K g ∧ ∀ x, Tendsto (fun i => f i x) L (𝓝 (g x)) := by
  have hex : ∀ x, ∃ y, Tendsto (fun i => f i x) L (𝓝 y) := fun x =>
    cauchy_map_iff_exists_tendsto.mp (cauchy_on_dense L K f hLip D hD hC x)
  choose g hg using hex
  refine ⟨g, LipschitzWith.of_dist_le_mul (fun x y => ?_), hg⟩
  exact le_of_tendsto ((hg x).dist (hg y)) (Filter.Eventually.of_forall fun i =>
    (hLip i).dist_le_mul x y)

/-- Compactness is used only on the set where uniform convergence is requested. -/
theorem compact_uniform_limit (L : Filter I) (K : ℝ≥0) (f : I → X → Y) (g : X → Y)
    (hLip : ∀ i, LipschitzWith K (f i))
    (hg : ∀ x, Tendsto (fun i => f i x) L (𝓝 (g x)))
    (S : Set X) (hS : IsCompact S) : TendstoUniformlyOn f g L S := by
  letI : CompactSpace S := isCompact_iff_compactSpace.mp hS
  have hl : ∀ i, LipschitzWith K (fun x : S => f i x) := by
    intro i
    simpa only [mul_one] using (hLip i).comp ((isometry_subtype_coe : Isometry (Subtype.val : S → X)).lipschitz)
  have he : Equicontinuous (fun i (x : S) => f i x) :=
    (LipschitzWith.uniformEquicontinuous _ K hl).equicontinuous
  have hp : Tendsto (fun i (x : S) => f i x) L (𝓝 fun x : S => g x) :=
    tendsto_pi_nhds.mpr fun x => hg x
  have hu := (he.tendsto_uniformFun_iff_pi L (fun x : S => g x)).mpr hp
  exact tendstoUniformlyOn_iff_restrict.mpr
    (UniformFun.tendsto_iff_tendstoUniformly.mp hu)

/-- Moving inputs need not stay in a common compact set. -/
theorem moving_input_limit (L : Filter I) (K : ℝ≥0) (f : I → X → Y) (g : X → Y)
    (hLip : ∀ i, LipschitzWith K (f i))
    (hg : ∀ x, Tendsto (fun i => f i x) L (𝓝 (g x)))
    (u : I → X) (x : X) (hu : Tendsto u L (𝓝 x)) :
    Tendsto (fun i => f i (u i)) L (𝓝 (g x)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  have ha : Tendsto (fun i => (K : ℝ) * dist (u i) x) L (𝓝 0) := by
    have hd : Tendsto (fun i => dist (u i) x) L (𝓝 (dist x x)) :=
      hu.dist (tendsto_const_nhds (x := x))
    simpa using hd.const_mul (K : ℝ)
  have hb : Tendsto (fun i => dist (f i x) (g x)) L (𝓝 0) :=
    tendsto_iff_dist_tendsto_zero.mp (hg x)
  have hab : Tendsto (fun i => (K : ℝ) * dist (u i) x + dist (f i x) (g x)) L (𝓝 0) := by
    simpa using ha.add hb
  exact squeeze_zero (fun _ => dist_nonneg) (fun i =>
    (dist_triangle (f i (u i)) (f i x) (g x)).trans
      (add_le_add ((hLip i).dist_le_mul (u i) x) le_rfl)) hab

def extensions (f : I → X → Y) : I → Completion X → Y :=
  fun i => Completion.extension (f i)

theorem extensions_lipschitz (K : ℝ≥0) (f : I → X → Y)
    (hLip : ∀ i, LipschitzWith K (f i)) : ∀ i, LipschitzWith K (extensions f i) :=
  fun i => (hLip i).completion_extension

@[simp] theorem extensions_coe (K : ℝ≥0) (f : I → X → Y)
    (hLip : ∀ i, LipschitzWith K (f i)) (i : I) (x : X) :
    extensions f i x = f i x :=
  Completion.extension_coe (hLip i).uniformContinuous x

theorem extensions_unique (K : ℝ≥0) (f : I → X → Y)
    (hLip : ∀ i, LipschitzWith K (f i)) (i : I) (u : Completion X → Y)
    (hu : UniformContinuous u) (heq : ∀ x : X, u x = f i x) :
    extensions f i = u :=
  Completion.extension_unique (hLip i).uniformContinuous hu (fun x => (heq x).symm)

/-- Full recovery on the completion, with arbitrary nontrivial indexing filter. -/
theorem complete_domain_recovery (L : Filter I) [L.NeBot] (K : ℝ≥0) (f : I → X → Y)
    (hLip : ∀ i, LipschitzWith K (f i)) (D : Set X) (hD : Dense D)
    (hC : ∀ d ∈ D, Cauchy (Filter.map (fun i => f i d) L)) :
    ∃ g : Completion X → Y,
      LipschitzWith K g ∧
      (∀ x, Tendsto (fun i => extensions f i x) L (𝓝 (g x))) ∧
      (∀ S, IsCompact S → TendstoUniformlyOn (extensions f) g L S) ∧
      (∀ (u : I → Completion X) x, Tendsto u L (𝓝 x) →
        Tendsto (fun i => extensions f i (u i)) L (𝓝 (g x))) := by
  let e : D → Completion X := fun d => ((d : X) : Completion X)
  have he : DenseRange e :=
    Completion.denseRange_coe.comp hD.denseRange_val (Completion.continuous_coe X)
  have hc : ∀ d ∈ Set.range e, Cauchy (Filter.map (fun i => extensions f i d) L) := by
    rintro _ ⟨d, rfl⟩
    simpa only [e, extensions_coe K f hLip] using hC d d.property
  obtain ⟨g, hgLip, hg⟩ := exists_lipschitz_limit L K (extensions f)
    (extensions_lipschitz K f hLip) (Set.range e) he hc
  exact ⟨g, hgLip, hg, compact_uniform_limit L K (extensions f) g
    (extensions_lipschitz K f hLip) hg,
    moving_input_limit L K (extensions f) g (extensions_lipschitz K f hLip) hg⟩

theorem recovered_unique (L : Filter I) [L.NeBot] (f : I → X → Y)
    {g h : Completion X → Y}
    (hg : ∀ x, Tendsto (fun i => extensions f i x) L (𝓝 (g x)))
    (hh : ∀ x, Tendsto (fun i => extensions f i x) L (𝓝 (h x))) : g = h := by
  funext x
  exact tendsto_nhds_unique (hg x) (hh x)

/-- Uniqueness already follows from the original dense observations. -/
theorem unique_from_dense_data (L : Filter I) [L.NeBot] (f : I → X → Y)
    (D : Set X) (hD : Dense D) {g h : Completion X → Y}
    (hg : Continuous g) (hh : Continuous h)
    (hgd : ∀ d ∈ D, Tendsto (fun i => f i d) L (𝓝 (g d)))
    (hhd : ∀ d ∈ D, Tendsto (fun i => f i d) L (𝓝 (h d))) : g = h := by
  let e : D → Completion X := fun d => ((d : X) : Completion X)
  have he : DenseRange e :=
    Completion.denseRange_coe.comp hD.denseRange_val (Completion.continuous_coe X)
  apply he.equalizer hg hh
  funext d
  exact tendsto_nhds_unique (hgd d d.property) (hhd d d.property)

end MathGauge.R106
