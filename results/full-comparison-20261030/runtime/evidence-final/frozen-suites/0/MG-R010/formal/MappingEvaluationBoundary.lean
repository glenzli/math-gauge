import MappingNaturality
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.UniformSpace.CompleteSeparated
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.NormNum

noncomputable section
open TopologicalSpace Topology Set Filter
namespace MathGauge.Mapping

theorem rational_not_locally_compact : ¬ LocallyCompactSpace ℚ := by
  intro h
  letI := h
  letI : CompleteSpace ℚ := IsRightUniformAddGroup.completeSpace_of_weaklyLocallyCompactSpace
  have hc : IsClosed (Set.range ((↑) : ℚ → ℝ)) :=
    Rat.isUniformEmbedding_coe_real.isClosedEmbedding.isClosed_range
  have hall : Set.range ((↑) : ℚ → ℝ) = univ := by
    rw [← hc.closure_eq]
    exact Rat.denseRange_cast.closure_range
  have hs : Real.sqrt 2 ∈ Set.range ((↑) : ℚ → ℝ) := by rw [hall]; trivial
  exact irrational_sqrt_two hs

/-- No compact subset of the rationals can contain a neighborhood of zero. -/
theorem rational_compact_not_mem_nhds {K : Set ℚ} (hK : IsCompact K) : K ∉ 𝓝 (0 : ℚ) := by
  intro h
  exact rational_not_locally_compact (hK.locallyCompactSpace_of_mem_nhds_of_addGroup h)

/-- The reference boundary uses a domain which really is compactly generated. -/
theorem rational_compactly_generated : UCompactlyGeneratedSpace.{0} ℚ := inferInstance

/-- Ordinary compact-open evaluation fails even at the zero map and zero point. -/
theorem rational_evaluation_not_continuousAt :
    ¬ ContinuousAt (fun p : C(ℚ,ℝ) × ℚ => p.1 p.2) (ContinuousMap.const ℚ 0,0) := by
  intro h
  have hm : (fun p : C(ℚ,ℝ) × ℚ => p.1 p.2) ⁻¹' Iio (1 : ℝ) ∈
      𝓝 (ContinuousMap.const ℚ 0, (0 : ℚ)) :=
    h.preimage_mem_nhds (isOpen_Iio.mem_nhds (by norm_num))
  obtain ⟨U,hU,V,hV,hUV⟩ := mem_nhds_prod_iff.mp hm
  obtain ⟨S,hSf,hS,hSU⟩ := ContinuousMap.mem_nhds_iff.mp hU
  let K : Set ℚ := ⋃ KU ∈ S, KU.1
  have hK : IsCompact K := hSf.isCompact_biUnion (fun KU hKU => (hS KU.1 KU.2 hKU).1)
  have hnot : ¬ V ⊆ K := by
    intro hv
    exact rational_compact_not_mem_nhds hK (mem_of_superset hV hv)
  obtain ⟨a,haV,haK⟩ := Set.not_subset.mp hnot
  obtain ⟨f,hfK,hfa,_⟩ := exists_continuous_zero_one_of_isClosed hK.isClosed
    (isClosed_singleton : IsClosed ({a} : Set ℚ)) (by
      simpa only [disjoint_singleton_right] using haK)
  let g : C(ℚ,ℝ) := ⟨fun x => 2 * f x, continuous_const.mul f.continuous⟩
  have hgU : g ∈ U := hSU (by
    intro C O hCO x hx
    have hxK : x ∈ K := Set.mem_iUnion.mpr ⟨(C,O),Set.mem_iUnion.mpr ⟨hCO,hx⟩⟩
    have hf0 : f x = 0 := hfK hxK
    have h0 : (0 : ℝ) ∈ O := (hS C O hCO).2.2 hx
    simpa only [g, ContinuousMap.coe_mk, hf0, mul_zero] using h0)
  have hg2 : g a = 2 := by
    have hf1 : f a = 1 := hfa (by simp)
    simp only [g, ContinuousMap.coe_mk, hf1, mul_one]
  have hlt := hUV (show (g,a) ∈ U ×ˢ V from ⟨hgU,haV⟩)
  change g a < 1 at hlt
  rw [hg2] at hlt
  norm_num at hlt

theorem rational_evaluation_not_continuous :
    ¬ Continuous (fun p : C(ℚ,ℝ) × ℚ => p.1 p.2) :=
  fun h => rational_evaluation_not_continuousAt h.continuousAt

end MathGauge.Mapping
