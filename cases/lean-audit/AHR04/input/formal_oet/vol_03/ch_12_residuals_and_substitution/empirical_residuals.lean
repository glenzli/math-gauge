import formal_oet.vol_02.ch_07_fitting_foundations.fitting_ball
import formal_oet.vol_02.ch_07_fitting_foundations.chain_recurrence
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace formal_oet.vol_03.ch_12_residuals_and_substitution

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open formal_oet.vol_01.ch_04_operator_chain_calculus
open formal_oet.vol_02.ch_07_fitting_foundations

open scoped BigOperators

variable {X I : Type} {bot : X} [Fintype I]

/--
OET anchor: h-6f9e054ce01ccfef
**定义（有限阈值）**
A tolerance or threshold is finite exactly when it is not the top element of
`\bar{\mathbb R}_+`.
-/
def finite_ennreal (a : ENNReal) : Prop :=
  a ≠ ⊤

/--
OET anchor: h-6f9e054ce01ccfef
**定义（采样结构与可评估分量）**
The component indices whose empirical residual can be evaluated because their
component sample set is nonempty.
-/
def evaluable_components (sample : I → Set X) : Set I :=
  {j | (sample j).Nonempty}

/--
OET anchor: h-6f9e054ce01ccfef
**定义（采样结构与可评估分量，采样结构）**
A finite ambient sample together with component sample subsets on which both
the proxy and target values are defined.
-/
structure SamplingStructure
    (target proxy : Operator X bot) (ambient : Set X)
    (sample : I → Set X) : Prop where
  finite_ambient : ambient.Finite
  component_subset :
    ∀ j : I, sample j ⊆
      {x | x ∈ ambient ∧ x ∈ dom proxy ∧ x ∈ dom target}

/--
OET anchor: h-6f9e054ce01ccfef
**定义（采样结构与可评估分量，环境包含）**
Every component sample point belongs to the finite ambient sample.
-/
theorem sampling_component_subset_ambient
    (target proxy : Operator X bot) (ambient : Set X)
    (sample : I → Set X)
    (str : SamplingStructure target proxy ambient sample) :
    ∀ j : I, sample j ⊆ ambient := by
  intro j x hx
  exact (str.component_subset j hx).1

/--
OET anchor: h-6f9e054ce01ccfef
**定义（采样结构与可评估分量，代理定义域）**
Every component sample point lies in the proxy domain.
-/
theorem sampling_component_subset_proxy_dom
    (target proxy : Operator X bot) (ambient : Set X)
    (sample : I → Set X)
    (str : SamplingStructure target proxy ambient sample) :
    ∀ j : I, sample j ⊆ dom proxy := by
  intro j x hx
  exact (str.component_subset j hx).2.1

/--
OET anchor: h-6f9e054ce01ccfef
**定义（采样结构与可评估分量，目标定义域）**
Every component sample point lies in the target domain.
-/
theorem sampling_component_subset_target_dom
    (target proxy : Operator X bot) (ambient : Set X)
    (sample : I → Set X)
    (str : SamplingStructure target proxy ambient sample) :
    ∀ j : I, sample j ⊆ dom target := by
  intro j x hx
  exact (str.component_subset j hx).2.2

/--
OET anchor: h-6f9e054ce01ccfef
**定义（采样结构与可评估分量，非可评估分量）**
Unfold the complement of the evaluable component set.
-/
theorem not_mem_evaluable_components_iff
    (sample : I → Set X) (j : I) :
    j ∉ evaluable_components sample ↔ ¬ (sample j).Nonempty := Iff.rfl

/--
OET anchor: h-6f9e054ce01ccfef
**定义（经验残差上界，采样上确界）**
The raw sampled residual supremum on one component.
-/
noncomputable def empirical_residual_raw_sup
    (d : I → X → X → ENNReal)
    (target proxy : Operator X bot) (sample : Set X) (j : I) : ENNReal :=
  ⨆ x : {x // x ∈ sample}, d j (proxy.func x.1) (target.func x.1)

/--
OET anchor: h-6f9e054ce01ccfef
**定义（经验残差上界，展开公式）**
The empirical residual upper bound is the sampled residual supremum plus the
observation-resolution correction.
-/
noncomputable def empirical_residual_upper
    (d : I → X → X → ENNReal)
    (target proxy : Operator X bot) (sample : I → Set X)
    (delta_o : I → ENNReal) (j : I) : ENNReal :=
  empirical_residual_raw_sup d target proxy (sample j) j + delta_o j

/--
OET anchor: h-6f9e054ce01ccfef
**定义（经验残差上界，采样上确界支配）**
Every sampled residual is bounded by the raw sampled supremum.
-/
theorem empirical_residual_raw_sup_bounds_sample
    (d : I → X → X → ENNReal)
    (target proxy : Operator X bot) (sample : Set X) (j : I) :
    ∀ x ∈ sample,
      d j (proxy.func x) (target.func x) ≤
        empirical_residual_raw_sup d target proxy sample j := by
  intro x hx
  exact le_iSup
    (fun y : {y // y ∈ sample} => d j (proxy.func y.1) (target.func y.1))
    ⟨x, hx⟩

/--
OET anchor: h-6f9e054ce01ccfef
**定义（经验残差上界，样本残差界）**
The empirical residual upper bound dominates every sampled residual.
-/
theorem empirical_residual_upper_bounds_sample
    (d : I → X → X → ENNReal)
    (target proxy : Operator X bot) (sample : I → Set X)
    (delta_o : I → ENNReal) (j : I) :
    ∀ x ∈ sample j,
      d j (proxy.func x) (target.func x) ≤
        empirical_residual_upper d target proxy sample delta_o j := by
  intro x hx
  unfold empirical_residual_upper
  exact le_trans
    (empirical_residual_raw_sup_bounds_sample d target proxy (sample j) j x hx)
    le_self_add

/--
OET anchor: h-6f9e054ce01ccfef
**定义（经验残差上界）**
A componentwise empirical residual certificate records exactly the pointwise
sample residual bounds used later by the chapter.
-/
structure EmpiricalResidualBound
    (d : I → X → X → ENNReal)
    (target proxy : Operator X bot)
    (sample : I → Set X) (eps : I → ENNReal) : Prop where
  sample_error :
    ∀ j : I, j ∈ evaluable_components sample →
      ∀ x ∈ sample j, d j (proxy.func x) (target.func x) ≤ eps j

/--
OET anchor: h-6f9e054ce01ccfef
**定义（经验残差上界，展开形式）**
Unpack the empirical residual certificate on an evaluable component.
-/
theorem empirical_residual_bound_on_sample
    (d : I → X → X → ENNReal)
    (target proxy : Operator X bot)
    (sample : I → Set X) (eps : I → ENNReal)
    (cert : EmpiricalResidualBound d target proxy sample eps) :
    ∀ j : I, j ∈ evaluable_components sample →
      ∀ x ∈ sample j, d j (proxy.func x) (target.func x) ≤ eps j :=
  cert.sample_error

/--
OET anchor: h-6f9e054ce01ccfef
**定义（经验残差上界，公式诱导证书）**
The `sup + δ_o` formula produces the residual certificate used by the later
chapter results on all evaluable components.
-/
theorem empirical_residual_upper_certificate
    (d : I → X → X → ENNReal)
    (target proxy : Operator X bot)
    (sample : I → Set X) (delta_o : I → ENNReal) :
    EmpiricalResidualBound d target proxy sample
      (empirical_residual_upper d target proxy sample delta_o) := by
  refine ⟨?_⟩
  intro j _hj x hx
  exact empirical_residual_upper_bounds_sample d target proxy sample delta_o j x hx

/--
OET anchor: h-6f9e054ce01ccfef
**定义（共同锚点加权距离）**
The column-`j` weighted common-anchor distance from a point to a component
sample set.  The same anchor `y` is used for every source component.
-/
noncomputable def weighted_anchor_distance
    (d : I → X → X → ENNReal)
    (A : I → I → ENNReal) (j : I) (x : X) (E : Set X) : ENNReal :=
  ⨅ y : {y // y ∈ E}, matrix_vector_bound A (fun i => d i x y.1) j

/--
OET anchor: h-6f9e054ce01ccfef
**定义（共同锚点最大间隙）**
The supremal weighted common-anchor gap over a working domain.
-/
noncomputable def max_anchor_gap
    (d : I → X → X → ENNReal)
    (A : I → I → ENNReal) (j : I) (U E : Set X) : ENNReal :=
  ⨆ x : {x // x ∈ U}, weighted_anchor_distance d A j x.1 E

/--
OET anchor: h-6f9e054ce01ccfef
**定义（经验保证子水平集）**
The sublevel set used in the sampling-augmentation monotonicity result.
-/
def anchor_gap_sublevel
    (d : I → X → X → ENNReal)
    (A : I → I → ENNReal) (j : I)
    (U E : Set X) (eta tau : ENNReal) : Set X :=
  {x | x ∈ U ∧ weighted_anchor_distance d A j x E + eta ≤ tau}

/--
OET anchor: h-48bb46f7ef1c3c2e
**命题（采样限制的单调性）**
Restricting the anchor set can only increase the common-anchor distance.
-/
theorem weighted_anchor_distance_mono_of_subset
    (d : I → X → X → ENNReal)
    (A : I → I → ENNReal) (j : I) (x : X)
    {S T : Set X} (hST : S ⊆ T) :
    weighted_anchor_distance d A j x T ≤ weighted_anchor_distance d A j x S := by
  unfold weighted_anchor_distance
  apply le_iInf
  intro y
  exact iInf_le
    (fun z : {z // z ∈ T} => matrix_vector_bound A (fun i => d i x z.1) j)
    ⟨y.1, hST y.2⟩

/--
OET anchor: h-48bb46f7ef1c3c2e
**引理（采样限制的单调性）**
Text-faithful wrapper retaining the nonempty restricted sample condition.
-/
theorem weighted_anchor_distance_mono_of_subset_text
    (d : I → X → X → ENNReal)
    (A : I → I → ENNReal) (j : I) (x : X)
    {Ssmall Slarge : Set X}
    (hsmall_nonempty : Ssmall.Nonempty)
    (hST : Ssmall ⊆ Slarge) :
    weighted_anchor_distance d A j x Slarge ≤
      weighted_anchor_distance d A j x Ssmall := by
  have _ := hsmall_nonempty
  exact weighted_anchor_distance_mono_of_subset d A j x hST

/--
OET anchor: h-48bb46f7ef1c3c2e
**命题（采样限制的单调性，最大间隙形式）**
The same monotonicity holds after taking the supremum over the working domain.
-/
theorem max_anchor_gap_mono_of_subset
    (d : I → X → X → ENNReal)
    (A : I → I → ENNReal) (j : I) (U : Set X)
    {S T : Set X} (hST : S ⊆ T) :
    max_anchor_gap d A j U T ≤ max_anchor_gap d A j U S := by
  unfold max_anchor_gap
  exact iSup_mono fun x =>
    weighted_anchor_distance_mono_of_subset d A j x.1 hST

/--
OET anchor: h-48bb46f7ef1c3c2e
**命题（采样限制的单调性，最大间隙正文前提版本）**
Text-faithful wrapper retaining the nonempty restricted sample condition.
-/
theorem max_anchor_gap_mono_of_subset_text
    (d : I → X → X → ENNReal)
    (A : I → I → ENNReal) (j : I) (U : Set X)
    {Ssmall Slarge : Set X}
    (hsmall_nonempty : Ssmall.Nonempty)
    (hST : Ssmall ⊆ Slarge) :
    max_anchor_gap d A j U Slarge ≤ max_anchor_gap d A j U Ssmall := by
  have _ := hsmall_nonempty
  exact max_anchor_gap_mono_of_subset d A j U hST

/--
OET anchor: h-59d7df4e412804c3
**推论（采样增广的条件单调性）**
Adding anchors can only decrease the common-anchor distance.
-/
theorem weighted_anchor_distance_mono_of_superset
    (d : I → X → X → ENNReal)
    (A : I → I → ENNReal) (j : I) (x : X)
    {S T : Set X} (hST : S ⊆ T) :
    weighted_anchor_distance d A j x T ≤ weighted_anchor_distance d A j x S :=
  weighted_anchor_distance_mono_of_subset d A j x hST

/--
OET anchor: h-59d7df4e412804c3
**推论（采样增广的条件单调性，最大间隙形式）**
The maximal gap also decreases when the anchor set is enlarged.
-/
theorem max_anchor_gap_mono_of_superset
    (d : I → X → X → ENNReal)
    (A : I → I → ENNReal) (j : I) (U : Set X)
    {S T : Set X} (hST : S ⊆ T) :
    max_anchor_gap d A j U T ≤ max_anchor_gap d A j U S :=
  max_anchor_gap_mono_of_subset d A j U hST

/--
OET anchor: h-59d7df4e412804c3
**推论（采样增广的条件单调性，保证域形式）**
If the anchor set is enlarged and the residual tolerance does not increase,
then the corresponding empirical guarantee sublevel set expands.
-/
theorem anchor_gap_sublevel_mono_of_sample_augmentation
    (d : I → X → X → ENNReal)
    (A : I → I → ENNReal) (j : I) (U : Set X)
    {S T : Set X} {etaS etaT tau : ENNReal}
    (hST : S ⊆ T) (heta : etaT ≤ etaS) :
    anchor_gap_sublevel d A j U S etaS tau ⊆
      anchor_gap_sublevel d A j U T etaT tau := by
  intro x hx
  exact ⟨hx.1,
    le_trans
      (add_le_add (weighted_anchor_distance_mono_of_superset d A j x hST) heta)
      hx.2⟩

/--
OET anchor: h-59d7df4e412804c3
**推论（采样增广的条件单调性，有限阈值版本）**
Text-faithful wrapper retaining the nonempty original sample and finite
threshold assumptions from the chapter text.
-/
theorem anchor_gap_sublevel_mono_of_sample_augmentation_text
    (d : I → X → X → ENNReal)
    (A : I → I → ENNReal) (j : I) (U : Set X)
    {S T : Set X} {etaS etaT tau : ENNReal}
    (hS_nonempty : S.Nonempty)
    (htau_finite : finite_ennreal tau)
    (hST : S ⊆ T) (heta : etaT ≤ etaS) :
    anchor_gap_sublevel d A j U S etaS tau ⊆
      anchor_gap_sublevel d A j U T etaT tau := by
  have _ := hS_nonempty
  have _ := htau_finite
  exact anchor_gap_sublevel_mono_of_sample_augmentation d A j U hST heta

end formal_oet.vol_03.ch_12_residuals_and_substitution
