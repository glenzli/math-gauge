import formal_oet.vol_03.ch_13_comparison_and_falsification.sampling_falsification
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace formal_oet.vol_03.ch_13_comparison_and_falsification

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_02.ch_07_fitting_foundations
open formal_oet.vol_03.ch_12_residuals_and_substitution

variable {X I : Type} {bot : X} [Fintype I]

/--
OET anchor: h-16c8c408719ed50b
**定义（采样相容类）**
The tolerant sample-compatible class determined by component samples, labels,
component set, and tolerance vector.
-/
def sample_compatible_class
    (d : I → X → X → ENNReal)
    (label : X → X) (sample : I → Set X) (J : Set I)
    (eta : I → ENNReal) (psi : Operator X bot) : Prop :=
  ∀ j : I, j ∈ J → ∀ x ∈ sample j,
    d j (psi.func x) (label x) ≤ eta j

/--
OET anchor: h-16c8c408719ed50b
**定义（相容类上的样本可识别性）**
A property is sample-identifiable on a compatible class exactly when it has
the same truth value for every two members of that class.
-/
def SampleIdentifiable
    (d : I → X → X → ENNReal)
    (label : X → X) (sample : I → Set X) (J : Set I)
    (eta : I → ENNReal) (P : Operator X bot → Prop) : Prop :=
  ∀ u v : Operator X bot,
    sample_compatible_class d label sample J eta u →
    sample_compatible_class d label sample J eta v →
    (P u ↔ P v)

/--
OET anchor: h-16c8c408719ed50b
**定义（采样相容类，零容限退化）**
Zero-tolerance compatibility with a target is the corresponding specialization
of the tolerant compatible class.
-/
theorem zero_tolerance_sample_compatible_is_compatible_class
    (d : I → X → X → ENNReal)
    (target psi : Operator X bot) (sample : I → Set X) (J : Set I)
    (h : zero_tolerance_sample_compatible d target psi sample J) :
    sample_compatible_class d target.func sample J (fun _ => 0) psi := by
  intro j hj x hx
  exact le_of_eq (h j hj x hx)

/--
OET anchor: h-144749b31a4914e1
**命题（采样相容类的非识别性，零容限情形）**
The finite-sample complement construction at `h-d58fb36d7b840be1` supplies two
zero-tolerance-compatible targets that differ at an unsampled point.
-/
theorem zero_tolerance_sample_nonidentification_from_unsampled_point
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target : Operator X bot) (sample : I → Set X) (J : Set I)
    (U : Set X)
    {x₀ a b : X} {ell : I}
    (hx₀U : x₀ ∈ U)
    (hx₀_not_sample : x₀ ∉ sample_union sample J)
    (hx₀_ne_bot : x₀ ≠ bot)
    (hsep : 0 < d ell a b) :
    ∃ psi_a psi_b : Operator X bot,
      zero_tolerance_sample_compatible d target psi_a sample J ∧
      zero_tolerance_sample_compatible d target psi_b sample J ∧
      0 < d ell (psi_a.func x₀) (psi_b.func x₀) :=
  finite_sample_complement_underdetermined d hd target sample J U
    hx₀U hx₀_not_sample hx₀_ne_bot hsep

/--
OET anchor: h-144749b31a4914e1
**命题（采样相容类的非识别性，零容限正文版本）**
The text-level statement retains the nonempty component family.
-/
theorem zero_tolerance_sample_nonidentification_from_unsampled_point_text
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target : Operator X bot) (sample : I → Set X) (J : Set I)
    (U : Set X)
    {x₀ a b : X} {ell : I}
    (hJ_nonempty : J.Nonempty)
    (hx₀U : x₀ ∈ U)
    (hx₀_not_sample : x₀ ∉ sample_union sample J)
    (hx₀_ne_bot : x₀ ≠ bot)
    (hsep : 0 < d ell a b) :
    ∃ psi_a psi_b : Operator X bot,
      zero_tolerance_sample_compatible d target psi_a sample J ∧
      zero_tolerance_sample_compatible d target psi_b sample J ∧
      0 < d ell (psi_a.func x₀) (psi_b.func x₀) := by
  have _ := hJ_nonempty
  exact zero_tolerance_sample_nonidentification_from_unsampled_point
    d hd target sample J U hx₀U hx₀_not_sample hx₀_ne_bot hsep

/--
OET anchor: h-144749b31a4914e1
**命题（采样相容类的非识别性）**
If a property is not constant on a compatible class, then it is not uniquely
determined by that class.
-/
theorem property_not_unique_on_compatible_of_witness
    (d : I → X → X → ENNReal)
    (label : X → X) (sample : I → Set X) (J : Set I)
    (eta : I → ENNReal) (P : Operator X bot → Prop)
    {psi chi : Operator X bot}
    (hpsi : sample_compatible_class d label sample J eta psi)
    (hchi : sample_compatible_class d label sample J eta chi)
    (hPpsi : P psi) (hPchi : ¬ P chi) :
    ¬ SampleIdentifiable d label sample J eta P := by
  intro hconstant
  exact hPchi ((hconstant psi chi hpsi hchi).1 hPpsi)

/--
OET anchor: h-144749b31a4914e1
**命题（采样相容类的非识别性，性质正文版本）**
The text-level property statement retains the nonempty component family.
-/
theorem property_not_unique_on_compatible_of_witness_text
    (d : I → X → X → ENNReal)
    (label : X → X) (sample : I → Set X) (J : Set I)
    (eta : I → ENNReal) (P : Operator X bot → Prop)
    {psi chi : Operator X bot}
    (hJ_nonempty : J.Nonempty)
    (hpsi : sample_compatible_class d label sample J eta psi)
    (hchi : sample_compatible_class d label sample J eta chi)
    (hPpsi : P psi) (hPchi : ¬ P chi) :
    ¬ SampleIdentifiable d label sample J eta P := by
  have _ := hJ_nonempty
  exact property_not_unique_on_compatible_of_witness
    d label sample J eta P hpsi hchi hPpsi hPchi

/--
OET anchor: h-16c8c408719ed50b
**定义（潜在采样坐标与潜在输出集，可见纤维）**
The hidden coordinates whose visible readout equals a fixed visible input.
-/
def visible_fiber {Z : Type} (pi : Z → X) (x : X) : Set Z :=
  {z | pi z = x}

/--
OET anchor: h-16c8c408719ed50b
**定义（潜在采样坐标与潜在输出集）**
The set of target outputs obtained from hidden coordinates over one visible
input.
-/
def latent_output_set {Z : Type} (pi : Z → X) (theta : Z → X) (x : X) : Set X :=
  theta '' visible_fiber pi x

/--
OET anchor: h-16c8c408719ed50b
**定义（潜在纤维冲突集）**
The visible inputs whose hidden fiber contains two outputs separated by more
than twice the tolerance.  Lean writes `2 ε` as `ε + ε`.
-/
def hidden_fiber_conflict {Z : Type}
    (d : I → X → X → ENNReal) (pi : Z → X) (theta : Z → X)
    (j : I) (eps : ENNReal) : Set X :=
  {x | ∃ z₁ ∈ visible_fiber pi x, ∃ z₂ ∈ visible_fiber pi x,
    eps + eps < d j (theta z₁) (theta z₂)}

/--
OET anchor: h-9c7dcb61b93679c7
**命题（表观多值冲突的单值拟合阻断，点对形式）**
Two hidden outputs separated by more than `2 ε` cannot both be fitted by one
visible output within `ε`.
-/
theorem no_single_value_fit_of_hidden_fiber_pair_gap {Z : Type}
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (pi : Z → X) (theta : Z → X)
    {x y : X} {z₁ z₂ : Z} {j : I} {eps : ENNReal}
    (hz₁ : z₁ ∈ visible_fiber pi x)
    (hz₂ : z₂ ∈ visible_fiber pi x)
    (hgap : eps + eps < d j (theta z₁) (theta z₂))
    (hy₁ : d j y (theta z₁) ≤ eps)
    (hy₂ : d j y (theta z₂) ≤ eps) :
    False := by
  have _ := hz₁
  have _ := hz₂
  have hy₁_symm : d j (theta z₁) y ≤ eps := by
    simpa [(hd j).symm (theta z₁) y] using hy₁
  have hupper :
      d j (theta z₁) (theta z₂) ≤ eps + eps := by
    exact le_trans ((hd j).triangle (theta z₁) y (theta z₂))
      (add_le_add hy₁_symm hy₂)
  exact not_lt_of_ge hupper hgap

/--
OET anchor: h-9c7dcb61b93679c7
**命题（表观多值冲突的单值拟合阻断，正文点对版本）**
The text-level statement retains the finite tolerance and expresses
nonexistence as the negation of simultaneous fitting.
-/
theorem no_single_value_fit_of_hidden_fiber_pair_gap_text {Z : Type}
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (pi : Z → X) (theta : Z → X)
    (J : Set I) {x y : X} {z₁ z₂ : Z} {j : I} {eps : ENNReal}
    (hj : j ∈ J)
    (heps_finite : finite_ennreal eps)
    (hz₁ : z₁ ∈ visible_fiber pi x)
    (hz₂ : z₂ ∈ visible_fiber pi x)
    (hgap : eps + eps < d j (theta z₁) (theta z₂)) :
    ¬ (d j y (theta z₁) ≤ eps ∧ d j y (theta z₂) ≤ eps) := by
  have _ := hj
  have _ := heps_finite
  intro hfit
  exact no_single_value_fit_of_hidden_fiber_pair_gap d hd pi theta
    hz₁ hz₂ hgap hfit.1 hfit.2

/--
OET anchor: h-9c7dcb61b93679c7
**命题（表观多值冲突的单值拟合阻断，纤维形式）**
A visible output fits a whole hidden fiber at tolerance `eps` when it fits every
hidden coordinate over that visible input.
-/
def single_value_fits_visible_fiber {Z : Type}
    (d : I → X → X → ENNReal) (pi : Z → X) (theta : Z → X)
    (j : I) (eps : ENNReal) (x y : X) : Prop :=
  ∀ z ∈ visible_fiber pi x, d j y (theta z) ≤ eps

/--
OET anchor: h-9c7dcb61b93679c7
**命题（表观多值冲突的单值拟合阻断）**
Membership in the hidden-fiber conflict set excludes every single visible
output from fitting the whole hidden fiber.
-/
theorem not_single_value_fits_visible_fiber_of_hidden_conflict {Z : Type}
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (pi : Z → X) (theta : Z → X)
    {j : I} {eps : ENNReal} {x y : X}
    (hx : x ∈ hidden_fiber_conflict d pi theta j eps) :
    ¬ single_value_fits_visible_fiber d pi theta j eps x y := by
  intro hfit
  rcases hx with ⟨z₁, hz₁, z₂, hz₂, hgap⟩
  exact no_single_value_fit_of_hidden_fiber_pair_gap d hd pi theta
    hz₁ hz₂ hgap (hfit z₁ hz₁) (hfit z₂ hz₂)

/--
OET anchor: h-9c7dcb61b93679c7
**命题（表观多值冲突的单值拟合阻断，代理形式）**
If a visible input lies in the hidden conflict set, the value of any
single-valued proxy at that input cannot fit the whole hidden fiber.
-/
theorem not_proxy_fits_visible_fiber_of_hidden_conflict {Z : Type}
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (pi : Z → X) (theta : Z → X) (proxy : Operator X bot)
    {j : I} {eps : ENNReal} {x : X}
    (hxdom : x ∈ dom proxy)
    (hx : x ∈ hidden_fiber_conflict d pi theta j eps) :
    ¬ single_value_fits_visible_fiber d pi theta j eps x (proxy.func x) := by
  have _ := hxdom
  exact not_single_value_fits_visible_fiber_of_hidden_conflict d hd pi theta hx

/--
OET anchor: h-9c7dcb61b93679c7
**命题（表观多值冲突的单值拟合阻断，正文代理版本）**
The proxy specialization retains the finite tolerance and domain condition.
-/
theorem not_proxy_fits_visible_fiber_of_hidden_conflict_text {Z : Type}
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (pi : Z → X) (theta : Z → X) (proxy : Operator X bot) (J : Set I)
    {j : I} {eps : ENNReal} {x : X}
    (hj : j ∈ J)
    (heps_finite : finite_ennreal eps)
    (hxdom : x ∈ dom proxy)
    (hx : x ∈ hidden_fiber_conflict d pi theta j eps) :
    ¬ single_value_fits_visible_fiber d pi theta j eps x (proxy.func x) := by
  have _ := hj
  have _ := heps_finite
  exact not_proxy_fits_visible_fiber_of_hidden_conflict d hd pi theta proxy hxdom hx

/--
OET anchor: h-069c6fb0beae6a3e
**命题（潜在纤维截面的零测距等价性，截面目标）**
The visible target induced by a hidden-coordinate selector.
-/
def visible_target_of_section {Z : Type} (theta : Z → X) (sel : X → Z) : X → X :=
  fun x => theta (sel x)

/--
OET anchor: h-069c6fb0beae6a3e
**命题（潜在纤维截面的零测距等价性）**
If every hidden fiber is zero-distance on the chosen component set, then any
two visible sections induce zero-equivalent visible targets on that set.
-/
theorem latent_zero_fiber_sections_equivalent {Z : Type}
    (d : I → X → X → ENNReal)
    (pi : Z → X) (theta : Z → X) (U : Set X) (J₀ : Set I)
    (section₁ section₂ : X → Z)
    (hzero :
      ∀ x ∈ U, ∀ z₁ ∈ visible_fiber pi x, ∀ z₂ ∈ visible_fiber pi x,
        ∀ j : I, j ∈ J₀ → d j (theta z₁) (theta z₂) = 0)
    (hsection₁ : ∀ x ∈ U, section₁ x ∈ visible_fiber pi x)
    (hsection₂ : ∀ x ∈ U, section₂ x ∈ visible_fiber pi x) :
    ∀ x ∈ U, ∀ j : I, j ∈ J₀ →
      d j (visible_target_of_section theta section₁ x)
        (visible_target_of_section theta section₂ x) = 0 := by
  intro x hx j hj
  exact hzero x hx (section₁ x) (hsection₁ x hx)
    (section₂ x) (hsection₂ x hx) j hj

/--
OET anchor: h-069c6fb0beae6a3e
**命题（潜在纤维截面的零测距等价性，正文前提版本）**
Sections are defined only on `U`, and the nonempty component family is retained
exactly as in the text.
-/
theorem latent_zero_fiber_subtype_sections_equivalent_text {Z : Type}
    (d : I → X → X → ENNReal)
    (pi : Z → X) (theta : Z → X) (U : Set X) (J J₀ : Set I)
    (section₁ section₂ : {x : X // x ∈ U} → Z)
    (hJ₀_subset : J₀ ⊆ J)
    (hJ₀_nonempty : J₀.Nonempty)
    (hzero :
      ∀ x ∈ U, ∀ z₁ ∈ visible_fiber pi x, ∀ z₂ ∈ visible_fiber pi x,
        ∀ j : I, j ∈ J₀ → d j (theta z₁) (theta z₂) = 0)
    (hsection₁ : ∀ x : {x : X // x ∈ U}, pi (section₁ x) = x.1)
    (hsection₂ : ∀ x : {x : X // x ∈ U}, pi (section₂ x) = x.1) :
    ∀ x : {x : X // x ∈ U}, ∀ j : I, j ∈ J₀ →
      d j (theta (section₁ x)) (theta (section₂ x)) = 0 := by
  have _ := hJ₀_subset
  have _ := hJ₀_nonempty
  intro x j hj
  exact hzero x.1 x.2 (section₁ x) (hsection₁ x)
    (section₂ x) (hsection₂ x) j hj

end formal_oet.vol_03.ch_13_comparison_and_falsification
