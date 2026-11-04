import formal_oet.vol_02.ch_07_fitting_foundations.fitting_ball
import formal_oet.vol_03.ch_12_residuals_and_substitution.empirical_residuals
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
OET anchor: h-9655cbb9401e5c90
**定义（目标 Lip 包络证书）**
An external target-side Lip envelope certificate on a specified domain.
-/
structure TargetLipEnvelopeCertificate
    (d : I → X → X → ENNReal)
    (target : Operator X bot) (V : Set X) (L : I → I → ENNReal) : Prop where
  lip_matrix : IsLipMatrix d target V L

/--
OET anchor: h-9655cbb9401e5c90
**定义（目标 co-Lip 下界证书）**
An external target-side co-Lip lower certificate on a specified domain.
-/
structure TargetCoLipLowerCertificate
    (d : I → X → X → ENNReal)
    (target : Operator X bot) (V : Set X) (K : I → I → ENNReal) : Prop where
  colip_matrix : IsCoLipMatrix d target V K

/--
OET anchor: h-f16da76e4331b725
**命题（经验目标扰动上界，矩阵加法）**
Pointwise matrix addition distributes across the finite matrix-vector action.
-/
theorem matrix_vector_bound_matrix_add
    (L₁ L₂ : I → I → ENNReal) (v : I → ENNReal) (j : I) :
    matrix_vector_bound (fun i j => L₁ i j + L₂ i j) v j =
      matrix_vector_bound L₁ v j + matrix_vector_bound L₂ v j := by
  unfold matrix_vector_bound
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]

/--
OET anchor: h-f16da76e4331b725
**命题（经验目标扰动上界，逐点形式）**
With proxy and target Lip certificates, one empirical anchor bounds the
target-proxy error.  Taking the infimum over the same anchor gives the
common-anchor estimate.
-/
theorem empirical_target_perturbation_upper_point
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot) (U V sample : Set X)
    (Lp Lstar : I → I → ENNReal) (eps : ENNReal) (j : I)
    (hU : U ⊆ V)
    (hsample : sample ⊆ U)
    (hLp : IsLipMatrix d proxy U Lp)
    (hLstar : IsLipMatrix d target V Lstar)
    (hres : ∀ y ∈ sample, d j (proxy.func y) (target.func y) ≤ eps) :
    ∀ x ∈ U,
      d j (proxy.func x) (target.func x) ≤
        weighted_anchor_distance d (fun i j => Lp i j + Lstar i j) j x sample + eps := by
  intro x hx
  have hxV : x ∈ V := hU hx
  have h_each :
      ∀ y : {y // y ∈ sample},
        d j (proxy.func x) (target.func x) ≤
          matrix_vector_bound (fun i j => Lp i j + Lstar i j)
            (fun i => d i x y.1) j + eps := by
    intro y
    have hyU : y.1 ∈ U := hsample y.2
    have hyV : y.1 ∈ V := hU hyU
    have htri₁ :=
      (hd j).triangle (proxy.func x) (proxy.func y.1) (target.func x)
    have htri₂ :=
      (hd j).triangle (proxy.func y.1) (target.func y.1) (target.func x)
    have hproxy :
        d j (proxy.func x) (proxy.func y.1) ≤
          matrix_vector_bound Lp (fun i => d i x y.1) j := by
      simpa [matrix_vector_bound] using hLp.2 x hx y.1 hyU j
    have htarget :
        d j (target.func y.1) (target.func x) ≤
          matrix_vector_bound Lstar (fun i => d i x y.1) j := by
      have hraw :
          d j (target.func x) (target.func y.1) ≤
            matrix_vector_bound Lstar (fun i => d i x y.1) j := by
        simpa [matrix_vector_bound] using hLstar.2 x hxV y.1 hyV j
      simpa [(hd j).symm (target.func y.1) (target.func x)] using hraw
    have hmiddle :
        d j (proxy.func y.1) (target.func x) ≤
          eps + matrix_vector_bound Lstar (fun i => d i x y.1) j := by
      exact le_trans htri₂ (add_le_add (hres y.1 y.2) htarget)
    calc
      d j (proxy.func x) (target.func x)
          ≤ d j (proxy.func x) (proxy.func y.1) +
              d j (proxy.func y.1) (target.func x) := htri₁
      _ ≤ matrix_vector_bound Lp (fun i => d i x y.1) j +
            (eps + matrix_vector_bound Lstar (fun i => d i x y.1) j) :=
          add_le_add hproxy hmiddle
      _ = matrix_vector_bound (fun i j => Lp i j + Lstar i j)
            (fun i => d i x y.1) j + eps := by
          rw [matrix_vector_bound_matrix_add]
          simp [add_comm, add_left_comm]
  have hiinf :
      d j (proxy.func x) (target.func x) ≤
        ⨅ y : {y // y ∈ sample},
          matrix_vector_bound (fun i j => Lp i j + Lstar i j)
            (fun i => d i x y.1) j + eps :=
    le_iInf h_each
  simpa [weighted_anchor_distance, ENNReal.iInf_add] using hiinf

/--
OET anchor: h-f16da76e4331b725
**命题（经验目标扰动上界，域上确界形式）**
The pointwise common-anchor estimate bounds the component distance vector on
the working domain.
-/
theorem empirical_target_perturbation_upper_sup
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot) (U V sample : Set X)
    (Lp Lstar : I → I → ENNReal) (eps : ENNReal) (j : I)
    (hU : U ⊆ V)
    (hsample : sample ⊆ U)
    (hLp : IsLipMatrix d proxy U Lp)
    (hLstar : IsLipMatrix d target V Lstar)
    (hres : ∀ y ∈ sample, d j (proxy.func y) (target.func y) ≤ eps) :
    component_error_vector d target proxy U j ≤
      max_anchor_gap d (fun i j => Lp i j + Lstar i j) j U sample + eps := by
  unfold component_error_vector max_anchor_gap
  apply iSup_le
  intro x
  have hpoint :=
    empirical_target_perturbation_upper_point d hd target proxy U V sample
      Lp Lstar eps j hU hsample hLp hLstar hres x.1 x.2
  have hsymm :
      d j (target.func x.1) (proxy.func x.1) ≤
        weighted_anchor_distance d (fun i j => Lp i j + Lstar i j) j x.1 sample + eps := by
    simpa [(hd j).symm (target.func x.1) (proxy.func x.1)] using hpoint
  exact le_trans hsymm
    (add_le_add (le_iSup
      (fun x : {x // x ∈ U} =>
        weighted_anchor_distance d (fun i j => Lp i j + Lstar i j) j x.1 sample) x) le_rfl)

/--
OET anchor: h-f16da76e4331b725
**命题（经验目标扰动上界）**
The pointwise upper bound specialized to an evaluable component and a
componentwise empirical residual certificate.
-/
theorem empirical_target_perturbation_upper_point_from_residual_certificate
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot) (U V : Set X)
    (sample : I → Set X)
    (Lp Lstar : I → I → ENNReal) (eps : I → ENNReal) (j : I)
    (hU : U ⊆ V)
    (hsample : sample j ⊆ U)
    (hLp : IsLipMatrix d proxy U Lp)
    (hLstar : TargetLipEnvelopeCertificate d target V Lstar)
    (hres : EmpiricalResidualBound d target proxy sample eps)
    (hj : j ∈ evaluable_components sample) :
    ∀ x ∈ U,
      d j (proxy.func x) (target.func x) ≤
        weighted_anchor_distance d (fun i j => Lp i j + Lstar i j) j x (sample j) +
          eps j := by
  exact empirical_target_perturbation_upper_point d hd target proxy U V (sample j)
    Lp Lstar (eps j) j hU hsample hLp hLstar.lip_matrix
    (hres.sample_error j hj)

/--
OET anchor: h-f16da76e4331b725
**命题（经验目标扰动上界，可评估分量上确界形式）**
The domain supremum version specialized to an evaluable component and a
componentwise empirical residual certificate.
-/
theorem empirical_target_perturbation_upper_sup_from_residual_certificate
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot) (U V : Set X)
    (sample : I → Set X)
    (Lp Lstar : I → I → ENNReal) (eps : I → ENNReal) (j : I)
    (hU : U ⊆ V)
    (hsample : sample j ⊆ U)
    (hLp : IsLipMatrix d proxy U Lp)
    (hLstar : TargetLipEnvelopeCertificate d target V Lstar)
    (hres : EmpiricalResidualBound d target proxy sample eps)
    (hj : j ∈ evaluable_components sample) :
    component_error_vector d target proxy U j ≤
      max_anchor_gap d (fun i j => Lp i j + Lstar i j) j U (sample j) + eps j := by
  exact empirical_target_perturbation_upper_sup d hd target proxy U V (sample j)
    Lp Lstar (eps j) j hU hsample hLp hLstar.lip_matrix
    (hres.sample_error j hj)

/--
OET anchor: h-5f713424d00a09e9
**定义（读取误差证书与读取修正锚点距离）**
The readout-corrected anchor distance replaces the target sample residual by
the proxy-to-label residual plus a pointwise readout error certificate.
-/
noncomputable def readout_corrected_anchor_distance
    (d : I → X → X → ENNReal)
    (proxy : Operator X bot) (A : I → I → ENNReal) (j : I)
    (label : X → X) (readout_error : X → ENNReal)
    (x : X) (sample : Set X) : ENNReal :=
  ⨅ y : {y // y ∈ sample},
    matrix_vector_bound A (fun i => d i x y.1) j +
      d j (proxy.func y.1) (label y.1) +
      readout_error y.1

/--
OET anchor: h-5f713424d00a09e9
**命题（逐点读取误差下的经验上界）**
With proxy and target Lip certificates, labels equipped with pointwise readout
error certificates give a refined common-anchor upper bound.
-/
theorem readout_error_empirical_upper_point
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot) (U V sample : Set X)
    (Lp Lstar : I → I → ENNReal) (label : X → X)
    (readout_error : X → ENNReal) (j : I)
    (hU : U ⊆ V)
    (hsample : sample ⊆ U)
    (hLp : IsLipMatrix d proxy U Lp)
    (hLstar : IsLipMatrix d target V Lstar)
    (hread : ∀ y ∈ sample, d j (label y) (target.func y) ≤ readout_error y) :
    ∀ x ∈ U,
      d j (proxy.func x) (target.func x) ≤
        readout_corrected_anchor_distance d proxy
          (fun i j => Lp i j + Lstar i j) j label readout_error x sample := by
  intro x hx
  have hxV : x ∈ V := hU hx
  have h_each :
      ∀ y : {y // y ∈ sample},
        d j (proxy.func x) (target.func x) ≤
          matrix_vector_bound (fun i j => Lp i j + Lstar i j)
            (fun i => d i x y.1) j +
            d j (proxy.func y.1) (label y.1) +
            readout_error y.1 := by
    intro y
    have hyU : y.1 ∈ U := hsample y.2
    have hyV : y.1 ∈ V := hU hyU
    have hproxy :
        d j (proxy.func x) (proxy.func y.1) ≤
          matrix_vector_bound Lp (fun i => d i x y.1) j := by
      simpa [matrix_vector_bound] using hLp.2 x hx y.1 hyU j
    have htarget :
        d j (target.func y.1) (target.func x) ≤
          matrix_vector_bound Lstar (fun i => d i x y.1) j := by
      have hraw :
          d j (target.func x) (target.func y.1) ≤
            matrix_vector_bound Lstar (fun i => d i x y.1) j := by
        simpa [matrix_vector_bound] using hLstar.2 x hxV y.1 hyV j
      simpa [(hd j).symm (target.func y.1) (target.func x)] using hraw
    have hlabel_target :
        d j (label y.1) (target.func x) ≤
          readout_error y.1 + matrix_vector_bound Lstar (fun i => d i x y.1) j := by
      exact le_trans ((hd j).triangle (label y.1) (target.func y.1) (target.func x))
        (add_le_add (hread y.1 y.2) htarget)
    have hproxy_label_target :
        d j (proxy.func y.1) (target.func x) ≤
          d j (proxy.func y.1) (label y.1) +
            (readout_error y.1 + matrix_vector_bound Lstar (fun i => d i x y.1) j) := by
      exact le_trans ((hd j).triangle (proxy.func y.1) (label y.1) (target.func x))
        (add_le_add le_rfl hlabel_target)
    calc
      d j (proxy.func x) (target.func x)
          ≤ d j (proxy.func x) (proxy.func y.1) +
              d j (proxy.func y.1) (target.func x) :=
            (hd j).triangle (proxy.func x) (proxy.func y.1) (target.func x)
      _ ≤ matrix_vector_bound Lp (fun i => d i x y.1) j +
            (d j (proxy.func y.1) (label y.1) +
              (readout_error y.1 + matrix_vector_bound Lstar (fun i => d i x y.1) j)) :=
            add_le_add hproxy hproxy_label_target
      _ = matrix_vector_bound (fun i j => Lp i j + Lstar i j)
            (fun i => d i x y.1) j +
            d j (proxy.func y.1) (label y.1) +
            readout_error y.1 := by
          rw [matrix_vector_bound_matrix_add]
          simp [add_comm, add_left_comm]
  exact le_iInf h_each

/--
OET anchor: h-5f713424d00a09e9
**命题（逐点读取误差下的经验上界，统一残差退化）**
If proxy-to-label residual plus readout error is uniformly bounded by `eta`,
the refined readout anchor bound is no larger than the original common-anchor
bound plus `eta`.
-/
theorem readout_corrected_anchor_distance_le_weighted_anchor_distance_add
    (d : I → X → X → ENNReal)
    (proxy : Operator X bot) (A : I → I → ENNReal) (j : I)
    (label : X → X) (readout_error : X → ENNReal)
    (x : X) (sample : Set X) (eta : ENNReal)
    (hbound :
      ∀ y ∈ sample, d j (proxy.func y) (label y) + readout_error y ≤ eta) :
    readout_corrected_anchor_distance d proxy A j label readout_error x sample ≤
      weighted_anchor_distance d A j x sample + eta := by
  have hle :
      (⨅ y : {y // y ∈ sample},
        matrix_vector_bound A (fun i => d i x y.1) j +
          d j (proxy.func y.1) (label y.1) +
          readout_error y.1) ≤
      (⨅ y : {y // y ∈ sample},
        matrix_vector_bound A (fun i => d i x y.1) j + eta) := by
    apply le_iInf
    intro y
    have hterm :
        matrix_vector_bound A (fun i => d i x y.1) j +
            d j (proxy.func y.1) (label y.1) +
            readout_error y.1 ≤
          matrix_vector_bound A (fun i => d i x y.1) j + eta := by
      calc
        matrix_vector_bound A (fun i => d i x y.1) j +
            d j (proxy.func y.1) (label y.1) +
            readout_error y.1
            = matrix_vector_bound A (fun i => d i x y.1) j +
                (d j (proxy.func y.1) (label y.1) + readout_error y.1) := by
                simp [add_assoc]
        _ ≤ matrix_vector_bound A (fun i => d i x y.1) j + eta :=
            add_le_add le_rfl (hbound y.1 y.2)
    exact le_trans
      (iInf_le
        (fun y : {y // y ∈ sample} =>
          matrix_vector_bound A (fun i => d i x y.1) j +
            d j (proxy.func y.1) (label y.1) +
            readout_error y.1) y)
      hterm
  simpa [readout_corrected_anchor_distance, weighted_anchor_distance, ENNReal.iInf_add]
    using hle

/--
OET anchor: h-5f713424d00a09e9
**命题（逐点读取误差下的经验上界，真实标签零读取误差形式）**
Using the true target values as labels and zero readout error recovers the
empirical pointwise upper bound with the empirical residual certificate.
-/
theorem readout_true_label_zero_error_recovers_empirical_upper
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot) (U V : Set X)
    (sample : I → Set X)
    (Lp Lstar : I → I → ENNReal) (eps : I → ENNReal) (j : I)
    (hU : U ⊆ V)
    (hsample : sample j ⊆ U)
    (hLp : IsLipMatrix d proxy U Lp)
    (hLstar : TargetLipEnvelopeCertificate d target V Lstar)
    (hres : EmpiricalResidualBound d target proxy sample eps)
    (hj : j ∈ evaluable_components sample) :
    ∀ x ∈ U,
      d j (proxy.func x) (target.func x) ≤
        weighted_anchor_distance d (fun i j => Lp i j + Lstar i j)
          j x (sample j) + eps j := by
  intro x hx
  have hread :
      d j (proxy.func x) (target.func x) ≤
        readout_corrected_anchor_distance d proxy
          (fun i j => Lp i j + Lstar i j) j target.func
          (fun _ => 0) x (sample j) := by
    exact readout_error_empirical_upper_point d hd target proxy U V (sample j)
      Lp Lstar target.func (fun _ => 0) j hU hsample hLp hLstar.lip_matrix
      (fun y _hy => by simp [(hd j).dist_self]) x hx
  have hcorrected :
      readout_corrected_anchor_distance d proxy
          (fun i j => Lp i j + Lstar i j) j target.func
          (fun _ => 0) x (sample j) ≤
        weighted_anchor_distance d (fun i j => Lp i j + Lstar i j)
          j x (sample j) + eps j := by
    exact readout_corrected_anchor_distance_le_weighted_anchor_distance_add
      d proxy (fun i j => Lp i j + Lstar i j) j target.func
      (fun _ => 0) x (sample j) (eps j)
      (fun y hy => by
        simpa using hres.sample_error j hj y hy)
  exact le_trans hread hcorrected

/--
OET anchor: h-d2ea49b322fbe56f
**命题（经验正偏差下界证书，代理 co-Lip 形式）**
If the proxy co-Lip lower bound exceeds the target-side Lip drift, sample
residual, and claimed radius, then the target-proxy deviation is larger than
that radius.
-/
theorem empirical_positive_deviation_lower_proxy_colip
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot) (U V : Set X)
    (Kp Lstar : I → I → ENNReal) (eps a : ENNReal) (j : I)
    (hU : U ⊆ V)
    (hKp : IsCoLipMatrix d proxy U Kp)
    (hLstar : IsLipMatrix d target V Lstar)
    {x xs : X}
    (hx : x ∈ U) (hxs : xs ∈ U)
    (hres : d j (proxy.func xs) (target.func xs) ≤ eps)
    (hgap :
      a + matrix_vector_bound Lstar (fun i => d i x xs) j + eps <
        matrix_vector_bound Kp (fun i => d i x xs) j) :
    a < d j (proxy.func x) (target.func x) := by
  by_contra hnot
  have hdev : d j (proxy.func x) (target.func x) ≤ a := le_of_not_gt hnot
  have hxV : x ∈ V := hU hx
  have hxsV : xs ∈ V := hU hxs
  have htarget :
      d j (target.func x) (target.func xs) ≤
        matrix_vector_bound Lstar (fun i => d i x xs) j := by
    simpa [matrix_vector_bound] using hLstar.2 x hxV xs hxsV j
  have htarget_symm :
      d j (target.func xs) (target.func x) ≤
        matrix_vector_bound Lstar (fun i => d i x xs) j := by
    simpa [(hd j).symm (target.func xs) (target.func x)] using htarget
  have hres_symm : d j (target.func xs) (proxy.func xs) ≤ eps := by
    simpa [(hd j).symm (target.func xs) (proxy.func xs)] using hres
  have htri₁ :=
    (hd j).triangle (proxy.func x) (target.func x) (proxy.func xs)
  have htri₂ :=
    (hd j).triangle (target.func x) (target.func xs) (proxy.func xs)
  have htarget_to_proxy :
      d j (target.func x) (proxy.func xs) ≤
        matrix_vector_bound Lstar (fun i => d i x xs) j + eps :=
    le_trans htri₂ (add_le_add htarget hres_symm)
  have hproxy_upper :
      d j (proxy.func x) (proxy.func xs) ≤
        a + matrix_vector_bound Lstar (fun i => d i x xs) j + eps := by
    calc
      d j (proxy.func x) (proxy.func xs)
          ≤ d j (proxy.func x) (target.func x) +
              d j (target.func x) (proxy.func xs) := htri₁
      _ ≤ a + (matrix_vector_bound Lstar (fun i => d i x xs) j + eps) :=
          add_le_add hdev htarget_to_proxy
      _ = a + matrix_vector_bound Lstar (fun i => d i x xs) j + eps := by
          simp [add_assoc]
  have hco :
      matrix_vector_bound Kp (fun i => d i x xs) j ≤
        d j (proxy.func x) (proxy.func xs) :=
    hKp.2.2 x hx xs hxs j
  exact not_lt_of_ge (le_trans hco hproxy_upper) hgap

/--
OET anchor: h-d2ea49b322fbe56f
**命题（经验正偏差下界证书，代理 co-Lip 可评估分量形式）**
The proxy co-Lip lower certificate specialized to an evaluable component and
a componentwise empirical residual certificate.
-/
theorem empirical_positive_deviation_lower_proxy_colip_from_residual_certificate
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot) (U V : Set X)
    (sample : I → Set X)
    (Kp Lstar : I → I → ENNReal) (eps : I → ENNReal) (a : ENNReal) (j : I)
    (hU : U ⊆ V)
    (hsample : sample j ⊆ U)
    (hKp : IsCoLipMatrix d proxy U Kp)
    (hLstar : TargetLipEnvelopeCertificate d target V Lstar)
    (hres : EmpiricalResidualBound d target proxy sample eps)
    (hj : j ∈ evaluable_components sample)
    {x xs : X}
    (hx : x ∈ U) (hxs : xs ∈ sample j)
    (hgap :
      a + matrix_vector_bound Lstar (fun i => d i x xs) j + eps j <
        matrix_vector_bound Kp (fun i => d i x xs) j) :
    a < d j (proxy.func x) (target.func x) := by
  exact empirical_positive_deviation_lower_proxy_colip d hd target proxy U V
    Kp Lstar (eps j) a j hU hKp hLstar.lip_matrix hx (hsample hxs)
    (hres.sample_error j hj xs hxs) hgap

/--
OET anchor: h-d2ea49b322fbe56f
**命题（经验正偏差下界证书）**
Text-faithful form retaining that the claimed lower radius is finite.
-/
theorem empirical_positive_deviation_lower_proxy_colip_text
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot) (U V : Set X)
    (sample : I → Set X)
    (Kp Lstar : I → I → ENNReal) (eps : I → ENNReal) (a : ENNReal) (j : I)
    (ha_finite : finite_ennreal a)
    (hU : U ⊆ V)
    (hsample : sample j ⊆ U)
    (hKp : IsCoLipMatrix d proxy U Kp)
    (hLstar : TargetLipEnvelopeCertificate d target V Lstar)
    (hres : EmpiricalResidualBound d target proxy sample eps)
    (hj : j ∈ evaluable_components sample)
    {x xs : X}
    (hx : x ∈ U) (hxs : xs ∈ sample j)
    (hgap :
      a + matrix_vector_bound Lstar (fun i => d i x xs) j + eps j <
        matrix_vector_bound Kp (fun i => d i x xs) j) :
    a < d j (proxy.func x) (target.func x) := by
  have _ := ha_finite
  exact empirical_positive_deviation_lower_proxy_colip_from_residual_certificate
    d hd target proxy U V sample Kp Lstar eps a j hU hsample hKp hLstar
    hres hj hx hxs hgap

/--
OET anchor: h-d2ea49b322fbe56f
**命题（经验正偏差下界证书，目标 co-Lip 形式）**
The symmetric lower certificate using a target-side co-Lip lower bound and a
proxy-side Lip upper bound.
-/
theorem empirical_positive_deviation_lower_target_colip
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot) (U V : Set X)
    (Kstar Lp : I → I → ENNReal) (eps a : ENNReal) (j : I)
    (hU : U ⊆ V)
    (hKstar : IsCoLipMatrix d target V Kstar)
    (hLp : IsLipMatrix d proxy U Lp)
    {x xs : X}
    (hx : x ∈ U) (hxs : xs ∈ U)
    (hres : d j (proxy.func xs) (target.func xs) ≤ eps)
    (hgap :
      a + matrix_vector_bound Lp (fun i => d i x xs) j + eps <
        matrix_vector_bound Kstar (fun i => d i x xs) j) :
    a < d j (proxy.func x) (target.func x) := by
  by_contra hnot
  have hdev : d j (proxy.func x) (target.func x) ≤ a := le_of_not_gt hnot
  have hxV : x ∈ V := hU hx
  have hxsV : xs ∈ V := hU hxs
  have hproxy :
      d j (proxy.func x) (proxy.func xs) ≤
        matrix_vector_bound Lp (fun i => d i x xs) j := by
    simpa [matrix_vector_bound] using hLp.2 x hx xs hxs j
  have hdev_symm : d j (target.func x) (proxy.func x) ≤ a := by
    simpa [(hd j).symm (target.func x) (proxy.func x)] using hdev
  have htri₁ :=
    (hd j).triangle (target.func x) (proxy.func x) (target.func xs)
  have htri₂ :=
    (hd j).triangle (proxy.func x) (proxy.func xs) (target.func xs)
  have hproxy_to_target :
      d j (proxy.func x) (target.func xs) ≤
        matrix_vector_bound Lp (fun i => d i x xs) j + eps :=
    le_trans htri₂ (add_le_add hproxy hres)
  have htarget_upper :
      d j (target.func x) (target.func xs) ≤
        a + matrix_vector_bound Lp (fun i => d i x xs) j + eps := by
    calc
      d j (target.func x) (target.func xs)
          ≤ d j (target.func x) (proxy.func x) +
              d j (proxy.func x) (target.func xs) := htri₁
      _ ≤ a + (matrix_vector_bound Lp (fun i => d i x xs) j + eps) :=
          add_le_add hdev_symm hproxy_to_target
      _ = a + matrix_vector_bound Lp (fun i => d i x xs) j + eps := by
          simp [add_assoc]
  have hco :
      matrix_vector_bound Kstar (fun i => d i x xs) j ≤
        d j (target.func x) (target.func xs) :=
    hKstar.2.2 x hxV xs hxsV j
  exact not_lt_of_ge (le_trans hco htarget_upper) hgap

/--
OET anchor: h-d2ea49b322fbe56f
**命题（经验正偏差下界证书，目标 co-Lip 可评估分量形式）**
The target co-Lip lower certificate specialized to an evaluable component and
a componentwise empirical residual certificate.
-/
theorem empirical_positive_deviation_lower_target_colip_from_residual_certificate
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot) (U V : Set X)
    (sample : I → Set X)
    (Kstar Lp : I → I → ENNReal) (eps : I → ENNReal) (a : ENNReal) (j : I)
    (hU : U ⊆ V)
    (hsample : sample j ⊆ U)
    (hKstar : TargetCoLipLowerCertificate d target V Kstar)
    (hLp : IsLipMatrix d proxy U Lp)
    (hres : EmpiricalResidualBound d target proxy sample eps)
    (hj : j ∈ evaluable_components sample)
    {x xs : X}
    (hx : x ∈ U) (hxs : xs ∈ sample j)
    (hgap :
      a + matrix_vector_bound Lp (fun i => d i x xs) j + eps j <
        matrix_vector_bound Kstar (fun i => d i x xs) j) :
    a < d j (proxy.func x) (target.func x) := by
  exact empirical_positive_deviation_lower_target_colip d hd target proxy U V
    Kstar Lp (eps j) a j hU hKstar.colip_matrix hLp hx (hsample hxs)
    (hres.sample_error j hj xs hxs) hgap

/--
OET anchor: h-d2ea49b322fbe56f
**命题（经验正偏差下界证书，目标 co-Lip 正文前提形式）**
Text-faithful form retaining that the claimed lower radius is finite.
-/
theorem empirical_positive_deviation_lower_target_colip_text
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot) (U V : Set X)
    (sample : I → Set X)
    (Kstar Lp : I → I → ENNReal) (eps : I → ENNReal) (a : ENNReal) (j : I)
    (ha_finite : finite_ennreal a)
    (hU : U ⊆ V)
    (hsample : sample j ⊆ U)
    (hKstar : TargetCoLipLowerCertificate d target V Kstar)
    (hLp : IsLipMatrix d proxy U Lp)
    (hres : EmpiricalResidualBound d target proxy sample eps)
    (hj : j ∈ evaluable_components sample)
    {x xs : X}
    (hx : x ∈ U) (hxs : xs ∈ sample j)
    (hgap :
      a + matrix_vector_bound Lp (fun i => d i x xs) j + eps j <
        matrix_vector_bound Kstar (fun i => d i x xs) j) :
    a < d j (proxy.func x) (target.func x) := by
  have _ := ha_finite
  exact empirical_positive_deviation_lower_target_colip_from_residual_certificate
    d hd target proxy U V sample Kstar Lp eps a j hU hsample hKstar hLp
    hres hj hx hxs hgap

/--
OET anchor: h-bb48a0ae4916198d
**命题（观测目标贴合的真实偏差下界）**
If a proxy fits an observed target within a finite tolerance at a point, while
the observed target is farther than that tolerance plus a finite claimed radius
from the true target at the same point and component, then the proxy is farther
than the claimed radius from the true target.
-/
theorem observed_target_fitting_true_deviation_lower_bound
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (observed target proxy : Operator X bot) (V : Set X)
    (x : X) (j : I) (eps a : ENNReal)
    (heps : eps ≠ ⊤) (ha : a ≠ ⊤)
    (hx : x ∈ V)
    (hV : V ⊆ dom observed ∩ dom target ∩ dom proxy)
    (hfit : d j (proxy.func x) (observed.func x) ≤ eps)
    (hgap : a + eps < d j (observed.func x) (target.func x)) :
    a < d j (proxy.func x) (target.func x) := by
  have _ := heps
  have _ := ha
  have _ := hV hx
  by_contra hnot
  have hproxy_true : d j (proxy.func x) (target.func x) ≤ a :=
    le_of_not_gt hnot
  have hobs_proxy : d j (observed.func x) (proxy.func x) ≤ eps := by
    simpa [(hd j).symm (observed.func x) (proxy.func x)] using hfit
  have htri :=
    (hd j).triangle (observed.func x) (proxy.func x) (target.func x)
  have hle : d j (observed.func x) (target.func x) ≤ eps + a :=
    le_trans htri (add_le_add hobs_proxy hproxy_true)
  have hle' : d j (observed.func x) (target.func x) ≤ a + eps := by
    simpa [add_comm, add_left_comm, add_assoc] using hle
  exact not_lt_of_ge hle' hgap

/--
OET anchor: h-bb48a0ae4916198d
**命题（观测目标贴合的真实偏差下界，精确贴合形式）**
The exact-fitting specialization of the observed-target lower certificate.
-/
theorem observed_target_exact_fitting_true_deviation_lower_bound
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (observed target proxy : Operator X bot) (V : Set X)
    (x : X) (j : I) (a : ENNReal)
    (ha : a ≠ ⊤)
    (hx : x ∈ V)
    (hV : V ⊆ dom observed ∩ dom target ∩ dom proxy)
    (hfit : d j (proxy.func x) (observed.func x) = 0)
    (hgap : a < d j (observed.func x) (target.func x)) :
    a < d j (proxy.func x) (target.func x) := by
  exact observed_target_fitting_true_deviation_lower_bound
    d hd observed target proxy V x j 0 a (by simp) ha hx hV
    (le_of_eq hfit) (by simpa using hgap)

/--
OET anchor: h-885c9167af3ee3ef
**命题（Lip 包络的采样必要条件）**
A target Lip envelope must satisfy its row inequality on every sampled pair.
-/
theorem target_lip_sample_necessary
    (d : I → X → X → ENNReal)
    (target : Operator X bot) (V sample : Set X)
    (Lstar : I → I → ENNReal) (j : I)
    (hsub : sample ⊆ V)
    (hLstar : IsLipMatrix d target V Lstar)
    {xs xt : X} (hxs : xs ∈ sample) (hxt : xt ∈ sample) :
    d j (target.func xs) (target.func xt) ≤
      matrix_vector_bound Lstar (fun i => d i xs xt) j := by
  exact hLstar.2 xs (hsub hxs) xt (hsub hxt) j

/--
OET anchor: h-885c9167af3ee3ef
**命题（Lip 包络的采样必要条件，可评估分量形式）**
The sampled Lip necessary condition specialized to an evaluable component and
a target Lip envelope certificate.
-/
theorem target_lip_sample_necessary_from_certificate
    (d : I → X → X → ENNReal)
    (target : Operator X bot) (V : Set X)
    (sample : I → Set X)
    (Lstar : I → I → ENNReal) (j : I)
    (hsub : sample j ⊆ V)
    (hLstar : TargetLipEnvelopeCertificate d target V Lstar)
    (hj : j ∈ evaluable_components sample)
    {xs xt : X} (hxs : xs ∈ sample j) (hxt : xt ∈ sample j) :
    d j (target.func xs) (target.func xt) ≤
      matrix_vector_bound Lstar (fun i => d i xs xt) j := by
  have _ := hj
  exact target_lip_sample_necessary d target V (sample j) Lstar j hsub
    hLstar.lip_matrix hxs hxt

/--
OET anchor: h-885c9167af3ee3ef
**命题（Lip 包络的采样必要条件，代理分离形式）**
If sampled proxy outputs are separated beyond two residual tolerances and a
finite radius, then the target Lip row sum must exceed that radius.
-/
theorem target_lip_sample_necessary_from_proxy_gap
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot) (V sample : Set X)
    (Lstar : I → I → ENNReal) (eps a : ENNReal) (j : I)
    (hsub : sample ⊆ V)
    (hLstar : IsLipMatrix d target V Lstar)
    {xs xt : X} (hxs : xs ∈ sample) (hxt : xt ∈ sample)
    (hres_s : d j (proxy.func xs) (target.func xs) ≤ eps)
    (hres_t : d j (proxy.func xt) (target.func xt) ≤ eps)
    (hgap : a + (eps + eps) < d j (proxy.func xs) (proxy.func xt)) :
    a < matrix_vector_bound Lstar (fun i => d i xs xt) j := by
  by_contra hnot
  have hrow : matrix_vector_bound Lstar (fun i => d i xs xt) j ≤ a :=
    le_of_not_gt hnot
  have htarget :=
    target_lip_sample_necessary d target V sample Lstar j hsub hLstar hxs hxt
  have hres_t_symm : d j (target.func xt) (proxy.func xt) ≤ eps := by
    simpa [(hd j).symm (target.func xt) (proxy.func xt)] using hres_t
  have htri₁ :=
    (hd j).triangle (proxy.func xs) (target.func xs) (proxy.func xt)
  have htri₂ :=
    (hd j).triangle (target.func xs) (target.func xt) (proxy.func xt)
  have htarget_to_proxy :
      d j (target.func xs) (proxy.func xt) ≤
        matrix_vector_bound Lstar (fun i => d i xs xt) j + eps :=
    le_trans htri₂ (add_le_add htarget hres_t_symm)
  have hproxy_upper :
      d j (proxy.func xs) (proxy.func xt) ≤ a + (eps + eps) := by
    calc
      d j (proxy.func xs) (proxy.func xt)
          ≤ d j (proxy.func xs) (target.func xs) +
              d j (target.func xs) (proxy.func xt) := htri₁
      _ ≤ eps + (matrix_vector_bound Lstar (fun i => d i xs xt) j + eps) :=
          add_le_add hres_s htarget_to_proxy
      _ ≤ eps + (a + eps) := add_le_add le_rfl (add_le_add hrow le_rfl)
      _ = a + (eps + eps) := by
          simp [add_comm, add_left_comm]
  exact not_lt_of_ge hproxy_upper hgap

/--
OET anchor: h-885c9167af3ee3ef
**命题（Lip 包络的采样必要条件，代理分离可评估分量形式）**
The proxy-separation test specialized to an evaluable component and an
empirical residual certificate.
-/
theorem target_lip_sample_necessary_from_proxy_gap_residual_certificate
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot) (V : Set X)
    (sample : I → Set X)
    (Lstar : I → I → ENNReal) (eps : I → ENNReal) (a : ENNReal) (j : I)
    (hsub : sample j ⊆ V)
    (hLstar : TargetLipEnvelopeCertificate d target V Lstar)
    (hres : EmpiricalResidualBound d target proxy sample eps)
    (hj : j ∈ evaluable_components sample)
    {xs xt : X} (hxs : xs ∈ sample j) (hxt : xt ∈ sample j)
    (hgap : a + (eps j + eps j) < d j (proxy.func xs) (proxy.func xt)) :
    a < matrix_vector_bound Lstar (fun i => d i xs xt) j := by
  exact target_lip_sample_necessary_from_proxy_gap d hd target proxy V (sample j)
    Lstar (eps j) a j hsub hLstar.lip_matrix hxs hxt
    (hres.sample_error j hj xs hxs) (hres.sample_error j hj xt hxt) hgap

/--
OET anchor: h-885c9167af3ee3ef
**命题（Lip 包络的采样必要条件，代理分离正文前提形式）**
Text-faithful form retaining that the tested lower radius is finite.
-/
theorem target_lip_sample_necessary_from_proxy_gap_text
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot) (V : Set X)
    (sample : I → Set X)
    (Lstar : I → I → ENNReal) (eps : I → ENNReal) (a : ENNReal) (j : I)
    (ha_finite : finite_ennreal a)
    (hsub : sample j ⊆ V)
    (hLstar : TargetLipEnvelopeCertificate d target V Lstar)
    (hres : EmpiricalResidualBound d target proxy sample eps)
    (hj : j ∈ evaluable_components sample)
    {xs xt : X} (hxs : xs ∈ sample j) (hxt : xt ∈ sample j)
    (hgap : a + (eps j + eps j) < d j (proxy.func xs) (proxy.func xt)) :
    a < matrix_vector_bound Lstar (fun i => d i xs xt) j := by
  have _ := ha_finite
  exact target_lip_sample_necessary_from_proxy_gap_residual_certificate
    d hd target proxy V sample Lstar eps a j hsub hLstar hres hj
    hxs hxt hgap

/--
OET anchor: h-9b0a38625719c139
**命题（co-Lip 下界的采样必要条件）**
A target co-Lip lower certificate must be no larger than the sampled target
output distance, hence no larger than the sampled proxy distance plus two
residual tolerances.
-/
theorem target_colip_sample_necessary
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot) (V sample : Set X)
    (Kstar : I → I → ENNReal) (eps : ENNReal) (j : I)
    (hsub : sample ⊆ V)
    (hKstar : IsCoLipMatrix d target V Kstar)
    {xs xt : X} (hxs : xs ∈ sample) (hxt : xt ∈ sample)
    (hres_s : d j (proxy.func xs) (target.func xs) ≤ eps)
    (hres_t : d j (proxy.func xt) (target.func xt) ≤ eps) :
    matrix_vector_bound Kstar (fun i => d i xs xt) j ≤
      d j (proxy.func xs) (proxy.func xt) + (eps + eps) := by
  have hco :
      matrix_vector_bound Kstar (fun i => d i xs xt) j ≤
        d j (target.func xs) (target.func xt) :=
    hKstar.2.2 xs (hsub hxs) xt (hsub hxt) j
  have hres_s_symm : d j (target.func xs) (proxy.func xs) ≤ eps := by
    simpa [(hd j).symm (target.func xs) (proxy.func xs)] using hres_s
  have htri₁ :=
    (hd j).triangle (target.func xs) (proxy.func xs) (target.func xt)
  have htri₂ :=
    (hd j).triangle (proxy.func xs) (proxy.func xt) (target.func xt)
  have hproxy_to_target :
      d j (proxy.func xs) (target.func xt) ≤
        d j (proxy.func xs) (proxy.func xt) + eps :=
    le_trans htri₂ (add_le_add le_rfl hres_t)
  have htarget_upper :
      d j (target.func xs) (target.func xt) ≤
        d j (proxy.func xs) (proxy.func xt) + (eps + eps) := by
    calc
      d j (target.func xs) (target.func xt)
          ≤ d j (target.func xs) (proxy.func xs) +
              d j (proxy.func xs) (target.func xt) := htri₁
      _ ≤ eps + (d j (proxy.func xs) (proxy.func xt) + eps) :=
          add_le_add hres_s_symm hproxy_to_target
      _ = d j (proxy.func xs) (proxy.func xt) + (eps + eps) := by
          simp [add_comm, add_assoc]
  exact le_trans hco htarget_upper

/--
OET anchor: h-9b0a38625719c139
**命题（co-Lip 下界的采样必要条件，可评估分量形式）**
The sampled co-Lip necessary condition specialized to an evaluable component,
a target co-Lip certificate, and an empirical residual certificate.
-/
theorem target_colip_sample_necessary_from_residual_certificate
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot) (V : Set X)
    (sample : I → Set X)
    (Kstar : I → I → ENNReal) (eps : I → ENNReal) (j : I)
    (hsub : sample j ⊆ V)
    (hKstar : TargetCoLipLowerCertificate d target V Kstar)
    (hres : EmpiricalResidualBound d target proxy sample eps)
    (hj : j ∈ evaluable_components sample)
    {xs xt : X} (hxs : xs ∈ sample j) (hxt : xt ∈ sample j) :
    matrix_vector_bound Kstar (fun i => d i xs xt) j ≤
      d j (proxy.func xs) (proxy.func xt) + (eps j + eps j) := by
  exact target_colip_sample_necessary d hd target proxy V (sample j)
    Kstar (eps j) j hsub hKstar.colip_matrix hxs hxt
    (hres.sample_error j hj xs hxs) (hres.sample_error j hj xt hxt)

end formal_oet.vol_03.ch_12_residuals_and_substitution
