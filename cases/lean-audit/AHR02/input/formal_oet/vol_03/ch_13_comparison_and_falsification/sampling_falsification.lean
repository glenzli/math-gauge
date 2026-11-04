import formal_oet.vol_03.ch_13_comparison_and_falsification.candidate_family
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace formal_oet.vol_03.ch_13_comparison_and_falsification

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open formal_oet.vol_01.ch_04_operator_chain_calculus
open formal_oet.vol_02.ch_07_fitting_foundations
open formal_oet.vol_03.ch_12_residuals_and_substitution

open scoped BigOperators

variable {X I : Type} {bot : X} [Fintype I]

/--
OET anchor: h-a533a584d60b7e68
**定义（留出分解）**
A componentwise training/validation split of a sample family.
-/
structure HoldoutSplit
    (sample train validation : I → Set X) (J : Set I) : Prop where
  train_subset : ∀ j : I, j ∈ J → train j ⊆ sample j
  validation_subset : ∀ j : I, j ∈ J → validation j ⊆ sample j
  disjoint : ∀ j : I, j ∈ J → Disjoint (train j) (validation j)
  union_eq : ∀ j : I, j ∈ J → sample j = train j ∪ validation j

/--
OET anchor: h-42f44a6b9ad2aa3d
**命题（上界留出证伪，预测上界）**
The training certificate predicts the target-proxy residual at every validation
point that lies in the working domain.
-/
theorem upper_holdout_bound_from_training_certificate
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot) (U V : Set X)
    (train validation : I → Set X)
    (Lp Lstar : I → I → ENNReal) (eps_tr : I → ENNReal) (j : I)
    (hU : U ⊆ V)
    (htrain : train j ⊆ U)
    (hLp : IsLipMatrix d proxy U Lp)
    (hLstar : TargetLipEnvelopeCertificate d target V Lstar)
    (hres : EmpiricalResidualBound d target proxy train eps_tr)
    (hj : j ∈ evaluable_components train)
    {xv : X} (hxv : xv ∈ validation j ∩ U) :
    d j (proxy.func xv) (target.func xv) ≤
      weighted_anchor_distance d (fun i j => Lp i j + Lstar i j) j xv (train j) +
        eps_tr j := by
  exact empirical_target_perturbation_upper_point_from_residual_certificate
    d hd target proxy U V train Lp Lstar eps_tr j hU htrain hLp hLstar hres hj
    xv hxv.2

/--
OET anchor: h-42f44a6b9ad2aa3d
**命题（上界留出证伪，正文前提版本）**
The text-level holdout statement retains the sample split, component
membership, and nonempty training sample.
-/
theorem upper_holdout_bound_from_training_certificate_text
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot) (U V : Set X)
    (sample train validation : I → Set X) (J : Set I)
    (Lp Lstar : I → I → ENNReal) (eps_tr : I → ENNReal) (j : I)
    (hsplit : HoldoutSplit sample train validation J)
    (hjJ : j ∈ J)
    (htrain_nonempty : (train j).Nonempty)
    (hU : U ⊆ V)
    (htrain : train j ⊆ U)
    (hLp : IsLipMatrix d proxy U Lp)
    (hLstar : TargetLipEnvelopeCertificate d target V Lstar)
    (hres : EmpiricalResidualBound d target proxy train eps_tr)
    {xv : X} (hxv : xv ∈ validation j ∩ U) :
    d j (proxy.func xv) (target.func xv) ≤
      weighted_anchor_distance d (fun i j => Lp i j + Lstar i j) j xv (train j) +
        eps_tr j := by
  have _ := hsplit
  have _ := hjJ
  have hj : j ∈ evaluable_components train := htrain_nonempty
  exact upper_holdout_bound_from_training_certificate
    d hd target proxy U V train validation Lp Lstar eps_tr j
    hU htrain hLp hLstar hres hj hxv

/--
OET anchor: h-42f44a6b9ad2aa3d
**命题（上界留出证伪，失败集合）**
Validation points whose observed residual is strictly larger than the training
certificate prediction.
-/
def upper_holdout_failure_set
    (d : I → X → X → ENNReal)
    (A : I → I → ENNReal) (target proxy : Operator X bot)
    (U : Set X) (train validation : I → Set X)
    (eps_tr : I → ENNReal) (j : I) : Set X :=
  {x | x ∈ validation j ∩ U ∧
    weighted_anchor_distance d A j x (train j) + eps_tr j <
      d j (proxy.func x) (target.func x)}

/--
OET anchor: h-42f44a6b9ad2aa3d
**命题（上界留出证伪）**
A holdout failure point contradicts the asserted training upper bound at that
point.
-/
theorem upper_holdout_failure_contradicts_bound
    (d : I → X → X → ENNReal)
    (A : I → I → ENNReal) (target proxy : Operator X bot)
    (U : Set X) (train validation : I → Set X)
    (eps_tr : I → ENNReal) (j : I) {x : X}
    (hx : x ∈ upper_holdout_failure_set d A target proxy U train validation eps_tr j)
    (hbound :
      d j (proxy.func x) (target.func x) ≤
        weighted_anchor_distance d A j x (train j) + eps_tr j) :
    False :=
  not_lt_of_ge hbound hx.2

/--
OET anchor: h-f2005481e35abfad
**命题（下界留出证伪，代理 co-Lip 预测）**
The lower certificate at `h-d2ea49b322fbe56f` predicts a strict positive
deviation at a
validation point.
-/
theorem lower_holdout_proxy_colip_prediction
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot) (U V : Set X)
    (train : I → Set X)
    (Kp Lstar : I → I → ENNReal) (eps_tr : I → ENNReal)
    (a : ENNReal) (j : I)
    (hU : U ⊆ V)
    (htrain : train j ⊆ U)
    (hKp : IsCoLipMatrix d proxy U Kp)
    (hLstar : TargetLipEnvelopeCertificate d target V Lstar)
    (hres : EmpiricalResidualBound d target proxy train eps_tr)
    (hj : j ∈ evaluable_components train)
    {xv xs : X}
    (hxv : xv ∈ U) (hxs : xs ∈ train j)
    (ha_finite : finite_ennreal a)
    (hgap :
      a + matrix_vector_bound Lstar (fun i => d i xv xs) j + eps_tr j <
        matrix_vector_bound Kp (fun i => d i xv xs) j) :
    a < d j (proxy.func xv) (target.func xv) := by
  have _ := ha_finite
  exact empirical_positive_deviation_lower_proxy_colip_from_residual_certificate
    d hd target proxy U V train Kp Lstar eps_tr a j hU htrain hKp hLstar
    hres hj hxv hxs hgap

/--
OET anchor: h-f2005481e35abfad
**命题（下界留出证伪，目标 co-Lip 预测）**
The target-side co-Lip variant of the lower holdout prediction.
-/
theorem lower_holdout_target_colip_prediction
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot) (U V : Set X)
    (train : I → Set X)
    (Kstar Lp : I → I → ENNReal) (eps_tr : I → ENNReal)
    (a : ENNReal) (j : I)
    (hU : U ⊆ V)
    (htrain : train j ⊆ U)
    (hKstar : TargetCoLipLowerCertificate d target V Kstar)
    (hLp : IsLipMatrix d proxy U Lp)
    (hres : EmpiricalResidualBound d target proxy train eps_tr)
    (hj : j ∈ evaluable_components train)
    {xv xs : X}
    (hxv : xv ∈ U) (hxs : xs ∈ train j)
    (ha_finite : finite_ennreal a)
    (hgap :
      a + matrix_vector_bound Lp (fun i => d i xv xs) j + eps_tr j <
        matrix_vector_bound Kstar (fun i => d i xv xs) j) :
    a < d j (proxy.func xv) (target.func xv) := by
  have _ := ha_finite
  exact empirical_positive_deviation_lower_target_colip_from_residual_certificate
    d hd target proxy U V train Kstar Lp eps_tr a j hU htrain hKstar hLp
    hres hj hxv hxs hgap

/--
OET anchor: h-f2005481e35abfad
**命题（下界留出证伪）**
A validation value below the claimed lower threshold contradicts a lower
certificate prediction.
-/
theorem lower_holdout_failure_contradicts_prediction
    (d : I → X → X → ENNReal)
    (target proxy : Operator X bot) (a : ENNReal) (j : I) (xv : X)
    (hprediction : a < d j (proxy.func xv) (target.func xv))
    (hactual : d j (proxy.func xv) (target.func xv) ≤ a) :
    False :=
  not_lt_of_ge hactual hprediction

/--
OET anchor: h-f2005481e35abfad
**命题（下界留出证伪，代理 co-Lip 正文版本）**
All proxy-side lower-certificate premises together with a validation value at
or below the threshold are inconsistent.
-/
theorem lower_holdout_proxy_colip_falsification_text
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot) (U V : Set X)
    (sample train validation : I → Set X) (J : Set I)
    (Kp Lstar : I → I → ENNReal) (eps_tr : I → ENNReal)
    (a : ENNReal) (j : I)
    (hsplit : HoldoutSplit sample train validation J)
    (hjJ : j ∈ J)
    (hU : U ⊆ V)
    (htrain : train j ⊆ U)
    (hKp : IsCoLipMatrix d proxy U Kp)
    (hLstar : TargetLipEnvelopeCertificate d target V Lstar)
    (hres : EmpiricalResidualBound d target proxy train eps_tr)
    (htrain_nonempty : (train j).Nonempty)
    {xv xs : X}
    (hxv : xv ∈ validation j ∩ U) (hxs : xs ∈ train j)
    (ha_finite : finite_ennreal a)
    (hgap :
      a + matrix_vector_bound Lstar (fun i => d i xv xs) j + eps_tr j <
        matrix_vector_bound Kp (fun i => d i xv xs) j)
    (hactual : d j (proxy.func xv) (target.func xv) ≤ a) :
    False := by
  have _ := hsplit
  have _ := hjJ
  have hj : j ∈ evaluable_components train := htrain_nonempty
  exact lower_holdout_failure_contradicts_prediction d target proxy a j xv
    (lower_holdout_proxy_colip_prediction d hd target proxy U V train
      Kp Lstar eps_tr a j hU htrain hKp hLstar hres hj
      hxv.2 hxs ha_finite hgap)
    hactual

/--
OET anchor: h-f2005481e35abfad
**命题（下界留出证伪，目标 co-Lip 正文版本）**
The target-side co-Lip specialization retains the same holdout context.
-/
theorem lower_holdout_target_colip_falsification_text
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot) (U V : Set X)
    (sample train validation : I → Set X) (J : Set I)
    (Kstar Lp : I → I → ENNReal) (eps_tr : I → ENNReal)
    (a : ENNReal) (j : I)
    (hsplit : HoldoutSplit sample train validation J)
    (hjJ : j ∈ J)
    (hU : U ⊆ V)
    (htrain : train j ⊆ U)
    (hKstar : TargetCoLipLowerCertificate d target V Kstar)
    (hLp : IsLipMatrix d proxy U Lp)
    (hres : EmpiricalResidualBound d target proxy train eps_tr)
    (htrain_nonempty : (train j).Nonempty)
    {xv xs : X}
    (hxv : xv ∈ validation j ∩ U) (hxs : xs ∈ train j)
    (ha_finite : finite_ennreal a)
    (hgap :
      a + matrix_vector_bound Lp (fun i => d i xv xs) j + eps_tr j <
        matrix_vector_bound Kstar (fun i => d i xv xs) j)
    (hactual : d j (proxy.func xv) (target.func xv) ≤ a) :
    False := by
  have _ := hsplit
  have _ := hjJ
  have hj : j ∈ evaluable_components train := htrain_nonempty
  exact lower_holdout_failure_contradicts_prediction d target proxy a j xv
    (lower_holdout_target_colip_prediction d hd target proxy U V train
      Kstar Lp eps_tr a j hU htrain hKstar hLp hres hj
      hxv.2 hxs ha_finite hgap)
    hactual

end formal_oet.vol_03.ch_13_comparison_and_falsification
