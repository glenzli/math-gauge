import formal_oet.vol_03.ch_14_empirical_network_fitting.path_sampling
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace formal_oet.vol_03.ch_14_empirical_network_fitting

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open formal_oet.vol_01.ch_04_operator_chain_calculus
open formal_oet.vol_01.ch_05_operator_networks
open formal_oet.vol_02.ch_07_fitting_foundations
open formal_oet.vol_03.ch_12_residuals_and_substitution

open scoped BigOperators

variable {X I V : Type} {bot : X} [Fintype I]

/--
OET anchor: h-0056e459b9376864
**定义（路径分量经验保证域）**
The empirical guarantee domain for one component on one proxy path.
-/
def path_component_empirical_guarantee_domain
    (d : I → X → X → ENNReal)
    (A : I → I → ENNReal)
    (N : FiniteOperatorNetwork X bot V) (sample : I → Set X)
    (q : N.ReachablePath) (j : I) (eps tau : ENNReal) : Set X :=
  empirical_component_guarantee_domain d A (N.path_domain q.nodes)
    (path_component_sample N sample q j) j eps tau

/--
OET anchor: h-0056e459b9376864
**定义（路径联合经验保证域）**
The joint empirical guarantee domain on one proxy path.
-/
def path_joint_empirical_guarantee_domain
    (d : I → X → X → ENNReal)
    (A : I → I → ENNReal)
    (N : FiniteOperatorNetwork X bot V) (sample : I → Set X)
    (q : N.ReachablePath) (J : Set I)
    (eps tau : I → ENNReal) : Set X :=
  empirical_joint_guarantee_domain d A (N.path_domain q.nodes)
    (path_sample_family N sample q) J eps tau

/--
OET anchor: h-4b5219aa3a3bbdad
**命题（路径局部经验上界）**
The empirical upper certificate at `h-f16da76e4331b725`, applied to the path
chain, gives the local path upper bound.
-/
theorem path_local_empirical_upper
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target : Operator X bot)
    (N : FiniteOperatorNetwork X bot V) (sample : I → Set X)
    (delta_o : I → ENNReal) (q : N.ReachablePath)
    (Vstar : Set X) (Lq Lstar : I → I → ENNReal) (j : I)
    (hpathV : N.path_domain q.nodes ⊆ Vstar)
    (hLq : IsLipMatrix d (N.path_chain q.nodes) (N.path_domain q.nodes) Lq)
    (hLstar : TargetLipEnvelopeCertificate d target Vstar Lstar)
    (hj : j ∈ path_evaluable_components N sample q) :
    ∀ x ∈ N.path_domain q.nodes,
      d j ((N.path_chain q.nodes).func x) (target.func x) ≤
        weighted_anchor_distance d (fun i j => Lq i j + Lstar i j)
          j x (path_component_sample N sample q j) +
          path_empirical_residual_upper d target N sample delta_o q j := by
  have hsample :
      path_sample_family N sample q j ⊆ N.path_domain q.nodes :=
    path_component_sample_subset_path_domain N sample q j
  have hres :
      EmpiricalResidualBound d target (N.path_chain q.nodes)
        (path_sample_family N sample q)
        (path_empirical_residual_upper d target N sample delta_o q) := by
    simpa [path_empirical_residual_upper] using
      (empirical_residual_upper_certificate d target (N.path_chain q.nodes)
        (path_sample_family N sample q) delta_o)
  exact empirical_target_perturbation_upper_point_from_residual_certificate
    d hd target (N.path_chain q.nodes) (N.path_domain q.nodes) Vstar
    (path_sample_family N sample q) Lq Lstar
    (path_empirical_residual_upper d target N sample delta_o q) j
    hpathV hsample hLq hLstar hres hj

/--
OET anchor: h-4b5219aa3a3bbdad
**命题（路径局部经验上界，代理表示逐点形式）**
If the network represents the proxy, the path-local empirical upper bound is a
pointwise upper bound for the proxy-target deviation on the path.
-/
theorem proxy_path_local_empirical_upper
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot)
    (N : FiniteOperatorNetwork X bot V) (sample : I → Set X)
    (delta_o : I → ENNReal) (q : N.ReachablePath)
    (Vstar : Set X) (Lq Lstar : I → I → ENNReal) (j : I)
    (hrep : N.represents proxy)
    (hpathV : N.path_domain q.nodes ⊆ Vstar)
    (hLq : IsLipMatrix d (N.path_chain q.nodes) (N.path_domain q.nodes) Lq)
    (hLstar : TargetLipEnvelopeCertificate d target Vstar Lstar)
    (hj : j ∈ path_evaluable_components N sample q) :
    ∀ x ∈ N.path_domain q.nodes,
      d j (proxy.func x) (target.func x) ≤
        weighted_anchor_distance d (fun i j => Lq i j + Lstar i j)
          j x (path_component_sample N sample q j) +
          path_empirical_residual_upper d target N sample delta_o q j := by
  intro x hx
  have hchain :=
    path_chain_eq_represented_proxy_on_path N proxy q hrep hx
  simpa [hchain] using
    (path_local_empirical_upper d hd target N sample delta_o q Vstar Lq Lstar
      j hpathV hLq hLstar hj x hx)

/--
OET anchor: h-4b5219aa3a3bbdad
**命题（路径局部经验上界，保证域形式）**
Membership in a path component guarantee domain gives the requested component
tolerance for the path chain.
-/
theorem path_component_guarantee_error_bound
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target : Operator X bot)
    (N : FiniteOperatorNetwork X bot V) (sample : I → Set X)
    (delta_o : I → ENNReal) (q : N.ReachablePath)
    (Vstar : Set X) (Lq Lstar : I → I → ENNReal)
    (j : I) (tau : ENNReal)
    (hpathV : N.path_domain q.nodes ⊆ Vstar)
    (hLq : IsLipMatrix d (N.path_chain q.nodes) (N.path_domain q.nodes) Lq)
    (hLstar : TargetLipEnvelopeCertificate d target Vstar Lstar)
    (hj : j ∈ path_evaluable_components N sample q)
    {x : X}
    (hx : x ∈ path_component_empirical_guarantee_domain d
      (fun i j => Lq i j + Lstar i j) N sample q j
      (path_empirical_residual_upper d target N sample delta_o q j) tau) :
    d j ((N.path_chain q.nodes).func x) (target.func x) ≤ tau := by
  exact empirical_component_guarantee_error_bound d
    (fun i j => Lq i j + Lstar i j) (N.path_domain q.nodes)
    (path_component_sample N sample q j) target (N.path_chain q.nodes)
    j (path_empirical_residual_upper d target N sample delta_o q j) tau
    (path_local_empirical_upper d hd target N sample delta_o q Vstar Lq Lstar j
      hpathV hLq hLstar hj) hx

/--
OET anchor: h-4b5219aa3a3bbdad
**命题（路径局部经验上界，代理表示形式）**
If the network represents the proxy, the same guarantee applies to the proxy
operator on the path.
-/
theorem proxy_path_component_guarantee_error_bound
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot)
    (N : FiniteOperatorNetwork X bot V) (sample : I → Set X)
    (delta_o : I → ENNReal) (q : N.ReachablePath)
    (Vstar : Set X) (Lq Lstar : I → I → ENNReal)
    (j : I) (tau : ENNReal)
    (hrep : N.represents proxy)
    (hpathV : N.path_domain q.nodes ⊆ Vstar)
    (hLq : IsLipMatrix d (N.path_chain q.nodes) (N.path_domain q.nodes) Lq)
    (hLstar : TargetLipEnvelopeCertificate d target Vstar Lstar)
    (hj : j ∈ path_evaluable_components N sample q)
    {x : X}
    (hx : x ∈ path_component_empirical_guarantee_domain d
      (fun i j => Lq i j + Lstar i j) N sample q j
      (path_empirical_residual_upper d target N sample delta_o q j) tau) :
    d j (proxy.func x) (target.func x) ≤ tau := by
  have hchain :=
    path_chain_eq_represented_proxy_on_path N proxy q hrep hx.1
  simpa [hchain] using
    (path_component_guarantee_error_bound d hd target N sample delta_o q
      Vstar Lq Lstar j tau hpathV hLq hLstar hj hx)

/--
OET anchor: h-4b5219aa3a3bbdad
**命题（路径局部经验上界，代理保证域正文前提形式）**
Text-faithful form retaining that the component threshold is finite.
-/
theorem proxy_path_component_guarantee_error_bound_text
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot)
    (N : FiniteOperatorNetwork X bot V) (sample : I → Set X)
    (delta_o : I → ENNReal) (q : N.ReachablePath)
    (Vstar : Set X) (Lq Lstar : I → I → ENNReal)
    (j : I) (tau : ENNReal)
    (htau_finite : finite_ennreal tau)
    (hrep : N.represents proxy)
    (hpathV : N.path_domain q.nodes ⊆ Vstar)
    (hLq : IsLipMatrix d (N.path_chain q.nodes) (N.path_domain q.nodes) Lq)
    (hLstar : TargetLipEnvelopeCertificate d target Vstar Lstar)
    (hj : j ∈ path_evaluable_components N sample q)
    {x : X}
    (hx : x ∈ path_component_empirical_guarantee_domain d
      (fun i j => Lq i j + Lstar i j) N sample q j
      (path_empirical_residual_upper d target N sample delta_o q j) tau) :
    d j (proxy.func x) (target.func x) ≤ tau := by
  have _ := htau_finite
  exact proxy_path_component_guarantee_error_bound d hd target proxy N sample
    delta_o q Vstar Lq Lstar j tau hrep hpathV hLq hLstar hj hx

/--
OET anchor: h-4b5219aa3a3bbdad
**命题（路径局部经验上界，联合保证域形式）**
Membership in a path joint guarantee domain gives all component tolerances in
the chosen component family.
-/
theorem path_joint_guarantee_error_bound
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target : Operator X bot)
    (N : FiniteOperatorNetwork X bot V) (sample : I → Set X)
    (delta_o : I → ENNReal) (q : N.ReachablePath)
    (Vstar : Set X) (Lq Lstar : I → I → ENNReal)
    (J : Set I) (tau : I → ENNReal)
    (hpathV : N.path_domain q.nodes ⊆ Vstar)
    (hLq : IsLipMatrix d (N.path_chain q.nodes) (N.path_domain q.nodes) Lq)
    (hLstar : TargetLipEnvelopeCertificate d target Vstar Lstar)
    (hJ : J ⊆ path_evaluable_components N sample q)
    {x : X}
    (hx : x ∈ path_joint_empirical_guarantee_domain d
      (fun i j => Lq i j + Lstar i j) N sample q J
      (path_empirical_residual_upper d target N sample delta_o q) tau) :
    ∀ j : I, j ∈ J →
      d j ((N.path_chain q.nodes).func x) (target.func x) ≤ tau j := by
  intro j hj
  exact empirical_joint_guarantee_error_bound d
    (fun i j => Lq i j + Lstar i j) (N.path_domain q.nodes)
    (path_sample_family N sample q) J target (N.path_chain q.nodes)
    (path_empirical_residual_upper d target N sample delta_o q) tau
    (fun x hxU j hj =>
      path_local_empirical_upper d hd target N sample delta_o q Vstar Lq Lstar j
        hpathV hLq hLstar (hJ hj) x hxU)
    hx j hj

/--
OET anchor: h-4b5219aa3a3bbdad
**命题（路径局部经验上界，代理联合保证域形式）**
If the network represents the proxy, membership in a path-local joint
guarantee domain gives all proxy-target component tolerances in `J`.
-/
theorem proxy_path_joint_guarantee_error_bound
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot)
    (N : FiniteOperatorNetwork X bot V) (sample : I → Set X)
    (delta_o : I → ENNReal) (q : N.ReachablePath)
    (Vstar : Set X) (Lq Lstar : I → I → ENNReal)
    (J : Set I) (tau : I → ENNReal)
    (hrep : N.represents proxy)
    (hpathV : N.path_domain q.nodes ⊆ Vstar)
    (hLq : IsLipMatrix d (N.path_chain q.nodes) (N.path_domain q.nodes) Lq)
    (hLstar : TargetLipEnvelopeCertificate d target Vstar Lstar)
    (hJ : J ⊆ path_evaluable_components N sample q)
    {x : X}
    (hx : x ∈ path_joint_empirical_guarantee_domain d
      (fun i j => Lq i j + Lstar i j) N sample q J
      (path_empirical_residual_upper d target N sample delta_o q) tau) :
    ∀ j : I, j ∈ J →
      d j (proxy.func x) (target.func x) ≤ tau j := by
  intro j hj
  have hchain :=
    path_chain_eq_represented_proxy_on_path N proxy q hrep hx.1
  simpa [hchain] using
    (path_joint_guarantee_error_bound d hd target N sample delta_o q
      Vstar Lq Lstar J tau hpathV hLq hLstar hJ hx j hj)

/--
OET anchor: h-4b5219aa3a3bbdad
**命题（路径局部经验上界，代理联合保证域正文前提形式）**
Text-faithful form retaining nonemptiness of the component family and
finiteness of every selected threshold.
-/
theorem proxy_path_joint_guarantee_error_bound_text
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot)
    (N : FiniteOperatorNetwork X bot V) (sample : I → Set X)
    (delta_o : I → ENNReal) (q : N.ReachablePath)
    (Vstar : Set X) (Lq Lstar : I → I → ENNReal)
    (J : Set I) (tau : I → ENNReal)
    (hJ_nonempty : J.Nonempty)
    (htau_finite : ∀ j : I, j ∈ J → finite_ennreal (tau j))
    (hrep : N.represents proxy)
    (hpathV : N.path_domain q.nodes ⊆ Vstar)
    (hLq : IsLipMatrix d (N.path_chain q.nodes) (N.path_domain q.nodes) Lq)
    (hLstar : TargetLipEnvelopeCertificate d target Vstar Lstar)
    (hJ : J ⊆ path_evaluable_components N sample q)
    {x : X}
    (hx : x ∈ path_joint_empirical_guarantee_domain d
      (fun i j => Lq i j + Lstar i j) N sample q J
      (path_empirical_residual_upper d target N sample delta_o q) tau) :
    ∀ j : I, j ∈ J →
      d j (proxy.func x) (target.func x) ≤ tau j := by
  have _ := hJ_nonempty
  have _ := htau_finite
  exact proxy_path_joint_guarantee_error_bound d hd target proxy N sample
    delta_o q Vstar Lq Lstar J tau hrep hpathV hLq hLstar hJ hx

/--
OET anchor: h-4091a4a3834bf02c
**命题（路径局部正偏差下界证书）**
A path co-Lip lower certificate larger than target drift, sample residual and
radius forces a positive target-proxy deviation on that path.
-/
theorem path_positive_deviation_lower_proxy_colip
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target : Operator X bot)
    (N : FiniteOperatorNetwork X bot V) (sample : I → Set X)
    (delta_o : I → ENNReal) (q : N.ReachablePath)
    (Vstar : Set X) (Kq Lstar : I → I → ENNReal)
    (a : ENNReal) (j : I)
    (hpathV : N.path_domain q.nodes ⊆ Vstar)
    (hKq : IsCoLipMatrix d (N.path_chain q.nodes) (N.path_domain q.nodes) Kq)
    (hLstar : TargetLipEnvelopeCertificate d target Vstar Lstar)
    (hj : j ∈ path_evaluable_components N sample q)
    {x xs : X}
    (hx : x ∈ N.path_domain q.nodes)
    (hxs : xs ∈ path_component_sample N sample q j)
    (hgap :
      a + matrix_vector_bound Lstar (fun i => d i x xs) j +
          path_empirical_residual_upper d target N sample delta_o q j <
        matrix_vector_bound Kq (fun i => d i x xs) j) :
    a < d j ((N.path_chain q.nodes).func x) (target.func x) := by
  have hsample :
      path_sample_family N sample q j ⊆ N.path_domain q.nodes :=
    path_component_sample_subset_path_domain N sample q j
  have hres :
      EmpiricalResidualBound d target (N.path_chain q.nodes)
        (path_sample_family N sample q)
        (path_empirical_residual_upper d target N sample delta_o q) := by
    simpa [path_empirical_residual_upper] using
      (empirical_residual_upper_certificate d target (N.path_chain q.nodes)
        (path_sample_family N sample q) delta_o)
  exact empirical_positive_deviation_lower_proxy_colip_from_residual_certificate
    d hd target (N.path_chain q.nodes) (N.path_domain q.nodes) Vstar
    (path_sample_family N sample q) Kq Lstar
    (path_empirical_residual_upper d target N sample delta_o q) a j
    hpathV hsample hKq hLstar hres hj hx hxs hgap

/--
OET anchor: h-4091a4a3834bf02c
**命题（路径局部正偏差下界证书，目标 co-Lip 形式）**
The symmetric path lower certificate using a target co-Lip lower bound and a
path-chain Lip upper bound.
-/
theorem path_positive_deviation_lower_target_colip
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target : Operator X bot)
    (N : FiniteOperatorNetwork X bot V) (sample : I → Set X)
    (delta_o : I → ENNReal) (q : N.ReachablePath)
    (Vstar : Set X) (Kstar Lq : I → I → ENNReal)
    (a : ENNReal) (j : I)
    (hpathV : N.path_domain q.nodes ⊆ Vstar)
    (hKstar : TargetCoLipLowerCertificate d target Vstar Kstar)
    (hLq : IsLipMatrix d (N.path_chain q.nodes) (N.path_domain q.nodes) Lq)
    (hj : j ∈ path_evaluable_components N sample q)
    {x xs : X}
    (hx : x ∈ N.path_domain q.nodes)
    (hxs : xs ∈ path_component_sample N sample q j)
    (hgap :
      a + matrix_vector_bound Lq (fun i => d i x xs) j +
          path_empirical_residual_upper d target N sample delta_o q j <
        matrix_vector_bound Kstar (fun i => d i x xs) j) :
    a < d j ((N.path_chain q.nodes).func x) (target.func x) := by
  have hsample :
      path_sample_family N sample q j ⊆ N.path_domain q.nodes :=
    path_component_sample_subset_path_domain N sample q j
  have hres :
      EmpiricalResidualBound d target (N.path_chain q.nodes)
        (path_sample_family N sample q)
        (path_empirical_residual_upper d target N sample delta_o q) := by
    simpa [path_empirical_residual_upper] using
      (empirical_residual_upper_certificate d target (N.path_chain q.nodes)
        (path_sample_family N sample q) delta_o)
  exact empirical_positive_deviation_lower_target_colip_from_residual_certificate
    d hd target (N.path_chain q.nodes) (N.path_domain q.nodes) Vstar
    (path_sample_family N sample q) Kstar Lq
    (path_empirical_residual_upper d target N sample delta_o q) a j
    hpathV hsample hKstar hLq hres hj hx hxs hgap

/--
OET anchor: h-4091a4a3834bf02c
**命题（路径局部正偏差下界证书，代理表示形式）**
When the network represents the proxy, the path-chain lower certificate is a
positive-deviation certificate for the proxy itself.
-/
theorem proxy_path_positive_deviation_lower_proxy_colip
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot)
    (N : FiniteOperatorNetwork X bot V) (sample : I → Set X)
    (delta_o : I → ENNReal) (q : N.ReachablePath)
    (Vstar : Set X) (Kq Lstar : I → I → ENNReal)
    (a : ENNReal) (j : I)
    (hrep : N.represents proxy)
    (hpathV : N.path_domain q.nodes ⊆ Vstar)
    (hKq : IsCoLipMatrix d (N.path_chain q.nodes) (N.path_domain q.nodes) Kq)
    (hLstar : TargetLipEnvelopeCertificate d target Vstar Lstar)
    (hj : j ∈ path_evaluable_components N sample q)
    {x xs : X}
    (hx : x ∈ N.path_domain q.nodes)
    (hxs : xs ∈ path_component_sample N sample q j)
    (hgap :
      a + matrix_vector_bound Lstar (fun i => d i x xs) j +
          path_empirical_residual_upper d target N sample delta_o q j <
        matrix_vector_bound Kq (fun i => d i x xs) j) :
    a < d j (proxy.func x) (target.func x) := by
  have hchain :=
    path_chain_eq_represented_proxy_on_path N proxy q hrep hx
  simpa [hchain] using
    (path_positive_deviation_lower_proxy_colip d hd target N sample delta_o q
      Vstar Kq Lstar a j hpathV hKq hLstar hj hx hxs hgap)

/--
OET anchor: h-4091a4a3834bf02c
**命题（路径局部正偏差下界证书，代理表示正文前提版本）**
Text-faithful wrapper retaining the finite radius condition.
-/
theorem proxy_path_positive_deviation_lower_proxy_colip_text
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot)
    (N : FiniteOperatorNetwork X bot V) (sample : I → Set X)
    (delta_o : I → ENNReal) (q : N.ReachablePath)
    (Vstar : Set X) (Kq Lstar : I → I → ENNReal)
    (a : ENNReal) (j : I)
    (ha_finite : finite_ennreal a)
    (hrep : N.represents proxy)
    (hpathV : N.path_domain q.nodes ⊆ Vstar)
    (hKq : IsCoLipMatrix d (N.path_chain q.nodes) (N.path_domain q.nodes) Kq)
    (hLstar : TargetLipEnvelopeCertificate d target Vstar Lstar)
    (hj : j ∈ path_evaluable_components N sample q)
    {x xs : X}
    (hx : x ∈ N.path_domain q.nodes)
    (hxs : xs ∈ path_component_sample N sample q j)
    (hgap :
      a + matrix_vector_bound Lstar (fun i => d i x xs) j +
          path_empirical_residual_upper d target N sample delta_o q j <
        matrix_vector_bound Kq (fun i => d i x xs) j) :
    a < d j (proxy.func x) (target.func x) := by
  have _ := ha_finite
  exact proxy_path_positive_deviation_lower_proxy_colip d hd target proxy N
    sample delta_o q Vstar Kq Lstar a j hrep hpathV hKq hLstar hj hx hxs hgap

/--
OET anchor: h-4091a4a3834bf02c
**命题（路径局部正偏差下界证书，目标 co-Lip 代理表示形式）**
The target co-Lip lower certificate also transfers from the path chain to the
represented proxy.
-/
theorem proxy_path_positive_deviation_lower_target_colip
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot)
    (N : FiniteOperatorNetwork X bot V) (sample : I → Set X)
    (delta_o : I → ENNReal) (q : N.ReachablePath)
    (Vstar : Set X) (Kstar Lq : I → I → ENNReal)
    (a : ENNReal) (j : I)
    (hrep : N.represents proxy)
    (hpathV : N.path_domain q.nodes ⊆ Vstar)
    (hKstar : TargetCoLipLowerCertificate d target Vstar Kstar)
    (hLq : IsLipMatrix d (N.path_chain q.nodes) (N.path_domain q.nodes) Lq)
    (hj : j ∈ path_evaluable_components N sample q)
    {x xs : X}
    (hx : x ∈ N.path_domain q.nodes)
    (hxs : xs ∈ path_component_sample N sample q j)
    (hgap :
      a + matrix_vector_bound Lq (fun i => d i x xs) j +
          path_empirical_residual_upper d target N sample delta_o q j <
        matrix_vector_bound Kstar (fun i => d i x xs) j) :
    a < d j (proxy.func x) (target.func x) := by
  have hchain :=
    path_chain_eq_represented_proxy_on_path N proxy q hrep hx
  simpa [hchain] using
    (path_positive_deviation_lower_target_colip d hd target N sample delta_o q
      Vstar Kstar Lq a j hpathV hKstar hLq hj hx hxs hgap)

/--
OET anchor: h-4091a4a3834bf02c
**命题（路径局部正偏差下界证书，目标 co-Lip 正文前提版本）**
Text-faithful wrapper retaining the finite radius condition.
-/
theorem proxy_path_positive_deviation_lower_target_colip_text
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot)
    (N : FiniteOperatorNetwork X bot V) (sample : I → Set X)
    (delta_o : I → ENNReal) (q : N.ReachablePath)
    (Vstar : Set X) (Kstar Lq : I → I → ENNReal)
    (a : ENNReal) (j : I)
    (ha_finite : finite_ennreal a)
    (hrep : N.represents proxy)
    (hpathV : N.path_domain q.nodes ⊆ Vstar)
    (hKstar : TargetCoLipLowerCertificate d target Vstar Kstar)
    (hLq : IsLipMatrix d (N.path_chain q.nodes) (N.path_domain q.nodes) Lq)
    (hj : j ∈ path_evaluable_components N sample q)
    {x xs : X}
    (hx : x ∈ N.path_domain q.nodes)
    (hxs : xs ∈ path_component_sample N sample q j)
    (hgap :
      a + matrix_vector_bound Lq (fun i => d i x xs) j +
          path_empirical_residual_upper d target N sample delta_o q j <
        matrix_vector_bound Kstar (fun i => d i x xs) j) :
    a < d j (proxy.func x) (target.func x) := by
  have _ := ha_finite
  exact proxy_path_positive_deviation_lower_target_colip d hd target proxy N
    sample delta_o q Vstar Kstar Lq a j hrep hpathV hKstar hLq hj hx hxs hgap

/--
OET anchor: h-93b9c20ea18b4e59
**推论（路径保证域的全局拟合含义，分量形式）**
The union of certified path component guarantee domains is contained in the
true proxy-target component tolerance region.
-/
theorem path_component_guarantee_union_subset_proxy_error
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot)
    (N : FiniteOperatorNetwork X bot V) (sample : I → Set X)
    (delta_o : I → ENNReal)
    (Vstar : Set X) (Lq : N.ReachablePath → I → I → ENNReal)
    (Lstar : I → I → ENNReal) (j : I) (tau : ENNReal)
    (hrep : N.represents proxy)
    (hpathV : ∀ q : N.ReachablePath, N.path_domain q.nodes ⊆ Vstar)
    (hLq : ∀ q : N.ReachablePath,
      j ∈ path_evaluable_components N sample q →
      IsLipMatrix d (N.path_chain q.nodes) (N.path_domain q.nodes) (Lq q))
    (hLstar : TargetLipEnvelopeCertificate d target Vstar Lstar) :
    {x | ∃ q : N.ReachablePath,
      j ∈ path_evaluable_components N sample q ∧
      x ∈ path_component_empirical_guarantee_domain d
        (fun i j => Lq q i j + Lstar i j) N sample q j
        (path_empirical_residual_upper d target N sample delta_o q j) tau}
      ⊆ {x | x ∈ N.U ∧ d j (proxy.func x) (target.func x) ≤ tau} := by
  intro x hx
  rcases hx with ⟨q, hj, hxq⟩
  exact ⟨N.path_domain_subset_source hxq.1,
    proxy_path_component_guarantee_error_bound d hd target proxy N sample
      delta_o q Vstar (Lq q) Lstar j tau hrep (hpathV q) (hLq q hj)
      hLstar hj hxq⟩

/--
OET anchor: h-93b9c20ea18b4e59
**推论（路径保证域的全局拟合含义，联合形式）**
The union of path-local joint guarantee domains is contained in the true joint
proxy-target tolerance region.
-/
theorem path_joint_guarantee_union_subset_proxy_error
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot)
    (N : FiniteOperatorNetwork X bot V) (sample : I → Set X)
    (delta_o : I → ENNReal)
    (Vstar : Set X) (Lq : N.ReachablePath → I → I → ENNReal)
    (Lstar : I → I → ENNReal) (J : Set I) (tau : I → ENNReal)
    (hrep : N.represents proxy)
    (hpathV : ∀ q : N.ReachablePath, N.path_domain q.nodes ⊆ Vstar)
    (hLq : ∀ q : N.ReachablePath,
      J ⊆ path_evaluable_components N sample q →
      IsLipMatrix d (N.path_chain q.nodes) (N.path_domain q.nodes) (Lq q))
    (hLstar : TargetLipEnvelopeCertificate d target Vstar Lstar) :
    {x | ∃ q : N.ReachablePath,
      J ⊆ path_evaluable_components N sample q ∧
      x ∈ path_joint_empirical_guarantee_domain d
        (fun i j => Lq q i j + Lstar i j) N sample q J
        (path_empirical_residual_upper d target N sample delta_o q) tau}
      ⊆ {x | x ∈ N.U ∧
        ∀ j : I, j ∈ J → d j (proxy.func x) (target.func x) ≤ tau j} := by
  intro x hx
  rcases hx with ⟨q, hJ, hxq⟩
  refine ⟨N.path_domain_subset_source hxq.1, ?_⟩
  intro j hj
  have hchain :=
    path_chain_eq_represented_proxy_on_path N proxy q hrep hxq.1
  simpa [hchain] using
    (path_joint_guarantee_error_bound d hd target N sample delta_o q
      Vstar (Lq q) Lstar J tau (hpathV q) (hLq q hJ) hLstar hJ hxq j hj)

/--
OET anchor: h-93b9c20ea18b4e59
**推论（路径保证域的全局拟合含义）**
The text-level component and joint conclusions retain finite thresholds and
the nonempty joint component family.
-/
theorem path_guarantee_union_subset_proxy_error_text
    (d : I → X → X → ENNReal)
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot)
    (N : FiniteOperatorNetwork X bot V) (sample : I → Set X)
    (delta_o : I → ENNReal)
    (Vstar : Set X) (Lq : N.ReachablePath → I → I → ENNReal)
    (Lstar : I → I → ENNReal) (j : I) (tau_j : ENNReal)
    (J : Set I) (tau : I → ENNReal)
    (hj_evaluable : j ∈ evaluable_components sample)
    (hJ_evaluable : J ⊆ evaluable_components sample)
    (htau_j_finite : finite_ennreal tau_j)
    (hJ_nonempty : J.Nonempty)
    (htau_finite : ∀ i : I, i ∈ J → finite_ennreal (tau i))
    (hrep : N.represents proxy)
    (hpathV : ∀ q : N.ReachablePath, N.path_domain q.nodes ⊆ Vstar)
    (hLq : ∀ q : N.ReachablePath,
      (j ∈ path_evaluable_components N sample q ∨
        J ⊆ path_evaluable_components N sample q) →
      IsLipMatrix d (N.path_chain q.nodes) (N.path_domain q.nodes) (Lq q))
    (hLstar : TargetLipEnvelopeCertificate d target Vstar Lstar) :
    ({x | ∃ q : N.ReachablePath,
        j ∈ path_evaluable_components N sample q ∧
        x ∈ path_component_empirical_guarantee_domain d
          (fun i j => Lq q i j + Lstar i j) N sample q j
          (path_empirical_residual_upper d target N sample delta_o q j) tau_j}
        ⊆ {x | x ∈ N.U ∧
          d j (proxy.func x) (target.func x) ≤ tau_j}) ∧
      ({x | ∃ q : N.ReachablePath,
        J ⊆ path_evaluable_components N sample q ∧
        x ∈ path_joint_empirical_guarantee_domain d
          (fun i j => Lq q i j + Lstar i j) N sample q J
          (path_empirical_residual_upper d target N sample delta_o q) tau}
        ⊆ {x | x ∈ N.U ∧
          ∀ i : I, i ∈ J →
            d i (proxy.func x) (target.func x) ≤ tau i}) := by
  have _ := hj_evaluable
  have _ := hJ_evaluable
  have _ := htau_j_finite
  have _ := hJ_nonempty
  have _ := htau_finite
  exact ⟨
    path_component_guarantee_union_subset_proxy_error d hd target proxy N
      sample delta_o Vstar Lq Lstar j tau_j hrep hpathV
      (fun q hj => hLq q (Or.inl hj)) hLstar,
    path_joint_guarantee_union_subset_proxy_error d hd target proxy N
      sample delta_o Vstar Lq Lstar J tau hrep hpathV
      (fun q hJ => hLq q (Or.inr hJ)) hLstar⟩

end formal_oet.vol_03.ch_14_empirical_network_fitting
