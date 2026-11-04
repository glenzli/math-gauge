import formal_oet.vol_02.ch_07_fitting_foundations.fitting_ball
import formal_oet.vol_01.ch_02_operator_bounds.lip_matrix
import formal_oet.vol_01.ch_04_operator_chain_calculus.distance_recurrence
import formal_oet.vol_01.ch_03_operator_local_degeneracy.component_partition
import Mathlib.Data.ENNReal.Basic
import Mathlib.Tactic

namespace formal_oet.vol_02.ch_07_fitting_foundations

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open formal_oet.vol_01.ch_03_operator_local_degeneracy
open formal_oet.vol_01.ch_04_operator_chain_calculus

open scoped BigOperators

variable {X I : Type} {bot : X} [Fintype I]
variable (d : I → X → X → ENNReal)

/--
OET anchor: h-10333868e2fa38b6
**命题 #h-10333868e2fa38b6（点态下游双侧界与共同前后接局部传递，点态下游双侧界）**
For a downstream operator with valid restricted L/K matrices, the terminal
distance is trapped between the matrix-vector lower and upper bounds.
-/
theorem terminal_composition_bounds
    (downstream : Operator X bot) (V : Set X)
    (K L : I → I → ENNReal)
    (hK : IsCoLipMatrix d downstream V K)
    (hL : IsLipMatrix d downstream V L) :
    ∀ y ∈ V, ∀ y' ∈ V, ∀ j : I,
      matrix_vector_bound K (fun i => d i y y') j ≤
        d j (downstream.func y) (downstream.func y') ∧
      d j (downstream.func y) (downstream.func y') ≤
        matrix_vector_bound L (fun i => d i y y') j := by
  intro y hy y' hy' j
  exact ⟨by simpa [matrix_vector_bound] using hK.2.2 y hy y' hy' j,
    by simpa [matrix_vector_bound] using hL.2 y hy y' hy' j⟩

/--
OET anchor: h-10333868e2fa38b6
**命题 #h-10333868e2fa38b6（点态下游双侧界与共同前后接局部传递，共同前后接局部上界）**
If the target/proxy pointwise distance is bounded by a local error certificate
on `S`, and a common pre-composition sends `A` into `S`, then a common
post-composition with a Lip matrix on the relevant local image set propagates
the upper bound.
-/
theorem common_pre_post_composition_local_upper_bound
    (c_up c_down target proxy : Operator X bot)
    (A S V : Set X) (eps' : I → ENNReal) (L_down' : I → I → ENNReal)
    (hc_up_dom : A ⊆ dom c_up)
    (hc_upS : ∀ x ∈ A, c_up.func x ∈ S)
    (hfit : ∀ u ∈ S, ∀ i : I, d i (target.func u) (proxy.func u) ≤ eps' i)
    (hV : ∀ x ∈ A, target.func (c_up.func x) ∈ V ∧ proxy.func (c_up.func x) ∈ V)
    (hL_down : IsLipMatrix d c_down V L_down') :
    ∀ x ∈ A, ∀ j : I,
      d j (c_down.func (target.func (c_up.func x)))
          (c_down.func (proxy.func (c_up.func x))) ≤
        matrix_vector_bound L_down' eps' j := by
  intro x hx j
  have _ := hc_up_dom hx
  have hxS : c_up.func x ∈ S := hc_upS x hx
  have hraw :
      d j (c_down.func (target.func (c_up.func x)))
          (c_down.func (proxy.func (c_up.func x))) ≤
        ∑ i : I, L_down' i j *
          d i (target.func (c_up.func x)) (proxy.func (c_up.func x)) := by
    exact hL_down.2 (target.func (c_up.func x)) (hV x hx).1
      (proxy.func (c_up.func x)) (hV x hx).2 j
  have hsum :
      (∑ i : I, L_down' i j *
          d i (target.func (c_up.func x)) (proxy.func (c_up.func x))) ≤
        matrix_vector_bound L_down' eps' j := by
    unfold matrix_vector_bound
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_right
      (hfit (c_up.func x) hxS i)
      (L_down' i j)
  exact le_trans hraw hsum

/--
OET anchor: h-10333868e2fa38b6
**命题 #h-10333868e2fa38b6（共同前后接的拟合上界与残差下界传递，有限传播闭球）**
The extended-valued pointwise bound above becomes proxy-ball membership only
when every propagated tolerance component is finite.
-/
theorem common_pre_post_composition_fitting_ball_of_finite
    (c_up c_down target proxy : Operator X bot)
    (A S_A V : Set X) (eps : I → ENNReal) (L_down : I → I → ENNReal)
    (hc_up_dom : A ⊆ dom c_up)
    (hc_upS : ∀ x ∈ A, c_up.func x ∈ S_A)
    (hfit : InFullFittingBall d target proxy S_A eps)
    (hV : ∀ x ∈ A, target.func (c_up.func x) ∈ V ∧ proxy.func (c_up.func x) ∈ V)
    (hL_down : IsLipMatrix d c_down V L_down)
    (hpropagated_finite : ∀ j : I, matrix_vector_bound L_down eps j ≠ ⊤) :
    InFullFittingBall d
      (OperatorChain [c_down, target, c_up])
      (OperatorChain [c_down, proxy, c_up]) A
      (matrix_vector_bound L_down eps) := by
  refine ⟨fun j _ => hpropagated_finite j, ?_, ?_, ?_⟩
  · intro x hx
    dsimp [dom, OperatorChain]
    exact hL_down.1 (hV x hx).1
  · intro x hx
    dsimp [dom, OperatorChain]
    exact hL_down.1 (hV x hx).2
  · intro x hx j _
    simpa [OperatorChain] using
      common_pre_post_composition_local_upper_bound d
        c_up c_down target proxy A S_A V eps L_down
        hc_up_dom hc_upS
        (fun u hu i => hfit.error u hu i (Set.mem_univ i))
        hV hL_down x hx j

/--
OET anchor: h-10333868e2fa38b6
**命题 #h-10333868e2fa38b6（点态下游双侧界与共同前后接局部传递，共同前后接局部下界）**
A common post-composition with a co-Lip matrix on the relevant local image set
propagates the lower matrix-vector bound of the actual pointwise error vector.
-/
theorem common_pre_post_composition_local_lower_bound
    (c_up c_down target proxy : Operator X bot)
    (A S V : Set X) (K_down' : I → I → ENNReal)
    (hc_up_dom : A ⊆ dom c_up)
    (hc_upS : ∀ x ∈ A, c_up.func x ∈ S)
    (hV : ∀ x ∈ A, target.func (c_up.func x) ∈ V ∧ proxy.func (c_up.func x) ∈ V)
    (hK_down : IsCoLipMatrix d c_down V K_down') :
    ∀ x ∈ A, ∀ j : I,
      matrix_vector_bound K_down'
          (fun i => d i (target.func (c_up.func x)) (proxy.func (c_up.func x))) j ≤
        d j (c_down.func (target.func (c_up.func x)))
          (c_down.func (proxy.func (c_up.func x))) := by
  intro x hx j
  have _ := hc_up_dom hx
  have _ := hc_upS x hx
  simpa [matrix_vector_bound] using
    hK_down.2.2 (target.func (c_up.func x)) (hV x hx).1
      (proxy.func (c_up.func x)) (hV x hx).2 j

/--
OET anchor: h-10333868e2fa38b6
**命题 #h-10333868e2fa38b6（共同前后接的拟合上界与残差下界传递，残差向量传播）**
A componentwise residual certificate is propagated by the downstream co-Lip
matrix without any finiteness assumption.
-/
theorem common_pre_post_composition_residual_lower_bound
    (c_up c_down target proxy : Operator X bot)
    (A S_A V : Set X) (eps_res : I → ENNReal)
    (K_down : I → I → ENNReal)
    (hc_up_dom : A ⊆ dom c_up)
    (hc_upS : ∀ x ∈ A, c_up.func x ∈ S_A)
    (hres :
      ∀ u ∈ S_A, ∀ i : I,
        eps_res i ≤ d i (target.func u) (proxy.func u))
    (hV : ∀ x ∈ A, target.func (c_up.func x) ∈ V ∧ proxy.func (c_up.func x) ∈ V)
    (hK_down : IsCoLipMatrix d c_down V K_down) :
    ∀ x ∈ A, ∀ j : I,
      matrix_vector_bound K_down eps_res j ≤
        d j (c_down.func (target.func (c_up.func x)))
          (c_down.func (proxy.func (c_up.func x))) := by
  intro x hx j
  have hxS : c_up.func x ∈ S_A := hc_upS x hx
  have hmono :
      matrix_vector_bound K_down eps_res j ≤
        matrix_vector_bound K_down
          (fun i => d i (target.func (c_up.func x)) (proxy.func (c_up.func x))) j := by
    unfold matrix_vector_bound
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_right (hres (c_up.func x) hxS i) (K_down i j)
  exact le_trans hmono
    (common_pre_post_composition_local_lower_bound d
      c_up c_down target proxy A S_A V K_down
      hc_up_dom hc_upS hV hK_down x hx j)

/--
OET anchor: h-10333868e2fa38b6
**命题 #h-10333868e2fa38b6（共同前后接的拟合上界与残差下界传递，残差下界证书）**
The propagated pointwise lower bound, together with the composed common-domain
conditions, is the residual lower-bound certificate asserted in the text.
-/
theorem common_pre_post_composition_residual_certificate
    [Nonempty I]
    (c_up c_down target proxy : Operator X bot)
    (A S_A V : Set X) (eps_res : I → ENNReal)
    (K_down : I → I → ENNReal)
    (hc_up_dom : A ⊆ dom c_up)
    (hc_upS : ∀ x ∈ A, c_up.func x ∈ S_A)
    (hres :
      ∀ u ∈ S_A, ∀ i : I,
        eps_res i ≤ d i (target.func u) (proxy.func u))
    (hV : ∀ x ∈ A,
      target.func (c_up.func x) ∈ V ∧ proxy.func (c_up.func x) ∈ V)
    (hK_down : IsCoLipMatrix d c_down V K_down) :
    ResidualLowerCertificate d
      (OperatorChain [c_down, target, c_up])
      (OperatorChain [c_down, proxy, c_up]) A Set.univ
      (matrix_vector_bound K_down eps_res) := by
  refine ⟨?_, ?_, Set.univ_nonempty, ?_⟩
  · intro x hx
    dsimp [dom, OperatorChain]
    exact hK_down.2.1 (hV x hx).1
  · intro x hx
    dsimp [dom, OperatorChain]
    exact hK_down.2.1 (hV x hx).2
  · intro x hx j _
    simpa [OperatorChain] using
      common_pre_post_composition_residual_lower_bound d
        c_up c_down target proxy A S_A V eps_res K_down
        hc_up_dom hc_upS hres hV hK_down x hx j

/--
OET anchor: h-10333868e2fa38b6
**命题 #h-10333868e2fa38b6（共同前后接的拟合上界与残差下界传递，正文汇总形式）**
This wrapper retains the complete upper/lower hypotheses of the text and
returns its pointwise two-sided estimate together with both named certificate
conclusions.
-/
theorem common_pre_post_composition_bounds_and_certificates_text
    [Nonempty I]
    (c_up c_down target proxy : Operator X bot)
    (A S_A V : Set X) (eps eps_res : I → ENNReal)
    (L_down K_down : I → I → ENNReal)
    (hc_up_dom : A ⊆ dom c_up)
    (hc_upS : ∀ x ∈ A, c_up.func x ∈ S_A)
    (hfit : InFullFittingBall d target proxy S_A eps)
    (hres :
      ∀ u ∈ S_A, ∀ i : I,
        eps_res i ≤ d i (target.func u) (proxy.func u))
    (hV : ∀ x ∈ A,
      target.func (c_up.func x) ∈ V ∧ proxy.func (c_up.func x) ∈ V)
    (hL_down : IsLipMatrix d c_down V L_down)
    (hK_down : IsCoLipMatrix d c_down V K_down)
    (hpropagated_finite : ∀ j : I, matrix_vector_bound L_down eps j ≠ ⊤) :
    (∀ x ∈ A, ∀ j : I,
      matrix_vector_bound K_down eps_res j ≤
          d j (c_down.func (target.func (c_up.func x)))
            (c_down.func (proxy.func (c_up.func x))) ∧
        d j (c_down.func (target.func (c_up.func x)))
            (c_down.func (proxy.func (c_up.func x))) ≤
          matrix_vector_bound L_down eps j) ∧
      InFullFittingBall d
        (OperatorChain [c_down, target, c_up])
        (OperatorChain [c_down, proxy, c_up]) A
        (matrix_vector_bound L_down eps) ∧
      ResidualLowerCertificate d
        (OperatorChain [c_down, target, c_up])
        (OperatorChain [c_down, proxy, c_up]) A Set.univ
        (matrix_vector_bound K_down eps_res) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx j
    constructor
    · exact common_pre_post_composition_residual_lower_bound d
        c_up c_down target proxy A S_A V eps_res K_down
        hc_up_dom hc_upS hres hV hK_down x hx j
    · exact common_pre_post_composition_local_upper_bound d
        c_up c_down target proxy A S_A V eps L_down
        hc_up_dom hc_upS
        (fun u hu i => hfit.error u hu i (Set.mem_univ i))
        hV hL_down x hx j
  · exact common_pre_post_composition_fitting_ball_of_finite d
      c_up c_down target proxy A S_A V eps L_down
      hc_up_dom hc_upS hfit hV hL_down hpropagated_finite
  · exact common_pre_post_composition_residual_certificate d
      c_up c_down target proxy A S_A V eps_res K_down
      hc_up_dom hc_upS hres hV hK_down

/--
Internal algebraic helper: the full upper matrix-vector bound splits into the
controlled component family and its complement.  On the selected family the raw
pointwise distances may be replaced by the fitting tolerances.
-/
theorem terminal_upper_bound_subset_split
    [DecidableEq I]
    (L : I → I → ENNReal) (raw eps : I → ENNReal) (J : Finset I) (j : I)
    (hfit : ∀ i : I, i ∈ J → raw i ≤ eps i) :
    matrix_vector_bound L raw j ≤
      ∑ i : I, if i ∈ J then L i j * eps i else L i j * raw i := by
  classical
  unfold matrix_vector_bound
  apply Finset.sum_le_sum
  intro i _
  by_cases hiJ : i ∈ J
  · simp [hiJ]
    simpa [mul_comm] using mul_le_mul_right (hfit i hiJ) (L i j)
  · simp [hiJ]

/--
Internal algebraic helper: if the downstream coefficients from uncovered
components to `j` vanish, the complementary summand in the split upper bound is
zero.
-/
theorem terminal_upper_bound_subset_split_uncovered_terms_vanish
    [DecidableEq I]
    (L : I → I → ENNReal) (raw eps : I → ENNReal) (J : Finset I) (j : I)
    (hfit : ∀ i : I, i ∈ J → raw i ≤ eps i)
    (hzero : ∀ i : I, i ∉ J → L i j = 0) :
    matrix_vector_bound L raw j ≤
      ∑ i : I, if i ∈ J then L i j * eps i else 0 := by
  classical
  have hsplit :=
    terminal_upper_bound_subset_split L raw eps J j hfit
  have hsum_eq :
      (∑ i : I, if i ∈ J then L i j * eps i else L i j * raw i) =
        ∑ i : I, if i ∈ J then L i j * eps i else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hiJ : i ∈ J
    · simp [hiJ]
    · simp [hiJ, hzero i hiJ]
  rwa [hsum_eq] at hsplit

/--
Internal algebraic helper: the `i₀ → j` co-Lip term is a lower summand of the
terminal error.
-/
theorem colip_path_term_le_terminal_error
    (K : I → I → ENNReal) (eps : I → ENNReal) (terminal_error : ENNReal)
    (i₀ j : I) (hlower : matrix_vector_bound K eps j ≤ terminal_error) :
    K i₀ j * eps i₀ ≤ terminal_error := by
  have hterm : K i₀ j * eps i₀ ≤ matrix_vector_bound K eps j := by
    unfold matrix_vector_bound
    exact Finset.single_le_sum (fun i _ => zero_le (K i j * eps i)) (Finset.mem_univ i₀)
  exact le_trans hterm hlower

/--
Internal algebraic helper: if the selected co-Lip coefficient and source error
are positive, the terminal error is positive.
-/
theorem terminal_error_pos_of_colip_path_pos
    (K : I → I → ENNReal) (eps : I → ENNReal) (terminal_error : ENNReal)
    (i₀ j : I) (hlower : matrix_vector_bound K eps j ≤ terminal_error)
    (hKpos : 0 < K i₀ j) (hepspos : 0 < eps i₀) :
    0 < terminal_error := by
  have hprod : 0 < K i₀ j * eps i₀ :=
    ENNReal.mul_pos hKpos.ne' hepspos.ne'
  exact lt_of_lt_of_le hprod
    (colip_path_term_le_terminal_error K eps terminal_error i₀ j hlower)

omit [Fintype I] in
/--
OET anchor: h-2ebc63596b817afd
**命题 #h-2ebc63596b817afd（零化截断条件，点态形式）**
If a pair in `V` has `d_i`-distance strictly below the restricted annihilation
radius, the downstream `j`-output distance is zero.
-/
theorem zeroing_truncation_point
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (c_down : Operator X bot) (V : Set X) (i j : I)
    {y y' : X} (hy : y ∈ V) (hy' : y' ∈ V)
    (hsmall :
      d i y y' <
        min_annihilation_radius d c_down i (singleton_nonempty_finset j) V) :
    d j (c_down.func y) (c_down.func y') = 0 := by
  classical
  have hmin_le :
      min_annihilation_radius d c_down i (singleton_nonempty_finset j) V ≤
        annihilation_radius d c_down i (singleton_nonempty_finset j) V y :=
    iInf₂_le y hy
  have hlt_ann :
      d i y' y <
        annihilation_radius d c_down i (singleton_nonempty_finset j) V y := by
    rw [(hd i).symm y' y]
    exact lt_of_lt_of_le hsmall hmin_le
  have hsup := lt_iSup_iff.mp hlt_ann
  rcases hsup with ⟨r, hr⟩
  have hsup₂ := lt_iSup_iff.mp hr
  rcases hsup₂ with ⟨hr_fin, hr₂⟩
  have hsup₃ := lt_iSup_iff.mp hr₂
  rcases hsup₃ with ⟨hsub, hfinal⟩
  have hy'_fiber :
      y' ∈ ComputationalFiber d c_down (singleton_nonempty_finset j) V (c_down.func y) :=
    hsub ⟨hfinal, hy'⟩
  have hzero' :
      d j (c_down.func y') (c_down.func y) = 0 := by
    have hcomp :=
      (comp_pseudo_metric_eq_zero_iff d (singleton_nonempty_finset j)
        (c_down.func y') (c_down.func y)).mp hy'_fiber.2
    exact hcomp j (Finset.mem_singleton.mpr rfl)
  rw [(hd j).symm (c_down.func y) (c_down.func y')]
  exact hzero'

omit [Fintype I] in
/--
OET anchor: h-2ebc63596b817afd
**命题 #h-2ebc63596b817afd（零化截断条件）**
For a fitting proxy pair, the pointwise fitting error below the restricted
annihilation radius forces the downstream output component to vanish.
-/
theorem zeroing_truncation_of_fitting
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy c_down : Operator X bot) (U V : Set X)
    (eps : I → ENNReal) (i j : I)
    (hfit : InFullFittingBall d target proxy U eps)
    (htargetV : ∀ x ∈ U, target.func x ∈ V)
    (hproxyV : ∀ x ∈ U, proxy.func x ∈ V)
    (hsmall :
      eps i <
        min_annihilation_radius d c_down i (singleton_nonempty_finset j) V) :
    ∀ x ∈ U,
      d j (c_down.func (target.func x)) (c_down.func (proxy.func x)) = 0 := by
  classical
  intro x hx
  have hdist_small :
      d i (target.func x) (proxy.func x) <
        min_annihilation_radius d c_down i (singleton_nonempty_finset j) V :=
    lt_of_le_of_lt (hfit.error x hx i (Set.mem_univ i)) hsmall
  exact zeroing_truncation_point d hd c_down V i j
    (htargetV x hx) (hproxyV x hx) hdist_small

omit [Fintype I] in
/--
OET anchor: h-2ebc63596b817afd
**命题 #h-2ebc63596b817afd（零化截断条件，正文前提版本）**
Text-faithful wrapper retaining the nonempty measuring domain and downstream
domain assumptions from the text.
-/
theorem zeroing_truncation_of_fitting_text
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy c_down : Operator X bot) (U V : Set X)
    (eps : I → ENNReal) (i j : I)
    (hU_nonempty : U.Nonempty)
    (hV_dom : V ⊆ dom c_down)
    (hfit : InFullFittingBall d target proxy U eps)
    (htargetV : ∀ x ∈ U, target.func x ∈ V)
    (hproxyV : ∀ x ∈ U, proxy.func x ∈ V)
    (hsmall :
      eps i <
        min_annihilation_radius d c_down i (singleton_nonempty_finset j) V) :
    ∀ x ∈ U,
      d j (c_down.func (target.func x)) (c_down.func (proxy.func x)) = 0 := by
  have _ := hU_nonempty
  have _ := hV_dom
  exact zeroing_truncation_of_fitting d hd target proxy c_down U V eps i j
    hfit htargetV hproxyV hsmall

/--
OET anchor: h-d24e38d73b9b81aa
**命题 #h-d24e38d73b9b81aa（纤维冲突下界，中间形式）**
The co-Lip separation certificate and a proxy zero-fiber pair force the sum of
the two pointwise fitting errors to dominate the separation certificate.
-/
theorem fiber_conflict_sum_lower
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot) (U : Set X)
    (K : I → I → ENNReal) (hK : IsCoLipMatrix d target U K)
    {x x' : X} (hx : x ∈ U) (hx' : x' ∈ U) (j : I) (eta : ENNReal)
    (hzero : d j (proxy.func x) (proxy.func x') = 0)
    (hsep : 2 * eta ≤ matrix_vector_bound K (fun i => d i x x') j) :
    2 * eta ≤
      d j (target.func x) (proxy.func x) +
        d j (target.func x') (proxy.func x') := by
  have hcolip :
      matrix_vector_bound K (fun i => d i x x') j ≤
        d j (target.func x) (target.func x') := by
    simpa [matrix_vector_bound] using hK.2.2 x hx x' hx' j
  have htarget : 2 * eta ≤ d j (target.func x) (target.func x') :=
    le_trans hsep hcolip
  have htri₁ :=
    (hd j).triangle (target.func x) (proxy.func x) (target.func x')
  have htri₂ :=
    (hd j).triangle (proxy.func x) (proxy.func x') (target.func x')
  have hproxy :
      d j (proxy.func x) (target.func x') ≤
        d j (proxy.func x') (target.func x') := by
    simpa [hzero, zero_add] using htri₂
  have hproxy' :
      d j (proxy.func x) (target.func x') ≤
        d j (target.func x') (proxy.func x') := by
    simpa [(hd j).symm (target.func x') (proxy.func x')] using hproxy
  have hupper :
      d j (target.func x) (target.func x') ≤
        d j (target.func x) (proxy.func x) +
          d j (target.func x') (proxy.func x') := by
    refine le_trans htri₁ ?_
    simpa [add_comm, add_left_comm, add_assoc] using
      add_le_add_left hproxy' (d j (target.func x) (proxy.func x))
  exact le_trans htarget hupper

/--
OET anchor: h-d24e38d73b9b81aa
**命题 #h-d24e38d73b9b81aa（纤维冲突下界）**
The maximum of the two pointwise fitting errors is at least the finite positive
certificate `eta`.
-/
theorem fiber_conflict_max_lower
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot) (U : Set X)
    (K : I → I → ENNReal) (hK : IsCoLipMatrix d target U K)
    {x x' : X} (hx : x ∈ U) (hx' : x' ∈ U) (j : I) (eta : ENNReal)
    (hzero : d j (proxy.func x) (proxy.func x') = 0)
    (hsep : 2 * eta ≤ matrix_vector_bound K (fun i => d i x x') j) :
    eta ≤
      max (d j (target.func x) (proxy.func x))
        (d j (target.func x') (proxy.func x')) := by
  let a := d j (target.func x) (proxy.func x)
  let b := d j (target.func x') (proxy.func x')
  have hsum : 2 * eta ≤ a + b := by
    simpa [a, b] using
      fiber_conflict_sum_lower d hd target proxy U K hK hx hx' j eta hzero hsep
  have hsum_le : a + b ≤ 2 * max a b := by
    have ha : a ≤ max a b := le_max_left a b
    have hb : b ≤ max a b := le_max_right a b
    calc
      a + b ≤ max a b + max a b := add_le_add ha hb
      _ = 2 * max a b := by rw [two_mul]
  have htwo : 2 * eta ≤ 2 * max a b := le_trans hsum hsum_le
  have htwo_ne_zero : (2 : ENNReal) ≠ 0 := by norm_num
  have htwo_ne_top : (2 : ENNReal) ≠ ⊤ := by norm_num
  exact (ENNReal.mul_le_mul_iff_right htwo_ne_zero htwo_ne_top).mp htwo

/--
OET anchor: h-d24e38d73b9b81aa
**命题 #h-d24e38d73b9b81aa（纤维冲突下界，正文前提版本）**
Text-faithful wrapper retaining the finite positive certificate condition.
-/
theorem fiber_conflict_max_lower_text
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot) (U : Set X)
    (K : I → I → ENNReal) (hK : IsCoLipMatrix d target U K)
    {x x' : X} (hx : x ∈ U) (hx' : x' ∈ U) (j : I) (eta : ENNReal)
    (heta_pos : 0 < eta)
    (heta_finite : eta ≠ ⊤)
    (hzero : d j (proxy.func x) (proxy.func x') = 0)
    (hsep : 2 * eta ≤ matrix_vector_bound K (fun i => d i x x') j) :
    eta ≤
      max (d j (target.func x) (proxy.func x))
        (d j (target.func x') (proxy.func x')) := by
  have _ := heta_pos
  have _ := heta_finite
  exact fiber_conflict_max_lower d hd target proxy U K hK hx hx' j eta hzero hsep

/--
OET anchor: h-3fbe51f15ef6d06c
**命题 #h-3fbe51f15ef6d06c（拟合闭球内的点对像距扰动界，Lip 上界）**
A proxy in a fitting ball inherits the target image-distance upper bound with
the additive `2 eps_j` tolerance.
-/
theorem fitting_ball_lip_matrix_constraint
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot) (U : Set X)
    (eps : I → ENNReal) (L : I → I → ENNReal)
    (hfit : InFullFittingBall d target proxy U eps)
    (hL : IsLipMatrix d target U L) :
    ∀ x ∈ U, ∀ x' ∈ U, ∀ j : I,
      d j (proxy.func x) (proxy.func x') ≤
        matrix_vector_bound L (fun i => d i x x') j + (eps j + eps j) := by
  intro x hx x' hx' j
  simpa [matrix_vector_bound] using
    operator_pair_lip_bound_of_pointwise_perturbation d hd target proxy U eps L
      hfit.target_dom hfit.proxy_dom
      (fun z hz k => hfit.error z hz k (Set.mem_univ k)) hL
      x hx x' hx' j

/--
OET anchor: h-3fbe51f15ef6d06c
**命题 #h-3fbe51f15ef6d06c（拟合闭球内的点对像距扰动界，co-Lip 下界）**
The target co-Lip lower bound survives on the additive side after adding the
two fitting tolerances.
-/
theorem fitting_ball_colip_matrix_constraint
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot) (U : Set X)
    (eps : I → ENNReal) (K : I → I → ENNReal)
    (hfit : InFullFittingBall d target proxy U eps)
    (hK : IsCoLipMatrix d target U K) :
    ∀ x ∈ U, ∀ x' ∈ U, ∀ j : I,
      matrix_vector_bound K (fun i => d i x x') j ≤
        d j (proxy.func x) (proxy.func x') + (eps j + eps j) := by
  intro x hx x' hx' j
  simpa [matrix_vector_bound] using
    operator_pair_colip_bound_of_pointwise_perturbation d hd target proxy U eps K
      hfit.target_dom hfit.proxy_dom
      (fun z hz k => hfit.error z hz k (Set.mem_univ k)) hK
      x hx x' hx' j

/--
OET anchor: h-3b97f42dbabb301d
**命题 #h-3b97f42dbabb301d（纤维非归零的 co-Lip 阈值证书）**
If the target co-Lip lower bound exceeds the additive tolerance, the proxy
cannot collapse the pair to zero in that component.
-/
theorem fiber_nonzero_of_colip_threshold
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot) (U : Set X)
    (eps : I → ENNReal) (K : I → I → ENNReal)
    (hfit : InFullFittingBall d target proxy U eps)
    (hK : IsCoLipMatrix d target U K)
    {x x' : X} (hx : x ∈ U) (hx' : x' ∈ U) (j : I)
    (hstrict :
      (eps j + eps j) <
        matrix_vector_bound K (fun i => d i x x') j) :
    0 < d j (proxy.func x) (proxy.func x') := by
  by_contra hnot
  have hle_zero : d j (proxy.func x) (proxy.func x') ≤ 0 := not_lt.mp hnot
  have hzero : d j (proxy.func x) (proxy.func x') = 0 :=
    le_antisymm hle_zero (zero_le _)
  have hbound :=
    fitting_ball_colip_matrix_constraint d hd target proxy U eps K hfit hK x hx x' hx' j
  have hle_eps :
      matrix_vector_bound K (fun i => d i x x') j ≤ eps j + eps j := by
    simpa [hzero, zero_add] using hbound
  exact (not_lt_of_ge hle_eps) hstrict

/--
OET anchor: h-7b1310be48fd8407
**推论 #h-7b1310be48fd8407（常值与活跃分量的 ε-稳定性，分量像直径）**
The `j`-component diameter of the image of `U` under an operator.
-/
noncomputable def component_image_diameter
    (phi : Operator X bot) (U : Set X) (j : I) : ENNReal :=
  ⨆ x : {x // x ∈ U}, ⨆ y : {y // y ∈ U},
    d j (phi.func x.1) (phi.func y.1)

omit [Fintype I] in
/--
OET anchor: h-7b1310be48fd8407
**推论 #h-7b1310be48fd8407（近似常值继承）**
A target component that is constant on `U` yields proxy image diameter at most
`2 ε_j`.
-/
theorem const_component_proxy_diameter_le_two_eps
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot) (U : Set X)
    (eps : I → ENNReal) (j : I)
    (hfit : InFullFittingBall d target proxy U eps)
    (hconst : j ∈ ConstComponent d target U) :
    component_image_diameter d proxy U j ≤ eps j + eps j := by
  unfold component_image_diameter
  apply iSup_le
  intro x
  apply iSup_le
  intro y
  have htri₁ :=
    (hd j).triangle (proxy.func x.1) (target.func x.1) (proxy.func y.1)
  have htri₂ :=
    (hd j).triangle (target.func x.1) (target.func y.1) (proxy.func y.1)
  have hxerr : d j (proxy.func x.1) (target.func x.1) ≤ eps j := by
    rw [(hd j).symm (proxy.func x.1) (target.func x.1)]
    exact hfit.error x.1 x.2 j (Set.mem_univ j)
  have hyerr : d j (target.func y.1) (proxy.func y.1) ≤ eps j :=
    hfit.error y.1 y.2 j (Set.mem_univ j)
  have hconst_zero : d j (target.func x.1) (target.func y.1) = 0 :=
    hconst x.1 x.2 y.1 y.2
  calc
    d j (proxy.func x.1) (proxy.func y.1)
        ≤ d j (proxy.func x.1) (target.func x.1) +
          d j (target.func x.1) (proxy.func y.1) := htri₁
    _ ≤ eps j + (d j (target.func x.1) (target.func y.1) +
          d j (target.func y.1) (proxy.func y.1)) :=
        add_le_add hxerr htri₂
    _ = eps j + d j (target.func y.1) (proxy.func y.1) := by
        simp [hconst_zero]
    _ ≤ eps j + eps j := by
        simpa [add_comm] using add_le_add_left hyerr (eps j)
    _ = eps j + eps j := by simp

omit [Fintype I] in
/--
OET anchor: h-7b1310be48fd8407
**推论 #h-7b1310be48fd8407（正像距排除常值退化）**
A positive proxy image distance on a pair in `U` rules out membership in the
constant-component class.
-/
theorem not_const_component_of_positive_image_pair
    (proxy : Operator X bot) (U : Set X) (j : I)
    {x x' : X} (hx : x ∈ U) (hx' : x' ∈ U)
    (hpos : 0 < d j (proxy.func x) (proxy.func x')) :
    j ∉ ConstComponent d proxy U := by
  intro hconst
  have hzero := hconst x hx x' hx'
  rw [hzero] at hpos
  exact (lt_irrefl (0 : ENNReal)) hpos

/--
OET anchor: h-7b1310be48fd8407
**推论 #h-7b1310be48fd8407（近似非常值继承）**
The co-Lip threshold certificate of h-3b97f42dbabb301d makes the proxy
non-constant in component `j`; with non-identity assumed, it is active.
-/
theorem act_component_of_colip_threshold
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot) (U : Set X)
    (eps : I → ENNReal) (K : I → I → ENNReal)
    (hfit : InFullFittingBall d target proxy U eps)
    (hK : IsCoLipMatrix d target U K)
    {x x' : X} (hx : x ∈ U) (hx' : x' ∈ U) (j : I)
    (hnot_id : j ∉ IdComponent d proxy U)
    (hstrict :
      (eps j + eps j) <
        matrix_vector_bound K (fun i => d i x x') j) :
    j ∈ ActComponent d proxy U := by
  refine ⟨hnot_id, ?_⟩
  exact not_const_component_of_positive_image_pair d proxy U j hx hx'
    (fiber_nonzero_of_colip_threshold d hd target proxy U eps K hfit hK hx hx' j hstrict)

/--
OET anchor: h-8a441271c942d299
**命题 #h-8a441271c942d299（域外偏差延拓界，点态版本）**
For any fitting-domain point `x ∈ U`, the off-domain error is bounded by the
weighted distance from `x'` to `x` plus the fitting tolerance.
-/
theorem domain_extension_error_point_bound
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot) (U W : Set X)
    (eps : I → ENNReal) (Lt Lp : I → I → ENNReal)
    (hUW : U ⊆ W)
    (hfit : InFullFittingBall d target proxy U eps)
    (hLt : IsLipMatrix d target W Lt)
    (hLp : IsLipMatrix d proxy W Lp) :
    ∀ x' ∈ W, ∀ x ∈ U, ∀ j : I,
      d j (target.func x') (proxy.func x') ≤
        matrix_vector_bound (fun i j => Lt i j + Lp i j) (fun i => d i x' x) j +
          eps j := by
  intro x' hxW x hxU j
  have hxW' : x ∈ W := hUW hxU
  have htri₁ :=
    (hd j).triangle (target.func x') (target.func x) (proxy.func x')
  have htri₂ :=
    (hd j).triangle (target.func x) (proxy.func x) (proxy.func x')
  have ht :
      d j (target.func x') (target.func x) ≤
        matrix_vector_bound Lt (fun i => d i x' x) j := by
    simpa [matrix_vector_bound] using hLt.2 x' hxW x hxW' j
  have hp :
      d j (proxy.func x) (proxy.func x') ≤
        matrix_vector_bound Lp (fun i => d i x' x) j := by
    have hraw := hLp.2 x hxW' x' hxW j
    calc
      d j (proxy.func x) (proxy.func x') ≤ ∑ i : I, Lp i j * d i x x' := hraw
      _ = matrix_vector_bound Lp (fun i => d i x' x) j := by
          unfold matrix_vector_bound
          apply Finset.sum_congr rfl
          intro i _
          rw [(hd i).symm x x']
  have heps : d j (target.func x) (proxy.func x) ≤ eps j :=
    hfit.error x hxU j (Set.mem_univ j)
  have hsum :
      matrix_vector_bound Lt (fun i => d i x' x) j +
        (eps j + matrix_vector_bound Lp (fun i => d i x' x) j) ≤
      matrix_vector_bound (fun i j => Lt i j + Lp i j) (fun i => d i x' x) j +
        eps j := by
    unfold matrix_vector_bound
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib]
    simp [add_comm, add_left_comm]
  calc
    d j (target.func x') (proxy.func x')
        ≤ d j (target.func x') (target.func x) +
          d j (target.func x) (proxy.func x') := htri₁
    _ ≤ d j (target.func x') (target.func x) +
          (d j (target.func x) (proxy.func x) +
            d j (proxy.func x) (proxy.func x')) :=
        by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_left htri₂ (d j (target.func x') (target.func x))
    _ ≤ matrix_vector_bound Lt (fun i => d i x' x) j +
          (eps j + matrix_vector_bound Lp (fun i => d i x' x) j) :=
        add_le_add ht (add_le_add heps hp)
    _ ≤ matrix_vector_bound (fun i j => Lt i j + Lp i j) (fun i => d i x' x) j +
          eps j := hsum

/--
OET anchor: h-8a441271c942d299
**命题 #h-8a441271c942d299（域外偏差延拓界，正文前提版本）**
Text-faithful wrapper retaining the nonempty fitting domain and finite-matrix
assumptions from the text.
-/
theorem domain_extension_error_point_bound_text
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot) (U W : Set X)
    (eps : I → ENNReal) (Lt Lp : I → I → ENNReal)
    (hU_nonempty : U.Nonempty)
    (hLt_finite : ∀ i j : I, Lt i j ≠ ⊤)
    (hLp_finite : ∀ i j : I, Lp i j ≠ ⊤)
    (hUW : U ⊆ W)
    (hfit : InFullFittingBall d target proxy U eps)
    (hLt : IsLipMatrix d target W Lt)
    (hLp : IsLipMatrix d proxy W Lp) :
    ∀ x' ∈ W, ∀ x ∈ U, ∀ j : I,
      d j (target.func x') (proxy.func x') ≤
        matrix_vector_bound (fun i j => Lt i j + Lp i j) (fun i => d i x' x) j +
          eps j := by
  have _ := hU_nonempty
  have _ := hLt_finite
  have _ := hLp_finite
  exact domain_extension_error_point_bound d hd target proxy U W eps Lt Lp hUW hfit hLt hLp

/--
OET anchor: h-96c357f03b81261a
**命题 #h-96c357f03b81261a（同目标代理对的域内外距离与补域自由，域外距离上界点态版本）**
The proxy-pair off-domain distance is controlled by the sum of the two proxy
Lip matrices and the two fitting tolerances.
-/
theorem proxy_pair_domain_extension_point
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy_a proxy_b : Operator X bot) (U W : Set X)
    (eps_a eps_b : I → ENNReal) (La Lb : I → I → ENNReal)
    (hUW : U ⊆ W)
    (hfit_a : InFullFittingBall d target proxy_a U eps_a)
    (hfit_b : InFullFittingBall d target proxy_b U eps_b)
    (hLa : IsLipMatrix d proxy_a W La)
    (hLb : IsLipMatrix d proxy_b W Lb) :
    ∀ x' ∈ W, ∀ x ∈ U, ∀ j : I,
      d j (proxy_a.func x') (proxy_b.func x') ≤
        matrix_vector_bound (fun i j => La i j + Lb i j) (fun i => d i x' x) j +
          (eps_a j + eps_b j) := by
  intro x' hxW x hxU j
  have hxW' : x ∈ W := hUW hxU
  have htri₁ :=
    (hd j).triangle (proxy_a.func x') (proxy_a.func x) (proxy_b.func x')
  have htri₂ :=
    (hd j).triangle (proxy_a.func x) (proxy_b.func x) (proxy_b.func x')
  have ha :
      d j (proxy_a.func x') (proxy_a.func x) ≤
        matrix_vector_bound La (fun i => d i x' x) j := by
    simpa [matrix_vector_bound] using hLa.2 x' hxW x hxW' j
  have hb :
      d j (proxy_b.func x) (proxy_b.func x') ≤
        matrix_vector_bound Lb (fun i => d i x' x) j := by
    have hraw := hLb.2 x hxW' x' hxW j
    calc
      d j (proxy_b.func x) (proxy_b.func x') ≤ ∑ i : I, Lb i j * d i x x' := hraw
      _ = matrix_vector_bound Lb (fun i => d i x' x) j := by
          unfold matrix_vector_bound
          apply Finset.sum_congr rfl
          intro i _
          rw [(hd i).symm x x']
  have hmid :
      d j (proxy_a.func x) (proxy_b.func x) ≤ eps_a j + eps_b j :=
    proxy_pair_cross_consistency d hd target proxy_a proxy_b U eps_a eps_b hfit_a hfit_b x hxU j
  have hsum :
      matrix_vector_bound La (fun i => d i x' x) j +
        ((eps_a j + eps_b j) + matrix_vector_bound Lb (fun i => d i x' x) j) ≤
      matrix_vector_bound (fun i j => La i j + Lb i j) (fun i => d i x' x) j +
        (eps_a j + eps_b j) := by
    unfold matrix_vector_bound
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib]
    simp [add_assoc, add_comm, add_left_comm]
  calc
    d j (proxy_a.func x') (proxy_b.func x')
        ≤ d j (proxy_a.func x') (proxy_a.func x) +
          d j (proxy_a.func x) (proxy_b.func x') := htri₁
    _ ≤ d j (proxy_a.func x') (proxy_a.func x) +
          (d j (proxy_a.func x) (proxy_b.func x) +
            d j (proxy_b.func x) (proxy_b.func x')) :=
        by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_left htri₂ (d j (proxy_a.func x') (proxy_a.func x))
    _ ≤ matrix_vector_bound La (fun i => d i x' x) j +
          ((eps_a j + eps_b j) + matrix_vector_bound Lb (fun i => d i x' x) j) :=
        add_le_add ha (add_le_add hmid hb)
    _ ≤ matrix_vector_bound (fun i j => La i j + Lb i j) (fun i => d i x' x) j +
          (eps_a j + eps_b j) := hsum

/--
OET anchor: h-96c357f03b81261a
**命题 #h-96c357f03b81261a（同目标代理对的域内外距离与补域自由，域外自由度）**
Overriding a proxy at a point outside `U` preserves its fitting-ball membership
on `U`.
-/
noncomputable def override_proxy_at
    (proxy : Operator X bot) (x' y : X) : Operator X bot := by
  classical
  exact
    { func := fun x => if x = bot then bot else if x = x' then y else proxy.func x
      preserves_bot := by simp }

/--
OET anchor: h-96c357f03b81261a
**命题 #h-96c357f03b81261a（同目标代理对的域内外距离与补域自由，域外指定点值）**
If the overridden point is not the absorbing element, the constructed proxy
takes the prescribed value there.
-/
theorem override_proxy_at_value
    (proxy : Operator X bot) {x' y : X} (hx'_ne_bot : x' ≠ bot) :
    (override_proxy_at proxy x' y).func x' = y := by
  classical
  unfold override_proxy_at
  simp [hx'_ne_bot]

/--
OET anchor: h-96c357f03b81261a
**命题 #h-96c357f03b81261a（同目标代理对的域内外距离与补域自由，域内限制不变）**
The override agrees with the original proxy throughout `U` when the modified
point is outside `U`.
-/
theorem override_proxy_at_eq_on_set
    (proxy : Operator X bot) (U : Set X) {x' y : X}
    (hx'_notU : x' ∉ U) :
    ∀ x ∈ U, (override_proxy_at proxy x' y).func x = proxy.func x := by
  classical
  intro x hx
  unfold override_proxy_at
  by_cases hbot : x = bot
  · simp [hbot, proxy.preserves_bot]
  · have hx_ne : x ≠ x' := by
      intro h
      exact hx'_notU (by simpa [h] using hx)
    simp [hbot, hx_ne]

omit [Fintype I] in
/--
OET anchor: h-96c357f03b81261a
**命题 #h-96c357f03b81261a（同目标代理对的域内外距离与补域自由，域外自由度）**
Changing the proxy at a point outside `U` does not affect fitting-ball
membership measured on `U`.
-/
theorem fitting_ball_outside_free_extension
    (target proxy : Operator X bot) (U : Set X)
    (eps : I → ENNReal) {x' y : X}
    (hfit : InFullFittingBall d target proxy U eps)
    (hx'_notU : x' ∉ U) :
    InFullFittingBall d target (override_proxy_at proxy x' y) U eps := by
  refine ⟨hfit.tolerance_finite, hfit.target_dom, ?_, ?_⟩
  · intro x hx
    dsimp [dom]
    rw [override_proxy_at_eq_on_set proxy U hx'_notU x hx]
    exact hfit.proxy_dom hx
  · intro x hx j hj
    rw [override_proxy_at_eq_on_set proxy U hx'_notU x hx]
    exact hfit.error x hx j hj

omit [Fintype I] in
/--
OET anchor: h-96c357f03b81261a
**命题 #h-96c357f03b81261a（同目标代理对的域内外距离与补域自由，保定义域指定值）**
At a nonabsorbing point outside `U`, prescribing a nonabsorbing value preserves
fitting on `U` and keeps that point in the modified proxy domain.
-/
theorem fitting_ball_outside_free_value
    (target proxy : Operator X bot) (U : Set X) (eps : I → ENNReal)
    {x' y : X}
    (hfit : InFullFittingBall d target proxy U eps)
    (hx'_dom : x' ∈ dom proxy) (hx'_notU : x' ∉ U) (hy_ne_bot : y ≠ bot) :
    ∃ modified : Operator X bot,
      InFullFittingBall d target modified U eps ∧
      (∀ x ∈ U, modified.func x = proxy.func x) ∧
      x' ∈ dom modified ∧ modified.func x' = y := by
  classical
  have hx'_ne_bot : x' ≠ bot := by
    intro hx'_bot
    apply hx'_dom
    simpa [hx'_bot] using proxy.preserves_bot
  let modified := override_proxy_at proxy x' y
  have hvalue : modified.func x' = y := by
    exact override_proxy_at_value proxy hx'_ne_bot
  refine ⟨modified, ?_, ?_, ?_, hvalue⟩
  · exact fitting_ball_outside_free_extension d target proxy U eps hfit hx'_notU
  · exact override_proxy_at_eq_on_set proxy U hx'_notU
  · dsimp [dom]
    rw [hvalue]
    exact hy_ne_bot

omit [Fintype I] in
/--
OET anchor: h-96c357f03b81261a
**命题 #h-96c357f03b81261a（同目标代理对的域内外距离与补域自由，有限阈值无界）**
If every finite threshold is exceeded by a nonabsorbing prescribed value, then
every finite threshold is exceeded by a modified fitting proxy that remains
defined at `x'`.
-/
theorem fitting_ball_outside_distances_unbounded
    (target proxy : Operator X bot) (U : Set X) (eps : I → ENNReal)
    {x' : X} (j : I)
    (hfit : InFullFittingBall d target proxy U eps)
    (hx'_dom : x' ∈ dom proxy) (hx'_notU : x' ∉ U)
    (hunbounded :
      ∀ M : ENNReal, M ≠ ⊤ →
        ∃ y : X, y ≠ bot ∧ M < d j (proxy.func x') y) :
    ∀ M : ENNReal, M ≠ ⊤ →
      ∃ modified : Operator X bot,
        InFullFittingBall d target modified U eps ∧
        (∀ x ∈ U, modified.func x = proxy.func x) ∧
        x' ∈ dom modified ∧ M < d j (proxy.func x') (modified.func x') := by
  intro M hM_finite
  rcases hunbounded M hM_finite with ⟨y, hy_ne_bot, hy_large⟩
  rcases fitting_ball_outside_free_value d target proxy U eps hfit
      hx'_dom hx'_notU hy_ne_bot with
    ⟨modified, hmodified_fit, hmodified_on_U, hx'_modified_dom, hvalue⟩
  exact ⟨modified, hmodified_fit, hmodified_on_U, hx'_modified_dom,
    by simpa [hvalue] using hy_large⟩

end formal_oet.vol_02.ch_07_fitting_foundations
