import formal_oet.vol_02.ch_07_fitting_foundations.single_step_bounds
import formal_oet.vol_01.ch_04_operator_chain_calculus.distance_recurrence
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Operations
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
OET anchor: h-f3c6356537b5c083
**命题 #h-f3c6356537b5c083（矩阵向量上界的单调性）**
The finite matrix-vector action is monotone in the vector argument.
-/
theorem matrix_vector_bound_mono
    (M : I → I → ENNReal) {v w : I → ENNReal}
    (hvw : ∀ i : I, v i ≤ w i) :
    ∀ j : I, matrix_vector_bound M v j ≤ matrix_vector_bound M w j := by
  intro j
  unfold matrix_vector_bound
  exact Finset.sum_le_sum fun i _ => by
    simpa [mul_comm] using mul_le_mul_right (hvw i) (M i j)

/--
OET anchor: h-f3c6356537b5c083
**命题 #h-f3c6356537b5c083（矩阵向量上界的加法性）**
The matrix-vector action distributes over finite componentwise addition.
-/
theorem matrix_vector_bound_add
    (M : I → I → ENNReal) (v w : I → ENNReal) :
    ∀ j : I,
      matrix_vector_bound M (fun i => v i + w i) j =
        matrix_vector_bound M v j + matrix_vector_bound M w j := by
  intro j
  unfold matrix_vector_bound
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]

/--
OET anchor: h-f3c6356537b5c083
**命题 #h-f3c6356537b5c083（仿射递推包络）**
Recursive finite-step envelope for inequalities of the form
`δ_{m+1} ≤ A_m δ_m + ε_m`.
-/
noncomputable def affine_upper_bound
    (A : Nat → I → I → ENNReal) (eps : Nat → I → ENNReal) :
    Nat → I → ENNReal
  | 0 => fun _ => 0
  | n + 1 => fun j => matrix_vector_bound (A n) (affine_upper_bound A eps n) j + eps n j

/-- The ordered product of matrices strictly after a selected error step. -/
noncomputable def ordered_suffix_matrix_product
    (A : Nat → I → I → ENNReal) (s : Nat) : Nat → I → I → ENNReal
  | 0 =>
      letI := Classical.decEq I
      matrix_id
  | k + 1 =>
      letI := Classical.decEq I
      if s < k + 1 then
        matrix_mul (A k) (ordered_suffix_matrix_product A s k)
      else
        matrix_id

/-- The explicit ordered suffix-product expansion of a finite affine recurrence. -/
noncomputable def ordered_suffix_error_sum
    (A : Nat → I → I → ENNReal) (eps : Nat → I → ENNReal)
    (k : Nat) (j : I) : ENNReal :=
  (Finset.range k).sum fun q =>
    matrix_vector_bound (ordered_suffix_matrix_product A (q + 1) k) (eps q) j

private theorem matrix_vector_bound_matrix_id
    (v : I → ENNReal) (j : I) :
    matrix_vector_bound matrix_id v j = v j := by
  classical
  simp [matrix_vector_bound, matrix_id]

private theorem matrix_vector_bound_matrix_mul
    (L₂ L₁ : I → I → ENNReal) (v : I → ENNReal) (j : I) :
    matrix_vector_bound (matrix_mul L₂ L₁) v j =
      matrix_vector_bound L₂ (matrix_vector_bound L₁ v) j := by
  classical
  unfold matrix_vector_bound matrix_mul
  calc
    (∑ i : I, (∑ q : I, L₂ q j * L₁ i q) * v i) =
        ∑ i : I, ∑ q : I, (L₂ q j * L₁ i q) * v i := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_mul]
    _ = ∑ q : I, ∑ i : I, (L₂ q j * L₁ i q) * v i := Finset.sum_comm
    _ = ∑ q : I, L₂ q j * ∑ i : I, L₁ i q * v i := by
          apply Finset.sum_congr rfl
          intro q _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [mul_assoc]

private theorem sum_matrix_vector_bound
    {alpha : Type}
    (M : I → I → ENNReal) (S : Finset alpha) (v : alpha → I → ENNReal) (j : I) :
    S.sum (fun a => matrix_vector_bound M (v a) j) =
      matrix_vector_bound M (fun i => S.sum fun a => v a i) j := by
  unfold matrix_vector_bound
  calc
    S.sum (fun a => ∑ i : I, M i j * v a i) =
        ∑ i : I, S.sum (fun a => M i j * v a i) := Finset.sum_comm
    _ = ∑ i : I, M i j * S.sum (fun a => v a i) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]

private theorem ordered_suffix_error_sum_succ
    (A : Nat → I → I → ENNReal) (eps : Nat → I → ENNReal)
    (k : Nat) (j : I) :
    ordered_suffix_error_sum A eps (k + 1) j =
      matrix_vector_bound (A k) (ordered_suffix_error_sum A eps k) j + eps k j := by
  classical
  have hold :
      (Finset.range k).sum (fun q =>
          matrix_vector_bound (ordered_suffix_matrix_product A (q + 1) (k + 1))
            (eps q) j) =
        (Finset.range k).sum (fun q =>
          matrix_vector_bound (A k)
            (matrix_vector_bound (ordered_suffix_matrix_product A (q + 1) k)
              (eps q)) j) := by
    apply Finset.sum_congr rfl
    intro q hq
    have hqk : q < k := Finset.mem_range.mp hq
    rw [ordered_suffix_matrix_product]
    simp only [if_pos (Nat.succ_lt_succ hqk)]
    exact matrix_vector_bound_matrix_mul (A k)
      (ordered_suffix_matrix_product A (q + 1) k) (eps q) j
  have hlast :
      matrix_vector_bound (ordered_suffix_matrix_product A (k + 1) (k + 1))
          (eps k) j = eps k j := by
    rw [ordered_suffix_matrix_product]
    simp only [lt_self_iff_false, ↓reduceIte]
    exact matrix_vector_bound_matrix_id (eps k) j
  unfold ordered_suffix_error_sum
  rw [Finset.sum_range_succ, hold, hlast]
  rw [sum_matrix_vector_bound]

/--
OET support: h-db404f24d5fa0541 and h-eff0f168218a98d0
The explicit ordered suffix-product sum equals the recursive affine envelope.
-/
theorem affine_upper_bound_eq_ordered_suffix_error_sum
    (A : Nat → I → I → ENNReal) (eps : Nat → I → ENNReal) :
    ∀ k : Nat, ∀ j : I,
      affine_upper_bound A eps k j = ordered_suffix_error_sum A eps k j := by
  intro k
  induction k with
  | zero =>
      intro j
      simp [affine_upper_bound, ordered_suffix_error_sum]
  | succ k ih =>
      intro j
      rw [affine_upper_bound, ordered_suffix_error_sum_succ]
      rw [show affine_upper_bound A eps k = ordered_suffix_error_sum A eps k from
        funext ih]

/--
OET anchor: h-7e8245f5a4ac1eb3
**引理 #h-7e8245f5a4ac1eb3（候选扩张域族的闭球容纳判据，多维闭球）**
The closed gauge ball determined by a component radius vector.
-/
def closed_gauge_ball (center : X) (radius : I → ENNReal) : Set X :=
  { y | ∀ i : I, d i center y ≤ radius i }

omit [Fintype I] in
/--
OET anchor: h-7e8245f5a4ac1eb3
**引理 #h-7e8245f5a4ac1eb3（候选扩张域族的闭球容纳判据，单步域包含）**
If the actual state is inside the candidate closed ball and the ball is
contained in the selected candidate extension domain, then the actual state is
in that domain.
-/
theorem state_mem_candidate_extension_domain_of_closed_ball
    (center state : X) (radius : I → ENNReal) (W : Set X)
    (hstate : state ∈ closed_gauge_ball d center radius)
    (hcover : closed_gauge_ball d center radius ⊆ W) :
    state ∈ W :=
  hcover hstate

/--
OET anchor: h-7e8245f5a4ac1eb3
**引理 #h-7e8245f5a4ac1eb3（候选扩张域族的闭球容纳判据，候选上界控制真实偏差）**
If the true deviation recurrence is dominated by the recurrence defining a
candidate envelope, then the candidate envelope bounds every step.
-/
theorem candidate_bound_controls_deviation
    (A : Nat → I → I → ENNReal) (eps delta delta_hat : Nat → I → ENNReal)
    (hinit : ∀ j : I, delta 0 j ≤ delta_hat 0 j)
    (hrec :
      ∀ m : Nat, ∀ j : I,
        delta (m + 1) j ≤ matrix_vector_bound (A m) (delta m) j + eps m j)
    (hhat :
      ∀ m : Nat, ∀ j : I,
        matrix_vector_bound (A m) (delta_hat m) j + eps m j ≤ delta_hat (m + 1) j) :
    ∀ n : Nat, ∀ j : I, delta n j ≤ delta_hat n j := by
  intro n
  induction n with
  | zero =>
      intro j
      exact hinit j
  | succ n ih =>
      intro j
      calc
        delta (n + 1) j
            ≤ matrix_vector_bound (A n) (delta n) j + eps n j := hrec n j
        _ ≤ matrix_vector_bound (A n) (delta_hat n) j + eps n j :=
            add_le_add (matrix_vector_bound_mono (A n) ih j) le_rfl
        _ ≤ delta_hat (n + 1) j := hhat n j

omit [Fintype I] in
/--
OET anchor: h-7e8245f5a4ac1eb3
**引理 #h-7e8245f5a4ac1eb3（候选扩张域族的闭球容纳判据）**
The candidate deviation bounds and closed-ball containment imply that each
proxy state lies in the selected candidate extension domain.
-/
theorem candidate_extension_containment_states
    (target_state proxy_state : Nat → X) (W : Nat → Set X)
    (delta_hat : Nat → I → ENNReal)
    (hdev :
      ∀ n : Nat, ∀ i : I,
        d i (target_state n) (proxy_state n) ≤ delta_hat n i)
    (hcover :
      ∀ n : Nat, closed_gauge_ball d (target_state n) (delta_hat n) ⊆ W n) :
    ∀ n : Nat, proxy_state n ∈ W n := by
  intro n
  exact hcover n (hdev n)

/--
OET anchor: h-7e8245f5a4ac1eb3
**引理 #h-7e8245f5a4ac1eb3（候选扩张域族的闭球容纳判据，候选包络与扩张域）**
Combining the affine candidate-envelope recurrence with closed-ball
containment gives both the deviation bound and membership in the selected
candidate extension domain.
-/
theorem candidate_envelope_controls_deviation_and_extension_domains
    (target_state proxy_state : Nat → X) (W : Nat → Set X)
    (A : Nat → I → I → ENNReal) (eps delta delta_hat : Nat → I → ENNReal)
    (hdelta_dist :
      ∀ n : Nat, ∀ i : I,
        d i (target_state n) (proxy_state n) ≤ delta n i)
    (hinit : ∀ j : I, delta 0 j ≤ delta_hat 0 j)
    (hrec :
      ∀ m : Nat, ∀ j : I,
        delta (m + 1) j ≤ matrix_vector_bound (A m) (delta m) j + eps m j)
    (hhat :
      ∀ m : Nat, ∀ j : I,
        matrix_vector_bound (A m) (delta_hat m) j + eps m j ≤ delta_hat (m + 1) j)
    (hcover :
      ∀ n : Nat, closed_gauge_ball d (target_state n) (delta_hat n) ⊆ W n) :
    (∀ n : Nat, ∀ i : I, delta n i ≤ delta_hat n i) ∧
      (∀ n : Nat, proxy_state n ∈ W n) := by
  constructor
  · exact candidate_bound_controls_deviation A eps delta delta_hat hinit hrec hhat
  · intro n
    apply hcover n
    intro i
    exact le_trans (hdelta_dist n i)
      (candidate_bound_controls_deviation A eps delta delta_hat hinit hrec hhat n i)

/--
OET anchor: h-f3c6356537b5c083
**命题（偏差累积律，代理 Lip 单步上界）**
Bridging through the proxy at the target input uses only the proxy Lip
certificate on the common safety domain. The proxy input need not lie in `U`.
-/
theorem deviation_step_upper
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot) (U W : Set X)
    (eps : I → ENNReal) (L_proxy : I → I → ENNReal)
    (hUW : U ⊆ W)
    (hfit : InFullFittingBall d target proxy U eps)
    (hLproxy : IsLipMatrix d proxy W L_proxy)
    {x_nat_prev x_prev : X}
    (hx_nat_U : x_nat_prev ∈ U)
    (hx_prev_W : x_prev ∈ W) :
    ∀ j : I,
      d j (target.func x_nat_prev) (proxy.func x_prev) ≤
        matrix_vector_bound L_proxy
          (fun i => d i x_nat_prev x_prev) j + eps j := by
  intro j
  calc
    d j (target.func x_nat_prev) (proxy.func x_prev)
        ≤ d j (target.func x_nat_prev) (proxy.func x_nat_prev) +
          d j (proxy.func x_nat_prev) (proxy.func x_prev) := (hd j).triangle _ _ _
    _ ≤ eps j + matrix_vector_bound L_proxy
          (fun i => d i x_nat_prev x_prev) j :=
      add_le_add (hfit.error x_nat_prev hx_nat_U j (Set.mem_univ j))
        (hLproxy.2 x_nat_prev (hUW hx_nat_U) x_prev hx_prev_W j)
    _ = _ := add_comm _ _

/--
OET anchor: h-f3c6356537b5c083
**命题 #h-f3c6356537b5c083（偏差累积律，全链累积递推形式）**
Iterating the one-step affine recurrence gives the finite chain envelope.  This
is the recursive Lean form of the displayed product-sum expansion in the text.
-/
theorem deviation_recurrence_bound
    (A : Nat → I → I → ENNReal) (eps delta : Nat → I → ENNReal)
    (hdelta0 : ∀ j : I, delta 0 j = 0)
    (hrec :
      ∀ m : Nat, ∀ j : I,
        delta (m + 1) j ≤ matrix_vector_bound (A m) (delta m) j + eps m j) :
    ∀ n : Nat, ∀ j : I, delta n j ≤ affine_upper_bound A eps n j := by
  intro n
  induction n with
  | zero =>
      intro j
      simp [affine_upper_bound, hdelta0 j]
  | succ n ih =>
      intro j
      calc
        delta (n + 1) j
            ≤ matrix_vector_bound (A n) (delta n) j + eps n j := hrec n j
        _ ≤ matrix_vector_bound (A n) (affine_upper_bound A eps n) j + eps n j :=
            add_le_add (matrix_vector_bound_mono (A n) ih j) le_rfl
        _ = affine_upper_bound A eps (n + 1) j := rfl

/--
OET anchor: h-7e8245f5a4ac1eb3
**引理（候选扩张域族的闭球容纳判据，代理 Lip 包络）**
Closed-ball containment proves safety-domain membership before the next
one-step estimate is applied. No proxy-domain membership is assumed.
-/
theorem candidate_proxy_trajectory_bounds
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Nat → Operator X bot)
    (U W : Nat → Set X) (eps : Nat → I → ENNReal)
    (L : Nat → I → I → ENNReal)
    (xTarget xProxy : Nat → X) (k : Nat)
    (hinitial : xTarget 0 = xProxy 0)
    (htarget_step : ∀ n, n < k → xTarget (n + 1) = (target n).func (xTarget n))
    (hproxy_step : ∀ n, n < k → xProxy (n + 1) = (proxy n).func (xProxy n))
    (hfit : ∀ n, n < k → InFullFittingBall d (target n) (proxy n) (U n) (eps n))
    (hUW : ∀ n, n < k → U n ⊆ W n)
    (hL : ∀ n, n < k → IsLipMatrix d (proxy n) (W n) (L n))
    (hxTarget : ∀ n, n < k → xTarget n ∈ U n)
    (hcover : ∀ n, n < k →
      closed_gauge_ball d (xTarget n) (affine_upper_bound L eps n) ⊆ W n) :
    (∀ n, n ≤ k → ∀ i,
      d i (xTarget n) (xProxy n) ≤ affine_upper_bound L eps n i) ∧
    (∀ n, n < k → xProxy n ∈ W n ∧ xProxy n ∈ dom (proxy n)) := by
  have hbound : ∀ n, n ≤ k → ∀ i,
      d i (xTarget n) (xProxy n) ≤ affine_upper_bound L eps n i := by
    intro n hn
    induction n with
    | zero =>
        intro i
        simpa [affine_upper_bound, hinitial] using (hd i).dist_self (xProxy 0)
    | succ n ih =>
        intro i
        have hnk : n < k := Nat.lt_of_succ_le hn
        have hprev := ih (Nat.le_of_lt hnk)
        have hxW : xProxy n ∈ W n := hcover n hnk hprev
        rw [htarget_step n hnk, hproxy_step n hnk]
        calc
          d i ((target n).func (xTarget n)) ((proxy n).func (xProxy n))
              ≤ matrix_vector_bound (L n)
                (fun j => d j (xTarget n) (xProxy n)) i + eps n i :=
            deviation_step_upper d hd (target n) (proxy n) (U n) (W n)
              (eps n) (L n) (hUW n hnk) (hfit n hnk) (hL n hnk) (hxTarget n hnk) hxW i
          _ ≤ matrix_vector_bound (L n) (affine_upper_bound L eps n) i + eps n i :=
            add_le_add (matrix_vector_bound_mono (L n) hprev i) le_rfl
          _ = affine_upper_bound L eps (n + 1) i := rfl
  refine ⟨hbound, ?_⟩
  intro n hn
  have hxW : xProxy n ∈ W n := hcover n hn (hbound n (Nat.le_of_lt hn))
  exact ⟨hxW, (hL n hn).1 hxW⟩

/--
OET anchor: h-db404f24d5fa0541
**推论 #h-db404f24d5fa0541（域内代理轨迹的链级递推，单步形式）**
When both current states lie in the fitting domain, target-side Lipschitz
propagation and the local fitting error give the in-domain recurrence.
-/
theorem in_domain_chain_step_recurrence
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot) (U : Set X)
    (eps : I → ENNReal) (L : I → I → ENNReal)
    (xTarget xProxy : X)
    (hfit : InFullFittingBall d target proxy U eps)
    (hL : IsLipMatrix d target U L)
    (hxTarget : xTarget ∈ U) (hxProxy : xProxy ∈ U) :
    ∀ j : I,
      d j (target.func xTarget) (proxy.func xProxy) ≤
        matrix_vector_bound L (fun i => d i xTarget xProxy) j + eps j := by
  intro j
  have htriangle := (hd j).triangle
    (target.func xTarget) (target.func xProxy) (proxy.func xProxy)
  have hlip :
      d j (target.func xTarget) (target.func xProxy) ≤
        matrix_vector_bound L (fun i => d i xTarget xProxy) j := by
    simpa [matrix_vector_bound] using hL.2 xTarget hxTarget xProxy hxProxy j
  have hlocal : d j (target.func xProxy) (proxy.func xProxy) ≤ eps j :=
    hfit.error xProxy hxProxy j (Set.mem_univ j)
  exact le_trans htriangle (add_le_add hlip hlocal)

/--
OET anchor: h-f3c6356537b5c083
**命题（偏差累积律，代理 Lip 全链展式）**
Only the target input must remain in the fitting domain; both inputs lie in
the safety domain carrying the proxy Lip certificate.
-/
theorem proxy_chain_deviation_accumulation
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Nat → Operator X bot)
    (U W : Nat → Set X) (eps : Nat → I → ENNReal)
    (L : Nat → I → I → ENNReal)
    (xTarget xProxy : Nat → X) (k : Nat)
    (hinitial : xTarget 0 = xProxy 0)
    (htarget_step : ∀ n : Nat, n < k →
      xTarget (n + 1) = (target n).func (xTarget n))
    (hproxy_step : ∀ n : Nat, n < k →
      xProxy (n + 1) = (proxy n).func (xProxy n))
    (hfit : ∀ n : Nat, n < k →
      InFullFittingBall d (target n) (proxy n) (U n) (eps n))
    (hUW : ∀ n : Nat, n < k → U n ⊆ W n)
    (hL : ∀ n : Nat, n < k → IsLipMatrix d (proxy n) (W n) (L n))
    (hxTarget : ∀ n : Nat, n < k → xTarget n ∈ U n)
    (hxProxy : ∀ n : Nat, n < k → xProxy n ∈ W n) :
    ∀ j : I,
      d j (xTarget k) (xProxy k) ≤ ordered_suffix_error_sum L eps k j := by
  intro j
  rw [← affine_upper_bound_eq_ordered_suffix_error_sum L eps k j]
  have hbound : ∀ n : Nat, n ≤ k → ∀ i : I,
      d i (xTarget n) (xProxy n) ≤ affine_upper_bound L eps n i := by
    intro n hn
    induction n with
    | zero =>
        intro i
        simpa [affine_upper_bound, hinitial] using (hd i).dist_self (xProxy 0)
    | succ n ih =>
        intro i
        have hnk : n < k := Nat.lt_of_succ_le hn
        rw [htarget_step n hnk, hproxy_step n hnk]
        have hstep := deviation_step_upper d hd
          (target n) (proxy n) (U n) (W n) (eps n) (L n)
          (hUW n hnk) (hfit n hnk) (hL n hnk)
          (hxTarget n hnk) (hxProxy n hnk) i
        calc
          d i ((target n).func (xTarget n)) ((proxy n).func (xProxy n))
              ≤ matrix_vector_bound (L n)
                  (fun q => d q (xTarget n) (xProxy n)) i + eps n i := hstep
          _ ≤ matrix_vector_bound (L n) (affine_upper_bound L eps n) i + eps n i :=
              add_le_add (matrix_vector_bound_mono (L n) (ih (Nat.le_of_lt hnk)) i) le_rfl
          _ = affine_upper_bound L eps (n + 1) i := rfl
  exact hbound k le_rfl j

/--
OET anchor: h-db404f24d5fa0541
**推论 #h-db404f24d5fa0541（域内代理轨迹的链级递推，全链展开）**
If every proxy input remains in its layerwise fitting domain, the terminal
deviation is bounded by the ordered suffix-product error sum.
-/
theorem in_domain_chain_deviation_accumulation
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Nat → Operator X bot)
    (U : Nat → Set X) (eps : Nat → I → ENNReal)
    (L : Nat → I → I → ENNReal)
    (xTarget xProxy : Nat → X) (k : Nat)
    (hinitial : xTarget 0 = xProxy 0)
    (htarget_step : ∀ n : Nat, n < k →
      xTarget (n + 1) = (target n).func (xTarget n))
    (hproxy_step : ∀ n : Nat, n < k →
      xProxy (n + 1) = (proxy n).func (xProxy n))
    (hfit : ∀ n : Nat, n < k →
      InFullFittingBall d (target n) (proxy n) (U n) (eps n))
    (hL : ∀ n : Nat, n < k → IsLipMatrix d (target n) (U n) (L n))
    (hxTarget : ∀ n : Nat, n < k → xTarget n ∈ U n)
    (hxProxy : ∀ n : Nat, n < k → xProxy n ∈ U n) :
    ∀ j : I,
      d j (xTarget k) (xProxy k) ≤ ordered_suffix_error_sum L eps k j := by
  intro j
  rw [← affine_upper_bound_eq_ordered_suffix_error_sum L eps k j]
  have hbound : ∀ n : Nat, n ≤ k → ∀ i : I,
      d i (xTarget n) (xProxy n) ≤ affine_upper_bound L eps n i := by
    intro n hn
    induction n with
    | zero =>
        intro i
        simpa [affine_upper_bound, hinitial] using (hd i).dist_self (xProxy 0)
    | succ n ih =>
        intro i
        have hnk : n < k := Nat.lt_of_succ_le hn
        rw [htarget_step n hnk, hproxy_step n hnk]
        have hstep := in_domain_chain_step_recurrence d hd
          (target n) (proxy n) (U n) (eps n) (L n)
          (xTarget n) (xProxy n) (hfit n hnk) (hL n hnk)
          (hxTarget n hnk) (hxProxy n hnk) i
        calc
          d i ((target n).func (xTarget n)) ((proxy n).func (xProxy n))
              ≤ matrix_vector_bound (L n)
                  (fun q => d q (xTarget n) (xProxy n)) i + eps n i := hstep
          _ ≤ matrix_vector_bound (L n) (affine_upper_bound L eps n) i + eps n i :=
              add_le_add (matrix_vector_bound_mono (L n) (ih (Nat.le_of_lt hnk)) i) le_rfl
          _ = affine_upper_bound L eps (n + 1) i := rfl
  exact hbound k le_rfl j

/--
OET anchor: h-f16fadfe318d0dbb
**注 #h-f16fadfe318d0dbb（误差支撑的通道传播）**
If a finite component set contains the support of an error vector, the
matrix-vector contribution can be restricted to that set.
-/
theorem matrix_vector_bound_eq_sum_over_support_superset
    (M : I → I → ENNReal) (eps : I → ENNReal) (S : Finset I) (j : I)
    (hsupport : ∀ i : I, i ∉ S → eps i = 0) :
    matrix_vector_bound M eps j = ∑ i ∈ S, M i j * eps i := by
  classical
  unfold matrix_vector_bound
  exact (Finset.sum_subset (Finset.subset_univ S) (fun i _hi his => by
    simp [hsupport i his])).symm

/--
OET anchor: h-f16fadfe318d0dbb
**注 #h-f16fadfe318d0dbb（误差支撑的通道传播）**
The chain-level upper bound only receives contributions from supported error
components through the corresponding matrix channels.  Lean indexes the finite
chain by `Finset.range k`; this is the zero-based version of the text's
`m = 1, ..., k` notation.
-/
theorem chain_error_support_channel_bound
    (A : Nat → I → I → ENNReal) (eps : Nat → I → ENNReal)
    (delta_upper : I → ENNReal) (S : Nat → Finset I) (k : Nat)
    (hupper :
      ∀ j : I,
        delta_upper j ≤
          ∑ m ∈ Finset.range k, matrix_vector_bound (A m) (eps m) j)
    (hsupport : ∀ m : Nat, ∀ i : I, i ∉ S m → eps m i = 0) :
    ∀ j : I,
      delta_upper j ≤
        ∑ m ∈ Finset.range k, ∑ i ∈ S m, A m i j * eps m i := by
  intro j
  calc
    delta_upper j
        ≤ ∑ m ∈ Finset.range k, matrix_vector_bound (A m) (eps m) j := hupper j
    _ = ∑ m ∈ Finset.range k, ∑ i ∈ S m, A m i j * eps m i := by
      apply Finset.sum_congr rfl
      intro m _hm
      exact matrix_vector_bound_eq_sum_over_support_superset
        (M := A m) (eps := eps m) (S := S m) (j := j) (hsupport m)

/--
OET anchor: h-f16fadfe318d0dbb
**注 #h-f16fadfe318d0dbb（误差支撑的通道传播）**
If every supported component has zero channel into a fixed output component,
the corresponding chain-level upper bound is zero.
-/
theorem chain_error_zero_of_support_channels_zero
    (A : Nat → I → I → ENNReal) (eps : Nat → I → ENNReal)
    (delta_upper : I → ENNReal) (S : Nat → Finset I) (k : Nat) (j : I)
    (hupper :
      ∀ j : I,
        delta_upper j ≤
          ∑ m ∈ Finset.range k, matrix_vector_bound (A m) (eps m) j)
    (hsupport : ∀ m : Nat, ∀ i : I, i ∉ S m → eps m i = 0)
    (hzero : ∀ m ∈ Finset.range k, ∀ i ∈ S m, A m i j = 0) :
    delta_upper j = 0 := by
  have hle : delta_upper j ≤
      ∑ m ∈ Finset.range k, ∑ i ∈ S m, A m i j * eps m i :=
    chain_error_support_channel_bound A eps delta_upper S k hupper hsupport j
  have hsum_zero :
      (∑ m ∈ Finset.range k, ∑ i ∈ S m, A m i j * eps m i) = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    apply Finset.sum_eq_zero
    intro i hi
    simp [hzero m hm i hi]
  exact le_antisymm (by simpa [hsum_zero] using hle) (zero_le _)

/--
OET anchor: h-eff0f168218a98d0
**命题（逐层替换链的偏差累积律，选择层的单步上界）**
The selected layer contributes its own Lip matrix, and only a proxy layer
contributes the fitting tolerance.
-/
theorem layerwise_substitution_step_upper
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot) (U W : Set X)
    (eps : I → ENNReal) (L_natural L_proxy : I → I → ENNReal)
    (replace : Bool) (hUW : U ⊆ W)
    (hfit : InFullFittingBall d target proxy U eps)
    (hLnat : replace = false → IsLipMatrix d target W L_natural)
    (hLproxy : replace = true → IsLipMatrix d proxy W L_proxy)
    {x_nat_prev x_prev : X}
    (hx_nat_U : x_nat_prev ∈ U) (hx_prev_W : x_prev ∈ W) :
    ∀ j : I,
      d j (target.func x_nat_prev) ((if replace then proxy else target).func x_prev) ≤
        matrix_vector_bound (if replace then L_proxy else L_natural)
          (fun i => d i x_nat_prev x_prev) j + (if replace then eps j else 0) := by
  cases replace with
  | false =>
      intro j
      simpa using (hLnat rfl).2 x_nat_prev (hUW hx_nat_U) x_prev hx_prev_W j
  | true =>
      exact deviation_step_upper d hd target proxy U W eps L_proxy
        hUW hfit (hLproxy rfl) hx_nat_U hx_prev_W

/--
OET anchor: h-eff0f168218a98d0
**命题 #h-eff0f168218a98d0（逐层替换链的偏差累积律，递推包络）**
For a fixed mixed-choice chain, the stepwise matrix recurrence with the
choice-dependent excitation term yields the finite affine envelope.
-/
theorem layerwise_substitution_chain_deviation_accumulation
    (A : Nat → I → I → ENNReal) (b delta : Nat → I → ENNReal)
    (hdelta0 : ∀ j : I, delta 0 j = 0)
    (hrec :
      ∀ m : Nat, ∀ j : I,
        delta (m + 1) j ≤ matrix_vector_bound (A m) (delta m) j + b m j) :
    ∀ n : Nat, ∀ j : I, delta n j ≤ affine_upper_bound A b n j :=
  deviation_recurrence_bound A b delta hdelta0 hrec

/--
OET anchor: h-eff0f168218a98d0
**命题 #h-eff0f168218a98d0（逐层替换链的偏差累积律，全目标零激励退化）**
If every step has zero excitation, the recurrence envelope is identically zero.
This formalizes the all-target-chain degeneration in which the mixed chain
coincides with the target chain.
-/
theorem affine_upper_bound_zero_excitation
    (A : Nat → I → I → ENNReal) :
    ∀ n : Nat, ∀ j : I, affine_upper_bound A (fun _ _ => 0) n j = 0 := by
  intro n
  induction n with
  | zero =>
      intro j
      simp [affine_upper_bound]
  | succ n ih =>
      intro j
      simp [affine_upper_bound, ih, matrix_vector_bound]

/--
OET anchor: h-eff0f168218a98d0
**命题 #h-eff0f168218a98d0（逐层替换链的偏差累积律，全目标零偏差）**
With zero initial deviation and zero excitation at every step, the mixed-chain
deviation is identically zero.
-/
theorem layerwise_substitution_chain_zero_deviation
    (A : Nat → I → I → ENNReal) (delta : Nat → I → ENNReal)
    (hdelta0 : ∀ j : I, delta 0 j = 0)
    (hrec :
      ∀ m : Nat, ∀ j : I,
        delta (m + 1) j ≤ matrix_vector_bound (A m) (delta m) j + 0) :
    ∀ n : Nat, ∀ j : I, delta n j = 0 := by
  intro n j
  apply le_antisymm
  · calc
      delta n j ≤ affine_upper_bound A (fun _ _ => 0) n j :=
        layerwise_substitution_chain_deviation_accumulation
          A (fun _ _ => 0) delta hdelta0 hrec n j
      _ = 0 := affine_upper_bound_zero_excitation A n j
  · exact zero_le _

omit [Fintype I] in
/--
OET anchor: h-f3c6356537b5c083
**命题（偏差累积律，代理零化截断）**
A zero proxy bridge leaves only the local error at the target input.
-/
theorem deviation_step_zeroing_upper
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot) (U : Set X)
    (eps : I → ENNReal) (hfit : InFullFittingBall d target proxy U eps)
    {x_nat_prev x_prev : X} (hx_nat_U : x_nat_prev ∈ U) (j : I)
    (hzero_bridge : d j (proxy.func x_nat_prev) (proxy.func x_prev) = 0) :
    d j (target.func x_nat_prev) (proxy.func x_prev) ≤ eps j := by
  calc
    d j (target.func x_nat_prev) (proxy.func x_prev)
        ≤ d j (target.func x_nat_prev) (proxy.func x_nat_prev) +
          d j (proxy.func x_nat_prev) (proxy.func x_prev) := (hd j).triangle _ _ _
    _ = d j (target.func x_nat_prev) (proxy.func x_nat_prev) := by rw [hzero_bridge, add_zero]
    _ ≤ eps j := hfit.error x_nat_prev hx_nat_U j (Set.mem_univ j)

omit [Fintype I] in
private theorem bridge_zero_of_lt_min_radius
    (op : Operator X bot) (W : Set X) (i j : I) (x y : X)
    (hx : x ∈ W) (hy : y ∈ W)
    (hlt : d i x y < metric_min_annihilation_radius (d i) (d j) op W) :
    d j (op.func x) (op.func y) = 0 := by
  apply output_zero_of_lt_metric_annihilation_radius (d i) (d j) op W x y hx
  exact lt_of_lt_of_le hlt (iInf₂_le y hy)

omit [Fintype I] in
/--
OET anchor: h-f3c6356537b5c083
**命题（偏差累积律，代理零化半径条件）**
The strict radius hypothesis constructs the zero bridge used above.
-/
theorem deviation_step_upper_of_lt_proxy_radius
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot) (U W : Set X)
    (eps : I → ENNReal) (hfit : InFullFittingBall d target proxy U eps)
    (hUW : U ⊆ W) {x_nat_prev x_prev : X}
    (hx_nat_U : x_nat_prev ∈ U) (hx_prev_W : x_prev ∈ W) (i j : I)
    (hlt : d i x_nat_prev x_prev <
      metric_min_annihilation_radius (d i) (d j) proxy W) :
    d j (proxy.func x_nat_prev) (proxy.func x_prev) = 0 ∧
      d j (target.func x_nat_prev) (proxy.func x_prev) ≤ eps j := by
  have hz := bridge_zero_of_lt_min_radius d proxy W i j x_nat_prev x_prev
    (hUW hx_nat_U) hx_prev_W hlt
  exact ⟨hz, deviation_step_zeroing_upper d hd target proxy U eps hfit hx_nat_U j hz⟩

omit [Fintype I] in
/--
OET anchor: h-f3c6356537b5c083
**命题（偏差累积律，拟合域内的目标零化条件）**
Target-side zeroing requires the proxy input to remain in the fitting domain.
-/
theorem deviation_step_upper_of_lt_target_radius
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot) (U W : Set X)
    (eps : I → ENNReal) (hfit : InFullFittingBall d target proxy U eps)
    (hUW : U ⊆ W) {x_nat_prev x_prev : X}
    (hx_nat_U : x_nat_prev ∈ U) (hx_prev_U : x_prev ∈ U) (i j : I)
    (hlt : d i x_nat_prev x_prev <
      metric_min_annihilation_radius (d i) (d j) target W) :
    d j (target.func x_nat_prev) (proxy.func x_prev) ≤ eps j := by
  have hz := bridge_zero_of_lt_min_radius d target W i j x_nat_prev x_prev
    (hUW hx_nat_U) (hUW hx_prev_U) hlt
  calc
    d j (target.func x_nat_prev) (proxy.func x_prev)
        ≤ d j (target.func x_nat_prev) (target.func x_prev) +
          d j (target.func x_prev) (proxy.func x_prev) := (hd j).triangle _ _ _
    _ = d j (target.func x_prev) (proxy.func x_prev) := by rw [hz, zero_add]
    _ ≤ eps j := hfit.error x_prev hx_prev_U j (Set.mem_univ j)

omit [Fintype I] in
/--
OET anchor: h-f3c6356537b5c083
**命题 #h-f3c6356537b5c083（偏差累积律，域内化简）**
If the proxy state remains in the fitting domain, the current step is controlled
directly by the local fitting tolerance.
-/
theorem deviation_step_in_domain_upper
    (target proxy : Operator X bot) (U : Set X)
    (eps : I → ENNReal)
    (hfit : InFullFittingBall d target proxy U eps)
    {x_prev : X} (hx_prev_U : x_prev ∈ U) :
    ∀ j : I, d j (target.func x_prev) (proxy.func x_prev) ≤ eps j := by
  intro j
  exact hfit.error x_prev hx_prev_U j (Set.mem_univ j)

/--
OET anchor: h-e6b35b7b528f8ebe
**命题 #h-e6b35b7b528f8ebe（co-Lip 偏差保留的加法侧证书，代理侧）**
The proxy co-Lip lower bound yields the additive-side recurrence
`K δ_prev ≤ δ_next + eps`.
-/
theorem proxy_colip_additive_step
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot) (U W : Set X)
    (eps : I → ENNReal) (K_proxy : I → I → ENNReal)
    (hfit : InFullFittingBall d target proxy U eps)
    (hKproxy : IsCoLipMatrix d proxy W K_proxy)
    {x_nat_prev x_prev : X}
    (hx_nat_U : x_nat_prev ∈ U)
    (hx_nat_W : x_nat_prev ∈ W)
    (hx_prev_W : x_prev ∈ W) :
    ∀ j : I,
      matrix_vector_bound K_proxy (fun i => d i x_nat_prev x_prev) j ≤
        d j (target.func x_nat_prev) (proxy.func x_prev) + eps j := by
  intro j
  have hcolip :
      matrix_vector_bound K_proxy (fun i => d i x_nat_prev x_prev) j ≤
        d j (proxy.func x_nat_prev) (proxy.func x_prev) := by
    simpa [matrix_vector_bound] using
      hKproxy.2.2 x_nat_prev hx_nat_W x_prev hx_prev_W j
  have htri :=
    (hd j).triangle (proxy.func x_nat_prev)
      (target.func x_nat_prev) (proxy.func x_prev)
  have hfit' : d j (proxy.func x_nat_prev) (target.func x_nat_prev) ≤ eps j := by
    rw [(hd j).symm (proxy.func x_nat_prev) (target.func x_nat_prev)]
    exact hfit.error x_nat_prev hx_nat_U j (Set.mem_univ j)
  have hupper :
      d j (proxy.func x_nat_prev) (proxy.func x_prev) ≤
        eps j + d j (target.func x_nat_prev) (proxy.func x_prev) :=
    le_trans htri (add_le_add_left hfit' _)
  calc
    matrix_vector_bound K_proxy (fun i => d i x_nat_prev x_prev) j
        ≤ d j (proxy.func x_nat_prev) (proxy.func x_prev) := hcolip
    _ ≤ eps j + d j (target.func x_nat_prev) (proxy.func x_prev) := hupper
    _ = d j (target.func x_nat_prev) (proxy.func x_prev) + eps j := by
        rw [add_comm]

/--
OET anchor: h-e6b35b7b528f8ebe
**命题 #h-e6b35b7b528f8ebe（co-Lip 偏差保留的加法侧证书，目标侧）**
When the proxy state remains in the fitting domain, the target co-Lip lower
bound also gives the additive-side recurrence.
-/
theorem target_colip_additive_step
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot) (U W : Set X)
    (eps : I → ENNReal) (K_target : I → I → ENNReal)
    (hfit : InFullFittingBall d target proxy U eps)
    (hKtarget : IsCoLipMatrix d target W K_target)
    {x_nat_prev x_prev : X}
    (hx_nat_W : x_nat_prev ∈ W)
    (hx_prev_W : x_prev ∈ W)
    (hx_prev_U : x_prev ∈ U) :
    ∀ j : I,
      matrix_vector_bound K_target (fun i => d i x_nat_prev x_prev) j ≤
        d j (target.func x_nat_prev) (proxy.func x_prev) + eps j := by
  intro j
  have hcolip :
      matrix_vector_bound K_target (fun i => d i x_nat_prev x_prev) j ≤
        d j (target.func x_nat_prev) (target.func x_prev) := by
    simpa [matrix_vector_bound] using
      hKtarget.2.2 x_nat_prev hx_nat_W x_prev hx_prev_W j
  have htri :=
    (hd j).triangle (target.func x_nat_prev)
      (proxy.func x_prev) (target.func x_prev)
  have hfit' : d j (proxy.func x_prev) (target.func x_prev) ≤ eps j := by
    rw [(hd j).symm (proxy.func x_prev) (target.func x_prev)]
    exact hfit.error x_prev hx_prev_U j (Set.mem_univ j)
  have hupper :
      d j (target.func x_nat_prev) (target.func x_prev) ≤
        d j (target.func x_nat_prev) (proxy.func x_prev) + eps j :=
    le_trans htri (add_le_add le_rfl hfit')
  exact le_trans hcolip hupper

/--
OET anchor: h-e6b35b7b528f8ebe
**命题 #h-e6b35b7b528f8ebe（co-Lip 偏差保留的加法侧证书，有限项实数余量）**
An additive co-Lip certificate may be converted to a positive real difference
only after the propagated term and the tolerance are both known to be finite.
-/
theorem colip_additive_step_finite_positive_margin
    (propagated deviation tolerance : ENNReal)
    (hcert : propagated ≤ deviation + tolerance)
    (hpropagated_finite : propagated ≠ ⊤)
    (htolerance_finite : tolerance ≠ ⊤)
    (hstrict : tolerance < propagated) :
    (propagated - tolerance).toReal =
        propagated.toReal - tolerance.toReal ∧
      0 < propagated - tolerance ∧
      propagated - tolerance ≠ ⊤ ∧
      propagated - tolerance ≤ deviation := by
  have _ := htolerance_finite
  have htolerance_le : tolerance ≤ propagated := le_of_lt hstrict
  refine ⟨ENNReal.toReal_sub_of_le htolerance_le hpropagated_finite, ?_, ?_, ?_⟩
  · exact tsub_pos_iff_lt.mpr hstrict
  · exact ENNReal.sub_ne_top hpropagated_finite
  · exact tsub_le_iff_right.mpr hcert

/--
OET anchor: h-e6b35b7b528f8ebe
**命题 #h-e6b35b7b528f8ebe（co-Lip 偏差保留的加法侧证书，全步量词）**
Zero-based Lean form of the text's quantification over every
`m = 1, ..., k` and every component `j` on the proxy side.
-/
theorem proxy_colip_additive_steps
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Nat → Operator X bot)
    (U W : Nat → Set X) (eps : Nat → I → ENNReal)
    (K_proxy : Nat → I → I → ENNReal)
    (x_natural x_proxy : Nat → X) (k : Nat)
    (hfit :
      ∀ m : Nat, m < k →
        InFullFittingBall d (target m) (proxy m) (U m) (eps m))
    (hKproxy :
      ∀ m : Nat, m < k → IsCoLipMatrix d (proxy m) (W m) (K_proxy m))
    (hx_natural_U : ∀ m : Nat, m < k → x_natural m ∈ U m)
    (hx_natural_W : ∀ m : Nat, m < k → x_natural m ∈ W m)
    (hx_proxy_W : ∀ m : Nat, m < k → x_proxy m ∈ W m) :
    ∀ m : Nat, m < k → ∀ j : I,
      matrix_vector_bound (K_proxy m)
          (fun i => d i (x_natural m) (x_proxy m)) j ≤
        d j ((target m).func (x_natural m)) ((proxy m).func (x_proxy m)) +
          eps m j := by
  intro m hm
  exact proxy_colip_additive_step d hd (target m) (proxy m) (U m) (W m)
    (eps m) (K_proxy m) (hfit m hm) (hKproxy m hm)
    (hx_natural_U m hm) (hx_natural_W m hm) (hx_proxy_W m hm)

/--
OET anchor: h-e6b35b7b528f8ebe
**命题 #h-e6b35b7b528f8ebe（co-Lip 偏差保留的加法侧证书，全步量词，目标侧）**
Zero-based all-step and all-component form of the target-side recurrence.
-/
theorem target_colip_additive_steps
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Nat → Operator X bot)
    (U W : Nat → Set X) (eps : Nat → I → ENNReal)
    (K_target : Nat → I → I → ENNReal)
    (x_natural x_proxy : Nat → X) (k : Nat)
    (hfit :
      ∀ m : Nat, m < k →
        InFullFittingBall d (target m) (proxy m) (U m) (eps m))
    (hKtarget :
      ∀ m : Nat, m < k → IsCoLipMatrix d (target m) (W m) (K_target m))
    (hx_natural_W : ∀ m : Nat, m < k → x_natural m ∈ W m)
    (hx_proxy_W : ∀ m : Nat, m < k → x_proxy m ∈ W m)
    (hx_proxy_U : ∀ m : Nat, m < k → x_proxy m ∈ U m) :
    ∀ m : Nat, m < k → ∀ j : I,
      matrix_vector_bound (K_target m)
          (fun i => d i (x_natural m) (x_proxy m)) j ≤
        d j ((target m).func (x_natural m)) ((proxy m).func (x_proxy m)) +
          eps m j := by
  intro m hm
  exact target_colip_additive_step d hd (target m) (proxy m) (U m) (W m)
    (eps m) (K_target m) (hfit m hm) (hKtarget m hm)
    (hx_natural_W m hm) (hx_proxy_W m hm) (hx_proxy_U m hm)

end formal_oet.vol_02.ch_07_fitting_foundations
