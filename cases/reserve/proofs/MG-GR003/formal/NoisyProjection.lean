import ProjectionDynamics

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Filter Topology
namespace MathGauge.OrthogonalComponents
open ErgodicOperators ErgodicRecovery

section ScalarBounds
variable {E : Type*} [NormedAddCommGroup E]

theorem half_recursion_bound (y : ℕ → E) {ε : ℝ}
    (hstep : ∀ n, ‖y (n+1)‖ ≤ (1/2:ℝ)*‖y n‖+ε) (n : ℕ) :
    ‖y n‖ ≤ (1/2:ℝ)^n*‖y 0‖ + 2*ε*(1-(1/2:ℝ)^n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hs := hstep n
    rw [pow_succ]
    nlinarith

theorem half_recursion_vanishing (y e : ℕ → E)
    (hstep : ∀ n, ‖y (n+1)‖ ≤ (1/2:ℝ)*‖y n‖+‖e n‖)
    (he : Tendsto e atTop (𝓝 0)) : Tendsto y atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp he (ε/4) (by positivity)
  have htail : ∀ n, ‖y (N+n+1)‖ ≤ (1/2:ℝ)*‖y (N+n)‖+ε/4 := by
    intro n
    have hen : ‖e (N+n)‖ < ε/4 := by simpa using hN (N+n) (Nat.le_add_right _ _)
    exact (hstep (N+n)).trans (by linarith)
  have hb (n : ℕ) : ‖y (N+n)‖ ≤ (1/2:ℝ)^n*‖y N‖ + 2*(ε/4)*(1-(1/2:ℝ)^n) := by
    simpa only [Nat.add_zero,Nat.add_assoc] using
      half_recursion_bound (fun n => y (N+n)) (by intro n; simpa only [Nat.add_assoc] using htail n) n
  have hp : Tendsto (fun n : ℕ => (1/2:ℝ)^n*‖y N‖) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0 ≤ (1/2:ℝ))
      (by norm_num : (1/2:ℝ)<1)).mul_const ‖y N‖
  obtain ⟨k,hk⟩ := eventually_atTop.mp (hp.eventually (gt_mem_nhds (by positivity : 0 < ε/2)))
  refine ⟨N+k,?_⟩
  intro m hm
  let n := m-N
  have hn : k ≤ n := by dsimp [n]; omega
  have hmn : m = N+n := by dsimp [n]; omega
  rw [hmn,dist_zero_right]
  have hpn := hk n hn
  have hbn := hb n
  have hnon : 0 ≤ (1/2:ℝ)^n := by positivity
  nlinarith
end ScalarBounds

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem projection_iteration {T S : E →L[ℝ] E} (hT : IsStarProjection T)
    (hS : IsStarProjection S) (h : Commute T S) :
    (T*S)*iteration T S = T*S ∧ iteration T S*(T*S) = T*S := by
  have hi : iteration T S*(T*S) = T*S := by
    simpa [component,side,lazyCoeff] using iteration_component hT hS h 1 (true,true)
  have hc : Commute (iteration T S) (T*S) := by
    simpa only [pow_one] using (iteration_commute_T T S h 1).mul_right (iteration_commute_S T S h 1)
  exact ⟨hc.eq.symm.trans hi,hi⟩

theorem projection_noise_invariant {T S : E →L[ℝ] E} (hT : IsStarProjection T)
    (hS : IsStarProjection S) (h : Commute T S) (x e : ℕ → E)
    (hrec : ∀ n, x (n+1) = iteration T S (x n)+e n)
    (he : ∀ n, e n ∈ differences T S) : ∀ n, (T*S) (x n) = (T*S) (x 0) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    have hen : (T*S) (e n) = 0 := by
      simpa only [differences_eq_kernel hT hS h,LinearMap.mem_ker] using he n
    rw [hrec,map_add,hen,add_zero]
    change ((T*S)*iteration T S) (x n) = (T*S) (x 0)
    rw [(projection_iteration hT hS h).1,ih]

theorem projection_noise_step {T S : E →L[ℝ] E} (hT : IsStarProjection T)
    (hS : IsStarProjection S) (h : Commute T S) (x e : ℕ → E)
    (hrec : ∀ n, x (n+1) = iteration T S (x n)+e n)
    (he : ∀ n, e n ∈ differences T S) (n : ℕ) :
    ‖x (n+1)-(T*S) (x 0)‖ ≤ (1/2:ℝ)*‖x n-(T*S) (x 0)‖+‖e n‖ := by
  let y := x n-(T*S) (x 0)
  have hy : (T*S) y = 0 := by
    rw [map_sub,projection_noise_invariant hT hS h x e hrec he]
    change (T*S) (x 0) - ((T*S)*(T*S)) (x 0) = 0
    rw [(hT.mul hS h).isIdempotentElem.eq,sub_self]
  have hr : iteration T S ((T*S) (x 0)) = (T*S) (x 0) :=
    congrArg (fun U : E →L[ℝ] E => U (x 0)) (projection_iteration hT hS h).2
  have hsplit : x (n+1)-(T*S) (x 0) = iteration T S y+e n := by
    rw [hrec]
    simp only [y,map_sub,hr]
    abel
  rw [hsplit]
  apply (norm_add_le _ _).trans
  suffices hs : ‖iteration T S y‖ ≤ (1/2:ℝ)*‖y‖ by exact add_le_add hs le_rfl
  have hn : ‖iteration T S-T*S‖ ≤ (1/2:ℝ) := by
    simpa only [pow_one] using iteration_operator_bound hT hS h 1
  have heq : iteration T S y = (iteration T S-T*S) y := by rw [ContinuousLinearMap.sub_apply,hy,sub_zero]
  rw [heq]
  exact ((iteration T S-T*S).le_opNorm y).trans
    (mul_le_mul_of_nonneg_right hn (norm_nonneg y))

theorem projection_noise_bound {T S : E →L[ℝ] E} (hT : IsStarProjection T)
    (hS : IsStarProjection S) (h : Commute T S) (x e : ℕ → E)
    (hrec : ∀ n, x (n+1) = iteration T S (x n)+e n)
    (he : ∀ n, e n ∈ differences T S) {ε : ℝ} (hb : ∀ n, ‖e n‖ ≤ ε) (n : ℕ) :
    ‖x n-(T*S) (x 0)‖ ≤ (1/2:ℝ)^n*‖x 0-(T*S) (x 0)‖ + 2*ε*(1-(1/2:ℝ)^n) := by
  refine half_recursion_bound (fun k => x k-(T*S) (x 0)) ?_ n
  intro k
  exact (projection_noise_step hT hS h x e hrec he k).trans (by linarith [hb k])

theorem projection_noise_vanishing {T S : E →L[ℝ] E} (hT : IsStarProjection T)
    (hS : IsStarProjection S) (h : Commute T S) (x e : ℕ → E)
    (hrec : ∀ n, x (n+1) = iteration T S (x n)+e n)
    (he : ∀ n, e n ∈ differences T S) (hz : Tendsto e atTop (𝓝 0)) :
    Tendsto x atTop (𝓝 ((T*S) (x 0))) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [norm_zero] using (half_recursion_vanishing (fun n => x n-(T*S) (x 0)) e
    (projection_noise_step hT hS h x e hrec he) hz).norm

end MathGauge.OrthogonalComponents
