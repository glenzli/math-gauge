import RegularGreen

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Filter Topology
namespace MathGauge.HilbertRegular
open HilbertCriteria
variable {E F G H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem laplacian_positive (A : E →L[ℂ] F) (B : F →L[ℂ] G) : Positive (laplacian A B) := by
  intro x
  rw [laplacian_energy]
  positivity

theorem laplacian_self_adjoint (A : E →L[ℂ] F) (B : F →L[ℂ] G) :
    (laplacian A B).adjoint=laplacian A B := by
  simp only [laplacian,map_add,ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint]

theorem laplacian_dense (A : E →L[ℂ] F) (B : F →L[ℂ] G)
    (hex : A.range.topologicalClosure=B.ker) :
    (laplacian A B).range.topologicalClosure=⊤ := by
  rw [Submodule.topologicalClosure_eq_top_iff,ContinuousLinearMap.orthogonal_range,
    laplacian_self_adjoint]
  exact LinearMap.ker_eq_bot.mpr (laplacian_injective_of_reduced_exactness A B hex)

/-- The closed-subspace argument applies to complex vectors and an arbitrary filter.
It is the uniform-boundedness/density argument used in the GR003 author source,
with the scalar field and the filter kept explicit here. -/
def vanishing {ι : Type*} (l : Filter ι) (Q : ι → F →L[ℂ] F) : Submodule ℂ F where
  carrier := {x | Tendsto (fun i => Q i x) l (𝓝 0)}
  zero_mem' := by simpa using (tendsto_const_nhds : Tendsto (fun _ : ι => (0:F)) l (𝓝 0))
  add_mem' := by intro x y hx hy; simpa using hx.add hy
  smul_mem' := by intro c x hx; simpa using hx.const_smul c

theorem vanishing_closed {ι : Type*} (l : Filter ι) (Q : ι → F →L[ℂ] F)
    {K : ℝ} (hK0 : 0≤K) (hK : ∀ i, ‖Q i‖≤K) : IsClosed (vanishing l Q : Set F) := by
  apply isClosed_of_closure_subset
  intro x hx
  apply Metric.tendsto_nhds.2
  intro ε hε
  have hδ : 0<ε/(2*(K+1)) := by positivity
  obtain ⟨y,hy,hxy⟩ := Metric.mem_closure_iff.1 hx _ hδ
  have hy' := (Metric.tendsto_nhds.1 hy) (ε/2) (by positivity)
  filter_upwards [hy'] with i hi
  rw [dist_zero_right] at hi ⊢
  have hdist : K*‖x-y‖<ε/2 := by
    rw [dist_eq_norm] at hxy
    have hn : 0≤‖x-y‖ := norm_nonneg _
    have hh := mul_lt_mul_of_pos_left hxy (show 0<K+1 by positivity)
    have he : (K+1)*(ε/(2*(K+1)))=ε/2 := by field_simp
    rw [he] at hh
    nlinarith
  have hb : ‖Q i (x-y)‖≤K*‖x-y‖ :=
    ((Q i).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hK i) (norm_nonneg _))
  have he : Q i x=Q i (x-y)+Q i y := by rw [map_sub]; abel
  rw [he]
  exact (norm_add_le _ _).trans_lt (by linarith)

theorem regularError_strong_of_dense (L : F →L[ℂ] F) (hL : Positive L)
    (hd : L.range.topologicalClosure=⊤) (x : F) :
    Tendsto (fun ε => regularError L hL ε x) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hr : L.range≤vanishing (𝓝[>] (0:ℝ)) (regularError L hL) := by
    rintro y ⟨z,rfl⟩
    exact error_range_tendsto L hL z
  have hc : L.range.topologicalClosure≤vanishing (𝓝[>] (0:ℝ)) (regularError L hL) :=
    Submodule.topologicalClosure_minimal _ hr
      (vanishing_closed _ _ (by norm_num : (0:ℝ)≤1) (regularError_bound L hL))
  rw [hd] at hc
  exact hc (show x ∈ (⊤ : Submodule ℂ F) from trivial)

theorem laplacian_regular_strong (A : E →L[ℂ] F) (B : F →L[ℂ] G)
    (hex : A.range.topologicalClosure=B.ker) (x : F) :
    Tendsto (fun ε => (1-regularError (laplacian A B) (laplacian_positive A B) ε) x)
      (𝓝[>] (0:ℝ)) (𝓝 x) := by
  have ht := regularError_strong_of_dense (laplacian A B) (laplacian_positive A B)
    (laplacian_dense A B hex) x
  simpa using tendsto_const_nhds.sub ht

theorem shifted_commutes (A : E →L[ℂ] F) (B : F →L[ℂ] G) (C : G →L[ℂ] H)
    (hBA : B.comp A=0) (hCB : C.comp B=0) (ε : ℝ) :
    B.comp (shifted (laplacian A B) ε)=(shifted (laplacian B C) ε).comp B := by
  have hc := laplacian_commutes A B C hBA hCB
  apply ContinuousLinearMap.ext
  intro x
  have hx := congrArg (fun U : F →L[ℂ] G => U x) hc
  simpa [shifted] using congrArg (fun y : G => y+(ε:ℂ) • B x) hx

theorem regular_inverse_commutes (A : E →L[ℂ] F) (B : F →L[ℂ] G) (C : G →L[ℂ] H)
    (hBA : B.comp A=0) (hCB : C.comp B=0) {ε : ℝ} (hε : 0<ε) :
    B.comp (regularGreen (laplacian A B) (laplacian_positive A B) ε)=
      (regularGreen (laplacian B C) (laplacian_positive B C) ε).comp B := by
  let U := regularGreen (laplacian A B) (laplacian_positive A B) ε
  let V := regularGreen (laplacian B C) (laplacian_positive B C) ε
  apply ContinuousLinearMap.ext
  intro x
  have he := congrArg (fun m : F →L[ℂ] G => V (m (U x))) (shifted_commutes A B C hBA hCB ε)
  have hu : shifted (laplacian A B) ε (U x)=x :=
    congrArg (fun m : F →L[ℂ] F => m x) (regular_right _ _ hε)
  have hv : V (shifted (laplacian B C) ε (B (U x)))=B (U x) :=
    congrArg (fun m : G →L[ℂ] G => m (B (U x))) (regular_left _ _ hε)
  change V (B (shifted (laplacian A B) ε (U x)))=V (shifted (laplacian B C) ε (B (U x))) at he
  rw [hu,hv] at he
  exact he.symm

theorem regular_contraction_identity (A : E →L[ℂ] F) (B : F →L[ℂ] G) (C : G →L[ℂ] H)
    (hBA : B.comp A=0) (hCB : C.comp B=0) {ε : ℝ} (hε : 0<ε) :
    A.comp (A.adjoint.comp (regularGreen (laplacian A B) (laplacian_positive A B) ε))+
      (B.adjoint.comp (regularGreen (laplacian B C) (laplacian_positive B C) ε)).comp B=
      1-regularError (laplacian A B) (laplacian_positive A B) ε := by
  have hc := regular_inverse_commutes A B C hBA hCB hε
  rw [← regular_error_identity _ _ hε]
  apply ContinuousLinearMap.ext
  intro x
  have hx := congrArg (fun U : F →L[ℂ] G => U x) hc
  change B (regularGreen (laplacian A B) (laplacian_positive A B) ε x)=
    regularGreen (laplacian B C) (laplacian_positive B C) ε (B x) at hx
  change A (A.adjoint (regularGreen (laplacian A B) (laplacian_positive A B) ε x))+
    B.adjoint (regularGreen (laplacian B C) (laplacian_positive B C) ε (B x))=
    A (A.adjoint (regularGreen (laplacian A B) (laplacian_positive A B) ε x))+
    B.adjoint (B (regularGreen (laplacian A B) (laplacian_positive A B) ε x))
  rw [← hx]

end MathGauge.HilbertRegular
