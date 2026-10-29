import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mathlib.Tactic

noncomputable section
open Set InnerProductSpace Function
namespace MathGauge.AffineProjections
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Closed subspaces of the supplied Hilbert space have the exact complete-space
instance used below; completeness of L is not an extra mathematical assumption. -/
theorem closed_submodule_complete (L : Submodule ℝ H) (hL : IsClosed (L : Set H)) :
    CompleteSpace L := hL.completeSpace_coe

def translate (p : H) (L : Submodule ℝ H) : Set H := {z | z-p ∈ L}

def affineProject (p : H) (L : Submodule ℝ H) [L.HasOrthogonalProjection] (x : H) : H :=
  p + L.starProjection (x-p)

theorem translate_nonempty (p : H) (L : Submodule ℝ H) : (translate p L).Nonempty :=
  ⟨p,by simp [translate]⟩

theorem translate_closed (p : H) (L : Submodule ℝ H) (hL : IsClosed (L : Set H)) :
    IsClosed (translate p L) := hL.preimage (continuous_id.sub continuous_const)

theorem affineProject_mem (p : H) (L : Submodule ℝ H) [L.HasOrthogonalProjection] (x : H) :
    affineProject p L x ∈ translate p L := by
  change p + L.starProjection (x-p) - p ∈ L
  rw [add_sub_cancel_left]
  exact (L.orthogonalProjection (x-p)).property

theorem affineProject_orthogonal (p : H) (L : Submodule ℝ H) [L.HasOrthogonalProjection]
    (x z : H) (hz : z ∈ translate p L) :
    ⟪x-affineProject p L x,z-affineProject p L x⟫_ℝ = 0 := by
  have hmem : z-affineProject p L x ∈ L := by
    have : z-affineProject p L x = (z-p)-L.starProjection (x-p) := by
      simp [affineProject,sub_add_eq_sub_sub]
    rw [this]
    exact L.sub_mem hz (L.orthogonalProjection (x-p)).property
  have he : x-affineProject p L x = (x-p)-L.starProjection (x-p) := by
    simp [affineProject,sub_add_eq_sub_sub]
  rw [he]
  exact L.starProjection_inner_eq_zero _ _ hmem

theorem affineProject_pythagoras (p : H) (L : Submodule ℝ H) [L.HasOrthogonalProjection]
    (x z : H) (hz : z ∈ translate p L) :
    ‖x-z‖^2 = ‖x-affineProject p L x‖^2 + ‖affineProject p L x-z‖^2 := by
  have h := norm_sub_sq_real (x-affineProject p L x) (z-affineProject p L x)
  rw [affineProject_orthogonal p L x z hz, sub_sub_sub_cancel_right,
    norm_sub_rev z] at h
  nlinarith

theorem affineProject_nearest_unique (p : H) (L : Submodule ℝ H)
    [L.HasOrthogonalProjection] (x : H) :
    affineProject p L x ∈ translate p L ∧
    (∀ z ∈ translate p L, ‖x-affineProject p L x‖ ≤ ‖x-z‖) ∧
    ∀ z ∈ translate p L,
      ‖x-z‖ ≤ ‖x-affineProject p L x‖ → z=affineProject p L x := by
  refine ⟨affineProject_mem p L x, ?_, ?_⟩
  · intro z hz
    have h := affineProject_pythagoras p L x z hz
    nlinarith [sq_nonneg ‖affineProject p L x-z‖,norm_nonneg (x-z),
      norm_nonneg (x-affineProject p L x)]
  · intro z hz hd
    have h := affineProject_pythagoras p L x z hz
    have hn : ‖affineProject p L x-z‖=0 := by
      nlinarith [norm_nonneg (affineProject p L x-z),norm_nonneg (x-z),
        norm_nonneg (x-affineProject p L x)]
    exact (sub_eq_zero.mp (norm_eq_zero.mp hn)).symm

theorem affineProject_linear_iff (p : H) (L : Submodule ℝ H) [L.HasOrthogonalProjection] :
    (∃ T : H →ₗ[ℝ] H, (T : H → H)=affineProject p L) ↔ p ∈ L := by
  constructor
  · rintro ⟨T,hT⟩
    have h := congrFun hT 0
    simp only [map_zero,affineProject,zero_sub,map_neg] at h
    have hp : L.starProjection p=p := by
      have he : p-L.starProjection p=0 := by simpa [sub_eq_add_neg] using h.symm
      exact (sub_eq_zero.mp he).symm
    exact L.starProjection_eq_self_iff.mp hp
  · intro hp
    refine ⟨L.starProjection.toLinearMap, ?_⟩
    funext x
    simp [affineProject,map_sub,L.starProjection_eq_self_iff.mpr hp]

theorem zero_in_translate_iff (p : H) (L : Submodule ℝ H) :
    (0:H) ∈ translate p L ↔ p ∈ L := by simp [translate]

/-- A point q of the same affine set may be chosen as a common origin. -/
theorem translate_rebase (p q : H) (L : Submodule ℝ H) (hq : q ∈ translate p L) :
    translate q L = translate p L := by
  ext x
  constructor
  · intro hx
    have he : x-p=(x-q)+(q-p) := by abel
    change x-p ∈ L
    rw [he]
    exact L.add_mem hx hq
  · intro hx
    have he : x-q=(x-p)-(q-p) := by abel
    change x-q ∈ L
    rw [he]
    exact L.sub_mem hx hq

theorem translate_subset_iff (p : H) (L M : Submodule ℝ H) :
    translate p L ⊆ translate p M ↔ L ≤ M := by
  constructor
  · intro h v hv
    have hm := h (a := p+v) (by simpa [translate] using hv)
    simpa [translate] using hm
  · intro h x hx
    exact h hx

theorem nested_first (L M : Submodule ℝ H) [L.HasOrthogonalProjection]
    [M.HasOrthogonalProjection] (hML : M ≤ L) (x : H) :
    L.starProjection (M.starProjection x) = M.starProjection x :=
  L.starProjection_eq_self_iff.mpr (hML (by simp))

theorem nested_second (L M : Submodule ℝ H) [L.HasOrthogonalProjection]
    [M.HasOrthogonalProjection] (hML : M ≤ L) (x : H) :
    M.starProjection (L.starProjection x) = M.starProjection x := by
  apply M.eq_starProjection_of_mem_of_inner_eq_zero (by simp)
  intro w hw
  have hL := L.starProjection_inner_eq_zero x w (hML hw)
  have hM := M.starProjection_inner_eq_zero x w hw
  simp only [inner_sub_left] at hL hM ⊢
  linarith

theorem nested_affine_projections (p : H) (L M : Submodule ℝ H)
    [L.HasOrthogonalProjection] [M.HasOrthogonalProjection] (hML : M ≤ L) (x : H) :
    affineProject p L (affineProject p M x)=affineProject p M x ∧
    affineProject p M (affineProject p L x)=affineProject p M x ∧
    ‖x-affineProject p M x‖^2 = ‖x-affineProject p L x‖^2 +
      ‖affineProject p L x-affineProject p M x‖^2 := by
  refine ⟨?_,?_,?_⟩
  · simp [affineProject,nested_first L M hML]
  · simp [affineProject,nested_second L M hML]
  · exact affineProject_pythagoras p L x (affineProject p M x)
      ((translate_subset_iff p M L).2 hML (affineProject_mem p M x))

section Products
variable {R : Type*} [Monoid R]

theorem idempotent_absorbs_product (l : List R) (p : R) (hp : p*p=p)
    (hc : ∀ q ∈ l, Commute p q) (hm : p ∈ l) : p*l.prod=l.prod := by
  induction l with
  | nil => simp at hm
  | cons a l ih =>
    simp only [List.prod_cons]
    rcases List.mem_cons.mp hm with he | he
    · subst a
      rw [← mul_assoc,hp]
    · rw [← mul_assoc,(hc a (by simp)).eq,mul_assoc,
        ih (fun q hq => hc q (by simp [hq])) he]

end Products

theorem product_is_projection (l : List (H →L[ℝ] H))
    (hp : ∀ p ∈ l, IsStarProjection p)
    (hc : ∀ p ∈ l, ∀ q ∈ l, Commute p q) : IsStarProjection l.prod := by
  induction l with
  | nil => simpa using IsStarProjection.one (H →L[ℝ] H)
  | cons p l ih =>
    rw [List.prod_cons]
    exact (hp p (by simp)).mul
      (ih (fun q hq => hp q (by simp [hq]))
        (fun q hq z hz => hc q (by simp [hq]) z (by simp [hz])))
      (Commute.list_prod_right l p (fun q hq => hc p (by simp) q (by simp [hq])))

theorem product_fixes (l : List (H →L[ℝ] H)) (x : H)
    (hx : ∀ p ∈ l, p x=x) : l.prod x=x := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    simp only [List.prod_cons,ContinuousLinearMap.mul_apply]
    rw [ih (fun q hq => hx q (by simp [hq])),hx p (by simp)]

/-- Arbitrary finite lists, including the empty list, give the exact common
range and are invariant under every reordering. -/
theorem finite_product_range (l : List (H →L[ℝ] H))
    (hp : ∀ p ∈ l, IsStarProjection p)
    (hc : ∀ p ∈ l, ∀ q ∈ l, Commute p q) :
    IsStarProjection l.prod ∧
    LinearMap.range l.prod.toLinearMap = ⨅ p ∈ l, LinearMap.range p.toLinearMap ∧
    ∀ l', l.Perm l' → l.prod=l'.prod := by
  refine ⟨product_is_projection l hp hc, ?_, ?_⟩
  · ext x
    simp only [Submodule.mem_iInf]
    constructor
    · rintro ⟨y,rfl⟩ p hpl
      refine ⟨l.prod y,?_⟩
      have h := idempotent_absorbs_product l p (hp p hpl).isIdempotentElem
        (fun q hq => hc p hpl q hq) hpl
      exact congrArg (fun T : H →L[ℝ] H => T y) h
    · intro hx
      refine ⟨x,product_fixes l x ?_⟩
      intro p hpl
      obtain ⟨y,hy⟩ := hx p hpl
      rw [← hy]
      exact congrArg (fun T : H →L[ℝ] H => T y) (hp p hpl).isIdempotentElem
  · intro l' he
    exact he.prod_eq' (List.pairwise_iff_forall_sublist.2 (by
      intro a b hab
      exact hc a (hab.subset (by simp)) b (hab.subset (by simp))))

theorem two_projection_product_iff (p q : H →L[ℝ] H)
    (hp : IsStarProjection p) (hq : IsStarProjection q) :
    IsStarProjection (p*q) ↔ Commute p q := by
  constructor
  · intro h
    exact (IsSelfAdjoint.commute_iff hp.isSelfAdjoint hq.isSelfAdjoint).2 h.isSelfAdjoint
  · exact hp.mul hq

/-- The algebraic star-projection obtained above really is the metric
orthogonal projection onto its already identified common range. -/
theorem finite_product_actual_orthogonal (l : List (H →L[ℝ] H))
    (hp : ∀ p ∈ l, IsStarProjection p)
    (hc : ∀ p ∈ l, ∀ q ∈ l, Commute p q) :
    ∃ h : l.prod.range.HasOrthogonalProjection, l.prod=l.prod.range.starProjection :=
  isStarProjection_iff_eq_starProjection_range.mp (product_is_projection l hp hc)

theorem finite_subspace_product {n : ℕ} (L : Fin n → Submodule ℝ H)
    [∀ i, (L i).HasOrthogonalProjection]
    (hc : ∀ i j, Commute (L i).starProjection (L j).starProjection) :
    let P := (List.ofFn (fun i => (L i).starProjection)).prod
    P.range = ⨅ i, L i ∧
      (∃ h : P.range.HasOrthogonalProjection, P=P.range.starProjection) ∧
      ∀ l', (List.ofFn (fun i => (L i).starProjection)).Perm l' → P=l'.prod := by
  dsimp only
  let l := List.ofFn (fun i => (L i).starProjection)
  have hp : ∀ p ∈ l, IsStarProjection p := by
    intro p hp
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
    exact isStarProjection_starProjection
  have hcomm : ∀ p ∈ l, ∀ q ∈ l, Commute p q := by
    intro p hp q hq
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hq
    exact hc i j
  obtain ⟨_,hr,hperm⟩ := finite_product_range l hp hcomm
  refine ⟨?_,finite_product_actual_orthogonal l hp hcomm,hperm⟩
  rw [hr]
  ext x
  simp only [Submodule.mem_iInf]
  constructor
  · intro h i
    have hi := h (L i).starProjection (List.mem_ofFn.mpr ⟨i,rfl⟩)
    simpa only [Submodule.range_starProjection] using hi
  · intro h p hp
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
    simpa only [Submodule.range_starProjection] using h i

end MathGauge.AffineProjections
