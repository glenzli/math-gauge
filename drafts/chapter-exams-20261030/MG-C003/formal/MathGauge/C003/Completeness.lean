import MathGauge.C003.SourceBridge

namespace MathGauge.C003

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open formal_oet.vol_01.ch_03_operator_local_degeneracy

noncomputable section

variable {X I : Type} {bot : X}

/-- Every scale family originally defined only on nonempty sets extends to the total representation. -/
def scale_family_extension (s : I → {A : Set X // A.Nonempty} → ENNReal)
    (hm : ∀ i (A B : {A : Set X // A.Nonempty}), A.val ⊆ B.val → s i A ≤ s i B) :
    ScaleFamily X I := by
  classical
  exact
    { val := fun i A => if h : A.Nonempty then s i ⟨A,h⟩ else 0
      monotone := by
        intro i A B hA hB hAB
        simpa [hA,hB] using hm i ⟨A,hA⟩ ⟨B,hB⟩ hAB }

theorem scale_family_extension_on_nonempty
    (s : I → {A : Set X // A.Nonempty} → ENNReal)
    (hm : ∀ i (A B : {A : Set X // A.Nonempty}), A.val ⊆ B.val → s i A ≤ s i B)
    (i : I) (A : Set X) (hA : A.Nonempty) :
    scale_family_extension s hm i A = s i ⟨A,hA⟩ := by
  simp [scale_family_extension,hA]

theorem threshold_readout_unique (d : I → X → X → ENNReal)
    (φ : Operator X bot) (A : Set X) (σ : ScaleFamily X I) (τσ τN : ENNReal) (i j : I) :
    ∃! b : Bool × Bool, operator_threshold_readout d φ A σ τσ τN i j = b := by
  exact ⟨_,rfl,fun b hb => hb.symm⟩

/-- Constant-first definitions really partition every index, including an empty domain. -/
theorem component_partition_exact (d : I → X → X → ENNReal)
    (φ : Operator X bot) (U : Set X) (i : I) :
    (i ∈ ConstComponent d φ U ∨ i ∈ IdComponent d φ U ∨ i ∈ ActComponent d φ U) ∧
    ¬ (i ∈ ConstComponent d φ U ∧ i ∈ IdComponent d φ U) ∧
    ¬ (i ∈ ConstComponent d φ U ∧ i ∈ ActComponent d φ U) ∧
    ¬ (i ∈ IdComponent d φ U ∧ i ∈ ActComponent d φ U) := by
  simp only [ConstComponent, IdComponent, ActComponent, Set.mem_setOf_eq]
  tauto

/-- Each image-indexed fiber has an actual input witness. -/
theorem image_fiber_nonempty (d : I → X → X → ENNReal)
    (φ : Operator X bot) (U : Set X) (J : NonemptyFinset I)
    (hd : ∀ i x, d i x x = 0) (y : X) (hy : y ∈ φ.func '' U) :
    (ComputationalFiber d φ J U y).Nonempty := by
  rcases hy with ⟨x, hx, rfl⟩
  refine ⟨x, hx, ?_⟩
  exact (comp_pseudo_metric_eq_zero_iff d J _ _).mpr (fun j _ => hd j _)

def equality_pairs (φ : Operator X bot) (U : Set X) : Set (X × X) :=
  {p | p.1 ∈ U ∧ p.2 ∈ U ∧ φ.func p.1 = φ.func p.2}

def zero_pairs (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) : Set (X × X) :=
  {p | p.1 ∈ U ∧ p.2 ∈ U ∧ GaugeZeroRelated d (φ.func p.1) (φ.func p.2)}

theorem equality_pairs_subset_iff (φ ψ : Operator X bot) (U : Set X) :
    equality_pairs φ U ⊆ equality_pairs ψ U ↔ EqPairSetLe φ ψ U := by
  constructor
  · intro h x hx y hy he
    exact (h (show (x,y) ∈ equality_pairs φ U from ⟨hx,hy,he⟩)).2.2
  · intro h p hp; exact ⟨hp.1, hp.2.1, h _ hp.1 _ hp.2.1 hp.2.2⟩

theorem zero_pairs_subset_iff (d : I → X → X → ENNReal) (φ ψ : Operator X bot) (U : Set X) :
    zero_pairs d φ U ⊆ zero_pairs d ψ U ↔ ZeroDistPairSetLe d φ ψ U := by
  constructor
  · intro h x hx y hy he
    exact (h (show (x,y) ∈ zero_pairs d φ U from ⟨hx,hy,he⟩)).2.2
  · intro h p hp; exact ⟨hp.1, hp.2.1, h _ hp.1 _ hp.2.1 hp.2.2⟩

theorem equality_pairs_eq_iff (φ ψ : Operator X bot) (U : Set X) :
    equality_pairs φ U = equality_pairs ψ U ↔
      EqPairSetLe φ ψ U ∧ EqPairSetLe ψ φ U := by
  rw [Set.Subset.antisymm_iff, equality_pairs_subset_iff, equality_pairs_subset_iff]

theorem zero_pairs_eq_iff (d : I → X → X → ENNReal) (φ ψ : Operator X bot) (U : Set X) :
    zero_pairs d φ U = zero_pairs d ψ U ↔
      ZeroDistPairSetLe d φ ψ U ∧ ZeroDistPairSetLe d ψ φ U := by
  rw [Set.Subset.antisymm_iff, zero_pairs_subset_iff, zero_pairs_subset_iff]

/-- OET anchor: h-77b9589cc080d4f0. The pair-set and full-fiber representations agree. -/
theorem zero_pairs_fiber_iff [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (U : Set X) (x y : X) (hx : x ∈ U) :
    (x,y) ∈ zero_pairs d φ U ↔
      y ∈ ComputationalFiber d φ full_nonempty_finset U (φ.func x) := by
  simp only [zero_pairs, Set.mem_setOf_eq, ComputationalFiber,
    comp_pseudo_metric_eq_zero_iff, full_nonempty_finset, Finset.mem_univ,
    forall_const, hx, true_and, GaugeZeroRelated]
  constructor <;> rintro ⟨hy, h⟩ <;> refine ⟨hy, ?_⟩ <;> intro i
  · rw [(hd i).symm]; exact h i
  · rw [(hd i).symm]; exact h i

/-- Extending an image-domain map with `bot` outside the image adds no mathematical assumption. -/
def extend_image_map (φ : Operator X bot) (U : Set X)
    (T : {y // y ∈ φ.func '' U} → X) (y : X) : X := by
  classical
  exact if h : y ∈ φ.func '' U then T ⟨y,h⟩ else bot

theorem image_map_exists_iff (φ ψ : Operator X bot) (U : Set X) :
    (∃ T : {y // y ∈ φ.func '' U} → X,
      ∀ x (hx : x ∈ U), T ⟨φ.func x, Set.mem_image_of_mem _ hx⟩ = ψ.func x) ↔
      equality_pairs φ U ⊆ equality_pairs ψ U := by
  rw [equality_pairs_subset_iff]
  constructor
  · rintro ⟨T,hT⟩
    apply eq_pair_set_le_of_point_transform φ ψ U (extend_image_map φ U T)
    intro x hx
    simpa [extend_image_map, Set.mem_image_of_mem φ.func hx] using hT x hx
  · intro h
    refine ⟨fun y => point_transform_from_eq_pair_set φ ψ U h y.val, ?_⟩
    exact point_transform_from_eq_pair_set_spec φ ψ U h

theorem image_maps_both_directions_iff (φ ψ : Operator X bot) (U : Set X) :
    ((∃ T : {y // y ∈ φ.func '' U} → X,
      ∀ x (hx : x ∈ U), T ⟨φ.func x, Set.mem_image_of_mem _ hx⟩ = ψ.func x) ∧
     (∃ T : {y // y ∈ ψ.func '' U} → X,
      ∀ x (hx : x ∈ U), T ⟨ψ.func x, Set.mem_image_of_mem _ hx⟩ = φ.func x)) ↔
      equality_pairs φ U = equality_pairs ψ U := by
  rw [image_map_exists_iff, image_map_exists_iff, Set.Subset.antisymm_iff]

theorem image_map_lip_on_actual_image (dist : X → X → ENNReal)
    (φ ψ : Operator X bot) (U : Set X)
    (T : {y // y ∈ φ.func '' U} → X) (K L : ENNReal)
    (hK : 0 < K) (hKfin : K ≠ ⊤) (hLfin : L ≠ ⊤)
    (hφ : U ⊆ dom φ) (hψ : U ⊆ dom ψ)
    (hT : ∀ x (hx : x ∈ U), T ⟨φ.func x, Set.mem_image_of_mem _ hx⟩ = ψ.func x)
    (hco : ∀ x ∈ U, ∀ y ∈ U, K * dist x y ≤ dist (φ.func x) (φ.func y))
    (hlip : ∀ x ∈ U, ∀ y ∈ U, dist (ψ.func x) (ψ.func y) ≤ L * dist x y) :
    ∀ a b : {y // y ∈ φ.func '' U}, dist (T a) (T b) ≤ (L / K) * dist a.val b.val := by
  have h := point_transform_scalar_lip_bound_of_colip dist φ ψ U
    (extend_image_map φ U T) K L (ne_of_gt hK) hKfin hLfin hφ hψ
    (fun x hx => by simpa [extend_image_map, Set.mem_image_of_mem φ.func hx] using hT x hx)
    hco hlip
  rintro ⟨a,ha⟩ ⟨b,hb⟩
  rcases ha with ⟨x,hx,rfl⟩; rcases hb with ⟨y,hy,rfl⟩
  simpa [extend_image_map, Set.mem_image_of_mem φ.func hx,
    Set.mem_image_of_mem φ.func hy, div_eq_mul_inv, mul_comm] using h x hx y hy

theorem image_separation_pairs_equal (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (U : Set X) (hs : ImageSeparating d φ U) :
    equality_pairs φ U = zero_pairs d φ U := by
  ext p
  constructor
  · rintro ⟨hx,hy,h⟩; refine ⟨hx,hy,?_⟩; intro i; rw [h]; exact (hd i).dist_self _
  · rintro ⟨hx,hy,h⟩
    exact ⟨hx,hy,hs _ (Set.mem_image_of_mem _ hx) _ (Set.mem_image_of_mem _ hy) h⟩

theorem fiber_chain_strict_witness (d : I → X → X → ENNReal)
    (φ : Nat → Operator X bot) (U : Set X) (m r : Nat)
    (hstep : ∀ s, s < m → zero_dist_fiber_le d (φ s) (φ (s+1)) U)
    (hr : 1 ≤ r) (hrm : r ≤ m)
    (hs : zero_dist_fiber_le d (φ (r-1)) (φ r) U ∧
      ¬ zero_dist_fiber_le d (φ r) (φ (r-1)) U) :
    zero_pairs d (φ 0) U ⊆ zero_pairs d (φ m) U ∧
      ∃ p, p ∈ zero_pairs d (φ m) U ∧ p ∉ zero_pairs d (φ 0) U := by
  have h := zero_dist_fiber_chain_strict_of_strict_step d φ U m r hstep hr hrm hs
  refine ⟨(zero_pairs_subset_iff d _ _ U).mpr h.1, ?_⟩
  have hn : ¬ zero_pairs d (φ m) U ⊆ zero_pairs d (φ 0) U :=
    fun hh => h.2 ((zero_pairs_subset_iff d _ _ U).mp hh)
  exact Set.not_subset.mp hn

/-- Shrinking the evaluation domain is a pointwise result before taking the new infimum. -/
theorem pointwise_radius_domain_antitone (d : I → X → X → ENNReal)
    (φ : Operator X bot) (A B : Set X) (i : I) (J : NonemptyFinset I)
    (hBA : B ⊆ A) (y : X) :
    annihilation_radius d φ i J A y ≤ annihilation_radius d φ i J B y := by
  apply iSup_le; intro r
  apply iSup_le; intro hr
  apply iSup_le; intro hball
  apply le_iSup_of_le r
  apply le_iSup_of_le hr
  apply le_iSup_of_le (show OpenBall d i y r ∩ B ⊆ ComputationalFiber d φ J B (φ.func y) from
    fun x hx => ⟨hx.2,(hball ⟨hx.1,hBA hx.2⟩).2⟩)
  exact le_rfl

/-- Finite positive radii for the step example are exactly the stated half-open interval. -/
theorem step_admissible_radius_iff (y : ℝ)
    (hy : some y ∈ pointwise_uniform_radius_example.sample_domain)
    (r : ENNReal) (hr : FinitePositiveRadius r) :
    ({x | threshold_examples.real_distance x (some y) < r} ∩
      pointwise_uniform_radius_example.sample_domain ⊆
      {x ∈ pointwise_uniform_radius_example.sample_domain |
        threshold_examples.real_distance
          (pointwise_uniform_radius_example.step_operator.func x)
          (pointwise_uniform_radius_example.step_operator.func (some y)) = 0}) ↔
      r ≤ ENNReal.ofReal |y| := by
  constructor
  · intro h
    rw [← pointwise_uniform_radius_example.pointwise_radius_eq y hy]
    exact le_iSup_of_le r (le_iSup_of_le hr (le_iSup_of_le h le_rfl))
  · intro hrle
    rintro x ⟨hdist,hx⟩
    refine ⟨hx,?_⟩
    rcases hx with ⟨z,hz,rfl⟩
    have hycases : (-1 ≤ y ∧ y < 0) ∨ (0 < y ∧ y ≤ 1) := by
      simpa [pointwise_uniform_radius_example.sample_domain] using hy
    have hyabs : 0 < |y| := by
      rcases hycases with h | h
      · rw [abs_of_neg h.2]; linarith
      · exact lt_of_lt_of_le h.1 (le_abs_self _)
    have hclose : |z-y| < |y| :=
      (ENNReal.ofReal_lt_ofReal_iff hyabs).mp (lt_of_lt_of_le hdist hrle)
    have heq : pointwise_uniform_radius_example.step_operator.func (some z) =
        pointwise_uniform_radius_example.step_operator.func (some y) := by
      rcases hycases with h | h
      · have hzneg : z < 0 := by
          rw [abs_of_neg h.2] at hclose
          have ht := (abs_lt.mp hclose).2; linarith
        simp [pointwise_uniform_radius_example.step_operator,h.2,hzneg]
      · have hznonneg : ¬ z < 0 := by
          rw [abs_of_pos h.1] at hclose
          have ht := (abs_lt.mp hclose).1; linarith
        simp [pointwise_uniform_radius_example.step_operator,not_lt.mpr h.1.le,hznonneg]
    rw [heq]
    exact threshold_examples.real_distance_is_extended.dist_self _

end
end MathGauge.C003
