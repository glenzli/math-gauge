import RealizationCompactness
import VendoredSuspension

/-!
The actual realization is the quotient of the disjoint union of its deletion
and the cylinder on its link. The cylinder parametrizes the closed star by
ordinary barycentric cone coordinates. Compactness supplies the quotient
topology, including after product with the homotopy interval.
-/

noncomputable section

open Finset Set ContinuousMap

namespace MathGauge.PublicProof.Topology

section Descent

variable {A X Y : Type*} [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace Y]

/-- Descent along a proved quotient map, with its actual fiber compatibility. -/
def descend_map (p : C(A, X)) (hp : Topology.IsQuotientMap p) (f : C(A, Y))
    (hf : ∀ a b, p a = p b → f a = f b) : C(X, Y) := by
  let g : X → Y := fun x => f (hp.surjective x).choose
  have hg : ∀ a, g (p a) = f a := fun a =>
    hf _ a (hp.surjective (p a)).choose_spec
  refine ⟨g, hp.continuous_iff.mpr ?_⟩
  convert f.continuous using 1
  funext a
  exact hg a

@[simp] theorem descend_map_apply (p : C(A, X)) (hp : Topology.IsQuotientMap p)
    (f : C(A, Y)) (hf : ∀ a b, p a = p b → f a = f b) (a : A) :
    descend_map p hp f hf (p a) = f a :=
  hf _ a (hp.surjective (p a)).choose_spec

end Descent

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
theorem vertex_link_le_deletion (K : PreAbstractSimplicialComplex V) (v : V) :
    vertex_link K v ≤ deletion K v := by
  intro s hs
  exact ⟨(K.isRelLowerSet_faces hs.2.2).2 (subset_insert v s) hs.1, hs.2.1⟩

def deletion_to_realization (K : PreAbstractSimplicialComplex V) (v : V) :
    C(Realization (deletion K v), Realization K) :=
  ⟨fun x => (deletion_inclusion K v x).1,
    continuous_subtype_val.comp (continuous_deletion_inclusion K v)⟩

def link_to_deletion (K : PreAbstractSimplicialComplex V) (v : V) :
    C(Realization (vertex_link K v), Realization (deletion K v)) where
  toFun x := ⟨x.1, x.2.1, by
    obtain ⟨s, hs, hsupport⟩ := x.2.2
    exact ⟨s, vertex_link_le_deletion K v hs, hsupport⟩⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

@[simp] theorem link_coordinate_zero (K : PreAbstractSimplicialComplex V) (v : V)
    (x : Realization (vertex_link K v)) : x.1 v = 0 :=
  (mem_carrier_deletion_iff.mp (link_to_deletion K v x).2).2

def link_cone_point (K : PreAbstractSimplicialComplex V) (v : V)
    (t : unitInterval) (x : Realization (vertex_link K v)) : Realization K := by
  let y : V → ℝ := fun u =>
    (1 - (t : ℝ)) * x.1 u + (t : ℝ) * (Pi.single v (1 : ℝ) : V → ℝ) u
  refine ⟨y, ⟨?_, ?_⟩, ?_⟩
  · intro u
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr t.2.2) (coordinate_nonneg x u))
      (mul_nonneg t.2.1 ((single_mem_stdSimplex ℝ v).1 u))
  · dsimp [y]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      coordinates_sum x, (single_mem_stdSimplex ℝ v).2]
    ring
  · obtain ⟨s, hs, hsupport⟩ := x.2.2
    refine ⟨insert v s, hs.2.2, ?_⟩
    intro u hu
    have huv : u ≠ v := fun h => hu (h ▸ mem_insert_self v s)
    have hus : u ∉ s := fun h => hu (mem_insert_of_mem h)
    simp [y, hsupport u hus, Pi.single_eq_of_ne huv]

def link_cone_map (K : PreAbstractSimplicialComplex V) (v : V) :
    C(unitInterval × Realization (vertex_link K v), Realization K) where
  toFun p := link_cone_point K v p.1 p.2
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro u
    have ht : Continuous (fun p : unitInterval × Realization (vertex_link K v) => (p.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    exact ((continuous_const.sub ht).mul
      ((continuous_apply u).comp (continuous_subtype_val.comp continuous_snd))).add
      (ht.mul continuous_const)

@[simp] theorem link_cone_coordinate (K : PreAbstractSimplicialComplex V) (v : V)
    (t : unitInterval) (x : Realization (vertex_link K v)) :
    (link_cone_point K v t x).1 v = (t : ℝ) := by
  simp [link_cone_point]

@[simp] theorem link_cone_zero (K : PreAbstractSimplicialComplex V) (v : V)
    (x : Realization (vertex_link K v)) :
    link_cone_point K v 0 x = deletion_to_realization K v (link_to_deletion K v x) := by
  apply Subtype.ext
  funext u
  simp [link_cone_point, deletion_to_realization, deletion_inclusion, link_to_deletion]

@[simp] theorem link_cone_one (K : PreAbstractSimplicialComplex V) (v : V)
    (x y : Realization (vertex_link K v)) :
    link_cone_point K v 1 x = link_cone_point K v 1 y := by
  apply Subtype.ext
  simp [link_cone_point]

theorem link_cone_eq_iff (K : PreAbstractSimplicialComplex V) (v : V)
    (t s : unitInterval) (x y : Realization (vertex_link K v)) :
    link_cone_point K v t x = link_cone_point K v s y ↔ t = s ∧ (t = 1 ∨ x = y) := by
  constructor
  · intro h
    have ht : t = s := Subtype.ext (by
      have hh := congrArg (fun z : Realization K => z.1 v) h
      simpa using hh)
    subst s
    refine ⟨rfl, ?_⟩
    by_cases h₁ : t = 1
    · exact Or.inl h₁
    · right
      have hn : 1 - (t : ℝ) ≠ 0 := by
        intro hz
        apply h₁
        apply Subtype.ext
        change (t : ℝ) = 1
        linarith
      apply Subtype.ext
      funext u
      have hh := congrArg (fun z : Realization K => z.1 u) h
      change (1 - (t : ℝ)) * x.1 u + _ = (1 - (t : ℝ)) * y.1 u + _ at hh
      exact mul_left_cancel₀ hn (add_right_cancel hh)
  · rintro ⟨rfl, rfl | rfl⟩
    · exact link_cone_one K v x y
    · rfl

/-- Away from both deletion and apex, radial normalization lands in the actual link. -/
def radial_link {K : PreAbstractSimplicialComplex V} {v : V}
    (x : Punctured K v) (hx : 0 < x.1.1 v) : Realization (vertex_link K v) := by
  refine ⟨radial_coordinates v x.1.1, ?_⟩
  have hr := radial_coordinates_mem x
  obtain ⟨s, hs, hsupport⟩ := x.1.2.2
  have hvs : v ∈ s := by
    by_contra hv
    have hz := hsupport v hv
    linarith
  have hr_support : ∀ u, u ∉ s.erase v → radial_coordinates v x.1.1 u = 0 := by
    intro u hu
    by_cases huv : u = v
    · simp [radial_coordinates, huv]
    · have hus : u ∉ s := fun hus => hu (mem_erase.mpr ⟨huv, hus⟩)
      simp [radial_coordinates, huv, hsupport u hus]
  have hne : (s.erase v).Nonempty := by
    by_contra hn
    have he := Finset.not_nonempty_iff_eq_empty.mp hn
    have hz : ∑ u, radial_coordinates v x.1.1 u = 0 :=
      Finset.sum_eq_zero fun u _ => hr_support u (by simp [he])
    linarith [hr.1.2]
  exact ⟨hr.1, s.erase v,
    ⟨hne, by simp, by simpa [insert_erase hvs] using hs⟩, hr_support⟩

theorem link_cone_radial {K : PreAbstractSimplicialComplex V} {v : V}
    (x : Punctured K v) (hx : 0 < x.1.1 v) :
    link_cone_point K v ⟨x.1.1 v, coordinate_nonneg x.1 v, coordinate_le_one x.1 v⟩
      (radial_link x hx) = x.1 := by
  apply Subtype.ext
  funext u
  by_cases huv : u = v
  · subst u
    exact link_cone_coordinate K v _ _
  · change (1 - x.1.1 v) * radial_coordinates v x.1.1 u + _ = x.1.1 u
    simp only [radial_coordinates, if_neg huv, Pi.single_eq_of_ne huv, mul_zero, add_zero]
    exact mul_div_cancel₀ _ (ne_of_gt (sub_pos.mpr x.2))

abbrev DeletionConeDomain (K : PreAbstractSimplicialComplex V) (v : V) :=
  Realization (deletion K v) ⊕ (unitInterval × Realization (vertex_link K v))

def deletion_cone_projection (K : PreAbstractSimplicialComplex V) (v : V) :
    C(DeletionConeDomain K v, Realization K) :=
  ⟨Sum.elim (deletion_to_realization K v) (link_cone_map K v),
    continuous_sum_dom.mpr ⟨(deletion_to_realization K v).continuous,
      (link_cone_map K v).continuous⟩⟩

theorem deletion_cone_surjective (K : PreAbstractSimplicialComplex V) (v : V)
    [Nonempty (Realization (vertex_link K v))] :
    Function.Surjective (deletion_cone_projection K v) := by
  intro x
  by_cases hz : x.1 v = 0
  · exact ⟨Sum.inl ⟨x.1, mem_carrier_deletion_iff.mpr ⟨x.2, hz⟩⟩, rfl⟩
  · by_cases h₁ : x.1 v = 1
    · let y : Realization (vertex_link K v) := Classical.arbitrary _
      have hv : {v} ∈ K := by
        obtain ⟨s, hs, _⟩ := y.2.2
        exact (K.isRelLowerSet_faces hs.2.2).2 (singleton_subset_iff.mpr (mem_insert_self _ _))
          (singleton_nonempty _)
      refine ⟨Sum.inr (1, y), ?_⟩
      apply (coordinate_eq_one_iff _ v hv).mp ?_ |>.trans
        ((coordinate_eq_one_iff x v hv).mp h₁).symm
      exact link_cone_coordinate K v 1 y
    · have hp : x.1 v < 1 := lt_of_le_of_ne (coordinate_le_one x v) h₁
      have hx : 0 < x.1 v := lt_of_le_of_ne (coordinate_nonneg x v) (Ne.symm hz)
      exact ⟨Sum.inr (⟨x.1 v, coordinate_nonneg x v, coordinate_le_one x v⟩,
        radial_link ⟨x, hp⟩ hx), link_cone_radial ⟨x, hp⟩ hx⟩

theorem deletion_cone_quotient (K : PreAbstractSimplicialComplex V) (v : V)
    [Nonempty (Realization (vertex_link K v))] :
    Topology.IsQuotientMap (deletion_cone_projection K v) :=
  IsQuotientMap.of_surjective_continuous (deletion_cone_surjective K v)
    (deletion_cone_projection K v).continuous

theorem deletion_to_realization_injective (K : PreAbstractSimplicialComplex V) (v : V) :
    Function.Injective (deletion_to_realization K v) :=
  fun _ _ h => Subtype.ext (congrArg (fun z : Realization K => z.1) h)

theorem deletion_cone_compatible (K : PreAbstractSimplicialComplex V) (v : V)
    {Y : Type*} (fD : Realization (deletion K v) → Y)
    (fC : unitInterval × Realization (vertex_link K v) → Y)
    (h₀ : ∀ x, fC (0, x) = fD (link_to_deletion K v x))
    (h₁ : ∀ x y, fC (1, x) = fC (1, y)) :
    ∀ a b, deletion_cone_projection K v a = deletion_cone_projection K v b →
      Sum.elim fD fC a = Sum.elim fD fC b := by
  have hDC : ∀ d t x, deletion_to_realization K v d = link_cone_point K v t x →
      fD d = fC (t, x) := by
    intro d t x h
    have ht : t = 0 := by
      apply Subtype.ext
      have hh := congrArg (fun z : Realization K => z.1 v) h
      change d.1 v = (link_cone_point K v t x).1 v at hh
      rw [link_cone_coordinate, (mem_carrier_deletion_iff.mp d.2).2] at hh
      exact hh.symm
    subst t
    rw [link_cone_zero] at h
    rw [deletion_to_realization_injective K v h]
    exact (h₀ x).symm
  intro a b h
  cases a with
  | inl d =>
    cases b with
    | inl e => exact congrArg fD (deletion_to_realization_injective K v h)
    | inr c => exact hDC d c.1 c.2 h
  | inr c =>
    cases b with
    | inl e => exact (hDC e c.1 c.2 h.symm).symm
    | inr d =>
      obtain ⟨t, x⟩ := c
      obtain ⟨s, y⟩ := d
      obtain ⟨ht, he⟩ := (link_cone_eq_iff K v t s x y).mp h
      subst s
      rcases he with h₁' | rfl
      · subst t
        exact h₁ x y
      · rfl

def deletion_cone_descend (K : PreAbstractSimplicialComplex V) (v : V)
    [Nonempty (Realization (vertex_link K v))] {Y : Type*} [TopologicalSpace Y]
    (fD : C(Realization (deletion K v), Y))
    (fC : C(unitInterval × Realization (vertex_link K v), Y))
    (h₀ : ∀ x, fC (0, x) = fD (link_to_deletion K v x))
    (h₁ : ∀ x y, fC (1, x) = fC (1, y)) : C(Realization K, Y) :=
  descend_map (deletion_cone_projection K v) (deletion_cone_quotient K v)
    ⟨Sum.elim fD fC, continuous_sum_dom.mpr ⟨fD.continuous, fC.continuous⟩⟩
    (deletion_cone_compatible K v fD fC h₀ h₁)

@[simp] theorem deletion_cone_descend_left (K : PreAbstractSimplicialComplex V) (v : V)
    [Nonempty (Realization (vertex_link K v))] {Y : Type*} [TopologicalSpace Y]
    (fD : C(Realization (deletion K v), Y))
    (fC : C(unitInterval × Realization (vertex_link K v), Y))
    (h₀ : ∀ x, fC (0, x) = fD (link_to_deletion K v x))
    (h₁ : ∀ x y, fC (1, x) = fC (1, y)) (d : Realization (deletion K v)) :
    deletion_cone_descend K v fD fC h₀ h₁ (deletion_to_realization K v d) = fD d :=
  descend_map_apply _ _ _ _ (Sum.inl d)

@[simp] theorem deletion_cone_descend_right (K : PreAbstractSimplicialComplex V) (v : V)
    [Nonempty (Realization (vertex_link K v))] {Y : Type*} [TopologicalSpace Y]
    (fD : C(Realization (deletion K v), Y))
    (fC : C(unitInterval × Realization (vertex_link K v), Y))
    (h₀ : ∀ x, fC (0, x) = fD (link_to_deletion K v x))
    (h₁ : ∀ x y, fC (1, x) = fC (1, y)) (t : unitInterval)
    (x : Realization (vertex_link K v)) :
    deletion_cone_descend K v fD fC h₀ h₁ (link_cone_point K v t x) = fC (t, x) :=
  descend_map_apply _ _ _ _ (Sum.inr (t, x))

def deletion_collapse (K : PreAbstractSimplicialComplex V) (v : V)
    [Nonempty (Realization (vertex_link K v))] :
    C(Realization K, Susp (Realization (vertex_link K v))) :=
  deletion_cone_descend K v (ContinuousMap.const _ (Susp.south _)) Susp.mk
    (Susp.mk_zero) (Susp.mk_one_eq_mk_one)

@[simp] theorem deletion_collapse_left (K : PreAbstractSimplicialComplex V) (v : V)
    [Nonempty (Realization (vertex_link K v))] (d : Realization (deletion K v)) :
    deletion_collapse K v (deletion_to_realization K v d) = Susp.south _ :=
  deletion_cone_descend_left _ _ _ _ _ _ _

@[simp] theorem deletion_collapse_right (K : PreAbstractSimplicialComplex V) (v : V)
    [Nonempty (Realization (vertex_link K v))] (t : unitInterval)
    (x : Realization (vertex_link K v)) :
    deletion_collapse K v (link_cone_point K v t x) = Susp.mk (t, x) :=
  deletion_cone_descend_right _ _ _ _ _ _ _ _

def timed_deletion_cone_projection (K : PreAbstractSimplicialComplex V) (v : V) :
    C(unitInterval × DeletionConeDomain K v, unitInterval × Realization K) :=
  ⟨fun p => (p.1, deletion_cone_projection K v p.2),
    continuous_fst.prodMk ((deletion_cone_projection K v).continuous.comp continuous_snd)⟩

theorem timed_deletion_cone_quotient (K : PreAbstractSimplicialComplex V) (v : V)
    [Nonempty (Realization (vertex_link K v))] :
    Topology.IsQuotientMap (timed_deletion_cone_projection K v) :=
  IsQuotientMap.of_surjective_continuous (by
    rintro ⟨t, x⟩
    obtain ⟨a, ha⟩ := deletion_cone_surjective K v x
    exact ⟨(t, a), Prod.ext rfl ha⟩) (timed_deletion_cone_projection K v).continuous

def timed_cone_source {Y : Type*} [TopologicalSpace Y]
    (K : PreAbstractSimplicialComplex V) (v : V)
    (fD : C(unitInterval × Realization (deletion K v), Y))
    (fC : C(unitInterval × (unitInterval × Realization (vertex_link K v)), Y)) :
    C(unitInterval × DeletionConeDomain K v, Y) where
  toFun p := Sum.elim (fun d => fD (p.1, d)) (fun c => fC (p.1, c)) p.2
  continuous_toFun := by
    have hsum : Continuous (Sum.elim fD fC) :=
      continuous_sumElim.mpr ⟨fD.continuous, fC.continuous⟩
    convert hsum.comp (Homeomorph.prodSumDistrib :
      unitInterval × DeletionConeDomain K v ≃ₜ
        (unitInterval × Realization (deletion K v)) ⊕
        (unitInterval × (unitInterval × Realization (vertex_link K v)))).continuous using 1
    funext p
    rcases p with ⟨s, d | c⟩ <;> rfl

def timed_deletion_cone_descend (K : PreAbstractSimplicialComplex V) (v : V)
    [Nonempty (Realization (vertex_link K v))] {Y : Type*} [TopologicalSpace Y]
    (fD : C(unitInterval × Realization (deletion K v), Y))
    (fC : C(unitInterval × (unitInterval × Realization (vertex_link K v)), Y))
    (h₀ : ∀ s x, fC (s, (0, x)) = fD (s, link_to_deletion K v x))
    (h₁ : ∀ s x y, fC (s, (1, x)) = fC (s, (1, y))) :
    C(unitInterval × Realization K, Y) :=
  descend_map (timed_deletion_cone_projection K v) (timed_deletion_cone_quotient K v)
    (timed_cone_source K v fD fC) (by
      rintro ⟨s, a⟩ ⟨t, b⟩ h
      have ht : s = t := congrArg Prod.fst h
      subst t
      exact deletion_cone_compatible K v (fun d => fD (s, d)) (fun c => fC (s, c))
        (h₀ s) (h₁ s) a b (congrArg Prod.snd h))

@[simp] theorem timed_deletion_cone_descend_left (K : PreAbstractSimplicialComplex V) (v : V)
    [Nonempty (Realization (vertex_link K v))] {Y : Type*} [TopologicalSpace Y]
    (fD : C(unitInterval × Realization (deletion K v), Y))
    (fC : C(unitInterval × (unitInterval × Realization (vertex_link K v)), Y))
    (h₀ : ∀ s x, fC (s, (0, x)) = fD (s, link_to_deletion K v x))
    (h₁ : ∀ s x y, fC (s, (1, x)) = fC (s, (1, y)))
    (s : unitInterval) (d : Realization (deletion K v)) :
    timed_deletion_cone_descend K v fD fC h₀ h₁ (s, deletion_to_realization K v d) = fD (s, d) :=
  descend_map_apply _ _ _ _ (s, Sum.inl d)

@[simp] theorem timed_deletion_cone_descend_right (K : PreAbstractSimplicialComplex V) (v : V)
    [Nonempty (Realization (vertex_link K v))] {Y : Type*} [TopologicalSpace Y]
    (fD : C(unitInterval × Realization (deletion K v), Y))
    (fC : C(unitInterval × (unitInterval × Realization (vertex_link K v)), Y))
    (h₀ : ∀ s x, fC (s, (0, x)) = fD (s, link_to_deletion K v x))
    (h₁ : ∀ s x y, fC (s, (1, x)) = fC (s, (1, y)))
    (s t : unitInterval) (x : Realization (vertex_link K v)) :
    timed_deletion_cone_descend K v fD fC h₀ h₁ (s, link_cone_point K v t x) = fC (s, (t, x)) :=
  descend_map_apply _ _ _ _ (s, Sum.inr (t, x))

end MathGauge.PublicProof.Topology
