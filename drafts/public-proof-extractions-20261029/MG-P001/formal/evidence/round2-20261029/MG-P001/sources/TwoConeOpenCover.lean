import SuspensionRealization

/-!
The two-cone realization has a genuine open cover by its two punctured spaces.
Both open sets are contractible; their intersection deformation retracts onto
the actual base realization by normalizing its non-pole coordinates.
-/

noncomputable section

open Finset Set ContinuousMap

namespace MathGauge.PublicProof.Topology

variable {V : Type*} [Fintype V] [DecidableEq V]

def pole_open (L : PreAbstractSimplicialComplex V) (b : Bool) :
    Set (Realization (realizing_complex L)) := {x | x.1 (Sum.inl b) < 1}

theorem isOpen_pole_open (L : PreAbstractSimplicialComplex V) (b : Bool) :
    IsOpen (pole_open L b) :=
  isOpen_lt ((continuous_apply (Sum.inl b)).comp continuous_subtype_val) continuous_const

theorem pole_open_cover (L : PreAbstractSimplicialComplex V) :
    pole_open L false ∪ pole_open L true = univ := by
  apply Set.eq_univ_of_forall
  intro x
  rcases realizing_poles_exclusive L x with h | h
  · left; change x.1 (Sum.inl false) < 1; rw [h]; norm_num
  · right; change x.1 (Sum.inl true) < 1; rw [h]; norm_num

theorem pole_open_contractible (L : PreAbstractSimplicialComplex V) (b : Bool) :
    ContractibleSpace ↥(pole_open L b) := by
  cases b
  · exact punctured_two_cones_contractible (embedded_base L) (Sum.inl false) (Sum.inl true)
      (by simp) (embedded_base_avoids_poles L false)
  · change ContractibleSpace (Punctured (realizing_complex L) (Sum.inl true))
    have he : realizing_complex L = two_cones (embedded_base L) (Sum.inl true) (Sum.inl false) :=
      sup_comm _ _
    rw [he]
    exact punctured_two_cones_contractible (embedded_base L) (Sum.inl true) (Sum.inl false)
      (by simp) (embedded_base_avoids_poles L true)

abbrev EquatorialBand (L : PreAbstractSimplicialComplex V) :=
  ↥(pole_open L false ∩ pole_open L true)

theorem equatorial_base_positive (L : PreAbstractSimplicialComplex V) (x : EquatorialBand L) :
    0 < ∑ v, x.1.1 (Sum.inr v) := by
  have hs := realizing_base_sum L x.1
  rcases realizing_poles_exclusive L x.1 with h | h
  · have ht := x.2.2
    change x.1.1 (Sum.inl true) < 1 at ht
    rw [h] at hs
    linarith
  · have ht := x.2.1
    change x.1.1 (Sum.inl false) < 1 at ht
    rw [h] at hs
    linarith

def equatorial_projection (L : PreAbstractSimplicialComplex V) :
    C(EquatorialBand L, Realization L) where
  toFun x := normalized_base L x.1 (equatorial_base_positive L x)
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro v
    have hc (u : V) : Continuous (fun x : EquatorialBand L => x.1.1 (Sum.inr u)) :=
      (continuous_apply (Sum.inr u)).comp (continuous_subtype_val.comp continuous_subtype_val)
    exact (hc v).div (continuous_finset_sum _ (fun u _ => hc u))
      (fun x => ne_of_gt (equatorial_base_positive L x))

def equator_time : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩

theorem equator_coordinates (L : PreAbstractSimplicialComplex V) (x : Realization L)
    (u : Sum Bool V) :
    (suspension_realization_point L equator_time x).1 u =
      Sum.elim (fun _ => 0) x.1 u := by
  cases u with
  | inl b => cases b <;> norm_num [suspension_realization_point, suspension_coordinates,
      equator_time, south_weight, north_weight, equator_weight]
  | inr v => norm_num [suspension_realization_point, suspension_coordinates,
      equator_time, south_weight, north_weight, equator_weight]

def equator_inclusion (L : PreAbstractSimplicialComplex V) :
    C(Realization L, EquatorialBand L) where
  toFun x := ⟨suspension_realization_point L equator_time x, by
    constructor
    · change (suspension_realization_point L equator_time x).1 (Sum.inl false) < 1
      rw [equator_coordinates]
      norm_num
    · change (suspension_realization_point L equator_time x).1 (Sum.inl true) < 1
      rw [equator_coordinates]
      norm_num⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (suspension_realization_cylinder L).continuous.comp
      (show Continuous (fun x : Realization L => (equator_time, x)) from
        continuous_const.prodMk continuous_id)

@[simp] theorem equatorial_projection_inclusion (L : PreAbstractSimplicialComplex V)
    (x : Realization L) : equatorial_projection L (equator_inclusion L x) = x := by
  apply Subtype.ext
  funext v
  change (suspension_realization_point L equator_time x).1 (Sum.inr v) /
    (∑ u, (suspension_realization_point L equator_time x).1 (Sum.inr u)) = x.1 v
  simp only [equator_coordinates, Sum.elim_inr, coordinates_sum x, div_one]

theorem equator_projection_support (L : PreAbstractSimplicialComplex V)
    (x : EquatorialBand L) (u : Sum Bool V) (hu : x.1.1 u = 0) :
    (equator_inclusion L (equatorial_projection L x)).1.1 u = 0 := by
  change (suspension_realization_point L equator_time (equatorial_projection L x)).1 u = 0
  rw [equator_coordinates]
  cases u with
  | inl b => rfl
  | inr v =>
    change x.1.1 (Sum.inr v) / (∑ w, x.1.1 (Sum.inr w)) = 0
    rw [hu, zero_div]

def equatorial_homotopy_point (L : PreAbstractSimplicialComplex V)
    (t : unitInterval) (x : EquatorialBand L) : EquatorialBand L := by
  let n := equator_inclusion L (equatorial_projection L x)
  let y : Sum Bool V → ℝ := fun u => (1 - (t : ℝ)) * x.1.1 u + (t : ℝ) * n.1.1 u
  have hy : y ∈ carrier (realizing_complex L) := by
    obtain ⟨s, hs, hsupport⟩ := x.1.2.2
    refine ⟨⟨?_, ?_⟩, s, hs, ?_⟩
    · intro u
      exact add_nonneg (mul_nonneg (sub_nonneg.mpr t.2.2) (coordinate_nonneg x.1 u))
        (mul_nonneg t.2.1 (coordinate_nonneg n.1 u))
    · dsimp [y]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        coordinates_sum x.1, coordinates_sum n.1]
      ring
    · intro u hu
      dsimp [y, n]
      rw [hsupport u hu, equator_projection_support L x u (hsupport u hu)]
      simp
  refine ⟨⟨y, hy⟩, ?_⟩
  have hbound (b : Bool) (hb : x.1.1 (Sum.inl b) < 1) : y (Sum.inl b) < 1 := by
    have hn : n.1.1 (Sum.inl b) = 0 := equator_coordinates L (equatorial_projection L x) _
    dsimp [y]
    rw [hn, mul_zero, add_zero]
    nlinarith [coordinate_nonneg x.1 (Sum.inl b), t.2.1]
  exact ⟨hbound false x.2.1, hbound true x.2.2⟩

def equatorial_homotopy (L : PreAbstractSimplicialComplex V) :
    ContinuousMap.Homotopy (ContinuousMap.id (EquatorialBand L))
      ((equator_inclusion L).comp (equatorial_projection L)) where
  toFun p := equatorial_homotopy_point L p.1 p.2
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    apply continuous_pi
    intro u
    have ht : Continuous (fun p : unitInterval × EquatorialBand L => (p.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have hx : Continuous (fun p : unitInterval × EquatorialBand L => p.2.1.1 u) :=
      (continuous_apply u).comp (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd))
    have hn : Continuous (fun p : unitInterval × EquatorialBand L =>
        (equator_inclusion L (equatorial_projection L p.2)).1.1 u) :=
      (continuous_apply u).comp (continuous_subtype_val.comp (continuous_subtype_val.comp
        ((equator_inclusion L).continuous.comp ((equatorial_projection L).continuous.comp continuous_snd))))
    exact ((continuous_const.sub ht).mul hx).add (ht.mul hn)
  map_zero_left x := by
    apply Subtype.ext
    apply Subtype.ext
    funext u
    simp [equatorial_homotopy_point]
  map_one_left x := by
    apply Subtype.ext
    apply Subtype.ext
    funext u
    simp [equatorial_homotopy_point]

/-- The intersection of the two genuine open cones is homotopy equivalent to the base. -/
def equatorial_equiv (L : PreAbstractSimplicialComplex V) : EquatorialBand L ≃ₕ Realization L where
  toFun := equatorial_projection L
  invFun := equator_inclusion L
  left_inv := ⟨(equatorial_homotopy L).symm⟩
  right_inv := by
    have he : (equatorial_projection L).comp (equator_inclusion L) = ContinuousMap.id _ := by
      apply DFunLike.ext
      exact equatorial_projection_inclusion L
    rw [he]

theorem equatorial_nonempty (L : PreAbstractSimplicialComplex V) [Nonempty (Realization L)] :
    Nonempty (EquatorialBand L) := ⟨equator_inclusion L (Classical.arbitrary _)⟩

end MathGauge.PublicProof.Topology
