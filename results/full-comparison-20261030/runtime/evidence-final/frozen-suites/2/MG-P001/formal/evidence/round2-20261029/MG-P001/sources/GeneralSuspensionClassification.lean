import DeletionConeGluing
import LinkNonempty
import SuspensionRetime

/-!
An explicit homotopy equivalence from the actual realization to the actual
unreduced suspension of its link, when the deletion is contractible.
The contraction of the deletion need not fix the link.
-/

noncomputable section

open Set ContinuousMap

namespace MathGauge.PublicProof.Topology

def cone_shift (s t : unitInterval) : ℝ := (1 + (s : ℝ)) * (t : ℝ) - (s : ℝ)

theorem cone_shift_bounds (s t : unitInterval) : -1 ≤ cone_shift s t ∧ cone_shift s t ≤ 1 := by
  dsimp [cone_shift]
  constructor <;> nlinarith [s.2.1, s.2.2, t.2.1, t.2.2]

def cone_positive (s t : unitInterval) : unitInterval :=
  ⟨max (cone_shift s t) 0, le_max_right _ _, max_le (cone_shift_bounds s t).2 (by norm_num)⟩

def cone_negative (s t : unitInterval) : unitInterval :=
  ⟨max (-cone_shift s t) 0, le_max_right _ _, max_le (by linarith [(cone_shift_bounds s t).1])
    (by norm_num)⟩

theorem continuous_cone_shift : Continuous (fun p : unitInterval × unitInterval => cone_shift p.1 p.2) :=
  ((continuous_const.add (continuous_subtype_val.comp continuous_fst)).mul
    (continuous_subtype_val.comp continuous_snd)).sub (continuous_subtype_val.comp continuous_fst)

theorem continuous_cone_positive :
    Continuous (fun p : unitInterval × unitInterval => cone_positive p.1 p.2) :=
  (continuous_cone_shift.max continuous_const).subtype_mk _

theorem continuous_cone_negative :
    Continuous (fun p : unitInterval × unitInterval => cone_negative p.1 p.2) :=
  (continuous_cone_shift.neg.max continuous_const).subtype_mk _

@[simp] theorem cone_positive_at_zero (t : unitInterval) : cone_positive 0 t = t := by
  apply Subtype.ext
  simp [cone_positive, cone_shift, max_eq_left t.2.1]

@[simp] theorem cone_positive_zero (s : unitInterval) : cone_positive s 0 = 0 := by
  apply Subtype.ext
  simp [cone_positive, cone_shift, max_eq_right (neg_nonpos.mpr s.2.1)]

@[simp] theorem cone_negative_zero (s : unitInterval) : cone_negative s 0 = s := by
  apply Subtype.ext
  simp [cone_negative, cone_shift, max_eq_left s.2.1]

@[simp] theorem cone_positive_one (s : unitInterval) : cone_positive s 1 = 1 := by
  apply Subtype.ext
  simp [cone_positive, cone_shift]

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (K : PreAbstractSimplicialComplex V) (v : V)
variable (c : Realization (deletion K v))
variable (H : ContinuousMap.Homotopy (ContinuousMap.id (Realization (deletion K v)))
  (ContinuousMap.const _ c))

def cone_deformation_point (s t : unitInterval) (x : Realization (vertex_link K v)) :
    Realization K :=
  if cone_shift s t ≤ 0 then
    deletion_to_realization K v (H (cone_negative s t, link_to_deletion K v x))
  else link_cone_point K v (cone_positive s t) x

def cone_deformation_cylinder :
    C(unitInterval × (unitInterval × Realization (vertex_link K v)), Realization K) where
  toFun p := cone_deformation_point K v c H p.1 p.2.1 p.2.2
  continuous_toFun := by
    have hp : Continuous (fun p : unitInterval × (unitInterval × Realization (vertex_link K v)) =>
        (p.1, p.2.1)) := continuous_fst.prodMk (continuous_fst.comp continuous_snd)
    have hx : Continuous (fun p : unitInterval × (unitInterval × Realization (vertex_link K v)) =>
        p.2.2) := continuous_snd.comp continuous_snd
    apply Continuous.if_le
    · exact (deletion_to_realization K v).continuous.comp
        (H.continuous.comp ((continuous_cone_negative.comp hp).prodMk
          ((link_to_deletion K v).continuous.comp hx)))
    · exact (link_cone_map K v).continuous.comp ((continuous_cone_positive.comp hp).prodMk hx)
    · exact continuous_cone_shift.comp hp
    · exact continuous_const
    · intro p he
      have hp0 : cone_positive p.1 p.2.1 = 0 := Subtype.ext (by simp [cone_positive, he])
      have hn0 : cone_negative p.1 p.2.1 = 0 := Subtype.ext (by simp [cone_negative, he])
      simp [hp0, hn0]

@[simp] theorem cone_deformation_zero_height (s : unitInterval)
    (x : Realization (vertex_link K v)) :
    cone_deformation_point K v c H s 0 x =
      deletion_to_realization K v (H (s, link_to_deletion K v x)) := by
  have he : cone_shift s 0 ≤ 0 := by simp [cone_shift, s.2.1]
  simp [cone_deformation_point, he]

@[simp] theorem cone_deformation_one_height (s : unitInterval)
    (x : Realization (vertex_link K v)) :
    cone_deformation_point K v c H s 1 x = link_cone_point K v 1 x := by
  have he : ¬cone_shift s 1 ≤ 0 := by simp [cone_shift]
  simp [cone_deformation_point, he]

@[simp] theorem cone_deformation_at_zero (t : unitInterval)
    (x : Realization (vertex_link K v)) :
    cone_deformation_point K v c H 0 t x = link_cone_point K v t x := by
  by_cases ht : t = 0
  · subst t
    simp
  · have ht' : 0 < (t : ℝ) := lt_of_le_of_ne t.2.1 (by
      intro h
      exact ht (Subtype.ext h.symm))
    have he : ¬cone_shift 0 t ≤ 0 := by simpa [cone_shift] using not_le.mpr ht'
    simp [cone_deformation_point, he]

variable [Nonempty (Realization (vertex_link K v))]

def deletion_deformation_map : C(unitInterval × Realization K, Realization K) :=
  timed_deletion_cone_descend K v
    ((deletion_to_realization K v).comp H.toContinuousMap)
    (cone_deformation_cylinder K v c H)
    (cone_deformation_zero_height K v c H)
    (fun s x y => by
      change cone_deformation_point K v c H s 1 x = cone_deformation_point K v c H s 1 y
      rw [cone_deformation_one_height, cone_deformation_one_height, link_cone_one K v x y])

@[simp] theorem deletion_deformation_left (s : unitInterval) (d : Realization (deletion K v)) :
    deletion_deformation_map K v c H (s, deletion_to_realization K v d) =
      deletion_to_realization K v (H (s, d)) :=
  timed_deletion_cone_descend_left _ _ _ _ _ _ _ _

@[simp] theorem deletion_deformation_right (s t : unitInterval)
    (x : Realization (vertex_link K v)) :
    deletion_deformation_map K v c H (s, link_cone_point K v t x) =
      cone_deformation_point K v c H s t x :=
  timed_deletion_cone_descend_right _ _ _ _ _ _ _ _ _

def suspension_return_cylinder :
    C(unitInterval × Realization (vertex_link K v), Realization K) :=
  (cone_deformation_cylinder K v c H).comp
    ⟨fun p => (1, p), continuous_const.prodMk continuous_id⟩

def suspension_return : C(Susp (Realization (vertex_link K v)), Realization K) :=
  Susp.lift (suspension_return_cylinder K v c H)
    (by intro x y; change cone_deformation_point K v c H 1 0 x = cone_deformation_point K v c H 1 0 y; simp)
    (by intro x y; change cone_deformation_point K v c H 1 1 x = cone_deformation_point K v c H 1 1 y
        simp only [cone_deformation_one_height]; exact link_cone_one K v x y)

omit [Nonempty (Realization (vertex_link K v))] in
@[simp] theorem suspension_return_mk (t : unitInterval) (x : Realization (vertex_link K v)) :
    suspension_return K v c H (Susp.mk (t, x)) = cone_deformation_point K v c H 1 t x := rfl

@[simp] theorem suspension_return_south :
    suspension_return K v c H (Susp.south _) = deletion_to_realization K v c := by
  unfold Susp.south
  rw [suspension_return_mk, cone_deformation_zero_height]
  simp

def deletion_collapse_return_homotopy :
    ContinuousMap.Homotopy (ContinuousMap.id (Realization K))
      ((suspension_return K v c H).comp (deletion_collapse K v)) where
  toContinuousMap := deletion_deformation_map K v c H
  map_zero_left x := by
    obtain ⟨a, rfl⟩ := deletion_cone_surjective K v x
    cases a with
    | inl d =>
      change deletion_deformation_map K v c H (0, deletion_to_realization K v d) =
        deletion_to_realization K v d
      simp
    | inr p =>
      change deletion_deformation_map K v c H (0, link_cone_point K v p.1 p.2) =
        link_cone_point K v p.1 p.2
      simp
  map_one_left x := by
    obtain ⟨a, rfl⟩ := deletion_cone_surjective K v x
    cases a with
    | inl d =>
      change deletion_deformation_map K v c H (1, deletion_to_realization K v d) =
        suspension_return K v c H (deletion_collapse K v (deletion_to_realization K v d))
      simp
    | inr p =>
      obtain ⟨t, y⟩ := p
      change deletion_deformation_map K v c H (1, link_cone_point K v t y) =
        suspension_return K v c H (deletion_collapse K v (link_cone_point K v t y))
      simp

def collapse_return_height : C(unitInterval, unitInterval) :=
  ⟨cone_positive 1, continuous_cone_positive.comp (continuous_const.prodMk continuous_id)⟩

theorem collapse_return_eq_retime :
    (deletion_collapse K v).comp (suspension_return K v c H) =
      suspension_retime collapse_return_height (cone_positive_zero 1) (cone_positive_one 1) := by
  apply DFunLike.ext
  intro z
  obtain ⟨⟨t, x⟩, rfl⟩ := Susp.mk_surjective z
  change deletion_collapse K v (cone_deformation_point K v c H 1 t x) =
    Susp.mk (cone_positive 1 t, x)
  by_cases ht : cone_shift 1 t ≤ 0
  · have hp : cone_positive 1 t = 0 := Subtype.ext (by simp [cone_positive, max_eq_right ht])
    simp [cone_deformation_point, ht, hp, Susp.mk_zero]
  · simp [cone_deformation_point, ht]

/-- The full geometric classification, obtained by explicit actual homotopies. -/
def general_suspension_equiv_of_contraction :
    Realization K ≃ₕ Susp (Realization (vertex_link K v)) where
  toFun := deletion_collapse K v
  invFun := suspension_return K v c H
  left_inv := ⟨(deletion_collapse_return_homotopy K v c H).symm⟩
  right_inv := by
    rw [collapse_return_eq_retime]
    exact ⟨(suspension_retime_homotopy collapse_return_height
      (cone_positive_zero 1) (cone_positive_one 1)).symm⟩

theorem general_suspension_classification
    [ContractibleSpace (Realization (deletion K v))] :
    Nonempty (Realization K ≃ₕ Susp (Realization (vertex_link K v))) := by
  obtain ⟨c, ⟨H⟩⟩ := id_nullhomotopic (Realization (deletion K v))
  exact ⟨general_suspension_equiv_of_contraction K v c H⟩

omit [Nonempty (Realization (vertex_link K v))] in
/-- The classification with exactly the original geometric hypotheses. -/
theorem original_suspension_classification (B : PreAbstractSimplicialComplex V)
    (hBK : B ≤ K) (hv : {v} ∈ B) [ContractibleSpace (Punctured K v)]
    (e : Punctured B v ≃ₕ Realization B) (he : e.toFun = punctured_inclusion_map B v) :
    Nonempty (Realization K ≃ₕ Susp (Realization (vertex_link K v))) := by
  obtain ⟨a, ha⟩ := vertex_link_has_vertex K B v hBK hv e he
  letI : Nonempty (Realization (vertex_link K v)) := ⟨vertex _ a ha⟩
  letI : ContractibleSpace (Realization (deletion K v)) := deletion_contractible K v
  exact general_suspension_classification K v

end MathGauge.PublicProof.Topology
