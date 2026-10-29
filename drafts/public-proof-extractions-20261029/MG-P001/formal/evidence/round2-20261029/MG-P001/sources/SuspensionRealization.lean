import TwoConeRealizations
import RealizationCompactness
import VendoredSuspension

/-! The actual suspension quotient maps into the actual two-cone simplicial realization. -/

noncomputable section

open Finset Set ContinuousMap

namespace MathGauge.PublicProof.Topology

def south_weight (t : unitInterval) : ℝ := max (1 - 2 * (t : ℝ)) 0
def north_weight (t : unitInterval) : ℝ := max (2 * (t : ℝ) - 1) 0
def equator_weight (t : unitInterval) : ℝ := 1 - south_weight t - north_weight t

theorem weights_lower (t : unitInterval) (ht : (t : ℝ) ≤ 1 / 2) :
    south_weight t = 1 - 2 * (t : ℝ) ∧ north_weight t = 0 ∧
      equator_weight t = 2 * (t : ℝ) := by
  have h₁ : 0 ≤ 1 - 2 * (t : ℝ) := by linarith
  have h₂ : 2 * (t : ℝ) - 1 ≤ 0 := by linarith
  simp [south_weight, north_weight, equator_weight, max_eq_left h₁, max_eq_right h₂]

theorem weights_upper (t : unitInterval) (ht : 1 / 2 ≤ (t : ℝ)) :
    south_weight t = 0 ∧ north_weight t = 2 * (t : ℝ) - 1 ∧
      equator_weight t = 2 - 2 * (t : ℝ) := by
  have h₁ : 1 - 2 * (t : ℝ) ≤ 0 := by linarith
  have h₂ : 0 ≤ 2 * (t : ℝ) - 1 := by linarith
  simp only [south_weight, north_weight, equator_weight, max_eq_right h₁, max_eq_left h₂,
    sub_zero, true_and]
  ring

theorem equator_weight_nonneg (t : unitInterval) : 0 ≤ equator_weight t := by
  rcases le_total (t : ℝ) (1 / 2) with ht | ht
  · rw [(weights_lower t ht).2.2]; exact mul_nonneg (by norm_num) t.2.1
  · rw [(weights_upper t ht).2.2]; linarith [t.2.2]

theorem time_from_weights (t : unitInterval) :
    (t : ℝ) = (1 - south_weight t + north_weight t) / 2 := by
  rcases le_total (t : ℝ) (1 / 2) with ht | ht
  · rw [(weights_lower t ht).1, (weights_lower t ht).2.1]; ring
  · rw [(weights_upper t ht).1, (weights_upper t ht).2.1]; ring

theorem equator_weight_eq_zero (t : unitInterval) : equator_weight t = 0 ↔ t = 0 ∨ t = 1 := by
  constructor
  · intro h
    rcases le_total (t : ℝ) (1 / 2) with ht | ht
    · left; apply Subtype.ext; change (t : ℝ) = 0
      rw [(weights_lower t ht).2.2] at h; linarith
    · right; apply Subtype.ext; change (t : ℝ) = 1
      rw [(weights_upper t ht).2.2] at h; linarith
  · rintro (rfl | rfl) <;> norm_num [equator_weight, south_weight, north_weight]

variable {V : Type*} [Fintype V] [DecidableEq V]

def suspension_coordinates (t : unitInterval) (x : V → ℝ) : Sum Bool V → ℝ :=
  Sum.elim (fun b => if b then north_weight t else south_weight t)
    (fun v => equator_weight t * x v)

def suspension_realization_point (L : PreAbstractSimplicialComplex V)
    (t : unitInterval) (x : Realization L) : Realization (realizing_complex L) := by
  refine ⟨suspension_coordinates t x.1, ⟨?_, ?_⟩, ?_⟩
  · intro u
    cases u with
    | inl b => cases b <;> exact le_max_right _ _
    | inr v => exact mul_nonneg (equator_weight_nonneg t) (coordinate_nonneg x v)
  · simp only [suspension_coordinates, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      Fintype.sum_bool, Bool.false_eq_true, if_false, if_true, ← Finset.mul_sum,
      coordinates_sum x, mul_one]
    dsimp [equator_weight]
    ring
  · obtain ⟨s, hs, hsupport⟩ := x.2.2
    have hb : s.image Sum.inr ∈ embedded_base L := ⟨s, hs, rfl⟩
    rcases le_total (t : ℝ) (1 / 2) with ht | ht
    · refine ⟨insert (Sum.inl false) (s.image Sum.inr),
        Or.inl (cone_insert_apex (base_le_cone _ _ hb)), ?_⟩
      intro u hu
      cases u with
      | inl b =>
        cases b
        · simp at hu
        · exact (weights_lower t ht).2.1
      | inr v =>
        have hv : v ∉ s := fun hv => hu (mem_insert_of_mem (mem_image.mpr ⟨v, hv, rfl⟩))
        simp [suspension_coordinates, hsupport v hv]
    · refine ⟨insert (Sum.inl true) (s.image Sum.inr),
        Or.inr (cone_insert_apex (base_le_cone _ _ hb)), ?_⟩
      intro u hu
      cases u with
      | inl b =>
        cases b
        · exact (weights_upper t ht).1
        · simp at hu
      | inr v =>
        have hv : v ∉ s := fun hv => hu (mem_insert_of_mem (mem_image.mpr ⟨v, hv, rfl⟩))
        simp [suspension_coordinates, hsupport v hv]

def suspension_realization_cylinder (L : PreAbstractSimplicialComplex V) :
    C(unitInterval × Realization L, Realization (realizing_complex L)) where
  toFun p := suspension_realization_point L p.1 p.2
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro u
    have ht : Continuous (fun p : unitInterval × Realization L => (p.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have hs : Continuous (fun p : unitInterval × Realization L => south_weight p.1) :=
      (continuous_const.sub (continuous_const.mul ht)).max continuous_const
    have hn : Continuous (fun p : unitInterval × Realization L => north_weight p.1) :=
      ((continuous_const.mul ht).sub continuous_const).max continuous_const
    cases u with
    | inl b => cases b <;> assumption
    | inr v =>
      exact ((continuous_const.sub hs).sub hn).mul
        ((continuous_apply v).comp (continuous_subtype_val.comp continuous_snd))

/-- A map from the actual unreduced suspension quotient to the two-cone realization. -/
def suspension_to_realization (L : PreAbstractSimplicialComplex V) :
    C(Susp (Realization L), Realization (realizing_complex L)) :=
  Susp.lift (suspension_realization_cylinder L)
    (by intro x y; apply Subtype.ext; funext u; cases u with
        | inl b => rfl
        | inr v => norm_num [suspension_realization_cylinder, suspension_realization_point,
            suspension_coordinates, equator_weight, south_weight, north_weight])
    (by intro x y; apply Subtype.ext; funext u; cases u with
        | inl b => rfl
        | inr v => norm_num [suspension_realization_cylinder, suspension_realization_point,
            suspension_coordinates, equator_weight, south_weight, north_weight])

theorem suspension_to_realization_injective (L : PreAbstractSimplicialComplex V) :
    Function.Injective (suspension_to_realization L) := by
  intro a b h
  induction a using Susp.ind with
  | h p =>
    induction b using Susp.ind with
    | h q =>
      obtain ⟨t, x⟩ := p
      obtain ⟨s, y⟩ := q
      have hsouth := congrArg (fun z : Realization (realizing_complex L) => z.1 (Sum.inl false)) h
      have hnorth := congrArg (fun z : Realization (realizing_complex L) => z.1 (Sum.inl true)) h
      change south_weight t = south_weight s at hsouth
      change north_weight t = north_weight s at hnorth
      have hts : t = s := by
        apply Subtype.ext
        rw [time_from_weights t, time_from_weights s, hsouth, hnorth]
      subst s
      by_cases he : equator_weight t = 0
      · rcases (equator_weight_eq_zero t).mp he with rfl | rfl
        · exact Susp.mk_zero_eq_mk_zero x y
        · exact Susp.mk_one_eq_mk_one x y
      · have hxy : x = y := by
          apply Subtype.ext
          funext v
          have hc := congrArg (fun z : Realization (realizing_complex L) => z.1 (Sum.inr v)) h
          change equator_weight t * x.1 v = equator_weight t * y.1 v at hc
          exact mul_left_cancel₀ he hc
        rw [hxy]

def base_vertices (s : Finset (Sum Bool V)) : Finset V :=
  univ.filter (fun v => Sum.inr v ∈ s)

@[simp] theorem mem_base_vertices (s : Finset (Sum Bool V)) (v : V) :
    v ∈ base_vertices s ↔ Sum.inr v ∈ s := by simp [base_vertices]

@[simp] theorem base_vertices_image (s : Finset V) : base_vertices (s.image Sum.inr) = s := by
  ext v; simp [base_vertices]

@[simp] theorem base_vertices_erase_pole (s : Finset (Sum Bool V)) (b : Bool) :
    base_vertices (s.erase (Sum.inl b)) = base_vertices s := by
  ext v; simp [base_vertices]

@[simp] theorem base_vertices_empty : base_vertices (∅ : Finset (Sum Bool V)) = ∅ := by
  ext v; simp [base_vertices]

theorem cone_base_face_or_empty (L : PreAbstractSimplicialComplex V) (b : Bool)
    (s : Finset (Sum Bool V)) (hs : s ∈ cone_complex (embedded_base L) (Sum.inl b)) :
    base_vertices s = ∅ ∨ base_vertices s ∈ L := by
  rcases hs.2 with h | h
  · left
    simpa using congrArg base_vertices h
  · right
    rcases h with ⟨t, ht, he⟩
    have he' := congrArg base_vertices he
    simp only [base_vertices_image, base_vertices_erase_pole] at he'
    exact he' ▸ ht

theorem realizing_base_sum (L : PreAbstractSimplicialComplex V)
    (x : Realization (realizing_complex L)) :
    ∑ v, x.1 (Sum.inr v) = 1 - x.1 (Sum.inl false) - x.1 (Sum.inl true) := by
  have h := coordinates_sum x
  rw [Fintype.sum_sum_type, Fintype.sum_bool] at h
  linarith

theorem realizing_poles_exclusive (L : PreAbstractSimplicialComplex V)
    (x : Realization (realizing_complex L)) :
    x.1 (Sum.inl false) = 0 ∨ x.1 (Sum.inl true) = 0 := by
  obtain ⟨s, hs | hs, hsupport⟩ := x.2.2
  · exact Or.inr (hsupport _ (cone_face_avoids_other (by simp)
      (embedded_base_avoids_poles L true) hs))
  · exact Or.inl (hsupport _ (cone_face_avoids_other (by simp)
      (embedded_base_avoids_poles L false) hs))

def realizing_time (L : PreAbstractSimplicialComplex V)
    (x : Realization (realizing_complex L)) : unitInterval :=
  ⟨(1 - x.1 (Sum.inl false) + x.1 (Sum.inl true)) / 2,
    by constructor <;> linarith [coordinate_nonneg x (Sum.inl false),
      coordinate_nonneg x (Sum.inl true), coordinate_le_one x (Sum.inl false),
      coordinate_le_one x (Sum.inl true)]⟩

theorem realizing_time_weights (L : PreAbstractSimplicialComplex V)
    (x : Realization (realizing_complex L)) :
    south_weight (realizing_time L x) = x.1 (Sum.inl false) ∧
      north_weight (realizing_time L x) = x.1 (Sum.inl true) ∧
      equator_weight (realizing_time L x) = ∑ v, x.1 (Sum.inr v) := by
  rcases realizing_poles_exclusive L x with hs | hn
  · have ht : 1 / 2 ≤ (realizing_time L x : ℝ) := by
      dsimp [realizing_time]; linarith [coordinate_nonneg x (Sum.inl true)]
    have h := weights_upper (realizing_time L x) ht
    rw [h.1, h.2.1, h.2.2, realizing_base_sum]
    dsimp [realizing_time]
    constructor
    · exact hs.symm
    · constructor <;> linarith
  · have ht : (realizing_time L x : ℝ) ≤ 1 / 2 := by
      dsimp [realizing_time]; linarith [coordinate_nonneg x (Sum.inl false)]
    have h := weights_lower (realizing_time L x) ht
    rw [h.1, h.2.1, h.2.2, realizing_base_sum]
    dsimp [realizing_time]
    constructor
    · linarith
    · exact ⟨hn.symm, by linarith⟩

/-- Normalize a point's nonzero base mass to an actual point of the original finite complex. -/
def normalized_base (L : PreAbstractSimplicialComplex V)
    (x : Realization (realizing_complex L)) (hpos : 0 < ∑ v, x.1 (Sum.inr v)) :
    Realization L := by
  let y : V → ℝ := fun v => x.1 (Sum.inr v) / ∑ w, x.1 (Sum.inr w)
  have hy : y ∈ stdSimplex ℝ V := by
    refine ⟨fun v => div_nonneg (coordinate_nonneg x _) (le_of_lt hpos), ?_⟩
    dsimp [y]
    rw [← Finset.sum_div, div_self (ne_of_gt hpos)]
  refine ⟨y, hy, ?_⟩
  obtain ⟨s, hs, hsupport⟩ := x.2.2
  have hf : base_vertices s = ∅ ∨ base_vertices s ∈ L := by
    rcases hs with hs | hs
    · exact cone_base_face_or_empty L false s hs
    · exact cone_base_face_or_empty L true s hs
  have hy_support : ∀ v, v ∉ base_vertices s → y v = 0 := by
    intro v hv
    have hvs : Sum.inr v ∉ s := by simpa using hv
    simp [y, hsupport _ hvs]
  rcases hf with hempty | hface
  · have hz : ∑ v, y v = 0 := Finset.sum_eq_zero (fun v _ => hy_support v (by simp [hempty]))
    have hsum := hy.2
    linarith
  · exact ⟨base_vertices s, hface, hy_support⟩

theorem suspension_to_realization_surjective (L : PreAbstractSimplicialComplex V)
    [Nonempty (Realization L)] : Function.Surjective (suspension_to_realization L) := by
  intro x
  let t := realizing_time L x
  have hw := realizing_time_weights L x
  by_cases hz : ∑ v, x.1 (Sum.inr v) = 0
  · let y : Realization L := Classical.arbitrary _
    refine ⟨Susp.mk (t, y), ?_⟩
    apply Subtype.ext
    funext u
    cases u with
    | inl b => cases b <;> first | exact hw.1 | exact hw.2.1
    | inr v =>
      change equator_weight t * y.1 v = x.1 (Sum.inr v)
      rw [hw.2.2, hz, zero_mul]
      have hle : x.1 (Sum.inr v) ≤ ∑ w, x.1 (Sum.inr w) :=
        Finset.single_le_sum (fun w _ => coordinate_nonneg x _) (mem_univ v)
      exact (le_antisymm (by linarith) (coordinate_nonneg x _)).symm
  · have hpos : 0 < ∑ v, x.1 (Sum.inr v) :=
      lt_of_le_of_ne (Finset.sum_nonneg (fun v _ => coordinate_nonneg x _)) (Ne.symm hz)
    refine ⟨Susp.mk (t, normalized_base L x hpos), ?_⟩
    apply Subtype.ext
    funext u
    cases u with
    | inl b => cases b <;> first | exact hw.1 | exact hw.2.1
    | inr v =>
      change equator_weight t * (x.1 (Sum.inr v) / ∑ w, x.1 (Sum.inr w)) = x.1 (Sum.inr v)
      rw [hw.2.2]
      field_simp

/-- Every finite nonempty base has exactly its usual suspension as the two-cone realization. -/
def suspension_realization_homeomorph (L : PreAbstractSimplicialComplex V)
    [Nonempty (Realization L)] : Susp (Realization L) ≃ₜ Realization (realizing_complex L) :=
  (Equiv.ofBijective (suspension_to_realization L)
    ⟨suspension_to_realization_injective L, suspension_to_realization_surjective L⟩).toHomeomorphOfContinuousClosed
        (suspension_to_realization L).continuous
        (suspension_to_realization L).continuous.isClosedMap

/-- The full reverse-realization part of MG-P001, for every finite base having a vertex. -/
theorem all_suspensions_realized (L : PreAbstractSimplicialComplex V)
    (hL : ∃ a : V, ({a} : Finset V) ∈ L) :
    ∃ (K B : PreAbstractSimplicialComplex (Sum Bool V)) (v : Sum Bool V),
      B ≤ K ∧ ({v} : Finset (Sum Bool V)) ∈ B ∧
      ContractibleSpace (Punctured K v) ∧
      (∃ e : Punctured B v ≃ₕ Realization B, e.toFun = punctured_inclusion_map B v) ∧
      Nonempty (Realization K ≃ₜ Susp (Realization L)) := by
  obtain ⟨a, ha⟩ := hL
  letI : Nonempty (Realization L) := ⟨vertex L a ha⟩
  obtain ⟨hBK, hv, hO, he⟩ := realizing_original_hypotheses L a ha
  exact ⟨realizing_complex L, realizing_edge a, Sum.inl false,
    hBK, hv, hO, he, ⟨(suspension_realization_homeomorph L).symm⟩⟩

end MathGauge.PublicProof.Topology
