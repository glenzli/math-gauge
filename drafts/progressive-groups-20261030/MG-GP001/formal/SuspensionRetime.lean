import DeletionConeGluing

/-! Continuous changes of suspension height fixing both poles are homotopic to the identity. -/

noncomputable section

open ContinuousMap

namespace MathGauge.PublicProof.Topology

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]

def suspension_retime_cylinder (r : C(unitInterval, unitInterval)) :
    C(unitInterval × X, Susp X) :=
  Susp.mk.comp ⟨fun p => (r p.1, p.2), (r.continuous.comp continuous_fst).prodMk continuous_snd⟩

def suspension_retime (r : C(unitInterval, unitInterval)) (r₀ : r 0 = 0) (r₁ : r 1 = 1) :
    C(Susp X, Susp X) :=
  Susp.lift (suspension_retime_cylinder r)
    (by intro x y; change Susp.mk (r 0, x) = Susp.mk (r 0, y); rw [r₀]; exact Susp.mk_zero_eq_mk_zero x y)
    (by intro x y; change Susp.mk (r 1, x) = Susp.mk (r 1, y); rw [r₁]; exact Susp.mk_one_eq_mk_one x y)

omit [CompactSpace X] [T2Space X] in
@[simp] theorem suspension_retime_mk (r : C(unitInterval, unitInterval))
    (r₀ : r 0 = 0) (r₁ : r 1 = 1) (t : unitInterval) (x : X) :
    suspension_retime r r₀ r₁ (Susp.mk (t, x)) = Susp.mk (r t, x) := rfl

def interval_mix (s t u : unitInterval) : unitInterval :=
  ⟨(1 - (s : ℝ)) * (t : ℝ) + (s : ℝ) * (u : ℝ),
    add_nonneg (mul_nonneg (sub_nonneg.mpr s.2.2) t.2.1) (mul_nonneg s.2.1 u.2.1), by
      nlinarith [s.2.1, s.2.2, t.2.1, t.2.2, u.2.1, u.2.2]⟩

@[simp] theorem interval_mix_zero (t u : unitInterval) : interval_mix 0 t u = t := by
  apply Subtype.ext; simp [interval_mix]

@[simp] theorem interval_mix_one (t u : unitInterval) : interval_mix 1 t u = u := by
  apply Subtype.ext; simp [interval_mix]

@[simp] theorem interval_mix_self (s t : unitInterval) : interval_mix s t t = t := by
  apply Subtype.ext; dsimp [interval_mix]; ring

def timed_suspension_projection : C(unitInterval × (unitInterval × X), unitInterval × Susp X) :=
  ⟨fun p => (p.1, Susp.mk p.2), continuous_fst.prodMk (Susp.mk.continuous.comp continuous_snd)⟩

theorem timed_suspension_quotient :
    Topology.IsQuotientMap (timed_suspension_projection (X := X)) :=
  Topology.IsQuotientMap.of_surjective_continuous (by
    rintro ⟨s, x⟩
    obtain ⟨p, hp⟩ := Susp.mk_surjective x
    exact ⟨(s, p), Prod.ext rfl hp⟩) timed_suspension_projection.continuous

def suspension_retime_homotopy_source (r : C(unitInterval, unitInterval)) :
    C(unitInterval × (unitInterval × X), Susp X) where
  toFun p := Susp.mk (interval_mix p.1 p.2.1 (r p.2.1), p.2.2)
  continuous_toFun := by
    apply Susp.mk.continuous.comp
    apply Continuous.prodMk _ (continuous_snd.comp continuous_snd)
    apply Continuous.subtype_mk
    have hs : Continuous (fun p : unitInterval × (unitInterval × X) => (p.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have ht : Continuous (fun p : unitInterval × (unitInterval × X) => (p.2.1 : ℝ)) :=
      continuous_subtype_val.comp (continuous_fst.comp continuous_snd)
    have hr : Continuous (fun p : unitInterval × (unitInterval × X) => (r p.2.1 : ℝ)) :=
      continuous_subtype_val.comp (r.continuous.comp (continuous_fst.comp continuous_snd))
    exact ((continuous_const.sub hs).mul ht).add (hs.mul hr)

omit [CompactSpace X] [T2Space X] in
theorem suspension_retime_homotopy_compatible (r : C(unitInterval, unitInterval))
    (r₀ : r 0 = 0) (r₁ : r 1 = 1) :
    ∀ a b : unitInterval × (unitInterval × X),
      timed_suspension_projection a = timed_suspension_projection b →
      suspension_retime_homotopy_source r a = suspension_retime_homotopy_source r b := by
  rintro ⟨s, t, x⟩ ⟨s', t', y⟩ h
  have hs : s = s' := congrArg Prod.fst h
  subst s'
  have hp : Susp.mk (t, x) = Susp.mk (t', y) := congrArg Prod.snd h
  rcases Susp.mk_eq_mk.mp hp with he | ⟨ht, ht'⟩ | ⟨ht, ht'⟩
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    rfl
  · simp only at ht ht'
    subst t
    subst t'
    change Susp.mk (interval_mix s 0 (r 0), x) = Susp.mk (interval_mix s 0 (r 0), y)
    rw [r₀, interval_mix_self]
    exact Susp.mk_zero_eq_mk_zero x y
  · simp only at ht ht'
    subst t
    subst t'
    change Susp.mk (interval_mix s 1 (r 1), x) = Susp.mk (interval_mix s 1 (r 1), y)
    rw [r₁, interval_mix_self]
    exact Susp.mk_one_eq_mk_one x y

def suspension_retime_homotopy (r : C(unitInterval, unitInterval)) (r₀ : r 0 = 0) (r₁ : r 1 = 1) :
    ContinuousMap.Homotopy (ContinuousMap.id (Susp X)) (suspension_retime r r₀ r₁) where
  toContinuousMap := descend_map timed_suspension_projection timed_suspension_quotient
    (suspension_retime_homotopy_source r) (suspension_retime_homotopy_compatible r r₀ r₁)
  map_zero_left x := by
    obtain ⟨⟨t, y⟩, rfl⟩ := Susp.mk_surjective x
    change descend_map _ _ _ _ (timed_suspension_projection (0, (t, y))) = _
    rw [descend_map_apply]
    change Susp.mk (interval_mix 0 t (r t), y) = Susp.mk (t, y)
    rw [interval_mix_zero]
  map_one_left x := by
    obtain ⟨⟨t, y⟩, rfl⟩ := Susp.mk_surjective x
    change descend_map _ _ _ _ (timed_suspension_projection (1, (t, y))) = _
    rw [descend_map_apply]
    change Susp.mk (interval_mix 1 t (r t), y) = Susp.mk (r t, y)
    rw [interval_mix_one]

end MathGauge.PublicProof.Topology
