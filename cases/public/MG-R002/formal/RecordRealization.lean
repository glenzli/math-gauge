import RecordBidual

noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
open Set

namespace MathGauge.RecordBidual
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The original task's supremum over norm-at-most-one single-observation records. -/
def recordDistance (r s : Record E) : ℝ :=
  sSup {a : ℝ | ∃ φ : Dual E, ‖φ‖ ≤ 1 ∧ a = ‖r.eval φ - s.eval φ‖}

theorem recordDistance_eq_norm (r s : Record E) :
    recordDistance r s = ‖r.toBidual-s.toBidual‖ := by
  let V : Set ℝ := {a | ∃ φ : Dual E, ‖φ‖ ≤ 1 ∧ a = ‖r.eval φ-s.eval φ‖}
  have hz : (0:ℝ) ∈ V := by
    refine ⟨0,by simp,?_⟩
    change 0 = ‖r.toBidual 0-s.toBidual 0‖
    rw [map_zero,map_zero,sub_self,norm_zero]
  have hn : V.Nonempty := ⟨0,hz⟩
  have hV : ∀ a ∈ V, a ≤ ‖r.toBidual-s.toBidual‖ := by
    rintro a ⟨φ,hφ,rfl⟩
    exact (r.toBidual-s.toBidual).unit_le_opNorm φ hφ
  have hb : BddAbove V := ⟨_,hV⟩
  apply le_antisymm
  · exact csSup_le hn hV
  · apply ContinuousLinearMap.opNorm_le_of_unit_norm (le_csSup hb hz)
    intro φ hφ
    exact le_csSup hb ⟨φ,hφ.le,rfl⟩

abbrev J : E →L[ℝ] Bidual E := NormedSpace.inclusionInDoubleDual ℝ E

theorem J_norm (x : E) : ‖J x‖ = ‖x‖ := (NormedSpace.inclusionInDoubleDualLi ℝ).norm_map x

theorem J_injective : Function.Injective (J : E → Bidual E) :=
  (NormedSpace.inclusionInDoubleDualLi ℝ).injective

/-- Actual realization in E, using every original finite-dimensional subspace. -/
def Represents (r : Record E) (x : E) : Prop :=
  ∀ (F : FinitePart E) (φ : F.val), φ.val x = r.value F φ

theorem represents_iff (r : Record E) (x : E) : Represents r x ↔ J x = r.toBidual := by
  constructor
  · intro hx
    apply ContinuousLinearMap.ext
    intro φ
    exact hx (line φ) (linePoint φ)
  · intro hx F φ
    have he := congrArg (fun z : Bidual E => z φ.val) hx
    exact he.trans (r.eval_eq F φ)

theorem realization_exists_iff (r : Record E) :
    (∃ x : E, Represents r x) ↔ r.toBidual ∈ Set.range (J : E → Bidual E) := by
  simp only [Set.mem_range, represents_iff]

theorem realization_unique {r : Record E} {x y : E} (hx : Represents r x) (hy : Represents r y) :
    x = y := J_injective ((represents_iff r x).mp hx |>.trans ((represents_iff r y).mp hy).symm)

theorem realization_norm {r : Record E} {x : E} (hx : Represents r x) :
    ‖x‖ = ‖r.toBidual‖ ∧ ‖x‖ ≤ r.bound := by
  have he : ‖x‖ = ‖r.toBidual‖ := (J_norm x).symm.trans (congrArg norm ((represents_iff r x).mp hx))
  exact ⟨he,he.trans_le r.toBidual_norm⟩

theorem bidual_norm_le_given_bound (r : Record E) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ (F : FinitePart E) (φ : F.val), ‖r.value F φ‖ ≤ C*‖φ‖) :
    ‖r.toBidual‖ ≤ C :=
  r.toBidual.opNorm_le_bound hC (fun φ => hb (line φ) (linePoint φ))

theorem realization_given_bound {r : Record E} {x : E} (hx : Represents r x)
    {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ (F : FinitePart E) (φ : F.val), ‖r.value F φ‖ ≤ C*‖φ‖) : ‖x‖ ≤ C :=
  (realization_norm hx).1.trans_le (bidual_norm_le_given_bound r hC hb)

theorem exact_stability {r s : Record E} {x y : E}
    (hx : Represents r x) (hy : Represents s y) : ‖x-y‖ = recordDistance r s := by
  rw [recordDistance_eq_norm, ← (represents_iff r x).mp hx, ← (represents_iff s y).mp hy,
    ← map_sub, J_norm]

/-- The reference's exact criterion for existence for every record. Surjectivity of the
canonical double-dual map is the definition of reflexivity used here. -/
theorem all_realizable_iff_surjective :
    (∀ r : Record E, ∃ x : E, Represents r x) ↔ Function.Surjective (J : E → Bidual E) := by
  constructor
  · intro hr z
    obtain ⟨x,hx⟩ := hr (restrict z)
    refine ⟨x,?_⟩
    simpa only [toBidual_restrict] using (represents_iff (restrict z) x).mp hx
  · intro hj r
    obtain ⟨x,hx⟩ := hj r.toBidual
    exact ⟨x,(represents_iff r x).mpr hx⟩

end MathGauge.RecordBidual
