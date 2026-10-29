import RecordRealization

noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
open Set

namespace MathGauge.RecordBidual
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def transposeLinear (T : E →L[ℝ] E) : Dual E →ₗ[ℝ] Dual E where
  toFun φ := φ.comp T
  map_add' φ ψ := by ext x; rfl
  map_smul' c φ := by ext x; rfl

def transpose (T : E →L[ℝ] E) : Dual E →L[ℝ] Dual E :=
  (transposeLinear T).mkContinuous ‖T‖ (by
    intro φ
    exact (φ.opNorm_comp_le T).trans_eq (mul_comm ‖φ‖ ‖T‖))

@[simp] theorem transpose_apply (T : E →L[ℝ] E) (φ : Dual E) (x : E) :
    transpose T φ x = φ (T x) := rfl

def imagePart (T : E →L[ℝ] E) (F : FinitePart E) : FinitePart E :=
  ⟨F.val.map (transpose T).toLinearMap, inferInstance⟩

def imagePoint (T : E →L[ℝ] E) (F : FinitePart E) (φ : F.val) : (imagePart T F).val :=
  ⟨transpose T φ.val, ⟨φ.val,φ.property,rfl⟩⟩

/-- Transform of the actual finite records; the next theorem proves the exact T'F formula. -/
def transform (T : E →L[ℝ] E) (r : Record E) : Record E :=
  restrict (r.toBidual.comp (transpose T))

theorem transform_formula (T : E →L[ℝ] E) (r : Record E)
    (F : FinitePart E) (φ : F.val) :
    (transform T r).value F φ = r.value (imagePart T F) (imagePoint T F φ) :=
  r.eval_eq (imagePart T F) (imagePoint T F φ)

theorem transform_bound (T : E →L[ℝ] E) (r : Record E) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ (F : FinitePart E) (φ : F.val), ‖r.value F φ‖ ≤ C*‖φ‖)
    (F : FinitePart E) (φ : F.val) :
    ‖(transform T r).value F φ‖ ≤ (C*‖T‖)*‖φ‖ := by
  rw [transform_formula]
  calc
    _ ≤ C*‖imagePoint T F φ‖ := hb _ _
    _ ≤ C*(‖T‖*‖φ‖) := mul_le_mul_of_nonneg_left
      ((φ.val.opNorm_comp_le T).trans_eq (mul_comm _ _)) hC
    _ = _ := by ring

theorem transform_toBidual (T : E →L[ℝ] E) (r : Record E) :
    (transform T r).toBidual = transpose (transpose T) r.toBidual :=
  toBidual_restrict _

theorem canonical_naturality (T : E →L[ℝ] E) (x : E) :
    transpose (transpose T) (J x) = J (T x) := by
  apply ContinuousLinearMap.ext
  intro φ
  rfl

theorem transform_realization (T : E →L[ℝ] E) {r : Record E} {x : E}
    (hx : Represents r x) : Represents (transform T r) (T x) := by
  apply (represents_iff _ _).mpr
  rw [transform_toBidual, ← (represents_iff _ _).mp hx, canonical_naturality]

/-- Precisely the realizable records, with existence restricted to J(E), never assumed for all. -/
def RealizableRecord := {r : Record E // ∃ x : E, Represents r x}

def recover (r : RealizableRecord (E := E)) : E := Classical.choose r.property

theorem recover_represents (r : RealizableRecord (E := E)) : Represents r.val (recover r) :=
  Classical.choose_spec r.property

theorem recover_unique (r : RealizableRecord (E := E)) (x : E) (hx : Represents r.val x) :
    recover r = x := realization_unique (recover_represents r) hx

theorem recover_exact_stability (r s : RealizableRecord (E := E)) :
    ‖recover r-recover s‖ = recordDistance r.val s.val :=
  exact_stability (recover_represents r) (recover_represents s)

def transformRealizable (T : E →L[ℝ] E) (r : RealizableRecord (E := E)) :
    RealizableRecord (E := E) :=
  ⟨transform T r.val, ⟨T (recover r), transform_realization T (recover_represents r)⟩⟩

theorem recover_covariant (T : E →L[ℝ] E) (r : RealizableRecord (E := E)) :
    recover (transformRealizable T r) = T (recover r) :=
  recover_unique _ _ (transform_realization T (recover_represents r))

end MathGauge.RecordBidual
