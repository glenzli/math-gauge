import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic

noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
open Set

namespace MathGauge.RecordBidual

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
abbrev Dual := E →L[ℝ] ℝ
abbrev Bidual := Dual E →L[ℝ] ℝ

def FinitePart := {F : Submodule ℝ (Dual E) // FiniteDimensional ℝ F}
instance finitePart_finite (F : FinitePart E) : FiniteDimensional ℝ F.val := F.property

/-- Exactly the task's data: every finite-dimensional subspace, inclusion compatibility,
and one finite uniform bound. No global functional is part of this structure. -/
structure Record where
  value : (F : FinitePart E) → F.val →ₗ[ℝ] ℝ
  compatible : ∀ (F G : FinitePart E) (h : F.val ≤ G.val) (φ : F.val),
    value G ⟨φ.val,h φ.property⟩ = value F φ
  bounded : ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : FinitePart E) (φ : F.val),
    ‖value F φ‖ ≤ C * ‖φ‖

variable {E}
def line (φ : Dual E) : FinitePart E := ⟨Submodule.span ℝ {φ}, inferInstance⟩
def linePoint (φ : Dual E) : (line φ).val := ⟨φ,Submodule.subset_span (by simp)⟩
def Record.eval (r : Record E) (φ : Dual E) : ℝ := r.value (line φ) (linePoint φ)

theorem Record.eval_eq (r : Record E) (F : FinitePart E) (φ : F.val) :
    r.eval φ.val = r.value F φ := by
  have hi : (line φ.val).val ≤ F.val := Submodule.span_le.mpr (by
    intro ψ hψ
    simp only [Set.mem_singleton_iff] at hψ
    simpa only [hψ] using φ.property)
  exact (r.compatible (line φ.val) F hi (linePoint φ.val)).symm

def pairPart (φ ψ : Dual E) : FinitePart E := ⟨(line φ).val ⊔ (line ψ).val, inferInstance⟩

theorem Record.eval_add (r : Record E) (φ ψ : Dual E) :
    r.eval (φ+ψ) = r.eval φ + r.eval ψ := by
  let F := pairPart φ ψ
  let a : F.val := ⟨φ, Submodule.mem_sup_left (linePoint φ).property⟩
  let b : F.val := ⟨ψ, Submodule.mem_sup_right (linePoint ψ).property⟩
  exact (r.eval_eq F (a+b)).trans ((r.value F).map_add a b |>.trans
    (congrArg₂ (·+·) (r.eval_eq F a).symm (r.eval_eq F b).symm))

theorem Record.eval_smul (r : Record E) (c : ℝ) (φ : Dual E) :
    r.eval (c • φ) = c * r.eval φ := by
  have he := r.eval_eq (line φ) (c • linePoint φ)
  simpa only [map_smul, smul_eq_mul] using he

def Record.linear (r : Record E) : Dual E →ₗ[ℝ] ℝ where
  toFun := r.eval
  map_add' := r.eval_add
  map_smul' := r.eval_smul

def Record.bound (r : Record E) : ℝ := Classical.choose r.bounded

theorem Record.bound_nonneg (r : Record E) : 0 ≤ r.bound := (Classical.choose_spec r.bounded).1

theorem Record.eval_bound (r : Record E) (φ : Dual E) : ‖r.eval φ‖ ≤ r.bound * ‖φ‖ :=
  (Classical.choose_spec r.bounded).2 (line φ) (linePoint φ)

/-- The global bidual functional is constructed from finite records. -/
def Record.toBidual (r : Record E) : Bidual E := r.linear.mkContinuous r.bound r.eval_bound

@[simp] theorem Record.toBidual_apply (r : Record E) (φ : Dual E) : r.toBidual φ = r.eval φ := rfl

theorem Record.toBidual_norm (r : Record E) : ‖r.toBidual‖ ≤ r.bound :=
  r.toBidual.opNorm_le_bound r.bound_nonneg r.eval_bound

def restrict (z : Bidual E) : Record E where
  value F := z.toLinearMap.comp F.val.subtype
  compatible _F _G _h _φ := rfl
  bounded := ⟨‖z‖,norm_nonneg z,fun _ φ => z.le_opNorm φ.val⟩

theorem toBidual_restrict (z : Bidual E) : (restrict z).toBidual = z := by
  apply ContinuousLinearMap.ext
  intro φ
  rfl

theorem restrict_toBidual_values (r : Record E) (F : FinitePart E) :
    (restrict r.toBidual).value F = r.value F := by
  apply LinearMap.ext
  intro φ
  exact r.eval_eq F φ

@[ext] theorem Record.ext {r s : Record E} (h : ∀ F, r.value F = s.value F) : r = s := by
  cases r with | mk lv lc lb =>
    cases s with | mk mv mc mb =>
      have he : lv = mv := funext h
      subst mv
      rfl

theorem restrict_toBidual (r : Record E) : restrict r.toBidual = r :=
  Record.ext (restrict_toBidual_values r)

def recordEquiv : Record E ≃ Bidual E where
  toFun := Record.toBidual
  invFun := restrict
  left_inv := restrict_toBidual
  right_inv := toBidual_restrict

end MathGauge.RecordBidual
