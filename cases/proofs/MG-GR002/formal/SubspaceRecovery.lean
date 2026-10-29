import ReflexiveRecovery
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Module.HahnBanach

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
namespace MathGauge.RecordBidual
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def annihilates (Y : Submodule ℝ E) (φ : Dual E) : Prop := ∀ y ∈ Y, φ y = 0

def quotientMap (Y : Submodule ℝ E) : E →L[ℝ] E ⧸ Y :=
  Y.mkQ.mkContinuous 1 (fun x => by simpa using Submodule.Quotient.norm_mk_le Y x)

theorem quotientMap_norm_le (Y : Submodule ℝ E) : ‖quotientMap Y‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  simpa using Submodule.Quotient.norm_mk_le Y x

theorem quotient_norm_distance (Y : Submodule ℝ E) (x : E) :
    ‖quotientMap Y x‖ = infDist x Y :=
  QuotientAddGroup.norm_mk (S := Y.toAddSubgroup) x

theorem annihilator_le_distance (Y : Submodule ℝ E) (x : E) (φ : Dual E)
    (hφ : annihilates Y φ) (hn : ‖φ‖ ≤ 1) : ‖φ x‖ ≤ infDist x Y := by
  apply (le_infDist (show (Y : Set E).Nonempty from ⟨0,Y.zero_mem⟩)).mpr
  intro y hy
  have he : φ x = φ (x-y) := by rw [map_sub,hφ y hy,sub_zero]
  rw [he,dist_eq_norm]
  exact (φ.le_opNorm _).trans (by simpa using mul_le_mul_of_nonneg_right hn (norm_nonneg (x-y)))

theorem exists_norming_annihilator (Y : Submodule ℝ E) (x : E) :
    ∃ φ : Dual E, annihilates Y φ ∧ ‖φ‖ ≤ 1 ∧ φ x = infDist x Y := by
  obtain ⟨g,hg,hgx⟩ := exists_dual_vector'' ℝ (quotientMap Y x)
  refine ⟨g.comp (quotientMap Y),?_,?_,?_⟩
  · intro y hy
    change g (Submodule.Quotient.mk y : E ⧸ Y) = 0
    rw [(Submodule.Quotient.mk_eq_zero Y).mpr hy,map_zero]
  · exact (g.opNorm_comp_le _).trans
      (by nlinarith [quotientMap_norm_le Y,norm_nonneg g,norm_nonneg (quotientMap Y)])
  · exact hgx.trans (quotient_norm_distance Y x)

def annihilatorValues (Y : Submodule ℝ E) (r : Record E) : Set ℝ :=
  {a | ∃ φ : Dual E, annihilates Y φ ∧ ‖φ‖ ≤ 1 ∧ a = ‖r.toBidual φ‖}

theorem record_distance_formula (Y : Submodule ℝ E) (r : Record E) (x : E)
    (hx : Represents r x) : infDist x Y = sSup (annihilatorValues Y r) := by
  have he : ∀ φ : Dual E, r.toBidual φ = φ x := by
    intro φ
    exact (congrArg (fun z : Bidual E => z φ) ((represents_iff r x).mp hx)).symm
  have hnon : (annihilatorValues Y r).Nonempty := by
    refine ⟨0,0,?_,by simp,?_⟩
    · intro y hy; rfl
    · rw [he]; simp
  have hb : BddAbove (annihilatorValues Y r) := by
    refine ⟨infDist x Y,?_⟩
    rintro a ⟨φ,hφ,hφn,rfl⟩
    rw [he]
    exact annihilator_le_distance Y x φ hφ hφn
  apply le_antisymm
  · obtain ⟨φ,hφ,hn,hval⟩ := exists_norming_annihilator Y x
    apply le_csSup hb
    refine ⟨φ,hφ,hn,?_⟩
    rw [he,hval,Real.norm_eq_abs,abs_of_nonneg infDist_nonneg]
  · apply csSup_le hnon
    rintro a ⟨φ,hφ,hn,rfl⟩
    rw [he]
    exact annihilator_le_distance Y x φ hφ hn

theorem member_iff_annihilator (Y : Submodule ℝ E) (hY : IsClosed (Y : Set E))
    (r : Record E) (x : E) (hx : Represents r x) :
    x ∈ Y ↔ ∀ φ : Dual E, annihilates Y φ → r.toBidual φ = 0 := by
  have he : ∀ φ : Dual E, r.toBidual φ = φ x := by
    intro φ
    exact (congrArg (fun z : Bidual E => z φ) ((represents_iff r x).mp hx)).symm
  constructor
  · intro h φ hφ
    rw [he,hφ x h]
  · intro h
    obtain ⟨φ,hφ,hn,hval⟩ := exists_norming_annihilator Y x
    have hz : infDist x Y = 0 := hval.symm.trans ((he φ).symm.trans (h φ hφ))
    change x ∈ (Y : Set E)
    rw [← hY.closure_eq]
    exact (mem_closure_iff_infDist_zero (show (Y : Set E).Nonempty from ⟨0,Y.zero_mem⟩)).mpr hz

end MathGauge.RecordBidual
