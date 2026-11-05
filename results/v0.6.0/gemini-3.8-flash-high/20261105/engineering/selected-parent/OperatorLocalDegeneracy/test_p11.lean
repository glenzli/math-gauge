import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space
import formal_oet.vol_01.ch_01_foundations.metric_entropy
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Finset.Basic
import OperatorLocalDegeneracy.ComponentPartition
import OperatorLocalDegeneracy.ComputationalFibers

namespace OperatorLocalDegeneracy

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds

variable {X I : Type} {bot : X} [Fintype I] [DecidableEq I]
variable (d : I → X → X → ENNReal)

noncomputable def r_null (d_in d_out : X → X → ENNReal) (ϕ : Operator X bot) (y : X) (U : Set X) : ENNReal :=
  sSup { r : ENNReal | 0 < r ∧ r < ⊤ ∧ ∀ x ∈ U, d_in x y < r → d_out (ϕ.func x) (ϕ.func y) = 0 }

noncomputable def r_null_single (ϕ : Operator X bot) (i j : I) (y : X) (U : Set X) : ENNReal :=
  r_null (d i) (d j) ϕ y U

noncomputable def r_null_subfamily (ϕ : Operator X bot) (i : I) (J : Set I) (y : X) (U : Set X) : ENNReal :=
  r_null (d i) (subfamily_pseudometric d J) ϕ y U

noncomputable def r_null_uniform (d_in d_out : X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) : ENNReal :=
  ⨅ y ∈ U, r_null d_in d_out ϕ y U

noncomputable def N_matrix (ϕ : Operator X bot) (U : Set X) (i j : I) : ENNReal :=
  r_null_uniform (d i) (d j) ϕ U

noncomputable def r_null_subfamily_uniform (ϕ : Operator X bot) (i : I) (J : Set I) (U : Set X) : ENNReal :=
  r_null_uniform (d i) (subfamily_pseudometric d J) ϕ U

theorem prop_3_8_i_a (ϕ : Operator X bot) (U : Set X) (J : Set I) (hJ : J ⊆ I_const d ϕ U)
    (y : X) (hy : y ∈ ϕ.func '' U) :
    Fib d ϕ J y U = U := by
  ext x
  simp only [Fib, Set.mem_setOf_eq]
  rcases hy with ⟨x0, hx0, rfl⟩
  constructor
  · exact fun h => h.1
  · intro hx
    refine ⟨hx, ?_⟩
    dsimp [subfamily_pseudometric]
    rw [← ENNReal.bot_eq_zero, iSup_eq_bot]
    intro ⟨j, hj⟩
    exact hJ hj x hx x0 hx0

theorem prop_3_8_i_b_ptwise (ϕ : Operator X bot) (U : Set X) (i : I) (J : Set I)
    (hJ : J ⊆ I_const d ϕ U) (y : X) (hy : y ∈ U) :
    r_null_subfamily d ϕ i J y U = ⊤ := by
  dsimp [r_null_subfamily, r_null]
  apply sSup_eq_top.mpr
  intro b hb
  rcases exists_between hb with ⟨r, hbr, hrt⟩
  refine ⟨r, ⟨?_, hrt, ?_⟩, hbr⟩
  · exact lt_of_le_of_lt bot_le hbr
  · intro x hx _
    dsimp [subfamily_pseudometric]
    rw [← ENNReal.bot_eq_zero, iSup_eq_bot]
    intro ⟨j, hj⟩
    exact hJ hj x hx y hy

theorem prop_3_8_i_b_uniform (ϕ : Operator X bot) (U : Set X) (i : I) (J : Set I)
    (hJ : J ⊆ I_const d ϕ U) :
    r_null_subfamily_uniform d ϕ i J U = ⊤ := by
  dsimp [r_null_subfamily_uniform, r_null_uniform]
  rw [iInf_eq_top]
  intro y
  rw [iInf_eq_top]
  intro hy
  exact prop_3_8_i_b_ptwise d ϕ U i J hJ y hy
