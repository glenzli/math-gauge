import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space
import formal_oet.vol_01.ch_01_foundations.metric_entropy
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv

namespace OperatorLocalDegeneracy

set_option linter.unusedVariables false

open formal_oet.vol_01.ch_01_foundations

variable {X I : Type} {bot : X} [Fintype I] [DecidableEq I]
variable (d : I → X → X → ENNReal)

noncomputable def r_null (d_in d_out : X → X → ENNReal) (ϕ : Operator X bot) (y : X) (U : Set X) : ENNReal :=
  sSup { r : ENNReal | 0 < r ∧ r < ⊤ ∧ ∀ x ∈ U, d_in x y < r → d_out (ϕ.func x) (ϕ.func y) = 0 }

noncomputable def r_null_subfamily (ϕ : Operator X bot) (i : I) (J : Set I) (y : X) (U : Set X) : ENNReal :=
  r_null (d i) (subfamily_pseudometric d J) ϕ y U

noncomputable def r_null_uniform (d_in d_out : X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) : ENNReal :=
  ⨅ y ∈ U, r_null d_in d_out ϕ y U

noncomputable def N_matrix (ϕ : Operator X bot) (U : Set X) (i j : I) : ENNReal :=
  r_null_uniform (d i) (d j) ϕ U

noncomputable def r_null_subfamily_uniform (ϕ : Operator X bot) (i : I) (J : Set I) (U : Set X) : ENNReal :=
  r_null_uniform (d i) (subfamily_pseudometric d J) ϕ U

theorem prop_3_10_ptwise_min (ϕ : Operator X bot) (i : I) (J : Set I) (hJ : J.Nonempty)
    (y : X) (U : Set X) :
    r_null_subfamily d ϕ i J y U = ⨅ j ∈ J, r_null (d i) (d j) ϕ y U := by
  apply le_antisymm
  · apply le_iInf; intro j
    apply le_iInf; intro hj
    dsimp [r_null_subfamily, r_null]
    apply sSup_le_sSup
    intro r hr
    rcases hr with ⟨hr0, hrt, hball⟩
    refine ⟨hr0, hrt, ?_⟩
    intro x hx hdist
    have hzero := hball x hx hdist
    dsimp [subfamily_pseudometric] at hzero
    rw [← ENNReal.bot_eq_zero, iSup_eq_bot] at hzero
    exact hzero ⟨j, hj⟩
  · set m := ⨅ j ∈ J, r_null (d i) (d j) ϕ y U
    dsimp [r_null_subfamily, r_null]
    by_cases hm0 : m = 0
    · rw [hm0]; exact bot_le
    by_contra! hlt
    rcases exists_between hlt with ⟨c, hc_sup, hc_m⟩
    have hc0 : 0 < c := lt_of_le_of_lt bot_le hc_sup
    have hc_top : c < ⊤ := by
      by_contra! hct
      have : c = ⊤ := top_le_iff.mp hct
      subst this
      exact (not_top_lt hc_m).elim
    have hc_adm : c ∈ { r : ENNReal | 0 < r ∧ r < ⊤ ∧ ∀ x ∈ U, d i x y < r → subfamily_pseudometric d J (ϕ.func x) (ϕ.func y) = 0 } := by
      refine ⟨hc0, hc_top, ?_⟩
      intro x hx hdist
      dsimp [subfamily_pseudometric]
      rw [← ENNReal.bot_eq_zero, iSup_eq_bot]
      intro ⟨j, hj⟩
      have hj_lt : c < r_null (d i) (d j) ϕ y U := lt_of_lt_of_le hc_m (biInf_le (fun j => r_null (d i) (d j) ϕ y U) hj)
      dsimp [r_null] at hj_lt
      rcases lt_sSup_iff.mp hj_lt with ⟨rj, hrj_adm, hcrj⟩
      exact hrj_adm.2.2 x hx (lt_trans hdist hcrj)
    have hc_le : c ≤ sSup { r : ENNReal | 0 < r ∧ r < ⊤ ∧ ∀ x ∈ U, d i x y < r → subfamily_pseudometric d J (ϕ.func x) (ϕ.func y) = 0 } :=
      le_sSup hc_adm
    exact (lt_self_iff_false c).mp (lt_of_le_of_lt hc_le hc_sup)

theorem prop_3_10_uniform_min (ϕ : Operator X bot) (i : I) (J : Set I) (hJ : J.Nonempty) (U : Set X) :
    r_null_subfamily_uniform d ϕ i J U = ⨅ j ∈ J, N_matrix d ϕ U i j := by
  dsimp [r_null_subfamily_uniform, r_null_uniform, N_matrix]
  have h_ptwise : (⨅ y ∈ U, r_null_subfamily d ϕ i J y U) = ⨅ y ∈ U, ⨅ j ∈ J, r_null (d i) (d j) ϕ y U := by
    congr 1; ext y
    congr 1; ext hy
    exact prop_3_10_ptwise_min d ϕ i J hJ y U
  change (⨅ y ∈ U, r_null_subfamily d ϕ i J y U) = _
  rw [h_ptwise]
  apply le_antisymm
  · apply le_iInf; intro j
    apply le_iInf; intro hj
    apply le_iInf; intro y
    apply le_iInf; intro hy
    have h1 := biInf_le (fun y => ⨅ j ∈ J, r_null (d i) (d j) ϕ y U) hy
    have h2 := biInf_le (fun j => r_null (d i) (d j) ϕ y U) hj
    exact le_trans h1 h2
  · apply le_iInf; intro y
    apply le_iInf; intro hy
    apply le_iInf; intro j
    apply le_iInf; intro hj
    have h1 := biInf_le (fun j => ⨅ y ∈ U, r_null (d i) (d j) ϕ y U) hj
    have h2 := biInf_le (fun y => r_null (d i) (d j) ϕ y U) hy
    exact le_trans h1 h2

theorem prop_3_10_antimono (ϕ : Operator X bot) (i : I) (J K : Set I) (hJK : J ⊆ K) (U : Set X) :
    r_null_subfamily_uniform d ϕ i K U ≤ r_null_subfamily_uniform d ϕ i J U := by
  dsimp [r_null_subfamily_uniform, r_null_uniform, r_null_subfamily, r_null]
  apply le_iInf; intro y
  apply le_iInf; intro hy
  refine le_trans (biInf_le (fun y => sSup {r | 0 < r ∧ r < ⊤ ∧ ∀ x ∈ U, d i x y < r → subfamily_pseudometric d K (ϕ.func x) (ϕ.func y) = 0}) hy) ?_
  apply sSup_le_sSup
  intro r hr
  rcases hr with ⟨hr0, hrt, hball⟩
  refine ⟨hr0, hrt, ?_⟩
  intro x hx hdist
  have hzero := hball x hx hdist
  dsimp [subfamily_pseudometric] at hzero ⊢
  rw [← ENNReal.bot_eq_zero, iSup_eq_bot] at hzero ⊢
  intro ⟨j, hj⟩
  exact hzero ⟨j, hJK hj⟩
