import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space
import formal_oet.vol_01.ch_01_foundations.metric_entropy
import formal_oet.vol_01.ch_02_operator_bounds.lip_matrix
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.EReal.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import OperatorLocalDegeneracy.ComponentPartition
import OperatorLocalDegeneracy.ComputationalFibers
import OperatorLocalDegeneracy.NullificationRadius
import OperatorLocalDegeneracy.ThresholdClassification

namespace OperatorLocalDegeneracy

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds

variable {X I : Type} {bot : X} [Fintype I] [DecidableEq I]
variable (d : I → X → X → ENNReal)

/-- CH03-D07: 全有界接口 -/
def IsTotallyBounded (d_metric : X → X → ENNReal) (U : Set X) : Prop :=
  ∀ ε : ENNReal, 0 < ε → covering_number d_metric ε U < ⊤

/-- CH03-D08: 映射熵差 -/
noncomputable def entropy_diff (d_in d_out : X → X → ENNReal) (ϕ : Operator X bot) (ε : ENNReal) (U : Set X) : EReal :=
  metric_entropy d_out ε (ϕ.func '' U) - metric_entropy d_in ε U

noncomputable def subfamily_entropy_diff (ϕ : Operator X bot) (J_in J_out : Set I) (ε : ENNReal) (U : Set X) : EReal :=
  subfamily_metric_entropy d J_out ε (ϕ.func '' U) - subfamily_metric_entropy d J_in ε U

/-- CH03-P18-01: 命题 3.15 (i) 严格低于统一半径的输入点对输出零距 -/
theorem prop_3_15_i (d_in d_out : X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    (hdist : d_in x y < r_null_uniform d_in d_out ϕ U) :
    d_out (ϕ.func x) (ϕ.func y) = 0 := by
  have h_le := biInf_le (fun z => r_null d_in d_out ϕ z U) hy
  have hlt : d_in x y < r_null d_in d_out ϕ y U := lt_of_lt_of_le hdist h_le
  exact prop_3_11_lt_sSup d_in d_out ϕ U y hx hlt

/-- CH03-P18-02: 命题 3.15 (ii) 输出正分离推出输入距离≥统一半径 -/
theorem prop_3_15_ii (d_in d_out : X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    (hsep : 0 < d_out (ϕ.func x) (ϕ.func y)) :
    r_null_uniform d_in d_out ϕ U ≤ d_in x y := by
  by_contra! hlt
  have hzero := prop_3_15_i d_in d_out ϕ U hx hy hlt
  rw [hzero] at hsep
  exact (lt_self_iff_false 0).mp hsep

def two_pt_alpha_in (α : ENNReal) (x y : Option (Fin 2)) : ENNReal :=
  match x, y with
  | none, none => 0
  | some a, some b => if a = b then 0 else α
  | _, _ => ⊤

def two_pt_eps_out (ε : ENNReal) (x y : Option (Fin 2)) : ENNReal :=
  match x, y with
  | none, none => 0
  | some a, some b => if a = b then 0 else ε
  | _, _ => ⊤

def two_pt_id_op : Operator (Option (Fin 2)) none where
  func := id
  preserves_bot := rfl

def two_pt_U_set : Set (Option (Fin 2)) := { some 0, some 1 }

lemma mem_two_pt_U_set (x : Option (Fin 2)) : x ∈ two_pt_U_set ↔ x = some 0 ∨ x = some 1 := by
  dsimp [two_pt_U_set]; simp

/-- CH03-P18-03: 命题 3.15 (iii) 对每个规定的有限正α构造两点和有限正ε，含输出距离无穷情形 -/
theorem prop_3_15_iii (α : ENNReal) (hα_pos : 0 < α) (hα_top : α < ⊤)
    (ε : ENNReal) (hε_pos : 0 < ε) :
    r_null_uniform (two_pt_alpha_in α) (two_pt_eps_out ε) two_pt_id_op two_pt_U_set = α ∧
    (two_pt_eps_out ε) (some 0) (some 1) = ε := by
  have h_out : (two_pt_eps_out ε) (some 0) (some 1) = ε := by
    dsimp [two_pt_eps_out]
  refine ⟨?_, h_out⟩
  dsimp [r_null_uniform, r_null]
  apply le_antisymm
  · have h0 : (some 0 : Option (Fin 2)) ∈ two_pt_U_set := by rw [mem_two_pt_U_set]; left; rfl
    refine le_trans (biInf_le (fun y => sSup {r | 0 < r ∧ r < ⊤ ∧ ∀ x ∈ two_pt_U_set, two_pt_alpha_in α x y < r → two_pt_eps_out ε (two_pt_id_op.func x) (two_pt_id_op.func y) = 0}) h0) ?_
    apply sSup_le
    intro r hr
    rcases hr with ⟨hr0, hrt, hball⟩
    by_contra! hgt
    have h1_mem : (some 1 : Option (Fin 2)) ∈ two_pt_U_set := by rw [mem_two_pt_U_set]; right; rfl
    have hdist : two_pt_alpha_in α (some 1) (some 0) < r := by
      dsimp [two_pt_alpha_in]; exact hgt
    have hzero := hball (some 1) h1_mem hdist
    dsimp [two_pt_eps_out, two_pt_id_op] at hzero
    rw [hzero] at hε_pos
    exact (lt_self_iff_false 0).mp hε_pos
  · apply le_iInf; intro y
    apply le_iInf; intro hy
    apply le_sSup
    refine ⟨hα_pos, hα_top, ?_⟩
    intro x hx hdist
    rw [mem_two_pt_U_set] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · simp [two_pt_eps_out, two_pt_id_op]
    · exfalso; dsimp [two_pt_alpha_in] at hdist
      exact (lt_self_iff_false α).mp hdist
    · exfalso; dsimp [two_pt_alpha_in] at hdist
      exact (lt_self_iff_false α).mp hdist
    · simp [two_pt_eps_out, two_pt_id_op]

/-- CH03-P19-01: 命题 3.16 (i) 统一半径≥有限正阈值时，每个中心的开球包含在纤维中 -/
theorem prop_3_16_i (ϕ : Operator X bot) (i j : I) (U : Set X)
    (τ_N : ENNReal) (hτ_pos : 0 < τ_N) (hN : τ_N ≤ N_matrix d ϕ U i j)
    (c : X) (hc : c ∈ U) :
    { x ∈ U | d i x c < τ_N } ⊆ Fib_single d ϕ j (ϕ.func c) U := by
  intro x hx
  simp only [Fib_single, Set.mem_setOf_eq] at hx ⊢
  refine ⟨hx.1, ?_⟩
  have hN_le : N_matrix d ϕ U i j ≤ r_null (d i) (d j) ϕ c U := by
    dsimp [N_matrix, r_null_uniform]
    exact biInf_le (fun z => r_null (d i) (d j) ϕ z U) hc
  have hlt : d i x c < r_null (d i) (d j) ϕ c U :=
    lt_of_lt_of_le (lt_of_lt_of_le hx.2 hN) hN_le
  exact prop_3_11_lt_sSup (d i) (d j) ϕ U c hx.1 hlt

/-- CH03-P19-02: 命题 3.16 (ii-a) 对任意B⊆A，证明覆盖数不等式 -/
theorem prop_3_16_ii_a [DecidableEq X] (ϕ : Operator X bot) (i j : I) (A : Set X)
    (τ_N : ENNReal) (hτ_pos : 0 < τ_N) (hN : τ_N ≤ N_matrix d ϕ A i j)
    (B : Set X) (hBA : B ⊆ A) (ε : ENNReal) (hε_pos : 0 < ε) :
    covering_number (d j) ε (ϕ.func '' B) ≤ covering_number (d i) τ_N B := by
  dsimp [covering_number]
  apply le_iInf; intro centers
  apply le_iInf; intro hnet
  set out_centers := centers.image ϕ.func
  have hout_net : InternalEpsilonNet (d j) ε (ϕ.func '' B) out_centers := by
    dsimp [InternalEpsilonNet] at hnet ⊢
    refine ⟨?_, ?_⟩
    · intro y hy
      rw [Finset.mem_coe, Finset.mem_image] at hy
      rcases hy with ⟨c, hc, rfl⟩
      exact ⟨c, hnet.1 hc, rfl⟩
    · rintro y ⟨x, hxB, rfl⟩
      rcases hnet.2 x hxB with ⟨c, hc, hdist⟩
      have hcA : c ∈ A := hBA (hnet.1 hc)
      have hxA : x ∈ A := hBA hxB
      have hzero := prop_3_16_i d ϕ i j A τ_N hτ_pos hN c hcA ⟨hxA, hdist⟩
      dsimp [Fib_single] at hzero
      refine ⟨ϕ.func c, Finset.mem_image_of_mem ϕ.func hc, ?_⟩
      rw [hzero.2]
      exact hε_pos
  have h_le : covering_number (d j) ε (ϕ.func '' B) ≤ (out_centers.card : ENNReal) := by
    dsimp [covering_number]
    refine le_trans (iInf_le (fun s => ⨅ (_ : InternalEpsilonNet (d j) ε (ϕ.func '' B) s), (s.card : ENNReal)) out_centers) ?_
    exact iInf_le (fun (_ : InternalEpsilonNet (d j) ε (ϕ.func '' B) out_centers) => (out_centers.card : ENNReal)) hout_net
  have h_card : (out_centers.card : ENNReal) ≤ (centers.card : ENNReal) := by
    exact Nat.cast_le.mpr (Finset.card_image_le)
  exact le_trans h_le h_card

lemma log2_ereal_mono {a b : ENNReal} (ha : 1 ≤ a) (hab : a ≤ b) :
    log2_ereal a ≤ log2_ereal b := by
  have ha0 : a ≠ 0 := by intro h; rw [h] at ha; revert ha; norm_num
  have hb0 : b ≠ 0 := by intro h; rw [h] at hab; have := le_trans ha hab; revert this; norm_num
  dsimp [log2_ereal]
  rw [if_neg ha0, if_neg hb0]
  by_cases hb_top : b = ⊤
  · rw [if_pos hb_top]; exact le_top
  · rw [if_neg hb_top]
    have ha_top : a ≠ ⊤ := by intro h; rw [h] at hab; rw [top_le_iff.mp hab] at hb_top; contradiction
    rw [if_neg ha_top]
    norm_cast
    have ha_real : 1 ≤ a.toReal := by
      have := (ENNReal.toReal_le_toReal (by norm_num) ha_top).mpr ha
      simpa using this
    have hab_real : a.toReal ≤ b.toReal := (ENNReal.toReal_le_toReal ha_top hb_top).mpr hab
    have h2 : (1 : ℝ) < 2 := by norm_num
    have ha_pos : 0 < a.toReal := by linarith
    have hb_pos : 0 < b.toReal := by linarith
    exact (Real.logb_le_logb h2 ha_pos hb_pos).mpr hab_real

/-- CH03-P19-03: 命题 3.16 (ii-b) B非空时由覆盖数单调推出熵不等式 -/
theorem prop_3_16_ii_b [DecidableEq X] (ϕ : Operator X bot) (i j : I) (A : Set X)
    (τ_N : ENNReal) (hτ_pos : 0 < τ_N) (hN : τ_N ≤ N_matrix d ϕ A i j)
    (B : Set X) (hBA : B ⊆ A) (hB : B.Nonempty) (ε : ENNReal) (hε_pos : 0 < ε) :
    metric_entropy (d j) ε (ϕ.func '' B) ≤ metric_entropy (d i) τ_N B := by
  dsimp [metric_entropy]
  have hcov := prop_3_16_ii_a d ϕ i j A τ_N hτ_pos hN B hBA ε hε_pos
  have h_img_nonempty : (ϕ.func '' B).Nonempty := hB.image ϕ.func
  have h_one_le := one_le_covering_number_of_nonempty (d j) ε (ϕ.func '' B) h_img_nonempty
  exact log2_ereal_mono h_one_le hcov

/-- CH03-P20-01: 命题 3.16 后正文反例：点态正半径不能代替统一阈值 -/
theorem prop_3_16_counterexample (τ : ENNReal) (hτ_pos : 0 < τ) (hτ_top : τ < ⊤) :
    ∃ (a : ℝ) (B : Set (Option ℝ)),
      0 < a ∧ a ≤ 1 ∧ ENNReal.ofReal (2 * a) < τ ∧
      B ⊆ U_step ∧
      covering_number d_real_bot τ B ≤ 1 ∧
      2 ≤ covering_number d_real_bot (ENNReal.ofReal (1 / 2)) (step_op.func '' B) := by
  lift τ to NNReal using hτ_top.ne
  have hτ_pos_real : 0 < (τ : ℝ) := by rwa [ENNReal.coe_pos] at hτ_pos
  set a : ℝ := min (1 / 2) ((τ : ℝ) / 4)
  have ha_pos : 0 < a := by
    apply lt_min (by norm_num)
    linarith
  have ha_le1 : a ≤ 1 := le_trans (min_le_left _ _) (by norm_num)
  have h2a_lt : 2 * a < (τ : ℝ) := by
    have : a ≤ (τ : ℝ) / 4 := min_le_right _ _
    linarith
  have h2a_lt_enn : ENNReal.ofReal (2 * a) < ↑τ := by
    rw [← ENNReal.ofReal_coe_nnreal]
    rw [ENNReal.ofReal_lt_ofReal_iff hτ_pos_real]
    exact h2a_lt
  set B : Set (Option ℝ) := { some (-a), some a }
  have hB_sub : B ⊆ U_step := by
    intro x hx
    simp only [B, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · refine ⟨-a, rfl, Or.inl ⟨by linarith, by linarith⟩⟩
    · refine ⟨a, rfl, Or.inr ⟨ha_pos, ha_le1⟩⟩
  have hB_cov1 : covering_number d_real_bot (↑τ) B ≤ 1 := by
    dsimp [covering_number]
    set c : Finset (Option ℝ) := { some a }
    have hnet : InternalEpsilonNet d_real_bot (↑τ) B c := by
      dsimp [InternalEpsilonNet, c, B]
      refine ⟨by simp, ?_⟩
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · use some a
        simp only [Finset.mem_singleton, true_and]
        rw [d_real_bot_some]
        have : |-a - a| = 2 * a := by
          have : -a - a = -(2 * a) := by ring
          rw [this, abs_neg, abs_of_pos (by linarith)]
        rw [this]
        exact h2a_lt_enn
      · use some a
        simp only [Finset.mem_singleton, true_and]
        rw [d_real_bot_self]
        rwa [ENNReal.coe_pos]
    refine le_trans (iInf_le (fun s => ⨅ (_ : InternalEpsilonNet d_real_bot (↑τ) B s), (s.card : ENNReal)) c) ?_
    refine le_trans (iInf_le (fun (_ : InternalEpsilonNet d_real_bot (↑τ) B c) => (c.card : ENNReal)) hnet) ?_
    simp [c]
  have h_img : step_op.func '' B = { some 0, some 1 } := by
    ext y
    simp only [B, Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, rfl | rfl, rfl⟩
      · dsimp [step_op, step_func]
        rw [if_neg (by linarith)]
        left; rfl
      · dsimp [step_op, step_func]
        rw [if_pos ha_pos]
        right; rfl
    · rintro (rfl | rfl)
      · use some (-a)
        refine ⟨Or.inl rfl, ?_⟩
        dsimp [step_op, step_func]
        rw [if_neg (by linarith)]
      · use some a
        refine ⟨Or.inr rfl, ?_⟩
        dsimp [step_op, step_func]
        rw [if_pos ha_pos]
  have h_out_ge2 : 2 ≤ covering_number d_real_bot (ENNReal.ofReal (1 / 2)) (step_op.func '' B) := by
    rw [h_img]
    dsimp [covering_number]
    apply le_iInf; intro c
    apply le_iInf; intro hnet
    by_contra! hlt
    have hcard : c.card ≤ 1 := by
      exact Nat.le_of_lt_succ (Nat.cast_lt.mp hlt)
    interval_cases hc : c.card
    · have : c = ∅ := Finset.card_eq_zero.mp hc
      dsimp [InternalEpsilonNet] at hnet
      subst this
      have hmem : (some 0 : Option ℝ) ∈ ({ some 0, some 1 } : Set (Option ℝ)) := by simp
      rcases hnet.2 (some 0) hmem with ⟨z, hz, _⟩
      simp at hz
    · rcases Finset.card_eq_one.mp hc with ⟨w, rfl⟩
      dsimp [InternalEpsilonNet] at hnet
      have hw_mem : w ∈ ({ some 0, some 1 } : Set (Option ℝ)) := by
        have := hnet.1 (by simp)
        exact this
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw_mem
      rcases hw_mem with rfl | rfl
      · rcases hnet.2 (some 1) (by simp) with ⟨z, hz, hdist⟩
        simp only [Finset.mem_singleton] at hz; subst hz
        dsimp [d_real_bot] at hdist
        have h_contra : (1 : ENNReal) < ENNReal.ofReal (1 / 2) := by
          have : |(1 : ℝ) - 0| = 1 := by norm_num
          rw [this] at hdist
          exact hdist
        have h_le := le_of_lt h_contra
        rw [ENNReal.ofReal_le_ofReal_iff (by norm_num)] at h_le
        norm_num at h_le
      · rcases hnet.2 (some 0) (by simp) with ⟨z, hz, hdist⟩
        simp only [Finset.mem_singleton] at hz; subst hz
        dsimp [d_real_bot] at hdist
        have h_contra : (1 : ENNReal) < ENNReal.ofReal (1 / 2) := by
          have : |(0 : ℝ) - 1| = 1 := by norm_num
          rw [this] at hdist
          exact hdist
        have h_le := le_of_lt h_contra
        rw [ENNReal.ofReal_le_ofReal_iff (by norm_num)] at h_le
        norm_num at h_le
  exact ⟨a, B, ha_pos, ha_le1, h2a_lt_enn, hB_sub, hB_cov1, h_out_ge2⟩

/-- CH03-P21-01: 推论 3.17 (i) 小输入域上的整体零化判据 -/
theorem cor_3_17_i (ϕ : Operator X bot) (i j : I) (A : Set X)
    (τ_σ τ_N : ENNReal) (h_diam : diam (d i) A < τ_σ) (h_tau : τ_σ ≤ τ_N) :
    τ_N ≤ N_matrix d ϕ A i j ↔ ∀ x ∈ A, ∀ y ∈ A, d j (ϕ.func x) (ϕ.func y) = 0 := by
  constructor
  · intro hN x hx y hy
    have hdist_le : d i x y ≤ diam (d i) A := by
      dsimp [diam]
      refine le_iSup_of_le x ?_
      refine le_iSup_of_le hx ?_
      refine le_iSup_of_le y ?_
      refine le_iSup_of_le hy le_rfl
    have hlt : d i x y < N_matrix d ϕ A i j :=
      lt_of_le_of_lt hdist_le (lt_of_lt_of_le h_diam (le_trans h_tau hN))
    have h_unif : N_matrix d ϕ A i j = r_null_uniform (d i) (d j) ϕ A := rfl
    rw [h_unif] at hlt
    exact prop_3_15_i (d i) (d j) ϕ A hx hy hlt
  · intro hconst
    have hj_const : j ∈ I_const d ϕ A := hconst
    have htop := prop_3_8_i_b_uniform d ϕ A j {j} (by intro k hk; simp at hk; subst hk; exact hj_const)
    dsimp [r_null_subfamily_uniform] at htop
    have hdj : subfamily_pseudometric d {j} = d j := by
      ext u v; dsimp [subfamily_pseudometric]; simp
    rw [hdj] at htop
    have hN : N_matrix d ϕ A j j = ⊤ := htop
    have hj_i : N_matrix d ϕ A i j = ⊤ := by
      dsimp [N_matrix, r_null_uniform, r_null]
      rw [iInf_eq_top]; intro y; rw [iInf_eq_top]; intro hy
      apply sSup_eq_top.mpr; intro b hb
      rcases exists_between hb with ⟨r, hbr, hrt⟩
      refine ⟨r, ⟨lt_of_le_of_lt bot_le hbr, hrt, ?_⟩, hbr⟩
      intro x hx _
      exact hconst x hx y hy
    rw [hj_i]
    exact le_top

/-- CH03-P21-02: 推论 3.17 (ii) 整体输出零距时输出内部覆盖数恰为1 -/
theorem cor_3_17_ii [DecidableEq X] (ϕ : Operator X bot) (i j : I) (A : Set X) (hA : A.Nonempty)
    (h_zero : ∀ x ∈ A, ∀ y ∈ A, d j (ϕ.func x) (ϕ.func y) = 0)
    (ε : ENNReal) (hε_pos : 0 < ε) :
    covering_number (d j) ε (ϕ.func '' A) = 1 := by
  rcases hA with ⟨x0, hx0⟩
  have h_img_nonempty : (ϕ.func '' A).Nonempty := ⟨ϕ.func x0, ⟨x0, hx0, rfl⟩⟩
  have h1_le := one_le_covering_number_of_nonempty (d j) ε (ϕ.func '' A) h_img_nonempty
  apply le_antisymm _ h1_le
  set c : Finset X := { ϕ.func x0 }
  have hnet : InternalEpsilonNet (d j) ε (ϕ.func '' A) c := by
    dsimp [InternalEpsilonNet, c]
    refine ⟨by simp [hx0], ?_⟩
    rintro y ⟨x, hx, rfl⟩
    refine ⟨ϕ.func x0, by simp, ?_⟩
    rw [h_zero x hx x0 hx0]
    exact hε_pos
  dsimp [covering_number]
  refine le_trans (iInf_le (fun s => ⨅ (_ : InternalEpsilonNet (d j) ε (ϕ.func '' A) s), (s.card : ENNReal)) c) ?_
  refine le_trans (iInf_le (fun (_ : InternalEpsilonNet (d j) ε (ϕ.func '' A) c) => (c.card : ENNReal)) hnet) ?_
  simp [c]

/-- CH03-P22-01: 注 有限集上映射熵差的良定性 -/
theorem remark_entropy_diff_well_defined [DecidableEq X] (ϕ : Operator X bot) (i j : I)
    (U : Set X) (hU_fin : U.Finite) (hU_nonempty : U.Nonempty)
    (ε : ENNReal) (hε_pos : 0 < ε) :
    1 ≤ covering_number (d i) ε U ∧ covering_number (d i) ε U < ⊤ ∧
    1 ≤ covering_number (d j) ε (ϕ.func '' U) ∧ covering_number (d j) ε (ϕ.func '' U) < ⊤ := by
  have h_img_fin : (ϕ.func '' U).Finite := hU_fin.image ϕ.func
  have h_img_nonempty : (ϕ.func '' U).Nonempty := hU_nonempty.image ϕ.func
  have h1_in := one_le_covering_number_of_nonempty (d i) ε U hU_nonempty
  have h1_out := one_le_covering_number_of_nonempty (d j) ε (ϕ.func '' U) h_img_nonempty
  set c_in := hU_fin.toFinset
  have hnet_in : InternalEpsilonNet (d i) ε U c_in := by
    dsimp [InternalEpsilonNet, c_in]
    refine ⟨by simp, ?_⟩
    intro x hx
    refine ⟨x, by simp [hx], ?_⟩
    have hd_self : d i x x = 0 := by
      -- since d i is a pseudometric or by dist_self if ExtendedPseudoMetric
      sorry
    rw [hd_self]
    exact hε_pos
  sorry

