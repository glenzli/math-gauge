
import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space
import formal_oet.vol_01.ch_01_foundations.metric_entropy
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import OperatorLocalDegeneracy.CoveringEntropy

namespace OperatorLocalDegeneracy

open formal_oet.vol_01.ch_01_foundations

def ex35_U : Set (Option ℝ) := { some 0, some 1, some 2, some 3 }

lemma mem_ex35_U (x : Option ℝ) : x ∈ ex35_U ↔ x = some 0 ∨ x = some 1 ∨ x = some 2 ∨ x = some 3 := by
  dsimp [ex35_U]; simp

noncomputable def ex35_f : Operator (Option ℝ) none where
  func := fun x => match x with
    | some r => if r = 0 then some 0 else if r = 1 then some 1 else if r = 2 then some 2 else if r = 3 then some 3 else none
    | none => none
  preserves_bot := rfl

noncomputable def ex35_g : Operator (Option ℝ) none where
  func := fun x => match x with
    | some r => if r = 0 then some 0 else if r = 1 then some 3 else if r = 2 then some 1 else if r = 3 then some 2 else none
    | none => none
  preserves_bot := rfl

lemma ex35_f_0 : ex35_f.func (some 0) = some 0 := by dsimp [ex35_f]; norm_num
lemma ex35_f_1 : ex35_f.func (some 1) = some 1 := by dsimp [ex35_f]; norm_num
lemma ex35_f_2 : ex35_f.func (some 2) = some 2 := by dsimp [ex35_f]; norm_num
lemma ex35_f_3 : ex35_f.func (some 3) = some 3 := by dsimp [ex35_f]; norm_num

lemma ex35_f_eq_id (x : Option ℝ) (hx : x ∈ ex35_U) : ex35_f.func x = x := by
  rw [mem_ex35_U] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact ex35_f_0
  · exact ex35_f_1
  · exact ex35_f_2
  · exact ex35_f_3

lemma ex35_g_0 : ex35_g.func (some 0) = some 0 := by dsimp [ex35_g]; norm_num
lemma ex35_g_1 : ex35_g.func (some 1) = some 3 := by dsimp [ex35_g]; norm_num
lemma ex35_g_2 : ex35_g.func (some 2) = some 1 := by dsimp [ex35_g]; norm_num
lemma ex35_g_3 : ex35_g.func (some 3) = some 2 := by dsimp [ex35_g]; norm_num

-- (i) Piecewise covering number of ex35_U
theorem ex35_cov_gt_2 (ε : ENNReal) (hε : 2 < ε) :
    covering_number d_real_bot ε ex35_U = 1 := by
  dsimp [covering_number]
  apply le_antisymm
  · set centers : Finset (Option ℝ) := { some 1 }
    have hnet : InternalEpsilonNet d_real_bot ε ex35_U centers := by
      dsimp [InternalEpsilonNet, centers]
      refine ⟨?_, ?_⟩
      · intro x hx; simp only [Finset.mem_coe, Finset.mem_singleton] at hx; subst hx; simp [mem_ex35_U]
      · intro x hx
        refine ⟨some 1, Finset.mem_singleton_self _, ?_⟩
        rw [mem_ex35_U] at hx
        rcases hx with rfl | rfl | rfl | rfl <;> {
          dsimp [d_real_bot]
          have : ENNReal.ofReal (abs ((_ : ℝ) - 1)) ≤ 2 := by norm_num
          exact lt_of_le_of_lt (by norm_num) hε
        }
    have h_le := iInf_le (fun s => ⨅ (_ : InternalEpsilonNet d_real_bot ε ex35_U s), (s.card : ENNReal)) centers
    have h_le2 := iInf_le (fun (_ : InternalEpsilonNet d_real_bot ε ex35_U centers) => (centers.card : ENNReal)) hnet
    have hcard : centers.card = 1 := Finset.card_singleton _
    have h_trans := le_trans h_le h_le2
    rw [hcard] at h_trans
    exact_mod_cast h_trans
  · exact one_le_covering_number_of_nonempty d_real_bot ε ex35_U ⟨some 0, by simp [mem_ex35_U]⟩

theorem ex35_cov_1_to_2 (ε : ENNReal) (h1 : 1 < ε) (h2 : ε ≤ 2) :
    covering_number d_real_bot ε ex35_U = 2 := by
  dsimp [covering_number]
  apply le_antisymm
  · set centers : Finset (Option ℝ) := { some 1, some 2 }
    have hnet : InternalEpsilonNet d_real_bot ε ex35_U centers := by
      dsimp [InternalEpsilonNet, centers]
      refine ⟨?_, ?_⟩
      · intro x hx; simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> simp [mem_ex35_U]
      · intro x hx
        rw [mem_ex35_U] at hx
        rcases hx with rfl | rfl | rfl | rfl
        · refine ⟨some 1, Finset.mem_insert_self _ _, ?_⟩
          dsimp [d_real_bot]; norm_num; exact h1
        · refine ⟨some 1, Finset.mem_insert_self _ _, ?_⟩
          dsimp [d_real_bot]; norm_num; exact lt_trans (by norm_num) h1
        · refine ⟨some 2, Finset.mem_insert_of_mem (Finset.mem_singleton_self _), ?_⟩
          dsimp [d_real_bot]; norm_num; exact lt_trans (by norm_num) h1
        · refine ⟨some 2, Finset.mem_insert_of_mem (Finset.mem_singleton_self _), ?_⟩
          dsimp [d_real_bot]; norm_num; exact h1
    have h_le := iInf_le (fun s => ⨅ (_ : InternalEpsilonNet d_real_bot ε ex35_U s), (s.card : ENNReal)) centers
    have h_le2 := iInf_le (fun (_ : InternalEpsilonNet d_real_bot ε ex35_U centers) => (centers.card : ENNReal)) hnet
    have hcard : centers.card = 2 := by
      dsimp [centers]
      rw [Finset.card_insert_of_notMem]
      · rw [Finset.card_singleton]
      · intro h; simp only [Finset.mem_singleton, Option.some.injEq] at h; norm_num at h
    have h_trans := le_trans h_le h_le2
    rw [hcard] at h_trans
    exact_mod_cast h_trans
  · apply le_iInf; intro c
    apply le_iInf; intro hnet
    by_contra! hlt
    have hcard : c.card ≤ 1 := Nat.le_of_lt_succ (Nat.cast_lt.mp hlt)
    have hc_nonempty : c.Nonempty := by
      rcases hnet.2 (some 0) (by simp [mem_ex35_U]) with ⟨w, hw, _⟩
      exact ⟨w, hw⟩
    have hcard1 : c.card = 1 := le_antisymm hcard (Finset.Nonempty.card_pos hc_nonempty)
    rcases Finset.card_eq_one.mp hcard1 with ⟨c0, rfl⟩
    have hc0_in : c0 ∈ ex35_U := by
      have := hnet.1
      simp only [Finset.coe_singleton, Set.singleton_subset_iff] at this
      exact this
    rw [mem_ex35_U] at hc0_in
    rcases hc0_in with rfl | rfl | rfl | rfl
    · rcases hnet.2 (some 3) (by simp [mem_ex35_U]) with ⟨w, hw, hd⟩
      simp only [Finset.mem_singleton] at hw; subst hw
      dsimp [d_real_bot] at hd
      have : (3 : ENNReal) < ε := by norm_num at hd; exact hd
      have : ε ≤ 2 := h2
      have : (3 : ENNReal) < 2 := lt_of_lt_of_le (by assumption) (by assumption)
      norm_num at this
    · rcases hnet.2 (some 3) (by simp [mem_ex35_U]) with ⟨w, hw, hd⟩
      simp only [Finset.mem_singleton] at hw; subst hw
      dsimp [d_real_bot] at hd
      have : (2 : ENNReal) < ε := by norm_num at hd; exact hd
      exact (not_le_of_gt this) h2
    · rcases hnet.2 (some 0) (by simp [mem_ex35_U]) with ⟨w, hw, hd⟩
      simp only [Finset.mem_singleton] at hw; subst hw
      dsimp [d_real_bot] at hd
      have : (2 : ENNReal) < ε := by norm_num at hd; exact hd
      exact (not_le_of_gt this) h2
    · rcases hnet.2 (some 0) (by simp [mem_ex35_U]) with ⟨w, hw, hd⟩
      simp only [Finset.mem_singleton] at hw; subst hw
      dsimp [d_real_bot] at hd
      have : (3 : ENNReal) < ε := by norm_num at hd; exact hd
      have : (3 : ENNReal) < 2 := lt_of_lt_of_le (by assumption) h2
      norm_num at this

theorem ex35_cov_le_1 (ε : ENNReal) (hε_pos : 0 < ε) (hε_le1 : ε ≤ 1) :
    covering_number d_real_bot ε ex35_U = 4 := by
  dsimp [covering_number]
  apply le_antisymm
  · set centers : Finset (Option ℝ) := { some 0, some 1, some 2, some 3 }
    have hnet : InternalEpsilonNet d_real_bot ε ex35_U centers := by
      dsimp [InternalEpsilonNet, centers]
      refine ⟨?_, ?_⟩
      · intro x hx; simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl | rfl <;> simp [mem_ex35_U]
      · intro x hx
        rw [mem_ex35_U] at hx
        rcases hx with rfl | rfl | rfl | rfl
        · refine ⟨some 0, Finset.mem_insert_self _ _, ?_⟩; dsimp [d_real_bot]; norm_num; exact hε_pos
        · refine ⟨some 1, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), ?_⟩; dsimp [d_real_bot]; norm_num; exact hε_pos
        · refine ⟨some 2, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)), ?_⟩; dsimp [d_real_bot]; norm_num; exact hε_pos
        · refine ⟨some 3, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))), ?_⟩; dsimp [d_real_bot]; norm_num; exact hε_pos
    have h_le := iInf_le (fun s => ⨅ (_ : InternalEpsilonNet d_real_bot ε ex35_U s), (s.card : ENNReal)) centers
    have h_le2 := iInf_le (fun (_ : InternalEpsilonNet d_real_bot ε ex35_U centers) => (centers.card : ENNReal)) hnet
    have hcard : centers.card = 4 := by
      dsimp [centers]
      rw [Finset.card_insert_of_notMem]
      · rw [Finset.card_insert_of_notMem]
        · rw [Finset.card_insert_of_notMem]
          · rw [Finset.card_singleton]
          · intro h; simp only [Finset.mem_singleton, Option.some.injEq] at h; norm_num at h
        · intro h; simp only [Finset.mem_insert, Finset.mem_singleton, Option.some.injEq] at h
          rcases h with h | h <;> norm_num at h
      · intro h; simp only [Finset.mem_insert, Finset.mem_singleton, Option.some.injEq] at h
        rcases h with h | h | h <;> norm_num at h
    have h_trans := le_trans h_le h_le2
    rw [hcard] at h_trans
    exact_mod_cast h_trans
  · apply le_iInf; intro c
    apply le_iInf; intro hnet
    -- distinct elements of ex35_U cannot share a center
    have h_inj : ∀ x ∈ ex35_U, ∀ y ∈ ex35_U, (∃ c0 ∈ c, d_real_bot x c0 < ε ∧ d_real_bot y c0 < ε) → x = y := by
      intro x hx y hy ⟨c0, hc0, hdx, hdy⟩
      have hc0_in := hnet.1 hc0
      rw [mem_ex35_U] at hx hy hc0_in
      rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;> try rfl
      all_goals {
        rcases hc0_in with rfl | rfl | rfl | rfl <;> {
          dsimp [d_real_bot] at hdx hdy
          have h_sum : d_real_bot x c0 + d_real_bot y c0 < ε + ε := ENNReal.add_lt_add hdx hdy
          norm_num at hdx hdy
        }
      }
    by_contra! hlt
    have hcard : c.card ≤ 3 := Nat.le_of_lt_succ (Nat.cast_lt.mp hlt)
    -- choose center for each of 0, 1, 2, 3
    rcases hnet.2 (some 0) (by simp [mem_ex35_U]) with ⟨c0, hc0, hd0⟩
    rcases hnet.2 (some 1) (by simp [mem_ex35_U]) with ⟨c1, hc1, hd1⟩
    rcases hnet.2 (some 2) (by simp [mem_ex35_U]) with ⟨c2, hc2, hd2⟩
    rcases hnet.2 (some 3) (by simp [mem_ex35_U]) with ⟨c3, hc3, hd3⟩
    -- c0, c1, c2, c3 are 4 distinct elements in c
    have hc01 : c0 ≠ c1 := by intro heq; have := h_inj (some 0) (by simp [mem_ex35_U]) (some 1) (by simp [mem_ex35_U]) ⟨c0, hc0, hd0, by rw [heq]; exact hd1⟩; injection this with this; norm_num at this
    have hc02 : c0 ≠ c2 := by intro heq; have := h_inj (some 0) (by simp [mem_ex35_U]) (some 2) (by simp [mem_ex35_U]) ⟨c0, hc0, hd0, by rw [heq]; exact hd2⟩; injection this with this; norm_num at this
    have hc03 : c0 ≠ c3 := by intro heq; have := h_inj (some 0) (by simp [mem_ex35_U]) (some 3) (by simp [mem_ex35_U]) ⟨c0, hc0, hd0, by rw [heq]; exact hd3⟩; injection this with this; norm_num at this
    have hc12 : c1 ≠ c2 := by intro heq; have := h_inj (some 1) (by simp [mem_ex35_U]) (some 2) (by simp [mem_ex35_U]) ⟨c1, hc1, hd1, by rw [heq]; exact hd2⟩; injection this with this; norm_num at this
    have hc13 : c1 ≠ c3 := by intro heq; have := h_inj (some 1) (by simp [mem_ex35_U]) (some 3) (by simp [mem_ex35_U]) ⟨c1, hc1, hd1, by rw [heq]; exact hd3⟩; injection this with this; norm_num at this
    have hc23 : c2 ≠ c3 := by intro heq; have := h_inj (some 2) (by simp [mem_ex35_U]) (some 3) (by simp [mem_ex35_U]) ⟨c2, hc2, hd2, by rw [heq]; exact hd3⟩; injection this with this; norm_num at this
    have h_sub : ({c0, c1, c2, c3} : Finset (Option ℝ)) ⊆ c := by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> assumption
    have h_card_le := Finset.card_le_card h_sub
    have h_card4 : ({c0, c1, c2, c3} : Finset (Option ℝ)).card = 4 := by
      rw [Finset.card_insert_of_notMem]
      · rw [Finset.card_insert_of_notMem]
        · rw [Finset.card_insert_of_notMem]
          · rw [Finset.card_singleton]
          · intro h; simp only [Finset.mem_singleton] at h; exact hc23 h
        · intro h; simp only [Finset.mem_insert, Finset.mem_singleton] at h
          rcases h with h | h
          · exact hc12 h
          · exact hc13 h
      · intro h; simp only [Finset.mem_insert, Finset.mem_singleton] at h
        rcases h with h | h | h
        · exact hc01 h
        · exact hc02 h
        · exact hc03 h
    rw [h_card4] at h_card_le
    omega

end OperatorLocalDegeneracy
