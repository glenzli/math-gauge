import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space
import formal_oet.vol_01.ch_01_foundations.metric_entropy
import OperatorLocalDegeneracy.CoveringEntropy

namespace OperatorLocalDegeneracy

open formal_oet.vol_01.ch_01_foundations

def ex35_U : Set (Option ℝ) := { some 0, some 1, some 2, some 3 }

lemma mem_ex35_U (x : Option ℝ) : x ∈ ex35_U ↔ x = some 0 ∨ x = some 1 ∨ x = some 2 ∨ x = some 3 := by
  dsimp [ex35_U]; simp

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
          norm_num
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
      have : (3 : ENNReal) < 2 := lt_of_lt_of_le (by assumption) h2
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

lemma unique_covered (x c0 : Option ℝ) (hx : x ∈ ex35_U) (hc0 : c0 ∈ ex35_U)
    (ε : ENNReal) (hd : d_real_bot x c0 < ε) (hε : ε ≤ 1) : x = c0 := by
  rw [mem_ex35_U] at hx hc0
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hc0 with rfl | rfl | rfl | rfl <;> try rfl
  all_goals {
    dsimp [d_real_bot] at hd
    norm_num at hd
    have : (1 : ENNReal) < ε := lt_of_le_of_lt (by norm_num) hd
    exact False.elim ((not_le_of_gt this) hε)
  }

lemma ex35_card_ge_4 (ε : ENNReal) (hε : ε ≤ 1) (c : Finset (Option ℝ))
    (hnet : InternalEpsilonNet d_real_bot ε ex35_U c) : 4 ≤ c.card := by
  rcases hnet.2 (some 0) (by simp [mem_ex35_U]) with ⟨c0, hc0, hd0⟩
  rcases hnet.2 (some 1) (by simp [mem_ex35_U]) with ⟨c1, hc1, hd1⟩
  rcases hnet.2 (some 2) (by simp [mem_ex35_U]) with ⟨c2, hc2, hd2⟩
  rcases hnet.2 (some 3) (by simp [mem_ex35_U]) with ⟨c3, hc3, hd3⟩
  have eq0 : some 0 = c0 := unique_covered (some 0) c0 (by simp [mem_ex35_U]) (hnet.1 hc0) ε hd0 hε
  have eq1 : some 1 = c1 := unique_covered (some 1) c1 (by simp [mem_ex35_U]) (hnet.1 hc1) ε hd1 hε
  have eq2 : some 2 = c2 := unique_covered (some 2) c2 (by simp [mem_ex35_U]) (hnet.1 hc2) ε hd2 hε
  have eq3 : some 3 = c3 := unique_covered (some 3) c3 (by simp [mem_ex35_U]) (hnet.1 hc3) ε hd3 hε
  subst eq0 eq1 eq2 eq3
  have hsub : ({some 0, some 1, some 2, some 3} : Finset (Option ℝ)) ⊆ c := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have hcard : ({some 0, some 1, some 2, some 3} : Finset (Option ℝ)).card = 4 := by
    rw [Finset.card_insert_of_notMem]
    · rw [Finset.card_insert_of_notMem]
      · rw [Finset.card_insert_of_notMem]
        · rw [Finset.card_singleton]
        · intro h; simp only [Finset.mem_singleton, Option.some.injEq] at h; norm_num at h
      · intro h; simp only [Finset.mem_insert, Finset.mem_singleton, Option.some.injEq] at h
        rcases h with h | h <;> norm_num at h
    · intro h; simp only [Finset.mem_insert, Finset.mem_singleton, Option.some.injEq] at h
      rcases h with h | h | h <;> norm_num at h
  rw [← hcard]
  exact Finset.card_le_card hsub

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
    exact_mod_cast ex35_card_ge_4 ε hε_le1 c hnet
