
import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space
import formal_oet.vol_01.ch_01_foundations.metric_entropy
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Card
import OperatorLocalDegeneracy.ComponentPartition
import OperatorLocalDegeneracy.ComputationalFibers
import OperatorLocalDegeneracy.NullificationRadius
import OperatorLocalDegeneracy.CoveringEntropy

namespace OperatorLocalDegeneracy

open formal_oet.vol_01.ch_01_foundations

noncomputable def trans_op : Operator (Option ℝ) none where
  func := fun x => match x with | none => none | some r => some (r + 1)
  preserves_bot := rfl

def ex33_U : Set (Option ℝ) := { some (-3), some (-2), some 0, some 2 }

lemma mem_ex33_U (x : Option ℝ) : x ∈ ex33_U ↔ x = some (-3) ∨ x = some (-2) ∨ x = some 0 ∨ x = some 2 := by
  dsimp [ex33_U]; simp

noncomputable def eps32 : ENNReal := ENNReal.ofReal (3 / 2)

lemma eps32_pos : 0 < eps32 := by
  dsimp [eps32]; rw [ENNReal.ofReal_pos]; norm_num

-- Let's check covering number <= 3
lemma ex_3_3_cov_U_le : covering_number d_real_bot eps32 ex33_U ≤ 3 := by
  dsimp [covering_number]
  set centers : Finset (Option ℝ) := { some (-2), some 0, some 2 }
  have hnet : InternalEpsilonNet d_real_bot eps32 ex33_U centers := by
    dsimp [InternalEpsilonNet, centers, ex33_U]
    refine ⟨?_, ?_⟩
    · intro x hx
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · right; left; rfl
      · right; right; left; rfl
      · right; right; right; rfl
    · intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · refine ⟨some (-2), Finset.mem_insert_self _ _, ?_⟩
        dsimp [d_real_bot, eps32]; rw [ENNReal.ofReal_lt_ofReal_iff (by norm_num)]; norm_num
      · refine ⟨some (-2), Finset.mem_insert_self _ _, ?_⟩
        dsimp [d_real_bot, eps32]; rw [ENNReal.ofReal_lt_ofReal_iff (by norm_num)]; norm_num
      · refine ⟨some 0, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), ?_⟩
        dsimp [d_real_bot, eps32]; rw [ENNReal.ofReal_lt_ofReal_iff (by norm_num)]; norm_num
      · refine ⟨some 2, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)), ?_⟩
        dsimp [d_real_bot, eps32]; rw [ENNReal.ofReal_lt_ofReal_iff (by norm_num)]; norm_num
  have h_le := iInf_le (fun s => ⨅ (_ : InternalEpsilonNet d_real_bot eps32 ex33_U s), (s.card : ENNReal)) centers
  have h_le2 := iInf_le (fun (_ : InternalEpsilonNet d_real_bot eps32 ex33_U centers) => (centers.card : ENNReal)) hnet
  have hcard : centers.card = 3 := by
    dsimp [centers]
    rw [Finset.card_insert_of_notMem]
    · rw [Finset.card_insert_of_notMem]
      · rw [Finset.card_singleton]
      · intro h; simp only [Finset.mem_singleton, Option.some.injEq] at h; norm_num at h
    · intro h; simp only [Finset.mem_insert, Finset.mem_singleton, Option.some.injEq] at h
      rcases h with h | h <;> norm_num at h
  have h_trans := le_trans h_le h_le2
  rw [hcard] at h_trans
  exact h_trans

lemma ex_3_3_cov_U_ge : 3 ≤ covering_number d_real_bot eps32 ex33_U := by
  dsimp [covering_number]
  apply le_iInf; intro c
  apply le_iInf; intro hnet
  by_contra! hlt
  have hcard : c.card ≤ 2 := Nat.le_of_lt_succ (Nat.cast_lt.mp hlt)
  have h_sub : {some (-2), some 0, some 2} ⊆ ex33_U := by
    intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
  dsimp [InternalEpsilonNet] at hnet
  rcases hnet.2 (some (-2)) (h_sub (Or.inl rfl)) with ⟨c1, hc1, hd1⟩
  rcases hnet.2 (some 0) (h_sub (Or.inr (Or.inl rfl))) with ⟨c2, hc2, hd2⟩
  rcases hnet.2 (some 2) (h_sub (Or.inr (Or.inr rfl))) with ⟨c3, hc3, hd3⟩
  have h_pairs : c1 = c2 ∨ c1 = c3 ∨ c2 = c3 := by
    have h_set : ({c1, c2, c3} : Finset (Option ℝ)) ⊆ c := by
      intro x hx; simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
    have h_le := Finset.card_le_card h_set
    by_contra! h_all_ne
    have h_card3 : ({c1, c2, c3} : Finset (Option ℝ)).card = 3 := by
      rw [Finset.card_insert_of_notMem]
      · rw [Finset.card_insert_of_notMem]
        · rw [Finset.card_singleton]
        · intro h; simp only [Finset.mem_singleton] at h; exact h_all_ne.2.2 h
      · intro h; simp only [Finset.mem_insert, Finset.mem_singleton] at h
        rcases h with h | h
        · exact h_all_ne.1 h
        · exact h_all_ne.2.1 h
    rw [h_card3] at h_le
    omega
  rcases h_pairs with rfl | rfl | rfl
  · have hc1_in := hnet.1 hc1
    rw [mem_ex33_U] at hc1_in
    rcases hc1_in with rfl | rfl | rfl | rfl
    · dsimp [d_real_bot, eps32] at hd2; norm_num at hd2
    · dsimp [d_real_bot, eps32] at hd2; norm_num at hd2
    · dsimp [d_real_bot, eps32] at hd1; norm_num at hd1
    · dsimp [d_real_bot, eps32] at hd1; norm_num at hd1
  · have hc1_in := hnet.1 hc1
    rw [mem_ex33_U] at hc1_in
    rcases hc1_in with rfl | rfl | rfl | rfl
    · dsimp [d_real_bot, eps32] at hd3; norm_num at hd3
    · dsimp [d_real_bot, eps32] at hd3; norm_num at hd3
    · dsimp [d_real_bot, eps32] at hd1; norm_num at hd1
    · dsimp [d_real_bot, eps32] at hd1; norm_num at hd1
  · have hc2_in := hnet.1 hc2
    rw [mem_ex33_U] at hc2_in
    rcases hc2_in with rfl | rfl | rfl | rfl
    · dsimp [d_real_bot, eps32] at hd2; norm_num at hd2
    · dsimp [d_real_bot, eps32] at hd2; norm_num at hd2
    · dsimp [d_real_bot, eps32] at hd3; norm_num at hd3
    · dsimp [d_real_bot, eps32] at hd2; norm_num at hd2

theorem ex_3_3_cov_U : covering_number d_real_bot eps32 ex33_U = 3 :=
  le_antisymm ex_3_3_cov_U_le ex_3_3_cov_U_ge

end OperatorLocalDegeneracy
