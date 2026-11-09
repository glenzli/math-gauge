import Ch03.ExercisesBasic

namespace OET.Ch03

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set

/-- Exercise 3.3(ii): the input needs two internal centres, the translated
image needs one, and the entropy difference is one bit. -/
theorem translate_covering_entropy :
    covering_number absReadDist (3 / 2 : ENNReal) translateDomain = 2 ∧
      covering_number absReadDist (3 / 2 : ENNReal) (translateOp.func '' translateDomain) = 1 ∧
      entropyDelta (fun _ : Unit => absReadDist) {()} {()} (3 / 2 : ENNReal)
        translateOp translateDomain = 1 := by
  have h1 : (1 : ENNReal) < 3 / 2 := by
    apply (ENNReal.lt_div_iff_mul_lt (Or.inl (by simp)) (Or.inl (by simp))).mpr
    norm_num
  have h0 : (0 : ENNReal) < 3 / 2 := zero_lt_one.trans h1
  have h15 : (3 / 2 : ENNReal) < 2 := by
    apply (ENNReal.div_lt_iff (Or.inl (by simp)) (Or.inl (by simp))).mpr
    norm_num
  have h3 : (3 / 2 : ENNReal) < 3 := h15.trans (by norm_num)
  have himage : translateOp.func '' translateDomain =
      {some (-2), some (-1), some 1, some 3} := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      simp only [translateDomain, mem_insert_iff, mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> norm_num [translateOp]
    · intro hz
      simp only [mem_insert_iff, mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl | rfl
      · exact ⟨some (-3), by simp [translateDomain], by norm_num [translateOp]⟩
      · exact ⟨some (-2), by simp [translateDomain], by norm_num [translateOp]⟩
      · exact ⟨some 0, by simp [translateDomain], by norm_num [translateOp]⟩
      · exact ⟨some 2, by simp [translateDomain], by norm_num [translateOp]⟩
  have hout : covering_number absReadDist (3 / 2 : ENNReal) (translateOp.func '' translateDomain) = 1 := by
    rw [himage]
    apply le_antisymm
    · have hnet : InternalEpsilonNet absReadDist (3 / 2 : ENNReal)
          {some (-2), some (-1), some 1, some 3} {some (-2)} := by
        constructor
        · simp
        · intro x hx
          simp only [mem_insert_iff, mem_singleton_iff] at hx
          rcases hx with rfl | rfl | rfl | rfl
          all_goals refine ⟨some (-2), by simp, ?_⟩
          all_goals norm_num [absReadDist, optionDist, h0, h1]
      simpa using covering_number_le_of_net hnet
    · exact one_le_covering_number_of_nonempty _ _ _ ⟨some (-2), by simp⟩
  have hin : covering_number absReadDist (3 / 2 : ENNReal) translateDomain = 2 := by
    apply le_antisymm
    · have hnet : InternalEpsilonNet absReadDist (3 / 2 : ENNReal) translateDomain
          {some (-2), some 0} := by
        constructor
        · intro x hx
          change x ∈ ({some (-2), some 0} : Finset RealBase) at hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> simp [translateDomain]
        · intro x hx
          simp only [translateDomain, mem_insert_iff, mem_singleton_iff] at hx
          rcases hx with rfl | rfl | rfl | rfl
          · exact ⟨some (-2), by simp, by norm_num [absReadDist, optionDist, h0, h1]⟩
          · exact ⟨some (-2), by simp, by norm_num [absReadDist, optionDist, h0, h1]⟩
          · exact ⟨some 0, by simp, by norm_num [absReadDist, optionDist, h0, h1]⟩
          · exact ⟨some (-2), by simp, by norm_num [absReadDist, optionDist, h0, h1]⟩
      simpa using covering_number_le_of_net hnet
    · apply le_covering_number_of_card
      intro S hS
      by_contra hn
      have hcardlt : S.card < 2 := lt_of_not_ge hn
      obtain ⟨c, hc, _⟩ := hS.2 (some (-3)) (by simp [translateDomain])
      have hcard1 : S.card = 1 := le_antisymm (Nat.le_of_lt_succ hcardlt)
        (Finset.card_pos.mpr ⟨c, hc⟩)
      obtain ⟨c, rfl⟩ := Finset.card_eq_one.mp hcard1
      have hcU : c ∈ translateDomain := hS.1 (by simp)
      simp only [translateDomain, mem_insert_iff, mem_singleton_iff] at hcU
      rcases hcU with rfl | rfl | rfl | rfl
      · obtain ⟨c', hc', hd⟩ := hS.2 (some 0) (by simp [translateDomain])
        simp at hc'
        subst c'
        norm_num [absReadDist, optionDist, h0, h1] at hd
        first | exact (not_lt_of_ge h3.le) hd | exact (not_lt_of_ge h15.le) hd
      · obtain ⟨c', hc', hd⟩ := hS.2 (some 0) (by simp [translateDomain])
        simp at hc'
        subst c'
        norm_num [absReadDist, optionDist, h0, h1] at hd
        first | exact (not_lt_of_ge h3.le) hd | exact (not_lt_of_ge h15.le) hd
      · obtain ⟨c', hc', hd⟩ := hS.2 (some (-3)) (by simp [translateDomain])
        simp at hc'
        subst c'
        norm_num [absReadDist, optionDist, h0, h1] at hd
        first | exact (not_lt_of_ge h3.le) hd | exact (not_lt_of_ge h15.le) hd
      · obtain ⟨c', hc', hd⟩ := hS.2 (some 0) (by simp [translateDomain])
        simp at hc'
        subst c'
        norm_num [absReadDist, optionDist, h0, h1] at hd
        first | exact (not_lt_of_ge h3.le) hd | exact (not_lt_of_ge h15.le) hd
  refine ⟨hin, hout, ?_⟩
  rw [entropyDelta, subfamily_metric_entropy_singleton, subfamily_metric_entropy_singleton]
  simp [metric_entropy, hin, hout, log2_ereal]

end OET.Ch03
