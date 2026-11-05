import Mathlib.Data.ENNReal.Basic

lemma eq_zero_of_forall_le (a : ENNReal) (h : ∀ ε : ENNReal, 0 < ε → a ≤ ε) : a = 0 := by
  by_contra ha
  have hpos : 0 < a := pos_iff_ne_zero.mpr ha
  rcases exists_between hpos with ⟨b, hb0, hba⟩
  have := h b hb0
  exact (lt_self_iff_false _).mp (lt_of_lt_of_le hba this)
