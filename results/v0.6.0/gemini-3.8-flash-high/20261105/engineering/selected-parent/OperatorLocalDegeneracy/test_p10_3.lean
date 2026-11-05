
lemma eq_zero_of_forall_le (a : ENNReal) (h : ∀ ε : ENNReal, 0 < ε → a ≤ ε) : a = 0 := by
  by_contra ha
  have hpos : 0 < a := pos_iff_ne_zero.mpr ha
  rcases exists_between hpos with ⟨b, hb0, hba⟩
  have := h b hb0
  exact (lt_self_iff_false _).mp (lt_of_lt_of_le hba this)

theorem prop_3_10_03 :
    r_null_uniform d_real_bot d_real_bot step_op U_step = 0 := by
  apply eq_zero_of_forall_le
  intro ε hε
  -- Choose n such that 1/(n+2) < ε
  -- Since ε > 0, we can take real ε_real > 0 if ε < ⊤, or just bound it
  by_cases htop : ε = ⊤
  · rw [htop]; exact le_top
  lift ε to NNReal using htop
  have hε_pos : 0 < (ε : ℝ) := by
    rwa [ENNReal.coe_pos] at hε
  rcases exists_nat_gt (1 / (ε : ℝ)) with ⟨n, hn⟩
  set y0 : ℝ := 1 / ((n : ℝ) + 2)
  have hy0_pos : 0 < y0 := by
    apply div_pos (by norm_num)
    linarith
  have hy0_le1 : y0 ≤ 1 := by
    dsimp [y0]
    rw [div_le_iff₀]
    · linarith
    · linarith
  have hy_mem : some y0 ∈ U_step := by
    exact ⟨y0, rfl, Or.inr ⟨hy0_pos, hy0_le1⟩⟩
  have hr_y0 : r_null d_real_bot d_real_bot step_op (some y0) U_step = ENNReal.ofReal y0 := by
    have h_abs : |y0| = y0 := abs_of_pos hy0_pos
    have h := (prop_3_10_02 y0 hy_mem).2.1
    rw [h_abs] at h
    exact h
  have h_inf_le : r_null_uniform d_real_bot d_real_bot step_op U_step ≤ r_null d_real_bot d_real_bot step_op (some y0) U_step := by
    dsimp [r_null_uniform]
    exact iInf_le (fun y => r_null d_real_bot d_real_bot step_op y U_step) (some y0)
  have h_inf_le2 : r_null_uniform d_real_bot d_real_bot step_op U_step ≤ ENNReal.ofReal y0 := by
    -- wait, iInf_le over subtype or iInf_le_of_mem?
    sorry
