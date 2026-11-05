import CH03.LineExamples

namespace formal_oet.vol_01.ch_03_operator_local_degeneracy
open formal_oet.vol_01.ch_01_foundations
open Set

set_option maxHeartbeats 4000000

def stepB (a : ℝ) : Set (Option ℝ) := {some (-a), some a}

theorem stepB_nonempty (a : ℝ) : (stepB a).Nonempty := by
  refine ⟨some a, ?_⟩
  simp [stepB]

theorem stepB_input_cover_one {a : ℝ} {τ : ENNReal} (ha : 0 < a) (ha1 : a ≤ 1)
    (h2a : ENNReal.ofReal (2 * a) < τ)
    (hτpos : 0 < τ) :
    covering_number lineDist τ (stepB a) = 1 := by
  have hnet : InternalEpsilonNet lineDist τ (stepB a) ({some (-a)} : Finset (Option ℝ)) := by
    constructor
    · intro x hx
      simp at hx
      subst x
      simp [stepB]
    · intro x hx
      refine ⟨some (-a), by simp, ?_⟩
      simp only [stepB, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · simp [hτpos]
      · rw [lineDist_some_some]
        have habs : |a - (-a)| = 2 * a := by
          rw [show a - (-a) = 2 * a by ring, abs_of_pos (by linarith)]
        rw [habs]
        exact h2a
  apply le_antisymm
  · calc
      covering_number lineDist τ (stepB a) ≤ (({some (-a)} : Finset (Option ℝ)).card : ENNReal) :=
        covering_number_le_card_of_net hnet
      _ = 1 := by simp
  · exact one_le_covering_number_of_nonempty lineDist τ (stepB a) (stepB_nonempty a)

theorem step_image_B {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    stepOp.func '' stepB a = ({some (0 : ℝ), some 1} : Set (Option ℝ)) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp only [stepB, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · have hneg : -a < 0 := by linarith
      simp [stepOp, stepFun, hneg]
    · have hnonneg : ¬a < 0 := not_lt.mpr (le_of_lt ha)
      simp [stepOp, stepFun, hnonneg]
  · intro hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · refine ⟨some (-a), ?_, ?_⟩
      · simp [stepB]
      · have hneg : -a < 0 := by linarith
        simp [stepOp, stepFun, hneg]
    · refine ⟨some a, ?_, ?_⟩
      · simp [stepB]
      · have hnonneg : ¬a < 0 := not_lt.mpr (le_of_lt ha)
        simp [stepOp, stepFun, hnonneg]

theorem out_two_cover_le :
    covering_number lineDist (1/2 : ENNReal) ({some (0 : ℝ), some 1} : Set (Option ℝ)) ≤ 2 := by
  have hnet : InternalEpsilonNet lineDist (1/2 : ENNReal)
      ({some (0 : ℝ), some 1} : Set (Option ℝ)) ({some 0, some 1} : Finset (Option ℝ)) := by
    constructor
    · intro x hx
      simp at hx
      rcases hx with rfl | rfl <;> simp
    · intro x hx
      refine ⟨x, ?_, ?_⟩
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl <;> simp
      · have hd : lineDist x x = 0 := by
          rcases x with _ | x <;> simp
        rw [hd]
        norm_num
  calc
    covering_number lineDist (1/2 : ENNReal) ({some (0 : ℝ), some 1} : Set (Option ℝ))
        ≤ (({some 0, some 1} : Finset (Option ℝ)).card : ENNReal) :=
          covering_number_le_card_of_net hnet
    _ = 2 := by norm_num

theorem no_one_center_covers_out :
    ¬ ∃ c ∈ ({some (0 : ℝ), some 1} : Set (Option ℝ)),
      lineDist (some 0) c < (1/2 : ENNReal) ∧ lineDist (some 1) c < (1/2 : ENNReal) := by
  rintro ⟨c, hc, h0, h1⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
  rcases hc with rfl | rfl
  · rw [lineDist_some_some] at h1
    norm_num at h1
  · rw [lineDist_some_some] at h0
    norm_num at h0

theorem out_two_cover_ge :
    (2 : ENNReal) ≤ covering_number lineDist (1/2 : ENNReal)
      ({some (0 : ℝ), some 1} : Set (Option ℝ)) := by
  have hfin : ∃ S : Finset (Option ℝ), InternalEpsilonNet lineDist (1/2 : ENNReal)
      ({some (0 : ℝ), some 1} : Set (Option ℝ)) S := by
    refine ⟨{some 0, some 1}, ?_⟩
    constructor
    · intro x hx
      simp at hx
      rcases hx with rfl | rfl <;> simp
    · intro x hx
      refine ⟨x, ?_, ?_⟩
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl <;> simp
      · rcases x with _ | x
        · norm_num [lineDist]
        · norm_num [lineDist]
  obtain ⟨S, hS, hcover, hmin⟩ :=
    covering_number_attained lineDist (1/2 : ENNReal)
      ({some (0 : ℝ), some 1} : Set (Option ℝ)) hfin
  have hcard : 2 ≤ S.card := by
    by_contra hnot
    have hle : S.card ≤ 1 := by omega
    have hall := Finset.card_le_one.mp hle
    rcases hS.2 (some 0) (by simp) with ⟨c0, hc0, hdist0⟩
    rcases hS.2 (some 1) (by simp) with ⟨c1, hc1, hdist1⟩
    have hc01 : c0 = c1 := hall c0 hc0 c1 hc1
    have hc0set : c0 ∈ ({some (0 : ℝ), some 1} : Set (Option ℝ)) := hS.1 hc0
    have hboth : lineDist (some 0) c0 < (1/2 : ENNReal) ∧
        lineDist (some 1) c0 < (1/2 : ENNReal) := by
      constructor
      · exact hdist0
      · simpa [hc01] using hdist1
    exact no_one_center_covers_out ⟨c0, hc0set, hboth.1, hboth.2⟩
  rw [hcover]
  exact_mod_cast hcard

theorem out_two_cover_eq :
    covering_number lineDist (1/2 : ENNReal)
      ({some (0 : ℝ), some 1} : Set (Option ℝ)) = 2 := by
  exact le_antisymm out_two_cover_le out_two_cover_ge

theorem step_two_point_cover_counterexample (τ : ENNReal) (hτpos : 0 < τ) (hτtop : τ ≠ ⊤) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧ ENNReal.ofReal (2 * a) < τ ∧
      covering_number lineDist τ (stepB a) = 1 ∧
      covering_number lineDist (1/2 : ENNReal) (stepOp.func '' stepB a) = 2 := by
  let a : ℝ := min (1/2 : ℝ) (τ.toReal / 4)
  have hτreal : 0 < τ.toReal := ENNReal.toReal_pos (ne_of_gt hτpos) hτtop
  have hapos : 0 < a := lt_min (by norm_num) (by positivity)
  have ha1 : a ≤ 1 := le_trans (min_le_left _ _) (by norm_num)
  have haτ : 2 * a < τ.toReal := by
    have hle : a ≤ τ.toReal / 4 := min_le_right _ _
    nlinarith
  have h2a : ENNReal.ofReal (2 * a) < τ :=
    (ENNReal.ofReal_lt_iff_lt_toReal (by positivity) hτtop).mpr haτ
  refine ⟨a, hapos, ha1, h2a, ?_, ?_⟩
  · exact stepB_input_cover_one hapos ha1 h2a hτpos
  · rw [step_image_B hapos ha1, out_two_cover_eq]

end formal_oet.vol_01.ch_03_operator_local_degeneracy
