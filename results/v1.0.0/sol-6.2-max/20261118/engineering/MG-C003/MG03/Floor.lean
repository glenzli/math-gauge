import MG03.Step

namespace MG03

open Set formal_oet.vol_01.ch_01_foundations

noncomputable def floorOp : Operator RealWithBot none := realOp fun x => (⌊x⌋ : ℤ)
def floorD₁ : Set RealWithBot := realSet (Icc 0 (1 / 2))
def floorD₂ : Set RealWithBot := realSet (Icc (9 / 10) (11 / 10))
def floorD₃ : Set RealWithBot := {some 0, some 2}
def floorD₄ : Set RealWithBot := realSet (Icc 0 2)

theorem floor_zero_on {x : ℝ} (h₀ : 0 ≤ x) (h₁ : x < 1) : floorOp.func (some x) = some 0 := by
  have h : ⌊x⌋ = 0 := Int.floor_eq_iff.mpr (by simpa using And.intro h₀ h₁)
  simp [floorOp, h]

@[simp] theorem floor_at_one : floorOp.func (some 1) = some 1 := by simp [floorOp]
@[simp] theorem floor_at_two : floorOp.func (some 2) = some 2 := by norm_num [floorOp]

theorem diameter_interval {a b : ℝ} (hab : a ≤ b) :
    diameter realDist (realSet (Icc a b)) = ENNReal.ofReal (b - a) := by
  apply le_antisymm
  · apply diameter_le
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    change ENNReal.ofReal |x - y| ≤ _
    apply ENNReal.ofReal_le_ofReal
    apply abs_le.mpr
    exact ⟨by linarith [hx.1, hy.2], by linarith [hx.2, hy.1]⟩
  · have h := le_diameter (e := realDist)
      (some_mem_realSet.mpr (show a ∈ Icc a b from ⟨le_rfl, hab⟩))
      (some_mem_realSet.mpr (show b ∈ Icc a b from ⟨hab, le_rfl⟩))
    change ENNReal.ofReal |a - b| ≤ _ at h
    rwa [abs_of_nonpos (sub_nonpos.mpr hab), neg_sub] at h

theorem floor_jump {D : Set RealWithBot} (hsub : realSet (Icc (9 / 10) 1) ⊆ D) :
    uniformOn realDist realDist floorOp D = 0 := by
  apply le_antisymm _ (zero_le _)
  apply le_of_not_gt
  intro h
  obtain ⟨a, ha, h1, hsmall⟩ := small_ofReal h
  let x : ℝ := 1 - a / 10
  have hx : some x ∈ D := hsub (some_mem_realSet.mpr ⟨by dsimp [x]; linarith, by dsimp [x]; linarith⟩)
  have hy : some (1 : ℝ) ∈ D := hsub (some_mem_realSet.mpr ⟨by norm_num, le_rfl⟩)
  have hfx : floorOp.func (some x) = some 0 :=
    floor_zero_on (by dsimp [x]; linarith) (by dsimp [x]; linarith)
  have hneq : realDist (floorOp.func (some x)) (floorOp.func (some 1)) ≠ 0 := by
    rw [hfx, floor_at_one]
    norm_num [realReadingDist_zero_iff]
  have hle := uniform_le_of_separated (eIn := realDist) hx hy hneq
  change uniformOn realDist realDist floorOp D ≤ ENNReal.ofReal |x - 1| at hle
  have heq : |x - 1| = a / 10 := by
    rw [abs_of_neg (by dsimp [x]; linarith)]
    dsimp [x]
    ring
  rw [heq] at hle
  exact (not_lt_of_ge hle) ((ENNReal.ofReal_le_ofReal (by linarith : a / 10 ≤ a)).trans_lt hsmall)

theorem floorD₁_nonempty : floorD₁.Nonempty := ⟨some 0, by norm_num [floorD₁]⟩
theorem floorD₂_nonempty : floorD₂.Nonempty := ⟨some 1, by norm_num [floorD₂]⟩
theorem floorD₃_nonempty : floorD₃.Nonempty := ⟨some 0, by simp [floorD₃]⟩
theorem floorD₄_nonempty : floorD₄.Nonempty := ⟨some 0, by norm_num [floorD₄]⟩

theorem floorD₃_dom : floorD₃ ⊆ dom floorOp := by
  intro x hx
  simp only [floorD₃, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl <;> simp [dom, floorOp]

theorem floor_valid :
    (∀ i, ExtendedPseudoMetric RealWithBot none (realGauge i)) ∧
      floorD₁ ⊆ dom floorOp ∧ floorD₂ ⊆ dom floorOp ∧
        floorD₃ ⊆ dom floorOp ∧ floorD₄ ⊆ dom floorOp :=
  ⟨fun _ => realReadingDist_gauge id, realSet_dom _ _, realSet_dom _ _, floorD₃_dom, realSet_dom _ _⟩

noncomputable def floorType (D : Set RealWithBot) (hD : D.Nonempty) : Bool × Bool :=
  channelType (diameterScale realGauge) realGauge floorOp ⟨D, hD⟩ 1 1 PUnit.unit PUnit.unit

theorem floorD₁_result :
    diameter realDist floorD₁ = ENNReal.ofReal (1 / 2) ∧
    uniformOn realDist realDist floorOp floorD₁ = ⊤ ∧
    floorType floorD₁ floorD₁_nonempty = (true, true) := by
  have hd : diameter realDist floorD₁ = ENNReal.ofReal (1 / 2) := by
    simpa [floorD₁] using diameter_interval (a := 0) (b := 1 / 2) (by norm_num)
  have hn : uniformOn realDist realDist floorOp floorD₁ = ⊤ := by
    apply uniform_eq_top_of_const
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [floor_zero_on hx.1 (by linarith [hx.2]), floor_zero_on hy.1 (by linarith [hy.2])]
    exact (realReadingDist_gauge id).dist_self _
  refine ⟨hd, hn, ?_⟩
  simp only [floorType, channelType, diameterScale, realGauge, nullMatrix, hd, hn, le_top, decide_true,
    Prod.mk.injEq, decide_eq_true_eq, and_true]
  rw [← ENNReal.ofReal_one]
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)

theorem floorD₂_result :
    diameter realDist floorD₂ = ENNReal.ofReal (1 / 5) ∧
    uniformOn realDist realDist floorOp floorD₂ = 0 ∧
    floorType floorD₂ floorD₂_nonempty = (true, false) := by
  have hd : diameter realDist floorD₂ = ENNReal.ofReal (1 / 5) := by
    have h := diameter_interval (a := 9 / 10) (b := 11 / 10) (by norm_num)
    norm_num [floorD₂] at h ⊢
    exact h
  have hn : uniformOn realDist realDist floorOp floorD₂ = 0 := by
    apply floor_jump
    rintro _ ⟨x, hx, rfl⟩
    exact some_mem_realSet.mpr ⟨hx.1, hx.2.trans (by norm_num)⟩
  have hs : ENNReal.ofReal (1 / 5) < 1 := by
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)
  exact ⟨hd, hn, by norm_num [floorType, channelType, diameterScale, realGauge, nullMatrix, hd, hn, hs]⟩

theorem floorD₃_result :
    diameter realDist floorD₃ = 2 ∧
    uniformOn realDist realDist floorOp floorD₃ = 2 ∧
    floorType floorD₃ floorD₃_nonempty = (false, true) := by
  have h02 : realDist (some 0) (some 2) = 2 := by norm_num
  have h20 : realDist (some 2) (some 0) = 2 :=
    ((realReadingDist_gauge id).symm _ _).trans h02
  have h0f : floorOp.func (some 0) = some 0 := floor_zero_on le_rfl (by norm_num)
  have hd : diameter realDist floorD₃ = 2 :=
    (diameter_pair (realReadingDist_gauge id) _ _).trans h02
  have hn : uniformOn realDist realDist floorOp floorD₃ = 2 := by
    apply le_antisymm
    · have hdout : realDist (floorOp.func (some 0)) (floorOp.func (some 2)) ≠ 0 := by
        rw [h0f, floor_at_two, h02]
        norm_num
      exact (uniform_le_of_separated (eIn := realDist) (by simp [floorD₃]) (by simp [floorD₃])
        hdout).trans_eq h02
    · apply le_uniform_iff.mpr
      intro y hy x hx hxy
      simp only [floorD₃, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact (realReadingDist_gauge id).dist_self _
      · exact ((not_lt_of_ge h02.ge) hxy).elim
      · exact ((not_lt_of_ge h20.ge) hxy).elim
      · exact (realReadingDist_gauge id).dist_self _
  exact ⟨hd, hn, by norm_num [floorType, channelType, diameterScale, realGauge, nullMatrix, hd, hn]⟩

theorem floorD₄_result :
    diameter realDist floorD₄ = 2 ∧
    uniformOn realDist realDist floorOp floorD₄ = 0 ∧
    floorType floorD₄ floorD₄_nonempty = (false, false) := by
  have hd : diameter realDist floorD₄ = 2 := by
    simpa using diameter_interval (a := 0) (b := 2) (by norm_num)
  have hn : uniformOn realDist realDist floorOp floorD₄ = 0 := by
    apply floor_jump
    rintro _ ⟨x, hx, rfl⟩
    exact some_mem_realSet.mpr ⟨(by norm_num : (0 : ℝ) ≤ 9 / 10).trans hx.1,
      hx.2.trans (by norm_num)⟩
  exact ⟨hd, hn, by norm_num [floorType, channelType, diameterScale, realGauge, nullMatrix, hd, hn]⟩

theorem floor_threshold_counterexample :
    floorD₃.Nonempty ∧ floorD₃ ⊆ dom floorOp ∧
    1 ≤ uniformOn realDist realDist floorOp floorD₃ ∧
    ∃ x ∈ floorD₃, ∃ y ∈ floorD₃, realDist x y = 2 ∧
      realDist (floorOp.func x) (floorOp.func y) = 2 := by
  have h : realDist (some 0) (some 2) = 2 := by norm_num
  refine ⟨floorD₃_nonempty, floorD₃_dom, ?_, some 0, by simp [floorD₃],
    some 2, by simp [floorD₃], h, ?_⟩
  · rw [floorD₃_result.2.1]
    norm_num
  · rw [floor_zero_on (x := 0) le_rfl (by norm_num), floor_at_two]
    exact h

end MG03
