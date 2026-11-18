import MG03.RealFibers

namespace MG03

open Set formal_oet.vol_01.ch_01_foundations formal_oet.vol_01.ch_02_operator_bounds

def fourU : Set RealWithBot := {some 0, some 1, some 2, some 3}

theorem four_nonempty : fourU.Nonempty := ⟨some 0, by simp [fourU]⟩

theorem four_distance_bounds {x y : RealWithBot} (hx : x ∈ fourU) (hy : y ∈ fourU) :
    realDist x y ≤ 3 ∧ (x ≠ y → 1 ≤ realDist x y) := by
  simp only [fourU, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;> norm_num

theorem four_cover_small {eps : ENNReal} (he : FiniteRadius eps) (h : eps ≤ 1) :
    covering_number realDist eps fourU = 4 := by
  classical
  let S : Finset RealWithBot := {some 0, some 1, some 2, some 3}
  have hS : (↑S : Set RealWithBot) = fourU := by simp [S, fourU]
  have hc : S.card = 4 := by norm_num [S]
  rw [← hS]
  suffices covering_number realDist eps (↑S : Set RealWithBot) = (S.card : ENNReal) by
    simpa [hc] using this
  apply separated_finset_cover (realReadingDist_gauge id).dist_self he.1
  intro x hx y hy hxy
  have hx' : x ∈ fourU := hS ▸ (show x ∈ (↑S : Set RealWithBot) from hx)
  have hy' : y ∈ fourU := hS ▸ (show y ∈ (↑S : Set RealWithBot) from hy)
  exact h.trans ((four_distance_bounds hx' hy').2 hxy)

theorem four_cover_middle {eps : ENNReal} (h₁ : 1 < eps) (h₂ : eps ≤ 2) :
    covering_number realDist eps fourU = 2 := by
  classical
  apply le_antisymm
  · let S : Finset RealWithBot := {some 0, some 2}
    have hn : InternalEpsilonNet realDist eps fourU S := by
      refine ⟨by simp [S, fourU], ?_⟩
      intro x hx
      simp only [fourU, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact ⟨some 0, by simp [S], (by norm_num : realDist (some 0) (some 0) ≤ 1).trans_lt h₁⟩
      · exact ⟨some 0, by simp [S], (by norm_num : realDist (some 1) (some 0) ≤ 1).trans_lt h₁⟩
      · exact ⟨some 2, by simp [S], (by norm_num : realDist (some 2) (some 2) ≤ 1).trans_lt h₁⟩
      · exact ⟨some 2, by simp [S], (by norm_num : realDist (some 3) (some 2) ≤ 1).trans_lt h₁⟩
    have hc : S.card = 2 := by norm_num [S]
    simpa [hc] using cover_le_card hn
  · apply two_le_cover four_nonempty
    intro c hc
    simp only [fourU, Set.mem_insert_iff, Set.mem_singleton_iff] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact ⟨some 3, by simp [fourU], h₂.trans (by norm_num)⟩
    · exact ⟨some 3, by simp [fourU], h₂.trans (by norm_num)⟩
    · exact ⟨some 0, by simp [fourU], h₂.trans (by norm_num)⟩
    · exact ⟨some 0, by simp [fourU], h₂.trans (by norm_num)⟩

theorem four_cover_large {eps : ENNReal} (he : 2 < eps) :
    covering_number realDist eps fourU = 1 := by
  classical
  have hc : (some 1 : RealWithBot) ∈ fourU := by simp [fourU]
  have hn : InternalEpsilonNet realDist eps fourU {some 1} := by
    refine ⟨by simpa using hc, ?_⟩
    intro x hx
    refine ⟨some 1, Finset.mem_singleton_self _, ?_⟩
    apply lt_of_le_of_lt _ he
    simp only [fourU, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> norm_num
  exact le_antisymm (by simpa using cover_le_card hn)
    (one_le_covering_number_of_nonempty _ _ _ four_nonempty)

theorem four_cover {eps : ENNReal} (he : FiniteRadius eps) :
    covering_number realDist eps fourU = if eps ≤ 1 then 4 else if eps ≤ 2 then 2 else 1 := by
  by_cases h₁ : eps ≤ 1
  · simp [h₁, four_cover_small he h₁]
  · by_cases h₂ : eps ≤ 2
    · simp [h₁, h₂, four_cover_middle (lt_of_not_ge h₁) h₂]
    · simp [h₁, h₂, four_cover_large (lt_of_not_ge h₂)]

noncomputable def rearrangeEps : ENNReal := ENNReal.ofReal (7 / 4)

theorem four_external_center :
    let c : RealWithBot := some (3 / 2)
    c ∉ fourU ∧ (∀ x ∈ fourU, realDist x c < rearrangeEps) ∧
      ¬ InternalEpsilonNet realDist rearrangeEps fourU {c} := by
  classical
  have hn : (some (3 / 2) : RealWithBot) ∉ fourU := by norm_num [fourU]
  refine ⟨hn, ?_, fun h => hn (h.1 (Finset.mem_singleton_self _))⟩
  intro x hx
  simp only [fourU, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> norm_num [rearrangeEps, reading_lt_ofReal_iff]

noncomputable def reorderF : Operator RealWithBot none := by
  classical
  exact partialOp fun x => if x ∈ ({0, 1, 2, 3} : Set ℝ) then some x else none

noncomputable def reorderG : Operator RealWithBot none := by
  classical
  exact partialOp fun x => if x = 0 then some 0 else if x = 1 then some 3
    else if x = 2 then some 1 else if x = 3 then some 2 else none

theorem reorderF_domain : dom reorderF = fourU := by
  ext x
  cases x with
  | none => simp [fourU]
  | some x =>
    classical
    have hm : some x ∈ fourU ↔ x ∈ ({0, 1, 2, 3} : Set ℝ) := by simp [fourU]
    rw [hm]
    change (if x ∈ ({0, 1, 2, 3} : Set ℝ) then some x else none) ≠ none ↔ _
    split <;> simp_all

theorem reorderG_domain : dom reorderG = fourU := by
  ext x
  cases x with
  | none => simp [fourU]
  | some x =>
    by_cases h₀ : x = 0 <;> by_cases h₁ : x = 1 <;> by_cases h₂ : x = 2 <;>
      by_cases h₃ : x = 3 <;> simp [reorderG, partialOp, dom, fourU, h₀, h₁, h₂, h₃]

theorem reorderF_apply {x : RealWithBot} (hx : x ∈ fourU) : reorderF.func x = x := by
  simp only [fourU, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> simp [reorderF, partialOp]

theorem reorderG_table :
    reorderG.func (some 0) = some 0 ∧ reorderG.func (some 1) = some 3 ∧
    reorderG.func (some 2) = some 1 ∧ reorderG.func (some 3) = some 2 := by
  norm_num [reorderG, partialOp]

theorem reorderF_image : reorderF.func '' fourU = fourU := by
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    rwa [reorderF_apply hx]
  · intro x hx
    exact ⟨x, hx, reorderF_apply hx⟩

theorem reorderG_image : reorderG.func '' fourU = fourU := by
  obtain ⟨h0, h1, h2, h3⟩ := reorderG_table
  ext x
  simp only [fourU, Set.image_insert_eq, Set.image_singleton, h0, h1, h2, h3,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

theorem reorder_entropy_same {f : Operator RealWithBot none} (hdom : fourU ⊆ dom f)
    (himg : f.func '' fourU = fourU) {eps : ENNReal} (he : FiniteRadius eps) :
    covering_number realDist eps (f.func '' fourU) = covering_number realDist eps fourU ∧
    ∃ h : EntropyAdmissible realDist realDist f fourU eps,
      entropyDifference realDist realDist f fourU eps four_nonempty hdom he h = 0 := by
  have hf : fourU.Finite := by simp [fourU]
  have ht := finite_hasFiniteCovers (realReadingDist_gauge id).dist_self hf eps he
  refine ⟨congrArg (covering_number realDist eps) himg, Or.inl ht, ?_⟩
  rw [entropyDifference, himg]
  exact EReal.sub_self ((entropy_ne_top_iff four_nonempty).mpr ht) (entropy_ne_bot four_nonempty)

theorem reorderF_entropy {eps : ENNReal} (he : FiniteRadius eps) :
    covering_number realDist eps (reorderF.func '' fourU) = covering_number realDist eps fourU ∧
    ∃ h : EntropyAdmissible realDist realDist reorderF fourU eps,
      entropyDifference realDist realDist reorderF fourU eps four_nonempty
        reorderF_domain.ge he h = 0 :=
  reorder_entropy_same reorderF_domain.ge reorderF_image he

theorem reorderG_entropy {eps : ENNReal} (he : FiniteRadius eps) :
    covering_number realDist eps (reorderG.func '' fourU) = covering_number realDist eps fourU ∧
    ∃ h : EntropyAdmissible realDist realDist reorderG fourU eps,
      entropyDifference realDist realDist reorderG fourU eps four_nonempty
        reorderG_domain.ge he h = 0 :=
  reorder_entropy_same reorderG_domain.ge reorderG_image he

theorem reorderF_lip {L : ENNReal} :
    HasScalarLipBound realGauge reorderF fourU PUnit.unit PUnit.unit L ↔ 1 ≤ L := by
  constructor
  · intro h
    have hx : (some 0 : RealWithBot) ∈ fourU := by simp [fourU]
    have hy : (some 1 : RealWithBot) ∈ fourU := by simp [fourU]
    have hp := h.2 _ hx _ hy
    change realDist (reorderF.func (some 0)) (reorderF.func (some 1)) ≤
      L * realDist (some 0) (some 1) at hp
    rw [reorderF_apply hx, reorderF_apply hy] at hp
    norm_num at hp
    exact hp
  · intro h
    refine ⟨reorderF_domain.ge, fun x hx y hy => ?_⟩
    change realDist (reorderF.func x) (reorderF.func y) ≤ L * realDist x y
    rw [reorderF_apply hx, reorderF_apply hy]
    simpa [mul_comm] using mul_le_mul_right h (realDist x y)

theorem reorderG_lip {L : ENNReal} :
    HasScalarLipBound realGauge reorderG fourU PUnit.unit PUnit.unit L ↔ 3 ≤ L := by
  constructor
  · intro h
    have hx : (some 0 : RealWithBot) ∈ fourU := by simp [fourU]
    have hy : (some 1 : RealWithBot) ∈ fourU := by simp [fourU]
    have hp := h.2 _ hx _ hy
    change realDist (reorderG.func (some 0)) (reorderG.func (some 1)) ≤
      L * realDist (some 0) (some 1) at hp
    rw [reorderG_table.1, reorderG_table.2.1] at hp
    norm_num at hp
    exact hp
  · intro h
    refine ⟨reorderG_domain.ge, fun x hx y hy => ?_⟩
    change realDist (reorderG.func x) (reorderG.func y) ≤ L * realDist x y
    by_cases he : x = y
    · subst y
      exact ((realReadingDist_gauge id).dist_self _).trans_le (zero_le _)
    · have h₁ := (four_distance_bounds hx hy).2 he
      have hx' := reorderG_image ▸ image_mem reorderG hx
      have hy' := reorderG_image ▸ image_mem reorderG hy
      exact (four_distance_bounds hx' hy').1.trans
        (by simpa only [mul_one] using mul_le_mul' h h₁)

theorem rearrangeEps_finite : FiniteRadius rearrangeEps :=
  ⟨by norm_num [rearrangeEps, ENNReal.ofReal_pos], ENNReal.ofReal_lt_top⟩

theorem rearrange_scale :
    rearrangeEps / 3 = ENNReal.ofReal (7 / 12) := by
  have hp : rearrangeEps / 3 ≠ ⊤ :=
    (finiteRadius_div rearrangeEps_finite (by constructor <;> norm_num : FiniteRadius 3)).2.ne
  rw [← ENNReal.ofReal_toReal hp, ENNReal.toReal_div]
  norm_num [rearrangeEps]

theorem reorder_lip_comparison :
    covering_number realDist rearrangeEps (reorderF.func '' fourU) = 2 ∧
    covering_number realDist rearrangeEps (reorderG.func '' fourU) = 2 ∧
    covering_number realDist (rearrangeEps / 1) fourU = 2 ∧
    covering_number realDist (rearrangeEps / 3) fourU = 4 ∧
    covering_number realDist rearrangeEps (reorderF.func '' fourU) ≤
      covering_number realDist (rearrangeEps / 1) fourU ∧
    covering_number realDist rearrangeEps (reorderG.func '' fourU) <
      covering_number realDist (rearrangeEps / 3) fourU := by
  have h1 : (1 : ENNReal) < rearrangeEps := by
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)
  have h2 : rearrangeEps ≤ (2 : ENNReal) := by
    rw [show (2 : ENNReal) = ENNReal.ofReal 2 by norm_num]
    exact ENNReal.ofReal_le_ofReal (by norm_num [rearrangeEps])
  have h3 : FiniteRadius (3 : ENNReal) := by constructor <;> norm_num
  have h4 : rearrangeEps / 3 ≤ 1 := by
    rw [rearrange_scale, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  have hc := four_cover_middle h1 h2
  have hc' := four_cover_small (finiteRadius_div rearrangeEps_finite h3) h4
  have hf := lip_cover four_nonempty PUnit.unit PUnit.unit
    (show FiniteRadius 1 by constructor <;> norm_num) rearrangeEps_finite (reorderF_lip.mpr le_rfl)
  have hg := lip_cover four_nonempty PUnit.unit PUnit.unit h3
    rearrangeEps_finite (reorderG_lip.mpr le_rfl)
  refine ⟨by rwa [reorderF_image], by rwa [reorderG_image], by simpa using hc, hc', hf, ?_⟩
  refine lt_of_le_of_ne hg ?_
  rw [reorderG_image, hc, hc']
  norm_num

end MG03
