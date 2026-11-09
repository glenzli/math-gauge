import CH03.Core6

namespace formal_oet.vol_01.ch_03_operator_local_degeneracy
open formal_oet.vol_01.ch_01_foundations
open Set

set_option maxHeartbeats 4000000

def lineDist : Option ℝ → Option ℝ → ENNReal
  | none, none => 0
  | some x, some y => ENNReal.ofReal |x - y|
  | none, some _ => ⊤
  | some _, none => ⊤

@[simp] theorem lineDist_none_none : lineDist none none = 0 := rfl
@[simp] theorem lineDist_some_some (x y : ℝ) :
    lineDist (some x) (some y) = ENNReal.ofReal |x - y| := rfl
@[simp] theorem lineDist_none_some (y : ℝ) : lineDist none (some y) = ⊤ := rfl
@[simp] theorem lineDist_some_none (x : ℝ) : lineDist (some x) none = ⊤ := rfl

theorem lineDist_extended : ExtendedPseudoMetric (Option ℝ) none lineDist where
  nonabsorbing := ⟨some 0, by simp⟩
  dist_self := by
    intro x
    rcases x with _ | x <;> simp
  symm := by
    intro x y
    rcases x with _ | x <;> rcases y with _ | y <;> simp [lineDist, abs_sub_comm]
  triangle := by
    intro x y z
    rcases x with _ | x <;> rcases y with _ | y <;> rcases z with _ | z <;> simp [lineDist]
    rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (abs_sub_le x y z)
  isolate_bot := by
    intro x hx
    rcases x with _ | x
    · exact (hx rfl).elim
    · simp

noncomputable def stepFun : Option ℝ → Option ℝ
  | none => none
  | some x => some (if x < 0 then 0 else 1)

@[simp] theorem stepFun_none : stepFun none = none := rfl
@[simp] theorem stepFun_some (x : ℝ) :
    stepFun (some x) = some (if x < 0 then 0 else 1) := rfl

theorem stepFun_preserves_bot : stepFun none = none := rfl

noncomputable def stepOp : Operator (Option ℝ) none where
  func := stepFun
  preserves_bot := stepFun_preserves_bot

def stepU : Set (Option ℝ) :=
  some '' (Set.Ico (-1 : ℝ) 0 ∪ Set.Ioc (0 : ℝ) 1)

theorem mem_stepU {x : Option ℝ} :
    x ∈ stepU ↔ ∃ r : ℝ, x = some r ∧ ((-1 ≤ r ∧ r < 0) ∨ (0 < r ∧ r ≤ 1)) := by
  unfold stepU
  constructor
  · rintro ⟨r, hr, rfl⟩
    rcases hr with hr | hr
    · exact ⟨r, rfl, Or.inl ⟨hr.1, hr.2⟩⟩
    · exact ⟨r, rfl, Or.inr ⟨hr.1, hr.2⟩⟩
  · rintro ⟨r, rfl, hr⟩
    refine ⟨r, ?_, rfl⟩
    rcases hr with hr | hr
    · exact Or.inl ⟨hr.1, hr.2⟩
    · exact Or.inr ⟨hr.1, hr.2⟩

theorem stepU_some_ne_zero {y : ℝ} (hy : some y ∈ stepU) : y ≠ 0 := by
  rcases (mem_stepU.mp hy) with ⟨r, hsr, hr⟩
  injection hsr with hry
  subst r
  rcases hr with hr | hr <;> linarith

theorem abs_pos_of_mem_stepU {y : ℝ} (hy : some y ∈ stepU) : 0 < |y| :=
  abs_pos.mpr (stepU_some_ne_zero hy)

theorem step_same_neg {x y : ℝ} (hx : x < 0) (hy : y < 0) :
    stepFun (some x) = stepFun (some y) := by
  simp [stepFun, hx, hy]

theorem step_same_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    stepFun (some x) = stepFun (some y) := by
  simp [stepFun, not_lt.mpr (le_of_lt hx), not_lt.mpr (le_of_lt hy)]

theorem step_neg_pos {x y : ℝ} (hx : x < 0) (hy : 0 < y) :
    lineDist (stepFun (some x)) (stepFun (some y)) = 1 := by
  simp [stepFun, hx, not_lt.mpr (le_of_lt hy)]

theorem step_pos_neg {x y : ℝ} (hx : 0 < x) (hy : y < 0) :
    lineDist (stepFun (some x)) (stepFun (some y)) = 1 := by
  simp [stepFun, not_lt.mpr (le_of_lt hx), hy]

theorem lineDist_step_same_sign {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : (x < 0 ∧ y < 0) ∨ (0 < x ∧ 0 < y)) :
    lineDist (stepFun (some x)) (stepFun (some y)) = 0 := by
  rcases h with ⟨hxneg, hyneg⟩ | ⟨hxpos, hypos⟩
  · rw [step_same_neg hxneg hyneg]; simp
  · rw [step_same_pos hxpos hypos]; simp

theorem opposite_sign_abs_gt {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : ¬ ((x < 0 ∧ y < 0) ∨ (0 < x ∧ 0 < y))) :
    |y| < |x - y| := by
  rcases lt_or_gt_of_ne hx with hxneg | hxpos <;>
    rcases lt_or_gt_of_ne hy with hyneg | hypos
  · exact False.elim (h (Or.inl ⟨hxneg, hyneg⟩))
  · rw [abs_of_pos hypos, abs_of_neg (sub_neg.mpr (by linarith))]
    linarith
  · rw [abs_of_neg hyneg, abs_of_pos (sub_pos.mpr (by linarith))]
    linarith
  · exact False.elim (h (Or.inr ⟨hxpos, hypos⟩))

theorem ofReal_abs_y_legal {y : ℝ} (hy : some y ∈ stepU) :
    LegalRadius lineDist (fun a b => lineDist a b = 0) stepOp (some y) stepU
      (ENNReal.ofReal |y|) := by
  refine ⟨ENNReal.ofReal_pos.mpr (abs_pos_of_mem_stepU hy), ENNReal.ofReal_ne_top, ?_⟩
  intro x hx hlt
  rcases (mem_stepU.mp hx) with ⟨xr, hxs, hxrU⟩
  subst x
  rcases (mem_stepU.mp hy) with ⟨yr, hys, hyrU⟩
  injection hys with hyr
  subst y
  have hxrne : xr ≠ 0 := by
    rcases hxrU with hxrU | hxrU <;> linarith
  have hyrne : yr ≠ 0 := by
    rcases hyrU with hyrU | hyrU <;> linarith
  have hltreal : |xr - yr| < |yr| := by
    rw [lineDist_some_some] at hlt
    rwa [ENNReal.ofReal_lt_ofReal_iff (abs_pos_of_mem_stepU hy)] at hlt
  have hsame : (xr < 0 ∧ yr < 0) ∨ (0 < xr ∧ 0 < yr) := by
    by_contra hnot
    have hgt := opposite_sign_abs_gt hxrne hyrne hnot
    linarith
  change lineDist (stepFun (some xr)) (stepFun (some yr)) = 0
  exact lineDist_step_same_sign hxrne hyrne hsame

/-- Every legal radius is at most `|y|`; the proof constructs a point of the
opposite sign inside the ball when the radius is larger. -/
theorem legal_radius_le_abs {y : ℝ} (hy : some y ∈ stepU) {r : ENNReal}
    (hr : LegalRadius lineDist (fun a b => lineDist a b = 0) stepOp (some y) stepU r) :
    r ≤ ENNReal.ofReal |y| := by
  by_contra hle
  have hlt : ENNReal.ofReal |y| < r := lt_of_not_ge hle
  have hrtop : r ≠ ⊤ := hr.2.1
  have hreal : |y| < r.toReal := by
    have := (ENNReal.ofReal_lt_iff_lt_toReal (abs_nonneg y) hrtop).mp hlt
    simpa using this
  let δ : ℝ := r.toReal - |y|
  have hδ : 0 < δ := by dsimp [δ]; linarith
  let a : ℝ := min (1/2 : ℝ) (δ / 2)
  have hapos : 0 < a := by
    dsimp [a]
    exact lt_min (by norm_num) (by linarith)
  have hahalf : a ≤ 1/2 := by dsimp [a]; exact min_le_left _ _
  have hadelta : a ≤ δ / 2 := by dsimp [a]; exact min_le_right _ _
  by_cases hypos : 0 < y
  · let x : ℝ := -a
    have hxneg : x < 0 := by dsimp [x]; linarith
    have hxU : some x ∈ stepU := by
      rw [mem_stepU]
      refine ⟨x, rfl, Or.inl ⟨?_, hxneg⟩⟩
      dsimp [x]; linarith
    have hdist : |x - y| < r.toReal := by
      have habs : |x - y| = y + a := by
        rw [abs_of_neg (sub_neg.mpr (by dsimp [x]; linarith))]
        dsimp [x]; ring
      rw [habs]
      dsimp [δ] at hadelta
      rw [abs_of_pos hypos] at hreal hadelta
      linarith
    have hltline : lineDist (some x) (some y) < r := by
      rw [lineDist_some_some]
      exact (ENNReal.ofReal_lt_iff_lt_toReal (abs_nonneg _) hrtop).mpr hdist
    have hzero := hr.2.2 (some x) hxU hltline
    change lineDist (stepFun (some x)) (stepFun (some y)) = 0 at hzero
    have hone : lineDist (stepFun (some x)) (stepFun (some y)) = 1 :=
      step_neg_pos hxneg hypos
    rw [hone] at hzero
    norm_num at hzero
  · have hyneg : y < 0 := by
      rcases (mem_stepU.mp hy) with ⟨yr, hsy, hyrU⟩
      injection hsy with hry
      subst yr
      rcases hyrU with hyrU | hyrU
      · exact hyrU.2
      · exact False.elim (hypos hyrU.1)
    let x : ℝ := a
    have hxpos : 0 < x := by dsimp [x]; exact hapos
    have hxU : some x ∈ stepU := by
      rw [mem_stepU]
      refine ⟨x, rfl, Or.inr ⟨hxpos, ?_⟩⟩
      dsimp [x]; linarith
    have hdist : |x - y| < r.toReal := by
      have habs : |x - y| = a + (-y) := by
        rw [abs_of_pos (sub_pos.mpr (by dsimp [x]; linarith))]
        dsimp [x]; ring
      rw [habs]
      have habs_y : |y| = -y := abs_of_neg hyneg
      dsimp [δ] at hadelta
      rw [habs_y] at hreal hadelta
      linarith
    have hltline : lineDist (some x) (some y) < r := by
      rw [lineDist_some_some]
      exact (ENNReal.ofReal_lt_iff_lt_toReal (abs_nonneg _) hrtop).mpr hdist
    have hzero := hr.2.2 (some x) hxU hltline
    change lineDist (stepFun (some x)) (stepFun (some y)) = 0 at hzero
    have hone : lineDist (stepFun (some x)) (stepFun (some y)) = 1 :=
      step_pos_neg hxpos hyneg
    rw [hone] at hzero
    norm_num at hzero

theorem pointwise_radius_eq_abs {y : ℝ} (hy : some y ∈ stepU) :
    pointwiseRadius lineDist (fun a b => lineDist a b = 0) stepOp (some y) stepU =
      ENNReal.ofReal |y| := by
  apply le_antisymm
  · unfold pointwiseRadius
    apply iSup_le
    intro r
    exact legal_radius_le_abs hy r.2
  · exact le_pointwiseRadius_of_legal (ofReal_abs_y_legal hy)

theorem unified_radius_step_eq_zero :
    unifiedRadius lineDist (fun a b => lineDist a b = 0) stepOp stepU stepU = 0 := by
  unfold unifiedRadius
  apply le_antisymm
  · have h : (⨅ y : {y : Option ℝ // y ∈ stepU},
        pointwiseRadius lineDist (fun a b => lineDist a b = 0) stepOp y.1 stepU) = ⊥ := by
      apply (iInf_eq_bot _).mpr
      intro b hb
      by_cases hbtop : b = ⊤
      · refine ⟨⟨some (1/2), ?_⟩, ?_⟩
        · rw [mem_stepU]
          exact ⟨1/2, rfl, Or.inr ⟨by norm_num, by norm_num⟩⟩
        · rw [pointwise_radius_eq_abs (by
            rw [mem_stepU]
            exact ⟨1/2, rfl, Or.inr ⟨by norm_num, by norm_num⟩⟩)]
          simp [hbtop]
      · have hbpos : 0 < b.toReal := ENNReal.toReal_pos (ne_of_gt hb) hbtop
        let ε : ℝ := min (1/2 : ℝ) (b.toReal / 2)
        have hεpos : 0 < ε := lt_min (by norm_num) (by linarith)
        have hεle : ε ≤ 1/2 := min_le_left _ _
        have hεb : ε < b.toReal := lt_of_le_of_lt (min_le_right _ _) (by linarith)
        refine ⟨⟨some ε, ?_⟩, ?_⟩
        · rw [mem_stepU]
          exact ⟨ε, rfl, Or.inr ⟨hεpos, by linarith⟩⟩
        · rw [pointwise_radius_eq_abs (by
            rw [mem_stepU]
            exact ⟨ε, rfl, Or.inr ⟨hεpos, by linarith⟩⟩)]
          rw [ENNReal.ofReal_lt_iff_lt_toReal (abs_nonneg _) hbtop]
          simpa [abs_of_pos hεpos] using hεb
    simpa using le_of_eq h
  · exact zero_le _


theorem stepU_subset_dom : stepU ⊆ dom stepOp := by
  intro x hx
  rcases (mem_stepU.mp hx) with ⟨r, rfl, hr⟩
  rw [dom]
  simp [stepOp, stepFun]

theorem legal_radius_iff_abs {y : ℝ} (hy : some y ∈ stepU) {r : ENNReal}
    (hr0 : 0 < r) :
    LegalRadius lineDist (fun a b => lineDist a b = 0) stepOp (some y) stepU r ↔
      r ≤ ENNReal.ofReal |y| := by
  constructor
  · exact legal_radius_le_abs hy
  · intro hle
    exact legalRadius_mono hr0 hle (ofReal_abs_y_legal hy)

theorem counterexample_3_1_structure :
    ExtendedPseudoMetric (Option ℝ) none lineDist ∧
      (∀ x ∈ stepU, stepOp.func x ≠ none) ∧
      (∀ y : ℝ, some y ∈ stepU → 0 < pointwiseRadius lineDist
        (fun a b => lineDist a b = 0) stepOp (some y) stepU) := by
  refine ⟨lineDist_extended, ?_, ?_⟩
  · intro x hx
    have hx' := stepU_subset_dom hx
    simpa [dom] using hx'
  · intro y hy
    rw [pointwise_radius_eq_abs hy]
    exact ENNReal.ofReal_pos.mpr (abs_pos_of_mem_stepU hy)
end formal_oet.vol_01.ch_03_operator_local_degeneracy
