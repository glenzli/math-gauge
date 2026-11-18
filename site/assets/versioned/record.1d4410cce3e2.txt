import MG03.Models

namespace MG03

open Set formal_oet.vol_01.ch_01_foundations

noncomputable def stepValue (x : ℝ) : ℝ := if x < 0 then 0 else 1
noncomputable def stepOp : Operator RealWithBot none := realOp stepValue
def stepU : Set RealWithBot := realSet (Ico (-1) 0 ∪ Ioc 0 1)

theorem step_valid :
    (∀ i, ExtendedPseudoMetric RealWithBot none (realGauge i)) ∧
      stepU.Nonempty ∧ stepU ⊆ dom stepOp :=
  ⟨fun _ => realReadingDist_gauge id, ⟨some 1, by norm_num [stepU]⟩, realSet_dom _ _⟩

theorem small_real {b : ℝ} (hb : 0 < b) : ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧ a < b := by
  refine ⟨min 1 (b / 2), lt_min (by norm_num) (by linarith), min_le_left _ _, ?_⟩
  exact (min_le_right _ _).trans_lt (by linarith)

theorem small_ofReal {b : ENNReal} (hb : 0 < b) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧ ENNReal.ofReal a < b := by
  obtain ⟨c, hc, hcb⟩ := exists_between hb
  have hctop := hcb.trans_le (le_top : b ≤ ⊤)
  obtain ⟨a, ha, h1, hac⟩ := small_real (ENNReal.toReal_pos (ne_of_gt hc) hctop.ne)
  exact ⟨a, ha, h1, ((ENNReal.ofReal_lt_iff_lt_toReal ha.le hctop.ne).mpr hac).trans hcb⟩

theorem step_mem {y : ℝ} : some y ∈ stepU ↔ (-1 ≤ y ∧ y < 0) ∨ (0 < y ∧ y ≤ 1) := by
  simp [stepU]

theorem step_ne_zero {y : ℝ} (hy : some y ∈ stepU) : y ≠ 0 := by
  rcases step_mem.mp hy with h | h
  · exact ne_of_lt h.2
  · exact ne_of_gt h.1

theorem step_legal {y : ℝ} (hy : some y ∈ stepU) {r : ENNReal} :
    LegalRadius realDist realDist stepOp stepU (some y) r ↔
      FiniteRadius r ∧ r ≤ ENNReal.ofReal |y| := by
  rw [legalRadius_iff]
  constructor
  · rintro ⟨hr, h⟩
    refine ⟨hr, le_of_not_gt ?_⟩
    intro hlt
    have hδ := (ENNReal.ofReal_lt_iff_lt_toReal (abs_nonneg y) hr.2.ne).mp hlt
    obtain ⟨a, ha, h1, hsmall⟩ := small_real (sub_pos.mpr hδ)
    by_cases hn : y < 0
    · have hx : some a ∈ stepU := step_mem.mpr (Or.inr ⟨ha, h1⟩)
      have hd : realDist (some a) (some y) < r := by
        change ENNReal.ofReal |a - y| < r
        apply (ENNReal.ofReal_lt_iff_lt_toReal (abs_nonneg _) hr.2.ne).mpr
        rw [abs_of_pos (by linarith : 0 < a - y)]
        rw [abs_of_neg hn] at hsmall
        linarith
      have hz := h _ hx hd
      norm_num [stepOp, stepValue, hn, ha.not_gt] at hz
    · have hy' : 0 < y := lt_of_le_of_ne (le_of_not_gt hn) (step_ne_zero hy).symm
      have hx : some (-a) ∈ stepU := step_mem.mpr (Or.inl ⟨by linarith, by linarith⟩)
      have hd : realDist (some (-a)) (some y) < r := by
        change ENNReal.ofReal |(-a) - y| < r
        apply (ENNReal.ofReal_lt_iff_lt_toReal (abs_nonneg _) hr.2.ne).mpr
        rw [abs_of_neg (by linarith : -a - y < 0)]
        rw [abs_of_pos hy'] at hsmall
        linarith
      have hz := h _ hx hd
      norm_num [stepOp, stepValue, hn, show -a < 0 by linarith] at hz
  · rintro ⟨hr, hle⟩
    refine ⟨hr, ?_⟩
    rintro _ ⟨x, _, rfl⟩ hd
    have hdist := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (abs_nonneg (x - y))).mp
      (hd.trans_le hle)
    have hs : (x < 0 ↔ y < 0) := by
      constructor
      · intro hx
        by_contra hn
        rw [abs_of_nonneg (le_of_not_gt hn)] at hdist
        have := (abs_lt.mp hdist).1
        linarith
      · intro hn
        by_contra hx
        rw [abs_of_neg hn] at hdist
        have := (abs_lt.mp hdist).2
        linarith [le_of_not_gt hx]
    apply (realReadingDist_zero_iff id (stepValue x) (stepValue y)).mpr
    simp only [id_eq, stepValue, hs]

theorem step_radius (y : RealWithBot) (hy : y ∈ stepU) :
    ∃ z : ℝ, y = some z ∧ radius realDist realDist stepOp stepU y = ENNReal.ofReal |z| ∧
      0 < radius realDist realDist stepOp stepU y := by
  obtain ⟨z, hz, rfl⟩ := hy
  have hy : some z ∈ stepU := ⟨z, hz, rfl⟩
  have hp := ENNReal.ofReal_pos.mpr (abs_pos.mpr (step_ne_zero hy))
  have heq : radius realDist realDist stepOp stepU (some z) = ENNReal.ofReal |z| := by
    apply le_antisymm
    · apply sSup_le
      exact fun _ hr => ((step_legal hy).mp hr).2
    · exact radius_ge_legal ((step_legal hy).mpr ⟨⟨hp, ENNReal.ofReal_lt_top⟩, le_rfl⟩)
  exact ⟨z, rfl, heq, heq.symm ▸ hp⟩

theorem step_uniform_zero : uniformOn realDist realDist stepOp stepU = 0 := by
  apply le_antisymm _ (zero_le _)
  apply le_of_not_gt
  intro h
  obtain ⟨a, ha, h1, hlt⟩ := small_ofReal h
  have hy : some a ∈ stepU := step_mem.mpr (Or.inr ⟨ha, h1⟩)
  obtain ⟨z, he, hr, _⟩ := step_radius (some a) hy
  have haz := Option.some.inj he
  rw [← haz, abs_of_pos ha] at hr
  exact (not_lt_of_ge ((uniform_le_point (eIn := realDist) (eOut := realDist)
    (f := stepOp) (U := stepU) hy).trans_eq hr)) hlt

theorem step_cover_counterexample {tau : ENNReal} (ht : FiniteRadius tau) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧ ENNReal.ofReal (2 * a) < tau ∧
      ({some (-a), some a} : Set RealWithBot) ⊆ stepU ∧
      stepOp.func '' ({some (-a), some a} : Set RealWithBot) = {some 0, some 1} ∧
      covering_number realDist tau {some (-a), some a} = 1 ∧
      covering_number realDist (ENNReal.ofReal (1 / 2))
        (stepOp.func '' ({some (-a), some a} : Set RealWithBot)) = 2 := by
  have htr : 0 < tau.toReal := ENNReal.toReal_pos (ne_of_gt ht.1) ht.2.ne
  obtain ⟨a, ha, ha₁, haτ⟩ := small_real (show 0 < tau.toReal / 2 by linarith)
  have ha₂ : ENNReal.ofReal (2 * a) < tau :=
    (ENNReal.ofReal_lt_iff_lt_toReal (by linarith : 0 ≤ 2 * a) ht.2.ne).mpr (by linarith)
  have hneg : -a < 0 := by linarith
  have hsub : ({some (-a), some a} : Set RealWithBot) ⊆ stepU :=
    Set.pair_subset_iff.mpr ⟨step_mem.mpr (Or.inl ⟨by linarith, hneg⟩),
      step_mem.mpr (Or.inr ⟨ha, ha₁⟩)⟩
  have himg : stepOp.func '' ({some (-a), some a} : Set RealWithBot) = {some 0, some 1} := by
    simp [Set.image_pair, stepOp, stepValue, hneg, ha.not_gt]
  refine ⟨a, ha, ha₁, ha₂, hsub, himg, ?_, ?_⟩
  · apply cover_one_of_close (by simp)
    intro x hx y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    have hp : realDist (some (-a)) (some a) < tau := by
      change ENNReal.ofReal |(-a) - a| < tau
      rw [abs_of_neg (by linarith : -a - a < 0), show -(-a - a) = 2 * a by ring]
      exact ha₂
    let he := realReadingDist_gauge id
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact (he.dist_self (some (-a))).trans_lt ht.1
    · exact hp
    · exact (he.symm (some a) (some (-a))).trans_lt hp
    · exact (he.dist_self (some a)).trans_lt ht.1
  · rw [himg]
    classical
    let S : Finset RealWithBot := {some 0, some 1}
    have hc : S.card = 2 := by simp [S]
    have hS : (↑S : Set RealWithBot) = {some 0, some 1} := by simp [S]
    rw [← hS]
    suffices covering_number realDist (ENNReal.ofReal (1 / 2)) (↑S : Set RealWithBot) =
        (S.card : ENNReal) by simpa [hc] using this
    apply separated_finset_cover (realReadingDist_gauge id).dist_self (by norm_num [ENNReal.ofReal_pos])
    intro x hx y hy hne
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact (hne rfl).elim
    · change ENNReal.ofReal (1 / 2) ≤ ENNReal.ofReal |(0 : ℝ) - 1|
      exact ENNReal.ofReal_le_ofReal (by norm_num)
    · change ENNReal.ofReal (1 / 2) ≤ ENNReal.ofReal |(1 : ℝ) - 0|
      exact ENNReal.ofReal_le_ofReal (by norm_num)
    · exact (hne rfl).elim

theorem step_no_uniform_cover :
    (∀ y ∈ stepU, 0 < radius realDist realDist stepOp stepU y) ∧
    ∀ tau, FiniteRadius tau → ¬ ∀ B ⊆ stepU,
      covering_number realDist (ENNReal.ofReal (1 / 2)) (stepOp.func '' B) ≤
        covering_number realDist tau B := by
  refine ⟨fun y hy => (step_radius y hy).choose_spec.2.2, ?_⟩
  intro tau ht hc
  obtain ⟨a, _, _, _, ha, _, hi, ho⟩ := step_cover_counterexample ht
  have h := hc {some (-a), some a} ha
  rw [hi, ho] at h
  norm_num at h

end MG03
