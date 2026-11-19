import Chapter.Models

open formal_oet.vol_01.ch_01_foundations
open scoped ENNReal
namespace Chapter

theorem two_center_upper {X : Type} {D : X → X → ℝ≥0∞} {U : Set X} {r : ℝ≥0∞}
    (a b : X) (ha : a ∈ U) (hb : b ∈ U) (h : ∀ x ∈ U, D x a < r ∨ D x b < r) :
    covering_number D r U ≤ 2 := by
  classical
  have hn : InternalEpsilonNet D r U {a,b} := by
    constructor
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact ha
      · exact (Finset.mem_singleton.mp hx).symm ▸ hb
    · intro x hx
      rcases h x hx with hx' | hx'
      · exact ⟨a,by simp,hx'⟩
      · exact ⟨b,by simp,hx'⟩
  exact (cover_le_card hn).trans (by simpa using
    (show (({a,b} : Finset X).card : ℝ≥0∞) ≤ (2 : ℕ) by
      exact_mod_cast Finset.card_insert_le a ({b} : Finset X)))

theorem two_center_lower {X : Type} {D : X → X → ℝ≥0∞} {U : Set X} {r : ℝ≥0∞}
    (hn : U.Nonempty) (h : ∀ c ∈ U, ∃ x ∈ U, r ≤ D x c) :
    2 ≤ covering_number D r U := by
  classical
  change ((2 : ℕ) : ℝ≥0∞) ≤ _
  apply card_lower_cover
  intro S hs
  by_contra! hh
  obtain ⟨x,hx⟩ := hn
  obtain ⟨c,hc,_⟩ := hs.2 x hx
  obtain ⟨z,hz,hcz⟩ := h c (hs.1 hc)
  obtain ⟨c',hc',hz'⟩ := hs.2 z hz
  have he : c' = c := Finset.card_le_one.mp (by omega) c' hc' c hc
  exact (not_lt_of_ge hcz) (he ▸ hz')

namespace Step

noncomputable def step (x : ℝ) : ℝ := if x < 0 then 0 else 1
noncomputable def f := liftRealMap step
def S : Set ℝ := Set.Ico (-1) 0 ∪ Set.Ioc 0 1
def U : Set (Option ℝ) := realSet S

theorem legal : ExtendedPseudoMetric (Option ℝ) none realDist ∧ U.Nonempty ∧ U ⊆ dom f :=
  ⟨read_legal id, ⟨some 1, by simp [U,S]⟩, realSet_domain step _⟩

theorem step_pair (x y : ℝ) (_hx : x ≠ 0) (_hy : y ≠ 0) :
    step x ≠ step y → |y| ≤ |x - y| := by
  intro h
  by_cases hy' : y < 0
  · have hx' : 0 ≤ x := by
      by_contra! hn
      exact h (by simp [step, hn, hy'])
    rw [abs_of_neg hy', abs_of_nonneg (by linarith)]
    linarith
  · have hx' : x < 0 := by
      by_contra! hn
      exact h (by simp [step, not_lt.mpr hn, hy'])
    rw [abs_of_nonneg (le_of_not_gt hy'), abs_of_neg (by linarith [le_of_not_gt hy'])]
    linarith

theorem nonzero_of_mem {x : ℝ} (hx : x ∈ S) : x ≠ 0 := by
  rcases hx with h | h
  · exact h.2.ne
  · exact h.1.ne'

theorem admissible_exact {y : ℝ} (hy : y ∈ S) {r : ℝ≥0∞} :
    r ∈ admissible f realDist realDist U (some y) ↔
      FinitePositive r ∧ r ≤ ENNReal.ofReal |y| := by
  rw [admissible_iff]
  constructor
  · rintro ⟨hr,h⟩
    refine ⟨hr, le_of_not_gt fun hr' => ?_⟩
    have hylt : |y| < r.toReal := (ENNReal.ofReal_lt_iff_lt_toReal (abs_nonneg _) hr.2.ne).mp hr'
    let a := min ((r.toReal - |y|)/2) 1
    have ha : 0 < a := lt_min (by linarith) zero_lt_one
    have ha1 : a ≤ 1 := min_le_right _ _
    have har : a + |y| < r.toReal := by
      have hh : a ≤ (r.toReal - |y|)/2 := min_le_left _ _
      linarith
    by_cases hyn : y < 0
    · have hx : a ∈ S := Or.inr ⟨ha,ha1⟩
      have hd : realDist (some a) (some y) < r := by
        rw [real_some, ENNReal.ofReal_lt_iff_lt_toReal (abs_nonneg _) hr.2.ne,
          abs_of_pos (by linarith)]
        rw [abs_of_neg hyn] at har
        linarith
      have he := (real_zero _ _).mp (h (some a) ((mem_realSet _ _).mpr hx) hd)
      simp [step, not_lt.mpr ha.le, hyn] at he
    · have hyp : 0 < y := lt_of_le_of_ne (le_of_not_gt hyn) (nonzero_of_mem hy).symm
      have hx : -a ∈ S := Or.inl ⟨by linarith,by linarith⟩
      have hd : realDist (some (-a)) (some y) < r := by
        rw [real_some, ENNReal.ofReal_lt_iff_lt_toReal (abs_nonneg _) hr.2.ne,
          abs_of_neg (by linarith)]
        rw [abs_of_pos hyp] at har
        linarith
      have he := (real_zero _ _).mp (h (some (-a)) ((mem_realSet _ _).mpr hx) hd)
      simp [step, show -a < 0 by linarith, hyn] at he
  · rintro ⟨hr,hr'⟩
    refine ⟨hr,?_⟩
    rintro _ ⟨x,hx,rfl⟩ hd
    apply (real_zero _ _).mpr
    by_contra hn
    exact (hd.trans_le hr').not_ge (ENNReal.ofReal_le_ofReal
      (step_pair x y (nonzero_of_mem hx) (nonzero_of_mem hy) hn))

theorem pointwise {y : ℝ} (hy : y ∈ S) :
    radius f realDist realDist U (some y) = ENNReal.ofReal |y| ∧
    0 < radius f realDist realDist U (some y) := by
  have hpos : 0 < ENNReal.ofReal |y| := ENNReal.ofReal_pos.mpr (abs_pos.mpr (nonzero_of_mem hy))
  have he : radius f realDist realDist U (some y) = ENNReal.ofReal |y| :=
    le_antisymm (sSup_le fun r hr => ((admissible_exact hy).mp hr).2)
      (le_sSup ((admissible_exact hy).mpr ⟨⟨hpos, ENNReal.ofReal_lt_top⟩,le_rfl⟩))
  exact ⟨he,he.symm ▸ hpos⟩

theorem small_positive {r : ℝ≥0∞} (hr : FinitePositive r) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧ ENNReal.ofReal (2*a) < r := by
  have h : 0 < r.toReal := ENNReal.toReal_pos hr.1.ne' hr.2.ne
  refine ⟨min (r.toReal / 4) 1, lt_min (by linarith) zero_lt_one, min_le_right _ _, ?_⟩
  have h1 : min (r.toReal / 4) 1 ≤ r.toReal / 4 := min_le_left _ _
  rw [ENNReal.ofReal_lt_iff_lt_toReal (by positivity) hr.2.ne]
  linarith

theorem uniform_zero_value : uniform f realDist realDist U U = 0 := by
  apply nonpos_iff_eq_zero.mp
  by_contra! h
  obtain ⟨r,hr,hrt⟩ := exists_between h
  obtain ⟨a,ha,ha1,har⟩ := small_positive ⟨hr,hrt.trans_le le_top⟩
  have hx : a ∈ S := Or.inr ⟨ha,ha1⟩
  have hrle : uniform f realDist realDist U U ≤ radius f realDist realDist U (some a) :=
    uniform_le_point ((mem_realSet _ _).mpr hx)
  rw [(pointwise hx).1, abs_of_pos ha] at hrle
  exact hrt.not_ge (hrle.trans ((ENNReal.ofReal_le_ofReal (by linarith : a ≤ 2*a)).trans har.le))

theorem cover_failure {r : ℝ≥0∞} (hr : FinitePositive r) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧ ENNReal.ofReal (2*a) < r ∧
      let B : Set (Option ℝ) := {some (-a), some a}
      B ⊆ U ∧ covering_number realDist r B = 1 ∧
        covering_number realDist (ENNReal.ofReal (1/2)) (f.func '' B) = 2 := by
  obtain ⟨a,ha,ha1,har⟩ := small_positive hr
  have hp : a ∈ S := Or.inr ⟨ha,ha1⟩
  have hn : -a ∈ S := Or.inl ⟨by linarith,by linarith⟩
  have himg : f.func '' ({some (-a),some a} : Set (Option ℝ)) = {some 0,some 1} := by
    simp [Set.image_insert_eq, f, step, show -a < 0 by linarith, not_lt.mpr ha.le]
  refine ⟨a,ha,ha1,har,?_,?_,?_⟩
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact (mem_realSet _ _).mpr hn
    · exact (mem_realSet _ _).mpr hp
  · apply cover_single_center
    refine ⟨some a,by simp,?_⟩
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · rwa [real_some, show -a-a = -(2*a) by ring, abs_neg, abs_of_nonneg (by positivity)]
    · simpa using hr.1
  · rw [himg]
    apply le_antisymm
    · apply two_center_upper (some 0) (some 1) (by simp) (by simp)
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · left; norm_num
      · right; norm_num
    · apply two_center_lower ⟨some 0,by simp⟩
      intro c hc
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
      rcases hc with rfl | rfl
      · exact ⟨some 1,by simp,by rw [real_some]; norm_num [ENNReal.ofReal_le_one]⟩
      · exact ⟨some 0,by simp,by rw [real_some]; norm_num [ENNReal.ofReal_le_one]⟩


theorem pointwise_cover_counterexample :
    (∀ y ∈ U, 0 < radius f realDist realDist U y) ∧
    ∀ r, FinitePositive r →
      ∃ B ⊆ U, covering_number realDist r B = 1 ∧
        covering_number realDist (ENNReal.ofReal (1/2)) (f.func '' B) = 2 := by
  constructor
  · rintro _ ⟨y,hy,rfl⟩
    exact (pointwise hy).2
  · intro r hr
    obtain ⟨a,_,_,_,hB,h1,h2⟩ := cover_failure hr
    exact ⟨{some (-a),some a},hB,h1,h2⟩

end Step
end Chapter
