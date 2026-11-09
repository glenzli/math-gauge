import Ch03.Floor

namespace OET.Ch03

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set

/-- Exercise 3.5's four-point domain. -/
def fourDomain : Set RealBase := {some 0, some 1, some 2, some 3}

noncomputable def fourFinset : Finset RealBase := {some 0, some 1, some 2, some 3}

theorem fourDist_ne_lower {x y : RealBase} (hx : x ∈ fourDomain) (hy : y ∈ fourDomain)
    (hne : x ≠ y) : 1 ≤ usualDist x y := by
  simp only [fourDomain, mem_insert_iff, mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
    norm_num [usualDist, optionDist] at *

/-- Complete finite-positive-precision covering formula for the four points. -/
theorem fourPoint_covering {ε : ENNReal} (hε0 : 0 < ε) (hεtop : ε < ⊤) :
    covering_number usualDist ε fourDomain =
      if ε ≤ 1 then 4 else if ε ≤ 2 then 2 else 1 := by
  by_cases h1 : ε ≤ 1
  · rw [if_pos h1]
    apply le_antisymm
    · have hnet : InternalEpsilonNet usualDist ε fourDomain fourFinset := by
        constructor
        · intro x hx
          change x ∈ fourFinset at hx
          simpa [fourDomain, fourFinset] using hx
        · intro x hx
          exact ⟨x, by simpa [fourDomain, fourFinset] using hx,
            by simpa [usualDist_extended.dist_self] using hε0⟩
      simpa [fourFinset] using covering_number_le_of_net hnet
    · apply le_covering_number_of_card
      intro S hS
      have hsub : fourFinset ⊆ S := by
        intro x hx
        have hxU : x ∈ fourDomain := by simpa [fourDomain, fourFinset] using hx
        obtain ⟨c, hc, hxc⟩ := hS.2 x hxU
        have hcU := hS.1 hc
        have hxc' : x = c := by
          by_contra hne
          have hone := fourDist_ne_lower hxU hcU hne
          exact (not_lt_of_ge h1) (hone.trans_lt hxc)
        rw [hxc']
        exact hc
      have hc := Finset.card_le_card hsub
      norm_num [fourFinset] at hc ⊢
      exact hc
  · rw [if_neg h1]
    have h1lt : 1 < ε := lt_of_not_ge h1
    by_cases h2 : ε ≤ 2
    · rw [if_pos h2]
      apply le_antisymm
      · have hnet : InternalEpsilonNet usualDist ε fourDomain {some 0, some 2} := by
          constructor
          · intro x hx
            change x ∈ ({some 0, some 2} : Finset RealBase) at hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl <;> simp [fourDomain]
          · intro x hx
            simp only [fourDomain, mem_insert_iff, mem_singleton_iff] at hx
            rcases hx with rfl | rfl | rfl | rfl
            · exact ⟨some 0, by simp, by simpa [usualDist, optionDist] using hε0⟩
            · exact ⟨some 0, by simp, by norm_num [usualDist, optionDist]; exact h1lt⟩
            · exact ⟨some 2, by simp, by simpa [usualDist, optionDist] using hε0⟩
            · exact ⟨some 2, by simp, by norm_num [usualDist, optionDist]; exact h1lt⟩
        simpa using covering_number_le_of_net hnet
      · apply le_covering_number_of_card
        intro S hS
        by_contra hn
        have hcardlt : S.card < 2 := lt_of_not_ge hn
        obtain ⟨c, hc, _⟩ := hS.2 (some 0) (by simp [fourDomain])
        have hcard1 : S.card = 1 := le_antisymm (Nat.le_of_lt_succ hcardlt)
          (Finset.card_pos.mpr ⟨c, hc⟩)
        obtain ⟨c, rfl⟩ := Finset.card_eq_one.mp hcard1
        have hcU : c ∈ fourDomain := hS.1 (by simp)
        simp only [fourDomain, mem_insert_iff, mem_singleton_iff] at hcU
        rcases hcU with rfl | rfl | rfl | rfl
        · obtain ⟨c', hc', hd⟩ := hS.2 (some 3) (by simp [fourDomain])
          simp at hc'; subst c'
          norm_num [usualDist, optionDist] at hd
          exact (not_lt_of_ge (h2.trans (by norm_num))) hd
        · obtain ⟨c', hc', hd⟩ := hS.2 (some 3) (by simp [fourDomain])
          simp at hc'; subst c'
          norm_num [usualDist, optionDist] at hd
          exact (not_lt_of_ge h2) hd
        · obtain ⟨c', hc', hd⟩ := hS.2 (some 0) (by simp [fourDomain])
          simp at hc'; subst c'
          norm_num [usualDist, optionDist] at hd
          exact (not_lt_of_ge h2) hd
        · obtain ⟨c', hc', hd⟩ := hS.2 (some 0) (by simp [fourDomain])
          simp at hc'; subst c'
          norm_num [usualDist, optionDist] at hd
          exact (not_lt_of_ge (h2.trans (by norm_num))) hd
    · rw [if_neg h2]
      have h2lt : 2 < ε := lt_of_not_ge h2
      apply le_antisymm
      · have hnet : InternalEpsilonNet usualDist ε fourDomain {some 1} := by
          constructor
          · simp [fourDomain]
          · intro x hx
            simp only [fourDomain, mem_insert_iff, mem_singleton_iff] at hx
            rcases hx with rfl | rfl | rfl | rfl
            all_goals refine ⟨some 1, by simp, ?_⟩
            · norm_num [usualDist, optionDist]; exact h1lt
            · simpa [usualDist, optionDist] using hε0
            · norm_num [usualDist, optionDist]; exact h1lt
            · norm_num [usualDist, optionDist]; exact h2lt
        simpa using covering_number_le_of_net hnet
      · exact one_le_covering_number_of_nonempty _ _ _ ⟨some 0, by simp [fourDomain]⟩

/-- `3/2` is not an internal centre of the four-point domain. -/
theorem three_halves_not_internal_center : some (3 / 2 : ℝ) ∉ fourDomain := by
  norm_num [fourDomain]

/-- The two operators on the four-point domain; both are `⊥` outside it. -/
noncomputable def reorderF : Operator RealBase none where
  func
    | none => none
    | some x => if x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 then some x else none
  preserves_bot := rfl

noncomputable def reorderG : Operator RealBase none where
  func
    | none => none
    | some x =>
      if x = 0 then some 0 else if x = 1 then some 3 else if x = 2 then some 1 else
        if x = 3 then some 2 else none
  preserves_bot := rfl

theorem reorder_images : reorderF.func '' fourDomain = fourDomain ∧ reorderG.func '' fourDomain = fourDomain := by
  constructor
  · ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      simp only [fourDomain, mem_insert_iff, mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> norm_num [reorderF, fourDomain]
    · intro hz
      simp only [fourDomain, mem_insert_iff, mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl | rfl
      · exact ⟨some 0, by simp [fourDomain], by norm_num [reorderF]⟩
      · exact ⟨some 1, by simp [fourDomain], by norm_num [reorderF]⟩
      · exact ⟨some 2, by simp [fourDomain], by norm_num [reorderF]⟩
      · exact ⟨some 3, by simp [fourDomain], by norm_num [reorderF]⟩
  · ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      simp only [fourDomain, mem_insert_iff, mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> norm_num [reorderG, fourDomain]
    · intro hz
      simp only [fourDomain, mem_insert_iff, mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl | rfl
      · exact ⟨some 0, by simp [fourDomain], by norm_num [reorderG]⟩
      · exact ⟨some 2, by simp [fourDomain], by norm_num [reorderG]⟩
      · exact ⟨some 3, by simp [fourDomain], by norm_num [reorderG]⟩
      · exact ⟨some 1, by simp [fourDomain], by norm_num [reorderG]⟩

/-- Both images have exactly the same covering numbers as the input. -/
theorem reorder_image_covering {ε : ENNReal} (hε0 : 0 < ε) (hεtop : ε < ⊤) :
    covering_number usualDist ε (reorderF.func '' fourDomain) = covering_number usualDist ε fourDomain ∧
      covering_number usualDist ε (reorderG.func '' fourDomain) = covering_number usualDist ε fourDomain := by
  rw [reorder_images.1, reorder_images.2]
  exact ⟨rfl, rfl⟩

/-- Both mapping entropy differences vanish at every finite positive precision. -/
theorem reorder_entropyDelta_zero {ε : ENNReal} (hε0 : 0 < ε) (hεtop : ε < ⊤) :
    entropyDelta (fun _ : Unit => usualDist) {()} {()} ε reorderF fourDomain = 0 ∧
      entropyDelta (fun _ : Unit => usualDist) {()} {()} ε reorderG fourDomain = 0 := by
  have hU : fourDomain.Nonempty := ⟨some 0, by simp [fourDomain]⟩
  have hfin : covering_number usualDist ε fourDomain < ⊤ := by
    rw [fourPoint_covering hε0 hεtop]
    split_ifs <;> norm_num
  have hent := metric_entropy_eq_coe_of_cover_finite hU hfin
  constructor
  · rw [entropyDelta, subfamily_metric_entropy_singleton, subfamily_metric_entropy_singleton,
      reorder_images.1, hent]
    exact EReal.sub_self (EReal.coe_ne_top _) (EReal.coe_ne_bot _)
  · rw [entropyDelta, subfamily_metric_entropy_singleton, subfamily_metric_entropy_singleton,
      reorder_images.2, hent]
    exact EReal.sub_self (EReal.coe_ne_top _) (EReal.coe_ne_bot _)

/-- The optimal scalar Lip constant of `f` is one, including necessity. -/
theorem reorderF_optimal_lip :
    (∀ x ∈ fourDomain, ∀ y ∈ fourDomain,
      usualDist (reorderF.func x) (reorderF.func y) ≤ ENNReal.ofReal 1 * usualDist x y) ∧
    ∀ L : ℝ, (∀ x ∈ fourDomain, ∀ y ∈ fourDomain,
      usualDist (reorderF.func x) (reorderF.func y) ≤ ENNReal.ofReal L * usualDist x y) → 1 ≤ L := by
  constructor
  · intro x hx y hy
    simp only [fourDomain, mem_insert_iff, mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      norm_num [reorderF, usualDist, optionDist]
  · intro L hL
    have h := hL (some 0) (by simp [fourDomain]) (some 1) (by simp [fourDomain])
    norm_num [reorderF, usualDist, optionDist] at h
    exact h

/-- The optimal scalar Lip constant of `g` is three, including necessity. -/
theorem reorderG_optimal_lip :
    (∀ x ∈ fourDomain, ∀ y ∈ fourDomain,
      usualDist (reorderG.func x) (reorderG.func y) ≤ ENNReal.ofReal 3 * usualDist x y) ∧
    ∀ L : ℝ, (∀ x ∈ fourDomain, ∀ y ∈ fourDomain,
      usualDist (reorderG.func x) (reorderG.func y) ≤ ENNReal.ofReal L * usualDist x y) → 3 ≤ L := by
  constructor
  · intro x hx y hy
    simp only [fourDomain, mem_insert_iff, mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      norm_num [reorderG, usualDist, optionDist, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
  · intro L hL
    have h := hL (some 0) (by simp [fourDomain]) (some 1) (by simp [fourDomain])
    norm_num [reorderG, usualDist, optionDist] at h
    exact h

/-- Exercise 3.5(iii-b): instantiate the general covering upper bound at
`ε = 7/4`; `f` gives the sharp value 2, while `g` gives the nonsharp bound 4. -/
theorem reorder_bounds_at_seven_quarters :
    covering_number usualDist (7 / 4 : ENNReal) (reorderF.func '' fourDomain) = 2 ∧
    covering_number usualDist ((7 / 4 : ENNReal) / 1) fourDomain = 2 ∧
    covering_number usualDist (7 / 4 : ENNReal) (reorderF.func '' fourDomain) ≤
      covering_number usualDist ((7 / 4 : ENNReal) / 1) fourDomain ∧
    covering_number usualDist (7 / 4 : ENNReal) (reorderG.func '' fourDomain) = 2 ∧
    covering_number usualDist ((7 / 4 : ENNReal) / 3) fourDomain = 4 ∧
    covering_number usualDist (7 / 4 : ENNReal) (reorderG.func '' fourDomain) ≤
      covering_number usualDist ((7 / 4 : ENNReal) / 3) fourDomain := by
  have hε0 : (0 : ENNReal) < 7 / 4 := ENNReal.div_pos (by simp) (by simp)
  have hεtop : (7 / 4 : ENNReal) < ⊤ := ENNReal.div_lt_top (by simp) (by simp)
  have hε1 : ¬ (7 / 4 : ENNReal) ≤ 1 := by
    intro h
    have h' := (ENNReal.div_le_iff (by simp) (by simp)).mp h
    norm_num at h'
  have hε2 : (7 / 4 : ENNReal) ≤ 2 := by
    apply (ENNReal.div_le_iff (by simp) (by simp)).mpr
    norm_num
  have hsmall : ((7 / 4 : ENNReal) / 3) ≤ 1 := by
    apply (ENNReal.div_le_iff (by simp) (by simp)).mpr
    apply (ENNReal.div_le_iff (by simp) (by simp)).mpr
    norm_num
  have hsmall0 : (0 : ENNReal) < (7 / 4 : ENNReal) / 3 := ENNReal.div_pos (by positivity) (by simp)
  have hsmalltop : ((7 / 4 : ENNReal) / 3) < ⊤ := ENNReal.div_lt_top (ne_of_lt hεtop) (by simp)
  have hN : covering_number usualDist (7 / 4 : ENNReal) fourDomain = 2 := by
    rw [fourPoint_covering hε0 hεtop, if_neg hε1, if_pos hε2]
  have hNsmall : covering_number usualDist ((7 / 4 : ENNReal) / 3) fourDomain = 4 := by
    rw [fourPoint_covering hsmall0 hsmalltop, if_pos hsmall]
  have hf := covering_number_image_le_of_scalar_lip (fun _ : Unit => usualDist) reorderF
    (i := ()) (j := ()) (L := 1) (ε := 7 / 4) zero_lt_one ENNReal.one_lt_top (by
      simpa using reorderF_optimal_lip.1)
  have hg := covering_number_image_le_of_scalar_lip (fun _ : Unit => usualDist) reorderG
    (i := ()) (j := ()) (L := 3) (ε := 7 / 4) (by norm_num) (by norm_num) (by
      simpa using reorderG_optimal_lip.1)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [reorder_images.1]; exact hN
  · simpa using hN
  · exact hf
  · rw [reorder_images.2]; exact hN
  · exact hNsmall
  · exact hg

end OET.Ch03
