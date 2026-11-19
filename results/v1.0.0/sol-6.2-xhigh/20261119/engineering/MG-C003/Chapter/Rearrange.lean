import Chapter.Step
import formal_oet.vol_01.ch_02_operator_bounds.single_channel

open formal_oet.vol_01.ch_01_foundations formal_oet.vol_01.ch_02_operator_bounds
open scoped ENNReal
namespace Chapter.Rearrange

def U : Set (Option ℝ) := {some 0,some 1,some 2,some 3}

noncomputable def f : Operator (Option ℝ) none := by
  classical
  exact ⟨fun x => if x ∈ U then x else none, by simp [U]⟩

noncomputable def g : Operator (Option ℝ) none :=
  ⟨fun x => if x = some 0 then some 0 else if x = some 1 then some 3 else
    if x = some 2 then some 1 else if x = some 3 then some 2 else none, by simp⟩

noncomputable def d : Unit → Option ℝ → Option ℝ → ℝ≥0∞ := fun _ => realDist

theorem gauge (i : Unit) : ExtendedPseudoMetric _ none (d i) := read_legal id

theorem mem_U (x : Option ℝ) : x ∈ U ↔ x = some 0 ∨ x = some 1 ∨ x = some 2 ∨ x = some 3 :=
  by simp [U]

theorem f_value {x : Option ℝ} (hx : x ∈ U) : f.func x = x := by
  simp [f,hx]

theorem g_values : g.func (some 0) = some 0 ∧ g.func (some 1) = some 3 ∧
    g.func (some 2) = some 1 ∧ g.func (some 3) = some 2 := by norm_num [g]

theorem outside {x : Option ℝ} (hx : x ∉ U) : f.func x = none ∧ g.func x = none := by
  have hn : x ≠ some 0 ∧ x ≠ some 1 ∧ x ≠ some 2 ∧ x ≠ some 3 := by
    simpa only [mem_U, not_or] using hx
  simp [f,g,hx,hn.1,hn.2.1,hn.2.2.1,hn.2.2.2]

theorem domains : U ⊆ dom f ∧ U ⊆ dom g := by
  constructor
  · intro x hx
    show f.func x ≠ none
    rw [f_value hx]
    rcases (mem_U x).mp hx with rfl | rfl | rfl | rfl <;> exact Option.some_ne_none _
  · intro x hx
    show g.func x ≠ none
    rcases (mem_U x).mp hx with rfl | rfl | rfl | rfl <;> simp [g]

theorem images : f.func '' U = U ∧ g.func '' U = U := by
  constructor
  · exact Set.image_congr (fun _ hx => f_value hx) |>.trans (Set.image_id U)
  · obtain ⟨h0,h1,h2,h3⟩ := g_values
    simp only [U, Set.image_insert_eq, Set.image_singleton, h0,h1,h2,h3]
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto

theorem separated {x y : Option ℝ} (hx : x ∈ U) (hy : y ∈ U) (h : x ≠ y) :
    1 ≤ realDist x y := by
  rcases (mem_U x).mp hx with rfl | rfl | rfl | rfl <;>
    rcases (mem_U y).mp hy with rfl | rfl | rfl | rfl <;>
    (norm_num at h <;> norm_num)

theorem at_most_three {x y : Option ℝ} (hx : x ∈ U) (hy : y ∈ U) :
    realDist x y ≤ 3 := by
  rcases (mem_U x).mp hx with rfl | rfl | rfl | rfl <;>
    rcases (mem_U y).mp hy with rfl | rfl | rfl | rfl <;>
    norm_num

noncomputable def centers : Finset (Option ℝ) := {some 0,some 1,some 2,some 3}

theorem centers_set : (↑centers : Set (Option ℝ)) = U := by
  classical
  ext x
  simp [centers,U]

theorem centers_card : centers.card = 4 := by
  classical
  norm_num [centers,Finset.card_insert_of_notMem]

theorem cover_small {r : ℝ≥0∞} (hr : 0 < r) (hr1 : r ≤ 1) :
    covering_number realDist r U = 4 := by
  classical
  apply le_antisymm
  · have hnet : InternalEpsilonNet realDist r U centers := by
      refine ⟨centers_set.le,fun x hx => ⟨x,?_ ,?_⟩⟩
      · exact show x ∈ (↑centers : Set (Option ℝ)) from centers_set.symm ▸ hx
      · rw [show realDist x x = 0 from (gauge ()).dist_self x]
        exact hr
    simpa [centers_card] using cover_le_card hnet
  · change ((4 : ℕ) : ℝ≥0∞) ≤ _
    apply card_lower_cover
    intro S hS
    rw [← centers_card]
    apply Finset.card_le_card
    intro x hx
    have hxu : x ∈ U := centers_set ▸ hx
    obtain ⟨c,hc,hxc⟩ := hS.2 x hxu
    have he : x = c := by
      by_contra hn
      exact (hxc.trans_le hr1).not_ge (separated hxu (hS.1 hc) hn)
    simpa [he] using hc

theorem cover_middle {r : ℝ≥0∞} (h1 : 1 < r) (h2 : r ≤ 2) :
    covering_number realDist r U = 2 := by
  apply le_antisymm
  · apply two_center_upper (some 0) (some 2) (by simp [U]) (by simp [U])
    intro x hx
    rcases (mem_U x).mp hx with rfl | rfl | rfl | rfl
    · left; simpa using zero_lt_one.trans h1
    · left; simpa using h1
    · right; simpa using zero_lt_one.trans h1
    · right; (convert h1 using 1; norm_num)
  · apply two_center_lower ⟨some 0,by simp [U]⟩
    intro c hc
    rcases (mem_U c).mp hc with rfl | rfl | rfl | rfl
    · exact ⟨some 3, by simp [U], h2.trans (by norm_num)⟩
    · exact ⟨some 3, by simp [U], h2.trans (by norm_num)⟩
    · exact ⟨some 0, by simp [U], h2.trans (by norm_num)⟩
    · exact ⟨some 0, by simp [U], h2.trans (by norm_num)⟩

theorem cover_large {r : ℝ≥0∞} (hr : 2 < r) :
    covering_number realDist r U = 1 := by
  apply cover_single_center
  refine ⟨some 1, by simp [U],?_⟩
  intro x hx
  apply lt_of_le_of_lt _ hr
  rcases (mem_U x).mp hx with rfl | rfl | rfl | rfl <;> norm_num

theorem cover_all {r : ℝ≥0∞} (hr : FinitePositive r) :
    covering_number realDist r U = if r ≤ 1 then 4 else if r ≤ 2 then 2 else 1 := by
  split
  · exact cover_small hr.1 (by assumption)
  · split
    · exact cover_middle (lt_of_not_ge (by assumption)) (by assumption)
    · exact cover_large (lt_of_not_ge (by assumption))

theorem excluded_center : some (3/2 : ℝ) ∉ U ∧
    ¬ InternalEpsilonNet realDist (ENNReal.ofReal (7/4)) U {some (3/2 : ℝ)} := by
  have h : some (3/2 : ℝ) ∉ U := by norm_num [U]
  exact ⟨h, fun H => h (H.1 (Finset.mem_singleton_self _))⟩

theorem image_statistics {r : ℝ≥0∞} (hr : FinitePositive r) :
    (∀ h : Operator (Option ℝ) none, (h = f ∨ h = g) →
      covering_number realDist r (h.func '' U) = covering_number realDist r U ∧
      ∃ hg : GapDefined h realDist realDist U r, entropyGap h realDist realDist U r hg = 0) := by
  intro h hh
  have hI : h.func '' U = U := hh.elim (fun e => e.symm ▸ images.1) (fun e => e.symm ▸ images.2)
  have hn : U.Nonempty := ⟨some 0,by simp [U]⟩
  have hf : covering_number realDist r U < ⊤ := by
    exact cover_finite (centers_set ▸ centers.finite_toSet) (fun x _ => (gauge ()).dist_self x) hr.1
  have he : covering_number realDist r (h.func '' U) = covering_number realDist r U :=
    congrArg (covering_number realDist r) hI
  exact ⟨he,Or.inl hf,equal_cover_gap hn he.symm (Or.inl hf)⟩

theorem f_optimal (L : ℝ≥0∞) : HasScalarLipBound d f U () () L ↔ 1 ≤ L := by
  constructor
  · intro h
    have he := h.2 (some 0) (by simp [U]) (some 1) (by simp [U])
    norm_num [d,f,U] at he
    exact he
  · intro h
    refine ⟨domains.1,fun x hx y hy => ?_⟩
    rw [f_value hx, f_value hy]
    calc
      d () x y = 1 * d () x y := (one_mul _).symm
      _ ≤ L * d () x y := mul_le_mul_left h _

theorem g_optimal (L : ℝ≥0∞) : HasScalarLipBound d g U () () L ↔ 3 ≤ L := by
  constructor
  · intro h
    have he := h.2 (some 0) (by simp [U]) (some 1) (by simp [U])
    norm_num [d,g] at he
    exact he
  · intro h
    refine ⟨domains.2,fun x hx y hy => ?_⟩
    by_cases he : x = y
    · subst y
      simp [(gauge ()).dist_self]
    · have hx' : g.func x ∈ U := images.2 ▸ (show g.func x ∈ g.func '' U from ⟨x,hx,rfl⟩)
      have hy' : g.func y ∈ U := images.2 ▸ (show g.func y ∈ g.func '' U from ⟨y,hy,rfl⟩)
      calc
        _ ≤ (3 : ℝ≥0∞) := at_most_three hx' hy'
        _ = 3 * 1 := by simp
        _ ≤ L * d () x y := mul_le_mul' h (separated hx hy he)

theorem bounds_at_seven_fourths :
    let r := ENNReal.ofReal (7/4)
    covering_number realDist r (f.func '' U) = 2 ∧
      covering_number realDist r (g.func '' U) = 2 ∧
      covering_number realDist r (f.func '' U) ≤ covering_number realDist (r/1) U ∧
      covering_number realDist (r/1) U = 2 ∧
      covering_number realDist r (g.func '' U) ≤ covering_number realDist (r/3) U ∧
      covering_number realDist (r/3) U = 4 := by
  dsimp
  let r := ENNReal.ofReal (7/4)
  have hr : covering_number realDist r U = 2 := by
    apply cover_middle
    · exact (ENNReal.lt_ofReal_iff_toReal_lt (by simp)).mpr (by norm_num)
    · exact ENNReal.ofReal_le_ofNat.mpr (by norm_num)
  have hp1 : FinitePositive (1 : ℝ≥0∞) := ⟨by norm_num,by simp⟩
  have hp3 : FinitePositive (3 : ℝ≥0∞) := ⟨by norm_num,by simp⟩
  have hf := lip_cover (r := r) hp1 ((f_optimal 1).mpr le_rfl).2
  have hg := lip_cover (r := r) hp3 ((g_optimal 3).mpr le_rfl).2
  refine ⟨images.1.symm ▸ hr, images.2.symm ▸ hr, hf, by simpa using hr, hg,?_⟩
  apply cover_small
  · exact ENNReal.div_pos (by simp) hp3.2.ne
  · rw [show (3 : ℝ≥0∞) = ENNReal.ofReal 3 by norm_num, ← ENNReal.ofReal_div_of_pos (by norm_num)]
    exact ENNReal.ofReal_le_one.mpr (by norm_num [r])

end Chapter.Rearrange
