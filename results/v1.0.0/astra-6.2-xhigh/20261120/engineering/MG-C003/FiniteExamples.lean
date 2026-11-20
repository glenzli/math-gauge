import RealExamples
open formal_oet.vol_01.ch_01_foundations formal_oet.vol_01.ch_02_operator_bounds
open Set
namespace C3
noncomputable section
open scoped Classical
variable {X I : Type} {b : X}

variable {p : D X} {U : Set X} {e : ENNReal}

theorem center_one {c : X} (hc : c ∈ U) (near : ∀ x ∈ U, p x c < e) : cov p e U = 1 := by
  have h : InternalEpsilonNet p e U {c} :=
    ⟨by simpa using hc, fun x hx => ⟨c,Finset.mem_singleton_self c,near x hx⟩⟩
  exact le_antisymm (by simpa using net_bound h) (one_le_covering_number_of_nonempty _ _ _ ⟨c,hc⟩)

theorem center_two {a b : X} (ha : a ∈ U) (hb : b ∈ U)
    (cover : ∀ x ∈ U, p x a < e ∨ p x b < e)
    (far : ∀ c ∈ U, ∃ x ∈ U, e ≤ p x c) : cov p e U = 2 := by
  have net : InternalEpsilonNet p e U {a,b} := by
    constructor
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hh
      · exact ha
      · exact (Finset.mem_singleton.mp hh) ▸ hb
    · intro x hx
      rcases cover x hx with h | h
      · exact ⟨a,by simp,h⟩
      · exact ⟨b,by simp,h⟩
  apply le_antisymm
  · exact (net_bound net).trans (by exact_mod_cast Finset.card_le_two)
  · refine le_iInf fun S => le_iInf fun hs => ?_
    obtain ⟨c,hc,_⟩ := hs.2 a ha
    obtain ⟨x,hx,hfar⟩ := far c (hs.1 hc)
    obtain ⟨z,hz,hh⟩ := hs.2 x hx
    have hn : z ≠ c := fun he => (he ▸ hh).not_ge hfar
    exact_mod_cast (show 2 ≤ S.card from Finset.one_lt_card.mpr ⟨z,hz,c,hc,hn⟩)

theorem isolated_cover {S : Finset X} (he : 0 < e) (self : ∀ x ∈ S, p x x = 0)
    (far : ∀ x ∈ S, ∀ y ∈ S, p x y < e → x = y) : cov p e (S : Set X) = S.card := by
  have net : InternalEpsilonNet p e (S : Set X) S :=
    ⟨Subset.rfl,fun x hx => ⟨x,hx,(self x hx).symm ▸ he⟩⟩
  apply le_antisymm (net_bound net)
  refine le_iInf fun T => le_iInf fun ht => ?_
  have h : S ⊆ T := by
    intro x hx
    obtain ⟨y,hy,hh⟩ := ht.2 x hx
    exact (far x hx y (ht.1 hy) hh).symm ▸ hy
  exact_mod_cast Finset.card_le_card h

theorem step_two {τ : ENNReal} (hτ : PosFin τ) : ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧
    ENNReal.ofReal (2*a) < τ ∧ {pt (-a),pt a} ⊆ area punct ∧
    cov (line id) τ {pt (-a),pt a} = 1 ∧
    cov (line id) (1/2) ((run step).func '' {pt (-a),pt a}) = 2 := by
  let a := min 1 (τ.toReal / 4)
  have ht := ENNReal.toReal_pos hτ.1.ne' hτ.2.ne
  have ha : 0 < a := lt_min (by norm_num) (by linarith)
  have ha' : a ≤ 1 := min_le_left _ _
  have hb : a ≤ τ.toReal / 4 := min_le_right _ _
  have hh : ENNReal.ofReal (2*a) < τ :=
    (ENNReal.ofReal_lt_iff_lt_toReal (by positivity) hτ.2.ne).mpr (by linarith)
  refine ⟨a,ha,ha',hh,?_,?_,?_⟩
  · simp only [Set.insert_subset_iff,Set.singleton_subset_iff,some_area]
    exact ⟨Or.inl ⟨by linarith,by linarith⟩,Or.inr ⟨ha,ha'⟩⟩
  · apply center_one (c := pt (-a)) (by simp)
    simp [pt, ← two_mul, sub_neg_eq_add, hτ.1, abs_of_nonneg (by positivity : 0 ≤ 2*a)]
    simpa using hh
  · have hI : (run step).func '' {pt (-a),pt a} = {pt 0,pt 1} := by
      simp [pt,step,neg_lt_zero.mpr ha,ha.not_gt,image_insert_eq]
    rw [hI]
    apply center_two (a := pt 0) (b := pt 1) (by simp) (by simp)
    · norm_num [pt]
    · norm_num [pt]

def affine := run (fun x : ℝ => 2*x-1)
def pair01 : Set (Option ℝ) := {pt 0,pt 1}
abbrev magnitude := line abs
theorem affine_values :
    affine.func (pt 0) = pt (-1) ∧ affine.func (pt 1) = pt 1 ∧
    (affine * affine).func (pt 0) = pt (-3) ∧ (affine * affine).func (pt 1) = pt 1 := by
  change _ ∧ _ ∧ affine.func (affine.func (pt 0)) = _ ∧ affine.func (affine.func (pt 1)) = _
  norm_num [affine,pt]

theorem affine_first : ExtendedPseudoMetric _ none magnitude ∧ pair01 ⊆ dom affine ∧
    fiber magnitude affine.func pair01 (affine.func (pt 0)) = pair01 ∧
    Const magnitude affine.func pair01 := by
  have h : Const magnitude affine.func pair01 := by norm_num [Const,pair01,affine,pt]
  refine ⟨line_metric _,?_,const_full h (by simp [pair01]),h⟩
  norm_num [Set.subset_def,pair01,dom,affine,pt]
  simp

theorem affine_second : pair01 ⊆ dom (affine * affine) ∧
    fiber magnitude (affine * affine).func pair01 ((affine * affine).func (pt 0)) = {pt 0} ∧
    Active magnitude (affine * affine).func pair01 := by
  obtain ⟨_,_,h0,h1⟩ := affine_values
  have hc : ¬ Const magnitude (affine * affine).func pair01 := by
    intro h
    have := h _ (show pt 0 ∈ pair01 by simp [pair01]) _ (show pt 1 ∈ pair01 by simp [pair01])
    norm_num [h0,h1,pt] at this
  have hi : ¬ Ident magnitude (affine * affine).func pair01 := by
    intro h
    have := h.2 _ (show pt 0 ∈ pair01 by simp [pair01])
    norm_num [h0,pt] at this
  refine ⟨?_,?_,hc,hi⟩
  · norm_num [Set.subset_def,pair01,dom,h0,h1]
    simp [pt]
  · ext x
    constructor
    · rintro ⟨hx,hz⟩
      rcases (show x = pt 0 ∨ x = pt 1 from hx) with rfl | rfl
      · rfl
      · norm_num [h0,h1,pt] at hz
    · rintro rfl
      exact ⟨by simp [pair01],(line_metric abs).dist_self _⟩

theorem constant_twice (F : Op (none : Option ℝ)) (c : ℝ) (h : ∀ x ∈ pair01, F.func x = pt c) :
    (∀ x ∈ pair01, (F*F).func x = F.func (pt c)) ∧
    (pair01 ⊆ dom (F*F) ↔ F.func (pt c) ≠ none) ∧
    (F.func (pt c) = none → Disjoint pair01 (dom (F*F))) ∧
    (F.func (pt c) ≠ none → ∀ z, fiber magnitude (F*F).func pair01 z = pair01 ∨
       fiber magnitude (F*F).func pair01 z = ∅) := by
  have hh (x) (hx : x ∈ pair01) := congrArg F.func (h x hx)
  refine ⟨hh,⟨fun hd => (hh _ (by simp [pair01] : pt 0 ∈ pair01)) ▸
    hd (by simp [pair01] : pt 0 ∈ pair01),fun hn x hx hbot => hn ((hh x hx).symm.trans hbot)⟩,?_,?_⟩
  · intro hn
    exact Set.disjoint_left.mpr fun x hx hd => hd ((hh x hx).trans hn)
  · intro _ z
    by_cases hz : magnitude (F.func (pt c)) z = 0
    · left
      exact Set.Subset.antisymm (fun _ hx => hx.1) (fun x hx => ⟨hx,(hh x hx).symm ▸ hz⟩)
    · right
      exact Set.eq_empty_iff_forall_notMem.mpr fun x hx => hz ((hh x hx.1) ▸ hx.2)

def transF := run (fun x : ℝ => x+1)
def fourMag : Set (Option ℝ) := {pt (-3),pt (-2),pt 0,pt 2}

theorem fiber_insert (p : D X) (f : X → X) (U : Set X) (a z : X) :
    fiber p f (insert a U) z =
      (if p (f a) z = 0 then insert a (fiber p f U z) else fiber p f U z) := by
  ext x
  by_cases h : p (f a) z = 0 <;> simp [fiber,h] <;> grind

theorem fiber_single (p : D X) (f : X → X) (a z : X) :
    fiber p f {a} z = (if p (f a) z = 0 then {a} else ∅) := by
  ext x
  by_cases h : p (f a) z = 0 <;> simp [fiber,h] <;> grind

theorem translate_blocks : ExtendedPseudoMetric _ none magnitude ∧ fourMag ⊆ dom transF ∧
    blocks magnitude id fourMag = {{pt (-3)},{pt (-2),pt 2},{pt 0}} ∧
    blocks magnitude transF.func fourMag = {{pt (-3)},{pt (-2),pt 0},{pt 2}} := by
  refine ⟨line_metric _,?_,?_,?_⟩
  · norm_num [fourMag,Set.subset_def,dom,transF,pt]
    simp
  · norm_num [blocks,fourMag,pt,fiber_insert,fiber_single,image_insert_eq,Set.insert_comm]
    ext z
    simp
    tauto
  · norm_num [blocks,fourMag,pt,transF,fiber_insert,fiber_single,image_insert_eq,Set.insert_comm]
    ext z
    simp [Set.pair_comm]

theorem threeHalves_gt_one : (1 : ENNReal) < 3/2 := by
  apply (scaled_lt (L := 2) ⟨by norm_num,by norm_num⟩).mpr
  norm_num

theorem threeHalves_le_two : (3/2 : ENNReal) ≤ 2 := by
  apply (ENNReal.div_le_iff (by norm_num) (by norm_num)).mpr
  norm_num

theorem translate_cover : cov magnitude (3/2) fourMag = 2 ∧
    cov magnitude (3/2) (transF.func '' fourMag) = 1 ∧
    ∃ h, delta magnitude magnitude transF.func fourMag (3/2) h = 1 := by
  have hi : cov magnitude (3/2) fourMag = 2 := by
    apply center_two (a := pt (-2)) (b := pt 0) (by simp [fourMag]) (by simp [fourMag])
    · norm_num [fourMag,pt,threeHalves_gt_one,threeHalves_le_two,threeHalves_le_two.trans (by norm_num : (2:ENNReal) ≤ 3)]
    · norm_num [fourMag,pt,threeHalves_gt_one,threeHalves_le_two,threeHalves_le_two.trans (by norm_num : (2:ENNReal) ≤ 3)]
  have ho : cov magnitude (3/2) (transF.func '' fourMag) = 1 := by
    apply center_one (c := pt (-2))
    · norm_num [fourMag,pt,transF,image_insert_eq,threeHalves_gt_one]
    · norm_num [fourMag,pt,transF,image_insert_eq,threeHalves_gt_one]
  refine ⟨hi,ho,Or.inr (ho ▸ ENNReal.one_lt_top),?_⟩
  change log2_ereal (cov magnitude (3/2) fourMag) - log2_ereal (cov magnitude (3/2) _) = 1
  rw [hi,ho]
  norm_num [log2_ereal,Real.logb_self_eq_one]

end
end C3
