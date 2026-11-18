import MG03.Models

namespace MG03

open Set formal_oet.vol_01.ch_01_foundations

theorem reading_lt_ofReal_iff (q : ℝ → ℝ) (x y r : ℝ) :
    realReadingDist q (some x) (some y) < ENNReal.ofReal r ↔ |q x - q y| < r :=
  ENNReal.ofReal_lt_ofReal_iff_of_nonneg (abs_nonneg _)

theorem reading_ofReal_le_iff (q : ℝ → ℝ) (x y r : ℝ) :
    ENNReal.ofReal r ≤ realReadingDist q (some x) (some y) ↔ r ≤ |q x - q y| :=
  ENNReal.ofReal_le_ofReal_iff (abs_nonneg _)

theorem fiber_eq_of_membership {X : Type} {bot : X} {e : X → X → ENNReal}
    {f : Operator X bot} {U V : Set X} {y : X} (hVU : V ⊆ U)
    (h : ∀ x ∈ U, e (f.func x) y = 0 ↔ x ∈ V) : fiberAt e f U y = V :=
  Subset.antisymm (fun x hx => (h x hx.1).mp hx.2)
    (fun x hx => ⟨hVU hx, (h x (hVU hx)).mpr hx⟩)

def affineOp : Operator RealWithBot none := realOp fun x => 2 * x - 1
def affineU : Set RealWithBot := {some 0, some 1}

theorem affine_values :
    affineOp.func (some 0) = some (-1) ∧ affineOp.func (some 1) = some 1 ∧
    (affineOp * affineOp).func (some 0) = some (-3) ∧
    (affineOp * affineOp).func (some 1) = some 1 := by
  norm_num [affineOp]

theorem affine_fiber :
    (∀ i, ExtendedPseudoMetric RealWithBot none (absGauge i)) ∧
    affineU ⊆ dom affineOp ∧
    fiberAt absDist affineOp affineU (affineOp.func (some 0)) = affineU ∧
    PUnit.unit ∈ constPart absGauge affineOp affineU ∧
    PUnit.unit ∉ idPart absGauge affineOp affineU ∧
    PUnit.unit ∉ actPart absGauge affineOp affineU := by
  have hc : PUnit.unit ∈ constPart absGauge affineOp affineU := by
    intro x hx y hy
    simp only [affineU, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
      norm_num [absGauge, affine_values.1, affine_values.2.1, realReadingDist_zero_iff]
  have h0 : some 0 ∈ affineU := by simp [affineU]
  refine ⟨fun _ => realReadingDist_gauge abs, ?_, ?_, hc, fun h => h.1 hc, fun h => h (Or.inl hc)⟩
  · intro x hx
    simp only [affineU, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;> simp [dom, affineOp]
  · exact Subset.antisymm (fun _ hx => hx.1) (fun x hx => ⟨hx, hc x hx _ h0⟩)

theorem affine_square_fiber :
    affineU ⊆ dom (affineOp * affineOp) ∧
    fiberAt absDist (affineOp * affineOp) affineU ((affineOp * affineOp).func (some 0)) = {some 0} ∧
    PUnit.unit ∉ constPart absGauge (affineOp * affineOp) affineU ∧
    PUnit.unit ∉ idPart absGauge (affineOp * affineOp) affineU ∧
    PUnit.unit ∈ actPart absGauge (affineOp * affineOp) affineU := by
  obtain ⟨_, _, ha, hb⟩ := affine_values
  have h0 : some 0 ∈ affineU := by simp [affineU]
  have h1 : some 1 ∈ affineU := by simp [affineU]
  have hconst : PUnit.unit ∉ constPart absGauge (affineOp * affineOp) affineU := by
    intro h
    have hz := h _ h0 _ h1
    change absDist ((affineOp * affineOp).func (some 0)) ((affineOp * affineOp).func (some 1)) = 0 at hz
    rw [ha, hb] at hz
    norm_num [realReadingDist_zero_iff] at hz
  have hid : PUnit.unit ∉ idPart absGauge (affineOp * affineOp) affineU := by
    intro h
    have hz := h.2 _ h0
    change absDist ((affineOp * affineOp).func (some 0)) (some 0) = 0 at hz
    rw [ha] at hz
    norm_num [realReadingDist_zero_iff] at hz
  refine ⟨?_, ?_, hconst, hid, fun h => h.elim hconst hid⟩
  · intro x hx
    change (affineOp * affineOp).func x ≠ none
    simp only [affineU, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;> simp [ha, hb]
  · apply fiber_eq_of_membership (Set.singleton_subset_iff.mpr h0)
    intro x hx
    simp only [affineU, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;> norm_num [ha, hb, realReadingDist_zero_iff]

theorem constant_square (f : Operator RealWithBot none) (a : ℝ)
    (h : ∀ x ∈ affineU, f.func x = some a) :
    (∀ x ∈ affineU, (f * f).func x = f.func (some a)) ∧
    (affineU ⊆ dom (f * f) ↔ f.func (some a) ≠ none) ∧
    (f.func (some a) = none → affineU ∩ dom (f * f) = ∅) ∧
    (f.func (some a) ≠ none → fiberAt absDist (f * f) affineU (f.func (some a)) = affineU) := by
  have hf (x : RealWithBot) (hx : x ∈ affineU) : (f * f).func x = f.func (some a) := by
    rw [mul_func, h x hx]
  have h0 : some 0 ∈ affineU := by simp [affineU]
  refine ⟨hf, ?_, ?_, ?_⟩
  · exact ⟨fun hdom hn => hdom h0 ((hf _ h0).trans hn),
      fun hn x hx hz => hn ((hf x hx).symm.trans hz)⟩
  · intro hn
    exact Set.eq_empty_iff_forall_notMem.mpr fun x hx => hx.2 ((hf x hx.1).trans hn)
  · intro _
    exact Subset.antisymm (fun _ hx => hx.1) (fun x hx =>
      ⟨hx, (congrArg (fun t => absDist t (f.func (some a))) (hf x hx)).trans
        ((realReadingDist_gauge abs).dist_self _)⟩)

def shiftOp : Operator RealWithBot none := realOp fun x => x + 1
def shiftU : Set RealWithBot := {some (-3), some (-2), some 0, some 2}
def shiftImage : Set RealWithBot := {some (-2), some (-1), some 1, some 3}

theorem shift_image : shiftOp.func '' shiftU = shiftImage := by
  norm_num [shiftOp, shiftU, shiftImage, Set.image_insert_eq, Set.image_singleton]

theorem shift_valid :
    (∀ i, ExtendedPseudoMetric RealWithBot none (absGauge i)) ∧ shiftU.Nonempty ∧
      shiftU ⊆ dom (1 : Operator RealWithBot none) ∩ dom shiftOp := by
  refine ⟨fun _ => realReadingDist_gauge abs, by simp [shiftU], ?_⟩
  intro x hx
  simp only [shiftU, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> simp [dom, shiftOp]

theorem shift_id_table :
    let f : Operator RealWithBot none := 1
    fiberAt absDist f shiftU (some (-3)) = {some (-3)} ∧
    fiberAt absDist f shiftU (some (-2)) = {some (-2), some 2} ∧
    fiberAt absDist f shiftU (some 0) = {some 0} ∧
    fiberAt absDist f shiftU (some 2) = {some (-2), some 2} := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply fiber_eq_of_membership (by simp [shiftU, Set.pair_subset_iff])
  all_goals
    intro x hx
    simp only [shiftU, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> norm_num [realReadingDist_zero_iff]

theorem shift_table :
    fiberAt absDist shiftOp shiftU (some (-2)) = {some (-3)} ∧
    fiberAt absDist shiftOp shiftU (some (-1)) = {some (-2), some 0} ∧
    fiberAt absDist shiftOp shiftU (some 1) = {some (-2), some 0} ∧
    fiberAt absDist shiftOp shiftU (some 3) = {some 2} := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply fiber_eq_of_membership (by simp [shiftU, Set.pair_subset_iff])
  all_goals
    intro x hx
    simp only [shiftU, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> norm_num [realReadingDist_zero_iff, shiftOp]

theorem shift_partitions :
    fiberBlocks absDist (1 : Operator RealWithBot none) shiftU =
      {{some (-3)}, {some (-2), some 2}, {some 0}} ∧
    fiberBlocks absDist shiftOp shiftU = {{some (-3)}, {some (-2), some 0}, {some 2}} := by
  obtain ⟨ha, hb, hc, hd⟩ := shift_id_table
  obtain ⟨he, hf, hg, hh⟩ := shift_table
  constructor
  · change (fun y => fiberAt absDist (1 : Operator RealWithBot none) shiftU y) '' (id '' shiftU) = _
    rw [Set.image_id]
    rw [show shiftU = {some (-3), some (-2), some 0, some 2} from rfl,
      Set.image_insert_eq, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]
    change ({fiberAt absDist (1 : Operator RealWithBot none) shiftU (some (-3)),
      fiberAt absDist (1 : Operator RealWithBot none) shiftU (some (-2)),
      fiberAt absDist (1 : Operator RealWithBot none) shiftU (some 0),
      fiberAt absDist (1 : Operator RealWithBot none) shiftU (some 2)} : Set (Set RealWithBot)) = _
    rw [ha, hb, hc, hd]
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  · unfold fiberBlocks
    rw [shift_image, shiftImage, Set.image_insert_eq, Set.image_insert_eq, Set.image_insert_eq,
      Set.image_singleton, he, hf, hg, hh]
    simp

noncomputable def shiftEps : ENNReal := ENNReal.ofReal (3 / 2)

theorem shift_cover_in : covering_number absDist shiftEps shiftU = 2 := by
  classical
  apply le_antisymm
  · let S : Finset RealWithBot := {some 0, some (-2)}
    have hn : InternalEpsilonNet absDist shiftEps shiftU S := by
      refine ⟨by simp [S, shiftU, Set.pair_subset_iff], ?_⟩
      intro x hx
      simp only [shiftU, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact ⟨some (-2), by simp [S], by norm_num [shiftEps, reading_lt_ofReal_iff]⟩
      · exact ⟨some (-2), by simp [S], by norm_num [shiftEps, reading_lt_ofReal_iff]⟩
      · exact ⟨some 0, by simp [S], by norm_num [shiftEps, reading_lt_ofReal_iff]⟩
      · exact ⟨some (-2), by simp [S], by norm_num [shiftEps, reading_lt_ofReal_iff]⟩
    have hc : S.card = 2 := by norm_num [S]
    simpa [hc] using cover_le_card hn
  · apply two_le_cover shift_valid.2.1
    intro c hc
    simp only [shiftU, Set.mem_insert_iff, Set.mem_singleton_iff] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact ⟨some 0, by simp [shiftU], by norm_num [shiftEps, reading_ofReal_le_iff]⟩
    · exact ⟨some 0, by simp [shiftU], by norm_num [shiftEps, reading_ofReal_le_iff]⟩
    · exact ⟨some 2, by simp [shiftU], by norm_num [shiftEps, reading_ofReal_le_iff]⟩
    · exact ⟨some 0, by simp [shiftU], by norm_num [shiftEps, reading_ofReal_le_iff]⟩

theorem shift_cover_out : covering_number absDist shiftEps (shiftOp.func '' shiftU) = 1 := by
  classical
  rw [shift_image]
  have hc : (some (-2) : RealWithBot) ∈ shiftImage := by simp [shiftImage]
  have hn : InternalEpsilonNet absDist shiftEps shiftImage {some (-2)} := by
    refine ⟨by simpa using hc, ?_⟩
    intro x hx
    refine ⟨some (-2), by simp, ?_⟩
    simp only [shiftImage, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> norm_num [shiftEps, reading_lt_ofReal_iff]
  exact le_antisymm (by simpa using cover_le_card hn)
    (one_le_covering_number_of_nonempty _ _ _ ⟨_, hc⟩)

theorem shiftEps_finite : FiniteRadius shiftEps :=
  ⟨by norm_num [shiftEps, ENNReal.ofReal_pos], ENNReal.ofReal_lt_top⟩

theorem shift_entropy :
    ∃ h : EntropyAdmissible absDist absDist shiftOp shiftU shiftEps,
      entropyDifference absDist absDist shiftOp shiftU shiftEps shift_valid.2.1
        (fun _ hx => (shift_valid.2.2 hx).2) shiftEps_finite h = 1 := by
  have hi : covering_number absDist shiftEps shiftU < ⊤ := by simp [shift_cover_in]
  refine ⟨Or.inl hi, ?_⟩
  rw [entropyDifference]
  have hlog : Real.logb 2 2 = 1 := Real.logb_self_eq_one (by norm_num)
  norm_num [metric_entropy, log2_ereal, shift_cover_in, shift_cover_out, hlog]

end MG03
