import MG03.Entropy

namespace MG03

open Set formal_oet.vol_01.ch_01_foundations

def extend {T : Type} (e : T → T → ENNReal) : Option T → Option T → ENNReal
  | none, none => 0
  | some x, some y => e x y
  | _, _ => ⊤

theorem extend_gauge {T : Type} [Nonempty T] (e : T → T → ENNReal)
    (h₀ : ∀ x, e x x = 0) (hs : ∀ x y, e x y = e y x)
    (ht : ∀ x y z, e x z ≤ e x y + e y z) :
    ExtendedPseudoMetric (Option T) none (extend e) := by
  obtain ⟨t⟩ := ‹Nonempty T›
  refine ⟨⟨some t, by simp⟩, ?_, ?_, ?_, ?_⟩
  · intro x
    cases x <;> simp [extend, h₀]
  · intro x y
    cases x <;> cases y <;> simp [extend, hs]
  · intro x y z
    cases x <;> cases y <;> cases z <;> simp [extend, ht]
  · intro x hx
    cases x <;> simp_all [extend]

def partialOp {T : Type} (p : T → Option T) : Operator (Option T) none :=
  ⟨fun x => x.bind p, rfl⟩

def realOp {T : Type} (p : T → T) : Operator (Option T) none :=
  partialOp (some ∘ p)

@[simp] theorem realOp_some {T : Type} (p : T → T) (x : T) :
    (realOp p).func (some x) = some (p x) := rfl

theorem realOp_dom {T : Type} (p : T → T) : dom (realOp p) = {x | x ≠ none} := by
  ext x
  cases x <;> simp [dom, realOp, partialOp]

section FiniteExamples

variable {T S : Type} [DecidableEq S]

def readingDiscrete (q : T → S) (c : ENNReal) (x y : T) : ENNReal :=
  if q x = q y then 0 else c

theorem readingDiscrete_gauge [Nonempty T] (q : T → S) (c : ENNReal) :
    ExtendedPseudoMetric (Option T) none (extend (readingDiscrete q c)) := by
  apply extend_gauge
  · simp [readingDiscrete]
  · intro x y
    simp [readingDiscrete, eq_comm]
  · intro x y z
    by_cases h : q x = q y
    · simp [readingDiscrete, h]
    · exact (by
        simp only [readingDiscrete, if_neg h]
        split <;> simp)

end FiniteExamples

noncomputable def twoGauge (c : ENNReal) : PUnit.{1} → Option Bool → Option Bool → ENNReal :=
  fun _ => extend (readingDiscrete id c)

def twoSet : Set (Option Bool) := {some false, some true}

def swapOp : Operator (Option Bool) none := realOp Bool.not

theorem twoSet_mem_iff (x : Option Bool) : x ∈ twoSet ↔ x ≠ none := by
  cases x with
  | none => simp [twoSet]
  | some b => cases b <;> simp [twoSet]

theorem swap_image : swapOp.func '' twoSet = twoSet := by
  simp [twoSet, Set.image_pair, swapOp, Set.pair_comm]

theorem swap_square : swapOp * swapOp = 1 := by
  apply Operator.ext
  funext x
  cases x with
  | none => rfl
  | some b => cases b <;> rfl

theorem swap_acts :
    actPart (twoGauge 1) swapOp twoSet = Set.univ ∧
      idPart (twoGauge 1) swapOp twoSet = ∅ := by
  have ha : some false ∈ twoSet := by simp [twoSet]
  have hb : some true ∈ twoSet := by simp [twoSet]
  have h (i : PUnit) : i ∈ actPart (twoGauge 1) swapOp twoSet := by
    intro hc
    rcases hc with hc | hi
    · have he := hc _ ha _ hb
      simp [twoGauge, readingDiscrete, extend, swapOp] at he
    · have he := hi.2 _ ha
      simp [twoGauge, readingDiscrete, extend, swapOp] at he
  exact ⟨Set.eq_univ_of_forall h, Set.eq_empty_iff_forall_notMem.mpr fun i hi => h i (Or.inr hi)⟩

theorem swap_comp_types :
    idPart (twoGauge 1) (swapOp * swapOp) twoSet = Set.univ ∧
      actPart (twoGauge 1) (swapOp * swapOp) twoSet = ∅ := by
  rw [swap_square]
  have ha : some false ∈ twoSet := by simp [twoSet]
  have hb : some true ∈ twoSet := by simp [twoSet]
  have h (i : PUnit) : i ∈ idPart (twoGauge 1) (1 : Operator (Option Bool) none) twoSet := by
    refine ⟨?_, fun x _ => (readingDiscrete_gauge id 1).dist_self x⟩
    intro hc
    have he := hc _ ha _ hb
    simp [twoGauge, readingDiscrete, extend] at he
  exact ⟨Set.eq_univ_of_forall h, Set.eq_empty_iff_forall_notMem.mpr fun i hi => hi (Or.inr (h i))⟩

theorem swap_strict :
    (∀ i, ExtendedPseudoMetric (Option Bool) none (twoGauge 1 i)) ∧
    twoSet ⊆ dom (swapOp * swapOp) ∧ swapOp.func '' twoSet = twoSet ∧
    actPart (twoGauge 1) swapOp twoSet = {PUnit.unit} ∧
    idPart (twoGauge 1) swapOp twoSet = ∅ ∧
    idPart (twoGauge 1) (swapOp * swapOp) twoSet = {PUnit.unit} ∧
    actPart (twoGauge 1) (swapOp * swapOp) twoSet = ∅ ∧
    actPart (twoGauge 1) (swapOp * swapOp) twoSet ⊂
      actPart (twoGauge 1) swapOp twoSet ∪ actPart (twoGauge 1) swapOp (swapOp.func '' twoSet) ∧
    idPart (twoGauge 1) swapOp twoSet ∩ idPart (twoGauge 1) swapOp (swapOp.func '' twoSet) ⊂
      idPart (twoGauge 1) (swapOp * swapOp) twoSet := by
  have hd (i : PUnit) : ExtendedPseudoMetric (Option Bool) none (twoGauge 1 i) :=
    readingDiscrete_gauge id 1
  have hu : twoSet ⊆ dom (swapOp * swapOp) := fun x hx =>
    (twoSet_mem_iff x).mp hx ∘ (congrArg (fun p : Operator (Option Bool) none => p.func x)
      swap_square).symm.trans
  have hsingle : (Set.univ : Set PUnit) = {PUnit.unit} := by ext ⟨⟩; simp
  refine ⟨hd, hu, swap_image, swap_acts.1.trans hsingle, swap_acts.2,
    swap_comp_types.1.trans hsingle, swap_comp_types.2, ?_, ?_⟩
  · rw [swap_image, swap_acts.1, swap_comp_types.2]
    simp
  · rw [swap_image, swap_acts.2, swap_comp_types.1]
    simp

inductive Six where
  | a | b | p | q | r | s
  deriving DecidableEq, Inhabited

def sixReading (i : Bool) (x : Six) : Six :=
  if i = false ∧ x = Six.q then Six.p else x

noncomputable def sevenGauge (i : Bool) : Option Six → Option Six → ENNReal :=
  extend (readingDiscrete (sixReading i) 1)

def sevenU : Set (Option Six) := {some Six.a, some Six.b}

def sevenInner : Operator (Option Six) none :=
  partialOp fun x => match x with
    | .a => some .p
    | .b => some .q
    | _ => none

def sevenOuter : Operator (Option Six) none :=
  partialOp fun x => match x with
    | .p => some .r
    | .q => some .s
    | _ => none

theorem seven_result :
    (∀ i, ExtendedPseudoMetric (Option Six) none (sevenGauge i)) ∧
    sevenU ⊆ dom (sevenOuter * sevenInner) ∧
    sevenInner.func '' sevenU = {some Six.p, some Six.q} ∧
    false ∈ constPart sevenGauge sevenInner sevenU ∧
    false ∉ constPart sevenGauge (sevenOuter * sevenInner) sevenU ∧
    sevenGauge true (some Six.p) (some Six.q) = 1 ∧
    sevenGauge false (some Six.r) (some Six.s) = 1 := by
  have ha : some Six.a ∈ sevenU := by simp [sevenU]
  have hb : some Six.b ∈ sevenU := by simp [sevenU]
  refine ⟨fun i => readingDiscrete_gauge (sixReading i) 1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    simp only [sevenU, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact show some Six.r ≠ none from Option.some_ne_none _
    · exact show some Six.s ≠ none from Option.some_ne_none _
  · rw [sevenU, Set.image_pair]
    rfl
  · intro x hx y hy
    simp only [sevenU, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rfl
  · intro h
    have he : (1 : ENNReal) = 0 := h _ ha _ hb
    exact one_ne_zero he
  · rfl
  · rfl

noncomputable def infiniteInputGauge {I : Type} [DecidableEq I] (i k : I) :
    Option Bool → Option Bool → ENNReal :=
  extend (readingDiscrete id (if k = i then ⊤ else 1))

theorem infiniteInput_result {I : Type} [DecidableEq I] (i j : I) :
    (∀ k, ExtendedPseudoMetric (Option Bool) none (infiniteInputGauge i k)) ∧
    twoSet.Nonempty ∧ twoSet ⊆ dom (1 : Operator (Option Bool) none) ∧
    infiniteInputGauge i i (some false) (some true) = ⊤ ∧
    (i = j → infiniteInputGauge i j (some false) (some true) = ⊤) ∧
    (i ≠ j → infiniteInputGauge i j (some false) (some true) = 1) ∧
    (∀ y ∈ twoSet, radius (infiniteInputGauge i i) (infiniteInputGauge i j)
      (1 : Operator (Option Bool) none) twoSet y = ⊤) ∧
    nullMatrix (infiniteInputGauge i) (1 : Operator (Option Bool) none) twoSet j i = ⊤ ∧
    j ∉ constPart (infiniteInputGauge i) (1 : Operator (Option Bool) none) twoSet := by
  have ha : some false ∈ twoSet := by simp [twoSet]
  have hb : some true ∈ twoSet := by simp [twoSet]
  have hg (k : I) : ExtendedPseudoMetric (Option Bool) none (infiniteInputGauge i k) :=
    readingDiscrete_gauge id _
  have heq : infiniteInputGauge i i (some false) (some true) = ⊤ := by
    simp [infiniteInputGauge, readingDiscrete, extend]
  have hpoint : ∀ y ∈ twoSet, radius (infiniteInputGauge i i) (infiniteInputGauge i j)
      (1 : Operator (Option Bool) none) twoSet y = ⊤ := by
    intro y hy
    apply top_unique (le_radius_iff.mpr ?_)
    intro x hx hxy
    simp only [twoSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact (hg j).dist_self _
    · exact ((not_lt_of_ge heq.ge) hxy).elim
    · rw [(hg i).symm, heq] at hxy
      exact (lt_irrefl _ hxy).elim
    · exact (hg j).dist_self _
  refine ⟨hg, ⟨_, ha⟩, fun x hx => (twoSet_mem_iff x).mp hx, heq, ?_, ?_, hpoint, ?_, ?_⟩
  · rintro rfl
    exact heq
  · intro h
    simp [infiniteInputGauge, readingDiscrete, extend, Ne.symm h]
  · exact top_unique (le_iInf fun y : twoSet => (hpoint y y.2).ge)
  · intro hc
    have h := hc _ ha _ hb
    simp only [one_func, infiniteInputGauge, extend, readingDiscrete, id,
      Bool.false_eq_true, if_false] at h
    split at h <;> simp_all

abbrev RealWithBot := Option ℝ

noncomputable def realReadingDist (q : ℝ → ℝ) : RealWithBot → RealWithBot → ENNReal :=
  extend fun x y => ENNReal.ofReal |q x - q y|

@[simp] theorem realReadingDist_some (q : ℝ → ℝ) (x y : ℝ) :
    realReadingDist q (some x) (some y) = ENNReal.ofReal |q x - q y| := rfl

theorem realReadingDist_zero_iff (q : ℝ → ℝ) (x y : ℝ) :
    realReadingDist q (some x) (some y) = 0 ↔ q x = q y := by
  simp [ENNReal.ofReal_eq_zero, abs_nonpos_iff, sub_eq_zero]

theorem realReadingDist_gauge (q : ℝ → ℝ) :
    ExtendedPseudoMetric RealWithBot none (realReadingDist q) := by
  apply extend_gauge
  · simp
  · intro x y
    rw [abs_sub_comm]
  · intro x y z
    rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (abs_sub_le _ _ _)

noncomputable abbrev realDist := realReadingDist id
noncomputable abbrev absDist := realReadingDist abs

noncomputable def realGauge : PUnit.{1} → RealWithBot → RealWithBot → ENNReal := fun _ => realDist
noncomputable def absGauge : PUnit.{1} → RealWithBot → RealWithBot → ENNReal := fun _ => absDist

def realSet (S : Set ℝ) : Set RealWithBot := some '' S

@[simp] theorem some_mem_realSet {S : Set ℝ} {x : ℝ} : some x ∈ realSet S ↔ x ∈ S := by
  simp [realSet]

theorem realSet_dom (S : Set ℝ) (p : ℝ → ℝ) : realSet S ⊆ dom (realOp p) := by
  rintro _ ⟨x, _, rfl⟩
  simp [dom]

theorem realSet_nonempty {S : Set ℝ} (h : S.Nonempty) : (realSet S).Nonempty := h.image _

theorem diameter_pair {T : Type} {bot : T} {e : T → T → ENNReal}
    (he : ExtendedPseudoMetric T bot e) (x y : T) :
    diameter e {x, y} = e x y := by
  apply le_antisymm
  · apply diameter_le
    intro a ha b hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp [ha, hb, he.dist_self, he.symm y x]
  · exact le_diameter (by simp) (by simp)

theorem diameter_singleton {T : Type} {bot : T} {e : T → T → ENNReal}
    (he : ExtendedPseudoMetric T bot e) (x : T) : diameter e {x} = 0 := by
  apply le_antisymm _ (zero_le _)
  apply diameter_le
  simpa using he.dist_self x

theorem scale_counterexample :
    let A : Set RealWithBot := {some 0, some 1}
    let B : Set RealWithBot := {some 0}
    let t := ENNReal.ofReal (1 / 2)
    B.Nonempty ∧ B ⊆ A ∧ A ⊆ dom (1 : Operator RealWithBot none) ∧ FiniteRadius t ∧
      (diameterScale realGauge).value PUnit.unit ⟨B, ⟨some 0, rfl⟩⟩ = 0 ∧
      (diameterScale realGauge).value PUnit.unit ⟨A, ⟨some 0, Or.inl rfl⟩⟩ = 1 ∧
      diameter realDist B < t ∧ t ≤ diameter realDist A := by
  have h₁ : diameter realDist {some (0 : ℝ), some 1} = 1 := by
    rw [diameter_pair (realReadingDist_gauge id)]
    norm_num
  have h₀ := diameter_singleton (realReadingDist_gauge id) (some 0)
  dsimp [diameterScale, realGauge]
  refine ⟨by simp, by simp, ?_, ⟨by norm_num [ENNReal.ofReal_pos], ENNReal.ofReal_lt_top⟩,
    h₀, h₁, ?_, ?_⟩
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;> simp [dom]
  · rw [h₀]
    norm_num [ENNReal.ofReal_pos]
  · rw [h₁, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by norm_num)

end MG03
