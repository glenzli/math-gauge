import formal_oet.vol_01.ch_01_foundations.metric_entropy
import formal_oet.vol_01.ch_02_operator_bounds.decoupling
import formal_oet.vol_01.ch_02_operator_bounds.single_channel
import Mathlib.Data.ENNReal.Inv

/-! Formalization of Chapter 3 of Zhe Li's The Operator Evolution Theory,
https://glenzli.com/books/oet/, adapted from the CC BY 4.0 source. -/

namespace MG03

open Set formal_oet.vol_01.ch_01_foundations formal_oet.vol_01.ch_02_operator_bounds

variable {X I : Type} {bot : X} {d : I → X → X → ENNReal}
variable {f g : Operator X bot} {U : Set X}

def FiniteRadius (r : ENNReal) : Prop := 0 < r ∧ r < ⊤

@[simp] theorem mul_func (g f : Operator X bot) (x : X) :
    (g * f).func x = g.func (f.func x) := rfl

@[simp] theorem one_func (x : X) : (1 : Operator X bot).func x = x := rfl

theorem image_mem (f : Operator X bot) {x : X} (hx : x ∈ U) :
    f.func x ∈ f.func '' U := ⟨x, hx, rfl⟩

theorem comp_domain (hU : U ⊆ dom (g * f)) :
    U ⊆ dom f ∧ f.func '' U ⊆ dom g := by
  constructor
  · intro x hx h
    exact hU hx (by rw [mul_func, h, g.preserves_bot])
  · rintro _ ⟨x, hx, rfl⟩
    exact hU hx

def constPart (d : I → X → X → ENNReal) (f : Operator X bot) (U : Set X) : Set I :=
  {i | ∀ x ∈ U, ∀ y ∈ U, d i (f.func x) (f.func y) = 0}

def idPart (d : I → X → X → ENNReal) (f : Operator X bot) (U : Set X) : Set I :=
  {i | i ∉ constPart d f U ∧ ∀ x ∈ U, d i (f.func x) x = 0}

def actPart (d : I → X → X → ENNReal) (f : Operator X bot) (U : Set X) : Set I :=
  (constPart d f U ∪ idPart d f U)ᶜ

theorem component_partition (i : I) :
    (i ∈ constPart d f U ∧ i ∉ idPart d f U ∧ i ∉ actPart d f U) ∨
    (i ∉ constPart d f U ∧ i ∈ idPart d f U ∧ i ∉ actPart d f U) ∨
    (i ∉ constPart d f U ∧ i ∉ idPart d f U ∧ i ∈ actPart d f U) := by
  classical
  by_cases hc : i ∈ constPart d f U
  · exact Or.inl ⟨hc, fun h => h.1 hc, fun h => h (Or.inl hc)⟩
  · by_cases hi : i ∈ idPart d f U
    · exact Or.inr (Or.inl ⟨hc, hi, fun h => h (Or.inr hi)⟩)
    · exact Or.inr (Or.inr ⟨hc, hi, fun h => h.elim hc hi⟩)

theorem const_zero_row [Fintype I] (_hU : U ⊆ dom f) {i : I}
    (hi : i ∈ constPart d f U) (x : X) (hx : x ∈ U) (y : X) (hy : y ∈ U) :
    d i (f.func x) (f.func y) ≤ ∑ k : I, (0 : ENNReal) * d k x y := by
  rw [hi x hx y hy]
  simp

theorem zero_row_sum [Fintype I] (x y : X) : (∑ k : I, (0 : ENNReal) * d k x y) = 0 := by
  simp

theorem const_colip_zero [Fintype I] (_hU : U ⊆ dom f) {i : I}
    (hi : i ∈ constPart d f U) {K : I → I → ENNReal}
    (hK : IsCoLipMatrix d f U K) (k : I)
    (hp : ∃ x ∈ U, ∃ y ∈ U, 0 < d k x y) : K k i = 0 := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hp
  exact colip_entry_eq_zero_of_output_zero_input_pos d f U K k i x y hK hx hy
    (hi x hx y hy) hxy

theorem dist_eq_of_zero {e : X → X → ENNReal} (he : ExtendedPseudoMetric X bot e)
    {a b c : X} (h : e a b = 0) : e a c = e b c := by
  have h' : e b a = 0 := (he.symm b a).trans h
  exact le_antisymm (by simpa [h] using he.triangle a b c)
    (by simpa [h'] using he.triangle b a c)

theorem id_isometry (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (_hU : U ⊆ dom f)
    {i : I} (hi : i ∈ idPart d f U) (x : X) (hx : x ∈ U) (y : X) (hy : y ∈ U) :
    d i (f.func x) (f.func y) = d i x y := by
  rw [dist_eq_of_zero (hd i) (hi.2 x hx), (hd i).symm x,
    dist_eq_of_zero (hd i) (hi.2 y hy), (hd i).symm y x]

theorem outer_const (_hU : U ⊆ dom (g * f)) {i : I}
    (hi : i ∈ constPart d g (f.func '' U)) : i ∈ constPart d (g * f) U :=
  fun _ hx _ hy => hi _ (image_mem f hx) _ (image_mem f hy)

theorem comp_id (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (hU : U ⊆ dom (g * f)) :
    idPart d f U ∩ idPart d g (f.func '' U) ⊆ idPart d (g * f) U := by
  rintro i ⟨hf, hg⟩
  refine ⟨?_, ?_⟩
  · intro hc
    apply hf.1
    intro _ hx _ hy
    rw [← id_isometry hd (comp_domain hU).2 hg _ (image_mem f hx) _ (image_mem f hy)]
    exact hc _ hx _ hy
  · intro x hx
    exact (dist_eq_of_zero (hd i) (hg.2 _ (image_mem f hx))).trans (hf.2 x hx)

theorem comp_act (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (hU : U ⊆ dom (g * f)) :
    actPart d (g * f) U ⊆ actPart d f U ∪ actPart d g (f.func '' U) := by
  classical
  intro i hi
  by_contra h
  have hf : i ∈ constPart d f U ∨ i ∈ idPart d f U :=
    not_not.mp (fun hn => h (Or.inl hn))
  have hg : i ∈ constPart d g (f.func '' U) ∨ i ∈ idPart d g (f.func '' U) :=
    not_not.mp (fun hn => h (Or.inr hn))
  rcases hg with hg | hg
  · exact hi (Or.inl (outer_const hU hg))
  · rcases hf with hf | hf
    · apply hi
      left
      intro x hx y hy
      exact (id_isometry hd (comp_domain hU).2 hg _ (image_mem f hx) _
        (image_mem f hy)).trans (hf x hx y hy)
    · exact hi (Or.inr (comp_id hd hU ⟨hf, hg⟩))

def composite (steps : ℕ → Operator X bot) : ℕ → Operator X bot
  | 0 => 1
  | n + 1 => steps n * composite steps n

def finiteSteps {n : ℕ} (steps : Fin n → Operator X bot) (m : ℕ) : Operator X bot :=
  if h : m < n then steps ⟨m, h⟩ else 1

@[simp] theorem finiteSteps_apply {n : ℕ} (steps : Fin n → Operator X bot) (m : Fin n) :
    finiteSteps steps m = steps m := by
  simp [finiteSteps, m.isLt]

def stage (steps : ℕ → Operator X bot) (U : Set X) (n : ℕ) : Set X :=
  (composite steps n).func '' U

@[simp] theorem stage_zero (steps : ℕ → Operator X bot) (U : Set X) :
    stage steps U 0 = U := Set.image_id _

theorem stage_succ (steps : ℕ → Operator X bot) (U : Set X) (n : ℕ) :
    stage steps U (n + 1) = (steps n).func '' stage steps U n :=
  (Set.image_image (steps n).func (composite steps n).func U).symm

theorem stage_domain (steps : ℕ → Operator X bot) (n : ℕ)
    (hU : U ⊆ dom (composite steps n)) : ∀ m < n, stage steps U m ⊆ dom (steps m) := by
  induction n with
  | zero => exact fun _ hm => (Nat.not_lt_zero _ hm).elim
  | succ n ih =>
    intro m hm
    rcases (Nat.lt_succ_iff.mp hm).lt_or_eq with h | rfl
    · exact ih (comp_domain hU).1 m h
    · exact (comp_domain hU).2

theorem prefix_act (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (steps : ℕ → Operator X bot) (n : ℕ) (hU : U ⊆ dom (composite steps n)) :
    actPart d (composite steps n) U ⊆ ⋃ m < n, actPart d (steps m) (stage steps U m) := by
  classical
  induction n with
  | zero =>
    intro i hi
    by_cases hc : i ∈ constPart d (1 : Operator X bot) U
    · exact (hi (Or.inl hc)).elim
    · exact (hi (Or.inr ⟨hc, fun x _ => (hd i).dist_self x⟩)).elim
  | succ n ih =>
    intro i hi
    rcases comp_act hd hU hi with hp | hs
    · obtain ⟨m, hm, hi⟩ := Set.mem_iUnion₂.mp (ih (comp_domain hU).1 hp)
      exact Set.mem_iUnion₂.mpr ⟨m, Nat.lt_succ_of_lt hm, hi⟩
    · exact Set.mem_iUnion₂.mpr ⟨n, Nat.lt_succ_self n, hs⟩

theorem finite_act (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) {n : ℕ}
    (steps : Fin n → Operator X bot) (hU : U ⊆ dom (composite (finiteSteps steps) n)) :
    actPart d (composite (finiteSteps steps) n) U ⊆
      ⋃ m : Fin n, actPart d (steps m) (stage (finiteSteps steps) U m) := by
  intro i hi
  obtain ⟨m, hm, h⟩ := Set.mem_iUnion₂.mp (prefix_act hd (finiteSteps steps) n hU hi)
  exact Set.mem_iUnion.mpr ⟨⟨m, hm⟩, by simpa only [finiteSteps, dif_pos hm] using h⟩

theorem inner_const_of_diagonal [Fintype I] (_hU : U ⊆ dom (g * f)) {j : I}
    (hj : j ∈ constPart d f U) {L : I → I → ENNReal}
    (hL : IsLipMatrix d g (f.func '' U) L) (hrow : ∀ k, k ≠ j → L k j = 0) :
    j ∈ constPart d (g * f) U := by
  intro x hx y hy
  have h := lip_bound_of_single_input_row d g _ L j j hL hrow
    _ (image_mem f hx) _ (image_mem f hy)
  rw [hj x hx y hy, mul_zero] at h
  exact le_antisymm h (zero_le _)

def fiberAt (e : X → X → ENNReal) (f : Operator X bot) (U : Set X) (y : X) : Set X :=
  {x ∈ U | e (f.func x) y = 0}

noncomputable def fiber (d : I → X → X → ENNReal) (J : Set I)
    (f : Operator X bot) (U : Set X) (y : X) : Set X :=
  fiberAt (subfamily_pseudometric d J) f U y

theorem subfamily_zero_iff {J : Set I} {x y : X} :
    subfamily_pseudometric d J x y = 0 ↔ ∀ j ∈ J, d j x y = 0 := by
  constructor
  · intro h j hj
    apply le_antisymm _ (zero_le _)
    exact (le_iSup (fun k : J => d k.1 x y) ⟨j, hj⟩).trans_eq h
  · intro h
    exact le_antisymm (iSup_le fun j : J => (h j j.2).le) (zero_le _)

theorem fiber_singleton (i : I) (y : X) :
    fiber d {i} f U y = fiberAt (d i) f U y := by
  unfold fiber
  rw [subfamily_pseudometric_singleton]

theorem fiber_eq_of_zero {e : X → X → ENNReal} (he : ExtendedPseudoMetric X bot e)
    {y z : X} (hz : e y z = 0) : fiberAt e f U y = fiberAt e f U z := by
  ext x
  dsimp [fiberAt]
  rw [he.symm (f.func x) y, dist_eq_of_zero he hz, he.symm z (f.func x)]

theorem fiber_target_zero (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (_hU : U ⊆ dom f) {J : Set I} (hJ : J.Nonempty) {y z : X}
    (hz : subfamily_pseudometric d J y z = 0) : fiber d J f U y = fiber d J f U z :=
  fiber_eq_of_zero (subfamily_pseudometric_is_extended d J hJ hd) hz

theorem fiber_empty_of_pos (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (_hU : U ⊆ dom f) {J : Set I} (hJ : J.Nonempty) {y : X}
    (h : ∀ z ∈ f.func '' U, 0 < subfamily_pseudometric d J y z) :
    fiber d J f U y = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  let e := subfamily_pseudometric_is_extended d J hJ hd
  exact (ne_of_gt (h _ (image_mem f hx.1))) ((e.symm _ _).trans hx.2)

def fiberBlocks (e : X → X → ENNReal) (f : Operator X bot) (U : Set X) : Set (Set X) :=
  (fun y => fiberAt e f U y) '' (f.func '' U)

theorem fiber_cover {e : X → X → ENNReal} (he : ExtendedPseudoMetric X bot e)
    (_hU : U ⊆ dom f) :
    (∀ y ∈ f.func '' U, (fiberAt e f U y).Nonempty) ∧
      ⋃₀ (fiberBlocks e f U) = U := by
  constructor
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, hx, he.dist_self _⟩
  · ext x
    constructor
    · rintro ⟨_, ⟨y, _, rfl⟩, hx⟩
      exact hx.1
    · intro hx
      exact ⟨_, ⟨_, image_mem f hx, rfl⟩, hx, he.dist_self _⟩

theorem fiber_equal_or_disjoint {e : X → X → ENNReal} (he : ExtendedPseudoMetric X bot e)
    (_hU : U ⊆ dom f) {y z : X} (_hy : y ∈ f.func '' U) (_hz : z ∈ f.func '' U) :
    fiberAt e f U y = fiberAt e f U z ∨ Disjoint (fiberAt e f U y) (fiberAt e f U z) := by
  classical
  by_cases h : Disjoint (fiberAt e f U y) (fiberAt e f U z)
  · exact Or.inr h
  · obtain ⟨x, hx, hx'⟩ := Set.not_disjoint_iff.mp h
    exact Or.inl (fiber_eq_of_zero he
      ((dist_eq_of_zero he ((he.symm _ _).trans hx.2)).trans hx'.2))

theorem fiber_partition (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (hU : U ⊆ dom f) {J : Set I} (hJ : J.Nonempty) :
    let blocks := fiberBlocks (subfamily_pseudometric d J) f U
    (∀ B ∈ blocks, B.Nonempty) ∧ ⋃₀ blocks = U ∧ blocks.PairwiseDisjoint id := by
  let he := subfamily_pseudometric_is_extended d J hJ hd
  obtain ⟨hn, hu⟩ := fiber_cover he hU
  refine ⟨?_, hu, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact hn y hy
  · rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩ hne
    exact (fiber_equal_or_disjoint he hU hy hz).resolve_left hne

theorem fiber_intersection (_hU : U ⊆ dom f) {J : Set I} (hJ : J.Nonempty) (y : X) :
    fiber d J f U y = ⋂ j ∈ J, fiberAt (d j) f U y := by
  ext x
  simp only [fiber, fiberAt, Set.mem_setOf_eq, subfamily_zero_iff, Set.mem_iInter]
  exact ⟨fun ⟨hx, h⟩ j hj => ⟨hx, h j hj⟩,
    fun h => ⟨hJ.choose_spec |> fun hj => (h _ hj).1, fun j hj => (h j hj).2⟩⟩

theorem fiber_antitone (_hU : U ⊆ dom f) {J K : Set I}
    (_hJ : J.Nonempty) (_hK : K.Nonempty) (hJK : J ⊆ K) (y : X) :
    fiber d K f U y ⊆ fiber d J f U y :=
  fun _ hx => ⟨hx.1, subfamily_zero_iff.mpr fun j hj => subfamily_zero_iff.mp hx.2 j (hJK hj)⟩

theorem fiber_full_subset (i : I) (y : X) : fiber d Set.univ f U y ⊆ fiberAt (d i) f U y :=
  fun _ hx => ⟨hx.1, subfamily_zero_iff.mp hx.2 i (Set.mem_univ _)⟩

theorem id_fiber (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (_hU : U ⊆ dom f)
    {i : I} (hi : i ∈ idPart d f U) (y : X) :
    fiberAt (d i) f U y = {x ∈ U | d i x y = 0} :=
  Set.ext fun x => and_congr_right fun hx => by
    rw [dist_eq_of_zero (hd i) (hi.2 x hx)]

theorem const_fiber (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (_hU : U ⊆ dom f)
    {i : I} (hi : i ∈ constPart d f U) {y₀ : X} (hy₀ : y₀ ∈ f.func '' U) :
    fiberAt (d i) f U y₀ = U ∧
      ∀ y, 0 < d i y y₀ → fiberAt (d i) f U y = ∅ := by
  obtain ⟨z, hz, rfl⟩ := hy₀
  refine ⟨Set.Subset.antisymm (fun _ hx => hx.1) (fun x hx => ⟨hx, hi x hx z hz⟩), ?_⟩
  intro y hy
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact (ne_of_gt hy)
    ((dist_eq_of_zero (hd i) (((hd i).symm _ _).trans hx.2)).trans (hi x hx.1 z hz))

def pairRelation (f : Operator X bot) (U : Set X) (R : X → X → Prop) : Set (X × X) :=
  {p | p.1 ∈ U ∧ p.2 ∈ U ∧ R (f.func p.1) (f.func p.2)}

def equalPairs (f : Operator X bot) (U : Set X) : Set (X × X) := pairRelation f U Eq

def zeroPairs (d : I → X → X → ENNReal) (f : Operator X bot) (U : Set X) :
    Set (X × X) := pairRelation f U (GaugeZeroRelated d)

def fiberDominates (d : I → X → X → ENNReal) (U : Set X) (f g : Operator X bot) : Prop :=
  zeroPairs d f U ⊆ zeroPairs d g U

theorem zeroPairs_fiber_iff (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    (x, y) ∈ zeroPairs d f U ↔ y ∈ fiber d Set.univ f U (f.func x) := by
  constructor
  · intro h
    exact ⟨hy, subfamily_zero_iff.mpr fun i _ => ((hd i).symm _ _).trans (h.2.2 i)⟩
  · intro h
    exact ⟨hx, hy, fun i => ((hd i).symm _ _).trans
      (subfamily_zero_iff.mp h.2 i (Set.mem_univ _))⟩

theorem fiberDominates_iff_refines (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (_hU : U ⊆ dom f ∩ dom g) :
    fiberDominates d U f g ↔
      ∀ x ∈ U, fiber d Set.univ f U (f.func x) ⊆ fiber d Set.univ g U (g.func x) := by
  constructor
  · intro h x hx y hy
    exact (zeroPairs_fiber_iff hd hx hy.1).mp (h ((zeroPairs_fiber_iff hd hx hy.1).mpr hy))
  · rintro h ⟨x, y⟩ hxy
    exact (zeroPairs_fiber_iff hd hxy.1 hxy.2.1).mpr
      (h x hxy.1 ((zeroPairs_fiber_iff hd hxy.1 hxy.2.1).mp hxy))

def imagePoint (f : Operator X bot) (U : Set X) (x : U) : f.func '' U :=
  ⟨f.func x, image_mem f x.2⟩

theorem imagePoint_surjective (f : Operator X bot) (U : Set X) :
    Function.Surjective (imagePoint f U) := by
  rintro ⟨_, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

def imageSetoid (d : I → X → X → ENNReal) (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (f : Operator X bot) (U : Set X) : Setoid (f.func '' U) :=
  ⟨fun x y => GaugeZeroRelated d x.1 y.1, by
    have h := gauge_zero_related_equivalence d (fun i => (hd i).dist_self)
      (fun i => (hd i).symm) (fun i => (hd i).triangle)
    exact ⟨fun x => h.refl x.1, fun hab => h.symm hab, fun hab hbc => h.trans hab hbc⟩⟩

def ImageQuotient (d : I → X → X → ENNReal) (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (f : Operator X bot) (U : Set X) := Quotient (imageSetoid d hd f U)

def imageClass (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (f : Operator X bot) (U : Set X) (x : U) : ImageQuotient d hd f U :=
  Quotient.mk _ (imagePoint f U x)

theorem imageClass_eq_iff (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (x y : U) :
    imageClass hd f U x = imageClass hd f U y ↔ (x.1, y.1) ∈ zeroPairs d f U :=
  ⟨fun h => ⟨x.2, y.2, Quotient.exact h⟩, fun h => Quotient.sound h.2.2⟩

theorem imageClass_surjective (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (f : Operator X bot) (U : Set X) : Function.Surjective (imageClass hd f U) := by
  intro q
  obtain ⟨z, rfl⟩ := Quotient.exists_rep q
  obtain ⟨x, hx⟩ := imagePoint_surjective f U z
  exact ⟨x, congrArg (Quotient.mk _) hx⟩

theorem factor_of_surjective {A B C : Type} {p : A → B} {q : A → C}
    (hp : Function.Surjective p) (h : ∀ x y, p x = p y → q x = q y) :
    ∃ T : B → C, ∀ x, T (p x) = q x := by
  classical
  exact ⟨fun b => q (hp b).choose, fun x => h _ _ (hp (p x)).choose_spec⟩

def ValueFactor (f g : Operator X bot) (U : Set X) : Prop :=
  ∃ T : (f.func '' U : Set X) → X, ∀ x : U, T (imagePoint f U x) = g.func x

theorem value_factor_subset (_hU : U ⊆ dom f ∩ dom g)
    (h : ValueFactor f g U) : equalPairs f U ⊆ equalPairs g U := by
  obtain ⟨T, hT⟩ := h
  rintro ⟨x, y⟩ ⟨hx, hy, hxy⟩
  exact ⟨hx, hy, (hT ⟨x, hx⟩).symm.trans
    ((congrArg T (Subtype.ext hxy)).trans (hT ⟨y, hy⟩))⟩

theorem value_factor_exists (_hU : U ⊆ dom f ∩ dom g)
    (h : equalPairs f U ⊆ equalPairs g U) : ValueFactor f g U :=
  factor_of_surjective (imagePoint_surjective f U)
    (fun x y hxy => (h (show (x.1, y.1) ∈ equalPairs f U from
      ⟨x.2, y.2, congrArg Subtype.val hxy⟩)).2.2)

theorem value_factor_empty : ValueFactor f g (∅ : Set X) :=
  value_factor_exists (Set.empty_subset _) (fun _ hx => hx.1.elim)

theorem value_factor_both (hU : U ⊆ dom f ∩ dom g) :
    ValueFactor f g U ∧ ValueFactor g f U ↔ equalPairs f U = equalPairs g U := by
  have hU' : U ⊆ dom g ∩ dom f := fun _ hx => ⟨(hU hx).2, (hU hx).1⟩
  exact ⟨fun h => Subset.antisymm (value_factor_subset hU h.1) (value_factor_subset hU' h.2),
    fun h => ⟨value_factor_exists hU h.le, value_factor_exists hU' h.ge⟩⟩

theorem value_factor_lip {e : X → X → ENNReal} (_he : ExtendedPseudoMetric X bot e)
    (_hU : U ⊆ dom f ∩ dom g) {K L : ENNReal}
    (hK : FiniteRadius K) (_hL : L < ⊤)
    (hlower : ∀ x ∈ U, ∀ y ∈ U, K * e x y ≤ e (f.func x) (f.func y))
    (hupper : ∀ x ∈ U, ∀ y ∈ U, e (g.func x) (g.func y) ≤ L * e x y)
    (T : (f.func '' U : Set X) → X) (hT : ∀ x : U, T (imagePoint f U x) = g.func x) :
    ∀ a b : (f.func '' U : Set X), e (T a) (T b) ≤ (L / K) * e a b := by
  intro a b
  obtain ⟨x, rfl⟩ := imagePoint_surjective f U a
  obtain ⟨y, rfl⟩ := imagePoint_surjective f U b
  rw [hT, hT]
  have hx : e x y ≤ e (f.func x) (f.func y) / K :=
    ENNReal.le_div_iff_mul_le (Or.inl (ne_of_gt hK.1)) (Or.inl hK.2.ne) |>.mpr
      (by simpa [mul_comm] using hlower x x.2 y y.2)
  exact (hupper x x.2 y y.2).trans (by
    simpa only [imagePoint, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      using mul_le_mul_right hx L)

def QuotientFactor (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (f g : Operator X bot) (U : Set X) : Prop :=
  ∃ T : ImageQuotient d hd f U → ImageQuotient d hd g U,
    ∀ x : U, T (imageClass hd f U x) = imageClass hd g U x

theorem quotient_factor_iff (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (_hU : U ⊆ dom f ∩ dom g) : QuotientFactor hd f g U ↔ fiberDominates d U f g := by
  constructor
  · rintro ⟨T, hT⟩ ⟨x, y⟩ h
    obtain ⟨hx, hy, hxy⟩ := h
    apply (imageClass_eq_iff hd ⟨x, hx⟩ ⟨y, hy⟩).mp
    rw [← hT ⟨x, hx⟩, ← hT ⟨y, hy⟩, (imageClass_eq_iff hd ⟨x, hx⟩ ⟨y, hy⟩).mpr ⟨hx, hy, hxy⟩]
  · intro h
    exact factor_of_surjective (imageClass_surjective hd f U) fun x y hxy =>
      (imageClass_eq_iff hd x y).mpr (h ((imageClass_eq_iff hd x y).mp hxy))

theorem quotient_factor_both (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (hU : U ⊆ dom f ∩ dom g) :
    QuotientFactor hd f g U ∧ QuotientFactor hd g f U ↔ zeroPairs d f U = zeroPairs d g U := by
  have hU' : U ⊆ dom g ∩ dom f := fun _ hx => ⟨(hU hx).2, (hU hx).1⟩
  rw [quotient_factor_iff hd hU, quotient_factor_iff hd hU']
  exact ⟨fun h => Subset.antisymm h.1 h.2, fun h => ⟨h.le, h.ge⟩⟩

def ImageSeparated (d : I → X → X → ENNReal) (f : Operator X bot) (U : Set X) : Prop :=
  ∀ a ∈ f.func '' U, ∀ b ∈ f.func '' U, GaugeZeroRelated d a b → a = b

theorem equalPairs_eq_zeroPairs (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (hs : ImageSeparated d f U) : equalPairs f U = zeroPairs d f U := by
  apply Subset.antisymm
  · rintro ⟨x, y⟩ ⟨hx, hy, hxy⟩
    exact ⟨hx, hy, fun i => by rw [hxy, (hd i).dist_self]⟩
  · rintro ⟨x, y⟩ ⟨hx, hy, hxy⟩
    exact ⟨hx, hy, hs _ (image_mem f hx) _ (image_mem f hy) hxy⟩

theorem separated_factor_iff (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (hU : U ⊆ dom f ∩ dom g) (hf : ImageSeparated d f U) (hg : ImageSeparated d g U) :
    (ValueFactor f g U ↔ QuotientFactor hd f g U) ∧
    ((ValueFactor f g U ∧ ValueFactor g f U) ↔
      (QuotientFactor hd f g U ∧ QuotientFactor hd g f U)) := by
  have he := equalPairs_eq_zeroPairs hd hf
  have he' := equalPairs_eq_zeroPairs hd hg
  constructor
  · rw [quotient_factor_iff hd hU, fiberDominates, ← he, ← he']
    exact ⟨value_factor_subset hU, value_factor_exists hU⟩
  · rw [value_factor_both hU, quotient_factor_both hd hU, he, he']

theorem fiber_preorder :
    (∀ f : Operator X bot, fiberDominates d U f f) ∧
      (∀ f g h : Operator X bot, fiberDominates d U f g →
        fiberDominates d U g h → fiberDominates d U f h) :=
  ⟨fun _ => Subset.rfl, fun _ _ _ h₁ h₂ => h₁.trans h₂⟩

theorem fiber_chain {m : ℕ} (steps : ℕ → Operator X bot)
    (_hU : ∀ k ≤ m, U ⊆ dom (steps k))
    (h : ∀ k < m, fiberDominates d U (steps k) (steps (k + 1)))
    {a b : ℕ} (hab : a ≤ b) (hb : b ≤ m) : fiberDominates d U (steps a) (steps b) := by
  induction b with
  | zero =>
    have : a = 0 := Nat.eq_zero_of_le_zero hab
    subst a
    exact Subset.rfl
  | succ b ih =>
    rcases hab.lt_or_eq with hl | rfl
    · exact (ih (Nat.le_of_lt_succ hl) (Nat.le_of_succ_le hb)).trans (h b hb)
    · exact Subset.rfl

theorem fiber_chain_fin {m : ℕ} (steps : Fin (m + 1) → Operator X bot)
    (hU : ∀ k, U ⊆ dom (steps k))
    (h : ∀ k : Fin m, fiberDominates d U (steps k.castSucc) (steps k.succ))
    {a b : Fin (m + 1)} (hab : a ≤ b) : fiberDominates d U (steps a) (steps b) := by
  have hdom (k : ℕ) (hk : k ≤ m) : U ⊆ dom (finiteSteps steps k) := by
    simpa only [finiteSteps, dif_pos (Nat.lt_succ_of_le hk)] using hU ⟨k, Nat.lt_succ_of_le hk⟩
  have hstep (k : ℕ) (hk : k < m) :
      fiberDominates d U (finiteSteps steps k) (finiteSteps steps (k + 1)) := by
    simpa only [finiteSteps, dif_pos (Nat.lt_succ_of_lt hk), dif_pos (Nat.succ_lt_succ hk)] using
      h ⟨k, hk⟩
  simpa only [finiteSteps_apply] using
    fiber_chain (finiteSteps steps) hdom hstep (show a.val ≤ b.val from hab) (Nat.le_of_lt_succ b.isLt)

theorem fiber_chain_strict {m : ℕ} (steps : ℕ → Operator X bot)
    (hU : ∀ k ≤ m, U ⊆ dom (steps k))
    (h : ∀ k < m, fiberDominates d U (steps k) (steps (k + 1))) {r : ℕ} (hr : r < m)
    (hs : zeroPairs d (steps r) U ⊂ zeroPairs d (steps (r + 1)) U) :
    zeroPairs d (steps 0) U ⊂ zeroPairs d (steps m) U ∧
      ∃ p ∈ zeroPairs d (steps (r + 1)) U \ zeroPairs d (steps r) U,
        p ∈ zeroPairs d (steps m) U \ zeroPairs d (steps 0) U := by
  obtain ⟨p, hp, hp'⟩ := Set.exists_of_ssubset hs
  have hpm := fiber_chain steps hU h (Nat.succ_le_of_lt hr) le_rfl hp
  have hp₀ := fun hp₀ => hp' (fiber_chain steps hU h (Nat.zero_le r) hr.le hp₀)
  exact ⟨Set.ssubset_iff_subset_ne.mpr ⟨fiber_chain steps hU h (Nat.zero_le m) le_rfl,
    fun he => hp₀ (he.symm ▸ hpm)⟩, p, ⟨hp, hp'⟩, hpm, hp₀⟩

end MG03
