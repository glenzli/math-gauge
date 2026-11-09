import formal_oet.vol_01.ch_01_foundations.metric_entropy
import formal_oet.vol_01.ch_02_operator_bounds.decoupling
import formal_oet.vol_01.ch_02_operator_bounds.single_channel

/- Based on Zhe Li (Glen Li / glenzli), The Operator Evolution Theory,
   Volume I, Chapter 3. https://glenzli.com/books/oet/ . CC BY 4.0.
   This file is a new Lean formalization, not the author's implementation. -/
namespace Chapter3
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set
variable {X I : Type} {bot : X}

def constComp (d : I → X → X → ENNReal) (f : Operator X bot) (U : Set X) : Set I :=
  {i | ∀ x ∈ U, ∀ y ∈ U, d i (f.func x) (f.func y) = 0}
def idComp (d : I → X → X → ENNReal) (f : Operator X bot) (U : Set X) : Set I :=
  {i | i ∉ constComp d f U ∧ ∀ x ∈ U, d i (f.func x) x = 0}
def activeComp (d : I → X → X → ENNReal) (f : Operator X bot) (U : Set X) : Set I :=
  (constComp d f U ∪ idComp d f U)ᶜ

theorem component_partition (d : I → X → X → ENNReal) (f : Operator X bot) (U : Set X) :
    constComp d f U ∪ idComp d f U ∪ activeComp d f U = univ ∧
    Disjoint (constComp d f U) (idComp d f U) ∧
    Disjoint (constComp d f U) (activeComp d f U) ∧
    Disjoint (idComp d f U) (activeComp d f U) := by
  classical
  constructor
  · exact Set.union_compl_self _
  · refine ⟨?_, ?_, ?_⟩
    · exact Set.disjoint_left.mpr (fun _ hc hi => hi.1 hc)
    · exact Set.disjoint_left.mpr (fun _ hc ha => ha (Or.inl hc))
    · exact Set.disjoint_left.mpr (fun _ hi ha => ha (Or.inr hi))

theorem zero_left {d : X → X → ENNReal} (h : ExtendedPseudoMetric X bot d)
    {a b : X} (hab : d a b = 0) (c : X) : d a c = d b c := by
  apply le_antisymm
  · simpa [hab] using h.triangle a b c
  · simpa [h.symm b a, hab] using h.triangle b a c

theorem zero_trans {d : X → X → ENNReal} (h : ExtendedPseudoMetric X bot d)
    {a b c : X} (hab : d a b = 0) (hbc : d b c = 0) : d a c = 0 := by
  rw [zero_left h hab, hbc]

theorem id_distance (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    {f : Operator X bot} {U : Set X} {i : I} (hi : i ∈ idComp d f U)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    d i (f.func x) (f.func y) = d i x y := by
  rw [zero_left (hd i) (hi.2 x hx), (hd i).symm x,
    zero_left (hd i) (hi.2 y hy), (hd i).symm y]

theorem const_zero_row [Fintype I] (d : I → X → X → ENNReal)
    {f : Operator X bot} {U : Set X} {i : I} (hi : i ∈ constComp d f U)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    d i (f.func x) (f.func y) ≤ ∑ k : I, 0 * d k x y := by
  simp [hi x hx y hy]

theorem const_colip_zero [Fintype I] (d : I → X → X → ENNReal)
    {f : Operator X bot} {U : Set X} {i k : I} {K : I → I → ENNReal}
    (hi : i ∈ constComp d f U) (hK : IsCoLipMatrix d f U K)
    (hp : ∃ x ∈ U, ∃ y ∈ U, 0 < d k x y) : K k i = 0 := by
  obtain ⟨x, hx, y, hy, hp⟩ := hp
  exact colip_entry_eq_zero_of_output_zero_input_pos d f U K k i x y hK hx hy
    (hi x hx y hy) hp

theorem outer_const (d : I → X → X → ENNReal)
    {f g : Operator X bot} {U : Set X} {i : I}
    (hi : i ∈ constComp d g (f.func '' U)) : i ∈ constComp d (g * f) U := by
  intro x hx y hy
  exact hi _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩

theorem compose_id (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    {f g : Operator X bot} {U : Set X} {i : I}
    (hf : i ∈ idComp d f U) (hg : i ∈ idComp d g (f.func '' U)) :
    i ∈ idComp d (g * f) U := by
  constructor
  · intro hc
    apply hf.1
    intro x hx y hy
    have he := id_distance d hd hg (show f.func x ∈ f.func '' U from ⟨x,hx,rfl⟩)
      (show f.func y ∈ f.func '' U from ⟨y,hy,rfl⟩)
    exact he.symm.trans (hc x hx y hy)
  · intro x hx
    exact zero_trans (hd i) (hg.2 _ ⟨x,hx,rfl⟩) (hf.2 x hx)

theorem compose_active (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f g : Operator X bot) (U : Set X) :
    activeComp d (g * f) U ⊆ activeComp d f U ∪ activeComp d g (f.func '' U) := by
  intro i hi
  by_contra hn
  have hf : i ∈ constComp d f U ∨ i ∈ idComp d f U := by
    simpa only [activeComp, mem_compl_iff, not_not] using (show i ∉ activeComp d f U from fun h => hn (Or.inl h))
  have hg : i ∈ constComp d g (f.func '' U) ∨ i ∈ idComp d g (f.func '' U) := by
    simpa only [activeComp, mem_compl_iff, not_not] using (show i ∉ activeComp d g (f.func '' U) from fun h => hn (Or.inr h))
  rcases hg with hg | hg
  · exact hi (Or.inl (outer_const d hg))
  · rcases hf with hf | hf
    · apply hi; left; intro x hx y hy
      exact (id_distance d hd hg ⟨x,hx,rfl⟩ ⟨y,hy,rfl⟩).trans (hf x hx y hy)
    · exact hi (Or.inr (compose_id d hd hf hg))

def run : List (Operator X bot) → Operator X bot
  | [] => 1
  | f :: fs => run fs * f
def stageActive (d : I → X → X → ENNReal) : List (Operator X bot) → Set X → Set I
  | [], _ => ∅
  | f :: fs, U => activeComp d f U ∪ stageActive d fs (f.func '' U)

theorem run_active (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (fs : List (Operator X bot)) (U : Set X) :
    activeComp d (run fs) U ⊆ stageActive d fs U := by
  induction fs generalizing U with
  | nil =>
      intro i hi
      apply hi
      by_cases hc : i ∈ constComp d (run (bot := bot) []) U
      · exact Or.inl hc
      · exact Or.inr ⟨hc, fun x _ => (hd i).dist_self x⟩
  | cons f fs ih =>
      exact (compose_active d hd f (run fs) U).trans (Set.union_subset_union_right _ (ih _))

theorem run_domains (f : Operator X bot) (fs : List (Operator X bot)) (U : Set X)
    (hU : U ⊆ dom (run (f :: fs))) :
    U ⊆ dom f ∧ f.func '' U ⊆ dom (run fs) := by
  constructor
  · intro x hx he
    have h := hU hx
    change (run fs).func (f.func x) ≠ bot at h
    exact h (by rw [he, (run fs).preserves_bot])
  · rintro _ ⟨x,hx,rfl⟩; exact hU hx

theorem const_diagonal [Fintype I] (d : I → X → X → ENNReal)
    {f g : Operator X bot} {U : Set X} {j : I} {L : I → I → ENNReal}
    (hf : j ∈ constComp d f U) (hL : IsLipMatrix d g (f.func '' U) L)
    (hz : ∀ k, k ≠ j → L k j = 0) : j ∈ constComp d (g * f) U := by
  intro x hx y hy
  apply le_antisymm _ (zero_le _)
  have h := lip_bound_of_single_input_row d g (f.func '' U) L j j hL hz
    _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
  simpa [hf x hx y hy] using h

def fiber (d : I → X → X → ENNReal) (f : Operator X bot) (J : Set I)
    (y : X) (U : Set X) : Set X :=
  {x | x ∈ U ∧ ∀ j ∈ J, d j (f.func x) y = 0}

theorem subfamily_zero (d : I → X → X → ENNReal) (J : Set I) (x y : X) :
    subfamily_pseudometric d J x y = 0 ↔ ∀ j ∈ J, d j x y = 0 := by
  constructor
  · intro h j hj
    exact le_antisymm (h ▸ le_iSup (fun k : J => d k x y) ⟨j,hj⟩) (zero_le _)
  · intro h
    exact le_antisymm (iSup_le (fun j => le_of_eq (h j j.property))) (zero_le _)

theorem fiber_representation (d : I → X → X → ENNReal) (f : Operator X bot)
    (J : Set I) (y : X) (U : Set X) :
    fiber d f J y U = {x ∈ U | subfamily_pseudometric d J (f.func x) y = 0} := by
  ext x; simp [fiber, subfamily_zero]

theorem fiber_target (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot)
    (J : Set I) (U : Set X) {y z : X} (hyz : ∀ j ∈ J, d j y z = 0) :
    fiber d f J y U = fiber d f J z U := by
  ext x; simp only [fiber, mem_setOf_eq]
  constructor
  · rintro ⟨hx,h⟩; exact ⟨hx, fun j hj => zero_trans (hd j) (h j hj) (hyz j hj)⟩
  · rintro ⟨hx,h⟩
    exact ⟨hx, fun j hj => zero_trans (hd j) (h j hj) ((hd j).symm z y |>.trans (hyz j hj))⟩

theorem fiber_cover (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot) (J : Set I) (U : Set X) :
    (∀ y ∈ f.func '' U, (fiber d f J y U).Nonempty) ∧
    (⋃ y ∈ f.func '' U, fiber d f J y U) = U := by
  constructor
  · rintro y ⟨x,hx,rfl⟩; exact ⟨x,hx,fun j _ => (hd j).dist_self _⟩
  · ext x; simp only [mem_iUnion]
    constructor
    · rintro ⟨y,hy,h⟩; exact h.1
    · intro hx; exact ⟨f.func x, ⟨x,hx,rfl⟩, hx, fun j _ => (hd j).dist_self _⟩

theorem fiber_disjoint (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot) (J : Set I)
    (U : Set X) (y z : X) :
    fiber d f J y U = fiber d f J z U ∨ Disjoint (fiber d f J y U) (fiber d f J z U) := by
  by_cases h : ∃ x, x ∈ fiber d f J y U ∧ x ∈ fiber d f J z U
  · obtain ⟨x,hx,hz⟩ := h
    left; apply fiber_target d hd; intro j hj
    exact zero_trans (hd j) ((hd j).symm y _ |>.trans (hx.2 j hj)) (hz.2 j hj)
  · right; rw [Set.disjoint_left]; aesop

theorem fiber_inter (d : I → X → X → ENNReal) (f : Operator X bot)
    (J : Set I) (hJ : J.Nonempty) (y : X) (U : Set X) :
    fiber d f J y U = ⋂ j ∈ J, fiber d f {j} y U := by
  ext x; simp only [fiber, mem_setOf_eq, mem_iInter, mem_singleton_iff, forall_eq]
  obtain ⟨j,hj⟩ := hJ
  constructor
  · rintro ⟨hx,h⟩ k hk; exact ⟨hx,h k hk⟩
  · intro h; exact ⟨(h j hj).1, fun k hk => (h k hk).2⟩

theorem fiber_antitone (d : I → X → X → ENNReal) (f : Operator X bot)
    {J K : Set I} (h : J ⊆ K) (y : X) (U : Set X) :
    fiber d f K y U ⊆ fiber d f J y U := fun _ hx => ⟨hx.1, fun j hj => hx.2 j (h hj)⟩

theorem fiber_singleton (d : I → X → X → ENNReal) (f : Operator X bot)
    (i : I) (y : X) (U : Set X) :
    fiber d f {i} y U = {x ∈ U | d i (f.func x) y = 0} := by ext; simp [fiber]

theorem fiber_full (d : I → X → X → ENNReal) (f : Operator X bot)
    (i : I) (y : X) (U : Set X) : fiber d f univ y U ⊆ fiber d f {i} y U :=
  fiber_antitone d f (Set.subset_univ _) y U

theorem fiber_id (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) {f : Operator X bot}
    {U : Set X} {i : I} (hi : i ∈ idComp d f U) (y : X) :
    fiber d f {i} y U = {x ∈ U | d i x y = 0} := by
  rw [fiber_singleton]; ext x
  constructor <;> rintro ⟨hx,h⟩ <;> refine ⟨hx, ?_⟩
  · rwa [zero_left (hd i) (hi.2 x hx)] at h
  · rwa [zero_left (hd i) (hi.2 x hx)]

theorem fiber_const (d : I → X → X → ENNReal) {f : Operator X bot}
    {U : Set X} {J : Set I} (h : J ⊆ constComp d f U) {y : X} (hy : y ∈ f.func '' U) :
    fiber d f J y U = U := by
  obtain ⟨z,hz,rfl⟩ := hy
  ext x; exact ⟨fun hx => hx.1, fun hx => ⟨hx, fun j hj => h hj x hx z hz⟩⟩

theorem fiber_const_empty (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) {f : Operator X bot}
    {U : Set X} {i : I} (hi : i ∈ constComp d f U) {y z : X}
    (hz : z ∈ f.func '' U) (hy : 0 < d i y z) : fiber d f {i} y U = ∅ := by
  obtain ⟨a,ha,rfl⟩ := hz
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact (ne_of_gt hy) (zero_trans (hd i)
    ((hd i).symm y _ |>.trans (hx.2 i (by simp))) (hi x hx.1 a ha))

def eqRel (f : Operator X bot) (U : Set X) : Set (X × X) :=
  {p | p.1 ∈ U ∧ p.2 ∈ U ∧ f.func p.1 = f.func p.2}
def zeroRel (d : I → X → X → ENNReal) (f : Operator X bot) (U : Set X) : Set (X × X) :=
  {p | p.1 ∈ U ∧ p.2 ∈ U ∧ GaugeZeroRelated d (f.func p.1) (f.func p.2)}
def fiberPreorder (d : I → X → X → ENNReal) (U : Set X) (f g : Operator X bot) : Prop :=
  zeroRel d f U ⊆ zeroRel d g U

theorem zeroRel_fiber (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot) (U : Set X)
    {x y : X} (hx : x ∈ U) :
    (x,y) ∈ zeroRel d f U ↔ y ∈ fiber d f univ (f.func x) U := by
  simp only [zeroRel, fiber, GaugeZeroRelated, mem_setOf_eq, mem_univ, forall_true_left]
  constructor
  · rintro ⟨_,hy,h⟩; exact ⟨hy, fun i => (hd i).symm _ _ |>.trans (h i)⟩
  · rintro ⟨hy,h⟩; exact ⟨hx,hy,fun i => (hd i).symm _ _ |>.trans (h i)⟩

def imagePoint (f : Operator X bot) (U : Set X) (x : U) : f.func '' U :=
  ⟨f.func x, x, x.property, rfl⟩
def Factors (f g : Operator X bot) (U : Set X) : Prop :=
  ∃ T : (f.func '' U) → X, ∀ x : U, T (imagePoint f U x) = g.func x

theorem factor_iff (f g : Operator X bot) (U : Set X) :
    Factors f g U ↔ eqRel f U ⊆ eqRel g U := by
  classical
  constructor
  · rintro ⟨T,hT⟩ ⟨x,y⟩ ⟨hx,hy,he⟩
    refine ⟨hx,hy,?_⟩
    rw [← hT ⟨x,hx⟩, ← hT ⟨y,hy⟩]
    congr 1; exact Subtype.ext he
  · intro h
    let pick : (f.func '' U) → X := fun z => Classical.choose z.property
    have hp : ∀ z : f.func '' U, pick z ∈ U ∧ f.func (pick z) = z :=
      fun z => Classical.choose_spec z.property
    refine ⟨fun z => g.func (pick z), ?_⟩
    intro x
    exact (h (show (pick (imagePoint f U x),(x : X)) ∈ eqRel f U from
      ⟨(hp _).1,x.property,(hp _).2⟩)).2.2

theorem factors_both (f g : Operator X bot) (U : Set X) :
    Factors f g U ∧ Factors g f U ↔ eqRel f U = eqRel g U := by
  rw [factor_iff, factor_iff]; exact Set.Subset.antisymm_iff.symm

def imageSetoid (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot) (U : Set X) :
    Setoid (f.func '' U) where
  r a b := GaugeZeroRelated d a b
  iseqv :=
    ⟨fun a i => (hd i).dist_self a,
     fun h i => (hd i).symm _ _ |>.trans (h i),
     fun h h' i => zero_trans (hd i) (h i) (h' i)⟩
abbrev ImageQuotient (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot) (U : Set X) :=
  Quotient (imageSetoid d hd f U)
def quotientPoint (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot) (U : Set X) (x : U) :
    ImageQuotient d hd f U := Quotient.mk _ (imagePoint f U x)
def QuotientFactors (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f g : Operator X bot) (U : Set X) : Prop :=
  ∃ T : ImageQuotient d hd f U → ImageQuotient d hd g U,
    ∀ x : U, T (quotientPoint d hd f U x) = quotientPoint d hd g U x

theorem quotient_factor_iff (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f g : Operator X bot) (U : Set X) :
    QuotientFactors d hd f g U ↔ zeroRel d f U ⊆ zeroRel d g U := by
  classical
  constructor
  · rintro ⟨T,hT⟩ ⟨x,y⟩ ⟨hx,hy,h⟩
    refine ⟨hx,hy,?_⟩
    have he : quotientPoint d hd f U ⟨x,hx⟩ = quotientPoint d hd f U ⟨y,hy⟩ :=
      Quotient.sound h
    exact Quotient.exact (show quotientPoint d hd g U ⟨x,hx⟩ = quotientPoint d hd g U ⟨y,hy⟩ by
      rw [← hT, ← hT, he])
  · intro h
    let pick : (f.func '' U) → U := fun z =>
      ⟨Classical.choose z.property, (Classical.choose_spec z.property).1⟩
    have hp : ∀ z : f.func '' U, f.func (pick z) = z :=
      fun z => (Classical.choose_spec z.property).2
    let F : (f.func '' U) → ImageQuotient d hd g U := fun z => quotientPoint d hd g U (pick z)
    have hF : ∀ a b, (imageSetoid d hd f U).r a b → F a = F b := by
      intro a b hab
      apply Quotient.sound
      apply (h (show ((pick a : X), (pick b : X)) ∈ zeroRel d f U from
        ⟨(pick a).property, (pick b).property, by simpa [hp] using hab⟩)).2.2
    refine ⟨Quotient.lift F hF, ?_⟩
    intro x
    apply Quotient.sound
    apply (h (show ((pick (imagePoint f U x) : X),(x : X)) ∈ zeroRel d f U from
      ⟨(pick _).property,x.property,?_⟩)).2.2
    intro i
    rw [hp]; exact (hd i).dist_self _

theorem quotient_factors_both (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f g : Operator X bot) (U : Set X) :
    QuotientFactors d hd f g U ∧ QuotientFactors d hd g f U ↔ zeroRel d f U = zeroRel d g U := by
  rw [quotient_factor_iff, quotient_factor_iff]; exact Set.Subset.antisymm_iff.symm

theorem separated_rel (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot) (U : Set X)
    (hs : ∀ a ∈ f.func '' U, ∀ b ∈ f.func '' U, GaugeZeroRelated d a b → a = b) :
    eqRel f U = zeroRel d f U := by
  ext ⟨x,y⟩; constructor
  · rintro ⟨hx,hy,h⟩; exact ⟨hx,hy,fun i => by rw [h]; exact (hd i).dist_self _⟩
  · rintro ⟨hx,hy,h⟩; exact ⟨hx,hy,hs _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ h⟩

theorem separated_criteria (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f g : Operator X bot) (U : Set X)
    (hf : ∀ a ∈ f.func '' U, ∀ b ∈ f.func '' U, GaugeZeroRelated d a b → a = b)
    (hg : ∀ a ∈ g.func '' U, ∀ b ∈ g.func '' U, GaugeZeroRelated d a b → a = b) :
    (Factors f g U ↔ QuotientFactors d hd f g U) ∧
    (Factors f g U ∧ Factors g f U ↔ QuotientFactors d hd f g U ∧ QuotientFactors d hd g f U) := by
  simp only [factor_iff, quotient_factor_iff, separated_rel d hd f U hf, separated_rel d hd g U hg]
  exact ⟨trivial,trivial⟩

theorem fiber_preorder_refl (d : I → X → X → ENNReal) (U : Set X) (f : Operator X bot) :
    fiberPreorder d U f f := Set.Subset.rfl
theorem fiber_preorder_trans (d : I → X → X → ENNReal) (U : Set X) {f g h : Operator X bot}
    (hfg : fiberPreorder d U f g) (hgh : fiberPreorder d U g h) : fiberPreorder d U f h := hfg.trans hgh

theorem relation_chain {α : Type} (R : ℕ → Set α) (m : ℕ)
    (h : ∀ k < m, R k ⊆ R (k+1)) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ m) : R a ⊆ R b := by
  induction b, hab using Nat.le_induction with
  | base => exact Set.Subset.rfl
  | succ b hab ih => exact (ih (by omega)).trans (h b (by omega))

theorem relation_chain_strict {α : Type} (R : ℕ → Set α) (m : ℕ)
    (h : ∀ k < m, R k ⊆ R (k+1)) {k : ℕ} (hk : k < m) (hs : R k ⊂ R (k+1)) :
    R 0 ⊂ R m ∧ ∃ z, z ∈ R m ∧ z ∉ R 0 := by
  obtain ⟨z,hz,hz'⟩ := Set.exists_of_ssubset hs
  have hm : z ∈ R m := relation_chain R m h (by omega) le_rfl hz
  have h0 : z ∉ R 0 := fun hh => hz' (relation_chain R m h (by omega) (by omega) hh)
  exact ⟨Set.ssubset_iff_subset_ne.mpr ⟨relation_chain R m h (by omega) le_rfl,
    fun he => h0 (he ▸ hm)⟩, z, hm, h0⟩

end Chapter3
