import formal_oet.vol_01.ch_01_foundations.metric_entropy
import formal_oet.vol_01.ch_02_operator_bounds.decoupling
import formal_oet.vol_01.ch_02_operator_bounds.single_channel

/-
Mathematical source: Zhe Li (Glen Li / glenzli), The Operator Evolution Theory,
Volume I, Chapter 3, https://glenzli.com/books/oet/, CC BY 4.0.
ORCID https://orcid.org/0009-0006-6536-3453.
This file is a new Lean formalization of that source.
-/
namespace Chapter3
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set
noncomputable section
variable {X I : Type} {bot : X}

def constComponents (d : I → X → X → ENNReal) (f : Operator X bot) (U : Set X) : Set I :=
  {i | ∀ x ∈ U, ∀ y ∈ U, d i (f.func x) (f.func y) = 0}
def idComponents (d : I → X → X → ENNReal) (f : Operator X bot) (U : Set X) : Set I :=
  {i | i ∉ constComponents d f U ∧ ∀ x ∈ U, d i (f.func x) x = 0}
def actComponents (d : I → X → X → ENNReal) (f : Operator X bot) (U : Set X) : Set I :=
  (constComponents d f U ∪ idComponents d f U)ᶜ

theorem component_partition (d : I → X → X → ENNReal) (f : Operator X bot) (U : Set X) :
    constComponents d f U ∪ idComponents d f U ∪ actComponents d f U = univ ∧
    Disjoint (constComponents d f U) (idComponents d f U) ∧
    Disjoint (constComponents d f U ∪ idComponents d f U) (actComponents d f U) := by
  classical
  simp only [actComponents, union_compl_self, true_and]
  constructor
  · exact disjoint_left.mpr (by intro i hi hj; exact hj.1 hi)
  · exact disjoint_compl_right

theorem zero_trans {d : X → X → ENNReal}
    (tri : ∀ x y z, d x z ≤ d x y + d y z) {x y z : X}
    (hxy : d x y = 0) (hyz : d y z = 0) : d x z = 0 := by
  apply le_antisymm _ (zero_le _)
  simpa [hxy, hyz] using tri x y z

theorem zero_replace {d : X → X → ENNReal}
    (sym : ∀ x y, d x y = d y x)
    (tri : ∀ x y z, d x z ≤ d x y + d y z)
    {a b c e : X} (hab : d a b = 0) (hce : d c e = 0) : d a c = d b e := by
  apply le_antisymm
  · calc
      d a c ≤ d a b + d b c := tri _ _ _
      _ ≤ d a b + (d b e + d e c) := add_le_add le_rfl (tri _ _ _)
      _ = d b e := by rw [hab, sym e c, hce]; simp
  · calc
      d b e ≤ d b a + d a e := tri _ _ _
      _ ≤ d b a + (d a c + d c e) := add_le_add le_rfl (tri _ _ _)
      _ = d a c := by rw [sym b a, hab, hce]; simp

theorem const_zero_row [Fintype I] (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) {i : I} (hi : i ∈ constComponents d f U) :
    ∀ x ∈ U, ∀ y ∈ U,
      d i (f.func x) (f.func y) ≤ ∑ k : I, (0 : ENNReal) * d k x y := by
  intro x hx y hy
  simp [hi x hx y hy]

theorem const_colip_zero [Fintype I] (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) {i k : I}
    (hi : i ∈ constComponents d f U) (K : I → I → ENNReal)
    (hK : IsCoLipMatrix d f U K)
    (hpos : ∃ x ∈ U, ∃ y ∈ U, 0 < d k x y) : K k i = 0 := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hpos
  exact colip_entry_eq_zero_of_output_zero_input_pos d f U K k i x y hK hx hy
    (hi x hx y hy) hxy

theorem id_isometry (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (f : Operator X bot) (U : Set X) {i : I} (hi : i ∈ idComponents d f U) :
    ∀ x ∈ U, ∀ y ∈ U, d i (f.func x) (f.func y) = d i x y := by
  intro x hx y hy
  exact zero_replace (hd i).symm (hd i).triangle (hi.2 x hx) (hi.2 y hy)

theorem outer_const (d : I → X → X → ENNReal)
    (f g : Operator X bot) (U : Set X) :
    constComponents d g (f.func '' U) ⊆ constComponents d (g * f) U := by
  intro i hi x hx y hy
  exact hi _ (mem_image_of_mem _ hx) _ (mem_image_of_mem _ hy)

theorem id_comp (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (f g : Operator X bot) (U : Set X) :
    idComponents d f U ∩ idComponents d g (f.func '' U) ⊆ idComponents d (g * f) U := by
  intro i hi
  constructor
  · intro hc
    apply hi.1.1
    intro x hx y hy
    rw [← id_isometry d hd g (f.func '' U) hi.2 _ (mem_image_of_mem _ hx)
      _ (mem_image_of_mem _ hy)]
    exact hc x hx y hy
  · intro x hx
    exact zero_trans (hd i).triangle
      (hi.2.2 _ (mem_image_of_mem _ hx)) (hi.1.2 x hx)

theorem act_comp (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (f g : Operator X bot) (U : Set X) :
    actComponents d (g * f) U ⊆ actComponents d f U ∪ actComponents d g (f.func '' U) := by
  classical
  intro i hi
  by_contra hn
  have hf : i ∈ constComponents d f U ∪ idComponents d f U := by
    exact Classical.not_not.mp ((not_or.mp hn).1)
  have hg : i ∈ constComponents d g (f.func '' U) ∪ idComponents d g (f.func '' U) := by
    exact Classical.not_not.mp ((not_or.mp hn).2)
  apply hi
  rcases hg with hgc | hgi
  · exact Or.inl (outer_const d f g U hgc)
  · rcases hf with hfc | hfi
    · left
      intro x hx y hy
      change d i (g.func (f.func x)) (g.func (f.func y)) = 0
      rw [id_isometry d hd g (f.func '' U) hgi _ (mem_image_of_mem _ hx)
        _ (mem_image_of_mem _ hy)]
      exact hfc x hx y hy
    · exact Or.inr (id_comp d hd f g U ⟨hfi, hgi⟩)

def run : List (Operator X bot) → Operator X bot
  | [] => 1
  | f :: fs => run fs * f
def chainActs (d : I → X → X → ENNReal) : List (Operator X bot) → Set X → Set I
  | [], _ => ∅
  | f :: fs, U => actComponents d f U ∪ chainActs d fs (f.func '' U)
def chainDomains : List (Operator X bot) → Set X → Prop
  | [], U => U ⊆ dom (1 : Operator X bot)
  | f :: fs, U => U ⊆ dom f ∧ chainDomains fs (f.func '' U)

theorem dom_comp (f g : Operator X bot) :
    dom (g * f) = {x | x ∈ dom f ∧ f.func x ∈ dom g} := by
  ext x
  change g.func (f.func x) ≠ bot ↔ f.func x ≠ bot ∧ g.func (f.func x) ≠ bot
  constructor
  · intro h
    refine ⟨?_, h⟩
    intro he
    apply h
    rw [he, g.preserves_bot]
  · exact And.right

theorem chain_domains (fs : List (Operator X bot)) (U : Set X)
    (h : U ⊆ dom (run fs)) : chainDomains fs U := by
  induction fs generalizing U with
  | nil => exact h
  | cons f fs ih =>
    have hh : ∀ x ∈ U, x ∈ dom f ∧ f.func x ∈ dom (run fs) := by
      intro x hx
      exact (Set.ext_iff.mp (dom_comp f (run fs)) x).mp (h hx)
    exact ⟨fun x hx => (hh x hx).1, ih _ (by
      rintro _ ⟨x, hx, rfl⟩; exact (hh x hx).2)⟩

theorem act_identity (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (U : Set X) :
    actComponents d (1 : Operator X bot) U = ∅ := by
  classical
  ext i
  simp only [mem_empty_iff_false, iff_false]
  intro h
  apply h
  by_cases hc : i ∈ constComponents d (1 : Operator X bot) U
  · exact Or.inl hc
  · exact Or.inr ⟨hc, fun x _ => (hd i).dist_self x⟩

theorem act_chain (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (fs : List (Operator X bot)) (U : Set X) :
    actComponents d (run fs) U ⊆ chainActs d fs U := by
  induction fs generalizing U with
  | nil => simp [run, chainActs, act_identity d hd]
  | cons f fs ih =>
    exact (act_comp d hd f (run fs) U).trans (union_subset_union subset_rfl (ih _))

theorem const_comp_diagonal [Fintype I] (d : I → X → X → ENNReal)
    (f g : Operator X bot) (U : Set X) {j : I}
    (hc : j ∈ constComponents d f U) (L : I → I → ENNReal)
    (hL : IsLipMatrix d g (f.func '' U) L) (hrow : ∀ k, k ≠ j → L k j = 0) :
    j ∈ constComponents d (g * f) U := by
  intro x hx y hy
  have h := lip_bound_of_single_input_row d g (f.func '' U) L j j hL hrow
    _ (mem_image_of_mem _ hx) _ (mem_image_of_mem _ hy)
  exact le_antisymm (by simpa [hc x hx y hy] using h) (zero_le _)

def fiber (d : I → X → X → ENNReal) (f : Operator X bot) (J : Set I)
    (y : X) (U : Set X) : Set X :=
  {x | x ∈ U ∧ subfamily_pseudometric d J (f.func x) y = 0}
def componentFiber (d : I → X → X → ENNReal) (f : Operator X bot)
    (i : I) (y : X) (U : Set X) : Set X := {x | x ∈ U ∧ d i (f.func x) y = 0}

theorem sup_zero_iff (d : I → X → X → ENNReal) (J : Set I) (x y : X) :
    subfamily_pseudometric d J x y = 0 ↔ ∀ j ∈ J, d j x y = 0 := by
  constructor
  · intro h j hj
    exact le_antisymm ((le_iSup (fun k : J => d k.1 x y) ⟨j,hj⟩).trans (le_of_eq h)) (zero_le _)
  · intro h
    apply le_antisymm _ (zero_le _)
    exact iSup_le (fun j => le_of_eq (h j.1 j.2))

theorem fiber_inter (d : I → X → X → ENNReal) (f : Operator X bot)
    (J : Set I) (hJ : J.Nonempty) (y : X) (U : Set X) :
    fiber d f J y U = ⋂ j ∈ J, componentFiber d f j y U := by
  ext x
  simp only [fiber, componentFiber, mem_setOf_eq, sup_zero_iff, mem_iInter]
  constructor
  · exact fun h j hj => ⟨h.1, h.2 j hj⟩
  · intro h
    exact ⟨(h hJ.choose hJ.choose_spec).1, fun j hj => (h j hj).2⟩

theorem fiber_antitone (d : I → X → X → ENNReal) (f : Operator X bot)
    {J K : Set I} (h : J ⊆ K) (y : X) (U : Set X) :
    fiber d f K y U ⊆ fiber d f J y U := by
  intro x hx
  exact ⟨hx.1, (sup_zero_iff _ _ _ _).mpr
    (fun j hj => (sup_zero_iff _ _ _ _).mp hx.2 j (h hj))⟩

theorem fiber_singleton (d : I → X → X → ENNReal) (f : Operator X bot)
    (i : I) (y : X) (U : Set X) :
    fiber d f {i} y U = componentFiber d f i y U := by
  simp [fiber, componentFiber, subfamily_pseudometric_singleton]

theorem fiber_full_subset (d : I → X → X → ENNReal) (f : Operator X bot)
    (i : I) (y : X) (U : Set X) :
    fiber d f univ y U ⊆ componentFiber d f i y U := by
  rw [← fiber_singleton]
  exact fiber_antitone d f (subset_univ _) y U

theorem fiber_target (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot)
    (J : Set I) {y z : X} (h : subfamily_pseudometric d J y z = 0) (U : Set X) :
    fiber d f J y U = fiber d f J z U := by
  have hz := (sup_zero_iff _ _ _ _).mp h
  ext x
  simp only [fiber, mem_setOf_eq, sup_zero_iff]
  constructor
  · intro hx
    exact ⟨hx.1, fun j hj => zero_trans (hd j).triangle (hx.2 j hj) (hz j hj)⟩
  · intro hx
    exact ⟨hx.1, fun j hj => zero_trans (hd j).triangle (hx.2 j hj)
      (by rw [(hd j).symm]; exact hz j hj)⟩

theorem fiber_nonempty (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot)
    (J : Set I) (U : Set X) {y : X} (hy : y ∈ f.func '' U) :
    (fiber d f J y U).Nonempty := by
  obtain ⟨x, hx, rfl⟩ := hy
  exact ⟨x, hx, (sup_zero_iff _ _ _ _).mpr (fun j _ => (hd j).dist_self _)⟩

theorem fiber_cover (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot)
    (J : Set I) (U : Set X) : (⋃ y ∈ f.func '' U, fiber d f J y U) = U := by
  ext x
  simp only [mem_iUnion]
  constructor
  · rintro ⟨y, _, hx⟩; exact hx.1
  · intro hx
    exact ⟨f.func x, mem_image_of_mem _ hx, hx,
      (sup_zero_iff _ _ _ _).mpr (fun j _ => (hd j).dist_self _)⟩

theorem fiber_equal_or_disjoint (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot)
    (J : Set I) (y z : X) (U : Set X) :
    fiber d f J y U = fiber d f J z U ∨ Disjoint (fiber d f J y U) (fiber d f J z U) := by
  classical
  by_cases hh : Disjoint (fiber d f J y U) (fiber d f J z U)
  · exact Or.inr hh
  · left
    obtain ⟨x, hx, hz⟩ := not_disjoint_iff.mp hh
    apply fiber_target d hd
    apply (sup_zero_iff _ _ _ _).mpr
    intro j hj
    exact zero_trans (hd j).triangle
      (by rw [(hd j).symm]; exact (sup_zero_iff _ _ _ _).mp hx.2 j hj)
      ((sup_zero_iff _ _ _ _).mp hz.2 j hj)

theorem id_fiber (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot)
    (U : Set X) {i : I} (hi : i ∈ idComponents d f U) (y : X) :
    componentFiber d f i y U = {x | x ∈ U ∧ d i x y = 0} := by
  ext x
  constructor
  · intro hx
    exact ⟨hx.1, by
      rw [← zero_replace (hd i).symm (hd i).triangle (hi.2 x hx.1) ((hd i).dist_self y)]
      exact hx.2⟩
  · intro hx
    exact ⟨hx.1, by
      rw [zero_replace (hd i).symm (hd i).triangle (hi.2 x hx.1) ((hd i).dist_self y)]
      exact hx.2⟩

theorem const_fiber (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) {i : I} (hi : i ∈ constComponents d f U)
    {y : X} (hy : y ∈ f.func '' U) : componentFiber d f i y U = U := by
  obtain ⟨a, ha, rfl⟩ := hy
  ext x
  exact ⟨And.left, fun hx => ⟨hx, hi x hx a ha⟩⟩

theorem const_fiber_empty (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot)
    (U : Set X) {i : I} (hi : i ∈ constComponents d f U)
    {y z : X} (hz : z ∈ f.func '' U) (hy : 0 < d i y z) :
    componentFiber d f i y U = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hh : d i (f.func x) z = 0 := by
    have hm : x ∈ componentFiber d f i z U := (const_fiber d f U hi hz).symm ▸ hx.1
    exact hm.2
  exact (ne_of_gt hy) (zero_trans (hd i).triangle
    (by rw [(hd i).symm]; exact hx.2) hh)

def pointRelation (f : Operator X bot) (U : Set X) : Set (X × X) :=
  {p | p.1 ∈ U ∧ p.2 ∈ U ∧ f.func p.1 = f.func p.2}
def zeroRelation (d : I → X → X → ENNReal) (f : Operator X bot) (U : Set X) : Set (X × X) :=
  {p | p.1 ∈ U ∧ p.2 ∈ U ∧ GaugeZeroRelated d (f.func p.1) (f.func p.2)}
def fiberPreorder (d : I → X → X → ENNReal) (U : Set X)
    (f g : Operator X bot) : Prop := zeroRelation d f U ⊆ zeroRelation d g U

theorem zeroRelation_fiber (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot)
    (U : Set X) {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    (x,y) ∈ zeroRelation d f U ↔ y ∈ fiber d f univ (f.func x) U := by
  simp only [zeroRelation, mem_setOf_eq, hx, hy, true_and, fiber, sup_zero_iff]
  constructor <;> intro h i
  · intro _; rw [(hd i).symm]; exact h i
  · rw [(hd i).symm]; exact h i (mem_univ _)

theorem factor_surjective {S A B : Type} (a : S → A) (b : S → B)
    (hs : Function.Surjective a) :
    (∃ T : A → B, ∀ x, T (a x) = b x) ↔
      ∀ x y, a x = a y → b x = b y := by
  constructor
  · rintro ⟨T, hT⟩ x y hxy
    rw [← hT x, ← hT y, hxy]
  · intro h
    refine ⟨fun z => b (Classical.choose (hs z)), ?_⟩
    intro x
    exact h _ x (Classical.choose_spec (hs (a x)))

def imageInclusion (f : Operator X bot) (U : Set X) (x : U) : f.func '' U :=
  ⟨f.func x, mem_image_of_mem _ x.2⟩
theorem imageInclusion_surjective (f : Operator X bot) (U : Set X) :
    Function.Surjective (imageInclusion f U) := by
  rintro ⟨_, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

theorem point_factor_iff (f g : Operator X bot) (U : Set X) :
    (∃ T : (f.func '' U) → X, ∀ x : U, T (imageInclusion f U x) = g.func x) ↔
      pointRelation f U ⊆ pointRelation g U := by
  rw [factor_surjective _ _ (imageInclusion_surjective f U)]
  constructor
  · intro h p hp
    exact ⟨hp.1, hp.2.1, h ⟨p.1, hp.1⟩ ⟨p.2, hp.2.1⟩ (Subtype.ext hp.2.2)⟩
  · intro h x y hxy
    exact (h (show (x.val,y.val) ∈ pointRelation f U from
      ⟨x.2, y.2, congrArg Subtype.val hxy⟩)).2.2

theorem point_factor_both_iff (f g : Operator X bot) (U : Set X) :
    ((∃ T : (f.func '' U) → X, ∀ x : U, T (imageInclusion f U x) = g.func x) ∧
     (∃ T : (g.func '' U) → X, ∀ x : U, T (imageInclusion g U x) = f.func x)) ↔
      pointRelation f U = pointRelation g U := by
  rw [point_factor_iff, point_factor_iff, subset_antisymm_iff]

def imageSetoid (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot) (U : Set X) :
    Setoid (f.func '' U) where
  r a b := GaugeZeroRelated d a.val b.val
  iseqv := by
    have h := gauge_zero_related_equivalence d (fun i => (hd i).dist_self)
      (fun i => (hd i).symm) (fun i => (hd i).triangle)
    exact ⟨fun _ => h.refl _, fun hxy => h.symm hxy, fun hxy hyz => h.trans hxy hyz⟩
def imageQuotient (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot) (U : Set X) :=
  Quotient (imageSetoid d hd f U)
def imageClass (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot) (U : Set X)
    (x : U) : imageQuotient d hd f U := Quotient.mk _ (imageInclusion f U x)

theorem imageClass_surjective (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot) (U : Set X) :
    Function.Surjective (imageClass d hd f U) := by
  intro q
  induction q using Quotient.inductionOn with
  | _ a =>
    obtain ⟨x, rfl⟩ := imageInclusion_surjective f U a
    exact ⟨x, rfl⟩

theorem quotient_factor_iff (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f g : Operator X bot) (U : Set X) :
    (∃ T : imageQuotient d hd f U → imageQuotient d hd g U,
      ∀ x : U, T (imageClass d hd f U x) = imageClass d hd g U x) ↔
      zeroRelation d f U ⊆ zeroRelation d g U := by
  rw [factor_surjective _ _ (imageClass_surjective d hd f U)]
  constructor
  · intro h p hp
    exact ⟨hp.1, hp.2.1, Quotient.exact
      (h ⟨p.1, hp.1⟩ ⟨p.2, hp.2.1⟩ (Quotient.sound hp.2.2))⟩
  · intro h x y hxy
    exact Quotient.sound (h (show (x.val,y.val) ∈ zeroRelation d f U from
      ⟨x.2, y.2, Quotient.exact hxy⟩)).2.2

theorem quotient_factor_both_iff (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f g : Operator X bot) (U : Set X) :
    ((∃ T : imageQuotient d hd f U → imageQuotient d hd g U,
      ∀ x : U, T (imageClass d hd f U x) = imageClass d hd g U x) ∧
     (∃ T : imageQuotient d hd g U → imageQuotient d hd f U,
      ∀ x : U, T (imageClass d hd g U x) = imageClass d hd f U x)) ↔
      zeroRelation d f U = zeroRelation d g U := by
  rw [quotient_factor_iff, quotient_factor_iff, subset_antisymm_iff]

theorem separated_relations (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot) (U : Set X)
    (hs : ∀ a ∈ f.func '' U, ∀ b ∈ f.func '' U, GaugeZeroRelated d a b → a = b) :
    pointRelation f U = zeroRelation d f U := by
  ext ⟨x,y⟩
  constructor
  · rintro ⟨hx, hy, he⟩
    exact ⟨hx, hy, fun i => by rw [he]; exact (hd i).dist_self _⟩
  · rintro ⟨hx, hy, he⟩
    exact ⟨hx, hy, hs _ (mem_image_of_mem _ hx) _ (mem_image_of_mem _ hy) he⟩

theorem fiber_preorder_refl (d : I → X → X → ENNReal) (U : Set X) (f : Operator X bot) :
    fiberPreorder d U f f := subset_rfl
theorem fiber_preorder_trans (d : I → X → X → ENNReal) (U : Set X)
    {f g h : Operator X bot} (hfg : fiberPreorder d U f g) (hgh : fiberPreorder d U g h) :
    fiberPreorder d U f h := hfg.trans hgh

theorem relation_chain {A : Type} (R : ℕ → Set A) {m : ℕ}
    (h : ∀ k < m, R k ⊆ R (k+1)) {a b : ℕ} (hab : a ≤ b) (hbm : b ≤ m) : R a ⊆ R b := by
  induction b, hab using Nat.le_induction with
  | base => exact subset_rfl
  | @succ b hab ih => exact (ih (by omega)).trans (h b (by omega))

theorem relation_chain_strict {A : Type} (R : ℕ → Set A) {m r : ℕ}
    (h : ∀ k < m, R k ⊆ R (k+1)) (hr : r < m) (hs : R r ⊂ R (r+1)) :
    R 0 ⊂ R m ∧ ∃ p, p ∈ R m ∧ p ∉ R 0 := by
  obtain ⟨p, hp, hn⟩ := exists_of_ssubset hs
  have hp' := relation_chain R h (a := r+1) (b := m) (by omega) le_rfl hp
  have hn' : p ∉ R 0 := fun hh => hn (relation_chain R h (Nat.zero_le r) (by omega) hh)
  exact ⟨ssubset_iff_subset_ne.mpr ⟨relation_chain R h (Nat.zero_le m) le_rfl,
    fun he => hn' (he.symm ▸ hp')⟩, p, hp', hn'⟩

end
end Chapter3
