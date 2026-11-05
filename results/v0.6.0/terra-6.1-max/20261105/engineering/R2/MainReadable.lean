import formal_oet.vol_01.ch_01_foundations.metric_entropy
import formal_oet.vol_01.ch_02_operator_bounds.decoupling

/-!
  A partial formalization of Chapter 3 of Zhe Li, The Operator Evolution
  Theory, Volume I, v1.0.0, https://glenzli.com/books/oet/, CC BY 4.0.
  The alignment file identifies which obligations are complete.
-/

namespace Chapter3

open Set
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds

variable {X I : Type} {bot : X}

def constComponents (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) : Set I :=
  {i | ∀ x ∈ U, ∀ y ∈ U, d i (f.func x) (f.func y) = 0}

def identityComponents (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) : Set I :=
  {i | i ∉ constComponents d f U ∧ ∀ x ∈ U, d i (f.func x) x = 0}

def activeComponents (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) : Set I :=
  (constComponents d f U ∪ identityComponents d f U)ᶜ

theorem components_partition (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (i : I) :
    (i ∈ constComponents d f U ∨ i ∈ identityComponents d f U ∨
      i ∈ activeComponents d f U) ∧
    ¬ (i ∈ constComponents d f U ∧ i ∈ identityComponents d f U) ∧
    ¬ (i ∈ constComponents d f U ∧ i ∈ activeComponents d f U) ∧
    ¬ (i ∈ identityComponents d f U ∧ i ∈ activeComponents d f U) := by
  classical
  simp only [identityComponents, activeComponents, mem_setOf_eq, mem_compl_iff,
    mem_union] 
  tauto

theorem const_zero_row [Fintype I] (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (i : I)
    (hi : i ∈ constComponents d f U) :
    ∀ x ∈ U, ∀ y ∈ U, d i (f.func x) (f.func y) ≤
      ∑ k : I, (0 : ENNReal) * d k x y := by
  intro x hx y hy
  simp [hi x hx y hy]

theorem const_colip_zero [Fintype I] (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (i k : I) (K : I → I → ENNReal)
    (hi : i ∈ constComponents d f U) (hK : IsCoLipMatrix d f U K)
    (x y : X) (hx : x ∈ U) (hy : y ∈ U) (hpos : 0 < d k x y) : K k i = 0 :=
  colip_entry_eq_zero_of_output_zero_input_pos d f U K k i x y hK hx hy
    (hi x hx y hy) hpos

theorem dist_eq_of_zero_endpoints (d : X → X → ENNReal)
    (hs : ∀ x y, d x y = d y x)
    (ht : ∀ x y z, d x z ≤ d x y + d y z)
    {a b c e : X} (hab : d a b = 0) (hce : d c e = 0) :
    d a c = d b e := by
  have hba : d b a = 0 := by rw [hs b a, hab]
  have hec : d e c = 0 := by rw [hs e c, hce]
  apply le_antisymm
  · calc
      d a c ≤ d a b + d b c := ht a b c
      _ ≤ d a b + (d b e + d e c) := add_le_add le_rfl (ht b e c)
      _ = d b e := by simp [hab, hec]
  · calc
      d b e ≤ d b a + d a e := ht b a e
      _ ≤ d b a + (d a c + d c e) := add_le_add le_rfl (ht a c e)
      _ = d a c := by simp [hba, hce]

theorem identity_preserves_distance (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (i : I)
    (hd : ExtendedPseudoMetric X bot (d i))
    (hi : i ∈ identityComponents d f U) :
    ∀ x ∈ U, ∀ y ∈ U, d i (f.func x) (f.func y) = d i x y := by
  intro x hx y hy
  exact dist_eq_of_zero_endpoints (d i) hd.symm hd.triangle (hi.2 x hx) (hi.2 y hy)

theorem outer_const (d : I → X → X → ENNReal)
    (f g : Operator X bot) (U : Set X) (i : I)
    (h : i ∈ constComponents d g (f.func '' U)) :
    i ∈ constComponents d (g * f) U := by
  intro x hx y hy
  exact h (f.func x) ⟨x, hx, rfl⟩ (f.func y) ⟨y, hy, rfl⟩

theorem inner_const_of_single_row [Fintype I] (d : I → X → X → ENNReal)
    (f g : Operator X bot) (U : Set X) (j : I) (L : I → I → ENNReal)
    (hc : j ∈ constComponents d f U)
    (hL : IsLipMatrix d g (f.func '' U) L)
    (hrow : ∀ k, k ≠ j → L k j = 0) :
    j ∈ constComponents d (g * f) U := by
  intro x hx y hy
  apply le_antisymm _ (zero_le _)
  have h := lip_bound_of_single_input_row d g (f.func '' U) L j j hL hrow
      (f.func x) ⟨x, hx, rfl⟩ (f.func y) ⟨y, hy, rfl⟩
  simpa [hc x hx y hy] using h

theorem identity_comp (d : I → X → X → ENNReal)
    (f g : Operator X bot) (U : Set X) (i : I)
    (hd : ExtendedPseudoMetric X bot (d i))
    (hf : i ∈ identityComponents d f U)
    (hg : i ∈ identityComponents d g (f.func '' U)) :
    i ∈ identityComponents d (g * f) U := by
  constructor
  · intro hc
    apply hf.1
    intro x hx y hy
    have heq := identity_preserves_distance d g (f.func '' U) i hd hg
      (f.func x) ⟨x, hx, rfl⟩ (f.func y) ⟨y, hy, rfl⟩
    exact heq.symm.trans (hc x hx y hy)
  · intro x hx
    apply le_antisymm _ (zero_le _)
    calc
      d i ((g * f).func x) x ≤ d i (g.func (f.func x)) (f.func x) + d i (f.func x) x :=
        hd.triangle _ _ _
      _ = 0 := by rw [hg.2 _ ⟨x, hx, rfl⟩, hf.2 x hx, add_zero]

theorem active_comp (d : I → X → X → ENNReal)
    (f g : Operator X bot) (U : Set X) (i : I)
    (hd : ExtendedPseudoMetric X bot (d i)) :
    i ∈ activeComponents d (g * f) U →
      i ∈ activeComponents d f U ∨ i ∈ activeComponents d g (f.func '' U) := by
  classical
  intro hc
  by_contra h
  have hf : i ∈ constComponents d f U ∨ i ∈ identityComponents d f U := by
    have h1 := (not_or.mp h).1
    simp only [activeComponents, mem_compl_iff, mem_union] at h1
    tauto
  have hg : i ∈ constComponents d g (f.func '' U) ∨
      i ∈ identityComponents d g (f.func '' U) := by
    have h2 := (not_or.mp h).2
    simp only [activeComponents, mem_compl_iff, mem_union] at h2
    tauto
  have hnot : i ∉ constComponents d (g * f) U ∧
      i ∉ identityComponents d (g * f) U := by simpa [activeComponents] using hc
  rcases hg with hg | hg
  · exact hnot.1 (outer_const d f g U i hg)
  · rcases hf with hf | hf
    · apply hnot.1
      intro x hx y hy
      have heq := identity_preserves_distance d g (f.func '' U) i hd hg
        (f.func x) ⟨x, hx, rfl⟩ (f.func y) ⟨y, hy, rfl⟩
      exact heq.trans (hf x hx y hy)
    · exact hnot.2 (identity_comp d f g U i hd hf hg)

def seqOp : List (Operator X bot) → Operator X bot
  | [] => 1
  | f :: fs => seqOp fs * f

def seqActive (d : I → X → X → ENNReal) :
    List (Operator X bot) → Set X → Set I
  | [], _ => ∅
  | f :: fs, U => activeComponents d f U ∪ seqActive d fs (f.func '' U)

theorem seqOp_eq_reverse_prod (fs : List (Operator X bot)) :
    seqOp fs = fs.reverse.prod := by
  induction fs with
  | nil => rfl
  | cons f fs ih => simp [seqOp, ih, List.prod_append]

theorem identity_not_active (d : I → X → X → ENNReal)
    (U : Set X) (i : I) (hself : ∀ x, d i x x = 0) :
    i ∉ activeComponents d (1 : Operator X bot) U := by
  classical
  simp only [activeComponents, mem_compl_iff, mem_union, not_not]
  by_cases hc : i ∈ constComponents d (1 : Operator X bot) U
  · exact Or.inl hc
  · right
    exact ⟨hc, fun x _ => hself x⟩

theorem active_seq (d : I → X → X → ENNReal)
    (fs : List (Operator X bot)) (U : Set X) (i : I)
    (hd : ExtendedPseudoMetric X bot (d i)) :
    i ∈ activeComponents d (seqOp fs) U → i ∈ seqActive d fs U := by
  induction fs generalizing U with
  | nil =>
      intro h
      exact (identity_not_active d U i hd.dist_self h).elim
  | cons f fs ih =>
      intro h
      rcases active_comp d f (seqOp fs) U i hd h with h | h
      · exact Or.inl h
      · exact Or.inr (ih (f.func '' U) h)

def fiber (d : I → X → X → ENNReal) (f : Operator X bot)
    (J : Set I) (y : X) (U : Set X) : Set X :=
  {x | x ∈ U ∧ subfamily_pseudometric d J (f.func x) y = 0}

def componentFiber (d : I → X → X → ENNReal) (f : Operator X bot)
    (j : I) (y : X) (U : Set X) : Set X :=
  {x | x ∈ U ∧ d j (f.func x) y = 0}

theorem subfamily_zero_iff (d : I → X → X → ENNReal)
    (J : Set I) (x y : X) :
    subfamily_pseudometric d J x y = 0 ↔ ∀ j ∈ J, d j x y = 0 := by
  constructor
  · intro h j hj
    apply le_antisymm _ (zero_le _)
    calc
      d j x y ≤ subfamily_pseudometric d J x y :=
        le_iSup (fun k : {k // k ∈ J} => d k.1 x y) ⟨j, hj⟩
      _ = 0 := h
  · intro h
    apply le_antisymm _ (zero_le _)
    apply iSup_le
    intro j
    exact le_of_eq (h j.1 j.2)

theorem fiber_components (d : I → X → X → ENNReal) (f : Operator X bot)
    (J : Set I) (y : X) (U : Set X) :
    fiber d f J y U = {x | x ∈ U ∧ ∀ j ∈ J, x ∈ componentFiber d f j y U} := by
  ext x
  simp only [fiber, componentFiber, mem_setOf_eq, subfamily_zero_iff]
  constructor
  · rintro ⟨hx, h⟩
    exact ⟨hx, fun j hj => ⟨hx, h j hj⟩⟩
  · rintro ⟨hx, h⟩
    exact ⟨hx, fun j hj => (h j hj).2⟩

theorem fiber_intersection (d : I → X → X → ENNReal) (f : Operator X bot)
    (J : Set I) (y : X) (U : Set X) (hJ : J.Nonempty) :
    fiber d f J y U = ⋂ j ∈ J, componentFiber d f j y U := by
  rw [fiber_components]
  ext x
  simp only [mem_setOf_eq, mem_iInter]
  constructor
  · exact And.right
  · intro h
    obtain ⟨j, hj⟩ := hJ
    exact ⟨(h j hj).1, h⟩

theorem fiber_antitone (d : I → X → X → ENNReal) (f : Operator X bot)
    (J K : Set I) (y : X) (U : Set X) (hJK : J ⊆ K) :
    fiber d f K y U ⊆ fiber d f J y U := by
  intro x hx
  exact ⟨hx.1, (subfamily_zero_iff d J _ _).2
    (fun j hj => (subfamily_zero_iff d K _ _).1 hx.2 j (hJK hj))⟩

theorem fiber_singleton (d : I → X → X → ENNReal) (f : Operator X bot)
    (j : I) (y : X) (U : Set X) :
    fiber d f {j} y U = componentFiber d f j y U := by
  ext x
  simp [fiber, componentFiber, subfamily_pseudometric_singleton]

theorem fiber_all_subset (d : I → X → X → ENNReal) (f : Operator X bot)
    (j : I) (y : X) (U : Set X) :
    fiber d f univ y U ⊆ componentFiber d f j y U := by
  rw [← fiber_singleton]
  exact fiber_antitone d f _ _ _ _ (subset_univ _)

theorem fiber_target_zero (d : I → X → X → ENNReal) (f : Operator X bot)
    (J : Set I) (y z : X) (U : Set X)
    (hd : ∀ j, ExtendedPseudoMetric X bot (d j))
    (hyz : subfamily_pseudometric d J y z = 0) :
    fiber d f J y U = fiber d f J z U := by
  ext x
  simp only [fiber, mem_setOf_eq, subfamily_zero_iff]
  constructor <;> intro h <;> refine ⟨h.1, ?_⟩ <;> intro j hj
  · apply le_antisymm _ (zero_le _)
    calc
      d j (f.func x) z ≤ d j (f.func x) y + d j y z := (hd j).triangle _ _ _
      _ = 0 := by rw [h.2 j hj, (subfamily_zero_iff d J y z).1 hyz j hj, add_zero]
  · apply le_antisymm _ (zero_le _)
    calc
      d j (f.func x) y ≤ d j (f.func x) z + d j z y := (hd j).triangle _ _ _
      _ = 0 := by rw [h.2 j hj, (hd j).symm z y,
        (subfamily_zero_iff d J y z).1 hyz j hj, add_zero]

theorem fiber_image_cover (d : I → X → X → ENNReal) (f : Operator X bot)
    (J : Set I) (U : Set X) (hd : ∀ j, ExtendedPseudoMetric X bot (d j)) :
    (∀ y ∈ f.func '' U, (fiber d f J y U).Nonempty) ∧
    (⋃ y ∈ f.func '' U, fiber d f J y U) = U := by
  constructor
  · rintro y ⟨x, hx, rfl⟩
    exact ⟨x, hx, (subfamily_zero_iff d J _ _).2 (fun j _ => (hd j).dist_self _)⟩
  · ext x
    constructor
    · intro hx
      obtain ⟨y, _, hxy⟩ := Set.mem_iUnion₂.mp hx
      exact hxy.1
    · intro hx
      apply Set.mem_iUnion₂.mpr
      exact ⟨f.func x, ⟨x, hx, rfl⟩, hx,
        (subfamily_zero_iff d J _ _).2 (fun j _ => (hd j).dist_self _)⟩

theorem fiber_equal_or_disjoint (d : I → X → X → ENNReal) (f : Operator X bot)
    (J : Set I) (U : Set X) (y z : X)
    (hd : ∀ j, ExtendedPseudoMetric X bot (d j)) :
    fiber d f J y U = fiber d f J z U ∨
      Disjoint (fiber d f J y U) (fiber d f J z U) := by
  classical
  by_cases h : Disjoint (fiber d f J y U) (fiber d f J z U)
  · exact Or.inr h
  · left
    have hex : ∃ x, x ∈ fiber d f J y U ∧ x ∈ fiber d f J z U :=
      Set.not_disjoint_iff.mp h
    obtain ⟨x, hx, hx'⟩ := hex
    apply fiber_target_zero d f J y z U hd
    apply (subfamily_zero_iff d J y z).2
    intro j hj
    apply le_antisymm _ (zero_le _)
    calc
      d j y z ≤ d j y (f.func x) + d j (f.func x) z := (hd j).triangle _ _ _
      _ = 0 := by rw [(hd j).symm y (f.func x),
        (subfamily_zero_iff d J _ _).1 hx.2 j hj,
        (subfamily_zero_iff d J _ _).1 hx'.2 j hj, add_zero]

theorem identity_component_fiber (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (i : I) (y : X)
    (hd : ExtendedPseudoMetric X bot (d i))
    (hi : i ∈ identityComponents d f U) :
    componentFiber d f i y U = {x | x ∈ U ∧ d i x y = 0} := by
  ext x
  simp only [componentFiber, mem_setOf_eq]
  constructor <;> intro h <;> refine ⟨h.1, ?_⟩
  · have hdist := dist_eq_of_zero_endpoints (d i) hd.symm hd.triangle (hi.2 x h.1) (hd.dist_self y)
    exact hdist.symm.trans h.2
  · have hdist := dist_eq_of_zero_endpoints (d i) hd.symm hd.triangle (hi.2 x h.1) (hd.dist_self y)
    exact hdist.trans h.2

theorem constant_component_fiber (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (i : I) (y₀ y : X)
    (hd : ExtendedPseudoMetric X bot (d i))
    (hc : i ∈ constComponents d f U) (hy₀ : y₀ ∈ f.func '' U) :
    componentFiber d f i y₀ U = U ∧
      (0 < d i y y₀ → componentFiber d f i y U = ∅) := by
  obtain ⟨z, hz, rfl⟩ := hy₀
  constructor
  · ext x
    simp only [componentFiber, mem_setOf_eq]
    constructor
    · exact And.left
    · intro hx
      exact ⟨hx, hc x hx z hz⟩
  · intro hpos
    ext x
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hx
    have hzero : d i y (f.func z) = 0 := by
      apply le_antisymm _ (zero_le _)
      calc
        d i y (f.func z) ≤ d i y (f.func x) + d i (f.func x) (f.func z) := hd.triangle _ _ _
        _ = 0 := by rw [hd.symm y (f.func x), hx.2, hc x hx.1 z hz, add_zero]
    exact (ne_of_gt hpos) hzero

def pointRelation (f : Operator X bot) (U : Set X) : Set (X × X) :=
  {p | p.1 ∈ U ∧ p.2 ∈ U ∧ f.func p.1 = f.func p.2}

def zeroRelation (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) : Set (X × X) :=
  {p | p.1 ∈ U ∧ p.2 ∈ U ∧ GaugeZeroRelated d (f.func p.1) (f.func p.2)}

def fiberPreorder (d : I → X → X → ENNReal)
    (U : Set X) (f g : Operator X bot) : Prop :=
  zeroRelation d f U ⊆ zeroRelation d g U

theorem zeroRelation_fiber (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    (x, y) ∈ zeroRelation d f U ↔ y ∈ fiber d f univ (f.func x) U := by
  simp only [zeroRelation, fiber, mem_setOf_eq, GaugeZeroRelated,
    subfamily_zero_iff, Set.mem_univ, forall_const]
  constructor
  · rintro ⟨_, _, h⟩
    exact ⟨hy, fun i => (hd i).symm _ _ |>.trans (h i)⟩
  · rintro ⟨_, h⟩
    exact ⟨hx, hy, fun i => (hd i).symm _ _ |>.trans (h i)⟩

theorem fiberPreorder_refl (d : I → X → X → ENNReal) (U : Set X)
    (f : Operator X bot) : fiberPreorder d U f f := Set.Subset.rfl

theorem fiberPreorder_trans (d : I → X → X → ENNReal) (U : Set X)
    (f g h : Operator X bot) (hfg : fiberPreorder d U f g)
    (hgh : fiberPreorder d U g h) : fiberPreorder d U f h := hfg.trans hgh

theorem fiberPreorder_chain (d : I → X → X → ENNReal) (U : Set X)
    (f : ℕ → Operator X bot) (hstep : ∀ n, fiberPreorder d U (f n) (f (n+1)))
    {a b : ℕ} (hab : a ≤ b) : fiberPreorder d U (f a) (f b) := by
  induction b, hab using Nat.le_induction with
  | base => exact fiberPreorder_refl d U (f a)
  | succ n _ ih => exact fiberPreorder_trans d U _ _ _ ih (hstep n)

theorem fiberPreorder_chain_strict (d : I → X → X → ENNReal) (U : Set X)
    (f : ℕ → Operator X bot) (hstep : ∀ n, fiberPreorder d U (f n) (f (n+1)))
    {r m : ℕ} (hr : r + 1 ≤ m)
    (hstrict : zeroRelation d (f r) U ⊂ zeroRelation d (f (r+1)) U) :
    zeroRelation d (f 0) U ⊂ zeroRelation d (f m) U ∧
      ∃ p, p ∈ zeroRelation d (f m) U ∧ p ∉ zeroRelation d (f 0) U := by
  have h0 : zeroRelation d (f 0) U ⊆ zeroRelation d (f r) U :=
    fiberPreorder_chain d U f hstep (Nat.zero_le r)
  have hm : zeroRelation d (f (r+1)) U ⊆ zeroRelation d (f m) U :=
    fiberPreorder_chain d U f hstep hr
  obtain ⟨p, hp, hpnot⟩ := Set.exists_of_ssubset hstrict
  have hp' : p ∈ zeroRelation d (f m) U := hm hp
  have hpnot' : p ∉ zeroRelation d (f 0) U := fun h => hpnot (h0 h)
  exact ⟨⟨(h0.trans hstrict.1).trans hm, fun h => hpnot' (h hp')⟩,
    ⟨p, hp', hpnot'⟩⟩

def imageType (f : Operator X bot) (U : Set X) := {z // z ∈ f.func '' U}

def imagePoint (f : Operator X bot) (U : Set X) (x : X) (hx : x ∈ U) : imageType f U :=
  ⟨f.func x, x, hx, rfl⟩

def hasImageFactor (f g : Operator X bot) (U : Set X) : Prop :=
  ∃ T : imageType f U → X, ∀ x (hx : x ∈ U), T (imagePoint f U x hx) = g.func x

theorem image_factor_iff (f g : Operator X bot) (U : Set X) :
    hasImageFactor f g U ↔ pointRelation f U ⊆ pointRelation g U := by
  classical
  constructor
  · rintro ⟨T, hT⟩ ⟨x, y⟩ hxy
    refine ⟨hxy.1, hxy.2.1, ?_⟩
    have heq : imagePoint f U x hxy.1 = imagePoint f U y hxy.2.1 := Subtype.ext hxy.2.2
    calc
      g.func x = T (imagePoint f U x hxy.1) := (hT x hxy.1).symm
      _ = T (imagePoint f U y hxy.2.1) := congrArg T heq
      _ = g.func y := hT y hxy.2.1
  · intro h
    let pick : imageType f U → X := fun z => Classical.choose z.2
    have hpick : ∀ z : imageType f U, pick z ∈ U ∧ f.func (pick z) = z.1 := by
      intro z
      exact Classical.choose_spec z.2
    refine ⟨fun z => g.func (pick z), ?_⟩
    intro x hx
    have hp := hpick (imagePoint f U x hx)
    have hp' : (pick (imagePoint f U x hx), x) ∈ pointRelation f U := ⟨hp.1, hx, hp.2⟩
    exact (h hp').2.2

theorem image_factor_both_iff (f g : Operator X bot) (U : Set X) :
    (hasImageFactor f g U ∧ hasImageFactor g f U) ↔
      pointRelation f U = pointRelation g U := by
  rw [image_factor_iff, image_factor_iff]
  exact Set.Subset.antisymm_iff.symm

def imageZeroSetoid (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) : Setoid (imageType f U) where
  r a b := GaugeZeroRelated d a.1 b.1
  iseqv := by
    have h := gauge_zero_related_equivalence d (fun i => (hd i).dist_self)
      (fun i => (hd i).symm) (fun i => (hd i).triangle)
    constructor
    · intro a
      exact h.refl a.1
    · intro a b hab
      exact h.symm hab
    · intro a b c hab hbc
      exact h.trans hab hbc

def imageQuotient (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) :=
  Quotient (imageZeroSetoid d f U hd)

def imageClass (d : I → X → X → ENNReal) (f : Operator X bot) (U : Set X)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (x : X) (hx : x ∈ U) :
    imageQuotient d f U hd := Quotient.mk _ (imagePoint f U x hx)

def hasQuotientFactor (d : I → X → X → ENNReal)
    (f g : Operator X bot) (U : Set X)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) : Prop :=
  ∃ T : imageQuotient d f U hd → imageQuotient d g U hd,
    ∀ x (hx : x ∈ U), T (imageClass d f U hd x hx) = imageClass d g U hd x hx

theorem quotient_factor_iff (d : I → X → X → ENNReal)
    (f g : Operator X bot) (U : Set X)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) :
    hasQuotientFactor d f g U hd ↔ fiberPreorder d U f g := by
  classical
  constructor
  · rintro ⟨T, hT⟩ ⟨x, y⟩ hxy
    refine ⟨hxy.1, hxy.2.1, ?_⟩
    have heq : imageClass d f U hd x hxy.1 = imageClass d f U hd y hxy.2.1 :=
      Quotient.sound hxy.2.2
    have hout : imageClass d g U hd x hxy.1 = imageClass d g U hd y hxy.2.1 := by
      rw [← hT x hxy.1, ← hT y hxy.2.1, heq]
    exact Quotient.exact hout
  · intro h
    let pick : imageType f U → X := fun z => Classical.choose z.2
    have hpick : ∀ z : imageType f U, pick z ∈ U ∧ f.func (pick z) = z.1 := by
      intro z
      exact Classical.choose_spec z.2
    let T₀ : imageType f U → imageQuotient d g U hd := fun z =>
      imageClass d g U hd (pick z) (hpick z).1
    have hwell : ∀ a b : imageType f U,
        (imageZeroSetoid d f U hd).r a b → T₀ a = T₀ b := by
      intro a b hab
      apply Quotient.sound
      change GaugeZeroRelated d (g.func (pick a)) (g.func (pick b))
      have hp : (pick a, pick b) ∈ zeroRelation d f U := by
        refine ⟨(hpick a).1, (hpick b).1, ?_⟩
        simpa [(hpick a).2, (hpick b).2] using hab
      exact (h hp).2.2
    refine ⟨Quotient.lift T₀ hwell, ?_⟩
    intro x hx
    apply Quotient.sound
    change GaugeZeroRelated d (g.func (pick (imagePoint f U x hx))) (g.func x)
    have hp : (pick (imagePoint f U x hx), x) ∈ zeroRelation d f U := by
      refine ⟨(hpick (imagePoint f U x hx)).1, hx, ?_⟩
      rw [(hpick (imagePoint f U x hx)).2]
      intro i
      exact (hd i).dist_self _
    exact (h hp).2.2

theorem quotient_factor_both_iff (d : I → X → X → ENNReal)
    (f g : Operator X bot) (U : Set X)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) :
    (hasQuotientFactor d f g U hd ∧ hasQuotientFactor d g f U hd) ↔
      zeroRelation d f U = zeroRelation d g U := by
  rw [quotient_factor_iff, quotient_factor_iff]
  exact Set.Subset.antisymm_iff.symm

def separatingOn (d : I → X → X → ENNReal) (A : Set X) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, GaugeZeroRelated d x y → x = y

theorem pointRelation_eq_zeroRelation (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (hsep : separatingOn d (f.func '' U)) :
    pointRelation f U = zeroRelation d f U := by
  ext ⟨x, y⟩
  simp only [pointRelation, zeroRelation, mem_setOf_eq]
  constructor
  · rintro ⟨hx, hy, hxy⟩
    refine ⟨hx, hy, ?_⟩
    intro i
    rw [hxy, (hd i).dist_self]
  · rintro ⟨hx, hy, hxy⟩
    exact ⟨hx, hy, hsep _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy⟩

theorem separated_factor_criteria (d : I → X → X → ENNReal)
    (f g : Operator X bot) (U : Set X)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (hf : separatingOn d (f.func '' U)) (hg : separatingOn d (g.func '' U)) :
    (hasImageFactor f g U ↔ hasQuotientFactor d f g U hd) ∧
    ((hasImageFactor f g U ∧ hasImageFactor g f U) ↔
      (hasQuotientFactor d f g U hd ∧ hasQuotientFactor d g f U hd)) := by
  simp only [image_factor_iff, quotient_factor_iff,
    pointRelation_eq_zeroRelation d f U hd hf,
    pointRelation_eq_zeroRelation d g U hd hg, fiberPreorder]
  exact ⟨trivial, trivial⟩

def admissibleRadius (din dout : X → X → ENNReal) (f : Operator X bot)
    (y : X) (U : Set X) (r : ENNReal) : Prop :=
  0 < r ∧ r < ⊤ ∧ ∀ x ∈ U, din x y < r → dout (f.func x) (f.func y) = 0

noncomputable def zeroRadius (din dout : X → X → ENNReal)
    (f : Operator X bot) (y : X) (U : Set X) : ENNReal :=
  sSup {r | admissibleRadius din dout f y U r}

noncomputable def uniformRadius (din dout : X → X → ENNReal)
    (f : Operator X bot) (A U : Set X) : ENNReal :=
  ⨅ y ∈ A, zeroRadius din dout f y U

noncomputable def zeroMatrix (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (i j : I) : ENNReal :=
  uniformRadius (d i) (d j) f U U

theorem admissibleRadius_iff_ball (din dout : X → X → ENNReal)
    (f : Operator X bot) (y : X) (U : Set X) (r : ENNReal) :
    admissibleRadius din dout f y U r ↔
      0 < r ∧ r < ⊤ ∧ ball din y r ∩ U ⊆
        {x | x ∈ U ∧ dout (f.func x) (f.func y) = 0} := by
  simp only [admissibleRadius, ball, Set.subset_def, mem_inter_iff, mem_setOf_eq]
  constructor
  · rintro ⟨hpos, hfin, h⟩
    refine ⟨hpos, hfin, ?_⟩
    rintro x ⟨hxy, hx⟩
    exact ⟨hx, h x hx hxy⟩
  · rintro ⟨hpos, hfin, h⟩
    refine ⟨hpos, hfin, ?_⟩
    intro x hx hxy
    exact (h x ⟨hxy, hx⟩).2

theorem admissibleRadius_iff_fiber (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (J : Set I) (i : I) (y : X) (r : ENNReal) :
    admissibleRadius (d i) (subfamily_pseudometric d J) f y U r ↔
      0 < r ∧ r < ⊤ ∧ ball (d i) y r ∩ U ⊆ fiber d f J (f.func y) U := by
  exact admissibleRadius_iff_ball _ _ _ _ _ _

theorem zeroRadius_empty_admissibles (din dout : X → X → ENNReal)
    (f : Operator X bot) (y : X) (U : Set X)
    (h : ∀ r, ¬ admissibleRadius din dout f y U r) : zeroRadius din dout f y U = 0 := by
  have hempty : {r | admissibleRadius din dout f y U r} = ∅ := by
    ext r
    simp [h r]
  simp [zeroRadius, hempty]

theorem radius_ge_admissible (din dout : X → X → ENNReal)
    (f : Operator X bot) (y : X) (U : Set X) (r : ENNReal)
    (hr : admissibleRadius din dout f y U r) : r ≤ zeroRadius din dout f y U :=
  le_sSup hr

theorem radius_strict_witness (din dout : X → X → ENNReal)
    (f : Operator X bot) (y : X) (U : Set X) (t : ENNReal)
    (h : t < zeroRadius din dout f y U) :
    ∃ r, admissibleRadius din dout f y U r ∧ t < r :=
  lt_sSup_iff.mp h

theorem radius_zero_output (din dout : X → X → ENNReal)
    (f : Operator X bot) (y x : X) (U : Set X)
    (hs : ∀ a b, din a b = din b a) (hx : x ∈ U)
    (h : din y x < zeroRadius din dout f y U) : dout (f.func x) (f.func y) = 0 := by
  obtain ⟨r, hr, hlt⟩ := radius_strict_witness din dout f y U _ h
  apply hr.2.2 x hx
  rw [hs x y]
  exact hlt

theorem fiber_zero_output (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (j : I) (y x : X)
    (hd : ExtendedPseudoMetric X bot (d j))
    (hx : x ∈ componentFiber d f j (f.func y) U) :
    d j (f.func y) (f.func x) = 0 := by
  rw [hd.symm _ _, hx.2]

theorem fiber_comp_zero_output (d : I → X → X → ENNReal)
    (f g : Operator X bot) (U₂ : Set X) (j : I) (x x' : X)
    (hd : ExtendedPseudoMetric X bot (d j))
    (hx : f.func x ∈ U₂) (hx' : f.func x' ∈ U₂)
    (hfib : f.func x' ∈ componentFiber d g j (g.func (f.func x)) U₂) :
    d j ((g * f).func x) ((g * f).func x') = 0 := by
  exact fiber_zero_output d g U₂ j (f.func x) (f.func x') hd hfib

theorem radius_domain_antitone (din dout : X → X → ENNReal)
    (f : Operator X bot) (y : X) (A B : Set X) (hBA : B ⊆ A) :
    zeroRadius din dout f y A ≤ zeroRadius din dout f y B := by
  apply sSup_le
  intro r hr
  apply le_sSup
  exact ⟨hr.1, hr.2.1, fun x hx hdist => hr.2.2 x (hBA hx) hdist⟩

theorem uniformRadius_domain_antitone (din dout : X → X → ENNReal)
    (f : Operator X bot) (A B : Set X) (hBA : B ⊆ A) :
    uniformRadius din dout f A A ≤ uniformRadius din dout f B B := by
  apply le_iInf₂
  intro y hy
  exact (iInf₂_le y (hBA hy)).trans (radius_domain_antitone din dout f y A B hBA)

theorem uniform_zero_output (din dout : X → X → ENNReal)
    (f : Operator X bot) (A : Set X) (y x : X)
    (hs : ∀ a b, din a b = din b a)
    (hx : x ∈ A) (hy : y ∈ A)
    (h : din y x < uniformRadius din dout f A A) :
    dout (f.func x) (f.func y) = 0 :=
  radius_zero_output din dout f y x A hs hx (lt_of_lt_of_le h (iInf₂_le y hy))

theorem uniform_output_separation (din dout : X → X → ENNReal)
    (f : Operator X bot) (A : Set X) (y x : X)
    (hs : ∀ a b, din a b = din b a)
    (hx : x ∈ A) (hy : y ∈ A)
    (h : 0 < dout (f.func x) (f.func y)) :
    uniformRadius din dout f A A ≤ din y x := by
  by_contra hn
  have hz := uniform_zero_output din dout f A y x hs hx hy (lt_of_not_ge hn)
  exact (ne_of_gt h) hz

theorem constant_radius_top (din dout : X → X → ENNReal)
    (f : Operator X bot) (U : Set X)
    (hc : ∀ x ∈ U, ∀ y ∈ U, dout (f.func x) (f.func y) = 0)
    (y : X) (hy : y ∈ U) : zeroRadius din dout f y U = ⊤ := by
  apply top_unique
  rw [← ENNReal.iSup_natCast]
  apply iSup_le
  intro n
  cases n with
  | zero => simp
  | succ n =>
      apply radius_ge_admissible
      refine ⟨?_, ENNReal.natCast_lt_top _, ?_⟩
      · exact_mod_cast Nat.zero_lt_succ n
      · intro x hx _
        exact hc x hx y hy

theorem constant_uniformRadius_top (din dout : X → X → ENNReal)
    (f : Operator X bot) (U : Set X)
    (hc : ∀ x ∈ U, ∀ y ∈ U, dout (f.func x) (f.func y) = 0) :
    uniformRadius din dout f U U = ⊤ := by
  apply top_unique
  apply le_iInf₂
  intro y hy
  rw [constant_radius_top din dout f U hc y hy]

theorem constant_subfamily_fiber (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (J : Set I)
    (hc : J ⊆ constComponents d f U) (y : X) (hy : y ∈ U) :
    fiber d f J (f.func y) U = U := by
  ext x
  simp only [fiber, mem_setOf_eq, subfamily_zero_iff]
  constructor
  · exact And.left
  · intro hx
    exact ⟨hx, fun j hj => hc hj x hx y hy⟩

theorem constant_subfamily_radius (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (J : Set I) (i : I)
    (hc : J ⊆ constComponents d f U) :
    (∀ y ∈ U, zeroRadius (d i) (subfamily_pseudometric d J) f y U = ⊤) ∧
      uniformRadius (d i) (subfamily_pseudometric d J) f U U = ⊤ := by
  have hzero : ∀ x ∈ U, ∀ y ∈ U,
      subfamily_pseudometric d J (f.func x) (f.func y) = 0 := by
    intro x hx y hy
    exact (subfamily_zero_iff d J _ _).2 (fun j hj => hc hj x hx y hy)
  exact ⟨fun y hy => constant_radius_top _ _ f U hzero y hy,
    constant_uniformRadius_top _ _ f U hzero⟩

theorem identity_image_fiber (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (i : I) (y : X)
    (hd : ExtendedPseudoMetric X bot (d i)) (hy : y ∈ U)
    (hi : i ∈ identityComponents d f U) :
    componentFiber d f i (f.func y) U = {x | x ∈ U ∧ d i x y = 0} := by
  ext x
  simp only [componentFiber, mem_setOf_eq]
  by_cases hx : x ∈ U
  · simp [hx, identity_preserves_distance d f U i hd hi x hx y hy]
  · simp [hx]

theorem identity_radius_lower (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (i : I) (y : X) (r : ENNReal)
    (hd : ExtendedPseudoMetric X bot (d i)) (hy : y ∈ U)
    (hi : i ∈ identityComponents d f U)
    (hr : 0 < r ∧ r < ⊤)
    (hball : ∀ x ∈ U, d i x y < r → d i x y = 0) :
    r ≤ zeroRadius (d i) (d i) f y U := by
  apply radius_ge_admissible
  refine ⟨hr.1, hr.2, ?_⟩
  intro x hx hxy
  rw [identity_preserves_distance d f U i hd hi x hx y hy]
  exact hball x hx hxy

structure ScaleFamily (X I : Type) where
  value : I → Set X → ENNReal
  monotone : ∀ i A B, A.Nonempty → B.Nonempty → A ⊆ B → value i A ≤ value i B

noncomputable def diameter (d : X → X → ENNReal) (A : Set X) : ENNReal :=
  ⨆ x ∈ A, ⨆ y ∈ A, d x y

theorem diameter_monotone (d : X → X → ENNReal) (A B : Set X) (h : A ⊆ B) :
    diameter d A ≤ diameter d B := by
  apply iSup_le
  intro x
  apply iSup_le
  intro hx
  apply iSup_le
  intro y
  apply iSup_le
  intro hy
  exact le_iSup_of_le x (le_iSup_of_le (h hx) (le_iSup_of_le y (le_iSup_of_le (h hy) le_rfl)))

noncomputable def diameterScale (d : I → X → X → ENNReal) : ScaleFamily X I where
  value i A := diameter (d i) A
  monotone i A B _ _ h := diameter_monotone (d i) A B h

noncomputable def thresholdType (σ : ScaleFamily X I)
    (d : I → X → X → ENNReal) (f : Operator X bot) (A : Set X)
    (τσ τN : ENNReal) (i j : I) : Bool × Bool :=
  (decide (σ.value i A < τσ), decide (τN ≤ zeroMatrix d f A i j))

theorem threshold_four (σ : ScaleFamily X I)
    (d : I → X → X → ENNReal) (f : Operator X bot) (A : Set X)
    (τσ τN : ENNReal) (i j : I) :
    thresholdType σ d f A τσ τN i j = (true, true) ∨
    thresholdType σ d f A τσ τN i j = (true, false) ∨
    thresholdType σ d f A τσ τN i j = (false, true) ∨
    thresholdType σ d f A τσ τN i j = (false, false) := by
  unfold thresholdType
  cases h1 : decide (σ.value i A < τσ) <;>
    cases h2 : decide (τN ≤ zeroMatrix d f A i j) <;> simp_all

theorem threshold_four_spec (σ : ScaleFamily X I)
    (d : I → X → X → ENNReal) (f : Operator X bot) (A : Set X)
    (τσ τN : ENNReal) (i j : I) :
    (thresholdType σ d f A τσ τN i j = (true, true) ↔
      σ.value i A < τσ ∧ τN ≤ zeroMatrix d f A i j) ∧
    (thresholdType σ d f A τσ τN i j = (true, false) ↔
      σ.value i A < τσ ∧ zeroMatrix d f A i j < τN) ∧
    (thresholdType σ d f A τσ τN i j = (false, true) ↔
      τσ ≤ σ.value i A ∧ τN ≤ zeroMatrix d f A i j) ∧
    (thresholdType σ d f A τσ τN i j = (false, false) ↔
      τσ ≤ σ.value i A ∧ zeroMatrix d f A i j < τN) := by
  simp [thresholdType, not_lt, not_le]

theorem threshold_scale_mono (σ : ScaleFamily X I) (A : Set X) (i : I)
    {τ τ' : ENNReal} (hτ : τ ≤ τ') :
    σ.value i A < τ → σ.value i A < τ' := fun h => lt_of_lt_of_le h hτ

theorem threshold_radius_antitone (r τ τ' : ENNReal) (hτ : τ ≤ τ') :
    τ' ≤ r → τ ≤ r := fun h => hτ.trans h

theorem scale_domain_mono (σ : ScaleFamily X I) (A B : Set X) (i : I)
    (hA : A.Nonempty) (hB : B.Nonempty) (hBA : B ⊆ A) :
    σ.value i B ≤ σ.value i A ∧ ∀ τ, σ.value i A < τ → σ.value i B < τ :=
  ⟨σ.monotone i B A hB hA hBA, fun _ h => lt_of_le_of_lt (σ.monotone i B A hB hA hBA) h⟩

def totallyBoundedAtAllScales (d : X → X → ENNReal) (U : Set X) : Prop :=
  ∀ ε : ENNReal, 0 < ε → ε < ⊤ → covering_number d ε U < ⊤

def entropyDifferenceValid (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (Jin Jout : Set I) (ε : ENNReal) : Prop :=
  U.Nonempty ∧ U ⊆ dom f ∧ Jin.Nonempty ∧ Jout.Nonempty ∧ 0 < ε ∧ ε < ⊤ ∧
    (covering_number (subfamily_pseudometric d Jin) ε U < ⊤ ∨
     covering_number (subfamily_pseudometric d Jout) ε (f.func '' U) < ⊤)

noncomputable def mappingEntropyDifference (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (Jin Jout : Set I) (ε : ENNReal)
    (_h : entropyDifferenceValid d f U Jin Jout ε) : EReal :=
  subfamily_metric_entropy d Jin ε U - subfamily_metric_entropy d Jout ε (f.func '' U)

theorem mappingEntropy_finite_values (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (Jin Jout : Set I) (ε : ENNReal)
    (h : entropyDifferenceValid d f U Jin Jout ε) (a b : ℝ)
    (ha : subfamily_metric_entropy d Jin ε U = (a : EReal))
    (hb : subfamily_metric_entropy d Jout ε (f.func '' U) = (b : EReal)) :
    mappingEntropyDifference d f U Jin Jout ε h = ((a - b : ℝ) : EReal) := by
  simp [mappingEntropyDifference, ha, hb, EReal.coe_sub]

theorem mappingEntropy_infinite_cases (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (Jin Jout : Set I) (ε : ENNReal)
    (h : entropyDifferenceValid d f U Jin Jout ε) (a b : ℝ) :
    (subfamily_metric_entropy d Jin ε U = ⊤ →
      subfamily_metric_entropy d Jout ε (f.func '' U) = (b : EReal) →
      mappingEntropyDifference d f U Jin Jout ε h = ⊤) ∧
    (subfamily_metric_entropy d Jin ε U = (a : EReal) →
      subfamily_metric_entropy d Jout ε (f.func '' U) = ⊤ →
      mappingEntropyDifference d f U Jin Jout ε h = ⊥) := by
  constructor <;> intro ha hb <;>
    simp [mappingEntropyDifference, ha, hb, EReal.top_sub_coe, EReal.sub_top]

theorem totallyBounded_iff_finite_nets (d : X → X → ENNReal) (U : Set X) :
    totallyBoundedAtAllScales d U ↔
      ∀ ε : ENNReal, 0 < ε → ε < ⊤ →
        ∃ S : Finset X, InternalEpsilonNet d ε U S := by
  classical
  constructor
  · intro h ε hε htop
    have hn : covering_number d ε U ≠ ⊤ := ne_of_lt (h ε hε htop)
    by_contra hno
    exact hn ((covering_number_eq_top_iff d ε U).2 hno)
  · intro h ε hε htop
    exact lt_top_iff_ne_top.mpr (fun heq =>
      (covering_number_eq_top_iff d ε U).1 heq (h ε hε htop))

theorem covering_image_le (din dout : X → X → ENNReal) (f : X → X)
    (B : Set X) (δ ε : ENNReal)
    (h : ∀ x ∈ B, ∀ c ∈ B, din x c < δ → dout (f x) (f c) < ε) :
    covering_number dout ε (f '' B) ≤ covering_number din δ B := by
  classical
  unfold covering_number
  apply le_iInf₂
  intro S hS
  let T := S.image f
  have hT : InternalEpsilonNet dout ε (f '' B) T := by
    constructor
    · intro z hz
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hz
      exact ⟨s, hS.1 hs, rfl⟩
    · intro z hz
      obtain ⟨x, hx, rfl⟩ := hz
      obtain ⟨c, hc, hxc⟩ := hS.2 x hx
      exact ⟨f c, Finset.mem_image.mpr ⟨c, hc, rfl⟩, h x hx c (hS.1 hc) hxc⟩
  calc
    (⨅ (T : Finset X) (_ : InternalEpsilonNet dout ε (f '' B) T), (T.card : ENNReal)) ≤
        (T.card : ENNReal) := iInf_le_of_le T (iInf_le_of_le hT le_rfl)
    _ ≤ (S.card : ENNReal) := by exact_mod_cast (Finset.card_image_le (s := S) (f := f))

theorem covering_preimage_le (din dout : X → X → ENNReal) (f : X → X) (fallback : X)
    (B : Set X) (δ ε : ENNReal)
    (h : ∀ x ∈ B, ∀ c ∈ B, dout (f x) (f c) < ε → din x c < δ) :
    covering_number din δ B ≤ covering_number dout ε (f '' B) := by
  classical
  let pick : X → X := fun z => if hz : z ∈ f '' B then Classical.choose hz else fallback
  have hpick : ∀ z ∈ f '' B, pick z ∈ B ∧ f (pick z) = z := by
    intro z hz
    dsimp only [pick]
    rw [dif_pos hz]
    exact Classical.choose_spec hz
  unfold covering_number
  apply le_iInf₂
  intro T hT
  let S := T.image pick
  have hS : InternalEpsilonNet din δ B S := by
    constructor
    · intro z hz
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hz
      exact (hpick t (hT.1 ht)).1
    · intro x hx
      obtain ⟨t, ht, hdist⟩ := hT.2 (f x) ⟨x, hx, rfl⟩
      refine ⟨pick t, Finset.mem_image.mpr ⟨t, ht, rfl⟩, ?_⟩
      apply h x hx (pick t) (hpick t (hT.1 ht)).1
      rwa [(hpick t (hT.1 ht)).2]
  calc
    (⨅ (S : Finset X) (_ : InternalEpsilonNet din δ B S), (S.card : ENNReal)) ≤
        (S.card : ENNReal) := iInf_le_of_le S (iInf_le_of_le hS le_rfl)
    _ ≤ (T.card : ENNReal) := by exact_mod_cast (Finset.card_image_le (s := T) (f := pick))

theorem zero_image_cover_one (d : X → X → ENNReal) (f : X → X)
    (U : Set X) (hU : U.Nonempty) (ε : ENNReal) (hε : 0 < ε)
    (hzero : ∀ x ∈ U, ∀ y ∈ U, d (f x) (f y) = 0) :
    covering_number d ε (f '' U) = 1 := by
  classical
  have hnonempty : (f '' U).Nonempty := hU.image f
  apply le_antisymm
  · obtain ⟨a, ha⟩ := hU
    have hnet : InternalEpsilonNet d ε (f '' U) {f a} := by
      constructor
      · intro c hc
        have : c = f a := Finset.mem_singleton.mp hc
        rw [this]
        exact ⟨a, ha, rfl⟩
      · intro c hc
        obtain ⟨x, hx, rfl⟩ := hc
        exact ⟨f a, Finset.mem_singleton_self _, by simpa [hzero x hx a ha] using hε⟩
    have hle : covering_number d ε (f '' U) ≤ (Finset.card {f a} : ENNReal) :=
      iInf_le_of_le _ (iInf_le_of_le hnet le_rfl)
    simpa using hle
  · exact one_le_covering_number_of_nonempty d ε (f '' U) hnonempty

theorem identity_cover_eq (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (i : I) (ε : ENNReal)
    (hd : ExtendedPseudoMetric X bot (d i))
    (hi : i ∈ identityComponents d f U) :
    covering_number (d i) ε (f.func '' U) = covering_number (d i) ε U ∧
    metric_entropy (d i) ε (f.func '' U) = metric_entropy (d i) ε U := by
  have hdist := identity_preserves_distance d f U i hd hi
  have hcover : covering_number (d i) ε (f.func '' U) = covering_number (d i) ε U := by
    apply le_antisymm
    · apply covering_image_le
      intro x hx y hy h
      rwa [hdist x hx y hy]
    · apply covering_preimage_le _ _ _ bot
      intro x hx y hy h
      rwa [hdist x hx y hy] at h
  exact ⟨hcover, congrArg log2_ereal hcover⟩

theorem uniform_threshold_fiber (din dout : X → X → ENNReal)
    (f : Operator X bot) (A : Set X) (τ : ENNReal)
    (hin : ∀ x y, din x y = din y x)
    (hτ : τ ≤ uniformRadius din dout f A A) (x : X) (hx : x ∈ A) :
    ball din x τ ∩ A ⊆ {y | y ∈ A ∧ dout (f.func y) (f.func x) = 0} := by
  rintro y ⟨hball, hy⟩
  refine ⟨hy, ?_⟩
  apply uniform_zero_output din dout f A x y hin hy hx
  rw [hin x y]
  exact lt_of_lt_of_le hball hτ

theorem uniform_threshold_cover (din dout : X → X → ENNReal)
    (f : Operator X bot) (A B : Set X) (τ ε : ENNReal)
    (hin : ∀ x y, din x y = din y x) (hBA : B ⊆ A)
    (hτ : τ ≤ uniformRadius din dout f A A) (hε : 0 < ε) :
    covering_number dout ε (f.func '' B) ≤ covering_number din τ B := by
  apply covering_image_le
  intro x hx c hc hdist
  have hz : dout (f.func x) (f.func c) = 0 := by
    apply uniform_zero_output din dout f A c x hin (hBA hx) (hBA hc)
    rw [hin c x]
    exact lt_of_lt_of_le hdist hτ
  simpa [hz] using hε

theorem diameter_upper (d : X → X → ENNReal) (A : Set X)
    (x y : X) (hx : x ∈ A) (hy : y ∈ A) : d x y ≤ diameter d A :=
  le_iSup_of_le x (le_iSup_of_le hx (le_iSup_of_le y (le_iSup_of_le hy le_rfl)))

theorem small_diameter_iff_constant (din dout : X → X → ENNReal)
    (f : Operator X bot) (A : Set X) (τσ τN : ENNReal)
    (hin : ∀ x y, din x y = din y x)
    (hout : ∀ x y, dout x y = dout y x)
    (hdiam : diameter din A < τσ) (hthreshold : τσ ≤ τN) :
    (τN ≤ uniformRadius din dout f A A) ↔
      (∀ x ∈ A, ∀ y ∈ A, dout (f.func x) (f.func y) = 0) := by
  constructor
  · intro h x hx y hy
    have hdist : din y x < uniformRadius din dout f A A :=
      lt_of_le_of_lt (diameter_upper din A y x hy hx)
        (lt_of_lt_of_le hdiam (hthreshold.trans h))
    exact uniform_zero_output din dout f A y x hin hx hy hdist
  · intro h
    rw [constant_uniformRadius_top din dout f A h]
    exact le_top

theorem small_diameter_cover_one (din dout : X → X → ENNReal)
    (f : Operator X bot) (A : Set X) (τσ τN ε : ENNReal)
    (hin : ∀ x y, din x y = din y x) (hout : ∀ x y, dout x y = dout y x)
    (hA : A.Nonempty) (hε : 0 < ε) (hdiam : diameter din A < τσ)
    (hthreshold : τσ ≤ τN) (hN : τN ≤ uniformRadius din dout f A A) :
    covering_number dout ε (f.func '' A) = 1 :=
  zero_image_cover_one dout f.func A hA ε hε
    ((small_diameter_iff_constant din dout f A τσ τN hin hout hdiam hthreshold).1 hN)

theorem positive_colip_radius_gap [Fintype I] (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (i j : I) (K : I → I → ENNReal)
    (hin : ExtendedPseudoMetric X bot (d i))
    (hK : IsCoLipMatrix d f U K) (hKpos : 0 < K i j)
    (y x : X) (hy : y ∈ U) (hx : x ∈ U)
    (hlt : d i x y < zeroRadius (d i) (d j) f y U) : d i x y = 0 := by
  have hz : d j (f.func x) (f.func y) = 0 := by
    apply radius_zero_output (d i) (d j) f y x U hin.symm hx
    rwa [hin.symm y x]
  exact positive_colip_entry_reflects_zero d f U K i j hK hKpos x hx y hy hz

theorem positive_colip_uniform_gap [Fintype I] (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (i j : I) (K : I → I → ENNReal)
    (hin : ExtendedPseudoMetric X bot (d i))
    (hK : IsCoLipMatrix d f U K) (hKpos : 0 < K i j)
    (x y : X) (hx : x ∈ U) (hy : y ∈ U) :
    d i x y = 0 ∨ uniformRadius (d i) (d j) f U U ≤ d i x y := by
  by_cases h : uniformRadius (d i) (d j) f U U ≤ d i x y
  · exact Or.inr h
  · left
    apply positive_colip_radius_gap d f U i j K hin hK hKpos y x hy hx
    exact lt_of_lt_of_le (lt_of_not_ge h) (iInf₂_le y hy)

theorem radius_output_mono (din dout₁ dout₂ : X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (y : X)
    (h : ∀ x ∈ U, dout₁ (f.func x) (f.func y) = 0 →
      dout₂ (f.func x) (f.func y) = 0) :
    zeroRadius din dout₁ f y U ≤ zeroRadius din dout₂ f y U := by
  apply sSup_le
  intro r hr
  apply le_sSup
  exact ⟨hr.1, hr.2.1, fun x hx hxy => h x hx (hr.2.2 x hx hxy)⟩

theorem uniform_subfamily_mono (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (J K : Set I) (i : I) (hJK : J ⊆ K) :
    uniformRadius (d i) (subfamily_pseudometric d K) f U U ≤
      uniformRadius (d i) (subfamily_pseudometric d J) f U U := by
  apply le_iInf₂
  intro y hy
  calc
    uniformRadius (d i) (subfamily_pseudometric d K) f U U ≤
        zeroRadius (d i) (subfamily_pseudometric d K) f y U := iInf₂_le y hy
    _ ≤ zeroRadius (d i) (subfamily_pseudometric d J) f y U := by
      apply radius_output_mono
      intro x _ hx
      apply (subfamily_zero_iff d J _ _).2
      intro j hj
      exact (subfamily_zero_iff d K _ _).1 hx j (hJK hj)

theorem uniform_comp_propagate (din dmid dout : X → X → ENNReal)
    (f g : Operator X bot) (U : Set X)
    (hprop : ∀ a ∈ f.func '' U, ∀ b ∈ f.func '' U,
      dmid a b = 0 → dout (g.func a) (g.func b) = 0) :
    uniformRadius din dmid f U U ≤ uniformRadius din dout (g * f) U U := by
  apply le_iInf₂
  intro y hy
  calc
    uniformRadius din dmid f U U ≤ zeroRadius din dmid f y U := iInf₂_le y hy
    _ ≤ zeroRadius din dout (g * f) y U := by
      apply sSup_le
      intro r hr
      apply le_sSup
      refine ⟨hr.1, hr.2.1, ?_⟩
      intro x hx hxy
      exact hprop (f.func x) ⟨x, hx, rfl⟩ (f.func y) ⟨y, hy, rfl⟩
        (hr.2.2 x hx hxy)

theorem radius_subfamily_inf (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (J : Set I) (i : I) (y : X) :
    zeroRadius (d i) (subfamily_pseudometric d J) f y U =
      ⨅ j : {j // j ∈ J}, zeroRadius (d i) (d j.1) f y U := by
  apply le_antisymm
  · apply le_iInf
    intro j
    apply radius_output_mono
    intro x _ h
    exact (subfamily_zero_iff d J _ _).1 h j.1 j.2
  · apply le_of_forall_lt
    intro r hr
    obtain ⟨s, hrs, hs⟩ := exists_between hr
    have hspos : 0 < s := lt_of_le_of_lt (zero_le r) hrs
    have hsfin : s < ⊤ := lt_of_lt_of_le hs le_top
    have hsvalid : admissibleRadius (d i) (subfamily_pseudometric d J) f y U s := by
      refine ⟨hspos, hsfin, ?_⟩
      intro x hx hdist
      apply (subfamily_zero_iff d J _ _).2
      intro j hj
      have hsj : s < zeroRadius (d i) (d j) f y U :=
        lt_of_lt_of_le hs (iInf_le (fun j : {j // j ∈ J} =>
          zeroRadius (d i) (d j.1) f y U) ⟨j, hj⟩)
      obtain ⟨t, ht, hst⟩ := radius_strict_witness (d i) (d j) f y U s hsj
      exact ht.2.2 x hx (lt_trans hdist hst)
    exact lt_of_lt_of_le hrs (radius_ge_admissible _ _ _ _ _ _ hsvalid)

theorem uniform_subfamily_inf (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (J : Set I) (i : I) :
    uniformRadius (d i) (subfamily_pseudometric d J) f U U =
      ⨅ j : {j // j ∈ J}, zeroMatrix d f U i j.1 := by
  unfold uniformRadius zeroMatrix
  simp_rw [radius_subfamily_inf]
  calc
    (⨅ y, ⨅ _ : y ∈ U, ⨅ j : {j // j ∈ J}, zeroRadius (d i) (d j.1) f y U) =
        ⨅ y, ⨅ j : {j // j ∈ J}, ⨅ _ : y ∈ U, zeroRadius (d i) (d j.1) f y U := by
      apply congrArg iInf
      funext y
      exact iInf_comm
    _ = ⨅ j : {j // j ∈ J}, ⨅ y, ⨅ _ : y ∈ U, zeroRadius (d i) (d j.1) f y U := iInf_comm

theorem uniform_subfamily_min_attained [Finite I] (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (J : Set I) (i : I) (hJ : J.Nonempty) :
    ∃ j ∈ J, uniformRadius (d i) (subfamily_pseudometric d J) f U U = zeroMatrix d f U i j ∧
      ∀ k ∈ J, zeroMatrix d f U i j ≤ zeroMatrix d f U i k := by
  letI : Nonempty {j // j ∈ J} := ⟨⟨hJ.choose, hJ.choose_spec⟩⟩
  obtain ⟨j, hj⟩ := exists_eq_ciInf_of_finite
    (f := fun j : {j // j ∈ J} => zeroMatrix d f U i j.1)
  refine ⟨j.1, j.2, ?_, ?_⟩
  · rw [uniform_subfamily_inf]
    exact hj.symm
  · intro k hk
    rw [hj]
    exact iInf_le (fun j : {j // j ∈ J} => zeroMatrix d f U i j.1) ⟨k, hk⟩

theorem radius_subfamily_min_attained [Finite I] (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (J : Set I) (i : I) (y : X) (hJ : J.Nonempty) :
    ∃ j ∈ J, zeroRadius (d i) (subfamily_pseudometric d J) f y U = zeroRadius (d i) (d j) f y U ∧
      ∀ k ∈ J, zeroRadius (d i) (d j) f y U ≤ zeroRadius (d i) (d k) f y U := by
  letI : Nonempty {j // j ∈ J} := ⟨⟨hJ.choose, hJ.choose_spec⟩⟩
  obtain ⟨j, hj⟩ := exists_eq_ciInf_of_finite
    (f := fun j : {j // j ∈ J} => zeroRadius (d i) (d j.1) f y U)
  refine ⟨j.1, j.2, ?_, ?_⟩
  · rw [radius_subfamily_inf]
    exact hj.symm
  · intro k hk
    rw [hj]
    exact iInf_le (fun j : {j // j ∈ J} => zeroRadius (d i) (d j.1) f y U) ⟨k, hk⟩

theorem uniform_comp_lip (din dmid dout : X → X → ENNReal)
    (f g : Operator X bot) (U : Set X) (L : ENNReal)
    (hmid : ∀ x y, dmid x y = dmid y x)
    (hlip : ∀ x ∈ U, ∀ y ∈ U, dmid (f.func x) (f.func y) ≤ L * din x y) :
    uniformRadius dmid dout g (f.func '' U) (f.func '' U) / L ≤
      uniformRadius din dout (g * f) U U := by
  apply le_iInf₂
  intro y hy
  apply le_of_forall_lt
  intro r hr
  obtain ⟨s, hrs, hs⟩ := exists_between hr
  have hspos : 0 < s := lt_of_le_of_lt (zero_le r) hrs
  have hsfin : s < ⊤ := lt_of_lt_of_le hs le_top
  have hvalid : admissibleRadius din dout (g * f) y U s := by
    refine ⟨hspos, hsfin, ?_⟩
    intro x hx hdist
    have hmul : L * din x y < uniformRadius dmid dout g (f.func '' U) (f.func '' U) :=
      ENNReal.mul_lt_of_lt_div' (lt_trans hdist hs)
    have hdist' : dmid (f.func y) (f.func x) <
        uniformRadius dmid dout g (f.func '' U) (f.func '' U) := by
      rw [hmid (f.func y) (f.func x)]
      exact lt_of_le_of_lt (hlip x hx y hy) hmul
    exact uniform_zero_output dmid dout g (f.func '' U) (f.func y) (f.func x) hmid
      ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩ hdist'
  exact lt_of_lt_of_le hrs (radius_ge_admissible _ _ _ _ _ _ hvalid)

theorem insufficient_uniform_radius_witness (din dout : X → X → ENNReal)
    (f : Operator X bot) (A : Set X) (α : ENNReal)
    (hα : 0 < α) (hαfin : α < ⊤)
    (hlt : uniformRadius din dout f A A < α) :
    ∃ x ∈ A, ∃ y ∈ A, ∃ ε : ENNReal,
      0 < ε ∧ ε < ⊤ ∧ din x y < α ∧ ε ≤ dout (f.func x) (f.func y) := by
  classical
  obtain ⟨y, hy, hyr⟩ := iInf_lt_iff.mp hlt |>.imp fun _ h => iInf_lt_iff.mp h
  have hn : ¬ admissibleRadius din dout f y A α := by
    intro ha
    exact (not_lt_of_ge (radius_ge_admissible din dout f y A α ha)) hyr
  have hex : ∃ x ∈ A, din x y < α ∧ dout (f.func x) (f.func y) ≠ 0 := by
    by_contra h
    apply hn
    refine ⟨hα, hαfin, ?_⟩
    intro x hx hdist
    by_contra hne
    exact h ⟨x, hx, hdist, hne⟩
  obtain ⟨x, hx, hdist, hne⟩ := hex
  have hpos : 0 < dout (f.func x) (f.func y) := pos_iff_ne_zero.mpr hne
  refine ⟨x, hx, y, hy, min (dout (f.func x) (f.func y)) 1, ?_, ?_, hdist, min_le_left _ _⟩
  · exact lt_min hpos zero_lt_one
  · exact lt_of_le_of_lt (min_le_right _ _) ENNReal.one_lt_top

theorem scalar_lip_cover (din dout : X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (L ε : ENNReal)
    (hlip : ∀ x ∈ U, ∀ y ∈ U, dout (f.func x) (f.func y) ≤ L * din x y) :
    covering_number dout ε (f.func '' U) ≤ covering_number din (ε / L) U := by
  apply covering_image_le
  intro x hx y hy hdist
  exact lt_of_le_of_lt (hlip x hx y hy) (ENNReal.mul_lt_of_lt_div' hdist)

theorem colip_cover [Fintype I] (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (i j : I) (K : I → I → ENNReal)
    (ε : ENNReal) (hK : IsCoLipMatrix d f U K)
    (hpos : 0 < K i j) (hfin : K i j < ⊤) :
    covering_number (d i) (ε / K i j) U ≤ covering_number (d j) ε (f.func '' U) := by
  classical
  apply covering_preimage_le _ _ _ bot
  intro x hx y hy hout
  apply (ENNReal.lt_div_iff_mul_lt (Or.inl (ne_of_gt hpos)) (Or.inl (ne_of_lt hfin))).2
  have hterm : K i j * d i x y ≤ ∑ k : I, K k j * d k x y :=
    Finset.single_le_sum (fun k _ => zero_le (K k j * d k x y)) (Finset.mem_univ i)
  have hbound := hterm.trans (hK.2.2 x hx y hy j)
  simpa [mul_comm] using lt_of_le_of_lt hbound hout

theorem factor_scalar_lip (d : X → X → ENNReal)
    (f g : Operator X bot) (U : Set X) (T : imageType f U → X)
    (KA LB : ENNReal) (hKA : 0 < KA) (hKAfin : KA < ⊤)
    (hT : ∀ x (hx : x ∈ U), T (imagePoint f U x hx) = g.func x)
    (hco : ∀ x ∈ U, ∀ y ∈ U, KA * d x y ≤ d (f.func x) (f.func y))
    (hlip : ∀ x ∈ U, ∀ y ∈ U, d (g.func x) (g.func y) ≤ LB * d x y) :
    ∀ a b : imageType f U, d (T a) (T b) ≤ (LB / KA) * d a.1 b.1 := by
  intro a b
  obtain ⟨x, hx, hxa⟩ := a.2
  obtain ⟨y, hy, hyb⟩ := b.2
  have ha : imagePoint f U x hx = a := Subtype.ext hxa
  have hb : imagePoint f U y hy = b := Subtype.ext hyb
  have hdiv : d x y ≤ d (f.func x) (f.func y) / KA := by
    apply (ENNReal.le_div_iff_mul_le (Or.inl (ne_of_gt hKA))
      (Or.inl (ne_of_lt hKAfin))).2
    simpa [mul_comm] using hco x hx y hy
  calc
    d (T a) (T b) = d (g.func x) (g.func y) := by rw [← ha, ← hb, hT x hx, hT y hy]
    _ ≤ LB * d x y := hlip x hx y hy
    _ ≤ LB * (d (f.func x) (f.func y) / KA) := mul_le_mul_left' hdiv LB
    _ = (LB / KA) * d a.1 b.1 := by
      rw [← hxa, ← hyb]
      simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

theorem point_constant_self_comp (f : Operator X bot) (U : Set X) (v : X)
    (hv : ∀ x ∈ U, f.func x = v) :
    (∀ x ∈ U, ∀ y ∈ U, (f * f).func x = (f * f).func y) ∧
    (∀ x ∈ U, x ∈ dom (f * f) ↔ f.func v ≠ bot) ∧
    (f.func v = bot → U ∩ dom (f * f) = ∅) ∧
    (f.func v ≠ bot → U ⊆ dom (f * f)) := by
  constructor
  · intro x hx y hy
    change f.func (f.func x) = f.func (f.func y)
    rw [hv x hx, hv y hy]
  constructor
  · intro x hx
    change f.func (f.func x) ≠ bot ↔ f.func v ≠ bot
    rw [hv x hx]
  constructor
  · intro h
    ext x
    simp only [mem_inter_iff, mem_empty_iff_false, iff_false]
    rintro ⟨hx, hdom⟩
    change f.func (f.func x) ≠ bot at hdom
    exact hdom (by rw [hv x hx, h])
  · intro h x hx
    change f.func (f.func x) ≠ bot
    simpa [hv x hx] using h

theorem point_constant_self_comp_zero (d : X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (v : X)
    (hself : ∀ x, d x x = 0) (hv : ∀ x ∈ U, f.func x = v) :
    ∀ x ∈ U, ∀ y ∈ U, d ((f * f).func x) ((f * f).func y) = 0 := by
  intro x hx y hy
  rw [(point_constant_self_comp f U v hv).1 x hx y hy, hself]

theorem log2_ereal_mono_of_one_le {a b : ENNReal}
    (ha : 1 ≤ a) (hab : a ≤ b) : log2_ereal a ≤ log2_ereal b := by
  have hb : 1 ≤ b := ha.trans hab
  have ha0 : a ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one ha)
  have hb0 : b ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hb)
  by_cases hbt : b = ⊤
  · simp [log2_ereal, hb0, hbt]
  · have hat : a ≠ ⊤ := by
      intro h
      apply hbt
      rw [h] at hab
      exact top_le_iff.mp hab
    have haR : (0 : ℝ) < a.toReal := by
      have := ENNReal.toReal_mono hat ha
      have : (1 : ℝ) ≤ a.toReal := by simpa using this
      linarith
    have hbR : (0 : ℝ) < b.toReal := by
      have := ENNReal.toReal_mono hbt hb
      have : (1 : ℝ) ≤ b.toReal := by simpa using this
      linarith
    have hlog : Real.logb 2 a.toReal ≤ Real.logb 2 b.toReal :=
      (Real.logb_le_logb one_lt_two haR hbR).2 (ENNReal.toReal_mono hbt hab)
    simpa [log2_ereal, ha0, hb0, hat, hbt] using (EReal.coe_le_coe_iff.2 hlog)

theorem entropy_mono_of_cover (din dout : X → X → ENNReal)
    (A B : Set X) (δ ε : ENNReal) (hA : A.Nonempty) (hB : B.Nonempty)
    (hcover : covering_number dout ε B ≤ covering_number din δ A) :
    metric_entropy dout ε B ≤ metric_entropy din δ A := by
  exact log2_ereal_mono_of_one_le
    (one_le_covering_number_of_nonempty dout ε B hB) hcover

theorem uniform_threshold_entropy (din dout : X → X → ENNReal)
    (f : Operator X bot) (A B : Set X) (τ ε : ENNReal)
    (hin : ∀ x y, din x y = din y x) (hBA : B ⊆ A) (hB : B.Nonempty)
    (hτ : τ ≤ uniformRadius din dout f A A) (hε : 0 < ε) :
    metric_entropy dout ε (f.func '' B) ≤ metric_entropy din τ B :=
  entropy_mono_of_cover din dout B (f.func '' B) τ ε hB (hB.image f.func)
    (uniform_threshold_cover din dout f A B τ ε hin hBA hτ hε)

theorem finite_cover_finite (d : X → X → ENNReal) (U : Set X) (ε : ENNReal)
    (hU : U.Finite) (hε : 0 < ε) (hself : ∀ x ∈ U, d x x = 0) :
    covering_number d ε U < ⊤ := by
  classical
  have hnet : InternalEpsilonNet d ε U hU.toFinset := by
    constructor
    · intro x hx
      exact hU.mem_toFinset.mp hx
    · intro x hx
      exact ⟨x, hU.mem_toFinset.mpr hx, by simpa [hself x hx] using hε⟩
  have hle : covering_number d ε U ≤ (hU.toFinset.card : ENNReal) :=
    iInf_le_of_le _ (iInf_le_of_le hnet le_rfl)
  exact lt_of_le_of_lt hle (ENNReal.natCast_lt_top _)

theorem finite_nonempty_cover_bounds (d : X → X → ENNReal) (U : Set X) (ε : ENNReal)
    (hne : U.Nonempty) (hU : U.Finite) (hε : 0 < ε) (hself : ∀ x ∈ U, d x x = 0) :
    1 ≤ covering_number d ε U ∧ covering_number d ε U < ⊤ :=
  ⟨one_le_covering_number_of_nonempty d ε U hne, finite_cover_finite d U ε hU hε hself⟩

theorem finite_cover_entropy_real (d : X → X → ENNReal) (U : Set X) (ε : ENNReal)
    (hne : U.Nonempty) (hfin : covering_number d ε U < ⊤) :
    ∃ r : ℝ, metric_entropy d ε U = (r : EReal) := by
  have h1 := one_le_covering_number_of_nonempty d ε U hne
  have h0 : covering_number d ε U ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one h1)
  refine ⟨Real.logb 2 (covering_number d ε U).toReal, ?_⟩
  simp [metric_entropy, log2_ereal, h0, ne_of_lt hfin]

theorem finite_mapping_entropy (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (Jin Jout : Set I) (ε : ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (hne : U.Nonempty) (hdom : U ⊆ dom f) (hfinite : U.Finite)
    (hJin : Jin.Nonempty) (hJout : Jout.Nonempty) (hε : 0 < ε) (hεfin : ε < ⊤) :
    (covering_number (subfamily_pseudometric d Jin) ε U < ⊤ ∧
      covering_number (subfamily_pseudometric d Jout) ε (f.func '' U) < ⊤) ∧
    (∃ r s : ℝ, subfamily_metric_entropy d Jin ε U = (r : EReal) ∧
      subfamily_metric_entropy d Jout ε (f.func '' U) = (s : EReal)) ∧
    entropyDifferenceValid d f U Jin Jout ε := by
  have self : ∀ J x, subfamily_pseudometric d J x x = 0 := by
    intro J x
    exact (subfamily_zero_iff d J x x).2 (fun j _ => (hd j).dist_self x)
  have hin : covering_number (subfamily_pseudometric d Jin) ε U < ⊤ :=
    finite_cover_finite _ U ε hfinite hε (fun x _ => self _ x)
  have hout : covering_number (subfamily_pseudometric d Jout) ε (f.func '' U) < ⊤ :=
    finite_cover_finite _ _ ε (hfinite.image f.func) hε (fun x _ => self _ x)
  have ⟨r, hr⟩ := finite_cover_entropy_real _ U ε hne hin
  have ⟨s, hs⟩ := finite_cover_entropy_real _ (f.func '' U) ε (hne.image f.func) hout
  exact ⟨⟨hin, hout⟩, ⟨r, s, hr, hs⟩,
    ⟨hne, hdom, hJin, hJout, hε, hεfin, Or.inl hin⟩⟩

theorem constant_mapping_entropy (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (i : I) (ε : ENNReal)
    (hne : U.Nonempty) (hε : 0 < ε) (hc : i ∈ constComponents d f U)
    (hvalid : entropyDifferenceValid d f U {i} {i} ε) :
    covering_number (d i) ε (f.func '' U) = 1 ∧
    metric_entropy (d i) ε (f.func '' U) = 0 ∧
    mappingEntropyDifference d f U {i} {i} ε hvalid = metric_entropy (d i) ε U := by
  have hcover := zero_image_cover_one (d i) f.func U hne ε hε hc
  have hout : metric_entropy (d i) ε (f.func '' U) = 0 := by
    simp [metric_entropy, log2_ereal, hcover]
  refine ⟨hcover, hout, ?_⟩
  simp [mappingEntropyDifference, subfamily_metric_entropy_singleton, hout]

theorem identity_mapping_entropy (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (i : I) (ε : ENNReal)
    (hd : ExtendedPseudoMetric X bot (d i)) (hne : U.Nonempty)
    (hi : i ∈ identityComponents d f U)
    (hvalid : entropyDifferenceValid d f U {i} {i} ε) :
    mappingEntropyDifference d f U {i} {i} ε hvalid = 0 := by
  have hc := (identity_cover_eq d f U i ε hd hi).1
  have hfin : covering_number (d i) ε U < ⊤ := by
    have h := hvalid.2.2.2.2.2.2
    rw [subfamily_pseudometric_singleton] at h
    rcases h with h | h
    · exact h
    · rwa [hc] at h
  obtain ⟨r, hr⟩ := finite_cover_entropy_real (d i) U ε hne hfin
  have heq := (identity_cover_eq d f U i ε hd hi).2
  simp only [mappingEntropyDifference, subfamily_metric_entropy_singleton, heq, hr, ← EReal.coe_sub]
  simp

theorem scalar_lip_entropy_bound (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (i j : I) (ε L : ENNReal)
    (hU : U.Nonempty) (hdom : U ⊆ dom f)
    (htot : totallyBoundedAtAllScales (d i) U)
    (hε : 0 < ε) (hεfin : ε < ⊤) (hL : 0 < L) (hLfin : L < ⊤)
    (hlip : ∀ x ∈ U, ∀ y ∈ U, d j (f.func x) (f.func y) ≤ L * d i x y) :
    ∃ hv : entropyDifferenceValid d f U {i} {j} ε,
      covering_number (d j) ε (f.func '' U) < ⊤ ∧
      (∃ a b : ℝ, metric_entropy (d i) ε U = (a : EReal) ∧
        metric_entropy (d j) ε (f.func '' U) = (b : EReal)) ∧
      metric_entropy (d i) ε U - metric_entropy (d i) (ε / L) U ≤
        mappingEntropyDifference d f U {i} {j} ε hv := by
  have hdivpos : 0 < ε / L := ENNReal.div_pos (ne_of_gt hε) (ne_of_lt hLfin)
  have hdivfin : ε / L < ⊤ := ENNReal.div_lt_top (ne_of_lt hεfin) (ne_of_gt hL)
  have hin := htot ε hε hεfin
  have hscale := htot (ε / L) hdivpos hdivfin
  have hcover := scalar_lip_cover (d i) (d j) f U L ε hlip
  have hout : covering_number (d j) ε (f.func '' U) < ⊤ := lt_of_le_of_lt hcover hscale
  have hv : entropyDifferenceValid d f U {i} {j} ε := by
    refine ⟨hU, hdom, Set.singleton_nonempty _, Set.singleton_nonempty _, hε, hεfin, Or.inl ?_⟩
    simpa [subfamily_pseudometric_singleton] using hin
  have hlog := entropy_mono_of_cover (d i) (d j) U (f.func '' U) (ε / L) ε
    hU (hU.image f.func) hcover
  obtain ⟨a, ha⟩ := finite_cover_entropy_real (d i) U ε hU hin
  obtain ⟨b, hb⟩ := finite_cover_entropy_real (d j) (f.func '' U) ε (hU.image f.func) hout
  refine ⟨hv, hout, ⟨a, b, ha, hb⟩, ?_⟩
  simpa only [mappingEntropyDifference, subfamily_metric_entropy_singleton] using
    (EReal.sub_le_sub (le_refl (metric_entropy (d i) ε U)) hlog)

theorem colip_entropy_bound [Fintype I] (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (i j : I) (ε : ENNReal)
    (K : I → I → ENNReal) (hU : U.Nonempty) (hdom : U ⊆ dom f)
    (htot : totallyBoundedAtAllScales (d i) U)
    (hε : 0 < ε) (hεfin : ε < ⊤) (hK : IsCoLipMatrix d f U K)
    (hpos : 0 < K i j) (hfin : K i j < ⊤) :
    ∃ hv : entropyDifferenceValid d f U {i} {j} ε,
      (∃ a b : ℝ, metric_entropy (d i) ε U = (a : EReal) ∧
        metric_entropy (d i) (ε / K i j) U = (b : EReal)) ∧
      mappingEntropyDifference d f U {i} {j} ε hv ≤
        metric_entropy (d i) ε U - metric_entropy (d i) (ε / K i j) U := by
  have hdivpos : 0 < ε / K i j := ENNReal.div_pos (ne_of_gt hε) (ne_of_lt hfin)
  have hdivfin : ε / K i j < ⊤ := ENNReal.div_lt_top (ne_of_lt hεfin) (ne_of_gt hpos)
  have hin := htot ε hε hεfin
  have hscale := htot (ε / K i j) hdivpos hdivfin
  have hcover := colip_cover d f U i j K ε hK hpos hfin
  have hv : entropyDifferenceValid d f U {i} {j} ε := by
    refine ⟨hU, hdom, Set.singleton_nonempty _, Set.singleton_nonempty _, hε, hεfin, Or.inl ?_⟩
    simpa [subfamily_pseudometric_singleton] using hin
  have hlog := entropy_mono_of_cover (d j) (d i) (f.func '' U) U ε (ε / K i j)
    (hU.image f.func) hU hcover
  obtain ⟨a, ha⟩ := finite_cover_entropy_real (d i) U ε hU hin
  obtain ⟨b, hb⟩ := finite_cover_entropy_real (d i) U (ε / K i j) hU hscale
  refine ⟨hv, ⟨a, b, ha, hb⟩, ?_⟩
  simpa only [mappingEntropyDifference, subfamily_metric_entropy_singleton] using
    (EReal.sub_le_sub (le_refl (metric_entropy (d i) ε U)) hlog)

namespace SwapExample

abbrev Point := Option Bool

def dist (x y : Point) : ENNReal :=
  if x = y then 0 else if x = none ∨ y = none then ⊤ else 1

def gauge (_ : Unit) : Point → Point → ENNReal := dist

def U : Set Point := {x | x ≠ none}

theorem U_nonempty : U.Nonempty := ⟨some false, by simp [U]⟩

def swap : Operator Point none where
  func
    | none => none
    | some b => some (!b)
  preserves_bot := rfl

theorem metric : ExtendedPseudoMetric Point none dist := by
  constructor
  · exact ⟨some false, by decide⟩
  · intro x
    simp [dist]
  · intro x y
    rcases x with _ | (_ | _) <;> rcases y with _ | (_ | _) <;> simp [dist]
  · intro x y z
    rcases x with _ | (_ | _) <;> rcases y with _ | (_ | _) <;>
      rcases z with _ | (_ | _) <;> simp [dist, Option.some_ne_none] <;> norm_num
  · intro x hx
    rcases x with _ | (_ | _) <;> simp_all [dist]

theorem image_U : swap.func '' U = U := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rcases y with _ | (_ | _) <;> simp_all [U, swap]
  · intro hx
    rcases x with _ | (_ | _)
    · exact (hx rfl).elim
    · exact ⟨some true, by simp [U], rfl⟩
    · exact ⟨some false, by simp [U], rfl⟩

theorem square : swap * swap = (1 : Operator Point none) := by
  ext x
  rcases x with _ | (_ | _) <;> rfl

theorem domain_U : U ⊆ dom (swap * swap) := by
  rw [square]
  intro x hx
  exact hx

theorem swap_not_const : () ∉ constComponents gauge swap U := by
  intro h
  have h' := h (some false) (by simp [U]) (some true) (by simp [U])
  simp [gauge, dist, swap, Option.some_ne_none] at h'

theorem swap_not_identity : () ∉ identityComponents gauge swap U := by
  intro h
  have h' := h.2 (some false) (by simp [U])
  simp [gauge, dist, swap, Option.some_ne_none] at h'

theorem swap_active : () ∈ activeComponents gauge swap U := by
  simp only [activeComponents, mem_compl_iff, mem_union, not_or]
  exact ⟨swap_not_const, swap_not_identity⟩

theorem id_not_const : () ∉ constComponents gauge (1 : Operator Point none) U := by
  intro h
  have h' := h (some false) (by simp [U]) (some true) (by simp [U])
  change dist (some false) (some true) = 0 at h'
  simp [dist, Option.some_ne_none] at h'

theorem square_identity_component : () ∈ identityComponents gauge (swap * swap) U := by
  rw [square]
  refine ⟨id_not_const, ?_⟩
  intro x hx
  exact metric.dist_self x

theorem reverse_inclusions_fail :
    () ∈ activeComponents gauge swap U ∧
    () ∈ activeComponents gauge swap (swap.func '' U) ∧
    () ∉ activeComponents gauge (swap * swap) U ∧
    () ∉ identityComponents gauge swap U ∧
    () ∉ identityComponents gauge swap (swap.func '' U) ∧
    () ∈ identityComponents gauge (swap * swap) U := by
  refine ⟨swap_active, ?_, ?_, swap_not_identity, ?_, square_identity_component⟩
  · simpa only [image_U] using swap_active
  · intro h
    exact h (Or.inr square_identity_component)
  · simpa only [image_U] using swap_not_identity

theorem component_sets_exact :
    activeComponents gauge swap U = univ ∧
    identityComponents gauge swap U = ∅ ∧
    activeComponents gauge (swap * swap) U = ∅ ∧
    identityComponents gauge (swap * swap) U = univ := by
  have h := reverse_inclusions_fail
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i
    cases i
    simpa using swap_active
  · ext i
    cases i
    simpa using swap_not_identity
  · ext i
    cases i
    simpa using h.2.2.1
  · ext i
    cases i
    simpa using square_identity_component

theorem diameter_U : diameter dist U = 1 := by
  apply le_antisymm
  · apply iSup_le
    intro x
    apply iSup_le
    intro hx
    apply iSup_le
    intro y
    apply iSup_le
    intro hy
    rcases x with _ | (_ | _) <;> rcases y with _ | (_ | _) <;>
      simp_all [U, dist, Option.some_ne_none]
  · have h := diameter_upper dist U (some false) (some true) (by simp [U]) (by simp [U])
    simpa [dist, Option.some_ne_none] using h

theorem diameter_singleton : diameter dist ({some false} : Set Point) = 0 := by
  apply le_antisymm _ (zero_le _)
  apply iSup_le
  intro x
  apply iSup_le
  intro hx
  apply iSup_le
  intro y
  apply iSup_le
  intro hy
  have hxy : x = y := (Set.mem_singleton_iff.mp hx).trans (Set.mem_singleton_iff.mp hy).symm
  simp [dist, hxy]

def intoReal : Point → Option ℝ
  | none => none
  | some false => some 0
  | some true => some 1

def realAbsorbingDist : Option ℝ → Option ℝ → ENNReal
  | none, none => 0
  | none, some _ => ⊤
  | some _, none => ⊤
  | some x, some y => ENNReal.ofReal |x - y|

theorem finite_real_isometry (x y : Point) :
    realAbsorbingDist (intoReal x) (intoReal y) = dist x y := by
  rcases x with _ | (_ | _) <;> rcases y with _ | (_ | _) <;>
    simp [intoReal, realAbsorbingDist, dist, Option.some_ne_none] <;> norm_num

theorem scale_reverse_counterexample :
    ({some false} : Set Point).Nonempty ∧ ({some false} : Set Point) ⊆ U ∧
    U ⊆ dom (1 : Operator Point none) ∧
    diameter dist ({some false} : Set Point) < (1 / 2 : ENNReal) ∧
    (1 / 2 : ENNReal) ≤ diameter dist U := by
  refine ⟨⟨some false, by simp⟩, ?_, ?_, ?_⟩
  · intro x hx
    have hx' : x = some false := Set.mem_singleton_iff.mp hx
    simp [U, hx']
  · intro x hx
    exact hx
  · rw [diameter_singleton, diameter_U]
    norm_num

def infiniteDist (x y : Point) : ENNReal := if x = y then 0 else ⊤

theorem infiniteMetric : ExtendedPseudoMetric Point none infiniteDist := by
  constructor
  · exact ⟨some false, by decide⟩
  · intro x
    simp [infiniteDist]
  · intro x y
    simp only [infiniteDist, eq_comm]
  · intro x y z
    by_cases hxz : x = z
    · simp [infiniteDist, hxz]
    · have h : x ≠ y ∨ y ≠ z := by
        by_contra hn
        push_neg at hn
        exact hxz (hn.1.trans hn.2)
      rcases h with h | h <;> simp [infiniteDist, hxz, h]
  · intro x hx
    simp [infiniteDist, hx]

def twoGauge : Bool → Point → Point → ENNReal
  | false => infiniteDist
  | true => dist

theorem twoGauge_extended (i : Bool) : ExtendedPseudoMetric Point none (twoGauge i) := by
  cases i
  · exact infiniteMetric
  · exact metric

theorem infinite_input_uniform (dout : Point → Point → ENNReal)
    (hself : ∀ x, dout x x = 0) :
    uniformRadius infiniteDist dout (1 : Operator Point none) U U = ⊤ := by
  apply top_unique
  apply le_iInf₂
  intro y hy
  rw [← ENNReal.iSup_natCast]
  apply iSup_le
  intro n
  cases n with
  | zero => simp
  | succ n =>
      apply radius_ge_admissible
      refine ⟨?_, ENNReal.natCast_lt_top _, ?_⟩
      · exact_mod_cast Nat.zero_lt_succ n
      · intro x hx hdist
        have hxy : x = y := by
          by_contra hne
          have ht : infiniteDist x y = ⊤ := by simp [infiniteDist, hne]
          rw [ht] at hdist
          exact (not_lt_of_ge le_top) hdist
        subst x
        exact hself y

theorem infinite_radius_not_constant :
    zeroMatrix twoGauge (1 : Operator Point none) U false false = ⊤ ∧
    false ∉ constComponents twoGauge (1 : Operator Point none) U ∧
    zeroMatrix twoGauge (1 : Operator Point none) U false true = ⊤ ∧
    true ∉ constComponents twoGauge (1 : Operator Point none) U := by
  have hnot₁ : false ∉ constComponents twoGauge (1 : Operator Point none) U := by
    intro h
    have h' := h (some false) (by simp [U]) (some true) (by simp [U])
    change infiniteDist (some false) (some true) = 0 at h'
    simp [infiniteDist] at h'
  have hnot₂ : true ∉ constComponents twoGauge (1 : Operator Point none) U := by
    intro h
    have h' := h (some false) (by simp [U]) (some true) (by simp [U])
    change dist (some false) (some true) = 0 at h'
    simp [dist, Option.some_ne_none] at h'
  exact ⟨infinite_input_uniform infiniteDist infiniteMetric.dist_self, hnot₁,
    infinite_input_uniform dist metric.dist_self, hnot₂⟩

end SwapExample

end Chapter3

