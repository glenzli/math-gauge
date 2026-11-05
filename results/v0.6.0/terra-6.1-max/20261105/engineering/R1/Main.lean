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

def z0 (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) : Set I :=
  {i | ∀ x ∈ U, ∀ y ∈ U, d i (f.func x) (f.func y) = 0}

def z1 (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) : Set I :=
  {i | i ∉ z0 d f U ∧ ∀ x ∈ U, d i (f.func x) x = 0}

def z2 (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) : Set I :=
  (z0 d f U ∪ z1 d f U)ᶜ

theorem z3 (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (i : I) :
    (i ∈ z0 d f U ∨ i ∈ z1 d f U ∨
      i ∈ z2 d f U) ∧
    ¬ (i ∈ z0 d f U ∧ i ∈ z1 d f U) ∧
    ¬ (i ∈ z0 d f U ∧ i ∈ z2 d f U) ∧
    ¬ (i ∈ z1 d f U ∧ i ∈ z2 d f U) := by
  classical
  simp only [z1, z2, mem_setOf_eq, mem_compl_iff,
    mem_union] 
  tauto

theorem const_zero_row [Fintype I] (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (i : I)
    (hi : i ∈ z0 d f U) :
    ∀ x ∈ U, ∀ y ∈ U, d i (f.func x) (f.func y) ≤
      ∑ k : I, (0 : ENNReal) * d k x y := by
  intro x hx y hy
  simp [hi x hx y hy]

theorem z4 [Fintype I] (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (i k : I) (K : I → I → ENNReal)
    (hi : i ∈ z0 d f U) (hK : IsCoLipMatrix d f U K)
    (x y : X) (hx : x ∈ U) (hy : y ∈ U) (hpos : 0 < d k x y) : K k i = 0 :=
  colip_entry_eq_zero_of_output_zero_input_pos d f U K k i x y hK hx hy
    (hi x hx y hy) hpos

theorem z5 (d : X → X → ENNReal)
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

theorem z6 (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (i : I)
    (hd : ExtendedPseudoMetric X bot (d i))
    (hi : i ∈ z1 d f U) :
    ∀ x ∈ U, ∀ y ∈ U, d i (f.func x) (f.func y) = d i x y := by
  intro x hx y hy
  exact z5 (d i) hd.symm hd.triangle (hi.2 x hx) (hi.2 y hy)

theorem outer_const (d : I → X → X → ENNReal)
    (f g : Operator X bot) (U : Set X) (i : I)
    (h : i ∈ z0 d g (f.func '' U)) :
    i ∈ z0 d (g * f) U := by
  intro x hx y hy
  exact h (f.func x) ⟨x, hx, rfl⟩ (f.func y) ⟨y, hy, rfl⟩

theorem z7 [Fintype I] (d : I → X → X → ENNReal)
    (f g : Operator X bot) (U : Set X) (j : I) (L : I → I → ENNReal)
    (hc : j ∈ z0 d f U)
    (hL : IsLipMatrix d g (f.func '' U) L)
    (hrow : ∀ k, k ≠ j → L k j = 0) :
    j ∈ z0 d (g * f) U := by
  intro x hx y hy
  apply le_antisymm _ (zero_le _)
  have h := lip_bound_of_single_input_row d g (f.func '' U) L j j hL hrow
      (f.func x) ⟨x, hx, rfl⟩ (f.func y) ⟨y, hy, rfl⟩
  simpa [hc x hx y hy] using h

theorem identity_comp (d : I → X → X → ENNReal)
    (f g : Operator X bot) (U : Set X) (i : I)
    (hd : ExtendedPseudoMetric X bot (d i))
    (hf : i ∈ z1 d f U)
    (hg : i ∈ z1 d g (f.func '' U)) :
    i ∈ z1 d (g * f) U := by
  constructor
  · intro hc
    apply hf.1
    intro x hx y hy
    have heq := z6 d g (f.func '' U) i hd hg
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
    i ∈ z2 d (g * f) U →
      i ∈ z2 d f U ∨ i ∈ z2 d g (f.func '' U) := by
  classical
  intro hc
  by_contra h
  have hf : i ∈ z0 d f U ∨ i ∈ z1 d f U := by
    have h1 := (not_or.mp h).1
    simp only [z2, mem_compl_iff, mem_union] at h1
    tauto
  have hg : i ∈ z0 d g (f.func '' U) ∨
      i ∈ z1 d g (f.func '' U) := by
    have h2 := (not_or.mp h).2
    simp only [z2, mem_compl_iff, mem_union] at h2
    tauto
  have hnot : i ∉ z0 d (g * f) U ∧
      i ∉ z1 d (g * f) U := by simpa [z2] using hc
  rcases hg with hg | hg
  · exact hnot.1 (outer_const d f g U i hg)
  · rcases hf with hf | hf
    · apply hnot.1
      intro x hx y hy
      have heq := z6 d g (f.func '' U) i hd hg
        (f.func x) ⟨x, hx, rfl⟩ (f.func y) ⟨y, hy, rfl⟩
      exact heq.trans (hf x hx y hy)
    · exact hnot.2 (identity_comp d f g U i hd hf hg)

def seqOp : List (Operator X bot) → Operator X bot
  | [] => 1
  | f :: fs => seqOp fs * f

def seqActive (d : I → X → X → ENNReal) :
    List (Operator X bot) → Set X → Set I
  | [], _ => ∅
  | f :: fs, U => z2 d f U ∪ seqActive d fs (f.func '' U)

theorem z8 (fs : List (Operator X bot)) :
    seqOp fs = fs.reverse.prod := by
  induction fs with
  | nil => rfl
  | cons f fs ih => simp [seqOp, ih, List.prod_append]

theorem z9 (d : I → X → X → ENNReal)
    (U : Set X) (i : I) (hself : ∀ x, d i x x = 0) :
    i ∉ z2 d (1 : Operator X bot) U := by
  classical
  simp only [z2, mem_compl_iff, mem_union, not_not]
  by_cases hc : i ∈ z0 d (1 : Operator X bot) U
  · exact Or.inl hc
  · right
    exact ⟨hc, fun x _ => hself x⟩

theorem active_seq (d : I → X → X → ENNReal)
    (fs : List (Operator X bot)) (U : Set X) (i : I)
    (hd : ExtendedPseudoMetric X bot (d i)) :
    i ∈ z2 d (seqOp fs) U → i ∈ seqActive d fs U := by
  induction fs generalizing U with
  | nil =>
      intro h
      exact (z9 d U i hd.dist_self h).elim
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

theorem z10 (d : I → X → X → ENNReal)
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

theorem z11 (d : I → X → X → ENNReal) (f : Operator X bot)
    (J : Set I) (y : X) (U : Set X) :
    fiber d f J y U = {x | x ∈ U ∧ ∀ j ∈ J, x ∈ componentFiber d f j y U} := by
  ext x
  simp only [fiber, componentFiber, mem_setOf_eq, z10]
  constructor
  · rintro ⟨hx, h⟩
    exact ⟨hx, fun j hj => ⟨hx, h j hj⟩⟩
  · rintro ⟨hx, h⟩
    exact ⟨hx, fun j hj => (h j hj).2⟩

theorem z12 (d : I → X → X → ENNReal) (f : Operator X bot)
    (J : Set I) (y : X) (U : Set X) (hJ : J.Nonempty) :
    fiber d f J y U = ⋂ j ∈ J, componentFiber d f j y U := by
  rw [z11]
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
  exact ⟨hx.1, (z10 d J _ _).2
    (fun j hj => (z10 d K _ _).1 hx.2 j (hJK hj))⟩

theorem z13 (d : I → X → X → ENNReal) (f : Operator X bot)
    (j : I) (y : X) (U : Set X) :
    fiber d f {j} y U = componentFiber d f j y U := by
  ext x
  simp [fiber, componentFiber, subfamily_pseudometric_singleton]

theorem z14 (d : I → X → X → ENNReal) (f : Operator X bot)
    (j : I) (y : X) (U : Set X) :
    fiber d f univ y U ⊆ componentFiber d f j y U := by
  rw [← z13]
  exact fiber_antitone d f _ _ _ _ (subset_univ _)

theorem z15 (d : I → X → X → ENNReal) (f : Operator X bot)
    (J : Set I) (y z : X) (U : Set X)
    (hd : ∀ j, ExtendedPseudoMetric X bot (d j))
    (hyz : subfamily_pseudometric d J y z = 0) :
    fiber d f J y U = fiber d f J z U := by
  ext x
  simp only [fiber, mem_setOf_eq, z10]
  constructor <;> intro h <;> refine ⟨h.1, ?_⟩ <;> intro j hj
  · apply le_antisymm _ (zero_le _)
    calc
      d j (f.func x) z ≤ d j (f.func x) y + d j y z := (hd j).triangle _ _ _
      _ = 0 := by rw [h.2 j hj, (z10 d J y z).1 hyz j hj, add_zero]
  · apply le_antisymm _ (zero_le _)
    calc
      d j (f.func x) y ≤ d j (f.func x) z + d j z y := (hd j).triangle _ _ _
      _ = 0 := by rw [h.2 j hj, (hd j).symm z y,
        (z10 d J y z).1 hyz j hj, add_zero]

theorem z16 (d : I → X → X → ENNReal) (f : Operator X bot)
    (J : Set I) (U : Set X) (hd : ∀ j, ExtendedPseudoMetric X bot (d j)) :
    (∀ y ∈ f.func '' U, (fiber d f J y U).Nonempty) ∧
    (⋃ y ∈ f.func '' U, fiber d f J y U) = U := by
  constructor
  · rintro y ⟨x, hx, rfl⟩
    exact ⟨x, hx, (z10 d J _ _).2 (fun j _ => (hd j).dist_self _)⟩
  · ext x
    constructor
    · intro hx
      obtain ⟨y, _, hxy⟩ := Set.mem_iUnion₂.mp hx
      exact hxy.1
    · intro hx
      apply Set.mem_iUnion₂.mpr
      exact ⟨f.func x, ⟨x, hx, rfl⟩, hx,
        (z10 d J _ _).2 (fun j _ => (hd j).dist_self _)⟩

theorem z17 (d : I → X → X → ENNReal) (f : Operator X bot)
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
    apply z15 d f J y z U hd
    apply (z10 d J y z).2
    intro j hj
    apply le_antisymm _ (zero_le _)
    calc
      d j y z ≤ d j y (f.func x) + d j (f.func x) z := (hd j).triangle _ _ _
      _ = 0 := by rw [(hd j).symm y (f.func x),
        (z10 d J _ _).1 hx.2 j hj,
        (z10 d J _ _).1 hx'.2 j hj, add_zero]

theorem z18 (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (i : I) (y : X)
    (hd : ExtendedPseudoMetric X bot (d i))
    (hi : i ∈ z1 d f U) :
    componentFiber d f i y U = {x | x ∈ U ∧ d i x y = 0} := by
  ext x
  simp only [componentFiber, mem_setOf_eq]
  constructor <;> intro h <;> refine ⟨h.1, ?_⟩
  · have hdist := z5 (d i) hd.symm hd.triangle (hi.2 x h.1) (hd.dist_self y)
    exact hdist.symm.trans h.2
  · have hdist := z5 (d i) hd.symm hd.triangle (hi.2 x h.1) (hd.dist_self y)
    exact hdist.trans h.2

theorem z19 (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (i : I) (y₀ y : X)
    (hd : ExtendedPseudoMetric X bot (d i))
    (hc : i ∈ z0 d f U) (hy₀ : y₀ ∈ f.func '' U) :
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

theorem z20 (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    (x, y) ∈ zeroRelation d f U ↔ y ∈ fiber d f univ (f.func x) U := by
  simp only [zeroRelation, fiber, mem_setOf_eq, GaugeZeroRelated,
    z10, Set.mem_univ, forall_const]
  constructor
  · rintro ⟨_, _, h⟩
    exact ⟨hy, fun i => (hd i).symm _ _ |>.trans (h i)⟩
  · rintro ⟨_, h⟩
    exact ⟨hx, hy, fun i => (hd i).symm _ _ |>.trans (h i)⟩

theorem z21 (d : I → X → X → ENNReal) (U : Set X)
    (f : Operator X bot) : fiberPreorder d U f f := Set.Subset.rfl

theorem z22 (d : I → X → X → ENNReal) (U : Set X)
    (f g h : Operator X bot) (hfg : fiberPreorder d U f g)
    (hgh : fiberPreorder d U g h) : fiberPreorder d U f h := hfg.trans hgh

theorem z23 (d : I → X → X → ENNReal) (U : Set X)
    (f : ℕ → Operator X bot) (hstep : ∀ n, fiberPreorder d U (f n) (f (n+1)))
    {a b : ℕ} (hab : a ≤ b) : fiberPreorder d U (f a) (f b) := by
  induction b, hab using Nat.le_induction with
  | base => exact z21 d U (f a)
  | succ n _ ih => exact z22 d U _ _ _ ih (hstep n)

theorem z24 (d : I → X → X → ENNReal) (U : Set X)
    (f : ℕ → Operator X bot) (hstep : ∀ n, fiberPreorder d U (f n) (f (n+1)))
    {r m : ℕ} (hr : r + 1 ≤ m)
    (hstrict : zeroRelation d (f r) U ⊂ zeroRelation d (f (r+1)) U) :
    zeroRelation d (f 0) U ⊂ zeroRelation d (f m) U ∧
      ∃ p, p ∈ zeroRelation d (f m) U ∧ p ∉ zeroRelation d (f 0) U := by
  have h0 : zeroRelation d (f 0) U ⊆ zeroRelation d (f r) U :=
    z23 d U f hstep (Nat.zero_le r)
  have hm : zeroRelation d (f (r+1)) U ⊆ zeroRelation d (f m) U :=
    z23 d U f hstep hr
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

theorem z25 (f g : Operator X bot) (U : Set X) :
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

theorem z26 (f g : Operator X bot) (U : Set X) :
    (hasImageFactor f g U ∧ hasImageFactor g f U) ↔
      pointRelation f U = pointRelation g U := by
  rw [z25, z25]
  exact Set.Subset.antisymm_iff.symm

def z27 (d : I → X → X → ENNReal)
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
  Quotient (z27 d f U hd)

def imageClass (d : I → X → X → ENNReal) (f : Operator X bot) (U : Set X)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (x : X) (hx : x ∈ U) :
    imageQuotient d f U hd := Quotient.mk _ (imagePoint f U x hx)

def z28 (d : I → X → X → ENNReal)
    (f g : Operator X bot) (U : Set X)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) : Prop :=
  ∃ T : imageQuotient d f U hd → imageQuotient d g U hd,
    ∀ x (hx : x ∈ U), T (imageClass d f U hd x hx) = imageClass d g U hd x hx

theorem z29 (d : I → X → X → ENNReal)
    (f g : Operator X bot) (U : Set X)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) :
    z28 d f g U hd ↔ fiberPreorder d U f g := by
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
        (z27 d f U hd).r a b → T₀ a = T₀ b := by
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

theorem z30 (d : I → X → X → ENNReal)
    (f g : Operator X bot) (U : Set X)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) :
    (z28 d f g U hd ∧ z28 d g f U hd) ↔
      zeroRelation d f U = zeroRelation d g U := by
  rw [z29, z29]
  exact Set.Subset.antisymm_iff.symm

def separatingOn (d : I → X → X → ENNReal) (A : Set X) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, GaugeZeroRelated d x y → x = y

theorem z31 (d : I → X → X → ENNReal)
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

theorem z32 (d : I → X → X → ENNReal)
    (f g : Operator X bot) (U : Set X)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (hf : separatingOn d (f.func '' U)) (hg : separatingOn d (g.func '' U)) :
    (hasImageFactor f g U ↔ z28 d f g U hd) ∧
    ((hasImageFactor f g U ∧ hasImageFactor g f U) ↔
      (z28 d f g U hd ∧ z28 d g f U hd)) := by
  simp only [z25, z29,
    z31 d f U hd hf,
    z31 d g U hd hg, fiberPreorder]
  exact ⟨trivial, trivial⟩

def z33 (din dout : X → X → ENNReal) (f : Operator X bot)
    (y : X) (U : Set X) (r : ENNReal) : Prop :=
  0 < r ∧ r < ⊤ ∧ ∀ x ∈ U, din x y < r → dout (f.func x) (f.func y) = 0

noncomputable def zeroRadius (din dout : X → X → ENNReal)
    (f : Operator X bot) (y : X) (U : Set X) : ENNReal :=
  sSup {r | z33 din dout f y U r}

noncomputable def uniformRadius (din dout : X → X → ENNReal)
    (f : Operator X bot) (A U : Set X) : ENNReal :=
  ⨅ y ∈ A, zeroRadius din dout f y U

noncomputable def zeroMatrix (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (i j : I) : ENNReal :=
  uniformRadius (d i) (d j) f U U

theorem z34 (din dout : X → X → ENNReal)
    (f : Operator X bot) (y : X) (U : Set X) (r : ENNReal) :
    z33 din dout f y U r ↔
      0 < r ∧ r < ⊤ ∧ ball din y r ∩ U ⊆
        {x | x ∈ U ∧ dout (f.func x) (f.func y) = 0} := by
  simp only [z33, ball, Set.subset_def, mem_inter_iff, mem_setOf_eq]
  constructor
  · rintro ⟨hpos, hfin, h⟩
    refine ⟨hpos, hfin, ?_⟩
    rintro x ⟨hxy, hx⟩
    exact ⟨hx, h x hx hxy⟩
  · rintro ⟨hpos, hfin, h⟩
    refine ⟨hpos, hfin, ?_⟩
    intro x hx hxy
    exact (h x ⟨hxy, hx⟩).2

theorem z35 (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (J : Set I) (i : I) (y : X) (r : ENNReal) :
    z33 (d i) (subfamily_pseudometric d J) f y U r ↔
      0 < r ∧ r < ⊤ ∧ ball (d i) y r ∩ U ⊆ fiber d f J (f.func y) U := by
  exact z34 _ _ _ _ _ _

theorem z36 (din dout : X → X → ENNReal)
    (f : Operator X bot) (y : X) (U : Set X)
    (h : ∀ r, ¬ z33 din dout f y U r) : zeroRadius din dout f y U = 0 := by
  have hempty : {r | z33 din dout f y U r} = ∅ := by
    ext r
    simp [h r]
  simp [zeroRadius, hempty]

theorem z37 (din dout : X → X → ENNReal)
    (f : Operator X bot) (y : X) (U : Set X) (r : ENNReal)
    (hr : z33 din dout f y U r) : r ≤ zeroRadius din dout f y U :=
  le_sSup hr

theorem z38 (din dout : X → X → ENNReal)
    (f : Operator X bot) (y : X) (U : Set X) (t : ENNReal)
    (h : t < zeroRadius din dout f y U) :
    ∃ r, z33 din dout f y U r ∧ t < r :=
  lt_sSup_iff.mp h

theorem z39 (din dout : X → X → ENNReal)
    (f : Operator X bot) (y x : X) (U : Set X)
    (hs : ∀ a b, din a b = din b a) (hx : x ∈ U)
    (h : din y x < zeroRadius din dout f y U) : dout (f.func x) (f.func y) = 0 := by
  obtain ⟨r, hr, hlt⟩ := z38 din dout f y U _ h
  apply hr.2.2 x hx
  rw [hs x y]
  exact hlt

theorem z40 (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (j : I) (y x : X)
    (hd : ExtendedPseudoMetric X bot (d j))
    (hx : x ∈ componentFiber d f j (f.func y) U) :
    d j (f.func y) (f.func x) = 0 := by
  rw [hd.symm _ _, hx.2]

theorem z41 (d : I → X → X → ENNReal)
    (f g : Operator X bot) (U₂ : Set X) (j : I) (x x' : X)
    (hd : ExtendedPseudoMetric X bot (d j))
    (hx : f.func x ∈ U₂) (hx' : f.func x' ∈ U₂)
    (hfib : f.func x' ∈ componentFiber d g j (g.func (f.func x)) U₂) :
    d j ((g * f).func x) ((g * f).func x') = 0 := by
  exact z40 d g U₂ j (f.func x) (f.func x') hd hfib

theorem z42 (din dout : X → X → ENNReal)
    (f : Operator X bot) (y : X) (A B : Set X) (hBA : B ⊆ A) :
    zeroRadius din dout f y A ≤ zeroRadius din dout f y B := by
  apply sSup_le
  intro r hr
  apply le_sSup
  exact ⟨hr.1, hr.2.1, fun x hx hdist => hr.2.2 x (hBA hx) hdist⟩

theorem z43 (din dout : X → X → ENNReal)
    (f : Operator X bot) (A B : Set X) (hBA : B ⊆ A) :
    uniformRadius din dout f A A ≤ uniformRadius din dout f B B := by
  apply le_iInf₂
  intro y hy
  exact (iInf₂_le y (hBA hy)).trans (z42 din dout f y A B hBA)

theorem z44 (din dout : X → X → ENNReal)
    (f : Operator X bot) (A : Set X) (y x : X)
    (hs : ∀ a b, din a b = din b a)
    (hx : x ∈ A) (hy : y ∈ A)
    (h : din y x < uniformRadius din dout f A A) :
    dout (f.func x) (f.func y) = 0 :=
  z39 din dout f y x A hs hx (lt_of_lt_of_le h (iInf₂_le y hy))

theorem z45 (din dout : X → X → ENNReal)
    (f : Operator X bot) (A : Set X) (y x : X)
    (hs : ∀ a b, din a b = din b a)
    (hx : x ∈ A) (hy : y ∈ A)
    (h : 0 < dout (f.func x) (f.func y)) :
    uniformRadius din dout f A A ≤ din y x := by
  by_contra hn
  have hz := z44 din dout f A y x hs hx hy (lt_of_not_ge hn)
  exact (ne_of_gt h) hz

theorem z46 (din dout : X → X → ENNReal)
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
      apply z37
      refine ⟨?_, ENNReal.natCast_lt_top _, ?_⟩
      · exact_mod_cast Nat.zero_lt_succ n
      · intro x hx _
        exact hc x hx y hy

theorem z47 (din dout : X → X → ENNReal)
    (f : Operator X bot) (U : Set X)
    (hc : ∀ x ∈ U, ∀ y ∈ U, dout (f.func x) (f.func y) = 0) :
    uniformRadius din dout f U U = ⊤ := by
  apply top_unique
  apply le_iInf₂
  intro y hy
  rw [z46 din dout f U hc y hy]

theorem z48 (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (J : Set I)
    (hc : J ⊆ z0 d f U) (y : X) (hy : y ∈ U) :
    fiber d f J (f.func y) U = U := by
  ext x
  simp only [fiber, mem_setOf_eq, z10]
  constructor
  · exact And.left
  · intro hx
    exact ⟨hx, fun j hj => hc hj x hx y hy⟩

theorem z49 (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (J : Set I) (i : I)
    (hc : J ⊆ z0 d f U) :
    (∀ y ∈ U, zeroRadius (d i) (subfamily_pseudometric d J) f y U = ⊤) ∧
      uniformRadius (d i) (subfamily_pseudometric d J) f U U = ⊤ := by
  have hzero : ∀ x ∈ U, ∀ y ∈ U,
      subfamily_pseudometric d J (f.func x) (f.func y) = 0 := by
    intro x hx y hy
    exact (z10 d J _ _).2 (fun j hj => hc hj x hx y hy)
  exact ⟨fun y hy => z46 _ _ f U hzero y hy,
    z47 _ _ f U hzero⟩

theorem z50 (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (i : I) (y : X)
    (hd : ExtendedPseudoMetric X bot (d i)) (hy : y ∈ U)
    (hi : i ∈ z1 d f U) :
    componentFiber d f i (f.func y) U = {x | x ∈ U ∧ d i x y = 0} := by
  ext x
  simp only [componentFiber, mem_setOf_eq]
  by_cases hx : x ∈ U
  · simp [hx, z6 d f U i hd hi x hx y hy]
  · simp [hx]

theorem z51 (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (i : I) (y : X) (r : ENNReal)
    (hd : ExtendedPseudoMetric X bot (d i)) (hy : y ∈ U)
    (hi : i ∈ z1 d f U)
    (hr : 0 < r ∧ r < ⊤)
    (hball : ∀ x ∈ U, d i x y < r → d i x y = 0) :
    r ≤ zeroRadius (d i) (d i) f y U := by
  apply z37
  refine ⟨hr.1, hr.2, ?_⟩
  intro x hx hxy
  rw [z6 d f U i hd hi x hx y hy]
  exact hball x hx hxy

structure ScaleFamily (X I : Type) where
  value : I → Set X → ENNReal
  monotone : ∀ i A B, A.Nonempty → B.Nonempty → A ⊆ B → value i A ≤ value i B

noncomputable def diameter (d : X → X → ENNReal) (A : Set X) : ENNReal :=
  ⨆ x ∈ A, ⨆ y ∈ A, d x y

theorem z52 (d : X → X → ENNReal) (A B : Set X) (h : A ⊆ B) :
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
  monotone i A B _ _ h := z52 (d i) A B h

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

theorem z53 (σ : ScaleFamily X I)
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

theorem z54 (σ : ScaleFamily X I) (A : Set X) (i : I)
    {τ τ' : ENNReal} (hτ : τ ≤ τ') :
    σ.value i A < τ → σ.value i A < τ' := fun h => lt_of_lt_of_le h hτ

theorem z55 (r τ τ' : ENNReal) (hτ : τ ≤ τ') :
    τ' ≤ r → τ ≤ r := fun h => hτ.trans h

theorem z56 (σ : ScaleFamily X I) (A B : Set X) (i : I)
    (hA : A.Nonempty) (hB : B.Nonempty) (hBA : B ⊆ A) :
    σ.value i B ≤ σ.value i A ∧ ∀ τ, σ.value i A < τ → σ.value i B < τ :=
  ⟨σ.monotone i B A hB hA hBA, fun _ h => lt_of_le_of_lt (σ.monotone i B A hB hA hBA) h⟩

def z57 (d : X → X → ENNReal) (U : Set X) : Prop :=
  ∀ ε : ENNReal, 0 < ε → ε < ⊤ → covering_number d ε U < ⊤

def z58 (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (Jin Jout : Set I) (ε : ENNReal) : Prop :=
  U.Nonempty ∧ U ⊆ dom f ∧ Jin.Nonempty ∧ Jout.Nonempty ∧ 0 < ε ∧ ε < ⊤ ∧
    (covering_number (subfamily_pseudometric d Jin) ε U < ⊤ ∨
     covering_number (subfamily_pseudometric d Jout) ε (f.func '' U) < ⊤)

noncomputable def z59 (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (Jin Jout : Set I) (ε : ENNReal)
    (_h : z58 d f U Jin Jout ε) : EReal :=
  subfamily_metric_entropy d Jin ε U - subfamily_metric_entropy d Jout ε (f.func '' U)

theorem z60 (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (Jin Jout : Set I) (ε : ENNReal)
    (h : z58 d f U Jin Jout ε) (a b : ℝ)
    (ha : subfamily_metric_entropy d Jin ε U = (a : EReal))
    (hb : subfamily_metric_entropy d Jout ε (f.func '' U) = (b : EReal)) :
    z59 d f U Jin Jout ε h = ((a - b : ℝ) : EReal) := by
  simp [z59, ha, hb, EReal.coe_sub]

theorem z61 (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (Jin Jout : Set I) (ε : ENNReal)
    (h : z58 d f U Jin Jout ε) (a b : ℝ) :
    (subfamily_metric_entropy d Jin ε U = ⊤ →
      subfamily_metric_entropy d Jout ε (f.func '' U) = (b : EReal) →
      z59 d f U Jin Jout ε h = ⊤) ∧
    (subfamily_metric_entropy d Jin ε U = (a : EReal) →
      subfamily_metric_entropy d Jout ε (f.func '' U) = ⊤ →
      z59 d f U Jin Jout ε h = ⊥) := by
  constructor <;> intro ha hb <;>
    simp [z59, ha, hb, EReal.top_sub_coe, EReal.sub_top]

theorem z62 (d : X → X → ENNReal) (U : Set X) :
    z57 d U ↔
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

theorem z63 (din dout : X → X → ENNReal) (f : X → X)
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

theorem z64 (din dout : X → X → ENNReal) (f : X → X) (fallback : X)
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

theorem z65 (d : X → X → ENNReal) (f : X → X)
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

theorem z66 (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (i : I) (ε : ENNReal)
    (hd : ExtendedPseudoMetric X bot (d i))
    (hi : i ∈ z1 d f U) :
    covering_number (d i) ε (f.func '' U) = covering_number (d i) ε U ∧
    metric_entropy (d i) ε (f.func '' U) = metric_entropy (d i) ε U := by
  have hdist := z6 d f U i hd hi
  have hcover : covering_number (d i) ε (f.func '' U) = covering_number (d i) ε U := by
    apply le_antisymm
    · apply z63
      intro x hx y hy h
      rwa [hdist x hx y hy]
    · apply z64 _ _ _ bot
      intro x hx y hy h
      rwa [hdist x hx y hy] at h
  exact ⟨hcover, congrArg log2_ereal hcover⟩

theorem z67 (din dout : X → X → ENNReal)
    (f : Operator X bot) (A : Set X) (τ : ENNReal)
    (hin : ∀ x y, din x y = din y x)
    (hτ : τ ≤ uniformRadius din dout f A A) (x : X) (hx : x ∈ A) :
    ball din x τ ∩ A ⊆ {y | y ∈ A ∧ dout (f.func y) (f.func x) = 0} := by
  rintro y ⟨hball, hy⟩
  refine ⟨hy, ?_⟩
  apply z44 din dout f A x y hin hy hx
  rw [hin x y]
  exact lt_of_lt_of_le hball hτ

theorem z68 (din dout : X → X → ENNReal)
    (f : Operator X bot) (A B : Set X) (τ ε : ENNReal)
    (hin : ∀ x y, din x y = din y x) (hBA : B ⊆ A)
    (hτ : τ ≤ uniformRadius din dout f A A) (hε : 0 < ε) :
    covering_number dout ε (f.func '' B) ≤ covering_number din τ B := by
  apply z63
  intro x hx c hc hdist
  have hz : dout (f.func x) (f.func c) = 0 := by
    apply z44 din dout f A c x hin (hBA hx) (hBA hc)
    rw [hin c x]
    exact lt_of_lt_of_le hdist hτ
  simpa [hz] using hε

theorem diameter_upper (d : X → X → ENNReal) (A : Set X)
    (x y : X) (hx : x ∈ A) (hy : y ∈ A) : d x y ≤ diameter d A :=
  le_iSup_of_le x (le_iSup_of_le hx (le_iSup_of_le y (le_iSup_of_le hy le_rfl)))

theorem z69 (din dout : X → X → ENNReal)
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
    exact z44 din dout f A y x hin hx hy hdist
  · intro h
    rw [z47 din dout f A h]
    exact le_top

theorem z70 (din dout : X → X → ENNReal)
    (f : Operator X bot) (A : Set X) (τσ τN ε : ENNReal)
    (hin : ∀ x y, din x y = din y x) (hout : ∀ x y, dout x y = dout y x)
    (hA : A.Nonempty) (hε : 0 < ε) (hdiam : diameter din A < τσ)
    (hthreshold : τσ ≤ τN) (hN : τN ≤ uniformRadius din dout f A A) :
    covering_number dout ε (f.func '' A) = 1 :=
  z65 dout f.func A hA ε hε
    ((z69 din dout f A τσ τN hin hout hdiam hthreshold).1 hN)

theorem z71 [Fintype I] (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (i j : I) (K : I → I → ENNReal)
    (hin : ExtendedPseudoMetric X bot (d i))
    (hK : IsCoLipMatrix d f U K) (hKpos : 0 < K i j)
    (y x : X) (hy : y ∈ U) (hx : x ∈ U)
    (hlt : d i x y < zeroRadius (d i) (d j) f y U) : d i x y = 0 := by
  have hz : d j (f.func x) (f.func y) = 0 := by
    apply z39 (d i) (d j) f y x U hin.symm hx
    rwa [hin.symm y x]
  exact positive_colip_entry_reflects_zero d f U K i j hK hKpos x hx y hy hz

theorem z72 [Fintype I] (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (i j : I) (K : I → I → ENNReal)
    (hin : ExtendedPseudoMetric X bot (d i))
    (hK : IsCoLipMatrix d f U K) (hKpos : 0 < K i j)
    (x y : X) (hx : x ∈ U) (hy : y ∈ U) :
    d i x y = 0 ∨ uniformRadius (d i) (d j) f U U ≤ d i x y := by
  by_cases h : uniformRadius (d i) (d j) f U U ≤ d i x y
  · exact Or.inr h
  · left
    apply z71 d f U i j K hin hK hKpos y x hy hx
    exact lt_of_lt_of_le (lt_of_not_ge h) (iInf₂_le y hy)

theorem z73 (din dout₁ dout₂ : X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (y : X)
    (h : ∀ x ∈ U, dout₁ (f.func x) (f.func y) = 0 →
      dout₂ (f.func x) (f.func y) = 0) :
    zeroRadius din dout₁ f y U ≤ zeroRadius din dout₂ f y U := by
  apply sSup_le
  intro r hr
  apply le_sSup
  exact ⟨hr.1, hr.2.1, fun x hx hxy => h x hx (hr.2.2 x hx hxy)⟩

theorem z74 (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (J K : Set I) (i : I) (hJK : J ⊆ K) :
    uniformRadius (d i) (subfamily_pseudometric d K) f U U ≤
      uniformRadius (d i) (subfamily_pseudometric d J) f U U := by
  apply le_iInf₂
  intro y hy
  calc
    uniformRadius (d i) (subfamily_pseudometric d K) f U U ≤
        zeroRadius (d i) (subfamily_pseudometric d K) f y U := iInf₂_le y hy
    _ ≤ zeroRadius (d i) (subfamily_pseudometric d J) f y U := by
      apply z73
      intro x _ hx
      apply (z10 d J _ _).2
      intro j hj
      exact (z10 d K _ _).1 hx j (hJK hj)

theorem z75 (din dmid dout : X → X → ENNReal)
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

theorem z76 (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (J : Set I) (i : I) (y : X) :
    zeroRadius (d i) (subfamily_pseudometric d J) f y U =
      ⨅ j : {j // j ∈ J}, zeroRadius (d i) (d j.1) f y U := by
  apply le_antisymm
  · apply le_iInf
    intro j
    apply z73
    intro x _ h
    exact (z10 d J _ _).1 h j.1 j.2
  · apply le_of_forall_lt
    intro r hr
    obtain ⟨s, hrs, hs⟩ := exists_between hr
    have hspos : 0 < s := lt_of_le_of_lt (zero_le r) hrs
    have hsfin : s < ⊤ := lt_of_lt_of_le hs le_top
    have hsvalid : z33 (d i) (subfamily_pseudometric d J) f y U s := by
      refine ⟨hspos, hsfin, ?_⟩
      intro x hx hdist
      apply (z10 d J _ _).2
      intro j hj
      have hsj : s < zeroRadius (d i) (d j) f y U :=
        lt_of_lt_of_le hs (iInf_le (fun j : {j // j ∈ J} =>
          zeroRadius (d i) (d j.1) f y U) ⟨j, hj⟩)
      obtain ⟨t, ht, hst⟩ := z38 (d i) (d j) f y U s hsj
      exact ht.2.2 x hx (lt_trans hdist hst)
    exact lt_of_lt_of_le hrs (z37 _ _ _ _ _ _ hsvalid)

theorem z77 (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (J : Set I) (i : I) :
    uniformRadius (d i) (subfamily_pseudometric d J) f U U =
      ⨅ j : {j // j ∈ J}, zeroMatrix d f U i j.1 := by
  unfold uniformRadius zeroMatrix
  simp_rw [z76]
  calc
    (⨅ y, ⨅ _ : y ∈ U, ⨅ j : {j // j ∈ J}, zeroRadius (d i) (d j.1) f y U) =
        ⨅ y, ⨅ j : {j // j ∈ J}, ⨅ _ : y ∈ U, zeroRadius (d i) (d j.1) f y U := by
      apply congrArg iInf
      funext y
      exact iInf_comm
    _ = ⨅ j : {j // j ∈ J}, ⨅ y, ⨅ _ : y ∈ U, zeroRadius (d i) (d j.1) f y U := iInf_comm

theorem z78 [Finite I] (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (J : Set I) (i : I) (hJ : J.Nonempty) :
    ∃ j ∈ J, uniformRadius (d i) (subfamily_pseudometric d J) f U U = zeroMatrix d f U i j ∧
      ∀ k ∈ J, zeroMatrix d f U i j ≤ zeroMatrix d f U i k := by
  letI : Nonempty {j // j ∈ J} := ⟨⟨hJ.choose, hJ.choose_spec⟩⟩
  obtain ⟨j, hj⟩ := exists_eq_ciInf_of_finite
    (f := fun j : {j // j ∈ J} => zeroMatrix d f U i j.1)
  refine ⟨j.1, j.2, ?_, ?_⟩
  · rw [z77]
    exact hj.symm
  · intro k hk
    rw [hj]
    exact iInf_le (fun j : {j // j ∈ J} => zeroMatrix d f U i j.1) ⟨k, hk⟩

theorem z79 [Finite I] (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (J : Set I) (i : I) (y : X) (hJ : J.Nonempty) :
    ∃ j ∈ J, zeroRadius (d i) (subfamily_pseudometric d J) f y U = zeroRadius (d i) (d j) f y U ∧
      ∀ k ∈ J, zeroRadius (d i) (d j) f y U ≤ zeroRadius (d i) (d k) f y U := by
  letI : Nonempty {j // j ∈ J} := ⟨⟨hJ.choose, hJ.choose_spec⟩⟩
  obtain ⟨j, hj⟩ := exists_eq_ciInf_of_finite
    (f := fun j : {j // j ∈ J} => zeroRadius (d i) (d j.1) f y U)
  refine ⟨j.1, j.2, ?_, ?_⟩
  · rw [z76]
    exact hj.symm
  · intro k hk
    rw [hj]
    exact iInf_le (fun j : {j // j ∈ J} => zeroRadius (d i) (d j.1) f y U) ⟨k, hk⟩

theorem z80 (din dmid dout : X → X → ENNReal)
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
  have hvalid : z33 din dout (g * f) y U s := by
    refine ⟨hspos, hsfin, ?_⟩
    intro x hx hdist
    have hmul : L * din x y < uniformRadius dmid dout g (f.func '' U) (f.func '' U) :=
      ENNReal.mul_lt_of_lt_div' (lt_trans hdist hs)
    have hdist' : dmid (f.func y) (f.func x) <
        uniformRadius dmid dout g (f.func '' U) (f.func '' U) := by
      rw [hmid (f.func y) (f.func x)]
      exact lt_of_le_of_lt (hlip x hx y hy) hmul
    exact z44 dmid dout g (f.func '' U) (f.func y) (f.func x) hmid
      ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩ hdist'
  exact lt_of_lt_of_le hrs (z37 _ _ _ _ _ _ hvalid)

theorem z81 (din dout : X → X → ENNReal)
    (f : Operator X bot) (A : Set X) (α : ENNReal)
    (hα : 0 < α) (hαfin : α < ⊤)
    (hlt : uniformRadius din dout f A A < α) :
    ∃ x ∈ A, ∃ y ∈ A, ∃ ε : ENNReal,
      0 < ε ∧ ε < ⊤ ∧ din x y < α ∧ ε ≤ dout (f.func x) (f.func y) := by
  classical
  obtain ⟨y, hy, hyr⟩ := iInf_lt_iff.mp hlt |>.imp fun _ h => iInf_lt_iff.mp h
  have hn : ¬ z33 din dout f y A α := by
    intro ha
    exact (not_lt_of_ge (z37 din dout f y A α ha)) hyr
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

theorem z82 (din dout : X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (L ε : ENNReal)
    (hlip : ∀ x ∈ U, ∀ y ∈ U, dout (f.func x) (f.func y) ≤ L * din x y) :
    covering_number dout ε (f.func '' U) ≤ covering_number din (ε / L) U := by
  apply z63
  intro x hx y hy hdist
  exact lt_of_le_of_lt (hlip x hx y hy) (ENNReal.mul_lt_of_lt_div' hdist)

theorem colip_cover [Fintype I] (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (i j : I) (K : I → I → ENNReal)
    (ε : ENNReal) (hK : IsCoLipMatrix d f U K)
    (hpos : 0 < K i j) (hfin : K i j < ⊤) :
    covering_number (d i) (ε / K i j) U ≤ covering_number (d j) ε (f.func '' U) := by
  classical
  apply z64 _ _ _ bot
  intro x hx y hy hout
  apply (ENNReal.lt_div_iff_mul_lt (Or.inl (ne_of_gt hpos)) (Or.inl (ne_of_lt hfin))).2
  have hterm : K i j * d i x y ≤ ∑ k : I, K k j * d k x y :=
    Finset.single_le_sum (fun k _ => zero_le (K k j * d k x y)) (Finset.mem_univ i)
  have hbound := hterm.trans (hK.2.2 x hx y hy j)
  simpa [mul_comm] using lt_of_le_of_lt hbound hout

theorem z83 (d : X → X → ENNReal)
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

theorem z84 (f : Operator X bot) (U : Set X) (v : X)
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

theorem z85 (d : X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (v : X)
    (hself : ∀ x, d x x = 0) (hv : ∀ x ∈ U, f.func x = v) :
    ∀ x ∈ U, ∀ y ∈ U, d ((f * f).func x) ((f * f).func y) = 0 := by
  intro x hx y hy
  rw [(z84 f U v hv).1 x hx y hy, hself]

theorem z86 {a b : ENNReal}
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

theorem z87 (din dout : X → X → ENNReal)
    (A B : Set X) (δ ε : ENNReal) (hA : A.Nonempty) (hB : B.Nonempty)
    (hcover : covering_number dout ε B ≤ covering_number din δ A) :
    metric_entropy dout ε B ≤ metric_entropy din δ A := by
  exact z86
    (one_le_covering_number_of_nonempty dout ε B hB) hcover

theorem z88 (din dout : X → X → ENNReal)
    (f : Operator X bot) (A B : Set X) (τ ε : ENNReal)
    (hin : ∀ x y, din x y = din y x) (hBA : B ⊆ A) (hB : B.Nonempty)
    (hτ : τ ≤ uniformRadius din dout f A A) (hε : 0 < ε) :
    metric_entropy dout ε (f.func '' B) ≤ metric_entropy din τ B :=
  z87 din dout B (f.func '' B) τ ε hB (hB.image f.func)
    (z68 din dout f A B τ ε hin hBA hτ hε)

theorem z89 (d : X → X → ENNReal) (U : Set X) (ε : ENNReal)
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

theorem z90 (d : X → X → ENNReal) (U : Set X) (ε : ENNReal)
    (hne : U.Nonempty) (hU : U.Finite) (hε : 0 < ε) (hself : ∀ x ∈ U, d x x = 0) :
    1 ≤ covering_number d ε U ∧ covering_number d ε U < ⊤ :=
  ⟨one_le_covering_number_of_nonempty d ε U hne, z89 d U ε hU hε hself⟩

theorem z91 (d : X → X → ENNReal) (U : Set X) (ε : ENNReal)
    (hne : U.Nonempty) (hfin : covering_number d ε U < ⊤) :
    ∃ r : ℝ, metric_entropy d ε U = (r : EReal) := by
  have h1 := one_le_covering_number_of_nonempty d ε U hne
  have h0 : covering_number d ε U ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one h1)
  refine ⟨Real.logb 2 (covering_number d ε U).toReal, ?_⟩
  simp [metric_entropy, log2_ereal, h0, ne_of_lt hfin]

theorem z92 (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (Jin Jout : Set I) (ε : ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (hne : U.Nonempty) (hdom : U ⊆ dom f) (hfinite : U.Finite)
    (hJin : Jin.Nonempty) (hJout : Jout.Nonempty) (hε : 0 < ε) (hεfin : ε < ⊤) :
    (covering_number (subfamily_pseudometric d Jin) ε U < ⊤ ∧
      covering_number (subfamily_pseudometric d Jout) ε (f.func '' U) < ⊤) ∧
    (∃ r s : ℝ, subfamily_metric_entropy d Jin ε U = (r : EReal) ∧
      subfamily_metric_entropy d Jout ε (f.func '' U) = (s : EReal)) ∧
    z58 d f U Jin Jout ε := by
  have self : ∀ J x, subfamily_pseudometric d J x x = 0 := by
    intro J x
    exact (z10 d J x x).2 (fun j _ => (hd j).dist_self x)
  have hin : covering_number (subfamily_pseudometric d Jin) ε U < ⊤ :=
    z89 _ U ε hfinite hε (fun x _ => self _ x)
  have hout : covering_number (subfamily_pseudometric d Jout) ε (f.func '' U) < ⊤ :=
    z89 _ _ ε (hfinite.image f.func) hε (fun x _ => self _ x)
  have ⟨r, hr⟩ := z91 _ U ε hne hin
  have ⟨s, hs⟩ := z91 _ (f.func '' U) ε (hne.image f.func) hout
  exact ⟨⟨hin, hout⟩, ⟨r, s, hr, hs⟩,
    ⟨hne, hdom, hJin, hJout, hε, hεfin, Or.inl hin⟩⟩

theorem z93 (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (i : I) (ε : ENNReal)
    (hne : U.Nonempty) (hε : 0 < ε) (hc : i ∈ z0 d f U)
    (hvalid : z58 d f U {i} {i} ε) :
    covering_number (d i) ε (f.func '' U) = 1 ∧
    metric_entropy (d i) ε (f.func '' U) = 0 ∧
    z59 d f U {i} {i} ε hvalid = metric_entropy (d i) ε U := by
  have hcover := z65 (d i) f.func U hne ε hε hc
  have hout : metric_entropy (d i) ε (f.func '' U) = 0 := by
    simp [metric_entropy, log2_ereal, hcover]
  refine ⟨hcover, hout, ?_⟩
  simp [z59, subfamily_metric_entropy_singleton, hout]

theorem z94 (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (i : I) (ε : ENNReal)
    (hd : ExtendedPseudoMetric X bot (d i)) (hne : U.Nonempty)
    (hi : i ∈ z1 d f U)
    (hvalid : z58 d f U {i} {i} ε) :
    z59 d f U {i} {i} ε hvalid = 0 := by
  have hc := (z66 d f U i ε hd hi).1
  have hfin : covering_number (d i) ε U < ⊤ := by
    have h := hvalid.2.2.2.2.2.2
    rw [subfamily_pseudometric_singleton] at h
    rcases h with h | h
    · exact h
    · rwa [hc] at h
  obtain ⟨r, hr⟩ := z91 (d i) U ε hne hfin
  have heq := (z66 d f U i ε hd hi).2
  simp only [z59, subfamily_metric_entropy_singleton, heq, hr, ← EReal.coe_sub]
  simp

theorem z95 (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (i j : I) (ε L : ENNReal)
    (hU : U.Nonempty) (hdom : U ⊆ dom f)
    (htot : z57 (d i) U)
    (hε : 0 < ε) (hεfin : ε < ⊤) (hL : 0 < L) (hLfin : L < ⊤)
    (hlip : ∀ x ∈ U, ∀ y ∈ U, d j (f.func x) (f.func y) ≤ L * d i x y) :
    ∃ hv : z58 d f U {i} {j} ε,
      covering_number (d j) ε (f.func '' U) < ⊤ ∧
      (∃ a b : ℝ, metric_entropy (d i) ε U = (a : EReal) ∧
        metric_entropy (d j) ε (f.func '' U) = (b : EReal)) ∧
      metric_entropy (d i) ε U - metric_entropy (d i) (ε / L) U ≤
        z59 d f U {i} {j} ε hv := by
  have hdivpos : 0 < ε / L := ENNReal.div_pos (ne_of_gt hε) (ne_of_lt hLfin)
  have hdivfin : ε / L < ⊤ := ENNReal.div_lt_top (ne_of_lt hεfin) (ne_of_gt hL)
  have hin := htot ε hε hεfin
  have hscale := htot (ε / L) hdivpos hdivfin
  have hcover := z82 (d i) (d j) f U L ε hlip
  have hout : covering_number (d j) ε (f.func '' U) < ⊤ := lt_of_le_of_lt hcover hscale
  have hv : z58 d f U {i} {j} ε := by
    refine ⟨hU, hdom, Set.singleton_nonempty _, Set.singleton_nonempty _, hε, hεfin, Or.inl ?_⟩
    simpa [subfamily_pseudometric_singleton] using hin
  have hlog := z87 (d i) (d j) U (f.func '' U) (ε / L) ε
    hU (hU.image f.func) hcover
  obtain ⟨a, ha⟩ := z91 (d i) U ε hU hin
  obtain ⟨b, hb⟩ := z91 (d j) (f.func '' U) ε (hU.image f.func) hout
  refine ⟨hv, hout, ⟨a, b, ha, hb⟩, ?_⟩
  simpa only [z59, subfamily_metric_entropy_singleton] using
    (EReal.sub_le_sub (le_refl (metric_entropy (d i) ε U)) hlog)

theorem z96 [Fintype I] (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (i j : I) (ε : ENNReal)
    (K : I → I → ENNReal) (hU : U.Nonempty) (hdom : U ⊆ dom f)
    (htot : z57 (d i) U)
    (hε : 0 < ε) (hεfin : ε < ⊤) (hK : IsCoLipMatrix d f U K)
    (hpos : 0 < K i j) (hfin : K i j < ⊤) :
    ∃ hv : z58 d f U {i} {j} ε,
      (∃ a b : ℝ, metric_entropy (d i) ε U = (a : EReal) ∧
        metric_entropy (d i) (ε / K i j) U = (b : EReal)) ∧
      z59 d f U {i} {j} ε hv ≤
        metric_entropy (d i) ε U - metric_entropy (d i) (ε / K i j) U := by
  have hdivpos : 0 < ε / K i j := ENNReal.div_pos (ne_of_gt hε) (ne_of_lt hfin)
  have hdivfin : ε / K i j < ⊤ := ENNReal.div_lt_top (ne_of_lt hεfin) (ne_of_gt hpos)
  have hin := htot ε hε hεfin
  have hscale := htot (ε / K i j) hdivpos hdivfin
  have hcover := colip_cover d f U i j K ε hK hpos hfin
  have hv : z58 d f U {i} {j} ε := by
    refine ⟨hU, hdom, Set.singleton_nonempty _, Set.singleton_nonempty _, hε, hεfin, Or.inl ?_⟩
    simpa [subfamily_pseudometric_singleton] using hin
  have hlog := z87 (d j) (d i) (f.func '' U) U ε (ε / K i j)
    (hU.image f.func) hU hcover
  obtain ⟨a, ha⟩ := z91 (d i) U ε hU hin
  obtain ⟨b, hb⟩ := z91 (d i) U (ε / K i j) hU hscale
  refine ⟨hv, ⟨a, b, ha, hb⟩, ?_⟩
  simpa only [z59, subfamily_metric_entropy_singleton] using
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

theorem swap_not_const : () ∉ z0 gauge swap U := by
  intro h
  have h' := h (some false) (by simp [U]) (some true) (by simp [U])
  simp [gauge, dist, swap, Option.some_ne_none] at h'

theorem z97 : () ∉ z1 gauge swap U := by
  intro h
  have h' := h.2 (some false) (by simp [U])
  simp [gauge, dist, swap, Option.some_ne_none] at h'

theorem swap_active : () ∈ z2 gauge swap U := by
  simp only [z2, mem_compl_iff, mem_union, not_or]
  exact ⟨swap_not_const, z97⟩

theorem id_not_const : () ∉ z0 gauge (1 : Operator Point none) U := by
  intro h
  have h' := h (some false) (by simp [U]) (some true) (by simp [U])
  change dist (some false) (some true) = 0 at h'
  simp [dist, Option.some_ne_none] at h'

theorem z98 : () ∈ z1 gauge (swap * swap) U := by
  rw [square]
  refine ⟨id_not_const, ?_⟩
  intro x hx
  exact metric.dist_self x

theorem z99 :
    () ∈ z2 gauge swap U ∧
    () ∈ z2 gauge swap (swap.func '' U) ∧
    () ∉ z2 gauge (swap * swap) U ∧
    () ∉ z1 gauge swap U ∧
    () ∉ z1 gauge swap (swap.func '' U) ∧
    () ∈ z1 gauge (swap * swap) U := by
  refine ⟨swap_active, ?_, ?_, z97, ?_, z98⟩
  · simpa only [image_U] using swap_active
  · intro h
    exact h (Or.inr z98)
  · simpa only [image_U] using z97

theorem z100 :
    z2 gauge swap U = univ ∧
    z1 gauge swap U = ∅ ∧
    z2 gauge (swap * swap) U = ∅ ∧
    z1 gauge (swap * swap) U = univ := by
  have h := z99
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i
    cases i
    simpa using swap_active
  · ext i
    cases i
    simpa using z97
  · ext i
    cases i
    simpa using h.2.2.1
  · ext i
    cases i
    simpa using z98

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

theorem z101 : diameter dist ({some false} : Set Point) = 0 := by
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

def z102 : Option ℝ → Option ℝ → ENNReal
  | none, none => 0
  | none, some _ => ⊤
  | some _, none => ⊤
  | some x, some y => ENNReal.ofReal |x - y|

theorem z103 (x y : Point) :
    z102 (intoReal x) (intoReal y) = dist x y := by
  rcases x with _ | (_ | _) <;> rcases y with _ | (_ | _) <;>
    simp [intoReal, z102, dist, Option.some_ne_none] <;> norm_num

theorem z104 :
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
  · rw [z101, diameter_U]
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

theorem z105 (i : Bool) : ExtendedPseudoMetric Point none (twoGauge i) := by
  cases i
  · exact infiniteMetric
  · exact metric

theorem z106 (dout : Point → Point → ENNReal)
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
      apply z37
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

theorem z107 :
    zeroMatrix twoGauge (1 : Operator Point none) U false false = ⊤ ∧
    false ∉ z0 twoGauge (1 : Operator Point none) U ∧
    zeroMatrix twoGauge (1 : Operator Point none) U false true = ⊤ ∧
    true ∉ z0 twoGauge (1 : Operator Point none) U := by
  have hnot₁ : false ∉ z0 twoGauge (1 : Operator Point none) U := by
    intro h
    have h' := h (some false) (by simp [U]) (some true) (by simp [U])
    change infiniteDist (some false) (some true) = 0 at h'
    simp [infiniteDist] at h'
  have hnot₂ : true ∉ z0 twoGauge (1 : Operator Point none) U := by
    intro h
    have h' := h (some false) (by simp [U]) (some true) (by simp [U])
    change dist (some false) (some true) = 0 at h'
    simp [dist, Option.some_ne_none] at h'
  exact ⟨z106 infiniteDist infiniteMetric.dist_self, hnot₁,
    z106 dist metric.dist_self, hnot₂⟩

end SwapExample

end Chapter3

