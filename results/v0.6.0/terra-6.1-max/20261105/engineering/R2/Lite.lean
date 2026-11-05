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

theorem diameter_upper (d : X → X → ENNReal) (A : Set X)
    (x y : X) (hx : x ∈ A) (hy : y ∈ A) : d x y ≤ diameter d A :=
  le_iSup_of_le x (le_iSup_of_le hx (le_iSup_of_le y (le_iSup_of_le hy le_rfl)))

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

namespace Chapter3.SevenExample

open formal_oet.vol_01.ch_01_foundations

abbrev Point := Option (Fin 6)

def a : Point := some 0
def b : Point := some 1
def p : Point := some 2
def q : Point := some 3
def r : Point := some 4
def s : Point := some 5

def discrete : Point → Point → ENNReal
  | none, none => 0
  | none, some _ => ⊤
  | some _, none => ⊤
  | some x, some y => if x = y then 0 else 1

theorem discrete_self (x : Point) : discrete x x = 0 := by
  cases x <;> simp [discrete]

theorem discrete_symm (x y : Point) : discrete x y = discrete y x := by
  cases x <;> cases y <;> simp [discrete, eq_comm]

theorem discrete_triangle (x y z : Point) :
    discrete x z ≤ discrete x y + discrete y z := by
  cases x with
  | none => cases y <;> cases z <;> simp [discrete]
  | some x =>
    cases y with
    | none => cases z <;> simp [discrete]
    | some y =>
      cases z with
      | none => simp [discrete]
      | some z =>
        by_cases hxy : x = y <;> by_cases hyz : y = z <;>
          by_cases hxz : x = z <;> simp_all [discrete]

def readout (i : Bool) : Point → Point
  | none => none
  | some x => some (if i = false ∧ x = 3 then 2 else x)

def gauge (i : Bool) (x y : Point) : ENNReal :=
  discrete (readout i x) (readout i y)

theorem gauge_metric (i : Bool) : ExtendedPseudoMetric Point none (gauge i) := by
  constructor
  · exact ⟨a, by decide⟩
  · intro x
    exact discrete_self (readout i x)
  · intro x y
    exact discrete_symm _ _
  · intro x y z
    exact discrete_triangle _ _ _
  · intro x hx
    cases x with
    | none => contradiction
    | some x => simp [gauge, readout, discrete]

theorem first_readout (x y : Fin 6) :
    gauge false (some x) (some y) =
      if x = y ∨ (x = 2 ∧ y = 3) ∨ (x = 3 ∧ y = 2) then 0 else 1 := by
  fin_cases x <;> fin_cases y <;> norm_num [gauge, readout, discrete, Fin.ext_iff]

theorem second_readout (x y : Fin 6) :
    gauge true (some x) (some y) = if x = y then 0 else 1 := by
  simp [gauge, readout, discrete]

def U : Set Point := {a, b}

def inner : Operator Point none where
  func x := if x = a then p else if x = b then q else none
  preserves_bot := by simp [a, b]

def outer : Operator Point none where
  func x := if x = p then r else if x = q then s else none
  preserves_bot := by simp [p, q]

theorem domain_U : U ⊆ dom (outer * inner) := by
  intro x hx
  simp only [U, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · change (outer * inner).func a ≠ none
    have h : (outer * inner).func a = r := rfl
    rw [h]
    decide
  · change (outer * inner).func b ≠ none
    have h : (outer * inner).func b = s := rfl
    rw [h]
    decide

theorem image_U : inner.func '' U = {p, q} := by
  ext x
  simp [U, inner, a, b, p, q, eq_comm, Fin.ext_iff]

theorem computation :
    false ∈ z0 gauge inner U ∧
    false ∉ z0 gauge (outer * inner) U ∧
    gauge false p q = 0 ∧ gauge true p q = 1 ∧ gauge false r s = 1 := by
  have h : false ∈ z0 gauge inner U := by
    intro x hx y hy
    simp only [U, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
      norm_num [inner, gauge, readout, discrete, a, b, p, q, Fin.ext_iff]
  refine ⟨h, ?_, ?_⟩
  · intro h'
    have hc := h' a (by simp [U]) b (by simp [U])
    change gauge false (outer.func (inner.func a)) (outer.func (inner.func b)) = 0 at hc
    norm_num [inner, outer, gauge, readout, discrete, a, b, p, q, r, s, Fin.ext_iff] at hc
  · norm_num [gauge, readout, discrete, p, q, r, s, Fin.ext_iff]

end Chapter3.SevenExample

namespace Chapter3.AbsoluteExample

open formal_oet.vol_01.ch_01_foundations

abbrev Point := Option ℝ

def dist : Point → Point → ENNReal
  | none, none => 0
  | none, some _ => ⊤
  | some _, none => ⊤
  | some x, some y => edist |x| |y|

theorem metric : ExtendedPseudoMetric Point none dist := by
  constructor
  · exact ⟨some 0, by decide⟩
  · intro x
    cases x <;> simp [dist]
  · intro x y
    cases x <;> cases y <;> simp [dist, edist_comm]
  · intro x y z
    cases x <;> cases y <;> cases z <;> simp [dist, edist_triangle]
  · intro x hx
    cases x <;> simp_all [dist]

def gauge (_ : Unit) : Point → Point → ENNReal := dist
def U : Set Point := {some 0, some 1}

def phi : Operator Point none where
  func := Option.map (fun x : ℝ => 2 * x - 1)
  preserves_bot := rfl

def square : Operator Point none := phi * phi

theorem phi_zero : phi.func (some 0) = some (-1) := by
  simp [phi]

theorem phi_one : phi.func (some 1) = some 1 := by
  norm_num [phi]

theorem square_zero : square.func (some 0) = some (-3) := by
  change some (2 * (2 * (0 : ℝ) - 1) - 1) = some (-3)
  norm_num

theorem square_one : square.func (some 1) = some 1 := by
  change some (2 * (2 * (1 : ℝ) - 1) - 1) = some 1
  norm_num

theorem domain : U ⊆ dom phi ∧ U ⊆ dom square := by
  constructor <;> intro x hx
  all_goals
    simp only [U, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
  · change phi.func (some 0) ≠ none
    simp [phi_zero]
  · change phi.func (some 1) ≠ none
    simp [phi_one]
  · change square.func (some 0) ≠ none
    simp [square_zero]
  · change square.func (some 1) ≠ none
    simp [square_one]

theorem first_const : () ∈ z0 gauge phi U := by
  intro x hx y hy
  simp only [U, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
    simp [gauge, phi_zero, phi_one, dist]

theorem first_type :
    () ∈ z0 gauge phi U ∧ () ∉ z1 gauge phi U ∧ () ∉ z2 gauge phi U := by
  refine ⟨first_const, ?_, ?_⟩
  · intro h
    exact h.1 first_const
  · intro h
    exact h (Or.inl first_const)

theorem first_fiber :
    componentFiber gauge phi () (phi.func (some 0)) U = U := by
  ext x
  constructor
  · exact fun hx => hx.1
  · intro hx
    exact ⟨hx, first_const x hx (some 0) (by simp [U])⟩

theorem square_fiber :
    componentFiber gauge square () (square.func (some 0)) U = {some 0} := by
  ext x
  constructor
  · rintro ⟨hx, hz⟩
    simp only [U, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · simp
    · norm_num [gauge, square_zero, square_one, dist, edist_dist, Real.dist_eq] at hz
  · intro hx
    have hx' : x = some 0 := Set.mem_singleton_iff.mp hx
    subst x
    exact ⟨by simp [U], by simp [gauge, square_zero, dist]⟩

theorem square_active : () ∈ z2 gauge square U := by
  have hconst : () ∉ z0 gauge square U := by
    intro h
    have hh := h (some 0) (by simp [U]) (some 1) (by simp [U])
    norm_num [gauge, square_zero, square_one, dist, edist_dist, Real.dist_eq] at hh
  have hid : () ∉ z1 gauge square U := by
    intro h
    have hh := h.2 (some 0) (by simp [U])
    norm_num [gauge, square_zero, dist, edist_dist, Real.dist_eq] at hh
  exact fun h => h.elim hconst hid

def Ufour : Set Point := {some (-3), some (-2), some 0, some 2}

def shift : Operator Point none where
  func := Option.map (fun x : ℝ => x + 1)
  preserves_bot := rfl

@[simp] theorem identity_some (x : ℝ) : (1 : Operator Point none).func (some x) = some x := rfl

theorem four_fibers :
    componentFiber gauge (1 : Operator Point none) () (some (-3)) Ufour = {some (-3), some (-3)} ∧
    componentFiber gauge (1 : Operator Point none) () (some (-2)) Ufour = {some (-2), some 2} ∧
    componentFiber gauge (1 : Operator Point none) () (some 0) Ufour = {some 0, some 0} ∧
    componentFiber gauge (1 : Operator Point none) () (some 2) Ufour = {some (-2), some 2} ∧
    componentFiber gauge shift () (some (-2)) Ufour = {some (-3), some (-3)} ∧
    componentFiber gauge shift () (some (-1)) Ufour = {some (-2), some 0} ∧
    componentFiber gauge shift () (some 1) Ufour = {some (-2), some 0} ∧
    componentFiber gauge shift () (some 3) Ufour = {some 2, some 2} := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    ext x
    constructor
    · rintro ⟨hx, hz⟩
      simp only [Ufour, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl <;>
        norm_num [gauge, dist, edist_dist, Real.dist_eq, shift] at *
    · intro hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl <;>
        norm_num [componentFiber, Ufour, gauge, dist, edist_dist, Real.dist_eq, shift]

theorem identity_image : (1 : Operator Point none).func '' Ufour = Ufour := by
  ext x
  simp [Ufour, eq_comm]

theorem shift_image : shift.func '' Ufour = {some (-2), some (-1), some 1, some 3} := by
  ext x
  norm_num [Ufour, shift, eq_comm]

theorem four_domain : Ufour ⊆ dom shift ∧ Ufour ⊆ dom (1 : Operator Point none) := by
  constructor <;> intro x hx <;>
    simp only [Ufour, Set.mem_insert_iff, Set.mem_singleton_iff] at hx <;>
    rcases hx with rfl | rfl | rfl | rfl <;>
    simp [dom, shift]

theorem input_cover : covering_number dist (3 / 2) Ufour = 2 := by
  classical
  have h13 : (1 : ENNReal) < 3 / 2 := by
    rw [ENNReal.lt_div_iff_mul_lt (Or.inl (by norm_num)) (Or.inl (by simp))]
    norm_num
  have h32 : (3 / 2 : ENNReal) < 2 := by
    rw [ENNReal.div_lt_iff (Or.inl (by norm_num)) (Or.inl (by simp))]
    norm_num
  have hnet : InternalEpsilonNet dist (3 / 2) Ufour {some (-3), some 0} := by
    constructor
    · intro c hc
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl <;> simp [Ufour]
    · intro x hx
      simp only [Ufour, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact ⟨some (-3), by simp, by norm_num [dist]⟩
      · refine ⟨some (-3), by simp, ?_⟩
        norm_num [dist, edist_dist, Real.dist_eq]
        exact h13
      · exact ⟨some 0, by simp, by norm_num [dist]⟩
      · refine ⟨some (-3), by simp, ?_⟩
        norm_num [dist, edist_dist, Real.dist_eq]
        exact h13
  apply le_antisymm
  · have h : covering_number dist (3 / 2) Ufour ≤
        (({some (-3), some 0} : Finset Point).card : ENNReal) :=
      iInf_le_of_le _ (iInf_le_of_le hnet le_rfl)
    simpa [covering_number] using h
  · unfold covering_number
    apply le_iInf
    intro S
    apply le_iInf
    intro hS
    have hcard : 2 ≤ S.card := by
      by_contra hn
      have hsmall : S.card ≤ 1 := by omega
      obtain ⟨c, hc, _⟩ := hS.2 (some 0) (by simp [Ufour])
      have hcU : c ∈ Ufour := hS.1 hc
      have hnear : ∀ x ∈ Ufour, dist x c < 3 / 2 := by
        intro x hx
        obtain ⟨z, hz, hdist⟩ := hS.2 x hx
        have heq : z = c := (Finset.card_le_one.mp hsmall) z hz c hc
        simpa [heq] using hdist
      simp only [Ufour, Set.mem_insert_iff, Set.mem_singleton_iff] at hcU
      rcases hcU with rfl | rfl | rfl | rfl
      · have h := hnear (some 0) (by simp [Ufour])
        norm_num [dist, edist_dist, Real.dist_eq] at h
        exact (not_lt_of_ge ((le_of_lt h32).trans (by norm_num))) h
      · have h := hnear (some 0) (by simp [Ufour])
        norm_num [dist, edist_dist, Real.dist_eq] at h
        exact (not_lt_of_ge (le_of_lt h32)) h
      · have h := hnear (some (-3)) (by simp [Ufour])
        norm_num [dist, edist_dist, Real.dist_eq] at h
        exact (not_lt_of_ge ((le_of_lt h32).trans (by norm_num))) h
      · have h := hnear (some 0) (by simp [Ufour])
        norm_num [dist, edist_dist, Real.dist_eq] at h
        exact (not_lt_of_ge (le_of_lt h32)) h
    exact_mod_cast hcard

theorem output_cover : covering_number dist (3 / 2) (shift.func '' Ufour) = 1 := by
  classical
  have h13 : (1 : ENNReal) < 3 / 2 := by
    rw [ENNReal.lt_div_iff_mul_lt (Or.inl (by norm_num)) (Or.inl (by simp))]
    norm_num
  apply le_antisymm
  · have hnet : InternalEpsilonNet dist (3 / 2) (shift.func '' Ufour) {some (-2)} := by
      rw [shift_image]
      constructor
      · intro c hc
        simp only [Finset.mem_coe, Finset.mem_singleton] at hc
        subst c
        simp
      · intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        refine ⟨some (-2), by simp, ?_⟩
        rcases hx with rfl | rfl | rfl | rfl <;>
          norm_num [dist, edist_dist, Real.dist_eq] <;> exact h13
    have h : covering_number dist (3 / 2) (shift.func '' Ufour) ≤
        (({some (-2)} : Finset Point).card : ENNReal) :=
      iInf_le_of_le _ (iInf_le_of_le hnet le_rfl)
    simpa [covering_number] using h
  · apply one_le_covering_number_of_nonempty
    exact ⟨shift.func (some 0), ⟨some 0, by simp [Ufour], rfl⟩⟩

theorem four_entropy :
    ∃ hv : z58 gauge shift Ufour {()} {()} (3 / 2),
      z59 gauge shift Ufour {()} {()} (3 / 2) hv = 1 := by
  have hv : z58 gauge shift Ufour {()} {()} (3 / 2) := by
    refine ⟨⟨some 0, by simp [Ufour]⟩, four_domain.1, by simp, by simp,
      by norm_num, ENNReal.div_lt_top (by simp) (by norm_num), Or.inl ?_⟩
    rw [subfamily_pseudometric_singleton]
    change covering_number dist (3 / 2) Ufour < ⊤
    rw [input_cover]
    norm_num
  refine ⟨hv, ?_⟩
  simp [z59, subfamily_metric_entropy_singleton, metric_entropy, log2_ereal,
    gauge, input_cover, output_cover]

end Chapter3.AbsoluteExample

namespace Chapter3.FloorExample

open formal_oet.vol_01.ch_01_foundations

abbrev Point := Option ℝ

def dist : Point → Point → ENNReal
  | none, none => 0
  | none, some _ => ⊤
  | some _, none => ⊤
  | some x, some y => edist x y

theorem metric : ExtendedPseudoMetric Point none dist := by
  constructor
  · exact ⟨some 0, by decide⟩
  · intro x
    cases x <;> simp [dist]
  · intro x y
    cases x <;> cases y <;> simp [dist, edist_comm]
  · intro x y z
    cases x <;> cases y <;> cases z <;> simp [dist, edist_triangle]
  · intro x hx
    cases x <;> simp_all [dist]

def gauge (_ : Unit) : Point → Point → ENNReal := dist

noncomputable def f : Operator Point none where
  func := Option.map (fun x : ℝ => (Int.floor x : ℝ))
  preserves_bot := rfl

def D : Set Point := {some 0, some 2}

theorem fzero : f.func (some 0) = some 0 := by simp [f]
theorem ftwo : f.func (some 2) = some 2 := by norm_num [f]

theorem D_nonempty : D.Nonempty := ⟨some 0, by simp [D]⟩

theorem D_domain : D ⊆ dom f := by
  intro x hx
  simp only [D, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · change f.func (some 0) ≠ none
    simp [fzero]
  · change f.func (some 2) ≠ none
    simp [ftwo]

theorem diameter_D : diameter dist D = 2 := by
  apply le_antisymm
  · apply iSup_le
    intro x
    apply iSup_le
    intro hx
    apply iSup_le
    intro y
    apply iSup_le
    intro hy
    simp only [D, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
      norm_num [dist, edist_dist, Real.dist_eq]
  · have h := diameter_upper dist D (some 0) (some 2) (by simp [D]) (by simp [D])
    norm_num [dist, edist_dist, Real.dist_eq] at h ⊢
    exact h

theorem radius_D (y : Point) (hy : y ∈ D) : zeroRadius dist dist f y D = 2 := by
  simp only [D, Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with rfl | rfl
  · apply le_antisymm
    · apply sSup_le
      intro t ht
      by_contra hn
      have htwo : (2 : ENNReal) < t := lt_of_not_ge hn
      have h := ht.2.2 (some 2) (by simp [D]) (by
        simpa [dist, edist_dist, Real.dist_eq] using htwo)
      norm_num [fzero, ftwo, dist, edist_dist, Real.dist_eq] at h
    · apply z37
      refine ⟨by norm_num, by norm_num, ?_⟩
      intro x hx hdist
      simp only [D, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · simp [fzero, dist]
      · norm_num [dist, edist_dist, Real.dist_eq] at hdist
  · apply le_antisymm
    · apply sSup_le
      intro t ht
      by_contra hn
      have htwo : (2 : ENNReal) < t := lt_of_not_ge hn
      have h := ht.2.2 (some 0) (by simp [D]) (by
        simpa [dist, edist_dist, Real.dist_eq] using htwo)
      norm_num [fzero, ftwo, dist, edist_dist, Real.dist_eq] at h
    · apply z37
      refine ⟨by norm_num, by norm_num, ?_⟩
      intro x hx hdist
      simp only [D, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · norm_num [dist, edist_dist, Real.dist_eq] at hdist
      · simp [ftwo, dist]

theorem uniform_D : uniformRadius dist dist f D D = 2 := by
  apply le_antisymm
  · exact (iInf₂_le (some 0) (show some 0 ∈ D by simp [D])).trans
      (le_of_eq (radius_D (some 0) (by simp [D])))
  · apply le_iInf₂
    intro y hy
    rw [radius_D y hy]

theorem classification_D :
    diameter dist D = 2 ∧ uniformRadius dist dist f D D = 2 ∧
      thresholdType (diameterScale gauge) gauge f D 1 1 () () = (false, true) := by
  refine ⟨diameter_D, uniform_D, ?_⟩
  apply (z53 (diameterScale gauge) gauge f D 1 1 () ()).2.2.1.mpr
  change (1 : ENNReal) ≤ diameter dist D ∧ 1 ≤ uniformRadius dist dist f D D
  rw [diameter_D, uniform_D]
  norm_num

theorem not_global_zero :
    (1 : ENNReal) ≤ uniformRadius dist dist f D D ∧
      ∃ x ∈ D, ∃ y ∈ D, dist (f.func x) (f.func y) ≠ 0 := by
  refine ⟨?_, some 0, by simp [D], some 2, by simp [D], ?_⟩
  · rw [uniform_D]
    norm_num
  · norm_num [fzero, ftwo, dist, edist_dist, Real.dist_eq]

def Dsmall : Set Point := some '' Set.Icc (0 : ℝ) (1 / 2)

theorem Dsmall_nonempty : Dsmall.Nonempty :=
  ⟨some 0, ⟨0, by norm_num, rfl⟩⟩

theorem Dsmall_domain : Dsmall ⊆ dom f := by
  rintro x ⟨t, ht, rfl⟩
  change some ((Int.floor t : ℤ) : ℝ) ≠ none
  simp

theorem Dsmall_constant (x : Point) (hx : x ∈ Dsmall) : f.func x = some 0 := by
  obtain ⟨t, ht, rfl⟩ := hx
  have hfloor : Int.floor t = 0 := Int.floor_eq_iff.mpr (by
    constructor
    · simpa using ht.1
    · have : t < (1 : ℝ) := by linarith [ht.2]
      simpa using this)
  simp [f, hfloor]

theorem diameter_Dsmall : diameter dist Dsmall = (1 / 2 : ENNReal) := by
  have half : ENNReal.ofReal (1 / 2 : ℝ) = (1 / 2 : ENNReal) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  apply le_antisymm
  · apply iSup_le
    intro x
    apply iSup_le
    intro hx
    apply iSup_le
    intro y
    apply iSup_le
    intro hy
    obtain ⟨t, ht, rfl⟩ := hx
    obtain ⟨u, hu, rfl⟩ := hy
    have h : |t - u| ≤ (1 / 2 : ℝ) := abs_le.mpr ⟨by linarith [ht.1, hu.2], by linarith [ht.2, hu.1]⟩
    calc
      dist (some t) (some u) = ENNReal.ofReal |t - u| := by
        simp [dist, edist_dist, Real.dist_eq]
      _ ≤ ENNReal.ofReal (1 / 2 : ℝ) := ENNReal.ofReal_le_ofReal h
      _ = 1 / 2 := half
  · have h := diameter_upper dist Dsmall (some 0) (some (1 / 2))
      (by exact ⟨0, by norm_num, rfl⟩)
      (by exact ⟨1 / 2, by norm_num, rfl⟩)
    simpa [dist, edist_dist, Real.dist_eq, half] using h

theorem uniform_Dsmall : uniformRadius dist dist f Dsmall Dsmall = ⊤ := by
  apply z47
  intro x hx y hy
  rw [Dsmall_constant x hx, Dsmall_constant y hy]
  simp [dist]

theorem classification_Dsmall :
    diameter dist Dsmall = 1 / 2 ∧ uniformRadius dist dist f Dsmall Dsmall = ⊤ ∧
      thresholdType (diameterScale gauge) gauge f Dsmall 1 1 () () = (true, true) := by
  refine ⟨diameter_Dsmall, uniform_Dsmall, ?_⟩
  apply (z53 (diameterScale gauge) gauge f Dsmall 1 1 () ()).1.mpr
  change diameter dist Dsmall < 1 ∧ (1 : ENNReal) ≤ uniformRadius dist dist f Dsmall Dsmall
  rw [diameter_Dsmall, uniform_Dsmall]
  norm_num

def interval (a b : ℝ) : Set Point := some '' Set.Icc a b

theorem interval_domain (a b : ℝ) : interval a b ⊆ dom f := by
  rintro x ⟨t, _, rfl⟩
  change some ((Int.floor t : ℤ) : ℝ) ≠ none
  simp

theorem interval_nonempty (a b : ℝ) (hab : a ≤ b) : (interval a b).Nonempty :=
  ⟨some a, ⟨a, ⟨le_rfl, hab⟩, rfl⟩⟩

theorem interval_diameter (a b : ℝ) (hab : a ≤ b) :
    diameter dist (interval a b) = ENNReal.ofReal (b - a) := by
  apply le_antisymm
  · apply iSup_le
    intro x
    apply iSup_le
    intro hx
    apply iSup_le
    intro y
    apply iSup_le
    intro hy
    obtain ⟨t, ht, rfl⟩ := hx
    obtain ⟨u, hu, rfl⟩ := hy
    have h : |t - u| ≤ b - a := abs_le.mpr ⟨by linarith [ht.1, hu.2], by linarith [ht.2, hu.1]⟩
    simpa [dist, edist_dist, Real.dist_eq] using ENNReal.ofReal_le_ofReal h
  · have h := diameter_upper dist (interval a b) (some a) (some b)
      (by exact ⟨a, ⟨le_rfl, hab⟩, rfl⟩)
      (by exact ⟨b, ⟨hab, le_rfl⟩, rfl⟩)
    have habs : |a - b| = b - a := by rw [abs_of_nonpos (sub_nonpos.mpr hab)]; ring
    simpa [dist, edist_dist, Real.dist_eq, habs] using h

theorem zero_near_one (A : Set Point)
    (hA : ∀ t ∈ Set.Icc (9 / 10 : ℝ) 1, some t ∈ A) :
    uniformRadius dist dist f A A = 0 := by
  apply le_antisymm _ (zero_le _)
  by_contra hn
  have hpos : 0 < uniformRadius dist dist f A A := lt_of_not_ge hn
  obtain ⟨t, ht0, htpos, htlt⟩ := ENNReal.lt_iff_exists_real_btwn.mp hpos
  have ht : 0 < t := ENNReal.ofReal_pos.mp htpos
  let δ : ℝ := min t (1 / 10)
  have hδ : 0 < δ := lt_min ht (by norm_num)
  have hδupper : δ ≤ (1 / 10 : ℝ) := min_le_right _ _
  have hδt : δ ≤ t := min_le_left _ _
  have hx : some (1 - δ) ∈ A := hA _ ⟨by linarith, by linarith⟩
  have hy : some 1 ∈ A := hA _ (by norm_num)
  have hflo : Int.floor (1 - δ) = 0 := Int.floor_eq_iff.mpr (by
    constructor <;> norm_num <;> linarith)
  have hf1 : f.func (some 1) = some 1 := by norm_num [f]
  have hfx : f.func (some (1 - δ)) = some 0 := by simp [f, hflo]
  have hout : 0 < dist (f.func (some (1 - δ))) (f.func (some 1)) := by
    rw [hfx, hf1]
    norm_num [dist, edist_dist, Real.dist_eq]
  have hle := z45 dist dist f A (some 1) (some (1 - δ)) metric.symm hx hy hout
  have hdist : dist (some 1) (some (1 - δ)) ≤ ENNReal.ofReal t := by
    simp only [dist, edist_dist, Real.dist_eq]
    have habs : |(1 : ℝ) - (1 - δ)| = δ := by
      rw [show (1 : ℝ) - (1 - δ) = δ by ring, abs_of_pos hδ]
    rw [habs]
    exact ENNReal.ofReal_le_ofReal hδt
  exact (not_lt_of_ge (hle.trans hdist)) htlt

theorem wide_classification :
    diameter dist (interval (9 / 10) (11 / 10)) = 1 / 5 ∧
    uniformRadius dist dist f (interval (9 / 10) (11 / 10)) (interval (9 / 10) (11 / 10)) = 0 ∧
    thresholdType (diameterScale gauge) gauge f (interval (9 / 10) (11 / 10)) 1 1 () () = (true, false) := by
  have hdiam : diameter dist (interval (9 / 10) (11 / 10)) = 1 / 5 := by
    rw [interval_diameter (9 / 10) (11 / 10) (by norm_num)]
    norm_num [ENNReal.ofReal_div_of_pos (show (0 : ℝ) < 5 by norm_num)]
  have hradius : uniformRadius dist dist f (interval (9 / 10) (11 / 10)) (interval (9 / 10) (11 / 10)) = 0 := by
    apply zero_near_one
    intro t ht
    exact ⟨t, ⟨ht.1, by linarith [ht.2]⟩, rfl⟩
  refine ⟨hdiam, hradius, ?_⟩
  apply (z53 (diameterScale gauge) gauge f (interval (9 / 10) (11 / 10)) 1 1 () ()).2.1.mpr
  change diameter dist (interval (9 / 10) (11 / 10)) < 1 ∧
    uniformRadius dist dist f (interval (9 / 10) (11 / 10)) (interval (9 / 10) (11 / 10)) < 1
  rw [hdiam, hradius]
  norm_num

theorem large_classification :
    diameter dist (interval 0 2) = 2 ∧
    uniformRadius dist dist f (interval 0 2) (interval 0 2) = 0 ∧
    thresholdType (diameterScale gauge) gauge f (interval 0 2) 1 1 () () = (false, false) := by
  have hdiam : diameter dist (interval 0 2) = 2 := by
    rw [interval_diameter 0 2 (by norm_num)]
    norm_num
  have hradius : uniformRadius dist dist f (interval 0 2) (interval 0 2) = 0 := by
    apply zero_near_one
    intro t ht
    exact ⟨t, ⟨by linarith [ht.1], by linarith [ht.2]⟩, rfl⟩
  refine ⟨hdiam, hradius, ?_⟩
  apply (z53 (diameterScale gauge) gauge f (interval 0 2) 1 1 () ()).2.2.2.mpr
  change (1 : ENNReal) ≤ diameter dist (interval 0 2) ∧
    uniformRadius dist dist f (interval 0 2) (interval 0 2) < 1
  rw [hdiam, hradius]
  norm_num

end Chapter3.FloorExample

namespace Chapter3

open formal_oet.vol_01.ch_01_foundations
variable {X I : Type} {bot : X}

theorem finite_fiber_chain (d : I → X → X → ENNReal) (U : Set X)
    (f : ℕ → Operator X bot) (m : ℕ)
    (hstep : ∀ n < m, fiberPreorder d U (f n) (f (n+1)))
    {a b : ℕ} (hab : a ≤ b) (hbm : b ≤ m) :
    fiberPreorder d U (f a) (f b) := by
  induction b, hab using Nat.le_induction with
  | base => exact z21 d U (f a)
  | succ n han ih =>
      exact z22 d U _ _ _ (ih (by omega)) (hstep n (by omega))

theorem finite_fiber_chain_strict (d : I → X → X → ENNReal) (U : Set X)
    (f : ℕ → Operator X bot) (m r : ℕ) (hr : r < m)
    (hstep : ∀ n < m, fiberPreorder d U (f n) (f (n+1)))
    (hstrict : zeroRelation d (f r) U ⊂ zeroRelation d (f (r+1)) U) :
    zeroRelation d (f 0) U ⊂ zeroRelation d (f m) U ∧
      ∃ p, p ∈ zeroRelation d (f m) U ∧ p ∉ zeroRelation d (f 0) U := by
  have h0 : zeroRelation d (f 0) U ⊆ zeroRelation d (f r) U :=
    finite_fiber_chain d U f m hstep (Nat.zero_le r) (by omega)
  have hm : zeroRelation d (f (r+1)) U ⊆ zeroRelation d (f m) U :=
    finite_fiber_chain d U f m hstep (by omega) (by omega)
  obtain ⟨p, hp, hpnot⟩ := Set.exists_of_ssubset hstrict
  have hp' : p ∈ zeroRelation d (f m) U := hm hp
  have hpnot' : p ∉ zeroRelation d (f 0) U := fun h => hpnot (h0 h)
  exact ⟨⟨(h0.trans hstrict.1).trans hm, fun h => hpnot' (h hp')⟩,
    ⟨p, hp', hpnot'⟩⟩

end Chapter3

