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

theorem dist_reals (x y : ℝ) :
    dist (some x) (some y) = ENNReal.ofReal (|(|x| - |y|)|) := by
  simp [dist, edist_dist, Real.dist_eq]

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

end Chapter3.AbsoluteExample
