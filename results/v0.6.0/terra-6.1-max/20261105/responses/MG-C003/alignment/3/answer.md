FULL

核查结论：上一轮没有提交源码和对齐表，也没有完成全部 92 项，因此并非 100% 覆盖。本轮仍无法完成整章；特别是像值因子化、覆盖数与熵估计、反例及章末具体计算仍有大量缺项。下面提交经 Lean 4.29.1 编译检查的**部分项目**及覆盖全部 ID 的对齐表；其中 33 项标为 `complete`，59 项标为 `incomplete`。这不是符合原题完整性交付要求的最终项目。

源码中的数学内容基于 Zhe Li（Glen Li）的 *The Operator Evolution Theory*, Volume I，https://glenzli.com/books/oet/ ，CC BY 4.0。

```lean filename=Main.lean
import formal_oet.vol_01.ch_01_foundations.metric_entropy
import formal_oet.vol_01.ch_02_operator_bounds.decoupling

/-! Partial formalization based on Zhe Li, The Operator Evolution Theory,
Volume I, https://glenzli.com/books/oet/, CC BY 4.0. -/

namespace Chapter3Fresh

open Set
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds

variable {X I : Type} {bot : X}

def constComponents (d : I → X → X → ENNReal) (f : Operator X bot) (U : Set X) : Set I :=
  {i | ∀ x ∈ U, ∀ y ∈ U, d i (f.func x) (f.func y) = 0}

def identityComponents (d : I → X → X → ENNReal) (f : Operator X bot) (U : Set X) : Set I :=
  {i | i ∉ constComponents d f U ∧ ∀ x ∈ U, d i (f.func x) x = 0}

def activeComponents (d : I → X → X → ENNReal) (f : Operator X bot) (U : Set X) : Set I :=
  (constComponents d f U ∪ identityComponents d f U)ᶜ

theorem components_partition (d : I → X → X → ENNReal) (f : Operator X bot) (U : Set X)
    (i : I) :
    (i ∈ constComponents d f U ∨ i ∈ identityComponents d f U ∨
      i ∈ activeComponents d f U) ∧
    ¬ (i ∈ constComponents d f U ∧ i ∈ identityComponents d f U) ∧
    ¬ (i ∈ constComponents d f U ∧ i ∈ activeComponents d f U) ∧
    ¬ (i ∈ identityComponents d f U ∧ i ∈ activeComponents d f U) := by
  classical
  simp only [identityComponents, activeComponents, mem_setOf_eq, mem_compl_iff, mem_union]
  tauto

theorem const_zero_row [Fintype I] (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (i : I) (hi : i ∈ constComponents d f U) :
    ∀ x ∈ U, ∀ y ∈ U, d i (f.func x) (f.func y) ≤ ∑ k : I, (0 : ENNReal) * d k x y := by
  intro x hx y hy
  simp [hi x hx y hy]

theorem const_colip_zero [Fintype I] (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (i k : I) (K : I → I → ENNReal)
    (hi : i ∈ constComponents d f U) (hK : IsCoLipMatrix d f U K)
    (x y : X) (hx : x ∈ U) (hy : y ∈ U) (hpos : 0 < d k x y) : K k i = 0 :=
  colip_entry_eq_zero_of_output_zero_input_pos d f U K k i x y hK hx hy
    (hi x hx y hy) hpos

theorem dist_eq_of_zero_endpoints (d : X → X → ENNReal)
    (hs : ∀ x y, d x y = d y x) (ht : ∀ x y z, d x z ≤ d x y + d y z)
    {a b c e : X} (hab : d a b = 0) (hce : d c e = 0) : d a c = d b e := by
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
    (hd : ExtendedPseudoMetric X bot (d i)) (hi : i ∈ identityComponents d f U) :
    ∀ x ∈ U, ∀ y ∈ U, d i (f.func x) (f.func y) = d i x y := by
  intro x hx y hy
  exact dist_eq_of_zero_endpoints (d i) hd.symm hd.triangle (hi.2 x hx) (hi.2 y hy)

theorem outer_const (d : I → X → X → ENNReal) (f g : Operator X bot)
    (U : Set X) (i : I) (h : i ∈ constComponents d g (f.func '' U)) :
    i ∈ constComponents d (g * f) U := by
  intro x hx y hy
  exact h (f.func x) ⟨x, hx, rfl⟩ (f.func y) ⟨y, hy, rfl⟩

theorem inner_const_of_single_row [Fintype I] (d : I → X → X → ENNReal)
    (f g : Operator X bot) (U : Set X) (j : I) (L : I → I → ENNReal)
    (hc : j ∈ constComponents d f U) (hL : IsLipMatrix d g (f.func '' U) L)
    (hrow : ∀ k, k ≠ j → L k j = 0) : j ∈ constComponents d (g * f) U := by
  intro x hx y hy
  apply le_antisymm _ (zero_le _)
  have h := lip_bound_of_single_input_row d g (f.func '' U) L j j hL hrow
      (f.func x) ⟨x, hx, rfl⟩ (f.func y) ⟨y, hy, rfl⟩
  simpa [hc x hx y hy] using h

theorem identity_comp (d : I → X → X → ENNReal) (f g : Operator X bot)
    (U : Set X) (i : I) (hd : ExtendedPseudoMetric X bot (d i))
    (hf : i ∈ identityComponents d f U) (hg : i ∈ identityComponents d g (f.func '' U)) :
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

theorem active_comp (d : I → X → X → ENNReal) (f g : Operator X bot)
    (U : Set X) (i : I) (hd : ExtendedPseudoMetric X bot (d i)) :
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
  have hnot : i ∉ constComponents d (g * f) U ∧ i ∉ identityComponents d (g * f) U := by
    simpa [activeComponents] using hc
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

def seqActive (d : I → X → X → ENNReal) : List (Operator X bot) → Set X → Set I
  | [], _ => ∅
  | f :: fs, U => activeComponents d f U ∪ seqActive d fs (f.func '' U)

theorem seqOp_eq_reverse_prod (fs : List (Operator X bot)) : seqOp fs = fs.reverse.prod := by
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

theorem active_seq (d : I → X → X → ENNReal) (fs : List (Operator X bot))
    (U : Set X) (i : I) (hd : ExtendedPseudoMetric X bot (d i)) :
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

theorem subfamily_zero_iff (d : I → X → X → ENNReal) (J : Set I) (x y : X) :
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

theorem fiber_intersection (d : I → X → X → ENNReal) (f : Operator X bot)
    (J : Set I) (y : X) (U : Set X) (hJ : J.Nonempty) :
    fiber d f J y U = ⋂ j ∈ J, componentFiber d f j y U := by
  ext x
  simp only [fiber, componentFiber, mem_setOf_eq, subfamily_zero_iff, mem_iInter]
  constructor
  · rintro ⟨hx, h⟩ j hj
    exact ⟨hx, h j hj⟩
  · intro h
    obtain ⟨j, hj⟩ := hJ
    exact ⟨(h j hj).1, fun j hj => (h j hj).2⟩

theorem fiber_antitone (d : I → X → X → ENNReal) (f : Operator X bot)
    (J K : Set I) (y : X) (U : Set X) (hJK : J ⊆ K) :
    fiber d f K y U ⊆ fiber d f J y U := by
  intro x hx
  exact ⟨hx.1, (subfamily_zero_iff d J _ _).2
    (fun j hj => (subfamily_zero_iff d K _ _).1 hx.2 j (hJK hj))⟩

theorem fiber_singleton (d : I → X → X → ENNReal) (f : Operator X bot)
    (j : I) (y : X) (U : Set X) : fiber d f {j} y U = componentFiber d f j y U := by
  ext x
  simp [fiber, componentFiber, subfamily_pseudometric_singleton]

theorem fiber_all_subset (d : I → X → X → ENNReal) (f : Operator X bot)
    (j : I) (y : X) (U : Set X) : fiber d f univ y U ⊆ componentFiber d f j y U := by
  rw [← fiber_singleton]
  exact fiber_antitone d f _ _ _ _ (subset_univ _)

def goodRadius (di dout : X → X → ENNReal) (f : Operator X bot)
    (y : X) (U : Set X) (r : ENNReal) : Prop :=
  0 < r ∧ r < ⊤ ∧ ∀ x ∈ U, di x y < r → dout (f.func x) (f.func y) = 0

noncomputable def pointRadius (di dout : X → X → ENNReal) (f : Operator X bot)
    (y : X) (U : Set X) : ENNReal := sSup {r | goodRadius di dout f y U r}

noncomputable def uniformRadius (di dout : X → X → ENNReal) (f : Operator X bot)
    (A U : Set X) : ENNReal := ⨅ y ∈ A, pointRadius di dout f y U

noncomputable def zeroMatrix (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (i j : I) : ENNReal := uniformRadius (d i) (d j) f U U

theorem radius_ball_iff (di dout : X → X → ENNReal) (f : Operator X bot)
    (y : X) (U : Set X) (r : ENNReal) : goodRadius di dout f y U r ↔
    0 < r ∧ r < ⊤ ∧
      (ball di y r ∩ U ⊆ {x | x ∈ U ∧ dout (f.func x) (f.func y) = 0}) := by
  simp only [goodRadius, ball, Set.subset_def, Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hpos, hfin, h⟩
    exact ⟨hpos, hfin, fun x hx => ⟨hx.2, h x hx.2 hx.1⟩⟩
  · rintro ⟨hpos, hfin, h⟩
    exact ⟨hpos, hfin, fun x hx hr => (h x ⟨hr, hx⟩).2⟩

theorem radius_subset (di dout : X → X → ENNReal) (f : Operator X bot)
    (y : X) (A B : Set X) (hBA : B ⊆ A) :
    pointRadius di dout f y A ≤ pointRadius di dout f y B := by
  apply sSup_le
  intro r hr
  apply le_sSup
  exact ⟨hr.1, hr.2.1, fun x hx => hr.2.2 x (hBA hx)⟩

theorem uniform_subset (di dout : X → X → ENNReal) (f : Operator X bot)
    (A B : Set X) (hBA : B ⊆ A) :
    uniformRadius di dout f A A ≤ uniformRadius di dout f B B := by
  apply le_iInf
  intro y
  apply le_iInf
  intro hy
  exact (iInf_le_of_le y (iInf_le_of_le (hBA hy) le_rfl)).trans
    (radius_subset di dout f y A B hBA)

theorem admissible_radius_le (di dout : X → X → ENNReal) (f : Operator X bot)
    (y : X) (U : Set X) (r : ENNReal) (h : goodRadius di dout f y U r) :
    r ≤ pointRadius di dout f y U := le_sSup h

theorem point_radius_witness (di dout : X → X → ENNReal) (f : Operator X bot)
    (y : X) (U : Set X) (a : ENNReal) (h : a < pointRadius di dout f y U) :
    ∃ r, goodRadius di dout f y U r ∧ a < r := lt_sSup_iff.mp h

theorem zero_of_lt_pointRadius (di dout : X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (y x : X) (hx : x ∈ U) (hds : ∀ a b, di a b = di b a)
    (h : di y x < pointRadius di dout f y U) : dout (f.func x) (f.func y) = 0 := by
  obtain ⟨r, hr, hlt⟩ := point_radius_witness di dout f y U (di y x) h
  apply hr.2.2 x hx
  rwa [hds x y]

theorem point_radius_component (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (i j : I) (y x : X) (hx : x ∈ U)
    (hi : ExtendedPseudoMetric X bot (d i)) (hj : ExtendedPseudoMetric X bot (d j))
    (h : d i y x < pointRadius (d i) (d j) f y U) :
    d j (f.func y) (f.func x) = 0 := by
  rw [hj.symm]
  exact zero_of_lt_pointRadius _ _ f U y x hx hi.symm h

theorem fiber_forces_zero (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (j : I) (y x : X) (hd : ExtendedPseudoMetric X bot (d j))
    (h : x ∈ componentFiber d f j (f.func y) U) :
    d j (f.func y) (f.func x) = 0 := by
  rw [hd.symm, h.2]

theorem composite_fiber_forces_zero (d : I → X → X → ENNReal)
    (f g : Operator X bot) (V : Set X) (j : I) (x y : X)
    (hd : ExtendedPseudoMetric X bot (d j))
    (hx : f.func x ∈ V) (hy : f.func y ∈ V)
    (h : f.func y ∈ componentFiber d g j (g.func (f.func x)) V) :
    d j ((g * f).func x) ((g * f).func y) = 0 := by
  exact fiber_forces_zero d g V j (f.func x) (f.func y) hd h

theorem uniform_le_point (di dout : X → X → ENNReal) (f : Operator X bot)
    (A U : Set X) (y : X) (hy : y ∈ A) :
    uniformRadius di dout f A U ≤ pointRadius di dout f y U :=
  iInf_le_of_le y (iInf_le_of_le hy le_rfl)

theorem zero_of_lt_uniformRadius (di dout : X → X → ENNReal) (f : Operator X bot)
    (A : Set X) (y x : X) (hy : y ∈ A) (hx : x ∈ A)
    (hin : ∀ a b, di a b = di b a) (hout : ∀ a b, dout a b = dout b a)
    (h : di y x < uniformRadius di dout f A A) : dout (f.func y) (f.func x) = 0 := by
  rw [hout]
  exact zero_of_lt_pointRadius di dout f A y x hx hin
    (lt_of_lt_of_le h (uniform_le_point di dout f A A y hy))

theorem positive_output_ge_uniform (di dout : X → X → ENNReal)
    (f : Operator X bot) (A : Set X) (x y : X) (hx : x ∈ A) (hy : y ∈ A)
    (hin : ∀ a b, di a b = di b a) (hout : ∀ a b, dout a b = dout b a)
    (hpos : 0 < dout (f.func x) (f.func y)) :
    uniformRadius di dout f A A ≤ di x y := by
  by_contra h
  have hlt : di x y < uniformRadius di dout f A A := lt_of_not_ge h
  exact (ne_of_gt hpos) (zero_of_lt_uniformRadius di dout f A x y hx hy hin hout hlt)

theorem radius_deficit_witness (di dout : X → X → ENNReal) (f : Operator X bot)
    (A : Set X) (alpha : ENNReal) (ha : 0 < alpha) (haf : alpha < ⊤)
    (hsmall : uniformRadius di dout f A A < alpha) :
    ∃ x ∈ A, ∃ y ∈ A, ∃ eps : ENNReal, 0 < eps ∧ eps < ⊤ ∧
      di x y < alpha ∧ eps ≤ dout (f.func x) (f.func y) := by
  classical
  obtain ⟨y, hy⟩ := iInf_lt_iff.mp hsmall
  obtain ⟨hyA, hyr⟩ := iInf_lt_iff.mp hy
  have hnot : ¬ ∀ x ∈ A, di x y < alpha → dout (f.func x) (f.func y) = 0 := by
    intro h
    have hle := admissible_radius_le di dout f y A alpha ⟨ha, haf, h⟩
    exact (not_le_of_gt hyr) hle
  push_neg at hnot
  obtain ⟨x, hx, hdist, hz⟩ := hnot
  have hpos : 0 < dout (f.func x) (f.func y) := pos_iff_ne_zero.mpr hz
  obtain ⟨eps, heps, hepslt⟩ := exists_between hpos
  refine ⟨x, hx, y, hyA, eps, heps, ?_, hdist, le_of_lt hepslt⟩
  exact lt_of_lt_of_le hepslt le_top

theorem threshold_ball_fiber (d : I → X → X → ENNReal) (f : Operator X bot)
    (A : Set X) (i j : I) (x : X) (hx : x ∈ A)
    (hi : ExtendedPseudoMetric X bot (d i)) (hj : ExtendedPseudoMetric X bot (d j))
    (t : ENNReal) (ht : t ≤ zeroMatrix d f A i j) :
    ball (d i) x t ∩ A ⊆ componentFiber d f j (f.func x) A := by
  intro y hy
  refine ⟨hy.2, ?_⟩
  have hlt : d i x y < uniformRadius (d i) (d j) f A A := by
    rw [hi.symm x y]
    exact lt_of_lt_of_le hy.1 ht
  rw [hj.symm]
  exact zero_of_lt_uniformRadius (d i) (d j) f A x y hx hy.2 hi.symm hj.symm hlt

theorem colip_gap_point [Fintype I] (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (i j : I) (K : I → I → ENNReal)
    (hK : IsCoLipMatrix d f U K) (hpos : 0 < K i j)
    (hi : ExtendedPseudoMetric X bot (d i))
    (y x : X) (hy : y ∈ U) (hx : x ∈ U)
    (h : d i y x < pointRadius (d i) (d j) f y U) : d i x y = 0 := by
  have hz := zero_of_lt_pointRadius (d i) (d j) f U y x hx hi.symm h
  exact positive_colip_entry_reflects_zero d f U K i j hK hpos x hx y hy hz

theorem colip_no_point_gap [Fintype I] (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (i j : I) (K : I → I → ENNReal)
    (hK : IsCoLipMatrix d f U K) (hpos : 0 < K i j)
    (hi : ExtendedPseudoMetric X bot (d i))
    (y x : X) (hy : y ∈ U) (hx : x ∈ U) :
    ¬ (0 < d i x y ∧ d i x y < pointRadius (d i) (d j) f y U) := by
  rintro ⟨hp, hl⟩
  have hz := colip_gap_point d f U i j K hK hpos hi y x hy hx (by rwa [hi.symm y x])
  exact (ne_of_gt hp) hz

theorem colip_gap_uniform [Fintype I] (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (i j : I) (K : I → I → ENNReal)
    (hK : IsCoLipMatrix d f U K) (hpos : 0 < K i j)
    (hi : ExtendedPseudoMetric X bot (d i)) (x y : X) (hx : x ∈ U) (hy : y ∈ U) :
    d i x y = 0 ∨ uniformRadius (d i) (d j) f U U ≤ d i x y := by
  by_cases h : uniformRadius (d i) (d j) f U U ≤ d i x y
  · exact Or.inr h
  · left
    have hl : d i x y < pointRadius (d i) (d j) f x U :=
      (lt_of_not_ge h).trans_le (uniform_le_point _ _ f U U x hx)
    have hz := colip_gap_point d f U i j K hK hpos hi x y hx hy hl
    rwa [hi.symm x y]

structure ScaleFamily (X I : Type) where
  scale : I → Set X → ENNReal
  mono : ∀ i (A B : Set X), A.Nonempty → A ⊆ B → scale i A ≤ scale i B

noncomputable def diameter (d : X → X → ENNReal) (A : Set X) : ENNReal :=
  ⨆ x ∈ A, ⨆ y ∈ A, d x y

theorem diameter_mono (d : X → X → ENNReal) (A B : Set X) (h : A ⊆ B) :
    diameter d A ≤ diameter d B := by
  apply iSup_le
  intro x
  apply iSup_le
  intro hx
  apply iSup_le
  intro y
  apply iSup_le
  intro hy
  exact le_iSup_of_le x (le_iSup_of_le (h hx)
    (le_iSup_of_le y (le_iSup_of_le (h hy) le_rfl)))

noncomputable def diameterScales (d : I → X → X → ENNReal) : ScaleFamily X I where
  scale i A := diameter (d i) A
  mono i A B _ h := diameter_mono (d i) A B h

noncomputable def channelType (s : ScaleFamily X I) (d : I → X → X → ENNReal)
    (f : Operator X bot) (A : Set X) (ts tn : ENNReal) (i j : I) : Bool × Bool := by
  classical
  exact (decide (s.scale i A < ts), decide (tn ≤ zeroMatrix d f A i j))

theorem threshold_cases (s : ScaleFamily X I) (d : I → X → X → ENNReal)
    (f : Operator X bot) (A : Set X) (ts tn : ENNReal) (i j : I) :
    channelType s d f A ts tn i j = (true, true) ∨
    channelType s d f A ts tn i j = (true, false) ∨
    channelType s d f A ts tn i j = (false, true) ∨
    channelType s d f A ts tn i j = (false, false) := by
  cases h : channelType s d f A ts tn i j with
  | mk a b => cases a <;> cases b <;> simp_all

theorem threshold_correspondence (s : ScaleFamily X I) (d : I → X → X → ENNReal)
    (f : Operator X bot) (A : Set X) (ts tn : ENNReal) (i j : I) :
    (channelType s d f A ts tn i j = (true, true) ↔
      s.scale i A < ts ∧ tn ≤ zeroMatrix d f A i j) ∧
    (channelType s d f A ts tn i j = (true, false) ↔
      s.scale i A < ts ∧ zeroMatrix d f A i j < tn) ∧
    (channelType s d f A ts tn i j = (false, true) ↔
      ts ≤ s.scale i A ∧ tn ≤ zeroMatrix d f A i j) ∧
    (channelType s d f A ts tn i j = (false, false) ↔
      ts ≤ s.scale i A ∧ zeroMatrix d f A i j < tn) := by
  classical
  simp [channelType, not_lt, not_le]

theorem scale_threshold_mono (s : ScaleFamily X I) (A : Set X) (i : I)
    (t t' : ENNReal) (h : t ≤ t') : s.scale i A < t → s.scale i A < t' :=
  fun hs => lt_of_lt_of_le hs h

theorem zero_threshold_mono (r t t' : ENNReal) (h : t ≤ t') : t' ≤ r → t ≤ r :=
  fun hr => h.trans hr

theorem scale_domain_mono (s : ScaleFamily X I) (A B : Set X) (i : I)
    (hB : B.Nonempty) (hBA : B ⊆ A) (t : ENNReal) :
    s.scale i B ≤ s.scale i A ∧ (s.scale i A < t → s.scale i B < t) := by
  exact ⟨s.mono i B A hB hBA, fun ht => lt_of_le_of_lt (s.mono i B A hB hBA) ht⟩

def TotallyBoundedInternal (d : X → X → ENNReal) (U : Set X) : Prop :=
  ∀ r : ENNReal, 0 < r → r < ⊤ → covering_number d r U < ⊤

theorem internalNet_text (d : X → X → ENNReal) (U : Set X) (r : ENNReal)
    (S : Finset X) : InternalEpsilonNet d r U S ↔
    (↑S : Set X) ⊆ U ∧ U ⊆ ⋃ c ∈ S, ball d c r := by
  simp only [InternalEpsilonNet, Set.subset_def, Set.mem_iUnion, ball, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hs, h⟩
    refine ⟨hs, ?_⟩
    intro x hx
    obtain ⟨c, hc, hd⟩ := h x hx
    exact ⟨c, hc, hd⟩
  · rintro ⟨hs, h⟩
    refine ⟨hs, ?_⟩
    intro x hx
    obtain ⟨c, hc, hd⟩ := h x hx
    exact ⟨c, hc, hd⟩

def entropyDomain (d : I → X → X → ENNReal) (f : Operator X bot) (U : Set X)
    (Jin Jout : Set I) (eps : ENNReal) : Prop :=
  U.Nonempty ∧ U ⊆ dom f ∧ Jin.Nonempty ∧ Jout.Nonempty ∧ 0 < eps ∧ eps < ⊤ ∧
  (covering_number (subfamily_pseudometric d Jin) eps U < ⊤ ∨
   covering_number (subfamily_pseudometric d Jout) eps (f.func '' U) < ⊤)

noncomputable def entropyDifference (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (Jin Jout : Set I) (eps : ENNReal)
    (_ : entropyDomain d f U Jin Jout eps) : EReal :=
  subfamily_metric_entropy d Jin eps U -
    subfamily_metric_entropy d Jout eps (f.func '' U)

end Chapter3Fresh
```

```json filename=alignment.json
{
  "case_id": "MG-C003",
  "version": "0.1.1",
  "items": [
    {"id":"CH03-D01","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3Fresh.constComponents"},{"file":"Main.lean","name":"Chapter3Fresh.identityComponents"},{"file":"Main.lean","name":"Chapter3Fresh.activeComponents"},{"file":"Main.lean","name":"Chapter3Fresh.components_partition"}],"representation":"按常值优先定义三类指标并证明互斥穷尽。","dependencies":[]},
    {"id":"CH03-D02","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3Fresh.fiber"},{"file":"Main.lean","name":"Chapter3Fresh.componentFiber"},{"file":"Main.lean","name":"Chapter3Fresh.subfamily_zero_iff"},{"file":"Main.lean","name":"Chapter3Fresh.fiber_singleton"}],"representation":"纤维是 U 中复合子族伪度量为零的点；证明单分量与各分量零距条件对应。","dependencies":[]},
    {"id":"CH03-D03","status":"incomplete","declarations":[],"representation":"点值关系、零距关系、像商和纤维预序未交付。","dependencies":[]},
    {"id":"CH03-D04","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3Fresh.goodRadius"},{"file":"Main.lean","name":"Chapter3Fresh.pointRadius"},{"file":"Main.lean","name":"Chapter3Fresh.radius_ball_iff"}],"representation":"对有限正合法半径取上确界，合法性等价于受限球包含。","dependencies":[]},
    {"id":"CH03-D05","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3Fresh.uniformRadius"},{"file":"Main.lean","name":"Chapter3Fresh.zeroMatrix"}],"representation":"对 A 的基点半径取下确界；矩阵参数 i、j 分别为输入列和输出行。","dependencies":["CH03-D04"]},
    {"id":"CH03-D06","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3Fresh.ScaleFamily"},{"file":"Main.lean","name":"Chapter3Fresh.diameter"},{"file":"Main.lean","name":"Chapter3Fresh.diameter_mono"},{"file":"Main.lean","name":"Chapter3Fresh.diameterScales"},{"file":"Main.lean","name":"Chapter3Fresh.channelType"},{"file":"Main.lean","name":"Chapter3Fresh.threshold_correspondence"}],"representation":"非空集上单调尺度、直径和两个比较构成布尔通道类型。","dependencies":["CH03-D05"]},
    {"id":"CH03-D07","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3Fresh.TotallyBoundedInternal"},{"file":"Main.lean","name":"Chapter3Fresh.internalNet_text"},{"file":"formal_oet/vol_01/ch_01_foundations/metric_entropy.lean","name":"formal_oet.vol_01.ch_01_foundations.InternalEpsilonNet"},{"file":"formal_oet/vol_01/ch_01_foundations/metric_entropy.lean","name":"formal_oet.vol_01.ch_01_foundations.covering_number"},{"file":"formal_oet/vol_01/ch_01_foundations/metric_entropy.lean","name":"formal_oet.vol_01.ch_01_foundations.covering_number_attained"},{"file":"formal_oet/vol_01/ch_01_foundations/metric_entropy.lean","name":"formal_oet.vol_01.ch_01_foundations.covering_number_eq_top_iff"},{"file":"formal_oet/vol_01/ch_01_foundations/metric_entropy.lean","name":"formal_oet.vol_01.ch_01_foundations.metric_entropy"},{"file":"formal_oet/vol_01/ch_01_foundations/metric_entropy.lean","name":"formal_oet.vol_01.ch_01_foundations.subfamily_pseudometric"},{"file":"formal_oet/vol_01/ch_01_foundations/metric_entropy.lean","name":"formal_oet.vol_01.ch_01_foundations.subfamily_metric_entropy"}],"representation":"使用冻结内覆盖数、熵和子族伪度量，证明球覆盖对应并定义有限正精度下全有界接口。","dependencies":[]},
    {"id":"CH03-D08","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3Fresh.entropyDomain"},{"file":"Main.lean","name":"Chapter3Fresh.entropyDifference"}],"representation":"在非空域、非空子族、有限正精度及至少一端有限覆盖数下，定义输入熵减输出熵。","dependencies":["CH03-D07"]},
    {"id":"CH03-P01-01","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3Fresh.const_zero_row"}],"representation":"常值输出与零行有限和均为零。","dependencies":["CH03-D01"]},
    {"id":"CH03-P01-02","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3Fresh.const_colip_zero"}],"representation":"正输入距离与常值输出迫使相应 co-Lip 条目为零。","dependencies":["CH03-D01"]},
    {"id":"CH03-P01-03","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3Fresh.identity_preserves_distance"}],"representation":"恒等分量下像点距离等于输入距离。","dependencies":["CH03-D01"]},
    {"id":"CH03-P02-01","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3Fresh.active_comp"}],"representation":"两步有效分量包含，外步域为实际中间像。","dependencies":["CH03-D01","CH03-P01-03","CH03-P02-03","CH03-P04-01"]},
    {"id":"CH03-P02-02","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3Fresh.seqOp"},{"file":"Main.lean","name":"Chapter3Fresh.seqActive"},{"file":"Main.lean","name":"Chapter3Fresh.seqOp_eq_reverse_prod"},{"file":"Main.lean","name":"Chapter3Fresh.identity_not_active"},{"file":"Main.lean","name":"Chapter3Fresh.active_seq"}],"representation":"列表顺序为作用顺序，递归实际像域并含零步。","dependencies":["CH03-D01","CH03-P02-01"]},
    {"id":"CH03-P02-03","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3Fresh.identity_comp"}],"representation":"两步恒等分量保持且排除常值优先分支。","dependencies":["CH03-D01","CH03-P01-03"]},
    {"id":"CH03-P03-01","status":"incomplete","declarations":[],"representation":"两点换位反例未交付。","dependencies":[]},
    {"id":"CH03-P04-01","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3Fresh.outer_const"}],"representation":"外侧在内侧像上常值推出复合常值。","dependencies":["CH03-D01"]},
    {"id":"CH03-P04-02","status":"incomplete","declarations":[],"representation":"七点双分量反例未交付。","dependencies":[]},
    {"id":"CH03-P05-01","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3Fresh.inner_const_of_single_row"}],"representation":"单同分量行 Lip 界将内侧常值传给复合，允许无穷系数。","dependencies":["CH03-D01"]},
    {"id":"CH03-P06-01","status":"incomplete","declarations":[],"representation":"目标零距时纤维相等未交付。","dependencies":[]},
    {"id":"CH03-P06-02","status":"incomplete","declarations":[],"representation":"像目标纤维非空和覆盖未交付。","dependencies":[]},
    {"id":"CH03-P06-03","status":"incomplete","declarations":[],"representation":"纤维相等或不交及分划证明未交付。","dependencies":[]},
    {"id":"CH03-P06-04","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3Fresh.fiber_intersection"}],"representation":"非空输出子族纤维是单分量纤维交集。","dependencies":["CH03-D02"]},
    {"id":"CH03-P06-05","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3Fresh.fiber_antitone"}],"representation":"J 包含于 K 时 K 纤维包含于 J 纤维。","dependencies":["CH03-D02"]},
    {"id":"CH03-P06-06","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3Fresh.fiber_singleton"},{"file":"Main.lean","name":"Chapter3Fresh.fiber_all_subset"}],"representation":"单指标子族等于对应分量，全指标纤维包含于每个分量。","dependencies":["CH03-D02","CH03-P06-05"]},
    {"id":"CH03-P06-07","status":"incomplete","declarations":[],"representation":"恒等分量的任意目标纤维公式未交付。","dependencies":[]},
    {"id":"CH03-P06-08","status":"incomplete","declarations":[],"representation":"常值分量的两种目标纤维结论未交付。","dependencies":[]},
    {"id":"CH03-P07-01","status":"incomplete","declarations":[],"representation":"点值因子化必要性未交付。","dependencies":[]},
    {"id":"CH03-P07-02","status":"incomplete","declarations":[],"representation":"点值因子化映射构造未交付。","dependencies":[]},
    {"id":"CH03-P07-03","status":"incomplete","declarations":[],"representation":"双向点值因子化判据未交付。","dependencies":[]},
    {"id":"CH03-P07-04","status":"incomplete","declarations":[],"representation":"实际像域上的标量 Lip 界未交付。","dependencies":[]},
    {"id":"CH03-P08-01","status":"incomplete","declarations":[],"representation":"单向零距商因子化未交付。","dependencies":[]},
    {"id":"CH03-P08-02","status":"incomplete","declarations":[],"representation":"双向零距商因子化未交付。","dependencies":[]},
    {"id":"CH03-P08-03","status":"incomplete","declarations":[],"representation":"像集分离下点值与商值判据对应未交付。","dependencies":[]},
    {"id":"CH03-P09-01","status":"incomplete","declarations":[],"representation":"纤维预序的自反性和传递性未交付。","dependencies":[]},
    {"id":"CH03-P09-02","status":"incomplete","declarations":[],"representation":"有限链任意两层的包含未交付。","dependencies":[]},
    {"id":"CH03-P09-03","status":"incomplete","declarations":[],"representation":"链中真包含推出端点真包含未交付。","dependencies":[]},
    {"id":"CH03-P10-01","status":"incomplete","declarations":[],"representation":"实线阶跃反例的合法结构未交付。","dependencies":[]},
    {"id":"CH03-P10-02","status":"incomplete","declarations":[],"representation":"阶跃反例点态半径计算未交付。","dependencies":[]},
    {"id":"CH03-P10-03","status":"incomplete","declarations":[],"representation":"阶跃反例统一半径为零未交付。","dependencies":[]},
    {"id":"CH03-P11-01","status":"incomplete","declarations":[],"representation":"常值子族像目标纤维公式未交付。","dependencies":[]},
    {"id":"CH03-P11-02","status":"incomplete","declarations":[],"representation":"常值子族的无穷半径结论未交付。","dependencies":[]},
    {"id":"CH03-P11-03","status":"incomplete","declarations":[],"representation":"两种通道情形的无穷输入距离反例未交付。","dependencies":[]},
    {"id":"CH03-P12-01","status":"incomplete","declarations":[],"representation":"恒等分量像目标纤维公式未交付。","dependencies":[]},
    {"id":"CH03-P12-02","status":"incomplete","declarations":[],"representation":"恒等分量点态半径下界未交付。","dependencies":[]},
    {"id":"CH03-P13-01","status":"incomplete","declarations":[],"representation":"点态半径的有限子族最小值公式未交付。","dependencies":[]},
    {"id":"CH03-P13-02","status":"incomplete","declarations":[],"representation":"统一半径的有限子族最小值公式未交付。","dependencies":[]},
    {"id":"CH03-P13-03","status":"incomplete","declarations":[],"representation":"统一半径关于输出子族的反单调性未交付。","dependencies":[]},
    {"id":"CH03-P14-01","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3Fresh.fiber_forces_zero"}],"representation":"纤维成员给出输出零距及对称方向。","dependencies":["CH03-D02"]},
    {"id":"CH03-P14-02","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3Fresh.point_radius_witness"},{"file":"Main.lean","name":"Chapter3Fresh.point_radius_component"}],"representation":"严格小于上确界时提取有限正合法半径并得到输出零距。","dependencies":["CH03-D04"]},
    {"id":"CH03-P14-03","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3Fresh.composite_fiber_forces_zero"}],"representation":"代入两个中间像点与下游纤维成员。","dependencies":["CH03-D02","CH03-P14-01"]},
    {"id":"CH03-P15-01","status":"incomplete","declarations":[],"representation":"零距保持下的复合半径下界未交付。","dependencies":[]},
    {"id":"CH03-P15-02","status":"incomplete","declarations":[],"representation":"Lip 拉回的复合半径下界未交付。","dependencies":[]},
    {"id":"CH03-P16-01","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3Fresh.threshold_cases"},{"file":"Main.lean","name":"Chapter3Fresh.threshold_correspondence"}],"representation":"布尔对四种情况穷尽，并分别对应四组互补不等式。","dependencies":["CH03-D06"]},
    {"id":"CH03-P16-02","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3Fresh.scale_threshold_mono"}],"representation":"增大尺度阈值保留原来小于阈值的通道。","dependencies":["CH03-D06"]},
    {"id":"CH03-P16-03","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3Fresh.zero_threshold_mono"}],"representation":"增大零化阈值后仍达标则原阈值也达标。","dependencies":["CH03-D06"]},
    {"id":"CH03-P17-01","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3Fresh.scale_domain_mono"}],"representation":"非空子域上的单调尺度及尺度阈值结论。","dependencies":["CH03-D06"]},
    {"id":"CH03-P17-02","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3Fresh.radius_subset"}],"representation":"缩小评估域时每个合法半径仍合法。","dependencies":["CH03-D04"]},
    {"id":"CH03-P17-03","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3Fresh.uniform_subset"}],"representation":"同时缩小评估域与基点集合后统一半径不减。","dependencies":["CH03-D04","CH03-D05","CH03-P17-02"]},
    {"id":"CH03-P17-04","status":"incomplete","declarations":[],"representation":"直径尺度二点单点反例未交付。","dependencies":[]},
    {"id":"CH03-P18-01","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3Fresh.zero_of_lt_uniformRadius"}],"representation":"小于统一半径的输入点对映到零距输出。","dependencies":["CH03-D04","CH03-D05","CH03-P14-02"]},
    {"id":"CH03-P18-02","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3Fresh.positive_output_ge_uniform"}],"representation":"输出正距离迫使输入距离不小于统一半径。","dependencies":["CH03-D04","CH03-D05","CH03-P18-01"]},
    {"id":"CH03-P18-03","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3Fresh.radius_deficit_witness"}],"representation":"任何有限正 α 高于统一半径时产生两点和有限正 ε，含无穷输出距离。","dependencies":["CH03-D04","CH03-D05"]},
    {"id":"CH03-P19-01","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3Fresh.threshold_ball_fiber"}],"representation":"低于统一阈值的输入球与域交集包含在纤维中。","dependencies":["CH03-D02","CH03-D04","CH03-D05","CH03-P18-01"]},
    {"id":"CH03-P19-02","status":"incomplete","declarations":[],"representation":"任意子集的内部覆盖数约束未交付。","dependencies":[]},
    {"id":"CH03-P19-03","status":"incomplete","declarations":[],"representation":"覆盖数约束对应的熵不等式未交付。","dependencies":[]},
    {"id":"CH03-P20-01","status":"incomplete","declarations":[],"representation":"阶跃反例上的二点覆盖构造未交付。","dependencies":[]},
    {"id":"CH03-P21-01","status":"incomplete","declarations":[],"representation":"小直径下整体零化的双向判据未交付。","dependencies":[]},
    {"id":"CH03-P21-02","status":"incomplete","declarations":[],"representation":"整体零化时输出覆盖数为一未交付。","dependencies":[]},
    {"id":"CH03-P22-01","status":"incomplete","declarations":[],"representation":"有限非空集上的熵差良定性未交付。","dependencies":[]},
    {"id":"CH03-P23-01","status":"incomplete","declarations":[],"representation":"常值分量的覆盖数、熵和熵差结论未交付。","dependencies":[]},
    {"id":"CH03-P23-02","status":"incomplete","declarations":[],"representation":"恒等分量的双向覆盖数比较未交付。","dependencies":[]},
    {"id":"CH03-P23-03","status":"incomplete","declarations":[],"representation":"恒等分量在良定条件下熵差为零未交付。","dependencies":[]},
    {"id":"CH03-P24-01","status":"incomplete","declarations":[],"representation":"Lip 输入覆盖推到输出覆盖未交付。","dependencies":[]},
    {"id":"CH03-P24-02","status":"incomplete","declarations":[],"representation":"全有界条件下的熵差下界未交付。","dependencies":[]},
    {"id":"CH03-P25-01","status":"incomplete","declarations":[],"representation":"正有限 co-Lip 条目的覆盖数下界未交付。","dependencies":[]},
    {"id":"CH03-P25-02","status":"incomplete","declarations":[],"representation":"允许输出熵无穷的熵差上界未交付。","dependencies":[]},
    {"id":"CH03-P26-01","status":"incomplete","declarations":[],"representation":"习题 3.1 的结构、一次纤维和类型未交付。","dependencies":[]},
    {"id":"CH03-P26-02","status":"incomplete","declarations":[],"representation":"习题 3.1 的自复合纤维和类型未交付。","dependencies":[]},
    {"id":"CH03-P26-03","status":"incomplete","declarations":[],"representation":"点值常算子的自复合及吸收元分支未交付。","dependencies":[]},
    {"id":"CH03-P27-01","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3Fresh.colip_no_point_gap"}],"representation":"正 co-Lip 条目可为无穷，并排除点态半径内的正输入距离。","dependencies":["CH03-D04","CH03-P14-02"]},
    {"id":"CH03-P27-02","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3Fresh.colip_gap_uniform"}],"representation":"对每个输入点对，距离为零或不小于统一半径。","dependencies":["CH03-D04","CH03-D05","CH03-P14-02"]},
    {"id":"CH03-P28-01","status":"incomplete","declarations":[],"representation":"习题 3.3 的两种纤维分划和结构未交付。","dependencies":[]},
    {"id":"CH03-P28-02","status":"incomplete","declarations":[],"representation":"习题 3.3 的覆盖数和熵差未交付。","dependencies":[]},
    {"id":"CH03-P29-01","status":"incomplete","declarations":[],"representation":"习题 3.4 第一个域的直径、半径和类型未交付。","dependencies":[]},
    {"id":"CH03-P29-02","status":"incomplete","declarations":[],"representation":"习题 3.4 第二个域的直径、半径和类型未交付。","dependencies":[]},
    {"id":"CH03-P29-03","status":"incomplete","declarations":[],"representation":"习题 3.4 第三个域的直径、半径和类型未交付。","dependencies":[]},
    {"id":"CH03-P29-04","status":"incomplete","declarations":[],"representation":"习题 3.4 第四个域的直径、半径和类型未交付。","dependencies":[]},
    {"id":"CH03-P29-05","status":"incomplete","declarations":[],"representation":"习题 3.4 无直径条件的反例未交付。","dependencies":[]},
    {"id":"CH03-P30-01","status":"incomplete","declarations":[],"representation":"四点集全部精度和端点的内部覆盖数未交付。","dependencies":[]},
    {"id":"CH03-P30-02","status":"incomplete","declarations":[],"representation":"两个像集及全部精度的覆盖数和熵差未交付。","dependencies":[]},
    {"id":"CH03-P30-03","status":"incomplete","declarations":[],"representation":"两个最优标量 Lip 常数及必要下界未交付。","dependencies":[]},
    {"id":"CH03-P30-04","status":"incomplete","declarations":[],"representation":"精度 7/4 时一般覆盖界和真实值的比较未交付。","dependencies":[]}
  ]
}
```