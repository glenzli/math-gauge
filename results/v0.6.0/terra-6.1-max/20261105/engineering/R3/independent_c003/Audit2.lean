import formal_oet.vol_01.ch_01_foundations.metric_entropy
import formal_oet.vol_01.ch_02_operator_bounds.decoupling

/-! Partial formalization of Chapter 3 of Zhe Li, The Operator Evolution
Theory, Volume I, https://glenzli.com/books/oet/, CC BY 4.0. -/

namespace Chapter3
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

theorem components_partition (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (i : I) :
    (i ∈ constComponents d f U ∨ i ∈ identityComponents d f U ∨
      i ∈ activeComponents d f U) ∧
    ¬ (i ∈ constComponents d f U ∧ i ∈ identityComponents d f U) ∧
    ¬ (i ∈ constComponents d f U ∧ i ∈ activeComponents d f U) ∧
    ¬ (i ∈ identityComponents d f U ∧ i ∈ activeComponents d f U) := by
  classical
  simp only [identityComponents, activeComponents, mem_setOf_eq, mem_compl_iff, mem_union]
  tauto

theorem const_zero_row [Fintype I] (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (i : I) (hi : i ∈ constComponents d f U) :
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
    (f : Operator X bot) (U : Set X) (i : I) (hd : ExtendedPseudoMetric X bot (d i))
    (hi : i ∈ identityComponents d f U) :
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

theorem identity_comp (d : I → X → X → ENNReal)
    (f g : Operator X bot) (U : Set X) (i : I) (hd : ExtendedPseudoMetric X bot (d i))
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
      d i ((g * f).func x) x ≤
          d i (g.func (f.func x)) (f.func x) + d i (f.func x) x := hd.triangle _ _ _
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
  have hg : i ∈ constComponents d g (f.func '' U) ∨ i ∈ identityComponents d g (f.func '' U) := by
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
theorem identity_not_active (d : I → X → X → ENNReal) (U : Set X) (i : I)
    (hself : ∀ x, d i x x = 0) : i ∉ activeComponents d (1 : Operator X bot) U := by
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
  | nil => intro h; exact (identity_not_active d U i hd.dist_self h).elim
  | cons f fs ih =>
      intro h
      rcases active_comp d f (seqOp fs) U i hd h with h | h
      · exact Or.inl h
      · exact Or.inr (ih (f.func '' U) h)

def fiber (d : I → X → X → ENNReal) (f : Operator X bot)
    (J : Set I) (y : X) (U : Set X) : Set X :=
  {x | x ∈ U ∧ subfamily_pseudometric d J (f.func x) y = 0}
def componentFiber (d : I → X → X → ENNReal) (f : Operator X bot)
    (j : I) (y : X) (U : Set X) : Set X := {x | x ∈ U ∧ d j (f.func x) y = 0}

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
    exact ⟨(h j hj).1, fun k hk => (h k hk).2⟩
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

theorem fiber_target_zero (d : I → X → X → ENNReal) (f : Operator X bot)
    (J : Set I) (y z : X) (U : Set X) (hd : ∀ j, ExtendedPseudoMetric X bot (d j))
    (hyz : subfamily_pseudometric d J y z = 0) : fiber d f J y U = fiber d f J z U := by
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
      _ = 0 := by
        rw [h.2 j hj, (hd j).symm z y, (subfamily_zero_iff d J y z).1 hyz j hj, add_zero]

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

theorem fiber_equal_or_disjoint (d : I → X → X → ENNReal)
    (f : Operator X bot) (J : Set I) (U : Set X) (y z : X)
    (hd : ∀ j, ExtendedPseudoMetric X bot (d j)) :
    fiber d f J y U = fiber d f J z U ∨ Disjoint (fiber d f J y U) (fiber d f J z U) := by
  classical
  by_cases h : Disjoint (fiber d f J y U) (fiber d f J z U)
  · exact Or.inr h
  · left
    obtain ⟨x, hx, hx'⟩ := Set.not_disjoint_iff.mp h
    apply fiber_target_zero d f J y z U hd
    apply (subfamily_zero_iff d J y z).2
    intro j hj
    apply le_antisymm _ (zero_le _)
    calc
      d j y z ≤ d j y (f.func x) + d j (f.func x) z := (hd j).triangle _ _ _
      _ = 0 := by
        rw [(hd j).symm y (f.func x), (subfamily_zero_iff d J _ _).1 hx.2 j hj,
          (subfamily_zero_iff d J _ _).1 hx'.2 j hj, add_zero]

theorem identity_component_fiber (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (i : I) (y : X)
    (hd : ExtendedPseudoMetric X bot (d i)) (hi : i ∈ identityComponents d f U) :
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
    (hd : ExtendedPseudoMetric X bot (d i)) (hc : i ∈ constComponents d f U)
    (hy₀ : y₀ ∈ f.func '' U) : componentFiber d f i y₀ U = U ∧
      (0 < d i y y₀ → componentFiber d f i y U = ∅) := by
  obtain ⟨z, hz, rfl⟩ := hy₀
  constructor
  · ext x
    simp only [componentFiber, mem_setOf_eq]
    exact ⟨And.left, fun hx => ⟨hx, hc x hx z hz⟩⟩
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

/- Finite positive radii only; the supremum itself may be infinity. -/
def admissibleRadius (din dout : X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (y : X) (r : ENNReal) : Prop :=
  0 < r ∧ r < ⊤ ∧ ∀ x ∈ U, din x y < r → dout (f.func x) (f.func y) = 0

noncomputable def radius (din dout : X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (y : X) : ENNReal := sSup {r | admissibleRadius din dout f U y r}

noncomputable def uniformRadius (din dout : X → X → ENNReal) (f : Operator X bot)
    (A U : Set X) : ENNReal := ⨅ y ∈ A, radius din dout f U y

noncomputable def zeroMatrix (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (i j : I) : ENNReal := uniformRadius (d i) (d j) f U U

theorem admissible_le_radius (din dout : X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (y : X) (r : ENNReal) (hr : admissibleRadius din dout f U y r) :
    r ≤ radius din dout f U y := le_sSup hr

theorem strict_radius_zero (din dout : X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (x y : X) (hx : x ∈ U)
    (h : din x y < radius din dout f U y) : dout (f.func x) (f.func y) = 0 := by
  obtain ⟨r, hr, hxr⟩ := lt_sSup_iff.mp h
  exact hr.2.2 x hx hxr

theorem radius_mono_domain (din dout : X → X → ENNReal) (f : Operator X bot)
    (A B : Set X) (y : X) (hBA : B ⊆ A) :
    radius din dout f A y ≤ radius din dout f B y := by
  apply sSup_le
  intro r hr
  apply le_sSup
  exact ⟨hr.1, hr.2.1, fun x hx hxr => hr.2.2 x (hBA hx) hxr⟩

theorem uniform_le_radius (din dout : X → X → ENNReal) (f : Operator X bot)
    (A U : Set X) (y : X) (hy : y ∈ A) :
    uniformRadius din dout f A U ≤ radius din dout f U y :=
  iInf_le_of_le y (iInf_le_of_le hy le_rfl)

theorem uniform_mono_domain (din dout : X → X → ENNReal) (f : Operator X bot)
    (A B : Set X) (hBA : B ⊆ A) :
    uniformRadius din dout f A A ≤ uniformRadius din dout f B B := by
  apply le_iInf
  intro y
  apply le_iInf
  intro hy
  exact (uniform_le_radius din dout f A A y (hBA hy)).trans
    (radius_mono_domain din dout f A B y hBA)

theorem strict_uniform_zero (din dout : X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (x y : X) (hx : x ∈ U) (hy : y ∈ U)
    (h : din x y < uniformRadius din dout f U U) : dout (f.func x) (f.func y) = 0 :=
  strict_radius_zero din dout f U x y hx (h.trans_le (uniform_le_radius din dout f U U y hy))

theorem positive_output_lower_bound (din dout : X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (x y : X) (hx : x ∈ U) (hy : y ∈ U)
    (h : 0 < dout (f.func x) (f.func y)) :
    uniformRadius din dout f U U ≤ din x y := by
  by_contra hnot
  exact (ne_of_gt h) (strict_uniform_zero din dout f U x y hx hy (lt_of_not_ge hnot))

theorem radius_eq_top_of_all_zero (din dout : X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (y : X) (h : ∀ x ∈ U, dout (f.func x) (f.func y) = 0) :
    radius din dout f U y = ⊤ := by
  apply top_unique
  rw [← ENNReal.iSup_natCast]
  apply iSup_le
  intro n
  have hn : ((n + 1 : ℕ) : ENNReal) ≤ radius din dout f U y := by
    apply admissible_le_radius
    refine ⟨?_, ENNReal.natCast_lt_top _, ?_⟩
    · exact_mod_cast Nat.zero_lt_succ n
    · exact fun x hx _ => h x hx
  exact (by exact_mod_cast Nat.le_succ n : (n : ENNReal) ≤ ((n + 1 : ℕ) : ENNReal)).trans hn

theorem uniform_eq_top_of_all_zero (din dout : X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (h : ∀ x ∈ U, ∀ y ∈ U, dout (f.func x) (f.func y) = 0) :
    uniformRadius din dout f U U = ⊤ := by
  apply top_unique
  apply le_iInf
  intro y
  apply le_iInf
  intro hy
  rw [radius_eq_top_of_all_zero din dout f U y (fun x hx => h x hx y hy)]

theorem const_subfamily_fiber (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (J : Set I) (y : X) (hy : y ∈ U)
    (hJ : J ⊆ constComponents d f U) : fiber d f J (f.func y) U = U := by
  ext x
  simp only [fiber, mem_setOf_eq]
  constructor
  · exact And.left
  · intro hx
    exact ⟨hx, (subfamily_zero_iff d J _ _).2 (fun j hj => hJ hj x hx y hy)⟩

theorem const_subfamily_radii (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (J : Set I) (din : X → X → ENNReal)
    (hJ : J ⊆ constComponents d f U) :
    (∀ y ∈ U, radius din (subfamily_pseudometric d J) f U y = ⊤) ∧
    uniformRadius din (subfamily_pseudometric d J) f U U = ⊤ := by
  have hz : ∀ x ∈ U, ∀ y ∈ U, subfamily_pseudometric d J (f.func x) (f.func y) = 0 := by
    intro x hx y hy
    exact (subfamily_zero_iff d J _ _).2 (fun j hj => hJ hj x hx y hy)
  exact ⟨fun y hy => radius_eq_top_of_all_zero din _ f U y (fun x hx => hz x hx y hy),
    uniform_eq_top_of_all_zero din _ f U hz⟩

theorem identity_fiber_at_image (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (i : I) (y : X) (hy : y ∈ U)
    (hd : ExtendedPseudoMetric X bot (d i)) (hi : i ∈ identityComponents d f U) :
    componentFiber d f i (f.func y) U = {x | x ∈ U ∧ d i x y = 0} := by
  ext x
  simp only [componentFiber, mem_setOf_eq]
  by_cases hx : x ∈ U
  · simp [hx, identity_preserves_distance d f U i hd hi x hx y hy]
  · simp [hx]

theorem identity_radius_lower (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (i : I) (y : X) (hy : y ∈ U)
    (hd : ExtendedPseudoMetric X bot (d i)) (hi : i ∈ identityComponents d f U)
    (r : ENNReal) (hr : 0 < r) (hrt : r < ⊤)
    (hball : ∀ x ∈ U, d i x y < r → d i x y = 0) :
    r ≤ radius (d i) (d i) f U y := by
  apply admissible_le_radius
  refine ⟨hr, hrt, ?_⟩
  intro x hx hxy
  rw [identity_preserves_distance d f U i hd hi x hx y hy]
  exact hball x hx hxy

theorem fiber_zero (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (j : I) (y x : X) (hd : ExtendedPseudoMetric X bot (d j))
    (hx : x ∈ componentFiber d f j (f.func y) U) :
    d j (f.func y) (f.func x) = 0 := by
  rw [hd.symm, hx.2]

theorem strict_radius_zero_symm (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (i j : I) (y x : X) (hx : x ∈ U)
    (hdi : ExtendedPseudoMetric X bot (d i)) (hdj : ExtendedPseudoMetric X bot (d j))
    (h : d i y x < radius (d i) (d j) f U y) : d j (f.func y) (f.func x) = 0 := by
  rw [hdi.symm] at h
  rw [hdj.symm]
  exact strict_radius_zero (d i) (d j) f U x y hx h

theorem fiber_zero_composite (d : I → X → X → ENNReal) (f g : Operator X bot)
    (U : Set X) (j : I) (x y : X) (hd : ExtendedPseudoMetric X bot (d j))
    (h : f.func y ∈ componentFiber d g j (g.func (f.func x)) U) :
    d j ((g * f).func x) ((g * f).func y) = 0 :=
  fiber_zero d g U j (f.func x) (f.func y) hd h

theorem colip_point_gap [Fintype I] (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (i j : I) (K : I → I → ENNReal)
    (hK : IsCoLipMatrix d f U K) (hpos : 0 < K i j) (x y : X)
    (hx : x ∈ U) (hy : y ∈ U)
    (h : d i x y < radius (d i) (d j) f U y) : d i x y = 0 := by
  exact positive_colip_entry_reflects_zero d f U K i j hK hpos x hx y hy
    (strict_radius_zero (d i) (d j) f U x y hx h)

theorem colip_uniform_gap [Fintype I] (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (i j : I) (K : I → I → ENNReal)
    (hK : IsCoLipMatrix d f U K) (hpos : 0 < K i j) (x y : X)
    (hx : x ∈ U) (hy : y ∈ U) :
    d i x y = 0 ∨ uniformRadius (d i) (d j) f U U ≤ d i x y := by
  by_cases h : d i x y < uniformRadius (d i) (d j) f U U
  · left
    exact colip_point_gap d f U i j K hK hpos x y hx hy
      (h.trans_le (uniform_le_radius (d i) (d j) f U U y hy))
  · exact Or.inr (le_of_not_gt h)

def pointRelation (f : Operator X bot) (U : Set X) : Set (X × X) :=
  {p | p.1 ∈ U ∧ p.2 ∈ U ∧ f.func p.1 = f.func p.2}

def zeroRelation (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) : Set (X × X) :=
  {p | p.1 ∈ U ∧ p.2 ∈ U ∧ GaugeZeroRelated d (f.func p.1) (f.func p.2)}

def fiberPreorder (d : I → X → X → ENNReal) (U : Set X)
    (f g : Operator X bot) : Prop := zeroRelation d f U ⊆ zeroRelation d g U

def imageZeroSetoid (d : I → X → X → ENNReal) (f : Operator X bot) (U : Set X)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) : Setoid (f.func '' U) where
  r a b := GaugeZeroRelated d a.1 b.1
  iseqv := by
    have he := gauge_zero_related_equivalence d (fun i => (hd i).dist_self)
      (fun i => (hd i).symm) (fun i => (hd i).triangle)
    exact ⟨fun a => he.refl a.1, fun h => he.symm h, fun h k => he.trans h k⟩

theorem zeroRelation_fiber (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (x y : X) (hx : x ∈ U)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) :
    (x,y) ∈ zeroRelation d f U ↔ y ∈ fiber d f univ (f.func x) U := by
  simp only [zeroRelation, fiber, mem_setOf_eq, subfamily_zero_iff, mem_univ,
    true_implies, GaugeZeroRelated]
  constructor
  · rintro ⟨_, hy, h⟩
    exact ⟨hy, fun i => by rw [(hd i).symm, h i]⟩
  · rintro ⟨hy, h⟩
    exact ⟨hx, hy, fun i => by rw [(hd i).symm, h i]⟩

theorem fiberPreorder_refl (d : I → X → X → ENNReal) (U : Set X) (f : Operator X bot) :
    fiberPreorder d U f f := Subset.rfl
theorem fiberPreorder_trans (d : I → X → X → ENNReal) (U : Set X)
    (f g h : Operator X bot) : fiberPreorder d U f g → fiberPreorder d U g h →
      fiberPreorder d U f h := Set.Subset.trans

theorem fiberPreorder_chain (d : I → X → X → ENNReal) (U : Set X)
    (f : ℕ → Operator X bot) (a b : ℕ) (hab : a ≤ b)
    (h : ∀ n, n < b → fiberPreorder d U (f n) (f (n+1))) :
    fiberPreorder d U (f a) (f b) := by
  induction hab with
  | refl => exact fiberPreorder_refl d U (f a)
  | @step b hab ih =>
    have hprev : ∀ n, n < b → fiberPreorder d U (f n) (f (n+1)) :=
      fun n hn => h n (lt_trans hn (Nat.lt_succ_self b))
    exact fiberPreorder_trans d U _ _ _ (ih hprev) (h b (Nat.lt_succ_self b))

theorem fiberPreorder_chain_strict (d : I → X → X → ENNReal) (U : Set X)
    (f : ℕ → Operator X bot) (m r : ℕ)
    (h : ∀ n, n < m → fiberPreorder d U (f n) (f (n+1))) (hr : r < m)
    (hs : zeroRelation d (f r) U ⊂ zeroRelation d (f (r+1)) U) :
    zeroRelation d (f 0) U ⊂ zeroRelation d (f m) U ∧
      ∃ p, p ∈ zeroRelation d (f m) U ∧ p ∉ zeroRelation d (f 0) U := by
  have h0 := fiberPreorder_chain d U f 0 r (Nat.zero_le r) (fun n hn => h n (lt_trans hn hr))
  have hm := fiberPreorder_chain d U f (r+1) m (Nat.succ_le_of_lt hr) h
  obtain ⟨p, hp, hn⟩ := Set.exists_of_ssubset hs
  have hmem := hm hp
  have hnot : p ∉ zeroRelation d (f 0) U := fun hp0 => hn (h0 hp0)
  exact ⟨Set.ssubset_iff_subset_ne.mpr ⟨fiberPreorder_chain d U f 0 m (Nat.zero_le m) h,
    fun heq => hnot (heq.symm ▸ hmem)⟩, ⟨p, hmem, hnot⟩⟩

def HasPointFactor (f g : Operator X bot) (U : Set X) : Prop :=
  ∃ T : (f.func '' U) → X, ∀ x (hx : x ∈ U), T ⟨f.func x, ⟨x, hx, rfl⟩⟩ = g.func x

theorem point_factor_iff (f g : Operator X bot) (U : Set X) :
    HasPointFactor f g U ↔ pointRelation f U ⊆ pointRelation g U := by
  classical
  constructor
  · rintro ⟨T, hT⟩ ⟨x, y⟩ ⟨hx, hy, heq⟩
    refine ⟨hx, hy, ?_⟩
    have he : (⟨f.func x, ⟨x,hx,rfl⟩⟩ : f.func '' U) = ⟨f.func y, ⟨y,hy,rfl⟩⟩ :=
      Subtype.ext heq
    exact (hT x hx).symm.trans ((congrArg T he).trans (hT y hy))
  · intro h
    let T : (f.func '' U) → X := fun t => g.func (Classical.choose t.property)
    refine ⟨T, ?_⟩
    intro x hx
    let t : f.func '' U := ⟨f.func x, ⟨x, hx, rfl⟩⟩
    have ht : Classical.choose t.property ∈ U ∧ f.func (Classical.choose t.property) = f.func x :=
      Classical.choose_spec t.property
    have hrel : (Classical.choose t.property, x) ∈ pointRelation f U := ⟨ht.1, hx, ht.2⟩
    exact (h hrel).2.2

theorem point_factor_both_iff (f g : Operator X bot) (U : Set X) :
    (HasPointFactor f g U ∧ HasPointFactor g f U) ↔ pointRelation f U = pointRelation g U := by
  rw [point_factor_iff, point_factor_iff, Set.Subset.antisymm_iff]

structure InputScale (X I : Type) where
  scale : I → Set X → ENNReal
  mono : ∀ i A B, A.Nonempty → A ⊆ B → scale i A ≤ scale i B

noncomputable def diameterScale (d : I → X → X → ENNReal) : InputScale X I where
  scale i A := ⨆ x ∈ A, ⨆ y ∈ A, d i x y
  mono := by
    intro i A B _ hAB
    apply iSup_le; intro x; apply iSup_le; intro hx
    apply iSup_le; intro y; apply iSup_le; intro hy
    exact le_iSup_of_le x (le_iSup_of_le (hAB hx)
      (le_iSup_of_le y (le_iSup_of_le (hAB hy) le_rfl)))

noncomputable def thresholdType (s : InputScale X I) (d : I → X → X → ENNReal)
    (f : Operator X bot) (A : Set X) (i j : I) (ts tn : ENNReal) : Bool × Bool := by
  classical
  exact (decide (s.scale i A < ts), decide (tn ≤ zeroMatrix d f A i j))

theorem threshold_four (s : InputScale X I) (d : I → X → X → ENNReal)
    (f : Operator X bot) (A : Set X) (i j : I) (ts tn : ENNReal) :
    thresholdType s d f A i j ts tn = (true, true) ∨
    thresholdType s d f A i j ts tn = (true, false) ∨
    thresholdType s d f A i j ts tn = (false, true) ∨
    thresholdType s d f A i j ts tn = (false, false) := by
  classical
  by_cases h1 : s.scale i A < ts <;> by_cases h2 : tn ≤ zeroMatrix d f A i j <;>
    simp [thresholdType, h1, h2]

theorem threshold_four_distinct :
    ((true,true) : Bool × Bool) ≠ (true,false) ∧
    ((true,true) : Bool × Bool) ≠ (false,true) ∧
    ((true,true) : Bool × Bool) ≠ (false,false) ∧
    ((true,false) : Bool × Bool) ≠ (false,true) ∧
    ((true,false) : Bool × Bool) ≠ (false,false) ∧
    ((false,true) : Bool × Bool) ≠ (false,false) := by decide

theorem threshold_first_mono (s : InputScale X I) (d : I → X → X → ENNReal)
    (f : Operator X bot) (A : Set X) (i j : I) (t t' n : ENNReal) (h : t ≤ t') :
    (thresholdType s d f A i j t n).1 = true →
      (thresholdType s d f A i j t' n).1 = true := by
  classical
  simp only [thresholdType, decide_eq_true_eq]
  exact fun hx => lt_of_lt_of_le hx h

theorem threshold_second_antitone (s : InputScale X I) (d : I → X → X → ENNReal)
    (f : Operator X bot) (A : Set X) (i j : I) (t n n' : ENNReal) (h : n ≤ n') :
    (thresholdType s d f A i j t n').2 = true →
      (thresholdType s d f A i j t n).2 = true := by
  classical
  simp only [thresholdType, decide_eq_true_eq]
  exact fun hx => h.trans hx

theorem scale_domain_mono (s : InputScale X I) (i : I) (A B : Set X)
    (hB : B.Nonempty) (hBA : B ⊆ A) (t : ENNReal) :
    s.scale i B ≤ s.scale i A ∧ (s.scale i A < t → s.scale i B < t) :=
  ⟨s.mono i B A hB hBA, fun h => lt_of_le_of_lt (s.mono i B A hB hBA) h⟩

abbrev ImageQuotient (d : I → X → X → ENNReal) (f : Operator X bot) (U : Set X)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) := Quotient (imageZeroSetoid d f U hd)

def imageClass (d : I → X → X → ENNReal) (f : Operator X bot) (U : Set X)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (x : U) : ImageQuotient d f U hd :=
  Quotient.mk _ ⟨f.func x, ⟨x, x.property, rfl⟩⟩

theorem imageClass_surjective (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) :
    Function.Surjective (imageClass d f U hd) := by
  intro q
  induction q using Quotient.inductionOn with
  | _ a =>
    obtain ⟨x, hx, he⟩ := a.property
    refine ⟨⟨x,hx⟩, ?_⟩
    apply congrArg (Quotient.mk (imageZeroSetoid d f U hd))
    exact Subtype.ext he

theorem imageClass_eq_iff (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (x y : U) :
    imageClass d f U hd x = imageClass d f U hd y ↔
      GaugeZeroRelated d (f.func x) (f.func y) := by
  constructor
  · intro h
    exact Quotient.exact h
  · intro h
    exact Quotient.sound h

theorem factor_surjective_iff {A B C : Type} (p : A → B) (q : A → C)
    (hp : Function.Surjective p) :
    (∃ T : B → C, ∀ x, T (p x) = q x) ↔ ∀ x y, p x = p y → q x = q y := by
  classical
  constructor
  · rintro ⟨T, hT⟩ x y h
    exact (hT x).symm.trans ((congrArg T h).trans (hT y))
  · intro h
    let T : B → C := fun b => q (Classical.choose (hp b))
    refine ⟨T, ?_⟩
    intro x
    exact h _ _ (Classical.choose_spec (hp (p x)))

def HasQuotientFactor (d : I → X → X → ENNReal) (f g : Operator X bot) (U : Set X)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) : Prop :=
  ∃ T : ImageQuotient d f U hd → ImageQuotient d g U hd,
    ∀ x : U, T (imageClass d f U hd x) = imageClass d g U hd x

theorem quotient_factor_iff (d : I → X → X → ENNReal) (f g : Operator X bot)
    (U : Set X) (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) :
    HasQuotientFactor d f g U hd ↔ zeroRelation d f U ⊆ zeroRelation d g U := by
  rw [HasQuotientFactor, factor_surjective_iff _ _ (imageClass_surjective d f U hd)]
  constructor
  · intro h p hp
    rcases p with ⟨x,y⟩
    refine ⟨hp.1, hp.2.1, ?_⟩
    exact (imageClass_eq_iff d g U hd ⟨x,hp.1⟩ ⟨y,hp.2.1⟩).1
      (h ⟨x,hp.1⟩ ⟨y,hp.2.1⟩ ((imageClass_eq_iff d f U hd _ _).2 hp.2.2))
  · intro h x y hxy
    apply (imageClass_eq_iff d g U hd x y).2
    exact (h (show (x.1,y.1) ∈ zeroRelation d f U from
      ⟨x.property, y.property, (imageClass_eq_iff d f U hd x y).1 hxy⟩)).2.2

theorem quotient_factor_both_iff (d : I → X → X → ENNReal) (f g : Operator X bot)
    (U : Set X) (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) :
    (HasQuotientFactor d f g U hd ∧ HasQuotientFactor d g f U hd) ↔
      zeroRelation d f U = zeroRelation d g U := by
  rw [quotient_factor_iff, quotient_factor_iff, Set.Subset.antisymm_iff]

def SeparatesImage (d : I → X → X → ENNReal) (f : Operator X bot) (U : Set X) : Prop :=
  ∀ a ∈ f.func '' U, ∀ b ∈ f.func '' U, GaugeZeroRelated d a b → a = b

theorem point_zero_relation_eq (d : I → X → X → ENNReal) (f : Operator X bot) (U : Set X)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (hsep : SeparatesImage d f U) :
    pointRelation f U = zeroRelation d f U := by
  ext ⟨x,y⟩
  constructor
  · rintro ⟨hx, hy, he⟩
    refine ⟨hx, hy, ?_⟩
    intro i
    rw [he, (hd i).dist_self]
  · rintro ⟨hx, hy, hz⟩
    exact ⟨hx,hy,hsep _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ hz⟩

theorem separated_factor_criteria (d : I → X → X → ENNReal) (f g : Operator X bot)
    (U : Set X) (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (hf : SeparatesImage d f U) (hg : SeparatesImage d g U) :
    (HasPointFactor f g U ↔ HasQuotientFactor d f g U hd) ∧
    ((HasPointFactor f g U ∧ HasPointFactor g f U) ↔
      (HasQuotientFactor d f g U hd ∧ HasQuotientFactor d g f U hd)) := by
  rw [point_factor_both_iff, quotient_factor_both_iff, point_factor_iff, quotient_factor_iff,
    point_zero_relation_eq d f U hd hf, point_zero_relation_eq d g U hd hg]
  exact ⟨Iff.rfl, Iff.rfl⟩

def TotallyBoundedIn (d : X → X → ENNReal) (U : Set X) : Prop :=
  ∀ ε : ENNReal, 0 < ε → ε < ⊤ → covering_number d ε U < ⊤

theorem totallyBoundedIn_iff_nets (d : X → X → ENNReal) (U : Set X) :
    TotallyBoundedIn d U ↔
      ∀ ε : ENNReal, 0 < ε → ε < ⊤ →
        ∃ s : Finset X, InternalEpsilonNet d ε U s := by
  classical
  constructor
  · intro h ε hp ht
    by_contra hn
    exact (ne_of_lt (h ε hp ht)) ((covering_number_eq_top_iff d ε U).2 hn)
  · intro h ε hp ht
    apply lt_top_iff_ne_top.mpr
    intro heq
    exact ((covering_number_eq_top_iff d ε U).1 heq) (h ε hp ht)

theorem threshold_ball_fiber (d : I → X → X → ENNReal) (f : Operator X bot)
    (A : Set X) (i j : I) (x : X) (hx : x ∈ A) (t : ENNReal)
    (ht : t ≤ zeroMatrix d f A i j) :
    ball (d i) x t ∩ A ⊆ componentFiber d f j (f.func x) A := by
  intro y hy
  exact ⟨hy.2, strict_uniform_zero (d i) (d j) f A y x hy.2 hx (hy.1.trans_le ht)⟩

theorem covering_image_le_of_zero (din dout : X → X → ENNReal) (f : Operator X bot)
    (B : Set X) (r ε : ENNReal) (he : 0 < ε)
    (hz : ∀ x ∈ B, ∀ y ∈ B, din x y < r → dout (f.func x) (f.func y) = 0) :
    covering_number dout ε (f.func '' B) ≤ covering_number din r B := by
  classical
  unfold covering_number
  apply le_iInf
  intro S
  apply le_iInf
  intro hS
  have hnet : InternalEpsilonNet dout ε (f.func '' B) (S.image f.func) := by
    constructor
    · intro z hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      exact ⟨x, hS.1 hx, rfl⟩
    · rintro z ⟨x,hx,rfl⟩
      obtain ⟨c, hc, hdist⟩ := hS.2 x hx
      refine ⟨f.func c, Finset.mem_image.mpr ⟨c,hc,rfl⟩, ?_⟩
      rw [hz x hx c (hS.1 hc) hdist]
      exact he
  calc
    (⨅ (T : Finset X) (_ : InternalEpsilonNet dout ε (f.func '' B) T),
        (T.card : ENNReal)) ≤ ((S.image f.func).card : ENNReal) :=
      iInf_le_of_le _ (iInf_le_of_le hnet le_rfl)
    _ ≤ (S.card : ENNReal) := by exact_mod_cast Finset.card_image_le

theorem threshold_covering (d : I → X → X → ENNReal) (f : Operator X bot)
    (A B : Set X) (hBA : B ⊆ A) (i j : I) (t ε : ENNReal)
    (ht : t ≤ zeroMatrix d f A i j) (he : 0 < ε) :
    covering_number (d j) ε (f.func '' B) ≤ covering_number (d i) t B := by
  apply covering_image_le_of_zero _ _ f B t ε he
  intro x hx y hy hxy
  exact strict_uniform_zero (d i) (d j) f A x y (hBA hx) (hBA hy) (hxy.trans_le ht)

theorem covering_eq_one_of_zero (d : X → X → ENNReal) (A : Set X)
    (hA : A.Nonempty) (hzero : ∀ x ∈ A, ∀ y ∈ A, d x y = 0)
    (ε : ENNReal) (he : 0 < ε) : covering_number d ε A = 1 := by
  classical
  obtain ⟨a, ha⟩ := hA
  apply le_antisymm
  · have hn : InternalEpsilonNet d ε A {a} := by
      constructor
      · intro x hx
        have heq : x = a := Finset.mem_singleton.mp hx
        simpa [heq] using ha
      · intro x hx
        exact ⟨a, Finset.mem_singleton_self a, by rw [hzero x hx a ha]; exact he⟩
    have hbound : covering_number d ε A ≤ (({a} : Finset X).card : ENNReal) := by
      unfold covering_number
      exact iInf_le_of_le ({a} : Finset X) (iInf_le_of_le hn le_rfl)
    simpa using hbound
  · exact one_le_covering_number_of_nonempty d ε A ⟨a,ha⟩

theorem small_diameter_zero_iff (d : I → X → X → ENNReal) (f : Operator X bot)
    (A : Set X) (i j : I) (ts tn : ENNReal)
    (hdiam : (diameterScale d).scale i A < ts) (hts : ts ≤ tn) :
    tn ≤ zeroMatrix d f A i j ↔ i ∈ Set.univ ∧
      j ∈ constComponents d f A := by
  constructor
  · intro hn
    refine ⟨mem_univ _, ?_⟩
    intro x hx y hy
    have hxy : d i x y ≤ (diameterScale d).scale i A := by
      exact le_iSup_of_le x (le_iSup_of_le hx (le_iSup_of_le y (le_iSup_of_le hy le_rfl)))
    exact strict_uniform_zero (d i) (d j) f A x y hx hy
      (lt_of_le_of_lt hxy (lt_of_lt_of_le hdiam (hts.trans hn)))
  · rintro ⟨_, hconst⟩
    have htop := uniform_eq_top_of_all_zero (d i) (d j) f A hconst
    change tn ≤ uniformRadius (d i) (d j) f A A
    rw [htop]
    exact le_top

theorem const_output_covering_one (d : I → X → X → ENNReal) (f : Operator X bot)
    (A : Set X) (hA : A.Nonempty) (j : I) (hc : j ∈ constComponents d f A)
    (ε : ENNReal) (he : 0 < ε) : covering_number (d j) ε (f.func '' A) = 1 := by
  apply covering_eq_one_of_zero
  · obtain ⟨x,hx⟩ := hA
    exact ⟨f.func x, x, hx, rfl⟩
  · rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
    exact hc x hx y hy
  · exact he

theorem composition_radius_zero_preserving (d : I → X → X → ENNReal)
    (f g : Operator X bot) (U : Set X) (i j l : I)
    (hpres : ∀ y ∈ f.func '' U, ∀ z ∈ f.func '' U,
      d l y z = 0 → d j (g.func y) (g.func z) = 0) :
    zeroMatrix d f U i l ≤ zeroMatrix d (g * f) U i j := by
  change uniformRadius (d i) (d l) f U U ≤ uniformRadius (d i) (d j) (g * f) U U
  apply le_iInf
  intro y
  apply le_iInf
  intro hy
  apply (uniform_le_radius (d i) (d l) f U U y hy).trans
  apply sSup_le
  intro r hr
  apply admissible_le_radius
  refine ⟨hr.1, hr.2.1, ?_⟩
  intro x hx hxy
  exact hpres (f.func x) ⟨x,hx,rfl⟩ (f.func y) ⟨y,hy,rfl⟩ (hr.2.2 x hx hxy)

def EntropyDifferenceDomain (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (Jin Jout : Set I) (ε : ENNReal) : Prop :=
  U.Nonempty ∧ U ⊆ dom f ∧ Jin.Nonempty ∧ Jout.Nonempty ∧ 0 < ε ∧ ε < ⊤ ∧
    (covering_number (subfamily_pseudometric d Jin) ε U ≠ ⊤ ∨
     covering_number (subfamily_pseudometric d Jout) ε (f.func '' U) ≠ ⊤)

noncomputable def entropyDifference (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (Jin Jout : Set I) (ε : ENNReal)
    (_h : EntropyDifferenceDomain d f U Jin Jout ε) : EReal :=
  subfamily_metric_entropy d Jin ε U - subfamily_metric_entropy d Jout ε (f.func '' U)

theorem entropy_real_of_cover_finite (d : X → X → ENNReal) (U : Set X)
    (ε : ENNReal) (hU : U.Nonempty) (hfinite : covering_number d ε U ≠ ⊤) :
    ∃ a : ℝ, metric_entropy d ε U = (a : EReal) := by
  have h0 : covering_number d ε U ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_covering_number_of_nonempty d ε U hU))
  exact ⟨Real.logb 2 (covering_number d ε U).toReal, by simp [metric_entropy, log2_ereal, h0, hfinite]⟩

theorem entropy_top_of_cover_top (d : X → X → ENNReal) (U : Set X)
    (ε : ENNReal) (htop : covering_number d ε U = ⊤) : metric_entropy d ε U = ⊤ := by
  simp [metric_entropy, log2_ereal, htop]

theorem entropy_difference_finite (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (Jin Jout : Set I) (ε : ENNReal)
    (h : EntropyDifferenceDomain d f U Jin Jout ε)
    (hin : covering_number (subfamily_pseudometric d Jin) ε U ≠ ⊤)
    (hout : covering_number (subfamily_pseudometric d Jout) ε (f.func '' U) ≠ ⊤) :
    ∃ a : ℝ, entropyDifference d f U Jin Jout ε h = (a : EReal) := by
  have him : (f.func '' U).Nonempty := by
    obtain ⟨x,hx⟩ := h.1
    exact ⟨f.func x, x, hx, rfl⟩
  obtain ⟨a,ha⟩ := entropy_real_of_cover_finite (subfamily_pseudometric d Jin) U ε h.1 hin
  obtain ⟨b,hb⟩ := entropy_real_of_cover_finite (subfamily_pseudometric d Jout) (f.func '' U) ε him hout
  refine ⟨a-b, ?_⟩
  simp only [entropyDifference, subfamily_metric_entropy_eq_metric_entropy, ha, hb, EReal.coe_sub]

theorem entropy_difference_input_infinite (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (Jin Jout : Set I) (ε : ENNReal)
    (h : EntropyDifferenceDomain d f U Jin Jout ε)
    (hin : covering_number (subfamily_pseudometric d Jin) ε U = ⊤)
    (hout : covering_number (subfamily_pseudometric d Jout) ε (f.func '' U) ≠ ⊤) :
    entropyDifference d f U Jin Jout ε h = ⊤ := by
  have him : (f.func '' U).Nonempty := by
    obtain ⟨x,hx⟩ := h.1
    exact ⟨f.func x, x, hx, rfl⟩
  obtain ⟨b,hb⟩ := entropy_real_of_cover_finite (subfamily_pseudometric d Jout) (f.func '' U) ε him hout
  simp [entropyDifference, subfamily_metric_entropy_eq_metric_entropy,
    entropy_top_of_cover_top _ _ _ hin, hb]

theorem entropy_difference_output_infinite (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (Jin Jout : Set I) (ε : ENNReal)
    (h : EntropyDifferenceDomain d f U Jin Jout ε)
    (hin : covering_number (subfamily_pseudometric d Jin) ε U ≠ ⊤)
    (hout : covering_number (subfamily_pseudometric d Jout) ε (f.func '' U) = ⊤) :
    entropyDifference d f U Jin Jout ε h = ⊥ := by
  obtain ⟨a,ha⟩ := entropy_real_of_cover_finite (subfamily_pseudometric d Jin) U ε h.1 hin
  simp [entropyDifference, subfamily_metric_entropy_eq_metric_entropy,
    entropy_top_of_cover_top _ _ _ hout, ha]

theorem const_output_entropy_zero (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (hU : U.Nonempty) (j : I) (hc : j ∈ constComponents d f U)
    (ε : ENNReal) (he : 0 < ε) : metric_entropy (d j) ε (f.func '' U) = 0 := by
  simp [metric_entropy, log2_ereal, const_output_covering_one d f U hU j hc ε he]

theorem const_entropy_difference (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (j : I) (ε : ENNReal)
    (h : EntropyDifferenceDomain d f U {j} {j} ε)
    (hc : j ∈ constComponents d f U) :
    entropyDifference d f U {j} {j} ε h = metric_entropy (d j) ε U := by
  simp [entropyDifference, subfamily_metric_entropy_singleton,
    const_output_entropy_zero d f U h.1 j hc ε h.2.2.2.2.1]

theorem const_entropy_domain (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (j : I) (ε : ENNReal) (hU : U.Nonempty) (hdom : U ⊆ dom f)
    (he : 0 < ε) (hefin : ε < ⊤) (hc : j ∈ constComponents d f U) :
    EntropyDifferenceDomain d f U {j} {j} ε := by
  refine ⟨hU, hdom, ⟨j, by simp⟩, ⟨j, by simp⟩, he, hefin, Or.inr ?_⟩
  rw [subfamily_pseudometric_singleton, const_output_covering_one d f U hU j hc ε he]
  simp

theorem small_uniform_radius_witness (d : I → X → X → ENNReal) (f : Operator X bot)
    (A : Set X) (i j : I) (α τ : ENNReal) (hαpos : 0 < α) (hαfin : α < ⊤)
    (hlo : zeroMatrix d f A i j < α) (hhi : α < τ) :
    ∃ x ∈ A, ∃ y ∈ A, ∃ ε : ENNReal, 0 < ε ∧ ε < ⊤ ∧
      d i x y < α ∧ ε ≤ d j (f.func x) (f.func y) := by
  classical
  have _ := hhi
  change (⨅ y ∈ A, radius (d i) (d j) f A y) < α at hlo
  obtain ⟨y, hy⟩ := iInf_lt_iff.mp hlo
  obtain ⟨hyA, hyr⟩ := iInf_lt_iff.mp hy
  have hnot : ¬ ∀ x ∈ A, d i x y < α → d j (f.func x) (f.func y) = 0 := by
    intro hball
    have hle := admissible_le_radius (d i) (d j) f A y α ⟨hαpos, hαfin, hball⟩
    exact (not_le_of_gt hyr) hle
  push Not at hnot
  obtain ⟨x,hx,hxy,hout⟩ := hnot
  have hpos : 0 < d j (f.func x) (f.func y) := lt_of_le_of_ne (zero_le _) (Ne.symm hout)
  refine ⟨x,hx,y,hyA,min 1 (d j (f.func x) (f.func y)), ?_, ?_, hxy, min_le_right _ _⟩
  · exact lt_min zero_lt_one hpos
  · exact lt_of_le_of_lt (min_le_left _ _) (by simp)

theorem log2_ereal_mono_above_one (a b : ENNReal) (ha : 1 ≤ a) (hab : a ≤ b) :
    log2_ereal a ≤ log2_ereal b := by
  have ha0 : a ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one ha)
  have hb0 : b ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (ha.trans hab))
  by_cases hb : b = ⊤
  · simp [log2_ereal, hb]
  · have hat : a ≠ ⊤ := fun ht => hb (top_unique (ht ▸ hab))
    simp only [log2_ereal, if_neg ha0, if_neg hb0, if_neg hat, if_neg hb]
    apply EReal.coe_le_coe_iff.mpr
    exact (Real.logb_le_logb one_lt_two (ENNReal.toReal_pos ha0 hat)
      (ENNReal.toReal_pos hb0 hb)).2 (ENNReal.toReal_mono hb hab)

theorem threshold_entropy (d : I → X → X → ENNReal) (f : Operator X bot)
    (A B : Set X) (hBA : B ⊆ A) (hB : B.Nonempty) (i j : I) (t ε : ENNReal)
    (ht : t ≤ zeroMatrix d f A i j) (he : 0 < ε) :
    metric_entropy (d j) ε (f.func '' B) ≤ metric_entropy (d i) t B := by
  apply log2_ereal_mono_above_one
  · apply one_le_covering_number_of_nonempty
    obtain ⟨x,hx⟩ := hB
    exact ⟨f.func x,x,hx,rfl⟩
  · exact threshold_covering d f A B hBA i j t ε ht he

theorem point_factor_lip (dist : X → X → ENNReal) (f g : Operator X bot)
    (U : Set X) (T : (f.func '' U) → X) (K L : ENNReal)
    (hK : 0 < K) (hKfin : K < ⊤) (_hLfin : L < ⊤)
    (hT : ∀ x (hx : x ∈ U), T ⟨f.func x, ⟨x,hx,rfl⟩⟩ = g.func x)
    (hco : ∀ x ∈ U, ∀ y ∈ U, K * dist x y ≤ dist (f.func x) (f.func y))
    (hlip : ∀ x ∈ U, ∀ y ∈ U, dist (g.func x) (g.func y) ≤ L * dist x y) :
    ∀ a b : (f.func '' U), dist (T a) (T b) ≤ (L / K) * dist a.1 b.1 := by
  intro a b
  obtain ⟨x,hx,hax⟩ := a.property
  obtain ⟨y,hy,hby⟩ := b.property
  have ha : a = ⟨f.func x, ⟨x,hx,rfl⟩⟩ := Subtype.ext hax.symm
  have hb : b = ⟨f.func y, ⟨y,hy,rfl⟩⟩ := Subtype.ext hby.symm
  subst a
  subst b
  rw [hT x hx, hT y hy]
  have hdiv : dist x y ≤ dist (f.func x) (f.func y) / K := by
    apply (ENNReal.le_div_iff_mul_le (Or.inl (ne_of_gt hK))
      (Or.inl (ne_of_lt hKfin))).2
    simpa [mul_comm] using hco x hx y hy
  calc
    dist (g.func x) (g.func y) ≤ L * dist x y := hlip x hx y hy
    _ ≤ L * (dist (f.func x) (f.func y) / K) := mul_le_mul_left' hdiv L
    _ = (L / K) * dist (f.func x) (f.func y) := by
      simp [div_eq_mul_inv, mul_assoc, mul_comm]

end Chapter3

#print axioms Chapter3.constComponents
#print axioms Chapter3.identityComponents
#print axioms Chapter3.activeComponents
#print axioms Chapter3.components_partition
#print axioms Chapter3.const_zero_row
#print axioms Chapter3.const_colip_zero
#print axioms Chapter3.dist_eq_of_zero_endpoints
#print axioms Chapter3.identity_preserves_distance
#print axioms Chapter3.outer_const
#print axioms Chapter3.inner_const_of_single_row
#print axioms Chapter3.identity_comp
#print axioms Chapter3.active_comp
#print axioms Chapter3.seqOp
#print axioms Chapter3.seqActive
#print axioms Chapter3.seqOp_eq_reverse_prod
#print axioms Chapter3.identity_not_active
#print axioms Chapter3.active_seq
#print axioms Chapter3.fiber
#print axioms Chapter3.componentFiber
#print axioms Chapter3.subfamily_zero_iff
#print axioms Chapter3.fiber_intersection
#print axioms Chapter3.fiber_antitone
#print axioms Chapter3.fiber_singleton
#print axioms Chapter3.fiber_all_subset
#print axioms Chapter3.fiber_target_zero
#print axioms Chapter3.fiber_image_cover
#print axioms Chapter3.fiber_equal_or_disjoint
#print axioms Chapter3.identity_component_fiber
#print axioms Chapter3.constant_component_fiber
#print axioms Chapter3.admissibleRadius
#print axioms Chapter3.radius
#print axioms Chapter3.uniformRadius
#print axioms Chapter3.zeroMatrix
#print axioms Chapter3.admissible_le_radius
#print axioms Chapter3.strict_radius_zero
#print axioms Chapter3.radius_mono_domain
#print axioms Chapter3.uniform_le_radius
#print axioms Chapter3.uniform_mono_domain
#print axioms Chapter3.strict_uniform_zero
#print axioms Chapter3.positive_output_lower_bound
#print axioms Chapter3.radius_eq_top_of_all_zero
#print axioms Chapter3.uniform_eq_top_of_all_zero
#print axioms Chapter3.const_subfamily_fiber
#print axioms Chapter3.const_subfamily_radii
#print axioms Chapter3.identity_fiber_at_image
#print axioms Chapter3.identity_radius_lower
#print axioms Chapter3.fiber_zero
#print axioms Chapter3.strict_radius_zero_symm
#print axioms Chapter3.fiber_zero_composite
#print axioms Chapter3.colip_point_gap
#print axioms Chapter3.colip_uniform_gap
#print axioms Chapter3.pointRelation
#print axioms Chapter3.zeroRelation
#print axioms Chapter3.fiberPreorder
#print axioms Chapter3.imageZeroSetoid
#print axioms Chapter3.zeroRelation_fiber
#print axioms Chapter3.fiberPreorder_refl
#print axioms Chapter3.fiberPreorder_trans
#print axioms Chapter3.fiberPreorder_chain
#print axioms Chapter3.fiberPreorder_chain_strict
#print axioms Chapter3.HasPointFactor
#print axioms Chapter3.point_factor_iff
#print axioms Chapter3.point_factor_both_iff
#print axioms Chapter3.InputScale
#print axioms Chapter3.diameterScale
#print axioms Chapter3.thresholdType
#print axioms Chapter3.threshold_four
#print axioms Chapter3.threshold_four_distinct
#print axioms Chapter3.threshold_first_mono
#print axioms Chapter3.threshold_second_antitone
#print axioms Chapter3.scale_domain_mono
#print axioms Chapter3.ImageQuotient
#print axioms Chapter3.imageClass
#print axioms Chapter3.imageClass_surjective
#print axioms Chapter3.imageClass_eq_iff
#print axioms Chapter3.factor_surjective_iff
#print axioms Chapter3.HasQuotientFactor
#print axioms Chapter3.quotient_factor_iff
#print axioms Chapter3.quotient_factor_both_iff
#print axioms Chapter3.SeparatesImage
#print axioms Chapter3.point_zero_relation_eq
#print axioms Chapter3.separated_factor_criteria
#print axioms Chapter3.TotallyBoundedIn
#print axioms Chapter3.totallyBoundedIn_iff_nets
#print axioms Chapter3.threshold_ball_fiber
#print axioms Chapter3.covering_image_le_of_zero
#print axioms Chapter3.threshold_covering
#print axioms Chapter3.covering_eq_one_of_zero
#print axioms Chapter3.small_diameter_zero_iff
#print axioms Chapter3.const_output_covering_one
#print axioms Chapter3.composition_radius_zero_preserving
#print axioms Chapter3.EntropyDifferenceDomain
#print axioms Chapter3.entropyDifference
#print axioms Chapter3.entropy_real_of_cover_finite
#print axioms Chapter3.entropy_top_of_cover_top
#print axioms Chapter3.entropy_difference_finite
#print axioms Chapter3.entropy_difference_input_infinite
#print axioms Chapter3.entropy_difference_output_infinite
#print axioms Chapter3.const_output_entropy_zero
#print axioms Chapter3.const_entropy_difference
#print axioms Chapter3.const_entropy_domain
#print axioms Chapter3.small_uniform_radius_witness
#print axioms Chapter3.log2_ereal_mono_above_one
#print axioms Chapter3.threshold_entropy
#print axioms Chapter3.point_factor_lip
