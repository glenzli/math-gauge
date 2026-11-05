import formal_oet.vol_01.ch_01_foundations.metric_entropy
import formal_oet.vol_01.ch_02_operator_bounds.decoupling

/-! Partial formalization based on Zhe Li, The Operator Evolution Theory,
Volume I, https://glenzli.com/books/oet/, CC BY 4.0. -/

namespace C3

open Set
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds

variable {X I : Type} {bot : X}

def c01 (d : I → X → X → ENNReal) (f : Operator X bot) (U : Set X) : Set I :=
  {i | ∀ x ∈ U, ∀ y ∈ U, d i (f.func x) (f.func y) = 0}

def c02 (d : I → X → X → ENNReal) (f : Operator X bot) (U : Set X) : Set I :=
  {i | i ∉ c01 d f U ∧ ∀ x ∈ U, d i (f.func x) x = 0}

def c03 (d : I → X → X → ENNReal) (f : Operator X bot) (U : Set X) : Set I :=
  (c01 d f U ∪ c02 d f U)ᶜ

theorem c04 (d : I → X → X → ENNReal) (f : Operator X bot) (U : Set X)
    (i : I) :
    (i ∈ c01 d f U ∨ i ∈ c02 d f U ∨
      i ∈ c03 d f U) ∧
    ¬ (i ∈ c01 d f U ∧ i ∈ c02 d f U) ∧
    ¬ (i ∈ c01 d f U ∧ i ∈ c03 d f U) ∧
    ¬ (i ∈ c02 d f U ∧ i ∈ c03 d f U) := by
  classical
  simp only [c02, c03, mem_setOf_eq, mem_compl_iff, mem_union]
  tauto

theorem c05 [Fintype I] (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (i : I) (hi : i ∈ c01 d f U) :
    ∀ x ∈ U, ∀ y ∈ U, d i (f.func x) (f.func y) ≤ ∑ k : I, (0 : ENNReal) * d k x y := by
  intro x hx y hy
  simp [hi x hx y hy]

theorem c06 [Fintype I] (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (i k : I) (K : I → I → ENNReal)
    (hi : i ∈ c01 d f U) (hK : IsCoLipMatrix d f U K)
    (x y : X) (hx : x ∈ U) (hy : y ∈ U) (hpos : 0 < d k x y) : K k i = 0 :=
  colip_entry_eq_zero_of_output_zero_input_pos d f U K k i x y hK hx hy
    (hi x hx y hy) hpos

theorem c07 (d : X → X → ENNReal)
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

theorem c08 (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (i : I)
    (hd : ExtendedPseudoMetric X bot (d i)) (hi : i ∈ c02 d f U) :
    ∀ x ∈ U, ∀ y ∈ U, d i (f.func x) (f.func y) = d i x y := by
  intro x hx y hy
  exact c07 (d i) hd.symm hd.triangle (hi.2 x hx) (hi.2 y hy)

theorem c09 (d : I → X → X → ENNReal) (f g : Operator X bot)
    (U : Set X) (i : I) (h : i ∈ c01 d g (f.func '' U)) :
    i ∈ c01 d (g * f) U := by
  intro x hx y hy
  exact h (f.func x) ⟨x, hx, rfl⟩ (f.func y) ⟨y, hy, rfl⟩

theorem c10 [Fintype I] (d : I → X → X → ENNReal)
    (f g : Operator X bot) (U : Set X) (j : I) (L : I → I → ENNReal)
    (hc : j ∈ c01 d f U) (hL : IsLipMatrix d g (f.func '' U) L)
    (hrow : ∀ k, k ≠ j → L k j = 0) : j ∈ c01 d (g * f) U := by
  intro x hx y hy
  apply le_antisymm _ (zero_le _)
  have h := lip_bound_of_single_input_row d g (f.func '' U) L j j hL hrow
      (f.func x) ⟨x, hx, rfl⟩ (f.func y) ⟨y, hy, rfl⟩
  simpa [hc x hx y hy] using h

theorem c11 (d : I → X → X → ENNReal) (f g : Operator X bot)
    (U : Set X) (i : I) (hd : ExtendedPseudoMetric X bot (d i))
    (hf : i ∈ c02 d f U) (hg : i ∈ c02 d g (f.func '' U)) :
    i ∈ c02 d (g * f) U := by
  constructor
  · intro hc
    apply hf.1
    intro x hx y hy
    have heq := c08 d g (f.func '' U) i hd hg
      (f.func x) ⟨x, hx, rfl⟩ (f.func y) ⟨y, hy, rfl⟩
    exact heq.symm.trans (hc x hx y hy)
  · intro x hx
    apply le_antisymm _ (zero_le _)
    calc
      d i ((g * f).func x) x ≤ d i (g.func (f.func x)) (f.func x) + d i (f.func x) x :=
        hd.triangle _ _ _
      _ = 0 := by rw [hg.2 _ ⟨x, hx, rfl⟩, hf.2 x hx, add_zero]

theorem c12 (d : I → X → X → ENNReal) (f g : Operator X bot)
    (U : Set X) (i : I) (hd : ExtendedPseudoMetric X bot (d i)) :
    i ∈ c03 d (g * f) U →
      i ∈ c03 d f U ∨ i ∈ c03 d g (f.func '' U) := by
  classical
  intro hc
  by_contra h
  have hf : i ∈ c01 d f U ∨ i ∈ c02 d f U := by
    have h1 := (not_or.mp h).1
    simp only [c03, mem_compl_iff, mem_union] at h1
    tauto
  have hg : i ∈ c01 d g (f.func '' U) ∨
      i ∈ c02 d g (f.func '' U) := by
    have h2 := (not_or.mp h).2
    simp only [c03, mem_compl_iff, mem_union] at h2
    tauto
  have hnot : i ∉ c01 d (g * f) U ∧ i ∉ c02 d (g * f) U := by
    simpa [c03] using hc
  rcases hg with hg | hg
  · exact hnot.1 (c09 d f g U i hg)
  · rcases hf with hf | hf
    · apply hnot.1
      intro x hx y hy
      have heq := c08 d g (f.func '' U) i hd hg
        (f.func x) ⟨x, hx, rfl⟩ (f.func y) ⟨y, hy, rfl⟩
      exact heq.trans (hf x hx y hy)
    · exact hnot.2 (c11 d f g U i hd hf hg)

def c13 : List (Operator X bot) → Operator X bot
  | [] => 1
  | f :: fs => c13 fs * f

def c14 (d : I → X → X → ENNReal) : List (Operator X bot) → Set X → Set I
  | [], _ => ∅
  | f :: fs, U => c03 d f U ∪ c14 d fs (f.func '' U)

theorem c15 (fs : List (Operator X bot)) : c13 fs = fs.reverse.prod := by
  induction fs with
  | nil => rfl
  | cons f fs ih => simp [c13, ih, List.prod_append]

theorem c16 (d : I → X → X → ENNReal)
    (U : Set X) (i : I) (hself : ∀ x, d i x x = 0) :
    i ∉ c03 d (1 : Operator X bot) U := by
  classical
  simp only [c03, mem_compl_iff, mem_union, not_not]
  by_cases hc : i ∈ c01 d (1 : Operator X bot) U
  · exact Or.inl hc
  · right
    exact ⟨hc, fun x _ => hself x⟩

theorem c17 (d : I → X → X → ENNReal) (fs : List (Operator X bot))
    (U : Set X) (i : I) (hd : ExtendedPseudoMetric X bot (d i)) :
    i ∈ c03 d (c13 fs) U → i ∈ c14 d fs U := by
  induction fs generalizing U with
  | nil =>
      intro h
      exact (c16 d U i hd.dist_self h).elim
  | cons f fs ih =>
      intro h
      rcases c12 d f (c13 fs) U i hd h with h | h
      · exact Or.inl h
      · exact Or.inr (ih (f.func '' U) h)

def c18 (d : I → X → X → ENNReal) (f : Operator X bot)
    (J : Set I) (y : X) (U : Set X) : Set X :=
  {x | x ∈ U ∧ subfamily_pseudometric d J (f.func x) y = 0}

def c19 (d : I → X → X → ENNReal) (f : Operator X bot)
    (j : I) (y : X) (U : Set X) : Set X :=
  {x | x ∈ U ∧ d j (f.func x) y = 0}

theorem c20 (d : I → X → X → ENNReal) (J : Set I) (x y : X) :
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

theorem c21 (d : I → X → X → ENNReal) (f : Operator X bot)
    (J : Set I) (y : X) (U : Set X) (hJ : J.Nonempty) :
    c18 d f J y U = ⋂ j ∈ J, c19 d f j y U := by
  ext x
  simp only [c18, c19, mem_setOf_eq, c20, mem_iInter]
  constructor
  · rintro ⟨hx, h⟩ j hj
    exact ⟨hx, h j hj⟩
  · intro h
    obtain ⟨j, hj⟩ := hJ
    exact ⟨(h j hj).1, fun j hj => (h j hj).2⟩

theorem c22 (d : I → X → X → ENNReal) (f : Operator X bot)
    (J K : Set I) (y : X) (U : Set X) (hJK : J ⊆ K) :
    c18 d f K y U ⊆ c18 d f J y U := by
  intro x hx
  exact ⟨hx.1, (c20 d J _ _).2
    (fun j hj => (c20 d K _ _).1 hx.2 j (hJK hj))⟩

theorem c23 (d : I → X → X → ENNReal) (f : Operator X bot)
    (j : I) (y : X) (U : Set X) : c18 d f {j} y U = c19 d f j y U := by
  ext x
  simp [c18, c19, subfamily_pseudometric_singleton]

theorem c24 (d : I → X → X → ENNReal) (f : Operator X bot)
    (j : I) (y : X) (U : Set X) : c18 d f univ y U ⊆ c19 d f j y U := by
  rw [← c23]
  exact c22 d f _ _ _ _ (subset_univ _)

theorem c25 (d : I → X → X → ENNReal) (f : Operator X bot)
    (J : Set I) (y z : X) (U : Set X) (hd : ∀ j, ExtendedPseudoMetric X bot (d j))
    (hyz : subfamily_pseudometric d J y z = 0) : c18 d f J y U = c18 d f J z U := by
  ext x
  simp only [c18, mem_setOf_eq, c20]
  constructor <;> intro h <;> refine ⟨h.1, ?_⟩ <;> intro j hj
  · apply le_antisymm _ (zero_le _)
    calc
      d j (f.func x) z ≤ d j (f.func x) y + d j y z := (hd j).triangle _ _ _
      _ = 0 := by rw [h.2 j hj, (c20 d J y z).1 hyz j hj, add_zero]
  · apply le_antisymm _ (zero_le _)
    calc
      d j (f.func x) y ≤ d j (f.func x) z + d j z y := (hd j).triangle _ _ _
      _ = 0 := by rw [h.2 j hj, (hd j).symm z y,
          (c20 d J y z).1 hyz j hj, add_zero]

theorem c26 (d : I → X → X → ENNReal) (f : Operator X bot)
    (J : Set I) (U : Set X) (hd : ∀ j, ExtendedPseudoMetric X bot (d j)) :
    (∀ y ∈ f.func '' U, (c18 d f J y U).Nonempty) ∧
    (⋃ y ∈ f.func '' U, c18 d f J y U) = U := by
  constructor
  · rintro y ⟨x, hx, rfl⟩
    exact ⟨x, hx, (c20 d J _ _).2 (fun j _ => (hd j).dist_self _)⟩
  · ext x
    constructor
    · intro hx
      obtain ⟨y, _, hxy⟩ := Set.mem_iUnion₂.mp hx
      exact hxy.1
    · intro hx
      apply Set.mem_iUnion₂.mpr
      exact ⟨f.func x, ⟨x, hx, rfl⟩, hx,
        (c20 d J _ _).2 (fun j _ => (hd j).dist_self _)⟩

theorem c27 (d : I → X → X → ENNReal) (f : Operator X bot)
    (J : Set I) (U : Set X) (y z : X) (hd : ∀ j, ExtendedPseudoMetric X bot (d j)) :
    c18 d f J y U = c18 d f J z U ∨ Disjoint (c18 d f J y U) (c18 d f J z U) := by
  classical
  by_cases h : Disjoint (c18 d f J y U) (c18 d f J z U)
  · exact Or.inr h
  · left
    have hex : ∃ x, x ∈ c18 d f J y U ∧ x ∈ c18 d f J z U := Set.not_disjoint_iff.mp h
    obtain ⟨x, hx, hx'⟩ := hex
    apply c25 d f J y z U hd
    apply (c20 d J y z).2
    intro j hj
    apply le_antisymm _ (zero_le _)
    calc
      d j y z ≤ d j y (f.func x) + d j (f.func x) z := (hd j).triangle _ _ _
      _ = 0 := by
        rw [(hd j).symm y (f.func x), (c20 d J _ _).1 hx.2 j hj,
          (c20 d J _ _).1 hx'.2 j hj, add_zero]

theorem c28 (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (i : I) (y : X)
    (hd : ExtendedPseudoMetric X bot (d i)) (hi : i ∈ c02 d f U) :
    c19 d f i y U = {x | x ∈ U ∧ d i x y = 0} := by
  ext x
  simp only [c19, mem_setOf_eq]
  constructor <;> intro h <;> refine ⟨h.1, ?_⟩
  · have hdist := c07 (d i) hd.symm hd.triangle (hi.2 x h.1) (hd.dist_self y)
    exact hdist.symm.trans h.2
  · have hdist := c07 (d i) hd.symm hd.triangle (hi.2 x h.1) (hd.dist_self y)
    exact hdist.trans h.2

theorem c29 (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (i : I) (y₀ y : X)
    (hd : ExtendedPseudoMetric X bot (d i)) (hc : i ∈ c01 d f U)
    (hy₀ : y₀ ∈ f.func '' U) : c19 d f i y₀ U = U ∧
      (0 < d i y y₀ → c19 d f i y U = ∅) := by
  obtain ⟨z, hz, rfl⟩ := hy₀
  constructor
  · ext x
    simp only [c19, mem_setOf_eq]
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

def c30 (f : Operator X bot) (U : Set X) : Set (X × X) :=
  {p | p.1 ∈ U ∧ p.2 ∈ U ∧ f.func p.1 = f.func p.2}

def c31 (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) : Set (X × X) :=
  {p | p.1 ∈ U ∧ p.2 ∈ U ∧ GaugeZeroRelated d (f.func p.1) (f.func p.2)}

def c32 (d : I → X → X → ENNReal) (f : Operator X bot) (U : Set X)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) : Setoid {y // y ∈ f.func '' U} where
  r y z := GaugeZeroRelated d y.1 z.1
  iseqv := by
    have he := gauge_zero_related_equivalence d (fun i => (hd i).dist_self)
      (fun i => (hd i).symm) (fun i => (hd i).triangle)
    refine ⟨?_, ?_, ?_⟩
    · intro y; exact he.refl y.1
    · intro y z h; exact he.symm h
    · intro y z w h k; exact he.trans h k

def c33 (d : I → X → X → ENNReal) (f : Operator X bot) (U : Set X)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) : Type :=
  Quotient (c32 d f U hd)

def c34 (d : I → X → X → ENNReal) (U : Set X)
    (f g : Operator X bot) : Prop := c31 d f U ⊆ c31 d g U

theorem c35 (d : I → X → X → ENNReal) (U : Set X)
    (f : Operator X bot) : c34 d U f f := Set.Subset.refl _

theorem c36 (d : I → X → X → ENNReal) (U : Set X)
    (f g h : Operator X bot) : c34 d U f g → c34 d U g h →
    c34 d U f h := Set.Subset.trans

theorem c37 (d : I → X → X → ENNReal) (U : Set X)
    (fs : ℕ → Operator X bot) (m : ℕ)
    (hstep : ∀ k, k < m → c34 d U (fs k) (fs (k + 1)))
    (a b : ℕ) (hab : a ≤ b) (hbm : b ≤ m) : c34 d U (fs a) (fs b) := by
  induction b with
  | zero =>
      have : a = 0 := by omega
      subst a
      exact c35 d U _
  | succ b ih =>
      by_cases h : a ≤ b
      · exact c36 d U _ _ _ (ih h (by omega)) (hstep b (by omega))
      · have : a = b + 1 := by omega
        subst a
        exact c35 d U _

theorem c38 (d : I → X → X → ENNReal) (U : Set X)
    (fs : ℕ → Operator X bot) (m r : ℕ)
    (hstep : ∀ k, k < m → c34 d U (fs k) (fs (k + 1)))
    (hr : r < m) (hstrict : c31 d (fs r) U ⊂ c31 d (fs (r + 1)) U) :
    c31 d (fs 0) U ⊂ c31 d (fs m) U ∧
      ∃ p, p ∈ c31 d (fs m) U ∧ p ∉ c31 d (fs 0) U := by
  have h0 := c37 d U fs m hstep 0 r (by omega) (by omega)
  have hm := c37 d U fs m hstep (r + 1) m (by omega) (by omega)
  have hs := hstrict.1
  have hp : ∃ p, p ∈ c31 d (fs (r + 1)) U ∧ p ∉ c31 d (fs r) U := by
    by_contra hn
    apply hstrict.2
    intro p hp
    by_contra hp'
    exact hn ⟨p, hp, hp'⟩
  obtain ⟨p, hp, hpn⟩ := hp
  have hw : p ∈ c31 d (fs m) U ∧ p ∉ c31 d (fs 0) U :=
    ⟨hm hp, fun hp0 => hpn (h0 hp0)⟩
  exact ⟨⟨c37 d U fs m hstep 0 m (by omega) (by omega),
    fun hback => hw.2 (hback hw.1)⟩, ⟨p, hw⟩⟩

theorem c39 (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (x y : X) (hx : x ∈ U) (hy : y ∈ U)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) :
    (x, y) ∈ c31 d f U ↔ y ∈ c18 d f univ (f.func x) U := by
  simp only [c31, c18, mem_setOf_eq, hx, hy, true_and, c20,
    mem_univ, forall_const, GaugeZeroRelated]
  constructor <;> intro h i
  · rw [(hd i).symm]
    exact h i
  · rw [(hd i).symm]
    exact h i

def c40 (f : Operator X bot) (U : Set X) (x : X) (hx : x ∈ U) :
    {y // y ∈ f.func '' U} := ⟨f.func x, ⟨x, hx, rfl⟩⟩

def c41 (f g : Operator X bot) (U : Set X) : Prop :=
  ∃ T : {y // y ∈ f.func '' U} → X, ∀ x (hx : x ∈ U), T (c40 f U x hx) = g.func x

theorem c42 (f g : Operator X bot) (U : Set X) :
    c41 f g U ↔ c30 f U ⊆ c30 g U := by
  classical
  constructor
  · rintro ⟨T, hT⟩ ⟨x, y⟩ ⟨hx, hy, hxy⟩
    refine ⟨hx, hy, ?_⟩
    have he : c40 f U x hx = c40 f U y hy := Subtype.ext hxy
    calc
      g.func x = T (c40 f U x hx) := (hT x hx).symm
      _ = T (c40 f U y hy) := congrArg T he
      _ = g.func y := hT y hy
  · intro h
    let T : {y // y ∈ f.func '' U} → X := fun y => g.func (Classical.choose y.2)
    refine ⟨T, ?_⟩
    intro x hx
    have hc := Classical.choose_spec (c40 f U x hx).2
    have hr : (Classical.choose (c40 f U x hx).2, x) ∈ c30 f U :=
      ⟨hc.1, hx, hc.2⟩
    exact (h hr).2.2

theorem c43 (f g : Operator X bot) (U : Set X) :
    (c41 f g U ∧ c41 g f U) ↔
      c30 f U = c30 g U := by
  rw [c42, c42, Set.Subset.antisymm_iff]

def c44 (d : I → X → X → ENNReal) (f : Operator X bot) (U : Set X)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (x : X) (hx : x ∈ U) :
    c33 d f U hd := Quotient.mk (c32 d f U hd) (c40 f U x hx)

def c45 (d : I → X → X → ENNReal) (f g : Operator X bot)
    (U : Set X) (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) : Prop :=
  ∃ T : c33 d f U hd → c33 d g U hd,
    ∀ x (hx : x ∈ U), T (c44 d f U hd x hx) = c44 d g U hd x hx

theorem c46 (d : I → X → X → ENNReal) (f g : Operator X bot)
    (U : Set X) (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) :
    c45 d f g U hd ↔ c34 d U f g := by
  classical
  constructor
  · rintro ⟨T, hT⟩ ⟨x, y⟩ ⟨hx, hy, hxy⟩
    refine ⟨hx, hy, ?_⟩
    have he : c44 d f U hd x hx = c44 d f U hd y hy :=
      Quotient.sound hxy
    have ho : c44 d g U hd x hx = c44 d g U hd y hy := by
      calc
        _ = T (c44 d f U hd x hx) := (hT x hx).symm
        _ = T (c44 d f U hd y hy) := congrArg T he
        _ = _ := hT y hy
    exact Quotient.exact ho
  · intro h
    let F : {y // y ∈ f.func '' U} → c33 d g U hd := fun z =>
      c44 d g U hd (Classical.choose z.2) (Classical.choose_spec z.2).1
    have hF : ∀ a b, (c32 d f U hd).r a b → F a = F b := by
      intro a b hab
      apply Quotient.sound
      have ha := Classical.choose_spec a.2
      have hb := Classical.choose_spec b.2
      apply (h (show (Classical.choose a.2, Classical.choose b.2) ∈ c31 d f U from ?_)).2.2
      refine ⟨ha.1, hb.1, ?_⟩
      simpa only [ha.2, hb.2] using hab
    refine ⟨Quotient.lift F hF, ?_⟩
    intro x hx
    apply Quotient.sound
    have hc := Classical.choose_spec (c40 f U x hx).2
    have hz : GaugeZeroRelated d (f.func (Classical.choose (c40 f U x hx).2)) (f.func x) := by
      rw [hc.2]
      exact fun i => (hd i).dist_self _
    exact (h (show (Classical.choose (c40 f U x hx).2, x) ∈ c31 d f U from
      ⟨hc.1, hx, hz⟩)).2.2

theorem c47 (d : I → X → X → ENNReal)
    (f g : Operator X bot) (U : Set X) (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) :
    (c45 d f g U hd ∧ c45 d g f U hd) ↔
      c31 d f U = c31 d g U := by
  rw [c46, c46]
  exact Set.Subset.antisymm_iff.symm

def c48 (d : I → X → X → ENNReal) (A : Set X) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, GaugeZeroRelated d x y → x = y

theorem c49 (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (hs : c48 d (f.func '' U)) : c30 f U = c31 d f U := by
  ext ⟨x, y⟩
  constructor
  · rintro ⟨hx, hy, he⟩
    refine ⟨hx, hy, ?_⟩
    intro i
    rw [he, (hd i).dist_self]
  · rintro ⟨hx, hy, hz⟩
    exact ⟨hx, hy, hs _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hz⟩

theorem c50 (d : I → X → X → ENNReal)
    (f g : Operator X bot) (U : Set X) (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (hf : c48 d (f.func '' U)) (hg : c48 d (g.func '' U)) :
    (c41 f g U ↔ c45 d f g U hd) ∧
    ((c41 f g U ∧ c41 g f U) ↔
     (c45 d f g U hd ∧ c45 d g f U hd)) := by
  have h1 := c49 d f U hd hf
  have h2 := c49 d g U hd hg
  constructor
  · rw [c42, c46, h1, h2]
    rfl
  · rw [c43, c47, h1, h2]

def c51 (di dout : X → X → ENNReal) (f : Operator X bot)
    (y : X) (U : Set X) (r : ENNReal) : Prop :=
  0 < r ∧ r < ⊤ ∧ ∀ x ∈ U, di x y < r → dout (f.func x) (f.func y) = 0

noncomputable def c52 (di dout : X → X → ENNReal) (f : Operator X bot)
    (y : X) (U : Set X) : ENNReal := sSup {r | c51 di dout f y U r}

noncomputable def c53 (di dout : X → X → ENNReal) (f : Operator X bot)
    (A U : Set X) : ENNReal := ⨅ y ∈ A, c52 di dout f y U

noncomputable def c54 (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (i j : I) : ENNReal := c53 (d i) (d j) f U U

theorem c55 (di dout : X → X → ENNReal) (f : Operator X bot)
    (y : X) (U : Set X) (r : ENNReal) : c51 di dout f y U r ↔
    0 < r ∧ r < ⊤ ∧
      (ball di y r ∩ U ⊆ {x | x ∈ U ∧ dout (f.func x) (f.func y) = 0}) := by
  simp only [c51, ball, Set.subset_def, Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hpos, hfin, h⟩
    exact ⟨hpos, hfin, fun x hx => ⟨hx.2, h x hx.2 hx.1⟩⟩
  · rintro ⟨hpos, hfin, h⟩
    exact ⟨hpos, hfin, fun x hx hr => (h x ⟨hr, hx⟩).2⟩

theorem c56 (di dout : X → X → ENNReal) (f : Operator X bot)
    (y : X) (A B : Set X) (hBA : B ⊆ A) :
    c52 di dout f y A ≤ c52 di dout f y B := by
  apply sSup_le
  intro r hr
  apply le_sSup
  exact ⟨hr.1, hr.2.1, fun x hx => hr.2.2 x (hBA hx)⟩

theorem c57 (di dout : X → X → ENNReal) (f : Operator X bot)
    (A B : Set X) (hBA : B ⊆ A) :
    c53 di dout f A A ≤ c53 di dout f B B := by
  apply le_iInf
  intro y
  apply le_iInf
  intro hy
  exact (iInf_le_of_le y (iInf_le_of_le (hBA hy) le_rfl)).trans
    (c56 di dout f y A B hBA)

theorem c58 (di dout : X → X → ENNReal) (f : Operator X bot)
    (y : X) (U : Set X) (r : ENNReal) (h : c51 di dout f y U r) :
    r ≤ c52 di dout f y U := le_sSup h

theorem c59 (di dout : X → X → ENNReal) (f : Operator X bot)
    (y : X) (U : Set X) (a : ENNReal) (h : a < c52 di dout f y U) :
    ∃ r, c51 di dout f y U r ∧ a < r := lt_sSup_iff.mp h

theorem c60 (di dout : X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (y x : X) (hx : x ∈ U) (hds : ∀ a b, di a b = di b a)
    (h : di y x < c52 di dout f y U) : dout (f.func x) (f.func y) = 0 := by
  obtain ⟨r, hr, hlt⟩ := c59 di dout f y U (di y x) h
  apply hr.2.2 x hx
  rwa [hds x y]

theorem c61 (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (i j : I) (y x : X) (hx : x ∈ U)
    (hi : ExtendedPseudoMetric X bot (d i)) (hj : ExtendedPseudoMetric X bot (d j))
    (h : d i y x < c52 (d i) (d j) f y U) :
    d j (f.func y) (f.func x) = 0 := by
  rw [hj.symm]
  exact c60 _ _ f U y x hx hi.symm h

theorem c62 (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (j : I) (y x : X) (hd : ExtendedPseudoMetric X bot (d j))
    (h : x ∈ c19 d f j (f.func y) U) :
    d j (f.func y) (f.func x) = 0 := by
  rw [hd.symm, h.2]

theorem c63 (d : I → X → X → ENNReal)
    (f g : Operator X bot) (V : Set X) (j : I) (x y : X)
    (hd : ExtendedPseudoMetric X bot (d j))
    (hx : f.func x ∈ V) (hy : f.func y ∈ V)
    (h : f.func y ∈ c19 d g j (g.func (f.func x)) V) :
    d j ((g * f).func x) ((g * f).func y) = 0 := by
  exact c62 d g V j (f.func x) (f.func y) hd h

theorem c64 (di dout : X → X → ENNReal) (f : Operator X bot)
    (A U : Set X) (y : X) (hy : y ∈ A) :
    c53 di dout f A U ≤ c52 di dout f y U :=
  iInf_le_of_le y (iInf_le_of_le hy le_rfl)

theorem c65 (di dout : X → X → ENNReal) (f : Operator X bot)
    (A : Set X) (y x : X) (hy : y ∈ A) (hx : x ∈ A)
    (hin : ∀ a b, di a b = di b a) (hout : ∀ a b, dout a b = dout b a)
    (h : di y x < c53 di dout f A A) : dout (f.func y) (f.func x) = 0 := by
  rw [hout]
  exact c60 di dout f A y x hx hin
    (lt_of_lt_of_le h (c64 di dout f A A y hy))

theorem c66 (di dout : X → X → ENNReal)
    (f : Operator X bot) (A : Set X) (x y : X) (hx : x ∈ A) (hy : y ∈ A)
    (hin : ∀ a b, di a b = di b a) (hout : ∀ a b, dout a b = dout b a)
    (hpos : 0 < dout (f.func x) (f.func y)) :
    c53 di dout f A A ≤ di x y := by
  by_contra h
  have hlt : di x y < c53 di dout f A A := lt_of_not_ge h
  exact (ne_of_gt hpos) (c65 di dout f A x y hx hy hin hout hlt)

theorem c67 (di dout : X → X → ENNReal) (f : Operator X bot)
    (A : Set X) (alpha : ENNReal) (ha : 0 < alpha) (haf : alpha < ⊤)
    (hsmall : c53 di dout f A A < alpha) :
    ∃ x ∈ A, ∃ y ∈ A, ∃ eps : ENNReal, 0 < eps ∧ eps < ⊤ ∧
      di x y < alpha ∧ eps ≤ dout (f.func x) (f.func y) := by
  classical
  obtain ⟨y, hy⟩ := iInf_lt_iff.mp hsmall
  obtain ⟨hyA, hyr⟩ := iInf_lt_iff.mp hy
  have hnot : ¬ ∀ x ∈ A, di x y < alpha → dout (f.func x) (f.func y) = 0 := by
    intro h
    have hle := c58 di dout f y A alpha ⟨ha, haf, h⟩
    exact (not_le_of_gt hyr) hle
  push_neg at hnot
  obtain ⟨x, hx, hdist, hz⟩ := hnot
  have hpos : 0 < dout (f.func x) (f.func y) := pos_iff_ne_zero.mpr hz
  obtain ⟨eps, heps, hepslt⟩ := exists_between hpos
  refine ⟨x, hx, y, hyA, eps, heps, ?_, hdist, le_of_lt hepslt⟩
  exact lt_of_lt_of_le hepslt le_top

theorem c68 (d : I → X → X → ENNReal) (f : Operator X bot)
    (A : Set X) (i j : I) (x : X) (hx : x ∈ A)
    (hi : ExtendedPseudoMetric X bot (d i)) (hj : ExtendedPseudoMetric X bot (d j))
    (t : ENNReal) (ht : t ≤ c54 d f A i j) :
    ball (d i) x t ∩ A ⊆ c19 d f j (f.func x) A := by
  intro y hy
  refine ⟨hy.2, ?_⟩
  have hlt : d i x y < c53 (d i) (d j) f A A := by
    rw [hi.symm x y]
    exact lt_of_lt_of_le hy.1 ht
  rw [hj.symm]
  exact c65 (d i) (d j) f A x y hx hy.2 hi.symm hj.symm hlt

theorem c69 (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (i : I) (y : X) (hy : y ∈ U)
    (hd : ExtendedPseudoMetric X bot (d i)) (hi : i ∈ c02 d f U) :
    c19 d f i (f.func y) U = {x | x ∈ U ∧ d i x y = 0} := by
  ext x
  simp only [c19, Set.mem_setOf_eq]
  by_cases hx : x ∈ U
  · simp [hx, c08 d f U i hd hi x hx y hy]
  · simp [hx]

theorem c70 (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (i : I) (y : X) (hy : y ∈ U)
    (hd : ExtendedPseudoMetric X bot (d i)) (hi : i ∈ c02 d f U)
    (r : ENNReal) (hr : 0 < r) (hrfin : r < ⊤)
    (hball : ∀ x ∈ U, d i x y < r → d i x y = 0) :
    r ≤ c52 (d i) (d i) f y U := by
  apply c58
  refine ⟨hr, hrfin, ?_⟩
  intro x hx hdist
  rw [c08 d f U i hd hi x hx y hy]
  exact hball x hx hdist

theorem c71 (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (J : Set I) (y : X) (hy : y ∈ U)
    (hJ : J ⊆ c01 d f U) : c18 d f J (f.func y) U = U := by
  ext x
  simp only [c18, Set.mem_setOf_eq, c20]
  constructor
  · exact And.left
  · intro hx
    exact ⟨hx, fun j hj => hJ hj x hx y hy⟩

theorem c72 (di dout : X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (y : X) (hy : y ∈ U)
    (hc : ∀ x ∈ U, ∀ z ∈ U, dout (f.func x) (f.func z) = 0) :
    c52 di dout f y U = ⊤ := by
  apply top_unique
  by_contra h
  have hl : c52 di dout f y U < ⊤ := lt_of_not_ge h
  obtain ⟨r, hr, hrfin⟩ := exists_between hl
  have hpos : 0 < r := lt_of_le_of_lt (zero_le _) hr
  have hgood : c51 di dout f y U r :=
    ⟨hpos, hrfin, fun x hx _ => hc x hx y hy⟩
  exact (not_le_of_gt hr) (c58 di dout f y U r hgood)

theorem c73 (di dout : X → X → ENNReal)
    (f : Operator X bot) (U : Set X)
    (hc : ∀ x ∈ U, ∀ y ∈ U, dout (f.func x) (f.func y) = 0) :
    c53 di dout f U U = ⊤ := by
  apply top_unique
  apply le_iInf
  intro y
  apply le_iInf
  intro hy
  rw [c72 di dout f U y hy hc]

theorem c74 (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (J : Set I) (i : I) (hJ : J ⊆ c01 d f U) :
    (∀ y ∈ U, c52 (d i) (subfamily_pseudometric d J) f y U = ⊤) ∧
    c53 (d i) (subfamily_pseudometric d J) f U U = ⊤ := by
  have hc : ∀ x ∈ U, ∀ y ∈ U,
      subfamily_pseudometric d J (f.func x) (f.func y) = 0 := by
    intro x hx y hy
    exact (c20 d J _ _).2 (fun j hj => hJ hj x hx y hy)
  exact ⟨fun y hy => c72 _ _ f U y hy hc,
    c73 _ _ f U hc⟩

theorem c75 (di dl dj : X → X → ENNReal)
    (f g : Operator X bot) (U : Set X)
    (hpres : ∀ a ∈ f.func '' U, ∀ b ∈ f.func '' U,
      dl a b = 0 → dj (g.func a) (g.func b) = 0) :
    c53 di dl f U U ≤ c53 di dj (g * f) U U := by
  apply le_iInf
  intro y
  apply le_iInf
  intro hy
  refine (c64 di dl f U U y hy).trans ?_
  apply sSup_le
  intro r hr
  apply le_sSup
  refine ⟨hr.1, hr.2.1, ?_⟩
  intro x hx hxy
  exact hpres (f.func x) ⟨x, hx, rfl⟩ (f.func y) ⟨y, hy, rfl⟩
    (hr.2.2 x hx hxy)

theorem c76 (d : I → X → X → ENNReal) (f : Operator X bot)
    (U A : Set X) (i : I) (J K : Set I) (hJK : J ⊆ K) :
    c53 (d i) (subfamily_pseudometric d K) f A U ≤
      c53 (d i) (subfamily_pseudometric d J) f A U := by
  apply le_iInf
  intro y
  apply le_iInf
  intro hy
  refine (c64 _ _ f A U y hy).trans ?_
  apply sSup_le
  intro r hr
  apply le_sSup
  refine ⟨hr.1, hr.2.1, ?_⟩
  intro x hx hdist
  apply (c20 d J _ _).2
  intro j hj
  exact (c20 d K _ _).1 (hr.2.2 x hx hdist) j (hJK hj)

theorem c77 [Fintype I] (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (i j : I) (K : I → I → ENNReal)
    (hK : IsCoLipMatrix d f U K) (hpos : 0 < K i j)
    (hi : ExtendedPseudoMetric X bot (d i))
    (y x : X) (hy : y ∈ U) (hx : x ∈ U)
    (h : d i y x < c52 (d i) (d j) f y U) : d i x y = 0 := by
  have hz := c60 (d i) (d j) f U y x hx hi.symm h
  exact positive_colip_entry_reflects_zero d f U K i j hK hpos x hx y hy hz

theorem c78 [Fintype I] (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (i j : I) (K : I → I → ENNReal)
    (hK : IsCoLipMatrix d f U K) (hpos : 0 < K i j)
    (hi : ExtendedPseudoMetric X bot (d i))
    (y x : X) (hy : y ∈ U) (hx : x ∈ U) :
    ¬ (0 < d i x y ∧ d i x y < c52 (d i) (d j) f y U) := by
  rintro ⟨hp, hl⟩
  have hz := c77 d f U i j K hK hpos hi y x hy hx (by rwa [hi.symm y x])
  exact (ne_of_gt hp) hz

theorem c79 [Fintype I] (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (i j : I) (K : I → I → ENNReal)
    (hK : IsCoLipMatrix d f U K) (hpos : 0 < K i j)
    (hi : ExtendedPseudoMetric X bot (d i)) (x y : X) (hx : x ∈ U) (hy : y ∈ U) :
    d i x y = 0 ∨ c53 (d i) (d j) f U U ≤ d i x y := by
  by_cases h : c53 (d i) (d j) f U U ≤ d i x y
  · exact Or.inr h
  · left
    have hl : d i x y < c52 (d i) (d j) f x U :=
      (lt_of_not_ge h).trans_le (c64 _ _ f U U x hx)
    have hz := c77 d f U i j K hK hpos hi x y hx hy hl
    rwa [hi.symm x y]

structure c80 (X I : Type) where
  scale : I → Set X → ENNReal
  mono : ∀ i (A B : Set X), A.Nonempty → A ⊆ B → scale i A ≤ scale i B

noncomputable def c81 (d : X → X → ENNReal) (A : Set X) : ENNReal :=
  ⨆ x ∈ A, ⨆ y ∈ A, d x y

theorem c82 (d : X → X → ENNReal) (A B : Set X) (h : A ⊆ B) :
    c81 d A ≤ c81 d B := by
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

noncomputable def c83 (d : I → X → X → ENNReal) : c80 X I where
  scale i A := c81 (d i) A
  mono i A B _ h := c82 (d i) A B h

theorem c84 (d : X → X → ENNReal) (A : Set X) (x y : X)
    (hx : x ∈ A) (hy : y ∈ A) : d x y ≤ c81 d A :=
  le_iSup_of_le x (le_iSup_of_le hx (le_iSup_of_le y (le_iSup_of_le hy le_rfl)))

theorem c85 (di dout : X → X → ENNReal) (f : Operator X bot)
    (A : Set X) (ts tn : ENNReal)
    (hi : ∀ x y, di x y = di y x) (ho : ∀ x y, dout x y = dout y x)
    (hsmall : c81 di A < ts) (ht : ts ≤ tn) :
    tn ≤ c53 di dout f A A ↔
      ∀ x ∈ A, ∀ y ∈ A, dout (f.func x) (f.func y) = 0 := by
  constructor
  · intro hn x hx y hy
    apply c65 di dout f A x y hx hy hi ho
    exact lt_of_le_of_lt (c84 di A x y hx hy)
      (lt_of_lt_of_le hsmall (ht.trans hn))
  · intro hc
    rw [c73 di dout f A hc]
    exact le_top

theorem c86 (d : X → X → ENNReal) (f : Operator X bot)
    (A : Set X) (hA : A.Nonempty) (eps : ENNReal) (heps : 0 < eps)
    (hc : ∀ x ∈ A, ∀ y ∈ A, d (f.func x) (f.func y) = 0) :
    covering_number d eps (f.func '' A) = 1 := by
  classical
  obtain ⟨x, hx⟩ := hA
  apply le_antisymm
  · have hn : InternalEpsilonNet d eps (f.func '' A) {f.func x} := by
      constructor
      · intro y hy
        simp only [Finset.mem_coe, Finset.mem_singleton] at hy
        rw [hy]
        exact ⟨x, hx, rfl⟩
      · rintro y ⟨z, hz, rfl⟩
        exact ⟨f.func x, Finset.mem_singleton_self _, by simpa [hc z hz x hx] using heps⟩
    have h : covering_number d eps (f.func '' A) ≤
        ((({f.func x} : Finset X).card : ℕ) : ENNReal) :=
      iInf_le_of_le ({f.func x} : Finset X) (iInf_le_of_le hn le_rfl)
    simpa using h
  · exact one_le_covering_number_of_nonempty d eps (f.func '' A) ⟨f.func x, x, hx, rfl⟩

noncomputable def c87 (s : c80 X I) (d : I → X → X → ENNReal)
    (f : Operator X bot) (A : Set X) (ts tn : ENNReal) (i j : I) : Bool × Bool := by
  classical
  exact (decide (s.scale i A < ts), decide (tn ≤ c54 d f A i j))

theorem c88 (s : c80 X I) (d : I → X → X → ENNReal)
    (f : Operator X bot) (A : Set X) (ts tn : ENNReal) (i j : I) :
    c87 s d f A ts tn i j = (true, true) ∨
    c87 s d f A ts tn i j = (true, false) ∨
    c87 s d f A ts tn i j = (false, true) ∨
    c87 s d f A ts tn i j = (false, false) := by
  cases h : c87 s d f A ts tn i j with
  | mk a b => cases a <;> cases b <;> simp_all

theorem c89 (s : c80 X I) (d : I → X → X → ENNReal)
    (f : Operator X bot) (A : Set X) (ts tn : ENNReal) (i j : I) :
    (c87 s d f A ts tn i j = (true, true) ↔
      s.scale i A < ts ∧ tn ≤ c54 d f A i j) ∧
    (c87 s d f A ts tn i j = (true, false) ↔
      s.scale i A < ts ∧ c54 d f A i j < tn) ∧
    (c87 s d f A ts tn i j = (false, true) ↔
      ts ≤ s.scale i A ∧ tn ≤ c54 d f A i j) ∧
    (c87 s d f A ts tn i j = (false, false) ↔
      ts ≤ s.scale i A ∧ c54 d f A i j < tn) := by
  classical
  simp [c87, not_lt, not_le]

theorem c90 (s : c80 X I) (A : Set X) (i : I)
    (t t' : ENNReal) (h : t ≤ t') : s.scale i A < t → s.scale i A < t' :=
  fun hs => lt_of_lt_of_le hs h

theorem c91 (r t t' : ENNReal) (h : t ≤ t') : t' ≤ r → t ≤ r :=
  fun hr => h.trans hr

theorem c92 (s : c80 X I) (A B : Set X) (i : I)
    (hB : B.Nonempty) (hBA : B ⊆ A) (t : ENNReal) :
    s.scale i B ≤ s.scale i A ∧ (s.scale i A < t → s.scale i B < t) := by
  exact ⟨s.mono i B A hB hBA, fun ht => lt_of_le_of_lt (s.mono i B A hB hBA) ht⟩

def c93 (d : X → X → ENNReal) (U : Set X) : Prop :=
  ∀ r : ENNReal, 0 < r → r < ⊤ → covering_number d r U < ⊤

theorem c94 (d : X → X → ENNReal) (U : Set X) (r : ENNReal)
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

def c95 (d : I → X → X → ENNReal) (f : Operator X bot) (U : Set X)
    (Jin Jout : Set I) (eps : ENNReal) : Prop :=
  U.Nonempty ∧ U ⊆ dom f ∧ Jin.Nonempty ∧ Jout.Nonempty ∧ 0 < eps ∧ eps < ⊤ ∧
  (covering_number (subfamily_pseudometric d Jin) eps U < ⊤ ∨
   covering_number (subfamily_pseudometric d Jout) eps (f.func '' U) < ⊤)

noncomputable def c96 (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (Jin Jout : Set I) (eps : ENNReal)
    (_ : c95 d f U Jin Jout eps) : EReal :=
  subfamily_metric_entropy d Jin eps U -
    subfamily_metric_entropy d Jout eps (f.func '' U)

end C3
