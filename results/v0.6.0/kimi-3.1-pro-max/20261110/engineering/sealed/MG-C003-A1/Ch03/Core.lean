import Ch03.Defs

namespace OET.Ch03

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set

variable {X I : Type} {bot : X}

section ComponentBounds

variable [Fintype I] (d : I → X → X → ENNReal)

/-- Proposition 3.1(i): a constant component admits the zero Lip row. -/
theorem constComponent_zero_row (φ : Operator X bot) (U : Set X) {i : I}
    (hi : i ∈ constComponents d φ U) :
    ∀ x ∈ U, ∀ y ∈ U,
      d i (φ.func x) (φ.func y) ≤ ∑ k : I, (0 : ENNReal) * d k x y := by
  intro x hx y hy
  simp [hi x hx y hy]

/-- Proposition 3.1(ii): positive input separation forces the corresponding
co-Lip entry in a constant output column to vanish. -/
theorem constComponent_colip_entry_eq_zero (φ : Operator X bot) (U : Set X)
    (K : I → I → ENNReal) (hK : IsCoLipMatrix d φ U K) {i k : I}
    (hi : i ∈ constComponents d φ U)
    (h : ∃ x ∈ U, ∃ y ∈ U, 0 < d k x y) : K k i = 0 := by
  obtain ⟨x, hx, y, hy, hxy⟩ := h
  exact colip_entry_eq_zero_of_output_zero_input_pos d φ U K k i x y hK hx hy
    (hi x hx y hy) hxy

/-- Proposition 3.1(iii): identity components preserve pairwise distances. -/
theorem idComponent_dist_eq (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (U : Set X) {i : I} (hi : i ∈ idComponents d φ U) :
    ∀ x ∈ U, ∀ y ∈ U, d i (φ.func x) (φ.func y) = d i x y := by
  intro x hx y hy
  apply le_antisymm
  · calc
      d i (φ.func x) (φ.func y) ≤ d i (φ.func x) x + d i x (φ.func y) :=
        (hd i).triangle _ _ _
      _ ≤ d i (φ.func x) x + (d i x y + d i y (φ.func y)) :=
        add_le_add le_rfl ((hd i).triangle _ _ _)
      _ = d i x y := by rw [hi.2 x hx, (hd i).symm y (φ.func y), hi.2 y hy]; simp
  · calc
      d i x y ≤ d i x (φ.func x) + d i (φ.func x) y := (hd i).triangle _ _ _
      _ ≤ d i x (φ.func x) + (d i (φ.func x) (φ.func y) + d i (φ.func y) y) :=
        add_le_add le_rfl ((hd i).triangle _ _ _)
      _ = d i (φ.func x) (φ.func y) := by
        rw [(hd i).symm x (φ.func x), hi.2 x hx, hi.2 y hy]
        simp

end ComponentBounds

section Composition

variable [Fintype I] (d : I → X → X → ENNReal)

private lemma not_act_iff_const_or_id {φ : Operator X bot} {U : Set X} {i : I} :
    i ∉ actComponents d φ U ↔ i ∈ constComponents d φ U ∨ i ∈ idComponents d φ U := by
  simp only [mem_actComponents, not_and_or, not_not]


private lemma composite_const_of_left_const {φ ψ : Operator X bot} {U : Set X} {i : I}
    (h : i ∈ constComponents d ψ (φ.func '' U)) :
    i ∈ constComponents d (operator_compose ψ φ) U := by
  intro x hx y hy
  exact h (φ.func x) ⟨x, hx, rfl⟩ (φ.func y) ⟨y, hy, rfl⟩

private lemma composite_const_of_right_const
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    {φ ψ : Operator X bot} {U : Set X} {i : I}
    (hφ : i ∈ constComponents d φ U)
    (hψ : i ∈ idComponents d ψ (φ.func '' U) ∨ i ∈ constComponents d ψ (φ.func '' U)) :
    i ∈ constComponents d (operator_compose ψ φ) U := by
  cases hψ with
  | inr h => exact composite_const_of_left_const d h
  | inl h =>
      intro x hx y hy
      have heq := idComponent_dist_eq d hd ψ (φ.func '' U) h
        (φ.func x) ⟨x, hx, rfl⟩ (φ.func y) ⟨y, hy, rfl⟩
      rw [show (operator_compose ψ φ).func x = ψ.func (φ.func x) from rfl,
        show (operator_compose ψ φ).func y = ψ.func (φ.func y) from rfl, heq]
      exact hφ x hx y hy

private lemma composite_id_of_id
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    {φ ψ : Operator X bot} {U : Set X} {i : I}
    (hφ : i ∈ idComponents d φ U) (hψ : i ∈ idComponents d ψ (φ.func '' U)) :
    i ∈ idComponents d (operator_compose ψ φ) U := by
  constructor
  · intro hc
    apply hφ.1
    intro x hx y hy
    have h1 := idComponent_dist_eq d hd φ U hφ x hx y hy
    have h2 := idComponent_dist_eq d hd ψ (φ.func '' U) hψ
      (φ.func x) ⟨x, hx, rfl⟩ (φ.func y) ⟨y, hy, rfl⟩
    rw [← h2]
    exact hc x hx y hy
  · intro x hx
    apply le_antisymm _ (zero_le _)
    calc
      d i ((operator_compose ψ φ).func x) x ≤
          d i (ψ.func (φ.func x)) (φ.func x) + d i (φ.func x) x :=
        (hd i).triangle _ _ _
      _ = 0 := by rw [hψ.2 (φ.func x) ⟨x, hx, rfl⟩, hφ.2 x hx, add_zero]

/-- Proposition 3.2(i), with the actual intermediate image domain. -/
theorem actComponents_compose_subset
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (φ ψ : Operator X bot) (U : Set X) :
    actComponents d (operator_compose ψ φ) U ⊆
      actComponents d φ U ∪ actComponents d ψ (φ.func '' U) := by
  intro i hi
  by_contra hnot
  have h1 : i ∉ actComponents d φ U := by
    intro h; exact hnot (Or.inl h)
  have h2 : i ∉ actComponents d ψ (φ.func '' U) := by
    intro h; exact hnot (Or.inr h)
  have hc1 := (not_act_iff_const_or_id d).mp h1
  have hc2 := (not_act_iff_const_or_id d).mp h2
  have hor : i ∈ constComponents d (operator_compose ψ φ) U ∨
      i ∈ idComponents d (operator_compose ψ φ) U := by
    cases hc1 with
    | inl hc =>
        exact Or.inl (composite_const_of_right_const d hd hc hc2.symm)
    | inr hid =>
        cases hc2 with
        | inl hc => exact Or.inl (composite_const_of_left_const d hc)
        | inr hid2 => exact Or.inr (composite_id_of_id d hd hid hid2)
  exact (not_act_iff_const_or_id d).mpr hor hi

/-- Proposition 3.2(iii), including the constant-priority exclusion. -/
theorem idComponents_inter_compose_subset
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (φ ψ : Operator X bot) (U : Set X) :
    idComponents d φ U ∩ idComponents d ψ (φ.func '' U) ⊆
      idComponents d (operator_compose ψ φ) U := by
  rintro i ⟨h1, h2⟩
  exact composite_id_of_id d hd h1 h2

private lemma chain_image
    (φ c : ℕ → Operator X bot) (U : ℕ → Set X)
    (hc0 : c 0 = operator_identity)
    (hcsucc : ∀ n, c (n+1) = operator_compose (φ n) (c n))
    (hU : ∀ m, U (m+1) = (φ m).func '' U m) :
    ∀ n, (c n).func '' U 0 = U n := by
  intro n
  induction n with
  | zero => simp [hc0, operator_identity]
  | succ n ih =>
      rw [hU n, ← ih, hcsucc n]
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨(c n).func x, ⟨x, hx, rfl⟩, rfl⟩
      · rintro ⟨w, hw, rfl⟩
        obtain ⟨x, hx, rfl⟩ := hw
        exact ⟨x, hx, rfl⟩

/-- Proposition 3.2(ii): arbitrary finite chains, including the empty chain.
`U 0` is the initial domain and `U (m+1) = φ m '' U m` is the actual domain
used at the next step. -/
theorem actComponents_finite_chain
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (φ c : ℕ → Operator X bot) (U : ℕ → Set X)
    (hc0 : c 0 = operator_identity)
    (hcsucc : ∀ n, c (n+1) = operator_compose (φ n) (c n))
    (hU : ∀ m, U (m+1) = (φ m).func '' U m) :
    ∀ n, U 0 ⊆ dom (c n) →
      actComponents d (c n) (U 0) ⊆ ⋃ m : Fin n, actComponents d (φ m.1) (U m.1) := by
  intro n
  induction n with
  | zero =>
      intro hdom i hi
      exfalso
      have hor : i ∈ constComponents d (c 0) (U 0) ∨ i ∈ idComponents d (c 0) (U 0) := by
        by_cases hc : i ∈ constComponents d (c 0) (U 0)
        · exact Or.inl hc
        · right
          refine ⟨hc, ?_⟩
          intro x hx
          rw [hc0]
          exact (hd i).dist_self x
      exact (not_act_iff_const_or_id d).mpr hor hi
  | succ n ih =>
      intro hdom
      have hdomprev : U 0 ⊆ dom (c n) := by
        intro x hx hzero
        have hcomp := hdom hx
        rw [hcsucc n] at hcomp
        exact hcomp (by change (φ n).func ((c n).func x) = bot; rw [hzero]; exact (φ n).preserves_bot)
      have himage : (c n).func '' U 0 = U n := chain_image φ c U hc0 hcsucc hU n
      rw [hcsucc n]
      intro i hi
      have hi' := actComponents_compose_subset d hd (c n) (φ n) (U 0) hi
      cases hi' with
      | inl h =>
          have hmem := ih hdomprev h
          simp only [mem_iUnion] at hmem ⊢
          obtain ⟨m, hm⟩ := hmem
          exact ⟨Fin.castSucc m, hm⟩
      | inr h =>
          rw [himage] at h
          simp only [mem_iUnion]
          exact ⟨Fin.last n, h⟩

/-- Proposition 3.3(i): outer constancy on the actual image is preserved. -/
theorem constComponents_compose_of_outer
    (φ ψ : Operator X bot) (U : Set X) :
    constComponents d ψ (φ.func '' U) ⊆ constComponents d (operator_compose ψ φ) U := by
  intro i hi
  exact composite_const_of_left_const d hi

/-- Corollary 3.4: a single-input Lip row propagates inner constancy. -/
theorem constComponents_compose_of_single_input_lip
    (φ ψ : Operator X bot) (U : Set X) (L : I → I → ENNReal) (j : I)
    (hL : IsLipMatrix d ψ (φ.func '' U) L)
    (hrow : ∀ k, k ≠ j → L k j = 0)
    (hj : j ∈ constComponents d φ U) :
    j ∈ constComponents d (operator_compose ψ φ) U := by
  intro x hx y hy
  apply le_antisymm _ (zero_le _)
  have h := lip_bound_of_single_input_row d ψ (φ.func '' U) L j j hL hrow
    (φ.func x) ⟨x, hx, rfl⟩ (φ.func y) ⟨y, hy, rfl⟩
  exact h.trans (by rw [hj x hx y hy, mul_zero])

end Composition

section Fibres

variable (d : I → X → X → ENNReal)

/-- Proposition 3.5(i). -/
theorem fib_target_zero_eq (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (J : Set I) {y y' : X}
    (hyy : subfamily_pseudometric d J y y' = 0) (U : Set X) :
    Fib d φ J y U = Fib d φ J y' U := by
  have hcomp : ∀ j ∈ J, d j y y' = 0 := subfamily_zero_iff.mp hyy
  ext x
  constructor
  · rintro ⟨hx, hxzero⟩
    refine ⟨hx, subfamily_zero_iff.mpr ?_⟩
    intro j hj
    have h1 : d j (φ.func x) y = 0 := subfamily_zero_iff.mp hxzero j hj
    apply le_antisymm _ (zero_le _)
    calc
      d j (φ.func x) y' ≤ d j (φ.func x) y + d j y y' := (hd j).triangle _ _ _
      _ = 0 := by rw [h1, hcomp j hj, add_zero]
  · rintro ⟨hx, hxzero⟩
    refine ⟨hx, subfamily_zero_iff.mpr ?_⟩
    intro j hj
    have h1 : d j (φ.func x) y' = 0 := subfamily_zero_iff.mp hxzero j hj
    apply le_antisymm _ (zero_le _)
    calc
      d j (φ.func x) y ≤ d j (φ.func x) y' + d j y' y := (hd j).triangle _ _ _
      _ = 0 := by rw [h1, (hd j).symm y' y, hcomp j hj, add_zero]

/-- Proposition 3.5(ii-a). -/
theorem image_fibres_nonempty_cover (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (J : Set I) (U : Set X) :
    (∀ y ∈ φ.func '' U, (Fib d φ J y U).Nonempty) ∧
      U ⊆ ⋃ y ∈ φ.func '' U, Fib d φ J y U := by
  constructor
  · rintro y ⟨x, hx, rfl⟩
    refine ⟨x, hx, subfamily_zero_iff.mpr ?_⟩
    intro j hj
    exact (hd j).dist_self _
  · intro x hx
    simp only [mem_iUnion]
    refine ⟨φ.func x, ?_⟩
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    exact ⟨hx, subfamily_zero_iff.mpr (fun j hj => (hd j).dist_self _)⟩

/-- Proposition 3.5(ii-b): two image-target fibres are equal or disjoint. -/
theorem image_fibres_eq_or_disjoint (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (J : Set I) (U : Set X)
    {y₁ y₂ : X} (hy₁ : y₁ ∈ φ.func '' U) (hy₂ : y₂ ∈ φ.func '' U) :
    Fib d φ J y₁ U = Fib d φ J y₂ U ∨ Disjoint (Fib d φ J y₁ U) (Fib d φ J y₂ U) := by
  by_cases h : (Fib d φ J y₁ U ∩ Fib d φ J y₂ U).Nonempty
  · left
    obtain ⟨x, hx1, hx2⟩ := h
    apply fib_target_zero_eq d hd φ J (y := y₁) (y' := y₂) _ U
    apply subfamily_zero_iff.mpr
    intro j hj
    have h1 := subfamily_zero_iff.mp hx1.2 j hj
    have h2 := subfamily_zero_iff.mp hx2.2 j hj
    apply le_antisymm _ (zero_le _)
    calc
      d j y₁ y₂ ≤ d j y₁ (φ.func x) + d j (φ.func x) y₂ := (hd j).triangle _ _ _
      _ = 0 := by rw [(hd j).symm y₁ (φ.func x), h1, h2, add_zero]
  · right
    rw [Set.not_nonempty_iff_eq_empty] at h
    exact disjoint_iff_inter_eq_empty.mpr h

/-- Proposition 3.5(iii). -/
theorem fib_eq_iInter (φ : Operator X bot) (J : Set I) (hJ : J.Nonempty) (y : X) (U : Set X) :
    Fib d φ J y U = ⋂ j ∈ J, FibSingle d φ j y U := by
  ext x
  constructor
  · rintro ⟨hx, hzero⟩
    simp only [mem_iInter]
    intro j
    intro hj
    exact ⟨hx, subfamily_zero_iff.mp hzero j hj⟩
  · intro h
    obtain ⟨j₀, hj₀⟩ := hJ
    have hx : x ∈ U := ((mem_iInter.mp (mem_iInter.mp h j₀) hj₀)).1
    refine ⟨hx, subfamily_zero_iff.mpr ?_⟩
    intro j hj
    exact ((mem_iInter.mp (mem_iInter.mp h j) hj)).2

/-- Proposition 3.5(iv). -/
theorem fib_antitone (φ : Operator X bot) {J K : Set I} (hJK : J ⊆ K)
    (y : X) (U : Set X) : Fib d φ K y U ⊆ Fib d φ J y U := by
  intro x hx
  refine ⟨hx.1, subfamily_zero_iff.mpr ?_⟩
  intro j hj
  exact subfamily_zero_iff.mp hx.2 j (hJK hj)

/-- Proposition 3.5(v). -/
theorem fib_singleton_and_full (φ : Operator X bot) (i : I) (y : X) (U : Set X) :
    Fib d φ ({i} : Set I) y U = FibSingle d φ i y U ∧
      Fib d φ Set.univ y U ⊆ FibSingle d φ i y U := by
  constructor
  · exact fib_eq_single d φ i y U
  · intro x hx
    refine ⟨hx.1, ?_⟩
    exact subfamily_zero_iff.mp hx.2 i (mem_univ i)

/-- Proposition 3.5(vi-a), for an arbitrary target. -/
theorem fib_idComponent (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) {j : I} (hj : j ∈ idComponents d φ U) (y : X) :
    FibSingle d φ j y U = {x | x ∈ U ∧ d j x y = 0} := by
  ext x
  constructor
  · rintro ⟨hx, hzero⟩
    refine ⟨hx, le_antisymm ?_ (zero_le _)⟩
    calc
      d j x y ≤ d j x (φ.func x) + d j (φ.func x) y := (hd j).triangle _ _ _
      _ = 0 := by rw [(hd j).symm x (φ.func x), hj.2 x hx, hzero, zero_add]
  · rintro ⟨hx, hzero⟩
    refine ⟨hx, le_antisymm ?_ (zero_le _)⟩
    calc
      d j (φ.func x) y ≤ d j (φ.func x) x + d j x y := (hd j).triangle _ _ _
      _ = 0 := by rw [hj.2 x hx, hzero, zero_add]

/-- Proposition 3.5(vi-b). -/
theorem fib_constComponent (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) {j : I} (hj : j ∈ constComponents d φ U)
    {y₀ : X} (hy₀ : y₀ ∈ φ.func '' U) (y : X) :
    FibSingle d φ j y₀ U = U ∧
      (0 < d j y y₀ → FibSingle d φ j y U = ∅) := by
  obtain ⟨z, hz, rfl⟩ := hy₀
  constructor
  · ext x
    constructor
    · intro hx; exact hx.1
    · intro hx
      refine ⟨hx, le_antisymm ?_ (zero_le _)⟩
      calc
        d j (φ.func x) (φ.func z) = 0 := hj x hx z hz
        _ ≤ 0 := le_rfl
  · intro hpos
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro x ⟨hx, hzero⟩
    have hconst : d j (φ.func x) (φ.func z) = 0 := hj x hx z hz
    have : d j y (φ.func z) = 0 := by
      apply le_antisymm _ (zero_le _)
      calc
        d j y (φ.func z) ≤ d j y (φ.func x) + d j (φ.func x) (φ.func z) :=
          (hd j).triangle _ _ _
        _ = 0 := by rw [(hd j).symm y (φ.func x), hzero, hconst, add_zero]
    exact (ne_of_gt hpos) this

end Fibres

section Preorder

variable (d : I → X → X → ENNReal)

theorem fiberGe_refl (φ : Operator X bot) (U : Set X) : FiberGe d φ φ U := Subset.rfl

theorem fiberGe_trans {φ ψ χ : Operator X bot} {U : Set X}
    (h1 : FiberGe d φ ψ U) (h2 : FiberGe d ψ χ U) : FiberGe d φ χ U := h1.trans h2

/-- Every two comparable layers of a finite fibre chain are related. -/
theorem fiberGe_chain {φ : ℕ → Operator X bot} {U : Set X}
    (hstep : ∀ r, FiberGe d (φ r) (φ (r+1)) U) {a b : ℕ} (hab : a ≤ b) :
    FiberGe d (φ a) (φ b) U := by
  induction b, hab using Nat.le_induction with
  | base => exact fiberGe_refl d (φ a) U
  | succ b hab ih => exact fiberGe_trans d ih (hstep b)


/-- Packaged strictness with an explicit difference witness. -/
theorem zeroRel_strict_endpoint_witness {φ : ℕ → Operator X bot} {U : Set X}
    (hstep : ∀ r, FiberGe d (φ r) (φ (r+1)) U) (m : ℕ)
    {r : ℕ} (hr : r < m) (p : X × X)
    (hp : p ∈ zeroRel d (φ (r+1)) U \ zeroRel d (φ r) U) :
    p ∈ zeroRel d (φ m) U \ zeroRel d (φ 0) U := by
  constructor
  · have h1 : zeroRel d (φ (r+1)) U ⊆ zeroRel d (φ m) U :=
      fiberGe_chain d hstep hr
    exact h1 hp.1
  · intro hp0
    have h0r : zeroRel d (φ 0) U ⊆ zeroRel d (φ r) U :=
      fiberGe_chain d hstep (Nat.zero_le r)
    exact hp.2 (h0r hp0)

theorem zeroRel_ssubset_endpoint {φ : ℕ → Operator X bot} {U : Set X}
    (hstep : ∀ r, FiberGe d (φ r) (φ (r+1)) U) (m : ℕ)
    {r : ℕ} (hr : r < m) (hstrict : zeroRel d (φ r) U ⊂ zeroRel d (φ (r+1)) U) :
    zeroRel d (φ 0) U ⊂ zeroRel d (φ m) U := by
  obtain ⟨p, hp⟩ := Set.exists_of_ssubset hstrict
  exact Set.ssubset_iff_of_subset (fiberGe_chain d hstep (Nat.zero_le m)) |>.mpr
    ⟨p, (zeroRel_strict_endpoint_witness d hstep m hr p hp).1,
      (zeroRel_strict_endpoint_witness d hstep m hr p hp).2⟩

end Preorder

end OET.Ch03
