import formal_oet.vol_01.ch_02_operator_bounds.decoupling

open formal_oet.vol_01.ch_01_foundations formal_oet.vol_01.ch_02_operator_bounds
open scoped ENNReal
namespace Chapter

variable {X I : Type} {bot : X} {d : I → X → X → ℝ≥0∞}
variable {f g : Operator X bot} {U : Set X} {i j : I}

def Const (d : I → X → X → ℝ≥0∞) (f : Operator X bot) (U : Set X) : Set I :=
  {i | ∀ x ∈ U, ∀ y ∈ U, d i (f.func x) (f.func y) = 0}

def Ident (d : I → X → X → ℝ≥0∞) (f : Operator X bot) (U : Set X) : Set I :=
  {i | i ∉ Const d f U ∧ ∀ x ∈ U, d i (f.func x) x = 0}

def Active (d : I → X → X → ℝ≥0∞) (f : Operator X bot) (U : Set X) : Set I :=
  (Const d f U ∪ Ident d f U)ᶜ

theorem partition (_hU : U ⊆ dom f) :
    Const d f U ∪ Ident d f U ∪ Active d f U = Set.univ ∧
    Disjoint (Const d f U) (Ident d f U) ∧
    Disjoint (Const d f U) (Active d f U) ∧
    Disjoint (Ident d f U) (Active d f U) := by
  classical
  refine ⟨Set.union_compl_self _, ?_, ?_, ?_⟩
  · exact Set.disjoint_left.mpr fun _ hc hi => hi.1 hc
  · exact Set.disjoint_left.mpr fun _ hc ha => ha (Or.inl hc)
  · exact Set.disjoint_left.mpr fun _ hi ha => ha (Or.inr hi)

theorem const_zero_row [Fintype I] (_hU : U ⊆ dom f) (hc : i ∈ Const d f U) :
    ∀ x ∈ U, ∀ y ∈ U,
      d i (f.func x) (f.func y) ≤ ∑ k : I, 0 * d k x y := by
  intro x hx y hy
  simp [hc x hx y hy]

theorem const_colip [Fintype I] {K : I → I → ℝ≥0∞}
    (hc : i ∈ Const d f U) (hK : IsCoLipMatrix d f U K)
    (hp : ∃ x ∈ U, ∃ y ∈ U, 0 < d j x y) : K j i = 0 := by
  obtain ⟨x, hx, y, hy, h⟩ := hp
  exact colip_entry_eq_zero_of_output_zero_input_pos d f U K j i x y hK hx hy (hc x hx y hy) h

theorem zero_left {D : X → X → ℝ≥0∞} (hD : ExtendedPseudoMetric X bot D)
    {a b : X} (h : D a b = 0) (c : X) : D a c = D b c := by
  have p := hD.triangle a b c
  have q := hD.triangle b a c
  rw [h, zero_add] at p
  rw [hD.symm b a, h, zero_add] at q
  exact le_antisymm p q

theorem ident_distance (hd : ExtendedPseudoMetric X bot (d i))
    (_hU : U ⊆ dom f) (hi : i ∈ Ident d f U) :
    ∀ x ∈ U, ∀ y ∈ U, d i (f.func x) (f.func y) = d i x y := by
  intro x hx y hy
  rw [zero_left hd (hi.2 x hx), hd.symm x, zero_left hd (hi.2 y hy), hd.symm y]

@[simp] theorem mul_func (f g : Operator X bot) (x : X) :
    (g * f).func x = g.func (f.func x) := rfl

theorem stage_domains (hU : U ⊆ dom (g * f)) :
    U ⊆ dom f ∧ f.func '' U ⊆ dom g := by
  constructor
  · intro x hx h
    exact hU hx (show g.func (f.func x) = bot by rw [h, g.preserves_bot])
  · rintro _ ⟨x, hx, rfl⟩
    exact hU hx

theorem outer_const (_hU : U ⊆ dom (g * f)) (hc : i ∈ Const d g (f.func '' U)) :
    i ∈ Const d (g * f) U :=
  fun x hx y hy => hc _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩

theorem ident_comp (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (hU : U ⊆ dom (g * f)) :
    Ident d f U ∩ Ident d g (f.func '' U) ⊆ Ident d (g * f) U := by
  rintro i ⟨hf, hg⟩
  have himg (x : X) (hx : x ∈ U) : f.func x ∈ f.func '' U := ⟨x, hx, rfl⟩
  refine ⟨fun hc => hf.1 ?_, ?_⟩
  · intro x hx y hy
    rw [← ident_distance (hd i) (stage_domains hU).2 hg _ (himg x hx) _ (himg y hy)]
    exact hc x hx y hy
  · intro x hx
    exact (zero_left (hd i) (hg.2 _ (himg x hx)) x).trans (hf.2 x hx)

theorem active_comp (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (hU : U ⊆ dom (g * f)) :
    Active d (g * f) U ⊆ Active d f U ∪ Active d g (f.func '' U) := by
  classical
  intro i ha
  by_contra h
  have hf : i ∈ Const d f U ∨ i ∈ Ident d f U := by
    by_contra hh
    exact h (Or.inl hh)
  have hg : i ∈ Const d g (f.func '' U) ∨ i ∈ Ident d g (f.func '' U) := by
    by_contra hh
    exact h (Or.inr hh)
  rcases hg with hg | hg
  · exact ha (Or.inl (outer_const hU hg))
  · rcases hf with hf | hf
    · apply ha
      left
      intro x hx y hy
      exact (ident_distance (hd i) (stage_domains hU).2 hg _ ⟨x, hx, rfl⟩
        _ ⟨y, hy, rfl⟩).trans (hf x hx y hy)
    · exact ha (Or.inr (ident_comp hd hU ⟨hf, hg⟩))

def chain : List (Operator X bot) → Operator X bot
  | [] => 1
  | f :: tail => chain tail * f

def stepActive (d : I → X → X → ℝ≥0∞) :
    List (Operator X bot) → Set X → Set I
  | [], _ => ∅
  | f :: tail, U => Active d f U ∪ stepActive d tail (f.func '' U)

theorem chain_representation (fs : List (Operator X bot)) :
    chain fs = OperatorChain fs.reverse := by
  rw [operator_chain_eq_prod]
  induction fs with
  | nil => rfl
  | cons f fs ih => simp [chain, ih, List.reverse_cons, List.prod_append]

theorem chain_active (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (fs : List (Operator X bot)) (U : Set X) (hU : U ⊆ dom (chain fs)) :
    Active d (chain fs) U ⊆ stepActive d fs U := by
  classical
  induction fs generalizing U with
  | nil =>
    intro i ha
    by_cases hc : i ∈ Const d (chain ([] : List (Operator X bot))) U
    · exact False.elim (ha (Or.inl hc))
    · exact False.elim (ha (Or.inr ⟨hc, fun x _ => (hd i).dist_self x⟩))
  | cons f fs ih =>
    intro i hi
    rcases active_comp hd hU hi with h | h
    · exact Or.inl h
    · exact Or.inr (ih _ (stage_domains hU).2 h)

theorem inner_const_of_row [Fintype I] {L : I → I → ℝ≥0∞}
    (_hU : U ⊆ dom (g * f)) (hc : j ∈ Const d f U)
    (hL : IsLipMatrix d g (f.func '' U) L) (hrow : ∀ k, k ≠ j → L k j = 0) :
    j ∈ Const d (g * f) U := by
  intro x hx y hy
  have h := lip_bound_of_single_input_row d g (f.func '' U) L j j hL hrow
    _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  rw [hc x hx y hy, mul_zero] at h
  exact nonpos_iff_eq_zero.mp h

end Chapter
