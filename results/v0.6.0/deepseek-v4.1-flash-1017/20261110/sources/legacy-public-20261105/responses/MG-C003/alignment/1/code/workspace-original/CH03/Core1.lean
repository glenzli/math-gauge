import CH03.Basic

namespace formal_oet.vol_01.ch_03_operator_local_degeneracy
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set

variable {X : Type} {I : Type} {bot : X}

/-! ## Proposition 3.1 -/

theorem const_component_zero_row_bound [Fintype I]
    (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) (i : I)
    (hi : i ∈ Iconst d φ U) :
    ∀ x ∈ U, ∀ y ∈ U,
      d i (φ.func x) (φ.func y) ≤ ∑ k : I, (0 : ENNReal) * d k x y := by
  intro x hx y hy
  rw [hi x hx y hy]
  simp

theorem const_component_colip_entry_zero
    [Fintype I] (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X)
    (K : I → I → ENNReal) (i k : I)
    (hK : IsCoLipMatrix d φ U K) (hi : i ∈ Iconst d φ U)
    (hpos : ∃ x ∈ U, ∃ y ∈ U, 0 < d k x y) :
    K k i = 0 := by
  rcases hpos with ⟨x, hx, y, hy, hxy⟩
  have hconst : d i (φ.func x) (φ.func y) = 0 := hi x hx y hy
  have hineq := hK.2.2 x hx y hy i
  rw [hconst] at hineq
  have hsingle :
      K k i * d k x y ≤ ∑ l : I, K l i * d l x y := by
    exact Finset.single_le_sum (fun l _ => (zero_le (K l i * d l x y) : (0 : ENNReal) ≤ _)) (Finset.mem_univ k)
  have hterm : K k i * d k x y = 0 :=
    le_antisymm (le_trans hsingle hineq) (zero_le (K k i * d k x y))
  rcases mul_eq_zero.mp hterm with h | h
  · exact h
  · exact False.elim ((ne_of_gt hxy) h)

theorem id_component_isometry
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (U : Set X) (i : I) (hi : i ∈ Iid d φ U) :
    ∀ x ∈ U, ∀ y ∈ U, d i (φ.func x) (φ.func y) = d i x y := by
  rcases hi with ⟨_, hzero⟩
  intro x hx y hy
  apply le_antisymm
  · calc
      d i (φ.func x) (φ.func y)
          ≤ d i (φ.func x) x + d i x (φ.func y) := (hd i).triangle _ _ _
      _ ≤ d i (φ.func x) x + (d i x y + d i y (φ.func y)) := by
        gcongr
        exact (hd i).triangle _ _ _
      _ = d i x y := by
        rw [hzero x hx, ← (hd i).symm (φ.func y) y, hzero y hy]
        simp
  · calc
      d i x y
          ≤ d i x (φ.func x) + d i (φ.func x) y := (hd i).triangle _ _ _
      _ ≤ d i x (φ.func x) + (d i (φ.func x) (φ.func y) + d i (φ.func y) y) := by
        gcongr
        exact (hd i).triangle _ _ _
      _ = d i (φ.func x) (φ.func y) := by
        rw [← (hd i).symm (φ.func x) x, hzero x hx, hzero y hy]
        simp

/-! ## Proposition 3.2 -/

theorem active_composite_of_not_active_steps
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ1 φ2 : Operator X bot) (U : Set X) (i : I)
    (h1 : i ∉ Iact d φ1 U) (h2 : i ∉ Iact d φ2 (φ1.func '' U)) :
    i ∉ Iact d (φ2 * φ1) U := by
  have h1c := (not_active_iff d φ1 U i).mp h1
  have h2c := (not_active_iff d φ2 (φ1.func '' U) i).mp h2
  have hcomp_notconst_or_id :
      i ∈ Iconst d (φ2 * φ1) U ∨ i ∈ Iid d (φ2 * φ1) U := by
    rcases h1c with h1const | h1id
    · rcases h2c with h2const | h2id
      · left
        intro x hx y hy
        exact h2const (φ1.func x) ⟨x, hx, rfl⟩ (φ1.func y) ⟨y, hy, rfl⟩
      · rcases h2id with ⟨_, h2zero⟩
        left
        intro x hx y hy
        have hφx : φ1.func x ∈ φ1.func '' U := ⟨x, hx, rfl⟩
        have hφy : φ1.func y ∈ φ1.func '' U := ⟨y, hy, rfl⟩
        have hmid : d i (φ1.func x) (φ1.func y) = 0 := h1const x hx y hy
        apply le_antisymm
        · calc
            d i ((φ2 * φ1).func x) ((φ2 * φ1).func y)
                = d i (φ2.func (φ1.func x)) (φ2.func (φ1.func y)) := rfl
            _ ≤ d i (φ2.func (φ1.func x)) (φ1.func x) +
                  d i (φ1.func x) (φ2.func (φ1.func y)) := (hd i).triangle _ _ _
            _ ≤ d i (φ2.func (φ1.func x)) (φ1.func x) +
                  (d i (φ1.func x) (φ1.func y) +
                    d i (φ1.func y) (φ2.func (φ1.func y))) := by
              gcongr
              exact (hd i).triangle _ _ _
            _ = 0 := by
              rw [h2zero (φ1.func x) hφx, hmid,
                ← (hd i).symm (φ2.func (φ1.func y)) (φ1.func y),
                h2zero (φ1.func y) hφy]
              simp
        · exact zero_le _
    · rcases h2c with h2const | h2id
      · left
        intro x hx y hy
        exact h2const (φ1.func x) ⟨x, hx, rfl⟩ (φ1.func y) ⟨y, hy, rfl⟩
      · rcases h1id with ⟨h1nc, h1zero⟩
        rcases h2id with ⟨h2nc', h2zero⟩
        right
        refine ⟨?_, ?_⟩
        · intro hcompconst
          apply h1nc
          intro x hx y hy
          have hout := hcompconst x hx y hy
          change d i (φ2.func (φ1.func x)) (φ2.func (φ1.func y)) = 0 at hout
          have hiso := id_component_isometry d hd φ2 (φ1.func '' U) i
            ⟨h2nc', h2zero⟩ (φ1.func x) ⟨x, hx, rfl⟩ (φ1.func y) ⟨y, hy, rfl⟩
          rw [hiso] at hout
          exact hout
        · intro x hx
          have hφx : φ1.func x ∈ φ1.func '' U := ⟨x, hx, rfl⟩
          apply le_antisymm
          · calc
              d i ((φ2 * φ1).func x) x
                  = d i (φ2.func (φ1.func x)) x := rfl
              _ ≤ d i (φ2.func (φ1.func x)) (φ1.func x) + d i (φ1.func x) x :=
                  (hd i).triangle _ _ _
              _ = 0 := by rw [h2zero (φ1.func x) hφx, h1zero x hx]; simp
          · exact zero_le _
  exact (not_active_iff d (φ2 * φ1) U i).mpr hcomp_notconst_or_id

theorem active_subset_two_step
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ1 φ2 : Operator X bot) (U : Set X) :
    Iact d (φ2 * φ1) U ⊆
      Iact d φ1 U ∪ Iact d φ2 (φ1.func '' U) := by
  intro i hi
  by_contra hnot
  have h1 : i ∉ Iact d φ1 U := fun h => hnot (Or.inl h)
  have h2 : i ∉ Iact d φ2 (φ1.func '' U) := fun h => hnot (Or.inr h)
  exact (active_composite_of_not_active_steps d hd φ1 φ2 U i h1 h2) hi

theorem id_subset_composite_id
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ1 φ2 : Operator X bot) (U : Set X) :
    Iid d φ1 U ∩ Iid d φ2 (φ1.func '' U) ⊆ Iid d (φ2 * φ1) U := by
  intro i hi
  rcases hi with ⟨h1id, h2id⟩
  rcases h1id with ⟨h1nc, h1zero⟩
  rcases h2id with ⟨h2nc, h2zero⟩
  refine ⟨?_, ?_⟩
  · intro hcompconst
    apply h1nc
    intro x hx y hy
    have hout := hcompconst x hx y hy
    change d i (φ2.func (φ1.func x)) (φ2.func (φ1.func y)) = 0 at hout
    have hiso := id_component_isometry d hd φ2 (φ1.func '' U) i
      ⟨h2nc, h2zero⟩ (φ1.func x) ⟨x, hx, rfl⟩ (φ1.func y) ⟨y, hy, rfl⟩
    rw [hiso] at hout
    exact hout
  · intro x hx
    have hφx : φ1.func x ∈ φ1.func '' U := ⟨x, hx, rfl⟩
    apply le_antisymm
    · calc
        d i ((φ2 * φ1).func x) x
            = d i (φ2.func (φ1.func x)) x := rfl
        _ ≤ d i (φ2.func (φ1.func x)) (φ1.func x) + d i (φ1.func x) x :=
            (hd i).triangle _ _ _
        _ = 0 := by rw [h2zero (φ1.func x) hφx, h1zero x hx]; simp
    · exact zero_le _

/-! ### Finite chains -/

/-- Compose a list of operators in the order of the list. -/
def listCompose : List (Operator X bot) → Operator X bot
  | [] => 1
  | φ :: rest => listCompose rest * φ

@[simp] theorem listCompose_nil : listCompose ([] : List (Operator X bot)) = 1 := rfl

@[simp] theorem listCompose_cons (φ : Operator X bot) (rest : List (Operator X bot)) :
    listCompose (φ :: rest) = listCompose rest * φ := rfl

/-- The list of actual successive evaluation domains. -/
def imageChain : List (Operator X bot) → Set X → List (Set X)
  | [], U => [U]
  | φ :: rest, U => U :: imageChain rest (φ.func '' U)

/-- The active component sets at successive steps. -/
def activeChain (d : I → X → X → ENNReal) :
    List (Operator X bot) → Set X → List (Set I)
  | [], _ => []
  | φ :: rest, U => Iact d φ U :: activeChain d rest (φ.func '' U)

/-- Union of a list of sets. -/
def listUnion {α : Type} : List (Set α) → Set α
  | [] => ∅
  | s :: ss => s ∪ listUnion ss

theorem active_identity_eq_empty
    (d : I → X → X → ENNReal) (hself : ∀ i x, d i x x = 0) (U : Set X) :
    Iact d (1 : Operator X bot) U = ∅ := by
  ext i
  constructor
  · intro hi
    by_cases hc : i ∈ Iconst d (1 : Operator X bot) U
    · exact (hi.1 hc).elim
    · have hiid : i ∈ Iid d (1 : Operator X bot) U := by
        refine ⟨hc, ?_⟩
        intro x hx
        change d i x x = 0
        exact hself i x
      exact (hi.2 hiid).elim
  · intro hi; simp at hi

/-- The active components of an arbitrary finite chain are contained in the
union of the active components at the actual successive image domains. -/
theorem active_subset_union_chain
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φs : List (Operator X bot)) (U : Set X)
    (hdom : U ⊆ dom (listCompose φs)) :
    Iact d (listCompose φs) U ⊆ listUnion (activeChain d φs U) := by
  induction φs generalizing U with
  | nil =>
      change Iact d (1 : Operator X bot) U ⊆ listUnion (activeChain d [] U)
      rw [active_identity_eq_empty d (fun i x => (hd i).dist_self x)]
      simp [listUnion, activeChain]
  | cons φ rest ih =>
      rw [listCompose_cons]
      have hdomφ : U ⊆ dom φ := by
        intro x hx
        by_contra hxbot
        have hxval : φ.func x = bot := by simpa [dom] using hxbot
        have hcomp : (listCompose rest * φ).func x = bot := by
          change (listCompose rest).func (φ.func x) = bot
          rw [hxval, (listCompose rest).preserves_bot]
        exact hdom hx (by simpa [dom] using hcomp)
      have hdomRest : φ.func '' U ⊆ dom (listCompose rest) := by
        intro y hy
        rcases hy with ⟨x, hx, rfl⟩
        have hxne : (listCompose rest).func (φ.func x) ≠ bot := by
          intro hb
          exact hdom hx (by simpa [dom, listCompose_cons] using hb)
        simpa [dom] using hxne
      intro i hi
      have hstep := active_subset_two_step d hd φ (listCompose rest) U hi
      rcases hstep with hleft | hright
      · exact Or.inl hleft
      · have hrec := ih (φ.func '' U) hdomRest hright
        exact Or.inr hrec

end formal_oet.vol_01.ch_03_operator_local_degeneracy
