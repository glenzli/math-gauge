import formal_oet.vol_01.ch_01_foundations.operator_space

open formal_oet.vol_01.ch_01_foundations
open scoped BigOperators

namespace Channels

variable {X I : Type} {bot : X} [Fintype I] [Nonempty I]

/-- Entries are indexed by input first and output second. -/
abbrev Coeff (I : Type) := I → I → ENNReal

noncomputable def matrixMul (B A : Coeff I) : Coeff I :=
  fun i j => ∑ k : I, B k j * A i k

def lipOn (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) (L : Coeff I) : Prop :=
  U ⊆ dom φ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j,
    d j (φ.func x) (φ.func y) ≤ ∑ i : I, L i j * d i x y

def lip (d : I → X → X → ENNReal) (φ : Operator X bot)
    (L : Coeff I) : Prop := lipOn d φ (dom φ) L

def lipFamily (d : I → X → X → ENNReal) (φ : Operator X bot) : Set (Coeff I) :=
  {L | lip d φ L}

def lipFamilyOn (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) : Set (Coeff I) := {L | lipOn d φ U L}

def coLipOn (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) (K : Coeff I) : Prop :=
  U.Nonempty ∧ U ⊆ dom φ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j,
    (∑ i : I, K i j * d i x y) ≤ d j (φ.func x) (φ.func y)

def coLipFamilyOn (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) : Set (Coeff I) := {K | coLipOn d φ U K}

/-- A component channel is an input/output pair. -/
abbrev Channel (I : Type) := I × I

def singleInputRow (L : Coeff I) (i j : I) : Prop :=
  ∀ k, k ≠ i → L k j = 0

def diagonal (L : Coeff I) : Prop := ∀ i j, i ≠ j → L i j = 0

theorem diagonal_singleInputRow (L : Coeff I) (h : diagonal L) (j : I) :
    singleInputRow L j j := by
  intro k hk
  exact h k j hk

theorem row_sum (L : Coeff I) (d : I → X → X → ENNReal)
    (i j : I) (h : singleInputRow L i j) (x y : X) :
    (∑ k : I, L k j * d k x y) = L i j * d i x y := by
  classical
  apply Finset.sum_eq_single i
  · intro k _ hk
    rw [h k hk, zero_mul]
  · simp

theorem lip_single_channel (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) (L : Coeff I) (i j : I)
    (hL : lipOn d φ U L) (hrow : singleInputRow L i j) :
    ∀ x ∈ U, ∀ y ∈ U, d j (φ.func x) (φ.func y) ≤ L i j * d i x y := by
  intro x hx y hy
  simpa only [row_sum L d i j hrow x y] using hL.2 x hx y hy j

theorem lip_diagonal_channel (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) (L : Coeff I) (hL : lipOn d φ U L) (hdiag : diagonal L) :
    ∀ j x, x ∈ U → ∀ y ∈ U,
      d j (φ.func x) (φ.func y) ≤ L j j * d j x y := by
  intro j x hx y hy
  exact lip_single_channel d φ U L j j hL (diagonal_singleInputRow L hdiag j) x hx y hy

theorem coLip_term_le (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) (K : Coeff I) (hK : coLipOn d φ U K)
    (i j : I) (x y : X) (hx : x ∈ U) (hy : y ∈ U) :
    K i j * d i x y ≤ d j (φ.func x) (φ.func y) := by
  classical
  calc
    K i j * d i x y ≤ ∑ k : I, K k j * d k x y :=
      Finset.single_le_sum (f := fun k => K k j * d k x y)
        (fun k _ => zero_le _) (Finset.mem_univ i)
    _ ≤ d j (φ.func x) (φ.func y) := hK.2.2 x hx y hy j

theorem positive_channel (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) (K : Coeff I) (hK : coLipOn d φ U K)
    (i j : I) (hpos : 0 < K i j) :
    ∀ x ∈ U, ∀ y ∈ U, 0 < d i x y → 0 < d j (φ.func x) (φ.func y) := by
  intro x hx y hy hd
  exact lt_of_lt_of_le (ENNReal.mul_pos_iff.mpr ⟨hpos, hd⟩)
    (coLip_term_le d φ U K hK i j x y hx hy)

theorem reflects_gauge_zero (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) (K : Coeff I) (hK : coLipOn d φ U K)
    (hdiag : ∀ j, 0 < K j j) :
    ∀ x ∈ U, ∀ y ∈ U,
      GaugeZeroRelated d (φ.func x) (φ.func y) → GaugeZeroRelated d x y := by
  intro x hx y hy hzero j
  by_contra hn
  have hp : 0 < d j x y := bot_lt_iff_ne_bot.mpr hn
  have hout := positive_channel d φ U K hK j j (hdiag j) x hx y hy hp
  rw [hzero j] at hout
  exact (lt_irrefl 0) hout

theorem scalar_two_sided (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) (L K : Coeff I) (j : I)
    (hL : lipOn d φ U L) (hK : coLipOn d φ U K)
    (hrow : singleInputRow L j j) :
    ∀ x ∈ U, ∀ y ∈ U,
      K j j * d j x y ≤ d j (φ.func x) (φ.func y) ∧
      d j (φ.func x) (φ.func y) ≤ L j j * d j x y := by
  intro x hx y hy
  exact ⟨coLip_term_le d φ U K hK j j x y hx hy,
    lip_single_channel d φ U L j j hL hrow x hx y hy⟩

end Channels
