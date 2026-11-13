/-
  Formalization of Operator Evolution Theory (OET), Volume I, Chapter 2,
  Section 2.1 (operator Lip/co-Lip matrix bounds, monotonicity, two-step and
  finite-chain composition, and zero-step identity certificates).

  Original mathematical theory by Zhe Li (Glen Li / glenzli),
  The Operator Evolution Theory, Volume I, v1.0.0, licensed under CC BY 4.0.
-/

import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space
import LCH02.MatrixBounds

namespace LCH02

open formal_oet.vol_01.ch_01_foundations

section MatrixCertificates

/--
**CH02-D01**: Predicate asserting that `L` is a valid global Lipschitz matrix
for operator `ϕ` under gauge family `d` (over `dom ϕ`).
-/
def IsLipMatrix {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (L : GaugeMatrix I) : Prop :=
  ∀ x ∈ dom ϕ, ∀ y ∈ dom ϕ, ∀ j : I,
    d j (ϕ.func x) (ϕ.func y) ≤ ∑ i : I, matrixEntry L i j * d i x y

/-- **CH02-D01**: Global Lipschitz certificate family `L(ϕ)`. -/
def LipMatrices {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) : Set (GaugeMatrix I) :=
  { L | IsLipMatrix d ϕ L }

/--
**CH02-D01**: Predicate asserting that `L` is a valid restricted Lipschitz matrix
for `ϕ` on `U ⊆ dom ϕ`.
-/
def IsRestrictedLipMatrix {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (L : GaugeMatrix I) : Prop :=
  U ⊆ dom ϕ ∧
  ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
    d j (ϕ.func x) (ϕ.func y) ≤ ∑ i : I, matrixEntry L i j * d i x y

/-- **CH02-D01**: Restricted Lipschitz certificate family `L(ϕ)|_U`. -/
def RestrictedLipMatrices {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) : Set (GaugeMatrix I) :=
  { L | IsRestrictedLipMatrix d ϕ U L }

theorem isRestrictedLipMatrix_dom_iff {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (L : GaugeMatrix I) :
    IsRestrictedLipMatrix d ϕ (dom ϕ) L ↔ IsLipMatrix d ϕ L := by
  simp [IsRestrictedLipMatrix, IsLipMatrix]

@[simp]
theorem restrictedLipMatrices_dom {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) :
    RestrictedLipMatrices d ϕ (dom ϕ) = LipMatrices d ϕ := by
  ext L
  exact isRestrictedLipMatrix_dom_iff d ϕ L

/--
**CH02-D02**: Predicate asserting that `K` is a valid restricted co-Lipschitz matrix
for `ϕ` on `U`. By definition, `U` must be nonempty and contained in `dom ϕ`.
-/
def IsRestrictedCoLipMatrix {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (K : GaugeMatrix I) : Prop :=
  U.Nonempty ∧ U ⊆ dom ϕ ∧
  ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
    ∑ i : I, matrixEntry K i j * d i x y ≤ d j (ϕ.func x) (ϕ.func y)

/-- **CH02-D02**: Restricted co-Lipschitz certificate family `K(ϕ)|_U`. -/
def RestrictedCoLipMatrices {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) : Set (GaugeMatrix I) :=
  { K | IsRestrictedCoLipMatrix d ϕ U K }

end MatrixCertificates

section SingleComponentAndMonotonicity

private theorem sum_eq_single_of_subsingleton {I : Type} [Fintype I] [Subsingleton I]
    (i : I) (f : I → ENNReal) :
    ∑ k : I, f k = f i := by
  have huniv : (Finset.univ : Finset I) = {i} := by
    ext k
    simp [Subsingleton.elim k i]
  rw [huniv, Finset.sum_singleton]

/--
**CH02-P01 (Single-component scalar Lip bound)**:
When `|I| = 1` with `I = {i}`, the global Lip matrix condition degenerates
to the scalar inequality `d_i(ϕ(x), ϕ(y)) ≤ L_{i -> i} * d_i(x, y)` on `dom ϕ`.
-/
theorem isLipMatrix_iff_scalar_of_card_eq_one {X I : Type} {bot : X} [Fintype I]
    (hcard : Fintype.card I = 1) (i : I)
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (L : GaugeMatrix I) :
    IsLipMatrix d ϕ L ↔
      ∀ x ∈ dom ϕ, ∀ y ∈ dom ϕ,
        d i (ϕ.func x) (ϕ.func y) ≤ matrixEntry L i i * d i x y := by
  haveI : Subsingleton I := Fintype.card_le_one_iff_subsingleton.mp hcard.le
  constructor
  · intro hL x hx y hy
    simpa [sum_eq_single_of_subsingleton i] using hL x hx y hy i
  · intro hscalar x hx y hy j
    have hj : j = i := Subsingleton.elim j i
    subst hj
    rw [sum_eq_single_of_subsingleton j]
    exact hscalar x hx y hy

/-- Restricted scalar Lip degeneration when `|I| = 1` and `I = {i}`. -/
theorem isRestrictedLipMatrix_iff_scalar_of_card_eq_one {X I : Type} {bot : X} [Fintype I]
    (hcard : Fintype.card I = 1) (i : I)
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (L : GaugeMatrix I) :
    IsRestrictedLipMatrix d ϕ U L ↔
      U ⊆ dom ϕ ∧
      ∀ x ∈ U, ∀ y ∈ U,
        d i (ϕ.func x) (ϕ.func y) ≤ matrixEntry L i i * d i x y := by
  haveI : Subsingleton I := Fintype.card_le_one_iff_subsingleton.mp hcard.le
  constructor
  · rintro ⟨hU, hL⟩
    exact ⟨hU, fun x hx y hy => by simpa [sum_eq_single_of_subsingleton i] using hL x hx y hy i⟩
  · rintro ⟨hU, hscalar⟩
    refine ⟨hU, fun x hx y hy j => ?_⟩
    have hj : j = i := Subsingleton.elim j i
    subst hj
    rw [sum_eq_single_of_subsingleton j]
    exact hscalar x hx y hy

/--
**CH02-P02 (Lemma 2.1, part 1)**:
Antitonicity of restricted Lip certificate families:
if `U ⊆ V ⊆ dom ϕ`, then `L(ϕ)|_V ⊆ L(ϕ)|_U`.
-/
theorem restrictedLipMatrices_antitone {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U V : Set X}
    (hUV : U ⊆ V) (hV : V ⊆ dom ϕ) :
    RestrictedLipMatrices d ϕ V ⊆ RestrictedLipMatrices d ϕ U := by
  intro L hL
  refine ⟨hUV.trans hV, fun x hx y hy j => ?_⟩
  exact hL.2 x (hUV hx) y (hUV hy) j

/--
**CH02-P03 (Lemma 2.1, part 2)**:
Global Lip certificates restrict to any subset `U ⊆ dom ϕ`: `L(ϕ) ⊆ L(ϕ)|_U`.
-/
theorem lipMatrices_subset_restrictedLipMatrices {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X}
    (hU : U ⊆ dom ϕ) :
    LipMatrices d ϕ ⊆ RestrictedLipMatrices d ϕ U := by
  rw [← restrictedLipMatrices_dom]
  exact restrictedLipMatrices_antitone d ϕ hU Set.Subset.rfl

/--
**CH02-P05 (Lemma 2.3, part 1)**:
Antitonicity of restricted co-Lip certificate families:
if `U` is nonempty and `U ⊆ V ⊆ dom ϕ`, then `K(ϕ)|_V ⊆ K(ϕ)|_U`.
-/
theorem restrictedCoLipMatrices_antitone {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U V : Set X}
    (hU_ne : U.Nonempty) (hUV : U ⊆ V) (hV : V ⊆ dom ϕ) :
    RestrictedCoLipMatrices d ϕ V ⊆ RestrictedCoLipMatrices d ϕ U := by
  intro K hK
  refine ⟨hU_ne, hUV.trans hV, fun x hx y hy j => ?_⟩
  exact hK.2.2 x (hUV hx) y (hUV hy) j

/--
**CH02-P06 (Lemma 2.3, part 2)**:
Global co-Lip certificates on `dom ϕ` restrict to any nonempty subset `U ⊆ dom ϕ`:
`K(ϕ)|_{dom ϕ} ⊆ K(ϕ)|_U`.
-/
theorem coLipMatrices_dom_subset_restrictedCoLipMatrices {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X}
    (hU_ne : U.Nonempty) (hU : U ⊆ dom ϕ) :
    RestrictedCoLipMatrices d ϕ (dom ϕ) ⊆ RestrictedCoLipMatrices d ϕ U :=
  restrictedCoLipMatrices_antitone d ϕ hU_ne hU Set.Subset.rfl

/--
**CH02-P07 (Sufficient condition for zero co-Lip entry)**:
If there exist `x, y ∈ dom ϕ` with `d_j(ϕ(x), ϕ(y)) = 0` and `0 < d_i(x, y)`,
then any global co-Lip matrix `K ∈ K(ϕ)|_{dom ϕ}` satisfies `K_{i -> j} = 0`.
-/
theorem coLipMatrix_entry_eq_zero_of_dist_zero_pos {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {i j : I} {K : GaugeMatrix I}
    (hxy : ∃ x ∈ dom ϕ, ∃ y ∈ dom ϕ, d j (ϕ.func x) (ϕ.func y) = 0 ∧ 0 < d i x y)
    (hK : K ∈ RestrictedCoLipMatrices d ϕ (dom ϕ)) :
    matrixEntry K i j = 0 := by
  rcases hxy with ⟨x, hx, y, hy, h_out_zero, h_in_pos⟩
  have h_le : matrixEntry K i j * d i x y ≤ d j (ϕ.func x) (ϕ.func y) := by
    calc
      matrixEntry K i j * d i x y
          ≤ ∑ k : I, matrixEntry K k j * d k x y :=
            Finset.single_le_sum (f := fun k => matrixEntry K k j * d k x y)
              (fun _ _ => zero_le _) (Finset.mem_univ i)
      _ ≤ d j (ϕ.func x) (ϕ.func y) := hK.2.2 x hx y hy j
  rw [h_out_zero] at h_le
  have h_mul_zero : matrixEntry K i j * d i x y = 0 := le_antisymm h_le (zero_le _)
  rcases mul_eq_zero.mp h_mul_zero with hK_zero | hd_zero
  · exact hK_zero
  · exact absurd hd_zero (ne_of_gt h_in_pos)

end SingleComponentAndMonotonicity

section TwoStepComposition

theorem subset_dom_left_of_subset_dom_comp {X : Type} {bot : X}
    (ϕ₁ ϕ₂ : Operator X bot) {U₁ : Set X} (hU₁ : U₁ ⊆ dom (ϕ₂ * ϕ₁)) :
    U₁ ⊆ dom ϕ₁ := by
  intro x hx h_bot
  have h_comp : (ϕ₂ * ϕ₁).func x ≠ bot := hU₁ hx
  apply h_comp
  change ϕ₂.func (ϕ₁.func x) = bot
  rw [h_bot, ϕ₂.preserves_bot]

theorem operator_image_subset_dom_right_of_subset_dom_comp {X : Type} {bot : X}
    (ϕ₁ ϕ₂ : Operator X bot) {U₁ : Set X} (hU₁ : U₁ ⊆ dom (ϕ₂ * ϕ₁)) :
    operator_image ϕ₁ U₁ ⊆ dom ϕ₂ := by
  rintro y ⟨x, hx, rfl⟩
  exact hU₁ hx

theorem operator_image_nonempty {X : Type} {bot : X}
    (ϕ : Operator X bot) {U : Set X} (hU : U.Nonempty) :
    (operator_image ϕ U).Nonempty :=
  hU.image ϕ.func

/--
**CH02-P04 (Proposition 2.2, Lip matrix composition law)**:
For `ϕ₂ * ϕ₁` and `U₁ ⊆ dom (ϕ₂ * ϕ₁)` with exact intermediate image `U₂ = ϕ₁(U₁)`,
if `L₁ ∈ L(ϕ₁)|_{U₁}` and `L₂ ∈ L(ϕ₂)|_{U₂}`, then `L₂ * L₁ ∈ L(ϕ₂ * ϕ₁)|_{U₁}`.
-/
theorem restrictedLipMatrices_comp {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ₁ ϕ₂ : Operator X bot)
    {U₁ : Set X} (hU₁ : U₁ ⊆ dom (ϕ₂ * ϕ₁))
    {L₁ L₂ : GaugeMatrix I}
    (hL₁ : L₁ ∈ RestrictedLipMatrices d ϕ₁ U₁)
    (hL₂ : L₂ ∈ RestrictedLipMatrices d ϕ₂ (operator_image ϕ₁ U₁)) :
    L₂ * L₁ ∈ RestrictedLipMatrices d (ϕ₂ * ϕ₁) U₁ := by
  refine ⟨hU₁, fun x hx y hy j => ?_⟩
  have hx₂ : ϕ₁.func x ∈ operator_image ϕ₁ U₁ := ⟨x, hx, rfl⟩
  have hy₂ : ϕ₁.func y ∈ operator_image ϕ₁ U₁ := ⟨y, hy, rfl⟩
  calc
    d j ((ϕ₂ * ϕ₁).func x) ((ϕ₂ * ϕ₁).func y)
        = d j (ϕ₂.func (ϕ₁.func x)) (ϕ₂.func (ϕ₁.func y)) := rfl
    _ ≤ ∑ k : I, matrixEntry L₂ k j * d k (ϕ₁.func x) (ϕ₁.func y) :=
          hL₂.2 (ϕ₁.func x) hx₂ (ϕ₁.func y) hy₂ j
    _ ≤ ∑ k : I, matrixEntry L₂ k j * ∑ i : I, matrixEntry L₁ i k * d i x y := by
          refine Finset.sum_le_sum fun k _ => ?_
          exact mul_le_mul_of_nonneg_left (hL₁.2 x hx y hy k) (zero_le _)
    _ = ∑ i : I, matrixEntry (L₂ * L₁) i j * d i x y := by
          rw [matrixEntry_mul_sum_eq]

/--
**CH02-P08 (Proposition 2.4, co-Lip matrix composition law)**:
For `ϕ₂ * ϕ₁` and `U₁ ⊆ dom (ϕ₂ * ϕ₁)` with exact intermediate image `U₂ = ϕ₁(U₁)`,
if `K₁ ∈ K(ϕ₁)|_{U₁}` and `K₂ ∈ K(ϕ₂)|_{U₂}`, then `K₂ * K₁ ∈ K(ϕ₂ * ϕ₁)|_{U₁}`
(with nonemptiness of `U₁` inherited from `K₁ ∈ K(ϕ₁)|_{U₁}`).
-/
theorem restrictedCoLipMatrices_comp {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ₁ ϕ₂ : Operator X bot)
    {U₁ : Set X} (hU₁ : U₁ ⊆ dom (ϕ₂ * ϕ₁))
    {K₁ K₂ : GaugeMatrix I}
    (hK₁ : K₁ ∈ RestrictedCoLipMatrices d ϕ₁ U₁)
    (hK₂ : K₂ ∈ RestrictedCoLipMatrices d ϕ₂ (operator_image ϕ₁ U₁)) :
    K₂ * K₁ ∈ RestrictedCoLipMatrices d (ϕ₂ * ϕ₁) U₁ := by
  refine ⟨hK₁.1, hU₁, fun x hx y hy j => ?_⟩
  have hx₂ : ϕ₁.func x ∈ operator_image ϕ₁ U₁ := ⟨x, hx, rfl⟩
  have hy₂ : ϕ₁.func y ∈ operator_image ϕ₁ U₁ := ⟨y, hy, rfl⟩
  calc
    ∑ i : I, matrixEntry (K₂ * K₁) i j * d i x y
        = ∑ k : I, matrixEntry K₂ k j * ∑ i : I, matrixEntry K₁ i k * d i x y :=
          matrixEntry_mul_sum_eq K₂ K₁ (fun i => d i x y) j
    _ ≤ ∑ k : I, matrixEntry K₂ k j * d k (ϕ₁.func x) (ϕ₁.func y) := by
          refine Finset.sum_le_sum fun k _ => ?_
          exact mul_le_mul_of_nonneg_left (hK₁.2.2 x hx y hy k) (zero_le _)
    _ ≤ d j (ϕ₂.func (ϕ₁.func x)) (ϕ₂.func (ϕ₁.func y)) :=
          hK₂.2.2 (ϕ₁.func x) hx₂ (ϕ₁.func y) hy₂ j
    _ = d j ((ϕ₂ * ϕ₁).func x) ((ϕ₂ * ϕ₁).func y) := rfl

end TwoStepComposition

section ZeroStepIdentity

private theorem matrixOne_sum_eq {I : Type} [Fintype I] [DecidableEq I]
    (v : I → ENNReal) (j : I) :
    ∑ i : I, matrixEntry (matrixOne : GaugeMatrix I) i j * v i = v j := by
  have h : (fun i : I => matrixEntry (matrixOne : GaugeMatrix I) i j * v i) =
      fun i : I => if i = j then v i else 0 := by
    ext i
    rw [matrixEntry_one]
    by_cases hij : i = j <;> simp [hij]
  rw [h]
  simp

/--
**CH02-P11 (Zero-step identity Lip certificate)**:
For any `U ⊆ dom id`, the identity matrix `I` belongs to `L(id)|_U`.
-/
theorem matrixOne_mem_restrictedLipMatrices_id {X I : Type} {bot : X}
    [Fintype I] [DecidableEq I]
    (d : I → X → X → ENNReal) {U : Set X}
    (hU : U ⊆ dom (operator_identity (X := X) (bot := bot))) :
    matrixOne ∈ RestrictedLipMatrices d (operator_identity (X := X) (bot := bot)) U := by
  refine ⟨hU, fun x _ y _ j => ?_⟩
  rw [matrixOne_sum_eq]
  rfl

/--
**CH02-P12 (Zero-step identity co-Lip certificate)**:
For any nonempty `U ⊆ dom id`, the identity matrix `I` belongs to `K(id)|_U`.
-/
theorem matrixOne_mem_restrictedCoLipMatrices_id {X I : Type} {bot : X}
    [Fintype I] [DecidableEq I]
    (d : I → X → X → ENNReal) {U : Set X}
    (hU_ne : U.Nonempty)
    (hU : U ⊆ dom (operator_identity (X := X) (bot := bot))) :
    matrixOne ∈ RestrictedCoLipMatrices d (operator_identity (X := X) (bot := bot)) U := by
  refine ⟨hU_ne, hU, fun x _ y _ j => ?_⟩
  rw [matrixOne_sum_eq]
  rfl

/-- Combined zero-step identity note: `I ∈ L(id)|_U ∩ K(id)|_U` for nonempty `U ⊆ dom id`. -/
theorem matrixOne_mem_id_inter {X I : Type} {bot : X}
    [Fintype I] [DecidableEq I]
    (d : I → X → X → ENNReal) {U : Set X}
    (hU_ne : U.Nonempty)
    (hU : U ⊆ dom (operator_identity (X := X) (bot := bot))) :
    matrixOne ∈ RestrictedLipMatrices d (operator_identity (X := X) (bot := bot)) U ∩
      RestrictedCoLipMatrices d (operator_identity (X := X) (bot := bot)) U :=
  ⟨matrixOne_mem_restrictedLipMatrices_id d hU,
    matrixOne_mem_restrictedCoLipMatrices_id d hU_ne hU⟩

end ZeroStepIdentity

section ChainDomainsAndFiniteComposition

theorem operator_image_mul {X : Type} {bot : X}
    (ϕ₂ ϕ₁ : Operator X bot) (U : Set X) :
    operator_image (ϕ₂ * ϕ₁) U = operator_image ϕ₂ (operator_image ϕ₁ U) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨ϕ₁.func x, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩

/--
**CH02-D05**: Step-indexed finite composition `c_k = ϕ_k ∘ ... ∘ ϕ_1`,
with `c_0 = id` when `k = 0`.
-/
def chainCompose {X : Type} {bot : X} :
    {k : ℕ} → (Fin k → Operator X bot) → Operator X bot
  | 0, _ => operator_identity
  | k + 1, ϕs => ϕs (Fin.last k) * chainCompose (fun r : Fin k => ϕs r.castSucc)

@[simp]
theorem chainCompose_zero {X : Type} {bot : X} (ϕs : Fin 0 → Operator X bot) :
    chainCompose ϕs = operator_identity :=
  rfl

@[simp]
theorem chainCompose_succ {X : Type} {bot : X} {k : ℕ}
    (ϕs : Fin (k + 1) → Operator X bot) :
    chainCompose ϕs = ϕs (Fin.last k) * chainCompose (fun r : Fin k => ϕs r.castSucc) :=
  rfl

/--
**CH02-D05**: Exact correspondence between step-indexed composition `chainCompose ϕs`
and `formal_oet.vol_01.ch_01_foundations.OperatorChain`.
Because `OperatorChain [ϕ_k, ..., ϕ_1]` applies the rightmost element first,
it equals `chainCompose` on the reversed step list.
-/
theorem chainCompose_eq_operatorChain_reverse {X : Type} {bot : X} :
    {k : ℕ} → (ϕs : Fin k → Operator X bot) →
      chainCompose ϕs = OperatorChain (List.ofFn ϕs).reverse
  | 0, _ => rfl
  | k + 1, ϕs => by
      have ih := chainCompose_eq_operatorChain_reverse (fun r : Fin k => ϕs r.castSucc)
      rw [chainCompose_succ, ih]
      conv_rhs => rw [List.ofFn_succ', List.concat_eq_append, List.reverse_append]
      rfl

theorem chainCompose_eq_prod {X : Type} {bot : X} {k : ℕ}
    (ϕs : Fin k → Operator X bot) :
    chainCompose ϕs = (List.ofFn ϕs).reverse.prod := by
  rw [chainCompose_eq_operatorChain_reverse, operator_chain_eq_prod]

/-- Extract step-ordered operators `(ϕ_1, ..., ϕ_k)` from an `OperatorChain` list `[ϕ_k, ..., ϕ_1]`. -/
def chainSteps {X : Type} {bot : X} (chain : List (Operator X bot)) :
    Fin chain.length → Operator X bot :=
  fun m => chain.reverse[m.1]'(by simp)

/-- Reverse correspondence: `OperatorChain` on any list equals `chainCompose` on `chainSteps chain`. -/
theorem operatorChain_eq_chainCompose_reverse {X : Type} {bot : X}
    (chain : List (Operator X bot)) :
    OperatorChain chain = chainCompose (chainSteps chain) := by
  have hrev : (List.ofFn (chainSteps chain)).reverse = chain := by
    have hof : List.ofFn (chainSteps chain) = chain.reverse := by
      refine List.ext_getElem (by simp) fun i hi₁ hi₂ => ?_
      simp [chainSteps]
    rw [hof, List.reverse_reverse]
  rw [chainCompose_eq_operatorChain_reverse, hrev]

/-- Recursive helper defining intermediate image domains `U_1, U_2, ..., U_{k+1}`. -/
def stepImage {X : Type} {bot : X} {k : ℕ}
    (ϕs : Fin k → Operator X bot) (U₁ : Set X) : ℕ → Set X
  | 0 => U₁
  | m + 1 =>
      if h : m < k then operator_image (ϕs ⟨m, h⟩) (stepImage ϕs U₁ m)
      else stepImage ϕs U₁ m

/--
**CH02-D05**: Actual intermediate image domains `U_1, ..., U_{k+1}` along `ϕ_1, ..., ϕ_k`,
defined recursively by `U_1` at index `0` and `U_{m+1} = ϕ_m(U_m)`.
-/
def chainDomain {X : Type} {bot : X} {k : ℕ}
    (ϕs : Fin k → Operator X bot) (U₁ : Set X) (m : Fin (k + 1)) : Set X :=
  stepImage ϕs U₁ m.1

@[simp]
theorem chainDomain_zero {X : Type} {bot : X} {k : ℕ}
    (ϕs : Fin k → Operator X bot) (U₁ : Set X) :
    chainDomain ϕs U₁ 0 = U₁ :=
  rfl

@[simp]
theorem chainDomain_succ {X : Type} {bot : X} {k : ℕ}
    (ϕs : Fin k → Operator X bot) (U₁ : Set X) (m : Fin k) :
    chainDomain ϕs U₁ m.succ = operator_image (ϕs m) (chainDomain ϕs U₁ m.castSucc) := by
  simp [chainDomain, stepImage, m.isLt]

private theorem stepImage_prefix_eq {X : Type} {bot : X} {k : ℕ}
    (ϕs : Fin (k + 1) → Operator X bot) (U₁ : Set X) :
    (m : ℕ) → m ≤ k →
      stepImage (fun r : Fin k => ϕs r.castSucc) U₁ m = stepImage ϕs U₁ m
  | 0, _ => rfl
  | m + 1, hm => by
      have hm_lt_k : m < k := hm
      have hm_lt_k1 : m < k + 1 := Nat.lt_succ_of_lt hm_lt_k
      have ih := stepImage_prefix_eq ϕs U₁ m (Nat.le_of_lt hm_lt_k)
      simp only [stepImage, dif_pos hm_lt_k, dif_pos hm_lt_k1]
      rw [ih]
      rfl

theorem chainDomain_prefix_eq {X : Type} {bot : X} {k : ℕ}
    (ϕs : Fin (k + 1) → Operator X bot) (U₁ : Set X) (m : Fin (k + 1)) :
    chainDomain (fun r : Fin k => ϕs r.castSucc) U₁ m = chainDomain ϕs U₁ m.castSucc :=
  stepImage_prefix_eq ϕs U₁ m.1 (Nat.lt_succ_iff.mp m.isLt)

/--
**CH02-D05**: The final domain `U_{k+1}` equals the image of `U_1` under `c_k = chainCompose ϕs`.
-/
theorem chainDomain_last_eq_image_chainCompose {X : Type} {bot : X} :
    {k : ℕ} → (ϕs : Fin k → Operator X bot) → (U₁ : Set X) →
      chainDomain ϕs U₁ (Fin.last k) = operator_image (chainCompose ϕs) U₁
  | 0, ϕs, U₁ => by
      simp [chainDomain, stepImage, chainCompose, operator_image, operator_identity]
  | k + 1, ϕs, U₁ => by
      have ih := chainDomain_last_eq_image_chainCompose (fun r : Fin k => ϕs r.castSucc) U₁
      have hlast : (Fin.last (k + 1) : Fin (k + 2)) = (Fin.last k : Fin (k + 1)).succ := rfl
      rw [hlast, chainDomain_succ, ← chainDomain_prefix_eq, ih, chainCompose_succ,
        operator_image_mul]

/-- Prefix composition `c_m = ϕ_m ∘ ... ∘ ϕ_1` for `m : Fin (k + 1)`. -/
def prefixCompose {X : Type} {bot : X} {k : ℕ}
    (ϕs : Fin k → Operator X bot) (m : Fin (k + 1)) : Operator X bot :=
  chainCompose (fun r : Fin m.1 =>
    ϕs ⟨r.1, Nat.lt_of_lt_of_le r.isLt (Nat.lt_succ_iff.mp m.isLt)⟩)

private theorem prefixCompose_succ_eq {X : Type} {bot : X} {k : ℕ}
    (ϕs : Fin k → Operator X bot) (m : Fin k) :
    prefixCompose ϕs m.succ = ϕs m * prefixCompose ϕs m.castSucc := by
  unfold prefixCompose
  simp only [Fin.val_succ, Fin.val_castSucc]
  rw [chainCompose_succ]
  rfl

/--
**CH02-D05**: Every intermediate domain `U_{m+1}` equals the image of `U_1` under
the prefix chain `c_m` (matching `OperatorChain` of the reversed prefix).
-/
theorem chainDomain_eq_image_prefix {X : Type} {bot : X} {k : ℕ}
    (ϕs : Fin k → Operator X bot) (U₁ : Set X) (m : Fin (k + 1)) :
    chainDomain ϕs U₁ m = operator_image (prefixCompose ϕs m) U₁ := by
  induction m using Fin.induction with
  | zero =>
      simp [prefixCompose, operator_image, operator_identity]
  | succ i ih =>
      rw [chainDomain_succ, ih, prefixCompose_succ_eq, operator_image_mul]

theorem subset_dom_prefix_of_subset_dom_chainCompose {X : Type} {bot : X} {k : ℕ}
    (ϕs : Fin (k + 1) → Operator X bot) {U₁ : Set X}
    (hU₁ : U₁ ⊆ dom (chainCompose ϕs)) :
    U₁ ⊆ dom (chainCompose (fun r : Fin k => ϕs r.castSucc)) := by
  rw [chainCompose_succ] at hU₁
  exact subset_dom_left_of_subset_dom_comp _ _ hU₁

/--
**CH02-D05**: Domain propagation along a chain:
if `U₁ ⊆ dom (c_k)`, then every actual intermediate domain `U_m` satisfies `U_m ⊆ dom (ϕ_m)`.
-/
theorem chainDomain_subset_dom_step {X : Type} {bot : X} :
    {k : ℕ} → (ϕs : Fin k → Operator X bot) → {U₁ : Set X} →
      U₁ ⊆ dom (chainCompose ϕs) →
      ∀ m : Fin k, chainDomain ϕs U₁ m.castSucc ⊆ dom (ϕs m)
  | 0, _, _, _, m => Fin.elim0 m
  | k + 1, ϕs, U₁, hU₁, m => by
      have h_pref : U₁ ⊆ dom (chainCompose (fun r : Fin k => ϕs r.castSucc)) :=
        subset_dom_prefix_of_subset_dom_chainCompose ϕs hU₁
      induction m using Fin.lastCases with
      | last =>
          rw [← chainDomain_prefix_eq, chainDomain_last_eq_image_chainCompose]
          rw [chainCompose_succ] at hU₁
          exact operator_image_subset_dom_right_of_subset_dom_comp _ _ hU₁
      | cast r =>
          change chainDomain ϕs U₁ r.castSucc.castSucc ⊆ dom (ϕs r.castSucc)
          rw [← chainDomain_prefix_eq]
          exact chainDomain_subset_dom_step (fun q : Fin k => ϕs q.castSucc) h_pref r

/-- Nonemptiness propagation along intermediate image domains. -/
theorem chainDomain_nonempty {X : Type} {bot : X} {k : ℕ}
    (ϕs : Fin k → Operator X bot) {U₁ : Set X} (hU₁ : U₁.Nonempty)
    (m : Fin (k + 1)) :
    (chainDomain ϕs U₁ m).Nonempty := by
  rw [chainDomain_eq_image_prefix]
  exact operator_image_nonempty _ hU₁

/--
**CH02-P11 (Zero-step chain form)**:
For `k = 0`, the empty matrix product belongs to `L(c_0)|_{U₁}` for any `U₁ ⊆ dom (c_0)`.
-/
theorem matrixProd_zero_mem_restrictedLipMatrices_chainCompose_zero
    {X I : Type} {bot : X} [Fintype I] [DecidableEq I]
    (d : I → X → X → ENNReal) (ϕs : Fin 0 → Operator X bot)
    (Ls : Fin 0 → GaugeMatrix I) {U₁ : Set X}
    (hU₁ : U₁ ⊆ dom (chainCompose ϕs)) :
    matrixProd Ls ∈ RestrictedLipMatrices d (chainCompose ϕs) U₁ := by
  simpa [matrixProd_zero, chainCompose_zero] using matrixOne_mem_restrictedLipMatrices_id d hU₁

/--
**CH02-P12 (Zero-step chain form)**:
For `k = 0` and nonempty `U₁ ⊆ dom (c_0)`, the empty matrix product belongs to `K(c_0)|_{U₁}`.
-/
theorem matrixProd_zero_mem_restrictedCoLipMatrices_chainCompose_zero
    {X I : Type} {bot : X} [Fintype I] [DecidableEq I]
    (d : I → X → X → ENNReal) (ϕs : Fin 0 → Operator X bot)
    (Ks : Fin 0 → GaugeMatrix I) {U₁ : Set X}
    (hU₁_ne : U₁.Nonempty) (hU₁ : U₁ ⊆ dom (chainCompose ϕs)) :
    matrixProd Ks ∈ RestrictedCoLipMatrices d (chainCompose ϕs) U₁ := by
  simpa [matrixProd_zero, chainCompose_zero] using
    matrixOne_mem_restrictedCoLipMatrices_id d hU₁_ne hU₁

private theorem chain_matrix_bound_pos_ind {X I : Type} {bot : X} [Fintype I]
    (P : Operator X bot → Set X → GaugeMatrix I → Prop)
    (h_comp : ∀ ϕ₁ ϕ₂ U₁ M₁ M₂,
      U₁ ⊆ dom (ϕ₂ * ϕ₁) →
      P ϕ₁ U₁ M₁ → P ϕ₂ (operator_image ϕ₁ U₁) M₂ →
      P (ϕ₂ * ϕ₁) U₁ (M₂ * M₁)) :
    {m : ℕ} → (ϕs : Fin (m + 1) → Operator X bot) → {U₁ : Set X} →
      U₁ ⊆ dom (chainCompose ϕs) →
      (Ms : Fin (m + 1) → GaugeMatrix I) →
      (∀ r : Fin (m + 1), P (ϕs r) (chainDomain ϕs U₁ r.castSucc) (Ms r)) →
      P (chainCompose ϕs) U₁ (matrixPosProd Ms)
  | 0, ϕs, U₁, _, Ms, hMs => by
      have h0 := hMs 0
      simpa [matrixPosProd, chainCompose, chainDomain] using h0
  | m + 1, ϕs, U₁, hU₁, Ms, hMs => by
      let ϕs' : Fin (m + 1) → Operator X bot := fun r => ϕs r.castSucc
      let Ms' : Fin (m + 1) → GaugeMatrix I := fun r => Ms r.castSucc
      have hU₁' : U₁ ⊆ dom (chainCompose ϕs') :=
        subset_dom_prefix_of_subset_dom_chainCompose ϕs hU₁
      have hMs' : ∀ r : Fin (m + 1),
          P (ϕs' r) (chainDomain ϕs' U₁ r.castSucc) (Ms' r) := by
        intro r
        rw [chainDomain_prefix_eq]
        exact hMs r.castSucc
      have ih := chain_matrix_bound_pos_ind P h_comp ϕs' hU₁' Ms' hMs'
      have h_last : P (ϕs (Fin.last (m + 1)))
          (operator_image (chainCompose ϕs') U₁) (Ms (Fin.last (m + 1))) := by
        rw [← chainDomain_last_eq_image_chainCompose, chainDomain_prefix_eq]
        exact hMs (Fin.last (m + 1))
      rw [matrixPosProd_succ, chainCompose_succ]
      exact h_comp (chainCompose ϕs') (ϕs (Fin.last (m + 1))) U₁
        (matrixPosProd Ms') (Ms (Fin.last (m + 1)))
        (by simpa [chainCompose_succ] using hU₁) ih h_last

private theorem chain_matrix_bound_ind {X I : Type} {bot : X} [Fintype I]
    (P : Operator X bot → Set X → GaugeMatrix I → Prop)
    (h_comp : ∀ ϕ₁ ϕ₂ U₁ M₁ M₂,
      U₁ ⊆ dom (ϕ₂ * ϕ₁) →
      P ϕ₁ U₁ M₁ → P ϕ₂ (operator_image ϕ₁ U₁) M₂ →
      P (ϕ₂ * ϕ₁) U₁ (M₂ * M₁))
    {k : ℕ} (hk : 0 < k) (ϕs : Fin k → Operator X bot)
    {U₁ : Set X} (hU₁ : U₁ ⊆ dom (chainCompose ϕs))
    (Ms : Fin k → GaugeMatrix I)
    (hMs : ∀ m : Fin k, P (ϕs m) (chainDomain ϕs U₁ m.castSucc) (Ms m)) :
    P (chainCompose ϕs) U₁ (matrixNonemptyProd hk Ms) := by
  cases k with
  | zero => exact absurd hk (Nat.lt_irrefl 0)
  | succ m => exact chain_matrix_bound_pos_ind P h_comp ϕs hU₁ Ms hMs

/--
**CH02-P09 (Corollary 2.5(i), finite-chain Lip product bound)**:
For any positive length `k ≥ 1`, if each step `m` has a restricted Lip certificate
`L^{(m)} ∈ L(ϕ_m)|_{U_m}` on the actual intermediate image domain `U_m`, then
`L^{(k)} * ... * L^{(1)} ∈ L(c_k)|_{U₁}`.
-/
theorem restrictedLipMatrices_chain {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal)
    {k : ℕ} (hk : 0 < k) (ϕs : Fin k → Operator X bot)
    {U₁ : Set X} (hU₁ : U₁ ⊆ dom (chainCompose ϕs))
    (Ls : Fin k → GaugeMatrix I)
    (hLs : ∀ m : Fin k, Ls m ∈ RestrictedLipMatrices d (ϕs m) (chainDomain ϕs U₁ m.castSucc)) :
    matrixNonemptyProd hk Ls ∈ RestrictedLipMatrices d (chainCompose ϕs) U₁ :=
  chain_matrix_bound_ind
    (fun ϕ U M => M ∈ RestrictedLipMatrices d ϕ U)
    (fun ϕ₁ ϕ₂ _ _ _ hU h₁ h₂ => restrictedLipMatrices_comp d ϕ₁ ϕ₂ hU h₁ h₂)
    hk ϕs hU₁ Ls hLs

/-- Direct corollary of `CH02-P09` formulated via `OperatorChain` from Chapter 1. -/
theorem restrictedLipMatrices_operatorChain {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal)
    (chain : List (Operator X bot)) (hchain : chain ≠ [])
    {U₁ : Set X} (hU₁ : U₁ ⊆ dom (OperatorChain chain))
    (Ls : Fin chain.length → GaugeMatrix I)
    (hLs : ∀ m : Fin chain.length,
      Ls m ∈ RestrictedLipMatrices d (chainSteps chain m)
        (chainDomain (chainSteps chain) U₁ m.castSucc)) :
    matrixNonemptyProd (List.length_pos_of_ne_nil hchain) Ls ∈
      RestrictedLipMatrices d (OperatorChain chain) U₁ := by
  have h_eq : OperatorChain chain = chainCompose (chainSteps chain) :=
    operatorChain_eq_chainCompose_reverse chain
  rw [h_eq] at hU₁ ⊢
  exact restrictedLipMatrices_chain d (List.length_pos_of_ne_nil hchain) (chainSteps chain) hU₁ Ls hLs

/--
**CH02-P10 (Corollary 2.5(ii), finite-chain co-Lip product bound)**:
For any positive length `k ≥ 1`, if each step `m` has a restricted co-Lip certificate
`K^{(m)} ∈ K(ϕ_m)|_{U_m}` on the actual intermediate image domain `U_m`, then
`K^{(k)} * ... * K^{(1)} ∈ K(c_k)|_{U₁}`.
-/
theorem restrictedCoLipMatrices_chain {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal)
    {k : ℕ} (hk : 0 < k) (ϕs : Fin k → Operator X bot)
    {U₁ : Set X} (hU₁ : U₁ ⊆ dom (chainCompose ϕs))
    (Ks : Fin k → GaugeMatrix I)
    (hKs : ∀ m : Fin k, Ks m ∈ RestrictedCoLipMatrices d (ϕs m) (chainDomain ϕs U₁ m.castSucc)) :
    matrixNonemptyProd hk Ks ∈ RestrictedCoLipMatrices d (chainCompose ϕs) U₁ :=
  chain_matrix_bound_ind
    (fun ϕ U M => M ∈ RestrictedCoLipMatrices d ϕ U)
    (fun ϕ₁ ϕ₂ _ _ _ hU h₁ h₂ => restrictedCoLipMatrices_comp d ϕ₁ ϕ₂ hU h₁ h₂)
    hk ϕs hU₁ Ks hKs

/-- Direct corollary of `CH02-P10` formulated via `OperatorChain` from Chapter 1. -/
theorem restrictedCoLipMatrices_operatorChain {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal)
    (chain : List (Operator X bot)) (hchain : chain ≠ [])
    {U₁ : Set X} (hU₁ : U₁ ⊆ dom (OperatorChain chain))
    (Ks : Fin chain.length → GaugeMatrix I)
    (hKs : ∀ m : Fin chain.length,
      Ks m ∈ RestrictedCoLipMatrices d (chainSteps chain m)
        (chainDomain (chainSteps chain) U₁ m.castSucc)) :
    matrixNonemptyProd (List.length_pos_of_ne_nil hchain) Ks ∈
      RestrictedCoLipMatrices d (OperatorChain chain) U₁ := by
  have h_eq : OperatorChain chain = chainCompose (chainSteps chain) :=
    operatorChain_eq_chainCompose_reverse chain
  rw [h_eq] at hU₁ ⊢
  exact restrictedCoLipMatrices_chain d (List.length_pos_of_ne_nil hchain) (chainSteps chain) hU₁ Ks hKs

end ChainDomainsAndFiniteComposition

end LCH02
