/-
Attribution: Formalization of material from Zhe Li (Glen Li / glenzli),
ORCID https://orcid.org/0009-0006-6536-3453,
The Operator Evolution Theory, Volume I, v1.0.0, https://glenzli.com/books/oet/,
licensed under CC BY 4.0.
-/
import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space
import LCH02.GaugeMatrix

namespace LCH02

open formal_oet.vol_01.ch_01_foundations

/--
**Definition (Global Lipschitz matrix)**:
A gauge matrix `L` is a valid global Lipschitz matrix for operator `ϕ` if for all
`x, y ∈ dom ϕ` and all output components `j ∈ I`,
`d_j(ϕ(x), ϕ(y)) ≤ ∑_{i ∈ I} L_{i → j} · d_i(x, y)`.
-/
def IsLipMatrix {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (L : GaugeMatrix I) : Prop :=
  ∀ x ∈ dom ϕ, ∀ y ∈ dom ϕ, ∀ j : I,
    d j (ϕ.func x) (ϕ.func y) ≤ ∑ i : I, matrixEntry L i j * d i x y

/-- The family `ℒ(ϕ)` of all valid global Lipschitz matrices for `ϕ`. -/
def LipFamily {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) : Set (GaugeMatrix I) :=
  { L | IsLipMatrix d ϕ L }

/--
**Definition (Subset-restricted Lipschitz matrix)**:
For a subset `U ⊆ dom ϕ`, `L` is a valid restricted Lipschitz matrix for `ϕ` on `U`
if `U ⊆ dom ϕ` and for all `x, y ∈ U` and all `j ∈ I`,
`d_j(ϕ(x), ϕ(y)) ≤ ∑_{i ∈ I} L_{i → j} · d_i(x, y)`.
-/
def IsRestrictedLipMatrix {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (L : GaugeMatrix I) : Prop :=
  U ⊆ dom ϕ ∧
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      d j (ϕ.func x) (ϕ.func y) ≤ ∑ i : I, matrixEntry L i j * d i x y

/-- The family `ℒ(ϕ)|_U` of all valid restricted Lipschitz matrices for `ϕ` on `U`. -/
def RestrictedLipFamily {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) : Set (GaugeMatrix I) :=
  { L | IsRestrictedLipMatrix d ϕ U L }

theorem isLipMatrix_iff_restricted_dom {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (L : GaugeMatrix I) :
    IsLipMatrix d ϕ L ↔ IsRestrictedLipMatrix d ϕ (dom ϕ) L := by
  simp [IsLipMatrix, IsRestrictedLipMatrix]

theorem lipFamily_eq_restricted_dom {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) :
    LipFamily d ϕ = RestrictedLipFamily d ϕ (dom ϕ) := by
  ext L
  exact isLipMatrix_iff_restricted_dom d ϕ L

/--
**Definition (Subset-restricted co-Lipschitz matrix)**:
For a nonempty subset `U ⊆ dom ϕ`, `K` is a valid restricted co-Lipschitz matrix for `ϕ` on `U`
if `U.Nonempty`, `U ⊆ dom ϕ`, and for all `x, y ∈ U` and all `j ∈ I`,
`∑_{i ∈ I} K_{i → j} · d_i(x, y) ≤ d_j(ϕ(x), ϕ(y))`.
Following §2.1, every appearance of `𝒦(ϕ)|_U` enforces the nonemptiness condition `U ≠ ∅`.
-/
def IsRestrictedCoLipMatrix {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (K : GaugeMatrix I) : Prop :=
  U.Nonempty ∧ U ⊆ dom ϕ ∧
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      (∑ i : I, matrixEntry K i j * d i x y) ≤ d j (ϕ.func x) (ϕ.func y)

/-- The family `𝒦(ϕ)|_U` of all valid restricted co-Lipschitz matrices for `ϕ` on `U`. -/
def RestrictedCoLipFamily {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) : Set (GaugeMatrix I) :=
  { K | IsRestrictedCoLipMatrix d ϕ U K }

theorem restrictedCoLipFamily_nonempty {X I : Type} {bot : X} [Fintype I]
    {d : I → X → X → ENNReal} {ϕ : Operator X bot} {U : Set X} {K : GaugeMatrix I}
    (hK : K ∈ RestrictedCoLipFamily d ϕ U) : U.Nonempty :=
  hK.1

theorem restrictedCoLipFamily_subset_dom {X I : Type} {bot : X} [Fintype I]
    {d : I → X → X → ENNReal} {ϕ : Operator X bot} {U : Set X} {K : GaugeMatrix I}
    (hK : K ∈ RestrictedCoLipFamily d ϕ U) : U ⊆ dom ϕ :=
  hK.2.1

theorem restrictedCoLipFamily_empty {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) :
    RestrictedCoLipFamily d ϕ ∅ = ∅ := by
  ext K
  simp [RestrictedCoLipFamily, IsRestrictedCoLipMatrix]

/--
**Remark (Scalar Lip bound in the single-component case)**:
When `I = {i}` (every index equals `i`), the Lip matrix condition degenerates to the
single scalar inequality `d_i(ϕ(x), ϕ(y)) ≤ L_{i → i} · d_i(x, y)` for `x, y ∈ dom ϕ`.
-/
theorem isLipMatrix_iff_scalar_of_singleton {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (L : GaugeMatrix I)
    (i : I) (hI : ∀ k : I, k = i) :
    IsLipMatrix d ϕ L ↔
      ∀ x ∈ dom ϕ, ∀ y ∈ dom ϕ, d i (ϕ.func x) (ϕ.func y) ≤ matrixEntry L i i * d i x y := by
  have huniv : (Finset.univ : Finset I) = {i} := by
    ext k
    simp [hI k]
  constructor
  · intro hL x hx y hy
    have h := hL x hx y hy i
    simpa [huniv] using h
  · intro hscalar x hx y hy j
    have hj : j = i := hI j
    subst hj
    simpa [huniv] using hscalar x hx y hy

/--
Single-component scalar Lip bound formulated directly with `Fintype.card I = 1` and `i : I`.
-/
theorem isLipMatrix_iff_scalar_of_card_one {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (L : GaugeMatrix I)
    (hcard : Fintype.card I = 1) (i : I) :
    IsLipMatrix d ϕ L ↔
      ∀ x ∈ dom ϕ, ∀ y ∈ dom ϕ, d i (ϕ.func x) (ϕ.func y) ≤ matrixEntry L i i * d i x y := by
  apply isLipMatrix_iff_scalar_of_singleton d ϕ L i
  intro k
  exact Fintype.card_le_one_iff.mp hcard.le k i

/-- Single-component scalar Lip bound for `[Unique I]`. -/
theorem isLipMatrix_iff_scalar_unique {X I : Type} {bot : X} [Fintype I] [Unique I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (L : GaugeMatrix I) :
    IsLipMatrix d ϕ L ↔
      ∀ x ∈ dom ϕ, ∀ y ∈ dom ϕ,
        d default (ϕ.func x) (ϕ.func y) ≤ matrixEntry L default default * d default x y :=
  isLipMatrix_iff_scalar_of_singleton d ϕ L default Unique.eq_default

/--
**Lemma 2.1 (Antimonotonicity of restricted Lip families)**:
If `U ⊆ V ⊆ dom ϕ`, then `ℒ(ϕ)|_V ⊆ ℒ(ϕ)|_U`.
-/
theorem restrictedLipFamily_antitone {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U V : Set X}
    (hUV : U ⊆ V) (hV : V ⊆ dom ϕ) :
    RestrictedLipFamily d ϕ V ⊆ RestrictedLipFamily d ϕ U := by
  intro L hL
  refine ⟨hUV.trans hV, ?_⟩
  intro x hx y hy j
  exact hL.2 x (hUV hx) y (hUV hy) j

/--
**Lemma 2.1 (Restriction of global Lip certificates)**:
For any `U ⊆ dom ϕ`, `ℒ(ϕ) ⊆ ℒ(ϕ)|_U`.
-/
theorem lipFamily_subset_restricted {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X}
    (hU : U ⊆ dom ϕ) :
    LipFamily d ϕ ⊆ RestrictedLipFamily d ϕ U := by
  rw [lipFamily_eq_restricted_dom]
  exact restrictedLipFamily_antitone d ϕ hU Set.Subset.rfl

/-- Domain inclusion for composition: `dom (ϕ₂ ∘ ϕ₁) ⊆ dom ϕ₁`. -/
theorem dom_mul_subset_dom_right {X : Type} {bot : X} (ϕ₁ ϕ₂ : Operator X bot) :
    dom (ϕ₂ * ϕ₁) ⊆ dom ϕ₁ := by
  intro x hx hbot
  apply hx
  change ϕ₂.func (ϕ₁.func x) = bot
  rw [hbot, ϕ₂.preserves_bot]

/-- Image-domain inclusion for composition: if `U₁ ⊆ dom (ϕ₂ ∘ ϕ₁)`, then `ϕ₁(U₁) ⊆ dom ϕ₂`. -/
theorem operator_image_subset_dom_left_of_subset_dom_mul {X : Type} {bot : X}
    (ϕ₁ ϕ₂ : Operator X bot) {U₁ : Set X}
    (hU₁ : U₁ ⊆ dom (ϕ₂ * ϕ₁)) :
    operator_image ϕ₁ U₁ ⊆ dom ϕ₂ := by
  rintro _ ⟨x, hx, rfl⟩
  exact hU₁ hx

/-- Exact characterization of subsets of `dom (ϕ₂ ∘ ϕ₁)`. -/
theorem subset_dom_mul_iff {X : Type} {bot : X}
    (ϕ₁ ϕ₂ : Operator X bot) (U₁ : Set X) :
    U₁ ⊆ dom (ϕ₂ * ϕ₁) ↔ U₁ ⊆ dom ϕ₁ ∧ operator_image ϕ₁ U₁ ⊆ dom ϕ₂ := by
  constructor
  · intro hU₁
    exact ⟨hU₁.trans (dom_mul_subset_dom_right ϕ₁ ϕ₂),
      operator_image_subset_dom_left_of_subset_dom_mul ϕ₁ ϕ₂ hU₁⟩
  · rintro ⟨_, hU₂⟩ x hx
    exact hU₂ ⟨x, hx, rfl⟩

/-- Nonemptiness is preserved by taking the operator image `ϕ(U)`. -/
theorem operator_image_nonempty {X : Type} {bot : X}
    (ϕ : Operator X bot) {U : Set X} (hU : U.Nonempty) :
    (operator_image ϕ U).Nonempty := by
  rcases hU with ⟨x, hx⟩
  exact ⟨ϕ.func x, x, hx, rfl⟩

/--
**Proposition 2.2 (Two-step Lip matrix composition law)**:
For `ϕ₂ ∘ ϕ₁` and `U₁ ⊆ dom (ϕ₂ ∘ ϕ₁)` with exact intermediate image `U₂ = ϕ₁(U₁)`,
if `L₁ ∈ ℒ(ϕ₁)|_{U₁}` and `L₂ ∈ ℒ(ϕ₂)|_{U₂}`, then `L₂ · L₁ ∈ ℒ(ϕ₂ ∘ ϕ₁)|_{U₁}`.
-/
theorem restrictedLipFamily_comp {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ₁ ϕ₂ : Operator X bot) {U₁ : Set X}
    (hU₁ : U₁ ⊆ dom (ϕ₂ * ϕ₁))
    {L₁ L₂ : GaugeMatrix I}
    (hL₁ : L₁ ∈ RestrictedLipFamily d ϕ₁ U₁)
    (hL₂ : L₂ ∈ RestrictedLipFamily d ϕ₂ (operator_image ϕ₁ U₁)) :
    gaugeMatrixMul L₂ L₁ ∈ RestrictedLipFamily d (ϕ₂ * ϕ₁) U₁ := by
  refine ⟨hU₁, ?_⟩
  intro x hx y hy j
  have hx₂ : ϕ₁.func x ∈ operator_image ϕ₁ U₁ := ⟨x, hx, rfl⟩
  have hy₂ : ϕ₁.func y ∈ operator_image ϕ₁ U₁ := ⟨y, hy, rfl⟩
  calc
    d j ((ϕ₂ * ϕ₁).func x) ((ϕ₂ * ϕ₁).func y)
        = d j (ϕ₂.func (ϕ₁.func x)) (ϕ₂.func (ϕ₁.func y)) := rfl
    _ ≤ ∑ k : I, matrixEntry L₂ k j * d k (ϕ₁.func x) (ϕ₁.func y) :=
        hL₂.2 (ϕ₁.func x) hx₂ (ϕ₁.func y) hy₂ j
    _ ≤ ∑ k : I, matrixEntry L₂ k j * (∑ i : I, matrixEntry L₁ i k * d i x y) := by
        refine Finset.sum_le_sum ?_
        intro k _
        exact mul_le_mul_of_nonneg_left (hL₁.2 x hx y hy k) (zero_le _)
    _ = ∑ k : I, ∑ i : I, matrixEntry L₂ k j * (matrixEntry L₁ i k * d i x y) := by
        refine Finset.sum_congr rfl ?_
        intro k _
        rw [Finset.mul_sum]
    _ = ∑ i : I, ∑ k : I, (matrixEntry L₂ k j * matrixEntry L₁ i k) * d i x y := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl ?_
        intro i _
        refine Finset.sum_congr rfl ?_
        intro k _
        rw [mul_assoc]
    _ = ∑ i : I, (∑ k : I, matrixEntry L₂ k j * matrixEntry L₁ i k) * d i x y := by
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [← Finset.sum_mul]
    _ = ∑ i : I, matrixEntry (gaugeMatrixMul L₂ L₁) i j * d i x y := by
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [matrixEntry_gaugeMatrixMul]

/--
**Lemma 2.3 (Antimonotonicity of nonempty restricted co-Lip families)**:
If `∅ ≠ U ⊆ V ⊆ dom ϕ`, then `𝒦(ϕ)|_V ⊆ 𝒦(ϕ)|_U`.
-/
theorem restrictedCoLipFamily_antitone {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U V : Set X}
    (hU_ne : U.Nonempty) (hUV : U ⊆ V) (hV : V ⊆ dom ϕ) :
    RestrictedCoLipFamily d ϕ V ⊆ RestrictedCoLipFamily d ϕ U := by
  intro K hK
  refine ⟨hU_ne, hUV.trans hV, ?_⟩
  intro x hx y hy j
  exact hK.2.2 x (hUV hx) y (hUV hy) j

/--
**Lemma 2.3 (Restriction of global co-Lip certificates)**:
For any nonempty subset `U ⊆ dom ϕ`, `𝒦(ϕ)|_{dom ϕ} ⊆ 𝒦(ϕ)|_U`.
-/
theorem globalCoLipFamily_subset_restricted {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X}
    (hU_ne : U.Nonempty) (hU : U ⊆ dom ϕ) :
    RestrictedCoLipFamily d ϕ (dom ϕ) ⊆ RestrictedCoLipFamily d ϕ U :=
  restrictedCoLipFamily_antitone d ϕ hU_ne hU Set.Subset.rfl

/--
**Remark (Sufficient condition for a restricted co-Lip entry to be zero)**:
If `K ∈ 𝒦(ϕ)|_U` and there exist `x, y ∈ U` with `d_j(ϕ(x), ϕ(y)) = 0` and `d_i(x, y) > 0`,
then `K_{i → j} = 0`.
-/
theorem restrictedCoLip_entry_eq_zero_of_collapse {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X}
    {K : GaugeMatrix I} (hK : K ∈ RestrictedCoLipFamily d ϕ U)
    {i j : I}
    (h_pair : ∃ x ∈ U, ∃ y ∈ U, d j (ϕ.func x) (ϕ.func y) = 0 ∧ 0 < d i x y) :
    matrixEntry K i j = 0 := by
  rcases h_pair with ⟨x, hx, y, hy, hzero, hpos⟩
  have hterm_le_sum :
      matrixEntry K i j * d i x y ≤ ∑ k : I, matrixEntry K k j * d k x y :=
    Finset.single_le_sum (fun k _ => zero_le (matrixEntry K k j * d k x y)) (Finset.mem_univ i)
  have hprod_le_zero : matrixEntry K i j * d i x y ≤ 0 := by
    calc
      matrixEntry K i j * d i x y
          ≤ ∑ k : I, matrixEntry K k j * d k x y := hterm_le_sum
      _ ≤ d j (ϕ.func x) (ϕ.func y) := hK.2.2 x hx y hy j
      _ = 0 := hzero
  have hprod_eq_zero : matrixEntry K i j * d i x y = 0 :=
    le_antisymm hprod_le_zero (zero_le _)
  rcases mul_eq_zero.mp hprod_eq_zero with hK0 | hd0
  · exact hK0
  · exact absurd hd0 (ne_of_gt hpos)

/--
**Remark (Sufficient condition for a global co-Lip entry to be zero)**:
If there exist `x, y ∈ dom ϕ` with `d_j(ϕ(x), ϕ(y)) = 0` and `d_i(x, y) > 0`,
then every global co-Lip matrix `K ∈ 𝒦(ϕ)|_{dom ϕ}` satisfies `K_{i → j} = 0`.
-/
theorem globalCoLip_entry_eq_zero_of_collapse {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    {K : GaugeMatrix I} (hK : K ∈ RestrictedCoLipFamily d ϕ (dom ϕ))
    {i j : I}
    (h_pair : ∃ x ∈ dom ϕ, ∃ y ∈ dom ϕ, d j (ϕ.func x) (ϕ.func y) = 0 ∧ 0 < d i x y) :
    matrixEntry K i j = 0 :=
  restrictedCoLip_entry_eq_zero_of_collapse d ϕ hK h_pair

/--
**Proposition 2.4 (Two-step co-Lip matrix composition law)**:
For `ϕ₂ ∘ ϕ₁` and `U₁ ⊆ dom (ϕ₂ ∘ ϕ₁)` with exact intermediate image `U₂ = ϕ₁(U₁)`,
if `K₁ ∈ 𝒦(ϕ₁)|_{U₁}` and `K₂ ∈ 𝒦(ϕ₂)|_{U₂}` (both carrying nonemptiness),
then `K₂ · K₁ ∈ 𝒦(ϕ₂ ∘ ϕ₁)|_{U₁}`.
-/
theorem restrictedCoLipFamily_comp {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ₁ ϕ₂ : Operator X bot) {U₁ : Set X}
    (hU₁ : U₁ ⊆ dom (ϕ₂ * ϕ₁))
    {K₁ K₂ : GaugeMatrix I}
    (hK₁ : K₁ ∈ RestrictedCoLipFamily d ϕ₁ U₁)
    (hK₂ : K₂ ∈ RestrictedCoLipFamily d ϕ₂ (operator_image ϕ₁ U₁)) :
    gaugeMatrixMul K₂ K₁ ∈ RestrictedCoLipFamily d (ϕ₂ * ϕ₁) U₁ := by
  refine ⟨hK₁.1, hU₁, ?_⟩
  intro x hx y hy j
  have hx₂ : ϕ₁.func x ∈ operator_image ϕ₁ U₁ := ⟨x, hx, rfl⟩
  have hy₂ : ϕ₁.func y ∈ operator_image ϕ₁ U₁ := ⟨y, hy, rfl⟩
  calc
    ∑ i : I, matrixEntry (gaugeMatrixMul K₂ K₁) i j * d i x y
        = ∑ i : I, (∑ k : I, matrixEntry K₂ k j * matrixEntry K₁ i k) * d i x y := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [matrixEntry_gaugeMatrixMul]
    _ = ∑ i : I, ∑ k : I, (matrixEntry K₂ k j * matrixEntry K₁ i k) * d i x y := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [Finset.sum_mul]
    _ = ∑ k : I, ∑ i : I, matrixEntry K₂ k j * (matrixEntry K₁ i k * d i x y) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl ?_
          intro k _
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [mul_assoc]
    _ = ∑ k : I, matrixEntry K₂ k j * (∑ i : I, matrixEntry K₁ i k * d i x y) := by
          refine Finset.sum_congr rfl ?_
          intro k _
          rw [← Finset.mul_sum]
    _ ≤ ∑ k : I, matrixEntry K₂ k j * d k (ϕ₁.func x) (ϕ₁.func y) := by
          refine Finset.sum_le_sum ?_
          intro k _
          exact mul_le_mul_of_nonneg_left (hK₁.2.2 x hx y hy k) (zero_le _)
    _ ≤ d j (ϕ₂.func (ϕ₁.func x)) (ϕ₂.func (ϕ₁.func y)) :=
          hK₂.2.2 (ϕ₁.func x) hx₂ (ϕ₁.func y) hy₂ j
    _ = d j ((ϕ₂ * ϕ₁).func x) ((ϕ₂ * ϕ₁).func y) := rfl

/-- Exact evaluation identity for the identity gauge matrix on any distance family. -/
theorem sum_idMatrix_mul_dist {X I : Type} [Fintype I] [DecidableEq I]
    (d : I → X → X → ENNReal) (x y : X) (j : I) :
    (∑ i : I, matrixEntry (idMatrix : GaugeMatrix I) i j * d i x y) = d j x y := by
  simp only [matrixEntry_idMatrix]
  simp

/--
**Remark (Zero-step identity operator — Lip certificate)**:
For any `U ⊆ dom id_X`, the identity matrix satisfies `I ∈ ℒ(id_X)|_U`.
-/
theorem idMatrix_mem_restrictedLipFamily_identity {X I : Type} {bot : X}
    [Fintype I] [DecidableEq I]
    (d : I → X → X → ENNReal) {U : Set X}
    (hU : U ⊆ dom (operator_identity (X := X) (bot := bot))) :
    idMatrix ∈ RestrictedLipFamily d (operator_identity (X := X) (bot := bot)) U := by
  refine ⟨hU, ?_⟩
  intro x _ y _ j
  change d j x y ≤ ∑ i : I, matrixEntry (idMatrix : GaugeMatrix I) i j * d i x y
  rw [sum_idMatrix_mul_dist]

/-- Global Lip certificate for the identity operator: `I ∈ ℒ(id_X)`. -/
theorem idMatrix_mem_lipFamily_identity {X I : Type} {bot : X}
    [Fintype I] [DecidableEq I]
    (d : I → X → X → ENNReal) :
    idMatrix ∈ LipFamily d (operator_identity (X := X) (bot := bot)) := by
  rw [lipFamily_eq_restricted_dom]
  exact idMatrix_mem_restrictedLipFamily_identity d Set.Subset.rfl

/--
**Remark (Zero-step identity operator — co-Lip certificate)**:
For any nonempty `U ⊆ dom id_X`, the identity matrix satisfies `I ∈ 𝒦(id_X)|_U`.
-/
theorem idMatrix_mem_restrictedCoLipFamily_identity {X I : Type} {bot : X}
    [Fintype I] [DecidableEq I]
    (d : I → X → X → ENNReal) {U : Set X}
    (hU_ne : U.Nonempty)
    (hU : U ⊆ dom (operator_identity (X := X) (bot := bot))) :
    idMatrix ∈ RestrictedCoLipFamily d (operator_identity (X := X) (bot := bot)) U := by
  refine ⟨hU_ne, hU, ?_⟩
  intro x _ y _ j
  change (∑ i : I, matrixEntry (idMatrix : GaugeMatrix I) i j * d i x y) ≤ d j x y
  rw [sum_idMatrix_mul_dist]

/--
Combined zero-step identity remark:
for any nonempty `U ⊆ dom id_X`, `I ∈ ℒ(id_X)|_U ∩ 𝒦(id_X)|_U`.
-/
theorem idMatrix_mem_restrictedLip_inter_coLip_identity {X I : Type} {bot : X}
    [Fintype I] [DecidableEq I]
    (d : I → X → X → ENNReal) {U : Set X}
    (hU_ne : U.Nonempty)
    (hU : U ⊆ dom (operator_identity (X := X) (bot := bot))) :
    idMatrix ∈
      RestrictedLipFamily d (operator_identity (X := X) (bot := bot)) U ∩
        RestrictedCoLipFamily d (operator_identity (X := X) (bot := bot)) U :=
  ⟨idMatrix_mem_restrictedLipFamily_identity d hU,
    idMatrix_mem_restrictedCoLipFamily_identity d hU_ne hU⟩

end LCH02
