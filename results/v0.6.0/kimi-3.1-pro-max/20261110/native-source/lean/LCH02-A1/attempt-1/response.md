以下交付基于 Zhe Li（Glen Li）的 *The Operator Evolution Theory* 选段，原作品采用 [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/) 许可。

已使用指定 Lean/mathlib 环境完成 `lake build Main`；全部 20 项义务均为 `complete`。主定理的公理审计仅包含 `propext`、`Classical.choice`、`Quot.sound`，未使用 `sorry`、`admit` 或新增公理。

```lean filename=Main.lean
import OperatorBounds
import MatrixPaths

/-!
Entry point for the LCH02 deliverable.  All target modules are imported here.
The selected Chapter 2 declarations live in
`formal_oet.vol_01.ch_02_operator_bounds`.
-/
```

```lean filename=OperatorBounds.lean
import formal_oet.vol_01.ch_01_foundations.operator_space
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Operator bounds

This file formalizes the selected definitions and results from Chapter 2.
Matrices use the textbook convention: rows are output components and columns
are input components.  Thus `channelEntry L i j` is the entry `L_{i → j}`.
-/

namespace formal_oet.vol_01.ch_02_operator_bounds

open formal_oet.vol_01.ch_01_foundations
open scoped BigOperators Classical

/-- An extended nonnegative matrix on the component index set. -/
abbrev ChannelMatrix (I : Type) := Matrix I I ENNReal

/-- The coefficient of input channel `i` in output channel `j`.
This is row `j`, column `i` of the underlying matrix. -/
def channelEntry {I : Type} (L : ChannelMatrix I) (i j : I) : ENNReal := L j i

@[simp] theorem channelEntry_apply {I : Type} (L : ChannelMatrix I) (i j : I) :
    channelEntry L i j = L j i := rfl

/-- Expansion of ordinary matrix multiplication in channel notation. -/
theorem channelEntry_mul {I : Type} [Fintype I] (A B : ChannelMatrix I) (i j : I) :
    channelEntry (A * B) i j = ∑ k : I, channelEntry A k j * channelEntry B i k := by
  rfl

/-- The unit matrix has exactly the diagonal unit channels. -/
theorem channelEntry_one {I : Type} [DecidableEq I] (i j : I) :
    channelEntry (1 : ChannelMatrix I) i j = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst j
    simp [channelEntry, Matrix.one_apply]
  · have h' : j ≠ i := Ne.symm h
    simp [channelEntry, Matrix.one_apply, h, h']

/-- Ordered product for matrices listed in their order of application.
For example, `orderedMatrixProduct [M₁, M₂, M₃] = M₃ * M₂ * M₁`.
The empty product is the unit matrix. -/
noncomputable def orderedMatrixProduct {I : Type} [Fintype I] : List (ChannelMatrix I) → ChannelMatrix I
  | [] => 1
  | M :: Ms => orderedMatrixProduct Ms * M

@[simp] theorem orderedMatrixProduct_nil {I : Type} [Fintype I] :
    orderedMatrixProduct ([] : List (ChannelMatrix I)) = 1 := rfl

@[simp] theorem orderedMatrixProduct_cons {I : Type} [Fintype I] (M : ChannelMatrix I)
    (Ms : List (ChannelMatrix I)) :
    orderedMatrixProduct (M :: Ms) = orderedMatrixProduct Ms * M := rfl

@[simp] theorem orderedMatrixProduct_singleton {I : Type} [Fintype I] (M : ChannelMatrix I) :
    orderedMatrixProduct [M] = M := by
  simp

/-- Restricted Lipschitz matrices.  The domain restriction is part of the
certificate, exactly as in the definition of `mathscr L(φ)|_U`. -/
def IsRestrictedLipMatrix {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X)
    (L : ChannelMatrix I) : Prop :=
  U ⊆ dom φ ∧
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      d j (φ.func x) (φ.func y) ≤ ∑ i : I, channelEntry L i j * d i x y

/-- Global Lipschitz matrices are restricted to the whole domain. -/
def IsGlobalLipMatrix {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (φ : Operator X bot) (L : ChannelMatrix I) : Prop :=
  IsRestrictedLipMatrix d φ (dom φ) L

/-- The family of restricted Lipschitz certificates. -/
def lipCertificates {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) :
    Set (ChannelMatrix I) := {L | IsRestrictedLipMatrix d φ U L}

/-- The family of global Lipschitz certificates. -/
def globalLipCertificates {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (φ : Operator X bot) : Set (ChannelMatrix I) :=
  {L | IsGlobalLipMatrix d φ L}

/-- Restricted co-Lipschitz matrices.  Both `U ⊆ dom φ` and `U.Nonempty`
are part of the certificate predicate. -/
def IsRestrictedCoLipMatrix {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X)
    (K : ChannelMatrix I) : Prop :=
  U.Nonempty ∧ U ⊆ dom φ ∧
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      ∑ i : I, channelEntry K i j * d i x y ≤ d j (φ.func x) (φ.func y)

/-- Global co-Lipschitz matrices; in particular, the domain is nonempty. -/
def IsGlobalCoLipMatrix {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (φ : Operator X bot) (K : ChannelMatrix I) : Prop :=
  IsRestrictedCoLipMatrix d φ (dom φ) K

/-- The family of restricted co-Lipschitz certificates. -/
def coLipCertificates {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) :
    Set (ChannelMatrix I) := {K | IsRestrictedCoLipMatrix d φ U K}

/-- The family of global co-Lipschitz certificates. -/
def globalCoLipCertificates {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (φ : Operator X bot) : Set (ChannelMatrix I) :=
  {K | IsGlobalCoLipMatrix d φ K}

/-- Finite composition in order of application: `[φ₁, φ₂, …, φₖ]`
represents `φₖ ∘ … ∘ φ₂ ∘ φ₁`; the empty list represents the identity. -/
def finiteComposition {X : Type} {bot : X} : List (Operator X bot) → Operator X bot
  | [] => operator_identity
  | φ :: φs => operator_compose (finiteComposition φs) φ

@[simp] theorem finiteComposition_nil {X : Type} {bot : X} :
    finiteComposition ([] : List (Operator X bot)) = operator_identity := rfl

@[simp] theorem finiteComposition_cons {X : Type} {bot : X} (φ : Operator X bot)
    (φs : List (Operator X bot)) :
    finiteComposition (φ :: φs) = operator_compose (finiteComposition φs) φ := rfl

@[simp] theorem finiteComposition_singleton {X : Type} {bot : X} (φ : Operator X bot) :
    finiteComposition [φ] = φ := rfl

/-- The chronological-list representation agrees with the frozen
`OperatorChain` implementation after reversing the list. -/
theorem finiteComposition_eq_operatorChain_reverse {X : Type} {bot : X}
    (φs : List (Operator X bot)) :
    finiteComposition φs = OperatorChain φs.reverse := by
  rw [operator_chain_eq_prod]
  induction φs with
  | nil => rfl
  | cons φ φs ih =>
      change operator_compose (finiteComposition φs) φ = (φ :: φs).reverse.prod
      rw [List.reverse_cons, List.prod_append]
      change finiteComposition φs * φ = φs.reverse.prod * [φ].prod
      rw [ih]
      rfl

/-- The actual intermediate image sets `U₁, …, Uₖ, Uₖ₊₁`. -/
def intermediateImages {X : Type} {bot : X} :
    List (Operator X bot) → Set X → List (Set X)
  | [], U => [U]
  | φ :: φs, U => U :: intermediateImages φs (φ.func '' U)

@[simp] theorem intermediateImages_nil {X : Type} {bot : X} (U : Set X) :
    intermediateImages ([] : List (Operator X bot)) U = [U] := rfl

@[simp] theorem intermediateImages_cons {X : Type} {bot : X} (φ : Operator X bot)
    (φs : List (Operator X bot)) (U : Set X) :
    intermediateImages (φ :: φs) U = U :: intermediateImages φs (φ.func '' U) := rfl

/-- There are `k + 1` actual image sets for a chain of length `k`. -/
theorem intermediateImages_length {X : Type} {bot : X}
    (φs : List (Operator X bot)) (U : Set X) :
    (intermediateImages φs U).length = φs.length + 1 := by
  induction φs generalizing U with
  | nil => rfl
  | cons φ φs ih =>
      simp only [intermediateImages_cons, List.length_cons, List.length]
      rw [ih]

/-- Stepwise Lip certificates, indexed recursively by the actual image sets. -/
def StepwiseLipCertificates {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) :
    (φs : List (Operator X bot)) → List (ChannelMatrix I) → Set X → Prop
  | [], [], _ => True
  | φ :: φs, L :: Ls, U =>
      IsRestrictedLipMatrix d φ U L ∧
        StepwiseLipCertificates d φs Ls (φ.func '' U)
  | _, _, _ => False

/-- Stepwise co-Lip certificates on the same actual image sets. -/
def StepwiseCoLipCertificates {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) :
    (φs : List (Operator X bot)) → List (ChannelMatrix I) → Set X → Prop
  | [], [], _ => True
  | φ :: φs, K :: Ks, U =>
      IsRestrictedCoLipMatrix d φ U K ∧
        StepwiseCoLipCertificates d φs Ks (φ.func '' U)
  | _, _, _ => False

/-- Passing to the image of the initial set leaves a subset of the domain
of the remaining composition. -/
theorem image_subset_dom_finiteComposition_tail {X : Type} {bot : X}
    (φ : Operator X bot) (φs : List (Operator X bot)) {U : Set X}
    (hU : U ⊆ dom (finiteComposition (φ :: φs))) :
    φ.func '' U ⊆ dom (finiteComposition φs) := by
  rintro y ⟨x, hx, rfl⟩
  exact hU hx

/-- A one-component sum is the corresponding scalar channel bound. -/
theorem unique_sum_channelEntry {I : Type} [Fintype I] [Unique I]
    (L : ChannelMatrix I) (f : I → ENNReal) :
    (∑ i : I, channelEntry L i default * f i) =
      channelEntry L default default * f default := by
  exact Fintype.sum_unique _

/-- On a singleton component index type, the restricted Lip condition is
exactly the displayed scalar inequality (together with its domain condition). -/
theorem isRestrictedLipMatrix_unique_iff {X I : Type} {bot : X}
    [Fintype I] [Unique I]
    (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X)
    (L : ChannelMatrix I) :
    IsRestrictedLipMatrix d φ U L ↔
      U ⊆ dom φ ∧ ∀ x ∈ U, ∀ y ∈ U,
        d default (φ.func x) (φ.func y) ≤
          channelEntry L default default * d default x y := by
  constructor
  · rintro ⟨hU, hL⟩
    refine ⟨hU, ?_⟩
    intro x hx y hy
    simpa only [unique_sum_channelEntry] using hL x hx y hy default
  · rintro ⟨hU, hL⟩
    refine ⟨hU, ?_⟩
    intro x hx y hy j
    have hj : j = default := Subsingleton.elim _ _
    subst j
    simpa only [unique_sum_channelEntry] using hL x hx y hy

/-- Global form of the one-component scalar simplification. -/
theorem isGlobalLipMatrix_unique_iff {X I : Type} {bot : X}
    [Fintype I] [Unique I]
    (d : I → X → X → ENNReal) (φ : Operator X bot) (L : ChannelMatrix I) :
    IsGlobalLipMatrix d φ L ↔ ∀ x ∈ dom φ, ∀ y ∈ dom φ,
      d default (φ.func x) (φ.func y) ≤
        channelEntry L default default * d default x y := by
  change IsRestrictedLipMatrix d φ (dom φ) L ↔ _
  rw [isRestrictedLipMatrix_unique_iff]
  simp

/-- Restricted Lip certificate families are reverse monotone in the domain. -/
theorem lipCertificates_antitone {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (φ : Operator X bot) {U V : Set X}
    (hUV : U ⊆ V) (hV : V ⊆ dom φ) :
    lipCertificates d φ V ⊆ lipCertificates d φ U := by
  intro L hL
  refine ⟨hUV.trans hV, ?_⟩
  intro x hx y hy j
  exact hL.2 x (hUV hx) y (hUV hy) j

/-- Every global Lip certificate restricts to any subset of the domain. -/
theorem globalLip_mem_lipCertificates {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (φ : Operator X bot) {U : Set X}
    (hU : U ⊆ dom φ) {L : ChannelMatrix I}
    (hL : L ∈ globalLipCertificates d φ) :
    L ∈ lipCertificates d φ U := by
  exact lipCertificates_antitone d φ hU (fun _ h => h) hL

/-- Restricted co-Lip certificate families are reverse monotone, with the
nonemptiness of the smaller set retained. -/
theorem coLipCertificates_antitone {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (φ : Operator X bot) {U V : Set X}
    (hUne : U.Nonempty) (hUV : U ⊆ V) (hV : V ⊆ dom φ) :
    coLipCertificates d φ V ⊆ coLipCertificates d φ U := by
  intro K hK
  refine ⟨hUne, hUV.trans hV, ?_⟩
  intro x hx y hy j
  exact hK.2.2 x (hUV hx) y (hUV hy) j

/-- Every global co-Lip certificate restricts to a nonempty domain subset. -/
theorem globalCoLip_mem_coLipCertificates {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (φ : Operator X bot) {U : Set X}
    (hUne : U.Nonempty) (hU : U ⊆ dom φ) {K : ChannelMatrix I}
    (hK : K ∈ globalCoLipCertificates d φ) :
    K ∈ coLipCertificates d φ U := by
  exact coLipCertificates_antitone d φ hUne hU (fun _ h => h) hK

/-- Algebra behind both two-step composition laws. -/
theorem sum_channelEntry_mul {I : Type} [Fintype I]
    (A B : ChannelMatrix I) (j : I) (f : I → ENNReal) :
    (∑ i : I, channelEntry (A * B) i j * f i) =
      ∑ k : I, channelEntry A k j * (∑ i : I, channelEntry B i k * f i) := by
  simp_rw [channelEntry_mul, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

/-- Two-step Lip composition, with the exact intermediate image domain and
with `L₂ * L₁` in the stated order. -/
theorem lip_compose_two {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (φ₂ φ₁ : Operator X bot) {U : Set X}
    (hU : U ⊆ dom (operator_compose φ₂ φ₁)) {L₁ L₂ : ChannelMatrix I}
    (h₁ : L₁ ∈ lipCertificates d φ₁ U)
    (h₂ : L₂ ∈ lipCertificates d φ₂ (φ₁.func '' U)) :
    L₂ * L₁ ∈ lipCertificates d (operator_compose φ₂ φ₁) U := by
  refine ⟨hU, ?_⟩
  intro x hx y hy j
  calc
    d j ((operator_compose φ₂ φ₁).func x) ((operator_compose φ₂ φ₁).func y)
        ≤ ∑ k : I, channelEntry L₂ k j * d k (φ₁.func x) (φ₁.func y) :=
      h₂.2 (φ₁.func x) ⟨x, hx, rfl⟩ (φ₁.func y) ⟨y, hy, rfl⟩ j
    _ ≤ ∑ k : I, channelEntry L₂ k j *
          (∑ i : I, channelEntry L₁ i k * d i x y) := by
      exact Finset.sum_le_sum fun k _ =>
        mul_le_mul_left' (h₁.2 x hx y hy k) (channelEntry L₂ k j)
    _ = ∑ i : I, channelEntry (L₂ * L₁) i j * d i x y := by
      rw [sum_channelEntry_mul]

/-- Two-step co-Lip composition, retaining nonemptiness and the exact
intermediate image domain. -/
theorem coLip_compose_two {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (φ₂ φ₁ : Operator X bot) {U : Set X}
    (hU : U ⊆ dom (operator_compose φ₂ φ₁)) {K₁ K₂ : ChannelMatrix I}
    (h₁ : K₁ ∈ coLipCertificates d φ₁ U)
    (h₂ : K₂ ∈ coLipCertificates d φ₂ (φ₁.func '' U)) :
    K₂ * K₁ ∈ coLipCertificates d (operator_compose φ₂ φ₁) U := by
  refine ⟨h₁.1, hU, ?_⟩
  intro x hx y hy j
  calc
    (∑ i : I, channelEntry (K₂ * K₁) i j * d i x y) =
        ∑ k : I, channelEntry K₂ k j *
          (∑ i : I, channelEntry K₁ i k * d i x y) := sum_channelEntry_mul _ _ _ _
    _ ≤ ∑ k : I, channelEntry K₂ k j * d k (φ₁.func x) (φ₁.func y) := by
      exact Finset.sum_le_sum fun k _ =>
        mul_le_mul_left' (h₁.2.2 x hx y hy k) (channelEntry K₂ k j)
    _ ≤ d j ((operator_compose φ₂ φ₁).func x) ((operator_compose φ₂ φ₁).func y) :=
      h₂.2.2 (φ₁.func x) ⟨x, hx, rfl⟩ (φ₁.func y) ⟨y, hy, rfl⟩ j

/-- A zero output distance together with a positive input distance forces
the corresponding entry of every global co-Lip certificate to vanish. -/
theorem channelEntry_eq_zero_of_output_zero_input_pos {X I : Type} {bot : X}
    [Fintype I] (d : I → X → X → ENNReal) (φ : Operator X bot)
    {K : ChannelMatrix I} (hK : K ∈ globalCoLipCertificates d φ)
    {x y : X} (hx : x ∈ dom φ) (hy : y ∈ dom φ) {i j : I}
    (hout : d j (φ.func x) (φ.func y) = 0) (hin : 0 < d i x y) :
    channelEntry K i j = 0 := by
  have hterm : channelEntry K i j * d i x y ≤
      ∑ k : I, channelEntry K k j * d k x y := by
    exact Finset.single_le_sum (fun k _ => zero_le (channelEntry K k j * d k x y))
      (Finset.mem_univ i)
  have hbound := hK.2.2 x hx y hy j
  rw [hout] at hbound
  have hz : channelEntry K i j * d i x y = 0 :=
    le_antisymm (hterm.trans hbound) (zero_le _)
  rcases mul_eq_zero.mp hz with hKi | hdi
  · exact hKi
  · exact (ne_of_gt hin hdi).elim

/-- The unit matrix collapses a channel sum to its diagonal term. -/
theorem sum_channelEntry_one {I : Type} [Fintype I] (f : I → ENNReal) (j : I) :
    (∑ i : I, channelEntry (1 : ChannelMatrix I) i j * f i) = f j := by
  classical
  calc
    (∑ i : I, channelEntry (1 : ChannelMatrix I) i j * f i) =
        ∑ i : I, if i = j then f i else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases h : i = j
      · subst i
        simp [channelEntry, Matrix.one_apply]
      · have h' : j ≠ i := Ne.symm h
        simp [channelEntry, Matrix.one_apply, h, h']
    _ = f j := by simp

/-- Zero-step composition: the empty ordered matrix product is a Lip
certificate for the identity operator. -/
theorem zeroStep_identity_lip {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) {U : Set X} (hUne : U.Nonempty)
    (hU : U ⊆ dom (finiteComposition ([] : List (Operator X bot)))) :
    orderedMatrixProduct ([] : List (ChannelMatrix I)) ∈
      lipCertificates d (finiteComposition ([] : List (Operator X bot))) U := by
  refine ⟨hU, ?_⟩
  intro x hx y hy j
  change d j x y ≤ ∑ i : I, channelEntry (1 : ChannelMatrix I) i j * d i x y
  rw [sum_channelEntry_one]

/-- Zero-step composition: the same empty product/unit matrix is a co-Lip
certificate for the identity operator. -/
theorem zeroStep_identity_coLip {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) {U : Set X} (hUne : U.Nonempty)
    (hU : U ⊆ dom (finiteComposition ([] : List (Operator X bot)))) :
    orderedMatrixProduct ([] : List (ChannelMatrix I)) ∈
      coLipCertificates d (finiteComposition ([] : List (Operator X bot))) U := by
  refine ⟨hUne, hU, ?_⟩
  intro x hx y hy j
  change (∑ i : I, channelEntry (1 : ChannelMatrix I) i j * d i x y) ≤ d j x y
  rw [sum_channelEntry_one]

/-- The ordered product of stepwise Lip certificates certifies every
nonempty finite composition chain. -/
theorem finiteComposition_lip {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) {φs : List (Operator X bot)}
    (hφs : φs ≠ []) {U : Set X} (hU : U ⊆ dom (finiteComposition φs))
    {Ls : List (ChannelMatrix I)} (hLs : StepwiseLipCertificates d φs Ls U) :
    orderedMatrixProduct Ls ∈ lipCertificates d (finiteComposition φs) U := by
  induction φs generalizing U Ls with
  | nil => exact (hφs rfl).elim
  | cons φ φs ih =>
      cases Ls with
      | nil => exact False.elim hLs
      | cons L Ls =>
          rcases hLs with ⟨hL, hLs⟩
          cases φs with
          | nil =>
              cases Ls with
              | nil => simpa using hL
              | cons L' Ls' => exact False.elim hLs
          | cons ψ ψs =>
              have htailU : φ.func '' U ⊆ dom (finiteComposition (ψ :: ψs)) :=
                image_subset_dom_finiteComposition_tail φ (ψ :: ψs) hU
              have htail : orderedMatrixProduct Ls ∈
                  lipCertificates d (finiteComposition (ψ :: ψs)) (φ.func '' U) :=
                ih (List.cons_ne_nil ψ ψs) htailU hLs
              exact lip_compose_two d (finiteComposition (ψ :: ψs)) φ hU hL htail

/-- The ordered product of stepwise co-Lip certificates certifies every
nonempty finite composition chain. -/
theorem finiteComposition_coLip {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) {φs : List (Operator X bot)}
    (hφs : φs ≠ []) {U : Set X} (hU : U ⊆ dom (finiteComposition φs))
    {Ks : List (ChannelMatrix I)} (hKs : StepwiseCoLipCertificates d φs Ks U) :
    orderedMatrixProduct Ks ∈ coLipCertificates d (finiteComposition φs) U := by
  induction φs generalizing U Ks with
  | nil => exact (hφs rfl).elim
  | cons φ φs ih =>
      cases Ks with
      | nil => exact False.elim hKs
      | cons K Ks =>
          rcases hKs with ⟨hK, hKs⟩
          cases φs with
          | nil =>
              cases Ks with
              | nil => simpa using hK
              | cons K' Ks' => exact False.elim hKs
          | cons ψ ψs =>
              have htailU : φ.func '' U ⊆ dom (finiteComposition (ψ :: ψs)) :=
                image_subset_dom_finiteComposition_tail φ (ψ :: ψs) hU
              have htail : orderedMatrixProduct Ks ∈
                  coLipCertificates d (finiteComposition (ψ :: ψs)) (φ.func '' U) :=
                ih (List.cons_ne_nil ψ ψs) htailU hKs
              exact coLip_compose_two d (finiteComposition (ψ :: ψs)) φ hU hK htail

end formal_oet.vol_01.ch_02_operator_bounds
```

```lean filename=MatrixPaths.lean
import OperatorBounds
import Mathlib.Algebra.BigOperators.Ring.List

/-!
# Finite matrix products and component-index paths

An index path stores only its intermediate vertices.  For a list of `n`
matrices it has length `n - 1`; in particular the unique path for one matrix
is empty.  Its factors use the same input/output convention as `channelEntry`.
-/

namespace formal_oet.vol_01.ch_02_operator_bounds

open scoped BigOperators Classical

/-- Adjacent directed edges of a vertex list. -/
def adjacentPairs {I : Type} : List I → List (I × I)
  | [] => []
  | [_] => []
  | a :: b :: rest => (a, b) :: adjacentPairs (b :: rest)

/-- The full vertex list determined by endpoints and intermediate vertices. -/
def pathVertices {I : Type} (i j : I) (p : List I) : List I := i :: (p ++ [j])

/-- The channel entries along a path, in order of application. -/
def pathFactors {I : Type} (Ms : List (ChannelMatrix I)) (i j : I) (p : List I) :
    List ENNReal :=
  List.zipWith (fun M e => channelEntry M e.1 e.2) Ms
    (adjacentPairs (pathVertices i j p))

/-- Product of all channel entries along a path. -/
noncomputable def pathWeight {I : Type} (Ms : List (ChannelMatrix I)) (i j : I) (p : List I) : ENNReal :=
  (pathFactors Ms i j p).prod

/-- A finite index path has exactly one fewer intermediate vertex than the
number of matrices. -/
def IsIndexPath {I : Type} (Ms : List (ChannelMatrix I)) (p : List I) : Prop :=
  p.length + 1 = Ms.length

/-- A valid path is all-positive when every one-step entry is strictly positive. -/
def IsAllPositivePath {I : Type} (Ms : List (ChannelMatrix I)) (i j : I) (p : List I) : Prop :=
  IsIndexPath Ms p ∧ ∀ a ∈ pathFactors Ms i j p, 0 < a

@[simp] theorem pathWeight_singleton {I : Type} (M : ChannelMatrix I) (i j : I) :
    pathWeight [M] i j [] = channelEntry M i j := by
  simp [pathWeight, pathFactors, pathVertices, adjacentPairs]

@[simp] theorem pathFactors_singleton {I : Type} (M : ChannelMatrix I) (i j : I) :
    pathFactors [M] i j [] = [channelEntry M i j] := by
  simp [pathFactors, pathVertices, adjacentPairs]

/-- Split the first edge from a path through at least two matrices. -/
theorem pathFactors_cons_two {I : Type} (M N : ChannelMatrix I)
    (Ms : List (ChannelMatrix I)) (i j k : I) (p : List I) :
    pathFactors (M :: N :: Ms) i j (k :: p) =
      channelEntry M i k :: pathFactors (N :: Ms) k j p := by
  simp [pathFactors, pathVertices, adjacentPairs]

/-- Multiplicative form of `pathFactors_cons_two`. -/
theorem pathWeight_cons_two {I : Type} (M N : ChannelMatrix I)
    (Ms : List (ChannelMatrix I)) (i j k : I) (p : List I) :
    pathWeight (M :: N :: Ms) i j (k :: p) =
      channelEntry M i k * pathWeight (N :: Ms) k j p := by
  simp [pathWeight, pathFactors_cons_two]

@[simp] theorem isIndexPath_singleton_iff {I : Type} (M : ChannelMatrix I) (p : List I) :
    IsIndexPath [M] p ↔ p = [] := by
  constructor
  · intro h
    apply List.length_eq_zero_iff.mp
    unfold IsIndexPath at h
    simp only [List.length_cons, List.length_nil] at h
    omega
  · rintro rfl
    rfl

@[simp] theorem isIndexPath_cons_two_iff {I : Type} (M N : ChannelMatrix I)
    (Ms : List (ChannelMatrix I)) (k : I) (p : List I) :
    IsIndexPath (M :: N :: Ms) (k :: p) ↔ IsIndexPath (N :: Ms) p := by
  unfold IsIndexPath
  simp only [List.length_cons, List.length_nil]
  omega

/-- In a canonically ordered semiring with no zero divisors, a path product
is positive exactly when all its factors are positive. -/
theorem pathWeight_pos_iff {I : Type} (Ms : List (ChannelMatrix I)) (i j : I) (p : List I) :
    0 < pathWeight Ms i j p ↔ ∀ a ∈ pathFactors Ms i j p, 0 < a := by
  simp only [pathWeight, pos_iff_ne_zero, ne_eq, List.prod_eq_zero_iff]
  constructor
  · intro h a ha hzero
    apply h
    simpa [hzero] using ha
  · intro h hmem
    exact h 0 hmem rfl

/-- Zero-entry criterion for every nonempty ordered matrix product.  The
`n = 1` case is the singleton branch and uses the unique empty path. -/
theorem orderedMatrixProduct_entry_eq_zero_iff {I : Type} [Fintype I]
    (Ms : List (ChannelMatrix I)) (hMs : Ms ≠ []) (i j : I) :
    channelEntry (orderedMatrixProduct Ms) i j = 0 ↔
      ∀ p : List I, IsIndexPath Ms p → pathWeight Ms i j p = 0 := by
  induction Ms generalizing i j with
  | nil => exact (hMs rfl).elim
  | cons M Ms ih =>
      cases Ms with
      | nil =>
          constructor
          · intro h p hp
            have hp' : p = [] := (isIndexPath_singleton_iff M p).mp hp
            subst p
            simpa using h
          · intro h
            have hp : IsIndexPath [M] [] := rfl
            simpa using h [] hp
      | cons N Ms =>
          have ih' := ih (List.cons_ne_nil N Ms)
          rw [orderedMatrixProduct_cons, channelEntry_mul]
          have hsum :
              (∑ k : I, channelEntry (orderedMatrixProduct (N :: Ms)) k j *
                channelEntry M i k) = 0 ↔
              ∀ k : I, channelEntry (orderedMatrixProduct (N :: Ms)) k j *
                channelEntry M i k = 0 := by
            constructor
            · intro h k
              exact (Finset.sum_eq_zero_iff_of_nonneg
                (fun k _ => zero_le (channelEntry (orderedMatrixProduct (N :: Ms)) k j *
                  channelEntry M i k))).mp h k (Finset.mem_univ k)
            · intro h
              exact Finset.sum_eq_zero fun k _ => h k
          rw [hsum]
          constructor
          · intro hterms p hp
            cases p with
            | nil => simp [IsIndexPath] at hp
            | cons k q =>
                have hq : IsIndexPath (N :: Ms) q :=
                  (isIndexPath_cons_two_iff M N Ms k q).mp hp
                rw [pathWeight_cons_two]
                have hterm := hterms k
                by_cases hM : channelEntry M i k = 0
                · rw [hM, zero_mul]
                · have hT : channelEntry (orderedMatrixProduct (N :: Ms)) k j = 0 := by
                    rcases mul_eq_zero.mp hterm with hT | hM0
                    · exact hT
                    · exact (hM hM0).elim
                  have hq0 : pathWeight (N :: Ms) k j q = 0 :=
                    (ih' k j).mp hT q hq
                  simp [hq0]
          · intro hpaths k
            by_cases hM : channelEntry M i k = 0
            · rw [hM, mul_zero]
            · have hT : channelEntry (orderedMatrixProduct (N :: Ms)) k j = 0 := by
                apply (ih' k j).mpr
                intro q hq
                have hfull := hpaths (k :: q)
                  ((isIndexPath_cons_two_iff M N Ms k q).mpr hq)
                rw [pathWeight_cons_two] at hfull
                rcases mul_eq_zero.mp hfull with hM0 | hq0
                · exact (hM hM0).elim
                · exact hq0
              rw [hT, zero_mul]

/-- Zero-entry criterion in the source's explicit form: every valid path
has at least one zero factor. -/
theorem orderedMatrixProduct_entry_eq_zero_iff_exists_zero_factor {I : Type} [Fintype I]
    (Ms : List (ChannelMatrix I)) (hMs : Ms ≠ []) (i j : I) :
    channelEntry (orderedMatrixProduct Ms) i j = 0 ↔
      ∀ p : List I, IsIndexPath Ms p →
        ∃ a ∈ pathFactors Ms i j p, a = 0 := by
  rw [orderedMatrixProduct_entry_eq_zero_iff Ms hMs i j]
  constructor
  · intro h p hp
    have hz : pathWeight Ms i j p = 0 := h p hp
    have hmem : (0 : ENNReal) ∈ pathFactors Ms i j p := by
      rw [← List.prod_eq_zero_iff]
      exact hz
    exact ⟨0, hmem, rfl⟩
  · intro h p hp
    rcases h p hp with ⟨a, ha, ha0⟩
    rw [pathWeight, List.prod_eq_zero_iff]
    simpa [ha0] using ha

/-- Positive-entry criterion: a nonempty ordered product entry is strictly
positive exactly when at least one valid path has all entries positive. -/
theorem orderedMatrixProduct_entry_pos_iff {I : Type} [Fintype I]
    (Ms : List (ChannelMatrix I)) (hMs : Ms ≠ []) (i j : I) :
    0 < channelEntry (orderedMatrixProduct Ms) i j ↔
      ∃ p : List I, IsAllPositivePath Ms i j p := by
  constructor
  · intro hpos
    have hne : channelEntry (orderedMatrixProduct Ms) i j ≠ 0 := ne_of_gt hpos
    have hnot : ¬ (∀ p : List I, IsIndexPath Ms p → pathWeight Ms i j p = 0) := by
      intro hzero
      exact hne ((orderedMatrixProduct_entry_eq_zero_iff Ms hMs i j).mpr hzero)
    push_neg at hnot
    rcases hnot with ⟨p, hp, hw⟩
    refine ⟨p, hp, ?_⟩
    exact (pathWeight_pos_iff Ms i j p).mp (pos_iff_ne_zero.mpr hw)
  · rintro ⟨p, hp, hall⟩
    have hw : 0 < pathWeight Ms i j p := (pathWeight_pos_iff Ms i j p).mpr hall
    apply pos_iff_ne_zero.mpr
    intro hentry
    have hzero := (orderedMatrixProduct_entry_eq_zero_iff Ms hMs i j).mp hentry
    exact (ne_of_gt hw) (hzero p hp)

end formal_oet.vol_01.ch_02_operator_bounds
```

```toml filename=lakefile.toml
name = "workspace"
defaultTargets = ["Main"]

[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4"
rev = "5e932f97dd25535344f80f9dd8da3aab83df0fe6"

[[lean_lib]]
name = "formal_oet"
globs = ["formal_oet.+"]

[[lean_lib]]
name = "OperatorBounds"

[[lean_lib]]
name = "MatrixPaths"

[[lean_lib]]
name = "Main"
```

```json filename=alignment.json
{
  "case_id": "LCH02",
  "version": "0.1.0",
  "items": [
    {
      "id": "CH02-D01",
      "status": "complete",
      "declarations": [
        {"file": "OperatorBounds.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.IsRestrictedLipMatrix"},
        {"file": "OperatorBounds.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.IsGlobalLipMatrix"},
        {"file": "OperatorBounds.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.lipCertificates"},
        {"file": "OperatorBounds.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.globalLipCertificates"}
      ],
      "representation": {
        "objects": "ChannelMatrix I = Matrix I I ENNReal；IsRestrictedLipMatrix d φ U L 表示 L∈mathscrL(φ)|_U，IsGlobalLipMatrix 取 U=dom φ；两个 Set 定义分别给出受限与全域证书族。",
        "parameters": "X、bot、I、d、φ、U、L 与原文一致，[Fintype I] 表示有限分量指标集。",
        "quantifiers": "受限谓词包含 U⊆dom φ，并保留 ∀x∈U、∀y∈U、∀j，以及对全部输入分量 i 的有限和。",
        "conclusion": "逐字实现 d_j(φx,φy)≤∑_i L_{i→j}d_i(x,y)；全域情形不增加非空要求。"
      },
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-D02",
      "status": "complete",
      "declarations": [
        {"file": "OperatorBounds.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.IsRestrictedCoLipMatrix"},
        {"file": "OperatorBounds.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.IsGlobalCoLipMatrix"},
        {"file": "OperatorBounds.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.coLipCertificates"},
        {"file": "OperatorBounds.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.globalCoLipCertificates"}
      ],
      "representation": {
        "objects": "IsRestrictedCoLipMatrix d φ U K 表示 K∈mathscrK(φ)|_U；coLipCertificates 与 globalCoLipCertificates 是对应证书族，全域谓词取 U=dom φ。",
        "parameters": "d、φ、U、K 与 Lip 情形使用相同矩阵和通道表示。",
        "quantifiers": "谓词显式合取 U.Nonempty 与 U⊆dom φ，并保留 ∀x∈U、∀y∈U、∀j 及有限输入和；全域谓词也保留 dom φ 非空。",
        "conclusion": "下界方向为 ∑_i K_{i→j}d_i(x,y)≤d_j(φx,φy)，与原文 ≥ 写法等价。"
      },
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-D03",
      "status": "complete",
      "declarations": [
        {"file": "OperatorBounds.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.ChannelMatrix"},
        {"file": "OperatorBounds.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.channelEntry"},
        {"file": "OperatorBounds.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.channelEntry_mul"},
        {"file": "OperatorBounds.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.channelEntry_one"},
        {"file": "OperatorBounds.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.sum_channelEntry_mul"}
      ],
      "representation": {
        "objects": "标准 Matrix 的行是输出分量、列是输入分量；channelEntry L i j 定义为 L j i，正是原文 L_{i→j}。",
        "parameters": "A、B 是同一有限指标集 I 上的 ENNReal 矩阵，i 为输入通道、j 为输出通道。",
        "quantifiers": "channelEntry_mul 对任意 A、B、i、j 展开全部中间指标 k 的有限和。",
        "conclusion": "(A*B)_{i→j}=∑_k A_{k→j}B_{i→k}，即 (A*B) j i=∑_k A j k*B k i；sum_channelEntry_mul 同时给出复合证明所需的分配与交换求和形式。"
      },
      "dependencies": []
    },
    {
      "id": "CH02-D04",
      "status": "complete",
      "declarations": [
        {"file": "OperatorBounds.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.orderedMatrixProduct"},
        {"file": "OperatorBounds.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.orderedMatrixProduct_nil"},
        {"file": "OperatorBounds.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.orderedMatrixProduct_cons"},
        {"file": "OperatorBounds.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.orderedMatrixProduct_singleton"},
        {"file": "OperatorBounds.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.sum_channelEntry_one"}
      ],
      "representation": {
        "objects": "矩阵列表按算子作用顺序排列；orderedMatrixProduct []=1，orderedMatrixProduct (M::Ms)=orderedMatrixProduct Ms*M。",
        "parameters": "Ms 是任意有限矩阵列表，M 是任意通道矩阵；单位矩阵来自标准 Matrix One 实例。",
        "quantifiers": "定义覆盖空列表、单元素列表和任意非空列表，不限定列表长度。",
        "conclusion": "[M₁,…,Mₙ] 的乘积为 Mₙ*…*M₁，空乘积为单位矩阵；sum_channelEntry_one 证明单位矩阵只保留对角项。"
      },
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-D05",
      "status": "complete",
      "declarations": [
        {"file": "OperatorBounds.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.finiteComposition"},
        {"file": "OperatorBounds.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.finiteComposition_eq_operatorChain_reverse"},
        {"file": "OperatorBounds.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.intermediateImages"},
        {"file": "OperatorBounds.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.intermediateImages_length"},
        {"file": "OperatorBounds.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.StepwiseLipCertificates"},
        {"file": "OperatorBounds.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.StepwiseCoLipCertificates"},
        {"file": "OperatorBounds.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.image_subset_dom_finiteComposition_tail"}
      ],
      "representation": {
        "objects": "finiteComposition [φ₁,…,φₖ]=φₖ∘…∘φ₁，空列表为恒等；intermediateImages 递推记录 U、φ₁''U、…，StepwiseLipCertificates/StepwiseCoLipCertificates 在这些实际像域上逐步配对算子和矩阵。",
        "parameters": "φs 是作用顺序列表，U 是起始集；矩阵列表与算子列表通过递归定义强制同长并逐步对应。",
        "quantifiers": "定义适用于任意有限链和任意起始集；image_subset_dom_finiteComposition_tail 对任意首算子和尾链，从 U⊆dom(finiteComposition(φ::φs)) 推出 φ''U⊆dom(finiteComposition φs)。",
        "conclusion": "intermediateImages_length 给出 k+1 个集合；与冻结 OperatorChain 的对应是 finiteComposition φs=OperatorChain φs.reverse，反转正是两种列表约定之间的表示对应。"
      },
      "dependencies": ["CH02-D01", "CH02-D02"]
    },
    {
      "id": "CH02-D06",
      "status": "complete",
      "declarations": [
        {"file": "MatrixPaths.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.adjacentPairs"},
        {"file": "MatrixPaths.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.pathVertices"},
        {"file": "MatrixPaths.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.pathFactors"},
        {"file": "MatrixPaths.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.pathWeight"},
        {"file": "MatrixPaths.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.IsIndexPath"},
        {"file": "MatrixPaths.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.IsAllPositivePath"},
        {"file": "MatrixPaths.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.pathWeight_cons_two"},
        {"file": "MatrixPaths.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.pathWeight_pos_iff"}
      ],
      "representation": {
        "objects": "p 只存中间指标 (k₁,…,kₙ₋₁)，完整顶点为 pathVertices i j p=i::(p++[j])；pathFactors 取相邻顶点对应的通道条目，pathWeight 为其乘积。",
        "parameters": "Ms 为按作用顺序给出的矩阵列表，i=k₀、j=kₙ 为端点，p 为中间指标列表。",
        "quantifiers": "IsIndexPath Ms p 要求 p.length+1=Ms.length；IsAllPositivePath 另外要求 ∀a∈pathFactors, 0<a。",
        "conclusion": "n=1 时唯一合法 p 是空列表且权为 M₁ 的对应条目；pathWeight_cons_two 给出至少两步时的首边分解，pathWeight_pos_iff 给出权正与逐因子正的等价。"
      },
      "dependencies": ["CH02-D03"]
    },
    {
      "id": "CH02-P01",
      "status": "complete",
      "declarations": [
        {"file": "OperatorBounds.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.unique_sum_channelEntry"},
        {"file": "OperatorBounds.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.isRestrictedLipMatrix_unique_iff"},
        {"file": "OperatorBounds.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.isGlobalLipMatrix_unique_iff"}
      ],
      "representation": {
        "objects": "[Unique I] 表示 I 恰有一个分量，default 就是原文唯一指标 i。",
        "parameters": "同时给出任意受限域 U 的版本和 U=dom φ 的全域版本，L 是 1×1 通道矩阵。",
        "quantifiers": "保留所有 x,y∈U（全域版本中 x,y∈dom φ）；唯一输出指标由 Subsingleton.elim 覆盖。",
        "conclusion": "Lip 谓词等价于 d_default(φx,φy)≤L_{default→default}d_default(x,y)，有限和严格退化为一项。"
      },
      "dependencies": ["CH02-D01", "CH02-D03"]
    },
    {
      "id": "CH02-P02",
      "status": "complete",
      "declarations": [
        {"file": "OperatorBounds.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.lipCertificates_antitone"}
      ],
      "representation": {
        "objects": "lipCertificates 是 D01 的受限 Lip 证书族。",
        "parameters": "固定 d、φ，任意集合 U、V 满足 hUV:U⊆V 和 hV:V⊆dom φ。",
        "quantifiers": "对任意 L∈lipCertificates d φ V，逐点使用原不等式于 U 中任意 x、y 和任意输出 j。",
        "conclusion": "lipCertificates d φ V⊆lipCertificates d φ U，即证书族关于限制域反单调。"
      },
      "dependencies": ["CH02-D01"]
    },
    {
      "id": "CH02-P04",
      "status": "complete",
      "declarations": [
        {"file": "OperatorBounds.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.lip_compose_two"}
      ],
      "representation": {
        "objects": "operator_compose φ₂ φ₁ 表示 φ₂∘φ₁；中间域精确写为 φ₁.func '' U。",
        "parameters": "保留 hU:U⊆dom(φ₂∘φ₁)、h₁:L₁∈mathscrL(φ₁)|_U、h₂:L₂∈mathscrL(φ₂)|_(φ₁''U)。",
        "quantifiers": "对任意 x,y∈U 和输出 j，先对像点 φ₁x、φ₁y 使用 L₂，再对所有中间 k 使用 L₁。",
        "conclusion": "L₂*L₁∈lipCertificates d (φ₂∘φ₁) U，矩阵次序与原文完全一致。"
      },
      "dependencies": ["CH02-D01", "CH02-D03"]
    },
    {
      "id": "CH02-P05",
      "status": "complete",
      "declarations": [
        {"file": "OperatorBounds.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.coLipCertificates_antitone"}
      ],
      "representation": {
        "objects": "coLipCertificates 是含非空条件的受限 co-Lip 证书族。",
        "parameters": "固定 d、φ，保留 hUne:U.Nonempty、hUV:U⊆V、hV:V⊆dom φ。",
        "quantifiers": "任意 V 上证书都限制为 U 上证书，逐点量词与原 co-Lip 不等式不变。",
        "conclusion": "coLipCertificates d φ V⊆coLipCertificates d φ U，并由 hUne 保留较小域的非空性。"
      },
      "dependencies": ["CH02-D02"]
    },
    {
      "id": "CH02-P07",
      "status": "complete",
      "declarations": [
        {"file": "OperatorBounds.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.channelEntry_eq_zero_of_output_zero_input_pos"}
      ],
      "representation": {
        "objects": "K 是全域 co-Lip 证书，channelEntry K i j 对应 K_{i→j}。",
        "parameters": "保留 x,y∈dom φ、hout:d_j(φx,φy)=0、hin:0<d_i(x,y)。",
        "quantifiers": "对任意满足条件的证书 K、点对 x,y 和通道 i,j 均作结论。",
        "conclusion": "由 K_{i→j}d_i(x,y)≤∑_k K_{k→j}d_k(x,y)≤0 及输入项严格正，推出 K_{i→j}=0。"
      },
      "dependencies": ["CH02-D02", "CH02-D03"]
    },
    {
      "id": "CH02-P08",
      "status": "complete",
      "declarations": [
        {"file": "OperatorBounds.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.coLip_compose_two"}
      ],
      "representation": {
        "objects": "与两步 Lip 定理使用相同的复合算子和精确中间像域 φ₁.func '' U。",
        "parameters": "保留 hU、K₁ 在 U 上的证书、K₂ 在 φ₁''U 上的证书；两个证书谓词都含非空与定义域条件。",
        "quantifiers": "对任意 x,y∈U 和输出 j，依次使用 K₁、K₂ 的下界不等式及全部中间指标求和。",
        "conclusion": "K₂*K₁ 是 φ₂∘φ₁ 在 U 上的 co-Lip 证书；结论中的 U.Nonempty 由 K₁ 的证书直接保留。"
      },
      "dependencies": ["CH02-D02", "CH02-D03"]
    },
    {
      "id": "CH02-P11",
      "status": "complete",
      "declarations": [
        {"file": "OperatorBounds.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.zeroStep_identity_lip"}
      ],
      "representation": {
        "objects": "finiteComposition [] 是恒等算子，orderedMatrixProduct [] 是单位矩阵。",
        "parameters": "保留原文非空 U 和 U⊆dom(id) 前提。",
        "quantifiers": "对任意 x,y∈U 和输出 j，单位矩阵求和折叠为 d_j(x,y)。",
        "conclusion": "空矩阵乘积属于恒等算子在 U 上的 Lip 证书族；证明使用等式，因而没有弱化上界。"
      },
      "dependencies": ["CH02-D01", "CH02-D03", "CH02-D04", "CH02-D05"]
    },
    {
      "id": "CH02-P12",
      "status": "complete",
      "declarations": [
        {"file": "OperatorBounds.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.zeroStep_identity_coLip"}
      ],
      "representation": {
        "objects": "与 P11 相同的零步恒等算子和单位矩阵，目标证书族换为 coLipCertificates。",
        "parameters": "保留 hUne:U.Nonempty 与 hU:U⊆dom(id)。",
        "quantifiers": "任意 x,y∈U 和输出 j 的整条输入和均化简到对角项。",
        "conclusion": "空乘积/单位矩阵属于恒等算子在 U 上的 co-Lip 证书族，非空性也出现在结论证书中。"
      },
      "dependencies": ["CH02-D02", "CH02-D03", "CH02-D04", "CH02-D05"]
    },
    {
      "id": "CH02-P14",
      "status": "complete",
      "declarations": [
        {"file": "MatrixPaths.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.orderedMatrixProduct_entry_pos_iff"}
      ],
      "representation": {
        "objects": "orderedMatrixProduct Ms 的非空有序乘积及 IsAllPositivePath 使用 D04、D06 表示。",
        "parameters": "Ms 是任意矩阵列表，hMs:Ms≠[]，i、j 是任意起止分量。",
        "quantifiers": "左端为 0<乘积的 i→j 条目，右端为 ∃p，合法路径且路径每个因子严格正。",
        "conclusion": "严格正值 iff 存在至少一条全正路径；证明对单矩阵分支使用唯一空路径，因此显式覆盖 n=1，且允许正条目为有限值或 +∞。"
      },
      "dependencies": ["CH02-D03", "CH02-D04", "CH02-D06", "CH02-P13"]
    },
    {
      "id": "CH02-P03",
      "status": "complete",
      "declarations": [
        {"file": "OperatorBounds.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.globalLip_mem_lipCertificates"}
      ],
      "representation": {
        "objects": "globalLipCertificates d φ 是全域 Lip 证书族，lipCertificates d φ U 是受限族。",
        "parameters": "对任意 U⊆dom φ 和任意全域证书 L。",
        "quantifiers": "全域证书的所有点对不等式经 P02 限制到 U 中所有点对。",
        "conclusion": "L∈globalLipCertificates d φ 蕴含 L∈lipCertificates d φ U，即 mathscrL(φ)⊆mathscrL(φ)|_U。"
      },
      "dependencies": ["CH02-D01", "CH02-P02"]
    },
    {
      "id": "CH02-P06",
      "status": "complete",
      "declarations": [
        {"file": "OperatorBounds.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.globalCoLip_mem_coLipCertificates"}
      ],
      "representation": {
        "objects": "globalCoLipCertificates 与 coLipCertificates 都来自 D02。",
        "parameters": "保留 hUne:U.Nonempty、hU:U⊆dom φ，并取任意全域 co-Lip 证书 K。",
        "quantifiers": "所有全域下界不等式经 P05 限制到非空 U 的全部点对和输出分量。",
        "conclusion": "K∈globalCoLipCertificates d φ 蕴含 K∈coLipCertificates d φ U，对应 mathscrK(φ)|_domφ⊆mathscrK(φ)|_U。"
      },
      "dependencies": ["CH02-D02", "CH02-P05"]
    },
    {
      "id": "CH02-P09",
      "status": "complete",
      "declarations": [
        {"file": "OperatorBounds.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.finiteComposition_lip"}
      ],
      "representation": {
        "objects": "φs、Ls 均按作用顺序排列，StepwiseLipCertificates 在 intermediateImages 的实际输入域上选取每个 L^(m)。",
        "parameters": "保留 hφs:φs≠[]、hU:U⊆dom(finiteComposition φs) 和逐步证书 hLs。",
        "quantifiers": "对任意正长度有限链、起始域及任意逐步证书列表成立；归纳覆盖单步和任意多步。",
        "conclusion": "orderedMatrixProduct Ls∈lipCertificates d (finiteComposition φs) U，即 L^(k)*…*L^(1)∈mathscrL(c_k)|_U；归纳步骤使用精确中间像域上的 P04。"
      },
      "dependencies": ["CH02-D01", "CH02-D03", "CH02-D04", "CH02-D05", "CH02-P04"]
    },
    {
      "id": "CH02-P10",
      "status": "complete",
      "declarations": [
        {"file": "OperatorBounds.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.finiteComposition_coLip"}
      ],
      "representation": {
        "objects": "与 P09 使用相同链和有序乘积，StepwiseCoLipCertificates 在每个实际像域上包含非空 co-Lip 证书。",
        "parameters": "保留 hφs、hU、hKs；首域非空性包含在第一个逐步证书中，并随像集传递到后续证书。",
        "quantifiers": "对任意正长度链和任意逐步 co-Lip 证书列表成立，单步及多步均由同一归纳覆盖。",
        "conclusion": "orderedMatrixProduct Ks∈coLipCertificates d (finiteComposition φs) U，即 K^(k)*…*K^(1)∈mathscrK(c_k)|_U，结论保留非空与定义域条件。"
      },
      "dependencies": ["CH02-D02", "CH02-D03", "CH02-D04", "CH02-D05", "CH02-P08"]
    },
    {
      "id": "CH02-P13",
      "status": "complete",
      "declarations": [
        {"file": "MatrixPaths.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.orderedMatrixProduct_entry_eq_zero_iff"},
        {"file": "MatrixPaths.lean", "name": "formal_oet.vol_01.ch_02_operator_bounds.orderedMatrixProduct_entry_eq_zero_iff_exists_zero_factor"}
      ],
      "representation": {
        "objects": "使用 D04 的非空有序矩阵乘积和 D06 的 pathFactors/IsIndexPath。",
        "parameters": "Ms 任意且 hMs:Ms≠[]，i、j 任意；每条 p 均满足中间指标数恰为矩阵数减一。",
        "quantifiers": "右端明确为 ∀p，若 IsIndexPath Ms p，则 ∃a∈pathFactors Ms i j p 使 a=0。",
        "conclusion": "乘积条目为零 iff 每条合法路径都有至少一个零因子；辅助形式把存在零因子写成 pathWeight=0，二者由 ENNReal 无零因子性等价。n=1 是唯一空路径的单条目判据。"
      },
      "dependencies": ["CH02-D03", "CH02-D04", "CH02-D06"]
    }
  ]
}
```