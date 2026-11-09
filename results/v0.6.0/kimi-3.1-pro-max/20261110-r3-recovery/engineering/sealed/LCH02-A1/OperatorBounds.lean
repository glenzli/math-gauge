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
