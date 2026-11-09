import formal_oet.vol_01.ch_02_operator_bounds.Basic

namespace formal_oet.vol_01.ch_02_operator_bounds

open scoped BigOperators ENNReal Classical
open formal_oet.vol_01.ch_01_foundations

universe u

@[simp] theorem boundIdentity_apply {I : Type u} (i j : I) :
    boundIdentity i j = if i = j then 1 else 0 := by
  classical
  rfl

/-- HC02-D04.  Right identity for input-first multiplication. -/
theorem boundMul_identity_right {I : Type u} [Fintype I] (M : BoundMatrix I) :
    boundMul M boundIdentity = M := by
  classical
  ext i j
  simp [boundMul, boundIdentity]

/-- HC02-D04.  Left identity for input-first multiplication. -/
theorem boundMul_identity_left {I : Type u} [Fintype I] (M : BoundMatrix I) :
    boundMul boundIdentity M = M := by
  classical
  ext i j
  simp [boundMul, boundIdentity]

/-- HC02-D04.  A one-step ordered product is its unique matrix. -/
@[simp] theorem orderedProduct_one {I : Type u} [Fintype I] (A : ℕ → BoundMatrix I) :
    orderedProduct A 1 = A 0 := by
  exact boundMul_identity_right (A 0)

@[simp] theorem identity_bound_sum {I X : Type} [Fintype I]
    (d : I → X → X → ENNReal) (x y : X) (j : I) :
    (∑ i : I, boundIdentity i j * d i x y) = d j x y := by
  classical
  simp [boundIdentity]

/-- HC02-P14.  The identity matrix is a Lip certificate for the empty
operator chain. -/
theorem identity_lip {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (U : Set X)
    (hU : U ⊆ dom (OperatorChain ([] : List (Operator X bot)))) :
    boundIdentity ∈ restrictedLipCertificates d (OperatorChain ([] : List (Operator X bot))) U := by
  refine ⟨hU, ?_⟩
  intro x hx y hy j
  change d j x y ≤ ∑ i : I, boundIdentity i j * d i x y
  exact (identity_bound_sum d x y j).ge

/-- HC02-P15.  On the same nonempty legal domain, the identity matrix is
also a co-Lip certificate. -/
theorem identity_coLip {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (U : Set X) (hUne : U.Nonempty)
    (hU : U ⊆ dom (OperatorChain ([] : List (Operator X bot)))) :
    boundIdentity ∈ restrictedCoLipCertificates d (OperatorChain ([] : List (Operator X bot))) U := by
  refine ⟨hUne, hU, ?_⟩
  intro x hx y hy j
  change (∑ i : I, boundIdentity i j * d i x y) ≤ d j x y
  exact (identity_bound_sum d x y j).le

/-- HC02-P01.  On a singleton index type the matrix condition is exactly
the displayed scalar inequality. -/
theorem lip_unique {X I : Type} {bot : X} [Fintype I] [Unique I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (L : BoundMatrix I) :
    L ∈ restrictedLipCertificates d ϕ U ↔
      U ⊆ dom ϕ ∧ ∀ x ∈ U, ∀ y ∈ U,
        d default (ϕ.func x) (ϕ.func y) ≤ L default default * d default x y := by
  constructor
  · intro hL
    refine ⟨hL.1, ?_⟩
    intro x hx y hy
    simpa using hL.2 x hx y hy default
  · rintro ⟨hU, hscalar⟩
    refine ⟨hU, ?_⟩
    intro x hx y hy j
    have hj : j = default := Subsingleton.elim _ _
    subst j
    simpa using hscalar x hx y hy

/-- The same singleton degeneration with an explicitly named unique index. -/
theorem lip_singleton {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (L : BoundMatrix I)
    (i₀ : I) (hI : ∀ k : I, k = i₀) :
    L ∈ restrictedLipCertificates d ϕ U ↔
      U ⊆ dom ϕ ∧ ∀ x ∈ U, ∀ y ∈ U,
        d i₀ (ϕ.func x) (ϕ.func y) ≤ L i₀ i₀ * d i₀ x y := by
  letI : Unique I := { toInhabited := ⟨i₀⟩, uniq := hI }
  exact lip_unique d ϕ U L

/-- HC02-P02.  A global Lip certificate restricts to every legal subset. -/
theorem lip_global_subset_restricted {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    (hU : U ⊆ dom ϕ) :
    lipCertificates d ϕ ⊆ restrictedLipCertificates d ϕ U := by
  intro L hL
  exact ⟨hU, fun x hx y hy j => hL.2 x (hU hx) y (hU hy) j⟩

/-- HC02-P03.  Shrinking the evaluation domain enlarges the certificate family. -/
theorem restrictedLip_mono {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U V : Set X}
    (hUV : U ⊆ V) :
    restrictedLipCertificates d ϕ V ⊆ restrictedLipCertificates d ϕ U := by
  intro L hL
  exact ⟨hUV.trans hL.1, fun x hx y hy j => hL.2 x (hUV hx) y (hUV hy) j⟩

/-- HC02-P04.  Entrywise infima do not increase when the evaluation domain
is enlarged. -/
theorem entryInf_mono {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U V : Set X}
    (hUV : U ⊆ V) (i j : I) :
    entryInf d ϕ U i j ≤ entryInf d ϕ V i j := by
  apply sInf_le_sInf
  exact Set.image_mono (restrictedLip_mono d ϕ hUV)

/-- The extended-nonnegative-real finite-sum calculation shared by the Lip
and co-Lip composition laws. -/
theorem weighted_sum_exchange {I : Type u} [Fintype I]
    (M₂ M₁ : BoundMatrix I) (w : I → ENNReal) (j : I) :
    (∑ k : I, M₂ k j * (∑ i : I, M₁ i k * w i)) =
      ∑ i : I, boundMul M₂ M₁ i j * w i := by
  classical
  simp_rw [boundMul, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

/-- HC02-P05.  Two-step Lipschitz composition on the actual intermediate
image domain. -/
theorem lip_comp_two {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ₁ ϕ₂ : Operator X bot) (U₁ : Set X)
    (L₁ L₂ : BoundMatrix I)
    (hU₁ : U₁ ⊆ dom (OperatorChain [ϕ₂, ϕ₁]))
    (hL₁ : L₁ ∈ restrictedLipCertificates d ϕ₁ U₁)
    (hL₂ : L₂ ∈ restrictedLipCertificates d ϕ₂ (ϕ₁.func '' U₁)) :
    boundMul L₂ L₁ ∈ restrictedLipCertificates d (OperatorChain [ϕ₂, ϕ₁]) U₁ := by
  refine ⟨hU₁, ?_⟩
  intro x hx y hy j
  change d j (ϕ₂.func (ϕ₁.func x)) (ϕ₂.func (ϕ₁.func y)) ≤
    ∑ i : I, boundMul L₂ L₁ i j * d i x y
  calc
    d j (ϕ₂.func (ϕ₁.func x)) (ϕ₂.func (ϕ₁.func y)) ≤
        ∑ k : I, L₂ k j * d k (ϕ₁.func x) (ϕ₁.func y) :=
      hL₂.2 (ϕ₁.func x) ⟨x, hx, rfl⟩ (ϕ₁.func y) ⟨y, hy, rfl⟩ j
    _ ≤ ∑ k : I, L₂ k j * (∑ i : I, L₁ i k * d i x y) := by
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_left' (hL₁.2 x hx y hy k) _
    _ = ∑ i : I, boundMul L₂ L₁ i j * d i x y :=
      weighted_sum_exchange L₂ L₁ (fun i => d i x y) j

/-- HC02-P07.  Two-step co-Lipschitz composition on the actual intermediate
image domain. -/
theorem coLip_comp_two {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ₁ ϕ₂ : Operator X bot) (U₁ : Set X)
    (K₁ K₂ : BoundMatrix I)
    (hU₁ : U₁ ⊆ dom (OperatorChain [ϕ₂, ϕ₁]))
    (hK₁ : K₁ ∈ restrictedCoLipCertificates d ϕ₁ U₁)
    (hK₂ : K₂ ∈ restrictedCoLipCertificates d ϕ₂ (ϕ₁.func '' U₁)) :
    boundMul K₂ K₁ ∈ restrictedCoLipCertificates d (OperatorChain [ϕ₂, ϕ₁]) U₁ := by
  refine ⟨hK₁.1, hU₁, ?_⟩
  intro x hx y hy j
  change (∑ i : I, boundMul K₂ K₁ i j * d i x y) ≤
    d j (ϕ₂.func (ϕ₁.func x)) (ϕ₂.func (ϕ₁.func y))
  calc
    (∑ i : I, boundMul K₂ K₁ i j * d i x y) =
        ∑ k : I, K₂ k j * (∑ i : I, K₁ i k * d i x y) :=
      (weighted_sum_exchange K₂ K₁ (fun i => d i x y) j).symm
    _ ≤ ∑ k : I, K₂ k j * d k (ϕ₁.func x) (ϕ₁.func y) := by
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_left' (hK₁.2.2 x hx y hy k) _
    _ ≤ d j (ϕ₂.func (ϕ₁.func x)) (ϕ₂.func (ϕ₁.func y)) :=
      hK₂.2.2 (ϕ₁.func x) ⟨x, hx, rfl⟩ (ϕ₁.func y) ⟨y, hy, rfl⟩ j

/-- HC02-P06.  A zero output distance together with positive input distance
forces the corresponding global co-Lip entry to vanish. -/
theorem coLip_entry_eq_zero_of_output_zero {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (K : BoundMatrix I)
    (hK : K ∈ coLipCertificates d ϕ) (x y : X) (hx : x ∈ dom ϕ) (hy : y ∈ dom ϕ)
    (i j : I) (hout : d j (ϕ.func x) (ϕ.func y) = 0) (hin : 0 < d i x y) :
    K i j = 0 := by
  have hsum : (∑ k : I, K k j * d k x y) = 0 := by
    apply le_antisymm
    · simpa [hout] using hK.2.2 x hx y hy j
    · exact zero_le _
  have hterm_le : K i j * d i x y ≤ ∑ k : I, K k j * d k x y := by
    exact Finset.single_le_sum (fun k _ => zero_le (K k j * d k x y)) (Finset.mem_univ i)
  have hterm : K i j * d i x y = 0 :=
    le_antisymm (hterm_le.trans_eq hsum) (zero_le _)
  by_contra hKne
  have hpos : 0 < K i j * d i x y := ENNReal.mul_pos hKne hin.ne'
  rw [hterm] at hpos
  exact (lt_irrefl 0) hpos

/-- HC02-P08.  Forward point-pair image-distance perturbation. -/
theorem perturbation_forward {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ₁ ϕ₂ : Operator X bot) (U : Set X) (δ : I → ENNReal)
    (hδ : ∀ z ∈ U, ∀ j : I, d j (ϕ₁.func z) (ϕ₂.func z) ≤ δ j)
    (x y : X) (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (ϕ₂.func x) (ϕ₂.func y) ≤
      d j (ϕ₁.func x) (ϕ₁.func y) + δ j + δ j := by
  have hδrev : ∀ z ∈ U, ∀ j : I, d j (ϕ₂.func z) (ϕ₁.func z) ≤ δ j := by
    intro z hz k
    rw [(hd k).symm (ϕ₂.func z) (ϕ₁.func z)]
    exact hδ z hz k
  calc
    d j (ϕ₂.func x) (ϕ₂.func y) ≤
        d j (ϕ₂.func x) (ϕ₁.func x) + d j (ϕ₁.func x) (ϕ₂.func y) :=
      (hd j).triangle _ _ _
    _ ≤ d j (ϕ₂.func x) (ϕ₁.func x) +
        (d j (ϕ₁.func x) (ϕ₁.func y) + d j (ϕ₁.func y) (ϕ₂.func y)) :=
      add_le_add (le_refl _) ((hd j).triangle _ _ _)
    _ ≤ δ j + (d j (ϕ₁.func x) (ϕ₁.func y) + δ j) :=
      add_le_add (hδrev x hx j) (add_le_add (le_refl _) (hδ y hy j))
    _ = d j (ϕ₁.func x) (ϕ₁.func y) + δ j + δ j := by
      rw [← add_assoc, add_comm (δ j) (d j (ϕ₁.func x) (ϕ₁.func y)), add_assoc]

/-- HC02-P09.  The reverse point-pair perturbation follows by symmetry. -/
theorem perturbation_reverse {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ₁ ϕ₂ : Operator X bot) (U : Set X) (δ : I → ENNReal)
    (hδ : ∀ z ∈ U, ∀ j : I, d j (ϕ₁.func z) (ϕ₂.func z) ≤ δ j)
    (x y : X) (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (ϕ₁.func x) (ϕ₁.func y) ≤
      d j (ϕ₂.func x) (ϕ₂.func y) + δ j + δ j := by
  apply perturbation_forward d hd ϕ₂ ϕ₁ U δ
  · intro z hz k
    rw [(hd k).symm (ϕ₂.func z) (ϕ₁.func z)]
    exact hδ z hz k
  · exact hx
  · exact hy

/-- HC02-P10.  Additive perturbation of a Lip upper bound. -/
theorem perturbation_lip {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ₁ ϕ₂ : Operator X bot) (U : Set X) (δ : I → ENNReal) (L₁ : BoundMatrix I)
    (hδ : ∀ z ∈ U, ∀ j : I, d j (ϕ₁.func z) (ϕ₂.func z) ≤ δ j)
    (hL₁ : L₁ ∈ restrictedLipCertificates d ϕ₁ U)
    (x y : X) (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (ϕ₂.func x) (ϕ₂.func y) ≤
      (∑ i : I, L₁ i j * d i x y) + 2 * δ j := by
  calc
    d j (ϕ₂.func x) (ϕ₂.func y) ≤
        d j (ϕ₁.func x) (ϕ₁.func y) + δ j + δ j :=
      perturbation_forward d hd ϕ₁ ϕ₂ U δ hδ x y hx hy j
    _ ≤ (∑ i : I, L₁ i j * d i x y) + δ j + δ j := by
      exact add_le_add (add_le_add (hL₁.2 x hx y hy j) (le_refl _)) (le_refl _)
    _ = (∑ i : I, L₁ i j * d i x y) + 2 * δ j := by rw [two_mul]; ac_rfl

/-- HC02-P11.  Additive perturbation of a co-Lip lower bound. -/
theorem perturbation_coLip {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ₁ ϕ₂ : Operator X bot) (U : Set X) (δ : I → ENNReal) (K₁ : BoundMatrix I)
    (hδ : ∀ z ∈ U, ∀ j : I, d j (ϕ₁.func z) (ϕ₂.func z) ≤ δ j)
    (hK₁ : K₁ ∈ restrictedCoLipCertificates d ϕ₁ U)
    (x y : X) (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    (∑ i : I, K₁ i j * d i x y) ≤
      d j (ϕ₂.func x) (ϕ₂.func y) + 2 * δ j := by
  calc
    (∑ i : I, K₁ i j * d i x y) ≤ d j (ϕ₁.func x) (ϕ₁.func y) :=
      hK₁.2.2 x hx y hy j
    _ ≤ d j (ϕ₂.func x) (ϕ₂.func y) + δ j + δ j :=
      perturbation_reverse d hd ϕ₁ ϕ₂ U δ hδ x y hx hy j
    _ = d j (ϕ₂.func x) (ϕ₂.func y) + 2 * δ j := by rw [two_mul]; ac_rfl

/-- HC02-P25.  A zero matrix coefficient removes its own summand, including
when the corresponding distance is infinite. -/
theorem zero_coefficient_term {I X : Type} (L : BoundMatrix I)
    (d : I → X → X → ENNReal) (i j : I) (x y : X) (hzero : L i j = 0) :
    L i j * d i x y = 0 := by simp [hzero]

/-- HC02-P25.  The zero input position can be deleted from the finite sum. -/
theorem sum_erase_of_coefficient_zero {I X : Type} [Fintype I]
    (L : BoundMatrix I) (d : I → X → X → ENNReal) (i j : I) (x y : X)
    (hzero : L i j = 0) :
    (∑ k : I, L k j * d k x y) =
      ∑ k ∈ Finset.univ.erase i, L k j * d k x y := by
  classical
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  simp [hzero]

/-- HC02-P26.  A single supported input position simplifies an output row. -/
theorem lip_row_sparse {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (L : BoundMatrix I)
    (hL : L ∈ restrictedLipCertificates d ϕ U) {i j : I}
    (hrow : RowSparse L i j) (x y : X) (hx : x ∈ U) (hy : y ∈ U) :
    d j (ϕ.func x) (ϕ.func y) ≤ L i j * d i x y := by
  refine (hL.2 x hx y hy j).trans_eq ?_
  classical
  apply Finset.sum_eq_single i
  · intro k hk hki
    simp [hrow k hki]
  · simp

/-- HC02-P27.  A singly supported input column can contribute only to its
designated output position. -/
theorem column_sparse_terms_zero {I X : Type}
    (L : BoundMatrix I) (d : I → X → X → ENNReal) {i j : I}
    (hcol : ColumnSparse L i j) (x y : X) :
    ∀ k : I, k ≠ j → L i k * d i x y = 0 := by
  intro k hk
  simp [hcol k hk]

/-- HC02-P28.  A diagonal Lip certificate gives scalar bounds on every
component. -/
theorem diagonal_lip_bounds {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (L : BoundMatrix I)
    (hL : L ∈ restrictedLipCertificates d ϕ U) (hdiag : Diagonal L)
    (x y : X) (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (ϕ.func x) (ϕ.func y) ≤ L j j * d j x y := by
  exact lip_row_sparse d ϕ U L hL (fun k hkj => hdiag k j hkj) x y hx hy

/-- HC02-P29.  Only row sparsity of the Lip certificate is needed for the
scalar two-sided bound; no sparsity assumption is made on `K`. -/
theorem diagonal_input_two_sided {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    (L K : BoundMatrix I)
    (hL : L ∈ restrictedLipCertificates d ϕ U)
    (hK : K ∈ restrictedCoLipCertificates d ϕ U) {j : I}
    (hrow : ∀ k : I, k ≠ j → L k j = 0)
    (x y : X) (hx : x ∈ U) (hy : y ∈ U) :
    K j j * d j x y ≤ d j (ϕ.func x) (ϕ.func y) ∧
      d j (ϕ.func x) (ϕ.func y) ≤ L j j * d j x y := by
  constructor
  · calc
      K j j * d j x y ≤ ∑ k : I, K k j * d k x y := by
        exact Finset.single_le_sum (fun k _ => zero_le (K k j * d k x y)) (Finset.mem_univ j)
      _ ≤ d j (ϕ.func x) (ϕ.func y) := hK.2.2 x hx y hy j
  · exact lip_row_sparse d ϕ U L hL hrow x y hx hy

/-- HC02-P30.  Componentwise two-sided bounds, including the finite-diagonal
coefficient branch. -/
theorem all_components_two_sided_finite {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    (L K : BoundMatrix I)
    (hL : L ∈ restrictedLipCertificates d ϕ U)
    (hK : K ∈ restrictedCoLipCertificates d ϕ U)
    (hrows : ∀ j k : I, k ≠ j → L k j = 0)
    (hfinite : ∀ j : I, L j j < ∞ ∧ K j j < ∞) :
    ∀ j : I, K j j < ∞ ∧ L j j < ∞ ∧
      ∀ x ∈ U, ∀ y ∈ U,
        K j j * d j x y ≤ d j (ϕ.func x) (ϕ.func y) ∧
          d j (ϕ.func x) (ϕ.func y) ≤ L j j * d j x y := by
  intro j
  exact ⟨(hfinite j).2, (hfinite j).1,
    fun x hx y hy => diagonal_input_two_sided d ϕ U L K hL hK (hrows j) x y hx hy⟩

/-- HC02-P31.  A positive co-Lip channel preserves distinguishability. -/
theorem positive_coLip_channel {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (K : BoundMatrix I)
    (hK : K ∈ restrictedCoLipCertificates d ϕ U) {i j : I}
    (hKpos : 0 < K i j) (x y : X) (hx : x ∈ U) (hy : y ∈ U)
    (hdist : 0 < d i x y) :
    0 < d j (ϕ.func x) (ϕ.func y) := by
  have hterm : K i j * d i x y ≤ ∑ k : I, K k j * d k x y := by
    exact Finset.single_le_sum (fun k _ => zero_le (K k j * d k x y)) (Finset.mem_univ i)
  have hpos : 0 < K i j * d i x y := ENNReal.mul_pos hKpos.ne' hdist.ne'
  exact hpos.trans_le (hterm.trans (hK.2.2 x hx y hy j))

/-- HC02-P32.  Positive diagonal co-Lip channels reflect the family zero
relation. -/
theorem positive_diagonal_coLip_reflects {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (K : BoundMatrix I)
    (hK : K ∈ restrictedCoLipCertificates d ϕ U)
    (hdiag : ∀ j : I, 0 < K j j) (x y : X) (hx : x ∈ U) (hy : y ∈ U)
    (hzero : GaugeZeroRelated d (ϕ.func x) (ϕ.func y)) :
    GaugeZeroRelated d x y := by
  intro j
  by_contra hj
  have hpos : 0 < d j x y := pos_iff_ne_zero.mpr hj
  have hout := positive_coLip_channel d ϕ U K hK (hdiag j) x y hx hy hpos
  exact hout.ne' (hzero j)

end formal_oet.vol_01.ch_02_operator_bounds
