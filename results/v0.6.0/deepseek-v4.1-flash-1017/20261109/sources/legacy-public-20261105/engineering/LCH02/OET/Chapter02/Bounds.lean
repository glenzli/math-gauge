import OET.Chapter02.Matrix

/-!
# Chapter 2: Lipschitz and co-Lipschitz matrix certificates

The predicates below follow the source convention: `L i j` (respectively
`K i j`) is the coefficient from input component `i` to output component `j`.
All inequalities involving `L` are upper bounds and all inequalities involving
`K` are lower bounds.
-/

namespace OET.Chapter02

open formal_oet.vol_01.ch_01_foundations

noncomputable section

variable {X : Type} {I : Type} [Fintype I] [DecidableEq I] {bot : X}

/-- A Lip matrix certificate on a restricted set `U ⊆ dom φ`. -/
def IsLipOn (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X)
    (L : Mat I) : Prop :=
  U ⊆ dom φ ∧
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      d j (φ.func x) (φ.func y) ≤ ∑ i, L i j * d i x y

/-- A full-domain Lip certificate. -/
def IsLip (d : I → X → X → ENNReal) (φ : Operator X bot) (L : Mat I) : Prop :=
  IsLipOn d φ (dom φ) L

/-- The family of all restricted Lip certificates of `φ` on `U`. -/
def lipCertsOn (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) :
    Set (Mat I) :=
  {L | IsLipOn d φ U L}

/-- The family of all full-domain Lip certificates of `φ`. -/
def lipCerts (d : I → X → X → ENNReal) (φ : Operator X bot) : Set (Mat I) :=
  {L | IsLip d φ L}

/-- A restricted co-Lip certificate.  The nonemptiness condition is part of the
predicate, as in the source definition of `𝓚(φ)|_U`. -/
def IsCoLipOn (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X)
    (K : Mat I) : Prop :=
  U.Nonempty ∧ U ⊆ dom φ ∧
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      (∑ i, K i j * d i x y) ≤ d j (φ.func x) (φ.func y)

/-- A full-domain co-Lip certificate. -/
def IsCoLip (d : I → X → X → ENNReal) (φ : Operator X bot) (K : Mat I) : Prop :=
  IsCoLipOn d φ (dom φ) K

/-- The family of all restricted co-Lip certificates of `φ` on `U`. -/
def coLipCertsOn (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) :
    Set (Mat I) :=
  {K | IsCoLipOn d φ U K}

/-- The family of all full-domain co-Lip certificates of `φ`. -/
def coLipCerts (d : I → X → X → ENNReal) (φ : Operator X bot) : Set (Mat I) :=
  {K | IsCoLip d φ K}

/-- In the single-component case the Lip sum has one summand. -/
theorem lip_single_component_scalar [Unique I]
    (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) (L : Mat I)
    (i : I) (hL : IsLipOn d φ U L) :
    ∀ x ∈ U, ∀ y ∈ U,
      d i (φ.func x) (φ.func y) ≤ L i i * d i x y := by
  intro x hx y hy
  have hsum : (∑ k : I, L k i * d k x y) = L i i * d i x y := by
    apply Finset.sum_eq_single (s := Finset.univ) (a := i)
      (f := fun k : I => L k i * d k x y)
    · intro k _ hki
      exact False.elim (hki (Subsingleton.elim k i))
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  have h := hL.2 x hx y hy i
  rw [hsum] at h
  exact h

/-- Restricted Lip certificate families are antitone in the restricted set. -/
theorem lipCertsOn_antitone
    (d : I → X → X → ENNReal) (φ : Operator X bot) {U V : Set X}
    (hUV : U ⊆ V) (_hV : V ⊆ dom φ) :
    lipCertsOn d φ V ⊆ lipCertsOn d φ U := by
  intro L hL
  exact ⟨fun x hx => hL.1 (hUV hx),
    fun x hx y hy j => hL.2 x (hUV hx) y (hUV hy) j⟩

/-- A full-domain Lip certificate restricts to every subset of the domain. -/
theorem lipCerts_subset_lipCertsOn
    (d : I → X → X → ENNReal) (φ : Operator X bot) {U : Set X}
    (hU : U ⊆ dom φ) :
    lipCerts d φ ⊆ lipCertsOn d φ U := by
  intro L hL
  exact ⟨fun x hx => hL.1 (hU hx),
    fun x hx y hy j => hL.2 x (hU hx) y (hU hy) j⟩

/-- Restricted co-Lip certificate families are antitone, with the source's
nonemptiness hypotheses made explicit. -/
theorem coLipCertsOn_antitone
    (d : I → X → X → ENNReal) (φ : Operator X bot) {U V : Set X}
    (hUne : U.Nonempty) (hUV : U ⊆ V) (_hV : V ⊆ dom φ) (_hVne : V.Nonempty) :
    coLipCertsOn d φ V ⊆ coLipCertsOn d φ U := by
  intro K hK
  exact ⟨hUne, fun x hx => hK.2.1 (hUV hx),
    fun x hx y hy j => hK.2.2 x (hUV hx) y (hUV hy) j⟩

/-- A full-domain co-Lip certificate restricts to every nonempty subset of the
domain. -/
theorem coLipCerts_subset_coLipCertsOn
    (d : I → X → X → ENNReal) (φ : Operator X bot) {U : Set X}
    (hUne : U.Nonempty) (hU : U ⊆ dom φ) :
    coLipCerts d φ ⊆ coLipCertsOn d φ U := by
  intro K hK
  exact ⟨hUne, hU,
    fun x hx y hy j => hK.2.2 x (hU hx) y (hU hy) j⟩

/-- A zero output distance together with a positive input distance forces the
corresponding co-Lip coefficient to vanish. -/
theorem coLip_entry_eq_zero_of_output_zero_input_pos
    (d : I → X → X → ENNReal) (φ : Operator X bot) (K : Mat I)
    (hK : IsCoLip d φ K) {i j : I} {x y : X}
    (hx : x ∈ dom φ) (hy : y ∈ dom φ)
    (hout : d j (φ.func x) (φ.func y) = 0)
    (hin : 0 < d i x y) :
    K i j = 0 := by
  have hterm : K i j * d i x y ≤ ∑ k, K k j * d k x y :=
    Finset.single_le_sum (f := fun k : I => K k j * d k x y)
      (fun k _ => zero_le _) (Finset.mem_univ i)
  have hle : K i j * d i x y ≤ 0 := by
    calc
      K i j * d i x y ≤ ∑ k, K k j * d k x y := hterm
      _ ≤ d j (φ.func x) (φ.func y) := hK.2.2 x hx y hy j
      _ = 0 := hout
  have hzero : K i j * d i x y = 0 := le_antisymm hle (zero_le _)
  by_contra hKij
  have hpos : 0 < K i j * d i x y :=
    ENNReal.mul_pos hKij (ne_of_gt hin)
  exact (ne_of_gt hpos) hzero

/-- The sum produced by the identity matrix collapses to the corresponding
component distance. -/
lemma matId_sum_dist (d : I → X → X → ENNReal) (x y : X) (j : I) :
    (∑ i : I, matId i j * d i x y) = d j x y := by
  simp [matId, Finset.sum_ite_eq']

/-- The identity matrix is a Lip certificate for the identity operator on every
subset of the identity operator's domain. -/
theorem lip_identity
    (d : I → X → X → ENNReal) (U : Set X)
    (hU : U ⊆ dom (1 : Operator X bot)) :
    IsLipOn d (1 : Operator X bot) U matId := by
  refine ⟨hU, ?_⟩
  intro x hx y hy j
  rw [matId_sum_dist]
  rfl

/-- The identity matrix is a co-Lip certificate for the identity operator on
every nonempty subset of its domain. -/
theorem coLip_identity
    (d : I → X → X → ENNReal) (U : Set X) (hUne : U.Nonempty)
    (hU : U ⊆ dom (1 : Operator X bot)) :
    IsCoLipOn d (1 : Operator X bot) U matId := by
  refine ⟨hUne, hU, ?_⟩
  intro x hx y hy j
  rw [matId_sum_dist]
  rfl

theorem matId_mem_lipCertsOn_identity
    (d : I → X → X → ENNReal) (U : Set X)
    (hU : U ⊆ dom (1 : Operator X bot)) :
    matId ∈ lipCertsOn d (1 : Operator X bot) U :=
  lip_identity d U hU

theorem matId_mem_coLipCertsOn_identity
    (d : I → X → X → ENNReal) (U : Set X) (hUne : U.Nonempty)
    (hU : U ⊆ dom (1 : Operator X bot)) :
    matId ∈ coLipCertsOn d (1 : Operator X bot) U :=
  coLip_identity d U hUne hU


/-- The domain of a composite is contained in the domain of its inner
operator. -/
lemma dom_mul_subset_right {X : Type} {bot : X} (φ ψ : Operator X bot) :
    dom (φ * ψ) ⊆ dom ψ := by
  intro x hx
  dsimp [dom] at hx ⊢
  change φ.func (ψ.func x) ≠ bot at hx
  intro hψ
  rw [hψ, φ.preserves_bot] at hx
  exact hx rfl

/-- The actual intermediate image of a composite is contained in the outer
operator's domain. -/
lemma image_subset_dom_of_subset_dom_comp
    {X : Type} {bot : X} (φ₁ φ₂ : Operator X bot) {U : Set X}
    (hU : U ⊆ dom (φ₂ * φ₁)) :
    φ₁.func '' U ⊆ dom φ₂ := by
  rintro _ ⟨x, hx, rfl⟩
  have hx' := hU hx
  dsimp [dom] at hx' ⊢
  exact hx'

/-- Reassociate the double sum appearing in a two-step matrix bound.  This is
the ENNReal form of distributing a finite sum and exchanging summations. -/
lemma sum_comp_coeff {I : Type} [Fintype I]
    (A B : Mat I) (f : I → ENNReal) (j : I) :
    (∑ k, A k j * (∑ i, B i k * f i)) =
      ∑ i, (∑ k, A k j * B i k) * f i := by
  calc
    (∑ k, A k j * (∑ i, B i k * f i))
        = ∑ k, ∑ i, A k j * (B i k * f i) := by
            apply Finset.sum_congr rfl
            intro k _
            rw [Finset.mul_sum]
    _ = ∑ i, ∑ k, A k j * (B i k * f i) := Finset.sum_comm
    _ = ∑ i, ∑ k, (A k j * B i k) * f i := by
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro k _
            rw [mul_assoc]
    _ = ∑ i, (∑ k, A k j * B i k) * f i := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_mul]

/-- Proposition 2.2: the two-step Lip composition law with the exact
intermediate image `φ₁ '' U₁`, and with the matrix product in the order
`L₂ · L₁`. -/
theorem lip_comp_two
    (d : I → X → X → ENNReal) (φ₁ φ₂ : Operator X bot)
    (U₁ U₂ : Set X) (L₁ L₂ : Mat I)
    (hU₂ : U₂ = φ₁.func '' U₁)
    (hcomp : U₁ ⊆ dom (φ₂ * φ₁))
    (h₁ : IsLipOn d φ₁ U₁ L₁)
    (h₂ : IsLipOn d φ₂ U₂ L₂) :
    IsLipOn d (φ₂ * φ₁) U₁ (matMul L₂ L₁) := by
  refine ⟨hcomp, ?_⟩
  intro x hx y hy j
  have hx₂ : φ₁.func x ∈ U₂ := by
    rw [hU₂]
    exact ⟨x, hx, rfl⟩
  have hy₂ : φ₁.func y ∈ U₂ := by
    rw [hU₂]
    exact ⟨y, hy, rfl⟩
  have h₂ineq :
      d j (φ₂.func (φ₁.func x)) (φ₂.func (φ₁.func y)) ≤
        ∑ k, L₂ k j * d k (φ₁.func x) (φ₁.func y) :=
    h₂.2 (φ₁.func x) hx₂ (φ₁.func y) hy₂ j
  have h₁ineq :
      ∀ k : I, d k (φ₁.func x) (φ₁.func y) ≤
        ∑ i, L₁ i k * d i x y :=
    fun k => h₁.2 x hx y hy k
  calc
    d j ((φ₂ * φ₁).func x) ((φ₂ * φ₁).func y)
        = d j (φ₂.func (φ₁.func x)) (φ₂.func (φ₁.func y)) := rfl
    _ ≤ ∑ k, L₂ k j * d k (φ₁.func x) (φ₁.func y) := h₂ineq
    _ ≤ ∑ k, L₂ k j * (∑ i, L₁ i k * d i x y) := by
          apply Finset.sum_le_sum
          intro k _
          exact mul_le_mul_right (h₁ineq k) (L₂ k j)
    _ = ∑ i, matMul L₂ L₁ i j * d i x y := by
          rw [sum_comp_coeff]
          rfl

/-- Proposition 2.4: the two-step co-Lip composition law with the exact
intermediate image `φ₁ '' U₁` and nonemptiness inherited from `U₁`. -/
theorem coLip_comp_two
    (d : I → X → X → ENNReal) (φ₁ φ₂ : Operator X bot)
    (U₁ U₂ : Set X) (K₁ K₂ : Mat I)
    (hU₂ : U₂ = φ₁.func '' U₁)
    (hcomp : U₁ ⊆ dom (φ₂ * φ₁))
    (h₁ : IsCoLipOn d φ₁ U₁ K₁)
    (h₂ : IsCoLipOn d φ₂ U₂ K₂) :
    IsCoLipOn d (φ₂ * φ₁) U₁ (matMul K₂ K₁) := by
  refine ⟨h₁.1, hcomp, ?_⟩
  intro x hx y hy j
  have hx₂ : φ₁.func x ∈ U₂ := by
    rw [hU₂]
    exact ⟨x, hx, rfl⟩
  have hy₂ : φ₁.func y ∈ U₂ := by
    rw [hU₂]
    exact ⟨y, hy, rfl⟩
  have h₂ineq :
      (∑ k, K₂ k j * d k (φ₁.func x) (φ₁.func y)) ≤
        d j (φ₂.func (φ₁.func x)) (φ₂.func (φ₁.func y)) :=
    h₂.2.2 (φ₁.func x) hx₂ (φ₁.func y) hy₂ j
  have h₁ineq :
      ∀ k : I, (∑ i, K₁ i k * d i x y) ≤
        d k (φ₁.func x) (φ₁.func y) :=
    fun k => h₁.2.2 x hx y hy k
  calc
    (∑ i, matMul K₂ K₁ i j * d i x y)
        = ∑ k, K₂ k j * (∑ i, K₁ i k * d i x y) := by
            rw [sum_comp_coeff]
            rfl
    _ ≤ ∑ k, K₂ k j * d k (φ₁.func x) (φ₁.func y) := by
          apply Finset.sum_le_sum
          intro k _
          exact mul_le_mul_right (h₁ineq k) (K₂ k j)
    _ ≤ d j (φ₂.func (φ₁.func x)) (φ₂.func (φ₁.func y)) := h₂ineq
    _ = d j ((φ₂ * φ₁).func x) ((φ₂ * φ₁).func y) := rfl

end

end OET.Chapter02
