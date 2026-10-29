import Mathlib.RingTheory.Idempotents
import Mathlib.Tactic

namespace MathGauge.R104

universe u v w
variable {I : Type u} [Preorder I] {R : I → Type v} [∀ i, CommRing (R i)]
variable {S : Type w} [CommRing S]

/-- Actual augmented inverse system; only the stagewise kernels are assumed nil. -/
structure System (I : Type u) [Preorder I] (R : I → Type v) [∀ i, CommRing (R i)]
    (S : Type w) [CommRing S] where
  transition : ∀ {i j : I}, i ≤ j → R j →+* R i
  transition_id : ∀ i (x : R i), transition (le_refl i) x = x
  transition_comp : ∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) (x : R k),
    transition hij (transition hjk x) = transition (hij.trans hjk) x
  augmentation : ∀ i, R i →+* S
  augmentation_surjective : ∀ i, Function.Surjective (augmentation i)
  augmentation_transition : ∀ {i j : I} (hij : i ≤ j) (x : R j),
    augmentation i (transition hij x) = augmentation j x
  nil_kernel : ∀ i x, augmentation i x = 0 → IsNilpotent x

namespace System

variable (D : System I R S)

/-- The inverse limit as a subring of the actual dependent product. -/
def limit_ring : Subring (∀ i, R i) where
  carrier := {x | ∀ i j (h : i ≤ j), D.transition h (x j) = x i}
  one_mem' := by
    intro i j h
    exact map_one (D.transition h)
  mul_mem' := by
    intro a b ha hb i j h
    change D.transition h (a j * b j) = a i * b i
    rw [map_mul, ha i j h, hb i j h]
  zero_mem' := by
    intro i j h
    exact map_zero (D.transition h)
  add_mem' := by
    intro a b ha hb i j h
    change D.transition h (a j + b j) = a i + b i
    rw [map_add, ha i j h, hb i j h]
  neg_mem' := by
    intro a ha i j h
    change D.transition h (-a j) = -a i
    rw [map_neg, ha i j h]

abbrev Limit := D.limit_ring

def evaluation (i : I) : D.Limit →+* R i where
  toFun x := x.1 i
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def limit_augmentation (i : I) : D.Limit →+* S :=
  (D.augmentation i).comp (D.evaluation i)

theorem augmentation_independent
    (directed : ∀ i j : I, ∃ k, i ≤ k ∧ j ≤ k)
    (i j : I) (x : D.Limit) : D.limit_augmentation i x = D.limit_augmentation j x := by
  obtain ⟨k, hik, hjk⟩ := directed i j
  change D.augmentation i (x.1 i) = D.augmentation j (x.1 j)
  rw [← x.2 i k hik, ← x.2 j k hjk,
    D.augmentation_transition, D.augmentation_transition]

theorem stage_idempotent_ext (i : I) {a b : R i}
    (ha : IsIdempotentElem a) (hb : IsIdempotentElem b)
    (hab : D.augmentation i a = D.augmentation i b) : a = b := by
  apply eq_of_isNilpotent_sub_of_isIdempotentElem ha hb
  apply D.nil_kernel i
  rw [map_sub, hab, sub_self]

omit [Preorder I] in
/-- The correction identity works in arbitrary characteristic, with no division. -/
theorem improvement_identity (i : I) (a : R i) :
    (3 * a ^ 2 - 2 * a ^ 3) ^ 2 - (3 * a ^ 2 - 2 * a ^ 3) =
      (4 * a ^ 2 - 4 * a - 3) * (a ^ 2 - a) ^ 2 := by ring

theorem stage_lift_exists (i : I) (e : S) (he : IsIdempotentElem e) :
    ∃! a : R i, IsIdempotentElem a ∧ D.augmentation i a = e := by
  apply existsUnique_isIdempotentElem_eq_of_ker_isNilpotent (D.augmentation i)
  · intro a ha
    exact D.nil_kernel i a ha
  · exact D.augmentation_surjective i e
  · exact he

noncomputable def stage_lift (i : I) (e : S) (he : IsIdempotentElem e) : R i :=
  (D.stage_lift_exists i e he).exists.choose

theorem stage_lift_idempotent (i : I) (e : S) (he : IsIdempotentElem e) :
    IsIdempotentElem (D.stage_lift i e he) :=
  (D.stage_lift_exists i e he).exists.choose_spec.1

theorem stage_lift_image (i : I) (e : S) (he : IsIdempotentElem e) :
    D.augmentation i (D.stage_lift i e he) = e :=
  (D.stage_lift_exists i e he).exists.choose_spec.2

theorem stage_lift_compatible {i j : I} (h : i ≤ j) (e : S) (he : IsIdempotentElem e) :
    D.transition h (D.stage_lift j e he) = D.stage_lift i e he := by
  apply D.stage_idempotent_ext i ((D.stage_lift_idempotent j e he).map (D.transition h))
    (D.stage_lift_idempotent i e he)
  rw [D.augmentation_transition, D.stage_lift_image, D.stage_lift_image]

noncomputable def limit_lift (e : S) (he : IsIdempotentElem e) : D.Limit :=
  ⟨fun i => D.stage_lift i e he, fun _ _ h => D.stage_lift_compatible h e he⟩

theorem limit_lift_idempotent (e : S) (he : IsIdempotentElem e) :
    IsIdempotentElem (D.limit_lift e he) := by
  apply Subtype.ext
  funext i
  exact (D.stage_lift_idempotent i e he).eq

theorem limit_lift_image (i : I) (e : S) (he : IsIdempotentElem e) :
    D.limit_augmentation i (D.limit_lift e he) = e := D.stage_lift_image i e he

theorem limit_idempotent_ext
    (directed : ∀ i j : I, ∃ k, i ≤ k ∧ j ≤ k) (i₀ : I)
    {a b : D.Limit} (ha : IsIdempotentElem a) (hb : IsIdempotentElem b)
    (hab : D.limit_augmentation i₀ a = D.limit_augmentation i₀ b) : a = b := by
  apply Subtype.ext
  funext i
  apply D.stage_idempotent_ext i (ha.map (D.evaluation i)) (hb.map (D.evaluation i))
  change D.limit_augmentation i a = D.limit_augmentation i b
  rw [D.augmentation_independent directed i i₀ a,
    D.augmentation_independent directed i i₀ b, hab]

/-- Every base idempotent has one coherent lift, even when the limit kernel is not nil. -/
theorem unique_limit_lift
    (directed : ∀ i j : I, ∃ k, i ≤ k ∧ j ≤ k) (i₀ : I)
    (e : S) (he : IsIdempotentElem e) :
    ∃! a : D.Limit, IsIdempotentElem a ∧ D.limit_augmentation i₀ a = e := by
  refine ⟨D.limit_lift e he, ⟨D.limit_lift_idempotent e he, D.limit_lift_image i₀ e he⟩, ?_⟩
  intro a ha
  exact D.limit_idempotent_ext directed i₀ ha.1 (D.limit_lift_idempotent e he)
    (ha.2.trans (D.limit_lift_image i₀ e he).symm)

section FiniteDecompositions
variable {J : Type*} [Fintype J]

noncomputable def lift_family (e : J → S) (he : CompleteOrthogonalIdempotents e) : J → D.Limit :=
  fun j => D.limit_lift (e j) (he.idem j)

theorem lift_family_complete
    (directed : ∀ i j : I, ∃ k, i ≤ k ∧ j ≤ k) (i₀ : I)
    (e : J → S) (he : CompleteOrthogonalIdempotents e) :
    CompleteOrthogonalIdempotents (D.lift_family e he) := by
  have hi : ∀ j, IsIdempotentElem (D.lift_family e he j) :=
    fun j => D.limit_lift_idempotent (e j) (he.idem j)
  have ho : OrthogonalIdempotents (D.lift_family e he) := by
    refine ⟨hi, ?_⟩
    intro j k hjk
    apply D.limit_idempotent_ext directed i₀ ((hi j).mul (hi k)) IsIdempotentElem.zero
    rw [map_mul, map_zero]
    change D.limit_augmentation i₀ (D.limit_lift (e j) (he.idem j)) *
      D.limit_augmentation i₀ (D.limit_lift (e k) (he.idem k)) = 0
    rw [D.limit_lift_image, D.limit_lift_image, he.ortho hjk]
  refine ⟨ho, ?_⟩
  apply D.limit_idempotent_ext directed i₀
    (ho.isIdempotentElem_sum (s := Finset.univ)) IsIdempotentElem.one
  rw [map_sum, map_one]
  simpa only [lift_family, limit_lift_image] using he.complete

theorem unique_lift_family
    (directed : ∀ i j : I, ∃ k, i ≤ k ∧ j ≤ k) (i₀ : I)
    (e : J → S) (he : CompleteOrthogonalIdempotents e) :
    ∃! a : J → D.Limit, CompleteOrthogonalIdempotents a ∧
      ∀ j, D.limit_augmentation i₀ (a j) = e j := by
  refine ⟨D.lift_family e he,
    ⟨D.lift_family_complete directed i₀ e he, fun j => D.limit_lift_image i₀ _ _⟩, ?_⟩
  intro a ha
  funext j
  exact D.limit_idempotent_ext directed i₀ (ha.1.idem j)
    (D.limit_lift_idempotent (e j) (he.idem j))
    ((ha.2 j).trans (D.limit_lift_image i₀ _ _).symm)

/-- The canonical quotient-factor map is a bijective ring homomorphism. -/
theorem lifted_product_decomposition
    (directed : ∀ i j : I, ∃ k, i ≤ k ∧ j ≤ k) (i₀ : I)
    (e : J → S) (he : CompleteOrthogonalIdempotents e) :
    Function.Bijective (Pi.ringHom fun j =>
      Ideal.Quotient.mk (Ideal.span {1 - D.lift_family e he j})) :=
  (D.lift_family_complete directed i₀ e he).bijective_pi

noncomputable def lifted_product_equiv
    (directed : ∀ i j : I, ∃ k, i ≤ k ∧ j ≤ k) (i₀ : I)
    (e : J → S) (he : CompleteOrthogonalIdempotents e) :
    D.Limit ≃+* (∀ j : J, D.Limit ⧸ Ideal.span {1 - D.lift_family e he j}) :=
  RingEquiv.ofBijective _ (D.lifted_product_decomposition directed i₀ e he)

end FiniteDecompositions

section Naturality
variable {T : Type*} [CommRing T]
variable {R' : I → Type*} [∀ i, CommRing (R' i)]
variable (E : System I R' T)

/-- A morphism of the actual inverse systems and their base rings. -/
structure Morphism (D : System I R S) (E : System I R' T) where
  base : S →+* T
  component : ∀ i, R i →+* R' i
  component_transition : ∀ {i j : I} (h : i ≤ j) (x : R j),
    component i (D.transition h x) = E.transition h (component j x)
  augmentation_component : ∀ i (x : R i),
    E.augmentation i (component i x) = base (D.augmentation i x)

variable (f : Morphism D E)

def map_limit : D.Limit →+* E.Limit where
  toFun x := ⟨fun i => f.component i (x.1 i), by
    intro i j h
    rw [← f.component_transition, x.2 i j h]⟩
  map_one' := by ext i; exact map_one _
  map_mul' a b := by ext i; exact map_mul _ _ _
  map_zero' := by ext i; exact map_zero _
  map_add' a b := by ext i; exact map_add _ _ _

theorem augmentation_map_limit (i : I) (x : D.Limit) :
    E.limit_augmentation i (D.map_limit E f x) = f.base (D.limit_augmentation i x) :=
  f.augmentation_component i (x.1 i)

/-- Uniqueness gives naturality; no preferred representatives of general ring elements are used. -/
theorem lift_natural (e : S) (he : IsIdempotentElem e) :
    D.map_limit E f (D.limit_lift e he) = E.limit_lift (f.base e) (he.map f.base) := by
  apply Subtype.ext
  funext i
  apply E.stage_idempotent_ext i
    ((D.stage_lift_idempotent i e he).map (f.component i))
    (E.stage_lift_idempotent i (f.base e) (he.map f.base))
  change E.augmentation i (f.component i (D.stage_lift i e he)) =
    E.augmentation i (E.stage_lift i (f.base e) (he.map f.base))
  rw [f.augmentation_component, D.stage_lift_image, E.stage_lift_image]

theorem lift_family_natural {J : Type*} [Fintype J]
    (e : J → S) (he : CompleteOrthogonalIdempotents e) (j : J) :
    D.map_limit E f (D.lift_family e he j) =
      E.lift_family (f.base ∘ e) (he.map f.base) j := by
  exact D.lift_natural E f (e j) (he.idem j)

end Naturality

end System

end MathGauge.R104
