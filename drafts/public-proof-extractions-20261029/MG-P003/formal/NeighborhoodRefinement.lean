import FinitePrimeLocalization

/-!
Open-neighborhood indexing facts used in the corrected shrinking argument.
The successful shrinking predicate is arbitrary; no geometric exactness theorem
is postulated or claimed here.
-/

namespace MathGauge.PublicProof.Semilocal

open Set TopologicalSpace

variable {X : Type*} [TopologicalSpace X]

/-- Open pairs separating two prescribed disjoint parts of the closed-point set. -/
def Separates (A B : Set X) (U V : Opens X) : Prop :=
  A ⊆ U ∧ Disjoint B (U : Set X) ∧ B ⊆ V ∧ Disjoint A (V : Set X)

/-- Intersections give common refinements of separating neighborhood pairs. -/
theorem separates_inter {A B : Set X} {U V U' V' : Opens X}
    (h : Separates A B U V) (h' : Separates A B U' V') :
    Separates A B (U ⊓ U') (V ⊓ V') := by
  refine ⟨fun x hx => ⟨h.1 hx, h'.1 hx⟩, ?_,
    (fun x hx => ⟨h.2.2.1 hx, h'.2.2.1 hx⟩), ?_⟩
  · exact Set.disjoint_left.mpr fun x hx hU => Set.disjoint_left.mp h.2.1 hx hU.1
  · exact Set.disjoint_left.mpr fun x hx hV => Set.disjoint_left.mp h.2.2.2 hx hV.1

/-- Shrinking the first open while retaining a cover cannot lose any point
of the first part, because the second open excludes that part. -/
theorem separates_shrink {A B : Set X} {U₀ U V : Opens X}
    (h : Separates A B U₀ V) (hsub : U ≤ U₀) (hcover : U ⊔ V = ⊤) :
    Separates A B U V := by
  refine ⟨?_, ?_, h.2.2.1, h.2.2.2⟩
  · intro x hx
    have hxcover : x ∈ U ⊔ V := by rw [hcover]; trivial
    rcases hxcover with hU | hV
    · exact hU
    · exact (Set.disjoint_left.mp h.2.2.2 hx hV).elim
  · exact Set.disjoint_left.mpr fun x hx hU => Set.disjoint_left.mp h.2.1 hx (hsub hU)

/-- Finite unions of closed points are closed without a T1 assumption on X. -/
theorem isClosed_finite_points {A : Set X} (hA : A.Finite)
    (hclosed : ∀ x ∈ A, IsClosed ({x} : Set X)) : IsClosed A := by
  simpa only [Set.biUnion_of_singleton] using hA.isClosed_biUnion hclosed

/-- Any pair of neighborhoods of the two parts can be refined to a pair
that excludes the other part. This proves the needed cofinality directly. -/
theorem exists_separating_refinement {A B : Set X} (hAB : Disjoint A B)
    (hA : IsClosed A) (hB : IsClosed B) (U V : Opens X)
    (hAU : A ⊆ U) (hBV : B ⊆ V) :
    ∃ U' V' : Opens X, U' ≤ U ∧ V' ≤ V ∧ Separates A B U' V' := by
  let U' : Opens X := U ⊓ ⟨Bᶜ, hB.isOpen_compl⟩
  let V' : Opens X := V ⊓ ⟨Aᶜ, hA.isOpen_compl⟩
  refine ⟨U', V', inf_le_left, inf_le_left, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact ⟨hAU hx, fun hxB => Set.disjoint_left.mp hAB hx hxB⟩
  · exact Set.disjoint_left.mpr fun x hx hU => hU.2 hx
  · intro x hx
    exact ⟨hBV hx, fun hxA => Set.disjoint_left.mp hAB hxA hx⟩
  · exact Set.disjoint_left.mpr fun x hx hV => hV.2 hx

section Spectrum

variable {R : Type*} [CommRing R]
variable {A B : Set (PrimeSpectrum R)}

/-- For a partition of all closed points of an affine spectrum, every
separating neighborhood pair is an open cover. -/
theorem separates_cover (hclosed : ∀ x : PrimeSpectrum R,
    IsClosed ({x} : Set (PrimeSpectrum R)) → x ∈ A ∪ B)
    {U V : Opens (PrimeSpectrum R)} (h : Separates A B U V) : U ⊔ V = ⊤ := by
  apply open_eq_top_of_contains_closed
  intro x hx
  exact (hclosed x hx).elim (fun hxA => Or.inl (h.1 hxA))
    (fun hxB => Or.inr (h.2.2.1 hxB))

/-- A successful first-open refinement property supplies successful stages
inside the same separating system. `P` is just a predicate; this theorem does
not assert that motivic Mayer--Vietoris exactness satisfies the premise. -/
theorem exists_successful_separating_refinement
    (hclosed : ∀ x : PrimeSpectrum R,
      IsClosed ({x} : Set (PrimeSpectrum R)) → x ∈ A ∪ B)
    (P : Opens (PrimeSpectrum R) → Opens (PrimeSpectrum R) → Prop)
    (hrefine : ∀ U V : Opens (PrimeSpectrum R), U ⊔ V = ⊤ →
      ∃ U' : Opens (PrimeSpectrum R), U' ≤ U ∧ U' ⊔ V = ⊤ ∧ P U' V)
    {U V : Opens (PrimeSpectrum R)} (h : Separates A B U V) :
    ∃ U' : Opens (PrimeSpectrum R),
      U' ≤ U ∧ Separates A B U' V ∧ P U' V := by
  obtain ⟨U', hsub, hcover, hP⟩ := hrefine U V (separates_cover hclosed h)
  exact ⟨U', hsub, separates_shrink h hsub hcover, hP⟩

end Spectrum

end MathGauge.PublicProof.Semilocal
