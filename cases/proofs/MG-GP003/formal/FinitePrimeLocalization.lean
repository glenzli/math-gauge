import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.Sets.Opens
import Mathlib.Tactic

/-!
The actual affine localization in MG-P003, over an arbitrary commutative ring.
This module proves ring/spectrum facts; it does not define finite correspondences
or prove the motivic sheafification comparison.
-/

namespace MathGauge.PublicProof.Semilocal

open Set

variable {R : Type*} [CommRing R]

/-- The complement of the union of the finitely many selected prime ideals. -/
def outside_primes (sigma : Finset (PrimeSpectrum R)) : Submonoid R where
  carrier := {a | ∀ p ∈ sigma, a ∉ p.asIdeal}
  one_mem' := by
    intro p _
    exact p.isPrime.one_notMem
  mul_mem' := by
    intro a b ha hb p hp hab
    exact (p.isPrime.mem_or_mem hab).elim (ha p hp) (hb p hp)

@[simp]
theorem mem_outside_primes (sigma : Finset (PrimeSpectrum R)) (a : R) :
    a ∈ outside_primes sigma ↔ ∀ p ∈ sigma, a ∉ p.asIdeal := Iff.rfl

/-- Finite prime avoidance identifies precisely the ideals disjoint from the
localizing monoid. The selected points need not be closed in the ambient spectrum. -/
theorem disjoint_outside_primes_iff (sigma : Finset (PrimeSpectrum R))
    (hsigma : sigma.Nonempty) (I : Ideal R) :
    Disjoint (outside_primes sigma : Set R) (I : Set R) ↔
      ∃ p ∈ sigma, I ≤ p.asIdeal := by
  classical
  obtain ⟨p₀, hp₀⟩ := hsigma
  constructor
  · intro hd
    apply (Ideal.subset_union_prime (f := PrimeSpectrum.asIdeal) p₀ p₀
      (fun p _ _ _ => p.isPrime)).mp
    intro a ha
    by_contra h
    have hm : a ∈ outside_primes sigma := by
      intro p hp hap
      exact h (Set.mem_iUnion₂.mpr ⟨p, hp, hap⟩)
    exact Set.disjoint_left.mp hd hm ha
  · rintro ⟨p, hp, hIp⟩
    exact Set.disjoint_left.mpr fun a ha hI => ha p hp (hIp hI)

/-- The ring appearing in the task's definition of its semilocal scheme. -/
abbrev finite_prime_localization (sigma : Finset (PrimeSpectrum R)) :=
  Localization (outside_primes sigma)

section Localization

variable (sigma : Finset (PrimeSpectrum R)) (hsigma : sigma.Nonempty)
variable (L : Type*) [CommRing L] [Algebra R L] [IsLocalization (outside_primes sigma) L]

include hsigma

/-- Every point of the localized spectrum maps to a generalization of a selected point. -/
theorem localization_prime_below_selected (q : PrimeSpectrum L) :
    ∃ p ∈ sigma, Ideal.comap (algebraMap R L) q.asIdeal ≤ p.asIdeal := by
  apply (disjoint_outside_primes_iff sigma hsigma _).mp
  exact ((IsLocalization.isPrime_iff_isPrime_disjoint (outside_primes sigma) L q.asIdeal).mp
    q.isPrime).2

/-- The full image of the spectrum map is the union of the generalizations
of the selected points, not the set of selected points alone. -/
theorem localization_spectrum_image_iff (p : PrimeSpectrum R) :
    (∃ q : PrimeSpectrum L, PrimeSpectrum.comap (algebraMap R L) q = p) ↔
      ∃ q ∈ sigma, p.asIdeal ≤ q.asIdeal := by
  constructor
  · rintro ⟨q, rfl⟩
    exact localization_prime_below_selected sigma hsigma L q
  · intro hp
    have hd := (disjoint_outside_primes_iff sigma hsigma p.asIdeal).mpr hp
    refine ⟨⟨Ideal.map (algebraMap R L) p.asIdeal,
      IsLocalization.isPrime_of_isPrime_disjoint (outside_primes sigma) L _ p.isPrime hd⟩, ?_⟩
    apply PrimeSpectrum.ext
    exact IsLocalization.under_map_of_isPrime_disjoint (outside_primes sigma) L p.isPrime hd

/-- A maximal ideal of the localization contracts to one of the selected
prime ideals. The selected ambient prime itself need not be maximal. -/
theorem localization_maximal_contracts_to_selected (q : Ideal L) (hq : q.IsMaximal) :
    ∃ p ∈ sigma, Ideal.comap (algebraMap R L) q = p.asIdeal := by
  obtain ⟨p, hp, hle⟩ := localization_prime_below_selected sigma hsigma L ⟨q, hq.isPrime⟩
  have hd : Disjoint (outside_primes sigma : Set R) (p.asIdeal : Set R) :=
    (disjoint_outside_primes_iff sigma hsigma _).mpr ⟨p, hp, le_rfl⟩
  have hprime := IsLocalization.isPrime_of_isPrime_disjoint
    (outside_primes sigma) L p.asIdeal p.isPrime hd
  have hmap : q ≤ Ideal.map (algebraMap R L) p.asIdeal := by
    calc
      q = Ideal.map (algebraMap R L) (Ideal.comap (algebraMap R L) q) :=
        (IsLocalization.map_comap (outside_primes sigma) L q).symm
      _ ≤ Ideal.map (algebraMap R L) p.asIdeal := Ideal.map_mono hle
  have heq := hq.eq_of_le hprime.ne_top hmap
  refine ⟨p, hp, ?_⟩
  rw [heq]
  exact IsLocalization.under_map_of_isPrime_disjoint (outside_primes sigma) L p.isPrime hd

/-- The actual closed-point set of the localized affine scheme is finite. -/
theorem finite_localization_closed_points :
    Set.Finite {q : PrimeSpectrum L | IsClosed ({q} : Set (PrimeSpectrum L))} := by
  have hinj : Function.Injective (PrimeSpectrum.comap (algebraMap R L)) := by
    intro q q' h
    apply PrimeSpectrum.ext
    apply (IsLocalization.orderEmbedding (outside_primes sigma) L).injective
    exact congrArg PrimeSpectrum.asIdeal h
  apply Set.Finite.of_finite_image (f := PrimeSpectrum.comap (algebraMap R L)) ?_ hinj.injOn
  apply sigma.finite_toSet.subset
  rintro p ⟨q, hq, rfl⟩
  obtain ⟨p, hp, heq⟩ := localization_maximal_contracts_to_selected sigma hsigma L q.asIdeal
    ((PrimeSpectrum.isClosed_singleton_iff_isMaximal q).mp hq)
  have heq' : PrimeSpectrum.comap (algebraMap R L) q = p := PrimeSpectrum.ext heq
  simpa only [heq', Finset.mem_coe] using hp

/-- Closed points are exactly the selected primes maximal under inclusion.
This keeps the distinction between closedness in the localization and in R. -/
theorem maximal_map_selected_iff (p : PrimeSpectrum R) (hp : p ∈ sigma) :
    (Ideal.map (algebraMap R L) p.asIdeal).IsMaximal ↔
      ∀ q ∈ sigma, p.asIdeal ≤ q.asIdeal → p = q := by
  have hd : Disjoint (outside_primes sigma : Set R) (p.asIdeal : Set R) :=
    (disjoint_outside_primes_iff sigma hsigma _).mpr ⟨p, hp, le_rfl⟩
  have hprime := IsLocalization.isPrime_of_isPrime_disjoint
    (outside_primes sigma) L p.asIdeal p.isPrime hd
  have hcontract :
      Ideal.comap (algebraMap R L) (Ideal.map (algebraMap R L) p.asIdeal) = p.asIdeal :=
    IsLocalization.under_map_of_isPrime_disjoint
    (outside_primes sigma) L p.isPrime hd
  constructor
  · intro hmax q hq hle
    have hdq : Disjoint (outside_primes sigma : Set R) (q.asIdeal : Set R) :=
      (disjoint_outside_primes_iff sigma hsigma _).mpr ⟨q, hq, le_rfl⟩
    have hprimeq := IsLocalization.isPrime_of_isPrime_disjoint
      (outside_primes sigma) L q.asIdeal q.isPrime hdq
    have heq := hmax.eq_of_le hprimeq.ne_top (Ideal.map_mono hle)
    apply PrimeSpectrum.ext
    calc
      p.asIdeal = Ideal.comap (algebraMap R L) (Ideal.map (algebraMap R L) p.asIdeal) :=
        hcontract.symm
      _ = Ideal.comap (algebraMap R L) (Ideal.map (algebraMap R L) q.asIdeal) :=
        congrArg _ heq
      _ = q.asIdeal := IsLocalization.under_map_of_isPrime_disjoint
        (outside_primes sigma) L q.isPrime hdq
  · intro hmax
    obtain ⟨m, hm, hle⟩ := (Ideal.map (algebraMap R L) p.asIdeal).exists_le_maximal
      hprime.ne_top
    obtain ⟨q, hq, hmq⟩ := localization_maximal_contracts_to_selected sigma hsigma L m hm
    have hpq : p.asIdeal ≤ q.asIdeal := by
      rw [← hmq, ← hcontract]
      exact Ideal.comap_mono hle
    have hpq' := hmax q hq hpq
    have heq : Ideal.map (algebraMap R L) p.asIdeal = m := by
      apply (IsLocalization.orderEmbedding (outside_primes sigma) L).injective
      change Ideal.comap (algebraMap R L) (Ideal.map (algebraMap R L) p.asIdeal) =
        Ideal.comap (algebraMap R L) m
      rw [hcontract, hmq, hpq']
    exact heq.symm ▸ hm

/-- A nonempty selected point set gives at least one closed point after localization. -/
theorem nonempty_localization_closed_points :
    Set.Nonempty {q : PrimeSpectrum L | IsClosed ({q} : Set (PrimeSpectrum L))} := by
  obtain ⟨p, hp⟩ := hsigma
  have hd : Disjoint (outside_primes sigma : Set R) (p.asIdeal : Set R) :=
    (disjoint_outside_primes_iff sigma ⟨p, hp⟩ _).mpr ⟨p, hp, le_rfl⟩
  have hprime := IsLocalization.isPrime_of_isPrime_disjoint
    (outside_primes sigma) L p.asIdeal p.isPrime hd
  obtain ⟨m, hm, _⟩ := (Ideal.map (algebraMap R L) p.asIdeal).exists_le_maximal hprime.ne_top
  exact ⟨⟨m, hm.isPrime⟩, (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr hm⟩

end Localization

/-- In an affine spectrum, any open set containing all closed points is the
whole spectrum. This applies to every open in the semilocal spectrum. -/
theorem open_eq_top_of_contains_closed (U : TopologicalSpace.Opens (PrimeSpectrum R))
    (hU : ∀ x : PrimeSpectrum R, IsClosed ({x} : Set (PrimeSpectrum R)) → x ∈ U) :
    U = ⊤ := by
  ext p
  constructor
  · intro _
    trivial
  · intro _
    obtain ⟨m, hm, hpm⟩ := p.asIdeal.exists_le_maximal p.isPrime.ne_top
    have hclosed : IsClosed ({(⟨m, hm.isPrime⟩ : PrimeSpectrum R)} : Set (PrimeSpectrum R)) :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr hm
    exact ((PrimeSpectrum.le_iff_specializes p ⟨m, hm.isPrime⟩).mp hpm).mem_open U.isOpen
      (hU _ hclosed)

end MathGauge.PublicProof.Semilocal
