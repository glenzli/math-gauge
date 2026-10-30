/-
Copyright (c) 2026 Math Gauge contributors.
SPDX-License-Identifier: Apache-2.0

Author proof for GP003 S5. Native transfer interfaces and adapted auxiliary
arguments use Motivic a6805c4a87cdfd7717dd7a94039246a167f15380.
Upstream adapted portions retain the Motivic Cohomology contributors copyright.
See verification/environments/motivic-4.34.1/THIRD_PARTY_NOTICES.md.
-/
import Mathlib.Topology.JacobsonSpace
import Mathlib.Topology.Sets.Opens
import Mathlib.Data.Finset.Image

/-! Finite geometric constructions around closed specializations retain all
original points. No closedness assumption is imposed on the original set. -/

namespace MathGauge.GP003
open TopologicalSpace
universe u
variable {X : Type u} [TopologicalSpace X] [JacobsonSpace X]

/-- Choose finitely many closed specializations of the original points.
Every open containing these auxiliary points contains all the original ones. -/
theorem exists_finite_closed_specializations (s : Finset X) :
    ∃ t : Finset X, (∀ y ∈ t, IsClosed ({y} : Set X)) ∧
      (∀ U : Opens X, (↑t : Set X) ⊆ U → (↑s : Set X) ⊆ U) ∧
      (s.Nonempty → t.Nonempty) := by
  classical
  have hex (x : X) : ∃ y : X, y ∈ closure ({x} : Set X) ∧ IsClosed ({y} : Set X) :=
    nonempty_inter_closedPoints
      (Z := closure ({x} : Set X)) ⟨x, subset_closure (Set.mem_singleton x)⟩
      isClosed_closure.isLocallyClosed
  choose y hy hclosed using hex
  refine ⟨s.image y, ?_, ?_, fun hs => hs.image y⟩
  · intro z hz
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hz
    exact hclosed x
  · intro U hU x hx
    have hyU : y x ∈ U := hU (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    by_contra hxU
    have hsub : closure ({x} : Set X) ⊆ (U : Set X)ᶜ :=
      U.isOpen.isClosed_compl.closure_subset_iff.mpr (by
        intro z hz
        obtain rfl := Set.mem_singleton_iff.mp hz
        exact hxU)
    exact hsub (hy x) hyU

end MathGauge.GP003
