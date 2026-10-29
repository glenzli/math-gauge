import FiniteOrbitDecomposition
import Mathlib.LinearAlgebra.Projection
import Mathlib.RingTheory.Idempotents

noncomputable section
open MathGauge.R102

namespace MathGauge.GR102
variable {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

def part (e : Module.End R M) (b : Bool) : Module.End R M := if b then e else 1 - e

theorem part_idempotent {e : Module.End R M} (he : IsIdempotentElem e) (b : Bool) :
    IsIdempotentElem (part e b) := by
  cases b
  · exact he.one_sub
  · exact he

theorem part_commute {e f : Module.End R M} (h : Commute e f) (a b : Bool) :
    Commute (part e a) (part f b) := by
  cases a <;> cases b
  · exact (Commute.one_right (1 - e)).sub_right ((Commute.one_left f).sub_left h)
  · exact (Commute.one_left f).sub_left h
  · exact (Commute.one_right e).sub_right h
  · exact h

theorem part_orthogonal {e : Module.End R M} (he : IsIdempotentElem e)
    (a b : Bool) (hab : a ≠ b) : part e a * part e b = 0 := by
  cases a <;> cases b
  · exact (hab rfl).elim
  · exact he.one_sub_mul_self
  · exact he.mul_one_sub_self
  · exact (hab rfl).elim

def four (e f : Module.End R M) (s : Bool × Bool) : Module.End R M :=
  part e s.1 * part f s.2

theorem four_idempotent {e f : Module.End R M} (he : IsIdempotentElem e)
    (hf : IsIdempotentElem f) (h : Commute e f) (s : Bool × Bool) :
    IsIdempotentElem (four e f s) :=
  IsIdempotentElem.mul_of_commute (part_commute h s.1 s.2)
    (part_idempotent he s.1) (part_idempotent hf s.2)

theorem four_orthogonal {e f : Module.End R M} (he : IsIdempotentElem e)
    (hf : IsIdempotentElem f) (h : Commute e f) (s t : Bool × Bool) (hst : s ≠ t) :
    four e f s * four e f t = 0 := by
  rw [four, four, (part_commute h t.1 s.2).symm.mul_mul_mul_comm]
  by_cases ha : s.1 = t.1
  · have hb : s.2 ≠ t.2 := fun hb => hst (Prod.ext ha hb)
    rw [part_orthogonal hf _ _ hb, mul_zero]
  · rw [part_orthogonal he _ _ ha, zero_mul]

theorem four_sum (e f : Module.End R M) :
    (∑ s : Bool × Bool, four e f s) = 1 := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, four, part]
  simp only [Bool.false_eq_true, ↓reduceIte]
  noncomm_ring

theorem range_product {e f : Module.End R M} (he : IsIdempotentElem e)
    (hf : IsIdempotentElem f) (h : Commute e f) :
    (e * f).range = e.range ⊓ f.range := by
  have hei (x : M) : e (e x) = e x := LinearMap.congr_fun he x
  have hfi (x : M) : f (f x) = f x := LinearMap.congr_fun hf x
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨⟨f y, rfl⟩, ⟨e y, (LinearMap.congr_fun h.eq y).symm⟩⟩
  · rintro ⟨⟨y, hy⟩, ⟨z, hz⟩⟩
    refine ⟨x, ?_⟩
    change e (f x) = x
    have hfx : f x = x := by rw [← hz, hfi]
    have hex : e x = x := by rw [← hy, hei]
    rw [hfx, hex]

theorem projection_commute {T U : Module.End R M}
    (hT : PointwiseFiniteOrbit T) (hU : PointwiseFiniteOrbit U) (h : Commute T U) :
    Commute (projection T hT) (projection U hU) := by
  have hUT (x : M) : U (T x) = T (U x) := (LinearMap.congr_fun h.eq x).symm
  have hue (x : M) := projection_natural hT hT U hUT x
  change projection T hT * projection U hU = projection U hU * projection T hT
  ext x
  exact projection_natural hU hU (projection T hT) (fun x => (hue x).symm) x

def sector (T : Module.End R M) (b : Bool) : Submodule R M :=
  if b then periodicpart T else nilpart T

theorem projection_isIdempotent (T : Module.End R M) (hT : PointwiseFiniteOrbit T) :
    IsIdempotentElem (projection T hT) := projection_idempotent T hT

theorem part_range (T : Module.End R M) (hT : PointwiseFiniteOrbit T) (b : Bool) :
    (part (projection T hT) b).range = sector T b := by
  cases b
  · change (1 - projection T hT).range = nilpart T
    rw [← LinearMap.IsIdempotentElem.ker_eq_range_one_sub (projection_isIdempotent T hT),
      projection_kernel]
  · exact projection_range T hT

/-- Both S2 and S6: no common power or polynomial is assumed for the infinite case. -/
theorem four_sector_range {T U : Module.End R M}
    (hT : PointwiseFiniteOrbit T) (hU : PointwiseFiniteOrbit U) (h : Commute T U)
    (s : Bool × Bool) :
    (four (projection T hT) (projection U hU) s).range = sector T s.1 ⊓ sector U s.2 := by
  rw [four, range_product (part_idempotent (projection_isIdempotent T hT) _)
    (part_idempotent (projection_isIdempotent U hU) _)
    (part_commute (projection_commute hT hU h) _ _), part_range, part_range]

theorem part_natural (a : M →ₗ[R] N) {e : Module.End R M} {e' : Module.End R N}
    (h : ∀ x, a (e x) = e' (a x)) (b : Bool) (x : M) :
    a (part e b x) = part e' b (a x) := by
  cases b <;> simp [part, LinearMap.sub_apply, map_sub, h]

theorem four_natural {T U : Module.End R M} {T' U' : Module.End R N}
    (hT : PointwiseFiniteOrbit T) (hU : PointwiseFiniteOrbit U)
    (hT' : PointwiseFiniteOrbit T') (hU' : PointwiseFiniteOrbit U')
    (a : M →ₗ[R] N) (ha : ∀ x, a (T x) = T' (a x)) (hb : ∀ x, a (U x) = U' (a x))
    (s : Bool × Bool) (x : M) :
    a (four (projection T hT) (projection U hU) s x) =
      four (projection T' hT') (projection U' hU') s (a x) := by
  change a (part (projection T hT) s.1 (part (projection U hU) s.2 x)) = _
  rw [part_natural a (projection_natural hT hT' a ha),
    part_natural a (projection_natural hU hU' a hb)]
  rfl

theorem four_decomposition (e f : Module.End R M) (x : M) :
    (∑ s : Bool × Bool, four e f s x) = x := by
  have h := LinearMap.congr_fun (four_sum e f) x
  simpa using h

/-- Orthogonality proves uniqueness of the four actual image components. -/
theorem four_components_unique {e f : Module.End R M} (he : IsIdempotentElem e)
    (hf : IsIdempotentElem f) (h : Commute e f) (v : Bool × Bool → M)
    (hv : ∀ s, v s ∈ (four e f s).range) (x : M) (hx : ∑ s, v s = x)
    (s : Bool × Bool) : four e f s x = v s := by
  rw [← hx, map_sum]
  rw [Finset.sum_eq_single s]
  · obtain ⟨y, hy⟩ := hv s
    rw [← hy]
    exact LinearMap.congr_fun (four_idempotent he hf h s) y
  · intro t _ hts
    obtain ⟨y, hy⟩ := hv t
    rw [← hy]
    exact LinearMap.congr_fun (four_orthogonal he hf h s t (Ne.symm hts)) y
  · simp

end MathGauge.GR102
