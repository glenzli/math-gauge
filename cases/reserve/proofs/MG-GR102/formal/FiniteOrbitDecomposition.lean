import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Tactic

set_option linter.unnecessarySeqFocus false

namespace MathGauge.R102

variable {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

def PointwiseFiniteOrbit (f : Module.End R M) : Prop :=
  ∀ x, (Set.range (fun n : ℕ => (f ^ n) x)).Finite

lemma pow_add_apply (f : Module.End R M) (n m : ℕ) (x : M) :
    (f ^ (n + m)) x = (f ^ n) ((f ^ m) x) := by
  rw [pow_add]
  rfl

lemma nil_at_larger {f : Module.End R M} {x : M} {n m : ℕ}
    (h : (f ^ n) x = 0) (hnm : n ≤ m) : (f ^ m) x = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  rw [Nat.add_comm, pow_add_apply, h, map_zero]

lemma periodic_pow {f : Module.End R M} {x : M} {p : ℕ}
    (h : Function.IsPeriodicPt f p x) : (f ^ p) x = x := by
  simpa only [Module.End.pow_apply] using h

lemma periodic_of_pow {f : Module.End R M} {x : M} {p : ℕ}
    (h : (f ^ p) x = x) : Function.IsPeriodicPt f p x := by
  simpa only [Module.End.pow_apply] using h

def nilpart (f : Module.End R M) : Submodule R M where
  carrier := {x | ∃ n : ℕ, (f ^ n) x = 0}
  zero_mem' := ⟨0, rfl⟩
  add_mem' := by
    rintro x y ⟨n, hn⟩ ⟨m, hm⟩
    exact ⟨n + m, by rw [map_add, nil_at_larger hn (by omega), nil_at_larger hm (by omega), add_zero]⟩
  smul_mem' := by
    rintro a x ⟨n, hn⟩
    exact ⟨n, by rw [map_smul, hn, smul_zero]⟩

def periodicpart (f : Module.End R M) : Submodule R M where
  carrier := {x | ∃ p : ℕ, 0 < p ∧ Function.IsPeriodicPt f p x}
  zero_mem' := ⟨1, by omega, by simp [Function.IsPeriodicPt, Function.IsFixedPt]⟩
  add_mem' := by
    rintro x y ⟨p, hp, hxp⟩ ⟨q, hq, hyq⟩
    refine ⟨p * q, Nat.mul_pos hp hq, periodic_of_pow ?_⟩
    rw [map_add, periodic_pow (hxp.mul_const q), periodic_pow (hyq.const_mul p)]
  smul_mem' := by
    rintro a x ⟨p, hp, hxp⟩
    refine ⟨p, hp, periodic_of_pow ?_⟩
    rw [map_smul, periodic_pow hxp]

lemma nil_periodic_zero {f : Module.End R M} {x : M}
    (hn : x ∈ nilpart f) (hp : x ∈ periodicpart f) : x = 0 := by
  rcases hn with ⟨n, hn⟩
  rcases hp with ⟨p, hp, hxp⟩
  have he : (f ^ (n * p)) x = x := periodic_pow (hxp.const_mul n)
  have hz : (f ^ (n * p)) x = 0 := nil_at_larger hn (by nlinarith)
  exact he.symm.trans hz

lemma finite_orbit_eventual (f : Module.End R M) (h : PointwiseFiniteOrbit f) (x : M) :
    ∃ n p : ℕ, 0 < p ∧ Function.IsPeriodicPt f p ((f ^ n) x) := by
  classical
  let S := Set.range (fun n : ℕ => (f ^ n) x)
  letI : Finite S := (h x).to_subtype
  let u : ℕ → S := fun n => ⟨(f ^ n) x, ⟨n, rfl⟩⟩
  have hu := not_injective_infinite_finite u
  simp only [Function.Injective, not_forall] at hu
  obtain ⟨i, j, he, hne⟩ := hu
  have hij : (f ^ i) x = (f ^ j) x := congrArg Subtype.val he
  have aux (i j : ℕ) (hlt : i < j) (heq : (f ^ i) x = (f ^ j) x) :
      ∃ n p : ℕ, 0 < p ∧ Function.IsPeriodicPt f p ((f ^ n) x) := by
    refine ⟨i, j - i, Nat.sub_pos_of_lt hlt, periodic_of_pow ?_⟩
    rw [← pow_add_apply, Nat.sub_add_cancel (Nat.le_of_lt hlt)]
    exact heq.symm
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact aux i j hlt hij
  · exact aux j i hgt hij.symm

lemma decomposition_exists (f : Module.End R M) (h : PointwiseFiniteOrbit f) (x : M) :
    ∃ y, y ∈ periodicpart f ∧ x - y ∈ nilpart f := by
  obtain ⟨n, p, hp, ht⟩ := finite_orbit_eventual f h x
  let k := n * p
  have hnk : n ≤ k := by dsimp [k]; nlinarith
  obtain ⟨s, hs⟩ := Nat.exists_eq_add_of_le hnk
  have hyp : Function.IsPeriodicPt f p ((f ^ k) x) := by
    rw [hs, Nat.add_comm, pow_add_apply, Module.End.pow_apply]
    exact ht.apply_iterate s
  refine ⟨(f ^ k) x, ⟨p, hp, hyp⟩, n, ?_⟩
  rw [map_sub]
  apply sub_eq_zero.mpr
  calc
    (f ^ n) x = (f ^ k) ((f ^ n) x) := (periodic_pow (ht.const_mul n)).symm
    _ = (f ^ n) ((f ^ k) x) := by rw [← pow_add_apply, ← pow_add_apply, Nat.add_comm]

lemma decomposition_unique {f : Module.End R M} {x y z : M}
    (hy : y ∈ periodicpart f) (hxy : x - y ∈ nilpart f)
    (hz : z ∈ periodicpart f) (hxz : x - z ∈ nilpart f) : y = z := by
  apply sub_eq_zero.mp
  apply nil_periodic_zero (f := f)
  · convert (nilpart f).sub_mem hxz hxy using 1 <;> abel
  · exact (periodicpart f).sub_mem hy hz

noncomputable def projection (f : Module.End R M) (h : PointwiseFiniteOrbit f) : Module.End R M where
  toFun x := Classical.choose (decomposition_exists f h x)
  map_add' x y := by
    let px := Classical.choose (decomposition_exists f h x)
    let py := Classical.choose (decomposition_exists f h y)
    have hx := Classical.choose_spec (decomposition_exists f h x)
    have hy := Classical.choose_spec (decomposition_exists f h y)
    have hxy := Classical.choose_spec (decomposition_exists f h (x + y))
    apply decomposition_unique hxy.1 hxy.2 ((periodicpart f).add_mem hx.1 hy.1)
    convert (nilpart f).add_mem hx.2 hy.2 using 1 <;> abel
  map_smul' a x := by
    have hx := Classical.choose_spec (decomposition_exists f h x)
    have hax := Classical.choose_spec (decomposition_exists f h (a • x))
    apply decomposition_unique hax.1 hax.2 ((periodicpart f).smul_mem a hx.1)
    simpa only [smul_sub] using (nilpart f).smul_mem a hx.2

lemma projection_spec (f : Module.End R M) (h : PointwiseFiniteOrbit f) (x : M) :
    projection f h x ∈ periodicpart f ∧ x - projection f h x ∈ nilpart f :=
  Classical.choose_spec (decomposition_exists f h x)

lemma projection_eq_self {f : Module.End R M} (h : PointwiseFiniteOrbit f) {x : M}
    (hx : x ∈ periodicpart f) : projection f h x = x := by
  apply decomposition_unique (projection_spec f h x).1 (projection_spec f h x).2 hx
  simp

lemma projection_eq_zero_iff (f : Module.End R M) (h : PointwiseFiniteOrbit f) (x : M) :
    projection f h x = 0 ↔ x ∈ nilpart f := by
  constructor
  · intro he
    simpa [he] using (projection_spec f h x).2
  · intro hx
    apply decomposition_unique (projection_spec f h x).1 (projection_spec f h x).2
      (periodicpart f).zero_mem
    simpa using hx

lemma projection_idempotent (f : Module.End R M) (h : PointwiseFiniteOrbit f) :
    (projection f h).comp (projection f h) = projection f h := by
  ext x
  exact projection_eq_self h (projection_spec f h x).1

lemma projection_kernel (f : Module.End R M) (h : PointwiseFiniteOrbit f) :
    (projection f h).ker = nilpart f := by
  ext x
  exact projection_eq_zero_iff f h x

lemma projection_range (f : Module.End R M) (h : PointwiseFiniteOrbit f) :
    (projection f h).range = periodicpart f := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact (projection_spec f h y).1
  · intro hx
    exact ⟨x, projection_eq_self h hx⟩

lemma semiconj_pow {f : Module.End R M} {g : Module.End R N} (a : M →ₗ[R] N)
    (ha : ∀ x, a (f x) = g (a x)) (n : ℕ) (x : M) :
    a ((f ^ n) x) = (g ^ n) (a x) := by
  simpa only [Module.End.pow_apply] using (Function.Semiconj.iterate_right ha n x)

lemma semiconj_nil {f : Module.End R M} {g : Module.End R N} (a : M →ₗ[R] N)
    (ha : ∀ x, a (f x) = g (a x)) {x : M} (hx : x ∈ nilpart f) :
    a x ∈ nilpart g := by
  rcases hx with ⟨n, hn⟩
  exact ⟨n, by rw [← semiconj_pow a ha, hn, map_zero]⟩

lemma semiconj_periodic {f : Module.End R M} {g : Module.End R N} (a : M →ₗ[R] N)
    (ha : ∀ x, a (f x) = g (a x)) {x : M} (hx : x ∈ periodicpart f) :
    a x ∈ periodicpart g := by
  rcases hx with ⟨p, hp, hxp⟩
  exact ⟨p, hp, hxp.map ha⟩

lemma projection_natural {f : Module.End R M} {g : Module.End R N}
    (hf : PointwiseFiniteOrbit f) (hg : PointwiseFiniteOrbit g) (a : M →ₗ[R] N)
    (ha : ∀ x, a (f x) = g (a x)) (x : M) :
    a (projection f hf x) = projection g hg (a x) := by
  apply decomposition_unique
    (semiconj_periodic a ha (projection_spec f hf x).1)
    (by simpa only [map_sub] using semiconj_nil a ha (projection_spec f hf x).2)
    (projection_spec g hg (a x)).1 (projection_spec g hg (a x)).2

lemma projection_commutes (f : Module.End R M) (h : PointwiseFiniteOrbit f) (x : M) :
    f (projection f h x) = projection f h (f x) :=
  projection_natural h h f (fun _ => rfl) x

/-- The periodic part is carried into itself and the restriction is a genuine linear map. -/
def periodic_restriction (f : Module.End R M) : Module.End R (periodicpart f) where
  toFun x := ⟨f x, semiconj_periodic f (fun _ => rfl) x.property⟩
  map_add' _ _ := Subtype.ext (map_add f _ _)
  map_smul' _ _ := Subtype.ext (map_smul f _ _)

lemma periodic_restriction_bijective (f : Module.End R M) :
    Function.Bijective (periodic_restriction f) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply sub_eq_zero.mp
    have hn : x.val - y.val ∈ nilpart f := by
      refine ⟨1, ?_⟩
      simpa [map_sub] using sub_eq_zero.mpr (congrArg Subtype.val hxy)
    exact nil_periodic_zero hn ((periodicpart f).sub_mem x.property y.property)
  · intro x
    obtain ⟨p, hp, hpx⟩ := x.property
    let y : periodicpart f := ⟨(f ^ (p - 1)) x.val,
      ⟨p, hp, by simpa only [Module.End.pow_apply] using hpx.apply_iterate (p - 1)⟩⟩
    refine ⟨y, Subtype.ext ?_⟩
    change f ((f ^ (p - 1)) x.val) = x.val
    have hnum : 1 + (p - 1) = p := by omega
    calc
      f ((f ^ (p - 1)) x.val) = (f ^ (1 + (p - 1))) x.val := by rw [pow_add_apply, pow_one]
      _ = x.val := by rw [hnum]; exact periodic_pow hpx

noncomputable def periodic_automorphism (f : Module.End R M) :
    periodicpart f ≃ₗ[R] periodicpart f :=
  LinearEquiv.ofBijective (periodic_restriction f) (periodic_restriction_bijective f)

noncomputable def decomposition_equiv (f : Module.End R M) (h : PointwiseFiniteOrbit f) :
    M ≃ₗ[R] (nilpart f × periodicpart f) where
  toFun x := (⟨x - projection f h x, (projection_spec f h x).2⟩,
    ⟨projection f h x, (projection_spec f h x).1⟩)
  invFun z := z.1.val + z.2.val
  left_inv x := sub_add_cancel x _
  right_inv z := by
    have hz : projection f h (z.1.val + z.2.val) = z.2.val := by
      apply decomposition_unique (projection_spec f h _).1 (projection_spec f h _).2 z.2.property
      simpa only [add_sub_cancel_right] using z.1.property
    apply Prod.ext
    · apply Subtype.ext
      change z.1.val + z.2.val - projection f h (z.1.val + z.2.val) = z.1.val
      rw [hz, add_sub_cancel_right]
    · exact Subtype.ext hz
  map_add' x y := by
    apply Prod.ext
    · apply Subtype.ext
      change x + y - projection f h (x + y) = (x - projection f h x) + (y - projection f h y)
      rw [map_add]
      abel
    · exact Subtype.ext (map_add (projection f h) x y)
  map_smul' a x := by
    apply Prod.ext
    · apply Subtype.ext
      change a • x - projection f h (a • x) = a • (x - projection f h x)
      rw [map_smul, smul_sub]
    · exact Subtype.ext (map_smul (projection f h) a x)

lemma projection_characterization (f : Module.End R M) (h : PointwiseFiniteOrbit f)
    (e : Module.End R M)
    (he : ∀ x, e x ∈ periodicpart f ∧ x - e x ∈ nilpart f) : e = projection f h := by
  ext x
  exact decomposition_unique (he x).1 (he x).2
    (projection_spec f h x).1 (projection_spec f h x).2

end MathGauge.R102
