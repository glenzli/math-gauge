import NilpotentDescent
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.ZMod.Basic

noncomputable section
namespace MathGauge.GR104

section Correction
variable {R S : Type*} [Ring R] [Ring S]
def correct (a : R) : R := 3 * a ^ 2 - 2 * a ^ 3

theorem correct_identity (a : R) :
    (correct a) ^ 2 - correct a = (4 * a ^ 2 - 4 * a - 3) * (a ^ 2 - a) ^ 2 := by
  dsimp [correct]
  noncomm_ring

theorem correct_fixed {e : R} (he : IsIdempotentElem e) : correct e = e := by
  have h2 : e ^ 2 = e := by simpa [pow_two] using he.eq
  have h3 : e ^ 3 = e := by rw [pow_succ, h2]; exact he.eq
  rw [correct, h2, h3]
  noncomm_ring

theorem map_correct (q : R →+* S) (a : R) : q (correct a) = correct (q a) := by
  norm_num [correct, map_sub, map_mul, map_pow, map_ofNat]

/-- Single-element polynomial correction works even in a noncommutative ring. -/
theorem square_zero_lift (q : R →+* S) (hs : Function.Surjective q)
    (hz : ∀ a b, q a = 0 → q b = 0 → a * b = 0)
    (e : S) (he : IsIdempotentElem e) : ∃ a, IsIdempotentElem a ∧ q a = e := by
  obtain ⟨a, ha⟩ := hs e
  have hd : q (a ^ 2 - a) = 0 := by
    rw [map_sub, map_pow, ha, pow_two, he.eq, sub_self]
  refine ⟨correct a, ?_, ?_⟩
  · change correct a * correct a = correct a
    apply sub_eq_zero.mp
    have hd2 : (a ^ 2 - a) ^ 2 = 0 := by rw [pow_two]; exact hz _ _ hd hd
    rw [← pow_two, correct_identity, hd2, mul_zero]
  · rw [map_correct, ha, correct_fixed he]
end Correction

section CommutativeCorrection
variable {R S : Type*} [CommRing R] [CommRing S]
def correctionIter (a : R) : ℕ → R
  | 0 => a
  | n + 1 => correct (correctionIter a n)

theorem correction_defect (a : R) (n : ℕ) :
    ∃ c : R, (correctionIter a n) ^ 2 - correctionIter a n = c * (a ^ 2 - a) ^ (2 ^ n) := by
  induction n with
  | zero => exact ⟨1, by simp [correctionIter]⟩
  | succ n ih =>
      obtain ⟨c, hc⟩ := ih
      refine ⟨(4 * (correctionIter a n) ^ 2 - 4 * correctionIter a n - 3) * c ^ 2, ?_⟩
      rw [correctionIter, correct_identity, hc, mul_pow, ← pow_mul, pow_succ]
      ring

theorem correction_image (q : R →+* S) (a : R) (he : IsIdempotentElem (q a)) (n : ℕ) :
    q (correctionIter a n) = q a := by
  induction n with
  | zero => rfl
  | succ n ih => rw [correctionIter, map_correct, ih, correct_fixed he]

theorem polynomial_lift_unique (q : R →+* S) (hs : Function.Surjective q)
    (hnil : ∀ x, q x = 0 → IsNilpotent x) (e : S) (he : IsIdempotentElem e) :
    ∃ a n, q a = e ∧ IsIdempotentElem (correctionIter a n) ∧
      q (correctionIter a n) = e ∧
      ∀ b, IsIdempotentElem b → q b = e → b = correctionIter a n := by
  obtain ⟨a, ha⟩ := hs e
  have hd : q (a ^ 2 - a) = 0 := by
    rw [map_sub, map_pow, ha, pow_two, he.eq, sub_self]
  obtain ⟨N, hN⟩ := hnil _ hd
  have hexp : N ≤ 2 ^ N := Nat.le_of_lt (show N < 2 ^ N from Nat.lt_two_pow_self)
  have hz : (a ^ 2 - a) ^ (2 ^ N) = 0 := pow_eq_zero_of_le hexp hN
  obtain ⟨c, hc⟩ := correction_defect a N
  have hei : IsIdempotentElem (correctionIter a N) := by
    change correctionIter a N * correctionIter a N = correctionIter a N
    apply sub_eq_zero.mp
    rw [hz, mul_zero] at hc
    simpa only [pow_two] using hc
  have hi : q (correctionIter a N) = e := (correction_image q a (ha ▸ he) N).trans ha
  refine ⟨a, N, ha, hei, hi, ?_⟩
  intro b hb hbe
  apply eq_of_isNilpotent_sub_of_isIdempotentElem hb hei
  apply hnil
  rw [map_sub, hbe, hi, sub_self]
end CommutativeCorrection

/-- Adjacent coherence represents the actual inverse limit of a countable tower. -/
structure Tower (R : ℕ → Type*) [∀ n, Ring (R n)] (S : Type*) [Ring S] where
  transition : ∀ n, R (n + 1) →+* R n
  augmentation : ∀ n, R n →+* S
  compatible : ∀ n x, augmentation n (transition n x) = augmentation (n + 1) x

namespace Tower
variable {R : ℕ → Type*} [∀ n, Ring (R n)] {S : Type*} [Ring S] (D : Tower R S)
def limitRing : Subring (∀ n, R n) where
  carrier := {x | ∀ n, D.transition n (x (n+1)) = x n}
  zero_mem' := fun n => map_zero _
  one_mem' := fun n => map_one _
  add_mem' := fun ha hb n => by simpa [map_add, ha n, hb n]
  mul_mem' := fun ha hb n => by simpa [map_mul, ha n, hb n]
  neg_mem' := fun ha n => by simpa [map_neg, ha n]

def evaluation (n : ℕ) : D.limitRing →+* R n where
  toFun x := x.val n
  map_one' := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

def limitAugmentation : D.limitRing →+* S := (D.augmentation 0).comp (D.evaluation 0)

theorem augmentation_independent (x : D.limitRing) (n : ℕ) :
    D.augmentation n (x.val n) = D.augmentation 0 (x.val 0) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [← D.compatible n, x.property n, ih]

/-- ZFC recursive choice gives elements only; the chosen lift is not a ring section. -/
def chosenSequence (hs : ∀ n, Function.Surjective (D.transition n)) (a : R 0) : ∀ n, R n
  | 0 => a
  | n + 1 => (hs n (chosenSequence hs a n)).choose

theorem chosenSequence_compatible (hs : ∀ n, Function.Surjective (D.transition n))
    (a : R 0) (n : ℕ) :
    D.transition n (D.chosenSequence hs a (n+1)) = D.chosenSequence hs a n :=
  (hs n (D.chosenSequence hs a n)).choose_spec

theorem augmentation_surjective (hs : ∀ n, Function.Surjective (D.transition n))
    (h0 : Function.Surjective (D.augmentation 0)) : Function.Surjective D.limitAugmentation := by
  intro s
  obtain ⟨a, ha⟩ := h0 s
  exact ⟨⟨D.chosenSequence hs a, D.chosenSequence_compatible hs a⟩, ha⟩
end Tower

section NoncommutativeExample
variable (k : Type*) [Field k]
def upper : Subring (Matrix (Fin 2) (Fin 2) k) where
  carrier := {a | a 1 0 = 0}
  zero_mem' := rfl
  one_mem' := by simp
  add_mem' := fun ha hb => by dsimp only [Set.mem_setOf_eq] at ha hb; simp [Matrix.add_apply, ha, hb]
  neg_mem' := fun ha => by dsimp only [Set.mem_setOf_eq] at ha; simp [Matrix.neg_apply, ha]
  mul_mem' := fun ha hb => by dsimp only [Set.mem_setOf_eq] at ha hb; simp [Matrix.mul_apply, Fin.sum_univ_two, ha, hb]

def diagonal : upper k →+* (k × k) where
  toFun a := (a.val 0 0, a.val 1 1)
  map_one' := by ext <;> simp
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' a b := by
    ext <;> simp [Matrix.mul_apply, Fin.sum_univ_two, (show a.val 1 0 = 0 from a.property), (show b.val 1 0 = 0 from b.property)]

def diagonalMatrix (a b : k) : upper k := ⟨!![a, 0; 0, b], by change (0 : k) = 0; rfl⟩
theorem diagonal_surjective : Function.Surjective (diagonal k) :=
  fun s => ⟨diagonalMatrix k s.1 s.2, by cases s; rfl⟩

theorem diagonal_kernel_square_zero (a b : upper k)
    (ha : diagonal k a = 0) (hb : diagonal k b = 0) : a * b = 0 := by
  have ha0 : a.val 0 0 = 0 := congrArg Prod.fst ha
  have ha1 : a.val 1 1 = 0 := congrArg Prod.snd ha
  have hb0 : b.val 0 0 = 0 := congrArg Prod.fst hb
  have hb1 : b.val 1 1 = 0 := congrArg Prod.snd hb
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, ha0, ha1, hb0, hb1, (show a.val 1 0 = 0 from a.property), (show b.val 1 0 = 0 from b.property)]

def idempotentMatrix (a : k) : upper k := ⟨!![1, a; 0, 0], by change (0 : k) = 0; rfl⟩
theorem idempotentMatrix_idempotent (a : k) : IsIdempotentElem (idempotentMatrix k a) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [idempotentMatrix, Matrix.mul_apply, Fin.sum_univ_two]

theorem idempotent_lift_not_unique :
    IsIdempotentElem (idempotentMatrix k 0) ∧ IsIdempotentElem (idempotentMatrix k 1) ∧
    diagonal k (idempotentMatrix k 0) = (1,0) ∧ diagonal k (idempotentMatrix k 1) = (1,0) ∧
    idempotentMatrix k 0 ≠ idempotentMatrix k 1 := by
  refine ⟨idempotentMatrix_idempotent k 0, idempotentMatrix_idempotent k 1, rfl, rfl, ?_⟩
  intro h
  have : (0 : k) = 1 := congrArg (fun a : upper k => a.val 0 1) h
  exact zero_ne_one this
end NoncommutativeExample
/-- Surjective ring maps do not in general admit unital ring sections. -/
theorem no_mod_two_to_mod_four_ring_hom : ¬ Nonempty (ZMod 2 →+* ZMod 4) := by
  rintro ⟨s⟩
  have h := congrArg s (show (2 : ZMod 2) = 0 from rfl)
  norm_num [map_ofNat] at h
  exact (by decide : (2 : ZMod 4) ≠ 0) h

def modFourReduction : ZMod 4 →+* ZMod 2 := ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)
theorem modFourReduction_surjective : Function.Surjective modFourReduction :=
  ZMod.castHom_surjective (by decide : 2 ∣ 4)

section FamilyEquivalence
open MathGauge.R104
variable {I : Type*} [Preorder I] {R : I → Type*} [∀ i, CommRing (R i)]
  {S : Type*} [CommRing S] (D : System I R S)
  {J : Type*} [Fintype J]
def familyAugmentation (i₀ : I) :
    {e : J → D.Limit // CompleteOrthogonalIdempotents e} →
    {e : J → S // CompleteOrthogonalIdempotents e} :=
  fun e => ⟨(D.limit_augmentation i₀) ∘ e.val, e.property.map (D.limit_augmentation i₀)⟩

theorem familyAugmentation_bijective (hd : ∀ i j : I, ∃ k, i ≤ k ∧ j ≤ k) (i₀ : I) :
    Function.Bijective (familyAugmentation D (J := J) i₀) := by
  constructor
  · intro a b hab
    apply Subtype.ext
    funext j
    apply D.limit_idempotent_ext hd i₀ (a.property.idem j) (b.property.idem j)
    exact congrArg (fun e => e.val j) hab
  · intro e
    refine ⟨⟨D.lift_family e.val e.property, D.lift_family_complete hd i₀ e.val e.property⟩, ?_⟩
    apply Subtype.ext
    funext j
    exact D.limit_lift_image i₀ _ _

def familyEquiv (hd : ∀ i j : I, ∃ k, i ≤ k ∧ j ≤ k) (i₀ : I) :
    {e : J → D.Limit // CompleteOrthogonalIdempotents e} ≃
      {e : J → S // CompleteOrthogonalIdempotents e} :=
  Equiv.ofBijective _ (familyAugmentation_bijective D hd i₀)
end FamilyEquivalence

end MathGauge.GR104
