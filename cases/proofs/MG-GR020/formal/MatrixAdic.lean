import PadicOrthogonal
import Mathlib.RingTheory.AdicCompletion.Basic

noncomputable section
namespace MathGauge.GR020
variable {R : Type*} [CommRing R] {d : ℕ}
abbrev Mat (R : Type*) (d : ℕ) := Matrix (Fin d) (Fin d) R

/-- Entrywise ideal congruence is the actual reduction of matrices. -/
def Near (I : Ideal R) (A B : Mat R d) : Prop := ∀ i j, A i j - B i j ∈ I

def reduce (I : Ideal R) : Mat R d →+* Mat (R ⧸ I) d := (Ideal.Quotient.mk I).mapMatrix

theorem near_iff_reduce (I : Ideal R) (A B : Mat R d) : Near I A B ↔ reduce I A = reduce I B := by
  constructor
  · intro h; ext i j
    exact Ideal.Quotient.eq.mpr (h i j)
  · intro h i j
    exact Ideal.Quotient.eq.mp (congrFun (congrFun h i) j)

theorem Near.refl (I : Ideal R) (A : Mat R d) : Near I A A :=
  (near_iff_reduce I A A).mpr rfl

theorem Near.symm {I : Ideal R} {A B : Mat R d} (h : Near I A B) : Near I B A :=
  (near_iff_reduce I B A).mpr ((near_iff_reduce I A B).mp h).symm

theorem Near.trans {I : Ideal R} {A B C : Mat R d} (h : Near I A B) (k : Near I B C) : Near I A C :=
  (near_iff_reduce I A C).mpr (((near_iff_reduce I A B).mp h).trans ((near_iff_reduce I B C).mp k))

theorem Near.mono {I J : Ideal R} (hIJ : I ≤ J) {A B : Mat R d} (h : Near I A B) : Near J A B :=
  fun i j => hIJ (h i j)

theorem Near.add {I : Ideal R} {A B C D : Mat R d} (h : Near I A B) (k : Near I C D) :
    Near I (A+C) (B+D) := by
  rw [near_iff_reduce] at *
  simpa only [map_add, h, k]

theorem Near.mul {I : Ideal R} {A B C D : Mat R d} (h : Near I A B) (k : Near I C D) :
    Near I (A*C) (B*D) := by
  rw [near_iff_reduce] at *
  simpa only [map_mul, h, k]

theorem Near.sub {I : Ideal R} {A B C D : Mat R d} (h : Near I A B) (k : Near I C D) :
    Near I (A-C) (B-D) := by
  rw [near_iff_reduce] at *
  simpa only [map_sub, h, k]

theorem Near.transpose {I : Ideal R} {A B : Mat R d} (h : Near I A B) : Near I A.transpose B.transpose :=
  fun i j => h j i

theorem entries_product {I J : Ideal R} {A B : Mat R d}
    (hA : Near I A 0) (hB : Near J B 0) : Near (I*J) (A*B) 0 := by
  intro i j
  simp only [Matrix.zero_apply, sub_zero, Matrix.mul_apply]
  exact Ideal.sum_mem _ (fun k _ => Ideal.mul_mem_mul (by simpa using hA i k) (by simpa using hB k j))

theorem near_pow_zero (I : Ideal R) (A : Mat R d) : Near (I^0) A 0 := by
  intro i j; simp

theorem near_all_powers_eq (I : Ideal R) [IsHausdorff I R] {A B : Mat R d}
    (h : ∀ n, Near (I^n) A B) : A=B := by
  ext i j
  apply (IsHausdorff.eq_iff_smodEq (I := I)).mpr
  intro n
  rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one, SModEq.sub_mem]
  exact h n i j

/-- Complete scalar entries construct an actual limit matrix. -/
theorem matrix_adic_limit (I : Ideal R) [IsAdicComplete I R] (f : ℕ → Mat R d)
    (h : ∀ m n, m ≤ n → Near (I^m) (f m) (f n)) :
    ∃ L : Mat R d, ∀ n, Near (I^n) (f n) L := by
  have hp : ∀ i j : Fin d, ∃ L : R, ∀ n, f n i j - L ∈ I^n := by
    intro i j
    have hc : ∀ {m n : ℕ}, m ≤ n →
        f m i j ≡ f n i j [SMOD (I^m • ⊤ : Ideal R)] := by
      intro m n hmn
      rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one, SModEq.sub_mem]
      exact h m n hmn i j
    obtain ⟨L,hL⟩ := IsPrecomplete.prec' (I := I) (fun n => f n i j) hc
    refine ⟨L,fun n => ?_⟩
    have hh := hL n
    rwa [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one, SModEq.sub_mem] at hh
  choose L hL using hp
  exact ⟨L,fun n i j => hL i j n⟩

/-- A denominator-free Catalan iteration; convergence uses the actual ideal topology. -/
def catalanIter (T : Mat R d) : ℕ → Mat R d
  | 0 => 0
  | n+1 => 1+T*(catalanIter T n*catalanIter T n)

theorem catalan_commute {T E : Mat R d} (h : Commute T E) (n : ℕ) :
    Commute (catalanIter T n) E := by
  induction n with
  | zero => exact Commute.zero_left _
  | succ n ih => exact (Commute.one_left _).add_left (h.mul_left (ih.mul_left ih))

theorem catalan_symmetric {T : Mat R d} (hT : T.transpose=T) (n : ℕ) :
    (catalanIter T n).transpose=catalanIter T n := by
  induction n with
  | zero => simp [catalanIter]
  | succ n ih =>
    simp only [catalanIter, Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_mul, ih, hT]
    exact congrArg (1+·) ((catalan_commute (Commute.refl T) n).mul_left
      (catalan_commute (Commute.refl T) n)).eq

theorem catalan_step_small (I : Ideal R) (T : Mat R d) (hT : Near I T 0) (n : ℕ) :
    Near (I^n) (catalanIter T (n+1)-catalanIter T n) 0 := by
  induction n with
  | zero => exact near_pow_zero I _
  | succ n ih =>
    let A := catalanIter T (n+1)
    let B := catalanIter T n
    have hd : Near (I^n) (A*A-B*B) 0 := by
      have ha := ih.mul (Near.refl (I^n) A)
      have hb := (Near.refl (I^n) B).mul ih
      have hh := ha.add hb
      have he : A*A-B*B=(A-B)*A+B*(A-B) := by noncomm_ring
      rw [he]
      simpa only [zero_mul,mul_zero,zero_add] using hh
    have hm := entries_product hT hd
    have he : catalanIter T (n+1+1)-catalanIter T (n+1)=T*(A*A-B*B) := by
      change (1+T*(A*A))-(1+T*(B*B))=T*(A*A-B*B)
      noncomm_ring
    rw [he, pow_succ']
    exact hm

theorem catalan_cauchy (I : Ideal R) (T : Mat R d) (hT : Near I T 0)
    (m n : ℕ) (hmn : m ≤ n) : Near (I^m) (catalanIter T m) (catalanIter T n) := by
  induction n, hmn using Nat.le_induction with
  | base => exact Near.refl _ _
  | succ n hmn ih =>
    apply ih.trans
    have hs := (catalan_step_small I T hT n).mono (Ideal.pow_le_pow_right hmn)
    have he : Near (I^m) (catalanIter T (n+1)) (catalanIter T n) := by
      intro i j; simpa only [Matrix.sub_apply, Matrix.zero_apply, sub_zero] using hs i j
    exact he.symm

theorem catalan_limit (I : Ideal R) [IsAdicComplete I R]
    (T : Mat R d) (hT : Near I T 0) :
    ∃ C : Mat R d, C=1+T*(C*C) ∧ Commute C T ∧
      (T.transpose=T → C.transpose=C) ∧
      (∀ E, Commute T E → Commute C E) := by
  obtain ⟨C,hC⟩ := matrix_adic_limit I (catalanIter T) (catalan_cauchy I T hT)
  have hcomm : ∀ E, Commute T E → Commute C E := by
    intro E hE
    change C*E=E*C
    apply near_all_powers_eq I
    intro n
    have h₁ := (hC n).mul (Near.refl (I^n) E)
    have h₂ := (Near.refl (I^n) E).mul (hC n)
    rw [(catalan_commute hE n).eq] at h₁
    exact h₁.symm.trans h₂
  refine ⟨C,?_,hcomm T (Commute.refl T),?_,hcomm⟩
  · apply near_all_powers_eq I
    intro n
    have hn := (hC (n+1)).mono (Ideal.pow_le_pow_right (Nat.le_succ n))
    have hm := (Near.refl (I^n) (1 : Mat R d)).add
      ((Near.refl (I^n) T).mul ((hC n).mul (hC n)))
    exact hn.symm.trans hm
  · intro hT'
    apply near_all_powers_eq I
    intro n
    have hn := (hC n).transpose
    rw [catalan_symmetric hT' n] at hn
    exact hn.symm.trans (hC n)

/-- The Catalan limit constructs a symmetric square root of 1-4T.
No inverse of 2, no characteristic assumption, and no square-root certificate
is an input. This is the integral convergence argument used in S2 and S5. -/
theorem adic_square_root (I : Ideal R) [IsAdicComplete I R]
    (T : Mat R d) (hT : Near I T 0) (hTs : T.transpose=T) :
    ∃ D : Mat R d, D*D=1-4*T ∧ D.transpose=D ∧ Near I D 1 ∧
      (∀ E, Commute T E → Commute D E) := by
  obtain ⟨C,hfix,hcomm,hsym,hcentral⟩ := catalan_limit I T hT
  let D : Mat R d := 1-2*(T*C)
  have hTC : T*C=C*T := hcomm.eq.symm
  have hword : C*(T*(C*T))=T*(T*(C*C)) := by
    calc
      C*(T*(C*T)) = (C*T)*(C*T) := by noncomm_ring
      _ = (T*C)*(T*C) := by rw [hcomm.eq]
      _ = T*(C*T)*C := by noncomm_ring
      _ = T*(T*C)*C := by rw [hcomm.eq]
      _ = T*(T*(C*C)) := by noncomm_ring
  refine ⟨D,?_,?_,?_,?_⟩
  · have he : D*D-(1-4*T)=4*T*(1-C+T*(C*C)) := by
      dsimp [D]
      noncomm_ring [hTC, hword]
    have hz : 1-C+T*(C*C)=0 := by
      calc
        1-C+T*(C*C) = (1+T*(C*C))-C := by noncomm_ring
        _ = 0 := by rw [← hfix]; exact sub_self _
    rw [hz,mul_zero] at he
    exact sub_eq_zero.mp he
  · dsimp [D]
    simp only [Matrix.transpose_sub,Matrix.transpose_one,Matrix.transpose_mul,
      Matrix.transpose_ofNat,hsym hTs,hTs]
    noncomm_ring [hTC]
  · have hh := (Near.refl I (2 : Mat R d)).mul (hT.mul (Near.refl I C))
    have hk := (Near.refl I (1 : Mat R d)).sub hh
    simpa only [zero_mul,mul_zero,sub_zero] using hk
  · intro E hE
    exact (Commute.one_left E).sub_left
      ((Commute.ofNat_left 2 E).mul_left (hE.mul_left (hcentral E hE)))

end MathGauge.GR020
