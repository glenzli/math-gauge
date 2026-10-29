import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Tactic

noncomputable section
namespace MathGauge.LinearSystems
universe u v w z
variable {k : Type u} [Field k]
variable {E : Type v} [AddCommGroup E] [Module k E]
variable {V : Type w} [AddCommGroup V] [Module k V]
variable (T : E →ₗ[k] V) (b : E →ₗ[k] k)

def Solutions := {f : V →ₗ[k] k // f.comp T = b}

/-- All relations among the input rows are respected by the constants. -/
theorem solvable_iff : Nonempty (Solutions T b) ↔ LinearMap.ker T ≤ LinearMap.ker b := by
  constructor
  · rintro ⟨⟨f,hf⟩⟩ x hx
    have h := LinearMap.congr_fun hf x
    simpa [LinearMap.mem_ker.mp hx] using h.symm
  · intro h
    obtain ⟨s,hs⟩ := T.rangeRestrict.exists_rightInverse_of_surjective T.range_rangeRestrict
    obtain ⟨f,hf⟩ := (b.comp s).exists_extend
    refine ⟨⟨f, ?_⟩⟩
    ext x
    have ht : T (s (T.rangeRestrict x)) = T x := by
      exact congrArg Subtype.val (LinearMap.congr_fun hs (T.rangeRestrict x))
    have hz : b (s (T.rangeRestrict x) - x) = 0 := h (by simp [ht])
    have hb : b (s (T.rangeRestrict x)) = b x := sub_eq_zero.mp (by simpa using hz)
    exact (LinearMap.congr_fun hf (T.rangeRestrict x)).trans hb

theorem homogeneous_comp (W : Submodule k V) (f : V →ₗ[k] k)
    (hf : W ≤ LinearMap.ker f) (x : W) : f x = 0 := hf x.property

/-- Quotient-dual coordinates of all solutions after one solution is chosen. -/
def solutionEquiv (f0 : Solutions T b) :
    ((V ⧸ LinearMap.range T) →ₗ[k] k) ≃ Solutions T b where
  toFun a := ⟨f0.val + a.comp (LinearMap.range T).mkQ, by
    ext x
    have h0 := LinearMap.congr_fun f0.property x
    have hx : (LinearMap.range T).mkQ (T x) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2 ⟨x,rfl⟩
    simpa [hx] using h0⟩
  invFun f := (LinearMap.range T).liftQ (f.val-f0.val) (by
    rintro _ ⟨x,rfl⟩
    change f.val (T x)-f0.val (T x)=0
    exact sub_eq_zero.mpr ((LinearMap.congr_fun f.property x).trans
      (LinearMap.congr_fun f0.property x).symm))
  left_inv a := by
    ext v
    simp
  right_inv f := by
    apply Subtype.ext
    ext v
    simp

/-- A universal affine equality is exactly a finite row relation, before choosing a basis. -/
theorem consequence_iff (f0 : Solutions T b) (v : V) (c : k) :
    (∀ f : Solutions T b, f.val v = c) ↔ ∃ e : E, T e = v ∧ b e = c := by
  constructor
  · intro h
    have hv : v ∈ LinearMap.range T := by
      by_contra hn
      obtain ⟨a,hav,ha⟩ := Submodule.exists_le_ker_of_notMem hn
      let f : Solutions T b := ⟨f0.val+a, by
        ext x
        have hz : a (T x)=0 := ha ⟨x,rfl⟩
        simpa [hz] using LinearMap.congr_fun f0.property x⟩
      have he := h f
      change f0.val v + a v = c at he
      rw [h f0] at he
      exact hav (add_left_cancel (he.trans (add_zero c).symm))
    obtain ⟨e,he⟩ := hv
    refine ⟨e,he,?_⟩
    exact (LinearMap.congr_fun f0.property e).symm.trans
      ((congrArg f0.val he).trans (h f0))
  · rintro ⟨e,rfl,he⟩ f
    exact (LinearMap.congr_fun f.property e).trans he

section Rows
variable {I : Type v} {J : Type z}
variable (r : J → I →₀ k) (d : J → k)

def rowMap : (J →₀ k) →ₗ[k] (I →₀ k) := Finsupp.linearCombination k r
def constantMap : (J →₀ k) →ₗ[k] k := Finsupp.linearCombination k d
def evaluate (x : I → k) : (I →₀ k) →ₗ[k] k := Finsupp.llift k k k I x
def finiteSolvable : Prop := ∀ F : Finset J, ∃ x : I → k, ∀ j ∈ F, evaluate x (r j) = d j
def coordinateSolutions := {x : I → k // ∀ j, evaluate x (r j) = d j}

@[simp] theorem evaluate_single (x : I → k) (i : I) :
    evaluate x (Finsupp.single i 1) = x i := by simp [evaluate, Finsupp.lift_apply]

theorem finiteSolvable_relations (h : finiteSolvable r d) :
    LinearMap.ker (rowMap r) ≤ LinearMap.ker (constantMap d) := by
  intro l hl
  obtain ⟨x,hx⟩ := h l.support
  have he : evaluate x (rowMap r l) = constantMap d l := by
    rw [rowMap, Finsupp.apply_linearCombination]
    change l.sum (fun j a => a • evaluate x (r j)) = l.sum (fun j a => a • d j)
    exact Finset.sum_congr rfl (fun j hj => by dsimp; rw [hx j hj])
  have hh : rowMap r l = 0 := hl
  simpa [hh] using he.symm

/-- The functional model and the original scalar assignments are actual equivalent sets. -/
def coordinateEquiv : coordinateSolutions r d ≃ Solutions (rowMap r) (constantMap d) where
  toFun x := ⟨evaluate x.val, by
    ext j
    change evaluate x.val (rowMap r (Finsupp.single j 1)) =
      constantMap d (Finsupp.single j 1)
    simpa only [rowMap, constantMap, Finsupp.linearCombination_single, one_smul]
      using x.property j⟩
  invFun f := ⟨(Finsupp.llift k k k I).symm f.val, by
    intro j
    have h := LinearMap.congr_fun f.property (Finsupp.single j 1)
    simpa [evaluate, rowMap, constantMap] using h⟩
  left_inv x := by apply Subtype.ext; exact (Finsupp.llift k k k I).symm_apply_apply x.val
  right_inv f := by apply Subtype.ext; exact (Finsupp.llift k k k I).apply_symm_apply f.val

def coordinateParameters (x0 : coordinateSolutions r d) :
    (((I →₀ k) ⧸ LinearMap.range (rowMap r)) →ₗ[k] k) ≃ coordinateSolutions r d :=
  (solutionEquiv _ _ ((coordinateEquiv r d) x0)).trans (coordinateEquiv r d).symm

@[simp] theorem coordinateParameters_apply (x0 : coordinateSolutions r d)
    (a : ((I →₀ k) ⧸ LinearMap.range (rowMap r)) →ₗ[k] k) (i : I) :
    (coordinateParameters r d x0 a).val i =
      x0.val i+a ((LinearMap.range (rowMap r)).mkQ (Finsupp.single i 1)) := by
  simp [coordinateParameters, coordinateEquiv, solutionEquiv, evaluate]

theorem parameter_difference (x0 : coordinateSolutions r d)
    (a c : ((I →₀ k) ⧸ LinearMap.range (rowMap r)) →ₗ[k] k) (i : I) :
    (coordinateParameters r d x0 a).val i-(coordinateParameters r d x0 c).val i =
      (a-c) ((LinearMap.range (rowMap r)).mkQ (Finsupp.single i 1)) := by
  simp only [coordinateParameters_apply, LinearMap.sub_apply]
  abel

theorem global_solution (h : finiteSolvable r d) : Nonempty (coordinateSolutions r d) := by
  obtain ⟨f⟩ := (solvable_iff (rowMap r) (constantMap d)).2 (finiteSolvable_relations r d h)
  exact ⟨(coordinateEquiv r d).symm f⟩

theorem coordinate_consequence (h : finiteSolvable r d) (v : I →₀ k) (c : k) :
    (∀ x : coordinateSolutions r d, evaluate x.val v = c) ↔
    ∃ l : J →₀ k, rowMap r l = v ∧ constantMap d l = c := by
  obtain ⟨x0⟩ := global_solution r d h
  rw [← consequence_iff (rowMap r) (constantMap d) ((coordinateEquiv r d) x0) v c]
  constructor
  · intro hh f
    have he := hh ((coordinateEquiv r d).symm f)
    simpa [coordinateEquiv, evaluate] using he
  · intro hh x
    exact hh ((coordinateEquiv r d) x)

end Rows
end MathGauge.LinearSystems
