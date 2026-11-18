import formal_oet.vol_01.ch_01_foundations.operator_space
import Mathlib.Data.Matrix.Mul

namespace LCH02

open formal_oet.vol_01.ch_01_foundations
open scoped BigOperators ENNReal Matrix

variable {X I : Type} {bot : X}

/-- The ambient finite, nonempty family of extended pseudometrics. -/
structure GaugeFamily (X I : Type) (bot : X) [Fintype I] [Nonempty I] where
  dist : I → X → X → ℝ≥0∞
  valid : ∀ i, ExtendedPseudoMetric X bot (dist i)

/-- The coefficient from input `i` to output `j` is stored at row `j`, column `i`. -/
abbrev BoundMatrix (I : Type) := Matrix I I ℝ≥0∞

theorem matrix_mul_entry [Fintype I] (B A : BoundMatrix I) (i j : I) :
    (B * A) j i = ∑ k, B j k * A k i :=
  Matrix.mul_apply

theorem matrix_mulVec_entry [Fintype I] (A : BoundMatrix I) (v : I → ℝ≥0∞) (j : I) :
    (A *ᵥ v) j = ∑ i, A j i * v i :=
  rfl

noncomputable def identityMatrix : BoundMatrix I := by
  classical
  exact 1

open scoped Classical in
theorem identityMatrix_entry (i j : I) :
    (identityMatrix : BoundMatrix I) j i = if j = i then 1 else 0 :=
  Matrix.one_apply

/-- The input list is in application order, from the first step to the last. -/
noncomputable def matrixProduct [Fintype I] (matrices : List (BoundMatrix I)) :
    BoundMatrix I := by
  classical
  exact matrices.reverse.prod

@[simp] theorem matrixProduct_nil [Fintype I] :
    matrixProduct ([] : List (BoundMatrix I)) = identityMatrix :=
  rfl

theorem matrixProduct_cons [Fintype I] (A : BoundMatrix I) (As : List (BoundMatrix I)) :
    matrixProduct (A :: As) = matrixProduct As * A := by
  classical
  simp [matrixProduct, List.prod_append]

@[simp] theorem matrixProduct_singleton [Fintype I] (A : BoundMatrix I) :
    matrixProduct [A] = A := by
  classical
  simp [matrixProduct]

private theorem mulVec_mono [Fintype I] (A : BoundMatrix I) {v w : I → ℝ≥0∞}
    (h : v ≤ w) : A *ᵥ v ≤ A *ᵥ w := by
  intro j
  rw [matrix_mulVec_entry, matrix_mulVec_entry]
  exact Finset.sum_le_sum (fun i _ => mul_le_mul_right (h i) (A j i))

private theorem identityMatrix_mulVec [Fintype I] (v : I → ℝ≥0∞) :
    identityMatrix *ᵥ v = v := by
  classical
  exact Matrix.one_mulVec v

variable [Fintype I] [Nonempty I] (G : GaugeFamily X I bot)

def distanceVector (x y : X) : I → ℝ≥0∞ := fun i => G.dist i x y

def IsLipOn (f : Operator X bot) (U : Set X) (A : BoundMatrix I) : Prop :=
  U ⊆ dom f ∧ ∀ ⦃x y⦄, x ∈ U → y ∈ U →
    distanceVector G (f.func x) (f.func y) ≤ A *ᵥ distanceVector G x y

def IsLip (f : Operator X bot) (A : BoundMatrix I) : Prop :=
  IsLipOn G f (dom f) A

def lipMatricesOn (f : Operator X bot) (U : Set X) : Set (BoundMatrix I) :=
  {A | IsLipOn G f U A}

def lipMatrices (f : Operator X bot) : Set (BoundMatrix I) :=
  {A | IsLip G f A}

def IsCoLipOn (f : Operator X bot) (U : Set X) (A : BoundMatrix I) : Prop :=
  U.Nonempty ∧ U ⊆ dom f ∧ ∀ ⦃x y⦄, x ∈ U → y ∈ U →
    A *ᵥ distanceVector G x y ≤ distanceVector G (f.func x) (f.func y)

def coLipMatricesOn (f : Operator X bot) (U : Set X) : Set (BoundMatrix I) :=
  {A | IsCoLipOn G f U A}

theorem lip_single_component [Subsingleton I] (i : I)
    (f : Operator X bot) (A : BoundMatrix I) :
    A ∈ lipMatrices G f ↔ ∀ x ∈ dom f, ∀ y ∈ dom f,
      G.dist i (f.func x) (f.func y) ≤ A i i * G.dist i x y := by
  classical
  have hrow (x y : X) : (A *ᵥ distanceVector G x y) i = A i i * G.dist i x y := by
    rw [matrix_mulVec_entry, Finset.sum_eq_single i]
    · rfl
    · intro k _ hki
      exact (hki (Subsingleton.elim k i)).elim
    · simp
  constructor
  · intro h x hx y hy
    have hi := h.2 hx hy i
    rw [hrow] at hi
    exact hi
  · intro h
    refine ⟨Set.Subset.rfl, ?_⟩
    intro x y hx hy j
    have hij : j = i := Subsingleton.elim _ _
    subst j
    change G.dist i (f.func x) (f.func y) ≤ (A *ᵥ distanceVector G x y) i
    rw [hrow]
    exact h x hx y hy

theorem lip_restrict {f : Operator X bot} {U V : Set X}
    (hUV : U ⊆ V) (hV : V ⊆ dom f) :
    lipMatricesOn G f V ⊆ lipMatricesOn G f U := by
  intro A hA
  refine ⟨hUV.trans hV, ?_⟩
  intro x y hx hy
  exact hA.2 (hUV hx) (hUV hy)

theorem global_lip_restrict {f : Operator X bot} {U : Set X} (hU : U ⊆ dom f) :
    lipMatrices G f ⊆ lipMatricesOn G f U :=
  lip_restrict G hU Set.Subset.rfl

theorem colip_restrict {f : Operator X bot} {U V : Set X}
    (hUn : U.Nonempty) (hUV : U ⊆ V) (hV : V ⊆ dom f) :
    coLipMatricesOn G f V ⊆ coLipMatricesOn G f U := by
  intro A hA
  refine ⟨hUn, hUV.trans hV, ?_⟩
  intro x y hx hy
  exact hA.2.2 (hUV hx) (hUV hy)

theorem global_colip_restrict {f : Operator X bot} {U : Set X}
    (hUn : U.Nonempty) (hU : U ⊆ dom f) :
    coLipMatricesOn G f (dom f) ⊆ coLipMatricesOn G f U :=
  colip_restrict G hUn hU Set.Subset.rfl

theorem composed_domains {f g : Operator X bot} {U : Set X} (hU : U ⊆ dom (g * f)) :
    U ⊆ dom f ∧ operator_image f U ⊆ dom g := by
  constructor
  · intro x hx hbot
    have h := hU hx
    change g.func (f.func x) ≠ bot at h
    apply h
    change f.func x = bot at hbot
    rw [hbot, g.preserves_bot]
  · rintro z ⟨x, hx, rfl⟩
    exact hU hx

theorem lip_comp {f g : Operator X bot} {U : Set X} {A B : BoundMatrix I}
    (hU : U ⊆ dom (g * f))
    (hA : A ∈ lipMatricesOn G f U)
    (hB : B ∈ lipMatricesOn G g (operator_image f U)) :
    B * A ∈ lipMatricesOn G (g * f) U := by
  refine ⟨hU, ?_⟩
  intro x y hx hy
  calc
    distanceVector G (g.func (f.func x)) (g.func (f.func y))
        ≤ B *ᵥ distanceVector G (f.func x) (f.func y) :=
      hB.2 (Set.mem_image_of_mem f.func hx) (Set.mem_image_of_mem f.func hy)
    _ ≤ B *ᵥ (A *ᵥ distanceVector G x y) := mulVec_mono B (hA.2 hx hy)
    _ = (B * A) *ᵥ distanceVector G x y := Matrix.mulVec_mulVec _ _ _

theorem colip_comp {f g : Operator X bot} {U : Set X} {A B : BoundMatrix I}
    (hU : U ⊆ dom (g * f))
    (hA : A ∈ coLipMatricesOn G f U)
    (hB : B ∈ coLipMatricesOn G g (operator_image f U)) :
    B * A ∈ coLipMatricesOn G (g * f) U := by
  refine ⟨hA.1, hU, ?_⟩
  intro x y hx hy
  calc
    (B * A) *ᵥ distanceVector G x y = B *ᵥ (A *ᵥ distanceVector G x y) :=
      (Matrix.mulVec_mulVec _ _ _).symm
    _ ≤ B *ᵥ distanceVector G (f.func x) (f.func y) := mulVec_mono B (hA.2.2 hx hy)
    _ ≤ distanceVector G (g.func (f.func x)) (g.func (f.func y)) :=
      hB.2.2 (Set.mem_image_of_mem f.func hx) (Set.mem_image_of_mem f.func hy)

theorem colip_entry_eq_zero {f : Operator X bot} {A : BoundMatrix I} (i j : I)
    (hA : A ∈ coLipMatricesOn G f (dom f))
    (hpair : ∃ x ∈ dom f, ∃ y ∈ dom f,
      G.dist j (f.func x) (f.func y) = 0 ∧ 0 < G.dist i x y) :
    A j i = 0 := by
  classical
  obtain ⟨x, hx, y, hy, hout, hin⟩ := hpair
  have hsum := hA.2.2 hx hy j
  change (A *ᵥ distanceVector G x y) j ≤ G.dist j (f.func x) (f.func y) at hsum
  rw [matrix_mulVec_entry, hout] at hsum
  have hterm : A j i * G.dist i x y ≤ ∑ k, A j k * distanceVector G x y k :=
    Finset.single_le_sum (fun k _ => zero_le (A j k * distanceVector G x y k))
      (Finset.mem_univ i)
  exact (mul_eq_zero.mp (nonpos_iff_eq_zero.mp (hterm.trans hsum))).resolve_right hin.ne'

theorem zero_step_lip {U : Set X} (_hne : U.Nonempty)
    (hU : U ⊆ dom (1 : Operator X bot)) :
    matrixProduct ([] : List (BoundMatrix I)) ∈ lipMatricesOn G 1 U := by
  refine ⟨hU, ?_⟩
  intro x y _ _
  change distanceVector G x y ≤ identityMatrix *ᵥ distanceVector G x y
  rw [identityMatrix_mulVec]

theorem zero_step_colip {U : Set X} (hne : U.Nonempty)
    (hU : U ⊆ dom (1 : Operator X bot)) :
    matrixProduct ([] : List (BoundMatrix I)) ∈ coLipMatricesOn G 1 U := by
  refine ⟨hne, hU, ?_⟩
  intro x y _ _
  change identityMatrix *ᵥ distanceVector G x y ≤ distanceVector G x y
  rw [identityMatrix_mulVec]

end LCH02
