/-
Formalization of selected results from Zhe Li (Glen Li / glenzli),
The Operator Evolution Theory, vol. I, v1.0.0, https://glenzli.com/books/oet/
Source DOI 10.5281/zenodo.21457931. License https://creativecommons.org/licenses/by/4.0/
-/
import formal_oet.vol_01.ch_01_foundations.operator_space
import Mathlib.Data.Matrix.Mul

namespace LCH02

open formal_oet.vol_01.ch_01_foundations
open scoped Classical
noncomputable section

abbrev Mat (I : Type) := Matrix I I ENNReal

variable {I X : Type} {b : X}

def entry (M : Mat I) (i j : I) : ENNReal := M j i

theorem entry_mul [Fintype I] (B A : Mat I) (i j : I) :
    entry (B * A) i j = ∑ k, entry B k j * entry A i k :=
  Matrix.mul_apply

theorem unit_entry (i j : I) :
    entry (1 : Mat I) i j = if j = i then 1 else 0 := Matrix.one_apply

/-- The last operation is at the head, as in the frozen OperatorChain. -/
def orderedProduct [Fintype I] (ms : List (Mat I)) : Mat I := ms.prod

@[simp] theorem product_nil [Fintype I] : orderedProduct ([] : List (Mat I)) = 1 := rfl

@[simp] theorem product_cons [Fintype I] (A : Mat I) (ms : List (Mat I)) :
    orderedProduct (A :: ms) = A * orderedProduct ms := rfl

structure Gauge (X I : Type) (b : X) [Fintype I] [Nonempty I] where
  d : I → X → X → ENNReal
  metric : ∀ i, ExtendedPseudoMetric X b (d i)

variable [Fintype I] [Nonempty I] (G : Gauge X I b)

def Gauge.vec (x y : X) : I → ENNReal := fun i => G.d i x y

def LipOn (f : Operator X b) (U : Set X) (M : Mat I) : Prop :=
  U ⊆ dom f ∧ ∀ x ∈ U, ∀ y ∈ U,
    G.vec (f.func x) (f.func y) ≤ M.mulVec (G.vec x y)

def IsLip (f : Operator X b) (M : Mat I) : Prop := LipOn G f (dom f) M

def lipFamilyOn (f : Operator X b) (U : Set X) : Set (Mat I) := {M | LipOn G f U M}

def lipFamily (f : Operator X b) : Set (Mat I) := {M | IsLip G f M}

def CoLipOn (f : Operator X b) (U : Set X) (M : Mat I) : Prop :=
  U.Nonempty ∧ U ⊆ dom f ∧ ∀ x ∈ U, ∀ y ∈ U,
    M.mulVec (G.vec x y) ≤ G.vec (f.func x) (f.func y)

def coLipFamilyOn (f : Operator X b) (U : Set X) : Set (Mat I) := {M | CoLipOn G f U M}

variable {f g : Operator X b} {U V : Set X} {A B : Mat I}

theorem singleton_lip [Subsingleton I] (i : I) :
    IsLip G f A ↔ ∀ x ∈ dom f, ∀ y ∈ dom f,
      G.d i (f.func x) (f.func y) ≤ entry A i i * G.d i x y := by
  have row (x y : X) : A.mulVec (G.vec x y) i = entry A i i * G.d i x y :=
    Fintype.sum_subsingleton (fun k => A i k * G.d k x y) i
  constructor
  · intro h x hx y hy
    exact (h.2 x hx y hy i).trans_eq (row x y)
  · intro h
    refine ⟨Set.Subset.rfl, fun x hx y hy j => ?_⟩
    obtain rfl : j = i := Subsingleton.elim _ _
    exact (h x hx y hy).trans_eq (row x y).symm

theorem lip_restrict (hUV : U ⊆ V) (hV : V ⊆ dom f) :
    lipFamilyOn G f V ⊆ lipFamilyOn G f U :=
  fun _ h => ⟨hUV.trans hV, fun x hx y hy => h.2 x (hUV hx) y (hUV hy)⟩

theorem lip_from_dom (hU : U ⊆ dom f) : lipFamily G f ⊆ lipFamilyOn G f U :=
  lip_restrict G hU Set.Subset.rfl

theorem coLip_restrict (hne : U.Nonempty) (hUV : U ⊆ V) (hV : V ⊆ dom f) :
    coLipFamilyOn G f V ⊆ coLipFamilyOn G f U :=
  fun _ h => ⟨hne, hUV.trans hV, fun x hx y hy => h.2.2 x (hUV hx) y (hUV hy)⟩

theorem coLip_from_dom (hne : U.Nonempty) (hU : U ⊆ dom f) :
    coLipFamilyOn G f (dom f) ⊆ coLipFamilyOn G f U :=
  coLip_restrict G hne hU Set.Subset.rfl

omit [Nonempty I] in
private theorem mulVec_mono (M : Mat I) {v w : I → ENNReal} (h : v ≤ w) :
    M.mulVec v ≤ M.mulVec w := fun j =>
  Finset.sum_le_sum fun i _ => mul_le_mul_right (h i) (M j i)

theorem lip_comp (hU : U ⊆ dom (g * f)) (ha : A ∈ lipFamilyOn G f U)
    (hb : B ∈ lipFamilyOn G g (f.func '' U)) :
    B * A ∈ lipFamilyOn G (g * f) U := by
  refine ⟨hU, fun x hx y hy => ?_⟩
  have h := hb.2 _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  exact (h.trans (mulVec_mono B (ha.2 x hx y hy))).trans_eq (Matrix.mulVec_mulVec _ _ _)

theorem coLip_comp (hU : U ⊆ dom (g * f)) (ha : A ∈ coLipFamilyOn G f U)
    (hb : B ∈ coLipFamilyOn G g (f.func '' U)) :
    B * A ∈ coLipFamilyOn G (g * f) U := by
  refine ⟨ha.1, hU, fun x hx y hy => ?_⟩
  rw [← Matrix.mulVec_mulVec]
  exact (mulVec_mono B (ha.2.2 x hx y hy)).trans (hb.2.2 _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩)

theorem coLip_zero_entry {i j : I} {x y : X} (hx : x ∈ dom f) (hy : y ∈ dom f)
    (hout : G.d j (f.func x) (f.func y) = 0) (hin : 0 < G.d i x y)
    (ha : A ∈ coLipFamilyOn G f (dom f)) : entry A i j = 0 := by
  have term : entry A i j * G.d i x y ≤ A.mulVec (G.vec x y) j :=
    Finset.single_le_sum (f := fun k => A j k * G.d k x y) (fun _ _ => zero_le _) (Finset.mem_univ i)
  have bound : entry A i j * G.d i x y ≤ 0 := (term.trans (ha.2.2 x hx y hy j)).trans_eq hout
  exact (mul_eq_zero.mp (le_antisymm bound (zero_le _))).resolve_right hin.ne'

theorem unit_lip (_hne : U.Nonempty) (hU : U ⊆ dom (1 : Operator X b)) :
    orderedProduct ([] : List (Mat I)) ∈ lipFamilyOn G 1 U :=
  ⟨hU, fun x _ y _ => (Matrix.one_mulVec (G.vec x y)).symm.le⟩

theorem unit_coLip (hne : U.Nonempty) (hU : U ⊆ dom (1 : Operator X b)) :
    orderedProduct ([] : List (Mat I)) ∈ coLipFamilyOn G 1 U :=
  ⟨hne, hU, fun x _ y _ => (Matrix.one_mulVec (G.vec x y)).le⟩

end
end LCH02
