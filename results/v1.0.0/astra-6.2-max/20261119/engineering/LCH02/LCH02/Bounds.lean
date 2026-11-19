import LCH02.Matrices
import formal_oet.vol_01.ch_01_foundations.operator_space

namespace LCH02

open formal_oet.vol_01.ch_01_foundations
open scoped BigOperators Classical Matrix

structure Gauge (X I : Type) (b : X) [Fintype I] [Nonempty I] where
  dist : I → X → X → ENNReal
  metric : ∀ i, ExtendedPseudoMetric X b (dist i)

variable {X I : Type} {b : X} [Fintype I] [Nonempty I] (G : Gauge X I b)

def Gauge.vec (x y : X) : I → ENNReal := fun i => G.dist i x y

def LipOn (f : Operator X b) (U : Set X) (A : Bound I) : Prop :=
  U ⊆ dom f ∧ ∀ x ∈ U, ∀ y ∈ U, G.vec (f.func x) (f.func y) ≤ A *ᵥ G.vec x y

abbrev Lip (f : Operator X b) (A : Bound I) : Prop := LipOn G f (dom f) A

def lipFamily (f : Operator X b) (U : Set X) : Set (Bound I) := {A | LipOn G f U A}

def globalLipFamily (f : Operator X b) : Set (Bound I) := {A | Lip G f A}

def CoLipOn (f : Operator X b) (U : Set X) (A : Bound I) : Prop :=
  U.Nonempty ∧ U ⊆ dom f ∧
    ∀ x ∈ U, ∀ y ∈ U, A *ᵥ G.vec x y ≤ G.vec (f.func x) (f.func y)

def coLipFamily (f : Operator X b) (U : Set X) : Set (Bound I) := {A | CoLipOn G f U A}

variable {f g : Operator X b} {U V : Set X} {A B : Bound I}

theorem lip_singleton [Subsingleton I] (i : I) :
    Lip G f A ↔ ∀ x ∈ dom f, ∀ y ∈ dom f,
      G.dist i (f.func x) (f.func y) ≤ entry A i i * G.dist i x y := by
  have row (x y : X) : (A *ᵥ G.vec x y) i = entry A i i * G.dist i x y := by
    rw [row_sum]
    exact Finset.sum_eq_single i (fun k _ hk => (hk (Subsingleton.elim k i)).elim)
      (fun h => (h (Finset.mem_univ i)).elim)
  constructor
  · intro h x hx y hy
    exact (h.2 x hx y hy i).trans_eq (row x y)
  · intro h
    refine ⟨Set.Subset.refl _, fun x hx y hy j => ?_⟩
    obtain rfl := Subsingleton.elim j i
    exact (h x hx y hy).trans_eq (row x y).symm

theorem lip_restrict (hUV : U ⊆ V) (hV : V ⊆ dom f) :
    lipFamily G f V ⊆ lipFamily G f U :=
  fun _ h => ⟨hUV.trans hV, fun x hx y hy => h.2 x (hUV hx) y (hUV hy)⟩

theorem global_lip_restrict (hU : U ⊆ dom f) :
    globalLipFamily G f ⊆ lipFamily G f U :=
  lip_restrict G hU (Set.Subset.refl _)

theorem coLip_restrict (hne : U.Nonempty) (hUV : U ⊆ V) (hV : V ⊆ dom f) :
    coLipFamily G f V ⊆ coLipFamily G f U :=
  fun _ h => ⟨hne, hUV.trans hV, fun x hx y hy => h.2.2 x (hUV hx) y (hUV hy)⟩

theorem global_coLip_restrict (hne : U.Nonempty) (hU : U ⊆ dom f) :
    coLipFamily G f (dom f) ⊆ coLipFamily G f U :=
  coLip_restrict G hne hU (Set.Subset.refl _)

theorem coLip_entry_zero (i j : I) {x y : X} (hx : x ∈ dom f) (hy : y ∈ dom f)
    (hout : G.dist j (f.func x) (f.func y) = 0) (hin : 0 < G.dist i x y)
    (hA : A ∈ coLipFamily G f (dom f)) : entry A i j = 0 := by
  have hterm : entry A i j * G.dist i x y ≤ (A *ᵥ G.vec x y) j :=
    Finset.single_le_sum (fun k _ => zero_le (A j k * G.dist k x y)) (Finset.mem_univ i)
  have h := hterm.trans (hA.2.2 x hx y hy j)
  change entry A i j * G.dist i x y ≤ G.dist j (f.func x) (f.func y) at h
  rw [hout] at h
  exact (mul_eq_zero.mp (le_antisymm h (zero_le _))).resolve_right hin.ne'

theorem lip_compose (hU : U ⊆ dom (g * f)) (hf : A ∈ lipFamily G f U)
    (hg : B ∈ lipFamily G g (f.func '' U)) : B * A ∈ lipFamily G (g * f) U := by
  refine ⟨hU, fun x hx y hy => ?_⟩
  calc
    G.vec (g.func (f.func x)) (g.func (f.func y))
        ≤ B *ᵥ G.vec (f.func x) (f.func y) :=
      hg.2 _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    _ ≤ B *ᵥ A *ᵥ G.vec x y := mulVec_mono B (hf.2 x hx y hy)
    _ = _ := Matrix.mulVec_mulVec _ _ _

theorem coLip_compose (hU : U ⊆ dom (g * f)) (hf : A ∈ coLipFamily G f U)
    (hg : B ∈ coLipFamily G g (f.func '' U)) : B * A ∈ coLipFamily G (g * f) U := by
  refine ⟨hf.1, hU, fun x hx y hy => ?_⟩
  calc
    (B * A) *ᵥ G.vec x y = B *ᵥ A *ᵥ G.vec x y := (Matrix.mulVec_mulVec _ _ _).symm
    _ ≤ B *ᵥ G.vec (f.func x) (f.func y) := mulVec_mono B (hf.2.2 x hx y hy)
    _ ≤ G.vec (g.func (f.func x)) (g.func (f.func y)) :=
      hg.2.2 _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩

theorem identity_lip (_hne : U.Nonempty) (hU : U ⊆ dom (operator_identity (bot := b))) :
    unitMatrix I ∈ lipFamily G operator_identity U := by
  refine ⟨hU, fun x _ y _ => ?_⟩
  exact (Matrix.one_mulVec (G.vec x y)).symm.le

theorem identity_coLip (hne : U.Nonempty) (hU : U ⊆ dom (operator_identity (bot := b))) :
    unitMatrix I ∈ coLipFamily G operator_identity U := by
  refine ⟨hne, hU, fun x _ y _ => ?_⟩
  exact (Matrix.one_mulVec (G.vec x y)).le

end LCH02
