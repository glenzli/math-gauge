import LCH02.Matrix
import formal_oet.vol_01.ch_01_foundations.operator_space

namespace LCH02

open formal_oet.vol_01.ch_01_foundations
open scoped BigOperators Classical

structure Gauge (X I : Type) (bot : X) where
  index_nonempty : Nonempty I
  dist : I → X → X → ENNReal
  component : ∀ i : I, ExtendedPseudoMetric X bot (dist i)

variable {X I : Type} {bot : X} [Fintype I]

noncomputable def matrixBound (A : Coefficients I) (v : I → ENNReal) (j : I) : ENNReal :=
  Matrix.mulVec A v j

theorem matrixBound_apply (A : Coefficients I) (v : I → ENNReal) (j : I) :
    matrixBound A v j = ∑ i : I, entry A i j * v i := rfl

def LipOn (g : Gauge X I bot) (φ : Operator X bot) (U : Set X)
    (A : Coefficients I) : Prop :=
  U ⊆ dom φ ∧
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      g.dist j (φ.func x) (φ.func y) ≤ matrixBound A (fun i => g.dist i x y) j

def Lip (g : Gauge X I bot) (φ : Operator X bot) (A : Coefficients I) : Prop :=
  LipOn g φ (dom φ) A

def lipMatricesOn (g : Gauge X I bot) (φ : Operator X bot) (U : Set X) :
    Set (Coefficients I) :=
  {A | LipOn g φ U A}

def lipMatrices (g : Gauge X I bot) (φ : Operator X bot) : Set (Coefficients I) :=
  {A | Lip g φ A}

def CoLipOn (g : Gauge X I bot) (φ : Operator X bot) (U : Set X)
    (A : Coefficients I) : Prop :=
  U ⊆ dom φ ∧ U.Nonempty ∧
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      matrixBound A (fun i => g.dist i x y) j ≤ g.dist j (φ.func x) (φ.func y)

def coLipMatricesOn (g : Gauge X I bot) (φ : Operator X bot) (U : Set X) :
    Set (Coefficients I) :=
  {A | CoLipOn g φ U A}

variable {g : Gauge X I bot} {φ ψ : Operator X bot} {U V : Set X}

theorem lip_scalar_iff [Subsingleton I] (i : I) (A : Coefficients I) :
    Lip g φ A ↔ ∀ x ∈ dom φ, ∀ y ∈ dom φ,
      g.dist i (φ.func x) (φ.func y) ≤ entry A i i * g.dist i x y := by
  have hsum (v : I → ENNReal) : matrixBound A v i = entry A i i * v i := by
    rw [matrixBound_apply]
    exact Fintype.sum_eq_single i (fun k hk => (hk (Subsingleton.elim k i)).elim)
  constructor
  · intro h x hx y hy
    simpa only [hsum] using h.2 x hx y hy i
  · intro h
    refine ⟨Set.Subset.rfl, ?_⟩
    intro x hx y hy j
    rw [Subsingleton.elim j i, hsum]
    exact h x hx y hy

theorem lipMatricesOn_antitone (hUV : U ⊆ V) (hV : V ⊆ dom φ) :
    lipMatricesOn g φ V ⊆ lipMatricesOn g φ U := by
  intro A h
  exact ⟨hUV.trans hV, fun x hx y hy j => h.2 x (hUV hx) y (hUV hy) j⟩

theorem lipMatrices_restrict (hU : U ⊆ dom φ) :
    lipMatrices g φ ⊆ lipMatricesOn g φ U :=
  lipMatricesOn_antitone hU Set.Subset.rfl

theorem coLipMatricesOn_antitone (hne : U.Nonempty) (hUV : U ⊆ V) (hV : V ⊆ dom φ) :
    coLipMatricesOn g φ V ⊆ coLipMatricesOn g φ U := by
  intro A h
  exact ⟨hUV.trans hV, hne, fun x hx y hy j => h.2.2 x (hUV hx) y (hUV hy) j⟩

theorem coLipMatrices_restrict (hne : U.Nonempty) (hU : U ⊆ dom φ) :
    coLipMatricesOn g φ (dom φ) ⊆ coLipMatricesOn g φ U :=
  coLipMatricesOn_antitone hne hU Set.Subset.rfl

theorem coLip_entry_zero {A : Coefficients I} (h : CoLipOn g φ (dom φ) A)
    {x y : X} (hx : x ∈ dom φ) (hy : y ∈ dom φ) {i j : I}
    (hout : g.dist j (φ.func x) (φ.func y) = 0) (hin : 0 < g.dist i x y) :
    entry A i j = 0 := by
  have hlower := h.2.2 x hx y hy j
  rw [hout, matrixBound_apply] at hlower
  have hterm : entry A i j * g.dist i x y ≤
      ∑ k : I, entry A k j * g.dist k x y :=
    Finset.single_le_sum (f := fun k => entry A k j * g.dist k x y)
      (fun _ _ => zero_le _) (Finset.mem_univ i)
  have heq := le_antisymm (hterm.trans hlower) (zero_le _)
  exact (mul_eq_zero.mp heq).resolve_right hin.ne'

theorem mem_dom_mul {x : X} :
    x ∈ dom (ψ * φ) ↔ x ∈ dom φ ∧ φ.func x ∈ dom ψ := by
  change ψ.func (φ.func x) ≠ bot ↔ φ.func x ≠ bot ∧ ψ.func (φ.func x) ≠ bot
  refine ⟨fun h => ⟨?_, h⟩, And.right⟩
  intro hx
  apply h
  rw [hx, ψ.preserves_bot]

theorem image_subset_dom_of_mul (hU : U ⊆ dom (ψ * φ)) :
    operator_image φ U ⊆ dom ψ := by
  rintro _ ⟨x, hx, rfl⟩
  exact (mem_dom_mul.mp (hU hx)).2

theorem image_mul (φ ψ : Operator X bot) (U : Set X) :
    operator_image (ψ * φ) U = operator_image ψ (operator_image φ U) :=
  (Set.image_image ψ.func φ.func U).symm

private theorem matrixBound_mono (A : Coefficients I) {v w : I → ENNReal}
    (h : ∀ i, v i ≤ w i) (j : I) : matrixBound A v j ≤ matrixBound A w j := by
  rw [matrixBound_apply, matrixBound_apply]
  exact Finset.sum_le_sum (fun i _ => mul_le_mul_right (h i) _)

private theorem matrixBound_mul (A B : Coefficients I) (v : I → ENNReal) (j : I) :
    matrixBound (B * A) v j = matrixBound B (matrixBound A v) j :=
  (congrFun (Matrix.mulVec_mulVec v B A) j).symm

theorem lip_comp {A B : Coefficients I} (hU : U ⊆ dom (ψ * φ))
    (hA : LipOn g φ U A) (hB : LipOn g ψ (operator_image φ U) B) :
    LipOn g (ψ * φ) U (B * A) := by
  refine ⟨hU, ?_⟩
  intro x hx y hy j
  have hx' : φ.func x ∈ operator_image φ U := ⟨x, hx, rfl⟩
  have hy' : φ.func y ∈ operator_image φ U := ⟨y, hy, rfl⟩
  rw [matrixBound_mul]
  exact (hB.2 _ hx' _ hy' j).trans (matrixBound_mono B (hA.2 x hx y hy) j)

theorem coLip_comp {A B : Coefficients I} (hU : U ⊆ dom (ψ * φ))
    (hA : CoLipOn g φ U A) (hB : CoLipOn g ψ (operator_image φ U) B) :
    CoLipOn g (ψ * φ) U (B * A) := by
  refine ⟨hU, hA.2.1, ?_⟩
  intro x hx y hy j
  have hx' : φ.func x ∈ operator_image φ U := ⟨x, hx, rfl⟩
  have hy' : φ.func y ∈ operator_image φ U := ⟨y, hy, rfl⟩
  rw [matrixBound_mul]
  exact (matrixBound_mono B (hA.2.2 x hx y hy) j).trans (hB.2.2 _ hx' _ hy' j)

private theorem matrixBound_unit (v : I → ENNReal) (j : I) :
    matrixBound matrixUnit v j = v j :=
  congrFun (Matrix.one_mulVec v) j

theorem unit_lip (hU : U ⊆ dom (1 : Operator X bot)) (_hne : U.Nonempty) :
    LipOn g 1 U matrixUnit := by
  refine ⟨hU, ?_⟩
  intro x _ y _ j
  rw [matrixBound_unit]
  exact le_rfl

theorem unit_coLip (hU : U ⊆ dom (1 : Operator X bot)) (hne : U.Nonempty) :
    CoLipOn g 1 U matrixUnit := by
  refine ⟨hU, hne, ?_⟩
  intro x _ y _ j
  rw [matrixBound_unit]
  exact le_rfl

end LCH02
