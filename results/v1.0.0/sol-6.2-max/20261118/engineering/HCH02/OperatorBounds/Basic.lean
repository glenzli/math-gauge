import formal_oet.vol_01.ch_01_foundations.operator_space
import Mathlib.Data.Matrix.Mul

/- The Operator Evolution Theory, historical Chapter 2, Zhe Li (Glen Li / glenzli).
   Independent Lean formalization of the frozen text, licensed under CC BY 4.0. -/

namespace HCH02

open formal_oet.vol_01.ch_01_foundations
open scoped BigOperators ENNReal

variable {X I : Type} {bot : X}

abbrev BoundMatrix (I : Type) := I → I → ℝ≥0∞

/-- Display a coefficient at row j and column i when its channel is i → j. -/
def display : BoundMatrix I ≃ Matrix I I ℝ≥0∞ where
  toFun M j i := M i j
  invFun M i j := M j i
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def matrixMul [Fintype I] (B A : BoundMatrix I) : BoundMatrix I :=
  fun i j => ∑ k, B k j * A i k

theorem display_mul [Fintype I] (B A : BoundMatrix I) :
    display (matrixMul B A) = display B * display A := rfl

def identityOp : Operator X bot := OperatorChain []

def composeOp (ψ φ : Operator X bot) : Operator X bot :=
  ⟨fun x => ψ.func (φ.func x), by simp only [φ.preserves_bot, ψ.preserves_bot]⟩

theorem mem_dom_compose {ψ φ : Operator X bot} {x : X} :
    x ∈ dom (composeOp ψ φ) ↔ x ∈ dom φ ∧ φ.func x ∈ dom ψ := by
  change ψ.func (φ.func x) ≠ bot ↔ φ.func x ≠ bot ∧ ψ.func (φ.func x) ≠ bot
  refine ⟨fun h => ⟨?_, h⟩, And.right⟩
  intro e
  exact h (by rw [e, ψ.preserves_bot])

theorem compose_domains {ψ φ : Operator X bot} {U : Set X}
    (h : U ⊆ dom (composeOp ψ φ)) :
    U ⊆ dom φ ∧ operator_image φ U ⊆ dom ψ := by
  refine ⟨fun x hx => (mem_dom_compose.mp (h hx)).1, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact (mem_dom_compose.mp (h hx)).2

variable [Fintype I] (d : I → X → X → ℝ≥0∞)

noncomputable def weightedDistance (M : BoundMatrix I) (x y : X) (j : I) : ℝ≥0∞ :=
  ∑ i, M i j * d i x y

def lipOn (φ : Operator X bot) (U : Set X) : Set (BoundMatrix I) :=
  {L | U ⊆ dom φ ∧ ∀ ⦃x y⦄, x ∈ U → y ∈ U → ∀ j,
    d j (φ.func x) (φ.func y) ≤ weightedDistance d L x y j}

def lip (φ : Operator X bot) : Set (BoundMatrix I) :=
  lipOn d φ (dom φ)

def coLipOn (φ : Operator X bot) (U : Set X) : Set (BoundMatrix I) :=
  {K | U.Nonempty ∧ U ⊆ dom φ ∧ ∀ ⦃x y⦄, x ∈ U → y ∈ U → ∀ j,
    weightedDistance d K x y j ≤ d j (φ.func x) (φ.func y)}

variable {d} {φ ψ : Operator X bot} {U V : Set X}

theorem mem_coLipOn_iff {K : BoundMatrix I} :
    K ∈ coLipOn d φ U ↔ U ≠ ∅ ∧ U ⊆ dom φ ∧
      ∀ ⦃x y⦄, x ∈ U → y ∈ U → ∀ j,
        weightedDistance d K x y j ≤ d j (φ.func x) (φ.func y) := by
  simp only [coLipOn, Set.mem_setOf_eq, Set.nonempty_iff_ne_empty]

theorem top_coefficient (r : ℝ≥0∞) :
    (⊤ : ℝ≥0∞) * r = if r = 0 then 0 else ⊤ :=
  ENNReal.top_mul'

theorem term_le_weightedDistance (M : BoundMatrix I) (x y : X) (i j : I) :
    M i j * d i x y ≤ weightedDistance d M x y j :=
  Finset.single_le_sum (f := fun k => M k j * d k x y)
    (fun _ _ => zero_le _) (Finset.mem_univ i)

theorem top_channel_bound {M : BoundMatrix I} {x y : X} {i j : I}
    (hM : M i j = ⊤) (hxy : 0 < d i x y) : weightedDistance d M x y j = ⊤ := by
  have h := term_le_weightedDistance (d := d) M x y i j
  rw [hM, ENNReal.top_mul hxy.ne'] at h
  exact top_unique h

theorem singleton_lip (i : I) (hi : ∀ k : I, k = i) (L : BoundMatrix I) :
    L ∈ lip d φ ↔ ∀ ⦃x y⦄, x ∈ dom φ → y ∈ dom φ →
      d i (φ.func x) (φ.func y) ≤ L i i * d i x y := by
  letI : Unique I := ⟨⟨i⟩, hi⟩
  have hsum (x y : X) : weightedDistance d L x y i = L i i * d i x y :=
    Fintype.sum_unique _
  constructor
  · intro h x y hx hy
    simpa only [← hsum] using h.2 hx hy i
  · intro h
    refine ⟨Set.Subset.rfl, fun x y hx hy j => ?_⟩
    rw [hi j, hsum]
    exact h hx hy

theorem lipOn_mono (hUV : U ⊆ V) : lipOn d φ V ⊆ lipOn d φ U :=
  fun _ h => ⟨hUV.trans h.1, fun _ _ hx hy j => h.2 (hUV hx) (hUV hy) j⟩

theorem lip_restrict (hU : U ⊆ dom φ) : lip d φ ⊆ lipOn d φ U :=
  lipOn_mono hU

noncomputable def lipEntryInf (d : I → X → X → ℝ≥0∞) (φ : Operator X bot)
    (U : Set X) (i j : I) : ℝ≥0∞ :=
  sInf ((fun L => L i j) '' lipOn d φ U)

theorem lipEntryInf_mono (hUV : U ⊆ V) (i j : I) :
    lipEntryInf d φ U i j ≤ lipEntryInf d φ V i j :=
  sInf_le_sInf (Set.image_mono (lipOn_mono hUV))

theorem coLip_channel_bound {K : BoundMatrix I} (hK : K ∈ coLipOn d φ U)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (i j : I) :
    K i j * d i x y ≤ d j (φ.func x) (φ.func y) :=
  (term_le_weightedDistance K x y i j).trans (hK.2.2 hx hy j)

theorem coLip_zero_of_collapsed {K : BoundMatrix I} (hK : K ∈ coLipOn d φ (dom φ))
    {x y : X} (hx : x ∈ dom φ) (hy : y ∈ dom φ) {i j : I}
    (hout : d j (φ.func x) (φ.func y) = 0) (hin : 0 < d i x y) : K i j = 0 := by
  have h := coLip_channel_bound hK hx hy i j
  rw [hout, nonpos_iff_eq_zero, mul_eq_zero] at h
  exact h.resolve_right hin.ne'

theorem weightedDistance_mul (B A : BoundMatrix I) (x y : X) (j : I) :
    weightedDistance d (matrixMul B A) x y j =
      ∑ k, B k j * weightedDistance d A x y k := by
  simp only [weightedDistance, matrixMul, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem lip_compose {A B : BoundMatrix I} (hU : U ⊆ dom (composeOp ψ φ))
    (hA : A ∈ lipOn d φ U) (hB : B ∈ lipOn d ψ (operator_image φ U)) :
    matrixMul B A ∈ lipOn d (composeOp ψ φ) U := by
  refine ⟨hU, fun x y hx hy j => ?_⟩
  change d j (ψ.func (φ.func x)) (ψ.func (φ.func y)) ≤
    weightedDistance d (matrixMul B A) x y j
  rw [weightedDistance_mul]
  exact (hB.2 ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩ j).trans
    (Finset.sum_le_sum fun k _ => mul_le_mul_right (hA.2 hx hy k) (B k j))

theorem coLip_compose {A B : BoundMatrix I} (hU : U ⊆ dom (composeOp ψ φ))
    (hA : A ∈ coLipOn d φ U) (hB : B ∈ coLipOn d ψ (operator_image φ U)) :
    matrixMul B A ∈ coLipOn d (composeOp ψ φ) U := by
  refine ⟨hA.1, hU, fun x y hx hy j => ?_⟩
  change weightedDistance d (matrixMul B A) x y j ≤
    d j (ψ.func (φ.func x)) (ψ.func (φ.func y))
  rw [weightedDistance_mul]
  exact (Finset.sum_le_sum fun k _ => mul_le_mul_right (hA.2.2 hx hy k) (B k j)).trans
    (hB.2.2 ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩ j)

def PointwiseClose (d : I → X → X → ℝ≥0∞) (φ ψ : Operator X bot)
    (U : Set X) (δ : I → ℝ≥0∞) : Prop :=
  U ⊆ dom φ ∩ dom ψ ∧ ∀ z ∈ U, ∀ j, d j (φ.func z) (ψ.func z) ≤ δ j

variable (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) {δ : I → ℝ≥0∞}

include hd

omit [Fintype I] in
theorem pointwiseClose_symm (h : PointwiseClose d φ ψ U δ) :
    PointwiseClose d ψ φ U δ := by
  refine ⟨fun x hx => ⟨(h.1 hx).2, (h.1 hx).1⟩, fun z hz j => ?_⟩
  rw [(hd j).symm (ψ.func z)]
  exact h.2 z hz j

omit [Fintype I] in
theorem perturb_forward (h : PointwiseClose d φ ψ U δ)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (ψ.func x) (ψ.func y) ≤ d j (φ.func x) (φ.func y) + δ j + δ j := by
  have h₁ := (pointwiseClose_symm hd h).2 x hx j
  have h₂ := h.2 y hy j
  calc
    _ ≤ d j (ψ.func x) (φ.func x) + d j (φ.func x) (ψ.func y) :=
      (hd j).triangle _ _ _
    _ ≤ δ j + (d j (φ.func x) (φ.func y) + δ j) :=
      add_le_add h₁ (((hd j).triangle _ (φ.func y) _).trans (add_le_add le_rfl h₂))
    _ = _ := by rw [← add_assoc, add_comm (δ j) (d j (φ.func x) (φ.func y))]

omit [Fintype I] in
theorem perturb_backward (h : PointwiseClose d φ ψ U δ)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (φ.func x) (φ.func y) ≤ d j (ψ.func x) (ψ.func y) + δ j + δ j :=
  perturb_forward hd (pointwiseClose_symm hd h) hx hy j

theorem perturb_lip (h : PointwiseClose d φ ψ U δ) {L : BoundMatrix I}
    (hL : L ∈ lipOn d φ U) {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (ψ.func x) (ψ.func y) ≤ weightedDistance d L x y j + 2 * δ j := by
  rw [two_mul, ← add_assoc]
  exact (perturb_forward hd h hx hy j).trans
    (add_le_add (add_le_add (hL.2 hx hy j) le_rfl) le_rfl)

theorem perturb_lip_reverse (h : PointwiseClose d φ ψ U δ) {L : BoundMatrix I}
    (hL : L ∈ lipOn d ψ U) {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (φ.func x) (φ.func y) ≤ weightedDistance d L x y j + 2 * δ j :=
  perturb_lip hd (pointwiseClose_symm hd h) hL hx hy j

theorem perturb_coLip (h : PointwiseClose d φ ψ U δ) {K : BoundMatrix I}
    (hK : K ∈ coLipOn d φ U) {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    weightedDistance d K x y j ≤ d j (ψ.func x) (ψ.func y) + 2 * δ j := by
  rw [two_mul, ← add_assoc]
  exact (hK.2.2 hx hy j).trans (perturb_backward hd h hx hy j)

theorem perturb_coLip_reverse (h : PointwiseClose d φ ψ U δ) {K : BoundMatrix I}
    (hK : K ∈ coLipOn d ψ U) {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    weightedDistance d K x y j ≤ d j (φ.func x) (φ.func y) + 2 * δ j :=
  perturb_coLip hd (pointwiseClose_symm hd h) hK hx hy j

end HCH02
