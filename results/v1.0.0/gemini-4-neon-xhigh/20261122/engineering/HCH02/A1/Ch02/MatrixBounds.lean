import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space
import Ch02.MatrixCore

/-!
# Chapter 2 Matrix Bounds: Lipschitz & co-Lipschitz Certificates, Two-Step Composition, and Perturbation

Formalizes Section 2.1 (definitions, basic restriction/monotonicity facts, two-step
composition laws, co-Lip vanishing criterion, and two-operator perturbation bounds)
from `source/02-operator-bounds.md` (`HC02-D01`, `HC02-D02`, `HC02-P01`–`HC02-P11`).
-/

namespace OetCh02

open formal_oet.vol_01.ch_01_foundations

/-! ### 1. Global and Restricted Lipschitz Matrix Certificates (HC02-D01) -/

/-- A gauge matrix `L` is a legal global Lipschitz matrix for `ϕ` if for all `x, y ∈ dom(ϕ)`
and all `j ∈ I`, `d_j(ϕ(x), ϕ(y)) ≤ ∑ i, L_{i → j} * d_i(x, y)`. -/
def IsLipMatrix {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (L : GaugeMatrix I) : Prop :=
  ∀ x ∈ dom ϕ, ∀ y ∈ dom ϕ, ∀ j : I,
    d j (ϕ.func x) (ϕ.func y) ≤ ∑ i : I, L i j * d i x y

/-- Certificate family `ℒ(ϕ)` of all legal global Lipschitz matrices of `ϕ`. -/
def LipSet {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) : Set (GaugeMatrix I) :=
  { L | IsLipMatrix d ϕ L }

/-- A gauge matrix `L` is a legal restricted Lipschitz matrix for `ϕ` on `U` if
`U ⊆ dom(ϕ)` and for all `x, y ∈ U` and `j ∈ I`,
`d_j(ϕ(x), ϕ(y)) ≤ ∑ i, L_{i → j} * d_i(x, y)`. -/
def IsRestrictedLipMatrix {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (L : GaugeMatrix I) : Prop :=
  U ⊆ dom ϕ ∧
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      d j (ϕ.func x) (ϕ.func y) ≤ ∑ i : I, L i j * d i x y

/-- Certificate family `ℒ(ϕ)|_U` of all legal restricted Lipschitz matrices of `ϕ` on `U`. -/
def RestrictedLipSet {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) : Set (GaugeMatrix I) :=
  { L | IsRestrictedLipMatrix d ϕ U L }

theorem lipSet_eq_restrictedLipSet_dom {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) :
    LipSet d ϕ = RestrictedLipSet d ϕ (dom ϕ) := by
  ext L
  simp [LipSet, RestrictedLipSet, IsLipMatrix, IsRestrictedLipMatrix]

/-- Generalized Lip convention: `∞ * 0 = 0`, so an `∞` entry contributes `0` when `d_i(x, y) = 0`. -/
theorem top_entry_mul_zero {X I : Type} (d : I → X → X → ENNReal)
    (L : GaugeMatrix I) {i j : I} {x y : X}
    (hL : L i j = ⊤) (hd : d i x y = 0) :
    L i j * d i x y = 0 := by
  rw [hL, hd, mul_zero]

/-- Generalized Lip convention: when `L_{i → j} = ∞` and `d_i(x, y) > 0`, the term is `∞`
and the Lip inequality holds trivially. -/
theorem top_entry_lip_ineq_trivial {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    (L : GaugeMatrix I) {i j : I} {x y : X}
    (hL : L i j = ⊤) (hd : 0 < d i x y) :
    d j (ϕ.func x) (ϕ.func y) ≤ ∑ k : I, L k j * d k x y := by
  have hterm : L i j * d i x y = ⊤ := by
    rw [hL, ENNReal.top_mul hd.ne']
  have hsum_top : (∑ k : I, L k j * d k x y) = ⊤ :=
    top_unique (hterm ▸ Finset.single_le_sum (f := fun k => L k j * d k x y)
      (fun _ _ => zero_le _) (Finset.mem_univ i))
  rw [hsum_top]
  exact le_top

/-! ### 2. Single-Component Degeneration and Restriction Monotonicity (HC02-P01–P04) -/

/--
OET anchor: h-c4369c63c86cbacf (`HC02-P01`)
When `I = {i}`, the Lipschitz matrix condition degenerates to the single scalar
inequality `d_i(ϕ(x), ϕ(y)) ≤ L_{i → i} * d_i(x, y)` on `dom(ϕ)`.
-/
theorem isLipMatrix_iff_scalar_of_singleton {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (L : GaugeMatrix I)
    (i : I) (hI : ∀ k : I, k = i) :
    L ∈ LipSet d ϕ ↔
      ∀ x ∈ dom ϕ, ∀ y ∈ dom ϕ, d i (ϕ.func x) (ϕ.func y) ≤ L i i * d i x y := by
  have hsum : ∀ x y : X, (∑ k : I, L k i * d k x y) = L i i * d i x y := by
    intro x y
    rw [Finset.sum_eq_single i]
    · intro k _ hki
      exact absurd (hI k) hki
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  constructor
  · intro hL x hx y hy
    simpa [hsum x y] using hL x hx y hy i
  · intro hscalar x hx y hy j
    have hj : j = i := hI j
    subst hj
    rw [hsum x y]
    exact hscalar x hx y hy

/-- `HC02-P01` stated directly with `Fintype.card I = 1`. -/
theorem isLipMatrix_iff_scalar_of_card_eq_one {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (L : GaugeMatrix I)
    (hcard : Fintype.card I = 1) (i : I) :
    L ∈ LipSet d ϕ ↔
      ∀ x ∈ dom ϕ, ∀ y ∈ dom ϕ, d i (ϕ.func x) (ϕ.func y) ≤ L i i * d i x y := by
  apply isLipMatrix_iff_scalar_of_singleton d ϕ L i
  intro k
  rcases Fintype.card_eq_one_iff.mp hcard with ⟨a, ha⟩
  rw [ha k, ha i]

/--
`HC02-P02`: For `U ⊆ dom(ϕ)`, every global Lip certificate restricts to `U`:
`ℒ(ϕ) ⊆ ℒ(ϕ)|_U`.
-/
theorem lipSet_subset_restrictedLipSet {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X} (hU : U ⊆ dom ϕ) :
    LipSet d ϕ ⊆ RestrictedLipSet d ϕ U := by
  intro L hL
  exact ⟨hU, fun x hx y hy j => hL x (hU hx) y (hU hy) j⟩

/--
`HC02-P03`: Shrinking the evaluation domain enlarges the restricted Lip certificate family:
if `U ⊆ V`, then `ℒ(ϕ)|_V ⊆ ℒ(ϕ)|_U` (in particular for `U ⊆ V ⊆ dom(ϕ)`).
-/
theorem restrictedLipSet_antitone {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U V : Set X}
    (hUV : U ⊆ V) :
    RestrictedLipSet d ϕ V ⊆ RestrictedLipSet d ϕ U := by
  intro L hL
  exact ⟨Set.Subset.trans hUV hL.1, fun x hx y hy j => hL.2 x (hUV hx) y (hUV hy) j⟩

/-- Entrywise infimum `a_{i → j}(U) := inf { M_{i → j} : M ∈ ℒ(ϕ)|_U }` (`HC02-P04`). -/
noncomputable def entrywiseLipInf {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i j : I) : ENNReal :=
  sInf { c : ENNReal | ∃ M ∈ RestrictedLipSet d ϕ U, M i j = c }

/--
`HC02-P04`: Shrinking the domain cannot increase the entrywise infimum of restricted Lip
certificates: if `U ⊆ V`, then `a_{i → j}(U) ≤ a_{i → j}(V)`.
-/
theorem entrywiseLipInf_mono {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U V : Set X}
    (hUV : U ⊆ V) (i j : I) :
    entrywiseLipInf d ϕ U i j ≤ entrywiseLipInf d ϕ V i j := by
  apply sInf_le_sInf
  rintro c ⟨M, hM, rfl⟩
  exact ⟨M, restrictedLipSet_antitone d ϕ hUV hM, rfl⟩

/-! ### 3. Two-Step Lipschitz Composition Law (HC02-P05) -/

/--
OET anchor: h-193cebcc1a7f9259 (`HC02-P05`)
**Proposition (Lip matrix composition law)**:
For `U₁ ⊆ dom(ϕ₂ ∘ ϕ₁)` and `U₂ = ϕ₁(U₁)`, if `L₁ ∈ ℒ(ϕ₁)|_{U₁}` and `L₂ ∈ ℒ(ϕ₂)|_{U₂}`,
then `L₂ · L₁ ∈ ℒ(ϕ₂ ∘ ϕ₁)|_{U₁}`.
-/
theorem restrictedLipSet_comp {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ1 ϕ2 : Operator X bot) (U1 : Set X)
    (hU1 : U1 ⊆ dom (compOp ϕ2 ϕ1))
    {L1 L2 : GaugeMatrix I}
    (hL1 : L1 ∈ RestrictedLipSet d ϕ1 U1)
    (hL2 : L2 ∈ RestrictedLipSet d ϕ2 (operator_image ϕ1 U1)) :
    matMul L2 L1 ∈ RestrictedLipSet d (compOp ϕ2 ϕ1) U1 := by
  refine ⟨hU1, ?_⟩
  intro x hx y hy j
  have hx2 : ϕ1.func x ∈ operator_image ϕ1 U1 := ⟨x, hx, rfl⟩
  have hy2 : ϕ1.func y ∈ operator_image ϕ1 U1 := ⟨y, hy, rfl⟩
  calc
    d j ((compOp ϕ2 ϕ1).func x) ((compOp ϕ2 ϕ1).func y)
        = d j (ϕ2.func (ϕ1.func x)) (ϕ2.func (ϕ1.func y)) := rfl
    _ ≤ ∑ k : I, L2 k j * d k (ϕ1.func x) (ϕ1.func y) :=
          hL2.2 (ϕ1.func x) hx2 (ϕ1.func y) hy2 j
    _ ≤ ∑ k : I, L2 k j * (∑ i : I, L1 i k * d i x y) := by
          refine Finset.sum_le_sum ?_
          intro k _
          exact mul_le_mul_right (hL1.2 x hx y hy k) (L2 k j)
    _ = ∑ k : I, ∑ i : I, L2 k j * (L1 i k * d i x y) := by
          refine Finset.sum_congr rfl ?_
          intro k _
          rw [Finset.mul_sum]
    _ = ∑ i : I, ∑ k : I, L2 k j * (L1 i k * d i x y) := Finset.sum_comm
    _ = ∑ i : I, (∑ k : I, L2 k j * L1 i k) * d i x y := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl ?_
          intro k _
          rw [mul_assoc]
    _ = ∑ i : I, matMul L2 L1 i j * d i x y := rfl

/-! ### 4. Restricted co-Lipschitz Matrix Certificates (HC02-D02) -/

/-- A gauge matrix `K` is a legal restricted co-Lipschitz matrix for `ϕ` on `U` if
`U` is nonempty, `U ⊆ dom(ϕ)`, and for all `x, y ∈ U` and `j ∈ I`,
`∑ i, K_{i → j} * d_i(x, y) ≤ d_j(ϕ(x), ϕ(y))`. -/
def IsCoLipMatrix {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (K : GaugeMatrix I) : Prop :=
  U.Nonempty ∧ U ⊆ dom ϕ ∧
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      ∑ i : I, K i j * d i x y ≤ d j (ϕ.func x) (ϕ.func y)

/-- Certificate family `𝒦(ϕ)|_U` of all legal restricted co-Lipschitz matrices of `ϕ` on `U`.
Membership always includes `U ≠ ∅` (`U.Nonempty`) and `U ⊆ dom(ϕ)`. -/
def CoLipSet {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) : Set (GaugeMatrix I) :=
  { K | IsCoLipMatrix d ϕ U K }

theorem coLipSet_nonempty_of_mem {X I : Type} {bot : X} [Fintype I]
    {d : I → X → X → ENNReal} {ϕ : Operator X bot} {U : Set X} {K : GaugeMatrix I}
    (hK : K ∈ CoLipSet d ϕ U) : U.Nonempty :=
  hK.1

theorem coLipSet_ne_empty_of_mem {X I : Type} {bot : X} [Fintype I]
    {d : I → X → X → ENNReal} {ϕ : Operator X bot} {U : Set X} {K : GaugeMatrix I}
    (hK : K ∈ CoLipSet d ϕ U) : U ≠ ∅ :=
  hK.1.ne_empty

theorem coLipSet_subset_dom_of_mem {X I : Type} {bot : X} [Fintype I]
    {d : I → X → X → ENNReal} {ϕ : Operator X bot} {U : Set X} {K : GaugeMatrix I}
    (hK : K ∈ CoLipSet d ϕ U) : U ⊆ dom ϕ :=
  hK.2.1

/-! ### 5. co-Lipschitz Vanishing Criterion and Two-Step Composition Law (HC02-P06, P07) -/

/-- General restricted-domain form of the co-Lip vanishing pair criterion. -/
theorem coLip_entry_eq_zero_of_pair_on {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    {K : GaugeMatrix I} (hK : K ∈ CoLipSet d ϕ U)
    {i j : I} {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    (h_out : d j (ϕ.func x) (ϕ.func y) = 0) (h_in : 0 < d i x y) :
    K i j = 0 := by
  have hle : K i j * d i x y ≤ 0 := by
    calc
      K i j * d i x y
          ≤ ∑ k : I, K k j * d k x y :=
            Finset.single_le_sum (f := fun k => K k j * d k x y)
              (fun _ _ => zero_le _) (Finset.mem_univ i)
      _ ≤ d j (ϕ.func x) (ϕ.func y) := hK.2.2 x hx y hy j
      _ = 0 := h_out
  have hmul : K i j * d i x y = 0 := le_antisymm hle (zero_le _)
  rcases mul_eq_zero.mp hmul with hK0 | hd0
  · exact hK0
  · exact absurd hd0 h_in.ne'

/--
OET anchor: h-88784dcbfff0ea66 (`HC02-P06`)
**Remark (Point-pair criterion for co-Lip channel degeneration)**:
If there exist `x, y ∈ dom(ϕ)` with `d_j(ϕ(x), ϕ(y)) = 0` and `d_i(x, y) > 0`,
then every global co-Lip matrix `K ∈ 𝒦(ϕ)|_{dom(ϕ)}` satisfies `K_{i → j} = 0`.
-/
theorem coLip_entry_eq_zero_of_pair {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    {K : GaugeMatrix I} (hK : K ∈ CoLipSet d ϕ (dom ϕ))
    {i j : I} {x y : X} (hx : x ∈ dom ϕ) (hy : y ∈ dom ϕ)
    (h_out : d j (ϕ.func x) (ϕ.func y) = 0) (h_in : 0 < d i x y) :
    K i j = 0 :=
  coLip_entry_eq_zero_of_pair_on d ϕ (dom ϕ) hK hx hy h_out h_in

/--
OET anchor: h-0f256e6f1d38a612 (`HC02-P07`)
**Proposition (co-Lip matrix composition law)**:
For `U₁ ⊆ dom(ϕ₂ ∘ ϕ₁)` and `U₂ = ϕ₁(U₁)`, if `K₁ ∈ 𝒦(ϕ₁)|_{U₁}` and `K₂ ∈ 𝒦(ϕ₂)|_{U₂}`,
then `K₂ · K₁ ∈ 𝒦(ϕ₂ ∘ ϕ₁)|_{U₁}` (which in particular certifies `U₁.Nonempty`).
-/
theorem coLipSet_comp {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ1 ϕ2 : Operator X bot) (U1 : Set X)
    (hU1 : U1 ⊆ dom (compOp ϕ2 ϕ1))
    {K1 K2 : GaugeMatrix I}
    (hK1 : K1 ∈ CoLipSet d ϕ1 U1)
    (hK2 : K2 ∈ CoLipSet d ϕ2 (operator_image ϕ1 U1)) :
    matMul K2 K1 ∈ CoLipSet d (compOp ϕ2 ϕ1) U1 := by
  refine ⟨hK1.1, hU1, ?_⟩
  intro x hx y hy j
  have hx2 : ϕ1.func x ∈ operator_image ϕ1 U1 := ⟨x, hx, rfl⟩
  have hy2 : ϕ1.func y ∈ operator_image ϕ1 U1 := ⟨y, hy, rfl⟩
  calc
    ∑ i : I, matMul K2 K1 i j * d i x y
        = ∑ i : I, (∑ k : I, K2 k j * K1 i k) * d i x y := rfl
    _ = ∑ i : I, ∑ k : I, K2 k j * (K1 i k * d i x y) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl ?_
          intro k _
          rw [mul_assoc]
    _ = ∑ k : I, ∑ i : I, K2 k j * (K1 i k * d i x y) := Finset.sum_comm
    _ = ∑ k : I, K2 k j * (∑ i : I, K1 i k * d i x y) := by
          refine Finset.sum_congr rfl ?_
          intro k _
          rw [Finset.mul_sum]
    _ ≤ ∑ k : I, K2 k j * d k (ϕ1.func x) (ϕ1.func y) := by
          refine Finset.sum_le_sum ?_
          intro k _
          exact mul_le_mul_right (hK1.2.2 x hx y hy k) (K2 k j)
    _ ≤ d j (ϕ2.func (ϕ1.func x)) (ϕ2.func (ϕ1.func y)) :=
          hK2.2.2 (ϕ1.func x) hx2 (ϕ1.func y) hy2 j
    _ = d j ((compOp ϕ2 ϕ1).func x) ((compOp ϕ2 ϕ1).func y) := rfl

/-! ### 6. Two-Operator Pairwise Image-Distance Perturbation Bounds (HC02-P08–P11) -/

/--
OET anchor: h-b959b42f25710105 (i), forward direction (`HC02-P08`)
If `U ⊆ dom(ϕ₁, ϕ₂)` and `d_j(ϕ₁(z), ϕ₂(z)) ≤ δ_j` on `U`, then
`d_j(ϕ₂(x), ϕ₂(y)) ≤ d_j(ϕ₁(x), ϕ₁(y)) + 2 * δ_j`.
-/
theorem perturbation_dist_forward {X I : Type} {bot : X}
    (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ1 ϕ2 : Operator X bot) (U : Set X) (_hU : U ⊆ commonDom2 ϕ1 ϕ2)
    (δ : I → ENNReal) (hδ : ∀ z ∈ U, ∀ j : I, d j (ϕ1.func z) (ϕ2.func z) ≤ δ j) :
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      d j (ϕ2.func x) (ϕ2.func y) ≤ d j (ϕ1.func x) (ϕ1.func y) + 2 * δ j := by
  intro x hx y hy j
  have h1 : d j (ϕ2.func x) (ϕ1.func x) ≤ δ j := by
    rw [(hd j).symm]
    exact hδ x hx j
  have h2 : d j (ϕ1.func y) (ϕ2.func y) ≤ δ j := hδ y hy j
  calc
    d j (ϕ2.func x) (ϕ2.func y)
        ≤ d j (ϕ2.func x) (ϕ1.func x) + d j (ϕ1.func x) (ϕ2.func y) :=
          (hd j).triangle _ _ _
    _ ≤ d j (ϕ2.func x) (ϕ1.func x) +
          (d j (ϕ1.func x) (ϕ1.func y) + d j (ϕ1.func y) (ϕ2.func y)) :=
          add_le_add_right ((hd j).triangle _ _ _) _
    _ = d j (ϕ1.func x) (ϕ1.func y) +
          (d j (ϕ2.func x) (ϕ1.func x) + d j (ϕ1.func y) (ϕ2.func y)) :=
          add_left_comm _ _ _
    _ ≤ d j (ϕ1.func x) (ϕ1.func y) + (δ j + δ j) :=
          add_le_add_right (add_le_add h1 h2) _
    _ = d j (ϕ1.func x) (ϕ1.func y) + 2 * δ j := by
          rw [two_mul]

/-- Explicit additive form `+ δ_j + δ_j` of `HC02-P08`. -/
theorem perturbation_dist_forward_add {X I : Type} {bot : X}
    (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ1 ϕ2 : Operator X bot) (U : Set X) (hU : U ⊆ commonDom2 ϕ1 ϕ2)
    (δ : I → ENNReal) (hδ : ∀ z ∈ U, ∀ j : I, d j (ϕ1.func z) (ϕ2.func z) ≤ δ j) :
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      d j (ϕ2.func x) (ϕ2.func y) ≤ d j (ϕ1.func x) (ϕ1.func y) + δ j + δ j := by
  intro x hx y hy j
  simpa [two_mul, add_assoc] using
    perturbation_dist_forward d hd ϕ1 ϕ2 U hU δ hδ x hx y hy j

/--
OET anchor: h-b959b42f25710105 (i), reverse direction (`HC02-P09`)
Under the same premises, swapping `ϕ₁` and `ϕ₂` yields
`d_j(ϕ₁(x), ϕ₁(y)) ≤ d_j(ϕ₂(x), ϕ₂(y)) + 2 * δ_j`.
-/
theorem perturbation_dist_backward {X I : Type} {bot : X}
    (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ1 ϕ2 : Operator X bot) (U : Set X) (hU : U ⊆ commonDom2 ϕ1 ϕ2)
    (δ : I → ENNReal) (hδ : ∀ z ∈ U, ∀ j : I, d j (ϕ1.func z) (ϕ2.func z) ≤ δ j) :
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      d j (ϕ1.func x) (ϕ1.func y) ≤ d j (ϕ2.func x) (ϕ2.func y) + 2 * δ j := by
  have hU' : U ⊆ commonDom2 ϕ2 ϕ1 := by
    simpa [commonDom2, Set.inter_comm] using hU
  have hδ' : ∀ z ∈ U, ∀ j : I, d j (ϕ2.func z) (ϕ1.func z) ≤ δ j := by
    intro z hz j
    rw [(hd j).symm]
    exact hδ z hz j
  exact perturbation_dist_forward d hd ϕ2 ϕ1 U hU' δ hδ'

/-- Explicit additive form `+ δ_j + δ_j` of `HC02-P09`. -/
theorem perturbation_dist_backward_add {X I : Type} {bot : X}
    (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ1 ϕ2 : Operator X bot) (U : Set X) (hU : U ⊆ commonDom2 ϕ1 ϕ2)
    (δ : I → ENNReal) (hδ : ∀ z ∈ U, ∀ j : I, d j (ϕ1.func z) (ϕ2.func z) ≤ δ j) :
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      d j (ϕ1.func x) (ϕ1.func y) ≤ d j (ϕ2.func x) (ϕ2.func y) + δ j + δ j := by
  intro x hx y hy j
  simpa [two_mul, add_assoc] using
    perturbation_dist_backward d hd ϕ1 ϕ2 U hU δ hδ x hx y hy j

/--
OET anchor: h-b959b42f25710105 (ii) (`HC02-P10`)
**Lip upper-bound bridge**: If in addition `L₁ ∈ ℒ(ϕ₁)|_U`, then
`d_j(ϕ₂(x), ϕ₂(y)) ≤ ∑ i, L₁_{i → j} * d_i(x, y) + 2 * δ_j`.
-/
theorem perturbation_lip_bridge {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ1 ϕ2 : Operator X bot) (U : Set X) (hU : U ⊆ commonDom2 ϕ1 ϕ2)
    (δ : I → ENNReal) (hδ : ∀ z ∈ U, ∀ j : I, d j (ϕ1.func z) (ϕ2.func z) ≤ δ j)
    {L1 : GaugeMatrix I} (hL1 : L1 ∈ RestrictedLipSet d ϕ1 U) :
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      d j (ϕ2.func x) (ϕ2.func y) ≤ (∑ i : I, L1 i j * d i x y) + 2 * δ j := by
  intro x hx y hy j
  calc
    d j (ϕ2.func x) (ϕ2.func y)
        ≤ d j (ϕ1.func x) (ϕ1.func y) + 2 * δ j :=
          perturbation_dist_forward d hd ϕ1 ϕ2 U hU δ hδ x hx y hy j
    _ ≤ (∑ i : I, L1 i j * d i x y) + 2 * δ j :=
          add_le_add_left (hL1.2 x hx y hy j) _

/-- Swapped Lip upper-bound bridge (line 178 remark): transferring `L₂ ∈ ℒ(ϕ₂)|_U` to `ϕ₁`. -/
theorem perturbation_lip_bridge_swap {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ1 ϕ2 : Operator X bot) (U : Set X) (hU : U ⊆ commonDom2 ϕ1 ϕ2)
    (δ : I → ENNReal) (hδ : ∀ z ∈ U, ∀ j : I, d j (ϕ1.func z) (ϕ2.func z) ≤ δ j)
    {L2 : GaugeMatrix I} (hL2 : L2 ∈ RestrictedLipSet d ϕ2 U) :
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      d j (ϕ1.func x) (ϕ1.func y) ≤ (∑ i : I, L2 i j * d i x y) + 2 * δ j := by
  intro x hx y hy j
  calc
    d j (ϕ1.func x) (ϕ1.func y)
        ≤ d j (ϕ2.func x) (ϕ2.func y) + 2 * δ j :=
          perturbation_dist_backward d hd ϕ1 ϕ2 U hU δ hδ x hx y hy j
    _ ≤ (∑ i : I, L2 i j * d i x y) + 2 * δ j :=
          add_le_add_left (hL2.2 x hx y hy j) _

/--
OET anchor: h-b959b42f25710105 (iii) (`HC02-P11`)
**co-Lip lower-bound bridge**: If in addition `K₁ ∈ 𝒦(ϕ₁)|_U`, then
`∑ i, K₁_{i → j} * d_i(x, y) ≤ d_j(ϕ₂(x), ϕ₂(y)) + 2 * δ_j`.
-/
theorem perturbation_coLip_bridge {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ1 ϕ2 : Operator X bot) (U : Set X) (hU : U ⊆ commonDom2 ϕ1 ϕ2)
    (δ : I → ENNReal) (hδ : ∀ z ∈ U, ∀ j : I, d j (ϕ1.func z) (ϕ2.func z) ≤ δ j)
    {K1 : GaugeMatrix I} (hK1 : K1 ∈ CoLipSet d ϕ1 U) :
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      (∑ i : I, K1 i j * d i x y) ≤ d j (ϕ2.func x) (ϕ2.func y) + 2 * δ j := by
  intro x hx y hy j
  calc
    ∑ i : I, K1 i j * d i x y
        ≤ d j (ϕ1.func x) (ϕ1.func y) := hK1.2.2 x hx y hy j
    _ ≤ d j (ϕ2.func x) (ϕ2.func y) + 2 * δ j :=
          perturbation_dist_backward d hd ϕ1 ϕ2 U hU δ hδ x hx y hy j

/-- Swapped co-Lip lower-bound bridge (line 178 remark): transferring `K₂ ∈ 𝒦(ϕ₂)|_U` to `ϕ₁`. -/
theorem perturbation_coLip_bridge_swap {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ1 ϕ2 : Operator X bot) (U : Set X) (hU : U ⊆ commonDom2 ϕ1 ϕ2)
    (δ : I → ENNReal) (hδ : ∀ z ∈ U, ∀ j : I, d j (ϕ1.func z) (ϕ2.func z) ≤ δ j)
    {K2 : GaugeMatrix I} (hK2 : K2 ∈ CoLipSet d ϕ2 U) :
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      (∑ i : I, K2 i j * d i x y) ≤ d j (ϕ1.func x) (ϕ1.func y) + 2 * δ j := by
  intro x hx y hy j
  calc
    ∑ i : I, K2 i j * d i x y
        ≤ d j (ϕ2.func x) (ϕ2.func y) := hK2.2.2 x hx y hy j
    _ ≤ d j (ϕ1.func x) (ϕ1.func y) + 2 * δ j :=
          perturbation_dist_forward d hd ϕ1 ϕ2 U hU δ hδ x hx y hy j

end OetCh02
