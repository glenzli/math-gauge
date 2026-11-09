/-
Formalization of the frozen historical Chapter 2 of The Operator Evolution Theory.
Source: Zhe Li / Glen Li / glenzli, https://glenzli.com/books/oet/.
License: CC-BY-4.0, https://creativecommons.org/licenses/by/4.0/.
This Lean adaptation was generated with AI assistance; it is not the author's code.
-/
import formal_oet.vol_01.ch_01_foundations.operator_space
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.ENNReal.Inv

open scoped BigOperators ENNReal Classical
open formal_oet.vol_01.ch_01_foundations

noncomputable section
namespace HCH02
set_option linter.unusedSectionVars false

abbrev Mat (I : Type) := I → I → ℝ≥0∞
abbrev Channel (I : Type) := I × I

variable {X I : Type} {bot : X} [Fintype I] [Nonempty I]

def compose (ψ φ : Operator X bot) : Operator X bot :=
  ⟨ψ.func ∘ φ.func, by simp [φ.preserves_bot, ψ.preserves_bot]⟩

def identity : Operator X bot := ⟨id, rfl⟩

theorem dom_comp (ψ φ : Operator X bot) (x : X) :
    x ∈ dom (compose ψ φ) ↔ x ∈ dom φ ∧ φ.func x ∈ dom ψ := by
  change ψ.func (φ.func x) ≠ bot ↔ φ.func x ≠ bot ∧ ψ.func (φ.func x) ≠ bot
  constructor
  · intro h
    refine ⟨?_, h⟩
    intro e
    exact h (by rw [e, ψ.preserves_bot])
  · exact And.right

def mmul (A B : Mat I) : Mat I := fun i j => ∑ k, A k j * B i k

noncomputable def unit : Mat I := fun i j => if i = j then 1 else 0

def display (A : Mat I) : Matrix I I ℝ≥0∞ := fun j i => A i j

theorem display_mmul (A B : Mat I) : display (mmul A B) = display A * display B := rfl

theorem display_unit : display (unit : Mat I) = (1 : Matrix I I ℝ≥0∞) := by
  classical
  ext j i
  simp [display, unit, Matrix.one_apply, eq_comm]

theorem unit_mmul (A : Mat I) : mmul unit A = A := by
  classical
  ext i j
  simp [mmul, unit]

theorem mmul_unit (A : Mat I) : mmul A unit = A := by
  classical
  ext i j
  simp [mmul, unit]

def action (M : Mat I) (v : I → ℝ≥0∞) (j : I) : ℝ≥0∞ := ∑ i, M i j * v i

theorem action_mmul (A B : Mat I) (v : I → ℝ≥0∞) (j : I) :
    action (mmul A B) v j = action A (action B v) j := by
  simp only [action, mmul, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem action_unit (v : I → ℝ≥0∞) (j : I) : action unit v j = v j := by
  classical
  simp [action, unit]

def LipOn (d : I → X → X → ℝ≥0∞) (φ : Operator X bot) (U : Set X) : Set (Mat I) :=
  {M | U ⊆ dom φ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j,
    d j (φ.func x) (φ.func y) ≤ action M (fun i => d i x y) j}

def Lip (d : I → X → X → ℝ≥0∞) (φ : Operator X bot) : Set (Mat I) :=
  LipOn d φ (dom φ)

def CoLipOn (d : I → X → X → ℝ≥0∞) (φ : Operator X bot) (U : Set X) : Set (Mat I) :=
  {M | U.Nonempty ∧ U ⊆ dom φ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j,
    action M (fun i => d i x y) j ≤ d j (φ.func x) (φ.func y)}

variable {d : I → X → X → ℝ≥0∞} {φ ψ : Operator X bot}
  {U V : Set X} {L K : Mat I}

theorem lip_restrict (h : L ∈ LipOn d φ V) (hUV : U ⊆ V) : L ∈ LipOn d φ U :=
  ⟨hUV.trans h.1, fun x hx y hy j => h.2 x (hUV hx) y (hUV hy) j⟩

theorem lip_global_restrict (hU : U ⊆ dom φ) : Lip d φ ⊆ LipOn d φ U :=
  fun _ h => lip_restrict h hU

noncomputable def entryInf (d : I → X → X → ℝ≥0∞) (φ : Operator X bot)
    (U : Set X) (i j : I) : ℝ≥0∞ := sInf ((fun M : Mat I => M i j) '' LipOn d φ U)

theorem entryInf_mono (hUV : U ⊆ V) (i j : I) :
    entryInf d φ U i j ≤ entryInf d φ V i j := by
  apply sInf_le_sInf
  rintro _ ⟨M, hM, rfl⟩
  exact ⟨M, lip_restrict hM hUV, rfl⟩

theorem lip_singleton [Subsingleton I] (i : I) (h : L ∈ LipOn d φ U)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    d i (φ.func x) (φ.func y) ≤ L i i * d i x y := by
  have he : action L (fun k => d k x y) i = L i i * d i x y := by
    apply Finset.sum_eq_single i
    · intro k _ hk
      exact (hk (Subsingleton.elim k i)).elim
    · simp
  simpa only [he] using h.2 x hx y hy i

theorem lip_comp (hU : U ⊆ dom (compose ψ φ))
    {A B : Mat I} (hB : B ∈ LipOn d φ U)
    (hA : A ∈ LipOn d ψ (φ.func '' U)) :
    mmul A B ∈ LipOn d (compose ψ φ) U := by
  refine ⟨hU, ?_⟩
  intro x hx y hy j
  calc
    d j (ψ.func (φ.func x)) (ψ.func (φ.func y))
        ≤ action A (fun k => d k (φ.func x) (φ.func y)) j :=
      hA.2 _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ j
    _ ≤ action A (fun k => action B (fun i => d i x y) k) j := by
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_left' (hB.2 x hx y hy k) _
    _ = action (mmul A B) (fun i => d i x y) j := (action_mmul A B _ j).symm

theorem colip_comp (hU : U ⊆ dom (compose ψ φ))
    {A B : Mat I} (hB : B ∈ CoLipOn d φ U)
    (hA : A ∈ CoLipOn d ψ (φ.func '' U)) :
    mmul A B ∈ CoLipOn d (compose ψ φ) U := by
  refine ⟨hB.1, hU, ?_⟩
  intro x hx y hy j
  rw [action_mmul]
  exact (Finset.sum_le_sum (fun k _ => mul_le_mul_left' (hB.2.2 x hx y hy k) _)).trans
    (hA.2.2 _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ j)

theorem colip_term (hK : K ∈ CoLipOn d φ U) {x y : X}
    (hx : x ∈ U) (hy : y ∈ U) (i j : I) :
    K i j * d i x y ≤ d j (φ.func x) (φ.func y) :=
  (Finset.single_le_sum (fun k _ => zero_le (K k j * d k x y)) (Finset.mem_univ i)).trans
    (hK.2.2 x hx y hy j)

theorem colip_zero_output (hK : K ∈ CoLipOn d φ (dom φ)) {x y : X}
    (hx : x ∈ dom φ) (hy : y ∈ dom φ) (i j : I)
    (hz : d j (φ.func x) (φ.func y) = 0) (hp : 0 < d i x y) : K i j = 0 := by
  have h := colip_term hK hx hy i j
  rw [hz] at h
  exact (mul_eq_zero.mp (le_antisymm h (zero_le _))).resolve_right (ne_of_gt hp)

theorem perturb_forward (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    {δ : I → ℝ≥0∞} (hU : U ⊆ dom φ ∩ dom ψ)
    (hδ : ∀ z ∈ U, ∀ j, d j (φ.func z) (ψ.func z) ≤ δ j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (ψ.func x) (ψ.func y) ≤ d j (φ.func x) (φ.func y) + δ j + δ j := by
  have hleft : d j (ψ.func x) (φ.func x) ≤ δ j := by
    rw [(hd j).symm]
    exact hδ x hx j
  calc
    d j (ψ.func x) (ψ.func y)
        ≤ d j (ψ.func x) (φ.func x) +
          (d j (φ.func x) (φ.func y) + d j (φ.func y) (ψ.func y)) :=
      ((hd j).triangle _ _ _).trans (add_le_add le_rfl ((hd j).triangle _ _ _))
    _ ≤ δ j + (d j (φ.func x) (φ.func y) + δ j) :=
      add_le_add hleft (add_le_add le_rfl (hδ y hy j))
    _ = _ := by simp only [add_assoc, add_left_comm (δ j)]

theorem perturb_reverse (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    {δ : I → ℝ≥0∞} (hU : U ⊆ dom φ ∩ dom ψ)
    (hδ : ∀ z ∈ U, ∀ j, d j (φ.func z) (ψ.func z) ≤ δ j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (φ.func x) (φ.func y) ≤ d j (ψ.func x) (ψ.func y) + δ j + δ j := by
  apply perturb_forward hd (fun _ hz => ⟨(hU hz).2, (hU hz).1⟩) _ hx hy j
  intro z hz k
  rw [(hd k).symm]
  exact hδ z hz k

theorem perturb_lip (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    {δ : I → ℝ≥0∞} (hU : U ⊆ dom φ ∩ dom ψ)
    (hδ : ∀ z ∈ U, ∀ j, d j (φ.func z) (ψ.func z) ≤ δ j)
    (hL : L ∈ LipOn d φ U) {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (ψ.func x) (ψ.func y) ≤ action L (fun i => d i x y) j + 2 * δ j := by
  rw [two_mul, ← add_assoc]
  exact (perturb_forward hd hU hδ hx hy j).trans
    (add_le_add (add_le_add (hL.2 x hx y hy j) le_rfl) le_rfl)

theorem perturb_colip (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    {δ : I → ℝ≥0∞} (hU : U ⊆ dom φ ∩ dom ψ)
    (hδ : ∀ z ∈ U, ∀ j, d j (φ.func z) (ψ.func z) ≤ δ j)
    (hK : K ∈ CoLipOn d φ U) {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    action K (fun i => d i x y) j ≤ d j (ψ.func x) (ψ.func y) + 2 * δ j := by
  simpa [two_mul, add_assoc] using
    (hK.2.2 x hx y hy j).trans (perturb_reverse hd hU hδ hx hy j)

def Row (L : Mat I) (i j : I) : Prop := ∀ k, k ≠ i → L k j = 0
def Col (L : Mat I) (i j : I) : Prop := ∀ k, k ≠ j → L i k = 0
def Diagonal (L : Mat I) : Prop := ∀ i j, i ≠ j → L i j = 0
def RowDecoupled (d : I → X → X → ℝ≥0∞) (φ : Operator X bot) (U : Set X) (j : I) : Prop :=
  ∃ L ∈ LipOn d φ U, ∃ i, Row L i j
def ColDecoupled (d : I → X → X → ℝ≥0∞) (φ : Operator X bot) (U : Set X) (i : I) : Prop :=
  ∃ L ∈ LipOn d φ U, ∃ j, Col L i j

theorem zero_term {i j : I} (h : L i j = 0) (v : I → ℝ≥0∞) : L i j * v i = 0 := by
  rw [h, zero_mul]

theorem erase_zero_term {i j : I} (h : L i j = 0) (v : I → ℝ≥0∞) :
    action L v j = ∑ k ∈ Finset.univ.erase i, L k j * v k := by
  classical
  have he := Finset.sum_erase_add Finset.univ (fun k => L k j * v k) (Finset.mem_univ i)
  simpa [h, action] using he.symm

theorem row_action {i j : I} (h : Row L i j) (v : I → ℝ≥0∞) :
    action L v j = L i j * v i := by
  classical
  apply Finset.sum_eq_single i
  · intro k _ hk
    rw [h k hk, zero_mul]
  · simp

theorem row_bound (hL : L ∈ LipOn d φ U) {i j : I} (h : Row L i j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    d j (φ.func x) (φ.func y) ≤ L i j * d i x y := by
  simpa [row_action h] using hL.2 x hx y hy j

theorem col_contribution {i j : I} (h : Col L i j) (v : I → ℝ≥0∞)
    (k : I) (hk : k ≠ j) : L i k * v i = 0 := zero_term (h k hk) v

theorem diagonal_bound (hL : L ∈ LipOn d φ U) (h : Diagonal L)
    (j : I) {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    d j (φ.func x) (φ.func y) ≤ L j j * d j x y :=
  row_bound hL (fun k hk => h k j hk) hx hy

theorem two_sided (hL : L ∈ LipOn d φ U) (hK : K ∈ CoLipOn d φ U)
    (j : I) (h : Row L j j) {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    K j j * d j x y ≤ d j (φ.func x) (φ.func y) ∧
      d j (φ.func x) (φ.func y) ≤ L j j * d j x y :=
  ⟨colip_term hK hx hy j j, row_bound hL h hx hy⟩

theorem all_two_sided (hL : L ∈ LipOn d φ U) (hK : K ∈ CoLipOn d φ U)
    (h : ∀ j, Row L j j) : ∀ j, ∀ x ∈ U, ∀ y ∈ U,
    K j j * d j x y ≤ d j (φ.func x) (φ.func y) ∧
      d j (φ.func x) (φ.func y) ≤ L j j * d j x y :=
  fun j _ hx _ hy => two_sided hL hK j (h j) hx hy

theorem finite_two_sided (hL : L ∈ LipOn d φ U) (hK : K ∈ CoLipOn d φ U)
    (h : ∀ j, Row L j j) (hfin : ∀ j, L j j < ⊤ ∧ K j j < ⊤) :
    ∀ j, L j j < ⊤ ∧ K j j < ⊤ ∧ ∀ x ∈ U, ∀ y ∈ U,
      K j j * d j x y ≤ d j (φ.func x) (φ.func y) ∧
        d j (φ.func x) (φ.func y) ≤ L j j * d j x y :=
  fun j => ⟨(hfin j).1, (hfin j).2, all_two_sided hL hK h j⟩

theorem positive_channel (hK : K ∈ CoLipOn d φ U) {i j : I} (h : 0 < K i j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (hp : 0 < d i x y) :
    0 < d j (φ.func x) (φ.func y) :=
  (ENNReal.mul_pos h.ne' hp.ne').trans_le (colip_term hK hx hy i j)

theorem reflect_zero (hK : K ∈ CoLipOn d φ U) (h : ∀ j, 0 < K j j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    (hz : GaugeZeroRelated d (φ.func x) (φ.func y)) : GaugeZeroRelated d x y := by
  intro j
  by_contra hn
  have hp := positive_channel hK (h j) hx hy (pos_iff_ne_zero.mpr hn)
  rw [hz j] at hp
  exact (lt_irrefl 0) hp

end HCH02
