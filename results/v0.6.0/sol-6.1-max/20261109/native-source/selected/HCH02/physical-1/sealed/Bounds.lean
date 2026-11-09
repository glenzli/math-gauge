import formal_oet.vol_01.ch_01_foundations.operator_space
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ENNReal.Inv

/-
Historical OET chapter 02, frozen snapshot 2d2f76c8392daf62.
Source: Zhe Li / Glen Li / glenzli, The Operator Evolution Theory,
https://glenzli.com/books/oet/, https://orcid.org/0009-0006-6536-3453.
Source repository: https://gitlab.com/glenzli/oet-public.
CC BY 4.0: https://creativecommons.org/licenses/by/4.0/.
Changes: Lean formalization of the supplied historical text.
The algebraic lemmas work for arbitrary ENNReal-valued families; metric
axioms are required explicitly where they are used.
-/

open formal_oet.vol_01.ch_01_foundations
open scoped BigOperators Classical ENNReal
noncomputable section
namespace HCH02

abbrev Mat (I : Type) := I → I → ℝ≥0∞
abbrev Channel (I : Type) := I × I

variable {X I : Type} {bot : X} [Fintype I]

def display (M : Mat I) : Matrix I I ℝ≥0∞ := fun j i => M i j
def undisplay (M : Matrix I I ℝ≥0∞) : Mat I := fun i j => M j i

theorem undisplay_display (M : Mat I) : undisplay (display M) = M := rfl
theorem display_undisplay (M : Matrix I I ℝ≥0∞) : display (undisplay M) = M := rfl

def mmul (B A : Mat I) : Mat I := fun i j => ∑ k, B k j * A i k
def unit : Mat I := fun i j => if i = j then 1 else 0

theorem display_mmul (B A : Mat I) :
    display (mmul B A) = display B * display A := by
  rfl

theorem display_unit : display (unit : Mat I) = 1 := by
  ext j i
  simp [display, unit, Matrix.one_apply, eq_comm]

theorem mmul_unit_left (A : Mat I) : mmul unit A = A := by
  ext i j
  simp [mmul, unit]

theorem mmul_unit_right (A : Mat I) : mmul A unit = A := by
  ext i j
  simp [mmul, unit]

theorem mmul_assoc (C B A : Mat I) : mmul C (mmul B A) = mmul (mmul C B) A := by
  have h : display (mmul C (mmul B A)) = display (mmul (mmul C B) A) := by
    simp only [display_mmul, Matrix.mul_assoc]
  exact funext fun i => funext fun j => congrFun (congrFun h j) i

def ident : Operator X bot := ⟨id, rfl⟩
def comp (q p : Operator X bot) : Operator X bot :=
  ⟨q.func ∘ p.func, by simp [p.preserves_bot, q.preserves_bot]⟩

theorem dom_comp (q p : Operator X bot) :
    dom (comp q p) = dom p ∩ p.func ⁻¹' dom q := by
  ext x
  change q.func (p.func x) ≠ bot ↔ p.func x ≠ bot ∧ q.func (p.func x) ≠ bot
  constructor
  · intro h
    refine ⟨?_, h⟩
    intro hx
    exact h (by rw [hx, q.preserves_bot])
  · exact And.right

def Lip (d : I → X → X → ℝ≥0∞) (p : Operator X bot) (U : Set X) : Set (Mat I) :=
  {M | U ⊆ dom p ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j,
    d j (p.func x) (p.func y) ≤ ∑ i, M i j * d i x y}

def GlobalLip (d : I → X → X → ℝ≥0∞) (p : Operator X bot) : Set (Mat I) :=
  Lip d p (dom p)

def CoLip (d : I → X → X → ℝ≥0∞) (p : Operator X bot) (U : Set X) : Set (Mat I) :=
  {M | U.Nonempty ∧ U ⊆ dom p ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j,
    (∑ i, M i j * d i x y) ≤ d j (p.func x) (p.func y)}

variable {d : I → X → X → ℝ≥0∞} {p q : Operator X bot}
variable {U V : Set X} {L K : Mat I} {i j : I} {x y : X}

theorem lip_singleton (hI : ∀ k : I, k = i) (hL : L ∈ Lip d p U)
    (hx : x ∈ U) (hy : y ∈ U) :
    d i (p.func x) (p.func y) ≤ L i i * d i x y := by
  have hs : (∑ k, L k i * d k x y) = L i i * d i x y := by
    apply Finset.sum_eq_single i
    · intro k _ hk
      exact (hk (hI k)).elim
    · simp
  simpa only [hs] using hL.2 x hx y hy i

theorem lip_restrict (hUV : U ⊆ V) : Lip d p V ⊆ Lip d p U := by
  intro M hM
  exact ⟨hUV.trans hM.1, fun x hx y hy j => hM.2 x (hUV hx) y (hUV hy) j⟩

theorem global_lip_restrict (hU : U ⊆ dom p) : GlobalLip d p ⊆ Lip d p U :=
  lip_restrict hU

def entryInf (d : I → X → X → ℝ≥0∞) (p : Operator X bot)
    (U : Set X) (i j : I) : ℝ≥0∞ := sInf ((fun M : Mat I => M i j) '' Lip d p U)

theorem entryInf_mono (hUV : U ⊆ V) : entryInf d p U i j ≤ entryInf d p V i j := by
  apply sInf_le_sInf
  rintro _ ⟨M, hM, rfl⟩
  exact ⟨M, lip_restrict hUV hM, rfl⟩

theorem weighted_mmul (B A : Mat I) (v : I → ℝ≥0∞) (j : I) :
    (∑ k, B k j * ∑ i, A i k * v i) = ∑ i, mmul B A i j * v i := by
  simp only [mmul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [mul_assoc]

theorem lip_comp (hU : U ⊆ dom (comp q p))
    (hA : L ∈ Lip d p U) (hB : K ∈ Lip d q (p.func '' U)) :
    mmul K L ∈ Lip d (comp q p) U := by
  refine ⟨hU, ?_⟩
  intro x hx y hy j
  calc
    d j (q.func (p.func x)) (q.func (p.func y))
        ≤ ∑ k, K k j * d k (p.func x) (p.func y) :=
      hB.2 _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ j
    _ ≤ ∑ k, K k j * ∑ i, L i k * d i x y := by
      exact Finset.sum_le_sum fun k _ => mul_le_mul_right (hA.2 x hx y hy k) _
    _ = ∑ i, mmul K L i j * d i x y := weighted_mmul K L _ j

theorem colip_comp (hU : U ⊆ dom (comp q p))
    (hA : L ∈ CoLip d p U) (hB : K ∈ CoLip d q (p.func '' U)) :
    mmul K L ∈ CoLip d (comp q p) U := by
  refine ⟨hA.1, hU, ?_⟩
  intro x hx y hy j
  calc
    (∑ i, mmul K L i j * d i x y) = ∑ k, K k j * ∑ i, L i k * d i x y :=
      (weighted_mmul K L _ j).symm
    _ ≤ ∑ k, K k j * d k (p.func x) (p.func y) := by
      exact Finset.sum_le_sum fun k _ => mul_le_mul_right (hA.2.2 x hx y hy k) _
    _ ≤ d j (q.func (p.func x)) (q.func (p.func y)) :=
      hB.2.2 _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ j

theorem colip_term (hK : K ∈ CoLip d p U) (hx : x ∈ U) (hy : y ∈ U) :
    K i j * d i x y ≤ d j (p.func x) (p.func y) :=
  (Finset.single_le_sum (fun k _ => zero_le (K k j * d k x y))
    (Finset.mem_univ i)).trans (hK.2.2 x hx y hy j)

theorem colip_zero_entry (hK : K ∈ CoLip d p (dom p))
    (hx : x ∈ dom p) (hy : y ∈ dom p)
    (hout : d j (p.func x) (p.func y) = 0) (hin : 0 < d i x y) : K i j = 0 := by
  have hz : K i j * d i x y = 0 := le_antisymm (hout ▸ colip_term hK hx hy) (zero_le _)
  exact (mul_eq_zero.mp hz).resolve_right (ne_of_gt hin)

theorem perturb_forward (hd : ∀ k, ExtendedPseudoMetric X bot (d k))
    (hU : U ⊆ dom p ∩ dom q) (δ : I → ℝ≥0∞)
    (hδ : ∀ z ∈ U, ∀ k, d k (p.func z) (q.func z) ≤ δ k)
    (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (q.func x) (q.func y) ≤ d j (p.func x) (p.func y) + δ j + δ j := by
  have ha : d j (q.func x) (p.func x) ≤ δ j := by
    rw [(hd j).symm]
    exact hδ x hx j
  calc
    d j (q.func x) (q.func y)
        ≤ d j (q.func x) (p.func x) + d j (p.func x) (q.func y) := (hd j).triangle _ _ _
    _ ≤ δ j + (d j (p.func x) (p.func y) + δ j) :=
      add_le_add ha (((hd j).triangle (p.func x) (p.func y) (q.func y)).trans
        (add_le_add le_rfl (hδ y hy j)))
    _ = d j (p.func x) (p.func y) + δ j + δ j := by
      simp only [add_assoc, add_left_comm]

theorem perturb_reverse (hd : ∀ k, ExtendedPseudoMetric X bot (d k))
    (hU : U ⊆ dom p ∩ dom q) (δ : I → ℝ≥0∞)
    (hδ : ∀ z ∈ U, ∀ k, d k (p.func z) (q.func z) ≤ δ k)
    (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (p.func x) (p.func y) ≤ d j (q.func x) (q.func y) + δ j + δ j := by
  apply perturb_forward hd (fun z hz => ⟨(hU hz).2, (hU hz).1⟩) δ ?_ hx hy j
  intro z hz k
  rw [(hd k).symm]
  exact hδ z hz k

theorem perturb_lip (hd : ∀ k, ExtendedPseudoMetric X bot (d k))
    (hU : U ⊆ dom p ∩ dom q) (δ : I → ℝ≥0∞)
    (hδ : ∀ z ∈ U, ∀ k, d k (p.func z) (q.func z) ≤ δ k)
    (hL : L ∈ Lip d p U) (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (q.func x) (q.func y) ≤ (∑ i, L i j * d i x y) + 2 * δ j := by
  simpa only [two_mul, add_assoc] using
    (perturb_forward hd hU δ hδ hx hy j).trans
      (add_le_add (add_le_add (hL.2 x hx y hy j) le_rfl) le_rfl)

theorem perturb_colip (hd : ∀ k, ExtendedPseudoMetric X bot (d k))
    (hU : U ⊆ dom p ∩ dom q) (δ : I → ℝ≥0∞)
    (hδ : ∀ z ∈ U, ∀ k, d k (p.func z) (q.func z) ≤ δ k)
    (hK : K ∈ CoLip d p U) (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    (∑ i, K i j * d i x y) ≤ d j (q.func x) (q.func y) + 2 * δ j := by
  simpa only [two_mul, add_assoc] using
    (hK.2.2 x hx y hy j).trans (perturb_reverse hd hU δ hδ hx hy j)

def Row (M : Mat I) (i j : I) : Prop := ∀ k, k ≠ i → M k j = 0
def Col (M : Mat I) (i j : I) : Prop := ∀ k, k ≠ j → M i k = 0
def Diagonal (M : Mat I) : Prop := ∀ i j, i ≠ j → M i j = 0
def RowDecoupled (d : I → X → X → ℝ≥0∞) (p : Operator X bot) (U : Set X) (j : I) : Prop :=
  ∃ M ∈ Lip d p U, ∃ i, Row M i j
def ColDecoupled (d : I → X → X → ℝ≥0∞) (p : Operator X bot) (U : Set X) (i : I) : Prop :=
  ∃ M ∈ Lip d p U, ∃ j, Col M i j

theorem zero_term (h : L i j = 0) : L i j * d i x y = 0 := by rw [h, zero_mul]

theorem erase_zero_term (h : L i j = 0) :
    (∑ k, L k j * d k x y) = ∑ k ∈ Finset.univ.erase i, L k j * d k x y := by
  have hs := Finset.sum_erase_add Finset.univ (fun k => L k j * d k x y)
    (Finset.mem_univ i)
  simpa only [zero_term h, add_zero] using hs.symm

theorem row_sum (h : Row L i j) : (∑ k, L k j * d k x y) = L i j * d i x y := by
  apply Finset.sum_eq_single i
  · intro k _ hk
    rw [h k hk, zero_mul]
  · simp

theorem row_lip (hL : L ∈ Lip d p U) (h : Row L i j) (hx : x ∈ U) (hy : y ∈ U) :
    d j (p.func x) (p.func y) ≤ L i j * d i x y := by
  simpa only [row_sum h] using hL.2 x hx y hy j

theorem col_contribution (h : Col L i j) (k : I) (hk : k ≠ j) :
    L i k * d i x y = 0 := by rw [h k hk, zero_mul]

theorem diagonal_lip (hL : L ∈ Lip d p U) (h : Diagonal L)
    (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (p.func x) (p.func y) ≤ L j j * d j x y :=
  row_lip hL (fun k hk => h k j hk) hx hy

theorem scalar_two_sided (hL : L ∈ Lip d p U) (hK : K ∈ CoLip d p U)
    (h : Row L j j) (hx : x ∈ U) (hy : y ∈ U) :
    K j j * d j x y ≤ d j (p.func x) (p.func y) ∧
      d j (p.func x) (p.func y) ≤ L j j * d j x y :=
  ⟨colip_term hK hx hy, row_lip hL h hx hy⟩

theorem component_two_sided (hL : L ∈ Lip d p U) (hK : K ∈ CoLip d p U)
    (h : ∀ j, Row L j j) : ∀ j, ∀ x ∈ U, ∀ y ∈ U,
    K j j * d j x y ≤ d j (p.func x) (p.func y) ∧
      d j (p.func x) (p.func y) ≤ L j j * d j x y := by
  intro j x hx y hy
  exact scalar_two_sided hL hK (h j) hx hy

theorem finite_component_two_sided (hL : L ∈ Lip d p U) (hK : K ∈ CoLip d p U)
    (h : ∀ j, Row L j j) (hf : ∀ j, L j j < ⊤ ∧ K j j < ⊤) :
    ∀ j, L j j < ⊤ ∧ K j j < ⊤ ∧ ∀ x ∈ U, ∀ y ∈ U,
      K j j * d j x y ≤ d j (p.func x) (p.func y) ∧
        d j (p.func x) (p.func y) ≤ L j j * d j x y := by
  intro j
  exact ⟨(hf j).1, (hf j).2, component_two_sided hL hK h j⟩

theorem positive_channel (hK : K ∈ CoLip d p U) (h : 0 < K i j)
    (hx : x ∈ U) (hy : y ∈ U) (hin : 0 < d i x y) :
    0 < d j (p.func x) (p.func y) :=
  (ENNReal.mul_pos_iff.mpr ⟨h, hin⟩).trans_le (colip_term hK hx hy)

theorem reflect_zero (hK : K ∈ CoLip d p U) (h : ∀ j, 0 < K j j)
    (hx : x ∈ U) (hy : y ∈ U) (hout : GaugeZeroRelated d (p.func x) (p.func y)) :
    GaugeZeroRelated d x y := by
  intro j
  by_contra hn
  have hp := positive_channel hK (h j) hx hy (pos_iff_ne_zero.mpr hn)
  rw [hout j] at hp
  exact (lt_irrefl _ hp)

end HCH02
