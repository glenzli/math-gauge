以下项目使用预置的冻结前置模块与 mathlib。构建方式是将这些预置依赖的编译产物加入 `LEAN_PATH`，然后运行 `lake run check`；该命令不会下载依赖。

```lean filename=Main.lean
import formal_oet.vol_01.ch_01_foundations.operator_space

/-!
Formalization based on chapter 2 of Zhe Li (Glen Li / glenzli),
*The Operator Evolution Theory*, https://glenzli.com/books/oet/,
CC BY 4.0, https://creativecommons.org/licenses/by/4.0/.
This Lean formalization is an adaptation of the frozen historical text.
-/

open formal_oet.vol_01.ch_01_foundations
open scoped BigOperators Classical

namespace HCH02

noncomputable section

variable {X I : Type} {bot : X} [Fintype I] [Nonempty I]

/-- Input index first, output index second. -/
abbrev Coeff (I : Type) := I → I → ENNReal

abbrev Channel (I : Type) := I × I

def displayMatrix (M : Coeff I) : I → I → ENNReal := fun j i => M i j

def matMul (B A : Coeff I) : Coeff I := fun i j => ∑ k, B k j * A i k

def matId : Coeff I := fun i j => if i = j then 1 else 0

theorem displayMatrix_apply (M : Coeff I) (i j : I) :
    displayMatrix M j i = M i j := rfl

theorem matMul_apply (B A : Coeff I) (i j : I) :
    matMul B A i j = ∑ k, B k j * A i k := rfl

def opId : Operator X bot := ⟨id, rfl⟩

def opComp (g f : Operator X bot) : Operator X bot :=
  ⟨g.func ∘ f.func, by simp [f.preserves_bot, g.preserves_bot]⟩

theorem opComp_apply (g f : Operator X bot) (x : X) :
    (opComp g f).func x = g.func (f.func x) := rfl

def LipOn (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (L : Coeff I) : Prop :=
  U ⊆ dom f ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j,
    d j (f.func x) (f.func y) ≤ ∑ i, L i j * d i x y

def LipFamily (d : I → X → X → ENNReal) (f : Operator X bot) : Set (Coeff I) :=
  {L | LipOn d f (dom f) L}

def LipFamilyOn (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) : Set (Coeff I) := {L | LipOn d f U L}

def CoLipOn (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (K : Coeff I) : Prop :=
  U.Nonempty ∧ U ⊆ dom f ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j,
    (∑ i, K i j * d i x y) ≤ d j (f.func x) (f.func y)

def CoLipFamilyOn (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) : Set (Coeff I) := {K | CoLipOn d f U K}

def Row (L : Coeff I) (i j : I) : Prop := ∀ k, k ≠ i → L k j = 0

def Col (L : Coeff I) (i j : I) : Prop := ∀ k, k ≠ j → L i k = 0

def Diagonal (L : Coeff I) : Prop := ∀ i j, i ≠ j → L i j = 0

def RowDecoupled (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (j : I) : Prop := ∃ L, LipOn d f U L ∧ ∃ i, Row L i j

def ColDecoupled (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (i : I) : Prop := ∃ L, LipOn d f U L ∧ ∃ j, Col L i j

def ScalarFeasible (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (i j : I) : Set ENNReal :=
  {a | ∀ x ∈ U, ∀ y ∈ U, d j (f.func x) (f.func y) ≤ a * d i x y}

def channelInf (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (i j : I) : ENNReal := sInf (ScalarFeasible d f U i j)

/-- The legal scopes from the chapter, with their domain inclusion made explicit. -/
abbrev LegalDomain (f : Operator X bot) := {U : Set X // U ⊆ dom f}

def ScalarFeasibleLegal (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : LegalDomain f) (i j : I) : Set ENNReal := ScalarFeasible d f U.val i j

def channelInfLegal (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : LegalDomain f) (i j : I) : ENNReal := sInf (ScalarFeasibleLegal d f U i j)

theorem legal_scalar_correspondence (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : LegalDomain f) (i j : I) :
    ScalarFeasibleLegal d f U i j = ScalarFeasible d f U.val i j ∧
      channelInfLegal d f U i j = channelInf d f U.val i j := ⟨rfl, rfl⟩

def entryInf (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (i j : I) : ENNReal :=
  sInf {a | ∃ L ∈ LipFamilyOn d f U, L i j = a}

variable (d : I → X → X → ENNReal)

theorem lip_restrict {f : Operator X bot} {U V : Set X} {L : Coeff I}
    (hUV : U ⊆ V) (h : LipOn d f V L) : LipOn d f U L := by
  refine ⟨hUV.trans h.1, ?_⟩
  intro x hx y hy j
  exact h.2 x (hUV hx) y (hUV hy) j

theorem global_lip_restrict {f : Operator X bot} {U : Set X}
    (hU : U ⊆ dom f) : LipFamily d f ⊆ LipFamilyOn d f U := by
  intro L h
  exact lip_restrict d hU h

theorem lip_family_antitone {f : Operator X bot} {U V : Set X}
    (hUV : U ⊆ V) : LipFamilyOn d f V ⊆ LipFamilyOn d f U := by
  intro L h
  exact lip_restrict d hUV h

theorem entryInf_antitone {f : Operator X bot} {U V : Set X} {i j : I}
    (hUV : U ⊆ V) : entryInf d f U i j ≤ entryInf d f V i j := by
  apply sInf_le_sInf
  rintro a ⟨L, hL, rfl⟩
  exact ⟨L, lip_restrict d hUV hL, rfl⟩

theorem singleton_lip [Unique I] {f : Operator X bot} {U : Set X} {L : Coeff I}
    (h : LipOn d f U L) (x y : X) (hx : x ∈ U) (hy : y ∈ U) (i : I) :
    d i (f.func x) (f.func y) ≤ L i i * d i x y := by
  simpa [Unique.eq_default i] using h.2 x hx y hy i

theorem singleton_lip_of_eq {f : Operator X bot} {U : Set X} {L : Coeff I}
    (i : I) (hi : ∀ k : I, k = i) (h : LipOn d f U L)
    (x y : X) (hx : x ∈ U) (hy : y ∈ U) :
    d i (f.func x) (f.func y) ≤ L i i * d i x y := by
  have hsum : (∑ k, L k i * d k x y) = L i i * d i x y := by
    apply Finset.sum_eq_single i
    · intro k _ hki
      exact False.elim (hki (hi k))
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ i))
  simpa [hsum] using h.2 x hx y hy i

theorem sum_matMul (B A : Coeff I) (v : I → ENNReal) (j : I) :
    (∑ i, matMul B A i j * v i) = ∑ k, B k j * (∑ i, A i k * v i) := by
  simp only [matMul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  ac_rfl

theorem lip_comp {f g : Operator X bot} {U : Set X} {A B : Coeff I}
    (hdom : U ⊆ dom (opComp g f))
    (hf : LipOn d f U A) (hg : LipOn d g (f.func '' U) B) :
    LipOn d (opComp g f) U (matMul B A) := by
  refine ⟨hdom, ?_⟩
  intro x hx y hy j
  have hfx : f.func x ∈ f.func '' U := ⟨x, hx, rfl⟩
  have hfy : f.func y ∈ f.func '' U := ⟨y, hy, rfl⟩
  calc
    d j ((opComp g f).func x) ((opComp g f).func y)
        ≤ ∑ k, B k j * d k (f.func x) (f.func y) := hg.2 _ hfx _ hfy j
    _ ≤ ∑ k, B k j * (∑ i, A i k * d i x y) := by
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_left' (hf.2 x hx y hy k) _
    _ = ∑ i, matMul B A i j * d i x y := (sum_matMul B A (fun i => d i x y) j).symm

theorem colip_comp {f g : Operator X bot} {U : Set X} {A B : Coeff I}
    (hdom : U ⊆ dom (opComp g f))
    (hf : CoLipOn d f U A) (hg : CoLipOn d g (f.func '' U) B) :
    CoLipOn d (opComp g f) U (matMul B A) := by
  refine ⟨hf.1, hdom, ?_⟩
  intro x hx y hy j
  have hfx : f.func x ∈ f.func '' U := ⟨x, hx, rfl⟩
  have hfy : f.func y ∈ f.func '' U := ⟨y, hy, rfl⟩
  calc
    (∑ i, matMul B A i j * d i x y)
        = ∑ k, B k j * (∑ i, A i k * d i x y) := sum_matMul B A (fun i => d i x y) j
    _ ≤ ∑ k, B k j * d k (f.func x) (f.func y) := by
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_left' (hf.2.2 x hx y hy k) _
    _ ≤ d j ((opComp g f).func x) ((opComp g f).func y) := hg.2.2 _ hfx _ hfy j

theorem term_le_sum (K : Coeff I) (x y : X) (i j : I) :
    K i j * d i x y ≤ ∑ k, K k j * d k x y := by
  exact Finset.single_le_sum (fun k _ => zero_le (K k j * d k x y)) (Finset.mem_univ i)

theorem colip_zero_of_collapsed {f : Operator X bot} {U : Set X} {K : Coeff I}
    {i j : I} {x y : X} (hK : CoLipOn d f U K) (hx : x ∈ U) (hy : y ∈ U)
    (hout : d j (f.func x) (f.func y) = 0) (hin : 0 < d i x y) : K i j = 0 := by
  have hprod : K i j * d i x y = 0 := by
    apply le_antisymm _ (zero_le _)
    calc
      K i j * d i x y ≤ ∑ k, K k j * d k x y := term_le_sum d K x y i j
      _ ≤ d j (f.func x) (f.func y) := hK.2.2 x hx y hy j
      _ = 0 := hout
  rcases mul_eq_zero.mp hprod with h | h
  · exact h
  · exact False.elim ((ne_of_gt hin) h)

theorem colip_channel_pos {f : Operator X bot} {U : Set X} {K : Coeff I}
    {i j : I} {x y : X} (hK : CoLipOn d f U K) (hx : x ∈ U) (hy : y ∈ U)
    (hij : 0 < K i j) (hin : 0 < d i x y) :
    0 < d j (f.func x) (f.func y) := by
  exact lt_of_lt_of_le (ENNReal.mul_pos (ne_of_gt hij) (ne_of_gt hin))
    (le_trans (term_le_sum d K x y i j) (hK.2.2 x hx y hy j))

theorem colip_reflect_zero {f : Operator X bot} {U : Set X} {K : Coeff I}
    {x y : X} (hK : CoLipOn d f U K) (hx : x ∈ U) (hy : y ∈ U)
    (hdiag : ∀ j, 0 < K j j)
    (hout : GaugeZeroRelated d (f.func x) (f.func y)) : GaugeZeroRelated d x y := by
  intro j
  by_contra hne
  have hpos : 0 < d j x y := pos_iff_ne_zero.mpr hne
  have hp := colip_channel_pos d hK hx hy (hdiag j) hpos
  rw [hout j] at hp
  exact (lt_irrefl 0) hp

theorem row_sum (L : Coeff I) (v : I → ENNReal) (i j : I) (h : Row L i j) :
    (∑ k, L k j * v k) = L i j * v i := by
  classical
  apply Finset.sum_eq_single i
  · intro k _ hki
    rw [h k hki, zero_mul]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

theorem row_lip {f : Operator X bot} {U : Set X} {L : Coeff I} {i j : I}
    (hL : LipOn d f U L) (hrow : Row L i j) {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    d j (f.func x) (f.func y) ≤ L i j * d i x y := by
  simpa [row_sum L (fun k => d k x y) i j hrow] using hL.2 x hx y hy j

theorem zero_term (L : Coeff I) (i j : I) (x y : X) (h : L i j = 0) :
    L i j * d i x y = 0 := by simp [h]

theorem zero_term_erase (L : Coeff I) (i j : I) (x y : X) (h : L i j = 0) :
    (∑ k, L k j * d k x y) = ∑ k ∈ Finset.univ.erase i, L k j * d k x y := by
  classical
  symm
  exact Finset.sum_erase Finset.univ (zero_term d L i j x y h)

theorem col_contribution (L : Coeff I) (i j : I) (h : Col L i j)
    (k : I) (hkj : k ≠ j) (x y : X) : L i k * d i x y = 0 := by
  rw [h k hkj, zero_mul]

theorem diagonal_lip {f : Operator X bot} {U : Set X} {L : Coeff I}
    (hL : LipOn d f U L) (hdiag : Diagonal L) (j : I)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    d j (f.func x) (f.func y) ≤ L j j * d j x y := by
  apply row_lip d hL ?_ hx hy
  intro k hkj
  exact hdiag k j hkj

theorem two_sided {f : Operator X bot} {U : Set X} {L K : Coeff I} {j : I}
    (hL : LipOn d f U L) (hK : CoLipOn d f U K) (hrow : Row L j j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    K j j * d j x y ≤ d j (f.func x) (f.func y) ∧
      d j (f.func x) (f.func y) ≤ L j j * d j x y := by
  exact ⟨(term_le_sum d K x y j j).trans (hK.2.2 x hx y hy j), row_lip d hL hrow hx hy⟩

theorem diagonal_two_sided {f : Operator X bot} {U : Set X} {L K : Coeff I}
    (hL : LipOn d f U L) (hK : CoLipOn d f U K) (hdiag : Diagonal L) :
    ∀ j, ∀ x ∈ U, ∀ y ∈ U,
      K j j * d j x y ≤ d j (f.func x) (f.func y) ∧
      d j (f.func x) (f.func y) ≤ L j j * d j x y := by
  intro j x hx y hy
  apply two_sided d hL hK ?_ hx hy
  intro k hk
  exact hdiag k j hk

theorem finite_diagonal_two_sided {f : Operator X bot} {U : Set X} {L K : Coeff I}
    (hL : LipOn d f U L) (hK : CoLipOn d f U K) (hdiag : Diagonal L)
    (hfin : ∀ j, L j j < ⊤ ∧ K j j < ⊤) :
    ∀ j, L j j < ⊤ ∧ K j j < ⊤ ∧
      ∀ x ∈ U, ∀ y ∈ U,
        K j j * d j x y ≤ d j (f.func x) (f.func y) ∧
        d j (f.func x) (f.func y) ≤ L j j * d j x y := by
  intro j
  exact ⟨(hfin j).1, (hfin j).2, diagonal_two_sided d hL hK hdiag j⟩

theorem matId_sum (v : I → ENNReal) (j : I) :
    (∑ i, matId i j * v i) = v j := by
  classical
  simp [matId, ite_mul, eq_comm]

theorem matMul_one_left (A : Coeff I) : matMul matId A = A := by
  classical
  funext i j
  simp [matMul, matId, ite_mul, eq_comm]

theorem matMul_one_right (A : Coeff I) : matMul A matId = A := by
  classical
  funext i j
  simp [matMul, matId, mul_ite]

theorem opId_lip {U : Set X} (hU : U ⊆ dom (opId : Operator X bot)) :
    LipOn d (opId : Operator X bot) U matId := by
  refine ⟨hU, ?_⟩
  intro x hx y hy j
  simpa [opId, matId_sum]

theorem opId_colip {U : Set X} (hne : U.Nonempty)
    (hU : U ⊆ dom (opId : Operator X bot)) :
    CoLipOn d (opId : Operator X bot) U matId := by
  refine ⟨hne, hU, ?_⟩
  intro x hx y hy j
  simpa [opId, matId_sum]

theorem perturb_forward {f g : Operator X bot} {U : Set X} (δ : I → ENNReal)
    (symm : ∀ j x y, d j x y = d j y x)
    (tri : ∀ j x y z, d j x z ≤ d j x y + d j y z)
    (hδ : ∀ z ∈ U, ∀ j, d j (f.func z) (g.func z) ≤ δ j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (g.func x) (g.func y) ≤ d j (f.func x) (f.func y) + δ j + δ j := by
  calc
    d j (g.func x) (g.func y)
        ≤ d j (g.func x) (f.func x) + d j (f.func x) (g.func y) := tri _ _ _ _
    _ ≤ d j (g.func x) (f.func x) +
          (d j (f.func x) (f.func y) + d j (f.func y) (g.func y)) :=
        add_le_add_right (tri _ _ _ _) _
    _ ≤ δ j + (d j (f.func x) (f.func y) + δ j) := by
      apply add_le_add
      · rw [symm j (g.func x) (f.func x)]
        exact hδ x hx j
      · exact add_le_add_right (hδ y hy j) _
    _ = d j (f.func x) (f.func y) + δ j + δ j := by
      simp [add_assoc, add_comm, add_left_comm]

theorem perturb_backward {f g : Operator X bot} {U : Set X} (δ : I → ENNReal)
    (symm : ∀ j x y, d j x y = d j y x)
    (tri : ∀ j x y z, d j x z ≤ d j x y + d j y z)
    (hδ : ∀ z ∈ U, ∀ j, d j (f.func z) (g.func z) ≤ δ j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (f.func x) (f.func y) ≤ d j (g.func x) (g.func y) + δ j + δ j := by
  apply perturb_forward d δ symm tri ?_ hx hy j
  intro z hz k
  rw [symm k (g.func z) (f.func z)]
  exact hδ z hz k

theorem perturb_lip {f g : Operator X bot} {U : Set X} {L : Coeff I}
    (δ : I → ENNReal) (symm : ∀ j x y, d j x y = d j y x)
    (tri : ∀ j x y z, d j x z ≤ d j x y + d j y z)
    (hδ : ∀ z ∈ U, ∀ j, d j (f.func z) (g.func z) ≤ δ j)
    (hL : LipOn d f U L) {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (g.func x) (g.func y) ≤ (∑ i, L i j * d i x y) + δ j + δ j := by
  exact (perturb_forward d δ symm tri hδ hx hy j).trans
    (add_le_add_left (add_le_add_left (hL.2 x hx y hy j) _) _)

theorem perturb_colip {f g : Operator X bot} {U : Set X} {K : Coeff I}
    (δ : I → ENNReal) (symm : ∀ j x y, d j x y = d j y x)
    (tri : ∀ j x y z, d j x z ≤ d j x y + d j y z)
    (hδ : ∀ z ∈ U, ∀ j, d j (f.func z) (g.func z) ≤ δ j)
    (hK : CoLipOn d f U K) {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    (∑ i, K i j * d i x y) ≤ d j (g.func x) (g.func y) + δ j + δ j := by
  exact (hK.2.2 x hx y hy j).trans (perturb_backward d δ symm tri hδ hx hy j)

theorem scalar_feasible_upward {f : Operator X bot} {U : Set X} {i j : I}
    {a b : ENNReal} (ha : a ∈ ScalarFeasible d f U i j) (hab : a ≤ b) :
    b ∈ ScalarFeasible d f U i j := by
  intro x hx y hy
  exact (ha x hx y hy).trans (mul_le_mul_right' hab _)

theorem scalar_above_inf {f : Operator X bot} {U : Set X} {i j : I}
    {b : ENNReal} (hb : channelInf d f U i j < b) :
    b ∈ ScalarFeasible d f U i j := by
  obtain ⟨a, ha, hab⟩ := sInf_lt_iff.mp hb
  exact scalar_feasible_upward d ha (le_of_lt hab)

theorem scalar_zero_inf_positive {f : Operator X bot} {U : Set X} {i j : I}
    (hinf : channelInf d f U i j = 0) {b : ENNReal} (hb : 0 < b) :
    b ∈ ScalarFeasible d f U i j := by
  apply scalar_above_inf d
  simpa [hinf] using hb

theorem scalar_inf_lt_top_iff {f : Operator X bot} {U : Set X} {i j : I} :
    channelInf d f U i j < ⊤ ↔
      ∃ b < ⊤, b ∈ ScalarFeasible d f U i j := by
  change sInf (ScalarFeasible d f U i j) < ⊤ ↔ _
  constructor
  · intro h
    obtain ⟨b, hb, htop⟩ := sInf_lt_iff.mp h
    exact ⟨b, htop, hb⟩
  · rintro ⟨b, hb, hmem⟩
    exact lt_of_le_of_lt (sInf_le hmem) hb

theorem scalar_infeasible_of_zero {f : Operator X bot} {U : Set X} {i j : I}
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (hin : d i x y = 0)
    (hout : 0 < d j (f.func x) (f.func y)) :
    ScalarFeasible d f U i j = ∅ ∧ channelInf d f U i j = ⊤ := by
  have he : ScalarFeasible d f U i j = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro a ha
    have h := ha x hx y hy
    rw [hin, mul_zero] at h
    exact (not_le_of_gt hout) h
  exact ⟨he, by simp [channelInf, he]⟩

theorem channelInf_of_empty {f : Operator X bot} {U : Set X} {i j : I}
    (h : ScalarFeasible d f U i j = ∅) : channelInf d f U i j = ⊤ := by
  simp [channelInf, h]

theorem scalar_inf_attained {f : Operator X bot} {U : Set X} {i j : I}
    (hpos : 0 < channelInf d f U i j) (hfin : channelInf d f U i j < ⊤) :
    channelInf d f U i j ∈ ScalarFeasible d f U i j := by
  let S := ScalarFeasible d f U i j
  obtain ⟨b, hb, _⟩ := sInf_lt_iff.mp hfin
  letI : Nonempty {b // b ∈ S} := ⟨⟨b, hb⟩⟩
  have hinf : channelInf d f U i j = ⨅ b : {b // b ∈ S}, (b : ENNReal) := by
    apply le_antisymm
    · apply le_iInf
      intro b
      exact sInf_le b.property
    · apply le_sInf
      intro b hb
      exact iInf_le (fun b : {b // b ∈ S} => (b : ENNReal)) ⟨b, hb⟩
  intro x hx y hy
  calc
    d j (f.func x) (f.func y) ≤ ⨅ b : {b // b ∈ S}, (b : ENNReal) * d i x y := by
      apply le_iInf
      intro b
      exact b.property x hx y hy
    _ = (⨅ b : {b // b ∈ S}, (b : ENNReal)) * d i x y := by
      symm
      apply ENNReal.iInf_mul
      intro _ hzero
      exact False.elim ((ne_of_gt hpos) (hinf.trans hzero))
    _ = channelInf d f U i j * d i x y := by rw [hinf]

/-- Both lists use chronological order: the head is applied first. -/
def opChain : List (Operator X bot) → Operator X bot
  | [] => opId
  | f :: fs => opComp (opChain fs) f

def matrixProduct : List (Coeff I) → Coeff I
  | [] => matId
  | M :: Ms => matMul (matrixProduct Ms) M

theorem matrixProduct_nil : matrixProduct ([] : List (Coeff I)) = matId := rfl

theorem matrixProduct_singleton (M : Coeff I) : matrixProduct [M] = M := by
  exact matMul_one_left M

theorem matrixProduct_cons (M : Coeff I) (Ms : List (Coeff I)) :
    matrixProduct (M :: Ms) = matMul (matrixProduct Ms) M := rfl

def reached : List (Operator X bot) → Set X → Set X
  | [], U => U
  | f :: fs, U => reached fs (f.func '' U)

def domainsAlong : List (Operator X bot) → Set X → Prop
  | [], U => U ⊆ dom (opId : Operator X bot)
  | f :: fs, U => U ⊆ dom f ∧ domainsAlong fs (f.func '' U)

theorem subset_dom_comp (f g : Operator X bot) (U : Set X) :
    U ⊆ dom (opComp g f) ↔ U ⊆ dom f ∧ f.func '' U ⊆ dom g := by
  constructor
  · intro h
    constructor
    · intro x hx hbot
      have hcomp := h hx
      change g.func (f.func x) ≠ bot at hcomp
      exact hcomp (by rw [hbot, g.preserves_bot])
    · rintro _ ⟨x, hx, rfl⟩
      exact h hx
  · rintro ⟨_, hg⟩ x hx
    exact hg ⟨x, hx, rfl⟩

theorem chain_domain_iff (fs : List (Operator X bot)) (U : Set X) :
    U ⊆ dom (opChain fs) ↔ domainsAlong fs U := by
  induction fs generalizing U with
  | nil => rfl
  | cons f fs ih =>
    change (U ⊆ dom (opComp (opChain fs) f)) ↔
      (U ⊆ dom f ∧ domainsAlong fs (f.func '' U))
    rw [subset_dom_comp, ih]

theorem domain_at_step (pre post : List (Operator X bot)) (f : Operator X bot)
    (U : Set X) (h : U ⊆ dom (opChain (pre ++ f :: post))) :
    reached pre U ⊆ dom f := by
  have hs := (chain_domain_iff _ _).mp h
  induction pre generalizing U with
  | nil => exact hs.1
  | cons a pre ih =>
    exact ih (a.func '' U) ((chain_domain_iff _ _).mpr hs.2) hs.2

theorem chain_image (fs : List (Operator X bot)) (U : Set X) :
    (opChain fs).func '' U = reached fs U := by
  induction fs generalizing U with
  | nil => simp [opChain, opId, reached]
  | cons f fs ih =>
    change ((opChain fs).func ∘ f.func) '' U = reached fs (f.func '' U)
    rw [Set.image_comp, ih]

/-- Each conjunct is a single-step certificate on its actual recursively computed input. -/
def LipSteps (d : I → X → X → ENNReal) :
    List (Operator X bot × Coeff I) → Set X → Prop
  | [], _ => True
  | (f, M) :: rest, U => LipOn d f U M ∧ LipSteps d rest (f.func '' U)

def CoLipSteps (d : I → X → X → ENNReal) :
    List (Operator X bot × Coeff I) → Set X → Prop
  | [], _ => True
  | (f, M) :: rest, U => CoLipOn d f U M ∧ CoLipSteps d rest (f.func '' U)

theorem lip_chain (steps : List (Operator X bot × Coeff I)) (U : Set X)
    (hdom : U ⊆ dom (opChain (steps.map Prod.fst))) (hs : LipSteps d steps U) :
    LipOn d (opChain (steps.map Prod.fst)) U (matrixProduct (steps.map Prod.snd)) := by
  induction steps generalizing U with
  | nil => exact opId_lip d hdom
  | cons p rest ih =>
    obtain ⟨f, M⟩ := p
    change LipOn d (opComp (opChain (rest.map Prod.fst)) f) U
      (matMul (matrixProduct (rest.map Prod.snd)) M)
    change U ⊆ dom (opComp (opChain (rest.map Prod.fst)) f) at hdom
    change LipOn d f U M ∧ LipSteps d rest (f.func '' U) at hs
    have htaildom := (subset_dom_comp f (opChain (rest.map Prod.fst)) U).mp hdom |>.2
    exact lip_comp d hdom hs.1 (ih (f.func '' U) htaildom hs.2)

theorem colip_chain (steps : List (Operator X bot × Coeff I)) (U : Set X)
    (hne : U.Nonempty) (hdom : U ⊆ dom (opChain (steps.map Prod.fst)))
    (hs : CoLipSteps d steps U) :
    CoLipOn d (opChain (steps.map Prod.fst)) U (matrixProduct (steps.map Prod.snd)) := by
  induction steps generalizing U with
  | nil => exact opId_colip d hne hdom
  | cons p rest ih =>
    obtain ⟨f, M⟩ := p
    change CoLipOn d (opComp (opChain (rest.map Prod.fst)) f) U
      (matMul (matrixProduct (rest.map Prod.snd)) M)
    change U ⊆ dom (opComp (opChain (rest.map Prod.fst)) f) at hdom
    change CoLipOn d f U M ∧ CoLipSteps d rest (f.func '' U) at hs
    have htaildom := (subset_dom_comp f (opChain (rest.map Prod.fst)) U).mp hdom |>.2
    have htailne : (f.func '' U).Nonempty := hne.image _
    exact colip_comp d hdom hs.1 (ih (f.func '' U) htailne htaildom hs.2)

theorem colip_nonempty_chain (first : Operator X bot × Coeff I)
    (rest : List (Operator X bot × Coeff I)) (U : Set X)
    (hdom : U ⊆ dom (opChain ((first :: rest).map Prod.fst)))
    (hs : CoLipSteps d (first :: rest) U) :
    CoLipOn d (opChain ((first :: rest).map Prod.fst)) U
      (matrixProduct ((first :: rest).map Prod.snd)) := by
  apply colip_chain d _ U ?_ hdom hs
  cases first with
  | mk f M => exact hs.1.1

theorem lipSteps_extract (pre post : List (Operator X bot × Coeff I))
    (f : Operator X bot) (M : Coeff I) (U : Set X)
    (hs : LipSteps d (pre ++ (f, M) :: post) U) :
    LipOn d f (reached (pre.map Prod.fst) U) M := by
  induction pre generalizing U with
  | nil => exact hs.1
  | cons a pre ih =>
    cases a with
    | mk g K => exact ih (g.func '' U) hs.2

theorem lipSteps_iff_all (steps : List (Operator X bot × Coeff I)) (U : Set X) :
    LipSteps d steps U ↔
      ∀ (pre post : List (Operator X bot × Coeff I)) (f : Operator X bot) (M : Coeff I),
        steps = pre ++ (f, M) :: post → LipOn d f (reached (pre.map Prod.fst) U) M := by
  constructor
  · intro hs pre post f M h
    subst steps
    exact lipSteps_extract d pre post f M U hs
  · intro hall
    induction steps generalizing U with
    | nil => trivial
    | cons a rest ih =>
      cases a with
      | mk f M =>
        refine ⟨hall [] rest f M rfl, ?_⟩
        apply ih
        intro pre post g K h
        have h' := hall ((f, M) :: pre) post g K (by simp [h])
        exact h'

theorem colipSteps_extract (pre post : List (Operator X bot × Coeff I))
    (f : Operator X bot) (M : Coeff I) (U : Set X)
    (hs : CoLipSteps d (pre ++ (f, M) :: post) U) :
    CoLipOn d f (reached (pre.map Prod.fst) U) M := by
  induction pre generalizing U with
  | nil => exact hs.1
  | cons a pre ih =>
    cases a with
    | mk g K => exact ih (g.func '' U) hs.2

theorem colipSteps_iff_all (steps : List (Operator X bot × Coeff I)) (U : Set X) :
    CoLipSteps d steps U ↔
      ∀ (pre post : List (Operator X bot × Coeff I)) (f : Operator X bot) (M : Coeff I),
        steps = pre ++ (f, M) :: post → CoLipOn d f (reached (pre.map Prod.fst) U) M := by
  constructor
  · intro hs pre post f M h
    subst steps
    exact colipSteps_extract d pre post f M U hs
  · intro hall
    induction steps generalizing U with
    | nil => trivial
    | cons a rest ih =>
      cases a with
      | mk f M =>
        refine ⟨hall [] rest f M rfl, ?_⟩
        apply ih
        intro pre post g K h
        have h' := hall ((f, M) :: pre) post g K (by simp [h])
        exact h'

/-- A path stores exactly the intermediate indices, in chronological order. -/
def Paths (I : Type) : Nat → Type
  | 0 => Unit
  | n + 1 => I × Paths I n

instance pathsFintype (n : Nat) : Fintype (Paths I n) := by
  induction n with
  | zero => dsimp [Paths]; infer_instance
  | succ n ih => dsimp [Paths]; infer_instance

def pathWeight : (M : Coeff I) → (Ms : List (Coeff I)) → I → I → Paths I Ms.length → ENNReal
  | M, [], i, j, _ => M i j
  | M, N :: Ms, i, j, p => M i p.1 * pathWeight N Ms p.1 j p.2

def pathHasZero : (M : Coeff I) → (Ms : List (Coeff I)) → I → I → Paths I Ms.length → Prop
  | M, [], i, j, _ => M i j = 0
  | M, N :: Ms, i, j, p => M i p.1 = 0 ∨ pathHasZero N Ms p.1 j p.2

def pathAllPositive : (M : Coeff I) → (Ms : List (Coeff I)) → I → I → Paths I Ms.length → Prop
  | M, [], i, j, _ => 0 < M i j
  | M, N :: Ms, i, j, p => 0 < M i p.1 ∧ pathAllPositive N Ms p.1 j p.2

theorem pathWeight_eq_zero (M : Coeff I) (Ms : List (Coeff I)) (i j : I)
    (p : Paths I Ms.length) :
    pathWeight M Ms i j p = 0 ↔ pathHasZero M Ms i j p := by
  induction Ms generalizing M i j with
  | nil => rfl
  | cons N Ns ih =>
    change M i p.1 * pathWeight N Ns p.1 j p.2 = 0 ↔
      M i p.1 = 0 ∨ pathHasZero N Ns p.1 j p.2
    rw [mul_eq_zero, ih]

theorem pathWeight_positive (M : Coeff I) (Ms : List (Coeff I)) (i j : I)
    (p : Paths I Ms.length) :
    0 < pathWeight M Ms i j p ↔ pathAllPositive M Ms i j p := by
  induction Ms generalizing M i j with
  | nil => rfl
  | cons N Ns ih =>
    change 0 < M i p.1 * pathWeight N Ns p.1 j p.2 ↔
      0 < M i p.1 ∧ pathAllPositive N Ns p.1 j p.2
    rw [ENNReal.mul_pos_iff, ih]

theorem matrixProduct_paths (M : Coeff I) (Ms : List (Coeff I)) (i j : I) :
    matrixProduct (M :: Ms) i j = ∑ p : Paths I Ms.length, pathWeight M Ms i j p := by
  induction Ms generalizing M i j with
  | nil => simp [matrixProduct_singleton, pathWeight, Paths]
  | cons N Ns ih =>
    change (∑ k, matrixProduct (N :: Ns) k j * M i k) =
      ∑ p : I × Paths I Ns.length, M i p.1 * pathWeight N Ns p.1 j p.2
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro k _
    rw [ih]
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p _
    exact mul_comm _ _

theorem matrixProduct_zero_iff_paths (M : Coeff I) (Ms : List (Coeff I)) (i j : I) :
    matrixProduct (M :: Ms) i j = 0 ↔
      ∀ p : Paths I Ms.length, pathHasZero M Ms i j p := by
  rw [matrixProduct_paths, Finset.sum_eq_zero_iff]
  simp only [Finset.mem_univ, true_implies, pathWeight_eq_zero]

theorem matrixProduct_pos_iff_paths (M : Coeff I) (Ms : List (Coeff I)) (i j : I) :
    0 < matrixProduct (M :: Ms) i j ↔
      ∃ p : Paths I Ms.length, pathAllPositive M Ms i j p := by
  rw [matrixProduct_paths, Finset.sum_pos_iff]
  simp only [Finset.mem_univ, true_and, pathWeight_positive]

theorem one_step_path_unique (M : Coeff I) (i j : I) (p : Paths I 0) :
    p = () ∧ (pathHasZero M [] i j p ↔ M i j = 0) ∧
      (pathAllPositive M [] i j p ↔ 0 < M i j) := by
  cases p
  exact ⟨rfl, Iff.rfl, Iff.rfl⟩

/-- Explicit equivalence with the standard type of all length-`n` index sequences. -/
def pathsEquivSequence : (n : Nat) → Paths I n ≃ (Fin n → I)
  | 0 =>
    { toFun := fun _ k => Fin.elim0 k
      invFun := fun _ => ()
      left_inv := by intro p; cases p; rfl
      right_inv := by intro s; funext k; exact Fin.elim0 k }
  | n + 1 => (Equiv.prodCongr (Equiv.refl I) (pathsEquivSequence n)).trans
      (Fin.consEquiv (fun _ => I))

theorem pathsEquivSequence_head (n : Nat) (p : Paths I (n + 1)) :
    pathsEquivSequence (n + 1) p 0 = p.1 := by
  rfl

theorem pathsEquivSequence_tail (n : Nat) (p : Paths I (n + 1)) :
    Fin.tail (pathsEquivSequence (n + 1) p) = pathsEquivSequence n p.2 := by
  rfl

/-- The same path semantics, on ordinary finite index sequences. -/
def sequenceWeight : (M : Coeff I) → (Ms : List (Coeff I)) → I → I →
    (Fin Ms.length → I) → ENNReal
  | M, [], i, j, _ => M i j
  | M, N :: Ms, i, j, p => M i (p 0) * sequenceWeight N Ms (p 0) j (Fin.tail p)

def sequenceHasZero : (M : Coeff I) → (Ms : List (Coeff I)) → I → I →
    (Fin Ms.length → I) → Prop
  | M, [], i, j, _ => M i j = 0
  | M, N :: Ms, i, j, p => M i (p 0) = 0 ∨ sequenceHasZero N Ms (p 0) j (Fin.tail p)

def sequenceAllPositive : (M : Coeff I) → (Ms : List (Coeff I)) → I → I →
    (Fin Ms.length → I) → Prop
  | M, [], i, j, _ => 0 < M i j
  | M, N :: Ms, i, j, p => 0 < M i (p 0) ∧ sequenceAllPositive N Ms (p 0) j (Fin.tail p)

theorem pathWeight_eq_sequence (M : Coeff I) (Ms : List (Coeff I)) (i j : I)
    (p : Paths I Ms.length) :
    pathWeight M Ms i j p = sequenceWeight M Ms i j (pathsEquivSequence _ p) := by
  induction Ms generalizing M i j with
  | nil => rfl
  | cons N Ns ih =>
    change M i p.1 * pathWeight N Ns p.1 j p.2 =
      M i (pathsEquivSequence (Ns.length + 1) p 0) *
        sequenceWeight N Ns (pathsEquivSequence (Ns.length + 1) p 0) j
          (Fin.tail (pathsEquivSequence (Ns.length + 1) p))
    rw [pathsEquivSequence_head, pathsEquivSequence_tail, ih]

theorem pathHasZero_iff_sequence (M : Coeff I) (Ms : List (Coeff I)) (i j : I)
    (p : Paths I Ms.length) :
    pathHasZero M Ms i j p ↔ sequenceHasZero M Ms i j (pathsEquivSequence _ p) := by
  induction Ms generalizing M i j with
  | nil => rfl
  | cons N Ns ih =>
    change (M i p.1 = 0 ∨ pathHasZero N Ns p.1 j p.2) ↔
      (M i (pathsEquivSequence (Ns.length + 1) p 0) = 0 ∨
        sequenceHasZero N Ns (pathsEquivSequence (Ns.length + 1) p 0) j
          (Fin.tail (pathsEquivSequence (Ns.length + 1) p)))
    rw [pathsEquivSequence_head, pathsEquivSequence_tail, ih]

theorem pathAllPositive_iff_sequence (M : Coeff I) (Ms : List (Coeff I)) (i j : I)
    (p : Paths I Ms.length) :
    pathAllPositive M Ms i j p ↔ sequenceAllPositive M Ms i j (pathsEquivSequence _ p) := by
  induction Ms generalizing M i j with
  | nil => rfl
  | cons N Ns ih =>
    change (0 < M i p.1 ∧ pathAllPositive N Ns p.1 j p.2) ↔
      (0 < M i (pathsEquivSequence (Ns.length + 1) p 0) ∧
        sequenceAllPositive N Ns (pathsEquivSequence (Ns.length + 1) p 0) j
          (Fin.tail (pathsEquivSequence (Ns.length + 1) p)))
    rw [pathsEquivSequence_head, pathsEquivSequence_tail, ih]

theorem matrixProduct_zero_iff_sequences (M : Coeff I) (Ms : List (Coeff I)) (i j : I) :
    matrixProduct (M :: Ms) i j = 0 ↔
      ∀ p : Fin Ms.length → I, sequenceHasZero M Ms i j p := by
  rw [matrixProduct_zero_iff_paths]
  constructor
  · intro h p
    obtain ⟨q, rfl⟩ := (pathsEquivSequence _).surjective p
    exact (pathHasZero_iff_sequence M Ms i j q).mp (h q)
  · intro h p
    exact (pathHasZero_iff_sequence M Ms i j p).mpr (h (pathsEquivSequence _ p))

theorem matrixProduct_pos_iff_sequences (M : Coeff I) (Ms : List (Coeff I)) (i j : I) :
    0 < matrixProduct (M :: Ms) i j ↔
      ∃ p : Fin Ms.length → I, sequenceAllPositive M Ms i j p := by
  rw [matrixProduct_pos_iff_paths]
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨pathsEquivSequence _ p, (pathAllPositive_iff_sequence M Ms i j p).mp hp⟩
  · rintro ⟨p, hp⟩
    obtain ⟨q, rfl⟩ := (pathsEquivSequence _).surjective p
    exact ⟨q, (pathAllPositive_iff_sequence M Ms i j q).mpr hp⟩

theorem frozen_chain_append_single (fs : List (Operator X bot)) (f : Operator X bot) :
    OperatorChain (fs ++ [f]) = opComp (OperatorChain fs) f := by
  induction fs with
  | nil => ext x; rfl
  | cons g gs ih =>
    ext x
    change g.func ((OperatorChain (gs ++ [f])).func x) =
      g.func ((OperatorChain gs).func (f.func x))
    rw [ih]
    rfl

theorem chain_eq_frozen_reverse (fs : List (Operator X bot)) :
    opChain fs = OperatorChain fs.reverse := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    simp only [List.reverse_cons, frozen_chain_append_single, opChain]
    rw [ih]

/-- A finite space displaying a zero infimum which is not feasible at zero. -/
def exampleDist (i : Bool) (x y : Option Bool) : ENNReal :=
  if x = y then 0 else if x = none ∨ y = none then ⊤ else if i then 1 else ⊤

def exampleDomain : Set (Option Bool) := {x | x ≠ none}

theorem example_metric (i : Bool) :
    ExtendedPseudoMetric (Option Bool) none (exampleDist i) := by
  refine ⟨⟨some true, by simp⟩, ?_, ?_, ?_, ?_⟩
  · intro x
    simp [exampleDist]
  · intro x y
    fin_cases i <;> fin_cases x <;> fin_cases y <;> simp [exampleDist]
  · intro x y z
    fin_cases i <;> fin_cases x <;> fin_cases y <;> fin_cases z <;> simp [exampleDist]
  · intro x hx
    fin_cases i <;> fin_cases x <;> simp_all [exampleDist]

theorem example_domain_nonempty : exampleDomain.Nonempty :=
  ⟨some true, by simp [exampleDomain]⟩

theorem example_domain_subset : exampleDomain ⊆ dom (opId : Operator (Option Bool) none) := by
  intro x hx
  exact hx

theorem example_positive_feasible {a : ENNReal} (ha : 0 < a) :
    a ∈ ScalarFeasible exampleDist (opId : Operator (Option Bool) none)
      exampleDomain false true := by
  intro x hx y hy
  fin_cases x <;> fin_cases y <;>
    simp_all [exampleDist, exampleDomain, opId, ENNReal.mul_top (ne_of_gt ha)]

theorem example_zero_not_feasible :
    (0 : ENNReal) ∉ ScalarFeasible exampleDist (opId : Operator (Option Bool) none)
      exampleDomain false true := by
  intro h
  have hxy := h (some true) (by simp [exampleDomain]) (some false) (by simp [exampleDomain])
  simp [exampleDist, opId] at hxy

theorem example_channelInf_zero :
    channelInf exampleDist (opId : Operator (Option Bool) none) exampleDomain false true = 0 := by
  apply le_antisymm
  · by_contra h
    have hpos : 0 < channelInf exampleDist (opId : Operator (Option Bool) none)
        exampleDomain false true := lt_of_not_ge h
    obtain ⟨a, ha, hal⟩ := exists_between hpos
    have hbound := sInf_le (example_positive_feasible ha)
    exact (not_le_of_gt hal) hbound
  · exact zero_le _

end
end HCH02
```

```lean filename=lakefile.lean
import Lake
open Lake DSL

/- The preinstalled mathlib commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6
   and the two frozen prerequisite modules are supplied through LEAN_PATH.
   There are no network dependencies to resolve in this package. -/
package hch02

script check do
  let result ← IO.Process.output {cmd := "lean", args := #["-o", "Main.olean", "Main.lean"]}
  IO.print result.stdout
  IO.eprint result.stderr
  return result.exitCode
```

```text filename=lean-toolchain
leanprover/lean4:v4.29.1
```

```json filename=lake-manifest.json
{
  "version": "1.1.0",
  "packagesDir": ".lake/packages",
  "packages": [],
  "name": "hch02",
  "lakeDir": ".lake"
}
```

```json filename=alignment.json
{
  "case_id": "HCH02",
  "version": "0.1.0",
  "items": [
    {"id":"HC02-D01","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.LipOn"},{"file":"Main.lean","name":"HCH02.LipFamily"},{"file":"Main.lean","name":"HCH02.LipFamilyOn"}],"representation":"ENNReal 系数按输入、输出存储；LipOn 同时要求 U⊆dom φ 和 U 上全点对、全输出指标的不等式；全域族令 U=dom φ。定义亦适用于较一般的有限指标类型。","dependencies":["HC02-D03"]},
    {"id":"HC02-D02","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.CoLipOn"},{"file":"Main.lean","name":"HCH02.CoLipFamilyOn"}],"representation":"CoLipOn 把 U 非空、U⊆dom φ 和全点对、全输出指标的 co-Lip 不等式全部列为证书条件；条目在 ENNReal 中。","dependencies":["HC02-D03"]},
    {"id":"HC02-D03","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.Coeff"},{"file":"Main.lean","name":"HCH02.displayMatrix"},{"file":"Main.lean","name":"HCH02.displayMatrix_apply"},{"file":"Main.lean","name":"HCH02.matMul"},{"file":"Main.lean","name":"HCH02.matMul_apply"}],"representation":"Coeff I 是 I→I→ENNReal，M i j 为 i→j；displayMatrix M j i=M i j；matMul B A i j=Σk B k j*A i k。","dependencies":[]},
    {"id":"HC02-D04","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.matId"},{"file":"Main.lean","name":"HCH02.matrixProduct"},{"file":"Main.lean","name":"HCH02.matrixProduct_nil"},{"file":"Main.lean","name":"HCH02.matrixProduct_singleton"},{"file":"Main.lean","name":"HCH02.matrixProduct_cons"}],"representation":"matId 为 Kronecker 单位矩阵；输入列表按施行顺序排列，递归式把后续矩阵乘积放在左侧；空列表为单位，单项列表等于该项。","dependencies":["HC02-D03"]},
    {"id":"HC02-D05","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.opChain"},{"file":"Main.lean","name":"HCH02.reached"},{"file":"Main.lean","name":"HCH02.chain_domain_iff"},{"file":"Main.lean","name":"HCH02.domain_at_step"},{"file":"Main.lean","name":"HCH02.chain_image"},{"file":"Main.lean","name":"HCH02.chain_eq_frozen_reverse"},{"file":"Main.lean","name":"HCH02.LipSteps"},{"file":"Main.lean","name":"HCH02.CoLipSteps"},{"file":"Main.lean","name":"HCH02.lipSteps_iff_all"},{"file":"Main.lean","name":"HCH02.colipSteps_iff_all"}],"representation":"正向列表的 reached 逐次取像；domain_at_step 由起始域包含于全复合定义域推出各实际步合法，chain_image 证明全像相同。chain_eq_frozen_reverse 对应前置模块的反序 OperatorChain。两个 Steps 当且仅当每个列表分解处的实际输入域上有相应单步证书，未把最终复合结论作为数据字段。","dependencies":["HC02-D01","HC02-D02"]},
    {"id":"HC02-D06","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.Paths"},{"file":"Main.lean","name":"HCH02.pathWeight"},{"file":"Main.lean","name":"HCH02.pathHasZero"},{"file":"Main.lean","name":"HCH02.pathAllPositive"},{"file":"Main.lean","name":"HCH02.pathsEquivSequence"},{"file":"Main.lean","name":"HCH02.pathWeight_eq_sequence"},{"file":"Main.lean","name":"HCH02.pathHasZero_iff_sequence"},{"file":"Main.lean","name":"HCH02.pathAllPositive_iff_sequence"},{"file":"Main.lean","name":"HCH02.one_step_path_unique"}],"representation":"长度 n 的矩阵链写成 M::Ms，Ms.length=n−1；Paths I Ms.length 是全部中间指标，起止指标单独传入，递归定义乘积、存在零边及所有边为正。pathsEquivSequence 双射到 Fin (n−1)→I，上述三个对应定理保持权重及谓词；n=1 只有 Unit 路径。","dependencies":["HC02-D03"]},
    {"id":"HC02-D07","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.Channel"},{"file":"Main.lean","name":"HCH02.Row"},{"file":"Main.lean","name":"HCH02.Col"},{"file":"Main.lean","name":"HCH02.Diagonal"},{"file":"Main.lean","name":"HCH02.RowDecoupled"},{"file":"Main.lean","name":"HCH02.ColDecoupled"}],"representation":"通道为 I×I；Row 固定输出 j、容许任意指定输入 i，Col 固定输入 i、容许任意指定输出 j；解耦分别存在合法证书及该行或列的支撑指标，Diagonal 令所有非对角项为零。","dependencies":["HC02-D01","HC02-D03"]},
    {"id":"HC02-D08","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.ScalarFeasible"},{"file":"Main.lean","name":"HCH02.channelInf"},{"file":"Main.lean","name":"HCH02.LegalDomain"},{"file":"Main.lean","name":"HCH02.ScalarFeasibleLegal"},{"file":"Main.lean","name":"HCH02.channelInfLegal"},{"file":"Main.lean","name":"HCH02.legal_scalar_correspondence"},{"file":"Main.lean","name":"HCH02.channelInf_of_empty"}],"representation":"可行族只使用输入分量 i 和输出分量 j；channelInf 是该集合的 sInf，空族时为顶。基础函数是对所有集合的保守全函数延拓；LegalDomain 将 U⊆dom φ 编入类型，legal_scalar_correspondence 证明与基础函数完全对应，不将其等同于矩阵条目。","dependencies":[]},
    {"id":"HC02-P01","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.singleton_lip_of_eq"}],"representation":"以任意 i 和 ∀k,k=i 表示单元素指标族，结论对任意 U 内点对给出唯一对角系数的标量 Lip 上界。","dependencies":["HC02-D01"]},
    {"id":"HC02-P02","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.global_lip_restrict"}],"representation":"对任意 U⊆dom φ，证明全域 Lip 证书族包含于受限证书族。","dependencies":["HC02-D01","HC02-P03"]},
    {"id":"HC02-P03","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.lip_restrict"},{"file":"Main.lean","name":"HCH02.lip_family_antitone"}],"representation":"对 U⊆V，任何 V 上的合法证书在 U 上仍合法；V 的定义域包含条件已包括在其证书中。","dependencies":["HC02-D01"]},
    {"id":"HC02-P04","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.entryInf"},{"file":"Main.lean","name":"HCH02.entryInf_antitone"}],"representation":"entryInf 是受限 Lip 证书对应条目的 sInf；U⊆V 时，基于证书限制证明 U 的条目下确界不大于 V 的。","dependencies":["HC02-D01","HC02-P03"]},
    {"id":"HC02-P05","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.sum_matMul"},{"file":"Main.lean","name":"HCH02.lip_comp"}],"representation":"f 先作用、g 后作用；g 的证书域恰为 f(U)，并显式假定 U⊆dom(g∘f)；结论为 matMul B A 的受限 Lip 证书。","dependencies":["HC02-D01","HC02-D03"]},
    {"id":"HC02-P06","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.term_le_sum"},{"file":"Main.lean","name":"HCH02.colip_zero_of_collapsed"}],"representation":"结论在任意合法受限域 U 上成立，因此可取 U=dom φ；输出 j 零距且输入 i 正距迫使 K i j=0。","dependencies":["HC02-D02"]},
    {"id":"HC02-P07","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.colip_comp"}],"representation":"两步 co-Lip 证书分别作用于 U 与 f(U)，复合域条件显式给出，结论保留 U 非空及乘积下界。","dependencies":["HC02-D02","HC02-D03","HC02-P05"]},
    {"id":"HC02-P08","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.perturb_forward"}],"representation":"对称性与三角不等式逐分量假设；局部逐点 δ 控制推出 g 像距≤f 像距+δ+δ。定理无需公共定义域假设，故涵盖原文较窄语境。","dependencies":[]},
    {"id":"HC02-P09","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.perturb_backward"}],"representation":"从相同逐点控制和对称性推出交换算子后的像距界。","dependencies":["HC02-P08"]},
    {"id":"HC02-P10","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.perturb_lip"}],"representation":"将 f 在 U 上的 Lip 求和证书代入正向扰动界，δ 重复相加两次。","dependencies":["HC02-D01","HC02-P08"]},
    {"id":"HC02-P11","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.perturb_colip"}],"representation":"将 f 在 U 上的 co-Lip 求和下界接到反向扰动界，δ 重复相加两次。","dependencies":["HC02-D02","HC02-P09"]},
    {"id":"HC02-P12","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.lip_chain"},{"file":"Main.lean","name":"HCH02.lipSteps_iff_all"}],"representation":"对正向算子及矩阵配对列表，假定起始域在全链定义域内，每步在实际像域上的 Lip 条件；所得有序矩阵积是全链证书。定理还涵盖空链。","dependencies":["HC02-D04","HC02-D05","HC02-P05","HC02-P14"]},
    {"id":"HC02-P13","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.colip_nonempty_chain"},{"file":"Main.lean","name":"HCH02.colip_chain"},{"file":"Main.lean","name":"HCH02.colipSteps_iff_all"}],"representation":"非空配对列表上的各步 co-Lip 证书均包含各实际域非空；从首步证书取得起始域非空并证明指定有序乘积为全链证书。","dependencies":["HC02-D04","HC02-D05","HC02-P07","HC02-P15"]},
    {"id":"HC02-P14","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.opId_lip"},{"file":"Main.lean","name":"HCH02.matId_sum"}],"representation":"U⊆dom id 时单位矩阵为 Lip 证书，证明对空 U 亦成立，因而包含原文非空情形。","dependencies":["HC02-D01","HC02-D04"]},
    {"id":"HC02-P15","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.opId_colip"}],"representation":"U 非空且 U⊆dom id 时，相同单位矩阵为 co-Lip 证书。","dependencies":["HC02-D02","HC02-D04","HC02-P14"]},
    {"id":"HC02-P16","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.matrixProduct_paths"},{"file":"Main.lean","name":"HCH02.matrixProduct_zero_iff_sequences"},{"file":"Main.lean","name":"HCH02.one_step_path_unique"}],"representation":"任意非空矩阵序列的乘积条目等于全部路径权重之和，且条目为零当且仅当每个普通有限中间序列都含零边；因此对实际 Lip 证书序列亦成立。单步情形只有空序列。","dependencies":["HC02-D04","HC02-D06"]},
    {"id":"HC02-P17","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.matrixProduct_pos_iff_sequences"},{"file":"Main.lean","name":"HCH02.one_step_path_unique"}],"representation":"任意非空矩阵序列的乘积条目正，当且仅当存在一个所有边正的普通中间序列；于是适用于实际 co-Lip 证书序列，并包含单步空序列。","dependencies":["HC02-D04","HC02-D06"]},
    {"id":"HC02-P18","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.scalar_infeasible_of_zero"}],"representation":"U 内零输入距、正输出距点对使可行 ENNReal 标量族为空，且其下确界为 ∞。","dependencies":["HC02-D08"]},
    {"id":"HC02-P19","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.scalar_inf_attained"}],"representation":"若单通道下确界正且有限，以 ENNReal 的下确界与乘法性质证明该下确界对 U 内全部点对可行。","dependencies":["HC02-D08"]},
    {"id":"HC02-P20","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.scalar_feasible_upward"}],"representation":"任意可行 λ0 与 λ1≥λ0 给出 λ1 可行，包括无限值。","dependencies":["HC02-D08"]},
    {"id":"HC02-P21","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.scalar_above_inf"}],"representation":"任意严格大于通道下确界的 ENNReal 常数可行，结论比原文的正有限下确界语境更一般。","dependencies":["HC02-D08","HC02-P20"]},
    {"id":"HC02-P22","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.scalar_zero_inf_positive"}],"representation":"下确界为零时任何正的 ENNReal 常数都可行，特别包括所有有限正常数。","dependencies":["HC02-P21"]},
    {"id":"HC02-P23","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.exampleDist"},{"file":"Main.lean","name":"HCH02.example_metric"},{"file":"Main.lean","name":"HCH02.exampleDomain"},{"file":"Main.lean","name":"HCH02.example_domain_nonempty"},{"file":"Main.lean","name":"HCH02.example_domain_subset"},{"file":"Main.lean","name":"HCH02.example_channelInf_zero"},{"file":"Main.lean","name":"HCH02.example_zero_not_feasible"}],"representation":"X=Option Bool，bot=none，指标 Bool；false 分量的不同点距为 ∞，true 分量在两个非吸收点间距为 1、对 bot 隔离。取恒等算子和全部非吸收点，证明规范空间合法、U 非空且合法、通道下确界为零但零不可行。","dependencies":["HC02-D08"]},
    {"id":"HC02-P24","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.scalar_inf_lt_top_iff"}],"representation":"下确界小于 ∞ 当且仅当存在小于 ∞ 的可行 ENNReal 常数，无须假定下确界被取到。","dependencies":["HC02-D08"]},
    {"id":"HC02-P25","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.zero_term"},{"file":"Main.lean","name":"HCH02.zero_term_erase"}],"representation":"L i j=0 则对应乘项为零，且有限求和等于删去 i 后的和；对于无限输入距同样成立。","dependencies":["HC02-D03"]},
    {"id":"HC02-P26","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.row_sum"},{"file":"Main.lean","name":"HCH02.row_lip"}],"representation":"任意指定的输入 i 可以不同于输出 j；Row L i j 与合法证书给出 i→j 单通道上界。","dependencies":["HC02-D01","HC02-D07"]},
    {"id":"HC02-P27","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.col_contribution"}],"representation":"Col L i j 时，每个 k≠j 的 i→k 乘项都为零，描述该证书中的贡献范围。","dependencies":["HC02-D07"]},
    {"id":"HC02-P28","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.diagonal_lip"}],"representation":"对角 Lip 证书对每个输出 j 和每对 U 中点给出对角单分量上界。","dependencies":["HC02-D07","HC02-P26"]},
    {"id":"HC02-P29","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.two_sided"}],"representation":"在 L、K 分别合法且仅假定 L 的第 j 行除对角项为零时，证明 Kjj*dj≤输出距≤Ljj*dj；K 无稀疏或有限性假设。","dependencies":["HC02-D02","HC02-D07","HC02-P06","HC02-P26"]},
    {"id":"HC02-P30","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.diagonal_two_sided"},{"file":"Main.lean","name":"HCH02.finite_diagonal_two_sided"}],"representation":"L 对角时所有分量同时满足双侧界；附加每个对角 L、K 系数有限时，证明同时保留有限性与各双侧界。","dependencies":["HC02-D07","HC02-P29"]},
    {"id":"HC02-P31","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.colip_channel_pos"}],"representation":"合法 co-Lip 证书的 i→j 条目正时，对任意 U 内点对，输入 i 正距蕴含输出 j 正距，包括 ∞ 情形。","dependencies":["HC02-D02","HC02-P06"]},
    {"id":"HC02-P32","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.colip_reflect_zero"}],"representation":"所有对角 co-Lip 条目为正时，U 内像点的冻结模块 GaugeZeroRelated 蕴含原点的该关系，不假设族分离。","dependencies":["HC02-D02","HC02-P31"]}
  ]
}
```

**完成与验证情况：**40 项义务均已完成并按清单对齐；没有已知未完成或未确认的数学范围。已在 Lean 4.29.1 和预置 mathlib 上运行 `lake run check`，并核对预置 mathlib 的 HEAD 为指定提交。所有定理的公理依赖检查仅出现允许的 `propext`、`Classical.choice` 和 `Quot.sound`。

数学原文作者为 Zhe Li（Glen Li / glenzli，ORCID https://orcid.org/0009-0006-6536-3453）；作品为 *The Operator Evolution Theory*，https://glenzli.com/books/oet/，采用 CC BY 4.0。本答复是对题目所给冻结历史版本的 Lean 改编。