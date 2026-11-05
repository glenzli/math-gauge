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
