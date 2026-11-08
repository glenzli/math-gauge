尚未完整完成整章：40 项义务中，以下交付完成了 36 项；**D06、P16、P17、P23 未完成**。因此目前不能声称严格对齐整章。

下列 `Main.lean` 已用本地 Lean 4.29.1 编译，所有声明的公理审计仅显示 `propext`、`Classical.choice` 和 `Quot.sound`。本地环境清单将 mathlib 标为指定提交；由于本机 `git` 无法启动，我未能独立复核其检出提交。源码依赖题目提供的两份冻结前置模块。

```lean filename=Main.lean
import formal_oet.vol_01.ch_01_foundations.operator_space

open scoped BigOperators
open formal_oet.vol_01.ch_01_foundations

namespace HCH02

variable {X I : Type} {bot : X} [Fintype I] [DecidableEq I]
variable (d : I → X → X → ENNReal)

abbrev Channel (I : Type) := I × I
abbrev Mat (I : Type) := I → I → ENNReal

def LipOn (φ : Operator X bot) (U : Set X) (L : Mat I) : Prop :=
  U ⊆ dom φ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j,
    d j (φ.func x) (φ.func y) ≤ ∑ i, L i j * d i x y

def Lip (φ : Operator X bot) : Set (Mat I) :=
  {L | LipOn d φ (dom φ) L}

def Lips (φ : Operator X bot) (U : Set X) : Set (Mat I) :=
  {L | LipOn d φ U L}

def CoLipOn (φ : Operator X bot) (U : Set X) (K : Mat I) : Prop :=
  U.Nonempty ∧ U ⊆ dom φ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j,
    (∑ i, K i j * d i x y) ≤ d j (φ.func x) (φ.func y)

def CoLips (φ : Operator X bot) (U : Set X) : Set (Mat I) :=
  {K | CoLipOn d φ U K}

noncomputable def matMul (B A : Mat I) : Mat I :=
  fun i j => ∑ k, B k j * A i k

def display (M : Mat I) : I → I → ENNReal :=
  fun j i => M i j

def matId : Mat I :=
  fun i j => if i = j then 1 else 0

def Row (L : Mat I) (i j : I) : Prop :=
  ∀ k, k ≠ i → L k j = 0

def Col (L : Mat I) (i j : I) : Prop :=
  ∀ k, k ≠ j → L i k = 0

def Diagonal (L : Mat I) : Prop :=
  ∀ i j, i ≠ j → L i j = 0

def RowDecoupled (φ : Operator X bot) (U : Set X) (j : I) : Prop :=
  ∃ L, LipOn d φ U L ∧ ∃ i, Row L i j

def ColDecoupled (φ : Operator X bot) (U : Set X) (i : I) : Prop :=
  ∃ L, LipOn d φ U L ∧ ∃ j, Col L i j

def ScalarFeasible (φ : Operator X bot) (U : Set X) (i j : I) :
    Set ENNReal :=
  {a | ∀ x ∈ U, ∀ y ∈ U,
    d j (φ.func x) (φ.func y) ≤ a * d i x y}

noncomputable def scalarInf (φ : Operator X bot) (U : Set X)
    (i j : I) : ENNReal :=
  sInf (ScalarFeasible d φ U i j)

noncomputable def entryInf (φ : Operator X bot) (U : Set X)
    (i j : I) : ENNReal :=
  sInf ((fun M : Mat I => M i j) '' Lips d φ U)

theorem lip_restrict {φ : Operator X bot} {U V : Set X} {L : Mat I}
    (hUV : U ⊆ V) (h : LipOn d φ V L) : LipOn d φ U L := by
  refine ⟨hUV.trans h.1, ?_⟩
  intro x hx y hy j
  exact h.2 x (hUV hx) y (hUV hy) j

theorem global_restrict {φ : Operator X bot} {U : Set X}
    (hU : U ⊆ dom φ) : Lip d φ ⊆ Lips d φ U := by
  intro L h
  exact lip_restrict d hU h

theorem entryInf_antitone {φ : Operator X bot} {U V : Set X}
    (hUV : U ⊆ V) (i j : I) :
    entryInf d φ U i j ≤ entryInf d φ V i j := by
  apply sInf_le_sInf
  rintro a ⟨M, hM, rfl⟩
  exact ⟨M, lip_restrict d hUV hM, rfl⟩

theorem scalar_upward {φ : Operator X bot} {U : Set X} {i j : I}
    {a b : ENNReal} (ha : a ∈ ScalarFeasible d φ U i j)
    (hab : a ≤ b) : b ∈ ScalarFeasible d φ U i j := by
  intro x hx y hy
  exact (ha x hx y hy).trans (mul_le_mul_right' hab _)

theorem scalar_above_inf {φ : Operator X bot} {U : Set X} {i j : I}
    {a : ENNReal} (ha : scalarInf d φ U i j < a) :
    a ∈ ScalarFeasible d φ U i j := by
  have hex : ∃ b ∈ ScalarFeasible d φ U i j, b < a := by
    by_contra h
    push_neg at h
    have : a ≤ scalarInf d φ U i j := le_sInf h
    exact (not_le_of_gt ha) this
  obtain ⟨b, hb, hba⟩ := hex
  exact scalar_upward d hb hba.le

theorem scalar_zero_inf {φ : Operator X bot} {U : Set X} {i j : I}
    (h : scalarInf d φ U i j = 0) {a : ENNReal} (ha : 0 < a) :
    a ∈ ScalarFeasible d φ U i j := by
  apply scalar_above_inf d
  simpa [h] using ha

theorem scalar_finite_iff {φ : Operator X bot} {U : Set X} {i j : I} :
    scalarInf d φ U i j < ⊤ ↔
      ∃ a < ⊤, a ∈ ScalarFeasible d φ U i j := by
  constructor
  · intro h
    obtain ⟨a, ha, hlt⟩ :
        ∃ a ∈ ScalarFeasible d φ U i j, a < ⊤ := by
      by_contra hn
      push_neg at hn
      have ht : ⊤ ≤ scalarInf d φ U i j := le_sInf hn
      exact (not_le_of_gt h) ht
    exact ⟨a, hlt, ha⟩
  · rintro ⟨a, ha, hm⟩
    exact lt_of_le_of_lt (sInf_le hm) ha

theorem scalar_inf_empty {φ : Operator X bot} {U : Set X} {i j : I}
    (h : ScalarFeasible d φ U i j = ∅) :
    scalarInf d φ U i j = ⊤ := by
  simp [scalarInf, h]

theorem scalar_infeasible {φ : Operator X bot} {U : Set X} {i j : I}
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (hzero : d i x y = 0)
    (hpos : 0 < d j (φ.func x) (φ.func y)) :
    ScalarFeasible d φ U i j = ∅ ∧ scalarInf d φ U i j = ⊤ := by
  have he : ScalarFeasible d φ U i j = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro a ha
    have h := ha x hx y hy
    rw [hzero, mul_zero] at h
    exact (not_le_of_gt hpos) h
  exact ⟨he, by simp [scalarInf, he]⟩

theorem zero_term (L : Mat I) (i j : I) (x y : X)
    (h : L i j = 0) : L i j * d i x y = 0 := by
  simp [h]

theorem row_bound {φ : Operator X bot} {U : Set X} {L : Mat I}
    {i j : I} (hL : LipOn d φ U L) (hrow : Row L i j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    d j (φ.func x) (φ.func y) ≤ L i j * d i x y := by
  have hs : (∑ k, L k j * d k x y) = L i j * d i x y := by
    apply Finset.sum_eq_single i
    · intro k _ hki
      simp [hrow k hki]
    · simp
  simpa [hs] using hL.2 x hx y hy j

theorem col_term {L : Mat I} {i j k : I}
    (h : Col L i j) (hk : k ≠ j) (x y : X) :
    L i k * d i x y = 0 := by
  simp [h k hk]

theorem diagonal_bound {φ : Operator X bot} {U : Set X} {L : Mat I}
    (hL : LipOn d φ U L) (hdiag : Diagonal L)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (φ.func x) (φ.func y) ≤ L j j * d j x y :=
  row_bound d hL (fun k hk => hdiag k j hk) hx hy

theorem colip_term {φ : Operator X bot} {U : Set X} {K : Mat I}
    (hK : CoLipOn d φ U K) {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    (i j : I) : K i j * d i x y ≤ d j (φ.func x) (φ.func y) := by
  exact
    (Finset.single_le_sum
      (fun k _ => zero_le (K k j * d k x y))
      (Finset.mem_univ i)).trans
      (hK.2.2 x hx y hy j)

theorem two_sided {φ : Operator X bot} {U : Set X} {L K : Mat I}
    {j : I} (hL : LipOn d φ U L) (hK : CoLipOn d φ U K)
    (hrow : Row L j j) {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    K j j * d j x y ≤ d j (φ.func x) (φ.func y) ∧
      d j (φ.func x) (φ.func y) ≤ L j j * d j x y :=
  ⟨colip_term d hK hx hy j j, row_bound d hL hrow hx hy⟩

theorem positive_channel {φ : Operator X bot} {U : Set X}
    {K : Mat I} {i j : I} (hK : CoLipOn d φ U K)
    (hk : 0 < K i j) {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    (hd : 0 < d i x y) : 0 < d j (φ.func x) (φ.func y) :=
  lt_of_lt_of_le (ENNReal.mul_pos hk.ne' hd.ne')
    (colip_term d hK hx hy i j)

theorem reflect_zero {φ : Operator X bot} {U : Set X} {K : Mat I}
    (hK : CoLipOn d φ U K) (hk : ∀ j, 0 < K j j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    (hzero : GaugeZeroRelated d (φ.func x) (φ.func y)) :
    GaugeZeroRelated d x y := by
  intro j
  apply le_antisymm _ (zero_le _)
  by_contra hn
  have hp : 0 < d j x y := lt_of_not_ge hn
  have hp' := positive_channel d hK (hk j) hx hy hp
  rw [hzero j] at hp'
  exact lt_irrefl 0 hp'

def comp (ψ φ : Operator X bot) : Operator X bot :=
  ⟨ψ.func ∘ φ.func, by simp [φ.preserves_bot, ψ.preserves_bot]⟩

def identity : Operator X bot := ⟨id, rfl⟩

theorem sum_product (A B : Mat I) (v : I → ENNReal) (j : I) :
    (∑ k, B k j * (∑ i, A i k * v i)) =
      ∑ i, (matMul B A) i j * v i := by
  simp only [matMul, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]

theorem lip_comp {φ ψ : Operator X bot} {U : Set X} {A B : Mat I}
    (hu : U ⊆ dom (comp ψ φ)) (ha : LipOn d φ U A)
    (hb : LipOn d ψ (φ.func '' U) B) :
    LipOn d (comp ψ φ) U (matMul B A) := by
  refine ⟨hu, ?_⟩
  intro x hx y hy j
  calc
    d j ((comp ψ φ).func x) ((comp ψ φ).func y) ≤
        ∑ k, B k j * d k (φ.func x) (φ.func y) :=
      hb.2 (φ.func x) ⟨x, hx, rfl⟩ (φ.func y) ⟨y, hy, rfl⟩ j
    _ ≤ ∑ k, B k j * (∑ i, A i k * d i x y) := by
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_left' (ha.2 x hx y hy k) _
    _ = ∑ i, (matMul B A) i j * d i x y :=
      sum_product A B (fun i => d i x y) j

theorem colip_comp {φ ψ : Operator X bot} {U : Set X} {A B : Mat I}
    (hu : U ⊆ dom (comp ψ φ)) (ha : CoLipOn d φ U A)
    (hb : CoLipOn d ψ (φ.func '' U) B) :
    CoLipOn d (comp ψ φ) U (matMul B A) := by
  refine ⟨ha.1, hu, ?_⟩
  intro x hx y hy j
  calc
    (∑ i, (matMul B A) i j * d i x y) =
        ∑ k, B k j * (∑ i, A i k * d i x y) :=
      (sum_product A B (fun i => d i x y) j).symm
    _ ≤ ∑ k, B k j * d k (φ.func x) (φ.func y) := by
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_left' (ha.2.2 x hx y hy k) _
    _ ≤ d j ((comp ψ φ).func x) ((comp ψ φ).func y) :=
      hb.2.2 (φ.func x) ⟨x, hx, rfl⟩ (φ.func y) ⟨y, hy, rfl⟩ j

theorem colip_zero {φ : Operator X bot} {K : Mat I} {i j : I}
    {x y : X} (hK : CoLipOn d φ (dom φ) K)
    (hx : x ∈ dom φ) (hy : y ∈ dom φ)
    (hz : d j (φ.func x) (φ.func y) = 0)
    (hp : 0 < d i x y) : K i j = 0 := by
  have h := colip_term d hK hx hy i j
  rw [hz] at h
  have hz' : K i j * d i x y = 0 := le_antisymm h (zero_le _)
  exact (mul_eq_zero.mp hz').resolve_right hp.ne'

theorem identity_sum (x y : X) (j : I) :
    (∑ i, matId i j * d i x y) = d j x y := by
  classical
  simp [matId]

theorem identity_lip {U : Set X}
    (hU : U ⊆ dom (identity : Operator X bot)) :
    LipOn d (identity : Operator X bot) U matId := by
  refine ⟨hU, ?_⟩
  intro x hx y hy j
  simp [identity, identity_sum]

theorem identity_colip {U : Set X} (hn : U.Nonempty)
    (hU : U ⊆ dom (identity : Operator X bot)) :
    CoLipOn d (identity : Operator X bot) U matId := by
  refine ⟨hn, hU, ?_⟩
  intro x hx y hy j
  simp [identity, identity_sum]

theorem perturb_forward {φ ψ : Operator X bot} {U : Set X}
    (δ : I → ENNReal)
    (hs : ∀ j x y, d j x y = d j y x)
    (ht : ∀ j x y z, d j x z ≤ d j x y + d j y z)
    (hδ : ∀ z ∈ U, ∀ j, d j (φ.func z) (ψ.func z) ≤ δ j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (ψ.func x) (ψ.func y) ≤
      d j (φ.func x) (φ.func y) + δ j + δ j := by
  calc
    d j (ψ.func x) (ψ.func y) ≤
        d j (ψ.func x) (φ.func x) + d j (φ.func x) (ψ.func y) :=
      ht j _ _ _
    _ ≤ d j (ψ.func x) (φ.func x) +
        (d j (φ.func x) (φ.func y) + d j (φ.func y) (ψ.func y)) := by
      gcongr
      exact ht j _ _ _
    _ ≤ δ j + (d j (φ.func x) (φ.func y) + δ j) := by
      apply add_le_add
      · rw [hs j]
        exact hδ x hx j
      · gcongr
        exact hδ y hy j
    _ = d j (φ.func x) (φ.func y) + δ j + δ j := by
      simp [add_comm, add_left_comm, add_assoc]

theorem perturb_reverse {φ ψ : Operator X bot} {U : Set X}
    (δ : I → ENNReal)
    (hs : ∀ j x y, d j x y = d j y x)
    (ht : ∀ j x y z, d j x z ≤ d j x y + d j y z)
    (hδ : ∀ z ∈ U, ∀ j, d j (φ.func z) (ψ.func z) ≤ δ j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (φ.func x) (φ.func y) ≤
      d j (ψ.func x) (ψ.func y) + δ j + δ j := by
  apply perturb_forward d δ hs ht _ hx hy j
  intro z hz k
  rw [hs k]
  exact hδ z hz k

theorem perturb_lip {φ ψ : Operator X bot} {U : Set X} {L : Mat I}
    (δ : I → ENNReal)
    (hs : ∀ j x y, d j x y = d j y x)
    (ht : ∀ j x y z, d j x z ≤ d j x y + d j y z)
    (hδ : ∀ z ∈ U, ∀ j, d j (φ.func z) (ψ.func z) ≤ δ j)
    (hL : LipOn d φ U L) {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    (j : I) :
    d j (ψ.func x) (ψ.func y) ≤
      (∑ i, L i j * d i x y) + δ j + δ j :=
  (perturb_forward d δ hs ht hδ hx hy j).trans
    (by gcongr; exact hL.2 x hx y hy j)

theorem perturb_colip {φ ψ : Operator X bot} {U : Set X} {K : Mat I}
    (δ : I → ENNReal)
    (hs : ∀ j x y, d j x y = d j y x)
    (ht : ∀ j x y z, d j x z ≤ d j x y + d j y z)
    (hδ : ∀ z ∈ U, ∀ j, d j (φ.func z) (ψ.func z) ≤ δ j)
    (hK : CoLipOn d φ U K) {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    (j : I) :
    (∑ i, K i j * d i x y) ≤
      d j (ψ.func x) (ψ.func y) + δ j + δ j :=
  (hK.2.2 x hx y hy j).trans
    (perturb_reverse d δ hs ht hδ hx hy j)

theorem scalar_inf_attained {φ : Operator X bot} {U : Set X} {i j : I}
    (hp : 0 < scalarInf d φ U i j)
    (hf : scalarInf d φ U i j < ⊤) :
    scalarInf d φ U i j ∈ ScalarFeasible d φ U i j := by
  obtain ⟨a, _, ha⟩ := (scalar_finite_iff d).mp hf
  intro x hx y hy
  by_cases hz : d i x y = 0
  · have h := ha x hx y hy
    simp only [hz, mul_zero] at h ⊢
    exact h
  by_cases ht : d i x y = ⊤
  · rw [ht, ENNReal.mul_top hp.ne']
    exact le_top
  · rw [scalarInf, sInf_eq_iInf', ENNReal.iInf_mul_of_ne hz ht]
    apply le_iInf
    intro b
    exact b.property x hx y hy

theorem sum_remove (L : Mat I) (i j : I) (x y : X) (h : L i j = 0) :
    (∑ k, L k j * d k x y) =
      ∑ k ∈ Finset.univ.erase i, L k j * d k x y := by
  have hs :=
    Finset.sum_erase_add (Finset.univ : Finset I)
      (fun k => L k j * d k x y) (Finset.mem_univ i)
  simpa [h] using hs.symm

theorem two_sided_all {φ : Operator X bot} {U : Set X} {L K : Mat I}
    (hL : LipOn d φ U L) (hK : CoLipOn d φ U K) (hdiag : Diagonal L) :
    ∀ j, ∀ x ∈ U, ∀ y ∈ U,
      K j j * d j x y ≤ d j (φ.func x) (φ.func y) ∧
      d j (φ.func x) (φ.func y) ≤ L j j * d j x y := by
  intro j x hx y hy
  exact two_sided d hL hK (fun k hk => hdiag k j hk) hx hy

theorem singleton_lip [Unique I] {φ : Operator X bot} {L : Mat I}
    (hL : LipOn d φ (dom φ) L) {x y : X}
    (hx : x ∈ dom φ) (hy : y ∈ dom φ) (i : I) :
    d i (φ.func x) (φ.func y) ≤ L i i * d i x y := by
  have hi : (default : I) = i := Subsingleton.elim _ _
  simpa [hi] using hL.2 x hx y hy i

theorem finite_two_sided {φ : Operator X bot} {U : Set X} {L K : Mat I}
    (hL : LipOn d φ U L) (hK : CoLipOn d φ U K) (hdiag : Diagonal L)
    (hfinite : ∀ j, L j j < ⊤ ∧ K j j < ⊤) :
    (∀ j, ∀ x ∈ U, ∀ y ∈ U,
      K j j * d j x y ≤ d j (φ.func x) (φ.func y) ∧
      d j (φ.func x) (φ.func y) ≤ L j j * d j x y) ∧
    (∀ j, L j j < ⊤ ∧ K j j < ⊤) :=
  ⟨two_sided_all d hL hK hdiag, hfinite⟩

noncomputable def matProduct : List (Mat I) → Mat I
  | [] => matId
  | A :: tail => matMul (matProduct tail) A

theorem matId_mul (A : Mat I) : matMul matId A = A := by
  funext i j
  simp only [matMul, matId]
  have hs : (∑ k, (if k = j then 1 else 0) * A i k) = A i j := by
    calc
      _ = (if j = j then 1 else 0) * A i j := by
        apply Finset.sum_eq_single j
        · intro k _ hkj
          simp [hkj]
        · simp
      _ = _ := by simp
  exact hs

theorem matProduct_nil : matProduct ([] : List (Mat I)) = matId := rfl

theorem matProduct_singleton (A : Mat I) : matProduct [A] = A :=
  matId_mul A

theorem comp_domain {φ ψ : Operator X bot} {U : Set X}
    (h : U ⊆ dom (comp ψ φ)) :
    U ⊆ dom φ ∧ φ.func '' U ⊆ dom ψ := by
  constructor
  · intro x hx hbot
    have hc := h hx
    apply hc
    change ψ.func (φ.func x) = bot
    rw [hbot, ψ.preserves_bot]
  · rintro z ⟨x, hx, rfl⟩
    exact h hx

theorem comp_image (φ ψ : Operator X bot) (U : Set X) :
    (comp ψ φ).func '' U = ψ.func '' (φ.func '' U) := by
  ext z
  simp only [Set.mem_image, comp, Function.comp_apply]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨φ.func x, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩

def chain : List (Operator X bot) → Operator X bot
  | [] => identity
  | φ :: fs => comp (chain fs) φ

def ChainLip : List (Operator X bot) → Set X → List (Mat I) → Prop
  | [], _, [] => True
  | φ :: fs, U, A :: As =>
      LipOn d φ U A ∧ ChainLip fs (φ.func '' U) As
  | _, _, _ => False

def ChainCoLip : List (Operator X bot) → Set X → List (Mat I) → Prop
  | [], _, [] => True
  | φ :: fs, U, A :: As =>
      CoLipOn d φ U A ∧ ChainCoLip fs (φ.func '' U) As
  | _, _, _ => False

theorem chain_lip (fs : List (Operator X bot)) :
    ∀ (U : Set X) (As : List (Mat I)),
    U ⊆ dom (chain fs) → ChainLip d fs U As →
    LipOn d (chain fs) U (matProduct As) := by
  induction fs with
  | nil =>
      intro U As hu h
      cases As with
      | nil => exact identity_lip d hu
      | cons A As => simp [ChainLip] at h
  | cons φ fs ih =>
      intro U As hu h
      cases As with
      | nil => simp [ChainLip] at h
      | cons A As =>
          change LipOn d φ U A ∧ ChainLip d fs (φ.func '' U) As at h
          have hd : φ.func '' U ⊆ dom (chain fs) := (comp_domain hu).2
          exact lip_comp d hu h.1 (ih _ _ hd h.2)

theorem chain_colip (fs : List (Operator X bot)) :
    ∀ (U : Set X) (As : List (Mat I)),
    U.Nonempty → U ⊆ dom (chain fs) → ChainCoLip d fs U As →
    CoLipOn d (chain fs) U (matProduct As) := by
  induction fs with
  | nil =>
      intro U As hn hu h
      cases As with
      | nil => exact identity_colip d hn hu
      | cons A As => simp [ChainCoLip] at h
  | cons φ fs ih =>
      intro U As hn hu h
      cases As with
      | nil => simp [ChainCoLip] at h
      | cons A As =>
          change CoLipOn d φ U A ∧
            ChainCoLip d fs (φ.func '' U) As at h
          have hd : φ.func '' U ⊆ dom (chain fs) := (comp_domain hu).2
          have hne : (φ.func '' U).Nonempty := hn.image φ.func
          exact colip_comp d hu h.1 (ih _ _ hne hd h.2)

def iterImage : List (Operator X bot) → Set X → Set X
  | [], U => U
  | φ :: fs, U => iterImage fs (φ.func '' U)

theorem chain_image (fs : List (Operator X bot)) :
    ∀ U : Set X, (chain fs).func '' U = iterImage fs U := by
  induction fs with
  | nil =>
      intro U
      simp [chain, identity, iterImage]
  | cons φ fs ih =>
      intro U
      change (comp (chain fs) φ).func '' U =
        iterImage fs (φ.func '' U)
      rw [comp_image, ih]

def ValidInputs : List (Operator X bot) → Set X → Prop
  | [], _ => True
  | φ :: fs, U => U ⊆ dom φ ∧ ValidInputs fs (φ.func '' U)

theorem chain_domains (fs : List (Operator X bot)) :
    ∀ U : Set X, U ⊆ dom (chain fs) → ValidInputs fs U := by
  induction fs with
  | nil => simp [ValidInputs]
  | cons φ fs ih =>
      intro U hu
      have hc := comp_domain hu
      exact ⟨hc.1, ih _ hc.2⟩

theorem chain_colip_nonempty
    {fs : List (Operator X bot)} {U : Set X} {As : List (Mat I)}
    (hfs : fs ≠ []) (hu : U ⊆ dom (chain fs))
    (h : ChainCoLip d fs U As) :
    CoLipOn d (chain fs) U (matProduct As) := by
  have hn : U.Nonempty := by
    cases fs with
    | nil => exact (hfs rfl).elim
    | cons φ fs =>
      cases As with
      | nil => simp [ChainCoLip] at h
      | cons A As => exact h.1.1
  exact chain_colip d fs U As hn hu h

end HCH02
```

```json filename=alignment.json
{
  "case_id": "HCH02",
  "version": "0.1.0",
  "items": [
    {"id":"HC02-D01","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.LipOn"},{"file":"Main.lean","name":"HCH02.Lip"},{"file":"Main.lean","name":"HCH02.Lips"}],"representation":"LipOn 包含 U⊆dom φ 和全部点对、输出指标的不等式；Lip 在 dom φ 上取值。指标有限；定义也适用于空指标类型，故覆盖原文非空情形。","dependencies":[]},
    {"id":"HC02-D02","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.CoLipOn"},{"file":"Main.lean","name":"HCH02.CoLips"}],"representation":"CoLipOn 包含 U 非空、U⊆dom φ 和全部点对的 ENNReal 下界。","dependencies":[]},
    {"id":"HC02-D03","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.Mat"},{"file":"Main.lean","name":"HCH02.display"},{"file":"Main.lean","name":"HCH02.matMul"}],"representation":"M i j 存输入 i 到输出 j；display M j i 显示该条目；matMul B A i j 是 Σk B k j * A i k。","dependencies":[]},
    {"id":"HC02-D04","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.matId"},{"file":"Main.lean","name":"HCH02.matProduct"},{"file":"Main.lean","name":"HCH02.matProduct_nil"},{"file":"Main.lean","name":"HCH02.matProduct_singleton"}],"representation":"列表按施行顺序记录矩阵；递归乘积将后一步放在左侧，空列表为单位矩阵，并证明单元素情形。","dependencies":["HC02-D03"]},
    {"id":"HC02-D05","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.chain"},{"file":"Main.lean","name":"HCH02.ChainLip"},{"file":"Main.lean","name":"HCH02.ChainCoLip"},{"file":"Main.lean","name":"HCH02.ValidInputs"},{"file":"Main.lean","name":"HCH02.chain_domains"},{"file":"Main.lean","name":"HCH02.iterImage"},{"file":"Main.lean","name":"HCH02.chain_image"}],"representation":"列表按实际施行次序递归复合；逐步证书谓词在每步的实际像域递归，不包含最终界字段。chain_domains 与 chain_image 分别证明各步域合法及总像等于逐次像。","dependencies":["HC02-D01","HC02-D02"]},
    {"id":"HC02-D06","status":"incomplete","declarations":[],"representation":"尚未构造全部有限中间指标路径及其权重、全正和含零谓词。","dependencies":[]},
    {"id":"HC02-D07","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.Channel"},{"file":"Main.lean","name":"HCH02.Row"},{"file":"Main.lean","name":"HCH02.Col"},{"file":"Main.lean","name":"HCH02.Diagonal"},{"file":"Main.lean","name":"HCH02.RowDecoupled"},{"file":"Main.lean","name":"HCH02.ColDecoupled"}],"representation":"Channel 是 I×I；Row、Col、Diagonal 使用输入优先存储，行列解耦量化合法 Lip 证书及可能的唯一支撑位置。","dependencies":["HC02-D01","HC02-D03"]},
    {"id":"HC02-D08","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.ScalarFeasible"},{"file":"Main.lean","name":"HCH02.scalarInf"},{"file":"Main.lean","name":"HCH02.scalar_inf_empty"}],"representation":"ScalarFeasible 是全部 U 内点对满足单输入分量界的 ENNReal 常数集合；scalarInf 为其下确界，空集时证明为 ∞。原文 U⊆dom φ 情形可直接特化。","dependencies":[]},
    {"id":"HC02-P01","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.singleton_lip"}],"representation":"Unique I 表示唯一指标，对 dom φ 上点对将有限和化为唯一对角项。","dependencies":["HC02-D01"]},
    {"id":"HC02-P02","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.global_restrict"}],"representation":"对任意 U⊆dom φ，将全域证书限制到 U。","dependencies":["HC02-D01","HC02-P03"]},
    {"id":"HC02-P03","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.lip_restrict"}],"representation":"U⊆V 时，V 上每个合法证书也是 U 上合法证书。","dependencies":["HC02-D01"]},
    {"id":"HC02-P04","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.entryInf"},{"file":"Main.lean","name":"HCH02.entryInf_antitone"}],"representation":"对证书族的指定条目取 sInf；由证书族包含关系得到 U 上下确界不大于 V 上下确界。","dependencies":["HC02-D01","HC02-P03"]},
    {"id":"HC02-P05","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.lip_comp"}],"representation":"第二步域是第一步对 U 的实际像，结论为复合算子在 U 上的 B·A 证书。","dependencies":["HC02-D01","HC02-D03"]},
    {"id":"HC02-P06","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.colip_zero"}],"representation":"全定义域上的 co-Lip 证书、输出零距和输入正距推出对应条目为零。","dependencies":["HC02-D02"]},
    {"id":"HC02-P07","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.colip_comp"}],"representation":"第二步使用实际像域；第一步证书提供 U 非空，所得乘积满足完整 co-Lip 定义。","dependencies":["HC02-D02","HC02-D03"]},
    {"id":"HC02-P08","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.perturb_forward"}],"representation":"使用对称性、三角不等式和 U 上逐点扰动，给出输出距加两个 δ 的界；结论对 U 无定义域限制，因而覆盖原前提。","dependencies":[]},
    {"id":"HC02-P09","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.perturb_reverse"}],"representation":"交换两个算子并由对称性重用正向扰动界。","dependencies":["HC02-P08"]},
    {"id":"HC02-P10","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.perturb_lip"}],"representation":"将 φ 的受限 Lip 界代入正向扰动界。","dependencies":["HC02-D01","HC02-P08"]},
    {"id":"HC02-P11","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.perturb_colip"}],"representation":"将 φ 的受限 co-Lip 界与反向扰动界相接。","dependencies":["HC02-D02","HC02-P09"]},
    {"id":"HC02-P12","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.chain_lip"}],"representation":"对施行顺序列表归纳，逐步证书取于递归实际像域，得到指定有序乘积的全复合证书；定理还覆盖零步。","dependencies":["HC02-D01","HC02-D04","HC02-D05","HC02-P05","HC02-P14"]},
    {"id":"HC02-P13","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.chain_colip_nonempty"}],"representation":"非空算子列表的逐步 co-Lip 证书自动提供起始域非空，归纳得到全复合的指定乘积证书。","dependencies":["HC02-D02","HC02-D04","HC02-D05","HC02-P07","HC02-P15"]},
    {"id":"HC02-P14","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.identity_lip"}],"representation":"恒等算子在任意合法 U 上有单位 Lip 证书，包含原文非空 U 情形。","dependencies":["HC02-D01","HC02-D04"]},
    {"id":"HC02-P15","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.identity_colip"}],"representation":"恒等算子在非空合法 U 上有单位 co-Lip 证书。","dependencies":["HC02-D02","HC02-D04"]},
    {"id":"HC02-P16","status":"incomplete","declarations":[],"representation":"尚未证明乘积零值与每条完整路径含零边的等价及单步特例。","dependencies":[]},
    {"id":"HC02-P17","status":"incomplete","declarations":[],"representation":"尚未证明乘积正值与存在全正完整路径的等价及单步特例。","dependencies":[]},
    {"id":"HC02-P18","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.scalar_infeasible"}],"representation":"输入零距而输出正距推出可行集为空且下确界为 ∞。","dependencies":["HC02-D08"]},
    {"id":"HC02-P19","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.scalar_inf_attained"}],"representation":"对每一 U 内点对区分输入距离为零、∞ 或有限非零；证明正有限下确界本身可行。","dependencies":["HC02-D08","HC02-P24"]},
    {"id":"HC02-P20","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.scalar_upward"}],"representation":"由 ENNReal 乘法单调性证明标量可行集向上封闭。","dependencies":["HC02-D08"]},
    {"id":"HC02-P21","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.scalar_above_inf"}],"representation":"证明任何严格大于下确界的 ENNReal 常数可行；覆盖原文正有限下确界和 λ=∞。","dependencies":["HC02-D08","HC02-P20"]},
    {"id":"HC02-P22","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.scalar_zero_inf"}],"representation":"下确界为零时证明每个严格正常数可行，强于只要求有限正常数。","dependencies":["HC02-P21"]},
    {"id":"HC02-P23","status":"incomplete","declarations":[],"representation":"尚未构造合法扩展规范空间和算子，使下确界为零但零不可行。","dependencies":[]},
    {"id":"HC02-P24","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.scalar_finite_iff"}],"representation":"下确界小于 ∞ 当且仅当可行集含有限 ENNReal 元素。","dependencies":["HC02-D08"]},
    {"id":"HC02-P25","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.zero_term"},{"file":"Main.lean","name":"HCH02.sum_remove"}],"representation":"零系数乘任意 ENNReal 距离为零，并证明可从有限和中删除该项。","dependencies":["HC02-D03"]},
    {"id":"HC02-P26","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.row_bound"}],"representation":"任意输入 i 支撑的输出 j 行化简为单项界，不要求 i=j。","dependencies":["HC02-D01","HC02-D07"]},
    {"id":"HC02-P27","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.col_term"}],"representation":"固定输入 i 的列仅可能在输出 j 非零时，其余输出的该输入项均为零。","dependencies":["HC02-D07"]},
    {"id":"HC02-P28","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.diagonal_bound"}],"representation":"将对角证书特化为各输出 j 的单行界。","dependencies":["HC02-D07","HC02-P26"]},
    {"id":"HC02-P29","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.two_sided"}],"representation":"仅要求 Lip 的 j 行保留对角输入；co-Lip 单项由非负和控制，得到双侧界。","dependencies":["HC02-D01","HC02-D02","HC02-D07","HC02-P26"]},
    {"id":"HC02-P30","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.two_sided_all"},{"file":"Main.lean","name":"HCH02.finite_two_sided"}],"representation":"对全部 j 同时给出双侧界，并给出附加对角系数有限前提下的有限系数分支。","dependencies":["HC02-D07","HC02-P29"]},
    {"id":"HC02-P31","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.positive_channel"}],"representation":"正 co-Lip 条目与正输入距的乘积严格正，并由下界传递到输出距。","dependencies":["HC02-D02"]},
    {"id":"HC02-P32","status":"complete","declarations":[{"file":"Main.lean","name":"HCH02.reflect_zero"}],"representation":"逐个对角通道应用正距保持，反证输入存在正距，从而反射全部分量零距关系。","dependencies":["HC02-P31"]}
  ]
}
```

未完成范围是有限指标路径的完整表示、乘积零值和正值的两个路径判据，以及零下确界不取到的具体反例。归属：Zhe Li（Glen Li / glenzli），[The Operator Evolution Theory](https://glenzli.com/books/oet/)，[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)；这里的 Lean 代码是对所给历史快照的形式化改写。