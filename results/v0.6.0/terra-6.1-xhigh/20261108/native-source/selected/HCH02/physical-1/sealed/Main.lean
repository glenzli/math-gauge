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
def Lip (φ : Operator X bot) : Set (Mat I) := {L | LipOn d φ (dom φ) L}
def Lips (φ : Operator X bot) (U : Set X) : Set (Mat I) := {L | LipOn d φ U L}
def CoLipOn (φ : Operator X bot) (U : Set X) (K : Mat I) : Prop :=
  U.Nonempty ∧ U ⊆ dom φ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j,
    (∑ i, K i j * d i x y) ≤ d j (φ.func x) (φ.func y)
def CoLips (φ : Operator X bot) (U : Set X) : Set (Mat I) := {K | CoLipOn d φ U K}
noncomputable def matMul (B A : Mat I) : Mat I := fun i j => ∑ k, B k j * A i k
def display (M : Mat I) : I → I → ENNReal := fun j i => M i j
def matId : Mat I := fun i j => if i = j then 1 else 0
def Row (L : Mat I) (i j : I) : Prop := ∀ k, k ≠ i → L k j = 0
def Col (L : Mat I) (i j : I) : Prop := ∀ k, k ≠ j → L i k = 0
def Diagonal (L : Mat I) : Prop := ∀ i j, i ≠ j → L i j = 0
def RowDecoupled (φ : Operator X bot) (U : Set X) (j : I) : Prop :=
  ∃ L, LipOn d φ U L ∧ ∃ i, Row L i j
def ColDecoupled (φ : Operator X bot) (U : Set X) (i : I) : Prop :=
  ∃ L, LipOn d φ U L ∧ ∃ j, Col L i j
def ScalarFeasible (φ : Operator X bot) (U : Set X) (i j : I) : Set ENNReal :=
  {a | ∀ x ∈ U, ∀ y ∈ U, d j (φ.func x) (φ.func y) ≤ a * d i x y}
noncomputable def scalarInf (φ : Operator X bot) (U : Set X) (i j : I) : ENNReal :=
  sInf (ScalarFeasible d φ U i j)
noncomputable def entryInf (φ : Operator X bot) (U : Set X) (i j : I) : ENNReal :=
  sInf ((fun M : Mat I => M i j) '' Lips d φ U)
theorem lip_restrict {φ : Operator X bot} {U V : Set X} {L : Mat I}
    (hUV : U ⊆ V) (h : LipOn d φ V L) : LipOn d φ U L := by
  refine ⟨hUV.trans h.1, ?_⟩
  intro x hx y hy j
  exact h.2 x (hUV hx) y (hUV hy) j
theorem global_restrict {φ : Operator X bot} {U : Set X} (hU : U ⊆ dom φ) :
    Lip d φ ⊆ Lips d φ U := by
  intro L h
  exact lip_restrict d hU h
theorem entryInf_antitone {φ : Operator X bot} {U V : Set X} (hUV : U ⊆ V) (i j : I) :
    entryInf d φ U i j ≤ entryInf d φ V i j := by
  apply sInf_le_sInf
  rintro a ⟨M, hM, rfl⟩
  exact ⟨M, lip_restrict d hUV hM, rfl⟩
theorem scalar_upward {φ : Operator X bot} {U : Set X} {i j : I} {a b : ENNReal}
    (ha : a ∈ ScalarFeasible d φ U i j) (hab : a ≤ b) : b ∈ ScalarFeasible d φ U i j := by
  intro x hx y hy
  exact (ha x hx y hy).trans (mul_le_mul_right' hab _)
theorem scalar_above_inf {φ : Operator X bot} {U : Set X} {i j : I} {a : ENNReal}
    (ha : scalarInf d φ U i j < a) : a ∈ ScalarFeasible d φ U i j := by
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
    scalarInf d φ U i j < ⊤ ↔ ∃ a < ⊤, a ∈ ScalarFeasible d φ U i j := by
  constructor
  · intro h
    obtain ⟨a, ha, hlt⟩ : ∃ a ∈ ScalarFeasible d φ U i j, a < ⊤ := by
      by_contra hn
      push_neg at hn
      have ht : ⊤ ≤ scalarInf d φ U i j := le_sInf hn
      exact (not_le_of_gt h) ht
    exact ⟨a, hlt, ha⟩
  · rintro ⟨a, ha, hm⟩
    exact lt_of_le_of_lt (sInf_le hm) ha
theorem scalar_inf_empty {φ : Operator X bot} {U : Set X} {i j : I}
    (h : ScalarFeasible d φ U i j = ∅) : scalarInf d φ U i j = ⊤ := by
  simp [scalarInf, h]
theorem scalar_infeasible {φ : Operator X bot} {U : Set X} {i j : I} {x y : X}
    (hx : x ∈ U) (hy : y ∈ U) (hzero : d i x y = 0)
    (hpos : 0 < d j (φ.func x) (φ.func y)) :
    ScalarFeasible d φ U i j = ∅ ∧ scalarInf d φ U i j = ⊤ := by
  have he : ScalarFeasible d φ U i j = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro a ha
    have h := ha x hx y hy
    rw [hzero, mul_zero] at h
    exact (not_le_of_gt hpos) h
  exact ⟨he, by simp [scalarInf, he]⟩
theorem zero_term (L : Mat I) (i j : I) (x y : X) (h : L i j = 0) :
    L i j * d i x y = 0 := by simp [h]
theorem row_bound {φ : Operator X bot} {U : Set X} {L : Mat I} {i j : I}
    (hL : LipOn d φ U L) (hrow : Row L i j) {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    d j (φ.func x) (φ.func y) ≤ L i j * d i x y := by
  have hs : (∑ k, L k j * d k x y) = L i j * d i x y := by
    apply Finset.sum_eq_single i
    · intro k _ hki
      simp [hrow k hki]
    · simp
  simpa [hs] using hL.2 x hx y hy j
theorem col_term {L : Mat I} {i j k : I} (h : Col L i j) (hk : k ≠ j) (x y : X) :
    L i k * d i x y = 0 := by simp [h k hk]
theorem diagonal_bound {φ : Operator X bot} {U : Set X} {L : Mat I}
    (hL : LipOn d φ U L) (hdiag : Diagonal L) {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (φ.func x) (φ.func y) ≤ L j j * d j x y :=
  row_bound d hL (fun k hk => hdiag k j hk) hx hy
theorem colip_term {φ : Operator X bot} {U : Set X} {K : Mat I}
    (hK : CoLipOn d φ U K) {x y : X} (hx : x ∈ U) (hy : y ∈ U) (i j : I) :
    K i j * d i x y ≤ d j (φ.func x) (φ.func y) := by
  exact (Finset.single_le_sum (fun k _ => zero_le (K k j * d k x y)) (Finset.mem_univ i)).trans
    (hK.2.2 x hx y hy j)
theorem two_sided {φ : Operator X bot} {U : Set X} {L K : Mat I} {j : I}
    (hL : LipOn d φ U L) (hK : CoLipOn d φ U K) (hrow : Row L j j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    K j j * d j x y ≤ d j (φ.func x) (φ.func y) ∧
      d j (φ.func x) (φ.func y) ≤ L j j * d j x y :=
  ⟨colip_term d hK hx hy j j, row_bound d hL hrow hx hy⟩
theorem positive_channel {φ : Operator X bot} {U : Set X} {K : Mat I} {i j : I}
    (hK : CoLipOn d φ U K) (hk : 0 < K i j) {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    (hd : 0 < d i x y) : 0 < d j (φ.func x) (φ.func y) :=
  lt_of_lt_of_le (ENNReal.mul_pos hk.ne' hd.ne') (colip_term d hK hx hy i j)
theorem reflect_zero {φ : Operator X bot} {U : Set X} {K : Mat I}
    (hK : CoLipOn d φ U K) (hk : ∀ j, 0 < K j j) {x y : X}
    (hx : x ∈ U) (hy : y ∈ U) (hzero : GaugeZeroRelated d (φ.func x) (φ.func y)) :
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
    (hb : LipOn d ψ (φ.func '' U) B) : LipOn d (comp ψ φ) U (matMul B A) := by
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
    _ = ∑ i, (matMul B A) i j * d i x y := sum_product A B (fun i => d i x y) j

theorem colip_comp {φ ψ : Operator X bot} {U : Set X} {A B : Mat I}
    (hu : U ⊆ dom (comp ψ φ)) (ha : CoLipOn d φ U A)
    (hb : CoLipOn d ψ (φ.func '' U) B) : CoLipOn d (comp ψ φ) U (matMul B A) := by
  refine ⟨ha.1, hu, ?_⟩
  intro x hx y hy j
  calc
    (∑ i, (matMul B A) i j * d i x y) =
        ∑ k, B k j * (∑ i, A i k * d i x y) := (sum_product A B (fun i => d i x y) j).symm
    _ ≤ ∑ k, B k j * d k (φ.func x) (φ.func y) := by
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_left' (ha.2.2 x hx y hy k) _
    _ ≤ d j ((comp ψ φ).func x) ((comp ψ φ).func y) :=
      hb.2.2 (φ.func x) ⟨x, hx, rfl⟩ (φ.func y) ⟨y, hy, rfl⟩ j

theorem colip_zero {φ : Operator X bot} {K : Mat I} {i j : I} {x y : X}
    (hK : CoLipOn d φ (dom φ) K) (hx : x ∈ dom φ) (hy : y ∈ dom φ)
    (hz : d j (φ.func x) (φ.func y) = 0) (hp : 0 < d i x y) : K i j = 0 := by
  have h := colip_term d hK hx hy i j
  rw [hz] at h
  have hz' : K i j * d i x y = 0 := le_antisymm h (zero_le _)
  exact (mul_eq_zero.mp hz').resolve_right hp.ne'

theorem identity_sum (x y : X) (j : I) :
    (∑ i, matId i j * d i x y) = d j x y := by
  classical
  simp [matId]

theorem identity_lip {U : Set X} (hU : U ⊆ dom (identity : Operator X bot)) :
    LipOn d (identity : Operator X bot) U matId := by
  refine ⟨hU, ?_⟩
  intro x hx y hy j
  simp [identity, identity_sum]

theorem identity_colip {U : Set X} (hn : U.Nonempty)
    (hU : U ⊆ dom (identity : Operator X bot)) : CoLipOn d (identity : Operator X bot) U matId := by
  refine ⟨hn, hU, ?_⟩
  intro x hx y hy j
  simp [identity, identity_sum]

theorem perturb_forward {φ ψ : Operator X bot} {U : Set X} (δ : I → ENNReal)
    (hs : ∀ j x y, d j x y = d j y x)
    (ht : ∀ j x y z, d j x z ≤ d j x y + d j y z)
    (hδ : ∀ z ∈ U, ∀ j, d j (φ.func z) (ψ.func z) ≤ δ j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (ψ.func x) (ψ.func y) ≤ d j (φ.func x) (φ.func y) + δ j + δ j := by
  calc
    d j (ψ.func x) (ψ.func y) ≤ d j (ψ.func x) (φ.func x) + d j (φ.func x) (ψ.func y) := ht j _ _ _
    _ ≤ d j (ψ.func x) (φ.func x) + (d j (φ.func x) (φ.func y) + d j (φ.func y) (ψ.func y)) := by gcongr; exact ht j _ _ _
    _ ≤ δ j + (d j (φ.func x) (φ.func y) + δ j) := by
      apply add_le_add
      · rw [hs j]; exact hδ x hx j
      · gcongr; exact hδ y hy j
    _ = d j (φ.func x) (φ.func y) + δ j + δ j := by simp [add_comm, add_left_comm, add_assoc]

theorem perturb_reverse {φ ψ : Operator X bot} {U : Set X} (δ : I → ENNReal)
    (hs : ∀ j x y, d j x y = d j y x)
    (ht : ∀ j x y z, d j x z ≤ d j x y + d j y z)
    (hδ : ∀ z ∈ U, ∀ j, d j (φ.func z) (ψ.func z) ≤ δ j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (φ.func x) (φ.func y) ≤ d j (ψ.func x) (ψ.func y) + δ j + δ j := by
  apply perturb_forward d δ hs ht _ hx hy j
  intro z hz k
  rw [hs k]
  exact hδ z hz k

theorem perturb_lip {φ ψ : Operator X bot} {U : Set X} {L : Mat I} (δ : I → ENNReal)
    (hs : ∀ j x y, d j x y = d j y x)
    (ht : ∀ j x y z, d j x z ≤ d j x y + d j y z)
    (hδ : ∀ z ∈ U, ∀ j, d j (φ.func z) (ψ.func z) ≤ δ j)
    (hL : LipOn d φ U L) {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (ψ.func x) (ψ.func y) ≤ (∑ i, L i j * d i x y) + δ j + δ j :=
  (perturb_forward d δ hs ht hδ hx hy j).trans (by gcongr; exact hL.2 x hx y hy j)

theorem perturb_colip {φ ψ : Operator X bot} {U : Set X} {K : Mat I} (δ : I → ENNReal)
    (hs : ∀ j x y, d j x y = d j y x)
    (ht : ∀ j x y z, d j x z ≤ d j x y + d j y z)
    (hδ : ∀ z ∈ U, ∀ j, d j (φ.func z) (ψ.func z) ≤ δ j)
    (hK : CoLipOn d φ U K) {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    (∑ i, K i j * d i x y) ≤ d j (ψ.func x) (ψ.func y) + δ j + δ j :=
  (hK.2.2 x hx y hy j).trans (perturb_reverse d δ hs ht hδ hx hy j)



theorem scalar_inf_attained {φ : Operator X bot} {U : Set X} {i j : I}
    (hp : 0 < scalarInf d φ U i j) (hf : scalarInf d φ U i j < ⊤) :
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
    (∑ k, L k j * d k x y) = ∑ k ∈ Finset.univ.erase i, L k j * d k x y := by
  have hs := Finset.sum_erase_add (Finset.univ : Finset I) (fun k => L k j * d k x y) (Finset.mem_univ i)
  simpa [h] using hs.symm

theorem two_sided_all {φ : Operator X bot} {U : Set X} {L K : Mat I}
    (hL : LipOn d φ U L) (hK : CoLipOn d φ U K) (hdiag : Diagonal L) :
    ∀ j, ∀ x ∈ U, ∀ y ∈ U, K j j * d j x y ≤ d j (φ.func x) (φ.func y) ∧
      d j (φ.func x) (φ.func y) ≤ L j j * d j x y := by
  intro j x hx y hy
  exact two_sided d hL hK (fun k hk => hdiag k j hk) hx hy

theorem singleton_lip [Unique I] {φ : Operator X bot} {L : Mat I} (hL : LipOn d φ (dom φ) L)
    {x y : X} (hx : x ∈ dom φ) (hy : y ∈ dom φ) (i : I) :
    d i (φ.func x) (φ.func y) ≤ L i i * d i x y := by
  have hi : (default : I) = i := Subsingleton.elim _ _
  simpa [hi] using hL.2 x hx y hy i



theorem finite_two_sided {φ : Operator X bot} {U : Set X} {L K : Mat I}
    (hL : LipOn d φ U L) (hK : CoLipOn d φ U K) (hdiag : Diagonal L)
    (hfinite : ∀ j, L j j < ⊤ ∧ K j j < ⊤) :
    (∀ j, ∀ x ∈ U, ∀ y ∈ U, K j j * d j x y ≤ d j (φ.func x) (φ.func y) ∧
      d j (φ.func x) (φ.func y) ≤ L j j * d j x y) ∧
    (∀ j, L j j < ⊤ ∧ K j j < ⊤) := ⟨two_sided_all d hL hK hdiag, hfinite⟩

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
theorem matProduct_singleton (A : Mat I) : matProduct [A] = A := matId_mul A

theorem comp_domain {φ ψ : Operator X bot} {U : Set X} (h : U ⊆ dom (comp ψ φ)) :
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
  | φ :: fs, U, A :: As => LipOn d φ U A ∧ ChainLip fs (φ.func '' U) As
  | _, _, _ => False

def ChainCoLip : List (Operator X bot) → Set X → List (Mat I) → Prop
  | [], _, [] => True
  | φ :: fs, U, A :: As => CoLipOn d φ U A ∧ ChainCoLip fs (φ.func '' U) As
  | _, _, _ => False

theorem chain_lip (fs : List (Operator X bot)) : ∀ (U : Set X) (As : List (Mat I)),
    U ⊆ dom (chain fs) → ChainLip d fs U As → LipOn d (chain fs) U (matProduct As) := by
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

theorem chain_colip (fs : List (Operator X bot)) : ∀ (U : Set X) (As : List (Mat I)),
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
          change CoLipOn d φ U A ∧ ChainCoLip d fs (φ.func '' U) As at h
          have hd : φ.func '' U ⊆ dom (chain fs) := (comp_domain hu).2
          have hne : (φ.func '' U).Nonempty := hn.image φ.func
          exact colip_comp d hu h.1 (ih _ _ hne hd h.2)

def iterImage : List (Operator X bot) → Set X → Set X
  | [], U => U
  | φ :: fs, U => iterImage fs (φ.func '' U)

theorem chain_image (fs : List (Operator X bot)) : ∀ U : Set X,
    (chain fs).func '' U = iterImage fs U := by
  induction fs with
  | nil => intro U; simp [chain, identity, iterImage]
  | cons φ fs ih =>
      intro U
      change (comp (chain fs) φ).func '' U = iterImage fs (φ.func '' U)
      rw [comp_image, ih]



def ValidInputs : List (Operator X bot) → Set X → Prop
  | [], _ => True
  | φ :: fs, U => U ⊆ dom φ ∧ ValidInputs fs (φ.func '' U)

theorem chain_domains (fs : List (Operator X bot)) : ∀ U : Set X,
    U ⊆ dom (chain fs) → ValidInputs fs U := by
  induction fs with
  | nil => simp [ValidInputs]
  | cons φ fs ih =>
      intro U hu
      have hc := comp_domain hu
      exact ⟨hc.1, ih _ hc.2⟩

theorem chain_colip_nonempty {fs : List (Operator X bot)} {U : Set X} {As : List (Mat I)}
    (hfs : fs ≠ []) (hu : U ⊆ dom (chain fs)) (h : ChainCoLip d fs U As) :
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
