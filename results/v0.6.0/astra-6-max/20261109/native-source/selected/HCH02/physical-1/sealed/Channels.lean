import Bounds

namespace HCH02
noncomputable section
open formal_oet.vol_01.ch_01_foundations
open scoped BigOperators Classical

variable {X I : Type} {bot : X} [Fintype I] [Nonempty I]
  {d : I → X → X → ENNReal} {φ : Operator X bot}
  {U : Set X} {L K : Mat I}

abbrev Channel (I : Type) := I × I

def Row (L : Mat I) (i j : I) : Prop := ∀ k, k ≠ i → L k j = 0
def Col (L : Mat I) (i j : I) : Prop := ∀ k, k ≠ j → L i k = 0
def Diagonal (L : Mat I) : Prop := ∀ i j, i ≠ j → L i j = 0
def RowDecoupled (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X)
    (j : I) : Prop := ∃ L ∈ Lip d φ U, ∃ i, Row L i j
def ColDecoupled (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X)
    (i : I) : Prop := ∃ L ∈ Lip d φ U, ∃ j, Col L i j

theorem diagonal_iff_rows : Diagonal L ↔ ∀ j, Row L j j :=
  ⟨fun h j k hk => h k j hk, fun h i j hij => h j i hij⟩

theorem zero_term (i j : I) (h : L i j = 0) (v : I → ENNReal) : L i j * v i = 0 := by
  rw [h, zero_mul]

theorem erase_zero_term (i j : I) (h : L i j = 0) (v : I → ENNReal) :
    action L v j = ∑ k ∈ Finset.univ.erase i, L k j * v k := by
  simpa [action, h] using
    (Finset.sum_erase_add Finset.univ (fun k => L k j * v k) (Finset.mem_univ i)).symm

theorem row_action {i j : I} (h : Row L i j) (v : I → ENNReal) :
    action L v j = L i j * v i := by
  apply Finset.sum_eq_single i
  · intro k hk hki
    rw [h k hki, zero_mul]
  · simp

theorem row_lip (hL : L ∈ Lip d φ U) {i j : I} (hr : Row L i j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    d j (φ.func x) (φ.func y) ≤ L i j * d i x y := by
  simpa only [row_action hr] using hL.2 x hx y hy j

theorem col_contribution {i j : I} (hc : Col L i j) (v : I → ENNReal)
    (k : I) (hk : k ≠ j) : L i k * v i = 0 := zero_term i k (hc k hk) v

theorem diagonal_lip (hL : L ∈ Lip d φ U) (hD : Diagonal L)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (φ.func x) (φ.func y) ≤ L j j * d j x y :=
  row_lip hL (fun k hk => hD k j hk) hx hy

theorem scalar_two_sided (hL : L ∈ Lip d φ U) (hK : K ∈ CoLip d φ U)
    {j : I} (hr : Row L j j) {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    K j j * d j x y ≤ d j (φ.func x) (φ.func y) ∧
      d j (φ.func x) (φ.func y) ≤ L j j * d j x y :=
  ⟨colip_term hK hx hy j j, row_lip hL hr hx hy⟩

theorem diagonal_two_sided (hL : L ∈ Lip d φ U) (hK : K ∈ CoLip d φ U)
    (hD : Diagonal L) : ∀ j x, x ∈ U → ∀ y, y ∈ U →
      K j j * d j x y ≤ d j (φ.func x) (φ.func y) ∧
      d j (φ.func x) (φ.func y) ≤ L j j * d j x y :=
  fun j x hx y hy => scalar_two_sided hL hK (fun k hk => hD k j hk) hx hy

theorem finite_diagonal_two_sided (hL : L ∈ Lip d φ U) (hK : K ∈ CoLip d φ U)
    (hD : Diagonal L) (hfin : ∀ j, L j j < ⊤ ∧ K j j < ⊤) :
    ∀ j, L j j < ⊤ ∧ K j j < ⊤ ∧ ∀ x ∈ U, ∀ y ∈ U,
      K j j * d j x y ≤ d j (φ.func x) (φ.func y) ∧
      d j (φ.func x) (φ.func y) ≤ L j j * d j x y :=
  fun j => ⟨(hfin j).1, (hfin j).2, diagonal_two_sided hL hK hD j⟩

theorem positive_channel (hK : K ∈ CoLip d φ U) {i j : I} (hpos : 0 < K i j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (hin : 0 < d i x y) :
    0 < d j (φ.func x) (φ.func y) :=
  (ENNReal.mul_pos (ne_of_gt hpos) (ne_of_gt hin)).trans_le (colip_term hK hx hy i j)

theorem reflects_zero (hK : K ∈ CoLip d φ U) (hpos : ∀ j, 0 < K j j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    (hout : GaugeZeroRelated d (φ.func x) (φ.func y)) : GaugeZeroRelated d x y := by
  intro j
  by_contra hne
  have hp := positive_channel hK (hpos j) hx hy (pos_iff_ne_zero.mpr hne)
  simpa [hout j] using hp

def Scalars (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X)
    (i j : I) : Set ENNReal :=
  {a | ∀ x ∈ U, ∀ y ∈ U, d j (φ.func x) (φ.func y) ≤ a * d i x y}

def singleInf (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X)
    (i j : I) : ENNReal := sInf (Scalars d φ U i j)

theorem scalars_upward {i j : I} {a b : ENNReal}
    (ha : a ∈ Scalars d φ U i j) (hab : a ≤ b) : b ∈ Scalars d φ U i j :=
  fun x hx y hy => (ha x hx y hy).trans (mul_le_mul_left hab _)

theorem above_inf_feasible {i j : I} {a : ENNReal}
    (ha : singleInf d φ U i j < a) : a ∈ Scalars d φ U i j := by
  obtain ⟨b, hb, hba⟩ := sInf_lt_iff.mp ha
  exact scalars_upward hb hba.le

theorem zero_input_obstruction {i j : I} {x y : X}
    (hx : x ∈ U) (hy : y ∈ U) (hin : d i x y = 0)
    (hout : 0 < d j (φ.func x) (φ.func y)) :
    Scalars d φ U i j = ∅ ∧ singleInf d φ U i j = ⊤ := by
  have hempty : Scalars d φ U i j = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro a ha
    have h := ha x hx y hy
    rw [hin, mul_zero] at h
    exact (not_le_of_gt hout) h
  exact ⟨hempty, by simp [singleInf, hempty]⟩

theorem positive_finite_attained {i j : I}
    (hpos : 0 < singleInf d φ U i j) (hfin : singleInf d φ U i j < ⊤) :
    singleInf d φ U i j ∈ Scalars d φ U i j := by
  obtain ⟨b, hb, _⟩ := sInf_lt_iff.mp hfin
  letI : Nonempty (Scalars d φ U i j) := ⟨⟨b, hb⟩⟩
  intro x hx y hy
  change d j (φ.func x) (φ.func y) ≤ sInf (Scalars d φ U i j) * d i x y
  rw [sInf_eq_iInf']
  rw [ENNReal.iInf_mul (fun _ hz => ?_)]
  · exact le_iInf fun a => a.property x hx y hy
  · exact False.elim ((ne_of_gt hpos) (by simpa only [singleInf, sInf_eq_iInf'] using hz))

theorem zero_inf_positive_feasible {i j : I}
    (hzero : singleInf d φ U i j = 0) {a : ENNReal} (ha : 0 < a) (_hfin : a < ⊤) :
    a ∈ Scalars d φ U i j := above_inf_feasible (hzero ▸ ha)

theorem finite_inf_iff {i j : I} :
    singleInf d φ U i j < ⊤ ↔ ∃ a, a < ⊤ ∧ a ∈ Scalars d φ U i j := by
  constructor
  · intro h
    obtain ⟨a, ha, hfin⟩ := sInf_lt_iff.mp h
    exact ⟨a, hfin, ha⟩
  · rintro ⟨a, hfin, ha⟩
    exact (sInf_le ha).trans_lt hfin

end
end HCH02
