import OperatorBounds.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Fintype.Option

namespace HCH02

open formal_oet.vol_01.ch_01_foundations
open scoped BigOperators ENNReal NNReal

variable {X I : Type} {bot : X} {d : I → X → X → ℝ≥0∞}
variable {φ : Operator X bot} {U : Set X} {i j : I}

abbrev Channel (I : Type) := I × I

def RowSparse (L : BoundMatrix I) (i j : I) : Prop :=
  ∀ k ≠ i, L k j = 0

def ColumnSparse (L : BoundMatrix I) (i j : I) : Prop :=
  ∀ k ≠ j, L i k = 0

def Diagonal (L : BoundMatrix I) : Prop :=
  ∀ i j, i ≠ j → L i j = 0

def scalarFeasible (d : I → X → X → ℝ≥0∞) (φ : Operator X bot)
    (U : Set X) (i j : I) : Set ℝ≥0∞ :=
  {a | U ⊆ dom φ ∧ ∀ ⦃x y⦄, x ∈ U → y ∈ U →
    d j (φ.func x) (φ.func y) ≤ a * d i x y}

noncomputable def channelConstant (d : I → X → X → ℝ≥0∞) (φ : Operator X bot)
    (U : Set X) (i j : I) : ℝ≥0∞ :=
  sInf (scalarFeasible d φ U i j)

theorem channelConstant_of_empty (h : scalarFeasible d φ U i j = ∅) :
    channelConstant d φ U i j = ⊤ := by simp [channelConstant, h]

theorem scalar_infeasible_of_zero {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    (hin : d i x y = 0) (hout : 0 < d j (φ.func x) (φ.func y)) :
    scalarFeasible d φ U i j = ∅ ∧ channelConstant d φ U i j = ⊤ := by
  have hempty : scalarFeasible d φ U i j = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro a h
    have hxy := h.2 hx hy
    rw [hin, mul_zero] at hxy
    exact hout.not_ge hxy
  exact ⟨hempty, channelConstant_of_empty hempty⟩

theorem scalar_upward {a b : ℝ≥0∞} (ha : a ∈ scalarFeasible d φ U i j) (h : a ≤ b) :
    b ∈ scalarFeasible d φ U i j :=
  ⟨ha.1, fun x y hx hy => (ha.2 hx hy).trans (mul_le_mul_left h (d i x y))⟩

theorem scalar_above_inf {a : ℝ≥0∞} (h : channelConstant d φ U i j < a) :
    a ∈ scalarFeasible d φ U i j := by
  obtain ⟨b, hb, hba⟩ := sInf_lt_iff.mp h
  exact scalar_upward hb hba.le

theorem scalar_above_positive_finite_inf {a : ℝ≥0∞}
    (_hpos : 0 < channelConstant d φ U i j)
    (_hfin : channelConstant d φ U i j < ⊤)
    (h : channelConstant d φ U i j < a) : a ∈ scalarFeasible d φ U i j :=
  scalar_above_inf h

theorem scalar_of_zero_inf {a : ℝ≥0∞} (hzero : channelConstant d φ U i j = 0)
    (ha : 0 < a) (_haFin : a < ⊤) : a ∈ scalarFeasible d φ U i j :=
  scalar_above_inf (hzero.symm ▸ ha)

theorem scalar_attains_inf (hpos : 0 < channelConstant d φ U i j)
    (hfin : channelConstant d φ U i j < ⊤) :
    channelConstant d φ U i j ∈ scalarFeasible d φ U i j := by
  have htop := scalar_above_inf hfin
  refine ⟨htop.1, fun x y hx hy => ?_⟩
  rcases eq_or_ne (d i x y) 0 with hzero | hzero
  · simpa only [hzero, mul_zero] using htop.2 hx hy
  rcases eq_or_ne (d i x y) ⊤ with hinf | hinf
  · rw [hinf, ENNReal.mul_top hpos.ne']
    exact le_top
  have hdiv (a : ℝ≥0∞) :
      d j (φ.func x) (φ.func y) / d i x y ≤ a ↔
        d j (φ.func x) (φ.func y) ≤ a * d i x y :=
    ENNReal.div_le_iff_le_mul (Or.inl hzero) (Or.inl hinf)
  exact (hdiv _).mp (le_sInf fun a ha => (hdiv a).mpr (ha.2 hx hy))

theorem channelConstant_finite_iff :
    channelConstant d φ U i j < ⊤ ↔
      ∃ a < ⊤, a ∈ scalarFeasible d φ U i j := by
  constructor
  · intro h
    obtain ⟨a, ha, haFin⟩ := sInf_lt_iff.mp h
    exact ⟨a, haFin, ha⟩
  · rintro ⟨a, ha, hfeas⟩
    exact (sInf_le hfeas).trans_lt ha

private def exampleDist (i : Bool) (x y : Option Bool) : ℝ≥0∞ :=
  if x = y then 0 else if i = false ∨ x = none ∨ y = none then ⊤ else 1

private theorem exampleDist_metric (i : Bool) :
    ExtendedPseudoMetric (Option Bool) none (exampleDist i) := by
  constructor
  · exact ⟨some false, by simp⟩
  · intro x
    simp [exampleDist]
  · intro x y
    simp [exampleDist, eq_comm, or_comm]
  · intro x y z
    fin_cases i <;> fin_cases x <;> fin_cases y <;> fin_cases z <;> simp [exampleDist]
  · intro x hx
    simp [exampleDist, hx]

theorem zero_inf_not_attained :
    ∃ (e : Bool → Option Bool → Option Bool → ℝ≥0∞)
      (ψ : Operator (Option Bool) none) (V : Set (Option Bool)),
      (∀ k, ExtendedPseudoMetric (Option Bool) none (e k)) ∧
      V.Nonempty ∧ V ⊆ dom ψ ∧ channelConstant e ψ V false true = 0 ∧
      (0 : ℝ≥0∞) ∉ scalarFeasible e ψ V false true := by
  let ψ : Operator (Option Bool) none := identityOp
  have hx : some false ∈ dom ψ := by
    change some false ≠ none
    simp
  have hy : some true ∈ dom ψ := by
    change some true ≠ none
    simp
  have hpositive (a : ℝ≥0∞) (ha : 0 < a) :
      a ∈ scalarFeasible exampleDist ψ (dom ψ) false true := by
    refine ⟨Set.Subset.rfl, fun x y _ _ => ?_⟩
    change exampleDist true x y ≤ a * exampleDist false x y
    by_cases h : x = y
    · simp [exampleDist, h]
    · simp [exampleDist, h, ENNReal.mul_top ha.ne']
  refine ⟨exampleDist, ψ, dom ψ, exampleDist_metric, ⟨_, hx⟩, Set.Subset.rfl, ?_, ?_⟩
  · apply le_antisymm _ (zero_le _)
    by_contra! h
    obtain ⟨a, ha, hainf⟩ := exists_between h
    exact hainf.not_ge (sInf_le (hpositive a ha))
  · intro h
    have hxy := h.2 hx hy
    change exampleDist true (some false) (some true) ≤
      0 * exampleDist false (some false) (some true) at hxy
    simp [exampleDist] at hxy

variable [Fintype I]

def RowDecoupled (d : I → X → X → ℝ≥0∞) (φ : Operator X bot) (U : Set X) (j : I) : Prop :=
  ∃ L ∈ lipOn d φ U, ∃ i, RowSparse L i j

def ColumnDecoupled (d : I → X → X → ℝ≥0∞) (φ : Operator X bot) (U : Set X) (i : I) : Prop :=
  ∃ L ∈ lipOn d φ U, ∃ j, ColumnSparse L i j

def FullyDecoupled (d : I → X → X → ℝ≥0∞) (φ : Operator X bot)
    (U : Set X) (L : BoundMatrix I) : Prop :=
  L ∈ lipOn d φ U ∧ Diagonal L

variable {L K : BoundMatrix I} {x y : X}

omit [Fintype I] in
theorem zero_channel_term (d : I → X → X → ℝ≥0∞) (hz : L i j = 0) (x y : X) :
    L i j * d i x y = 0 := by simp [hz]

open scoped Classical in
theorem erase_zero_channel (hz : L i j = 0) :
    weightedDistance d L x y j = ∑ k ∈ Finset.univ.erase i, L k j * d k x y := by
  unfold weightedDistance
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), zero_channel_term d hz, add_zero]

theorem lip_of_sparse_row (hL : L ∈ lipOn d φ U) (hrow : RowSparse L i j)
    (hx : x ∈ U) (hy : y ∈ U) :
    d j (φ.func x) (φ.func y) ≤ L i j * d i x y := by
  have heq : weightedDistance d L x y j = L i j * d i x y :=
    Finset.sum_eq_single i (fun k _ hk => zero_channel_term d (hrow k hk) x y)
      (fun h => (h (Finset.mem_univ i)).elim)
  exact (hL.2 hx hy j).trans_eq heq

omit [Fintype I] in
theorem column_contributions (d : I → X → X → ℝ≥0∞) (hcol : ColumnSparse L i j)
    (x y : X) (k : I) (hk : k ≠ j) :
    L i k * d i x y = 0 :=
  zero_channel_term d (hcol k hk) x y

theorem lip_of_diagonal (hL : L ∈ lipOn d φ U) (hdiag : Diagonal L)
    (j : I) (hx : x ∈ U) (hy : y ∈ U) :
    d j (φ.func x) (φ.func y) ≤ L j j * d j x y :=
  lip_of_sparse_row hL (fun k hk => hdiag k j hk) hx hy

theorem diagonal_row_two_sided (hL : L ∈ lipOn d φ U) (hK : K ∈ coLipOn d φ U)
    (hrow : RowSparse L j j) (hx : x ∈ U) (hy : y ∈ U) :
    K j j * d j x y ≤ d j (φ.func x) (φ.func y) ∧
      d j (φ.func x) (φ.func y) ≤ L j j * d j x y :=
  ⟨coLip_channel_bound hK hx hy j j, lip_of_sparse_row hL hrow hx hy⟩

theorem all_diagonal_two_sided (hL : L ∈ lipOn d φ U) (hK : K ∈ coLipOn d φ U)
    (hdiag : Diagonal L) :
    ∀ j x y, x ∈ U → y ∈ U →
      K j j * d j x y ≤ d j (φ.func x) (φ.func y) ∧
        d j (φ.func x) (φ.func y) ≤ L j j * d j x y :=
  fun j _ _ hx hy => diagonal_row_two_sided hL hK (fun k hk => hdiag k j hk) hx hy

theorem finite_diagonal_two_sided (hL : L ∈ lipOn d φ U) (hK : K ∈ coLipOn d φ U)
    (hdiag : Diagonal L) (hfin : ∀ j, L j j < ⊤ ∧ K j j < ⊤) :
    ∃ l k : I → ℝ≥0,
      (∀ j, (l j : ℝ≥0∞) = L j j ∧ (k j : ℝ≥0∞) = K j j) ∧
      ∀ j x y, x ∈ U → y ∈ U →
        (k j : ℝ≥0∞) * d j x y ≤ d j (φ.func x) (φ.func y) ∧
          d j (φ.func x) (φ.func y) ≤ (l j : ℝ≥0∞) * d j x y := by
  have hl (j : I) := ENNReal.coe_toNNReal (hfin j).1.ne
  have hk (j : I) := ENNReal.coe_toNNReal (hfin j).2.ne
  refine ⟨fun j => (L j j).toNNReal, fun j => (K j j).toNNReal,
    fun j => ⟨hl j, hk j⟩, fun j x y hx hy => ?_⟩
  rw [hl, hk]
  exact all_diagonal_two_sided hL hK hdiag j x y hx hy

theorem coLip_preserves_positive (hK : K ∈ coLipOn d φ U)
    (hpos : 0 < K i j) (hx : x ∈ U) (hy : y ∈ U) (hin : 0 < d i x y) :
    0 < d j (φ.func x) (φ.func y) :=
  (pos_iff_ne_zero.mpr (mul_ne_zero hpos.ne' hin.ne')).trans_le
    (coLip_channel_bound hK hx hy i j)

theorem coLip_reflects_gauge_zero (hK : K ∈ coLipOn d φ U)
    (hpos : ∀ j, 0 < K j j) (hx : x ∈ U) (hy : y ∈ U)
    (hout : GaugeZeroRelated d (φ.func x) (φ.func y)) : GaugeZeroRelated d x y := by
  intro j
  by_contra h
  exact (coLip_preserves_positive hK (hpos j) hx hy (pos_iff_ne_zero.mpr h)).ne' (hout j)

end HCH02
