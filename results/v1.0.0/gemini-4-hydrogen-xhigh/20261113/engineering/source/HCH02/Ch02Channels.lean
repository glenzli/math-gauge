import Ch02Certificates

/-!
# Chapter 2 — Channel Decoupling, Single-Channel Lip Constants, Bilateral Bounds, and Reflection

Formalizes obligations `HC02-D07` (decoupling predicates), `HC02-D08`, and
`HC02-P18` through `HC02-P32` from `source/02-operator-bounds.md`.
-/

namespace formal_oet.vol_01.ch_02_operator_bounds

open formal_oet.vol_01.ch_01_foundations

/-! ### Channel decoupling predicates (HC02-D07) -/

/-- Row decoupling of `ϕ` on `U` with respect to output component `j`:
there exists a restricted Lip certificate `L ∈ LipRestricted d ϕ U` whose `j`-th row
has at most one nonzero entry (at some input `i`). -/
def IsRowDecoupledAt {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (j : I) : Prop :=
  ∃ L ∈ LipRestricted d ϕ U, ∃ i : I, RowSparseAt L i j

/-- Column decoupling of `ϕ` on `U` with respect to input component `i`:
there exists a restricted Lip certificate `L ∈ LipRestricted d ϕ U` whose `i`-th column
has at most one nonzero entry (at some output `j`). -/
def IsColDecoupledAt {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i : I) : Prop :=
  ∃ L ∈ LipRestricted d ϕ U, ∃ j : I, ColSparseAt L i j

/-- A certificate `L` yields a fully decoupled system for `ϕ` on `U` when `L` is
a diagonal matrix in `LipRestricted d ϕ U`. -/
def IsFullyDecoupledCert {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (L : GaugeMatrix I) : Prop :=
  L ∈ LipRestricted d ϕ U ∧ IsDiagMatrix L

/-- `ϕ` admits a fully decoupled system certificate on `U`. -/
def IsFullyDecoupled {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) : Prop :=
  ∃ L : GaugeMatrix I, IsFullyDecoupledCert d ϕ U L

/-! ### Single-channel feasible scalar set and infimum (HC02-D08, HC02-P18 to HC02-P24) -/

/-- Set $S_{i \to j}(\phi; U)$ of feasible scalar Lipschitz constants $\lambda \in \bar{\mathbb{R}}_+$
along channel `(i, j)` on domain $U \subseteq \mathrm{dom}(\phi)$. -/
def singleChannelFeasible {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i j : I) : Set ENNReal :=
  { l : ENNReal | ∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ l * d i x y }

/-- Single-channel Lipschitz constant $\underline{L}_{i \to j}(\phi; U) := \inf S_{i \to j}(\phi; U)$
with `sInf ∅ = ⊤`. -/
noncomputable def singleChannelLip {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i j : I) : ENNReal :=
  sInf (singleChannelFeasible d ϕ U i j)

/-- **HC02-P18**: If there exist $x, y \in U$ with $d_i(x, y) = 0 < d_j(\phi(x), \phi(y))$,
then the feasible scalar set is empty and $\underline{L}_{i \to j}(\phi; U) = +\infty$. -/
theorem singleChannelFeasible_eq_empty_of_zero_pos {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X} {i j : I}
    {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    (hin : d i x y = 0) (hout : 0 < d j (ϕ.func x) (ϕ.func y)) :
    singleChannelFeasible d ϕ U i j = ∅ := by
  ext l
  simp only [singleChannelFeasible, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro hl
  have hle := hl x hx y hy
  rw [hin, mul_zero] at hle
  exact absurd hle (not_le_of_gt hout)

theorem singleChannelLip_eq_top_of_zero_pos {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X} {i j : I}
    {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    (hin : d i x y = 0) (hout : 0 < d j (ϕ.func x) (ϕ.func y)) :
    singleChannelLip d ϕ U i j = ⊤ := by
  rw [singleChannelLip, singleChannelFeasible_eq_empty_of_zero_pos d ϕ hx hy hin hout, sInf_empty]

/-- **HC02-P20**: The feasible scalar set is upward closed. -/
theorem singleChannelFeasible_upward_closed {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X} {i j : I}
    {l₀ l₁ : ENNReal}
    (h0 : l₀ ∈ singleChannelFeasible d ϕ U i j) (hle : l₀ ≤ l₁) :
    l₁ ∈ singleChannelFeasible d ϕ U i j := by
  intro x hx y hy
  calc
    d j (ϕ.func x) (ϕ.func y) ≤ l₀ * d i x y := h0 x hx y hy
    _ ≤ l₁ * d i x y := by gcongr

/-- General form of **HC02-P21**: Every `l > singleChannelLip` (including `l = ⊤`) is feasible. -/
theorem singleChannelLip_lt_mem_feasible {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X} {i j : I}
    {l : ENNReal} (hl : singleChannelLip d ϕ U i j < l) :
    l ∈ singleChannelFeasible d ϕ U i j := by
  have hex : ∃ l₀ ∈ singleChannelFeasible d ϕ U i j, l₀ < l := by
    by_contra hno
    push Not at hno
    have hle : l ≤ singleChannelLip d ϕ U i j := le_sInf hno
    exact absurd hl (not_lt_of_ge hle)
  rcases hex with ⟨l₀, hl₀, hlt⟩
  exact singleChannelFeasible_upward_closed d ϕ hl₀ (le_of_lt hlt)

/-- **HC02-P21**: In the positive finite infimum regime $0 < a < +\infty$, every $\lambda > a$
(including $\lambda = +\infty$) belongs to the feasible scalar set. -/
theorem singleChannelLip_gt_mem_feasible_of_pos_lt_top {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X} {i j : I}
    (_hpos : 0 < singleChannelLip d ϕ U i j) (_hlt : singleChannelLip d ϕ U i j < ⊤)
    {l : ENNReal} (hl : singleChannelLip d ϕ U i j < l) :
    l ∈ singleChannelFeasible d ϕ U i j :=
  singleChannelLip_lt_mem_feasible d ϕ hl

/-- **HC02-P19**: When $0 < \underline{L}_{i \to j}(\phi; U) < +\infty$, the infimum itself
belongs to $S_{i \to j}(\phi; U)$, i.e. the scalar bound holds for $a = \underline{L}_{i \to j}(\phi; U)$. -/
theorem singleChannelLip_mem_feasible_of_pos_lt_top {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X} {i j : I}
    (hpos : 0 < singleChannelLip d ϕ U i j) (hlt : singleChannelLip d ϕ U i j < ⊤) :
    singleChannelLip d ϕ U i j ∈ singleChannelFeasible d ϕ U i j := by
  set a := singleChannelLip d ϕ U i j
  intro x hx y hy
  by_cases hB0 : d i x y = 0
  · have htop : (⊤ : ENNReal) ∈ singleChannelFeasible d ϕ U i j :=
      singleChannelLip_lt_mem_feasible d ϕ hlt
    have hle := htop x hx y hy
    rw [hB0, mul_zero] at hle
    simpa [hB0] using hle
  · by_cases hBtop : d i x y = ⊤
    · have ha_ne : a ≠ 0 := ne_of_gt hpos
      rw [hBtop, ENNReal.mul_top ha_ne]
      exact le_top
    · have hB_pos : 0 < d i x y := pos_iff_ne_zero.mpr hB0
      by_contra hnot
      have hlt_ab : a * d i x y < d j (ϕ.func x) (ϕ.func y) := lt_of_not_ge hnot
      have ha_div : a < d j (ϕ.func x) (ϕ.func y) / d i x y :=
        (ENNReal.lt_div_iff_mul_lt (Or.inl hB0) (Or.inl hBtop)).mpr hlt_ab
      obtain ⟨l, hal, hl_div⟩ := exists_between ha_div
      have hl_mem : l ∈ singleChannelFeasible d ϕ U i j :=
        singleChannelLip_lt_mem_feasible d ϕ hal
      have h_upper : d j (ϕ.func x) (ϕ.func y) ≤ l * d i x y := hl_mem x hx y hy
      have h_strict : l * d i x y < d j (ϕ.func x) (ϕ.func y) :=
        (ENNReal.lt_div_iff_mul_lt (Or.inl hB0) (Or.inl hBtop)).mp hl_div
      exact absurd (lt_of_le_of_lt h_upper h_strict) (lt_irrefl _)

/-- **HC02-P22**: When $\underline{L}_{i \to j}(\phi; U) = 0$, every finite positive constant
$0 < \lambda < +\infty$ is a valid single-channel scalar certificate. -/
theorem finite_pos_mem_feasible_of_singleChannelLip_eq_zero {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X} {i j : I}
    (h0 : singleChannelLip d ϕ U i j = 0) {l : ENNReal} (hl_pos : 0 < l) (_hl_lt : l < ⊤) :
    l ∈ singleChannelFeasible d ϕ U i j := by
  apply singleChannelLip_lt_mem_feasible d ϕ
  rw [h0]
  exact hl_pos

/-- **HC02-P24**: $\underline{L}_{i \to j}(\phi; U) < +\infty$ if and only if there exists
a finite constant $\lambda < +\infty$ satisfying the pairwise scalar bound on $U$. -/
theorem singleChannelLip_lt_top_iff {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X} {i j : I} :
    singleChannelLip d ϕ U i j < ⊤ ↔
      ∃ l : ENNReal, l < ⊤ ∧ l ∈ singleChannelFeasible d ϕ U i j := by
  constructor
  · intro hlt
    by_cases h0 : singleChannelLip d ϕ U i j = 0
    · refine ⟨1, ENNReal.one_lt_top, ?_⟩
      exact finite_pos_mem_feasible_of_singleChannelLip_eq_zero d ϕ h0 zero_lt_one ENNReal.one_lt_top
    · have hpos : 0 < singleChannelLip d ϕ U i j := pos_iff_ne_zero.mpr h0
      exact ⟨singleChannelLip d ϕ U i j, hlt,
        singleChannelLip_mem_feasible_of_pos_lt_top d ϕ hpos hlt⟩
  · rintro ⟨l, hlt, hl⟩
    exact lt_of_le_of_lt (sInf_le hl) hlt

/-! ### Counterexample for HC02-P23 and matrix-entry vs single-channel separation for HC02-D08 -/

/-- Discrete `{0, ⊤}` extended pseudo-metric on `Option Bool` with absorbing element `none`. -/
def discreteGauge (_ : Unit) (x y : Option Bool) : ENNReal :=
  if x = y then 0 else ⊤

theorem discreteGauge_extendedPseudoMetric :
    ∀ u : Unit, ExtendedPseudoMetric (Option Bool) none (discreteGauge u) := by
  intro u
  refine
    { nonabsorbing := ⟨some false, by simp⟩
      dist_self := fun x => by simp [discreteGauge]
      symm := fun x y => by
        by_cases h : x = y <;> simp [discreteGauge, h, eq_comm]
      triangle := fun x y z => by
        by_cases hxz : x = z
        · subst hxz
          simp [discreteGauge]
        · by_cases hxy : x = y
          · subst hxy
            simp [discreteGauge, hxz]
          · simp [discreteGauge, hxz, hxy]
      isolate_bot := fun x hx => by simp [discreteGauge, hx] }

/-- **HC02-P23**: Counterexample showing $\underline{L}_{i \to j}(\phi; U) = 0$ need not be
achieved by $\lambda = 0$.
Uses a legal extended gauge space `(Option Bool, discreteGauge, none)` over `Unit`,
the identity operator `idOperator`, and nonempty `U = {some false, some true} ⊆ dom idOperator`. -/
theorem zero_singleChannelLip_not_necessarily_attained :
    ∃ (X I : Type) (bot : X) (_ : Fintype I) (_ : Nonempty I)
      (d : I → X → X → ENNReal) (_ : ∀ i, ExtendedPseudoMetric X bot (d i))
      (ϕ : Operator X bot) (U : Set X) (i j : I),
      U.Nonempty ∧ U ⊆ dom ϕ ∧
      singleChannelLip d ϕ U i j = 0 ∧
      0 ∉ singleChannelFeasible d ϕ U i j := by
  let U : Set (Option Bool) := {some false, some true}
  let ϕ : Operator (Option Bool) none := idOperator
  refine ⟨Option Bool, Unit, none, inferInstance, inferInstance,
    discreteGauge, discreteGauge_extendedPseudoMetric, ϕ, U, (), (), ?_, ?_, ?_, ?_⟩
  · exact ⟨some false, by simp [U]⟩
  · intro x hx
    rcases hx with rfl | rfl <;> simp [dom, ϕ, idOperator]
  · have hpos_mem : ∀ l : ENNReal, 0 < l → l ∈ singleChannelFeasible discreteGauge ϕ U () () := by
      intro l hl x _ y _
      by_cases hxy : x = y
      · subst hxy
        simp [discreteGauge, ϕ]
      · simp [discreteGauge, ϕ, hxy, ENNReal.mul_top (ne_of_gt hl)]
    by_contra hne
    have hpos : 0 < singleChannelLip discreteGauge ϕ U () () := pos_iff_ne_zero.mpr hne
    obtain ⟨l, hl0, hla⟩ := exists_between hpos
    have hle : singleChannelLip discreteGauge ϕ U () () ≤ l := sInf_le (hpos_mem l hl0)
    exact absurd hla (not_lt_of_ge hle)
  · intro h0
    have hbad := h0 (some false) (by simp [U]) (some true) (by simp [U])
    simp [discreteGauge, ϕ] at hbad

/-- Auxiliary two-component gauge on `Option Bool` where component `false` collapses non-absorbing
points while component `true` separates them with `⊤`. -/
def twoCompWitnessGauge (b : Bool) (x y : Option Bool) : ENNReal :=
  match b with
  | false =>
    match x, y with
    | none, none => 0
    | none, some _ => ⊤
    | some _, none => ⊤
    | some _, some _ => 0
  | true =>
    if x = y then 0 else ⊤

theorem twoCompWitnessGauge_extendedPseudoMetric :
    ∀ b : Bool, ExtendedPseudoMetric (Option Bool) none (twoCompWitnessGauge b) := by
  intro b
  cases b with
  | false =>
    refine
      { nonabsorbing := ⟨some false, by simp⟩
        dist_self := fun x => by cases x <;> rfl
        symm := fun x y => by cases x <;> cases y <;> rfl
        triangle := fun x y z => by cases x <;> cases y <;> cases z <;> simp [twoCompWitnessGauge]
        isolate_bot := fun x hx => by cases x <;> simp_all [twoCompWitnessGauge] }
  | true =>
    refine
      { nonabsorbing := ⟨some false, by simp⟩
        dist_self := fun x => by simp [twoCompWitnessGauge]
        symm := fun x y => by by_cases h : x = y <;> simp [twoCompWitnessGauge, h, eq_comm]
        triangle := fun x y z => by
          by_cases hxz : x = z
          · subst hxz; simp [twoCompWitnessGauge]
          · by_cases hxy : x = y
            · subst hxy; simp [twoCompWitnessGauge, hxz]
            · simp [twoCompWitnessGauge, hxz, hxy]
        isolate_bot := fun x hx => by simp [twoCompWitnessGauge, hx] }

/-- **HC02-D08 (non-identification witness)**: `singleChannelLip d ϕ U i j` is a genuinely
different object from an arbitrary Lip matrix entry `L i j` (even on the same operator and domain). -/
theorem singleChannelLip_ne_matrix_entry_witness :
    ∃ (X I : Type) (bot : X) (_ : Fintype I) (_ : Nonempty I)
      (d : I → X → X → ENNReal) (_ : ∀ i, ExtendedPseudoMetric X bot (d i))
      (ϕ : Operator X bot) (U : Set X) (L : GaugeMatrix I) (i j : I),
      U.Nonempty ∧ L ∈ LipRestricted d ϕ U ∧
      L i j ≠ singleChannelLip d ϕ U i j := by
  let U : Set (Option Bool) := {some false, some true}
  let ϕ : Operator (Option Bool) none := idOperator
  have hU : U ⊆ dom ϕ := by
    intro x hx
    rcases hx with rfl | rfl <;> simp [dom, ϕ, idOperator]
  refine ⟨Option Bool, Bool, none, inferInstance, inferInstance,
    twoCompWitnessGauge, twoCompWitnessGauge_extendedPseudoMetric,
    ϕ, U, idMatrix, false, true, ⟨some false, by simp [U]⟩,
    idMatrix_mem_lipRestricted twoCompWitnessGauge hU, ?_⟩
  have hL : (idMatrix (I := Bool)) false true = 0 := idMatrix_apply_ne (by decide)
  have hsingle : singleChannelLip twoCompWitnessGauge ϕ U false true = ⊤ := by
    apply singleChannelLip_eq_top_of_zero_pos twoCompWitnessGauge ϕ
      (x := some false) (y := some true) (by simp [U]) (by simp [U])
    · rfl
    · simp [twoCompWitnessGauge, ϕ]
  rw [hL, hsingle]
  exact ENNReal.zero_ne_top

/-! ### Channel decoupling, zero-coefficient removal, bilateral bounds, reflection (HC02-P25 to HC02-P32) -/

/-- **HC02-P25**: A zero entry `L i j = 0` annihilates its term `L i j * d i x y = 0`
(even when `d i x y = ⊤`) and allows removing input `i` from the output-`j` sum. -/
theorem zero_coeff_mul_eq_zero {X I : Type} (d : I → X → X → ENNReal)
    {L : GaugeMatrix I} {i j : I} (h0 : L i j = 0) (x y : X) :
    L i j * d i x y = 0 := by
  rw [h0, zero_mul]

theorem sum_erase_of_coeff_zero {X I : Type} [Fintype I] [DecidableEq I]
    (d : I → X → X → ENNReal) {L : GaugeMatrix I} {i j : I} (h0 : L i j = 0) (x y : X) :
    (∑ k : I, L k j * d k x y) = ∑ k ∈ Finset.univ.erase i, L k j * d k x y := by
  rw [← Finset.add_sum_erase Finset.univ (fun k => L k j * d k x y) (Finset.mem_univ i),
    zero_coeff_mul_eq_zero d h0 x y, zero_add]

theorem lipRestricted_erase_of_coeff_zero {X I : Type} {bot : X}
    [Fintype I] [Nonempty I] [DecidableEq I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X}
    {L : GaugeMatrix I} (hL : L ∈ LipRestricted d ϕ U) {i j : I} (h0 : L i j = 0)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    d j (ϕ.func x) (ϕ.func y) ≤ ∑ k ∈ Finset.univ.erase i, L k j * d k x y := by
  rw [← sum_erase_of_coeff_zero d h0 x y]
  exact hL.2 x hx y hy j

/-- **HC02-P26**: Single-row sparsity at arbitrary `(i, j)` (not necessarily `i = j`)
yields the single-input scalar upper bound $d_j(\phi(x), \phi(y)) \le L_{i \to j} d_i(x, y)$. -/
theorem rowSparseAt_bound {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X}
    {L : GaugeMatrix I} (hL : L ∈ LipRestricted d ϕ U) {i j : I} (hrow : RowSparseAt L i j) :
    ∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ L i j * d i x y := by
  intro x hx y hy
  have hsum := hL.2 x hx y hy j
  have hsingle : (∑ k : I, L k j * d k x y) = L i j * d i x y := by
    rw [Finset.sum_eq_single i]
    · intro k _ hki
      rw [hrow k hki, zero_mul]
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  rwa [hsingle] at hsum

theorem isRowDecoupledAt_bound {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X} {j : I}
    (hdec : IsRowDecoupledAt d ϕ U j) :
    ∃ (L : GaugeMatrix I) (i : I), L ∈ LipRestricted d ϕ U ∧
      ∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ L i j * d i x y := by
  rcases hdec with ⟨L, hL, i, hrow⟩
  exact ⟨L, i, hL, rowSparseAt_bound d ϕ hL hrow⟩

/-- **HC02-P27**: Single-column sparsity at `(i, j)` forces `L i k * d i x y = 0` for all `k ≠ j`,
so in `L`, input component `i` can contribute at most to output component `j`. -/
theorem colSparseAt_off_zero {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X}
    {L : GaugeMatrix I} (_hL : L ∈ LipRestricted d ϕ U) {i j : I} (hcol : ColSparseAt L i j) :
    ∀ k : I, k ≠ j → ∀ x ∈ U, ∀ y ∈ U, L i k * d i x y = 0 := by
  intro k hkj x _ y _
  rw [hcol k hkj, zero_mul]

theorem colSparseAt_erase_bound {X I : Type} {bot : X}
    [Fintype I] [Nonempty I] [DecidableEq I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X}
    {L : GaugeMatrix I} (hL : L ∈ LipRestricted d ϕ U) {i j : I} (hcol : ColSparseAt L i j) :
    ∀ k : I, k ≠ j → ∀ x ∈ U, ∀ y ∈ U,
      d k (ϕ.func x) (ϕ.func y) ≤ ∑ m ∈ Finset.univ.erase i, L m k * d m x y := by
  intro k hkj x hx y hy
  exact lipRestricted_erase_of_coeff_zero d ϕ hL (hcol k hkj) hx hy

theorem isColDecoupledAt_erase_bound {X I : Type} {bot : X}
    [Fintype I] [Nonempty I] [DecidableEq I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X} {i : I}
    (hdec : IsColDecoupledAt d ϕ U i) :
    ∃ (L : GaugeMatrix I) (j : I), L ∈ LipRestricted d ϕ U ∧
      (∀ k : I, k ≠ j → ∀ x ∈ U, ∀ y ∈ U, L i k * d i x y = 0) ∧
      (∀ k : I, k ≠ j → ∀ x ∈ U, ∀ y ∈ U,
        d k (ϕ.func x) (ϕ.func y) ≤ ∑ m ∈ Finset.univ.erase i, L m k * d m x y) := by
  rcases hdec with ⟨L, hL, j, hcol⟩
  exact ⟨L, j, hL, colSparseAt_off_zero d ϕ hL hcol, colSparseAt_erase_bound d ϕ hL hcol⟩

/-- **HC02-P28**: A diagonal Lip matrix gives componentwise scalar upper bounds for all components. -/
theorem diag_lip_bounds {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X}
    {L : GaugeMatrix I} (hL : L ∈ LipRestricted d ϕ U) (hdiag : IsDiagMatrix L) :
    ∀ j : I, ∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ L j j * d j x y := by
  intro j
  exact rowSparseAt_bound d ϕ hL ((isDiagMatrix_iff_rowSparseAt L).mp hdiag j)

/-- **HC02-P29**: Bilateral scalar inequality for output component `j` requires only
Lip row sparsity `∀ k ≠ j, L k j = 0` (no sparsity assumed on `K`). -/
theorem diag_row_bilateral_bound {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X}
    {L K : GaugeMatrix I} (hL : L ∈ LipRestricted d ϕ U) (hK : K ∈ CoLipRestricted d ϕ U)
    {j : I} (hrow : RowSparseAt L j j) :
    ∀ x ∈ U, ∀ y ∈ U,
      K j j * d j x y ≤ d j (ϕ.func x) (ϕ.func y) ∧
      d j (ϕ.func x) (ϕ.func y) ≤ L j j * d j x y := by
  intro x hx y hy
  constructor
  · exact (Finset.single_le_sum (f := fun k => K k j * d k x y)
      (fun _ _ => zero_le _) (Finset.mem_univ j)).trans (hK.2.2 x hx y hy j)
  · exact rowSparseAt_bound d ϕ hL hrow x hx y hy

/-- **HC02-P30 (componentwise bilateral bounds)**: If diagonal Lip row sparsity holds
for all `j : I`, bilateral scalar bounds hold simultaneously for all components. -/
theorem all_diag_row_bilateral_bounds {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X}
    {L K : GaugeMatrix I} (hL : L ∈ LipRestricted d ϕ U) (hK : K ∈ CoLipRestricted d ϕ U)
    (hdiag : ∀ j : I, RowSparseAt L j j) :
    ∀ j : I, ∀ x ∈ U, ∀ y ∈ U,
      K j j * d j x y ≤ d j (ϕ.func x) (ϕ.func y) ∧
      d j (ϕ.func x) (ϕ.func y) ≤ L j j * d j x y :=
  fun j => diag_row_bilateral_bound d ϕ hL hK (hdiag j)

/-- **HC02-P30 (finite scalar factor branch)**: If additionally `L j j < ⊤` and `K j j < ⊤`
for all `j : I`, the bilateral scalar bounds hold with finite `NNReal` scalar coefficients. -/
theorem all_diag_row_bilateral_bounds_finite {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X}
    {L K : GaugeMatrix I} (hL : L ∈ LipRestricted d ϕ U) (hK : K ∈ CoLipRestricted d ϕ U)
    (hdiag : ∀ j : I, RowSparseAt L j j)
    (hLfin : ∀ j : I, L j j < ⊤) (hKfin : ∀ j : I, K j j < ⊤) :
    ∃ (k_fin l_fin : I → NNReal),
      ∀ j : I, (k_fin j : ENNReal) = K j j ∧ (l_fin j : ENNReal) = L j j ∧
        ∀ x ∈ U, ∀ y ∈ U,
          (k_fin j : ENNReal) * d j x y ≤ d j (ϕ.func x) (ϕ.func y) ∧
          d j (ϕ.func x) (ϕ.func y) ≤ (l_fin j : ENNReal) * d j x y := by
  refine ⟨fun j => (K j j).toNNReal, fun j => (L j j).toNNReal, fun j => ?_⟩
  have hk : ((K j j).toNNReal : ENNReal) = K j j := ENNReal.coe_toNNReal (ne_of_lt (hKfin j))
  have hl : ((L j j).toNNReal : ENNReal) = L j j := ENNReal.coe_toNNReal (ne_of_lt (hLfin j))
  refine ⟨hk, hl, fun x hx y hy => ?_⟩
  rw [hk, hl]
  exact all_diag_row_bilateral_bounds d ϕ hL hK hdiag j x hx y hy

/-- **HC02-P31**: A positive co-Lip entry `0 < K i j` preserves positive distance along
channel `(i, j)`: `0 < d i x y → 0 < d j (ϕ x) (ϕ y)`. -/
theorem coLip_pos_preserves_dist_pos {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X}
    {K : GaugeMatrix I} (hK : K ∈ CoLipRestricted d ϕ U)
    {i j : I} (hpos : 0 < K i j) :
    ∀ x ∈ U, ∀ y ∈ U, 0 < d i x y → 0 < d j (ϕ.func x) (ϕ.func y) := by
  intro x hx y hy hdist
  have hmul : 0 < K i j * d i x y := ENNReal.mul_pos (ne_of_gt hpos) (ne_of_gt hdist)
  have hle : K i j * d i x y ≤ d j (ϕ.func x) (ϕ.func y) :=
    (Finset.single_le_sum (f := fun k => K k j * d k x y)
      (fun _ _ => zero_le _) (Finset.mem_univ i)).trans (hK.2.2 x hx y hy j)
  exact lt_of_lt_of_le hmul hle

/-- **HC02-P32**: Positive diagonal co-Lip entries (`∀ j, 0 < K j j`) reflect
the full-gauge zero-distance equivalence relation `GaugeZeroRelated` ($\sim_{\mathcal{G}}$). -/
theorem coLip_pos_diag_reflects_gaugeZeroRelated {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X}
    {K : GaugeMatrix I} (hK : K ∈ CoLipRestricted d ϕ U)
    (hpos : ∀ j : I, 0 < K j j) :
    ∀ x ∈ U, ∀ y ∈ U, GaugeZeroRelated d (ϕ.func x) (ϕ.func y) → GaugeZeroRelated d x y := by
  intro x hx y hy hrel j
  by_contra hne
  have hdist : 0 < d j x y := pos_iff_ne_zero.mpr hne
  have hout := coLip_pos_preserves_dist_pos d ϕ hK (hpos j) x hx y hy hdist
  rw [hrel j] at hout
  exact (lt_irrefl 0) hout

end formal_oet.vol_01.ch_02_operator_bounds
