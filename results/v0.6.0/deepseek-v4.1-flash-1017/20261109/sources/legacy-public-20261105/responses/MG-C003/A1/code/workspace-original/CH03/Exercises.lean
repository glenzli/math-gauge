import CH03.Core6
import CH03.LineExamples

namespace formal_oet.vol_01.ch_03_operator_local_degeneracy
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set

set_option maxHeartbeats 5000000

/-! ## Absolute-value pseudometric -/

def absLineDist : Option ℝ → Option ℝ → ENNReal
  | none, none => 0
  | some x, some y => ENNReal.ofReal (abs (abs x - abs y))
  | none, some _ => ⊤
  | some _, none => ⊤

@[simp] theorem absLineDist_none_none : absLineDist none none = 0 := rfl
@[simp] theorem absLineDist_some_some (x y : ℝ) :
    absLineDist (some x) (some y) = ENNReal.ofReal (abs (abs x - abs y)) := rfl
@[simp] theorem absLineDist_none_some (y : ℝ) : absLineDist none (some y) = ⊤ := rfl
@[simp] theorem absLineDist_some_none (x : ℝ) : absLineDist (some x) none = ⊤ := rfl

theorem absLineDist_self (x : Option ℝ) : absLineDist x x = 0 := by
  rcases x with _ | x <;> simp [absLineDist]

theorem absLineDist_extended : ExtendedPseudoMetric (Option ℝ) none absLineDist where
  nonabsorbing := ⟨some 0, by simp⟩
  dist_self := by intro x; rcases x with _ | x <;> simp
  symm := by
    intro x y
    rcases x with _ | x <;> rcases y with _ | y <;> simp [absLineDist, abs_sub_comm]
  triangle := by
    intro x y z
    rcases x with _ | x <;> rcases y with _ | y <;> rcases z with _ | z <;> simp [absLineDist]
    rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (abs_sub_le |x| |y| |z|)
  isolate_bot := by
    intro x hx
    rcases x with _ | x
    · exact (hx rfl).elim
    · simp

def absLineFam : Unit → Option ℝ → Option ℝ → ENNReal := fun _ => absLineDist

theorem absLineFam_extended :
    ∀ i : Unit, ExtendedPseudoMetric (Option ℝ) none (absLineFam i) :=
  fun _ => absLineDist_extended

def phi31 : Operator (Option ℝ) none where
  func
    | none => none
    | some x => some (2 * x - 1)
  preserves_bot := rfl

@[simp] theorem operator_mul_func {X : Type} {bot : X} (φ ψ : Operator X bot) (x : X) :
    (φ * ψ).func x = φ.func (ψ.func x) := rfl

@[simp] theorem operator_one_func {X : Type} {bot : X} (x : X) :
    ((1 : Operator X bot).func x) = x := rfl

def phi31sq : Operator (Option ℝ) none := phi31 * phi31

def U31 : Set (Option ℝ) := {some (0 : ℝ), some 1}

theorem ex31_phi_const : (() : Unit) ∈ Iconst absLineFam phi31 U31 := by
  intro x hx y hy
  simp only [U31, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
    norm_num [absLineFam, absLineDist, phi31]

theorem ex31_phi_fiber :
    Fiber absLineFam phi31 ({()} : Set Unit) (some (-1 : ℝ)) U31 = U31 := by
  ext x
  constructor
  · intro hx; exact hx.1
  · intro hx
    refine ⟨hx, ?_⟩
    intro k hk
    cases k
    simp only [U31, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;> norm_num [absLineFam, absLineDist, phi31]

theorem ex31_phi2_not_const : (() : Unit) ∉ Iconst absLineFam phi31sq U31 := by
  intro h
  have h01 := h (some 0) (by simp [U31]) (some 1) (by simp [U31])
  change absLineDist (phi31sq.func (some 0)) (phi31sq.func (some 1)) = 0 at h01
  norm_num [phi31sq, phi31, absLineFam, absLineDist] at h01

theorem ex31_phi2_not_id : (() : Unit) ∉ Iid absLineFam phi31sq U31 := by
  intro h
  have hz := h.2 (some 0) (by simp [U31])
  change absLineDist (phi31sq.func (some 0)) (some 0) = 0 at hz
  norm_num [phi31sq, phi31, absLineFam, absLineDist] at hz

theorem ex31_phi2_active : (() : Unit) ∈ Iact absLineFam phi31sq U31 :=
  ⟨ex31_phi2_not_const, ex31_phi2_not_id⟩

theorem ex31_phi2_fiber :
    Fiber absLineFam phi31sq ({()} : Set Unit) (some (-3 : ℝ)) U31 = {some 0} := by
  ext x
  constructor
  · intro hx
    simp only [U31, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx.1 with hx0 | hx1
    · simp [hx0]
    · exfalso
      subst x
      have hz := hx.2 () (by simp)
      norm_num [phi31sq, phi31, absLineFam, absLineDist] at hz
  · intro hx
    simp only [Set.mem_singleton_iff] at hx
    subst x
    refine ⟨by simp [U31], ?_⟩
    intro k hk
    cases k
    norm_num [phi31sq, phi31, absLineFam, absLineDist]

theorem ex31_constant_self_comp_no_distinguish
    (ψ : Operator (Option ℝ) none) {c : Option ℝ}
    (hconst : ∀ x ∈ U31, ψ.func x = c) :
    some (0 : ℝ) ∈ Fiber absLineFam (ψ * ψ) ({()} : Set Unit) ((ψ * ψ).func (some 0)) U31 ∧
      some (1 : ℝ) ∈ Fiber absLineFam (ψ * ψ) ({()} : Set Unit) ((ψ * ψ).func (some 0)) U31 := by
  have h0 : (ψ * ψ).func (some (0:ℝ)) = ψ.func c := by
    change ψ.func (ψ.func (some 0)) = ψ.func c
    rw [hconst (some 0) (by simp [U31])]
  have h1 : (ψ * ψ).func (some (1:ℝ)) = ψ.func c := by
    change ψ.func (ψ.func (some 1)) = ψ.func c
    rw [hconst (some 1) (by simp [U31])]
  constructor
  · refine ⟨by simp [U31], ?_⟩
    intro k hk
    cases k
    exact absLineDist_self _
  · refine ⟨by simp [U31], ?_⟩
    intro k hk
    cases k
    rw [h1, ← h0]
    exact absLineDist_self _

/-! ## Exercise 3.2: positive co-Lip channels and radius gaps -/

theorem colip_positive_pointwise_radius_gap
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (U : Set X) (i j : I) (K : ENNReal)
    (hco : ∀ x ∈ U, ∀ y ∈ U, K * d i x y ≤ d j (φ.func x) (φ.func y))
    (hKpos : 0 < K) (y : X) (hy : y ∈ U)
    (hrpos : 0 < pointwiseZeroRadius d φ i j y U) :
    ∀ x ∈ U, ¬ (0 < d i x y ∧ d i x y < pointwiseZeroRadius d φ i j y U) := by
  intro x hx hlt
  have hsym : d i y x < pointwiseZeroRadius d φ i j y U := by
    rw [(hd i).symm]
    exact hlt.2
  have hzero : d j (φ.func y) (φ.func x) = 0 :=
    pointwise_radius_truncation d hd φ U i j hx hsym
  have hcoxy := hco x hx y hy
  have hposmul : 0 < K * d i x y := ENNReal.mul_pos (ne_of_gt hKpos) (ne_of_gt hlt.1)
  have hle : K * d i x y ≤ 0 := by
    calc
      K * d i x y ≤ d j (φ.func x) (φ.func y) := hcoxy
      _ = d j (φ.func y) (φ.func x) := (hd j).symm _ _
      _ = 0 := hzero
  exact (not_lt_of_ge hle) hposmul

theorem colip_positive_unified_radius_gap
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (U : Set X) (i j : I) (K : ENNReal)
    (hco : ∀ x ∈ U, ∀ y ∈ U, K * d i x y ≤ d j (φ.func x) (φ.func y))
    (hKpos : 0 < K) (hrpos : 0 < zeroingMatrix d φ U j i) :
    ∀ x ∈ U, ∀ y ∈ U,
      d i x y = 0 ∨ zeroingMatrix d φ U j i ≤ d i x y := by
  intro x hx y hy
  by_cases hzero : d i x y = 0
  · exact Or.inl hzero
  · right
    by_contra hnot
    have hlt : d i x y < zeroingMatrix d φ U j i := lt_of_not_ge hnot
    have hpos : 0 < d i x y := lt_of_le_of_ne (zero_le _) (Ne.symm hzero)
    unfold zeroingMatrix unifiedRadius at hlt
    have hltp : d i x y < pointwiseZeroRadius d φ i j x U :=
      lt_of_lt_of_le hlt (iInf_le _ (⟨x, hx⟩ : {x : X // x ∈ U}))
    have hout : d j (φ.func x) (φ.func y) = 0 :=
      pointwise_radius_truncation d hd φ U i j hy hltp
    have hcop := hco x hx y hy
    have hposmul : 0 < K * d i x y := ENNReal.mul_pos (ne_of_gt hKpos) (ne_of_gt hpos)
    have hle : K * d i x y ≤ 0 := by
      calc
        K * d i x y ≤ d j (φ.func x) (φ.func y) := hcop
        _ = 0 := hout
    exact (not_lt_of_ge hle) hposmul


/-! ## Exercise 3.3: translation and fiber entropy -/
noncomputable abbrev threeHalves : ENNReal := (3/2 : ENNReal)

theorem threeHalves_eq : threeHalves = ((3/2 : NNReal) : ENNReal) := by
  norm_num [threeHalves, ENNReal.coe_div]

theorem one_lt_threeHalves : (1 : ENNReal) < threeHalves := by
  rw [threeHalves_eq]
  exact_mod_cast (by norm_num : (1 : NNReal) < 3/2)

theorem threeHalves_le_two : threeHalves ≤ (2 : ENNReal) := by
  rw [threeHalves_eq]
  change ((3/2 : NNReal) : ENNReal) ≤ ((2 : NNReal) : ENNReal)
  exact_mod_cast (by
    rw [div_le_iff₀ (by norm_num : (0 : NNReal) < 2)]
    norm_num : (3/2 : NNReal) ≤ 2)

theorem threeHalves_lt_three : threeHalves < (3 : ENNReal) := by
  rw [threeHalves_eq]
  exact_mod_cast (by norm_num : (3/2 : NNReal) < 3)

theorem zero_lt_threeHalves : (0 : ENNReal) < threeHalves := lt_trans zero_lt_one one_lt_threeHalves

theorem absLineDist_one_lt (x y : ℝ) (h : abs (abs x - abs y) = 1) :
    absLineDist (some x) (some y) < threeHalves := by
  rw [absLineDist_some_some, h]
  simpa using one_lt_threeHalves

theorem absLineDist_zero_lt (x y : ℝ) (h : abs (abs x - abs y) = 0) :
    absLineDist (some x) (some y) < threeHalves := by
  rw [absLineDist_some_some, h]
  simpa using zero_lt_threeHalves


def U33 : Set (Option ℝ) := {some (-3), some (-2), some 0, some 2}

def shift33 : Operator (Option ℝ) none where
  func
    | none => none
    | some x => some (x + 1)
  preserves_bot := rfl

def identityOp : Operator (Option ℝ) none := 1

theorem identity_fiber_neg3 :
    Fiber absLineFam identityOp ({()} : Set Unit) (some (-3 : ℝ)) U33 = {some (-3)} := by
  ext x
  constructor
  · intro hx
    simp only [U33, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx.1 with rfl | rfl | rfl | rfl
    · simp
    · exfalso
      have hz := hx.2 () (by simp)
      norm_num [absLineFam, absLineDist, identityOp, operator_one_func] at hz
    · exfalso
      have hz := hx.2 () (by simp)
      norm_num [absLineFam, absLineDist, identityOp, operator_one_func] at hz
    · exfalso
      have hz := hx.2 () (by simp)
      norm_num [absLineFam, absLineDist, identityOp, operator_one_func] at hz
  · intro hx
    simp only [Set.mem_singleton_iff] at hx
    subst x
    refine ⟨by simp [U33], ?_⟩
    intro k hk
    cases k
    exact absLineDist_self _

theorem identity_fiber_neg2 :
    Fiber absLineFam identityOp ({()} : Set Unit) (some (-2 : ℝ)) U33 =
      {some (-2), some 2} := by
  ext x
  constructor
  · intro hx
    simp only [U33, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx.1 with rfl | rfl | rfl | rfl
    · exfalso
      have hz := hx.2 () (by simp)
      norm_num [absLineFam, absLineDist, identityOp, operator_one_func] at hz
    · simp
    · exfalso
      have hz := hx.2 () (by simp)
      norm_num [absLineFam, absLineDist, identityOp, operator_one_func] at hz
    · simp
  · intro hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · refine ⟨by simp [U33], ?_⟩
      intro k hk; cases k; exact absLineDist_self _
    · refine ⟨by simp [U33], ?_⟩
      intro k hk; cases k
      norm_num [absLineFam, absLineDist, identityOp, operator_one_func]

theorem identity_fiber_zero :
    Fiber absLineFam identityOp ({()} : Set Unit) (some 0 : Option ℝ) U33 = {some 0} := by
  ext x
  constructor
  · intro hx
    simp only [U33, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx.1 with rfl | rfl | rfl | rfl
    · exfalso
      have hz := hx.2 () (by simp)
      norm_num [absLineFam, absLineDist, identityOp, operator_one_func] at hz
    · exfalso
      have hz := hx.2 () (by simp)
      norm_num [absLineFam, absLineDist, identityOp, operator_one_func] at hz
    · simp
    · exfalso
      have hz := hx.2 () (by simp)
      norm_num [absLineFam, absLineDist, identityOp, operator_one_func] at hz
  · intro hx
    simp only [Set.mem_singleton_iff] at hx
    subst x
    refine ⟨by simp [U33], ?_⟩
    intro k hk; cases k; exact absLineDist_self _

theorem identity_fiber_two :
    Fiber absLineFam identityOp ({()} : Set Unit) (some 2 : Option ℝ) U33 =
      {some (-2), some 2} := by
  rw [show (some (2:ℝ)) = (some 2) by rfl]
  -- the same zero class as `-2`
  ext x
  constructor
  · intro hx
    simp only [U33, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx.1 with rfl | rfl | rfl | rfl
    · exfalso
      have hz := hx.2 () (by simp)
      norm_num [absLineFam, absLineDist, identityOp, operator_one_func] at hz
    · simp
    · exfalso
      have hz := hx.2 () (by simp)
      norm_num [absLineFam, absLineDist, identityOp, operator_one_func] at hz
    · simp
  · intro hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · refine ⟨by simp [U33], ?_⟩
      intro k hk; cases k
      norm_num [absLineFam, absLineDist, identityOp, operator_one_func]
    · refine ⟨by simp [U33], ?_⟩
      intro k hk; cases k; exact absLineDist_self _

theorem shift_fiber_neg2 :
    Fiber absLineFam shift33 ({()} : Set Unit) (some (-2 : ℝ)) U33 = {some (-3)} := by
  ext x
  constructor
  · intro hx
    simp only [U33, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx.1 with rfl | rfl | rfl | rfl
    · simp
    · exfalso
      have hz := hx.2 () (by simp)
      norm_num [absLineFam, absLineDist, shift33] at hz
    · exfalso
      have hz := hx.2 () (by simp)
      norm_num [absLineFam, absLineDist, shift33] at hz
    · exfalso
      have hz := hx.2 () (by simp)
      norm_num [absLineFam, absLineDist, shift33] at hz
  · intro hx
    simp only [Set.mem_singleton_iff] at hx
    subst x
    refine ⟨by simp [U33], ?_⟩
    intro k hk; cases k
    norm_num [absLineFam, absLineDist, shift33]

theorem shift_fiber_neg1 :
    Fiber absLineFam shift33 ({()} : Set Unit) (some (-1 : ℝ)) U33 =
      {some (-2), some 0} := by
  ext x
  constructor
  · intro hx
    simp only [U33, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx.1 with rfl | rfl | rfl | rfl
    · exfalso
      have hz := hx.2 () (by simp)
      norm_num [absLineFam, absLineDist, shift33] at hz
    · simp
    · simp
    · exfalso
      have hz := hx.2 () (by simp)
      norm_num [absLineFam, absLineDist, shift33] at hz
  · intro hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · refine ⟨by simp [U33], ?_⟩
      intro k hk; cases k
      norm_num [absLineFam, absLineDist, shift33]
    · refine ⟨by simp [U33], ?_⟩
      intro k hk; cases k
      norm_num [absLineFam, absLineDist, shift33]

theorem shift_fiber_one :
    Fiber absLineFam shift33 ({()} : Set Unit) (some (1 : ℝ)) U33 =
      {some (-2), some 0} := by
  ext x
  constructor
  · intro hx
    simp only [U33, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx.1 with rfl | rfl | rfl | rfl
    · exfalso
      have hz := hx.2 () (by simp)
      norm_num [absLineFam, absLineDist, shift33] at hz
    · simp
    · simp
    · exfalso
      have hz := hx.2 () (by simp)
      norm_num [absLineFam, absLineDist, shift33] at hz
  · intro hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · refine ⟨by simp [U33], ?_⟩
      intro k hk; cases k
      norm_num [absLineFam, absLineDist, shift33]
    · refine ⟨by simp [U33], ?_⟩
      intro k hk; cases k
      norm_num [absLineFam, absLineDist, shift33]

theorem shift_fiber_three :
    Fiber absLineFam shift33 ({()} : Set Unit) (some (3 : ℝ)) U33 = {some 2} := by
  ext x
  constructor
  · intro hx
    simp only [U33, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx.1 with rfl | rfl | rfl | rfl
    · exfalso
      have hz := hx.2 () (by simp)
      norm_num [absLineFam, absLineDist, shift33] at hz
    · exfalso
      have hz := hx.2 () (by simp)
      norm_num [absLineFam, absLineDist, shift33] at hz
    · exfalso
      have hz := hx.2 () (by simp)
      norm_num [absLineFam, absLineDist, shift33] at hz
    · simp
  · intro hx
    simp only [Set.mem_singleton_iff] at hx
    subst x
    refine ⟨by simp [U33], ?_⟩
    intro k hk; cases k
    norm_num [absLineFam, absLineDist, shift33]

theorem U33_no_single_center :
    ¬ ∃ c ∈ U33, ∀ x ∈ U33, absLineDist x c < threeHalves := by
  rintro ⟨c, hc, hcov⟩
  simp only [U33, Set.mem_insert_iff, Set.mem_singleton_iff] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · have h := hcov (some 0) (by simp [U33])
    norm_num [absLineDist] at h
    exact (not_lt_of_ge threeHalves_lt_three.le) h
  · have h := hcov (some 0) (by simp [U33])
    norm_num [absLineDist] at h
    exact (not_lt_of_ge threeHalves_le_two) h
  · have h := hcov (some 2) (by simp [U33])
    norm_num [absLineDist] at h
    exact (not_lt_of_ge threeHalves_le_two) h
  · have h := hcov (some 0) (by simp [U33])
    norm_num [absLineDist] at h
    exact (not_lt_of_ge threeHalves_le_two) h

theorem U33_cover_le :
    covering_number absLineDist threeHalves U33 ≤ 2 := by
  have hnet : InternalEpsilonNet absLineDist threeHalves U33
      ({some (-2), some 0} : Finset (Option ℝ)) := by
    constructor
    · intro x hx
      simp at hx
      rcases hx with rfl | rfl <;> simp [U33]
    · intro x hx
      simp only [U33, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact ⟨some (-2), by simp, absLineDist_one_lt _ _ (by norm_num)⟩
      · exact ⟨some (-2), by simp, absLineDist_zero_lt _ _ (by norm_num)⟩
      · exact ⟨some 0, by simp, absLineDist_zero_lt _ _ (by norm_num)⟩
      · exact ⟨some (-2), by simp, absLineDist_zero_lt _ _ (by norm_num)⟩
  calc
    covering_number absLineDist threeHalves U33
        ≤ (({some (-2), some 0} : Finset (Option ℝ)).card : ENNReal) :=
          covering_number_le_card_of_net hnet
    _ = 2 := by norm_num

theorem U33_cover_ge :
    (2 : ENNReal) ≤ covering_number absLineDist threeHalves U33 := by
  have hfin : ∃ S : Finset (Option ℝ), InternalEpsilonNet absLineDist threeHalves U33 S :=
    ⟨{some (-2), some 0}, by
      constructor
      · intro x hx; simp at hx
        rcases hx with rfl | rfl <;> simp [U33]
      · intro x hx
        simp only [U33, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl | rfl
        · exact ⟨some (-2), by simp, absLineDist_one_lt _ _ (by norm_num)⟩
        · exact ⟨some (-2), by simp, absLineDist_zero_lt _ _ (by norm_num)⟩
        · exact ⟨some 0, by simp, absLineDist_zero_lt _ _ (by norm_num)⟩
        · exact ⟨some (-2), by simp, absLineDist_zero_lt _ _ (by norm_num)⟩⟩
  obtain ⟨S, hS, hcover, hmin⟩ := covering_number_attained absLineDist threeHalves U33 hfin
  have hcard : 2 ≤ S.card := by
    by_contra hnot
    have hle : S.card ≤ 1 := by omega
    have hall := Finset.card_le_one.mp hle
    rcases hS.2 (some 0) (by simp [U33]) with ⟨c0, hc0, h0⟩
    have hc0U : c0 ∈ U33 := hS.1 hc0
    have hcov : ∀ x ∈ U33, absLineDist x c0 < threeHalves := by
      intro x hx
      rcases hS.2 x hx with ⟨c, hc, hdist⟩
      have hcc0 : c = c0 := hall c hc c0 hc0
      simpa [hcc0] using hdist
    exact U33_no_single_center ⟨c0, hc0U, hcov⟩
  rw [hcover]
  exact_mod_cast hcard

theorem U33_cover_eq : covering_number absLineDist threeHalves U33 = 2 :=
  le_antisymm U33_cover_le U33_cover_ge

theorem shift_image_U33 : shift33.func '' U33 =
    ({some (-2), some (-1), some 1, some 3} : Set (Option ℝ)) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp only [U33, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> norm_num [shift33]
  · intro hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact ⟨some (-3), by simp [U33], by norm_num [shift33]⟩
    · exact ⟨some (-2), by simp [U33], by norm_num [shift33]⟩
    · exact ⟨some 0, by simp [U33], by norm_num [shift33]⟩
    · exact ⟨some 2, by simp [U33], by norm_num [shift33]⟩

theorem shift_image_cover_le :
    covering_number absLineDist threeHalves (shift33.func '' U33) ≤ 1 := by
  rw [shift_image_U33]
  have hnet : InternalEpsilonNet absLineDist threeHalves
      ({some (-2), some (-1), some 1, some 3} : Set (Option ℝ))
      ({some (-2)} : Finset (Option ℝ)) := by
    constructor
    · intro x hx; simp at hx; subst x; simp
    · intro x hx
      simp at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact ⟨some (-2), by simp, absLineDist_zero_lt _ _ (by norm_num)⟩
      · exact ⟨some (-2), by simp, absLineDist_one_lt _ _ (by norm_num)⟩
      · exact ⟨some (-2), by simp, absLineDist_one_lt _ _ (by norm_num)⟩
      · exact ⟨some (-2), by simp, absLineDist_one_lt _ _ (by norm_num)⟩
  calc
    covering_number absLineDist threeHalves
        ({some (-2), some (-1), some 1, some 3} : Set (Option ℝ))
        ≤ (({some (-2)} : Finset (Option ℝ)).card : ENNReal) :=
          covering_number_le_card_of_net hnet
    _ = 1 := by simp

theorem shift_image_cover_eq :
    covering_number absLineDist threeHalves (shift33.func '' U33) = 1 := by
  apply le_antisymm shift_image_cover_le
  exact one_le_covering_number_of_nonempty absLineDist threeHalves
    (shift33.func '' U33) (image_nonempty_of_nonempty shift33 ⟨some (-3), by simp [U33]⟩)

theorem ex33_entropy_diff :
    mappingEntropyDiff absLineFam shift33 U33 {()} {()} threeHalves = 1 := by
  unfold mappingEntropyDiff
  rw [subfamily_metric_entropy_singleton absLineFam () threeHalves U33,
    subfamily_metric_entropy_singleton absLineFam () threeHalves (shift33.func '' U33)]
  change erealSub (metric_entropy absLineDist threeHalves U33)
    (metric_entropy absLineDist threeHalves (shift33.func '' U33)) = 1
  have hU0 : covering_number absLineDist threeHalves U33 ≠ 0 :=
    covering_number_pos_of_nonempty absLineDist threeHalves U33
      ⟨some (-3), by simp [U33]⟩
  have hUtop : covering_number absLineDist threeHalves U33 ≠ ⊤ := by
    rw [U33_cover_eq]; exact ENNReal.natCast_ne_top 2
  have hI0 : covering_number absLineDist threeHalves (shift33.func '' U33) ≠ 0 :=
    covering_number_pos_of_nonempty absLineDist threeHalves (shift33.func '' U33)
      (image_nonempty_of_nonempty shift33 ⟨some (-3), by simp [U33]⟩)
  have hItop : covering_number absLineDist threeHalves (shift33.func '' U33) ≠ ⊤ := by
    rw [shift_image_cover_eq]; simp
  rw [metric_entropy_eq_coe_of_cover_finite absLineDist threeHalves U33 hU0 hUtop,
    metric_entropy_eq_coe_of_cover_finite absLineDist threeHalves (shift33.func '' U33) hI0 hItop,
    U33_cover_eq, shift_image_cover_eq, erealSub_coe_coe]
  norm_num [Real.logb]
end formal_oet.vol_01.ch_03_operator_local_degeneracy
