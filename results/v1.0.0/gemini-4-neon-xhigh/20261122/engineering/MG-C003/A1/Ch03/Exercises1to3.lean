/-
Formalization of Chapter 3 (Section 3.7: Exercises 3.1, 3.2, and 3.3)
of "The Operator Evolution Theory, Volume I" by Zhe Li (Glen Li / glenzli), CC BY 4.0.
-/
import Ch03.MappingEntropyDiff

namespace Ch03

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set

/-! ### Shared Pseudometric `d(x, y) = ||x| - |y||` on `ℝ ⊔ {⊥}` for Exercises 3.1 & 3.3 -/

/-- Single-component extended pseudometric `d(x, y) = ||x| - |y||` on `ℝ ⊔ {⊥}` with `⊥` isolated. -/
noncomputable def absDiffDist : Unit → RealWithBot → RealWithBot → ENNReal
  | _, none, none => 0
  | _, some _, none => ⊤
  | _, none, some _ => ⊤
  | _, some x, some y => ENNReal.ofReal |(|x| - |y|)|

theorem absDiffDist_extendedPseudoMetric :
    ∀ u : Unit, ExtendedPseudoMetric RealWithBot none (absDiffDist u) := by
  intro u
  refine
    { nonabsorbing := ⟨some 0, by simp⟩
      dist_self := by
        intro x; cases x <;> simp [absDiffDist]
      symm := by
        intro x y; cases x <;> cases y <;> simp [absDiffDist, abs_sub_comm]
      triangle := by
        intro x y z
        cases x <;> cases y <;> cases z <;> simp [absDiffDist]
        rename_i a b c
        calc
          ENNReal.ofReal |(|a| - |c|)| ≤ ENNReal.ofReal (|(|a| - |b|)| + |(|b| - |c|)|) :=
            ENNReal.ofReal_le_ofReal (abs_sub_le |a| |b| |c|)
          _ = ENNReal.ofReal |(|a| - |b|)| + ENNReal.ofReal |(|b| - |c|)| :=
            ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
      isolate_bot := by
        intro x hx
        cases x
        · exact (hx rfl).elim
        · rfl }

/-! ### Exercise 3.1: Computational Fibers and Self-Composition (CH03-P26-01..03) -/

/-- Affine operator `ϕ(x) = 2x - 1` on `ℝ`, `ϕ(⊥) = ⊥`. -/
def ex31Op : Operator RealWithBot none where
  func
    | none => none
    | some x => some (2 * x - 1)
  preserves_bot := rfl

/-- Domain `U = {0, 1} ⊂ ℝ ⊔ {⊥}` for Exercise 3.1. -/
def ex31U : Set RealWithBot := {some 0, some 1}

/-- Exercise 3.1(i-a) (CH03-P26-01): Legality of `absDiffDist` and `ex31Op`, fiber of `ϕ(0)`,
and component classification `() ∈ I_const(ϕ | U)`. -/
theorem exercise_3_1_i_a :
    (∀ u : Unit, ExtendedPseudoMetric RealWithBot none (absDiffDist u)) ∧
    ex31U ⊆ dom ex31Op ∧
    compFiberSingle absDiffDist ex31Op () ex31U (ex31Op.func (some 0)) = ex31U ∧
    () ∈ I_const absDiffDist ex31Op ex31U ∧
    () ∉ I_id absDiffDist ex31Op ex31U ∧
    () ∉ I_act absDiffDist ex31Op ex31U := by
  have hdom : ex31U ⊆ dom ex31Op := by
    intro x hx
    rcases hx with rfl | rfl <;> simp [dom, ex31Op]
  have hconst : () ∈ I_const absDiffDist ex31Op ex31U := by
    intro x hx y hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
      norm_num [ex31Op, absDiffDist]
  have hfib : compFiberSingle absDiffDist ex31Op () ex31U (ex31Op.func (some 0)) = ex31U := by
    ext x
    simp only [compFiberSingle, Set.mem_setOf_eq, and_iff_left_iff_imp]
    intro hx
    exact hconst x hx (some 0) (Or.inl rfl)
  refine ⟨absDiffDist_extendedPseudoMetric, hdom, hfib, hconst,
    fun hid => hid.1 hconst, fun hact => hact (Or.inl hconst)⟩

/-- Exercise 3.1(i-b) (CH03-P26-02): Fiber of `ϕ²(0)` on the same `U = {0, 1}` is `{0}`,
and `() ∈ I_act(ϕ² | U)`. -/
theorem exercise_3_1_i_b :
    let ϕ2 := operator_compose ex31Op ex31Op
    ex31U ⊆ dom ϕ2 ∧
    compFiberSingle absDiffDist ϕ2 () ex31U (ϕ2.func (some 0)) = {some 0} ∧
    () ∈ I_act absDiffDist ϕ2 ex31U ∧
    () ∉ I_const absDiffDist ϕ2 ex31U ∧
    () ∉ I_id absDiffDist ϕ2 ex31U := by
  intro ϕ2
  have hdom : ex31U ⊆ dom ϕ2 := by
    intro x hx
    rcases hx with rfl | rfl <;> simp [dom, ϕ2, operator_compose, ex31Op]
  have hd01 : absDiffDist () (ϕ2.func (some 1)) (ϕ2.func (some 0)) = ENNReal.ofReal 2 := by
    simp only [ϕ2, operator_compose, Function.comp_apply, ex31Op, absDiffDist]
    norm_num
  have hnot_const : () ∉ I_const absDiffDist ϕ2 ex31U := by
    intro hc
    have h := hc (some 1) (Or.inr rfl) (some 0) (Or.inl rfl)
    rw [hd01] at h
    norm_num at h
  have hnot_id : () ∉ I_id absDiffDist ϕ2 ex31U := by
    intro hid
    have h := hid.2 (some 0) (Or.inl rfl)
    simp only [ϕ2, operator_compose, Function.comp_apply, ex31Op, absDiffDist] at h
    norm_num at h
  have hfib : compFiberSingle absDiffDist ϕ2 () ex31U (ϕ2.func (some 0)) = {some 0} := by
    ext x
    simp only [compFiberSingle, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hx, h0⟩
      rcases hx with rfl | rfl
      · rfl
      · rw [hd01] at h0
        norm_num at h0
    · rintro rfl
      exact ⟨Or.inl rfl, (absDiffDist_extendedPseudoMetric ()).dist_self _⟩
  have hact : () ∈ I_act absDiffDist ϕ2 ex31U := by
    intro h
    rcases h with hc | hi
    · exact hnot_const hc
    · exact hnot_id hi
  exact ⟨hdom, hfib, hact, hnot_const, hnot_id⟩

/-- Exercise 3.1(ii) (CH03-P26-03): If `ψ` takes the same real value `c` on `U = {0, 1}`, then
`ψ²(0) = ψ²(1)`. Either `some c ∈ dom ψ` (in which case `U ⊆ dom ψ²`, `0` and `1` stay in the
same fiber `U`, and `() ∈ I_const(ψ² | U)`), or `some c ∉ dom ψ` (in which case `U ⊈ dom ψ²`
and `U ∩ dom ψ² = ∅`, so the restricted domain condition fails). -/
theorem exercise_3_1_ii (ψ : Operator RealWithBot none) (c : ℝ)
    (h0 : ψ.func (some 0) = some c) (h1 : ψ.func (some 1) = some c) :
    let ψ2 := operator_compose ψ ψ
    ψ2.func (some 0) = ψ2.func (some 1) ∧
    (some c ∈ dom ψ →
      ex31U ⊆ dom ψ2 ∧
      compFiberSingle absDiffDist ψ2 () ex31U (ψ2.func (some 0)) = ex31U ∧
      compFiberSingle absDiffDist ψ2 () ex31U (ψ2.func (some 0)) =
        compFiberSingle absDiffDist ψ2 () ex31U (ψ2.func (some 1)) ∧
      () ∈ I_const absDiffDist ψ2 ex31U) ∧
    (some c ∉ dom ψ →
      ¬ (ex31U ⊆ dom ψ2) ∧ ex31U ∩ dom ψ2 = ∅) := by
  intro ψ2
  have heq : ψ2.func (some 0) = ψ2.func (some 1) := by
    change ψ.func (ψ.func (some 0)) = ψ.func (ψ.func (some 1))
    rw [h0, h1]
  refine ⟨heq, ?_, ?_⟩
  · intro hc_dom
    have hdom : ex31U ⊆ dom ψ2 := by
      intro x hx
      rcases hx with rfl | rfl
      · change ψ.func (ψ.func (some 0)) ≠ none
        rw [h0]; exact hc_dom
      · change ψ.func (ψ.func (some 1)) ≠ none
        rw [h1]; exact hc_dom
    have hconst : () ∈ I_const absDiffDist ψ2 ex31U := by
      intro x hx y hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact (absDiffDist_extendedPseudoMetric ()).dist_self _
      · rw [heq]; exact (absDiffDist_extendedPseudoMetric ()).dist_self _
      · rw [heq]; exact (absDiffDist_extendedPseudoMetric ()).dist_self _
      · exact (absDiffDist_extendedPseudoMetric ()).dist_self _
    have hfib : compFiberSingle absDiffDist ψ2 () ex31U (ψ2.func (some 0)) = ex31U := by
      ext x
      simp only [compFiberSingle, Set.mem_setOf_eq, and_iff_left_iff_imp]
      intro hx
      exact hconst x hx (some 0) (Or.inl rfl)
    refine ⟨hdom, hfib, by rw [heq], hconst⟩
  · intro hc_ndom
    have hbot : ψ.func (some c) = none := by
      by_contra hne
      exact hc_ndom hne
    have hinter : ex31U ∩ dom ψ2 = ∅ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      intro hx hdx
      rcases hx with rfl | rfl
      · apply hdx
        change ψ.func (ψ.func (some 0)) = none
        rw [h0, hbot]
      · apply hdx
        change ψ.func (ψ.func (some 1)) = none
        rw [h1, hbot]
    refine ⟨?_, hinter⟩
    intro hsub
    have hmem : some (0 : ℝ) ∈ ex31U ∩ dom ψ2 := ⟨Or.inl rfl, hsub (Or.inl rfl)⟩
    rw [hinter] at hmem
    exact hmem

/-! ### Exercise 3.2: Nullification Radius and Distance Gap (CH03-P27-01..02) -/

/-- Exercise 3.2(i) (CH03-P27-01): With a positive co-Lip entry `K_{i → j} > 0` (not assumed
finite) and positive pointwise nullification radius `r^N_{ϕ, i, j}(y | U) > 0`, no input point
`x ∈ U` has distance `d_i(x, y) ∈ (0, r^N_{ϕ, i, j}(y | U))`. -/
theorem exercise_3_2_i {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (hd : ∀ k : I, ExtendedPseudoMetric X bot (d k))
    (ϕ : Operator X bot) (U : Set X) (K : I → I → ENNReal) (i j : I) (y : X)
    (_hUne : U.Nonempty) (hUdom : U ⊆ dom ϕ)
    (hK : IsCoLipMatrix d ϕ U K) (hK_pos : 0 < K i j)
    (hy : y ∈ U) (_hr_pos : 0 < pointwiseNullRadiusComp d ϕ i j U y) :
    ∀ x ∈ U, d i x y ∉ Set.Ioo 0 (pointwiseNullRadiusComp d ϕ i j U y) := by
  intro x hx ⟨hpos, hlt⟩
  have hlt_symm : d i y x < pointwiseNullRadiusComp d ϕ i j U y := by
    rw [(hd i).symm]; exact hlt
  have hout0 : d j (ϕ.func y) (ϕ.func x) = 0 :=
    prop_3_11_radius d hd ϕ U i j hUdom hy hx hlt_symm
  have hin0 : d i y x = 0 :=
    positive_colip_entry_reflects_zero d ϕ U K i j hK hK_pos y hy x hx hout0
  rw [(hd i).symm] at hin0
  exact (ne_of_gt hpos) hin0

/-- Exercise 3.2(ii) (CH03-P27-02): If `\underline{r}^N_{ϕ, i, j}|_U > 0` under `K_{i → j} > 0`,
then for all `x, y ∈ U`, `d_i(x, y) ∈ {0} ⊔ [\underline{r}^N_{ϕ, i, j}|_U, +∞]`. -/
theorem exercise_3_2_ii {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (hd : ∀ k : I, ExtendedPseudoMetric X bot (d k))
    (ϕ : Operator X bot) (U : Set X) (K : I → I → ENNReal) (i j : I)
    (hUne : U.Nonempty) (hUdom : U ⊆ dom ϕ)
    (hK : IsCoLipMatrix d ϕ U K) (hK_pos : 0 < K i j)
    (hr_pos : 0 < uniformNullRadiusCompOn d ϕ i j U) :
    Disjoint ({0} : Set ENNReal) (Set.Ici (uniformNullRadiusCompOn d ϕ i j U)) ∧
    ∀ x ∈ U, ∀ y ∈ U,
      d i x y ∈ ({0} : Set ENNReal) ∪ Set.Ici (uniformNullRadiusCompOn d ϕ i j U) := by
  constructor
  · rw [Set.disjoint_left]
    intro a ha0 hage
    simp only [Set.mem_singleton_iff] at ha0
    subst ha0
    exact not_lt_of_ge hage hr_pos
  · intro x hx y hy
    by_cases h0 : d i x y = 0
    · exact Or.inl h0
    · right
      have hpos : 0 < d i x y := pos_iff_ne_zero.mpr h0
      have hr_y : uniformNullRadiusCompOn d ϕ i j U ≤ pointwiseNullRadiusComp d ϕ i j U y :=
        iInf₂_le y hy
      have hgap := exercise_3_2_i d hd ϕ U K i j y hUne hUdom hK hK_pos hy
        (lt_of_lt_of_le hr_pos hr_y) x hx
      by_contra hlt
      have hlt_y : d i x y < pointwiseNullRadiusComp d ϕ i j U y :=
        lt_of_lt_of_le (lt_of_not_ge hlt) hr_y
      exact hgap ⟨hpos, hlt_y⟩

/-! ### Exercise 3.3: Fibers and Entropy Difference under Translation (CH03-P28-01..02) -/

/-- Translation operator `ϕ(x) = x + 1` on `ℝ`, `ϕ(⊥) = ⊥`. -/
def ex33Op : Operator RealWithBot none where
  func
    | none => none
    | some x => some (x + 1)
  preserves_bot := rfl

/-- Four-point domain `U = {-3, -2, 0, 2} ⊂ ℝ ⊔ {⊥}` for Exercise 3.3. -/
def ex33U : Set RealWithBot := {some (-3), some (-2), some 0, some 2}

/-- Exercise 3.3(i) (CH03-P28-01): Complete fiber partitions of `id` and `ϕ(x) = x + 1`
on `U = {-3, -2, 0, 2}` under `d_i(x, y) = ||x| - |y||`. -/
theorem exercise_3_3_i :
    (∀ u : Unit, ExtendedPseudoMetric RealWithBot none (absDiffDist u)) ∧
    ex33U ⊆ dom (@operator_identity RealWithBot none) ∧
    ex33U ⊆ dom ex33Op ∧
    compFiberFamily absDiffDist (@operator_identity RealWithBot none) Set.univ ex33U =
      {{some (-3)}, {some (-2), some 2}, {some 0}} ∧
    compFiberFamily absDiffDist ex33Op Set.univ ex33U =
      {{some (-3)}, {some (-2), some 0}, {some 2}} := by
  have hdom_id : ex33U ⊆ dom (@operator_identity RealWithBot none) := by
    intro x hx
    rcases hx with rfl | rfl | rfl | rfl <;> simp [dom, operator_identity]
  have hdom_op : ex33U ⊆ dom ex33Op := by
    intro x hx
    rcases hx with rfl | rfl | rfl | rfl <;> simp [dom, ex33Op]
  have hfib_univ : ∀ (ϕ : Operator RealWithBot none) (y : RealWithBot),
      compFiber absDiffDist ϕ Set.univ ex33U y = compFiberSingle absDiffDist ϕ () ex33U y := by
    intro ϕ y
    ext x
    simp only [compFiber, compFiberSingle, Set.mem_setOf_eq,
      subfamily_pseudometric_eq_zero_iff, Set.mem_univ, forall_true_left]
    exact ⟨fun ⟨hx, h⟩ => ⟨hx, h ()⟩, fun ⟨hx, h⟩ => ⟨hx, fun u => by cases u; exact h⟩⟩
  have hid_m3 : compFiberSingle absDiffDist (@operator_identity RealWithBot none) () ex33U
      (some (-3)) = {some (-3)} := by
    ext x
    simp only [compFiberSingle, ex33U, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff, operator_identity, id_eq]
    constructor
    · rintro ⟨rfl | rfl | rfl | rfl, h0⟩
      · rfl
      · norm_num [absDiffDist] at h0
      · norm_num [absDiffDist] at h0
      · norm_num [absDiffDist] at h0
    · rintro rfl
      exact ⟨Or.inl rfl, by norm_num [absDiffDist]⟩
  have hid_m2 : compFiberSingle absDiffDist (@operator_identity RealWithBot none) () ex33U
      (some (-2)) = {some (-2), some 2} := by
    ext x
    simp only [compFiberSingle, ex33U, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff, operator_identity, id_eq]
    constructor
    · rintro ⟨rfl | rfl | rfl | rfl, h0⟩
      · norm_num [absDiffDist] at h0
      · exact Or.inl rfl
      · norm_num [absDiffDist] at h0
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨Or.inr (Or.inl rfl), by norm_num [absDiffDist]⟩
      · exact ⟨Or.inr (Or.inr (Or.inr rfl)), by norm_num [absDiffDist]⟩
  have hid_2 : compFiberSingle absDiffDist (@operator_identity RealWithBot none) () ex33U
      (some 2) = {some (-2), some 2} := by
    ext x
    simp only [compFiberSingle, ex33U, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff, operator_identity, id_eq]
    constructor
    · rintro ⟨rfl | rfl | rfl | rfl, h0⟩
      · norm_num [absDiffDist] at h0
      · exact Or.inl rfl
      · norm_num [absDiffDist] at h0
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨Or.inr (Or.inl rfl), by norm_num [absDiffDist]⟩
      · exact ⟨Or.inr (Or.inr (Or.inr rfl)), by norm_num [absDiffDist]⟩
  have hid_0 : compFiberSingle absDiffDist (@operator_identity RealWithBot none) () ex33U
      (some 0) = {some 0} := by
    ext x
    simp only [compFiberSingle, ex33U, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff, operator_identity, id_eq]
    constructor
    · rintro ⟨rfl | rfl | rfl | rfl, h0⟩
      · norm_num [absDiffDist] at h0
      · norm_num [absDiffDist] at h0
      · rfl
      · norm_num [absDiffDist] at h0
    · rintro rfl
      exact ⟨Or.inr (Or.inr (Or.inl rfl)), by norm_num [absDiffDist]⟩
  have hpart_id : compFiberFamily absDiffDist (@operator_identity RealWithBot none) Set.univ ex33U =
      {{some (-3)}, {some (-2), some 2}, {some 0}} := by
    ext F
    simp only [compFiberFamily, operator_image, Set.mem_image, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
      rw [hfib_univ]
      rcases hx with rfl | rfl | rfl | rfl
      · left; exact hid_m3
      · right; left; exact hid_m2
      · right; right; exact hid_0
      · right; left; exact hid_2
    · rintro (rfl | rfl | rfl)
      · exact ⟨some (-3), ⟨some (-3), Or.inl rfl, rfl⟩, by rw [hfib_univ]; exact hid_m3⟩
      · exact ⟨some (-2), ⟨some (-2), Or.inr (Or.inl rfl), rfl⟩, by rw [hfib_univ]; exact hid_m2⟩
      · exact ⟨some 0, ⟨some 0, Or.inr (Or.inr (Or.inl rfl)), rfl⟩, by rw [hfib_univ]; exact hid_0⟩
  have hop_m2 : compFiberSingle absDiffDist ex33Op () ex33U (some (-2)) = {some (-3)} := by
    ext x
    simp only [compFiberSingle, ex33U, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨rfl | rfl | rfl | rfl, h0⟩
      · rfl
      · norm_num [ex33Op, absDiffDist] at h0
      · norm_num [ex33Op, absDiffDist] at h0
      · norm_num [ex33Op, absDiffDist] at h0
    · rintro rfl
      exact ⟨Or.inl rfl, by norm_num [ex33Op, absDiffDist]⟩
  have hop_m1 : compFiberSingle absDiffDist ex33Op () ex33U (some (-1)) = {some (-2), some 0} := by
    ext x
    simp only [compFiberSingle, ex33U, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨rfl | rfl | rfl | rfl, h0⟩
      · norm_num [ex33Op, absDiffDist] at h0
      · exact Or.inl rfl
      · exact Or.inr rfl
      · norm_num [ex33Op, absDiffDist] at h0
    · rintro (rfl | rfl)
      · exact ⟨Or.inr (Or.inl rfl), by norm_num [ex33Op, absDiffDist]⟩
      · exact ⟨Or.inr (Or.inr (Or.inl rfl)), by norm_num [ex33Op, absDiffDist]⟩
  have hop_1 : compFiberSingle absDiffDist ex33Op () ex33U (some 1) = {some (-2), some 0} := by
    ext x
    simp only [compFiberSingle, ex33U, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨rfl | rfl | rfl | rfl, h0⟩
      · norm_num [ex33Op, absDiffDist] at h0
      · exact Or.inl rfl
      · exact Or.inr rfl
      · norm_num [ex33Op, absDiffDist] at h0
    · rintro (rfl | rfl)
      · exact ⟨Or.inr (Or.inl rfl), by norm_num [ex33Op, absDiffDist]⟩
      · exact ⟨Or.inr (Or.inr (Or.inl rfl)), by norm_num [ex33Op, absDiffDist]⟩
  have hop_3 : compFiberSingle absDiffDist ex33Op () ex33U (some 3) = {some 2} := by
    ext x
    simp only [compFiberSingle, ex33U, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨rfl | rfl | rfl | rfl, h0⟩
      · norm_num [ex33Op, absDiffDist] at h0
      · norm_num [ex33Op, absDiffDist] at h0
      · norm_num [ex33Op, absDiffDist] at h0
      · rfl
    · rintro rfl
      exact ⟨Or.inr (Or.inr (Or.inr rfl)), by norm_num [ex33Op, absDiffDist]⟩
  have hpart_op : compFiberFamily absDiffDist ex33Op Set.univ ex33U =
      {{some (-3)}, {some (-2), some 0}, {some 2}} := by
    ext F
    simp only [compFiberFamily, operator_image, Set.mem_image, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
      rw [hfib_univ]
      rcases hx with rfl | rfl | rfl | rfl
      · left; simpa [ex33Op, show (-3 : ℝ) + 1 = -2 by norm_num] using hop_m2
      · right; left; simpa [ex33Op, show (-2 : ℝ) + 1 = -1 by norm_num] using hop_m1
      · right; left; simpa [ex33Op, show (0 : ℝ) + 1 = 1 by norm_num] using hop_1
      · right; right; simpa [ex33Op, show (2 : ℝ) + 1 = 3 by norm_num] using hop_3
    · rintro (rfl | rfl | rfl)
      · refine ⟨ex33Op.func (some (-3)), ⟨some (-3), Or.inl rfl, rfl⟩, ?_⟩
        rw [hfib_univ]; simpa [ex33Op, show (-3 : ℝ) + 1 = -2 by norm_num] using hop_m2
      · refine ⟨ex33Op.func (some (-2)), ⟨some (-2), Or.inr (Or.inl rfl), rfl⟩, ?_⟩
        rw [hfib_univ]; simpa [ex33Op, show (-2 : ℝ) + 1 = -1 by norm_num] using hop_m1
      · refine ⟨ex33Op.func (some 2), ⟨some 2, Or.inr (Or.inr (Or.inr rfl)), rfl⟩, ?_⟩
        rw [hfib_univ]; simpa [ex33Op, show (2 : ℝ) + 1 = 3 by norm_num] using hop_3
  exact ⟨absDiffDist_extendedPseudoMetric, hdom_id, hdom_op, hpart_id, hpart_op⟩

/-- Exercise 3.3(ii) (CH03-P28-02): At `ε = 3/2`, `N_i(3/2, U) = 2`, `N_i(3/2, ϕ(U)) = 1`,
`ΔE_{3/2, i}(ϕ | U)` is well-defined and equals `1`. -/
theorem exercise_3_3_ii :
    let ε : ENNReal := ENNReal.ofReal (3 / 2)
    0 < ε ∧ ε < ⊤ ∧
    covering_number (absDiffDist ()) ε ex33U = 2 ∧
    covering_number (absDiffDist ()) ε (operator_image ex33Op ex33U) = 1 ∧
    MappingEntropyDiffWellDefined absDiffDist {()} {()} ε ex33Op ex33U ∧
    ∀ hwd : MappingEntropyDiffWellDefined absDiffDist {()} {()} ε ex33Op ex33U,
      mappingEntropyDiffCompSame absDiffDist () ε ex33Op ex33U hwd = 1 := by
  classical
  intro ε
  have hε_pos : 0 < ε := ENNReal.ofReal_pos.mpr (by norm_num)
  have hε_fin : ε < ⊤ := ENNReal.ofReal_lt_top
  have hcovU : covering_number (absDiffDist ()) ε ex33U = 2 := by
    apply le_antisymm
    · have hnet : InternalEpsilonNet (absDiffDist ()) ε ex33U {some 0, some 2} := by
        constructor
        · intro c hc
          simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
            Set.mem_singleton_iff] at hc
          rcases hc with rfl | rfl
          · exact Or.inr (Or.inr (Or.inl rfl))
          · exact Or.inr (Or.inr (Or.inr rfl))
        · intro x hx
          rcases hx with rfl | rfl | rfl | rfl
          · refine ⟨some 2, by simp, ?_⟩
            simp only [absDiffDist, ε]
            apply (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 3 / 2)).mpr
            norm_num
          · refine ⟨some 2, by simp, ?_⟩
            simp only [absDiffDist, ε]
            apply (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 3 / 2)).mpr
            norm_num
          · refine ⟨some 0, by simp, ?_⟩
            simp only [absDiffDist, ε]
            apply (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 3 / 2)).mpr
            norm_num
          · refine ⟨some 2, by simp, ?_⟩
            simp only [absDiffDist, ε]
            apply (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 3 / 2)).mpr
            norm_num
      have hcard : ({some (0 : ℝ), some (2 : ℝ)} : Finset RealWithBot).card = 2 := by
        rw [Finset.card_pair (by simp)]
      simpa [hcard] using covering_number_le_of_net hnet
    · rw [le_covering_number_iff]
      intro S hS
      have h0_mem : some (0 : ℝ) ∈ S := by
        rcases hS.2 (some 0) (Or.inr (Or.inr (Or.inl rfl))) with ⟨c, hcS, hdist⟩
        rcases hS.1 hcS with rfl | rfl | rfl | rfl
        · exfalso
          simp only [absDiffDist, ε] at hdist
          have hlt := (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 3 / 2)).mp hdist
          norm_num at hlt
        · exfalso
          simp only [absDiffDist, ε] at hdist
          have hlt := (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 3 / 2)).mp hdist
          norm_num at hlt
        · exact hcS
        · exfalso
          simp only [absDiffDist, ε] at hdist
          have hlt := (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 3 / 2)).mp hdist
          norm_num at hlt
      rcases hS.2 (some 2) (Or.inr (Or.inr (Or.inr rfl))) with ⟨c₂, hc₂S, hdist₂⟩
      have hc₂_ne : c₂ ≠ some (0 : ℝ) := by
        rintro rfl
        simp only [absDiffDist, ε] at hdist₂
        have hlt := (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 3 / 2)).mp hdist₂
        norm_num at hlt
      have hsub : ({some (0 : ℝ), c₂} : Finset RealWithBot) ⊆ S := by
        intro c hc
        simp only [Finset.mem_insert, Finset.mem_singleton] at hc
        rcases hc with rfl | rfl <;> assumption
      have hcard : 2 ≤ S.card := by
        calc
          2 = ({some (0 : ℝ), c₂} : Finset RealWithBot).card :=
              (Finset.card_pair hc₂_ne.symm).symm
          _ ≤ S.card := Finset.card_le_card hsub
      exact_mod_cast hcard
  have hcovImg : covering_number (absDiffDist ()) ε (operator_image ex33Op ex33U) = 1 := by
    have himg_ne : (operator_image ex33Op ex33U).Nonempty :=
      ⟨ex33Op.func (some (-3)), ⟨some (-3), Or.inl rfl, rfl⟩⟩
    apply le_antisymm
    · have hnet : InternalEpsilonNet (absDiffDist ()) ε (operator_image ex33Op ex33U)
          {ex33Op.func (some (-3))} := by
        constructor
        · intro c hc
          simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hc
          subst hc
          exact ⟨some (-3), Or.inl rfl, rfl⟩
        · rintro y ⟨x, hx, rfl⟩
          refine ⟨ex33Op.func (some (-3)), Finset.mem_singleton_self _, ?_⟩
          rcases hx with rfl | rfl | rfl | rfl <;>
            (simp only [ex33Op, absDiffDist, ε]
             apply (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 3 / 2)).mpr
             norm_num)
      simpa using covering_number_le_of_net hnet
    · exact one_le_covering_number_of_nonempty _ _ _ himg_ne
  have hwd : MappingEntropyDiffWellDefined absDiffDist {()} {()} ε ex33Op ex33U := by
    rw [mappingEntropyDiffWellDefined_comp_iff]
    left
    rw [hcovU]
    exact ENNReal.ofNat_lt_top
  refine ⟨hε_pos, hε_fin, hcovU, hcovImg, hwd, ?_⟩
  intro hwd'
  change mappingEntropyDiffComp absDiffDist () () ε ex33Op ex33U hwd' = 1
  rw [mappingEntropyDiffComp_eq, metric_entropy, metric_entropy, hcovU, hcovImg,
      log2_ereal_two, log2_ereal_one, sub_zero]

end Ch03
