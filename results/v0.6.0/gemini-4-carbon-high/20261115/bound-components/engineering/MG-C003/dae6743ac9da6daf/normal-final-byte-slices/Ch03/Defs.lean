import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.metric_entropy
import formal_oet.vol_01.ch_01_foundations.operator_space
import formal_oet.vol_01.ch_02_operator_bounds.lip_matrix
import formal_oet.vol_01.ch_02_operator_bounds.decoupling
import formal_oet.vol_01.ch_02_operator_bounds.single_channel

namespace Ch03

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set

/-!
# Chapter 3 Core Definitions & Representation Bridges (`CH03-D01` – `CH03-D08`)
-/

/-! ## `CH03-D01`: 分量分划 (Component Partition) -/

/-- 常值分量 `I_const(ϕ | U)`：在 `U` 上使输出两两 `d_i`-零距的分量集合。 -/
def constComponents {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) : Set I :=
  { i : I | ∀ x ∈ U, ∀ y ∈ U, d i (ϕ.func x) (ϕ.func y) = 0 }

/-- 恒等分量 `I_id(ϕ | U)`：常值优先排除 `I_const(ϕ | U)` 后，满足输入输出逐点 `d_i`-零距的分量集合。 -/
def idComponents {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) : Set I :=
  { i : I | i ∉ constComponents d ϕ U ∧ ∀ x ∈ U, d i (ϕ.func x) x = 0 }

/-- 有效分量 `I_act(ϕ | U)`：既非常值分量也非恒等分量的其余指标集合。 -/
def actComponents {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) : Set I :=
  Set.univ \ (constComponents d ϕ U ∪ idComponents d ϕ U)

/-- 全域常值分量 `I_const(ϕ)`（即 `U = dom(ϕ)`）。 -/
def globalConstComponents {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) : Set I :=
  constComponents d ϕ (dom ϕ)

/-- 全域恒等分量 `I_id(ϕ)`（即 `U = dom(ϕ)`）。 -/
def globalIdComponents {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) : Set I :=
  idComponents d ϕ (dom ϕ)

/-- 全域有效分量 `I_act(ϕ)`（即 `U = dom(ϕ)`）。 -/
def globalActComponents {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) : Set I :=
  actComponents d ϕ (dom ϕ)

/-- 分量分划的三部分两两不交且并集为全指标集 `I`。 -/
theorem component_partition_props {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) :
    Disjoint (constComponents d ϕ U) (idComponents d ϕ U) ∧
    Disjoint (constComponents d ϕ U) (actComponents d ϕ U) ∧
    Disjoint (idComponents d ϕ U) (actComponents d ϕ U) ∧
    constComponents d ϕ U ∪ idComponents d ϕ U ∪ actComponents d ϕ U = Set.univ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Set.disjoint_left.mpr (fun _ hc hid => hid.1 hc)
  · exact Set.disjoint_left.mpr (fun _ hc hact => hact.2 (Or.inl hc))
  · exact Set.disjoint_left.mpr (fun _ hid hact => hact.2 (Or.inr hid))
  · ext i
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    by_cases h : i ∈ constComponents d ϕ U ∪ idComponents d ϕ U
    · exact Or.inl h
    · exact Or.inr ⟨ trivial, h ⟩

/-- 复合算子限制域自动落入内侧定义域并将像集送入外侧定义域。 -/
theorem dom_comp_subset {X : Type} {bot : X}
    (ϕ₁ ϕ₂ : Operator X bot) (U : Set X)
    (hU : U ⊆ dom (operator_compose ϕ₂ ϕ₁)) :
    U ⊆ dom ϕ₁ ∧ operator_image ϕ₁ U ⊆ dom ϕ₂ := by
  constructor
  · intro x hx
    have hcomp : ϕ₂.func (ϕ₁.func x) ≠ bot := hU hx
    intro hbot
    rw [hbot, ϕ₂.preserves_bot] at hcomp
    exact hcomp rfl
  · rintro y ⟨x, hx, rfl⟩
    exact hU hx

/-! ## `CH03-D02`: 计算纤维 (Computational Fiber) -/

/-- 非空子族复合伪度量为零当且仅当各分量伪度量均为零。 -/
theorem subfamily_pseudometric_eq_zero_iff {X I : Type}
    (d : I → X → X → ENNReal) (J : Set I) (hJ : J.Nonempty) (x y : X) :
    subfamily_pseudometric d J x y = 0 ↔ ∀ j ∈ J, d j x y = 0 := by
  have _ := hJ
  constructor
  · intro h0 j hj
    apply le_antisymm _ (zero_le _)
    have hle : d j x y ≤ subfamily_pseudometric d J x y :=
      le_iSup (fun k : {k // k ∈ J} => d k.1 x y) ⟨j, hj⟩
    simpa [h0] using hle
  · intro hall
    apply le_antisymm _ (zero_le _)
    dsimp [subfamily_pseudometric]
    apply iSup_le
    intro j
    rw [hall j.1 j.2]

/-- 有限指标集上非空子族复合伪度量由某个分量取得最大值（与正文 `max_{j ∈ J}` 对应）。 -/
theorem subfamily_pseudometric_attained {X I : Type} [Fintype I]
    (d : I → X → X → ENNReal) (J : Set I) (hJ : J.Nonempty) (x y : X) :
    ∃ j ∈ J, subfamily_pseudometric d J x y = d j x y := by
  classical
  have hfin : (J.toFinset).Nonempty := by
    rcases hJ with ⟨j₀, hj₀⟩
    exact ⟨j₀, Set.mem_toFinset.mpr hj₀⟩
  obtain ⟨j₀, hj₀, hmax⟩ := Finset.exists_max_image J.toFinset (fun j => d j x y) hfin
  have hj₀_mem : j₀ ∈ J := Set.mem_toFinset.mp hj₀
  refine ⟨j₀, hj₀_mem, ?_⟩
  apply le_antisymm
  · dsimp [subfamily_pseudometric]
    apply iSup_le
    intro j
    exact hmax j.1 (Set.mem_toFinset.mpr j.2)
  · exact le_iSup (fun k : {k // k ∈ J} => d k.1 x y) ⟨j₀, hj₀_mem⟩

/-- 计算纤维 `Fib_{ϕ, J}(y | U)`：`U` 中输出与目标 `y` 关于 `d_J` 零距的点集。 -/
def compFiber {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    (J : Set I) (y : X) (U : Set X) : Set X :=
  { x ∈ U | subfamily_pseudometric d J (ϕ.func x) y = 0 }

/-- 全域计算纤维 `Fib_{ϕ, J}(y)`（即 `U = dom(ϕ)`）。 -/
def globalCompFiber {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    (J : Set I) (y : X) : Set X :=
  compFiber d ϕ J y (dom ϕ)

/-- 单分量计算纤维 `Fib_{ϕ, j}(y | U)`。 -/
def singleCompFiber {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    (j : I) (y : X) (U : Set X) : Set X :=
  { x ∈ U | d j (ϕ.func x) y = 0 }

/-- 全域单分量计算纤维 `Fib_{ϕ, j}(y)`。 -/
def globalSingleCompFiber {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    (j : I) (y : X) : Set X :=
  singleCompFiber d ϕ j y (dom ϕ)

/-- 单元素子族的计算纤维与单分量计算纤维一致。 -/
theorem compFiber_singleton_eq {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    (j : I) (y : X) (U : Set X) :
    compFiber d ϕ ({j} : Set I) y U = singleCompFiber d ϕ j y U := by
  ext x
  simp [compFiber, singleCompFiber, subfamily_pseudometric_singleton]

/-! ## `CH03-D03`: 点值和零距关系、像商、纤维预序 -/

/-- 受限域上的点值相等关系 `R_=(ϕ | U)`。 -/
def relEq {X : Type} {bot : X} (ϕ : Operator X bot) (U : Set X) : Set (X × X) :=
  { p : X × X | p.1 ∈ U ∧ p.2 ∈ U ∧ ϕ.func p.1 = ϕ.func p.2 }

/-- 受限域上的族零距关系 `R_∼(ϕ | U)`。 -/
def relZero {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) : Set (X × X) :=
  { p : X × X | p.1 ∈ U ∧ p.2 ∈ U ∧ GaugeZeroRelated d (ϕ.func p.1) (ϕ.func p.2) }

/-- 正文等价表达：对 `x, y ∈ U`，`(x, y) ∈ R_∼(ϕ | U)` 当且仅当 `y ∈ Fib_{ϕ, I}(ϕ(x) | U)`。 -/
theorem mem_relZero_iff_mem_compFiber_univ {X I : Type} {bot : X} [Nonempty I]
    (d : I → X → X → ENNReal)
    (symm : ∀ i x y, d i x y = d i y x)
    (ϕ : Operator X bot) (U : Set X) {x y : X} (hx : x ∈ U) :
    (x, y) ∈ relZero d ϕ U ↔ y ∈ compFiber d ϕ Set.univ (ϕ.func x) U := by
  have huniv : (Set.univ : Set I).Nonempty := Set.univ_nonempty
  simp only [relZero, Set.mem_setOf_eq, hx, true_and, compFiber,
    subfamily_pseudometric_eq_zero_iff d Set.univ huniv, Set.mem_univ, forall_true_left,
    GaugeZeroRelated]
  constructor
  · intro ⟨hy, hzero⟩
    refine ⟨hy, fun i => ?_⟩
    rw [symm i]
    exact hzero i
  · intro ⟨hy, hzero⟩
    refine ⟨hy, fun i => ?_⟩
    rw [symm i]
    exact hzero i

/-- 规范族限制到任意子集 `S` 上的零距等价关系 `Setoid`。 -/
def subsetZeroSetoid {X I : Type} {bot : X}
    (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (S : Set X) : Setoid S where
  r a b := GaugeZeroRelated d a.1 b.1
  iseqv := by
    have heq := gauge_zero_related_equivalence d
      (fun i => (hd i).dist_self)
      (fun i => (hd i).symm)
      (fun i => (hd i).triangle)
    exact ⟨fun a => heq.refl a.1, fun h => heq.symm h, fun h₁ h₂ => heq.trans h₁ h₂⟩

/-- 受限像集上的零距商 `ϕ(U) / ∼_G`。 -/
def ImageZeroQuotient {X I : Type} {bot : X}
    (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ : Operator X bot) (U : Set X) : Type :=
  Quotient (subsetZeroSetoid d hd (operator_image ϕ U))

/-- 将输入点 `x ∈ U` 映到像商类 `[ϕ(x)] ∈ ϕ(U) / ∼_G`。 -/
def imageZeroQuotMk {X I : Type} {bot : X}
    (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ : Operator X bot) (U : Set X) (x : X) (hx : x ∈ U) :
    ImageZeroQuotient d hd ϕ U :=
  Quotient.mk (subsetZeroSetoid d hd (operator_image ϕ U)) ⟨ϕ.func x, ⟨x, hx, rfl⟩⟩

/-- 规范族在子集 `S` 上分离：在 `S` 内全分量零距蕴含点值相等。 -/
def IsSeparatingOn {X I : Type} (d : I → X → X → ENNReal) (S : Set X) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, GaugeZeroRelated d x y → x = y

/-- 零测距纤维预序 `ϕ_A ⪰_{fiber, U} ϕ_B`：`R_∼(ϕ_A | U) ⊆ R_∼(ϕ_B | U)`。 -/
def FiberGe {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (U : Set X) (ϕA ϕB : Operator X bot) : Prop :=
  relZero d ϕA U ⊆ relZero d ϕB U

/-- 具有公共评估域 `U` 的算子子类型上的纤维预序实例。 -/
instance fiberGePreorderOnCommonDom {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (U : Set X) :
    Preorder { ϕ : Operator X bot // U ⊆ dom ϕ } where
  le a b := FiberGe d U b.1 a.1
  le_refl _ := Set.Subset.rfl
  le_trans _ _ _ hab hbc := Set.Subset.trans hbc hab

/-! ## `CH03-D04`: 点态零化半径 (Pointwise Nullification Radius) -/

/-- 有限正半径 `r ∈ (0, +∞)` 关于 `(ϕ, d_in, d_out, U, y)` 满足局部零化球包含条件。 -/
def IsNullifyingRadius {X : Type} {bot : X}
    (ϕ : Operator X bot) (d_in d_out : X → X → ENNReal)
    (U : Set X) (y : X) (r : ENNReal) : Prop :=
  0 < r ∧ r < ⊤ ∧ ball d_in y r ∩ U ⊆ { x ∈ U | d_out (ϕ.func x) (ϕ.func y) = 0 }

/-- 点态零化内切半径 `r^N_{ϕ, d_in, d_out}(y | U)`。无合法有限正半径时按 `ENNReal` 空上确界取 `0`。 -/
noncomputable def nullRadius {X : Type} {bot : X}
    (ϕ : Operator X bot) (d_in d_out : X → X → ENNReal)
    (y : X) (U : Set X) : ENNReal :=
  sSup { r : ENNReal | IsNullifyingRadius ϕ d_in d_out U y r }

/-- 全域点态零化内切半径 `r^N_{ϕ, d_in, d_out}(y)`（即 `U = dom(ϕ)`）。 -/
noncomputable def globalNullRadius {X : Type} {bot : X}
    (ϕ : Operator X bot) (d_in d_out : X → X → ENNReal) (y : X) : ENNReal :=
  nullRadius ϕ d_in d_out y (dom ϕ)

/-- 输出取子族复合伪度量时的点态零化内切半径 `r^N_{ϕ, i, J}(y | U)`。 -/
noncomputable def nullRadiusSubfamily {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    (i : I) (J : Set I) (y : X) (U : Set X) : ENNReal :=
  nullRadius ϕ (d i) (subfamily_pseudometric d J) y U

/-- 单输入分量 `i`、单输出分量 `j` 的点态零化内切半径 `r^N_{ϕ, i, j}(y | U)`。 -/
noncomputable def nullRadiusComp {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    (i j : I) (y : X) (U : Set X) : ENNReal :=
  nullRadius ϕ (d i) (d j) y U

/-- 子族输出零测距目标集恰为计算纤维 `Fib_{ϕ, J}(ϕ(y) | U)`。 -/
theorem nullRadiusSubfamily_target_eq_compFiber {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    (J : Set I) (y : X) (U : Set X) :
    { x ∈ U | subfamily_pseudometric d J (ϕ.func x) (ϕ.func y) = 0 } =
      compFiber d ϕ J (ϕ.func y) U := rfl

/-- 单元素输出子族的点态零化半径等于单分量点态零化半径。 -/
theorem nullRadiusSubfamily_singleton {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    (i j : I) (y : X) (U : Set X) :
    nullRadiusSubfamily d ϕ i ({j} : Set I) y U = nullRadiusComp d ϕ i j y U := by
  simp [nullRadiusSubfamily, nullRadiusComp, subfamily_pseudometric_singleton]

/-- 不存在合法有限正零化半径时，点态零化半径为 `0`。 -/
theorem nullRadius_eq_zero_of_empty {X : Type} {bot : X}
    (ϕ : Operator X bot) (d_in d_out : X → X → ENNReal) (y : X) (U : Set X)
    (h : ∀ r : ENNReal, ¬ IsNullifyingRadius ϕ d_in d_out U y r) :
    nullRadius ϕ d_in d_out y U = 0 := by
  have hemp : { r : ENNReal | IsNullifyingRadius ϕ d_in d_out U y r } = ∅ := by
    ext r
    simp [h r]
  simp [nullRadius, hemp]

/-- 统一工具引理：若所有满足 `0 < r < ⊤` 且 `r < M` 的有限正半径均合法，则 `M ≤ nullRadius`（同时覆盖 `M = 0`、有限正 `M` 与 `M = ⊤`）。 -/
theorem le_nullRadius_of_forall_lt {X : Type} {bot : X}
    (ϕ : Operator X bot) (d_in d_out : X → X → ENNReal) (y : X) (U : Set X)
    (M : ENNReal)
    (h : ∀ r : ENNReal, 0 < r → r < ⊤ → r < M →
      ball d_in y r ∩ U ⊆ { x ∈ U | d_out (ϕ.func x) (ϕ.func y) = 0 }) :
    M ≤ nullRadius ϕ d_in d_out y U := by
  by_cases hM0 : M = 0
  · simp [hM0]
  · by_cases hMtop : M = ⊤
    · subst hMtop
      rw [top_le_iff]
      by_contra hne_top
      set b := nullRadius ϕ d_in d_out y U
      have hb_lt_top : b < ⊤ := lt_top_iff_ne_top.mpr hne_top
      have h1_pos : (0 : ENNReal) < b + 1 := by simp
      have h1_lt_top : b + 1 < ⊤ := ENNReal.add_lt_top.mpr ⟨hb_lt_top, ENNReal.one_lt_top⟩
      have hadm : IsNullifyingRadius ϕ d_in d_out U y (b + 1) :=
        ⟨h1_pos, h1_lt_top, h (b + 1) h1_pos h1_lt_top h1_lt_top⟩
      have hle : b + 1 ≤ b := le_sSup hadm
      have hlt : b < b + 1 := ENNReal.lt_add_right hne_top one_ne_zero
      exact (not_lt_of_ge hle) hlt
    · have hM_pos : 0 < M := pos_iff_ne_zero.mpr hM0
      have hM_lt_top : M < ⊤ := lt_top_iff_ne_top.mpr hMtop
      apply le_of_forall_lt
      intro r hr
      by_cases hr0 : r = 0
      · subst hr0
        have hhalf_pos : 0 < M / 2 := ENNReal.div_pos hM0 (by simp)
        have hhalf_lt : M / 2 < M := ENNReal.half_lt_self hM0 hMtop
        have hhalf_lt_top : M / 2 < ⊤ := lt_trans hhalf_lt hM_lt_top
        have hadm : IsNullifyingRadius ϕ d_in d_out U y (M / 2) :=
          ⟨hhalf_pos, hhalf_lt_top, h (M / 2) hhalf_pos hhalf_lt_top hhalf_lt⟩
        exact lt_of_lt_of_le hhalf_pos (le_sSup hadm)
      · obtain ⟨q, hrq, hqM⟩ := exists_between hr
        have hq_pos : 0 < q := lt_trans (pos_iff_ne_zero.mpr hr0) hrq
        have hq_lt_top : q < ⊤ := lt_trans hqM hM_lt_top
        have hadm : IsNullifyingRadius ϕ d_in d_out U y q :=
          ⟨hq_pos, hq_lt_top, h q hq_pos hq_lt_top hqM⟩
        exact lt_of_lt_of_le hrq (le_sSup hadm)

/-! ## `CH03-D05`: 统一半径与零化矩阵 (Uniform Nullification Radius & Nullification Matrix) -/

/-- 基点集 `A` 关于评估域 `U` 的统一零化半径 `\underline{r}^N_{ϕ, d_in, d_out}(A | U)`。 -/
noncomputable def uniformNullRadiusOn {X : Type} {bot : X}
    (ϕ : Operator X bot) (d_in d_out : X → X → ENNReal)
    (A U : Set X) : ENNReal :=
  ⨅ y ∈ A, nullRadius ϕ d_in d_out y U

/-- 评估域 `U` 上的统一零化半径 `\underline{r}^N_{ϕ, d_in, d_out}|_U`（即 `A = U`）。 -/
noncomputable def uniformNullRadius {X : Type} {bot : X}
    (ϕ : Operator X bot) (d_in d_out : X → X → ENNReal)
    (U : Set X) : ENNReal :=
  uniformNullRadiusOn ϕ d_in d_out U U

/-- 全域统一零化半径 `\underline{r}^N_{ϕ, d_in, d_out}`（即 `A = U = dom(ϕ)`）。 -/
noncomputable def globalUniformNullRadius {X : Type} {bot : X}
    (ϕ : Operator X bot) (d_in d_out : X → X → ENNReal) : ENNReal :=
  uniformNullRadius ϕ d_in d_out (dom ϕ)

/-- 输出取子族复合伪度量时的统一零化半径 `\underline{r}^N_{ϕ, i, J}|_U`。 -/
noncomputable def uniformNullRadiusSubfamily {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    (i : I) (J : Set I) (U : Set X) : ENNReal :=
  uniformNullRadius ϕ (d i) (subfamily_pseudometric d J) U

/-- 单分量通道 `(i, j)` 在基点集 `A`、评估域 `U` 上的统一零化半径。 -/
noncomputable def uniformNullRadiusCompOn {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    (i j : I) (A U : Set X) : ENNReal :=
  uniformNullRadiusOn ϕ (d i) (d j) A U

/-- 单分量通道 `(i, j)` 在 `U` 上的统一零化半径 `\underline{r}^N_{ϕ, i, j}|_U`。 -/
noncomputable def uniformNullRadiusComp {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    (i j : I) (U : Set X) : ENNReal :=
  uniformNullRadius ϕ (d i) (d j) U

/-- 受限零化矩阵 `N(ϕ)|_U`：以输出分量 `j` 为行指标、输入分量 `i` 为列指标，`[N(ϕ)|_U]_{j, i} = \underline{r}^N_{ϕ, i, j}|_U`。 -/
noncomputable def nullMatrix {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) : I → I → ENNReal :=
  fun j i => uniformNullRadiusComp d ϕ i j U

/-- 全域零化矩阵 `N(ϕ)`（即 `U = dom(ϕ)`）。 -/
noncomputable def globalNullMatrix {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) : I → I → ENNReal :=
  nullMatrix d ϕ (dom ϕ)

/-! ## `CH03-D06`: 输入尺度与阈值分类 (Input Scale & Threshold Classification) -/

/-- 输入尺度函数族谓词：对任意非空子集 `A₁ ⊆ A₂`，每个分量尺度单调不减。 -/
def IsInputScaleFamily {X I : Type} (σ : I → Set X → ENNReal) : Prop :=
  ∀ i : I, ∀ ⦃A₁ A₂ : Set X⦄, A₁.Nonempty → A₂.Nonempty → A₁ ⊆ A₂ → σ i A₁ ≤ σ i A₂

/-- 伪度量 `d` 下的集合直径 `diam_d(A) = sup_{x, y ∈ A} d(x, y)`。 -/
noncomputable def setDiam {X : Type} (d : X → X → ENNReal) (A : Set X) : ENNReal :=
  ⨆ x ∈ A, ⨆ y ∈ A, d x y

/-- 默认直径输入尺度函数族 `σ_i(A) = diam_{d_i}(A)`。 -/
noncomputable def diamScaleFamily {X I : Type}
    (d : I → X → X → ENNReal) : I → Set X → ENNReal :=
  fun i A => setDiam (d i) A

/-- 默认直径尺度族是合法输入尺度函数族。 -/
theorem diamScaleFamily_isInputScaleFamily {X I : Type}
    (d : I → X → X → ENNReal) :
    IsInputScaleFamily (diamScaleFamily d) := by
  intro i A₁ A₂ _ _ hsub
  dsimp [diamScaleFamily, setDiam]
  apply iSup₂_le
  intro x hx
  apply iSup₂_le
  intro y hy
  exact le_iSup₂_of_le x (hsub hx) (le_iSup₂_of_le y (hsub hy) le_rfl)

/-- 有限正阈值条件 `0 < τ < +∞`。 -/
def IsFinitePosThreshold (τ : ENNReal) : Prop :=
  0 < τ ∧ τ < ⊤

/-- 命题的 `{0, 1}` 指示函数。 -/
noncomputable def ind01 (P : Prop) : ℕ := by
  classical
  exact if P then 1 else 0

/-- 通道 `(i, j)` 的两项阈值分类 `Type_{f, A}(i, j) ∈ {0, 1}²`。 -/
noncomputable def channelType {X I : Type} {bot : X}
    (σ : I → Set X → ENNReal) (τ_σ τ_N : ENNReal)
    (d : I → X → X → ENNReal) (f : Operator X bot) (A : Set X)
    (i j : I) : ℕ × ℕ :=
  (ind01 (σ i A < τ_σ), ind01 (τ_N ≤ uniformNullRadiusComp d f i j A))

/-! ## `CH03-D07`: 内部覆盖数、熵与全有界接口 -/

/-- 子族覆盖数 `N_J(ε, U)`：关于子族复合伪度量 `d_J` 的 `ε`-内覆盖数。 -/
noncomputable def subfamilyCoveringNumber {X I : Type}
    (d : I → X → X → ENNReal) (J : Set I) (ε : ENNReal) (U : Set X) : ENNReal :=
  covering_number (subfamily_pseudometric d J) ε U

/-- 单元素子族覆盖数退化为单分量覆盖数。 -/
theorem subfamilyCoveringNumber_singleton {X I : Type}
    (d : I → X → X → ENNReal) (i : I) (ε : ENNReal) (U : Set X) :
    subfamilyCoveringNumber d ({i} : Set I) ε U = covering_number (d i) ε U := by
  rw [subfamilyCoveringNumber, subfamily_pseudometric_singleton]

/-- 子集 `U` 在扩展伪度量 `d` 下全有界：`∀ r ∈ (0, +∞)`，`N(r, U) < ∞`。 -/
def IsTotallyBounded {X : Type} (d : X → X → ENNReal) (U : Set X) : Prop :=
  ∀ r : ENNReal, 0 < r → r < ⊤ → covering_number d r U < ⊤

/-- 冻结模块中的 `InternalEpsilonNet` 与正文内部开球覆盖 `S ⊆ U ∧ U ⊆ ⋃_{s ∈ S} B(s, ε)` 完全等价。 -/
theorem internalEpsilonNet_iff_ball_cover {X : Type}
    (d : X → X → ENNReal) (ε : ENNReal) (U : Set X) (S : Finset X) :
    InternalEpsilonNet d ε U S ↔
      (↑S : Set X) ⊆ U ∧ U ⊆ ⋃ s ∈ S, ball d s ε := by
  constructor
  · rintro ⟨hSU, hcov⟩
    refine ⟨hSU, fun x hx => ?_⟩
    rcases hcov x hx with ⟨s, hs, hdist⟩
    exact Set.mem_biUnion hs hdist
  · rintro ⟨hSU, hcov⟩
    refine ⟨hSU, fun x hx => ?_⟩
    have hmem := hcov hx
    rcases Set.mem_iUnion₂.mp hmem with ⟨s, hs, hdist⟩
    exact ⟨s, hs, hdist⟩

/-- 冻结 `covering_number` 与第1/3章内覆盖数定义的完整对应：空集为 `0`，可有限内覆盖时取最小内部中心数，否则取 `⊤`。 -/
theorem covering_number_textbook_correspondence {X : Type}
    (d : X → X → ENNReal) (ε : ENNReal) (U : Set X) :
    covering_number d ε (∅ : Set X) = 0 ∧
    ((∃ S : Finset X, (↑S : Set X) ⊆ U ∧ U ⊆ ⋃ s ∈ S, ball d s ε) →
      ∃ S : Finset X, ((↑S : Set X) ⊆ U ∧ U ⊆ ⋃ s ∈ S, ball d s ε) ∧
        covering_number d ε U = (S.card : ENNReal) ∧
        ∀ T : Finset X, ((↑T : Set X) ⊆ U ∧ U ⊆ ⋃ t ∈ T, ball d t ε) → S.card ≤ T.card) ∧
    (covering_number d ε U = ⊤ ↔
      ¬ ∃ S : Finset X, (↑S : Set X) ⊆ U ∧ U ⊆ ⋃ s ∈ S, ball d s ε) := by
  refine ⟨covering_number_empty d ε, ?_, ?_⟩
  · intro hfin
    have hfin' : ∃ S : Finset X, InternalEpsilonNet d ε U S := by
      rcases hfin with ⟨S, hS⟩
      exact ⟨S, (internalEpsilonNet_iff_ball_cover d ε U S).mpr hS⟩
    obtain ⟨S, hS, hcard, hmin⟩ := covering_number_attained d ε U hfin'
    refine ⟨S, (internalEpsilonNet_iff_ball_cover d ε U S).mp hS, hcard, ?_⟩
    intro T hT
    exact hmin T ((internalEpsilonNet_iff_ball_cover d ε U T).mpr hT)
  · rw [covering_number_eq_top_iff]
    constructor
    · intro hnot ⟨S, hS⟩
      exact hnot ⟨S, (internalEpsilonNet_iff_ball_cover d ε U S).mpr hS⟩
    · intro hnot ⟨S, hS⟩
      exact hnot ⟨S, (internalEpsilonNet_iff_ball_cover d ε U S).mp hS⟩

/-- 全有界当且仅当对每个有限正精度 `r ∈ (0, +∞)` 均存在有限内覆盖。 -/
theorem isTotallyBounded_iff_exists_internalNet {X : Type}
    (d : X → X → ENNReal) (U : Set X) :
    IsTotallyBounded d U ↔
      ∀ r : ENNReal, 0 < r → r < ⊤ → ∃ S : Finset X, InternalEpsilonNet d r U S := by
  constructor
  · intro htb r hr_pos hr_top
    have hlt := htb r hr_pos hr_top
    by_contra hno
    have htop := (covering_number_eq_top_iff d r U).mpr hno
    exact (ne_of_lt hlt) htop
  · intro hex r hr_pos hr_top
    rw [lt_top_iff_ne_top]
    intro htop
    exact ((covering_number_eq_top_iff d r U).mp htop) (hex r hr_pos hr_top)

/-- `log2_ereal` 在整个 `ENNReal` 上单调不减。 -/
theorem log2_ereal_mono : Monotone log2_ereal := by
  intro x y hxy
  by_cases hx0 : x = 0
  · subst hx0
    simp [log2_ereal]
  · have hy0 : y ≠ 0 := ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.mpr hx0) hxy)
    by_cases hytop : y = ⊤
    · subst hytop
      simp [log2_ereal]
    · have hxtop : x ≠ ⊤ := ne_of_lt (lt_of_le_of_lt hxy (lt_top_iff_ne_top.mpr hytop))
      simp only [log2_ereal, if_neg hx0, if_neg hxtop, if_neg hy0, if_neg hytop]
      apply EReal.coe_le_coe_iff.mpr
      exact Real.logb_le_logb_of_le one_lt_two
        (ENNReal.toReal_pos hx0 hxtop)
        (ENNReal.toReal_mono hytop hxy)

/-! ## `CH03-D08`: 映射熵差 (Mapping Entropy Difference) -/

/-- 映射熵差 `\Delta E_{ε, J_in, J_out}(ϕ | U)` 的良定性前提：
`∅ ≠ U ⊆ dom(ϕ)`，`J_in, J_out` 非空，`0 < ε < +∞`，且输入与输出覆盖数不全为 `+∞`（严格排除 `+∞ - +∞`）。 -/
def MappingEntropyDiffDefined {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    (J_in J_out : Set I) (ε : ENNReal) : Prop :=
  U.Nonempty ∧ U ⊆ dom ϕ ∧ J_in.Nonempty ∧ J_out.Nonempty ∧
    0 < ε ∧ ε < ⊤ ∧
    (subfamilyCoveringNumber d J_in ε U < ⊤ ∨
      subfamilyCoveringNumber d J_out ε (operator_image ϕ U) < ⊤)

/-- 同子族映射熵差 `\Delta E_{ε, J}(ϕ | U)` 的良定性前提。 -/
def MappingEntropyDiffSameDefined {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    (J : Set I) (ε : ENNReal) : Prop :=
  MappingEntropyDiffDefined d ϕ U J J ε

/-- 单通道映射熵差 `\Delta E_{ε, i, j}(ϕ | U)` 的良定性前提。 -/
def MappingEntropyDiffCompDefined {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    (i j : I) (ε : ENNReal) : Prop :=
  MappingEntropyDiffDefined d ϕ U ({i} : Set I) ({j} : Set I) ε

/-- 同分量映射熵差 `\Delta E_{ε, j}(ϕ | U)` 的良定性前提。 -/
def MappingEntropyDiffSingleDefined {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    (j : I) (ε : ENNReal) : Prop :=
  MappingEntropyDiffDefined d ϕ U ({j} : Set I) ({j} : Set I) ε

/-- 映射熵差 `\Delta E_{ε, J_in, J_out}(ϕ | U) ∈ [-∞, +∞]`。
通过依赖参数 `hdef` 在类型层面排除 `+∞ - +∞` 不定形，并显式按两端有限/无穷分支构造。 -/
noncomputable def mappingEntropyDiff {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    (J_in J_out : Set I) (ε : ENNReal)
    (hdef : MappingEntropyDiffDefined d ϕ U J_in J_out ε) : EReal := by
  classical
  exact
    if hin : subfamilyCoveringNumber d J_in ε U < ⊤ then
      if hout : subfamilyCoveringNumber d J_out ε (operator_image ϕ U) < ⊤ then
        ((Real.logb 2 (subfamilyCoveringNumber d J_in ε U).toReal -
            Real.logb 2 (subfamilyCoveringNumber d J_out ε (operator_image ϕ U)).toReal : ℝ) : EReal)
      else
        ⊥
    else
      if hout : subfamilyCoveringNumber d J_out ε (operator_image ϕ U) < ⊤ then
        ⊤
      else
        False.elim (by
          rcases hdef.2.2.2.2.2.2 with h₁ | h₂
          · exact hin h₁
          · exact hout h₂)

/-- 同子族映射熵差简写 `\Delta E_{ε, J}(ϕ | U)`。 -/
noncomputable def mappingEntropyDiffSame {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    (J : Set I) (ε : ENNReal)
    (hdef : MappingEntropyDiffSameDefined d ϕ U J ε) : EReal :=
  mappingEntropyDiff d ϕ U J J ε hdef

/-- 单通道映射熵差简写 `\Delta E_{ε, i, j}(ϕ | U)`。 -/
noncomputable def mappingEntropyDiffComp {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    (i j : I) (ε : ENNReal)
    (hdef : MappingEntropyDiffCompDefined d ϕ U i j ε) : EReal :=
  mappingEntropyDiff d ϕ U ({i} : Set I) ({j} : Set I) ε hdef

/-- 单同分量映射熵差简写 `\Delta E_{ε, j}(ϕ | U)`。 -/
noncomputable def mappingEntropyDiffSingle {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    (j : I) (ε : ENNReal)
    (hdef : MappingEntropyDiffSingleDefined d ϕ U j ε) : EReal :=
  mappingEntropyDiff d ϕ U ({j} : Set I) ({j} : Set I) ε hdef

/-- 在良定性前提下，`mappingEntropyDiff` 等于 `E_{ε, J_in}(U) - E_{ε, J_out}(ϕ(U))`，且严格满足正文三分支规则。 -/
theorem mappingEntropyDiff_eq_sub {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    (J_in J_out : Set I) (ε : ENNReal)
    (hdef : MappingEntropyDiffDefined d ϕ U J_in J_out ε) :
    mappingEntropyDiff d ϕ U J_in J_out ε hdef =
      subfamily_metric_entropy d J_in ε U -
        subfamily_metric_entropy d J_out ε (operator_image ϕ U) := by
  classical
  have hU_ne : U.Nonempty := hdef.1
  have himg_ne : (operator_image ϕ U).Nonempty := hU_ne.image ϕ.func
  have hc_in_ge1 : (1 : ENNReal) ≤ subfamilyCoveringNumber d J_in ε U :=
    one_le_covering_number_of_nonempty _ ε U hU_ne
  have hc_out_ge1 : (1 : ENNReal) ≤ subfamilyCoveringNumber d J_out ε (operator_image ϕ U) :=
    one_le_covering_number_of_nonempty _ ε (operator_image ϕ U) himg_ne
  have hc_in_ne0 : subfamilyCoveringNumber d J_in ε U ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one hc_in_ge1)
  have hc_out_ne0 : subfamilyCoveringNumber d J_out ε (operator_image ϕ U) ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one hc_out_ge1)
  unfold subfamilyCoveringNumber at hc_in_ne0 hc_out_ne0
  unfold mappingEntropyDiff subfamily_metric_entropy subfamilyCoveringNumber
  by_cases hin : covering_number (subfamily_pseudometric d J_in) ε U < ⊤
  · have hin_ne_top : covering_number (subfamily_pseudometric d J_in) ε U ≠ ⊤ := ne_of_lt hin
    by_cases hout : covering_number (subfamily_pseudometric d J_out) ε (operator_image ϕ U) < ⊤
    · have hout_ne_top :
          covering_number (subfamily_pseudometric d J_out) ε (operator_image ϕ U) ≠ ⊤ :=
        ne_of_lt hout
      simp [hin, hout, log2_ereal, hc_in_ne0, hin_ne_top,
        hc_out_ne0, hout_ne_top, EReal.coe_sub]
    · have hout_top :
          covering_number (subfamily_pseudometric d J_out) ε (operator_image ϕ U) = ⊤ :=
        not_lt_top_iff.mp hout
      simp [hin, hout_top, log2_ereal, hc_in_ne0, hin_ne_top]
  · have hin_top : covering_number (subfamily_pseudometric d J_in) ε U = ⊤ :=
      not_lt_top_iff.mp hin
    have hout : covering_number (subfamily_pseudometric d J_out) ε (operator_image ϕ U) < ⊤ := by
      rcases hdef.2.2.2.2.2.2 with h₁ | h₂
      · exact False.elim (hin h₁)
      · exact h₂
    have hout_ne_top :
        covering_number (subfamily_pseudometric d J_out) ε (operator_image ϕ U) ≠ ⊤ :=
      ne_of_lt hout
    have hsub_top :
        (⊤ : EReal) - ↑(Real.logb 2
          (covering_number (subfamily_pseudometric d J_out) ε (operator_image ϕ U)).toReal) = ⊤ := by
      rfl
    simp [hin_top, hout, log2_ereal, hc_out_ne0, hout_ne_top, hsub_top]

end Ch03
