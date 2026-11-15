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
 
/-! ### CH03-D01: 分量分划 -/
 
/-- 常值分量 `I_const(ϕ | U)`：在受限域 `U` 上输出两两零距的分量指标集合。 -/
def I_const {X I : Type} {bot : X} (d : I → X → X → ENNReal)
    (ϕ : Operator X bot) (U : Set X) : Set I :=
  {i : I | ∀ x ∈ U, ∀ y ∈ U, d i (ϕ.func x) (ϕ.func y) = 0}
 
/-- 恒等分量 `I_id(ϕ | U)`：按常值优先排除 `I_const(ϕ | U)` 后，在 `U` 上输出与输入逐点零距的分量指标集合。 -/
def I_id {X I : Type} {bot : X} (d : I → X → X → ENNReal)
    (ϕ : Operator X bot) (U : Set X) : Set I :=
  {i : I | i ∉ I_const d ϕ U ∧ ∀ x ∈ U, d i (ϕ.func x) x = 0}
 
/-- 有效分量 `I_act(ϕ | U) = I \ (I_const(ϕ | U) ∪ I_id(ϕ | U))`。 -/
def I_act {X I : Type} {bot : X} (d : I → X → X → ENNReal)
    (ϕ : Operator X bot) (U : Set X) : Set I :=
  Set.univ \ (I_const d ϕ U ∪ I_id d ϕ U)
 
/-- 全域常值分量 `I_const(ϕ) := I_const(ϕ | dom(ϕ))`。 -/
def I_const_global {X I : Type} {bot : X} (d : I → X → X → ENNReal)
    (ϕ : Operator X bot) : Set I :=
  I_const d ϕ (dom ϕ)
 
/-- 全域恒等分量 `I_id(ϕ) := I_id(ϕ | dom(ϕ))`。 -/
def I_id_global {X I : Type} {bot : X} (d : I → X → X → ENNReal)
    (ϕ : Operator X bot) : Set I :=
  I_id d ϕ (dom ϕ)
 
/-- 全域有效分量 `I_act(ϕ) := I_act(ϕ | dom(ϕ))`。 -/
def I_act_global {X I : Type} {bot : X} (d : I → X → X → ENNReal)
    (ϕ : Operator X bot) : Set I :=
  I_act d ϕ (dom ϕ)
 
/-- 分量分划两两不交且覆盖全体指标集 `I`，并满足常值优先约定。 -/
theorem component_partition_props {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) :
    Disjoint (I_const d ϕ U) (I_id d ϕ U) ∧
    Disjoint (I_const d ϕ U) (I_act d ϕ U) ∧
    Disjoint (I_id d ϕ U) (I_act d ϕ U) ∧
    I_const d ϕ U ∪ I_id d ϕ U ∪ I_act d ϕ U = Set.univ ∧
    (∀ i : I,
      (∀ x ∈ U, ∀ y ∈ U, d i (ϕ.func x) (ϕ.func y) = 0) →
      (∀ x ∈ U, d i (ϕ.func x) x = 0) →
      i ∈ I_const d ϕ U ∧ i ∉ I_id d ϕ U) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact Set.disjoint_left.mpr (fun _ hc hid => hid.1 hc)
  · exact Set.disjoint_left.mpr (fun _ hc hact => hact.2 (Or.inl hc))
  · exact Set.disjoint_left.mpr (fun _ hid hact => hact.2 (Or.inr hid))
  · ext i
    simp only [I_act, Set.mem_union, Set.mem_diff, Set.mem_univ, true_and]
    tauto
  · intro i hconst _
    exact ⟨hconst, fun hid => hid.1 hconst⟩
 
/-! ### CH03-D02: 计算纤维 -/
 
/-- 受限计算纤维 `Fib_{ϕ, J}(y | U) := {x ∈ U | d_J(ϕ(x), y) = 0}`。 -/
def CompFiber {X I : Type} {bot : X} (d : I → X → X → ENNReal)
    (ϕ : Operator X bot) (J : Set I) (y : X) (U : Set X) : Set X :=
  {x ∈ U | subfamily_pseudometric d J (ϕ.func x) y = 0}
 
/-- 全域计算纤维 `Fib_{ϕ, J}(y) := Fib_{ϕ, J}(y | dom(ϕ))`。 -/
def CompFiberGlobal {X I : Type} {bot : X} (d : I → X → X → ENNReal)
    (ϕ : Operator X bot) (J : Set I) (y : X) : Set X :=
  CompFiber d ϕ J y (dom ϕ)
 
/-- 单分量计算纤维 `Fib_{ϕ, j}(y | U)`。 -/
def CompFiberSingle {X I : Type} {bot : X} (d : I → X → X → ENNReal)
    (ϕ : Operator X bot) (j : I) (y : X) (U : Set X) : Set X :=
  CompFiber d ϕ {j} y U
 
theorem CompFiberSingle_eq {X I : Type} {bot : X} (d : I → X → X → ENNReal)
    (ϕ : Operator X bot) (j : I) (y : X) (U : Set X) :
    CompFiberSingle d ϕ j y U = {x ∈ U | d j (ϕ.func x) y = 0} := by
  unfold CompFiberSingle CompFiber
  rw [subfamily_pseudometric_singleton]
 
theorem CompFiber_eq_empty_of_pos_dist {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (J : Set I) (y : X) (U : Set X)
    (hpos : ∀ z ∈ operator_image ϕ U, 0 < subfamily_pseudometric d J z y) :
    CompFiber d ϕ J y U = ∅ := by
  ext x
  simp only [CompFiber, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro hxU hzero
  exact (ne_of_gt (hpos (ϕ.func x) ⟨x, hxU, rfl⟩)) hzero
 
/-! ### CH03-D03: 点值和零距关系、像商、纤维预序 -/
 
/-- 点值相等点对集 `ℛ_{=}(ϕ | U) = {(x, y) ∈ U × U : ϕ(x) = ϕ(y)}`。 -/
def RelEq {X : Type} {bot : X} (ϕ : Operator X bot) (U : Set X) : Set (X × X) :=
  {p : X × X | p.1 ∈ U ∧ p.2 ∈ U ∧ ϕ.func p.1 = ϕ.func p.2}
 
/-- 族零距点对集 `ℛ_{∼}(ϕ | U) = {(x, y) ∈ U × U : ϕ(x) ∼_𝒢 ϕ(y)}`。 -/
def RelGaugeZero {X I : Type} {bot : X} (d : I → X → X → ENNReal)
    (ϕ : Operator X bot) (U : Set X) : Set (X × X) :=
  {p : X × X | p.1 ∈ U ∧ p.2 ∈ U ∧ GaugeZeroRelated d (ϕ.func p.1) (ϕ.func p.2)}
 
/-- `(x, y) ∈ ℛ_{∼}(ϕ | U) ↔ y ∈ Fib_{ϕ, I}(ϕ(x) | U)`（对 `x, y ∈ U`）。 -/
theorem mem_RelGaugeZero_iff_mem_CompFiber_univ {X I : Type} {bot : X}
    (d : I → X → X → ENNReal)
    (hsymm : ∀ i x y, d i x y = d i y x)
    (ϕ : Operator X bot) (U : Set X) {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    (x, y) ∈ RelGaugeZero d ϕ U ↔ y ∈ CompFiber d ϕ Set.univ (ϕ.func x) U := by
  simp only [RelGaugeZero, CompFiber, Set.mem_setOf_eq, hx, hy, true_and]
  constructor
  · intro hrel
    apply le_antisymm _ (zero_le _)
    apply iSup_le
    intro i
    rw [hsymm i.1 (ϕ.func y) (ϕ.func x)]
    exact le_of_eq (hrel i.1)
  · intro hsup i
    have hle : d i (ϕ.func y) (ϕ.func x) ≤ subfamily_pseudometric d Set.univ (ϕ.func y) (ϕ.func x) :=
      le_iSup (fun j : {j // j ∈ (Set.univ : Set I)} => d j.1 (ϕ.func y) (ϕ.func x)) ⟨i, trivial⟩
    rw [hsup] at hle
    rw [hsymm i (ϕ.func x) (ϕ.func y)]
    exact le_antisymm hle (zero_le _)
 
/-- 族零距关系限制到实际像集 `ϕ(U)` 上的 `Setoid`。 -/
def ImageGaugeSetoid {X I : Type} {bot : X} (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ : Operator X bot) (U : Set X) : Setoid ↥(operator_image ϕ U) where
  r a b := GaugeZeroRelated d a.1 b.1
  iseqv := by
    have heq := gauge_zero_related_equivalence d
      (fun i => (hd i).dist_self) (fun i => (hd i).symm) (fun i => (hd i).triangle)
    exact ⟨fun a => heq.refl a.1, fun hab => heq.symm hab, fun hab hbc => heq.trans hab hbc⟩
 
/-- 像集在族零距关系下的商集 `ϕ(U) / ∼_𝒢`。 -/
def ImageGaugeQuotient {X I : Type} {bot : X} (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ : Operator X bot) (U : Set X) : Type :=
  Quotient (ImageGaugeSetoid d hd ϕ U)
 
/-- 输入点 `x ∈ U` 在像商 `ϕ(U) / ∼_𝒢` 中对应的等价类 `[ϕ(x)]`。 -/
def imageQuotientClass {X I : Type} {bot : X} (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ : Operator X bot) (U : Set X) {x : X} (hx : x ∈ U) :
    ImageGaugeQuotient d hd ϕ U :=
  Quotient.mk (ImageGaugeSetoid d hd ϕ U) ⟨ϕ.func x, ⟨x, hx, rfl⟩⟩
 
/-- 规范族在指定子集 `S` 上分离。 -/
def IsSeparatingOn {X I : Type} (d : I → X → X → ENNReal) (S : Set X) : Prop :=
  ∀ y₁ ∈ S, ∀ y₂ ∈ S, GaugeZeroRelated d y₁ y₂ → y₁ = y₂
 
/-- 零测距纤维预序 `ϕ_A ⪰_{fiber, U} ϕ_B`：`ℛ_{∼}(ϕ_A | U) ⊆ ℛ_{∼}(ϕ_B | U)`。 -/
def FiberPreorder {X I : Type} {bot : X} (d : I → X → X → ENNReal)
    (U : Set X) (ϕA ϕB : Operator X bot) : Prop :=
  RelGaugeZero d ϕA U ⊆ RelGaugeZero d ϕB U
 
/-! ### CH03-D04: 点态零化半径 -/
 
/-- 有限正半径 `r ∈ (0, +∞)` 在基点 `y`、受限域 `U` 上满足零化球包含条件。 -/
def ValidNullRadius {X : Type} {bot : X} (ϕ : Operator X bot)
    (d_in d_out : X → X → ENNReal) (y : X) (U : Set X) (r : ENNReal) : Prop :=
  0 < r ∧ r < ⊤ ∧
    ball d_in y r ∩ U ⊆ {x ∈ U | d_out (ϕ.func x) (ϕ.func y) = 0}
 
/-- 点态零化内切半径 `r^N_{ϕ, d_in, d_out}(y | U)`。无合法有限正半径时按 `sSup ∅ = 0` 取 `0`。 -/
noncomputable def pointwiseNullRadius {X : Type} {bot : X} (ϕ : Operator X bot)
    (d_in d_out : X → X → ENNReal) (y : X) (U : Set X) : ENNReal :=
  sSup {r : ENNReal | ValidNullRadius ϕ d_in d_out y U r}
 
/-- 全域点态零化内切半径 `r^N_{ϕ, d_in, d_out}(y) := r^N_{ϕ, d_in, d_out}(y | dom(ϕ))`。 -/
noncomputable def pointwiseNullRadiusGlobal {X : Type} {bot : X} (ϕ : Operator X bot)
    (d_in d_out : X → X → ENNReal) (y : X) : ENNReal :=
  pointwiseNullRadius ϕ d_in d_out y (dom ϕ)
 
/-- 子族输出简写 `r^N_{ϕ, i, J}(y | U) := r^N_{ϕ, d_i, d_J}(y | U)`。 -/
noncomputable def pointwiseNullRadiusSubfamily {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (i : I) (J : Set I)
    (y : X) (U : Set X) : ENNReal :=
  pointwiseNullRadius ϕ (d i) (subfamily_pseudometric d J) y U
 
/-- 单分量通道简写 `r^N_{ϕ, i, j}(y | U) := r^N_{ϕ, d_i, d_j}(y | U)`。 -/
noncomputable def pointwiseNullRadiusComp {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (i j : I)
    (y : X) (U : Set X) : ENNReal :=
  pointwiseNullRadius ϕ (d i) (d j) y U
 
theorem pointwiseNullRadiusSubfamily_singleton {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (i j : I) (y : X) (U : Set X) :
    pointwiseNullRadiusSubfamily d ϕ i {j} y U = pointwiseNullRadiusComp d ϕ i j y U := by
  unfold pointwiseNullRadiusSubfamily pointwiseNullRadiusComp
  rw [subfamily_pseudometric_singleton]
 
theorem ValidNullRadius_subfamily_iff_fiber {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (i : I) (J : Set I)
    (y : X) (U : Set X) (r : ENNReal) :
    ValidNullRadius ϕ (d i) (subfamily_pseudometric d J) y U r ↔
      0 < r ∧ r < ⊤ ∧ ball (d i) y r ∩ U ⊆ CompFiber d ϕ J (ϕ.func y) U := Iff.rfl
 
theorem pointwiseNullRadius_eq_zero_of_no_valid {X : Type} {bot : X} (ϕ : Operator X bot)
    (d_in d_out : X → X → ENNReal) (y : X) (U : Set X)
    (hnone : ¬ ∃ r : ENNReal, ValidNullRadius ϕ d_in d_out y U r) :
    pointwiseNullRadius ϕ d_in d_out y U = 0 := by
  unfold pointwiseNullRadius
  have hemp : {r : ENNReal | ValidNullRadius ϕ d_in d_out y U r} = ∅ := by
    ext r
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    exact fun hr => hnone ⟨r, hr⟩
  rw [hemp, sSup_empty]
  rfl
 
/-! ### CH03-D05: 统一半径与零化矩阵 -/
 
/-- 基点集合 `A` 关于评估域 `U` 的统一零化半径 `\underline{r}^N_{ϕ, d_in, d_out}(A | U)`。 -/
noncomputable def uniformNullRadiusOn {X : Type} {bot : X} (ϕ : Operator X bot)
    (d_in d_out : X → X → ENNReal) (A U : Set X) : ENNReal :=
  ⨅ y ∈ A, pointwiseNullRadius ϕ d_in d_out y U
 
/-- 受限域统一零化半径 `\underline{r}^N_{ϕ, d_in, d_out}|_U := \underline{r}^N(U | U)`。 -/
noncomputable def uniformNullRadius {X : Type} {bot : X} (ϕ : Operator X bot)
    (d_in d_out : X → X → ENNReal) (U : Set X) : ENNReal :=
  uniformNullRadiusOn ϕ d_in d_out U U
 
/-- 全域统一零化半径 `\underline{r}^N_{ϕ, d_in, d_out} := \underline{r}^N|_{dom(ϕ)}`。 -/
noncomputable def uniformNullRadiusGlobal {X : Type} {bot : X} (ϕ : Operator X bot)
    (d_in d_out : X → X → ENNReal) : ENNReal :=
  uniformNullRadius ϕ d_in d_out (dom ϕ)
 
/-- 子族输出统一零化半径 `\underline{r}^N_{ϕ, i, J}(A | U)`。 -/
noncomputable def uniformNullRadiusSubfamilyOn {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (i : I) (J : Set I)
    (A U : Set X) : ENNReal :=
  uniformNullRadiusOn ϕ (d i) (subfamily_pseudometric d J) A U
 
/-- 子族输出受限统一零化半径 `\underline{r}^N_{ϕ, i, J}|_U`。 -/
noncomputable def uniformNullRadiusSubfamily {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (i : I) (J : Set I)
    (U : Set X) : ENNReal :=
  uniformNullRadius ϕ (d i) (subfamily_pseudometric d J) U
 
/-- 单分量通道受限统一零化半径 `\underline{r}^N_{ϕ, i, j}|_U`。 -/
noncomputable def uniformNullRadiusComp {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (i j : I)
    (U : Set X) : ENNReal :=
  uniformNullRadius ϕ (d i) (d j) U
 
/-- 受限零化矩阵 `[N(ϕ)|_U]_{j, i} := \underline{r}^N_{ϕ, i, j}|_U`（行指标为输出 `j`，列指标为输入 `i`）。 -/
noncomputable def nullMatrix {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (j i : I) : ENNReal :=
  uniformNullRadiusComp d ϕ i j U
 
/-- 全域零化矩阵 `N(ϕ) := N(ϕ)|_{dom(ϕ)}`。 -/
noncomputable def nullMatrixGlobal {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (j i : I) : ENNReal :=
  nullMatrix d ϕ (dom ϕ) j i
 
theorem uniformNullRadiusSubfamily_singleton {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (i j : I) (U : Set X) :
    uniformNullRadiusSubfamily d ϕ i {j} U = nullMatrix d ϕ U j i := by
  unfold uniformNullRadiusSubfamily nullMatrix uniformNullRadiusComp
  rw [subfamily_pseudometric_singleton]
 
/-! ### CH03-D06: 输入尺度与阈值分类 -/
 
/-- 输入尺度函数族单调性公理：对任意非空子集 `A₁ ⊆ A₂`，`σ_i(A₁) ≤ σ_i(A₂)`。 -/
def IsInputScaleFamily {X I : Type} (σ : I → Set X → ENNReal) : Prop :=
  ∀ i : I, ∀ ⦃A₁ A₂ : Set X⦄, A₁.Nonempty → A₂.Nonempty → A₁ ⊆ A₂ → σ i A₁ ≤ σ i A₂
 
/-- 集合关于伪度量 `d` 的直径 `diam_d(A) = sup_{x, y ∈ A} d(x, y)`。 -/
noncomputable def setDiam {X : Type} (d : X → X → ENNReal) (A : Set X) : ENNReal :=
  ⨆ x ∈ A, ⨆ y ∈ A, d x y
 
/-- 默认直径尺度函数族 `σ_i(A) = diam_{d_i}(A)`。 -/
noncomputable def diameterScaleFamily {X I : Type} (d : I → X → X → ENNReal) :
    I → Set X → ENNReal :=
  fun i A => setDiam (d i) A
 
theorem diameterScaleFamily_isInputScaleFamily {X I : Type}
    (d : I → X → X → ENNReal) :
    IsInputScaleFamily (diameterScaleFamily d) := by
  intro i A₁ A₂ _ _ hsub
  unfold diameterScaleFamily setDiam
  apply iSup₂_le
  intro x hx
  apply iSup₂_le
  intro y hy
  exact le_iSup₂_of_le x (hsub hx) (le_iSup₂_of_le y (hsub hy) le_rfl)
 
/-- 命题指示函数 `1_{P} ∈ {0, 1}`（以 `Fin 2` 表示 `{0, 1}`）。 -/
noncomputable def ind01 (P : Prop) : Fin 2 :=
  open scoped Classical in
  if P then 1 else 0
 
/-- 通道 `(i, j)` 在尺度函数族 `σ` 与有限正阈值 `(τσ, τN)` 下的阈值分类 `Type_{f, A}(i, j) ∈ {0, 1}²`。 -/
noncomputable def channelType {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (σ : I → Set X → ENNReal)
    (f : Operator X bot) (A : Set X) (τσ τN : ENNReal) (i j : I) : Fin 2 × Fin 2 :=
  (ind01 (σ i A < τσ), ind01 (τN ≤ uniformNullRadiusComp d f i j A))
 
/-! ### CH03-D07: 内部覆盖数、熵与全有界接口 -/
 
/-- 子族覆盖数 `𝒩_J(ε, U)`，直接复用第1章冻结覆盖数在子族复合伪度量 `d_J` 上的实例。 -/
noncomputable def subfamily_covering_number {X I : Type}
    (d : I → X → X → ENNReal) (J : Set I) (ε : ENNReal) (U : Set X) : ENNReal :=
  covering_number (subfamily_pseudometric d J) ε U
 
theorem subfamily_covering_number_singleton {X I : Type}
    (d : I → X → X → ENNReal) (i : I) (ε : ENNReal) (U : Set X) :
    subfamily_covering_number d ({i} : Set I) ε U = covering_number (d i) ε U := by
  unfold subfamily_covering_number
  rw [subfamily_pseudometric_singleton]
 
/-- 验证第1章冻结 `InternalEpsilonNet` 与正文开球并集表述 `S ⊆ U ∧ U ⊆ ⋃_{s ∈ S} B_d(s, ε)` 完全一致。 -/
theorem InternalEpsilonNet_iff_ball_cover {X : Type} (d : X → X → ENNReal)
    (ε : ENNReal) (U : Set X) (S : Finset X) :
    InternalEpsilonNet d ε U S ↔
      (↑S : Set X) ⊆ U ∧ U ⊆ ⋃ s ∈ S, ball d s ε := by
  unfold InternalEpsilonNet ball
  constructor
  · rintro ⟨hsub, hcov⟩
    refine ⟨hsub, fun x hx => ?_⟩
    rcases hcov x hx with ⟨s, hs, hdist⟩
    exact Set.mem_iUnion₂.mpr ⟨s, hs, hdist⟩
  · rintro ⟨hsub, hcov⟩
    refine ⟨hsub, fun x hx => ?_⟩
    rcases Set.mem_iUnion₂.mp (hcov hx) with ⟨s, hs, hdist⟩
    exact ⟨s, hs, hdist⟩
 
/-- `log2_ereal` 在 `ENNReal` 上单调不减。 -/
theorem log2_ereal_mono {x y : ENNReal} (hxy : x ≤ y) :
    log2_ereal x ≤ log2_ereal y := by
  unfold log2_ereal
  by_cases hx0 : x = 0
  · simp [hx0]
  · have hy0 : y ≠ 0 := ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.mpr hx0) hxy)
    by_cases hytop : y = ⊤
    · simp [hx0, hytop]
    · have hxtop : x ≠ ⊤ := ne_of_lt (lt_of_le_of_lt hxy (lt_top_iff_ne_top.mpr hytop))
      simp only [if_neg hx0, if_neg hy0, if_neg hxtop, if_neg hytop, EReal.coe_le_coe_iff]
      apply Real.logb_le_logb_of_le one_lt_two
      · exact ENNReal.toReal_pos hx0 hxtop
      · exact ENNReal.toReal_mono hytop hxy
 
/-- 集合 `U` 在伪度量 `d` 下全有界：对一切有限正精度 `r ∈ (0, +∞)`，`𝒩_d(r, U) < +∞`。 -/
def IsTotallyBounded {X : Type} (d : X → X → ENNReal) (U : Set X) : Prop :=
  ∀ r : ENNReal, 0 < r → r < ⊤ → covering_number d r U < ⊤
 
theorem metric_entropy_lt_top_iff {X : Type} (d : X → X → ENNReal)
    (ε : ENNReal) (U : Set X) :
    metric_entropy d ε U < ⊤ ↔ covering_number d ε U < ⊤ := by
  unfold metric_entropy log2_ereal
  by_cases h0 : covering_number d ε U = 0
  · simp [h0]
  · by_cases htop : covering_number d ε U = ⊤
    · simp [htop]
    · simp [h0, htop, lt_top_iff_ne_top]
 
theorem metric_entropy_finite_of_totallyBounded {X : Type} (d : X → X → ENNReal)
    (U : Set X) (hU : U.Nonempty) (htb : IsTotallyBounded d U)
    {ε : ENNReal} (hε0 : 0 < ε) (hεtop : ε < ⊤) :
    (0 : EReal) ≤ metric_entropy d ε U ∧ metric_entropy d ε U < ⊤ :=
  ⟨metric_entropy_nonneg d ε U hU, (metric_entropy_lt_top_iff d ε U).mpr (htb ε hε0 hεtop)⟩
 
/-! ### CH03-D08: 映射熵差 -/
 
/-- 映射熵差良定前提：`U` 非空、`U ⊆ dom(ϕ)`、`Jin, Jout` 非空、`ε ∈ (0, +∞)`，且输入/输出覆盖数至少一个有限（排除 `∞ - ∞`）。 -/
def MappingEntropyDiffWellDefined {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    (Jin Jout : Set I) (ε : ENNReal) : Prop :=
  U.Nonempty ∧ U ⊆ dom ϕ ∧ Jin.Nonempty ∧ Jout.Nonempty ∧
  0 < ε ∧ ε < ⊤ ∧
  (subfamily_covering_number d Jin ε U < ⊤ ∨
    subfamily_covering_number d Jout ε (operator_image ϕ U) < ⊤)
 
/-- 映射熵差 `ΔE_{ε, Jin, Jout}(ϕ | U)`：仅在 `MappingEntropyDiffWellDefined` 证明下有定义，不定义 `∞ - ∞`。 -/
noncomputable def mappingEntropyDiff {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    (Jin Jout : Set I) (ε : ENNReal)
    (hwf : MappingEntropyDiffWellDefined d ϕ U Jin Jout ε) : EReal :=
  open scoped Classical in
  let Nin := subfamily_covering_number d Jin ε U
  let Nout := subfamily_covering_number d Jout ε (operator_image ϕ U)
  if hin : Nin < ⊤ then
    if Nout < ⊤ then
      ((Real.logb 2 Nin.toReal - Real.logb 2 Nout.toReal : ℝ) : EReal)
    else
      ⊥
  else
    if hout : Nout < ⊤ then
      ⊤
    else
      False.elim (hwf.2.2.2.2.2.2.elim hin hout)
 
/-- 同子族简写 `ΔE_{ε, J}(ϕ | U)` 的良定条件。 -/
def MappingEntropyDiffSameWellDefined {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    (J : Set I) (ε : ENNReal) : Prop :=
  MappingEntropyDiffWellDefined d ϕ U J J ε
 
/-- 同子族映射熵差 `ΔE_{ε, J}(ϕ | U)`。 -/
noncomputable def mappingEntropyDiffSame {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    (J : Set I) (ε : ENNReal)
    (hwf : MappingEntropyDiffSameWellDefined d ϕ U J ε) : EReal :=
  mappingEntropyDiff d ϕ U J J ε hwf
 
/-- 单通道简写 `ΔE_{ε, i, j}(ϕ | U)` 的良定条件。 -/
def MappingEntropyDiffCompWellDefined {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    (i j : I) (ε : ENNReal) : Prop :=
  MappingEntropyDiffWellDefined d ϕ U {i} {j} ε
 
/-- 单通道映射熵差 `ΔE_{ε, i, j}(ϕ | U)`。 -/
noncomputable def mappingEntropyDiffComp {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    (i j : I) (ε : ENNReal)
    (hwf : MappingEntropyDiffCompWellDefined d ϕ U i j ε) : EReal :=
  mappingEntropyDiff d ϕ U {i} {j} ε hwf
 
/-- 单分量简写 `ΔE_{ε, j}(ϕ | U)` 的良定条件。 -/
def MappingEntropyDiffSingleWellDefined {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    (j : I) (ε : ENNReal) : Prop :=
  MappingEntropyDiffWellDefined d ϕ U {j} {j} ε
 
/-- 单分量映射熵差 `ΔE_{ε, j}(ϕ | U)`。 -/
noncomputable def mappingEntropyDiffSingle {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    (j : I) (ε : ENNReal)
    (hwf : MappingEntropyDiffSingleWellDefined d ϕ U j ε) : EReal :=
  mappingEntropyDiff d ϕ U {j} {j} ε hwf
 
/-- 在良定条件下，`mappingEntropyDiff` 与 `E_{ε, Jin}(U) - E_{ε, Jout}(ϕ(U))` 在有限、`+∞`、`-∞` 三种合法分支上严格一致。 -/
theorem mappingEntropyDiff_eq_sub {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    (Jin Jout : Set I) (ε : ENNReal)
    (hwf : MappingEntropyDiffWellDefined d ϕ U Jin Jout ε) :
    mappingEntropyDiff d ϕ U Jin Jout ε hwf =
      subfamily_metric_entropy d Jin ε U -
        subfamily_metric_entropy d Jout ε (operator_image ϕ U) := by
  have hU : U.Nonempty := hwf.1
  have hIm : (operator_image ϕ U).Nonempty := hU.image ϕ.func
  have hin0 : covering_number (subfamily_pseudometric d Jin) ε U ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one
      (one_le_covering_number_of_nonempty (subfamily_pseudometric d Jin) ε U hU))
  have hout0 : covering_number (subfamily_pseudometric d Jout) ε (operator_image ϕ U) ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one
      (one_le_covering_number_of_nonempty (subfamily_pseudometric d Jout) ε (operator_image ϕ U) hIm))
  unfold mappingEntropyDiff subfamily_metric_entropy subfamily_covering_number log2_ereal
  dsimp only
  by_cases hin : covering_number (subfamily_pseudometric d Jin) ε U < ⊤
  · have hintop : covering_number (subfamily_pseudometric d Jin) ε U ≠ ⊤ := lt_top_iff_ne_top.mp hin
    by_cases hout : covering_number (subfamily_pseudometric d Jout) ε (operator_image ϕ U) < ⊤
    · have houttop : covering_number (subfamily_pseudometric d Jout) ε (operator_image ϕ U) ≠ ⊤ :=
        lt_top_iff_ne_top.mp hout
      simp [hin, hout, hin0, hout0, hintop, houttop, EReal.coe_sub]
    · have houttop : covering_number (subfamily_pseudometric d Jout) ε (operator_image ϕ U) = ⊤ :=
        not_lt_top_iff.mp hout
      simp [hin, hin0, hintop, houttop]
  · have hintop : covering_number (subfamily_pseudometric d Jin) ε U = ⊤ := not_lt_top_iff.mp hin
    rcases hwf.2.2.2.2.2.2 with hin' | hout
    · exact False.elim (hin hin')
    · change covering_number (subfamily_pseudometric d Jout) ε (operator_image ϕ U) < ⊤ at hout
      have houttop : covering_number (subfamily_pseudometric d Jout) ε (operator_image ϕ U) ≠ ⊤ :=
        lt_top_iff_ne_top.mp hout
      simp [hout, hout0, hintop, houttop]
 
end Ch03
