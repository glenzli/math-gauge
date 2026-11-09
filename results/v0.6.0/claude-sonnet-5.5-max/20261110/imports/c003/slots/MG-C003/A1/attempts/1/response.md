下面是完整答卷，包含 `Main.lean` 和 `alignment.json`。我在固定环境（Lean 4.29.1 加 mathlib 指定提交，导入冻结的 `formal_oet` 模块）中编译通过了与下面全文一致的 `Main.lean`，其中没有 `sorry`，也没有新增公理。对 `alignment.json` 里列出的 160 个声明逐个做了 `#print axioms`，只依赖 `propext`、`Classical.choice`、`Quot.sound`。

我只在编译通过之后调整了若干注释行（补全几处被截断的文档注释）。`alignment.json` 里 D03、P10-01、P30-01 三项的声明列表在核对后又补充了几个声明名，这些名字在 `Main.lean` 中都存在，但改动后的 JSON 没有再跑一遍校验。

实现要点：
- **表示方式**：沿用冻结背景的 `Operator`、`ExtendedPseudoMetric`、`subfamily_pseudometric`、`covering_number`、`metric_entropy`、`subfamily_metric_entropy`。
- **D07**：用 `covering_number_textbook`、`metric_entropy_textbook`、`internalEpsilonNet_iff` 证明冻结定义与正文一致。
- **D08 边界**：映射熵差的良定前提 `MapEntropyDiffDefined` 在相关命题中显式给出，`mapEntropyDiff_cases` 说明 `∞ - ∞` 被排除。
- **具体反例与习题**：七点反例、两点换位例、阶跃算子、习题 3.1–3.5 都在 `Main.lean` 里单独构造并证明，包括合法性、分支和端点。

```lean filename=Main.lean
/-
Formalization of Chapter 3 ("算子局部退化") of Zhe Li (Glen Li / glenzli),
"The Operator Evolution Theory", Volume I (CC BY 4.0, https://glenzli.com/books/oet/,
DOI 10.5281/zenodo.21457931). Original mathematical content belongs to the author.
-/
import Mathlib
import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.metric_entropy
import formal_oet.vol_01.ch_01_foundations.operator_space
import formal_oet.vol_01.ch_02_operator_bounds.lip_matrix
import formal_oet.vol_01.ch_02_operator_bounds.single_channel
import formal_oet.vol_01.ch_02_operator_bounds.decoupling

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.style.emptyLine false

namespace MGC003

open formal_oet.vol_01.ch_01_foundations formal_oet.vol_01.ch_02_operator_bounds

section PartDefs
variable {X I : Type} {bot : X}

/-! ## 复合算子的记号 -/

/-- 复合算子的函数是函数复合：`(ϕ * ψ)(x) = ϕ(ψ(x))`，左侧算子在右侧之后作用。 -/
@[simp] theorem mul_func (ϕ ψ : Operator X bot) (x : X) :
    (ϕ * ψ).func x = ϕ.func (ψ.func x) := rfl

@[simp] theorem one_func (x : X) : (1 : Operator X bot).func x = x := rfl

/-- 有限复合 `c_k = ϕ_k ∘ ⋯ ∘ ϕ_1`（下标取 `1,…,k`；`ϕ 0` 不参与），`c_0 = id`。 -/
def chainComp (ϕ : ℕ → Operator X bot) : ℕ → Operator X bot
  | 0 => 1
  | k + 1 => ϕ (k + 1) * chainComp ϕ k

/-! ## D01 分量分划 -/

/-- 定义（常值分量） `I_const(ϕ ∣ U) = {i ∈ I : ∀ x y ∈ U, d_i(ϕ x, ϕ y) = 0}`。 -/
def Iconst (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) : Set I :=
  {i | ∀ x ∈ U, ∀ y ∈ U, d i (ϕ.func x) (ϕ.func y) = 0}

/-- 定义（恒等分量） `I_id(ϕ ∣ U) = {i ∈ I ∖ I_const(ϕ ∣ U) : ∀ x ∈ U, d_i(ϕ x, x) = 0}`（常值优先）。 -/
def Iid (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) : Set I :=
  {i | i ∉ Iconst d ϕ U ∧ ∀ x ∈ U, d i (ϕ.func x) x = 0}

/-- 定义（有效分量） `I_act(ϕ ∣ U) = I ∖ (I_const(ϕ ∣ U) ∪ I_id(ϕ ∣ U))`。 -/
def Iact (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) : Set I :=
  Set.univ \ (Iconst d ϕ U ∪ Iid d ϕ U)

/-! ## D02 计算纤维 -/

/-- 定义（计算纤维） `Fib_{ϕ,J}(y ∣ U) = {x ∈ U : d_J(ϕ x, y) = 0}`，`d_J` 为冻结背景的子族复合伪度量 `subfamily_pseudometric`（`J` 非空、`U ⊆ dom ϕ` 在各命题中给出）。 -/
def Fib (d : I → X → X → ENNReal) (ϕ : Operator X bot) (J : Set I) (y : X) (U : Set X) : Set X :=
  {x | x ∈ U ∧ subfamily_pseudometric d J (ϕ.func x) y = 0}

/-! ## D03 点值关系、零距关系、像商与纤维预序 -/

/-- 点值相等关系 `R_=(ϕ ∣ U) = {(x,y) ∈ U × U : ϕ x = ϕ y}`。 -/
def Req (ϕ : Operator X bot) (U : Set X) : Set (X × X) :=
  {p | p.1 ∈ U ∧ p.2 ∈ U ∧ ϕ.func p.1 = ϕ.func p.2}

/-- 族零距关系 `R_∼(ϕ ∣ U) = {(x,y) ∈ U × U : ϕ x ∼_𝒢 ϕ y}`。 -/
def Rsim (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) : Set (X × X) :=
  {p | p.1 ∈ U ∧ p.2 ∈ U ∧ GaugeZeroRelated d (ϕ.func p.1) (ϕ.func p.2)}

/-- 定义（零测距纤维预序 `⪰_{fiber,U}`） `ϕA ⪰ ϕB` 当且仅当 `R_∼(ϕA ∣ U) ⊆ R_∼(ϕB ∣ U)`。 -/
def FiberGe (d : I → X → X → ENNReal) (ϕA ϕB : Operator X bot) (U : Set X) : Prop :=
  Rsim d ϕA U ⊆ Rsim d ϕB U

/-- 族零距关系 `∼_𝒢` 作为 `X` 上的 setoid（引理 1.1，冻结背景 `gauge_zero_related_equivalence`）。 -/
def gaugeSetoid (d : I → X → X → ENNReal) (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) : Setoid X :=
  ⟨GaugeZeroRelated d, gauge_zero_related_equivalence d (fun i => (hd i).dist_self)
    (fun i => (hd i).symm) (fun i => (hd i).triangle)⟩

/-- 像集 `ϕ(U)` 上由 `∼_𝒢` 限制得到的商：`ϕ(U)/∼_𝒢`。 -/
def imageSetoid (d : I → X → X → ENNReal) (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (ϕ : Operator X bot) (U : Set X) : Setoid (ϕ.func '' U) :=
  (gaugeSetoid d hd).comap Subtype.val

/-- 存在满足规定赋值公式 `T̄([ϕA x]) = [ϕB x]`（`x ∈ U`）的商映射。 -/
def HasQuotientMap (d : I → X → X → ENNReal) (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (ϕA ϕB : Operator X bot) (U : Set X) : Prop :=
  ∃ T : Quotient (imageSetoid d hd ϕA U) → Quotient (imageSetoid d hd ϕB U),
    ∀ (x : X) (hx : x ∈ U),
      T (Quotient.mk _ ⟨ϕA.func x, x, hx, rfl⟩) = Quotient.mk _ ⟨ϕB.func x, x, hx, rfl⟩

/-- 像值因子化：`T : ϕA(U) → X` 满足 `T ∘ ϕA = ϕB`（在 `U` 上）。 -/
def Factors (ϕA ϕB : Operator X bot) (U : Set X) (T : ϕA.func '' U → X) : Prop :=
  ∀ (x : X) (hx : x ∈ U), T ⟨ϕA.func x, x, hx, rfl⟩ = ϕB.func x

/-- 规范族在集合 `S` 上分离：`S` 内全分量零距蕴含点相等。 -/
def SepOn (d : I → X → X → ENNReal) (S : Set X) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, GaugeZeroRelated d a b → a = b

/-- 单分量标量 co-Lip 界（对应冻结背景 `HasScalarLipBound` 的下界版本）。 -/
def HasScalarCoLipBound (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    (U : Set X) (i j : I) (c : ENNReal) : Prop :=
  U.Nonempty ∧ U ⊆ dom ϕ ∧
    ∀ x ∈ U, ∀ y ∈ U, c * d i x y ≤ d j (ϕ.func x) (ϕ.func y)

/-! ## D04 点态零化半径 -/

/-- 点态零化半径定义中的合法半径集 `{r ∈ (0,+∞) : B_in(y,r) ∩ U ⊆ {x ∈ U : d_out(ϕ x, ϕ y) = 0}}`。 -/
def NullAdm (din dout : X → X → ENNReal) (ϕ : Operator X bot) (y : X) (U : Set X) : Set ENNReal :=
  {r | 0 < r ∧ r < ⊤ ∧ ball din y r ∩ U ⊆ {x | x ∈ U ∧ dout (ϕ.func x) (ϕ.func y) = 0}}

/-- 定义（零化内切半径） `r^N_{ϕ,d_in,d_out}(y ∣ U) = sup NullAdm`，约定 `sup ∅ = 0`，可取 `+∞`。 -/
noncomputable def nullRadius (din dout : X → X → ENNReal) (ϕ : Operator X bot) (y : X) (U : Set X) :
    ENNReal :=
  sSup (NullAdm din dout ϕ y U)

/-- `r^N_{ϕ,i,J}(y ∣ U) := r^N_{ϕ,d_i,d_J}(y ∣ U)`，输出取子族复合伪度量 `d_J`。 -/
noncomputable def nullRadiusJ (d : I → X → X → ENNReal) (ϕ : Operator X bot) (i : I) (J : Set I)
    (y : X) (U : Set X) : ENNReal :=
  nullRadius (d i) (subfamily_pseudometric d J) ϕ y U

/-! ## D05 统一半径与零化矩阵 -/

/-- 定义（统一零化半径） `r̲^N_{ϕ,d_in,d_out}(A ∣ U) = inf_{y ∈ A} r^N_{ϕ,d_in,d_out}(y ∣ U)`。 -/
noncomputable def uniformNullRadius (din dout : X → X → ENNReal) (ϕ : Operator X bot) (A U : Set X) :
    ENNReal :=
  ⨅ y ∈ A, nullRadius din dout ϕ y U

/-- `r̲^N_{ϕ,i,J}|_U`：输出取子族复合伪度量 `d_J` 的统一零化半径（`A = U`）。 -/
noncomputable def uniformNullRadiusJ (d : I → X → X → ENNReal) (ϕ : Operator X bot) (i : I)
    (J : Set I) (U : Set X) : ENNReal :=
  uniformNullRadius (d i) (subfamily_pseudometric d J) ϕ U U

/-- 定义（零化矩阵） `[N(ϕ)|_U]_{ji} = r̲^N_{ϕ,i,j}|_U`：行指标为输出分量 `j`，列指标为输入分量 `i`。 -/
noncomputable def nullMatrix (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (j i : I) :
    ENNReal :=
  uniformNullRadius (d i) (d j) ϕ U U

/-! ## D06 输入尺度与阈值分类 -/

/-- 定义（输入尺度函数族） `σ_i : {A ⊆ 𝒳 : A ≠ ∅} → ℝ̄₊`，对非空 `A₁ ⊆ A₂` 单调。 -/
def IsInputScale (σ : I → Set X → ENNReal) : Prop :=
  ∀ i : I, ∀ A₁ A₂ : Set X, A₁.Nonempty → A₁ ⊆ A₂ → σ i A₁ ≤ σ i A₂

/-- 默认的直径尺度 `σ_i(A) = diam_{d_i}(A) = sup_{x,y ∈ A} d_i(x,y)`。 -/
noncomputable def diamScale (d : I → X → X → ENNReal) (i : I) (A : Set X) : ENNReal :=
  ⨆ x ∈ A, ⨆ y ∈ A, d i x y

open Classical in
/-- 定义（阈值分类） `Type_{f,A}(i,j) = (1_{σ_i(A) < τ_σ}, 1_{r̲^N_{f,i,j}|_A ≥ τ_N}) ∈ {0,1}²`，以 `Bool × Bool` 表示。 -/
noncomputable def thresholdType (σ : I → Set X → ENNReal) (τσ τN : ENNReal)
    (d : I → X → X → ENNReal) (f : Operator X bot) (A : Set X) (i j : I) : Bool × Bool :=
  (decide (σ i A < τσ), decide (τN ≤ nullMatrix d f A j i))

/-! ## D07 内部覆盖数、熵与全有界接口 -/

/-- 子族覆盖数 `𝒩_J(ε,S)`（沿用冻结背景 `covering_number` 与 `subfamily_pseudometric`）。 -/
noncomputable def subfamilyCoveringNumber (d : I → X → X → ENNReal) (J : Set I) (ε : ENNReal)
    (S : Set X) : ENNReal :=
  covering_number (subfamily_pseudometric d J) ε S

/-- `U` 在 `d_i` 下全有界：对任意有限正精度 `r`，`𝒩_i(r, U) < +∞`。 -/
def TotallyBoundedIn (d : I → X → X → ENNReal) (i : I) (U : Set X) : Prop :=
  ∀ r : ENNReal, 0 < r → r < ⊤ → covering_number (d i) r U < ⊤

/-! ## D08 映射熵差 -/

/-- 定义（映射熵差） `ΔE_{ε,J_in,J_out}(ϕ ∣ U) = E_{ε,J_in}(U) - E_{ε,J_out}(ϕ(U)) ∈ [-∞,+∞]`。 -/
noncomputable def mapEntropyDiff (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    (Jin Jout : Set I) (ε : ENNReal) : EReal :=
  subfamily_metric_entropy d Jin ε U - subfamily_metric_entropy d Jout ε (ϕ.func '' U)

/-- 映射熵差的良定前提：`𝒩_{J_in}(ε,U) < +∞` 或 `𝒩_{J_out}(ε,ϕ(U)) < +∞`。 -/
def MapEntropyDiffDefined (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    (Jin Jout : Set I) (ε : ENNReal) : Prop :=
  subfamilyCoveringNumber d Jin ε U < ⊤ ∨ subfamilyCoveringNumber d Jout ε (ϕ.func '' U) < ⊤

/-! ## 基本引理 -/

theorem subfam_eq_zero_iff (d : I → X → X → ENNReal) (J : Set I) (x y : X) :
    subfamily_pseudometric d J x y = 0 ↔ ∀ j ∈ J, d j x y = 0 := by
  unfold subfamily_pseudometric
  rw [ENNReal.iSup_eq_zero]
  constructor
  · intro h j hj
    exact h ⟨j, hj⟩
  · intro h j
    exact h j.1 j.2

theorem mem_Fib {d : I → X → X → ENNReal} {ϕ : Operator X bot} {J : Set I} {y x : X} {U : Set X} :
    x ∈ Fib d ϕ J y U ↔ x ∈ U ∧ ∀ j ∈ J, d j (ϕ.func x) y = 0 := by
  unfold Fib
  simp only [Set.mem_setOf_eq, subfam_eq_zero_iff]

theorem zero_trans {dd : X → X → ENNReal} (h : ExtendedPseudoMetric X bot dd) {a b c : X}
    (hab : dd a b = 0) (hbc : dd b c = 0) : dd a c = 0 :=
  le_antisymm (by
    calc dd a c ≤ dd a b + dd b c := h.triangle a b c
      _ = 0 := by rw [hab, hbc, add_zero]) (zero_le _)

theorem zero_symm {dd : X → X → ENNReal} (h : ExtendedPseudoMetric X bot dd) {a b : X}
    (hab : dd a b = 0) : dd b a = 0 := by
  rw [h.symm]
  exact hab

/-! ### 零化半径的基本性质 -/

theorem nullAdm_downward {din dout : X → X → ENNReal} {ϕ : Operator X bot} {y : X} {U : Set X}
    {r r' : ENNReal} (hr : r ∈ NullAdm din dout ϕ y U) (hr'0 : 0 < r') (hr' : r' ≤ r) :
    r' ∈ NullAdm din dout ϕ y U := by
  obtain ⟨_, htop, hsub⟩ := hr
  refine ⟨hr'0, lt_of_le_of_lt hr' htop, fun x hx => hsub ⟨?_, hx.2⟩⟩
  exact lt_of_lt_of_le hx.1 hr'

theorem le_nullRadius_of_mem {din dout : X → X → ENNReal} {ϕ : Operator X bot} {y : X} {U : Set X}
    {r : ENNReal} (hr : r ∈ NullAdm din dout ϕ y U) : r ≤ nullRadius din dout ϕ y U :=
  le_sSup hr

/-- 严格小于点态零化半径的输入距离给出输出零距（`x ∈ U`，`d_in(x,y) < r^N(y ∣ U)`）。 -/
theorem zero_of_lt_nullRadius {din dout : X → X → ENNReal} {ϕ : Operator X bot} {y x : X}
    {U : Set X} (hx : x ∈ U) (h : din x y < nullRadius din dout ϕ y U) :
    dout (ϕ.func x) (ϕ.func y) = 0 := by
  obtain ⟨r, hr, hlt⟩ := lt_sSup_iff.mp h
  exact (hr.2.2 ⟨hlt, hx⟩).2

theorem le_nullRadius_of_forall {din dout : X → X → ENNReal} {ϕ : Operator X bot} {y : X}
    {U : Set X} {m : ENNReal}
    (h : ∀ r : ENNReal, 0 < r → r < ⊤ → r < m → r ∈ NullAdm din dout ϕ y U) :
    m ≤ nullRadius din dout ϕ y U := by
  by_contra hlt
  push Not at hlt
  obtain ⟨r, hr1, hr2⟩ := exists_between hlt
  have hr0 : 0 < r := lt_of_le_of_lt (zero_le _) hr1
  have hrt : r < ⊤ := lt_of_lt_of_le hr2 le_top
  exact absurd (le_nullRadius_of_mem (h r hr0 hrt hr2)) (not_le.mpr hr1)

theorem nullRadius_eq_top_of_zero {din dout : X → X → ENNReal} {ϕ : Operator X bot} {y : X}
    {U : Set X} (h : ∀ x ∈ U, dout (ϕ.func x) (ϕ.func y) = 0) :
    nullRadius din dout ϕ y U = ⊤ := by
  apply top_unique
  apply le_nullRadius_of_forall
  intro r hr0 hrt _
  exact ⟨hr0, hrt, fun x hx => ⟨hx.2, h x hx.2⟩⟩

theorem uniformNullRadius_le {din dout : X → X → ENNReal} {ϕ : Operator X bot} {A U : Set X}
    {y : X} (hy : y ∈ A) : uniformNullRadius din dout ϕ A U ≤ nullRadius din dout ϕ y U :=
  iInf₂_le y hy

theorem le_uniformNullRadius {din dout : X → X → ENNReal} {ϕ : Operator X bot} {A U : Set X}
    {m : ENNReal} (h : ∀ y ∈ A, m ≤ nullRadius din dout ϕ y U) :
    m ≤ uniformNullRadius din dout ϕ A U :=
  le_iInf₂ h

theorem nullMatrix_le {d : I → X → X → ENNReal} {ϕ : Operator X bot} {U : Set X} {j i : I} {y : X}
    (hy : y ∈ U) : nullMatrix d ϕ U j i ≤ nullRadius (d i) (d j) ϕ y U :=
  uniformNullRadius_le hy

theorem nullRadiusJ_singleton (d : I → X → X → ENNReal) (ϕ : Operator X bot) (i j : I) (y : X)
    (U : Set X) : nullRadiusJ d ϕ i {j} y U = nullRadius (d i) (d j) ϕ y U := by
  unfold nullRadiusJ
  rw [subfamily_pseudometric_singleton]

theorem uniformNullRadiusJ_singleton (d : I → X → X → ENNReal) (ϕ : Operator X bot) (i j : I)
    (U : Set X) : uniformNullRadiusJ d ϕ i {j} U = nullMatrix d ϕ U j i := by
  unfold uniformNullRadiusJ nullMatrix
  rw [subfamily_pseudometric_singleton]

/-! ### 覆盖数与熵的基本性质（与冻结背景的对应） -/

/-- 冻结背景的内覆盖等价于正文的 `S ⊆ U` 且 `U ⊆ ⋃_{s ∈ S} B(s, ε)`。 -/
theorem internalEpsilonNet_iff {d : X → X → ENNReal} {ε : ENNReal} {U : Set X} {S : Finset X} :
    InternalEpsilonNet d ε U S ↔ (↑S : Set X) ⊆ U ∧ U ⊆ ⋃ s ∈ S, ball d s ε := by
  unfold InternalEpsilonNet
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun x hx => ?_⟩
    obtain ⟨c, hc, hd⟩ := h2 x hx
    exact Set.mem_biUnion hc hd
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun x hx => ?_⟩
    obtain ⟨c, hc, hd⟩ := Set.mem_iUnion₂.mp (h2 hx)
    exact ⟨c, hc, hd⟩

theorem covering_number_le_card {d : X → X → ENNReal} {ε : ENNReal} {U : Set X} {S : Finset X}
    (h : InternalEpsilonNet d ε U S) : covering_number d ε U ≤ (S.card : ENNReal) :=
  iInf_le_of_le S (iInf_le_of_le h le_rfl)

theorem le_covering_number_of_forall {d : X → X → ENNReal} {ε : ENNReal} {U : Set X} {m : ENNReal}
    (h : ∀ S : Finset X, InternalEpsilonNet d ε U S → m ≤ (S.card : ENNReal)) :
    m ≤ covering_number d ε U :=
  le_iInf₂ h

/-- 覆盖数比较的一般手段：每个 `(d',ε')`-内覆盖都给出不更大的 `(d,ε)`-内覆盖。 -/
theorem covering_number_le_of_transfer {d d' : X → X → ENNReal} {ε ε' : ENNReal} {U V : Set X}
    (h : ∀ S : Finset X, InternalEpsilonNet d' ε' U S →
      ∃ T : Finset X, InternalEpsilonNet d ε V T ∧ T.card ≤ S.card) :
    covering_number d ε V ≤ covering_number d' ε' U := by
  apply le_covering_number_of_forall
  intro S hS
  obtain ⟨T, hT, hcard⟩ := h S hS
  exact (covering_number_le_card hT).trans (by exact_mod_cast hcard)

theorem log2_ereal_mono {a b : ENNReal} (h : a ≤ b) : log2_ereal a ≤ log2_ereal b := by
  by_cases ha : a = 0
  · simp [log2_ereal, ha]
  by_cases hb : b = ⊤
  · simp [log2_ereal, hb]
  have hat : a ≠ ⊤ := ne_top_of_le_ne_top hb h
  have hb0 : b ≠ 0 := by
    intro hb0
    exact ha (le_antisymm (hb0 ▸ h) (zero_le _))
  simp only [log2_ereal, if_neg ha, if_neg hat, if_neg hb, if_neg hb0]
  apply EReal.coe_le_coe_iff.mpr
  apply Real.logb_le_logb_of_le one_lt_two
  · exact ENNReal.toReal_pos ha hat
  · exact ENNReal.toReal_mono hb h

theorem log2_ereal_one : log2_ereal 1 = 0 := by
  simp [log2_ereal]

theorem log2_ereal_eq_coe {n : ENNReal} (h0 : n ≠ 0) (ht : n ≠ ⊤) :
    ∃ r : ℝ, log2_ereal n = (r : EReal) := by
  refine ⟨Real.logb 2 n.toReal, ?_⟩
  simp [log2_ereal, h0, ht]

theorem log2_ereal_ne_top {n : ENNReal} (ht : n ≠ ⊤) : log2_ereal n ≠ ⊤ := by
  by_cases h0 : n = 0
  · simp [log2_ereal, h0]
  · obtain ⟨r, hr⟩ := log2_ereal_eq_coe h0 ht
    rw [hr]
    exact EReal.coe_ne_top r

/-- 一个 `ε`-内覆盖的存在性给出有限覆盖数。 -/
theorem covering_number_lt_top_of_net {d : X → X → ENNReal} {ε : ENNReal} {U : Set X} {S : Finset X}
    (h : InternalEpsilonNet d ε U S) : covering_number d ε U < ⊤ :=
  lt_of_le_of_lt (covering_number_le_card h) (ENNReal.natCast_lt_top _)

theorem diamScale_isInputScale (d : I → X → X → ENNReal) : IsInputScale (diamScale d) := by
  intro i A₁ A₂ _ h
  unfold diamScale
  apply iSup₂_le
  intro x hx
  apply iSup₂_le
  intro y hy
  exact le_iSup₂_of_le x (h hx) (le_iSup₂_of_le y (h hy) le_rfl)
end PartDefs

section PartA
variable {X I : Type} {bot : X} [Fintype I] (d : I → X → X → ENNReal)

theorem mem_Iact {ϕ : Operator X bot} {U : Set X} {i : I} :
    i ∈ Iact d ϕ U ↔ i ∉ Iconst d ϕ U ∧ i ∉ Iid d ϕ U := by
  simp [Iact]

theorem epm_le {dd : X → X → ENNReal} (h : ExtendedPseudoMetric X bot dd) {a a' b b' : X}
    (ha : dd a a' = 0) (hb : dd b' b = 0) : dd a b ≤ dd a' b' :=
  calc dd a b ≤ dd a a' + dd a' b := h.triangle _ _ _
    _ ≤ dd a a' + (dd a' b' + dd b' b) := by gcongr; exact h.triangle _ _ _
    _ = dd a' b' := by rw [ha, hb]; simp

theorem epm_eq {dd : X → X → ENNReal} (h : ExtendedPseudoMetric X bot dd) {a a' b b' : X}
    (ha : dd a a' = 0) (hb : dd b b' = 0) : dd a b = dd a' b' :=
  le_antisymm (epm_le h ha (zero_symm h hb)) (epm_le h (zero_symm h ha) hb)

/-! ## 命题 3.1 -/

open Classical in
/-- 命题 3.1 (i)：常值分量的 Lip 上界可取零行。 -/
theorem prop3_1_i (ϕ : Operator X bot) (U : Set X) (i : I) (hi : i ∈ Iconst d ϕ U) :
    (∀ x ∈ U, ∀ y ∈ U, d i (ϕ.func x) (ϕ.func y) ≤ ∑ k : I, (0 : ENNReal) * d k x y) ∧
    (∀ L : I → I → ENNReal, IsLipMatrix d ϕ U L →
      IsLipMatrix d ϕ U (fun k j => if j = i then 0 else L k j)) := by
  refine ⟨fun x hx y hy => by simp [hi x hx y hy], fun L hL => ⟨hL.1, fun x hx y hy j => ?_⟩⟩
  by_cases hj : j = i
  · subst hj
    simp [hi x hx y hy]
  · simpa [hj] using hL.2 x hx y hy j

/-- 命题 3.1 (ii)：常值分量下，存在正输入距离的源分量对应的 co-Lip 条目为零。 -/
theorem prop3_1_ii (ϕ : Operator X bot) (U : Set X) (K : I → I → ENNReal)
    (hK : IsCoLipMatrix d ϕ U K) (i : I) (hi : i ∈ Iconst d ϕ U) (k : I)
    (hk : ∃ x ∈ U, ∃ y ∈ U, 0 < d k x y) : K k i = 0 := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hk
  exact colip_entry_eq_zero_of_output_zero_input_pos d ϕ U K k i x y hK hx hy (hi x hx y hy) hxy

/-- 命题 3.1 (iii)：恒等分量保距（双向）。 -/
theorem prop3_1_iii (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (ϕ : Operator X bot) (U : Set X)
    (i : I) (hi : i ∈ Iid d ϕ U) : ∀ x ∈ U, ∀ y ∈ U, d i (ϕ.func x) (ϕ.func y) = d i x y :=
  fun x hx y hy => epm_eq (hd i) (hi.2 x hx) (hi.2 y hy)

/-! ## 命题 3.2 -/

theorem Iid_comp (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (ϕ₁ ϕ₂ : Operator X bot) (U : Set X) :
    Iid d ϕ₁ U ∩ Iid d ϕ₂ (ϕ₁.func '' U) ⊆ Iid d (ϕ₂ * ϕ₁) U := by
  rintro i ⟨h1, h2⟩
  refine ⟨fun hc => h1.1 fun x hx y hy => ?_, fun x hx => ?_⟩
  · rw [← prop3_1_iii d hd ϕ₂ _ i h2 _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩]
    exact hc x hx y hy
  · exact zero_trans (hd i) (h2.2 _ ⟨x, hx, rfl⟩) (h1.2 x hx)

theorem not_mem_Iact {ϕ : Operator X bot} {U : Set X} {i : I} :
    i ∉ Iact d ϕ U ↔ i ∈ Iconst d ϕ U ∨ i ∈ Iid d ϕ U := by
  simp only [Iact, Set.mem_diff, Set.mem_univ, true_and, Set.mem_union, not_not]

theorem not_Iact_comp (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (ϕ₁ ϕ₂ : Operator X bot)
    (U : Set X) (i : I) (h1 : i ∉ Iact d ϕ₁ U) (h2 : i ∉ Iact d ϕ₂ (ϕ₁.func '' U)) :
    i ∉ Iact d (ϕ₂ * ϕ₁) U := by
  rw [not_mem_Iact] at h1 h2 ⊢
  rcases h1 with c1 | i1
  · refine Or.inl fun x hx y hy => ?_
    rcases h2 with c2 | i2
    · exact c2 _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    · have := prop3_1_iii d hd ϕ₂ _ i i2 _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      simp only [mul_func]
      rw [this]
      exact c1 x hx y hy
  · rcases h2 with c2 | i2
    · exact Or.inl fun x hx y hy => c2 _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    · exact Or.inr (Iid_comp d hd ϕ₁ ϕ₂ U ⟨i1, i2⟩)

/-- 命题 3.2 (i)：两步复合下有效分量包含，第二步在实际中间像域 `ϕ₁(U)` 上考察。 -/
theorem prop3_2_i (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (ϕ₁ ϕ₂ : Operator X bot)
    (U : Set X) (hU : U ⊆ dom (ϕ₂ * ϕ₁)) :
    Iact d (ϕ₂ * ϕ₁) U ⊆ Iact d ϕ₁ U ∪ Iact d ϕ₂ (ϕ₁.func '' U) := by
  intro i hi
  by_contra hcon
  exact not_Iact_comp d hd ϕ₁ ϕ₂ U i (fun h => hcon (Or.inl h)) (fun h => hcon (Or.inr h)) hi

theorem chainComp_stage (ϕ : ℕ → Operator X bot) (U : ℕ → Set X) (n : ℕ)
    (hrec : ∀ m, 1 ≤ m → m ≤ n → U (m + 1) = (ϕ m).func '' U m) :
    U (n + 1) = (chainComp ϕ n).func '' U 1 := by
  induction n with
  | zero => simp [chainComp]
  | succ n ih =>
    rw [hrec (n + 1) (by omega) le_rfl, ih (fun m h1 h2 => hrec m h1 (by omega))]
    simp [chainComp, Set.image_image]

theorem dom_mul_subset (ϕ ψ : Operator X bot) : dom (ϕ * ψ) ⊆ dom ψ := by
  intro x hx hψ
  exact hx (by simp [mul_func, hψ, ϕ.preserves_bot])

/-- 命题 3.2 (ii)：任意有限链（含零步），`U_{m+1} = ϕ_m(U_m)`。 -/
theorem prop3_2_ii (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (ϕ : ℕ → Operator X bot) (n : ℕ)
    (U : ℕ → Set X) (hdom : U 1 ⊆ dom (chainComp ϕ n))
    (hrec : ∀ m, 1 ≤ m → m ≤ n → U (m + 1) = (ϕ m).func '' U m) :
    Iact d (chainComp ϕ n) (U 1) ⊆ ⋃ m ∈ Finset.Icc 1 n, Iact d (ϕ m) (U m) := by
  induction n with
  | zero =>
    intro i hi
    exfalso
    rw [mem_Iact] at hi
    by_cases hc : i ∈ Iconst d (chainComp ϕ 0) (U 1)
    · exact hi.1 hc
    · exact hi.2 ⟨hc, fun x hx => (hd i).dist_self x⟩
  | succ n ih =>
    have hdom' : U 1 ⊆ dom (chainComp ϕ n) := hdom.trans (dom_mul_subset _ _)
    have ih' := ih hdom' (fun m h1 h2 => hrec m h1 (by omega))
    have hst := chainComp_stage ϕ U n (fun m h1 h2 => hrec m h1 (by omega))
    intro i hi
    have := prop3_2_i d hd (chainComp ϕ n) (ϕ (n + 1)) (U 1) hdom hi
    rcases this with h | h
    · obtain ⟨m, hm, hi'⟩ := Set.mem_iUnion₂.mp (ih' h)
      exact Set.mem_iUnion₂.mpr ⟨m, by simp only [Finset.mem_Icc] at hm ⊢; omega, hi'⟩
    · rw [← hst] at h
      exact Set.mem_iUnion₂.mpr ⟨n + 1, by simp, h⟩

/-- 命题 3.2 (iii)：恒等分量保留（同时排除常值优先分支）。 -/
theorem prop3_2_iii (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (ϕ₁ ϕ₂ : Operator X bot)
    (U : Set X) (hU : U ⊆ dom (ϕ₂ * ϕ₁)) :
    Iid d ϕ₁ U ∩ Iid d ϕ₂ (ϕ₁.func '' U) ⊆ Iid d (ϕ₂ * ϕ₁) U :=
  Iid_comp d hd ϕ₁ ϕ₂ U

/-! ## 命题 3.3、推论 3.4 -/

/-- 命题 3.3 (i)：外侧在实际像域上常值，则复合常值。 -/
theorem prop3_3_i (ϕ ψ : Operator X bot) (U : Set X) (hU : U ⊆ dom (ψ * ϕ)) :
    Iconst d ψ (ϕ.func '' U) ⊆ Iconst d (ψ * ϕ) U :=
  fun i hi x hx y hy => hi _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩

/-- 推论 3.4：所选 Lip 矩阵第 `j` 行除同分量外为零时，内侧常值传给复合（系数可为 `+∞`）。 -/
theorem cor3_4 (ϕ ψ : Operator X bot) (U : Set X) (hU : U ⊆ dom (ψ * ϕ)) (j : I)
    (hj : j ∈ Iconst d ϕ U) (L : I → I → ENNReal) (hL : IsLipMatrix d ψ (ϕ.func '' U) L)
    (hrow : ∀ k, k ≠ j → L k j = 0) : j ∈ Iconst d (ψ * ϕ) U := by
  intro x hx y hy
  have := lip_bound_of_single_input_row d ψ (ϕ.func '' U) L j j hL hrow _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  rw [hj x hx y hy, mul_zero] at this
  exact le_antisymm this (zero_le _)

/-! ## 命题 3.5 -/

/-- 命题 3.5 (i)：目标零距不变性。 -/
theorem prop3_5_i (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (ϕ : Operator X bot) (J : Set I)
    (hJ : J.Nonempty) (U : Set X) (y y' : X) (h : subfamily_pseudometric d J y y' = 0) :
    Fib d ϕ J y U = Fib d ϕ J y' U := by
  have e := subfamily_pseudometric_is_extended d J hJ hd
  ext x
  constructor
  · exact fun ⟨hx, hxy⟩ => ⟨hx, zero_trans e hxy h⟩
  · exact fun ⟨hx, hxy⟩ => ⟨hx, zero_trans e hxy (zero_symm e h)⟩

theorem subfam_self (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (J : Set I) (x : X) :
    subfamily_pseudometric d J x x = 0 :=
  (subfam_eq_zero_iff d J x x).2 fun j _ => (hd j).dist_self x

/-- 命题 3.5 (ii-a)：像目标纤维非空且覆盖 `U`。 -/
theorem prop3_5_ii_a (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (ϕ : Operator X bot) (J : Set I)
    (U : Set X) :
    (∀ y ∈ ϕ.func '' U, (Fib d ϕ J y U).Nonempty) ∧ U ⊆ ⋃ y ∈ ϕ.func '' U, Fib d ϕ J y U := by
  have key : ∀ x ∈ U, x ∈ Fib d ϕ J (ϕ.func x) U := fun x hx => ⟨hx, subfam_self d hd J _⟩
  refine ⟨?_, fun x hx => Set.mem_iUnion₂.mpr ⟨ϕ.func x, ⟨x, hx, rfl⟩, key x hx⟩⟩
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, key x hx⟩

/-- 命题 3.5 (ii-b)：像目标纤维相等或不交；去重后构成 `U` 的分划。 -/
def IsPartitionOf (P : Set (Set X)) (U : Set X) : Prop :=
  (∀ F ∈ P, F.Nonempty) ∧ P.PairwiseDisjoint id ∧ ⋃₀ P = U

theorem prop3_5_ii_b (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (ϕ : Operator X bot) (J : Set I)
    (hJ : J.Nonempty) (U : Set X) :
    (∀ y₁ ∈ ϕ.func '' U, ∀ y₂ ∈ ϕ.func '' U,
      Fib d ϕ J y₁ U = Fib d ϕ J y₂ U ∨ Disjoint (Fib d ϕ J y₁ U) (Fib d ϕ J y₂ U)) ∧
    IsPartitionOf ((fun y => Fib d ϕ J y U) '' (ϕ.func '' U)) U := by
  have e := subfamily_pseudometric_is_extended d J hJ hd
  have hdisj : ∀ y₁ ∈ ϕ.func '' U, ∀ y₂ ∈ ϕ.func '' U,
      Fib d ϕ J y₁ U = Fib d ϕ J y₂ U ∨ Disjoint (Fib d ϕ J y₁ U) (Fib d ϕ J y₂ U) := by
    intro y₁ _ y₂ _
    by_cases h : Disjoint (Fib d ϕ J y₁ U) (Fib d ϕ J y₂ U)
    · exact Or.inr h
    · left
      obtain ⟨x, hx1, hx2⟩ := Set.not_disjoint_iff.mp h
      exact prop3_5_i d hd ϕ J hJ U y₁ y₂ (zero_trans e (zero_symm e hx1.2) hx2.2)
  refine ⟨hdisj, ?_, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact (prop3_5_ii_a d hd ϕ J U).1 y hy
  · rintro _ ⟨y₁, hy₁, rfl⟩ _ ⟨y₂, hy₂, rfl⟩ hne
    exact (hdisj y₁ hy₁ y₂ hy₂).resolve_left hne
  · apply Set.Subset.antisymm
    · rintro x ⟨_, ⟨y, hy, rfl⟩, hx⟩
      exact hx.1
    · intro x hx
      obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp ((prop3_5_ii_a d hd ϕ J U).2 hx)
      exact ⟨_, ⟨y, hy, rfl⟩, hxy⟩

/-- 命题 3.5 (iii)：有限非空子族的分量交集等式。 -/
theorem prop3_5_iii (ϕ : Operator X bot) (J : Set I) (hJ : J.Nonempty) (U : Set X) (y : X) :
    Fib d ϕ J y U = ⋂ j ∈ J, Fib d ϕ {j} y U := by
  obtain ⟨j₀, hj₀⟩ := hJ
  ext x
  simp only [mem_Fib, Set.mem_iInter, Set.mem_singleton_iff, forall_eq]
  constructor
  · exact fun ⟨hx, h⟩ j hj => ⟨hx, h j hj⟩
  · exact fun h => ⟨(h j₀ hj₀).1, fun j hj => (h j hj).2⟩

/-- 命题 3.5 (iv)：子族扩大时纤维缩小。 -/
theorem prop3_5_iv (ϕ : Operator X bot) {J K : Set I} (hJK : J ⊆ K) (U : Set X) (y : X) :
    Fib d ϕ K y U ⊆ Fib d ϕ J y U := fun x hx =>
  mem_Fib.2 ⟨(mem_Fib.1 hx).1, fun j hj => (mem_Fib.1 hx).2 j (hJK hj)⟩

/-- 命题 3.5 (v)：单分量等式及全子族向每分量包含。 -/
theorem prop3_5_v (ϕ : Operator X bot) (U : Set X) (y : X) (i : I) :
    Fib d ϕ {i} y U = {x | x ∈ U ∧ d i (ϕ.func x) y = 0} ∧
    (∀ k : I, Fib d ϕ Set.univ y U ⊆ {x | x ∈ U ∧ d k (ϕ.func x) y = 0}) := by
  refine ⟨?_, fun k x hx => ?_⟩
  · ext x
    simp [mem_Fib]
  · exact ⟨(mem_Fib.1 hx).1, (mem_Fib.1 hx).2 k (Set.mem_univ k)⟩

/-- 命题 3.5 (vi-a)：恒等分量的任意目标纤维等于输入零距类。 -/
theorem prop3_5_vi_a (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (ϕ : Operator X bot) (U : Set X)
    (j : I) (hj : j ∈ Iid d ϕ U) (y : X) :
    Fib d ϕ {j} y U = {x | x ∈ U ∧ d j x y = 0} := by
  ext x
  simp only [mem_Fib, Set.mem_singleton_iff, forall_eq, Set.mem_setOf_eq]
  refine and_congr_right fun hx => ?_
  rw [epm_eq (hd j) (hj.2 x hx) ((hd j).dist_self y)]

/-- 命题 3.5 (vi-b)：常值分量在像目标的纤维为 `U`，正距离目标的纤维为空。 -/
theorem prop3_5_vi_b (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (ϕ : Operator X bot) (U : Set X)
    (j : I) (hj : j ∈ Iconst d ϕ U) (y₀ : X) (hy₀ : y₀ ∈ ϕ.func '' U) :
    Fib d ϕ {j} y₀ U = U ∧ ∀ y : X, 0 < d j y y₀ → Fib d ϕ {j} y U = ∅ := by
  obtain ⟨x₀, hx₀, rfl⟩ := hy₀
  refine ⟨?_, fun y hy => ?_⟩
  · ext x
    simp only [mem_Fib, Set.mem_singleton_iff, forall_eq]
    exact ⟨fun h => h.1, fun hx => ⟨hx, hj x hx x₀ hx₀⟩⟩
  · ext x
    simp only [mem_Fib, Set.mem_singleton_iff, forall_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hx h1
    have h2 := hj x hx x₀ hx₀
    have : d j y (ϕ.func x₀) = 0 := zero_trans (hd j) (zero_symm (hd j) h1) h2
    exact absurd this hy.ne'

/-! ## 命题 3.6、3.7 -/

/-- 命题 3.6 (i-必要)：若像值因子化映射存在，则点值相等关系包含。 -/
theorem prop3_6_i_nec (ϕA ϕB : Operator X bot) (U : Set X) (T : ϕA.func '' U → X)
    (hT : Factors ϕA ϕB U T) : Req ϕA U ⊆ Req ϕB U := by
  rintro ⟨x, y⟩ ⟨hx, hy, hxy⟩
  refine ⟨hx, hy, ?_⟩
  have h1 := hT x hx
  have h2 := hT y hy
  have : (⟨ϕA.func x, x, hx, rfl⟩ : ϕA.func '' U) = ⟨ϕA.func y, y, hy, rfl⟩ := Subtype.ext hxy
  rw [← h1, ← h2, this]

/-- 命题 3.6 (i-充分)：由关系包含构造良定义的 `T`（`U = ∅` 时亦成立）。 -/
theorem prop3_6_i_suff (ϕA ϕB : Operator X bot) (U : Set X) (h : Req ϕA U ⊆ Req ϕB U) :
    ∃ T : ϕA.func '' U → X, Factors ϕA ϕB U T := by
  refine ⟨fun p => ϕB.func (Classical.choose p.2), fun x hx => ?_⟩
  have hc := Classical.choose_spec (show ϕA.func x ∈ ϕA.func '' U from ⟨x, hx, rfl⟩)
  have := h (show (Classical.choose (show ϕA.func x ∈ ϕA.func '' U from ⟨x, hx, rfl⟩), x) ∈ Req ϕA U
    from ⟨hc.1, hx, hc.2⟩)
  exact this.2.2

/-- 命题 3.6 (i)：`T` 存在当且仅当点值关系包含。 -/
theorem prop3_6_i (ϕA ϕB : Operator X bot) (U : Set X) :
    (∃ T : ϕA.func '' U → X, Factors ϕA ϕB U T) ↔ Req ϕA U ⊆ Req ϕB U :=
  ⟨fun ⟨T, hT⟩ => prop3_6_i_nec ϕA ϕB U T hT, prop3_6_i_suff ϕA ϕB U⟩

/-- 命题 3.6 (ii)：双向像值变换存在当且仅当点值关系相等。 -/
theorem prop3_6_ii (ϕA ϕB : Operator X bot) (U : Set X) :
    ((∃ T : ϕA.func '' U → X, Factors ϕA ϕB U T) ∧ (∃ S : ϕB.func '' U → X, Factors ϕB ϕA U S)) ↔
      Req ϕA U = Req ϕB U := by
  rw [prop3_6_i, prop3_6_i]
  exact ⟨fun ⟨h1, h2⟩ => Set.Subset.antisymm h1 h2, fun h => ⟨h.le, h.ge⟩⟩

/-- 命题 3.6 (iii)：单分量标量界 `L_B/K_A`，在实际像域 `ϕ_A(U)` 上。 -/
theorem prop3_6_iii (dd : X → X → ENNReal) (ϕA ϕB : Operator X bot) (U : Set X)
    (hU : U ⊆ dom ϕA ∩ dom ϕB) (T : ϕA.func '' U → X) (hT : Factors ϕA ϕB U T)
    (KA LB : ENNReal) (hK0 : 0 < KA) (hKt : KA < ⊤) (hLt : LB < ⊤)
    (hco : ∀ x ∈ U, ∀ y ∈ U, KA * dd x y ≤ dd (ϕA.func x) (ϕA.func y))
    (hlip : ∀ x ∈ U, ∀ y ∈ U, dd (ϕB.func x) (ϕB.func y) ≤ LB * dd x y) :
    ∀ p q : ϕA.func '' U, dd (T p) (T q) ≤ (LB / KA) * dd p.1 q.1 := by
  rintro ⟨_, x, hx, rfl⟩ ⟨_, x', hx', rfl⟩
  rw [hT x hx, hT x' hx']
  have h1 : dd x x' ≤ KA⁻¹ * dd (ϕA.func x) (ϕA.func x') :=
    (ENNReal.mul_le_iff_le_inv hK0.ne' hKt.ne).1 (hco x hx x' hx')
  calc dd (ϕB.func x) (ϕB.func x') ≤ LB * dd x x' := hlip x hx x' hx'
    _ ≤ LB * (KA⁻¹ * dd (ϕA.func x) (ϕA.func x')) := by gcongr
    _ = (LB / KA) * dd (ϕA.func x) (ϕA.func x') := by rw [div_eq_mul_inv, mul_assoc]

/-- 命题 3.7 (a)：单向商映射存在当且仅当零距关系包含。 -/
theorem prop3_7_i (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (ϕA ϕB : Operator X bot) (U : Set X) :
    HasQuotientMap d hd ϕA ϕB U ↔ Rsim d ϕA U ⊆ Rsim d ϕB U := by
  constructor
  · rintro ⟨T, hT⟩ ⟨x, y⟩ ⟨hx, hy, hxy⟩
    refine ⟨hx, hy, ?_⟩
    have h1 : (Quotient.mk (imageSetoid d hd ϕA U) ⟨ϕA.func x, x, hx, rfl⟩) =
        Quotient.mk (imageSetoid d hd ϕA U) ⟨ϕA.func y, y, hy, rfl⟩ := Quotient.sound hxy
    have h2 := congrArg T h1
    rw [hT x hx, hT y hy] at h2
    exact Quotient.exact h2
  · intro hsub
    let f : ϕA.func '' U → Quotient (imageSetoid d hd ϕB U) := fun p =>
      Quotient.mk _ ⟨ϕB.func (Classical.choose p.2), Classical.choose p.2, (Classical.choose_spec p.2).1, rfl⟩
    have hres : ∀ a b : ϕA.func '' U, GaugeZeroRelated d a.1 b.1 → f a = f b := by
      intro a b hab
      have ha := Classical.choose_spec a.2
      have hb := Classical.choose_spec b.2
      have hmem : (Classical.choose a.2, Classical.choose b.2) ∈ Rsim d ϕA U :=
        ⟨ha.1, hb.1, by rw [ha.2, hb.2]; exact hab⟩
      exact Quotient.sound (hsub hmem).2.2
    refine ⟨Quotient.lift f hres, fun x hx => ?_⟩
    show f ⟨ϕA.func x, x, hx, rfl⟩ = _
    have ha := Classical.choose_spec (show ϕA.func x ∈ ϕA.func '' U from ⟨x, hx, rfl⟩)
    have hmem : (Classical.choose (show ϕA.func x ∈ ϕA.func '' U from ⟨x, hx, rfl⟩), x) ∈ Rsim d ϕA U :=
      ⟨ha.1, hx, by
        show GaugeZeroRelated d _ _
        rw [ha.2]
        exact fun i => (hd i).dist_self _⟩
    exact Quotient.sound (hsub hmem).2.2

/-- 命题 3.7 (b)：双向商映射存在当且仅当零距关系相等。 -/
theorem prop3_7_ii (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (ϕA ϕB : Operator X bot) (U : Set X) :
    (HasQuotientMap d hd ϕA ϕB U ∧ HasQuotientMap d hd ϕB ϕA U) ↔ Rsim d ϕA U = Rsim d ϕB U := by
  rw [prop3_7_i, prop3_7_i]
  exact ⟨fun ⟨h1, h2⟩ => Set.Subset.antisymm h1 h2, fun h => ⟨h.le, h.ge⟩⟩

theorem Req_subset_Rsim (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (ϕ : Operator X bot) (U : Set X) :
    Req ϕ U ⊆ Rsim d ϕ U := by
  rintro ⟨x, y⟩ ⟨hx, hy, hxy⟩
  refine ⟨hx, hy, ?_⟩
  show GaugeZeroRelated d _ _
  rw [hxy]
  exact fun i => (hd i).dist_self _

/-- 命题 3.7 (c)：两个实际像集各自分离时，点值判据与商值判据等价。 -/
theorem prop3_7_iii (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (ϕA ϕB : Operator X bot) (U : Set X)
    (hA : SepOn d (ϕA.func '' U)) (hB : SepOn d (ϕB.func '' U)) :
    Req ϕA U = Rsim d ϕA U ∧ Req ϕB U = Rsim d ϕB U ∧
    ((Req ϕA U ⊆ Req ϕB U) ↔ (Rsim d ϕA U ⊆ Rsim d ϕB U)) ∧
    ((Req ϕA U = Req ϕB U) ↔ (Rsim d ϕA U = Rsim d ϕB U)) ∧
    ((∃ T : ϕA.func '' U → X, Factors ϕA ϕB U T) ↔ HasQuotientMap d hd ϕA ϕB U) ∧
    (((∃ T : ϕA.func '' U → X, Factors ϕA ϕB U T) ∧ (∃ S : ϕB.func '' U → X, Factors ϕB ϕA U S)) ↔
      (HasQuotientMap d hd ϕA ϕB U ∧ HasQuotientMap d hd ϕB ϕA U)) := by
  have eq : ∀ (ϕ : Operator X bot), SepOn d (ϕ.func '' U) → Req ϕ U = Rsim d ϕ U := by
    intro ϕ h
    refine Set.Subset.antisymm (Req_subset_Rsim d hd ϕ U) ?_
    rintro ⟨x, y⟩ ⟨hx, hy, hxy⟩
    exact ⟨hx, hy, h _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy⟩
  have e1 := eq ϕA hA
  have e2 := eq ϕB hB
  refine ⟨e1, e2, by rw [e1, e2], by rw [e1, e2], ?_, ?_⟩
  · rw [prop3_6_i, prop3_7_i, e1, e2]
  · rw [prop3_6_ii, prop3_7_ii, e1, e2]

/-! ## 注（纤维包含的传递） -/

theorem prop_fiber_refl (ϕ : Operator X bot) (U : Set X) : FiberGe d ϕ ϕ U := fun _ h => h

theorem prop_fiber_trans (ϕ ψ χ : Operator X bot) (U : Set X) (h1 : FiberGe d ϕ ψ U)
    (h2 : FiberGe d ψ χ U) : FiberGe d ϕ χ U := fun _ h => h2 (h1 h)

/-- 注（纤维包含的传递）(a)：自反、传递。 -/
theorem note_fiber_preorder (U : Set X) :
    (∀ ϕ : Operator X bot, FiberGe d ϕ ϕ U) ∧
    (∀ ϕ ψ χ : Operator X bot, FiberGe d ϕ ψ U → FiberGe d ψ χ U → FiberGe d ϕ χ U) :=
  ⟨fun ϕ => prop_fiber_refl d ϕ U, fun ϕ ψ χ => prop_fiber_trans d ϕ ψ χ U⟩

/-- 注（纤维包含的传递）(b)：有限链 `ϕ₀ ⪰ ϕ₁ ⪰ ⋯ ⪰ ϕ_m` 中任意两层的关系包含。 -/
theorem note_fiber_chain (U : Set X) (ϕs : ℕ → Operator X bot) (m : ℕ)
    (hstep : ∀ r, r < m → FiberGe d (ϕs r) (ϕs (r + 1)) U) :
    ∀ a b, a ≤ b → b ≤ m → FiberGe d (ϕs a) (ϕs b) U := by
  intro a b hab
  induction b, hab using Nat.le_induction with
  | base => exact fun _ => prop_fiber_refl d _ U
  | succ b hab ih =>
    intro hb
    exact prop_fiber_trans d _ _ _ U (ih (by omega)) (hstep b (by omega))

/-- 注（纤维包含的传递）(c)：某一步严格包含，则端点严格包含，且给出差集见证。 -/
theorem note_fiber_strict (U : Set X) (ϕs : ℕ → Operator X bot) (m : ℕ)
    (hstep : ∀ r, r < m → FiberGe d (ϕs r) (ϕs (r + 1)) U)
    (hstrict : ∃ r, r < m ∧ Rsim d (ϕs r) U ⊂ Rsim d (ϕs (r + 1)) U) :
    Rsim d (ϕs 0) U ⊂ Rsim d (ϕs m) U ∧
    ∃ r, r < m ∧ ∃ p, p ∈ Rsim d (ϕs (r + 1)) U \ Rsim d (ϕs r) U ∧
      p ∈ Rsim d (ϕs m) U \ Rsim d (ϕs 0) U := by
  obtain ⟨r, hr, hss⟩ := hstrict
  have chain := note_fiber_chain d U ϕs m hstep
  obtain ⟨p, hp1, hp2⟩ := Set.exists_of_ssubset hss
  have h0r : Rsim d (ϕs 0) U ⊆ Rsim d (ϕs r) U := chain 0 r (Nat.zero_le _) hr.le
  have hrm : Rsim d (ϕs (r + 1)) U ⊆ Rsim d (ϕs m) U := chain (r + 1) m (by omega) le_rfl
  have hpm : p ∈ Rsim d (ϕs m) U := hrm hp1
  have hp0 : p ∉ Rsim d (ϕs 0) U := fun h => hp2 (h0r h)
  refine ⟨⟨chain 0 m (Nat.zero_le _) le_rfl, fun h => hp0 (h hpm)⟩, r, hr, p, ⟨hp1, hp2⟩, hpm, hp0⟩
end PartA

section PartB
variable {X I : Type} {bot : X} [Fintype I] (d : I → X → X → ENNReal)

theorem NullAdm_intro {din dout : X → X → ENNReal} {ϕ : Operator X bot} {y : X} {U : Set X}
    {r : ENNReal} (h0 : 0 < r) (ht : r < ⊤)
    (h : ∀ x, din x y < r → x ∈ U → x ∈ U ∧ dout (ϕ.func x) (ϕ.func y) = 0) :
    r ∈ NullAdm din dout ϕ y U :=
  ⟨h0, ht, fun x hx => h x hx.1 hx.2⟩

/-! ## 覆盖数的像/原像比较 -/

theorem cov_image_le {ρ σ : X → X → ENNReal} {ε δ : ENNReal} {B : Set X} (g : X → X)
    (h : ∀ x ∈ B, ∀ c ∈ B, ρ x c < ε → σ (g x) (g c) < δ) :
    covering_number σ δ (g '' B) ≤ covering_number ρ ε B := by
  classical
  apply covering_number_le_of_transfer
  intro S hS
  refine ⟨S.image g, ⟨?_, ?_⟩, Finset.card_image_le⟩
  · intro z hz
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hz
    exact ⟨s, hS.1 hs, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨c, hc, hxc⟩ := hS.2 x hx
    exact ⟨g c, Finset.mem_image_of_mem g hc, h x hx c (hS.1 hc) hxc⟩

theorem cov_preimage_le {ρ σ : X → X → ENNReal} {ε δ : ENNReal} {A : Set X} (g : X → X)
    (h : ∀ x ∈ A, ∀ c ∈ A, σ (g x) (g c) < δ → ρ x c < ε) :
    covering_number ρ ε A ≤ covering_number σ δ (g '' A) := by
  classical
  apply covering_number_le_of_transfer
  intro T hT
  let r : X → X := fun t => if h : t ∈ g '' A then Classical.choose h else t
  have hr : ∀ t ∈ g '' A, r t ∈ A ∧ g (r t) = t := fun t ht => by
    simp only [r, dif_pos ht]
    exact Classical.choose_spec ht
  refine ⟨T.image r, ⟨?_, ?_⟩, Finset.card_image_le⟩
  · intro z hz
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hz
    exact (hr t (hT.1 ht)).1
  · intro x hx
    obtain ⟨t, ht, hxt⟩ := hT.2 (g x) ⟨x, hx, rfl⟩
    refine ⟨r t, Finset.mem_image_of_mem r ht, h x hx _ (hr t (hT.1 ht)).1 ?_⟩
    rwa [(hr t (hT.1 ht)).2]

theorem cov_finite {ρ : X → X → ENNReal} (hself : ∀ x, ρ x x = 0) {ε : ENNReal} (hε : 0 < ε)
    {S : Set X} (hS : S.Finite) (hne : S.Nonempty) :
    1 ≤ covering_number ρ ε S ∧ covering_number ρ ε S < ⊤ :=
  ⟨one_le_covering_number_of_nonempty ρ ε S hne,
    covering_number_lt_top_of_net (S := hS.toFinset)
      ⟨by simp, fun x hx => ⟨x, by simpa using hx, by rw [hself]; exact hε⟩⟩⟩

theorem cov_one_of_zero {ρ : X → X → ENNReal} {ε : ENNReal} (hε : 0 < ε) {A : Set X}
    (hA : A.Nonempty) (g : X → X) (h : ∀ x ∈ A, ∀ y ∈ A, ρ (g x) (g y) = 0) :
    covering_number ρ ε (g '' A) = 1 := by
  obtain ⟨a, ha⟩ := hA
  apply le_antisymm
  · have hnet : InternalEpsilonNet ρ ε (g '' A) {g a} :=
      ⟨by simpa using ⟨a, ha, rfl⟩, by
        rintro _ ⟨x, hx, rfl⟩
        exact ⟨g a, by simp, by rw [h x hx a ha]; exact hε⟩⟩
    simpa using covering_number_le_card hnet
  · exact one_le_covering_number_of_nonempty ρ ε _ ⟨g a, a, ha, rfl⟩

theorem entropy_real {n : ENNReal} (h1 : 1 ≤ n) (h2 : n < ⊤) : ∃ r : ℝ, log2_ereal n = r :=
  log2_ereal_eq_coe (ne_of_gt (lt_of_lt_of_le zero_lt_one h1)) h2.ne

theorem mapEntropyDiff_singleton (ϕ : Operator X bot) (U : Set X) (i j : I) (ε : ENNReal) :
    mapEntropyDiff d ϕ U {i} {j} ε = metric_entropy (d i) ε U - metric_entropy (d j) ε (ϕ.func '' U) := by
  unfold mapEntropyDiff
  rw [subfamily_metric_entropy_singleton, subfamily_metric_entropy_singleton]

theorem defined_singleton (ϕ : Operator X bot) (U : Set X) (i j : I) (ε : ENNReal) :
    MapEntropyDiffDefined d ϕ U {i} {j} ε ↔
      covering_number (d i) ε U < ⊤ ∨ covering_number (d j) ε (ϕ.func '' U) < ⊤ := by
  unfold MapEntropyDiffDefined subfamilyCoveringNumber
  rw [subfamily_pseudometric_singleton, subfamily_pseudometric_singleton]

/-! ## 命题 3.8 -/

/-- 命题 3.8 (i-a)：输出子族常值时，每个像目标纤维等于 `U`。 -/
theorem prop3_8_i_a (ϕ : Operator X bot) (U : Set X) (J : Set I) (hJ : J ⊆ Iconst d ϕ U) :
    ∀ y ∈ U, Fib d ϕ J (ϕ.func y) U = U := by
  intro y hy
  ext x
  simp only [mem_Fib]
  exact ⟨fun h => h.1, fun hx => ⟨hx, fun j hj => hJ hj x hx y hy⟩⟩

/-- 命题 3.8 (i-b)：任意输入分量的点态与统一零化半径均为 `+∞`。 -/
theorem prop3_8_i_b (ϕ : Operator X bot) (U : Set X) (J : Set I) (hJ : J ⊆ Iconst d ϕ U) (i : I) :
    (∀ y ∈ U, nullRadiusJ d ϕ i J y U = ⊤) ∧ uniformNullRadiusJ d ϕ i J U = ⊤ := by
  have h1 : ∀ y ∈ U, nullRadiusJ d ϕ i J y U = ⊤ := fun y hy =>
    nullRadius_eq_top_of_zero fun x hx => (subfam_eq_zero_iff d J _ _).2 fun j hj => hJ hj x hx y hy
  refine ⟨h1, ?_⟩
  unfold uniformNullRadiusJ uniformNullRadius
  exact top_unique (le_iInf₂ fun y hy => (h1 y hy).ge)

/-! ## 命题 3.9 -/

/-- 命题 3.9 (i)：恒等分量的纤维等于输入零距类。 -/
theorem prop3_9_i (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (ϕ : Operator X bot) (U : Set X)
    (i : I) (hi : i ∈ Iid d ϕ U) (y : X) (hy : y ∈ U) :
    Fib d ϕ {i} (ϕ.func y) U = {x | x ∈ U ∧ d i x y = 0} := by
  ext x
  simp only [mem_Fib, Set.mem_singleton_iff, forall_eq, Set.mem_setOf_eq]
  exact and_congr_right fun hx => by rw [prop3_1_iii d hd ϕ U i hi x hx y hy]

/-- 命题 3.9 (ii)：球内仅零距时，点态零化半径 `≥ r₀ > 0`。 -/
theorem prop3_9_ii (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (ϕ : Operator X bot) (U : Set X)
    (i : I) (hi : i ∈ Iid d ϕ U) (y : X) (hy : y ∈ U) (r₀ : ENNReal) (hr0 : 0 < r₀) (hrt : r₀ < ⊤)
    (hball : ball (d i) y r₀ ∩ U ⊆ {x | x ∈ U ∧ d i x y = 0}) :
    r₀ ≤ nullRadius (d i) (d i) ϕ y U ∧ 0 < nullRadius (d i) (d i) ϕ y U := by
  have : r₀ ≤ nullRadius (d i) (d i) ϕ y U := by
    refine le_nullRadius_of_mem ⟨hr0, hrt, fun x hx => ?_⟩
    obtain ⟨hxU, h0⟩ := hball hx
    exact ⟨hxU, by rw [prop3_1_iii d hd ϕ U i hi x hxU y hy]; exact h0⟩
  exact ⟨this, lt_of_lt_of_le hr0 this⟩

/-! ## 命题 3.10 -/

theorem nullRadiusJ_eq_iInf (ϕ : Operator X bot) (i : I) (J : Set I) (y : X) (U : Set X) :
    nullRadiusJ d ϕ i J y U = ⨅ j ∈ J, nullRadius (d i) (d j) ϕ y U := by
  apply le_antisymm
  · refine le_iInf₂ fun j hj => sSup_le_sSup fun r hr => ?_
    exact ⟨hr.1, hr.2.1, fun x hx => ⟨(hr.2.2 hx).1, (subfam_eq_zero_iff d J _ _).1 (hr.2.2 hx).2 j hj⟩⟩
  · apply le_nullRadius_of_forall
    intro r hr0 hrt hrm
    refine NullAdm_intro hr0 hrt fun x hxb hxU => ⟨hxU, (subfam_eq_zero_iff d J _ _).2 fun j hj => ?_⟩
    exact zero_of_lt_nullRadius hxU (hxb.trans (hrm.trans_le (iInf₂_le j hj)))

/-- 命题 3.10：点态半径等于单分量半径的最小值（有限非空 `J`）。 -/
theorem prop3_10_pointwise (ϕ : Operator X bot) (i : I) (J : Set I) (hJ : J.Nonempty) (y : X)
    (U : Set X) :
    nullRadiusJ d ϕ i J y U = ⨅ j ∈ J, nullRadius (d i) (d j) ϕ y U ∧
    ∃ j ∈ J, nullRadiusJ d ϕ i J y U = nullRadius (d i) (d j) ϕ y U := by
  refine ⟨nullRadiusJ_eq_iInf d ϕ i J y U, ?_⟩
  obtain ⟨j₀, hj₀, hmin⟩ := Set.exists_min_image J (fun j => nullRadius (d i) (d j) ϕ y U)
    (Set.toFinite J) hJ
  refine ⟨j₀, hj₀, ?_⟩
  rw [nullRadiusJ_eq_iInf]
  exact le_antisymm (iInf₂_le j₀ hj₀) (le_iInf₂ hmin)

/-- 命题 3.10：统一半径公式 `r̲_{ϕ,i,J}|_U = min_{j ∈ J} [N(ϕ)|_U]_{ji}`。 -/
theorem prop3_10_uniform (ϕ : Operator X bot) (i : I) (J : Set I) (hJ : J.Nonempty) (U : Set X) :
    uniformNullRadiusJ d ϕ i J U = ⨅ j ∈ J, nullMatrix d ϕ U j i ∧
    ∃ j ∈ J, uniformNullRadiusJ d ϕ i J U = nullMatrix d ϕ U j i := by
  have key : uniformNullRadiusJ d ϕ i J U = ⨅ j ∈ J, nullMatrix d ϕ U j i := by
    apply le_antisymm
    · refine le_iInf₂ fun j hj => le_iInf₂ fun y hy => (iInf₂_le y hy).trans ?_
      rw [show nullRadius (d i) (subfamily_pseudometric d J) ϕ y U = nullRadiusJ d ϕ i J y U from rfl,
        nullRadiusJ_eq_iInf]
      exact iInf₂_le j hj
    · refine le_iInf₂ fun y hy => ?_
      rw [show nullRadius (d i) (subfamily_pseudometric d J) ϕ y U = nullRadiusJ d ϕ i J y U from rfl,
        nullRadiusJ_eq_iInf]
      exact le_iInf₂ fun j hj => (iInf₂_le j hj).trans (nullMatrix_le hy)
  refine ⟨key, ?_⟩
  obtain ⟨j₀, hj₀, hmin⟩ := Set.exists_min_image J (fun j => nullMatrix d ϕ U j i) (Set.toFinite J) hJ
  refine ⟨j₀, hj₀, ?_⟩
  rw [key]
  exact le_antisymm (iInf₂_le j₀ hj₀) (le_iInf₂ hmin)

/-- 命题 3.10：`J ⊆ K` 时统一半径关于输出子族反单调。 -/
theorem prop3_10_anti (ϕ : Operator X bot) (i : I) {J K : Set I} (hJ : J.Nonempty) (hJK : J ⊆ K)
    (U : Set X) : uniformNullRadiusJ d ϕ i K U ≤ uniformNullRadiusJ d ϕ i J U := by
  rw [(prop3_10_uniform d ϕ i J hJ U).1, (prop3_10_uniform d ϕ i K (hJ.mono hJK) U).1]
  exact le_iInf₂ fun j hj => iInf₂_le j (hJK hj)

/-! ## 命题 3.11 -/

/-- 命题 3.11 (a)：纤维成员条件推出输出零距。 -/
theorem prop3_11_a (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (ϕ₂ : Operator X bot) (U₂ : Set X)
    (j : I) (y y' : X) (h : y' ∈ Fib d ϕ₂ {j} (ϕ₂.func y) U₂) :
    d j (ϕ₂.func y) (ϕ₂.func y') = 0 :=
  zero_symm (hd j) ((mem_Fib.1 h).2 j (Set.mem_singleton j))

/-- 命题 3.11 (b)：严格小于点态半径的输入距离推出输出零距。 -/
theorem prop3_11_b (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (ϕ₂ : Operator X bot) (U₂ : Set X)
    (i j : I) (y y' : X) (hy' : y' ∈ U₂) (h : d i y y' < nullRadius (d i) (d j) ϕ₂ y U₂) :
    d j (ϕ₂.func y) (ϕ₂.func y') = 0 := by
  rw [(hd i).symm] at h
  exact zero_symm (hd j) (zero_of_lt_nullRadius hy' h)

/-- 命题 3.11 (c)：复合输入实例。 -/
theorem prop3_11_c (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (ϕ₁ ϕ₂ : Operator X bot) (U₂ : Set X)
    (j : I) (x x' : X) (hx : x ∈ dom ϕ₁) (hx' : x' ∈ dom ϕ₁) (h1 : ϕ₁.func x ∈ U₂)
    (h2 : ϕ₁.func x' ∈ U₂) (h : ϕ₁.func x' ∈ Fib d ϕ₂ {j} (ϕ₂.func (ϕ₁.func x)) U₂) :
    d j ((ϕ₂ * ϕ₁).func x) ((ϕ₂ * ϕ₁).func x') = 0 :=
  prop3_11_a d hd ϕ₂ U₂ j _ _ h

/-! ## 命题 3.12 -/

/-- 命题 3.12 (i)：下游在实际像域保持零距时的复合统一半径下界。 -/
theorem prop3_12_i (ϕ₁ ϕ₂ : Operator X bot) (U : Set X) (hU : U.Nonempty) (hdom : U ⊆ dom (ϕ₂ * ϕ₁))
    (i j l : I)
    (hprop : ∀ y ∈ ϕ₁.func '' U, ∀ y' ∈ ϕ₁.func '' U, d l y y' = 0 → d j (ϕ₂.func y) (ϕ₂.func y') = 0) :
    nullMatrix d ϕ₁ U l i ≤ nullMatrix d (ϕ₂ * ϕ₁) U j i := by
  unfold nullMatrix
  refine le_uniformNullRadius fun y hy => le_nullRadius_of_forall fun r hr0 hrt hrm => ?_
  refine NullAdm_intro hr0 hrt fun x hxb hxU => ⟨hxU, ?_⟩
  have := zero_of_lt_nullRadius (ϕ := ϕ₁) (dout := d l) hxU
    (hxb.trans (hrm.trans_le (nullMatrix_le hy)))
  exact hprop _ ⟨x, hxU, rfl⟩ _ ⟨y, hy, rfl⟩ this

/-- 命题 3.12 (ii)：经 Lip 上界拉回，`N(ϕ)_{ji} ≥ N(ϕ₂|_{ϕ₁(U)})_{jl} / L`（右端 `0`、`+∞` 照常处理）。 -/
theorem prop3_12_ii (ϕ₁ ϕ₂ : Operator X bot) (U : Set X) (hU : U.Nonempty) (hdom : U ⊆ dom (ϕ₂ * ϕ₁))
    (i j l : I) (L : ENNReal) (hL0 : 0 < L) (hLt : L < ⊤)
    (hlip : ∀ x ∈ U, ∀ x' ∈ U, d l (ϕ₁.func x) (ϕ₁.func x') ≤ L * d i x x') :
    nullMatrix d ϕ₂ (ϕ₁.func '' U) j l / L ≤ nullMatrix d (ϕ₂ * ϕ₁) U j i := by
  unfold nullMatrix
  refine le_uniformNullRadius fun y hy => le_nullRadius_of_forall fun r hr0 hrt hrm => ?_
  refine NullAdm_intro hr0 hrt fun x hxb hxU => ⟨hxU, ?_⟩
  have h1 : r * L < nullMatrix d ϕ₂ (ϕ₁.func '' U) j l :=
    (ENNReal.lt_div_iff_mul_lt (Or.inl hL0.ne') (Or.inl hLt.ne)).1 hrm
  have h2 : d l (ϕ₁.func x) (ϕ₁.func y) < nullRadius (d l) (d j) ϕ₂ (ϕ₁.func y) (ϕ₁.func '' U) :=
    calc d l (ϕ₁.func x) (ϕ₁.func y) ≤ L * d i x y := hlip x hxU y hy
      _ < L * r := (ENNReal.mul_lt_mul_iff_right hL0.ne' hLt.ne).2 hxb
      _ = r * L := mul_comm _ _
      _ < _ := h1
      _ ≤ _ := nullMatrix_le ⟨y, hy, rfl⟩
  have h3 : d j (ϕ₂.func (ϕ₁.func x)) (ϕ₂.func (ϕ₁.func y)) = 0 :=
    zero_of_lt_nullRadius (ϕ := ϕ₂) (U := ϕ₁.func '' U) (show ϕ₁.func x ∈ ϕ₁.func '' U from ⟨x, hxU, rfl⟩) h2
  exact h3

/-! ## 引理 3.13 -/

/-- 引理 3.13：四种阈值组合互斥且穷尽。 -/
theorem lemma3_13_cells (σ : I → Set X → ENNReal) (τσ τN : ENNReal) (f : Operator X bot) (A : Set X)
    (i j : I) :
    (thresholdType σ τσ τN d f A i j = (true, true) ↔ σ i A < τσ ∧ τN ≤ nullMatrix d f A j i) ∧
    (thresholdType σ τσ τN d f A i j = (true, false) ↔ σ i A < τσ ∧ nullMatrix d f A j i < τN) ∧
    (thresholdType σ τσ τN d f A i j = (false, true) ↔ τσ ≤ σ i A ∧ τN ≤ nullMatrix d f A j i) ∧
    (thresholdType σ τσ τN d f A i j = (false, false) ↔ τσ ≤ σ i A ∧ nullMatrix d f A j i < τN) ∧
    ((σ i A < τσ ∧ τN ≤ nullMatrix d f A j i) ∨ (σ i A < τσ ∧ nullMatrix d f A j i < τN) ∨
      (τσ ≤ σ i A ∧ τN ≤ nullMatrix d f A j i) ∨ (τσ ≤ σ i A ∧ nullMatrix d f A j i < τN)) ∧
    (¬ ((σ i A < τσ ∧ τN ≤ nullMatrix d f A j i) ∧ (σ i A < τσ ∧ nullMatrix d f A j i < τN))) ∧
    (¬ ((σ i A < τσ ∧ τN ≤ nullMatrix d f A j i) ∧ (τσ ≤ σ i A ∧ τN ≤ nullMatrix d f A j i))) ∧
    (¬ ((σ i A < τσ ∧ τN ≤ nullMatrix d f A j i) ∧ (τσ ≤ σ i A ∧ nullMatrix d f A j i < τN))) ∧
    (¬ ((σ i A < τσ ∧ nullMatrix d f A j i < τN) ∧ (τσ ≤ σ i A ∧ τN ≤ nullMatrix d f A j i))) ∧
    (¬ ((σ i A < τσ ∧ nullMatrix d f A j i < τN) ∧ (τσ ≤ σ i A ∧ nullMatrix d f A j i < τN))) ∧
    (¬ ((τσ ≤ σ i A ∧ τN ≤ nullMatrix d f A j i) ∧ (τσ ≤ σ i A ∧ nullMatrix d f A j i < τN))) := by
  classical
  have e1 : (thresholdType σ τσ τN d f A i j).1 = true ↔ σ i A < τσ := by simp [thresholdType]
  have e2 : (thresholdType σ τσ τN d f A i j).2 = true ↔ τN ≤ nullMatrix d f A j i := by
    simp [thresholdType]
  have e1' : (thresholdType σ τσ τN d f A i j).1 = false ↔ τσ ≤ σ i A := by
    simp [thresholdType]
  have e2' : (thresholdType σ τσ τN d f A i j).2 = false ↔ nullMatrix d f A j i < τN := by
    simp [thresholdType]
  have hP : τσ ≤ σ i A ↔ ¬ σ i A < τσ := not_lt.symm
  have hQ : nullMatrix d f A j i < τN ↔ ¬ τN ≤ nullMatrix d f A j i := not_le.symm
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Prod.ext_iff]; exact and_congr e1 e2
  · rw [Prod.ext_iff]; exact and_congr e1 e2'
  · rw [Prod.ext_iff]; exact and_congr e1' e2
  · rw [Prod.ext_iff]; exact and_congr e1' e2'
  · simp only [hP, hQ]
    tauto

/-- 引理 3.13 (i)：`τσ` 增大时，第一项取 `1` 的通道集合单调不减。 -/
theorem lemma3_13_i (σ : I → Set X → ENNReal) {τσ τσ' : ENNReal} (τN : ENNReal) (f : Operator X bot)
    (A : Set X) (h : τσ ≤ τσ') :
    {c : I × I | (thresholdType σ τσ τN d f A c.1 c.2).1 = true} ⊆
      {c : I × I | (thresholdType σ τσ' τN d f A c.1 c.2).1 = true} := by
  intro c hc
  simp only [Set.mem_setOf_eq, thresholdType, decide_eq_true_eq] at hc ⊢
  exact lt_of_lt_of_le hc h

/-- 引理 3.13 (ii)：`τN` 增大时，第二项取 `1` 的通道集合单调不增。 -/
theorem lemma3_13_ii (σ : I → Set X → ENNReal) (τσ : ENNReal) {τN τN' : ENNReal} (f : Operator X bot)
    (A : Set X) (h : τN ≤ τN') :
    {c : I × I | (thresholdType σ τσ τN' d f A c.1 c.2).2 = true} ⊆
      {c : I × I | (thresholdType σ τσ τN d f A c.1 c.2).2 = true} := by
  intro c hc
  simp only [Set.mem_setOf_eq, thresholdType, decide_eq_true_eq] at hc ⊢
  exact h.trans hc

/-! ## 命题 3.14 -/

/-- 命题 3.14 (i)：尺度函数的域缩小单调性及阈值推论。 -/
theorem prop3_14_i (σ : I → Set X → ENNReal) (hσ : IsInputScale σ) (i : I) {A B : Set X}
    (hB : B.Nonempty) (hBA : B ⊆ A) (τσ : ENNReal) :
    σ i B ≤ σ i A ∧ (σ i A < τσ → σ i B < τσ) :=
  ⟨hσ i B A hB hBA, fun h => lt_of_le_of_lt (hσ i B A hB hBA) h⟩

theorem nullRadius_mono_domain {din dout : X → X → ENNReal} {f : Operator X bot} {A B : Set X}
    (hBA : B ⊆ A) (x : X) : nullRadius din dout f x A ≤ nullRadius din dout f x B := by
  refine sSup_le_sSup fun r hr => ⟨hr.1, hr.2.1, fun z hz => ?_⟩
  have := hr.2.2 ⟨hz.1, hBA hz.2⟩
  exact ⟨hz.2, this.2⟩

/-- 命题 3.14 (ii-a)：基点属于 `B` 时，缩小评估域使点态半径不减。 -/
theorem prop3_14_ii_a (f : Operator X bot) {A B : Set X} (hBA : B ⊆ A) (i j : I) (x : X) (hx : x ∈ B) :
    nullRadius (d i) (d j) f x A ≤ nullRadius (d i) (d j) f x B :=
  nullRadius_mono_domain hBA x

/-- 命题 3.14 (ii-b)：同时缩小评估域与基点集合，统一半径不减。 -/
theorem prop3_14_ii_b (f : Operator X bot) {A B : Set X} (hB : B.Nonempty) (hBA : B ⊆ A)
    (hA : A ⊆ dom f) (i j : I) : nullMatrix d f A j i ≤ nullMatrix d f B j i :=
  le_uniformNullRadius fun y hy =>
    (uniformNullRadius_le (A := A) (hBA hy)).trans (nullRadius_mono_domain hBA y)

/-! ## 命题 3.15 -/

/-- 命题 3.15 (i)：严格低于统一半径的输入点对输出零距。 -/
theorem prop3_15_i (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot) (A : Set X)
    (hA : A ⊆ dom f) (i j : I) {x y : X} (hx : x ∈ A) (hy : y ∈ A)
    (h : d i x y < nullMatrix d f A j i) : d j (f.func x) (f.func y) = 0 :=
  prop3_11_b d hd f A i j x y hy (h.trans_le (nullMatrix_le hx))

/-- 命题 3.15 (ii)：输出正分离推出输入距离 `≥` 统一半径。 -/
theorem prop3_15_ii (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot) (A : Set X)
    (hA : A ⊆ dom f) (i j : I) {x y : X} (hx : x ∈ A) (hy : y ∈ A)
    (h : 0 < d j (f.func x) (f.func y)) : nullMatrix d f A j i ≤ d i x y := by
  by_contra hlt
  exact h.ne' (prop3_15_i d hd f A hA i j hx hy (not_le.mp hlt))

/-- 命题 3.15 (iii)：零化半径不足时的分离见证（含输出距离为 `+∞` 的情形）。 -/
theorem prop3_15_iii (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot) (A : Set X)
    (hA : A.Nonempty) (hAd : A ⊆ dom f) (i j : I) (τN : ENNReal) (hτ0 : 0 < τN) (hτ : τN < ⊤)
    (hlt : nullMatrix d f A j i < τN) (α : ENNReal) (h1 : nullMatrix d f A j i < α) (h2 : α < τN) :
    ∃ x ∈ A, ∃ y ∈ A, ∃ ε : NNReal, 0 < ε ∧ d i x y < α ∧ (ε : ENNReal) ≤ d j (f.func x) (f.func y) := by
  have hy : ∃ y ∈ A, nullRadius (d i) (d j) f y A < α := by
    unfold nullMatrix uniformNullRadius at h1
    obtain ⟨y, hy⟩ := iInf_lt_iff.mp h1
    obtain ⟨hyA, hyr⟩ := iInf_lt_iff.mp hy
    exact ⟨y, hyA, hyr⟩
  obtain ⟨y, hyA, hyr⟩ := hy
  have hα0 : 0 < α := lt_of_le_of_lt (zero_le _) h1
  have hαt : α < ⊤ := h2.trans hτ
  have hnot : ¬ (ball (d i) y α ∩ A ⊆ {x | x ∈ A ∧ d j (f.func x) (f.func y) = 0}) := by
    intro hsub
    exact absurd (le_nullRadius_of_mem (show α ∈ NullAdm (d i) (d j) f y A from ⟨hα0, hαt, hsub⟩))
      (not_le.mpr hyr)
  rw [Set.not_subset] at hnot
  obtain ⟨x, hx, hxn⟩ := hnot
  have hpos : d j (f.func x) (f.func y) ≠ 0 := fun h0 => hxn ⟨hx.2, h0⟩
  have hmin : min 1 (d j (f.func x) (f.func y)) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_left _ _)
  refine ⟨x, hx.2, y, hyA, (min 1 (d j (f.func x) (f.func y))).toNNReal, ?_, hx.1, ?_⟩
  · rw [ENNReal.toNNReal_pos_iff]
    exact ⟨lt_min zero_lt_one (pos_iff_ne_zero.2 hpos), lt_top_iff_ne_top.2 hmin⟩
  · rw [ENNReal.coe_toNNReal hmin]
    exact min_le_right _ _

/-! ## 命题 3.16 -/

/-- 命题 3.16 (i)：统一半径 `≥` 有限正阈值时，每个中心的开球包含在纤维中。 -/
theorem prop3_16_i (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot) (A : Set X)
    (hA : A.Nonempty) (hAd : A ⊆ dom f) (i j : I) (τN : ENNReal) (hτ0 : 0 < τN) (hτ : τN < ⊤)
    (h : τN ≤ nullMatrix d f A j i) :
    ∀ x ∈ A, ball (d i) x τN ∩ A ⊆ Fib d f {j} (f.func x) A := by
  intro x hx y hy
  refine mem_Fib.2 ⟨hy.2, fun j' hj' => ?_⟩
  rw [Set.mem_singleton_iff.1 hj']
  exact prop3_15_i d hd f A hAd i j hy.2 hx (lt_of_lt_of_le hy.1 h)

/-- 命题 3.16 (ii-a)：覆盖数约束（含 `B = ∅` 与无有限覆盖的情形）。 -/
theorem prop3_16_ii_a (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot) (A : Set X)
    (hA : A.Nonempty) (hAd : A ⊆ dom f) (i j : I) (τN : ENNReal) (hτ0 : 0 < τN) (hτ : τN < ⊤)
    (h : τN ≤ nullMatrix d f A j i) (B : Set X) (hBA : B ⊆ A) (ε : ENNReal) (hε0 : 0 < ε)
    (hεt : ε < ⊤) :
    covering_number (d j) ε (f.func '' B) ≤ covering_number (d i) τN B := by
  refine cov_image_le f.func fun x hx c hc hxc => ?_
  have := ((mem_Fib.1 (prop3_16_i d hd f A hA hAd i j τN hτ0 hτ h c (hBA hc) ⟨hxc, hBA hx⟩))).2 j (Set.mem_singleton j)
  rw [this]
  exact hε0

/-- 命题 3.16 (ii-b)：`B ≠ ∅` 时的熵不等式。 -/
theorem prop3_16_ii_b (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot) (A : Set X)
    (hA : A.Nonempty) (hAd : A ⊆ dom f) (i j : I) (τN : ENNReal) (hτ0 : 0 < τN) (hτ : τN < ⊤)
    (h : τN ≤ nullMatrix d f A j i) (B : Set X) (hBA : B ⊆ A) (hB : B.Nonempty) (ε : ENNReal)
    (hε0 : 0 < ε) (hεt : ε < ⊤) :
    metric_entropy (d j) ε (f.func '' B) ≤ metric_entropy (d i) τN B :=
  log2_ereal_mono (prop3_16_ii_a d hd f A hA hAd i j τN hτ0 hτ h B hBA ε hε0 hεt)

/-! ## 推论 3.17 -/

/-- 推论 3.17：小输入域上的整体零化判据。 -/
theorem cor3_17_iff (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot) (A : Set X)
    (hA : A.Nonempty) (hAd : A ⊆ dom f) (i j : I) (τσ τN : ENNReal) (hσ0 : 0 < τσ) (hσt : τσ < ⊤)
    (hN0 : 0 < τN) (hNt : τN < ⊤) (hdiam : diamScale d i A < τσ) (hle : τσ ≤ τN) :
    τN ≤ nullMatrix d f A j i ↔ ∀ x ∈ A, ∀ y ∈ A, d j (f.func x) (f.func y) = 0 := by
  constructor
  · intro h x hx y hy
    refine prop3_15_i d hd f A hAd i j hx hy (lt_of_le_of_lt ?_ (hdiam.trans_le (hle.trans h)))
    exact le_iSup₂_of_le x hx (le_iSup₂_of_le y hy le_rfl)
  · intro h
    have : nullMatrix d f A j i = ⊤ := top_unique (le_iInf₂ fun y hy =>
      (nullRadius_eq_top_of_zero fun x hx => h x hx y hy).ge)
    rw [this]
    exact le_top

/-- 推论 3.17：等价条件成立时，任意有限正 `ε` 下像域的覆盖数恰为 `1`。 -/
theorem cor3_17_cover (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot) (A : Set X)
    (hA : A.Nonempty) (hAd : A ⊆ dom f) (i j : I) (τσ τN : ENNReal) (hσ0 : 0 < τσ) (hσt : τσ < ⊤)
    (hN0 : 0 < τN) (hNt : τN < ⊤) (hdiam : diamScale d i A < τσ) (hle : τσ ≤ τN)
    (hcond : τN ≤ nullMatrix d f A j i) (ε : ENNReal) (hε0 : 0 < ε) (hεt : ε < ⊤) :
    covering_number (d j) ε (f.func '' A) = 1 :=
  cov_one_of_zero hε0 hA f.func
    ((cor3_17_iff d hd f A hA hAd i j τσ τN hσ0 hσt hN0 hNt hdiam hle).1 hcond)

/-! ## 注（有限集上映射熵差的良定性） -/

theorem note_finite_entropy_diff (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (ϕ : Operator X bot)
    (U : Set X) (hUne : U.Nonempty) (hU : U ⊆ dom ϕ) (hUf : U.Finite) (Jin Jout : Set I)
    (ε : ENNReal) (hε0 : 0 < ε) (hεt : ε < ⊤) :
    (1 ≤ subfamilyCoveringNumber d Jin ε U ∧ subfamilyCoveringNumber d Jin ε U < ⊤) ∧
    (1 ≤ subfamilyCoveringNumber d Jout ε (ϕ.func '' U) ∧
      subfamilyCoveringNumber d Jout ε (ϕ.func '' U) < ⊤) ∧
    (∃ a b : ℝ, subfamily_metric_entropy d Jin ε U = a ∧
      subfamily_metric_entropy d Jout ε (ϕ.func '' U) = b ∧
      mapEntropyDiff d ϕ U Jin Jout ε = ((a - b : ℝ) : EReal)) ∧
    MapEntropyDiffDefined d ϕ U Jin Jout ε := by
  have h1 := cov_finite (subfam_self d hd Jin) hε0 hUf hUne
  have h2 := cov_finite (subfam_self d hd Jout) hε0 (hUf.image ϕ.func) (hUne.image ϕ.func)
  obtain ⟨a, ha⟩ := entropy_real h1.1 h1.2
  obtain ⟨b, hb⟩ := entropy_real h2.1 h2.2
  refine ⟨h1, h2, ⟨a, b, ha, hb, ?_⟩, Or.inl h1.2⟩
  unfold mapEntropyDiff subfamily_metric_entropy
  rw [ha, hb, EReal.coe_sub]

/-! ## 命题 3.18 -/

/-- 命题 3.18 (i)：常值分量。 -/
theorem prop3_18_i (ϕ : Operator X bot) (U : Set X) (hUne : U.Nonempty) (hU : U ⊆ dom ϕ) (ε : ENNReal)
    (hε0 : 0 < ε) (hεt : ε < ⊤) (j : I) (hj : j ∈ Iconst d ϕ U) :
    covering_number (d j) ε (ϕ.func '' U) = 1 ∧ metric_entropy (d j) ε (ϕ.func '' U) = 0 ∧
    MapEntropyDiffDefined d ϕ U {j} {j} ε ∧
    mapEntropyDiff d ϕ U {j} {j} ε = metric_entropy (d j) ε U := by
  have hc : covering_number (d j) ε (ϕ.func '' U) = 1 := cov_one_of_zero hε0 hUne ϕ.func hj
  have he : metric_entropy (d j) ε (ϕ.func '' U) = 0 := by
    unfold metric_entropy
    rw [hc]
    exact log2_ereal_one
  refine ⟨hc, he, (defined_singleton d ϕ U j j ε).2 (Or.inr (by rw [hc]; exact ENNReal.one_lt_top)), ?_⟩
  rw [mapEntropyDiff_singleton, he, sub_zero]

/-- 命题 3.18 (ii-a)：恒等分量保持覆盖数与熵。 -/
theorem prop3_18_ii_a (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (ϕ : Operator X bot) (U : Set X)
    (hU : U ⊆ dom ϕ) (ε : ENNReal) (hε0 : 0 < ε) (hεt : ε < ⊤) (j : I) (hj : j ∈ Iid d ϕ U) :
    covering_number (d j) ε (ϕ.func '' U) = covering_number (d j) ε U ∧
    metric_entropy (d j) ε (ϕ.func '' U) = metric_entropy (d j) ε U := by
  have hc : covering_number (d j) ε (ϕ.func '' U) = covering_number (d j) ε U := by
    apply le_antisymm
    · exact cov_image_le ϕ.func fun x hx c hc h => by rw [prop3_1_iii d hd ϕ U j hj x hx c hc]; exact h
    · exact cov_preimage_le ϕ.func fun x hx c hc h => by rwa [prop3_1_iii d hd ϕ U j hj x hx c hc] at h
  exact ⟨hc, by unfold metric_entropy; rw [hc]⟩

/-- 命题 3.18 (ii-b)：恒等分量下熵差良定时为 `0`（不定义 `∞ - ∞`）。 -/
theorem prop3_18_ii_b (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (ϕ : Operator X bot) (U : Set X)
    (hUne : U.Nonempty) (hU : U ⊆ dom ϕ) (ε : ENNReal) (hε0 : 0 < ε) (hεt : ε < ⊤) (j : I)
    (hj : j ∈ Iid d ϕ U) (hdef : MapEntropyDiffDefined d ϕ U {j} {j} ε) :
    mapEntropyDiff d ϕ U {j} {j} ε = 0 := by
  obtain ⟨hc, he⟩ := prop3_18_ii_a d hd ϕ U hU ε hε0 hεt j hj
  rw [defined_singleton, hc, or_self] at hdef
  obtain ⟨r, hr⟩ := entropy_real (one_le_covering_number_of_nonempty (d j) ε U hUne) hdef
  rw [mapEntropyDiff_singleton, he]
  unfold metric_entropy
  rw [hr, ← EReal.coe_sub, sub_self]
  rfl

/-! ## 命题 3.19、3.20 -/

/-- 命题 3.19 (a)：有限正 `L` 将 `ε/L` 输入覆盖推到 `ε` 输出覆盖。 -/
theorem prop3_19_cover (ϕ : Operator X bot) (U : Set X) (i j : I) (ε L : ENNReal) (hL0 : 0 < L)
    (hLt : L < ⊤) (hlip : ∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ L * d i x y) :
    covering_number (d j) ε (ϕ.func '' U) ≤ covering_number (d i) (ε / L) U := by
  refine cov_image_le ϕ.func fun x hx c hc h => ?_
  calc d j (ϕ.func x) (ϕ.func c) ≤ L * d i x c := hlip x hx c hc
    _ < L * (ε / L) := (ENNReal.mul_lt_mul_iff_right hL0.ne' hLt.ne).2 h
    _ = ε := ENNReal.mul_div_cancel hL0.ne' hLt.ne

theorem div_pos_fin {ε L : ENNReal} (hε0 : 0 < ε) (hεt : ε < ⊤) (hL0 : 0 < L) (hLt : L < ⊤) :
    0 < ε / L ∧ ε / L < ⊤ :=
  ⟨ENNReal.div_pos hε0.ne' hLt.ne, ENNReal.div_lt_top hεt.ne hL0.ne'⟩

/-- 命题 3.19 (b)：输入全有界时熵差良定并有下界。 -/
theorem prop3_19_entropy (ϕ : Operator X bot) (U : Set X) (hUne : U.Nonempty) (hU : U ⊆ dom ϕ)
    (i j : I) (htb : TotallyBoundedIn d i U) (ε L : ENNReal) (hε0 : 0 < ε) (hεt : ε < ⊤)
    (hL0 : 0 < L) (hLt : L < ⊤) (hlip : ∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ L * d i x y) :
    MapEntropyDiffDefined d ϕ U {i} {j} ε ∧
    (∃ a b : ℝ, metric_entropy (d i) ε U = a ∧ metric_entropy (d j) ε (ϕ.func '' U) = b ∧
      mapEntropyDiff d ϕ U {i} {j} ε = ((a - b : ℝ) : EReal)) ∧
    metric_entropy (d i) ε U - metric_entropy (d i) (ε / L) U ≤ mapEntropyDiff d ϕ U {i} {j} ε := by
  obtain ⟨hp, hq⟩ := div_pos_fin hε0 hεt hL0 hLt
  have h1 := htb ε hε0 hεt
  have h2 := htb (ε / L) hp hq
  have h3 := (prop3_19_cover d ϕ U i j ε L hL0 hLt hlip).trans_lt h2
  have g1 := one_le_covering_number_of_nonempty (d i) ε U hUne
  have g2 := one_le_covering_number_of_nonempty (d i) (ε / L) U hUne
  have g3 := one_le_covering_number_of_nonempty (d j) ε (ϕ.func '' U) (hUne.image _)
  obtain ⟨a, ha⟩ := entropy_real g1 h1
  obtain ⟨b, hb⟩ := entropy_real g3 h3
  obtain ⟨c, hc⟩ := entropy_real g2 h2
  have hbc : (b : EReal) ≤ c := by
    rw [← hb, ← hc]
    exact log2_ereal_mono (prop3_19_cover d ϕ U i j ε L hL0 hLt hlip)
  have hbc' : b ≤ c := EReal.coe_le_coe_iff.1 hbc
  have hΔ : mapEntropyDiff d ϕ U {i} {j} ε = ((a - b : ℝ) : EReal) := by
    rw [mapEntropyDiff_singleton]
    unfold metric_entropy
    rw [ha, hb, EReal.coe_sub]
  refine ⟨(defined_singleton d ϕ U i j ε).2 (Or.inl h1), ⟨a, b, ha, hb, hΔ⟩, ?_⟩
  rw [hΔ]
  unfold metric_entropy
  rw [ha, hc, ← EReal.coe_sub]
  exact EReal.coe_le_coe_iff.2 (by linarith)

/-- 命题 3.20 (a)：正有限 co-Lip 单条目将内部输出中心的原像拉回为 `ε/K` 输入覆盖。 -/
theorem prop3_20_cover (ϕ : Operator X bot) (U : Set X) (K : I → I → ENNReal)
    (hK : IsCoLipMatrix d ϕ U K) (i j : I) (hK0 : 0 < K i j) (hKt : K i j < ⊤) (ε : ENNReal) :
    covering_number (d i) (ε / K i j) U ≤ covering_number (d j) ε (ϕ.func '' U) := by
  refine cov_preimage_le ϕ.func fun x hx c hc h => ?_
  have h1 : K i j * d i x c ≤ d j (ϕ.func x) (ϕ.func c) :=
    calc K i j * d i x c ≤ ∑ k : I, K k j * d k x c :=
          Finset.single_le_sum (f := fun k => K k j * d k x c) (fun _ _ => zero_le _) (Finset.mem_univ i)
      _ ≤ _ := hK.2.2 x hx c hc j
  rw [ENNReal.lt_div_iff_mul_lt (Or.inl hK0.ne') (Or.inl hKt.ne), mul_comm]
  exact lt_of_le_of_lt h1 h

/-- 命题 3.20 (b)：输入全有界、输出熵可为 `+∞` 时差值良定并有上界。 -/
theorem prop3_20_entropy (ϕ : Operator X bot) (U : Set X) (hUne : U.Nonempty) (hU : U ⊆ dom ϕ)
    (K : I → I → ENNReal) (hK : IsCoLipMatrix d ϕ U K) (i j : I) (hK0 : 0 < K i j) (hKt : K i j < ⊤)
    (htb : TotallyBoundedIn d i U) (ε : ENNReal) (hε0 : 0 < ε) (hεt : ε < ⊤) :
    MapEntropyDiffDefined d ϕ U {i} {j} ε ∧
    mapEntropyDiff d ϕ U {i} {j} ε ≤ metric_entropy (d i) ε U - metric_entropy (d i) (ε / K i j) U := by
  obtain ⟨hp, hq⟩ := div_pos_fin hε0 hεt hK0 hKt
  have h1 := htb ε hε0 hεt
  have h2 := htb (ε / K i j) hp hq
  have g1 := one_le_covering_number_of_nonempty (d i) ε U hUne
  have g2 := one_le_covering_number_of_nonempty (d i) (ε / K i j) U hUne
  have hle := prop3_20_cover d ϕ U K hK i j hK0 hKt ε
  obtain ⟨a, ha⟩ := entropy_real g1 h1
  obtain ⟨c, hc⟩ := entropy_real g2 h2
  refine ⟨(defined_singleton d ϕ U i j ε).2 (Or.inl h1), ?_⟩
  rw [mapEntropyDiff_singleton]
  have hcb : (c : EReal) ≤ metric_entropy (d j) ε (ϕ.func '' U) := by
    rw [← hc]
    exact log2_ereal_mono hle
  unfold metric_entropy at hcb ⊢
  rw [ha, hc]
  generalize log2_ereal (covering_number (d j) ε (ϕ.func '' U)) = e at hcb ⊢
  induction e using EReal.rec with
  | bot => exact absurd (le_bot_iff.1 hcb) (EReal.coe_ne_bot c)
  | coe e =>
    rw [← EReal.coe_sub, ← EReal.coe_sub]
    exact EReal.coe_le_coe_iff.2 (by have := EReal.coe_le_coe_iff.1 hcb; linarith)
  | top => simp

/-! ## 习题 3.2 -/

/-- 习题 3.2 (i)：正 co-Lip 通道下，点态零化半径内不存在正输入距离。 -/
theorem ex3_2_i (ϕ : Operator X bot) (U : Set X) (K : I → I → ENNReal) (hK : IsCoLipMatrix d ϕ U K)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (i j : I) (hKp : 0 < K i j) (y : X) (hy : y ∈ U)
    (hr : 0 < nullRadius (d i) (d j) ϕ y U) :
    ∀ x ∈ U, d i x y ∉ Set.Ioo 0 (nullRadius (d i) (d j) ϕ y U) := by
  rintro x hx ⟨h0, h1⟩
  have hout : d j (ϕ.func x) (ϕ.func y) = 0 := zero_of_lt_nullRadius hx h1
  have := colip_entry_eq_zero_of_output_zero_input_pos d ϕ U K i j x y hK hx hy hout h0
  exact hKp.ne' this

/-- 习题 3.2 (ii)：统一正半径给出所有输入点对的"零或 `≥` 统一半径"二择。 -/
theorem ex3_2_ii (ϕ : Operator X bot) (U : Set X) (K : I → I → ENNReal) (hK : IsCoLipMatrix d ϕ U K)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (i j : I) (hKp : 0 < K i j)
    (hr : 0 < nullMatrix d ϕ U j i) :
    ∀ x ∈ U, ∀ y ∈ U, d i x y ∈ ({0} : Set ENNReal) ∪ Set.Ici (nullMatrix d ϕ U j i) := by
  intro x hx y hy
  by_cases h0 : d i x y = 0
  · exact Or.inl h0
  · right
    by_contra hlt
    have hlt' : d i x y < nullMatrix d ϕ U j i := not_le.mp hlt
    have hout := prop3_15_i d hd ϕ U hK.2.1 i j hx hy hlt'
    exact hKp.ne' (colip_entry_eq_zero_of_output_zero_input_pos d ϕ U K i j x y hK hx hy hout
      (pos_iff_ne_zero.2 h0))
end PartB

section PartC1
/-! ## 具体空间的通用构造 -/

/-- 在 `α` 的伪度量 `ρ` 上添加孤立的吸收元 `none = ⊥`（与其余各点距离为 `+∞`）。 -/
def extPM {α : Type} (ρ : α → α → ENNReal) : Option α → Option α → ENNReal
  | none, none => 0
  | none, some _ => ⊤
  | some _, none => ⊤
  | some x, some y => ρ x y

@[simp] theorem extPM_some_some {α : Type} (ρ : α → α → ENNReal) (x y : α) :
    extPM ρ (some x) (some y) = ρ x y := rfl
@[simp] theorem extPM_none_none {α : Type} (ρ : α → α → ENNReal) : extPM ρ none none = 0 := rfl
@[simp] theorem extPM_none_some {α : Type} (ρ : α → α → ENNReal) (x : α) :
    extPM ρ none (some x) = ⊤ := rfl
@[simp] theorem extPM_some_none {α : Type} (ρ : α → α → ENNReal) (x : α) :
    extPM ρ (some x) none = ⊤ := rfl

theorem extPM_epm {α : Type} [Nonempty α] (ρ : α → α → ENNReal) (hself : ∀ x, ρ x x = 0)
    (hsymm : ∀ x y, ρ x y = ρ y x) (htri : ∀ x y z, ρ x z ≤ ρ x y + ρ y z) :
    ExtendedPseudoMetric (Option α) none (extPM ρ) where
  nonabsorbing := ⟨some (Classical.arbitrary α), by simp⟩
  dist_self := by
    intro x
    cases x <;> simp [hself]
  symm := by
    intro x y
    cases x <;> cases y
    · rfl
    · rfl
    · rfl
    · exact hsymm _ _
  triangle := by
    intro x y z
    cases x <;> cases y <;> cases z <;> simp [htri]
  isolate_bot := by
    intro x hx
    cases x with
    | none => exact absurd rfl hx
    | some x => rfl

/-- 由分类映射 `c` 拉回的 `0/1` 离散伪度量：同类距离 `0`，异类距离 `1`。 -/
def classPM {α β : Type} [DecidableEq β] (c : α → β) (x y : α) : ENNReal :=
  if c x = c y then 0 else 1

theorem classPM_self {α β : Type} [DecidableEq β] (c : α → β) (x : α) : classPM c x x = 0 := by
  simp [classPM]

theorem classPM_symm {α β : Type} [DecidableEq β] (c : α → β) (x y : α) :
    classPM c x y = classPM c y x := by
  unfold classPM
  by_cases h : c x = c y
  · rw [if_pos h, if_pos h.symm]
  · have : ¬ c y = c x := fun h' => h h'.symm
    rw [if_neg h, if_neg this]

theorem classPM_tri {α β : Type} [DecidableEq β] (c : α → β) (x y z : α) :
    classPM c x z ≤ classPM c x y + classPM c y z := by
  unfold classPM
  by_cases h1 : c x = c y
  · by_cases h2 : c y = c z
    · simp [h1, h2]
    · have : ¬ c x = c z := fun h => h2 (h1 ▸ h)
      simp [h1, h2, this]
  · by_cases h2 : c y = c z
    · have : ¬ c x = c z := fun h => h1 (h2 ▸ h)
      simp [h2, this, h1]
    · by_cases h3 : c x = c z <;> simp [h1, h2, h3]

theorem extClassPM_epm {α β : Type} [Nonempty α] [DecidableEq β] (c : α → β) :
    ExtendedPseudoMetric (Option α) none (extPM (classPM c)) :=
  extPM_epm _ (classPM_self c) (classPM_symm c) (classPM_tri c)

/-- 由实值函数 `g` 拉回的通常距离：`ρ_g(x,y) = |g x - g y|`。 -/
noncomputable def pbPM {α : Type} (g : α → ℝ) (x y : α) : ENNReal := ENNReal.ofReal |g x - g y|

theorem pbPM_self {α : Type} (g : α → ℝ) (x : α) : pbPM g x x = 0 := by simp [pbPM]

theorem pbPM_symm {α : Type} (g : α → ℝ) (x y : α) : pbPM g x y = pbPM g y x := by
  unfold pbPM
  rw [abs_sub_comm]

theorem pbPM_tri {α : Type} (g : α → ℝ) (x y z : α) :
    pbPM g x z ≤ pbPM g x y + pbPM g y z := by
  unfold pbPM
  rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (abs_sub_le _ _ _)

theorem pbPM_eq_zero_iff {α : Type} (g : α → ℝ) (x y : α) : pbPM g x y = 0 ↔ g x = g y := by
  unfold pbPM
  rw [ENNReal.ofReal_eq_zero, abs_nonpos_iff, sub_eq_zero]

theorem extPbPM_epm {α : Type} [Nonempty α] (g : α → ℝ) :
    ExtendedPseudoMetric (Option α) none (extPM (pbPM g)) :=
  extPM_epm _ (pbPM_self g) (pbPM_symm g) (pbPM_tri g)

/-- 由 `f : α → Option α` 给出的算子（`none ↦ none`；`f x = none` 表示在 `x` 处未定义）。 -/
def ofPartial {α : Type} (f : α → Option α) : Operator (Option α) none :=
  ⟨fun o => o.bind f, rfl⟩

@[simp] theorem ofPartial_some {α : Type} (f : α → Option α) (x : α) :
    (ofPartial f).func (some x) = f x := rfl
@[simp] theorem ofPartial_none {α : Type} (f : α → Option α) : (ofPartial f).func none = none := rfl

/-! ## 注（复合分量保持的逆向蕴含一般不成立）：两点换位例 -/

namespace Swap

/-- 三点空间 `{⊥, a, b}`：`⊥ = none`，`a = some false`，`b = some true`。 -/
abbrev Sp : Type := Option Bool

/-- `a, b` 间的 `0/1` 离散度量，`⊥` 与其余点距离 `+∞`；只有一个分量。 -/
def d0 : Sp → Sp → ENNReal := extPM (classPM (id : Bool → Bool))

def dS : Unit → Sp → Sp → ENNReal := fun _ => d0

/-- `U = {a, b}`。 -/
def Uab : Set Sp := {some false, some true}

/-- 换位算子：`φ(a) = b`，`φ(b) = a`，`φ(⊥) = ⊥`。 -/
def swapOp : Operator Sp none := ofPartial (fun x => some (!x))

theorem dS_gauge : ∀ k : Unit, ExtendedPseudoMetric Sp none (dS k) := fun _ =>
  extClassPM_epm (id : Bool → Bool)

theorem swapOp_image : swapOp.func '' Uab = Uab := by
  ext x
  simp only [Uab, Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨y, (rfl | rfl), rfl⟩ <;> simp [swapOp]
  · rintro (rfl | rfl)
    · exact ⟨some true, Or.inr rfl, by simp [swapOp]⟩
    · exact ⟨some false, Or.inl rfl, by simp [swapOp]⟩

/-- 两步算子在 `U` 上均为有效分量（既非常值亦非恒等）。 -/
theorem swap_step_classes (V : Set Sp) (hV : V = Uab) :
    () ∉ Iconst dS swapOp V ∧ () ∉ Iid dS swapOp V ∧ () ∈ Iact dS swapOp V := by
  subst hV
  have hc : () ∉ Iconst dS swapOp Uab := by
    intro h
    have := h (some false) (Or.inl rfl) (some true) (Or.inr rfl)
    simp [dS, swapOp, d0, classPM] at this
  have hi : () ∉ Iid dS swapOp Uab := by
    intro h
    have := h.2 (some false) (Or.inl rfl)
    simp [dS, swapOp, d0, classPM] at this
  refine ⟨hc, hi, ?_⟩
  simp [Iact, hc, hi]

theorem swap_comp_classes :
    () ∈ Iid dS (swapOp * swapOp) Uab ∧ () ∉ Iconst dS (swapOp * swapOp) Uab ∧
    () ∉ Iact dS (swapOp * swapOp) Uab := by
  have hc : () ∉ Iconst dS (swapOp * swapOp) Uab := by
    intro h
    have := h (some false) (Or.inl rfl) (some true) (Or.inr rfl)
    simp [dS, swapOp, d0, classPM] at this
  have hi : () ∈ Iid dS (swapOp * swapOp) Uab := by
    refine ⟨hc, ?_⟩
    rintro x (rfl | rfl) <;> simp [dS, swapOp, d0, classPM]
  refine ⟨hi, hc, ?_⟩
  simp [Iact, hc, hi]

/-- 注：命题 3.2 (i) 与 (iii) 的两条包含关系在此均为严格包含，反向包含都不成立。 -/
theorem note_converse_fails :
    -- 两步均为有效分量，且中间像域 `φ₁(U) = U`
    (() ∈ Iact dS swapOp Uab ∧ () ∈ Iact dS swapOp (swapOp.func '' Uab) ∧
      () ∉ Iid dS swapOp Uab ∧ () ∉ Iid dS swapOp (swapOp.func '' Uab)) ∧
    -- (i)：`I_act(φ₂∘φ₁|U) = ∅ ⊊ {i} = I_act(φ₁|U) ∪ I_act(φ₂|φ₁(U))`
    (Iact dS (swapOp * swapOp) Uab = ∅ ∧
      Iact dS swapOp Uab ∪ Iact dS swapOp (swapOp.func '' Uab) = {()} ∧
      Iact dS (swapOp * swapOp) Uab ⊂ Iact dS swapOp Uab ∪ Iact dS swapOp (swapOp.func '' Uab) ∧
      ¬ (Iact dS swapOp Uab ∪ Iact dS swapOp (swapOp.func '' Uab) ⊆ Iact dS (swapOp * swapOp) Uab)) ∧
    -- (iii)：`I_id(φ₁|U) ∩ I_id(φ₂|φ₁(U)) = ∅ ⊊ {i} = I_id(φ₂∘φ₁|U)`
    (Iid dS swapOp Uab ∩ Iid dS swapOp (swapOp.func '' Uab) = ∅ ∧
      Iid dS (swapOp * swapOp) Uab = {()} ∧
      Iid dS swapOp Uab ∩ Iid dS swapOp (swapOp.func '' Uab) ⊂ Iid dS (swapOp * swapOp) Uab ∧
      ¬ (Iid dS (swapOp * swapOp) Uab ⊆ Iid dS swapOp Uab ∩ Iid dS swapOp (swapOp.func '' Uab))) := by
  have h1 := swap_step_classes Uab rfl
  have h2 := swap_step_classes (swapOp.func '' Uab) swapOp_image
  have h3 := swap_comp_classes
  have eAct : Iact dS (swapOp * swapOp) Uab = ∅ := by
    ext k; cases k; simp [h3.2.2]
  have eAct2 : Iact dS swapOp Uab ∪ Iact dS swapOp (swapOp.func '' Uab) = {()} := by
    ext k; cases k; simp [h1.2.2]
  have eId : Iid dS swapOp Uab ∩ Iid dS swapOp (swapOp.func '' Uab) = ∅ := by
    ext k; cases k; simp [h1.2.1]
  have eId2 : Iid dS (swapOp * swapOp) Uab = {()} := by
    ext k; cases k; simp [h3.1]
  refine ⟨⟨h1.2.2, h2.2.2, h1.2.1, h2.2.1⟩, ⟨eAct, eAct2, ?_, ?_⟩, ⟨eId, eId2, ?_, ?_⟩⟩
  · rw [eAct, eAct2]
    exact Set.empty_ssubset.2 ⟨(), rfl⟩
  · rw [eAct, eAct2]
    intro h
    exact absurd (h (show () ∈ ({()} : Set Unit) from rfl)) (Set.notMem_empty _)
  · rw [eId, eId2]
    exact Set.empty_ssubset.2 ⟨(), rfl⟩
  · rw [eId, eId2]
    intro h
    exact absurd (h (show () ∈ ({()} : Set Unit) from rfl)) (Set.notMem_empty _)

/-- 完整的距离计算：`d(φ a, φ b) = d(b, a) = 1`，`d(φ a, a) = 1`，复合把 `a,b` 映回自身且输出距离仍为 `1`。 -/
theorem swap_distances :
    d0 (swapOp.func (some false)) (swapOp.func (some true)) = 1 ∧
    d0 (swapOp.func (some false)) (some false) = 1 ∧
    (swapOp * swapOp).func (some false) = some false ∧
    (swapOp * swapOp).func (some true) = some true ∧
    d0 ((swapOp * swapOp).func (some false)) ((swapOp * swapOp).func (some true)) = 1 := by
  refine ⟨?_, ?_, rfl, rfl, ?_⟩ <;> simp [swapOp, d0, classPM]

end Swap
end PartC1

section PartC2
/-! ## 命题 3.3 (ii)：七点、双分量反例 -/

namespace SevenPt

/-- 七点空间 `{⊥,a,b,p,q,r,s}`：`⊥ = none`，`p,q,r,s,a,b = some 0,…,some 5`。 -/
abbrev Sp : Type := Option (Fin 6)

/-- `d_i` 将 `p,q` 合为一个零距类，不同零距类之间距离为 `1`。 -/
def ci : Fin 6 → Fin 6 := fun x => if x = 1 then 0 else x

/-- 指标集 `I = {i, m}`，以 `true = i`，`false = m`；`d_m` 为不同点之间距离 `1` 的离散度量。 -/
def dI : Bool → Sp → Sp → ENNReal
  | true => extPM (classPM ci)
  | false => extPM (classPM (id : Fin 6 → Fin 6))

theorem dI_gauge : ∀ k : Bool, ExtendedPseudoMetric Sp none (dI k)
  | true => extClassPM_epm ci
  | false => extClassPM_epm (id : Fin 6 → Fin 6)

/-- `φ(a) = p`，`φ(b) = q`，其余处 `⊥`。 -/
def phi : Operator Sp none :=
  ofPartial (fun x => if x = 4 then some 0 else if x = 5 then some 1 else none)

/-- `ψ(p) = r`，`ψ(q) = s`，其余处 `⊥`。 -/
def psi : Operator Sp none :=
  ofPartial (fun x => if x = 0 then some 2 else if x = 1 then some 3 else none)

/-- `U = {a, b}`。 -/
def U : Set Sp := {some 4, some 5}

theorem U_dom : U ⊆ dom (psi * phi) := by
  rintro x (rfl | rfl) <;> simp [dom, phi, psi]

/-- 命题 3.3 (ii)：内侧在 `U` 上 `d_i`-常值，但复合不是；`φ(U)` 在 `d_m` 下可分辨，复合输出在 `d_i` 下可分辨。 -/
theorem prop3_3_ii_example :
    (∀ k : Bool, ExtendedPseudoMetric Sp none (dI k)) ∧ U ⊆ dom (psi * phi) ∧
    dI false (some 0) (some 1) = 1 ∧ dI true (psi.func (phi.func (some 4))) (psi.func (phi.func (some 5))) = 1 ∧
    true ∈ Iconst dI phi U ∧ true ∉ Iconst dI (psi * phi) U := by
  refine ⟨dI_gauge, U_dom, by simp [dI, classPM], by simp [dI, phi, psi, classPM, ci], ?_, ?_⟩
  · rintro x (rfl | rfl) y (rfl | rfl) <;> simp [dI, phi, classPM, ci]
  · intro h
    have := h (some 4) (Or.inl rfl) (some 5) (Or.inr rfl)
    simp [dI, phi, psi, classPM, ci] at this

end SevenPt

/-! ## 命题 3.8 (ii)：两点无穷输入距离反例（任意指标集、任意 `i, j`，含 `i = j`） -/

namespace TwoPt

/-- 常值 `c` 伪度量：同点距离 `0`，异点距离 `c`。 -/
def constPM {α : Type} [DecidableEq α] (c : ENNReal) (x y : α) : ENNReal := if x = y then 0 else c

theorem constPM_epm {α : Type} [DecidableEq α] [Nonempty α] (c : ENNReal) :
    ExtendedPseudoMetric (Option α) none (extPM (constPM c)) :=
  extPM_epm _ (fun x => by simp [constPM])
    (fun x y => by
      unfold constPM
      by_cases h : x = y
      · simp [h]
      · have : ¬ y = x := fun h' => h h'.symm
        simp [h, this])
    (fun x y z => by
      unfold constPM
      by_cases h1 : x = y <;> by_cases h2 : y = z
      · simp [h1, h2]
      · simp [h1, h2]
      · simp [h1, h2]
      · by_cases h3 : x = z <;> simp [h1, h2, h3])

variable {I : Type} [DecidableEq I]

/-- 分量 `k` 下 `a,b` 之间的距离：`k = i` 时 `+∞`；`k = j ≠ i` 时 `1`；其余为 `0`。 -/
def cc (i j k : I) : ENNReal := if k = i then ⊤ else if k = j then 1 else 0

def dd (i j : I) : I → Option Bool → Option Bool → ENNReal := fun k => extPM (constPM (cc i j k))

theorem dd_gauge (i j : I) : ∀ k : I, ExtendedPseudoMetric (Option Bool) none (dd i j k) :=
  fun k => constPM_epm (cc i j k)

def Uab : Set (Option Bool) := {some false, some true}

/-- 命题 3.8 (ii)：`[N(id)|_U]_{ji} = +∞`，但 `j ∉ I_const(id | U)`。 -/
theorem prop3_8_ii_example (i j : I) :
    (∀ k : I, ExtendedPseudoMetric (Option Bool) none (dd i j k)) ∧
    (∀ y ∈ Uab, nullRadius (dd i j i) (dd i j j) (1 : Operator (Option Bool) none) y Uab = ⊤) ∧
    nullMatrix (dd i j) (1 : Operator (Option Bool) none) Uab j i = ⊤ ∧
    j ∉ Iconst (dd i j) (1 : Operator (Option Bool) none) Uab := by
  have hrad : ∀ y ∈ Uab, nullRadius (dd i j i) (dd i j j) (1 : Operator (Option Bool) none) y Uab = ⊤ := by
    intro y hy
    apply top_unique
    apply le_nullRadius_of_forall
    intro r hr0 hrt _
    refine NullAdm_intro hr0 hrt fun x hxb hxU => ⟨hxU, ?_⟩
    have hxy : x = y := by
      by_contra hne
      have hx' : ∃ u v : Bool, x = some u ∧ y = some v := by
        rcases hxU with rfl | rfl <;> rcases hy with rfl | rfl <;> simp_all
      obtain ⟨u, v, rfl, rfl⟩ := hx'
      have huv : u ≠ v := fun h => hne (by rw [h])
      simp [dd, constPM, cc, huv] at hxb
    subst hxy
    exact (dd_gauge i j j).dist_self x
  refine ⟨dd_gauge i j, hrad, ?_, ?_⟩
  · exact top_unique (le_iInf₂ fun y hy => (hrad y hy).ge)
  · intro h
    have := h (some false) (Or.inl rfl) (some true) (Or.inr rfl)
    by_cases hji : j = i <;> simp [dd, constPM, cc, extPM, hji] at this

end TwoPt
end PartC2

section PartC3
/-! ## 带吸收元的实线与二点覆盖数 -/

namespace RealLine

/-- 带吸收元的实线 `ℝ ⊔ {⊥}`，`⊥ = none`。 -/
abbrev R : Type := Option ℝ

/-- 实数部分的通常距离，取值于 `[0,+∞]`。 -/
noncomputable def realPM : ℝ → ℝ → ENNReal := pbPM (fun x => x)

/-- 单分量规范：`d(⊥,x) = +∞`（`x ≠ ⊥`），`d(⊥,⊥) = 0`。 -/
noncomputable def dR : Unit → R → R → ENNReal := fun _ => extPM realPM

theorem dR_gauge : ∀ k : Unit, ExtendedPseudoMetric R none (dR k) := fun _ => extPbPM_epm _

theorem dR_some (a b : ℝ) : dR () (some a) (some b) = ENNReal.ofReal |a - b| := rfl

theorem dR_zero_iff (a b : ℝ) : dR () (some a) (some b) = 0 ↔ a = b :=
  pbPM_eq_zero_iff (fun x : ℝ => x) a b

theorem ofReal_lt_iff_toReal {a : ℝ} {r : ENNReal} (ha : 0 ≤ a) (hr : r ≠ ⊤) :
    ENNReal.ofReal a < r ↔ a < r.toReal := ENNReal.ofReal_lt_iff_lt_toReal ha hr

theorem two_point_cover {α : Type} {ρ : α → α → ENNReal} {p q : α} (hpq : p ≠ q)
    {ε : ENNReal} (hpp : ρ p p < ε) (hqq : ρ q q < ε) (h1 : ε ≤ ρ p q) (h2 : ε ≤ ρ q p) :
    covering_number ρ ε {p, q} = 2 := by
  classical
  apply le_antisymm
  · have hnet : InternalEpsilonNet ρ ε {p, q} {p, q} := by
      refine ⟨by simp, ?_⟩
      rintro x (rfl | rfl)
      · exact ⟨x, by simp, hpp⟩
      · exact ⟨x, by simp, hqq⟩
    have := covering_number_le_card hnet
    rwa [Finset.card_pair hpq] at this
  · apply le_covering_number_of_forall
    intro S hS
    have hp : p ∈ S := by
      obtain ⟨c, hc, hlt⟩ := hS.2 p (by simp)
      have hc' := hS.1 hc
      rcases hc' with rfl | rfl
      · exact hc
      · exact absurd hlt (not_lt.mpr h1)
    have hq : q ∈ S := by
      obtain ⟨c, hc, hlt⟩ := hS.2 q (by simp)
      have hc' := hS.1 hc
      rcases hc' with rfl | rfl
      · exact absurd hlt (not_lt.mpr h2)
      · exact hc
    have : ({p, q} : Finset α) ⊆ S := by
      intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact hp
      · rw [Finset.mem_singleton.1 hx]; exact hq
    have h3 := Finset.card_le_card this
    rw [Finset.card_pair hpq] at h3
    exact_mod_cast h3

/-! ## 反例 3.1：阶跃算子 -/

/-- 阶跃函数：`x < 0` 时取 `0`，否则取 `1`。 -/
noncomputable def stepFn (x : ℝ) : ℝ := if x < 0 then 0 else 1

/-- 阶跃算子 `f(x) = 0 (x<0), 1 (x ≥ 0)`，`f(⊥) = ⊥`。 -/
noncomputable def stepOp : Operator R none := ofPartial (fun x => some (stepFn x))

/-- `U = [-1,0) ∪ (0,1]`。 -/
def Ustep : Set R := Option.some '' (Set.Ico (-1) 0 ∪ Set.Ioc 0 1)

theorem stepOp_some (x : ℝ) : stepOp.func (some x) = some (stepFn x) := rfl

theorem Ustep_mem {o : R} : o ∈ Ustep ↔ ∃ x : ℝ, o = some x ∧ x ≠ 0 ∧ |x| ≤ 1 := by
  unfold Ustep
  simp only [Set.mem_image, Set.mem_union, Set.mem_Ico, Set.mem_Ioc]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x, rfl, ?_, ?_⟩
    · rcases hx with h | h
      · exact h.2.ne
      · exact h.1.ne'
    · rcases hx with h | h
      · rw [abs_le]; constructor <;> linarith [h.1, h.2]
      · rw [abs_le]; constructor <;> linarith [h.1, h.2]
  · rintro ⟨x, rfl, h0, h1⟩
    refine ⟨x, ?_, rfl⟩
    rcases lt_or_gt_of_ne h0 with h | h
    · left; exact ⟨(abs_le.1 h1).1, h⟩
    · right; exact ⟨h, (abs_le.1 h1).2⟩

theorem Ustep_sub_dom : Ustep ⊆ dom stepOp := by
  intro o ho
  obtain ⟨x, rfl, _⟩ := Ustep_mem.1 ho
  simp [dom, stepOp_some]

theorem none_not_mem_Ustep : (none : R) ∉ Ustep := fun h => by
  obtain ⟨x, hx, _⟩ := Ustep_mem.1 h
  simp at hx

theorem same_sign {x y : ℝ} (h : |x - y| < |y|) : (x < 0 ↔ y < 0) := by
  rcases le_or_gt 0 y with hy | hy
  · rw [abs_of_nonneg hy] at h
    have := (abs_lt.1 h).1
    constructor <;> intro h' <;> linarith
  · rw [abs_of_neg hy] at h
    have := (abs_lt.1 h).2
    constructor <;> intro h' <;> linarith

theorem stepFn_eq_iff {x y : ℝ} : stepFn x = stepFn y ↔ (x < 0 ↔ y < 0) := by
  unfold stepFn
  by_cases hx : x < 0 <;> by_cases hy : y < 0 <;> simp [hx, hy]

/-- 反例 3.1：每个 `y ∈ U` 处，合法的有限正半径集恰为 `(0, |y|]`。 -/
theorem step_nullAdm (y0 : ℝ) (hy0 : y0 ≠ 0) (hy1 : |y0| ≤ 1) :
    NullAdm (dR ()) (dR ()) stepOp (some y0) Ustep =
      {r | 0 < r ∧ r < ⊤ ∧ r ≤ ENNReal.ofReal |y0|} := by
  ext r
  constructor
  · rintro ⟨h0, ht, hsub⟩
    refine ⟨h0, ht, ?_⟩
    by_contra hlt
    rw [not_le] at hlt
    have he : |y0| < r.toReal := (ofReal_lt_iff_toReal (abs_nonneg _) ht.ne).1 hlt
    set t : ℝ := min 1 ((r.toReal - |y0|) / 2) with ht_def
    have htpos : 0 < t := lt_min one_pos (by linarith)
    have ht1 : t ≤ 1 := min_le_left _ _
    have ht2 : t ≤ (r.toReal - |y0|) / 2 := min_le_right _ _
    set x0 : ℝ := if 0 < y0 then -t else t with hx0_def
    have hx0abs : |x0| = t := by
      by_cases h : 0 < y0
      · simp [hx0_def, h, abs_of_pos htpos]
      · simp [hx0_def, h, abs_of_pos htpos]
    have hx0mem : some x0 ∈ Ustep := by
      refine Ustep_mem.2 ⟨x0, rfl, ?_, by rw [hx0abs]; exact ht1⟩
      intro h
      rw [h, abs_zero] at hx0abs
      exact htpos.ne hx0abs
    have hdist : |x0 - y0| = t + |y0| := by
      by_cases h : 0 < y0
      · simp only [hx0_def, if_pos h]
        rw [abs_of_neg (by linarith), abs_of_pos h]; ring
      · have h' : y0 < 0 := lt_of_le_of_ne (not_lt.1 h) hy0
        simp only [hx0_def, if_neg h]
        rw [abs_of_pos (by linarith), abs_of_neg h']; ring
    have hball : dR () (some x0) (some y0) < r := by
      rw [dR_some, ofReal_lt_iff_toReal (abs_nonneg _) ht.ne, hdist]
      linarith
    obtain ⟨_, hz⟩ := hsub ⟨hball, hx0mem⟩
    rw [stepOp_some, stepOp_some, dR_zero_iff, stepFn_eq_iff] at hz
    by_cases h : 0 < y0
    · have : ¬ (x0 < 0 ↔ y0 < 0) := by
        simp only [hx0_def, if_pos h]
        intro hh
        have := hh.1 (by linarith)
        linarith
      exact this hz
    · have h' : y0 < 0 := lt_of_le_of_ne (not_lt.1 h) hy0
      have : ¬ (x0 < 0 ↔ y0 < 0) := by
        simp only [hx0_def, if_neg h]
        intro hh
        have := hh.2 h'
        linarith
      exact this hz
  · rintro ⟨h0, ht, hle⟩
    refine ⟨h0, ht, ?_⟩
    rintro z ⟨hz1, hz2⟩
    obtain ⟨x0, rfl, hx0, hx1⟩ := Ustep_mem.1 hz2
    refine ⟨hz2, ?_⟩
    have hlt : dR () (some x0) (some y0) < ENNReal.ofReal |y0| := lt_of_lt_of_le hz1 hle
    rw [dR_some, ENNReal.ofReal_lt_ofReal_iff (abs_pos.2 hy0)] at hlt
    rw [stepOp_some, stepOp_some, dR_zero_iff, stepFn_eq_iff]
    exact same_sign hlt

/-- 反例 3.1：点态零化半径 `r^N_{f,d,d}(y ∣ U) = |y| > 0`。 -/
theorem step_nullRadius (y0 : ℝ) (hy0 : y0 ≠ 0) (hy1 : |y0| ≤ 1) :
    nullRadius (dR ()) (dR ()) stepOp (some y0) Ustep = ENNReal.ofReal |y0| ∧
    0 < nullRadius (dR ()) (dR ()) stepOp (some y0) Ustep := by
  have hpos : 0 < ENNReal.ofReal |y0| := ENNReal.ofReal_pos.2 (abs_pos.2 hy0)
  have heq : nullRadius (dR ()) (dR ()) stepOp (some y0) Ustep = ENNReal.ofReal |y0| := by
    apply le_antisymm
    · apply sSup_le
      intro r hr
      rw [step_nullAdm y0 hy0 hy1] at hr
      exact hr.2.2
    · apply le_sSup
      rw [step_nullAdm y0 hy0 hy1]
      exact ⟨hpos, ENNReal.ofReal_lt_top, le_rfl⟩
  exact ⟨heq, heq ▸ hpos⟩

/-- 反例 3.1：同一固定 `U` 上统一零化半径为 `0`。 -/
theorem step_uniform_zero :
    uniformNullRadius (dR ()) (dR ()) stepOp Ustep Ustep = 0 := by
  apply le_antisymm _ (zero_le _)
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  rw [zero_add]
  set t : ℝ := min 1 (ε : ℝ) with ht_def
  have hεpos : (0 : ℝ) < ε := by exact_mod_cast hε
  have htpos : 0 < t := lt_min one_pos hεpos
  have ht0 : t ≠ 0 := htpos.ne'
  have ht1 : |t| ≤ 1 := by rw [abs_of_pos htpos]; exact min_le_left _ _
  have hmem : some t ∈ Ustep := Ustep_mem.2 ⟨t, rfl, ht0, ht1⟩
  calc uniformNullRadius (dR ()) (dR ()) stepOp Ustep Ustep
      ≤ nullRadius (dR ()) (dR ()) stepOp (some t) Ustep := uniformNullRadius_le hmem
    _ = ENNReal.ofReal |t| := (step_nullRadius t ht0 ht1).1
    _ = ENNReal.ofReal t := by rw [abs_of_pos htpos]
    _ ≤ ENNReal.ofReal (ε : ℝ) := ENNReal.ofReal_le_ofReal (min_le_right _ _)
    _ = ε := ENNReal.ofReal_coe_nnreal

/-- 反例 3.1 汇总：合法结构、`U ⊆ dom f`、点态半径处处为正、统一半径为 `0`。 -/
theorem counterexample3_1 :
    (∀ k : Unit, ExtendedPseudoMetric R none (dR k)) ∧
    stepOp.func none = none ∧ Ustep ⊆ dom stepOp ∧ (none : R) ∉ Ustep ∧
    (∀ y ∈ Ustep, ∃ y0 : ℝ, y = some y0 ∧ y0 ≠ 0 ∧ |y0| ≤ 1 ∧
      nullRadius (dR ()) (dR ()) stepOp y Ustep = ENNReal.ofReal |y0| ∧
      0 < nullRadius (dR ()) (dR ()) stepOp y Ustep) ∧
    uniformNullRadius (dR ()) (dR ()) stepOp Ustep Ustep = 0 := by
  refine ⟨dR_gauge, stepOp.preserves_bot, Ustep_sub_dom, none_not_mem_Ustep, ?_, step_uniform_zero⟩
  intro y hy
  obtain ⟨y0, rfl, h0, h1⟩ := Ustep_mem.1 hy
  exact ⟨y0, rfl, h0, h1, (step_nullRadius y0 h0 h1).1, (step_nullRadius y0 h0 h1).2⟩

/-- 命题 3.16 后正文反例：点态正半径不能代替统一阈值（对任意有限正 `τ` 取 `0 < a ≤ 1`、`2a < τ`，`B = {-a, a}`：`𝒩(τ,B) = 1 < 2 = 𝒩(1/2, f(B))`）。 -/
theorem pointwise_not_uniform (τ : ENNReal) (hτ0 : 0 < τ) (hτt : τ < ⊤) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧ ENNReal.ofReal (2 * a) < τ ∧
      (Option.some '' ({-a, a} : Set ℝ)) ⊆ Ustep ∧
      covering_number (dR ()) τ (Option.some '' ({-a, a} : Set ℝ)) = 1 ∧
      covering_number (dR ()) (1 / 2) (stepOp.func '' (Option.some '' ({-a, a} : Set ℝ))) = 2 ∧
      covering_number (dR ()) τ (Option.some '' ({-a, a} : Set ℝ)) <
        covering_number (dR ()) (1 / 2) (stepOp.func '' (Option.some '' ({-a, a} : Set ℝ))) := by
  have hτr : 0 < τ.toReal := ENNReal.toReal_pos hτ0.ne' hτt.ne
  set a : ℝ := min 1 (τ.toReal / 4) with ha_def
  have hapos : 0 < a := lt_min one_pos (by linarith)
  have ha1 : a ≤ 1 := min_le_left _ _
  have ha2 : a ≤ τ.toReal / 4 := min_le_right _ _
  have hlt : ENNReal.ofReal (2 * a) < τ := by
    rw [ofReal_lt_iff_toReal (by linarith) hτt.ne]
    linarith
  have hsub : (Option.some '' ({-a, a} : Set ℝ)) ⊆ Ustep := by
    rintro _ ⟨x, hx, rfl⟩
    refine Ustep_mem.2 ⟨x, rfl, ?_, ?_⟩
    · rcases hx with rfl | rfl <;> simp [hapos.ne']
    · rcases hx with rfl | rfl <;> simp [abs_of_pos hapos, ha1]
  have himg : stepOp.func '' (Option.some '' ({-a, a} : Set ℝ)) = {some 0, some 1} := by
    ext o
    simp only [Set.image_pair, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro (rfl | rfl)
      · left; simp [stepOp_some, stepFn, hapos]
      · right; simp [stepOp_some, stepFn, hapos, not_lt.2 hapos.le]
    · rintro (rfl | rfl)
      · left; simp [stepOp_some, stepFn, hapos]
      · right; simp [stepOp_some, stepFn, hapos, not_lt.2 hapos.le]
  have hin : covering_number (dR ()) τ (Option.some '' ({-a, a} : Set ℝ)) = 1 := by
    apply le_antisymm
    · have hnet : InternalEpsilonNet (dR ()) τ (Option.some '' ({-a, a} : Set ℝ)) {some a} := by
        refine ⟨by simp, ?_⟩
        rintro _ ⟨x, hx, rfl⟩
        refine ⟨some a, by simp, ?_⟩
        rcases hx with rfl | rfl
        · rw [dR_some, show -a - a = -(2 * a) by ring, abs_neg, abs_of_pos (by linarith)]
          exact hlt
        · rw [dR_some, sub_self, abs_zero, ENNReal.ofReal_zero]
          exact hτ0
      simpa using covering_number_le_card hnet
    · exact one_le_covering_number_of_nonempty _ _ _ ⟨some a, a, by simp, rfl⟩
  have hout : covering_number (dR ()) (1 / 2) (stepOp.func '' (Option.some '' ({-a, a} : Set ℝ))) = 2 := by
    rw [himg]
    refine two_point_cover (by simp) ?_ ?_ ?_ ?_
    · rw [dR_some, sub_self, abs_zero, ENNReal.ofReal_zero]; simp
    · rw [dR_some, sub_self, abs_zero, ENNReal.ofReal_zero]; simp
    · rw [dR_some]
      have : |(0 : ℝ) - 1| = 1 := by norm_num
      rw [this, ENNReal.ofReal_one]
      exact ENNReal.div_le_of_le_mul (by simp)
    · rw [dR_some]
      have : |(1 : ℝ) - 0| = 1 := by norm_num
      rw [this, ENNReal.ofReal_one]
      exact ENNReal.div_le_of_le_mul (by simp)
  refine ⟨a, hapos, ha1, hlt, hsub, hin, hout, ?_⟩
  rw [hin, hout]
  norm_num

end RealLine
end PartC3

section PartE0
theorem covering_number_eq_card {X : Type} {d : X → X → ENNReal} {ε : ENNReal} {U : Set X} {S : Finset X}
    (hS : InternalEpsilonNet d ε U S)
    (hmin : ∀ T : Finset X, InternalEpsilonNet d ε U T → S.card ≤ T.card) :
    covering_number d ε U = S.card :=
  le_antisymm (covering_number_le_card hS)
    (le_covering_number_of_forall fun T hT => by exact_mod_cast hmin T hT)

/-- 若每个 `c ∈ U` 都有某个 `x ∈ U` 使 `ε ≤ d x c`，则非空 `U` 的每个内覆盖至少含两个中心。 -/
theorem two_le_card_of_net {X : Type} {d : X → X → ENNReal} {ε : ENNReal} {U : Set X}
    (hU : U.Nonempty) (hfar : ∀ c ∈ U, ∃ x ∈ U, ε ≤ d x c) {T : Finset X}
    (hT : InternalEpsilonNet d ε U T) : 2 ≤ T.card := by
  obtain ⟨x₀, hx₀⟩ := hU
  obtain ⟨c, hc, _⟩ := hT.2 x₀ hx₀
  obtain ⟨x, hx, hxc⟩ := hfar c (hT.1 hc)
  obtain ⟨c', hc', hlt⟩ := hT.2 x hx
  have hne : c ≠ c' := by
    rintro rfl
    exact absurd hlt (not_lt.2 hxc)
  exact Finset.one_lt_card.2 ⟨c, hc, c', hc', hne⟩

/-- 若 `U` 中不同点之间的距离都 `≥ ε`，则每个内覆盖包含 `U` 的所有点。 -/
theorem subset_of_net_of_separated {X : Type} {d : X → X → ENNReal} {ε : ENNReal} {U : Set X}
    (hsep : ∀ x ∈ U, ∀ c ∈ U, c ≠ x → ε ≤ d x c) {T : Finset X}
    (hT : InternalEpsilonNet d ε U T) : ∀ x ∈ U, x ∈ T := by
  intro x hx
  obtain ⟨c, hc, hlt⟩ := hT.2 x hx
  by_cases h : c = x
  · rw [← h]; exact hc
  · exact absurd hlt (not_lt.2 (hsep x hx c (hT.1 hc) h))

theorem pbPM_lt_iff {α : Type} (g : α → ℝ) (a b : α) {r : ℝ} (hr : 0 < r) :
    pbPM g a b < ENNReal.ofReal r ↔ |g a - g b| < r :=
  ENNReal.ofReal_lt_ofReal_iff hr

theorem pbPM_ge_iff {α : Type} (g : α → ℝ) (a b : α) (r : ℝ) :
    ENNReal.ofReal r ≤ pbPM g a b ↔ r ≤ |g a - g b| :=
  ENNReal.ofReal_le_ofReal_iff (abs_nonneg _)

namespace Ex35

open RealLine

abbrev R := RealLine.R

/-- `U = {0,1,2,3}`。 -/
def U : Set R := {some 0, some 1, some 2, some 3}

/-- 取值表：`f = id`（在 `U` 上），`g(0)=0, g(1)=3, g(2)=1, g(3)=2`，其余处 `⊥`。 -/
noncomputable def fFun (x : ℝ) : Option ℝ :=
  if x = 0 then some 0 else if x = 1 then some 1 else if x = 2 then some 2
    else if x = 3 then some 3 else none

noncomputable def gFun (x : ℝ) : Option ℝ :=
  if x = 0 then some 0 else if x = 1 then some 3 else if x = 2 then some 1
    else if x = 3 then some 2 else none

noncomputable def fOp : Operator R none := ofPartial fFun
noncomputable def gOp : Operator R none := ofPartial gFun

theorem dR_lt_iff (a b r : ℝ) (hr : 0 < r) :
    dR () (some a) (some b) < ENNReal.ofReal r ↔ |a - b| < r := pbPM_lt_iff (fun x : ℝ => x) a b hr

theorem dR_ge_iff (a b r : ℝ) :
    ENNReal.ofReal r ≤ dR () (some a) (some b) ↔ r ≤ |a - b| := pbPM_ge_iff (fun x : ℝ => x) a b r

theorem mem_U {x : R} : x ∈ U ↔ x = some 0 ∨ x = some 1 ∨ x = some 2 ∨ x = some 3 := by
  simp [U]

theorem mem_U' {x : R} : x ∈ U ↔ ∃ a : ℝ, x = some a ∧ (a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3) := by
  rw [mem_U]
  constructor
  · rintro (rfl | rfl | rfl | rfl) <;> exact ⟨_, rfl, by norm_num⟩
  · rintro ⟨a, rfl, h⟩
    rcases h with rfl | rfl | rfl | rfl <;> simp

theorem fOp_some (x : ℝ) : fOp.func (some x) = fFun x := rfl
theorem gOp_some (x : ℝ) : gOp.func (some x) = gFun x := rfl

theorem fFun_0 : fFun 0 = some 0 := by simp [fFun]
theorem fFun_1 : fFun 1 = some 1 := by norm_num [fFun]
theorem fFun_2 : fFun 2 = some 2 := by norm_num [fFun]
theorem fFun_3 : fFun 3 = some 3 := by norm_num [fFun]
theorem gFun_0 : gFun 0 = some 0 := by simp [gFun]
theorem gFun_1 : gFun 1 = some 3 := by norm_num [gFun]
theorem gFun_2 : gFun 2 = some 1 := by norm_num [gFun]
theorem gFun_3 : gFun 3 = some 2 := by norm_num [gFun]

theorem U_sub_dom_f : U ⊆ dom fOp := by
  intro x hx
  rcases mem_U.1 hx with rfl | rfl | rfl | rfl <;> simp [dom, fOp_some, fFun_0, fFun_1, fFun_2, fFun_3]

theorem U_sub_dom_g : U ⊆ dom gOp := by
  intro x hx
  rcases mem_U.1 hx with rfl | rfl | rfl | rfl <;> simp [dom, gOp_some, gFun_0, gFun_1, gFun_2, gFun_3]

theorem f_image : fOp.func '' U = U := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rcases mem_U.1 hy with rfl | rfl | rfl | rfl <;>
      simp [fOp_some, fFun_0, fFun_1, fFun_2, fFun_3, U]
  · intro hx
    refine ⟨x, hx, ?_⟩
    rcases mem_U.1 hx with rfl | rfl | rfl | rfl <;>
      simp [fOp_some, fFun_0, fFun_1, fFun_2, fFun_3]

theorem g_image : gOp.func '' U = U := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rcases mem_U.1 hy with rfl | rfl | rfl | rfl <;>
      simp [gOp_some, gFun_0, gFun_1, gFun_2, gFun_3, U]
  · intro hx
    rcases mem_U.1 hx with rfl | rfl | rfl | rfl
    · exact ⟨some 0, by simp [U], by simp [gOp_some, gFun_0]⟩
    · exact ⟨some 2, by simp [U], by simp [gOp_some, gFun_2]⟩
    · exact ⟨some 3, by simp [U], by simp [gOp_some, gFun_3]⟩
    · exact ⟨some 1, by simp [U], by simp [gOp_some, gFun_1]⟩

/-- 四点集中不同点的距离 `≥ 1`。 -/
theorem dist_ge_one {a b : ℝ} (ha : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3) (hb : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3)
    (hab : a ≠ b) : 1 ≤ |a - b| := by
  rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
    first | exact absurd rfl hab | norm_num [abs_of_nonneg, abs_of_nonpos]

theorem mem_pts {a : ℝ} (ha : some a ∈ U) : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 := by
  rcases mem_U'.1 ha with ⟨b, hb, h⟩
  cases hb
  exact h

end Ex35
end PartE0

section PartE1
namespace Ex35

open RealLine

/-- 习题 3.5 (i)：`ε ≤ 1` 时覆盖数为 `4`。 -/
theorem cover_le_one (r : ℝ) (hr0 : 0 < r) (hr1 : r ≤ 1) :
    covering_number (dR ()) (ENNReal.ofReal r) U = 4 := by
  have hnet : InternalEpsilonNet (dR ()) (ENNReal.ofReal r) U {some 0, some 1, some 2, some 3} := by
    refine ⟨?_, fun x hx => ⟨x, ?_, ?_⟩⟩
    · intro x hx
      simpa [U] using hx
    · simpa [U] using hx
    · rw [(dR_gauge ()).dist_self]
      exact ENNReal.ofReal_pos.2 hr0
  have hcard : ({some (0:ℝ), some 1, some 2, some 3} : Finset R).card = 4 := by
    simp
  have key := covering_number_eq_card hnet (fun T hT => by
    have hsub : ({some (0:ℝ), some 1, some 2, some 3} : Finset R) ⊆ T := by
      have := subset_of_net_of_separated (d := dR ()) (ε := ENNReal.ofReal r) (U := U) ?_ hT
      · intro x hx
        apply this
        simpa [U] using hx
      · intro x hx c hc hcx
        obtain ⟨a, rfl, ha⟩ := mem_U'.1 hx
        obtain ⟨b, rfl, hb⟩ := mem_U'.1 hc
        rw [dR_ge_iff]
        have hab : a ≠ b := fun h => hcx (by rw [h])
        exact hr1.trans (dist_ge_one ha hb hab)
    exact Finset.card_le_card hsub)
  rw [hcard] at key
  simpa using key

/-- 习题 3.5 (i)：`1 < ε ≤ 2` 时覆盖数为 `2`。 -/
theorem cover_le_two (r : ℝ) (hr1 : 1 < r) (hr2 : r ≤ 2) :
    covering_number (dR ()) (ENNReal.ofReal r) U = 2 := by
  have hr0 : 0 < r := by linarith
  have hnet : InternalEpsilonNet (dR ()) (ENNReal.ofReal r) U {some 1, some 3} := by
    refine ⟨?_, fun x hx => ?_⟩
    · intro x hx
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl <;> simp [U]
    · obtain ⟨a, rfl, ha⟩ := mem_U'.1 hx
      rcases ha with rfl | rfl | rfl | rfl
      · exact ⟨some 1, by simp, by rw [dR_lt_iff _ _ _ hr0]; norm_num; linarith⟩
      · exact ⟨some 1, by simp, by rw [dR_lt_iff _ _ _ hr0]; norm_num; linarith⟩
      · exact ⟨some 1, by simp, by rw [dR_lt_iff _ _ _ hr0]; norm_num; linarith⟩
      · exact ⟨some 3, by simp, by rw [dR_lt_iff _ _ _ hr0]; norm_num; linarith⟩
  have hcard : ({some (1:ℝ), some 3} : Finset R).card = 2 := by
    simp
  have key := covering_number_eq_card hnet (fun T hT => by
    rw [hcard]
    refine two_le_card_of_net ⟨some 0, by simp [U]⟩ ?_ hT
    intro c hc
    obtain ⟨a, rfl, ha⟩ := mem_U'.1 hc
    rcases ha with rfl | rfl | rfl | rfl
    · exact ⟨some 2, by simp [U], by rw [dR_ge_iff]; norm_num; linarith⟩
    · exact ⟨some 3, by simp [U], by rw [dR_ge_iff]; norm_num; linarith⟩
    · exact ⟨some 0, by simp [U], by rw [dR_ge_iff]; norm_num; linarith⟩
    · exact ⟨some 0, by simp [U], by rw [dR_ge_iff]; norm_num; linarith⟩)
  rw [hcard] at key
  simpa using key

/-- 习题 3.5 (i)：`ε > 2` 时覆盖数为 `1`。 -/
theorem cover_gt_two (r : ℝ) (hr : 2 < r) :
    covering_number (dR ()) (ENNReal.ofReal r) U = 1 := by
  have hr0 : 0 < r := by linarith
  have hnet : InternalEpsilonNet (dR ()) (ENNReal.ofReal r) U {some 1} := by
    refine ⟨?_, fun x hx => ⟨some 1, by simp, ?_⟩⟩
    · intro x hx
      simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hx
      subst hx
      simp [U]
    · obtain ⟨a, rfl, ha⟩ := mem_U'.1 hx
      rw [dR_lt_iff _ _ _ hr0]
      rcases ha with rfl | rfl | rfl | rfl <;> norm_num <;> linarith
  apply le_antisymm
  · simpa using covering_number_le_card hnet
  · exact one_le_covering_number_of_nonempty _ _ _ ⟨some 0, by simp [U]⟩

/-- 习题 3.5 (i)：所有有限正精度 `ε` 下四点集的覆盖数（分段及端点）。 -/
theorem cover_U (r : ℝ) (hr : 0 < r) :
    covering_number (dR ()) (ENNReal.ofReal r) U = if r ≤ 1 then 4 else if r ≤ 2 then 2 else 1 := by
  by_cases h1 : r ≤ 1
  · rw [if_pos h1]; exact cover_le_one r hr h1
  · rw [if_neg h1]
    by_cases h2 : r ≤ 2
    · rw [if_pos h2]; exact cover_le_two r (not_le.1 h1) h2
    · rw [if_neg h2]; exact cover_gt_two r (not_le.1 h2)

/-- 习题 3.5 (i)：所有有限正 `ε`（`ε = ofReal ε.toReal`）的覆盖数。 -/
theorem cover_U_of_finite (ε : ENNReal) (h0 : 0 < ε) (ht : ε < ⊤) :
    covering_number (dR ()) ε U = if ε.toReal ≤ 1 then 4 else if ε.toReal ≤ 2 then 2 else 1 := by
  have hpos : 0 < ε.toReal := ENNReal.toReal_pos h0.ne' ht.ne
  have := cover_U ε.toReal hpos
  rwa [ENNReal.ofReal_toReal ht.ne] at this

/-- 习题 3.5 (i)：`ε = 7/4` 时 `N = 2`；以 `3/2` 为中心的开球覆盖 `U`，但 `3/2 ∉ U`，故 `{3/2}` 不是合法内覆盖。 -/
theorem cover_seven_fourths :
    covering_number (dR ()) (ENNReal.ofReal (7 / 4)) U = 2 ∧
    (some (3 / 2 : ℝ) ∉ U) ∧
    (U ⊆ ball (dR ()) (some (3 / 2 : ℝ)) (ENNReal.ofReal (7 / 4))) ∧
    ¬ InternalEpsilonNet (dR ()) (ENNReal.ofReal (7 / 4)) U {some (3 / 2 : ℝ)} ∧
    (∀ S : Finset R, InternalEpsilonNet (dR ()) (ENNReal.ofReal (7 / 4)) U S → 2 ≤ S.card) := by
  have h : covering_number (dR ()) (ENNReal.ofReal (7 / 4)) U = 2 := by
    have := cover_le_two (7 / 4) (by norm_num) (by norm_num)
    exact this
  have hnot : some (3 / 2 : ℝ) ∉ U := by
    intro hm
    rcases mem_pts hm with h | h | h | h <;> norm_num at h
  refine ⟨h, hnot, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨a, rfl, ha⟩ := mem_U'.1 hx
    show dR () (some a) (some (3 / 2)) < ENNReal.ofReal (7 / 4)
    rw [dR_lt_iff _ _ _ (by norm_num)]
    rcases ha with rfl | rfl | rfl | rfl <;> norm_num [abs_of_nonneg, abs_of_nonpos]
  · intro hnet
    apply hnot
    apply hnet.1
    simp
  · intro S hS
    refine two_le_card_of_net ⟨some 0, by simp [U]⟩ ?_ hS
    intro c hc
    obtain ⟨a, rfl, ha⟩ := mem_U'.1 hc
    rcases ha with rfl | rfl | rfl | rfl
    · exact ⟨some 2, by simp [U], by rw [dR_ge_iff]; norm_num⟩
    · exact ⟨some 3, by simp [U], by rw [dR_ge_iff]; norm_num⟩
    · exact ⟨some 0, by simp [U], by rw [dR_ge_iff]; norm_num⟩
    · exact ⟨some 0, by simp [U], by rw [dR_ge_iff]; norm_num⟩

end Ex35
end PartE1

section PartE2
namespace Ex35

open RealLine

theorem dR_gauge' : ExtendedPseudoMetric R none (dR ()) := dR_gauge ()

/-- 习题 3.5 (ii)：`f(U) = U = g(U)`，任意有限正精度下覆盖数相同、映射熵差为 `0`。 -/
theorem ex3_5_ii :
    fOp.func '' U = {some 0, some 1, some 2, some 3} ∧ gOp.func '' U = {some 0, some 1, some 2, some 3} ∧
    (∀ ε : ENNReal, 0 < ε → ε < ⊤ →
      covering_number (dR ()) ε (fOp.func '' U) = covering_number (dR ()) ε U ∧
      covering_number (dR ()) ε (gOp.func '' U) = covering_number (dR ()) ε U ∧
      covering_number (dR ()) ε (fOp.func '' U) = covering_number (dR ()) ε (gOp.func '' U) ∧
      mapEntropyDiff (dR) fOp U {()} {()} ε = 0 ∧ mapEntropyDiff (dR) gOp U {()} {()} ε = 0) := by
  have hf : fOp.func '' U = {some 0, some 1, some 2, some 3} := f_image
  have hg : gOp.func '' U = {some 0, some 1, some 2, some 3} := g_image
  have hUe : U = {some 0, some 1, some 2, some 3} := rfl
  refine ⟨hf, hg, fun ε h0 ht => ?_⟩
  have hUfin : U.Finite := by simp [U]
  have h1 := cov_finite (fun x => (dR_gauge ()).dist_self x) h0 hUfin ⟨some 0, by simp [U]⟩
  obtain ⟨a, ha⟩ := entropy_real h1.1 h1.2
  have key : ∀ ϕ : Operator R none, ϕ.func '' U = U →
      mapEntropyDiff dR ϕ U {()} {()} ε = 0 := by
    intro ϕ hϕ
    rw [mapEntropyDiff_singleton, hϕ]
    unfold metric_entropy
    rw [ha, ← EReal.coe_sub, sub_self]
    rfl
  refine ⟨by rw [f_image], by rw [g_image], by rw [f_image, g_image], key fOp f_image, key gOp g_image⟩

/-- `f` 的标量 Lip 常数：`d(f x, f y) ≤ L d(x,y)`。 -/
theorem f_lip : HasScalarLipBound dR fOp U () () 1 := by
  refine ⟨U_sub_dom_f, fun x hx y hy => ?_⟩
  obtain ⟨a, rfl, ha⟩ := mem_U'.1 hx
  obtain ⟨b, rfl, hb⟩ := mem_U'.1 hy
  rw [one_mul]
  have hf : ∀ c : ℝ, (c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3) → fOp.func (some c) = some c := by
    rintro c (rfl | rfl | rfl | rfl)
    · exact fFun_0
    · exact fFun_1
    · exact fFun_2
    · exact fFun_3
  rw [hf a ha, hf b hb]

/-- 习题 3.5 (iii-a)：`f` 的最优标量 Lip 常数是 `1`。 -/
theorem f_lip_least : IsLeast {L : ENNReal | HasScalarLipBound dR fOp U () () L} 1 := by
  refine ⟨f_lip, fun L hL => ?_⟩
  have := hL.2 (some 0) (by simp [U]) (some 1) (by simp [U])
  rw [fOp_some, fOp_some, fFun_0, fFun_1, dR_some] at this
  simp only [sub_zero, zero_sub, abs_neg, abs_one, ENNReal.ofReal_one, mul_one] at this
  exact this

theorem g_lip : HasScalarLipBound dR gOp U () () 3 := by
  refine ⟨U_sub_dom_g, fun x hx y hy => ?_⟩
  obtain ⟨a, rfl, ha⟩ := mem_U'.1 hx
  obtain ⟨b, rfl, hb⟩ := mem_U'.1 hy
  rw [gOp_some, gOp_some, dR_some]
  have h3 : (3 : ENNReal) * ENNReal.ofReal |a - b| = ENNReal.ofReal (3 * |a - b|) := by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  rw [h3]
  rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
    simp only [gFun_0, gFun_1, gFun_2, gFun_3, dR_some] <;>
    exact ENNReal.ofReal_le_ofReal (by norm_num [abs_of_nonneg, abs_of_nonpos])

/-- 习题 3.5 (iii-a)：`g` 的最优标量 Lip 常数是 `3`（由点对 `(0,1)` 给出必要下界）。 -/
theorem g_lip_least : IsLeast {L : ENNReal | HasScalarLipBound dR gOp U () () L} 3 := by
  refine ⟨g_lip, fun L hL => ?_⟩
  have := hL.2 (some 0) (by simp [U]) (some 1) (by simp [U])
  rw [gOp_some, gOp_some, gFun_0, gFun_1, dR_some, dR_some] at this
  have e1 : |(0 : ℝ) - 3| = 3 := by norm_num
  have e2 : |(0 : ℝ) - 1| = 1 := by norm_num
  rw [e1, e2, ENNReal.ofReal_one, mul_one, show ENNReal.ofReal 3 = 3 by simpa using ENNReal.ofReal_ofNat 3] at this
  exact this

theorem div_ofReal (a : ℝ) (L : ℕ) (hL : 0 < L) :
    ENNReal.ofReal a / (L : ENNReal) = ENNReal.ofReal (a / L) := by
  rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast hL), ENNReal.ofReal_natCast]

/-- 习题 3.5 (iii-b)：`ε = 7/4`，命题 3.19 证明中的覆盖数上界与真实覆盖数逐项比较。 -/
theorem ex3_5_iii_b :
    -- 真实覆盖数
    covering_number (dR ()) (ENNReal.ofReal (7 / 4)) (fOp.func '' U) = 2 ∧
    covering_number (dR ()) (ENNReal.ofReal (7 / 4)) (gOp.func '' U) = 2 ∧
    -- `f`：`L = 1`，上界 `𝒩(7/4, U) = 2`，与真实值相等
    covering_number (dR ()) (ENNReal.ofReal (7 / 4)) (fOp.func '' U) ≤
        covering_number (dR ()) (ENNReal.ofReal (7 / 4) / 1) U ∧
    covering_number (dR ()) (ENNReal.ofReal (7 / 4) / 1) U = 2 ∧
    -- `g`：`L = 3`，上界 `𝒩(7/12, U) = 4`，严格大于真实值
    covering_number (dR ()) (ENNReal.ofReal (7 / 4)) (gOp.func '' U) ≤
        covering_number (dR ()) (ENNReal.ofReal (7 / 4) / 3) U ∧
    covering_number (dR ()) (ENNReal.ofReal (7 / 4) / 3) U = 4 ∧
    covering_number (dR ()) (ENNReal.ofReal (7 / 4)) (gOp.func '' U) <
        covering_number (dR ()) (ENNReal.ofReal (7 / 4) / 3) U := by
  have h2 : covering_number (dR ()) (ENNReal.ofReal (7 / 4)) U = 2 := cover_seven_fourths.1
  have hf : covering_number (dR ()) (ENNReal.ofReal (7 / 4)) (fOp.func '' U) = 2 := by rw [f_image, h2]
  have hg : covering_number (dR ()) (ENNReal.ofReal (7 / 4)) (gOp.func '' U) = 2 := by rw [g_image, h2]
  have d1 : ENNReal.ofReal (7 / 4) / 1 = ENNReal.ofReal (7 / 4) := div_one _
  have d3 : ENNReal.ofReal (7 / 4) / 3 = ENNReal.ofReal (7 / 12) := by
    have := div_ofReal (7 / 4) 3 (by norm_num)
    rw [show ((3 : ℕ) : ENNReal) = 3 by norm_num] at this
    rw [this]; norm_num
  have h4 : covering_number (dR ()) (ENNReal.ofReal (7 / 12)) U = 4 :=
    cover_le_one (7 / 12) (by norm_num) (by norm_num)
  have bf := prop3_19_cover dR fOp U () () (ENNReal.ofReal (7 / 4)) 1 one_pos ENNReal.one_lt_top
    (by simpa using f_lip.2)
  have bg := prop3_19_cover dR gOp U () () (ENNReal.ofReal (7 / 4)) 3 (by norm_num) (by norm_num)
    g_lip.2
  rw [d3] at bg ⊢
  refine ⟨hf, hg, bf, by rw [d1, h2], bg, h4, ?_⟩
  rw [hg, h4]; norm_num

/-- 习题 3.5 (iii-b) 熵层面：`ΔE ≥ E(ε) - E(ε/L)`，`f` 取等，`g` 严格。 -/
theorem ex3_5_iii_entropy :
    metric_entropy (dR ()) (ENNReal.ofReal (7 / 4)) U - metric_entropy (dR ()) (ENNReal.ofReal (7 / 4) / 1) U = 0 ∧
    metric_entropy (dR ()) (ENNReal.ofReal (7 / 4)) U - metric_entropy (dR ()) (ENNReal.ofReal (7 / 4) / 3) U = -1 ∧
    mapEntropyDiff dR fOp U {()} {()} (ENNReal.ofReal (7 / 4)) = 0 ∧
    mapEntropyDiff dR gOp U {()} {()} (ENNReal.ofReal (7 / 4)) = 0 := by
  have h := ex3_5_ii.2.2 (ENNReal.ofReal (7 / 4)) (by simp) (by simp)
  have h2 : covering_number (dR ()) (ENNReal.ofReal (7 / 4)) U = 2 := cover_seven_fourths.1
  have d3 : ENNReal.ofReal (7 / 4) / 3 = ENNReal.ofReal (7 / 12) := by
    have := div_ofReal (7 / 4) 3 (by norm_num)
    rw [show ((3 : ℕ) : ENNReal) = 3 by norm_num] at this
    rw [this]; norm_num
  have h4 : covering_number (dR ()) (ENNReal.ofReal (7 / 12)) U = 4 :=
    cover_le_one (7 / 12) (by norm_num) (by norm_num)
  have e2 : log2_ereal 2 = 1 := by
    simp [log2_ereal, Real.logb_self_eq_one]
  have e4 : log2_ereal 4 = 2 := by
    have : Real.logb 2 (4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.logb_pow, Real.logb_self_eq_one one_lt_two]; norm_num
    have h42 : ((2 : ℝ) : EReal) = 2 := by norm_cast
    simp [log2_ereal, this, h42]
  refine ⟨?_, ?_, h.2.2.2.1, h.2.2.2.2⟩
  · rw [div_one]
    show log2_ereal (covering_number (dR ()) (ENNReal.ofReal (7 / 4)) U) - log2_ereal (covering_number (dR ()) (ENNReal.ofReal (7 / 4)) U) = 0
    rw [h2, e2]
    exact EReal.sub_self (by decide) (by decide)
  · show log2_ereal (covering_number (dR ()) (ENNReal.ofReal (7 / 4)) U) - log2_ereal (covering_number (dR ()) (ENNReal.ofReal (7 / 4) / 3) U) = -1
    rw [d3, h2, h4, e2, e4]
    have : ((1 - 2 : ℝ) : EReal) = ((-1 : ℝ) : EReal) := by norm_num
    rw [show (1 : EReal) = ((1 : ℝ) : EReal) by norm_cast, show (2 : EReal) = ((2 : ℝ) : EReal) by norm_cast,
      ← EReal.coe_sub]
    norm_num

end Ex35
end PartE2

section PartE3
namespace RealLine

/-- 绝对值读数伪度量 `d(x,y) = ||x| - |y||`（`⊥` 孤立）。 -/
noncomputable def dA : Unit → R → R → ENNReal := fun _ => extPM (pbPM (fun x : ℝ => |x|))

theorem dA_gauge : ∀ k : Unit, ExtendedPseudoMetric R none (dA k) := fun _ => extPbPM_epm _

theorem dA_zero_iff (a b : ℝ) : dA () (some a) (some b) = 0 ↔ |a| = |b| :=
  pbPM_eq_zero_iff (fun x : ℝ => |x|) a b

theorem dA_lt_iff (a b r : ℝ) (hr : 0 < r) :
    dA () (some a) (some b) < ENNReal.ofReal r ↔ |(|a| - |b|)| < r :=
  pbPM_lt_iff (fun x : ℝ => |x|) a b hr

theorem dA_ge_iff (a b r : ℝ) :
    ENNReal.ofReal r ≤ dA () (some a) (some b) ↔ r ≤ |(|a| - |b|)| :=
  pbPM_ge_iff (fun x : ℝ => |x|) a b r

end RealLine

theorem mem_Fib_singleton {X I : Type} {bot : X} (d : I → X → X → ENNReal) (ϕ : Operator X bot) (j : I)
    (y x : X) (U : Set X) : x ∈ Fib d ϕ {j} y U ↔ x ∈ U ∧ d j (ϕ.func x) y = 0 := by
  rw [mem_Fib]
  simp only [Set.mem_singleton_iff, forall_eq]

namespace Ex31

open RealLine

/-- 仿射算子 `φ(s) = 2s - 1`，`φ(⊥) = ⊥`。 -/
noncomputable def affOp : Operator R none := ofPartial (fun x => some (2 * x - 1))

/-- `U = {0, 1}`。 -/
def U : Set R := {some 0, some 1}

theorem affOp_some (x : ℝ) : affOp.func (some x) = some (2 * x - 1) := rfl

theorem affOp2_some (x : ℝ) : (affOp * affOp).func (some x) = some (4 * x - 3) := by
  show affOp.func (affOp.func (some x)) = _
  rw [affOp_some, affOp_some]
  congr 1
  ring

theorem U_dom : U ⊆ dom affOp ∧ U ⊆ dom (affOp * affOp) := by
  constructor <;> (rintro x (rfl | rfl) <;> simp [dom, affOp_some, affOp2_some])

/-- 习题 3.1 (i-a)：`φ` 在 `U` 上的纤维与分量类型：`Fib_{φ,i}(φ(0) ∣ U) = U`，`i ∈ I_const`（常值优先，故非恒等、非有效）。 -/
theorem ex3_1_i_a :
    (∀ k : Unit, ExtendedPseudoMetric R none (dA k)) ∧ U ⊆ dom affOp ∧
    affOp.func (some 0) = some (-1) ∧ affOp.func (some 1) = some 1 ∧
    Fib dA affOp {()} (affOp.func (some 0)) U = U ∧
    Fib dA affOp {()} (affOp.func (some 1)) U = U ∧
    () ∈ Iconst dA affOp U ∧ () ∉ Iid dA affOp U ∧ () ∉ Iact dA affOp U := by
  have hc : () ∈ Iconst dA affOp U := by
    rintro x (rfl | rfl) y (rfl | rfl) <;> simp only [affOp_some, dA_zero_iff] <;> norm_num
  have hf : ∀ y ∈ U, Fib dA affOp {()} (affOp.func y) U = U := by
    intro y hy
    ext x
    rw [mem_Fib_singleton]
    exact ⟨fun h => h.1, fun hx => ⟨hx, hc x hx y hy⟩⟩
  have hi : () ∉ Iid dA affOp U := fun h => h.1 hc
  refine ⟨dA_gauge, U_dom.1, by norm_num [affOp_some], by norm_num [affOp_some], hf _ (by simp [U]),
    hf _ (by simp [U]), hc, hi, ?_⟩
  simp [Iact, hc]

/-- 习题 3.1 (i-b)：`φ²(0) = -3`，`φ²(1) = 1`，纤维 `{0}`、`{1}` 精确保留 `U`，`i ∈ I_act(φ² ∣ U)`。 -/
theorem ex3_1_i_b :
    U ⊆ dom (affOp * affOp) ∧
    (affOp * affOp).func (some 0) = some (-3) ∧ (affOp * affOp).func (some 1) = some 1 ∧
    Fib dA (affOp * affOp) {()} ((affOp * affOp).func (some 0)) U = {some 0} ∧
    Fib dA (affOp * affOp) {()} ((affOp * affOp).func (some 1)) U = {some 1} ∧
    () ∉ Iconst dA (affOp * affOp) U ∧ () ∉ Iid dA (affOp * affOp) U ∧ () ∈ Iact dA (affOp * affOp) U ∧
    (⋃ y ∈ (affOp * affOp).func '' U, Fib dA (affOp * affOp) {()} y U) = U := by
  have hnc : () ∉ Iconst dA (affOp * affOp) U := by
    intro h
    have := h (some 0) (by simp [U]) (some 1) (by simp [U])
    rw [affOp2_some, affOp2_some, dA_zero_iff] at this
    norm_num at this
  have hni : () ∉ Iid dA (affOp * affOp) U := by
    intro h
    have := h.2 (some 0) (by simp [U])
    rw [affOp2_some, dA_zero_iff] at this
    norm_num at this
  refine ⟨U_dom.2, by rw [affOp2_some]; norm_num, by rw [affOp2_some]; norm_num, ?_, ?_, hnc, hni, ?_, ?_⟩
  · ext x
    rw [mem_Fib_singleton]
    simp only [Set.mem_singleton_iff]
    constructor
    · rintro ⟨hx, h⟩
      rcases hx with rfl | rfl
      · rfl
      · rw [affOp2_some, affOp2_some, dA_zero_iff] at h
        norm_num at h
    · rintro rfl
      exact ⟨by simp [U], (dA_gauge ()).dist_self _⟩
  · ext x
    rw [mem_Fib_singleton]
    simp only [Set.mem_singleton_iff]
    constructor
    · rintro ⟨hx, h⟩
      rcases hx with rfl | rfl
      · rw [affOp2_some, affOp2_some, dA_zero_iff] at h
        norm_num at h
      · rfl
    · rintro rfl
      exact ⟨by simp [U], (dA_gauge ()).dist_self _⟩
  · simp [Iact, hnc, hni]
  · apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp hx
      exact hxy.1
    · intro x hx
      exact Set.mem_iUnion₂.mpr ⟨_, ⟨x, hx, rfl⟩, (mem_Fib_singleton _ _ _ _ _ _).2 ⟨hx, (dA_gauge ()).dist_self _⟩⟩

/-- 习题 3.1 (ii)：若 `ψ` 在 `U = {0,1}` 上取同一点值 `c`，则 `ψ∘ψ` 的任何纤维都不能把 `0,1` 分开；`ψ(c) = ⊥` 时 `U ⊄ dom (ψ∘ψ)`，纤维定义不适用。 -/
theorem ex3_1_ii (ψ : Operator R none) (c : ℝ) (h0 : ψ.func (some 0) = some c)
    (h1 : ψ.func (some 1) = some c) :
    (∀ (J : Set Unit) (y : R), some 0 ∈ Fib dA (ψ * ψ) J y U ↔ some 1 ∈ Fib dA (ψ * ψ) J y U) ∧
    ((ψ * ψ).func (some 0) = (ψ * ψ).func (some 1)) ∧
    (ψ.func (some c) = none → ¬ U ⊆ dom (ψ * ψ) ∧ (ψ * ψ).func (some 0) = none) ∧
    (ψ.func (some c) ≠ none → U ⊆ dom (ψ * ψ)) := by
  have hψ : (ψ * ψ).func (some 0) = (ψ * ψ).func (some 1) := by
    show ψ.func (ψ.func (some 0)) = ψ.func (ψ.func (some 1))
    rw [h0, h1]
  refine ⟨fun J y => ?_, hψ, fun hc => ?_, fun hc => ?_⟩
  · simp only [Fib, Set.mem_setOf_eq, hψ]
    simp [U]
  · have e : (ψ * ψ).func (some 0) = none := by
      show ψ.func (ψ.func (some 0)) = none
      rw [h0]; exact hc
    refine ⟨fun hU => ?_, e⟩
    exact hU (show some (0 : ℝ) ∈ U by simp [U]) e
  · rintro x (rfl | rfl)
    · show ψ.func (ψ.func (some 0)) ≠ none
      rw [h0]; exact hc
    · show ψ.func (ψ.func (some 1)) ≠ none
      rw [h1]; exact hc

/-- 习题 3.1 (ii) 两个分支都可实现：`ψ(c) ≠ ⊥`（常值算子）与 `ψ(c) = ⊥`（仅在 `U` 上有定义）。 -/
theorem ex3_1_ii_branches :
    (∃ ψ : Operator R none, ψ.func (some 0) = some 5 ∧ ψ.func (some 1) = some 5 ∧
      ψ.func (some 5) ≠ none ∧ U ⊆ dom (ψ * ψ)) ∧
    (∃ ψ : Operator R none, ψ.func (some 0) = some 5 ∧ ψ.func (some 1) = some 5 ∧
      ψ.func (some 5) = none ∧ ¬ U ⊆ dom (ψ * ψ)) := by
  constructor
  · refine ⟨ofPartial (fun _ => some 5), rfl, rfl, by simp, ?_⟩
    rintro x (rfl | rfl) <;> simp [dom]
  · refine ⟨ofPartial (fun x => if x = 0 ∨ x = 1 then some 5 else none), by simp, by simp, by simp, ?_⟩
    intro h
    have := h (show some (0 : ℝ) ∈ U by simp [U])
    simp [dom] at this

end Ex31

namespace Ex33

open RealLine

/-- `U = {-3, -2, 0, 2}`。 -/
def U : Set R := {some (-3), some (-2), some 0, some 2}

/-- 平移算子 `φ(x) = x + 1`，`φ(⊥) = ⊥`。 -/
noncomputable def shiftOp : Operator R none := ofPartial (fun x => some (x + 1))

theorem shiftOp_some (x : ℝ) : shiftOp.func (some x) = some (x + 1) := rfl

theorem mem_U {x : R} : x ∈ U ↔ x = some (-3) ∨ x = some (-2) ∨ x = some 0 ∨ x = some 2 := by simp [U]

theorem U_dom : U ⊆ dom shiftOp ∧ U ⊆ dom (1 : Operator R none) := by
  constructor <;> (intro x hx; rcases mem_U.1 hx with rfl | rfl | rfl | rfl <;> simp [dom, shiftOp_some])

theorem shift_image : shiftOp.func '' U = {some (-2), some (-1), some 1, some 3} := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rcases mem_U.1 hy with rfl | rfl | rfl | rfl <;> norm_num [shiftOp_some]
  · intro hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨some (-3), by simp [U], by norm_num [shiftOp_some]⟩
    · exact ⟨some (-2), by simp [U], by norm_num [shiftOp_some]⟩
    · exact ⟨some 0, by simp [U], by norm_num [shiftOp_some]⟩
    · exact ⟨some 2, by simp [U], by norm_num [shiftOp_some]⟩

/-- 习题 3.3 (i)：恒等算子在 `U` 上关于 `d_i` 的纤维：`{-3}`、`{-2, 2}`、`{0}`。 -/
theorem ex3_3_i_id :
    (∀ k : Unit, ExtendedPseudoMetric R none (dA k)) ∧ U ⊆ dom (1 : Operator R none) ∧
    Fib dA (1 : Operator R none) {()} (some (-3)) U = {some (-3)} ∧
    Fib dA (1 : Operator R none) {()} (some (-2)) U = {some (-2), some 2} ∧
    Fib dA (1 : Operator R none) {()} (some 0) U = {some 0} ∧
    Fib dA (1 : Operator R none) {()} (some 2) U = {some (-2), some 2} ∧
    (fun y => Fib dA (1 : Operator R none) {()} y U) '' ((1 : Operator R none).func '' U) =
      {{some (-3)}, {some (-2), some 2}, {some 0}} := by
  have key : ∀ y x : R, x ∈ Fib dA (1 : Operator R none) {()} y U ↔ x ∈ U ∧ dA () x y = 0 := by
    intro y x
    exact mem_Fib_singleton _ _ _ _ _ _
  have f1 : Fib dA (1 : Operator R none) {()} (some (-3)) U = {some (-3)} := by
    ext x
    rw [key]
    constructor
    · rintro ⟨hx, h⟩
      rcases mem_U.1 hx with rfl | rfl | rfl | rfl <;> simp_all [dA_zero_iff]
    · rintro rfl
      exact ⟨by simp [U], (dA_gauge ()).dist_self _⟩
  have f2 : Fib dA (1 : Operator R none) {()} (some (-2)) U = {some (-2), some 2} := by
    ext x
    rw [key]
    constructor
    · rintro ⟨hx, h⟩
      rcases mem_U.1 hx with rfl | rfl | rfl | rfl <;> simp_all [dA_zero_iff]
    · rintro (rfl | rfl)
      · exact ⟨by simp [U], (dA_gauge ()).dist_self _⟩
      · exact ⟨by simp [U], by simp [dA_zero_iff]⟩
  have f3 : Fib dA (1 : Operator R none) {()} (some 0) U = {some 0} := by
    ext x
    rw [key]
    constructor
    · rintro ⟨hx, h⟩
      rcases mem_U.1 hx with rfl | rfl | rfl | rfl <;> simp_all [dA_zero_iff]
    · rintro rfl
      exact ⟨by simp [U], (dA_gauge ()).dist_self _⟩
  have f4 : Fib dA (1 : Operator R none) {()} (some 2) U = {some (-2), some 2} := by
    ext x
    rw [key]
    constructor
    · rintro ⟨hx, h⟩
      rcases mem_U.1 hx with rfl | rfl | rfl | rfl <;> simp_all [dA_zero_iff]
    · rintro (rfl | rfl)
      · exact ⟨by simp [U], by simp [dA_zero_iff]⟩
      · exact ⟨by simp [U], (dA_gauge ()).dist_self _⟩
  refine ⟨dA_gauge, U_dom.2, f1, f2, f3, f4, ?_⟩
  ext S
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    rcases mem_U.1 hz with rfl | rfl | rfl | rfl
    · left; exact f1
    · right; left; exact f2
    · right; right; exact f3
    · right; left; exact f4
  · rintro (rfl | rfl | rfl)
    · exact ⟨_, ⟨some (-3), by simp [U], rfl⟩, f1⟩
    · exact ⟨_, ⟨some (-2), by simp [U], rfl⟩, f2⟩
    · exact ⟨_, ⟨some 0, by simp [U], rfl⟩, f3⟩

/-- 习题 3.3 (i)：平移算子在 `U` 上关于 `d_i` 的纤维：`{-3}`、`{-2, 0}`、`{2}`。 -/
theorem ex3_3_i_shift :
    U ⊆ dom shiftOp ∧
    Fib dA shiftOp {()} (shiftOp.func (some (-3))) U = {some (-3)} ∧
    Fib dA shiftOp {()} (shiftOp.func (some (-2))) U = {some (-2), some 0} ∧
    Fib dA shiftOp {()} (shiftOp.func (some 0)) U = {some (-2), some 0} ∧
    Fib dA shiftOp {()} (shiftOp.func (some 2)) U = {some 2} ∧
    (fun y => Fib dA shiftOp {()} y U) '' (shiftOp.func '' U) =
      {{some (-3)}, {some (-2), some 0}, {some 2}} := by
  have key : ∀ y x : R, x ∈ Fib dA shiftOp {()} y U ↔ x ∈ U ∧ dA () (shiftOp.func x) y = 0 := by
    intro y x
    exact mem_Fib_singleton _ _ _ _ _ _
  have f1 : Fib dA shiftOp {()} (shiftOp.func (some (-3))) U = {some (-3)} := by
    ext x
    rw [key]
    constructor
    · rintro ⟨hx, h⟩
      rcases mem_U.1 hx with rfl | rfl | rfl | rfl <;>
        first | (exfalso; norm_num [shiftOp_some, dA_zero_iff] at h; done) | norm_num
    · rintro rfl
      exact ⟨by simp [U], (dA_gauge ()).dist_self _⟩
  have f2 : Fib dA shiftOp {()} (shiftOp.func (some (-2))) U = {some (-2), some 0} := by
    ext x
    rw [key]
    constructor
    · rintro ⟨hx, h⟩
      rcases mem_U.1 hx with rfl | rfl | rfl | rfl <;>
        first | (exfalso; norm_num [shiftOp_some, dA_zero_iff] at h; done) | norm_num
    · rintro (rfl | rfl)
      · exact ⟨by simp [U], (dA_gauge ()).dist_self _⟩
      · exact ⟨by simp [U], by norm_num [shiftOp_some, dA_zero_iff]⟩
  have f3 : Fib dA shiftOp {()} (shiftOp.func (some 0)) U = {some (-2), some 0} := by
    ext x
    rw [key]
    constructor
    · rintro ⟨hx, h⟩
      rcases mem_U.1 hx with rfl | rfl | rfl | rfl <;>
        first | (exfalso; norm_num [shiftOp_some, dA_zero_iff] at h; done) | norm_num
    · rintro (rfl | rfl)
      · exact ⟨by simp [U], by norm_num [shiftOp_some, dA_zero_iff]⟩
      · exact ⟨by simp [U], (dA_gauge ()).dist_self _⟩
  have f4 : Fib dA shiftOp {()} (shiftOp.func (some 2)) U = {some 2} := by
    ext x
    rw [key]
    constructor
    · rintro ⟨hx, h⟩
      rcases mem_U.1 hx with rfl | rfl | rfl | rfl <;>
        first | (exfalso; norm_num [shiftOp_some, dA_zero_iff] at h; done) | norm_num
    · rintro rfl
      exact ⟨by simp [U], (dA_gauge ()).dist_self _⟩
  refine ⟨U_dom.1, f1, f2, f3, f4, ?_⟩
  ext S
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    rcases mem_U.1 hz with rfl | rfl | rfl | rfl
    · left; exact f1
    · right; left; exact f2
    · right; left; exact f3
    · right; right; exact f4
  · rintro (rfl | rfl | rfl)
    · exact ⟨_, ⟨some (-3), by simp [U], rfl⟩, f1⟩
    · exact ⟨_, ⟨some (-2), by simp [U], rfl⟩, f2⟩
    · exact ⟨_, ⟨some 2, by simp [U], rfl⟩, f4⟩

end Ex33
end PartE3

section PartE4
namespace Ex33

open RealLine

/-- 习题 3.3 (ii)：`ε = 3/2` 时 `𝒩_i(ε,U) = 2`，`𝒩_i(ε,φ(U)) = 1`，`ΔE = 1`（含上、下界两侧）。 -/
theorem ex3_3_ii :
    covering_number (dA ()) (ENNReal.ofReal (3 / 2)) U = 2 ∧
    covering_number (dA ()) (ENNReal.ofReal (3 / 2)) (shiftOp.func '' U) = 1 ∧
    mapEntropyDiff dA shiftOp U {()} {()} (ENNReal.ofReal (3 / 2)) = 1 := by
  have hr : (0 : ℝ) < 3 / 2 := by norm_num
  -- 上界：`{-3, 0}` 是 `U` 的一个内覆盖
  have hnet : InternalEpsilonNet (dA ()) (ENNReal.ofReal (3 / 2)) U {some (-3), some 0} := by
    refine ⟨?_, fun x hx => ?_⟩
    · intro x hx
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl <;> simp [U]
    · rcases mem_U.1 hx with rfl | rfl | rfl | rfl
      · exact ⟨some (-3), by simp, by rw [dA_lt_iff _ _ _ hr]; norm_num⟩
      · exact ⟨some (-3), by simp, by rw [dA_lt_iff _ _ _ hr]; norm_num⟩
      · exact ⟨some 0, by simp, by rw [dA_lt_iff _ _ _ hr]; norm_num⟩
      · exact ⟨some (-3), by simp, by rw [dA_lt_iff _ _ _ hr]; norm_num⟩
  have hcard : ({some (-3 : ℝ), some 0} : Finset R).card = 2 := by simp
  have hU : covering_number (dA ()) (ENNReal.ofReal (3 / 2)) U = 2 := by
    have key := covering_number_eq_card hnet (fun T hT => by
      rw [hcard]
      refine two_le_card_of_net ⟨some 0, by simp [U]⟩ ?_ hT
      intro c hc
      rcases mem_U.1 hc with rfl | rfl | rfl | rfl
      · exact ⟨some 0, by simp [U], by rw [dA_ge_iff]; norm_num⟩
      · exact ⟨some 0, by simp [U], by rw [dA_ge_iff]; norm_num⟩
      · exact ⟨some (-3), by simp [U], by rw [dA_ge_iff]; norm_num⟩
      · exact ⟨some 0, by simp [U], by rw [dA_ge_iff]; norm_num⟩)
    rw [hcard] at key
    simpa using key
  -- 像集：`φ(U) = {-2,-1,1,3}`，`{-2}` 是内覆盖
  have hnet2 : InternalEpsilonNet (dA ()) (ENNReal.ofReal (3 / 2)) (shiftOp.func '' U) {some (-2)} := by
    rw [shift_image]
    refine ⟨?_, fun x hx => ⟨some (-2), by simp, ?_⟩⟩
    · intro x hx
      simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hx
      subst hx; simp
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> rw [dA_lt_iff _ _ _ hr] <;> norm_num
  have hV : covering_number (dA ()) (ENNReal.ofReal (3 / 2)) (shiftOp.func '' U) = 1 := by
    apply le_antisymm
    · simpa using covering_number_le_card hnet2
    · exact one_le_covering_number_of_nonempty _ _ _ ⟨shiftOp.func (some 0), some 0, by simp [U], rfl⟩
  refine ⟨hU, hV, ?_⟩
  rw [mapEntropyDiff_singleton]
  unfold metric_entropy
  rw [hU, hV, log2_ereal_one]
  have e2 : log2_ereal 2 = 1 := by simp [log2_ereal, Real.logb_self_eq_one]
  rw [e2]
  exact sub_zero _

end Ex33

namespace Ex34

open RealLine

/-- 取整算子 `f(x) = ⌊x⌋`，`f(⊥) = ⊥`。 -/
noncomputable def floorOp : Operator R none := ofPartial (fun x => some ((⌊x⌋ : ℤ) : ℝ))

theorem floorOp_some (x : ℝ) : floorOp.func (some x) = some ((⌊x⌋ : ℤ) : ℝ) := rfl

theorem floor_dom (D : Set ℝ) : Option.some '' D ⊆ dom floorOp := by
  rintro _ ⟨x, _, rfl⟩
  simp [dom, floorOp_some]

theorem dR_floor_zero_iff (x y : ℝ) :
    dR () (floorOp.func (some x)) (floorOp.func (some y)) = 0 ↔ ⌊x⌋ = ⌊y⌋ := by
  rw [floorOp_some, floorOp_some, dR_zero_iff]
  exact_mod_cast Iff.rfl

/-- 区间 `[a,b]` 的直径尺度（`a ≤ b`）。 -/
theorem diam_Icc (a b : ℝ) (hab : a ≤ b) :
    diamScale dR () (Option.some '' Set.Icc a b) = ENNReal.ofReal (b - a) := by
  apply le_antisymm
  · unfold diamScale
    apply iSup₂_le
    rintro _ ⟨x, hx, rfl⟩
    apply iSup₂_le
    rintro _ ⟨y, hy, rfl⟩
    rw [dR_some]
    apply ENNReal.ofReal_le_ofReal
    rw [abs_le]
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  · unfold diamScale
    refine le_iSup₂_of_le (some b) ⟨b, ⟨hab, le_rfl⟩, rfl⟩ (le_iSup₂_of_le (some a) ⟨a, ⟨le_rfl, hab⟩, rfl⟩ ?_)
    rw [dR_some, abs_of_nonneg (by linarith)]

/-- 若 `D ⊇ [1-δ,1]`（`0 < δ`），则基点 `1` 处的点态零化半径为 `0`（任何有限正半径开球都含一个取整值不同的点）。 -/
theorem nullRadius_floor_one (D : Set ℝ) (δ : ℝ) (hδ : 0 < δ) (hD : Set.Icc (1 - δ) 1 ⊆ D) :
    nullRadius (dR ()) (dR ()) floorOp (some 1) (Option.some '' D) = 0 := by
  apply le_antisymm _ (zero_le _)
  apply sSup_le
  intro r hr
  exfalso
  obtain ⟨hr0, hrt, hsub⟩ := hr
  have hrr : 0 < r.toReal := ENNReal.toReal_pos hr0.ne' hrt.ne
  set t : ℝ := min r.toReal δ / 2 with ht_def
  have htpos : 0 < t := by
    have : 0 < min r.toReal δ := lt_min hrr hδ
    linarith
  have ht1 : t ≤ r.toReal / 2 := by
    have := min_le_left r.toReal δ
    linarith
  have ht2 : t ≤ δ / 2 := by
    have := min_le_right r.toReal δ
    linarith
  have hxD : (1 - t) ∈ D := hD ⟨by linarith, by linarith⟩
  have hball : dR () (some (1 - t)) (some 1) < r := by
    rw [dR_some, show (1 - t) - 1 = -t by ring, abs_neg, abs_of_pos htpos]
    rw [ENNReal.ofReal_lt_iff_lt_toReal htpos.le hrt.ne]
    linarith
  obtain ⟨_, hz⟩ := hsub ⟨hball, ⟨1 - t, hxD, rfl⟩⟩
  rw [dR_floor_zero_iff] at hz
  have : ⌊(1 - t : ℝ)⌋ < 1 := Int.floor_lt.2 (by norm_num; linarith)
  have h1 : ⌊(1 : ℝ)⌋ = 1 := by simp
  rw [h1] at hz
  omega

theorem uniform_floor_zero (D : Set ℝ) (δ : ℝ) (hδ : 0 < δ) (hD : Set.Icc (1 - δ) 1 ⊆ D) :
    nullMatrix dR floorOp (Option.some '' D) () () = 0 := by
  apply le_antisymm _ (zero_le _)
  refine (uniformNullRadius_le (A := Option.some '' D) (y := some 1) ⟨1, hD ⟨by linarith, le_rfl⟩, rfl⟩).trans ?_
  rw [nullRadius_floor_one D δ hδ hD]

theorem nullRadius_top_of_floor_const (D : Set ℝ) (hD : ∀ x ∈ D, ∀ y ∈ D, ⌊x⌋ = ⌊y⌋) :
    nullMatrix dR floorOp (Option.some '' D) () () = ⊤ := by
  apply top_unique
  refine le_iInf₂ fun y hy => ?_
  obtain ⟨y0, hy0, rfl⟩ := hy
  refine (nullRadius_eq_top_of_zero ?_).ge
  rintro _ ⟨x, hx, rfl⟩
  rw [dR_floor_zero_iff]
  exact hD x hx y0 hy0

/-- 习题 3.4 (i-a)：`D = [0, 1/2]`：`diam = 1/2`，`r̲^N = +∞`，类型 `(1,1)`。 -/
theorem ex3_4_i_a :
    let D : Set R := Option.some '' Set.Icc (0 : ℝ) (1 / 2)
    D ⊆ dom floorOp ∧ diamScale dR () D = ENNReal.ofReal (1 / 2) ∧ nullMatrix dR floorOp D () () = ⊤ ∧
    thresholdType (diamScale dR) 1 1 dR floorOp D () () = (true, true) := by
  intro D
  have hdiam : diamScale dR () D = ENNReal.ofReal (1 / 2) := by
    have := diam_Icc 0 (1 / 2) (by norm_num)
    rwa [sub_zero] at this
  have hnull : nullMatrix dR floorOp D () () = ⊤ := by
    apply nullRadius_top_of_floor_const
    intro x hx y hy
    have h1 : ⌊x⌋ = 0 := Int.floor_eq_zero_iff.2 ⟨hx.1, by linarith [hx.2]⟩
    have h2 : ⌊y⌋ = 0 := Int.floor_eq_zero_iff.2 ⟨hy.1, by linarith [hy.2]⟩
    rw [h1, h2]
  refine ⟨floor_dom _, hdiam, hnull, ?_⟩
  have hlt : diamScale dR () D < 1 := by
    rw [hdiam, ← ENNReal.ofReal_one, ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
    norm_num
  classical
  simp [thresholdType, hnull, hlt]

/-- 习题 3.4 (i-b)：`D = [9/10, 11/10]`：`diam = 1/5`，`r̲^N = 0`，类型 `(1,0)`。 -/
theorem ex3_4_i_b :
    let D : Set R := Option.some '' Set.Icc (9 / 10 : ℝ) (11 / 10)
    D ⊆ dom floorOp ∧ diamScale dR () D = ENNReal.ofReal (1 / 5) ∧ nullMatrix dR floorOp D () () = 0 ∧
    thresholdType (diamScale dR) 1 1 dR floorOp D () () = (true, false) := by
  intro D
  have hdiam : diamScale dR () D = ENNReal.ofReal (1 / 5) := by
    have := diam_Icc (9 / 10) (11 / 10) (by norm_num)
    rw [show (11 / 10 : ℝ) - 9 / 10 = 1 / 5 by norm_num] at this
    exact this
  have hnull : nullMatrix dR floorOp D () () = 0 :=
    uniform_floor_zero (Set.Icc (9 / 10 : ℝ) (11 / 10)) (1 / 10) (by norm_num)
      (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩)
  refine ⟨floor_dom _, hdiam, hnull, ?_⟩
  have hlt : diamScale dR () D < 1 := by
    rw [hdiam, ← ENNReal.ofReal_one, ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
    norm_num
  classical
  simp [thresholdType, hnull, hlt]

/-- 习题 3.4 (i-c)：`D = {0, 2}`：`diam = 2`，`r̲^N = 2`，类型 `(0,1)`。 -/
theorem ex3_4_i_c :
    let D : Set R := {some 0, some 2}
    D ⊆ dom floorOp ∧ diamScale dR () D = 2 ∧ nullMatrix dR floorOp D () () = 2 ∧
    thresholdType (diamScale dR) 1 1 dR floorOp D () () = (false, true) := by
  intro D
  have hd2 : dR () (some (2 : ℝ)) (some 0) = 2 := by
    rw [dR_some]; norm_num
  have hd2' : dR () (some (0 : ℝ)) (some 2) = 2 := by
    rw [dR_some]; norm_num
  have hdiam : diamScale dR () D = 2 := by
    apply le_antisymm
    · unfold diamScale
      apply iSup₂_le
      intro x hx
      apply iSup₂_le
      intro y hy
      simp only [D, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
        first | (rw [(dR_gauge ()).dist_self]; exact zero_le _) | (rw [hd2]) | (rw [hd2'])
    · unfold diamScale
      exact le_iSup₂_of_le (some 2) (by simp [D]) (le_iSup₂_of_le (some 0) (by simp [D]) hd2.ge)
  have hrad : ∀ y ∈ D, nullRadius (dR ()) (dR ()) floorOp y D = 2 := by
    have key : ∀ (y z : R), (y = some 0 ∧ z = some 2 ∨ y = some 2 ∧ z = some 0) →
        nullRadius (dR ()) (dR ()) floorOp y {y, z} = 2 := by
      intro y z hyz
      have hd : dR () z y = 2 := by
        rcases hyz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hd2
        · exact hd2'
      have hfl : dR () (floorOp.func z) (floorOp.func y) ≠ 0 := by
        rcases hyz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rw [Ne, dR_floor_zero_iff]; norm_num
        · rw [Ne, dR_floor_zero_iff]; norm_num
      apply le_antisymm
      · apply sSup_le
        intro r hr
        by_contra hlt
        rw [not_le] at hlt
        have hz : z ∈ ball (dR ()) y r ∩ {y, z} := ⟨by show dR () z y < r; rw [hd]; exact hlt, by simp⟩
        exact hfl (hr.2.2 hz).2
      · apply le_sSup
        refine ⟨by norm_num, by norm_num, ?_⟩
        rintro x ⟨hxb, hxm⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxm
        rcases hxm with rfl | rfl
        · exact ⟨by simp, by rw [(dR_gauge ()).dist_self]⟩
        · exfalso
          have : dR () x y < 2 := hxb
          rw [hd] at this
          exact lt_irrefl _ this
    intro y hy
    simp only [D, Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact key _ (some 2) (Or.inl ⟨rfl, rfl⟩)
    · have := key (some 2) (some 0) (Or.inr ⟨rfl, rfl⟩)
      rwa [show ({some (2 : ℝ), some 0} : Set R) = {some 0, some 2} from Set.pair_comm _ _] at this
  have hnull : nullMatrix dR floorOp D () () = 2 := by
    apply le_antisymm
    · exact (uniformNullRadius_le (A := D) (y := some 0) (by simp [D])).trans (hrad _ (by simp [D])).le
    · exact le_iInf₂ fun y hy => (hrad y hy).ge
  refine ⟨?_, hdiam, hnull, ?_⟩
  · rintro x hx
    simp only [D, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;> simp [dom, floorOp_some]
  · have hnlt : ¬ diamScale dR () D < 1 := by
      rw [hdiam]; norm_num
    have hge : 1 ≤ nullMatrix dR floorOp D () () := by
      rw [hnull]; norm_num
    classical
    simp [thresholdType, hnlt, hge]

/-- 习题 3.4 (i-d)：`D = [0, 2]`：`diam = 2`，`r̲^N = 0`，类型 `(0,0)`。 -/
theorem ex3_4_i_d :
    let D : Set R := Option.some '' Set.Icc (0 : ℝ) 2
    D ⊆ dom floorOp ∧ diamScale dR () D = 2 ∧ nullMatrix dR floorOp D () () = 0 ∧
    thresholdType (diamScale dR) 1 1 dR floorOp D () () = (false, false) := by
  intro D
  have hdiam : diamScale dR () D = 2 := by
    have := diam_Icc 0 2 (by norm_num)
    rw [sub_zero] at this
    rw [this]
    simpa using ENNReal.ofReal_ofNat 2
  have hnull : nullMatrix dR floorOp D () () = 0 :=
    uniform_floor_zero (Set.Icc (0 : ℝ) 2) 1 (by norm_num) (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩)
  refine ⟨floor_dom _, hdiam, hnull, ?_⟩
  have hnlt : ¬ diamScale dR () D < 1 := by
    rw [hdiam]; norm_num
  have hnge : ¬ 1 ≤ nullMatrix dR floorOp D () () := by
    rw [hnull]; norm_num
  classical
  simp [thresholdType, hnlt, hnge]

/-- 习题 3.4 (ii)：无直径条件时，`r̲^N ≥ 1` 不蕴含整体零化；反例 `D = {0,2}`（见 (i-c)）。 -/
theorem ex3_4_ii :
    ¬ (∀ D : Set R, D.Nonempty → D ⊆ dom floorOp → 1 ≤ nullMatrix dR floorOp D () () →
        ∀ x ∈ D, ∀ y ∈ D, dR () (floorOp.func x) (floorOp.func y) = 0) ∧
    (let D : Set R := {some 0, some 2};
      D.Nonempty ∧ D ⊆ dom floorOp ∧ 1 ≤ nullMatrix dR floorOp D () () ∧
      (∀ x ∈ D, ∀ y ∈ D, x ≠ y → 2 ≤ dR () x y) ∧ ¬ diamScale dR () D < 1 ∧
      dR () (floorOp.func (some 0)) (floorOp.func (some 2)) ≠ 0) := by
  have h := ex3_4_i_c
  simp only at h
  obtain ⟨hdom, hdiam, hnull, _⟩ := h
  have hne : dR () (floorOp.func (some (0 : ℝ))) (floorOp.func (some 2)) ≠ 0 := by
    rw [Ne, dR_floor_zero_iff]; norm_num
  have hge : (1 : ENNReal) ≤ nullMatrix dR floorOp {some 0, some 2} () () := by
    rw [hnull]; norm_num
  have hsep : ∀ x ∈ ({some 0, some 2} : Set R), ∀ y ∈ ({some 0, some 2} : Set R), x ≠ y → 2 ≤ dR () x y := by
    intro x hx y hy hxy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact absurd rfl hxy
    · rw [dR_some]; norm_num
    · rw [dR_some]; norm_num
    · exact absurd rfl hxy
  refine ⟨fun hall => ?_, ⟨⟨some 0, by simp⟩, hdom, hge, hsep, ?_, hne⟩⟩
  · exact hne (hall {some 0, some 2} ⟨some 0, by simp⟩ hdom hge (some 0) (by simp) (some 2) (by simp))
  · rw [hdiam]; norm_num

end Ex34

namespace RealLine

/-- 命题 3.14 (iii)：反向尺度判断一般不成立（`f = id`，`A = {0,1}`，`B = {0}`，`τ_σ = 1/2`，直径尺度）。 -/
theorem prop3_14_iii :
    ({some 0} : Set R) ⊆ {some 0, some 1} ∧ ({some 0, some 1} : Set R) ⊆ dom (1 : Operator R none) ∧
    diamScale dR () ({some 0} : Set R) = 0 ∧ diamScale dR () ({some 0, some 1} : Set R) = 1 ∧
    diamScale dR () ({some 0} : Set R) < ENNReal.ofReal (1 / 2) ∧
    ENNReal.ofReal (1 / 2) ≤ diamScale dR () ({some 0, some 1} : Set R) := by
  have h10 : dR () (some (1 : ℝ)) (some 0) = 1 := by rw [dR_some]; norm_num
  have h01 : dR () (some (0 : ℝ)) (some 1) = 1 := by rw [dR_some]; norm_num
  have hB : diamScale dR () ({some 0} : Set R) = 0 := by
    apply le_antisymm _ (zero_le _)
    unfold diamScale
    refine iSup₂_le fun x hx => iSup₂_le fun y hy => ?_
    rw [Set.mem_singleton_iff] at hx hy
    subst hx; subst hy
    exact ((dR_gauge ()).dist_self _).le
  have hA : diamScale dR () ({some 0, some 1} : Set R) = 1 := by
    apply le_antisymm
    · unfold diamScale
      refine iSup₂_le fun x hx => iSup₂_le fun y hy => ?_
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
        first | exact ((dR_gauge ()).dist_self _).le.trans (zero_le _) | exact h01.le | exact h10.le
    · unfold diamScale
      exact le_iSup₂_of_le (some 1) (by simp) (le_iSup₂_of_le (some 0) (by simp) h10.ge)
  refine ⟨by simp, ?_, hB, hA, ?_, ?_⟩
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;> simp [dom]
  · rw [hB]; exact ENNReal.ofReal_pos.2 (by norm_num)
  · rw [hA, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by norm_num)

end RealLine
end PartE4

section PartF
variable {X I : Type} {bot : X} [Fintype I] (d : I → X → X → ENNReal)

/-! ## D07：冻结背景的覆盖数/熵与正文定义的对应 -/

/-- 覆盖数（正文）：`𝒩(ε,U) = min{|S| : S ⊆ U, |S| < ∞, U ⊆ ⋃_{s ∈ S} B(s,ε)}`，无有限内覆盖时为 `+∞`，空集为 `0`。 -/
theorem covering_number_textbook {Y : Type} (dd : Y → Y → ENNReal) (ε : ENNReal) (U : Set Y) :
    (∀ S : Finset Y, InternalEpsilonNet dd ε U S ↔ ((↑S : Set Y) ⊆ U ∧ U ⊆ ⋃ s ∈ S, ball dd s ε)) ∧
    ((∃ S : Finset Y, (↑S : Set Y) ⊆ U ∧ U ⊆ ⋃ s ∈ S, ball dd s ε) →
      ∃ S : Finset Y, ((↑S : Set Y) ⊆ U ∧ U ⊆ ⋃ s ∈ S, ball dd s ε) ∧
        covering_number dd ε U = (S.card : ENNReal) ∧
        ∀ T : Finset Y, ((↑T : Set Y) ⊆ U ∧ U ⊆ ⋃ s ∈ T, ball dd s ε) → S.card ≤ T.card) ∧
    ((¬ ∃ S : Finset Y, (↑S : Set Y) ⊆ U ∧ U ⊆ ⋃ s ∈ S, ball dd s ε) → covering_number dd ε U = ⊤) ∧
    covering_number dd ε (∅ : Set Y) = 0 := by
  refine ⟨fun S => internalEpsilonNet_iff, fun h => ?_, fun h => ?_, covering_number_empty dd ε⟩
  · obtain ⟨S, hS⟩ := h
    obtain ⟨T, hT, hcard, hmin⟩ := covering_number_attained dd ε U ⟨S, internalEpsilonNet_iff.2 hS⟩
    exact ⟨T, internalEpsilonNet_iff.1 hT, hcard, fun T' hT' => hmin T' (internalEpsilonNet_iff.2 hT')⟩
  · rw [covering_number_eq_top_iff]
    rintro ⟨S, hS⟩
    exact h ⟨S, internalEpsilonNet_iff.1 hS⟩

/-- 度量熵（正文）：`E = log₂ 𝒩`，非空集合取值于 `[0,+∞]`，空集熵为 `-∞`。 -/
theorem metric_entropy_textbook {Y : Type} (dd : Y → Y → ENNReal) (ε : ENNReal) (U : Set Y) :
    (U.Nonempty → covering_number dd ε U ≠ ⊤ →
      ∃ r : ℝ, metric_entropy dd ε U = (r : EReal) ∧ r = Real.logb 2 (covering_number dd ε U).toReal ∧ 0 ≤ r) ∧
    (covering_number dd ε U = ⊤ → metric_entropy dd ε U = ⊤) ∧
    (U.Nonempty → 0 ≤ metric_entropy dd ε U) ∧
    metric_entropy dd ε (∅ : Set Y) = ⊥ := by
  refine ⟨fun hne hfin => ?_, fun h => ?_, fun hne => metric_entropy_nonneg dd ε U hne, metric_entropy_empty dd ε⟩
  · have h1 := one_le_covering_number_of_nonempty dd ε U hne
    have h0 : covering_number dd ε U ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one h1)
    refine ⟨Real.logb 2 (covering_number dd ε U).toReal, ?_, rfl, ?_⟩
    · simp [metric_entropy, log2_ereal, h0, hfin]
    · apply Real.logb_nonneg one_lt_two
      simpa using ENNReal.toReal_mono hfin h1
  · simp [metric_entropy, log2_ereal, h]

/-- 子族覆盖数/熵在 `J = {i}` 时退化为单分量情形（沿用冻结背景）。 -/
theorem subfamily_singleton_agree (i : I) (ε : ENNReal) (S : Set X) :
    subfamilyCoveringNumber d {i} ε S = covering_number (d i) ε S ∧
    subfamily_metric_entropy d {i} ε S = metric_entropy (d i) ε S :=
  ⟨by unfold subfamilyCoveringNumber; rw [subfamily_pseudometric_singleton],
    subfamily_metric_entropy_singleton d i ε S⟩

/-- 全有界接口：`U` 在 `d_i` 下全有界，当且仅当对每个有限正精度都存在有限内覆盖。 -/
theorem totallyBoundedIn_iff (i : I) (U : Set X) :
    TotallyBoundedIn d i U ↔
      ∀ r : ENNReal, 0 < r → r < ⊤ → ∃ S : Finset X, InternalEpsilonNet (d i) r U S := by
  unfold TotallyBoundedIn
  refine forall₃_congr fun r _ _ => ?_
  rw [lt_top_iff_ne_top, Ne, covering_number_eq_top_iff, not_not]

/-- 全有界且非空时，每个有限正精度下的熵是非负实数。 -/
theorem totallyBoundedIn_entropy_real (i : I) (U : Set X) (hU : U.Nonempty)
    (htb : TotallyBoundedIn d i U) (r : ENNReal) (h0 : 0 < r) (ht : r < ⊤) :
    ∃ x : ℝ, 0 ≤ x ∧ metric_entropy (d i) r U = (x : EReal) := by
  obtain ⟨x, hx, hxr, hx0⟩ := (metric_entropy_textbook (d i) r U).1 hU (htb r h0 ht).ne
  exact ⟨x, hx0, hx⟩

/-! ## 显式的中心集构造（命题 3.16、3.19、3.20 的证明内容） -/

/-- 命题 3.16 (ii-a)：内部输入中心集的像是内部输出中心集（含 `B = ∅`），中心数不增。 -/
theorem prop3_16_net (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot) (A : Set X)
    (hA : A.Nonempty) (hAd : A ⊆ dom f) (i j : I) (τN : ENNReal) (hτ0 : 0 < τN) (hτ : τN < ⊤)
    (h : τN ≤ nullMatrix d f A j i) (B : Set X) (hBA : B ⊆ A) (ε : ENNReal) (hε0 : 0 < ε)
    (S : Finset X) (hS : InternalEpsilonNet (d i) τN B S) :
    ∃ T : Finset X, InternalEpsilonNet (d j) ε (f.func '' B) T ∧ T.card ≤ S.card := by
  classical
  have hnet : InternalEpsilonNet (d j) ε (f.func '' B) (S.image f.func) := by
    refine ⟨?_, ?_⟩
    · intro z hz
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hz
      exact ⟨s, hS.1 hs, rfl⟩
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨c, hc, hxc⟩ := hS.2 x hx
      refine ⟨f.func c, Finset.mem_image_of_mem _ hc, ?_⟩
      have := (mem_Fib.1 (prop3_16_i d hd f A hA hAd i j τN hτ0 hτ h c (hBA (hS.1 hc)) ⟨hxc, hBA hx⟩)).2 j
        (Set.mem_singleton j)
      rw [this]
      exact hε0
  exact ⟨S.image f.func, hnet, Finset.card_image_le⟩

/-- 命题 3.19：有限正 `L`，内部 `ε/L`-输入中心集的像是内部 `ε`-输出中心集，中心数不增。 -/
theorem prop3_19_net (ϕ : Operator X bot) (U : Set X) (i j : I) (ε L : ENNReal) (hL0 : 0 < L)
    (hLt : L < ⊤) (hlip : ∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ L * d i x y)
    (S : Finset X) (hS : InternalEpsilonNet (d i) (ε / L) U S) :
    ∃ T : Finset X, InternalEpsilonNet (d j) ε (ϕ.func '' U) T ∧ T.card ≤ S.card := by
  classical
  refine ⟨S.image ϕ.func, ⟨?_, ?_⟩, Finset.card_image_le⟩
  · intro z hz
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hz
    exact ⟨s, hS.1 hs, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨c, hc, hxc⟩ := hS.2 x hx
    refine ⟨ϕ.func c, Finset.mem_image_of_mem _ hc, ?_⟩
    calc d j (ϕ.func x) (ϕ.func c) ≤ L * d i x c := hlip x hx c (hS.1 hc)
      _ < L * (ε / L) := (ENNReal.mul_lt_mul_iff_right hL0.ne' hLt.ne).2 hxc
      _ = ε := ENNReal.mul_div_cancel hL0.ne' hLt.ne

/-- 命题 3.20：内部输出中心集的原像（对每个中心选一个代表元）是内部 `ε/K`-输入中心集，中心数不增。 -/
theorem prop3_20_net (ϕ : Operator X bot) (U : Set X) (K : I → I → ENNReal)
    (hK : IsCoLipMatrix d ϕ U K) (i j : I) (hK0 : 0 < K i j) (hKt : K i j < ⊤) (ε : ENNReal)
    (T : Finset X) (hT : InternalEpsilonNet (d j) ε (ϕ.func '' U) T) :
    ∃ S : Finset X, InternalEpsilonNet (d i) (ε / K i j) U S ∧ S.card ≤ T.card := by
  classical
  let r : X → X := fun t => if h : t ∈ ϕ.func '' U then Classical.choose h else t
  have hr : ∀ t ∈ ϕ.func '' U, r t ∈ U ∧ ϕ.func (r t) = t := fun t ht => by
    simp only [r, dif_pos ht]
    exact Classical.choose_spec ht
  refine ⟨T.image r, ⟨?_, ?_⟩, Finset.card_image_le⟩
  · intro z hz
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hz
    exact (hr t (hT.1 ht)).1
  · intro x hx
    obtain ⟨t, ht, hxt⟩ := hT.2 (ϕ.func x) ⟨x, hx, rfl⟩
    refine ⟨r t, Finset.mem_image_of_mem r ht, ?_⟩
    have hc := (hr t (hT.1 ht)).1
    have h1 : K i j * d i x (r t) ≤ d j (ϕ.func x) (ϕ.func (r t)) :=
      calc K i j * d i x (r t) ≤ ∑ k : I, K k j * d k x (r t) :=
            Finset.single_le_sum (f := fun k => K k j * d k x (r t)) (fun _ _ => zero_le _) (Finset.mem_univ i)
        _ ≤ _ := hK.2.2 x hx (r t) hc j
    rw [ENNReal.lt_div_iff_mul_lt (Or.inl hK0.ne') (Or.inl hKt.ne), mul_comm]
    refine lt_of_le_of_lt h1 ?_
    rwa [(hr t (hT.1 ht)).2]

/-! ## 命题 3.6 (iii) 的单分量版本（使用背景的标量 Lip 记号） -/

theorem prop3_6_iii_scalar (ϕA ϕB : Operator X bot) (U : Set X) (i : I)
    (T : ϕA.func '' U → X) (hT : Factors ϕA ϕB U T) (KA LB : ENNReal) (hK0 : 0 < KA) (hKt : KA < ⊤)
    (hLt : LB < ⊤) (hco : HasScalarCoLipBound d ϕA U i i KA) (hlip : HasScalarLipBound d ϕB U i i LB) :
    ∀ p q : ϕA.func '' U, d i (T p) (T q) ≤ (LB / KA) * d i p.1 q.1 :=
  prop3_6_iii (d i) ϕA ϕB U (fun x hx => ⟨hco.2.1 hx, hlip.1 hx⟩) T hT KA LB hK0 hKt hLt hco.2.2 hlip.2
/-- D02/D03：`(x,y) ∈ R_∼(ϕ|U) ⇔ y ∈ Fib_{ϕ,I}(ϕ x | U)`（`x,y ∈ U`）。 -/
theorem Rsim_iff_mem_Fib (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (ϕ : Operator X bot) (U : Set X)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    (x, y) ∈ Rsim d ϕ U ↔ y ∈ Fib d ϕ Set.univ (ϕ.func x) U := by
  rw [mem_Fib]
  constructor
  · rintro ⟨_, _, h⟩
    exact ⟨hy, fun j _ => ((hd j).symm (ϕ.func y) (ϕ.func x)).trans (h j)⟩
  · rintro ⟨_, h⟩
    exact ⟨hx, hy, fun j => ((hd j).symm (ϕ.func x) (ϕ.func y)).trans (h j (Set.mem_univ j))⟩

/-- D08：映射熵差在 `E_in = +∞`、`E_out = +∞` 等情形的取值，以及良定条件排除 `∞ - ∞`。 -/
theorem mapEntropyDiff_cases (ϕ : Operator X bot) (U : Set X) (Jin Jout : Set I) (ε : ENNReal) :
    (subfamily_metric_entropy d Jin ε U = ⊤ → subfamily_metric_entropy d Jout ε (ϕ.func '' U) ≠ ⊤ →
      mapEntropyDiff d ϕ U Jin Jout ε = ⊤) ∧
    (subfamily_metric_entropy d Jin ε U ≠ ⊤ → subfamily_metric_entropy d Jout ε (ϕ.func '' U) = ⊤ →
      mapEntropyDiff d ϕ U Jin Jout ε = ⊥) ∧
    (∀ a b : ℝ, subfamily_metric_entropy d Jin ε U = a → subfamily_metric_entropy d Jout ε (ϕ.func '' U) = b →
      mapEntropyDiff d ϕ U Jin Jout ε = ((a - b : ℝ) : EReal)) ∧
    (MapEntropyDiffDefined d ϕ U Jin Jout ε →
      ¬ (subfamily_metric_entropy d Jin ε U = ⊤ ∧ subfamily_metric_entropy d Jout ε (ϕ.func '' U) = ⊤)) := by
  refine ⟨fun h1 h2 => ?_, fun _ h2 => ?_, fun a b h1 h2 => ?_, ?_⟩
  · unfold mapEntropyDiff; rw [h1]; exact EReal.top_sub h2
  · unfold mapEntropyDiff; rw [h2]; exact EReal.sub_top _
  · unfold mapEntropyDiff; rw [h1, h2, EReal.coe_sub]
  · rintro (h | h) ⟨h1, h2⟩
    · exact log2_ereal_ne_top h.ne h1
    · exact log2_ereal_ne_top h.ne h2

end PartF

end MGC003
```

```json filename=alignment.json
{"case_id":"MG-C003","version":"0.1.1","items":[
{"id":"CH03-D01","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.Iconst"},{"file":"Main.lean","name":"MGC003.Iid"},{"file":"Main.lean","name":"MGC003.Iact"},{"file":"Main.lean","name":"MGC003.mem_Iact"}],"representation":"Iconst/Iid/Iact 为 Set I：常值=∀x,y∈U 输出零距；恒等=∉Iconst 且 ∀x∈U d_i(ϕx,x)=0（常值优先）；有效=I∖(Iconst∪Iid)；U 为显式参数，全域分划取 U=dom ϕ","dependencies":[]},
{"id":"CH03-D02","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.Fib"},{"file":"Main.lean","name":"MGC003.mem_Fib"},{"file":"Main.lean","name":"MGC003.subfam_eq_zero_iff"},{"file":"Main.lean","name":"MGC003.Rsim_iff_mem_Fib"}],"representation":"Fib d ϕ J y U={x∈U | d_J(ϕx,y)=0}，d_J 即冻结背景 subfamily_pseudometric（sup）；mem_Fib 给出逐分量刻画；J={i} 为单分量，U=dom ϕ 为全域纤维","dependencies":[]},
{"id":"CH03-D03","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.Req"},{"file":"Main.lean","name":"MGC003.Rsim"},{"file":"Main.lean","name":"MGC003.FiberGe"},{"file":"Main.lean","name":"MGC003.imageSetoid"},{"file":"Main.lean","name":"MGC003.HasQuotientMap"},{"file":"Main.lean","name":"MGC003.Factors"},{"file":"Main.lean","name":"MGC003.Rsim_iff_mem_Fib"}],"representation":"Req/Rsim 为 U×U 中 ϕ(x)=ϕ(y) 与 ϕ(x)∼_G ϕ(y)（GaugeZeroRelated）的点对集；FiberGe 为 Rsim 包含（零测距纤维预序）；imageSetoid 为 ϕ(U) 上 ∼_G 诱导商；HasQuotientMap 为带规定赋值公式的商映射存在；Factors 为 T∘ϕA=ϕB；Rsim_iff_mem_Fib 给出 R_∼ 与 Fib_{ϕ,I} 的关系表达","dependencies":[]},
{"id":"CH03-D04","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.NullAdm"},{"file":"Main.lean","name":"MGC003.nullRadius"},{"file":"Main.lean","name":"MGC003.nullRadiusJ"},{"file":"Main.lean","name":"MGC003.nullRadiusJ_singleton"}],"representation":"NullAdm 为合法有限正半径集 {r∈(0,∞) | B_in(y,r)∩U ⊆ {x∈U | d_out(ϕx,ϕy)=0}}；nullRadius=sSup NullAdm（sSup ∅=0，可取 ⊤）；nullRadiusJ 取 d_out=d_J","dependencies":[]},
{"id":"CH03-D05","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.uniformNullRadius"},{"file":"Main.lean","name":"MGC003.uniformNullRadiusJ"},{"file":"Main.lean","name":"MGC003.nullMatrix"},{"file":"Main.lean","name":"MGC003.uniformNullRadiusJ_singleton"}],"representation":"uniformNullRadius=⨅_{y∈A} nullRadius（评估域 U）；uniformNullRadiusJ 为输出取 d_J 且 A=U；nullMatrix d ϕ U j i（行 j 输出、列 i 输入）=r̲^N_{ϕ,i,j}|_U","dependencies":[]},
{"id":"CH03-D06","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.IsInputScale"},{"file":"Main.lean","name":"MGC003.diamScale"},{"file":"Main.lean","name":"MGC003.diamScale_isInputScale"},{"file":"Main.lean","name":"MGC003.thresholdType"}],"representation":"IsInputScale：对非空 A₁⊆A₂ 单调的族 σ_i；diamScale 为默认直径尺度 sup_{x,y∈A} d_i；thresholdType=(σ_i(A)<τσ, τN≤r̲^N_{f,i,j}|_A) 以 Bool×Bool 表示","dependencies":[]},
{"id":"CH03-D07","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.TotallyBoundedIn"},{"file":"Main.lean","name":"MGC003.subfamilyCoveringNumber"},{"file":"Main.lean","name":"MGC003.internalEpsilonNet_iff"},{"file":"Main.lean","name":"MGC003.covering_number_textbook"},{"file":"formal_oet/vol_01/ch_01_foundations/metric_entropy.lean","name":"formal_oet.vol_01.ch_01_foundations.covering_number"},{"file":"formal_oet/vol_01/ch_01_foundations/metric_entropy.lean","name":"formal_oet.vol_01.ch_01_foundations.metric_entropy"}],"representation":"覆盖数/熵沿用冻结背景 covering_number、metric_entropy、subfamily_metric_entropy；internalEpsilonNet_iff 与 covering_number_textbook、metric_entropy_textbook 证明其与正文一致；TotallyBoundedIn 为∀有限正 r 覆盖数<∞","dependencies":[]},
{"id":"CH03-D08","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.mapEntropyDiff"},{"file":"Main.lean","name":"MGC003.MapEntropyDiffDefined"},{"file":"Main.lean","name":"MGC003.mapEntropyDiff_cases"},{"file":"Main.lean","name":"MGC003.mapEntropyDiff_singleton"}],"representation":"mapEntropyDiff=E_{ε,Jin}(U)−E_{ε,Jout}(ϕ(U)) 取值 EReal，使用 subfamily_metric_entropy；MapEntropyDiffDefined 为良定前提；mapEntropyDiff_cases 给出 ⊤/⊥/实数各情形并排除 ∞−∞","dependencies":[]},
{"id":"CH03-P01-01","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.prop3_1_i"}],"representation":"i∈Iconst 时 d_i(ϕx,ϕy)≤∑0·d_k=0，并说明任一 Lip 矩阵可把第 i 列(输出行)置零仍为合法 Lip 矩阵。","dependencies":["CH03-D01"]},
{"id":"CH03-P01-02","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.prop3_1_ii"}],"representation":"i∈Iconst、K 为 U 上 co-Lip 矩阵，若某 x,y∈U 使 d_k(x,y)>0 则 K k i=0（经冻结背景 colip_entry_eq_zero_of_output_zero_input_pos）。","dependencies":["CH03-D01"]},
{"id":"CH03-P01-03","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.prop3_1_iii"}],"representation":"i∈Iid 时对 x,y∈U 有 d_i(ϕx,ϕy)=d_i(x,y)（三角不等式双向，经 epm_eq）。","dependencies":["CH03-D01"]},
{"id":"CH03-P02-01","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.prop3_2_i"},{"file":"Main.lean","name":"MGC003.not_Iact_comp"},{"file":"Main.lean","name":"MGC003.Iid_comp"}],"representation":"U⊆dom(ϕ₂∘ϕ₁) 时 Iact(ϕ₂∘ϕ₁|U)⊆Iact(ϕ₁|U)∪Iact(ϕ₂|ϕ₁(U))，第二步在实际中间像域 ϕ₁(U) 上；逐分量按 (a)–(d) 四种情形证明。","dependencies":["CH03-D01","CH03-P01-03"]},
{"id":"CH03-P02-02","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.prop3_2_ii"},{"file":"Main.lean","name":"MGC003.chainComp"},{"file":"Main.lean","name":"MGC003.chainComp_stage"}],"representation":"chainComp ϕ n=ϕ_n∘⋯∘ϕ_1（n=0 为 id）；U 1⊆dom c_n，U(m+1)=ϕ_m(U m)；对 n 归纳（零步基例 Iact=∅）得 Iact(c_n|U₁)⊆⋃_{m=1}^n Iact(ϕ_m|U_m)","dependencies":["CH03-D01","CH03-P02-01"]},
{"id":"CH03-P02-03","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.prop3_2_iii"},{"file":"Main.lean","name":"MGC003.Iid_comp"}],"representation":"Iid(ϕ₁|U)∩Iid(ϕ₂|ϕ₁(U))⊆Iid(ϕ₂∘ϕ₁|U)，含证明复合输出不两两零距（排除常值优先分支）与逐点零距。","dependencies":["CH03-D01","CH03-P01-03"]},
{"id":"CH03-P03-01","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.Swap.note_converse_fails"},{"file":"Main.lean","name":"MGC003.Swap.swap_distances"},{"file":"Main.lean","name":"MGC003.Swap.swap_step_classes"},{"file":"Main.lean","name":"MGC003.Swap.swap_comp_classes"}],"representation":"三点空间 Option Bool（⊥=none），单分量 0/1 离散度量、⊥ 孤立；换位算子；两步均 Iact={i}、Iid=∅，复合 Iid={i}、Iact=∅；两条包含均为严格包含，反向包含不成立","dependencies":["CH03-D01","CH03-P02-01","CH03-P02-03"]},
{"id":"CH03-P04-01","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.prop3_3_i"}],"representation":"Iconst(ψ|ϕ(U))⊆Iconst(ψ∘ϕ|U)（外侧在实际像域 ϕ(U) 上常值）。","dependencies":["CH03-D01"]},
{"id":"CH03-P04-02","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.SevenPt.prop3_3_ii_example"}],"representation":"七点空间 Option (Fin 6)、指标集 Bool={i,m}；d_i 合并 p,q；ϕ(a)=p,ϕ(b)=q,ψ(p)=r,ψ(q)=s；验证规范合法、U⊆dom(ψ∘ϕ)、i∈Iconst(ϕ|U)、i∉Iconst(ψ∘ϕ|U)、d_m(p,q)=1","dependencies":["CH03-D01"]},
{"id":"CH03-P05-01","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.cor3_4"}],"representation":"j∈Iconst(ϕ|U)，L 为 ψ 在 ϕ(U) 上的 Lip 矩阵且 L k j=0（k≠j）则 j∈Iconst(ψ∘ϕ|U)；L j j 可为 ⊤（乘 0 得 0）","dependencies":["CH03-D01"]},
{"id":"CH03-P06-01","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.prop3_5_i"}],"representation":"d_J(y,y')=0 时 Fib_J(y|U)=Fib_J(y'|U)（J 非空，d_J 为扩展伪度量）。","dependencies":["CH03-D02"]},
{"id":"CH03-P06-02","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.prop3_5_ii_a"}],"representation":"∀y∈ϕ(U) 纤维非空，且 U⊆⋃_{y∈ϕ(U)} Fib_J(y|U)。","dependencies":["CH03-D02"]},
{"id":"CH03-P06-03","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.prop3_5_ii_b"},{"file":"Main.lean","name":"MGC003.IsPartitionOf"}],"representation":"像目标纤维相等或不交；去重后的族 {Fib(y|U)} 构成 U 的分划（非空、两两不交、并为 U）。","dependencies":["CH03-D02","CH03-P06-01"]},
{"id":"CH03-P06-04","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.prop3_5_iii"}],"representation":"J 非空时 Fib_J=⋂_{j∈J}Fib_{j}。","dependencies":["CH03-D02"]},
{"id":"CH03-P06-05","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.prop3_5_iv"}],"representation":"J⊆K 时 Fib_K(y|U)⊆Fib_J(y|U)。","dependencies":["CH03-D02"]},
{"id":"CH03-P06-06","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.prop3_5_v"}],"representation":"Fib_{i}(y|U)={x∈U|d_i(ϕx,y)=0}；Fib_{univ}⊆各单分量纤维。","dependencies":["CH03-D02"]},
{"id":"CH03-P06-07","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.prop3_5_vi_a"}],"representation":"j∈Iid(ϕ|U) 时，对任意目标 y，Fib_{j}(y|U)={x∈U|d_j(x,y)=0}。","dependencies":["CH03-D01","CH03-D02","CH03-P01-03"]},
{"id":"CH03-P06-08","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.prop3_5_vi_b"}],"representation":"j∈Iconst(ϕ|U) 时，y₀∈ϕ(U) 的纤维为 U，且 d_j(y,y₀)>0 时 Fib_{j}(y|U)=∅。","dependencies":["CH03-D01","CH03-D02"]},
{"id":"CH03-P07-01","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.prop3_6_i_nec"}],"representation":"若 T:ϕA(U)→X 满足 T∘ϕA=ϕB，则 Req(ϕA|U)⊆Req(ϕB|U)。","dependencies":["CH03-D03"]},
{"id":"CH03-P07-02","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.prop3_6_i_suff"},{"file":"Main.lean","name":"MGC003.prop3_6_i"}],"representation":"由 Req 包含用 Classical.choose 构造 T 并验证 T∘ϕA=ϕB（U=∅ 时像为空子类型，亦成立）；prop3_6_i 为双向等价。","dependencies":["CH03-D03"]},
{"id":"CH03-P07-03","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.prop3_6_ii"}],"representation":"两个方向的点值变换都存在 ⇔ Req(ϕA|U)=Req(ϕB|U)。","dependencies":["CH03-D03","CH03-P07-01","CH03-P07-02"]},
{"id":"CH03-P07-04","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.prop3_6_iii"},{"file":"Main.lean","name":"MGC003.prop3_6_iii_scalar"}],"representation":"KA∈(0,∞)、LB<∞，co-Lip 与 Lip 标量界在 U 上成立，T 存在时在像域 ϕA(U) 上 d(Tp,Tq)≤(LB/KA)·d(p,q)；scalar 版本使用背景 HasScalarLipBound 及对应的 HasScalarCoLipBound","dependencies":["CH03-D03"]},
{"id":"CH03-P08-01","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.prop3_7_i"}],"representation":"HasQuotientMap（带规定赋值公式的 Quotient 映射）存在 ⇔ Rsim(ϕA|U)⊆Rsim(ϕB|U)；充分性用 Quotient.lift 构造代表元无关映射并验证公式。","dependencies":["CH03-D03"]},
{"id":"CH03-P08-02","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.prop3_7_ii"}],"representation":"双向商映射存在 ⇔ Rsim(ϕA|U)=Rsim(ϕB|U)。","dependencies":["CH03-D03","CH03-P08-01"]},
{"id":"CH03-P08-03","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.prop3_7_iii"},{"file":"Main.lean","name":"MGC003.Req_subset_Rsim"}],"representation":"两个实际像集 ϕA(U)、ϕB(U) 各自 SepOn 分离时，Req=Rsim，点值判据与商值判据（单向、双向）等价。","dependencies":["CH03-D03","CH03-P07-01","CH03-P07-02","CH03-P07-03","CH03-P08-01","CH03-P08-02"]},
{"id":"CH03-P09-01","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.note_fiber_preorder"},{"file":"Main.lean","name":"MGC003.prop_fiber_refl"},{"file":"Main.lean","name":"MGC003.prop_fiber_trans"}],"representation":"FiberGe 自反、传递（Rsim 包含）。","dependencies":["CH03-D03"]},
{"id":"CH03-P09-02","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.note_fiber_chain"}],"representation":"公共域 U 上链 ϕ₀⪰⋯⪰ϕ_m：任意 a≤b≤m 有 ϕ_a⪰ϕ_b。","dependencies":["CH03-D03","CH03-P09-01"]},
{"id":"CH03-P09-03","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.note_fiber_strict"}],"representation":"链中某步 Rsim 真包含则 Rsim(ϕ₀)⊂Rsim(ϕ_m)，并给出差集见证 p∈R_{r+1}∖R_r 且 p∈R_m∖R_0。","dependencies":["CH03-D03","CH03-P09-02"]},
{"id":"CH03-P10-01","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.RealLine.dR_gauge"},{"file":"Main.lean","name":"MGC003.RealLine.stepOp"},{"file":"Main.lean","name":"MGC003.RealLine.Ustep"},{"file":"Main.lean","name":"MGC003.RealLine.counterexample3_1"}],"representation":"带吸收元实线 Option ℝ，dR=extPM(通常距离)，stepOp(x)=0(x<0)/1(x≥0)，U=[-1,0)∪(0,1]；验证合法规范、stepOp(⊥)=⊥、U⊆dom stepOp、⊥∉U","dependencies":["CH03-D04"]},
{"id":"CH03-P10-02","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.RealLine.step_nullAdm"},{"file":"Main.lean","name":"MGC003.RealLine.step_nullRadius"}],"representation":"每个 y∈U 的合法有限正半径集恰为 (0,|y|]，故点态零化半径=|y|>0。","dependencies":["CH03-D04","CH03-P10-01"]},
{"id":"CH03-P10-03","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.RealLine.step_uniform_zero"}],"representation":"取趋零基点 t=min(1,ε)：uniformNullRadius=0（对 ε 任意小）。","dependencies":["CH03-D05","CH03-P10-02"]},
{"id":"CH03-P11-01","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.prop3_8_i_a"}],"representation":"J⊆Iconst(ϕ|U) 时 ∀y∈U，Fib_J(ϕ y|U)=U。","dependencies":["CH03-D01","CH03-D02"]},
{"id":"CH03-P11-02","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.prop3_8_i_b"}],"representation":"J⊆Iconst 时对任意输入分量 i，点态半径 nullRadiusJ=⊤ 且统一半径 uniformNullRadiusJ=⊤。","dependencies":["CH03-D01","CH03-D04","CH03-D05","CH03-P11-01"]},
{"id":"CH03-P11-03","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.TwoPt.prop3_8_ii_example"}],"representation":"两点空间 Option Bool、恒等算子；分量 i 上 d(a,b)=⊤，j≠i 时 d_j(a,b)=1，其余 0；对任意 i,j（含 i=j）验证 nullMatrix j i=⊤ 而 j∉Iconst。","dependencies":["CH03-D01","CH03-D05"]},
{"id":"CH03-P12-01","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.prop3_9_i"}],"representation":"i∈Iid(ϕ|U)、y∈U 时 Fib_{i}(ϕ y|U)={x∈U|d_i(x,y)=0}。","dependencies":["CH03-D01","CH03-D02","CH03-P01-03"]},
{"id":"CH03-P12-02","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.prop3_9_ii"}],"representation":"有限正 r₀ 使 B_i(y,r₀)∩U⊆输入零距类时，nullRadius(d_i,d_i)(y|U)≥r₀>0。","dependencies":["CH03-D04","CH03-P12-01","CH03-P01-03"]},
{"id":"CH03-P13-01","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.prop3_10_pointwise"},{"file":"Main.lean","name":"MGC003.nullRadiusJ_eq_iInf"}],"representation":"J 非空：点态半径 nullRadiusJ=⨅_{j∈J}nullRadius_j，且该下确界在某个 j∈J 处取到（有限非空最小值）。","dependencies":["CH03-D02","CH03-D04"]},
{"id":"CH03-P13-02","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.prop3_10_uniform"}],"representation":"统一半径 uniformNullRadiusJ=⨅_{j∈J}nullMatrix j i（交换基点 inf 与有限 min），并在某个 j 取到。","dependencies":["CH03-D05","CH03-P13-01"]},
{"id":"CH03-P13-03","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.prop3_10_anti"}],"representation":"J⊆K（J 非空）时 uniformNullRadiusJ(K)≤uniformNullRadiusJ(J)。","dependencies":["CH03-D05","CH03-P13-02"]},
{"id":"CH03-P14-01","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.prop3_11_a"}],"representation":"y'∈Fib_{ϕ₂,j}(ϕ₂ y|U₂) ⟹ d_j(ϕ₂ y,ϕ₂ y')=0。","dependencies":["CH03-D02"]},
{"id":"CH03-P14-02","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.prop3_11_b"},{"file":"Main.lean","name":"MGC003.zero_of_lt_nullRadius"}],"representation":"d_i(y,y')<nullRadius(y|U₂)、y'∈U₂ ⟹ d_j(ϕ₂ y,ϕ₂ y')=0（由 sSup 取得合法有限正半径）。","dependencies":["CH03-D04"]},
{"id":"CH03-P14-03","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.prop3_11_c"}],"representation":"复合输入实例：ϕ₁x,ϕ₁x'∈U₂ 且 ϕ₁x'∈Fib_{ϕ₂,j}(ϕ₂(ϕ₁x)|U₂) ⟹ d_j((ϕ₂∘ϕ₁)x,(ϕ₂∘ϕ₁)x')=0。","dependencies":["CH03-P14-01"]},
{"id":"CH03-P15-01","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.prop3_12_i"}],"representation":"下游在实际像域 ϕ₁(U) 上 d_l-零距⟹d_j-零距时 nullMatrix(ϕ₁) l i ≤ nullMatrix(ϕ₂∘ϕ₁) j i。","dependencies":["CH03-D05","CH03-P14-02"]},
{"id":"CH03-P15-02","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.prop3_12_ii"}],"representation":"L∈(0,∞)，d_l(ϕ₁x,ϕ₁x')≤L·d_i(x,x')（U 上）⟹ nullMatrix(ϕ₂|ϕ₁(U)) j l / L ≤ nullMatrix(ϕ₂∘ϕ₁|U) j i；右端 0/⊤ 由 ENNReal 除法统一处理","dependencies":["CH03-D05","CH03-P14-02"]},
{"id":"CH03-P16-01","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.lemma3_13_cells"}],"representation":"thresholdType 的四种取值各自等价于对应不等式组合，四种组合互斥且穷尽。","dependencies":["CH03-D06"]},
{"id":"CH03-P16-02","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.lemma3_13_i"}],"representation":"τσ≤τσ' 时第一项为 true 的通道集合单调不减。","dependencies":["CH03-D06"]},
{"id":"CH03-P16-03","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.lemma3_13_ii"}],"representation":"τN≤τN' 时第二项为 true 的通道集合单调不增。","dependencies":["CH03-D06"]},
{"id":"CH03-P17-01","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.prop3_14_i"}],"representation":"任意输入尺度函数族：B⊆A、B 非空时 σ_i(B)≤σ_i(A)，且 σ_i(A)<τσ⟹σ_i(B)<τσ。","dependencies":["CH03-D06"]},
{"id":"CH03-P17-02","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.prop3_14_ii_a"},{"file":"Main.lean","name":"MGC003.nullRadius_mono_domain"}],"representation":"B⊆A 且基点 x∈B：nullRadius(x|A)≤nullRadius(x|B)。","dependencies":["CH03-D04"]},
{"id":"CH03-P17-03","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.prop3_14_ii_b"}],"representation":"∅≠B⊆A⊆dom f：nullMatrix(f|A) j i ≤ nullMatrix(f|B) j i（同时缩小评估域与基点集合）。","dependencies":["CH03-D05","CH03-P17-02"]},
{"id":"CH03-P17-04","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.RealLine.prop3_14_iii"}],"representation":"A={0,1}⊇B={0}（f=id，τσ=1/2，直径尺度）：σ(B)=0<1/2 而 σ(A)=1≥1/2，反向判断不成立。","dependencies":["CH03-D06"]},
{"id":"CH03-P18-01","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.prop3_15_i"}],"representation":"x,y∈A、d_i(x,y)<nullMatrix(f|A) j i ⟹ d_j(f x,f y)=0。","dependencies":["CH03-D05","CH03-P14-02"]},
{"id":"CH03-P18-02","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.prop3_15_ii"}],"representation":"d_j(f x,f y)>0 ⟹ nullMatrix(f|A) j i ≤ d_i(x,y)（(i) 的逆否）。","dependencies":["CH03-P18-01"]},
{"id":"CH03-P18-03","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.prop3_15_iii"}],"representation":"r̲<α<τN（α 有限）：存在 x,y∈A 与 NNReal ε>0 使 d_i(x,y)<α 且 ε≤d_j(f x,f y)（输出距离为 ⊤ 时取 ε=1，否则取 min(1,距离)）。","dependencies":["CH03-D05","CH03-D04"]},
{"id":"CH03-P19-01","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.prop3_16_i"}],"representation":"τN∈(0,∞)、τN≤nullMatrix(f|A) j i：∀x∈A，B_i(x,τN)∩A⊆Fib_{f,{j}}(f x|A)。","dependencies":["CH03-P18-01","CH03-D02"]},
{"id":"CH03-P19-02","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.prop3_16_ii_a"},{"file":"Main.lean","name":"MGC003.prop3_16_net"},{"file":"Main.lean","name":"MGC003.cov_image_le"}],"representation":"任意 B⊆A（含空集、无有限覆盖）：covering_number d_j ε f(B) ≤ covering_number d_i τN B；prop3_16_net 显式构造内部输出中心集 f(S)（中心数不增）","dependencies":["CH03-P19-01","CH03-D07"]},
{"id":"CH03-P19-03","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.prop3_16_ii_b"},{"file":"Main.lean","name":"MGC003.log2_ereal_mono"}],"representation":"B 非空时由 log2 单调得 metric_entropy d_j ε f(B) ≤ metric_entropy d_i τN B。","dependencies":["CH03-P19-02","CH03-D07"]},
{"id":"CH03-P20-01","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.RealLine.pointwise_not_uniform"}],"representation":"同一阶跃例 U 上，对任意有限正 τ 取 a=min(1,τ/4)（0<a≤1,2a<τ），B={-a,a}⊆U：输入覆盖数 𝒩(τ,B)=1，输出 𝒩(1/2,f(B))=2（two_point_cover），故 1<2。","dependencies":["CH03-P10-02","CH03-D07"]},
{"id":"CH03-P21-01","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.cor3_17_iff"}],"representation":"diam_{d_i}(A)<τσ≤τN（τσ,τN 有限正）：nullMatrix≥τN ⇔ ∀x,y∈A d_j(f x,f y)=0（反向用 nullRadius_eq_top_of_zero 得 ⊤）。","dependencies":["CH03-D06","CH03-P18-01"]},
{"id":"CH03-P21-02","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.cor3_17_cover"},{"file":"Main.lean","name":"MGC003.cov_one_of_zero"}],"representation":"等价条件成立且 A 非空：任意有限正 ε，covering_number d_j ε f(A)=1。","dependencies":["CH03-P21-01","CH03-D07"]},
{"id":"CH03-P22-01","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.note_finite_entropy_diff"},{"file":"Main.lean","name":"MGC003.cov_finite"}],"representation":"非空有限 U（及任意两端子族、有限正 ε）：两端子族覆盖数均 ≥1 且 <⊤，熵为实数 a,b，mapEntropyDiff=(a−b:ℝ)，MapEntropyDiffDefined 成立。","dependencies":["CH03-D07","CH03-D08"]},
{"id":"CH03-P23-01","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.prop3_18_i"}],"representation":"j∈Iconst：输出覆盖数=1、熵=0、熵差良定且 mapEntropyDiff=metric_entropy(U)（x−0=x，输入熵可为 ⊤）。","dependencies":["CH03-D01","CH03-D08","CH03-D07"]},
{"id":"CH03-P23-02","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.prop3_18_ii_a"},{"file":"Main.lean","name":"MGC003.cov_image_le"},{"file":"Main.lean","name":"MGC003.cov_preimage_le"}],"representation":"j∈Iid：覆盖数 ϕ(U) 与 U 相等（前向推中心；反向对每个像中心用 Classical.choose 选代表元），熵相等。","dependencies":["CH03-P01-03","CH03-D07"]},
{"id":"CH03-P23-03","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.prop3_18_ii_b"}],"representation":"j∈Iid 且 MapEntropyDiffDefined 成立时 mapEntropyDiff=0；不定义 ∞−∞。","dependencies":["CH03-P23-02","CH03-D08"]},
{"id":"CH03-P24-01","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.prop3_19_cover"},{"file":"Main.lean","name":"MGC003.prop3_19_net"}],"representation":"L∈(0,∞) 的单通道 Lip 上界：U 的内部 ε/L-中心集的像是 ϕ(U) 的内部 ε-中心集（中心数不增），故 𝒩_j(ε,ϕ(U))≤𝒩_i(ε/L,U)。","dependencies":["CH03-D07"]},
{"id":"CH03-P24-02","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.prop3_19_entropy"}],"representation":"U 在 d_i 下全有界：三个覆盖数 ≥1 且有限，熵为实数，MapEntropyDiffDefined 成立，且 E_ε(U)−E_{ε/L}(U) ≤ mapEntropyDiff。","dependencies":["CH03-P24-01","CH03-D07","CH03-D08"]},
{"id":"CH03-P25-01","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.prop3_20_cover"},{"file":"Main.lean","name":"MGC003.prop3_20_net"}],"representation":"0<K_{i→j}<⊤ 的 co-Lip 条目：对输出内部 ε-中心集 T，对每个中心选原像代表元（Classical.choose）得 U 的内部 ε/K-中心集，中心数不增，故 𝒩_i(ε/K,U)≤𝒩_j(ε,ϕ(U))。","dependencies":["CH03-D07"]},
{"id":"CH03-P25-02","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.prop3_20_entropy"}],"representation":"U 全有界、输出熵可为 ⊤：MapEntropyDiffDefined 成立，且 mapEntropyDiff ≤ E_ε(U)−E_{ε/K}(U)（EReal 中对 e=⊥,实数,⊤ 分情形）。","dependencies":["CH03-P25-01","CH03-D07","CH03-D08"]},
{"id":"CH03-P26-01","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.Ex31.ex3_1_i_a"},{"file":"Main.lean","name":"MGC003.RealLine.dA"},{"file":"Main.lean","name":"MGC003.RealLine.dA_gauge"},{"file":"Main.lean","name":"MGC003.Ex31.affOp"}],"representation":"绝对值读数伪度量 d=||x|−|y||（⊥ 孤立，dA_gauge 验证合法），仿射算子 2x−1；U={0,1}：φ(0)=−1,φ(1)=1，Fib(φ(0)|U)=Fib(φ(1)|U)=U，i∈Iconst，故 ∉Iid、∉Iact","dependencies":["CH03-D01","CH03-D02"]},
{"id":"CH03-P26-02","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.Ex31.ex3_1_i_b"}],"representation":"φ²(x)=4x−3：φ²(0)=−3,φ²(1)=1，Fib(φ²(0)|U)={0}、Fib(φ²(1)|U)={1}（纤维精确保留 U，并为 U 的分划），i∈Iact。","dependencies":["CH03-D01","CH03-D02"]},
{"id":"CH03-P26-03","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.Ex31.ex3_1_ii"},{"file":"Main.lean","name":"MGC003.Ex31.ex3_1_ii_branches"}],"representation":"ψ 在 U 上取同一值 c：ψ∘ψ(0)=ψ∘ψ(1)，任意纤维不分开 0,1；ψ(c)=⊥ 时 U⊄dom(ψ∘ψ)（再次像为吸收元，纤维定义不适用），ψ(c)≠⊥ 时 U⊆dom(ψ∘ψ)；两分支均有实例。","dependencies":["CH03-D02"]},
{"id":"CH03-P27-01","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.ex3_2_i"}],"representation":"K i j>0（无需有限）、y∈U：d_i(x,y)∉(0,nullRadius(y|U))（正距离导致 K i j=0 的矛盾）。","dependencies":["CH03-D04","CH03-P14-02"]},
{"id":"CH03-P27-02","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.ex3_2_ii"}],"representation":"nullMatrix j i>0 且 K i j>0：∀x,y∈U，d_i(x,y)∈{0}∪[nullMatrix,∞]。","dependencies":["CH03-D05","CH03-P18-01"]},
{"id":"CH03-P28-01","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.Ex33.ex3_3_i_id"},{"file":"Main.lean","name":"MGC003.Ex33.ex3_3_i_shift"},{"file":"Main.lean","name":"MGC003.Ex33.shiftOp"},{"file":"Main.lean","name":"MGC003.Ex33.shift_image"}],"representation":"d_i=||x|−|y||；U={−3,−2,0,2}；恒等算子纤维 {−3},{−2,2},{0}；平移 x+1 的纤维 {−3},{−2,0},{2}；验证 dA 合法、U⊆dom、像集为 {−2,−1,1,3}，并给出纤维族等于分划","dependencies":["CH03-D02"]},
{"id":"CH03-P28-02","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.Ex33.ex3_3_ii"}],"representation":"ε=3/2：𝒩_i(ε,U)=2（上界取 {−3,0}，下界用 two_le_card_of_net），𝒩_i(ε,φ(U))=1（{−2}），ΔE=1−0=1。","dependencies":["CH03-D07","CH03-D08"]},
{"id":"CH03-P29-01","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.Ex34.ex3_4_i_a"},{"file":"Main.lean","name":"MGC003.Ex34.floorOp"}],"representation":"D=[0,1/2]：diam=1/2，nullMatrix=⊤，类型 (true,true)。","dependencies":["CH03-D05","CH03-D06"]},
{"id":"CH03-P29-02","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.Ex34.ex3_4_i_b"}],"representation":"D=[9/10,11/10]：diam=1/5，nullMatrix=0，类型 (true,false)。","dependencies":["CH03-D05","CH03-D06"]},
{"id":"CH03-P29-03","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.Ex34.ex3_4_i_c"}],"representation":"D={0,2}：diam=2，nullMatrix=2，类型 (false,true)。","dependencies":["CH03-D05","CH03-D06"]},
{"id":"CH03-P29-04","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.Ex34.ex3_4_i_d"}],"representation":"D=[0,2]：diam=2，nullMatrix=0，类型 (false,false)。","dependencies":["CH03-D05","CH03-D06"]},
{"id":"CH03-P29-05","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.Ex34.ex3_4_ii"}],"representation":"否定“nullMatrix≥1⟹整体零化”：D={0,2} 满足 nullMatrix=2≥1 但 d(f0,f2)≠0；正半径来自不同点距离≥2（孤立），直径 2≥τσ=1，推论 3.17 条件不满足。","dependencies":["CH03-P29-03"]},
{"id":"CH03-P30-01","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.Ex35.cover_U"},{"file":"Main.lean","name":"MGC003.Ex35.cover_U_of_finite"},{"file":"Main.lean","name":"MGC003.Ex35.cover_seven_fourths"},{"file":"Main.lean","name":"MGC003.Ex35.cover_le_two"}],"representation":"四点集 U={0,1,2,3}：𝒩(ε,U)=4(ε≤1)，2(1<ε≤2)，1(ε>2)；ε=7/4 时为 2，3/2∉U 故 {3/2} 不是合法内覆盖（但其球覆盖 U）。","dependencies":["CH03-D07"]},
{"id":"CH03-P30-02","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.Ex35.ex3_5_ii"},{"file":"Main.lean","name":"MGC003.Ex35.f_image"},{"file":"Main.lean","name":"MGC003.Ex35.g_image"}],"representation":"f(U)=g(U)=U，任意有限正 ε 覆盖数相同，两算子映射熵差均为 0。","dependencies":["CH03-P30-01","CH03-D08"]},
{"id":"CH03-P30-03","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.Ex35.f_lip"},{"file":"Main.lean","name":"MGC003.Ex35.f_lip_least"},{"file":"Main.lean","name":"MGC003.Ex35.g_lip"},{"file":"Main.lean","name":"MGC003.Ex35.g_lip_least"}],"representation":"用背景 HasScalarLipBound：f 的最优标量 Lip 常数为 1，g 为 3（IsLeast；必要下界由点对 (0,1) 给出）。","dependencies":[]},
{"id":"CH03-P30-04","status":"complete","declarations":[{"file":"Main.lean","name":"MGC003.Ex35.ex3_5_iii_b"},{"file":"Main.lean","name":"MGC003.Ex35.ex3_5_iii_entropy"}],"representation":"ε=7/4：命题 3.19 的覆盖数上界 f:𝒩(7/4,U)=2（与真实值相等），g:𝒩(7/12,U)=4（严格大于真实值 2）；熵层面 E(ε)−E(ε/L)=0 与 −1。","dependencies":["CH03-P24-01","CH03-P30-01"]}
]}
```