FULL

### 1. 本轮核查依据
- 完整读取可见历史附件（`.visible-history/R1/index.json` 及全部消息片段），并与工作区中的冻结规格 [task.md](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/alignment/R1/physical-1/session/work/task.md)、[obligations.json](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/alignment/R1/physical-1/session/work/obligations.json)、[dependencies.md](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/alignment/R1/physical-1/session/work/dependencies.md)、[source/03-operator-local-degeneracy.md](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/alignment/R1/physical-1/session/work/source/03-operator-local-degeneracy.md) 及前置背景 `formal_oet/` 逐项对照。
- 对紧邻上一版全部 92 项义务的 Lean 声明逐条核对前提、量词、边界（空集、吸收元、无穷大、严格/非严格不等式、矩阵行列约定）与结论，并在冻结环境中执行从零编译与基于编译后 `Environment` 的元程序审计（模块归属、传递公理集、禁用设施扫描、义务间实际常量引用图与 `alignment.json` 依赖表双向比对）。

### 2. 发现的缺陷与本轮修改

#### (a) 对齐表 [alignment.json](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/alignment/R1/physical-1/session/work/alignment.json) 实质性修复
1. **移除虚假依赖（`CH03-P07-04`）**：上一版 `CH03-P07-04` 列出 `"dependencies": ["CH03-D03"]`，但经环境常量图审计，`Ch03.prop_3_6_iii` 与 `Ch03.prop_3_6_iii_subsingleton` 既未直接也未传递引用 `CH03-D03` 的任何声明；现已更正为 `[]`。
2. **修正 `CH03-D07` 背景声明归属，消除跨节反向引用**：上一版在 §3.5 覆盖数/熵接口 `CH03-D07` 中列入了第 1 章伪度量基础定义 `subfamily_pseudometric`，导致 §3.2–3.3 的纤维与零化半径义务在常量图上反向引用 `CH03-D07`。现将 `CH03-D07` 聚焦于覆盖数、度量熵与全有界接口（复用冻结 `metric_entropy.lean` 中的 `InternalEpsilonNet`、`covering_number*`、`metric_entropy*`、`subfamily_metric_entropy*` 及 `Ch03/ScaleAndCovering.lean` 中的对应定理）。
3. **消除 `CH03-P07-01` 与 `CH03-P07-02` 的互指环**：上一版两项均重复列出合并充要定理 `Ch03.prop_3_6_i`，在声明依赖图上形成二元环；现精确拆分为 `CH03-P07-01 → Ch03.prop_3_6_i_nec` 与 `CH03-P07-02 → Ch03.prop_3_6_i_suff`（`CH03-P07-03` 仍通过 `prop_3_6_i` 依赖二者）。
4. **全量补齐实际直接依赖并验证无环**：上一版有 30 余项遗漏了声明类型或证明项中实际直接引用的义务 ID（如 `CH03-P10-03`、`CH03-P12-02`、`CH03-P21-02`、`CH03-P23-03`、`CH03-P28-02`、`CH03-P30-03/04` 等）。本轮由编译后 Lean 环境自动提取并核验全部 92 项的实际直接引用义务，实现零遗漏、零冗余、有向无环图（DAG）。

#### (b) Lean 源码的表示对应与边界补强
1. [Ch03/FiberFactorization.lean](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/alignment/R1/physical-1/session/work/Ch03/FiberFactorization.lean)（`CH03-D02`）：新增 `Ch03.subfamily_pseudometric_eq_finset_sup'`，显式证明有限非空子族下冻结 `subfamily_pseudometric`（`⨆`）与正文有限最大值 $\max_{j\in J} d_j(x,y)$（`Finset.sup'`）严格一致。
2. [Ch03/NullificationRadius.lean](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/alignment/R1/physical-1/session/work/Ch03/NullificationRadius.lean)（`CH03-P10-02`、`CH03-P11-03`）：新增 `Ch03.counterexample_3_1_pointwise_all`（直接对所有 $y\in U$ 给出 $r^{\mathrm N}>0$）；为命题 3.8(ii) 新增有限非空指标集上的具体见证 `Ch03.prop_3_8_ii_eq_concrete`（`Unit`）与 `Ch03.prop_3_8_ii_ne_concrete`（`TwoIdx`）。
3. [Ch03/ScaleAndCovering.lean](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/alignment/R1/physical-1/session/work/Ch03/ScaleAndCovering.lean)（`CH03-D07`、`CH03-P20-01`）：新增 `Ch03.subfamily_metric_entropy_eq_log2_subfamily_covering`；新增 `Ch03.post_prop_3_16_pointwise_pos_insufficient`，在反例 3.1 的同一阶跃算子与域 `stepU` 上显式结合处处正点态半径与任意 $\tau\in(0,\infty)$ 的反例，直接否定“仅点态正半径即存在统一有限正尺度 $\tau$ 控制全部子集 $B\subseteq U$ 覆盖数”。
4. [Ch03/Exercises1to3.lean](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/alignment/R1/physical-1/session/work/Ch03/Exercises1to3.lean)（`CH03-P26-03`）：加强 `Ch03.exercise_3_1_ii`，在 `some c ∈ dom ψ` 分支中显式证明整个纤维分划退化为单块 `compFiberFamily absDiffDist ψ2 Set.univ ex31U = {ex31U}`。
5. [Ch03/Exercises4to5.lean](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/alignment/R1/physical-1/session/work/Ch03/Exercises4to5.lean)（`CH03-P29-05`、`CH03-P30-03`）：新增 `Ch03.dom_floorOp_eq_range_some` 并在 `Ch03.exercise_3_4_ii` 中显式否定对任意非空 $D\subseteq \mathrm{range}(\mathrm{some})$（即 $D\subseteq\mathbb R$）的命题；导入冻结 `formal_oet.vol_01.ch_02_operator_bounds.single_channel` 并新增 `Ch03.exercise_3_5_iii_a_hasScalarLipBound`，给出与冻结定义 `HasScalarLipBound` 的等价封装。

### 3. 实际完成范围
- 完整交付 7 个章节模块与入口文件：[Ch03/ComponentPartition.lean](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/alignment/R1/physical-1/session/work/Ch03/ComponentPartition.lean)、[Ch03/FiberFactorization.lean](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/alignment/R1/physical-1/session/work/Ch03/FiberFactorization.lean)、[Ch03/NullificationRadius.lean](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/alignment/R1/physical-1/session/work/Ch03/NullificationRadius.lean)、[Ch03/ScaleAndCovering.lean](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/alignment/R1/physical-1/session/work/Ch03/ScaleAndCovering.lean)、[Ch03/MappingEntropyDiff.lean](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/alignment/R1/physical-1/session/work/Ch03/MappingEntropyDiff.lean)、[Ch03/Exercises1to3.lean](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/alignment/R1/physical-1/session/work/Ch03/Exercises1to3.lean)、[Ch03/Exercises4to5.lean](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/alignment/R1/physical-1/session/work/Ch03/Exercises4to5.lean)、[Main.lean](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/alignment/R1/physical-1/session/work/Main.lean)（导入全部 7 个目标模块）以及 [alignment.json](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/alignment/R1/physical-1/session/work/alignment.json)。
- `obligations.json` 规定的全部 **92/92** 项义务均为 `complete`（共 219 条声明引用），冻结规格与 `formal_oet/` 原字节未改动。

### 4. 编译与审计情况
- 在冻结环境（`LEAN_ENV.sh`：Lean 4.29.1 + 固定 mathlib + 冻结 `formal_oet/`）下从零完整编译全部 6 个前置模块、7 个 `Ch03` 模块及 `Main.lean`，**零错误、零警告**。
- 元审计验证：
  - `alignment.json` 中全部 219 条声明均存在于对应 `file` 编译所得模块中（缺失 0，错模块 0），且仅允许项 `CH03-D07` 引用了冻结背景模块 `formal_oet/vol_01/ch_01_foundations/metric_entropy.lean`。
  - `Ch03.*` 与 `Main` 中全部 587 个常量及 219 条对齐声明的传递公理并集严格为 `{propext, Quot.sound, Classical.choice}`（禁用公理 0，无 `sorry`/`admit`/`native_decide`/`unsafe`/`set_option`）。
  - 92 项义务的实际直接常量依赖与 `alignment.json` 中 `dependencies` 100% 精确一致（缺失 0、多余 0、环 0）。

### 5. 仍有的不确定性
- **依赖粒度约定**：本轮 `dependencies` 按编译期常量引用图（穿透未列入 `alignment.json` 的内部辅助引理，并在遇到其他义务所列声明处截断）自动生成，因此当某定理引用另一项的大合取定理（如 `CH03-P30-03`/`04` 引用 `exercise_3_5_ii`）时，后者类型签名中出现的定义义务（如 `CH03-D08`）也会被计入直接依赖。这严格忠实于 Lean 内核常量依赖，但若评审偏好仅按“语义证明步骤”作传递约简，粒度会略有差异。
- **等价表示选择**：`InputScaleFamily` 以 `Set X → ENNReal` 并在 `mono` 中施加 `A₁.Nonempty`（而非子类型 `{A // A.Nonempty} → ENNReal`）；`prop_3_2_ii` 采用 0 起始索引 `Fin n` 的递归复合 `chainOp`/`chainOpFin` 与 `chainDomain`/`chainDomainFin`（与正文 1 起始索引同构）；`mappingEntropyDiff` 将良定条件作为依赖参数以确保类型层面排除 $\infty - \infty$。上述表示均与原文数学严格等价，但若外部评审脚本期望特定签名形态仍需通过 `alignment.json` 对照理解。