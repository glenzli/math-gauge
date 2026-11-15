KEEP

### 本轮核查依据

本轮在不改动工作区任何源码、冻结背景模块及历史附件的前提下，对紧邻上一版封卷工程完成了全量编译、公理审计、对齐表核验与逐项数学语义复核，未发现任何缺陷：

1. **固定环境全量编译与入口完整性核查**
   - 在 [LEAN_ENV.sh](file:///private/tmp/math-gauge-carbon-medium-c003-native-context-worker-20261115-v12/alignment/R1/physical-1/session/work/LEAN_ENV.sh) 指定的冻结工具链（Lean 4.29.1 + 固定 mathlib）及 [formal_oet/](file:///private/tmp/math-gauge-carbon-medium-c003-native-context-worker-20261115-v12/alignment/R1/physical-1/session/work/formal_oet) 背景模块之上，对 [Defs.lean](file:///private/tmp/math-gauge-carbon-medium-c003-native-context-worker-20261115-v12/alignment/R1/physical-1/session/work/Ch03/Defs.lean)、[Sec01.lean](file:///private/tmp/math-gauge-carbon-medium-c003-native-context-worker-20261115-v12/alignment/R1/physical-1/session/work/Ch03/Sec01.lean)、[Sec02.lean](file:///private/tmp/math-gauge-carbon-medium-c003-native-context-worker-20261115-v12/alignment/R1/physical-1/session/work/Ch03/Sec02.lean)、[Sec03.lean](file:///private/tmp/math-gauge-carbon-medium-c003-native-context-worker-20261115-v12/alignment/R1/physical-1/session/work/Ch03/Sec03.lean)、[Sec04_05.lean](file:///private/tmp/math-gauge-carbon-medium-c003-native-context-worker-20261115-v12/alignment/R1/physical-1/session/work/Ch03/Sec04_05.lean)、[Sec06.lean](file:///private/tmp/math-gauge-carbon-medium-c003-native-context-worker-20261115-v12/alignment/R1/physical-1/session/work/Ch03/Sec06.lean)、[Sec07_Ex1_3.lean](file:///private/tmp/math-gauge-carbon-medium-c003-native-context-worker-20261115-v12/alignment/R1/physical-1/session/work/Ch03/Sec07_Ex1_3.lean)、[Sec07_Ex4_5.lean](file:///private/tmp/math-gauge-carbon-medium-c003-native-context-worker-20261115-v12/alignment/R1/physical-1/session/work/Ch03/Sec07_Ex4_5.lean) 及汇总入口 [Main.lean](file:///private/tmp/math-gauge-carbon-medium-c003-native-context-worker-20261115-v12/alignment/R1/physical-1/session/work/Main.lean) 逐一执行内核编译，全部 0 错误、0 警告通过。
   - [Main.lean](file:///private/tmp/math-gauge-carbon-medium-c003-native-context-worker-20261115-v12/alignment/R1/physical-1/session/work/Main.lean) 已完整导入全部自建模块，未修改或同名覆盖任何冻结外部依赖。

2. **公理闭包与反作弊限制核查**
   - 静态扫描全部源码文件，确认无 `sorry`、`admit`、`axiom`、`unsafe`、`partial`、`native_decide`、`implemented_by` 等跳过内核检查的设施，亦无把目标结论塞入证书字段、假设或类型类实例的情形。
   - 通过 Lean 元编程对 [alignment.json](file:///private/tmp/math-gauge-carbon-medium-c003-native-context-worker-20261115-v12/alignment/R1/physical-1/session/work/alignment.json) 引用的全部 210 个跨模块声明逐一核验了所属编译模块归属（`getModuleIdxFor?` 精确匹配对应 `file`），并对 `Ch03.*` 命名空间下全部 518 个常元执行 `Lean.collectAxioms`，确认公理闭包严格包含于 `{propext, Classical.choice, Quot.sound}`。

3. **义务清单与对齐表逐项核查（92/92）**
   - 核对 [alignment.json](file:///private/tmp/math-gauge-carbon-medium-c003-native-context-worker-20261115-v12/alignment/R1/physical-1/session/work/alignment.json) 与 [obligations.json](file:///private/tmp/math-gauge-carbon-medium-c003-native-context-worker-20261115-v12/alignment/R1/physical-1/session/work/obligations.json)：`case_id`（`MG-C003`）、`version`（`0.1.1`）及 92 个义务 ID（`CH03-D01` 至 `CH03-P30-04`）无重复、无遗漏，全部状态为 `complete`；仅在显式允许 `allow_background_declarations: true` 的 `CH03-D07` 中引用了冻结模块 [metric_entropy.lean](file:///private/tmp/math-gauge-carbon-medium-c003-native-context-worker-20261115-v12/alignment/R1/physical-1/session/work/formal_oet/vol_01/ch_01_foundations/metric_entropy.lean) 的覆盖数与熵声明，并补充了章节接口等价引理。
   - 对照 [03-operator-local-degeneracy.md](file:///private/tmp/math-gauge-carbon-medium-c003-native-context-worker-20261115-v12/alignment/R1/physical-1/session/work/source/03-operator-local-degeneracy.md) 逐项复核全部数学前提、量词、下标方向与边界分支：
     - **§3.1–§3.2**：常值优先分划（`I_id` 排除 `I_const`）、实际中间像域 `ϕ₁(U)` 与任意长度有限复合链（含零步基例 `c₀ = id`）、两点换位与七点双分量反例的完整公理验证、推论 3.4 允许同分量条目取 `⊤`、点值因子化含空域 `U = ∅` 边界、命题 3.7 仅要求两个实际像集各自分离（`IsSeparatingOn`）而非全空间分离。
     - **§3.3–§3.6**：零化矩阵行列约定 `$[\mathbf{N}(\phi)|_U]_{ji} = \underline{r}^{\mathrm N}_{\phi,i,j}|_U$` 与第 2 章 `L i j`（`$L_{i\to j}$`）的精确区分与桥接、阶跃反例 3.1 点态合法半径集 `(0, |y|]` 与同一固定 `U` 上统一半径为 `0`、命题 3.8(ii) 覆盖 `i = j` 与 `i ≠ j`、命题 3.10 有限非空最小值可达性、命题 3.12(ii) 右端 `0` 与 `⊤` 的除法兼容、命题 3.15(iii) 输出距离为 `⊤` 时的有限正 `ε` 见证、映射熵差严格以 `MappingEntropyDiffWellDefined` 排除 `∞ - ∞`（命题 3.18(ii) 显式带良定前提，命题 3.20 允许输出熵为 `+∞`）。
     - **§3.7 习题 3.1–3.5**：习题 3.1(ii) 完整区分再次作用像 `ψ(c) ≠ ⊥` 与 `ψ(c) = ⊥`（脱离受限定义域）两分支；习题 3.2 不附加 `K_{i→j} < +∞` 的多余有限性假设；习题 3.3–3.5 的全部具体空间与算子（含 `𝒳 \ U` 映至 `⊥`）均已验证扩展伪度量与定义域合法性，并覆盖所有分段端点（`ε = 1, 2`）及外部中心 `3/2 ∉ U` 的非法性证明。

### 仍有的不确定性说明

数学内容、证明完备性与规格对齐上无已知缺陷；仅存形式化设计层面的常规等价表示选择（均符合题面“允许等价表示、合并声明、辅助引理”之规定）：

1. **复合链与指标的索引表示**：有限复合链 `chainCompSeq` / `chainDomainSeq` 采用 Lean 惯用的 0 基自然数索引 `m < n` 表示原文的 `$m = 1, \dots, n$`，阈值分类指示值采用 `Fin 2 × Fin 2` 表示 `$\{0,1\}^2$`，并在引理 3.13 中给出了与四类显式集合 `Regime11`..`Regime00` 的充要对应。
2. **部分函数良定条件的承载方式**：映射熵差 `mappingEntropyDiff` 将“输入或输出覆盖数至少一端有限”作为依赖类型参数 `hwf : MappingEntropyDiffWellDefined ...` 传入，从类型层面根除 `∞ - ∞` 的人工默认赋值，各涉及熵差的定理（如命题 3.18、3.19、3.20 及习题 3.3、3.5）均以存在量词显式构造并给出该良定性证明。