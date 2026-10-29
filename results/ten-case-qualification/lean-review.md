# MG-R001 原文—Lean 独立资格审核

审核日期：2026-10-29。审核对象：`/Users/g4i/lab/math-gauge` 当前工作区，Git HEAD 为 `27bac16ccdc753d247eba23ee8c21ec3463f3bdf`；当前题目和形式化文件存在尚未提交的工作区内容，故本报告以文件 SHA-256 为证据身份。审核者为独立 AI 审阅者；本报告不构成人工审定。

已完整阅读 MG-R001 的题面、参考稿、rubric 和全部 12 个 Lean 文件，核对其实际定义与证明。没有读取 `results/ten-case-validation` 的先前 AI 审核，没有修改仓库，没有运行候选模型，没有新建 Math Workspace 配置或捕获契约。R002–R010 只检查形式化文件及声明状态，其数学实质由其他审核范围负责。

## 结论

MG-R001 的参考核心成立。两类存在性反例、二维非唯一与非一致收敛反例、实际展开的扩展矩阵界、谱条件导出的正权重、有限距离下的零距结论，以及最小偏定义解，都有与其数学作用匹配的 Lean 实现。没有发现把原目标放进证书字段、把分离性或完备性偷偷加入一般定理、把有限残差假定为题设、或以偏定义解冒充全定义解的问题。

历史的“12 模块、81 条定理”数字属实，12 个当前源文件散列全部匹配保存的成功核验报告；81 条源码定理、清单、Audit 指令和公理日志相互一致。按验证预算复用原编译，没有重编译未改源码。此处确认的是“当前源码与已有成功核验完全同一”，不是宣称本次重新运行 Lean。

最强可声称的结论是：**MG-R001 的主要参考结果经过源文件身份核对，并通过本次独立语义审查；一般对象翻译及少量最终装配仍有明确的人工语义边界。R002–R010 没有对应 Lean 工程，不能说十题全部严格形式化对齐。**

MG-R001 适合作为条件保持和识别错误目标的候选题；尚不具备“高难度研究题已经验证”的资格。现有 rubric 正确接受短反例，而一个节点、单点输入、正半轴上除以 2 的反例就足以完成目标否定。复杂参考稿不能提高最短合法解的难度下限。

## 对象、假设与量词核对

| 原文对象 | 实际 Lean 编码 | 独立判断 |
|---|---|---|
| 扩展伪度量族，无分离/完备假设 | [Core 14–18](/Users/g4i/lab/math-gauge/cases/public/MG-R001/formal/Core.lean:14)：`Gauge` 只有自距、对称、三角不等式 | 忠实；`ℝ≥0∞` 保留无穷值。 |
| 孤立吸收元 | [Core 21–39](/Users/g4i/lab/math-gauge/cases/public/MG-R001/formal/Core.lean:21)：`Option Y`、`liftDistance`、四条 `lift_*` | 忠实；没有把底元和零距点合并。 |
| 有限非空 V、有限非空规范指标、有限 E | [Bounds 7](/Users/g4i/lab/math-gauge/cases/public/MG-R001/formal/Bounds.lean:7)、[Weighted 57](/Users/g4i/lab/math-gauge/cases/public/MG-R001/formal/Weighted.lean:57) | `Fintype` 表有限；产生正 q 的主接口显式要求 `Nonempty V/I`，正好由题面 V≠∅、m≥1 提供。其他引理不要求非空是推广而非增添条件。 |
| 非空输入子集 U_v⊆X° | [Core 43–51](/Users/g4i/lab/math-gauge/cases/public/MG-R001/formal/Core.lean:43)：任意类型 `Input v` | 未把输入假设收紧。对原题取 U_v 的子类型即可；原始集合分割到 `System` 的通用构造没有另编码，属于 [COVERAGE 10–15](/Users/g4i/lab/math-gauge/cases/public/MG-R001/formal/COVERAGE.md:10) 已披露的语义翻译边界。 |
| 停止/调用分割与局域映射 | `step : Input v → Y ⊕ Σ e, Input (dst e)`、`step_src` | `step` 存储的是给定的局域选择、终止输出、后继，不存储全局解、终止证书、极限或有限残差。原分割可以构造此数据。 |
| a_e 保持吸收元与非吸收值 | `ret : E → Y → Y`；偏展开用 `Option.map ret` | 忠实限制/扩展。`transform_some` 检查全定义与偏定义的实际展开一致。 |
| L_e 为有限值非负矩阵，局域 Lip 界 | `L : E → I → I → ℝ≥0`、`lip` | 给定的 Lip 条件是合法前提，没有预设全局收缩。有限系数嵌入 ENNReal；0·∞ 运算正确。 |
| Δ 取所有输入上确界，D_w 取有限指标最大值 | [Core 76–77](/Users/g4i/lab/math-gauge/cases/public/MG-R001/formal/Core.lean:76)、[Weighted 12–13](/Users/g4i/lab/math-gauge/cases/public/MG-R001/formal/Weighted.lean:12) | 真实函数空间上的 `iSup`，没有改成有限输入、有限维函数空间或有界函数空间。有限非空索引的 `iSup` 对应原文 max。 |
| 完备性与分离性 | 只出现在二维具体反例的结论，以及零伪度量具体模型的完备性结论 | 没有加入一般正向结果。反例使用更强结构来否定原全称命题完全合法。 |

## 自然语言分项—声明—桥梁矩阵

“直接覆盖”指形式命题与相应分项匹配；“条件覆盖”保留原文自己明确添加的条件；“语义装配”表示已证明组成部分，最终集合重编码或推论没有单独成为 Lean 定理；“未单独形式化”不等于数学错误。

| 自然语言分项 | Lean 声明与位置 | 覆盖结论和边界 |
|---|---|---|
| 题面 3：吸收元隔离的扩展伪度量 | `lift_self/symm/triangle/bottom_isolated`，[Core 21–39](/Users/g4i/lab/math-gauge/cases/public/MG-R001/formal/Core.lean:21) | 直接覆盖。 |
| 参考 19：T 良定义且输出非吸收 | `System.transform` 的函数类型，[Core 59–62](/Users/g4i/lab/math-gauge/cases/public/MG-R001/formal/Core.lean:59) | 定义级覆盖；分割到 `step` 的编码按上表作语义核对。 |
| 参考 21–34：实际调用顺序与 n 步返回复合 | `Calls`、`calls_unfold`，[Routes 8–21](/Users/g4i/lab/math-gauge/cases/public/MG-R001/formal/Routes.lean:8) | 直接覆盖。`Calls` 保存真实 `step` 等式及返回复合，没有保存期望结论。 |
| 参考 28–32：τ 次调用后终止，深度≥τ+1 稳定 | `calls_then_stop`，[Routes 23–28](/Users/g4i/lab/math-gauge/cases/public/MG-R001/formal/Routes.lean:23)；`finite_stop_stable`，[Partial 191–198](/Users/g4i/lab/math-gauge/cases/public/MG-R001/formal/Partial.lean:191) | 直接覆盖，索引偏移正确。 |
| 参考 34：沿一条调用路径的界矩阵为 L_e0⋯L_en−1 | `Calls` 只携带函数复合，不携带矩阵乘积；局域 `System.lip` 可供归纳 | **未单独形式化**。数学上是非负矩阵复合界的短归纳；`delta_matrix_iterate` 证明的是聚合 M^n，不能当作逐路径矩阵乘积定理。 |
| 参考 38–51：真实函数族 Δ(TF,TG)≤MΔ(F,G) 及迭代 | `delta_transform`、`gainAction_matrix`、`delta_matrix_iterate`，[Core 96–125](/Users/g4i/lab/math-gauge/cases/public/MG-R001/formal/Core.lean:96)、[Bounds 10–36](/Users/g4i/lab/math-gauge/cases/public/MG-R001/formal/Bounds.lean:10) | 直接覆盖。局域输入 b 不需 Lip 界，因同输入比较访问同一后继。 |
| 参考 54：无穷初距不能从 M^n→0 消掉 | Δ 与整个估计均在 ENNReal；反例 `different_fixed_distance_top`、`error_top_every_depth` | 直接的实例支持与正确的类型边界；没有作非法无穷消去。 |
| 参考 56：谱半径<1 导出矩阵幂趋零 | `spectral_powers_decay`，[Spectral 10–28](/Users/g4i/lab/math-gauge/cases/public/MG-R001/formal/Spectral.lean:10) | 直接覆盖复矩阵算子范数的 ENNReal 趋零，足以完成后续权重构造。 |
| 参考 56–62：由 M 构造有限正权重和 0<q<1 | `positive_weights_of_spectral`，[Spectral 64–114](/Users/g4i/lab/math-gauge/cases/public/MG-R001/formal/Spectral.lean:64) | 直接覆盖；有限幂和、行和、r 与 q 都实际构造，没有输入权重证书。 |
| 参考 65–68：D_w(TF,TG)≤qD_w(F,G) | `weighted_contraction`、`spectral_weighted_contraction`，[Weighted 39–63](/Users/g4i/lab/math-gauge/cases/public/MG-R001/formal/Weighted.lean:39) | 直接覆盖。辅助定理接受权重不等式；最终接口已从实际 `s.coeff` 谱条件提供，不是循环假设。 |
| 参考 68–75：有限残差时几何 Cauchy 估计 | `weighted_iterate`、`residual_step`、`residual_finite_sum`、`residual_geometric_bound`，[Weighted 65–103](/Users/g4i/lab/math-gauge/cases/public/MG-R001/formal/Weighted.lean:65) | **条件覆盖**。代码先证明更一般的扩展值不等式；有限 R、q<1 才使其为有限且趋零的界，参考稿与 COVERAGE 明示此点。没有另写 `Cauchy` 命题，也没有声称极限落回原空间。 |
| 参考 77：有限距离的固定族只能推出零距 | `fixed_weighted_zero`、`fixed_pointwise_zero`，[Weighted 105–129](/Users/g4i/lab/math-gauge/cases/public/MG-R001/formal/Weighted.lean:105) | **条件覆盖**。`hfinite` 在声明中显式保留；结论是全部分量零距，未升格为点值相等。 |
| 参考 81：构造最小偏定义解 | `eval`、`least`、`least_fixed`，[Partial 26–107](/Users/g4i/lab/math-gauge/cases/public/MG-R001/formal/Partial.lean:26) | 直接覆盖。`least` 由有限展开是否产生 `some` 构造；证明固定性，没有预装解字段。 |
| 参考 83：所有偏定义固定族在终止处一致，且 least 最小 | `eval_le_fixed`、`least_le_fixed`，[Partial 109–124](/Users/g4i/lab/math-gauge/cases/public/MG-R001/formal/Partial.lean:109) | 直接覆盖平坦信息序；目标值域是 `Option Y`。 |
| 参考 83：非吸收定义域恰为有限终止域 | `Halts`、`halts_iff_evaluates`、`least_domain`，[Partial 126–161](/Users/g4i/lab/math-gauge/cases/public/MG-R001/formal/Partial.lean:126) | 直接覆盖。Halts 由真实一步分支归纳，不是假定终止的字段。 |
| 参考 85：逐点有限终止不推出统一有限深度 | 一般程序未添加统一深度假设，但无单独见证/否定定理 | **未单独形式化**。这是正确的一般区别；不影响 `least_*` 已证明部分。 |
| 参考 89：二维输出空间分离且完备，max 规范匹配 | `gauge_separates`、`output_complete`，[Core 143–150](/Users/g4i/lab/math-gauge/cases/public/MG-R001/formal/Core.lean:143)；`metric_matches_gauge`，[Limits 11–13](/Users/g4i/lab/math-gauge/cases/public/MG-R001/formal/Limits.lean:11) | 直接覆盖实际 R² 的乘积最大距离，没有以任意坐标模型替代一般正向命题。 |
| 参考 91–105：整数输入子集、正负分割、两个后继 | `sys`、`inputEmbedding_injective`，[Core 173–196](/Users/g4i/lab/math-gauge/cases/public/MG-R001/formal/Core.lean:173)；`actualInputEquiv`，[Limits 8–9](/Users/g4i/lab/math-gauge/cases/public/MG-R001/formal/Limits.lean:8) | 忠实参数化；有 Z≃range embedding。把 step/ret 等整体传回原集合表示的 bundled 等价定理未另写，属于已披露语义装配。 |
| 参考 108–116：局域界与实际块和，ρ(M)=1/2 | `ret_lip`，[Core 168–171](/Users/g4i/lab/math-gauge/cases/public/MG-R001/formal/Core.lean:168)；`ix_bijective`、`M_is_aggregate`、`half_in_spectrum`、`matrix_spectral_eq_half`，[Counterexample 11–45](/Users/g4i/lab/math-gauge/cases/public/MG-R001/formal/Counterexample.lean:11) | 核心直接覆盖。Fin 4 矩阵与 Bool×Fin 2 系数逐项相同且索引双射；未另写谱半径重编号不变的最终装配定理。无更换矩阵。 |
| 参考 118–135：连续无穷族 F^c 都是固定族且互异 | `solution_fixed/injective/not_unique_fixed`，[Core 198–221](/Users/g4i/lab/math-gauge/cases/public/MG-R001/formal/Core.lean:198)；`fixed_families_infinite`，[Counterexample 47–50](/Users/g4i/lab/math-gauge/cases/public/MG-R001/formal/Counterexample.lean:47) | 直接覆盖，不要求这些是全部固定族。 |
| 参考 135：异参数固定族 Δ=∞ | `different_fixed_distance_top`，[Extra 21–40](/Users/g4i/lab/math-gauge/cases/public/MG-R001/formal/Extra.lean:21) | 直接覆盖第一节点第一分量，足以推出整体距离无穷。 |
| 参考 137–147：偶/奇展开公式、每深度至少一个统一误差∞ | `unfold_formulas`、`even_second_zero`、`error_top_every_depth`，[Counterexample 62–157](/Users/g4i/lab/math-gauge/cases/public/MG-R001/formal/Counterexample.lean:62)、[Limits 41–46](/Users/g4i/lab/math-gauge/cases/public/MG-R001/formal/Limits.lean:41) | 直接覆盖对 F^0 的误差；不是只检查有限样本输入。n=0 也成立，因而覆盖题面 n≥1。 |
| 参考 147：每个固定输入仍收敛到 F^0 | `pointwise_unfold_limit`，[Limits 48–89](/Users/g4i/lab/math-gauge/cases/public/MG-R001/formal/Limits.lean:48) | 直接覆盖，包括 n≤0 的最终常值分支。 |
| 题面 41–45：不存在满足原要求的唯一整体解和任意初值几何逼近理论 | 上述非唯一反例、无解反例、对 F^0 的无限误差和点态极限组成否定证据 | **语义装配**。未定义一个原目标总谓词并证明其否定；但原目标作为合取已被无解/非唯一反例直接否定。若单独要求对任何可能中心的统一收敛都失败，需把点态唯一极限或不同固定初值再接起来；组成事实已足够，没有暗加条件。 |
| 参考 149：分量依赖经复合恢复 | `component_restoration`，[Counterexample 159–162](/Users/g4i/lab/math-gauge/cases/public/MG-R001/formal/Counterexample.lean:159) | 直接覆盖正确复合次序 a21∘a12。 |
| 参考 155：正半轴上无固定族 | `positiveSystem`、`positive_no_fixed`、`single_loop_spectral_lt_one`，[Obstructions 10–38,63–72](/Users/g4i/lab/math-gauge/cases/public/MG-R001/formal/Obstructions.lean:10) | 直接覆盖核心；Unit 输入对应 {1} 的重编码在正文披露，未另写 subtype 等价。 |
| 参考 156：完备的零伪度量两点空间仍可能无点值固定族 | `swap_no_fixed`、`single_loop_spectral_lt_one`、`zero_quotient_subsingleton`，[Obstructions 40–83](/Users/g4i/lab/math-gauge/cases/public/MG-R001/formal/Obstructions.lean:40)；`zero_pseudo_complete/matches`，[Extra 10–17](/Users/g4i/lab/math-gauge/cases/public/MG-R001/formal/Extra.lean:10) | 核心覆盖。单点商用全关系 setoid；其与全零距离的关系是定义级语义桥梁，并未从商固定点推出点值固定点。 |

## 参考数学的独立核验

1. 真实调用边的局域界被非负矩阵之和控制，故 Δ(TF,TG)≤MΔ(F,G) 有效，即使上界为无穷。输入转移无需连续或 Lip，因为比较同一输入的不同函数族。
2. 有限幂和权重是有效构造。M^K 行和小于 1 给出 Mω+1=ω+M^K1，因此 Mω<ω；所有权重至少 1，有限最大比例 r<1，从而 q=(1+r)/2 合法。此论证只把有限矩阵视为有限维，没有把整个函数空间视为有限维。
3. 最小偏解由有限终止求值决定，无限调用取底元。单步递归保留信息序，且一个调用的后继终止当且仅当当前调用有限终止，因此固定性和精确定义域成立。返回算子对非吸收点的保持性阻止终止结果退回底元。
4. 二维反例的非零矩阵项确为 (1,4)、(4,1) 的 1/2；正特征向量给下界，最大行和给上界。固定族 F1^c(n)=c4^n、F2^c(n)=2c4^n 满足两步比例关系，任意不同参数给全输入上确界无穷。
5. 给定 H 的偶/奇公式正确，每个有限输入上的多项式乘几何因子趋零，但每个固定展开深度随输入 n 增大仍无界。这正是点态收敛与函数族统一规范收敛的区别。
6. 两个更小的无解反例各自满足全部原条件。它们足以推翻原强目标；要求候选额外重建作者二维例子会违反现有评分约定。

本次没有发现足以判定 MG-R001 参考答案数学错误的反例或推理缺口。

## 题面、评分与难度

题面只给对象、局域条件、诱导规范及最终目标，没有加入缺失条件列表、反例提醒或作者路线，表达整体克制。目标为假不等于题面数据自相矛盾；评测协议明确允许研究目标失败。[task 41–48](/Users/g4i/lab/math-gauge/cases/public/MG-R001/task.md:41) 的请求与 [rubric 20–21](/Users/g4i/lab/math-gauge/cases/public/MG-R001/rubric.json:20) 的反例完成政策应一起用于作者审核。

rubric 总体合理：允许替代证明和短反例，纯代数偏解不被迫证明无关收缩，条件化贡献与无说明的前提漂移分开。一个可改进的小措辞是 [rubric 12](/Users/g4i/lab/math-gauge/cases/public/MG-R001/rubric.json:12) 的 `assume finite residual/completeness`：按第 21 行应理解为“无说明地假定为题设”，建议未来版本明确写出 silently/unjustifiably，避免误罚明示附加条件的有效定理。这是评分文字消歧，不是已发现的一次数学误判。

难度的最短合法解为：令 X°=(0,∞)，一节点一自环，U={1}，S=∅，b(1)=1，a(y)=y/2，L=1/2。谱条件成立；固定族必须满足 F(1)=F(1)/2，所以 F(1)=0，违反输出类型。这个标准短反例解决存在性，从而否定整个原目标。因而本题可以检验模型是否盲用 Banach 定理，却不足以单靠题面复杂度和参考篇幅证明持续研究能力或高级数学难度。

## 核验证据与当前哈希

| 文件/模块 | SHA-256 | 源码 theorem 数 |
|---|---|---:|
| task.md | `779bf275a6184fb848a12f3d72089a21d4704513512e10323aa48d4ee462cecd` | — |
| reference.md | `dd01173445122c9f91b22d07ff05dc49ae385d58edf1dece0e39927a59c41186` | — |
| rubric.json | `a35f2fbbfe6723614222a8e81e3e687494e1a3526b72581e45d03eb6a8e16569` | — |
| Core | `43b2eeadca67e0ac39f1018009576634c19f49e4a60c29b0e675495f87accf5a` | 19 |
| Partial | `cf6a366ee9e5593f037e6b7650c615591be4163d143b840256f50f8b735e0a4e` | 17 |
| Bounds | `262739382b36a0c21275f2dffa61ce2be71bab545f453146e7f8dd40f269894c` | 2 |
| Spectral | `b353f0e9a6a2b5477960888f5e9a775ba02c2d381d30ff51674045c1f3740aae` | 5 |
| Weighted | `80451dd41897e1218f6621706ec51bb52bd2c0b410f4afe7860f1c48da84373c` | 11 |
| Counterexample | `90b148b7d1d55e0b0b8bbf28597b861d7c33a49bd8979dba554090123c19e6be` | 13 |
| Obstructions | `01204fd26d27d50619062b9523d735c1bd4c03cceac942c707789774b8042682` | 4 |
| Limits | `a8514de9637ea9e65b692efc385d927fffbcba70f2cd64a568b059681d780ec1` | 5 |
| Extra | `e8ce297972b8f16a86fc2883e1605d5e397af534ff8f1bb8eab433e3e14a4c4d` | 3 |
| Routes | `bf02b7195c3a962feef1b192ad0f81e77f473c4b13c3f68b7a6268346eaccf3b` | 2 |
| Reference | `d71c37aa1ea59c60aeca040e8d8d16ff30b3105b90a05acc6fd251bf8bff4bae` | 0 |
| Audit | `a04ebf0bfe04a2749bb3c7070027c243d941c752cf3cfe26667615b2c2e4b9bd` | 0 |

12 个模块中 10 个含数学定理，`Reference` 是汇总导入，`Audit` 是公理打印入口。因此 81 是真实定理声明计数，不能理解为 81 个独立研究结果或自然语言覆盖率分子。

保存的 `verification-report.json` SHA-256 为 `fe1e79e7cd796211e8bbb8979c27d8e277156648bec610e56081caaa7508f27e`，与 draft 工程实际 `.verification/report.json` 字节相同；`axiom-audit.log` SHA-256 为 `dd688604cfd779dc22065e13674950185bd8e17d819de8433e1e7da93d48d3ef`，与 draft 的实际 `logs/Audit.log` 字节相同。公开版 12 源码也与 draft 核验源码逐文件字节相同。

报告记录 Lean 4.29.1、Mathlib `5e932f97dd25535344f80f9dd8da3aab83df0fe6`；当前 toolchain 和 lakefile 声明与之匹配。当前源码没有 `sorry`、`admit` 或新增 `axiom`。81 条日志里 79 条使用标准公理、2 条无公理；实际公理并集恰为 `Classical.choice`、`Quot.sound`、`propext`。这项身份核对不把保存的文本日志升级成独立签名证明，也不替代本次对命题语义的人工式逐项检查。

## 资格阻碍与建议的准确表述

| 项目 | 资格影响 |
|---|---|
| R002–R010 没有 Lean 文件或对应正式工程，`lean_checks` 全为空 | 阻止“十题已严格完成 Lean 对齐”的声称；不据此判九题数学错误。 |
| R001 主核心覆盖充分，但逐路径矩阵乘积、逐点终止与统一深度区别等旁支未单独形式化，部分对象搬运与最终否定仍作语义装配 | 不宜写“参考全文每个断言已机器证明”；可写“主要结论已有形式化与明确边界”。 |
| R001 的合法最短完成路线很短，且当前审核不重新运行模型 | 阻止以作者参考复杂度宣称高难度、稳定区分度或持续研究能力；已有单次实验也不能给出整体难度率。 |
| 本报告是 AI 审核，仓库仍标注 human pending | 不改变协议规定的正式比较资格。 |

建议对外使用：**“MG-R001 的主要参考结论具有经过源码身份核对和独立语义审核的 Lean 证据；其余九题尚未形式化。十题仍是待人工审定和难度校准的候选集。”**
