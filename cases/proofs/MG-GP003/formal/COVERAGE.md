# MG-GP003 作者 Lean 与题面对齐

冻结题面和合同 0.1.1；S1–S6 的作者 Lean 覆盖完整。S5 已由真实有限对应、任意域上的同时有限点 moving、实际普通 Zariski 层化和原 X 的邻域余极限，证明题面指定的典范单位同构。作者证明、独立 AI 语义审核、Lean 编译与人工批准分别记录；候选模型未运行，human pending，题目仍为 draft。

本组使用固定 profile `lean-4.34.1-motivic`：Lean 4.34.1，Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`，Motivic `a6805c4a87cdfd7717dd7a94039246a167f15380`，Aglib `2c34f185fa859e862661f939cd216b07bcccfb26`。44 个显式本地模块按依赖顺序列于 [modules.json](modules.json) 和 [manifest.json](manifest.json)。可复现环境、来源及许可证见 [环境说明](../../../../verification/environments/motivic-4.34.1/README.md)。其余题目的固定环境不变。

真实 fresh 编译、所有本地声明（含私有）的传递公理审计见 [verification-report.json](verification-report.json)、[declarations.json](declarations.json) 和 logs/。仅允许 `propext`、`Classical.choice`、`Quot.sound`。实际外部导入闭包同时绑定源码和编译产物，编译前后核对；这不是把外部定理作为公理，也不是仅检查本地文件的表面导入。独立语义审核另见 [当前审核收据](../../../../verification/author/semantic-reviews/MG-GP003.json)。

| 阶段 | 状态 | 实际数学范围 |
| --- | --- | --- |
| S1 | complete | 原 X 上的层 G、真实 S、局部谱 S_i、实际 Scheme.pullback 与两投影限制满足等化子；另证明光滑仿射平面两个有理点处的半局部化具有非开局部谱。 |
| S2 | complete | 原 X 上的 H/G/η 的真实邻域延拓比较，只用题给单射、局部同构及保覆盖成功收缩。没有假定原覆盖正合或交叠满射。 |
| S3 | complete | 含指定点集的开集产生真正 final 邻域子系统；任意反变阿贝尔群预层的典范余极限同构及代表元公式已证明。 |
| S4 | complete | 实际光滑积分仿射 Spec k[t]、原点和稠密 D(t)；受限邻域范畴为空，故不 final。 |
| S5 | complete | 真实 HI PST 在任意域、原 X 任意有限非空点集的原典范 Zariski 单位同构；实际同时 moving、有限域 trace/Bezout、非整分支拼接及大/小位点单位比较均已证明。 |
| S6 | complete | 每阶段不正合而极限正合的真实整数复形；逐同调类最终消失推出极限正合，不偷换为统一阶段。 |

## S1：原对象、全部箭头与非开反例

既有 `ActualSemilocalGeometry` 构造实际 `Spec((M⁻¹A)_q)`、相应局部环同构和真实纤维积/张量积同构；`SchemeNeighborhoodValues` 以实际开概形因子分解定义邻域范畴。`PairLocalizationNeighborhoods` 证明共同一般化邻域可由两个局部邻域的交细化，包括空交。`ActualSemilocalDescent` 由真实有限点层拼接得仿射等化子，不预设延拓已经是层。

新增 `AffineRestriction` 从实际开浸入 `j : Spec A → X` 的像/逆像伴随给出 `ambientNeighborhoodIso`。它在代表元上保持同一截面，并与原 η、实际局部化和纤维积限制交换。`GeneralAmbient.general_semilocal_descent_exact` 因而直接陈述原 X 上的等化子；`generalFinitePointValueIso` 还把这些值与题定有限点邻域余极限对应，允许原 X 中非闭点。

仿射图是给定半局部化的呈现数据，不要求原 X 自身仿射。证明对每个这样的呈现、每个交换环、每个原环境概形成立；没有新增从 Lean 的拟射影类型构造共同仿射图的定理，也不以该标签替代已证明的原 X 比较。题面中的光滑拟射影假设保证其通常半局部化构造适用。

`GeneralAmbientNonOpen` 给出真正反例：令 R=ℚ[X][Y]，在 (0,0)、(0,1) 两个有理点半局部化。实际第二个闭点处局部概形到 S 的像不是开集，因此不是开浸入。证明用所有 `ker(Y↦aX)`：它们在原点之下而不在第二点之下；若局部谱像开，就有一个不在第二点极大理想中的多项式落入所有这些素理想，但无限多根迫使该多项式为零。实际闭点、有限点局部化、结构态射光滑、原概形仿射且整均已形式化。

## S2：原单位与成功收缩

`SchemeNeighborhoodMaps` 将原η送到真实 `colim.map`，其开子概形、交叠和局部谱限制有自然性。`ActualOpenComparison` 从实际局部值满射提取邻域代表、除去另一闭点构造分离覆盖、调用题给成功收缩，最后用交叠单射与 S1 的唯一性得到比较双射。

`GeneralAmbientComparison` 将整个论证搬回原 X。`ambientMap_injective_iff`、`ambientMap_surjective_iff` 和 `ambientTwoOpen_exact_iff` 分别搬运原映射与成功收缩后的正合行；三处同构都来自实际开浸入。端点 `general_two_closed_comparison` 对原η成立，故可直接取题给层化单位；无需另假设图上某个任意同构就是该单位。局部只使用满射，比题给同构更弱。

## S5：核心转移几何到原典范单位

最终端点在 [S5Complete.lean](MathGauge/GP003/S5Complete.lean)：`semilocal_zariski_unit_isIso` 与 `semilocal_small_zariski_unit_isIso`。二者的假设只有任意域、题给实际 HI PST、光滑对象、有限非空点集及题面已选择的共同仿射开；结论分别是大位点和小位点普通 Zariski 层化的原单位在题定余极限上为同构。共同仿射开是 S 的呈现数据，不是用来绕过 S5 的新增假设；不另行宣称从 Lean 的 `IsQuasiProjective` 类型构造该开集。

1. `S5ZariskiKernel` 证明实际 Nisnevich 单位核恰为 Zariski 局部零子群，实际转移保持该子群；将 Nis 单位像与字面商群对应，验证其 HI。`S5ZariskiComparison` 证明商前后普通 Zariski 层化同构，以及原 Zariski 层化到 Nis 层化的典范单射与单位等式。没有用 Nis 层化替换目标。
2. `S5SimultaneousUniversal` 在无限域以一组共同参数、真实有限紧化和边界标架，构造保留全部指定点的 moving 对应及 A1 端点。`S5SimultaneousFinite` 在有限域选两个互素次数扩张，并保留指定点的完整原像；不要求原对象几何整。`S5FiniteScalarMovingDescent` 用真实有限可分扩张转移和整数 Bézout 等式降下，得到对所有 HI PST 都适用的同一个实际对应 β。
3. `S5FiniteClosedPointReduction` 通过闭特殊化把构造用的点变为闭点，所得开集仍包含所有原点；`S5InfiniteAffineMoving`、`S5FiniteFieldMoving`、`S5AllFieldMoving` 处理零维、仿射坐标变换及任意域，最终证明 `integralAffineMoving_of_field`。辅助命题 `IntegralAffineMoving` 已被消去，不保留为最终输入。
4. `S5IntegralComparison` 与 `S5TransferSectionLift` 用这个共同 β 同时作用于原 P 和已证明 HI 的 Nis 层化，得到核截面的共同消失和普通 Zariski 层化截面的共同提升。`S5DisjointAssembly`、`S5DisjointGeometry`、`S5AffineComparison` 通过实际有限个 clopen 整分支和 Cor 的有限余积处理非整对象；原 P 的拼接来自加性对应结构，不偷用层条件。
5. `S5AmbientComparison` 在原 X 的任意给定邻域中细化到含全部点的仿射开，将几何输出化为原 X 的实际更小开。`S5SiteBridge` 证明真实 Zariski 拓扑、big/small 层化同构及单位相容，并用共同邻域代表元准则完成注入和满射。目标就是题面定义的所有开邻域余极限。

这条完整路线不依赖旧 `S5FiniteInduction` 中尚未从几何独立推出的 `SingletonBlockGluing`，也不声称完整形式化了 MVW Lemma 22.10 的更强二开正合结论。旧条件式辅助定理仍明确保留条件，不充当完成证据。先前 G0–G4 的目标如何被实际证明取代及范围界限见 [GAPS](GAPS.md)；书面参考所引定理的来源复核见 [SOURCE-RECHECK](SOURCE-RECHECK.md)。
