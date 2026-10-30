# MG-GP003 作者 Lean 与题面对齐

冻结题面和合同 0.1.1；S1、S2、S3、S4、S6 完整，S5 部分完成。S1/S2 现已覆盖原来的任意环境概形，S1 的非开局部化说明也有真实反例。S5 的有限点归纳和典范单位装配已证明，但其转移几何输入尚未证明；不能据此宣布全题完成。候选模型未运行，human pending。

固定 Lean 4.29.1 / Mathlib `5e932f97dd25535344f80f9dd8da3aab83df0fe6`。26 个显式本地模块按依赖顺序列于 [modules.json](modules.json) 和 [manifest.json](manifest.json)。真实 fresh 编译、所有本地声明（含私有）的传递公理审计见 [verification-report.json](verification-report.json)、[declarations.json](declarations.json) 和 logs/。仅允许 `propext`、`Classical.choice`、`Quot.sound`；没有引入外部动机库、额外公理或目标证书。

| 阶段 | 状态 | 实际数学范围 |
| --- | --- | --- |
| S1 | complete | 原 X 上的层 G、真实 S、局部谱 S_i、实际 Scheme.pullback 与两投影限制满足等化子；另证明光滑仿射平面两个有理点处的半局部化具有非开局部谱。 |
| S2 | complete | 原 X 上的 H/G/η 的真实邻域延拓比较，只用题给单射、局部同构及保覆盖成功收缩。没有假定原覆盖正合或交叠满射。 |
| S3 | complete | 含指定点集的开集产生真正 final 邻域子系统；任意反变阿贝尔群预层的典范余极限同构及代表元公式已证明。 |
| S4 | complete | 实际光滑积分仿射 Spec k[t]、原点和稠密 D(t)；受限邻域范畴为空，故不 final。 |
| S5 | partial | 实际有限点单位、单点同构及条件式有限点归纳、商后恢复原单位已证明；实际 HI PST 的分离化、同时有限点检测和成功收缩仍缺。 |
| S6 | complete | 每阶段不正合而极限正合的真实整数复形；逐同调类最终消失推出极限正合，不偷换为统一阶段。 |

## S1：原对象、全部箭头与非开反例

既有 `ActualSemilocalGeometry` 构造实际 `Spec((M⁻¹A)_q)`、相应局部环同构和真实纤维积/张量积同构；`SchemeNeighborhoodValues` 以实际开概形因子分解定义邻域范畴。`PairLocalizationNeighborhoods` 证明共同一般化邻域可由两个局部邻域的交细化，包括空交。`ActualSemilocalDescent` 由真实有限点层拼接得仿射等化子，不预设延拓已经是层。

新增 `AffineRestriction` 从实际开浸入 `j : Spec A → X` 的像/逆像伴随给出 `ambientNeighborhoodIso`。它在代表元上保持同一截面，并与原 η、实际局部化和纤维积限制交换。`GeneralAmbient.general_semilocal_descent_exact` 因而直接陈述原 X 上的等化子；`generalFinitePointValueIso` 还把这些值与题定有限点邻域余极限对应，允许原 X 中非闭点。

仿射图是给定半局部化的呈现数据，不要求原 X 自身仿射。证明对每个这样的呈现、每个交换环、每个原环境概形成立；没有新增从 Lean 的拟射影类型构造共同仿射图的定理，也不以该标签替代已证明的原 X 比较。题面中的光滑拟射影假设保证其通常半局部化构造适用。

`GeneralAmbientNonOpen` 给出真正反例：令 R=ℚ[X][Y]，在 (0,0)、(0,1) 两个有理点半局部化。实际第二个闭点处局部概形到 S 的像不是开集，因此不是开浸入。证明用所有 `ker(Y↦aX)`：它们在原点之下而不在第二点之下；若局部谱像开，就有一个不在第二点极大理想中的多项式落入所有这些素理想，但无限多根迫使该多项式为零。实际闭点、有限点局部化、结构态射光滑、原概形仿射且整均已形式化。

## S2：原单位与成功收缩

`SchemeNeighborhoodMaps` 将原η送到真实 `colim.map`，其开子概形、交叠和局部谱限制有自然性。`ActualOpenComparison` 从实际局部值满射提取邻域代表、除去另一闭点构造分离覆盖、调用题给成功收缩，最后用交叠单射与 S1 的唯一性得到比较双射。

`GeneralAmbientComparison` 将整个论证搬回原 X。`ambientMap_injective_iff`、`ambientMap_surjective_iff` 和 `ambientTwoOpen_exact_iff` 分别搬运原映射与成功收缩后的正合行；三处同构都来自实际开浸入。端点 `general_two_closed_comparison` 对原η成立，故可直接取题给层化单位；无需另假设图上某个任意同构就是该单位。局部只使用满射，比题给同构更弱。

## S5：已完成装配与仍缺的几何

`S5FiniteInduction` 在真实 stalk、overlap colimit 和 `neighborhood_value` 上证明有限插入归纳、映射自然性及字面层化单位的条件式同构。其 `SingletonBlockGluing` 是明示待证的二块拼接性质，不是原题假设，也没有被宣称已由 transfers/HI 推出。

`finite_neighborhood_original_unit_of_quotient_comparison` 使用真实商候选态射、`sheafifyMap` 和 `toSheafify_naturality` 恢复原 F 的单位，不对原 F 偷加分离性。应用它仍需构造真正 Zariski 分离商并证明其有限点比较与几何拼接。这些缺口以及大/小位点比较见 [GAPS](GAPS.md)。本轮上游实际源码复查见 [upstream-recheck.json](transfers/upstream-recheck.json)；书面定理来源与假设复核见 [SOURCE-RECHECK](SOURCE-RECHECK.md)。外部论文结论没有被写成 Lean 公理。
