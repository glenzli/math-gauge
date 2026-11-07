# Gemini 3.8 Flash High · 当前固定记录

benchmark0.6.0开发草稿；聚合0.8.0／MC0.2.0／Strict0.2.0，承诺扣罚组件0.1.0，选题组件0.3.0、书面替换组件0.1.0。AI审核、人审待定，正式比较资格false，未发布release。

三种分数共用34题（公24／私10）、30个数学家族及书面35／Lean35／研究30权重，另固定三轮Lean自查。已建90／100，研究稿完善10分待建；不将已建部分或已测部分重新归一化。

| 条件 | MC | RMC（默认） | Strict |
|---|---:|---:|---:|
| 首次 | 54.52 | 45.18 | 13.75 |
| 允许非逻辑重跑 | 54.52 | 45.18 | 13.75 |

箭头表示首次→允许计次非逻辑重跑；相同只列一次。DeepSeek另10道研究题、1道新增私有书面题及PS001未测，保持未知及固定分母。GR103旧成绩不回填PS001；已确认贡献降低不代表新增数学失败。题包待建10分另列。

PS001按用户选择替换公开GR103，仍为8公／4私书面论证、12家族等权。Gemini只采用原始A1原评94/100、Strict不通过；独立再评不进入当前留档。Terra新Max A1为100/100、Strict通过，用时430.738秒，工具开放、实际0次命令；单射段的局部引用错误单独记录。DeepSeek留待后测，记unknown。GR103原答、原审核和冻结计划保留为历史来源，不再进入当前聚合。

Gemini的94分原评保持原字节。现行RMC对跨阈值迭代中的错误断言扣10%，对边界下界被错误断言为正扣5%；两个独立根因共扣15%，不使用核心放行封顶。Terra的全部参数构造有效；已证像集密度为1使缺失坐标的均值趋零，单射段重复不等式方向的连接语按冻结规则列为局部引用笔误，不另扣分。

所有正式测试允许本地工具与预置公共依赖，禁止联网检索和工具联网；模型服务与认证连接另记。允许与实际使用分别记录。纯系统故障不占有效尝试，输出耗尽仍占一次；数学错误不能重跑。本次没有Lean重编译，冻结旧输入、原答、自评和0.4.0审核不改写。

[原答与证据](record.json) · [当前承诺审核](claim-review-public-ps001.json) · [PS001来源](written-replacement-evidence.json)

## 六视图及分类贡献

| 子类 | MC首次 | MC重跑 | RMC首次 | RMC重跑 | Strict首次 | Strict重跑 |
|---|---:|---:|---:|---:|---:|---:|
| 书面论证 | 17.41 | 17.41 | 14.07 | 14.07 | 2.08 | 2.08 |
| 论证审阅 | 6.94 | 6.94 | 5.44 | 5.44 | 2.50 | 2.50 |
| 语义审计 | 7.72 | 7.72 | 6.72 | 6.72 | 2.50 | 2.50 |
| 形式化 | 13.28 | 13.28 | 12.78 | 12.78 | 2.50 | 2.50 |
| 对齐自查 | 0.00 | 0.00 | -2.00 | -2.00 | 0.00 | 0.00 |
| 背景核查 | 4.17 | 4.17 | 3.17 | 3.17 | 2.50 | 2.50 |
| 研究稿完善 | 建设中 | 建设中 | 建设中 | 建设中 | 建设中 | 建设中 |
| 命题拓展 | 5.00 | 5.00 | 5.00 | 5.00 | 1.67 | 1.67 |

## 首次：公开题错误承诺审核

| 任务 | MC题内比例 | RMC题内比例 | Strict | 新发现记录 | 整题最高0 |
|---|---:|---:|---|---:|---|
| MG-GP002 | 75.00 | 65.00 | 未通过 | 1 | 否 |
| MG-GR005 | 76.00 | 66.00 | 未通过 | 1 | 否 |
| MG-GR009 | 60.00 | 40.00 | 未通过 | 1 | 否 |
| MG-GR021 | 66.67 | 46.67 | 未通过 | 4 | 否 |
| MG-GR023 | 98.89 | 93.89 | 未通过 | 1 | 否 |
| MG-AR002 | 55.00 | 45.00 | 未通过 | 1 | 否 |
| MG-AR003 | 45.00 | 0.00 | 未通过 | 1 | 是 |
| MG-AR004 | 77.50 | 72.50 | 未通过 | 1 | 否 |
| AHR01 | 83.00 | 73.00 | 未通过 | 1 | 否 |
| AHR02 | 30.00 | 0.00 | 未通过 | 1 | 是 |
| LCH02 | 95.00 | 85.00 | 未通过 | 1 | 否 |
| HCH02 | 95.00 | 85.00 | 未通过 | 1 | 否 |
| MG-BC001 | 66.67 | 51.67 | 未通过 | 2 | 否 |
| MG-BC002 | 0.00 | -5.00 | 未通过 | 1 | 否 |
| MG-PS001 | 94.00 | 79.00 | 未通过 | 2 | 否 |

### MG-GP002

Checked the retained source judgment and available candidate answer/artifacts. Only specific established false or unsupported commitments are appended; missing work alone receives no additional finding.

- **MG-GP002-claim-1 · material**：具体反例否定所交统一常数，影响C^m证明；不是因证明较短扣分。 根因：wrong_uniform_constant；已覆盖：none。
  [原审核证据](https://github.com/glenzli/math-gauge/blob/178e95c1e5ae690087c728c02c5258eeb8c4d608/results/v0.6.0/gemini-3.8-flash-high/20261105/scoring-inputs.json) · JSON定位 /slots/26/group_diagnostic/stages/3/notes · SHA-256 9dd4ce0784879108bee0eb785a7197660268600117d98ed0be50f2a94b56d183。

### MG-GR005

Checked the retained source judgment and available candidate answer/artifacts. Only specific established false or unsupported commitments are appended; missing work alone receives no additional finding.

- **MG-GR005-claim-1 · material**：将完整允许竞争类缩为正规情形后宣布最大性证明；有保留原前提的反例。 根因：improper_competitor；已覆盖：none。
  [原审核证据](https://github.com/glenzli/math-gauge/blob/178e95c1e5ae690087c728c02c5258eeb8c4d608/results/v0.6.0/gemini-3.8-flash-high/20261105/scoring-inputs.json) · JSON定位 /slots/2/group_diagnostic/stages/3/math_review/notes · SHA-256 9dd4ce0784879108bee0eb785a7197660268600117d98ed0be50f2a94b56d183。

### MG-GR009

Checked the retained source judgment and available candidate answer/artifacts. Only specific established false or unsupported commitments are appended; missing work alone receives no additional finding.

- **MG-GR009-claim-1 · critical**：把基底满射这一充分条件提升为必要条件；具体平凡群例已反驳。 根因：false_necessity；已覆盖：none。
  [原审核证据](https://github.com/glenzli/math-gauge/blob/178e95c1e5ae690087c728c02c5258eeb8c4d608/results/v0.6.0/gemini-3.8-flash-high/20261105/scoring-inputs.json) · JSON定位 /slots/4/group_diagnostic/stages/5/notes · SHA-256 9dd4ce0784879108bee0eb785a7197660268600117d98ed0be50f2a94b56d183。

### MG-GR021

Checked the retained source judgment and available candidate answer/artifacts. Only specific established false or unsupported commitments are appended; missing work alone receives no additional finding.

原内嵌可靠性：5/10，数学贡献按(S−r)/90换算；来源判准未改。

- **MG-GR021-claim-1 · material**：明确的全称有限计数为假。 根因：finite_counts；已覆盖：none。
  [原审核证据](https://github.com/glenzli/math-gauge/blob/178e95c1e5ae690087c728c02c5258eeb8c4d608/results/v0.6.0/gemini-3.8-flash-high/20261105/scoring-inputs.json) · JSON定位 /slots/39/group_diagnostic/criteria/0/notes · SHA-256 9dd4ce0784879108bee0eb785a7197660268600117d98ed0be50f2a94b56d183。

- **MG-GR021-claim-2 · material**：实际固定类分类遗漏实质耦合，答卷自身合法例亦反驳其通式。 根因：fixed_classification；已覆盖：none。
  [原审核证据](https://github.com/glenzli/math-gauge/blob/178e95c1e5ae690087c728c02c5258eeb8c4d608/results/v0.6.0/gemini-3.8-flash-high/20261105/scoring-inputs.json) · JSON定位 /slots/39/group_diagnostic/criteria/1/notes · SHA-256 9dd4ce0784879108bee0eb785a7197660268600117d98ed0be50f2a94b56d183。

- **MG-GR021-claim-3 · material**：约化满射性有明确标量反例。 根因：reduction_surjectivity；已覆盖：none。
  [原审核证据](https://github.com/glenzli/math-gauge/blob/178e95c1e5ae690087c728c02c5258eeb8c4d608/results/v0.6.0/gemini-3.8-flash-high/20261105/scoring-inputs.json) · JSON定位 /slots/39/group_diagnostic/criteria/2/notes · SHA-256 9dd4ce0784879108bee0eb785a7197660268600117d98ed0be50f2a94b56d183。

- **MG-GR021-claim-4 · local**：此独立反号已由旧可靠性5分损失处理，不能再叠扣。 根因：cayley_sign；已覆盖：embedded_reliability。
  [原审核证据](https://github.com/glenzli/math-gauge/blob/178e95c1e5ae690087c728c02c5258eeb8c4d608/results/v0.6.0/gemini-3.8-flash-high/20261105/scoring-inputs.json) · JSON定位 /slots/39/group_diagnostic/criteria/4/notes · SHA-256 9dd4ce0784879108bee0eb785a7197660268600117d98ed0be50f2a94b56d183。

### MG-GR023

Checked the retained source judgment and available candidate answer/artifacts. Only specific established false or unsupported commitments are appended; missing work alone receives no additional finding.

原内嵌可靠性：10/10，数学贡献按(S−r)/90换算；来源判准未改。

- **MG-GR023-claim-1 · local**：延拓不唯一的局部断言与单点实例及本答卷正确计数矛盾；其他结构性成果保留。 根因：unique_extension；已覆盖：none。
  [原审核证据](https://github.com/glenzli/math-gauge/blob/178e95c1e5ae690087c728c02c5258eeb8c4d608/results/v0.6.0/gemini-3.8-flash-high/20261105/scoring-inputs.json) · JSON定位 /slots/41/group_diagnostic/criteria/0/notes · SHA-256 9dd4ce0784879108bee0eb785a7197660268600117d98ed0be50f2a94b56d183。

### MG-AR002

Checked the retained source judgment and available candidate answer/artifacts. Only specific established false or unsupported commitments are appended; missing work alone receives no additional finding.

- **MG-AR002-claim-1 · material**：明确认可错误的仿射/线性补充路线；原正文另有有效证明，按非核心放行扣10%，不整题封顶。 根因：affine_supplement；已覆盖：none。
  [原审核证据](https://github.com/glenzli/math-gauge/blob/178e95c1e5ae690087c728c02c5258eeb8c4d608/results/v0.6.0/gemini-3.8-flash-high/20261105/scoring-inputs.json) · JSON定位 /slots/36/group_diagnostic/dimensions/0/notes · SHA-256 9dd4ce0784879108bee0eb785a7197660268600117d98ed0be50f2a94b56d183。

### MG-AR003

Checked the retained source judgment and available candidate answer/artifacts. Only specific established false or unsupported commitments are appended; missing work alone receives no additional finding.

- **MG-AR003-claim-1 · critical**：明确放行使被审核心识别论证失效的假断言。RMC整题最高0；MC保留其余有效审阅。 根因：fixed_target_image；已覆盖：none。
  [原审核证据](https://github.com/glenzli/math-gauge/blob/178e95c1e5ae690087c728c02c5258eeb8c4d608/results/v0.6.0/gemini-3.8-flash-high/20261105/scoring-inputs.json) · JSON定位 /slots/37/group_diagnostic/major_error_notes · SHA-256 9dd4ce0784879108bee0eb785a7197660268600117d98ed0be50f2a94b56d183。

### MG-AR004

Checked the retained source judgment and available candidate answer/artifacts. Only specific established false or unsupported commitments are appended; missing work alone receives no additional finding.

- **MG-AR004-claim-1 · local**：原条件被误删并扩大局部化结论的适用范围；已正确识别主证核心错误，不列核心错误放行。 根因：localization_scope；已覆盖：none。
  [原审核证据](https://github.com/glenzli/math-gauge/blob/178e95c1e5ae690087c728c02c5258eeb8c4d608/results/v0.6.0/gemini-3.8-flash-high/20261105/scoring-inputs.json) · JSON定位 /slots/38/group_diagnostic/dimensions/1/notes · SHA-256 9dd4ce0784879108bee0eb785a7197660268600117d98ed0be50f2a94b56d183。

### AHR01

Checked the retained source judgment and available candidate answer/artifacts. Only specific established false or unsupported commitments are appended; missing work alone receives no additional finding.

- **AHR01-claim-1 · material**：反例推断缺少非实际输出像条件，不是有效的普遍范围证据。 根因：invalid_counterexample_scope；已覆盖：none。
  [原审核证据](https://github.com/glenzli/math-gauge/blob/178e95c1e5ae690087c728c02c5258eeb8c4d608/results/v0.6.0/gemini-3.8-flash-high/20261105/scoring-inputs.json) · JSON定位 /slots/18/group_diagnostic/dimensions/2/notes · SHA-256 9dd4ce0784879108bee0eb785a7197660268600117d98ed0be50f2a94b56d183。

### AHR02

Checked the retained source judgment and available candidate answer/artifacts. Only specific established false or unsupported commitments are appended; missing work alone receives no additional finding.

- **AHR02-claim-1 · critical**：未识别采样可评估路径与所有路径的实质量词差异，却给原范围全对齐结论。 根因：all_path_quantifier；已覆盖：none。
  [原审核证据](https://github.com/glenzli/math-gauge/blob/178e95c1e5ae690087c728c02c5258eeb8c4d608/results/v0.6.0/gemini-3.8-flash-high/20261105/scoring-inputs.json) · JSON定位 /slots/19/group_diagnostic/dimensions/0/notes · SHA-256 9dd4ce0784879108bee0eb785a7197660268600117d98ed0be50f2a94b56d183。

### LCH02

Checked the retained source judgment and available candidate answer/artifacts. Only specific established false or unsupported commitments are appended; missing work alone receives no additional finding.

- **LCH02-claim-1 · material**：逐项自表宣称20/20完整，但原封卷源码缺D05要求的实际域合法性蕴含。编译成功不等于语义完成；不指控虚假编译。 根因：domain_legality；已覆盖：none。
  [原审核证据](https://github.com/glenzli/math-gauge/blob/178e95c1e5ae690087c728c02c5258eeb8c4d608/results/v0.6.0/gemini-3.8-flash-high/20261105/reviews/formalization.json) · JSON定位 /cases/1/obligations/4/notes · SHA-256 e46958c7cdd051ae8e5f681ec415fac17453b98ad60d90acfabd8ae2121d099f。

### HCH02

Checked the retained source judgment and available candidate answer/artifacts. Only specific established false or unsupported commitments are appended; missing work alone receives no additional finding.

- **HCH02-claim-1 · material**：逐项自表宣称40/40完整，但P16/P17仅证明独立路径权重和，未建立与实际复合矩阵的桥。两项同根只扣一次。 根因：path_matrix_bridge；已覆盖：none。
  [原审核证据](https://github.com/glenzli/math-gauge/blob/178e95c1e5ae690087c728c02c5258eeb8c4d608/results/v0.6.0/gemini-3.8-flash-high/20261105/reviews/formalization.json) · JSON定位 /cases/2/obligations/23/notes · SHA-256 e46958c7cdd051ae8e5f681ec415fac17453b98ad60d90acfabd8ae2121d099f。

### MG-BC001

Checked the retained source judgment and available candidate answer/artifacts. Only specific established false or unsupported commitments are appended; missing work alone receives no additional finding.

- **MG-BC001-claim-1 · material**：已正确识别正能隙背景错误，但独立给出错误的rank-one凸包断言。 根因：rank_one_hull；已覆盖：none。
  [原审核证据](https://github.com/glenzli/math-gauge/blob/178e95c1e5ae690087c728c02c5258eeb8c4d608/results/v0.6.0/gemini-3.8-flash-high/20261105/background-check/MG-BC001/source-review.json) · JSON定位 /summary · SHA-256 796538d4afe1b0daaba736b2858e6c4b37039c5c6433348ed9a6278b11278588。

- **MG-BC001-claim-2 · local**：既有评审核验的线性系统行列式计算错误；不将单纯构造证明未写全另行处罚。 根因：determinant_arithmetic；已覆盖：none。
  [原审核证据](https://github.com/glenzli/math-gauge/blob/178e95c1e5ae690087c728c02c5258eeb8c4d608/results/v0.6.0/gemini-3.8-flash-high/20261105/background-check/MG-BC001/source-review.json) · JSON定位 /summary · SHA-256 796538d4afe1b0daaba736b2858e6c4b37039c5c6433348ed9a6278b11278588。

### MG-BC002

Checked the retained source judgment and available candidate answer/artifacts. Only specific established false or unsupported commitments are appended; missing work alone receives no additional finding.

- **MG-BC002-claim-1 · local**：条件三点证书中的恒等式有明确一维反例，影响所写证明。实际prox存在性始终是条件论述，不按错误背景承诺处罚。 根因：prox_identity_sign；已覆盖：none。
  [原审核证据](https://github.com/glenzli/math-gauge/blob/178e95c1e5ae690087c728c02c5258eeb8c4d608/results/v0.6.0/gemini-3.8-flash-high/20261105/background-check/MG-BC002/source-review.json) · JSON定位 /criteria/3/judgment · SHA-256 c4946a7d9785602fe597b8f290bb72104812753dda83938d5e5cb76dd85e2f69。

### MG-PS001

原始数学评审94分不变；以下为当前RMC追加的具体错误承诺审核，未采用独立再评。

- **MG-PS001-claim-1 · material**：跨阈值断言遗漏阈值前增长；在原构造a=3,b=2中，n约为下一阈值的一半即可有二步比值趋于6，不能由声称的3控制。扣10%。
- **MG-PS001-claim-2 · local**：给定稀疏条件不能推出所写边界下界为正；实际构造递增，但原下界断言错误。独立根因扣5%。

[原始答卷](written-replacements/MG-PS001/answer.md) · [原94分审核](written-replacements/MG-PS001/source-review.json) · [当前承诺审核](claim-review-public-ps001.json)

## 允许非逻辑重跑：公开题错误承诺审核

| 任务 | MC题内比例 | RMC题内比例 | Strict | 新发现记录 | 整题最高0 |
|---|---:|---:|---|---:|---|
| MG-GP002 | 75.00 | 65.00 | 未通过 | 1 | 否 |
| MG-GR005 | 76.00 | 66.00 | 未通过 | 1 | 否 |
| MG-GR009 | 60.00 | 40.00 | 未通过 | 1 | 否 |
| MG-GR021 | 66.67 | 46.67 | 未通过 | 4 | 否 |
| MG-GR023 | 98.89 | 93.89 | 未通过 | 1 | 否 |
| MG-AR002 | 55.00 | 45.00 | 未通过 | 1 | 否 |
| MG-AR003 | 45.00 | 0.00 | 未通过 | 1 | 是 |
| MG-AR004 | 77.50 | 72.50 | 未通过 | 1 | 否 |
| AHR01 | 83.00 | 73.00 | 未通过 | 1 | 否 |
| AHR02 | 30.00 | 0.00 | 未通过 | 1 | 是 |
| LCH02 | 95.00 | 85.00 | 未通过 | 1 | 否 |
| HCH02 | 95.00 | 85.00 | 未通过 | 1 | 否 |
| MG-BC001 | 66.67 | 51.67 | 未通过 | 2 | 否 |
| MG-BC002 | 0.00 | -5.00 | 未通过 | 1 | 否 |
| MG-PS001 | 94.00 | 79.00 | 未通过 | 2 | 否 |

### MG-GP002

Checked the retained source judgment and available candidate answer/artifacts. Only specific established false or unsupported commitments are appended; missing work alone receives no additional finding.

- **MG-GP002-claim-1 · material**：具体反例否定所交统一常数，影响C^m证明；不是因证明较短扣分。 根因：wrong_uniform_constant；已覆盖：none。
  [原审核证据](https://github.com/glenzli/math-gauge/blob/178e95c1e5ae690087c728c02c5258eeb8c4d608/results/v0.6.0/gemini-3.8-flash-high/20261105/scoring-inputs.json) · JSON定位 /slots/26/group_diagnostic/stages/3/notes · SHA-256 9dd4ce0784879108bee0eb785a7197660268600117d98ed0be50f2a94b56d183。

### MG-GR005

Checked the retained source judgment and available candidate answer/artifacts. Only specific established false or unsupported commitments are appended; missing work alone receives no additional finding.

- **MG-GR005-claim-1 · material**：将完整允许竞争类缩为正规情形后宣布最大性证明；有保留原前提的反例。 根因：improper_competitor；已覆盖：none。
  [原审核证据](https://github.com/glenzli/math-gauge/blob/178e95c1e5ae690087c728c02c5258eeb8c4d608/results/v0.6.0/gemini-3.8-flash-high/20261105/scoring-inputs.json) · JSON定位 /slots/2/group_diagnostic/stages/3/math_review/notes · SHA-256 9dd4ce0784879108bee0eb785a7197660268600117d98ed0be50f2a94b56d183。

### MG-GR009

Checked the retained source judgment and available candidate answer/artifacts. Only specific established false or unsupported commitments are appended; missing work alone receives no additional finding.

- **MG-GR009-claim-1 · critical**：把基底满射这一充分条件提升为必要条件；具体平凡群例已反驳。 根因：false_necessity；已覆盖：none。
  [原审核证据](https://github.com/glenzli/math-gauge/blob/178e95c1e5ae690087c728c02c5258eeb8c4d608/results/v0.6.0/gemini-3.8-flash-high/20261105/scoring-inputs.json) · JSON定位 /slots/4/group_diagnostic/stages/5/notes · SHA-256 9dd4ce0784879108bee0eb785a7197660268600117d98ed0be50f2a94b56d183。

### MG-GR021

Checked the retained source judgment and available candidate answer/artifacts. Only specific established false or unsupported commitments are appended; missing work alone receives no additional finding.

原内嵌可靠性：5/10，数学贡献按(S−r)/90换算；来源判准未改。

- **MG-GR021-claim-1 · material**：明确的全称有限计数为假。 根因：finite_counts；已覆盖：none。
  [原审核证据](https://github.com/glenzli/math-gauge/blob/178e95c1e5ae690087c728c02c5258eeb8c4d608/results/v0.6.0/gemini-3.8-flash-high/20261105/scoring-inputs.json) · JSON定位 /slots/39/group_diagnostic/criteria/0/notes · SHA-256 9dd4ce0784879108bee0eb785a7197660268600117d98ed0be50f2a94b56d183。

- **MG-GR021-claim-2 · material**：实际固定类分类遗漏实质耦合，答卷自身合法例亦反驳其通式。 根因：fixed_classification；已覆盖：none。
  [原审核证据](https://github.com/glenzli/math-gauge/blob/178e95c1e5ae690087c728c02c5258eeb8c4d608/results/v0.6.0/gemini-3.8-flash-high/20261105/scoring-inputs.json) · JSON定位 /slots/39/group_diagnostic/criteria/1/notes · SHA-256 9dd4ce0784879108bee0eb785a7197660268600117d98ed0be50f2a94b56d183。

- **MG-GR021-claim-3 · material**：约化满射性有明确标量反例。 根因：reduction_surjectivity；已覆盖：none。
  [原审核证据](https://github.com/glenzli/math-gauge/blob/178e95c1e5ae690087c728c02c5258eeb8c4d608/results/v0.6.0/gemini-3.8-flash-high/20261105/scoring-inputs.json) · JSON定位 /slots/39/group_diagnostic/criteria/2/notes · SHA-256 9dd4ce0784879108bee0eb785a7197660268600117d98ed0be50f2a94b56d183。

- **MG-GR021-claim-4 · local**：此独立反号已由旧可靠性5分损失处理，不能再叠扣。 根因：cayley_sign；已覆盖：embedded_reliability。
  [原审核证据](https://github.com/glenzli/math-gauge/blob/178e95c1e5ae690087c728c02c5258eeb8c4d608/results/v0.6.0/gemini-3.8-flash-high/20261105/scoring-inputs.json) · JSON定位 /slots/39/group_diagnostic/criteria/4/notes · SHA-256 9dd4ce0784879108bee0eb785a7197660268600117d98ed0be50f2a94b56d183。

### MG-GR023

Checked the retained source judgment and available candidate answer/artifacts. Only specific established false or unsupported commitments are appended; missing work alone receives no additional finding.

原内嵌可靠性：10/10，数学贡献按(S−r)/90换算；来源判准未改。

- **MG-GR023-claim-1 · local**：延拓不唯一的局部断言与单点实例及本答卷正确计数矛盾；其他结构性成果保留。 根因：unique_extension；已覆盖：none。
  [原审核证据](https://github.com/glenzli/math-gauge/blob/178e95c1e5ae690087c728c02c5258eeb8c4d608/results/v0.6.0/gemini-3.8-flash-high/20261105/scoring-inputs.json) · JSON定位 /slots/41/group_diagnostic/criteria/0/notes · SHA-256 9dd4ce0784879108bee0eb785a7197660268600117d98ed0be50f2a94b56d183。

### MG-AR002

Checked the retained source judgment and available candidate answer/artifacts. Only specific established false or unsupported commitments are appended; missing work alone receives no additional finding.

- **MG-AR002-claim-1 · material**：明确认可错误的仿射/线性补充路线；原正文另有有效证明，按非核心放行扣10%，不整题封顶。 根因：affine_supplement；已覆盖：none。
  [原审核证据](https://github.com/glenzli/math-gauge/blob/178e95c1e5ae690087c728c02c5258eeb8c4d608/results/v0.6.0/gemini-3.8-flash-high/20261105/scoring-inputs.json) · JSON定位 /slots/36/group_diagnostic/dimensions/0/notes · SHA-256 9dd4ce0784879108bee0eb785a7197660268600117d98ed0be50f2a94b56d183。

### MG-AR003

Checked the retained source judgment and available candidate answer/artifacts. Only specific established false or unsupported commitments are appended; missing work alone receives no additional finding.

- **MG-AR003-claim-1 · critical**：明确放行使被审核心识别论证失效的假断言。RMC整题最高0；MC保留其余有效审阅。 根因：fixed_target_image；已覆盖：none。
  [原审核证据](https://github.com/glenzli/math-gauge/blob/178e95c1e5ae690087c728c02c5258eeb8c4d608/results/v0.6.0/gemini-3.8-flash-high/20261105/scoring-inputs.json) · JSON定位 /slots/37/group_diagnostic/major_error_notes · SHA-256 9dd4ce0784879108bee0eb785a7197660268600117d98ed0be50f2a94b56d183。

### MG-AR004

Checked the retained source judgment and available candidate answer/artifacts. Only specific established false or unsupported commitments are appended; missing work alone receives no additional finding.

- **MG-AR004-claim-1 · local**：原条件被误删并扩大局部化结论的适用范围；已正确识别主证核心错误，不列核心错误放行。 根因：localization_scope；已覆盖：none。
  [原审核证据](https://github.com/glenzli/math-gauge/blob/178e95c1e5ae690087c728c02c5258eeb8c4d608/results/v0.6.0/gemini-3.8-flash-high/20261105/scoring-inputs.json) · JSON定位 /slots/38/group_diagnostic/dimensions/1/notes · SHA-256 9dd4ce0784879108bee0eb785a7197660268600117d98ed0be50f2a94b56d183。

### AHR01

Checked the retained source judgment and available candidate answer/artifacts. Only specific established false or unsupported commitments are appended; missing work alone receives no additional finding.

- **AHR01-claim-1 · material**：反例推断缺少非实际输出像条件，不是有效的普遍范围证据。 根因：invalid_counterexample_scope；已覆盖：none。
  [原审核证据](https://github.com/glenzli/math-gauge/blob/178e95c1e5ae690087c728c02c5258eeb8c4d608/results/v0.6.0/gemini-3.8-flash-high/20261105/scoring-inputs.json) · JSON定位 /slots/18/group_diagnostic/dimensions/2/notes · SHA-256 9dd4ce0784879108bee0eb785a7197660268600117d98ed0be50f2a94b56d183。

### AHR02

Checked the retained source judgment and available candidate answer/artifacts. Only specific established false or unsupported commitments are appended; missing work alone receives no additional finding.

- **AHR02-claim-1 · critical**：未识别采样可评估路径与所有路径的实质量词差异，却给原范围全对齐结论。 根因：all_path_quantifier；已覆盖：none。
  [原审核证据](https://github.com/glenzli/math-gauge/blob/178e95c1e5ae690087c728c02c5258eeb8c4d608/results/v0.6.0/gemini-3.8-flash-high/20261105/scoring-inputs.json) · JSON定位 /slots/19/group_diagnostic/dimensions/0/notes · SHA-256 9dd4ce0784879108bee0eb785a7197660268600117d98ed0be50f2a94b56d183。

### LCH02

Checked the retained source judgment and available candidate answer/artifacts. Only specific established false or unsupported commitments are appended; missing work alone receives no additional finding.

- **LCH02-claim-1 · material**：逐项自表宣称20/20完整，但原封卷源码缺D05要求的实际域合法性蕴含。编译成功不等于语义完成；不指控虚假编译。 根因：domain_legality；已覆盖：none。
  [原审核证据](https://github.com/glenzli/math-gauge/blob/178e95c1e5ae690087c728c02c5258eeb8c4d608/results/v0.6.0/gemini-3.8-flash-high/20261105/reviews/formalization.json) · JSON定位 /cases/1/obligations/4/notes · SHA-256 e46958c7cdd051ae8e5f681ec415fac17453b98ad60d90acfabd8ae2121d099f。

### HCH02

Checked the retained source judgment and available candidate answer/artifacts. Only specific established false or unsupported commitments are appended; missing work alone receives no additional finding.

- **HCH02-claim-1 · material**：逐项自表宣称40/40完整，但P16/P17仅证明独立路径权重和，未建立与实际复合矩阵的桥。两项同根只扣一次。 根因：path_matrix_bridge；已覆盖：none。
  [原审核证据](https://github.com/glenzli/math-gauge/blob/178e95c1e5ae690087c728c02c5258eeb8c4d608/results/v0.6.0/gemini-3.8-flash-high/20261105/reviews/formalization.json) · JSON定位 /cases/2/obligations/23/notes · SHA-256 e46958c7cdd051ae8e5f681ec415fac17453b98ad60d90acfabd8ae2121d099f。

### MG-BC001

Checked the retained source judgment and available candidate answer/artifacts. Only specific established false or unsupported commitments are appended; missing work alone receives no additional finding.

- **MG-BC001-claim-1 · material**：已正确识别正能隙背景错误，但独立给出错误的rank-one凸包断言。 根因：rank_one_hull；已覆盖：none。
  [原审核证据](https://github.com/glenzli/math-gauge/blob/178e95c1e5ae690087c728c02c5258eeb8c4d608/results/v0.6.0/gemini-3.8-flash-high/20261105/background-check/MG-BC001/source-review.json) · JSON定位 /summary · SHA-256 796538d4afe1b0daaba736b2858e6c4b37039c5c6433348ed9a6278b11278588。

- **MG-BC001-claim-2 · local**：既有评审核验的线性系统行列式计算错误；不将单纯构造证明未写全另行处罚。 根因：determinant_arithmetic；已覆盖：none。
  [原审核证据](https://github.com/glenzli/math-gauge/blob/178e95c1e5ae690087c728c02c5258eeb8c4d608/results/v0.6.0/gemini-3.8-flash-high/20261105/background-check/MG-BC001/source-review.json) · JSON定位 /summary · SHA-256 796538d4afe1b0daaba736b2858e6c4b37039c5c6433348ed9a6278b11278588。

### MG-BC002

Checked the retained source judgment and available candidate answer/artifacts. Only specific established false or unsupported commitments are appended; missing work alone receives no additional finding.

- **MG-BC002-claim-1 · local**：条件三点证书中的恒等式有明确一维反例，影响所写证明。实际prox存在性始终是条件论述，不按错误背景承诺处罚。 根因：prox_identity_sign；已覆盖：none。
  [原审核证据](https://github.com/glenzli/math-gauge/blob/178e95c1e5ae690087c728c02c5258eeb8c4d608/results/v0.6.0/gemini-3.8-flash-high/20261105/background-check/MG-BC002/source-review.json) · JSON定位 /criteria/3/judgment · SHA-256 c4946a7d9785602fe597b8f290bb72104812753dda83938d5e5cb76dd85e2f69。

### MG-PS001

原始数学评审94分不变；以下为当前RMC追加的具体错误承诺审核，未采用独立再评。

- **MG-PS001-claim-1 · material**：跨阈值断言遗漏阈值前增长；在原构造a=3,b=2中，n约为下一阈值的一半即可有二步比值趋于6，不能由声称的3控制。扣10%。
- **MG-PS001-claim-2 · local**：给定稀疏条件不能推出所写边界下界为正；实际构造递增，但原下界断言错误。独立根因扣5%。

[原始答卷](written-replacements/MG-PS001/answer.md) · [原94分审核](written-replacements/MG-PS001/source-review.json) · [当前承诺审核](claim-review-public-ps001.json)

## 记录边界

原题、原返回、自评、原数学审核、实际编译及执行身份不变。新审核只在已有证据范围追加归类，AI判断不等于人审批准；未测与系统故障不凭空记数学错误。公开报告不包含私有题号或逐题资料。

[档案](record.json) · [当前摘要](README.md)
