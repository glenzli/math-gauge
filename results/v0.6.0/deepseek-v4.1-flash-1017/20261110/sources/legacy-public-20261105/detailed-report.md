# DeepSeek v4.1 Flash 1017 · 当前固定记录

benchmark0.6.0开发草稿；聚合0.8.0／MC0.2.0／Strict0.2.0，承诺扣罚组件0.1.0，选题组件0.3.0、书面替换组件0.1.0。AI审核、人审待定，正式比较资格false，未发布release。

三种分数共用34题（公24／私10）、30个数学家族及书面35／Lean35／研究30权重，另固定三轮Lean自查。已建90／100，研究稿完善10分待建；不将已建部分或已测部分重新归一化。

| 条件 | MC | RMC（默认） | Strict |
|---|---:|---:|---:|
| 首次 | 45.15 | 39.40 | 19.17 |
| 允许非逻辑重跑 | 48.07 | 41.48 | 19.17 |

箭头表示首次→允许计次非逻辑重跑；相同只列一次。DeepSeek另10道研究题、1道新增私有书面题及PS001未测，保持未知及固定分母。GR103旧成绩不回填PS001；已确认贡献降低不代表新增数学失败。题包待建10分另列。

PS001按用户选择替换公开GR103，仍为8公／4私书面论证、12家族等权。Gemini只采用原始A1原评94/100、Strict不通过；独立再评不进入当前留档。Terra新Max A1为100/100、Strict通过，用时430.738秒，工具开放、实际0次命令；单射段的局部引用错误单独记录。DeepSeek留待后测，记unknown。GR103原答、原审核和冻结计划保留为历史来源，不再进入当前聚合。

Gemini的94分原评保持原字节。现行RMC对跨阈值迭代中的错误断言扣10%，对边界下界被错误断言为正扣5%；两个独立根因共扣15%，不使用核心放行封顶。Terra的全部参数构造有效；已证像集密度为1使缺失坐标的均值趋零，单射段重复不等式方向的连接语按冻结规则列为局部引用笔误，不另扣分。

所有正式测试允许本地工具与预置公共依赖，禁止联网检索和工具联网；模型服务与认证连接另记。允许与实际使用分别记录。纯系统故障不占有效尝试，输出耗尽仍占一次；数学错误不能重跑。本次没有Lean重编译，冻结旧输入、原答、自评和0.4.0审核不改写。

[原答与证据](record.json) · [当前承诺审核](claim-review-public-ps001.json) · [PS001来源](written-replacement-evidence.json)

## 六视图及分类贡献

| 子类 | MC首次 | MC重跑 | RMC首次 | RMC重跑 | Strict首次 | Strict重跑 |
|---|---:|---:|---:|---:|---:|---:|
| 书面论证 | 14.11 | 17.03 | 12.55 | 14.64 | 4.17 | 4.17 |
| 论证审阅 | 5.56 | 5.56 | 4.38 | 4.38 | 0.00 | 0.00 |
| 语义审计 | 9.19 | 9.19 | 8.94 | 8.94 | 7.50 | 7.50 |
| 形式化 | 14.18 | 14.18 | 13.43 | 13.43 | 7.50 | 7.50 |
| 对齐自查 | 2.10 | 2.10 | 0.10 | 0.10 | 0.00 | 0.00 |
| 背景核查 | 0.00 | 0.00 | 0.00 | 0.00 | 0.00 | 0.00 |
| 研究稿完善 | 建设中 | 建设中 | 建设中 | 建设中 | 建设中 | 建设中 |
| 命题拓展 | 0.00 | 0.00 | 0.00 | 0.00 | 0.00 | 0.00 |

## 首次：公开题错误承诺审核

| 任务 | MC题内比例 | RMC题内比例 | Strict | 新发现记录 | 整题最高0 |
|---|---:|---:|---|---:|---|
| MG-C003 | 89.13 | 79.13 | 未通过 | 1 | 否 |
| MG-GP001 | 85.00 | 75.00 | 未通过 | 1 | 否 |
| MG-GP002 | 85.00 | 75.00 | 未通过 | 1 | 否 |
| MG-GR005 | 85.00 | 75.00 | 未通过 | 1 | 否 |
| MG-GR009 | 70.00 | 60.00 | 未通过 | 1 | 否 |
| MG-AR001 | 87.50 | 82.50 | 未通过 | 1 | 否 |
| MG-AR002 | 55.00 | 45.00 | 未通过 | 1 | 否 |
| MG-AR003 | 27.50 | 0.00 | 未通过 | 1 | 是 |
| MG-AR004 | 52.50 | 47.50 | 未通过 | 1 | 否 |
| AHR02 | 67.50 | 57.50 | 未通过 | 1 | 否 |

### MG-C003

Checked the retained source judgment and available candidate answer/artifacts. Only specific established false or unsupported commitments are appended; missing work alone receives no additional finding.

- **MG-C003-claim-1 · material**：初答逐项自表宣称92项完成，封卷工程仅82项核实对应，包括任意目标域被弱化。此处只计A1，不重复使用后续三轮误报。 根因：all_obligations_claim；已覆盖：none。
  [原审核证据](https://github.com/glenzli/math-gauge/blob/178e95c1e5ae690087c728c02c5258eeb8c4d608/results/v0.6.0/deepseek-v4.1-flash-1017/20261105/scoring-inputs.json) · JSON定位 /slots/0/group_diagnostic/stages/24/notes · SHA-256 7c99ee545e582dd77f33ce5ad4bd4b6c13aa8ea32df288371d27e22155cf5b7a。

### MG-GP001

Checked the retained source judgment and available candidate answer/artifacts. Only specific established false or unsupported commitments are appended; missing work alone receives no additional finding.

- **MG-GP001-claim-1 · material**：以非紧的去顶点空间与紧闭锥同胚作为证明依据；同根的后续错误符号不重复处罚。 根因：suspension_homeomorphism；已覆盖：none。
  [原审核证据](https://github.com/glenzli/math-gauge/blob/178e95c1e5ae690087c728c02c5258eeb8c4d608/results/v0.6.0/deepseek-v4.1-flash-1017/20261105/reviews/MG-GP001.json) · JSON定位 /entries/0/stage_notes/S3 · SHA-256 9103c3dd4b76f842731bc6f288cc0e3071d0aca3866df02ceb944f65ace66306。

### MG-GP002

Checked the retained source judgment and available candidate answer/artifacts. Only specific established false or unsupported commitments are appended; missing work alone receives no additional finding.

- **MG-GP002-claim-1 · material**：所写全称整频率长度界被N=1,k=(1,1)反驳，影响当前尾估计证明。 根因：fourier_tail_length；已覆盖：none。
  [原审核证据](https://github.com/glenzli/math-gauge/blob/178e95c1e5ae690087c728c02c5258eeb8c4d608/results/v0.6.0/deepseek-v4.1-flash-1017/20261105/reviews/MG-GP002.json) · JSON定位 /entries/0/stage_notes/S2 · SHA-256 1109919480218bfbac14292afae2f37193529a332afb8d52d559f805b787de64。

### MG-GR005

Checked the retained source judgment and available candidate answer/artifacts. Only specific established false or unsupported commitments are appended; missing work alone receives no additional finding.

- **MG-GR005-claim-1 · material**：将上图投影闭误作省略闭包的必要条件，有显式exp(y)反例。 根因：closed_projection_necessity；已覆盖：none。
  [原审核证据](https://github.com/glenzli/math-gauge/blob/178e95c1e5ae690087c728c02c5258eeb8c4d608/results/v0.6.0/deepseek-v4.1-flash-1017/20261105/reviews/MG-GR005.json) · JSON定位 /entries/0/stage_notes/S6 · SHA-256 1af76dbe7aa740e62aa6c8e294423bf9a7d81edc668fc8a5ed4c8ecce93da90b。

### MG-GR009

Checked the retained source judgment and available candidate answer/artifacts. Only specific established false or unsupported commitments are appended; missing work alone receives no additional finding.

- **MG-GR009-claim-1 · material**：混淆保留实现识别与遗忘识别后的自同构群；不是仅缺分类证明。 根因：marked_groupoid；已覆盖：none。
  [原审核证据](https://github.com/glenzli/math-gauge/blob/178e95c1e5ae690087c728c02c5258eeb8c4d608/results/v0.6.0/deepseek-v4.1-flash-1017/20261105/reviews/MG-GR009.json) · JSON定位 /entries/0/stage_notes/S3 · SHA-256 a36b066a0d5e7b1e0bb345e9904e83ace96a13f595e0cd4f91f6684e5c7a31a3。

### MG-AR001

Checked the retained source judgment and available candidate answer/artifacts. Only specific established false or unsupported commitments are appended; missing work alone receives no additional finding.

- **MG-AR001-claim-1 · local**：误判局部表格方向并增添原题未要求的证明义务；未否定核心有效反例，不作核心放行封顶。 根因：table_direction；已覆盖：none。
  [原审核证据](https://github.com/glenzli/math-gauge/blob/178e95c1e5ae690087c728c02c5258eeb8c4d608/results/v0.6.0/deepseek-v4.1-flash-1017/20261105/reviews/MG-AR001.json) · JSON定位 /entries/0/note · SHA-256 3521f15cfe6754153b7ac63610c363289c32bff2db0d0377fa38a90c4fd022cf。

### MG-AR002

Checked the retained source judgment and available candidate answer/artifacts. Only specific established false or unsupported commitments are appended; missing work alone receives no additional finding.

- **MG-AR002-claim-1 · material**：把错误仿射/线性附加路线作为有效冗余论证放行，未限制其影响；主结论另有有效证明，不作整题零分封顶。 根因：affine_supplement；已覆盖：none。
  [原审核证据](https://github.com/glenzli/math-gauge/blob/178e95c1e5ae690087c728c02c5258eeb8c4d608/results/v0.6.0/deepseek-v4.1-flash-1017/20261105/reviews/MG-AR002.json) · JSON定位 /entries/0/note · SHA-256 3897ec3dc6292a6465b3ff31588c4278d1eda28e6f8599eab5ce0bf6f47cead8。

### MG-AR003

Checked the retained source judgment and available candidate answer/artifacts. Only specific established false or unsupported commitments are appended; missing work alone receives no additional finding.

- **MG-AR003-claim-1 · critical**：除漏核心固定Y错误外，还以假的拓扑连续性理由否定有效方向，影响核心审阅结论。 根因：fixed_target_topology；已覆盖：none。
  [原审核证据](https://github.com/glenzli/math-gauge/blob/178e95c1e5ae690087c728c02c5258eeb8c4d608/results/v0.6.0/deepseek-v4.1-flash-1017/20261105/reviews/MG-AR003.json) · JSON定位 /entries/0/note · SHA-256 4fe193650d43fc8b8cf722447c3a8cbfd519a33be95d55e8da3bbf7b6134cf5f。

### MG-AR004

Checked the retained source judgment and available candidate answer/artifacts. Only specific established false or unsupported commitments are appended; missing work alone receives no additional finding.

- **MG-AR004-claim-1 · local**：误删被审材料的维数前提并扩大引用范围；正确定位主证缺口的工作保留。 根因：source_hypothesis；已覆盖：none。
  [原审核证据](https://github.com/glenzli/math-gauge/blob/178e95c1e5ae690087c728c02c5258eeb8c4d608/results/v0.6.0/deepseek-v4.1-flash-1017/20261105/reviews/MG-AR004.json) · JSON定位 /entries/0/note · SHA-256 589c09300e7be24ea271e8ff839701e9d2b45d7bc826eb1c0ce3076618dfe6f1。

### AHR02

Checked the retained source judgment and available candidate answer/artifacts. Only specific established false or unsupported commitments are appended; missing work alone receives no additional finding.

- **AHR02-claim-1 · material**：正文已准确指出全路径前提并给合法量词修复，不能仅因开头完整一词判核心放行；但结尾仍将实质范围损失概括成无数学缺口，按范围不一致扣10%。 根因：all_path_quantifier；已覆盖：none。
  [原审核证据](https://github.com/glenzli/math-gauge/blob/178e95c1e5ae690087c728c02c5258eeb8c4d608/results/v0.6.0/deepseek-v4.1-flash-1017/20261105/reviews/AHR02.json) · JSON定位 /entries/0/note · SHA-256 daab1090f50d4f55da73b5aafc8ac6daebdc2a9cdd930bf67aeecc1435076c01。

## 允许非逻辑重跑：公开题错误承诺审核

| 任务 | MC题内比例 | RMC题内比例 | Strict | 新发现记录 | 整题最高0 |
|---|---:|---:|---|---:|---|
| MG-C003 | 89.13 | 79.13 | 未通过 | 1 | 否 |
| MG-GP001 | 85.00 | 75.00 | 未通过 | 1 | 否 |
| MG-GP002 | 85.00 | 75.00 | 未通过 | 1 | 否 |
| MG-GR005 | 85.00 | 75.00 | 未通过 | 1 | 否 |
| MG-GR009 | 70.00 | 60.00 | 未通过 | 1 | 否 |
| MG-GR021 | 52.78 | 32.78 | 未通过 | 3 | 否 |
| MG-GR023 | 87.22 | 67.22 | 未通过 | 3 | 否 |
| MG-AR001 | 87.50 | 82.50 | 未通过 | 1 | 否 |
| MG-AR002 | 55.00 | 45.00 | 未通过 | 1 | 否 |
| MG-AR003 | 27.50 | 0.00 | 未通过 | 1 | 是 |
| MG-AR004 | 52.50 | 47.50 | 未通过 | 1 | 否 |
| AHR02 | 67.50 | 57.50 | 未通过 | 1 | 否 |

### MG-C003

Checked the retained source judgment and available candidate answer/artifacts. Only specific established false or unsupported commitments are appended; missing work alone receives no additional finding.

- **MG-C003-claim-1 · material**：初答逐项自表宣称92项完成，封卷工程仅82项核实对应，包括任意目标域被弱化。此处只计A1，不重复使用后续三轮误报。 根因：all_obligations_claim；已覆盖：none。
  [原审核证据](https://github.com/glenzli/math-gauge/blob/178e95c1e5ae690087c728c02c5258eeb8c4d608/results/v0.6.0/deepseek-v4.1-flash-1017/20261105/retry-scoring-inputs.json) · JSON定位 /slots/0/group_diagnostic/stages/24/notes · SHA-256 10c1ed91de8be61cb8e7cf34425648c0c652eeb21c9b12b123e5329c8f6bae82。

### MG-GP001

Checked the retained source judgment and available candidate answer/artifacts. Only specific established false or unsupported commitments are appended; missing work alone receives no additional finding.

- **MG-GP001-claim-1 · material**：以非紧的去顶点空间与紧闭锥同胚作为证明依据；同根的后续错误符号不重复处罚。 根因：suspension_homeomorphism；已覆盖：none。
  [原审核证据](https://github.com/glenzli/math-gauge/blob/178e95c1e5ae690087c728c02c5258eeb8c4d608/results/v0.6.0/deepseek-v4.1-flash-1017/20261105/reviews/MG-GP001.json) · JSON定位 /entries/0/stage_notes/S3 · SHA-256 9103c3dd4b76f842731bc6f288cc0e3071d0aca3866df02ceb944f65ace66306。

### MG-GP002

Checked the retained source judgment and available candidate answer/artifacts. Only specific established false or unsupported commitments are appended; missing work alone receives no additional finding.

- **MG-GP002-claim-1 · material**：所写全称整频率长度界被N=1,k=(1,1)反驳，影响当前尾估计证明。 根因：fourier_tail_length；已覆盖：none。
  [原审核证据](https://github.com/glenzli/math-gauge/blob/178e95c1e5ae690087c728c02c5258eeb8c4d608/results/v0.6.0/deepseek-v4.1-flash-1017/20261105/reviews/MG-GP002.json) · JSON定位 /entries/0/stage_notes/S2 · SHA-256 1109919480218bfbac14292afae2f37193529a332afb8d52d559f805b787de64。

### MG-GR005

Checked the retained source judgment and available candidate answer/artifacts. Only specific established false or unsupported commitments are appended; missing work alone receives no additional finding.

- **MG-GR005-claim-1 · material**：将上图投影闭误作省略闭包的必要条件，有显式exp(y)反例。 根因：closed_projection_necessity；已覆盖：none。
  [原审核证据](https://github.com/glenzli/math-gauge/blob/178e95c1e5ae690087c728c02c5258eeb8c4d608/results/v0.6.0/deepseek-v4.1-flash-1017/20261105/reviews/MG-GR005.json) · JSON定位 /entries/0/stage_notes/S6 · SHA-256 1af76dbe7aa740e62aa6c8e294423bf9a7d81edc668fc8a5ed4c8ecce93da90b。

### MG-GR009

Checked the retained source judgment and available candidate answer/artifacts. Only specific established false or unsupported commitments are appended; missing work alone receives no additional finding.

- **MG-GR009-claim-1 · material**：混淆保留实现识别与遗忘识别后的自同构群；不是仅缺分类证明。 根因：marked_groupoid；已覆盖：none。
  [原审核证据](https://github.com/glenzli/math-gauge/blob/178e95c1e5ae690087c728c02c5258eeb8c4d608/results/v0.6.0/deepseek-v4.1-flash-1017/20261105/reviews/MG-GR009.json) · JSON定位 /entries/0/stage_notes/S3 · SHA-256 a36b066a0d5e7b1e0bb345e9904e83ace96a13f595e0cd4f91f6684e5c7a31a3。

### MG-GR021

Checked the retained source judgment and available candidate answer/artifacts. Only specific established false or unsupported commitments are appended; missing work alone receives no additional finding.

原内嵌可靠性：0/10，数学贡献按(S−r)/90换算；来源判准未改。

- **MG-GR021-claim-1 · material**：独立实际解集无限性断言为假，旧可靠性0/10已承担10分，不能再加一次。 根因：infinite_solution_set；已覆盖：embedded_reliability。
  [原审核证据](https://github.com/glenzli/math-gauge/blob/178e95c1e5ae690087c728c02c5258eeb8c4d608/results/v0.6.0/deepseek-v4.1-flash-1017/20261105/retry-scoring-inputs.json) · JSON定位 /slots/12/group_diagnostic/criteria/4/checks/0/reason · SHA-256 10c1ed91de8be61cb8e7cf34425648c0c652eeb21c9b12b123e5329c8f6bae82。

- **MG-GR021-claim-2 · material**：明确的有限计数通式被列举的小维度实例反驳。 根因：finite_counts；已覆盖：none。
  [原审核证据](https://github.com/glenzli/math-gauge/blob/178e95c1e5ae690087c728c02c5258eeb8c4d608/results/v0.6.0/deepseek-v4.1-flash-1017/20261105/retry-scoring-inputs.json) · JSON定位 /slots/12/group_diagnostic/criteria/0/checks/1/reason · SHA-256 10c1ed91de8be61cb8e7cf34425648c0c652eeb21c9b12b123e5329c8f6bae82。

- **MG-GR021-claim-3 · material**：M=2的实际反例矩阵分母奇异，不能交付为有效锐性构造。 根因：undefined_cayley_witness；已覆盖：none。
  [原审核证据](https://github.com/glenzli/math-gauge/blob/178e95c1e5ae690087c728c02c5258eeb8c4d608/results/v0.6.0/deepseek-v4.1-flash-1017/20261105/retry-scoring-inputs.json) · JSON定位 /slots/12/group_diagnostic/criteria/3/checks/1/reason · SHA-256 10c1ed91de8be61cb8e7cf34425648c0c652eeb21c9b12b123e5329c8f6bae82。

### MG-GR023

Checked the retained source judgment and available candidate answer/artifacts. Only specific established false or unsupported commitments are appended; missing work alone receives no additional finding.

原内嵌可靠性：10/10，数学贡献按(S−r)/90换算；来源判准未改。

- **MG-GR023-claim-1 · material**：把重叠集合当成分划用于交封闭证明；不是按证明路线扣分。 根因：false_partition；已覆盖：none。
  [原审核证据](https://github.com/glenzli/math-gauge/blob/178e95c1e5ae690087c728c02c5258eeb8c4d608/results/v0.6.0/deepseek-v4.1-flash-1017/20261105/retry-scoring-inputs.json) · JSON定位 /slots/14/group_diagnostic/criteria/0/checks/2/reason · SHA-256 10c1ed91de8be61cb8e7cf34425648c0c652eeb21c9b12b123e5329c8f6bae82。

- **MG-GR023-claim-2 · material**：同一必答计数范围内明确给出错误的有限公式。 根因：finite_binary_count；已覆盖：none。
  [原审核证据](https://github.com/glenzli/math-gauge/blob/178e95c1e5ae690087c728c02c5258eeb8c4d608/results/v0.6.0/deepseek-v4.1-flash-1017/20261105/retry-scoring-inputs.json) · JSON定位 /slots/14/group_diagnostic/criteria/0/checks/4/reason · SHA-256 10c1ed91de8be61cb8e7cf34425648c0c652eeb21c9b12b123e5329c8f6bae82。

- **MG-GR023-claim-3 · material**：在已包含对角补集的完整超滤子上声称可加入对角；所交双耦合反例不成立。 根因：diagonal_coupling；已覆盖：none。
  [原审核证据](https://github.com/glenzli/math-gauge/blob/178e95c1e5ae690087c728c02c5258eeb8c4d608/results/v0.6.0/deepseek-v4.1-flash-1017/20261105/retry-scoring-inputs.json) · JSON定位 /slots/14/group_diagnostic/criteria/3/checks/3/reason · SHA-256 10c1ed91de8be61cb8e7cf34425648c0c652eeb21c9b12b123e5329c8f6bae82。

### MG-AR001

Checked the retained source judgment and available candidate answer/artifacts. Only specific established false or unsupported commitments are appended; missing work alone receives no additional finding.

- **MG-AR001-claim-1 · local**：误判局部表格方向并增添原题未要求的证明义务；未否定核心有效反例，不作核心放行封顶。 根因：table_direction；已覆盖：none。
  [原审核证据](https://github.com/glenzli/math-gauge/blob/178e95c1e5ae690087c728c02c5258eeb8c4d608/results/v0.6.0/deepseek-v4.1-flash-1017/20261105/reviews/MG-AR001.json) · JSON定位 /entries/0/note · SHA-256 3521f15cfe6754153b7ac63610c363289c32bff2db0d0377fa38a90c4fd022cf。

### MG-AR002

Checked the retained source judgment and available candidate answer/artifacts. Only specific established false or unsupported commitments are appended; missing work alone receives no additional finding.

- **MG-AR002-claim-1 · material**：把错误仿射/线性附加路线作为有效冗余论证放行，未限制其影响；主结论另有有效证明，不作整题零分封顶。 根因：affine_supplement；已覆盖：none。
  [原审核证据](https://github.com/glenzli/math-gauge/blob/178e95c1e5ae690087c728c02c5258eeb8c4d608/results/v0.6.0/deepseek-v4.1-flash-1017/20261105/reviews/MG-AR002.json) · JSON定位 /entries/0/note · SHA-256 3897ec3dc6292a6465b3ff31588c4278d1eda28e6f8599eab5ce0bf6f47cead8。

### MG-AR003

Checked the retained source judgment and available candidate answer/artifacts. Only specific established false or unsupported commitments are appended; missing work alone receives no additional finding.

- **MG-AR003-claim-1 · critical**：除漏核心固定Y错误外，还以假的拓扑连续性理由否定有效方向，影响核心审阅结论。 根因：fixed_target_topology；已覆盖：none。
  [原审核证据](https://github.com/glenzli/math-gauge/blob/178e95c1e5ae690087c728c02c5258eeb8c4d608/results/v0.6.0/deepseek-v4.1-flash-1017/20261105/reviews/MG-AR003.json) · JSON定位 /entries/0/note · SHA-256 4fe193650d43fc8b8cf722447c3a8cbfd519a33be95d55e8da3bbf7b6134cf5f。

### MG-AR004

Checked the retained source judgment and available candidate answer/artifacts. Only specific established false or unsupported commitments are appended; missing work alone receives no additional finding.

- **MG-AR004-claim-1 · local**：误删被审材料的维数前提并扩大引用范围；正确定位主证缺口的工作保留。 根因：source_hypothesis；已覆盖：none。
  [原审核证据](https://github.com/glenzli/math-gauge/blob/178e95c1e5ae690087c728c02c5258eeb8c4d608/results/v0.6.0/deepseek-v4.1-flash-1017/20261105/reviews/MG-AR004.json) · JSON定位 /entries/0/note · SHA-256 589c09300e7be24ea271e8ff839701e9d2b45d7bc826eb1c0ce3076618dfe6f1。

### AHR02

Checked the retained source judgment and available candidate answer/artifacts. Only specific established false or unsupported commitments are appended; missing work alone receives no additional finding.

- **AHR02-claim-1 · material**：正文已准确指出全路径前提并给合法量词修复，不能仅因开头完整一词判核心放行；但结尾仍将实质范围损失概括成无数学缺口，按范围不一致扣10%。 根因：all_path_quantifier；已覆盖：none。
  [原审核证据](https://github.com/glenzli/math-gauge/blob/178e95c1e5ae690087c728c02c5258eeb8c4d608/results/v0.6.0/deepseek-v4.1-flash-1017/20261105/reviews/AHR02.json) · JSON定位 /entries/0/note · SHA-256 daab1090f50d4f55da73b5aafc8ac6daebdc2a9cdd930bf67aeecc1435076c01。

## 记录边界

原题、原返回、自评、原数学审核、实际编译及执行身份不变。新审核只在已有证据范围追加归类，AI判断不等于人审批准；未测与系统故障不凭空记数学错误。公开报告不包含私有题号或逐题资料。

[档案](record.json) · [当前摘要](README.md)
