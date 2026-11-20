# 开放研究能力 0.1.0

本组件为评分版1.2.0的数学画像增加独立的“开放研究能力”（Open research capability）。它评价在题目明确要求开展开放数学工作时，模型实际交出了什么；“研究主动性”（Research initiative）则观察未被要求时是否自行展开。两者不互相换算，不改变MC、RMC、SMC或既有七轴裁定，不新增候选调用。评审依据是既有原答；方法为观察后制定的AI评审，人工数学审核待完成。

## 共同机会与范围

先核查全部15道研究题的实际题面。六道命题题要求证明固定结论，四道背景题要求完成具体核查、计算及方法判断；它们没有给所有模型相同的开放研究请求。完成这些任务后停止，不构成开放研究能力失败。其自发拓展保留在研究主动性和原有研究记录中，不给新轴增加分数。

新轴采用共同的五个数学手稿家族：一道公开、四道私有，固定等权。它们明确要求从给定想法发展定义、理论、条件、证明及适用边界。所有模型使用相同机会、任务级目标及验收尺度；不会因为某个模型写了更多附加理论，就给其他模型新增必需目标。这个值描述五个已有开放任务上的表现，不推断未测试领域的研究上限。

## 数学验收

每题独立审查四个方面，并分别记录原文依据：

1. **问题组织与建模**：将给定想法组织为可研究的问题，明确对象、定义、量词、结构和任务目标，并保持原问题或建立合法表示桥。
2. **实质机制**：构造或识别真正支撑结果的数学机制，建立有用的定理、反例或明确的不可能性；不能用定义重述、例子罗列或未经证明的设想代替。
3. **自然条件与边界**：说明结果为何在所给条件下成立，处理必要的退化情形、作用域和障碍；正确反驳过强愿望并给出有据的条件化修复也可完成任务。
4. **可用成果与证明**：实际交付的核心理论、依赖及返回桥完整闭合，读者能在明确范围内使用。已有标准结果可以使用，但须核对实际前提及适用结论。

四方面是验收证据，不是四个可互相抵补的分数。逐题取同时满足的最高档：

| 档 | 标准 |
|---|---|
| 0 | 没有可核实的相关研究进展，或已结算为空白且无可采纳原内容。 |
| 1 | 有正确的局部定义、例子或准备性结论，但尚未建立任务的关键研究机制。 |
| 2 | 已建立有用的实质机制或独立结果，但仍有不可省的核心问题、分支、依赖、条件或表示桥未成立；核心范围漂移而无桥也最多为本档。 |
| 3 | 原请求的核心研究机制和必要范围已建立，只余明确定位、无需新数学机制的局部证明或交付缺口；不存在被反驳的必需核心断言。 |
| 4 | 在原请求的开放范围内，建模、实质机制、自然条件与核心成果形成严谨、忠实、可用且闭合的研究工作。无需额外拓展、模仿参考路线或达到文献首创。 |

4档须四方面均已成立；3档仅允许已成立或局部缺口。必要核心被反驳、缺少不可省的新机制或发生无桥范围替换时，不能由其他正确内容抵补至3、4档。不能从主分、B/R、旧画像等级、通过目标比例、篇幅或额外成果组数推导新等级。

独立可删除的题外错误不抹去已成立的核心能力，但须逐项说明删除后为何不改变核心定义、定理、证明、范围或一般性。所有原错误、可靠性扣分和严格完成判决继续保留；这一能力验收不改写任何任务的Strict例外政策。

## 证据与聚合

完整读取原题、所给材料、规则选定原答及明确交付附件，核对现有源绑定数学审核中的有效结果与错误。新裁定独立保存逐题等级、四方面理由、核心/范围状态、确切引文及原文件散列。不能把旧审标题直接当成新数学评审，也不能用未提交工作区、后续修改或跨尝试并集补齐交付。

首答按五家族各1/5汇总，0–4档线性换算到0–100。真正未运行或缺原证据保留固定分母及0–4未知区间；已结算失败的可核实原内容按同一提交边界评价，无有效原内容才记0。未正常交卷仍按正式SMC处理，不由新轴恢复交卷资格。

“含续答”阶段仅对实际采用的手稿续答另作独立能力评审，逐题按80%首答与20%续答合成；未选入续答的家族沿用首答，已选但缺评审的续答保持未知。退步如实计入，不取最佳、不拼接两稿。待采用的模型只保留首答阶段。研究主动性始终沿用首答，不因收到统一完善邀请而增加。

## 展示与留档

1.2画像将能力维度置前，“研究主动性”置于最后，并说明它描述自发行为而非研究能力上限。新轴只使用五个共同开放家族，其余独立评审轴保留原35家族，严格完成度仍直接取正式SMC；覆盖单位分别展示，不混用分母，也不按雷达面积排名。

原0.4.0画像、0.1.0续答画像、基线更正和历史1.1展示来源保持原字节。新组件独立绑定它们，只在1.2当前视图加入能力值、修改主动性显示名称及顺序。公开仅有共同标准、匿名合并值、覆盖及不透明散列；四个私有家族的题号、内容、逐题裁定及来源路径留私库。

## English

Open research capability evaluates mathematical work actually delivered when an original task explicitly requests open development. Research initiative separately describes unsolicited exploration. The common quantitative opportunity set is the five manuscript families, equally weighted. The other ten research tasks are screened, but their fixed proof/audit requests do not make stopping after completion a capability failure, and their unsolicited extensions do not add capability credit.

Each judgment independently examines formulation, substantive mechanisms, natural conditions and boundaries, and usable proof closure. These are acceptance facets, not compensating scores. Grades0–4 range from no verified progress through local preparation and substantial partial mechanisms to a core with only local gaps and fully rigorous, faithful completion. A refuted or essentially unproved required core, or unbridged core scope drift, caps the grade at2. Extra theory, novelty claims, manuscript length, old scores and surplus counts do not determine a grade. Valid alternative constructions and proved refutations or conditional repairs are accepted.

All models retain the same five-family denominator and exact original submission boundaries. Unknown evidence retains intervals; settled blanks without usable work receive zero. Adopted manuscript continuations receive independent judgments and blend80% original with20% revision at the original family. Initiative remains first-answer-only. The new component augments the current1.2 profile, puts initiative last, and preserves all original profiles, archived views and main benchmark scores. Reviews are AI assessments with human mathematical approval pending.
