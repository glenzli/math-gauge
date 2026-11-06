# 真实答卷审阅

本组从题库 **0.4.0** 起进入默认公开集，含4份完整真实答卷。考生得到完整原题与原始答案，审阅它们是否成立、依据是否充分、错误影响到哪里；不提供参考、旧成绩、作者模型名或下表的选材理由。其中一题还含继承正文和原始 `KEEP` 核查答复。

四份任务关联四个已有母题，测量独立审阅能力。它们是新增任务类型，不是四个独立新增数学题材；公开36份任务仍关联32个母题家族。参考与判准继续公开供复核，但不进入候选题包。

## 题目与评审材料

| 审阅题 | 原始材料 | 考察重点（仅评审侧） | 完整材料 |
| --- | --- | --- | --- |
| MG-AR001 | MG-GR104 的完整初答 | 正确对照；接受有效替代构造，按上下文判断表格表述 | [题面](MG-AR001/task.md) · [参考](MG-AR001/reference.md) · [判准](MG-AR001/rubric.json) · [来源](MG-AR001/provenance.json) · [状态](MG-AR001/review.json) |
| MG-AR002 | MG-GR014 的完整继承正文与本轮核查 | 正确主结论与附加论据缺口并存，准确限制错误影响 | [题面](MG-AR002/task.md) · [参考](MG-AR002/reference.md) · [判准](MG-AR002/rubric.json) · [来源](MG-AR002/provenance.json) · [状态](MG-AR002/review.json) |
| MG-AR003 | MG-GR010 的完整初答 | 核心错误识别、条件错引、大小性遗漏与独立有效路线 | [题面](MG-AR003/task.md) · [参考](MG-AR003/reference.md) · [判准](MG-AR003/rubric.json) · [来源](MG-AR003/provenance.json) · [状态](MG-AR003/review.json) |
| MG-AR004 | MG-GP003 的完整初答 | 假引理对主证明的真实影响，原定理与证明有效性的区别 | [题面](MG-AR004/task.md) · [参考](MG-AR004/reference.md) · [判准](MG-AR004/rubric.json) · [来源](MG-AR004/provenance.json) · [状态](MG-AR004/review.json) |

原题中的作答要求也是待审材料，不要求审阅者重新解母题或交付 Lean。候选只得到统一审阅题面及 `case.json` 白名单附件，评分和分类不追加到消息中。

## 评分与执行

主指标为100分的审阅能力分：核心数学判断60、依据与影响范围30、补充核查完整度10。重大误判率另列，Strict模式采用整题通过判断；短而充分的判断不因少复述证明而扣分。先按同一母题平均审阅变体，再按母题家族平均；此子类在完整100分框架中占10分，归入书面证明35分。见[完整评分标准](../../protocol/answer-review-scoring.md)。

四题已各有一份 Terra 6.1 Max 与 Gemini 3.8 Flash High 的独立原答，共8份。v0.4.0按新标准复评这些答案，没有重跑模型；这是观察答卷后的方法调整，不是新的预注册试验。原候选材料与响应保持不变，旧执行与冻结评审留作证据。当前结果见[对比页](../../docs/results/comparison-2026-11-03/index.html)。

当前默认计划所有题都只做首次独立A1；C003另有三轮Lean对齐自查，书面重复和立场分支已退出默认安排。可用 `cases/answer-review-suite.json` 单独选择本组，复用同一套准备、执行、外部导出、导入与评分接口：

```sh
python3 -m math_gauge validate --suite cases/answer-review-suite.json
python3 -m math_gauge prepare --suite cases/answer-review-suite.json \
  --case MG-AR001 --out runs/answer-review-ar001
```

准备与核验不调用模型。每次使用新输出目录，完整消息仍由共享 `candidate_message(request)` 构造；独立分项的选卷与导出操作见[说明](../../docs/answer-review-pilot.md)。

4题均为 **draft / author-ai-review-complete / human pending**。母题作者 Lean 证据不自动成为审阅题的形式化证明或人工批准；本组评分合同中的三个维度也不是三个候选阶段或独立样本。

[返回试卷目录](../README.md) · [项目首页](../../README.md)
