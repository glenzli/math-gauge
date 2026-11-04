# 本地0.6.0任务包与补考

本地草稿 / human pending，尚无0.6发布资产。默认26任务、18家族、42标准记录，另31份reserve；合并3私有探索为29任务、21家族、45记录。旧0.5结果、原答与发布资产保持原身份。

## 后续 C003：统一 180 分钟

未来 MG-C003 初答、每次中性跟进及操作续作，每轮上限均为10800秒；模型原生、broker和外层墙钟须实际设置并分别留证。准备新的C003计划时使用独立profile与目标：

```sh
python3 -m math_gauge benchmark-plan --profile protocol/benchmark-profile-c003-180.json --target c003-180 --runtime /ABS/c003-180-runtime.json --out /NEW/c003-180-plan.json
python3 -m math_gauge benchmark-export --plan /NEW/c003-180-plan.json --out /NEW/c003-180-bundle
```

其余七份新Lean使用同一未来profile的`lean-90`目标及5400秒的独立runtime，不能以一个全局预算混跑。实际适配器与[预算v0.2.0](../protocol/lean-tool-budget-policy-v0.2.0.json)必须一致，详见[180分钟配置](../protocol/c003-180-budget.md)。已完成的Terra交卷复用，原90分钟运行不重标预算。

当前展示另按用户选定来源，将Gemini加时实际工程严格完成的74/92项计入数学完成分，原首答及执行状态不覆盖。新的三轮中性续查承接该工程，以180分钟上限分别归档；它们属于新工程承接研究，不补写旧阻断轮次、不回填原标准分。来源和分数见[结果报告](benchmark-comparison-v0.6.0.md)。

## 原标准采集：保留历史配置

以下描述本轮已冻结的原标准采集方式，其中5400秒是原实际预算；未来C003按上节独立配置执行。

稳定的8份Lean新A1已经有独立initial-acquisition profile，与最终四written面板分离。先冻结具体模型/参数/系统/预算，再准备，不调用模型：

```sh
python3 -m math_gauge validate
python3 scripts/catalog.py --check
python3 scripts/validate_protocol.py
python3 -m unittest discover -s tests
python3 -m math_gauge benchmark-plan --profile protocol/benchmark-profile-a1-acquisition.json --runtime /ABS/runtime.json --target lean-audit --target lean-formalization --out /NEW/a1-plan.json
python3 -m math_gauge benchmark-export --plan /NEW/a1-plan.json --out /NEW/a1-bundle
```

新Lean runtime显式local-tools-no-search且timeout_seconds5400；native、broker和外层UTC须另行实际预检5400。generic CLI默认120秒不变。完整采集计划26A1、实际选8，无A2/后续，也不是完整标准考试分数。

最终标准使用protocol/benchmark-profile.json。重复与neutral/affirm/deny各一轮只覆盖GR002、GR014、GP001、GP002四written；Lean、AR和探索只测A1。普通书面后续保留原case真实系统/参数及内外预算，不套Lean5400。A1/A2独立，三分支分别只含自己A1及对应用户提示，不能读取A2、其他分支或其他模型。

v1 partial返回使用共享harness.py的submission-template.json与candidate_request_from_bundle；新GP001/GP002各完整5槽fresh，不接旧A1。当前harness通过三个标准目标导出四题的20槽；实际补考控制器预先冻结GP001/GP002的10槽白名单，其余槽保留未执行状态，再与原GR002/GR014整套证据组合。`written-new-panel`仅用于评审侧选择，当前外部导出使用以下标准目标。冻结written runtime后准备，不调用模型：

```sh
python3 -m math_gauge benchmark-plan --profile protocol/benchmark-profile.json --runtime /ABS/written-runtime.json --target repeat --target neutral --target stance --out /NEW/written-plan.json
python3 -m math_gauge benchmark-export --plan /NEW/written-plan.json --out /NEW/written-bundle
python3 -m math_gauge benchmark-import --bundle /ABS/bundle --input /ABS/submission.json --plan /ABS/plan.json --suite cases --out /NEW/imported
```

两模型标准各18新调用：8Lean A1加两written各5槽。旧GR002/GR014完整五槽包、其余未变written和AR严格相容时按原身份复用；旧GP001/GP002答卷保留0.5，不择优。完整raw、source plan、system/params/track与内外实际预算分别保留；跨case来源分层可用，同case条件漂移拒绝。
错误但可读的原raw完整保留，attempt.status不改；responded只表示可读。非ok终态阻断后续，数学审核须unresolved/no-delivery，[0,1]保留而非数学0。KEEP继承本分支完整主体且独立审核当前理由；FULL重新完整交付。准备/检查/导入本身不调用模型。

MG-C003(92)的100%对齐专项另按protocol/lean-alignment/study.json，从正式A1接原工程，固定3次中性跟进，每轮5400。它不入42/45分母或权重、不替代A1。HCH02旧专项独立归档。原生执行薄适配与最终放行由操作者另行冻结，不能复制私有runner。
