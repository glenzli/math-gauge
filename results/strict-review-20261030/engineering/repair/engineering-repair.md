# Math Gauge engineering repair — 2026-10-30

已修复首轮严格审查的 ENG-001 / ENG-002。只修改四个 runner／测试文件，未改题目、rubric、数学材料、历史结果或旧收据；没有提交、push 或候选模型请求。

- ENG-001：候选 Lean 报告与工件 manifest 保存冻结 group_contract_sha256；审核要求它与本次运行和题组合同相同。相同 request/response 的弱合同收据、缺少合同散列的题组收据均拒绝。
- ENG-002：当前运行在 inspect、模板、审核和报告前重算真实 request／candidate message 散列并核对题目身份；原请求改变、元数据散列失配均拒绝。
- 历史兼容仅覆盖有依据的旧外部导入形态：无 run_id、无消息散列、指定旧 import origin 的非题组记录。缺请求或仅绑定 raw-task 的记录明确显示 historical/unverifiable 和 verified=false，保留原因，禁止新增审核和当前比较资格；泛 legacy 标记不能绕过当前运行。

新增10项回归覆盖跨合同、缺散列、真实生成字段、原请求与身份漂移、消息绑定、旧非题组、缺历史请求、raw-task合同和泛legacy标记。最终针对检查61项：60通过、1可选隔离Lean跳过。源码身份和补丁见 [code-identity.json](code-identity.json) 与 [runner-contract-fixes.patch](runner-contract-fixes.patch)。

最终全套执行确实进行了，但未通过：152项，8条failure、4条error、15跳过，均位于同期新加入且尚未完成的 test_focus_catalog.py（focus-catalog.json缺失／progressive suite drift）。此结果不能描述为全套通过；原日志保留在 [compatibility/unit-tests.stderr.log](compatibility/unit-tests.stderr.log)。父任务将在focus整合完成后统一跑最终全套。此前修复阶段的139项全套为124通过、15跳过，完整记录保留在 [checks.json](checks.json)，不冒充最终源码全套证据。

只读检查89个既有run：新增拒绝0。4个旧外部导入包共28题明确为输入身份未验证，当前比较资格0；旧结果文件未改变。详见 [historical-run-compatibility-after.json](historical-run-compatibility-after.json)。

真实 macOS 隔离 Lean 合成工程仅运行1次，编译3个模块并通过审核；原样源码、背景、原答卷、alignment、合同、报告、日志和olean均保存在 [isolated-group-run](isolated-group-run)。编译后仅审核模块的历史兼容处理发生变化；执行器／编译引擎散列未变，因此复用该真实编译产物，并用最终审核器重验5/5阶段通过，见 [isolated-group-final-review.json](isolated-group-final-review.json)。没有重编作者参考，不能据此声称新增题组或整章作者Lean已完整覆盖。

六套validate在修复阶段均exit0，原题集身份不变；随后GR001版本化数学修订由父任务独立负责，最终新题集／材料验证需要使用该修订后的身份。本Agent没有修改该题。

精确命令、原始日志及散列分别见 [compatibility/focused.json](compatibility/focused.json)、[compatibility/unit-tests.json](compatibility/unit-tests.json)、[isolated-group.json](isolated-group.json) 和 [engineering-repair.json](engineering-repair.json)。
