# 使用与复核

本页是仓库内的评审与维护操作指南。只希望接入外部平台并交回答卷时，使用[任务包唯一 README](release-consumer-README-v0.3.0.md)：0.3.0与题集同版，命名任务包为 `benchmark-v0.3.0.zip`，旧包保持不变。执行端不需要仓库、Math Gauge 安装或 Codex。

以下命令在仓库根目录执行。共享runner需要Python 3.10+，无第三方运行依赖。所有输出目录使用新路径；Lean核验与实际模型调用另需对应环境。

## 当前题集与候选材料

```sh
python3 -m math_gauge validate
python3 -m math_gauge list
python3 -m math_gauge prepare --case MG-GR002 --out runs/gr002
python3 -m math_gauge prepare --case MG-GF101 --out runs/gf101
python3 -m math_gauge prepare --case MG-C002 --out runs/chapter02
```

默认题集为 `cases`（`cases/suite.json`），含32份公开开发试卷；`--suite cases/reserve-suite.json` 显式选择后备11题。两集同根且不重叠，保留原43卷材料。新版32题/80槽尚未运行；旧177槽的真实结果见[Terra暂定试跑](terra-pilot-2026-11-02.md)，不按新版分母重算。参考答案继续公开以供透明复核，但属于 evaluator 出题材料，不能交给 solver。`validate` 检查合同、来源和身份，`prepare` 只导出材料；二者不调用模型。题目路径、分类和版本见[目录](../cases/README.md)。

导出目录只有prompt.md、request.json及显式附件。适配器应使用共享消息构造器，完整发送白名单文本：

```python
from math_gauge.catalog import candidate_message, read_json

request = read_json("runs/gf101/request.json")
message = candidate_message(request)
```

无附件且instruction为空时消息等于原题面；有附件时追加中性文件名和完整内容。参考、评分、来源、真假、审核和作者源码留在评审侧，不由适配器补入。

## 单份答卷、审核与报告

通用命令适配器从stdin读取JSON请求，向stdout写完整答卷。以下入口会真实调用指定适配器；运行前需另行确定模型、预算、工具与隔离条件：

```sh
python3 -m math_gauge run --case MG-GR002 --out runs/model-gr002 \
  --model 'actual requested model and settings' \
  --command-json '["python3", "/absolute/path/to/adapter.py"]'
python3 -m math_gauge review-template --run runs/model-gr002 \
  --out runs/review-gr002.json
# 完成真实审核后应用该文件：
python3 -m math_gauge review --run runs/model-gr002 --input runs/review-gr002.json
python3 -m math_gauge report --run runs/model-gr002 --out runs/report-gr002
```

审核模板不是完成评分。reviewer、reviewer_kind、decision和各数学轴必须按实际证据填写，并绑定答卷散列。私有题通过同一 `--suite /absolute/path/to/private-suite` 运行，私有位置不复制runner。

[单轮比较工具](../protocol/full-comparison-run.md)是共享runner之上的薄调度层；[隔离流程](../protocol/isolated-cli-runs.md)核验真实文件、进程与工具边界。单轮run不自动执行完整80槽位方案。以下benchmark入口共享同一套案例合同、原始证据和审核规则。

## 七个分项与完整计划

只准备计划，不调用模型：

```sh
python3 -m math_gauge benchmark-plan --target all --out runs/full-plan.json
python3 -m math_gauge benchmark-check --plan runs/full-plan.json
# 也可只准备一类，不会生成其他方向的精确总分：
python3 -m math_gauge benchmark-plan --target lean-audit --out runs/audit-plan.json
```

可选目标为 `proofs`、`lean-audit`、`lean-construction`、`chapters`、`repeat`、`neutral`、`stance`、`core`、`all`；可重复传入 `--target`。默认配置为 [benchmark-profile.json](../protocol/benchmark-profile.json)。完整计划80槽，能力只取32份A1；六题面板另有12份A2/A3、12份中性及24份立场答卷。中性目标单跑需18槽，立场目标30槽；两者合跑42槽，因为共享同六个A1。这些是计划调用数，不含传输重试。

`benchmark-plan` 保存评审侧范围、权重、阶段合同、消息和顺序。未提供真实runtime时是未冻结的准备材料，只可检查或离线fixture验收，不能发起真实候选调用。将已核实的模型配置、适配器、预算和隔离条件写入runtime，再用 `--runtime /absolute/path/to/runtime.json` 生成用于执行的新计划。运行前应查明每个参数的实际后端含义；请求的型号标签不等于独立身份核验。

runtime的字段结构示例（替换示例身份和预算后才能用于实际运行）：

```json
{
  "model_label": "REPLACE_WITH_REQUESTED_MODEL_AND_SETTINGS",
  "adapter_identity": {"name": "REPLACE_WITH_ADAPTER", "version": "1"},
  "candidate_parameters": {"model": "REPLACE_WITH_ACTUAL_MODEL"},
  "budget": {"timeout_seconds": 120, "output_tokens": 4096, "max_transport_attempts": 160},
  "retry": {"max_attempts": 2, "wait_seconds": 0, "retryable_exit_codes": [75]},
  "fresh_context": true,
  "execution_requirements": {
    "schema": "math-gauge.execution-requirements/v1",
    "allowed_tools": [],
    "internal_tools": [],
    "denied_categories": ["reference", "history", "prior_run", "memory", "global_config"],
    "read_exceptions": [],
    "tool_control_tool": "REPLACE_WITH_ACTUAL_CONTROL_TOOL"
  }
}
```

这里的120秒与4096输出token仅演示字段，不是对整章题的推荐预算。正的 `budget.timeout_seconds` 必填，限制适配器进程时间。示例的 `output_tokens` 传为请求的 `max_output_tokens`，仅适用于实际传输支持且会执行该上限的情况；执行前须核实。可用 `budget.case_parameters` 事前指定各题受支持的生成参数，同题独立轮与对应复核轮保持一致。

仅当实际传输没有受支持的输出上限时，才可省略 `budget.output_tokens`；省略表示平台默认输出策略及未知实际限制，必须在 `adapter_identity` 及操作者冻结说明中明确记录。不得发送会被忽略的上限字段，也不能仅凭配置声称上限已生效。`max_transport_attempts` 限制真正发出的传输尝试；可选 `max_total_tokens` 依据实际返回的 `total_tokens` 在达到阈值后停止新请求，单个在途请求可能超过阈值。若用量缺失则停止后续调度并明记无法核实，不能称为硬费用上限。

runtime省略 `execution_track` 时，默认无工具上下文保持原样。可显式设置 `execution_track: "math-gauge.local-tools-no-search/v1"`：只开放 `exec_command`、`write_stdin`、`apply_patch`，禁止联网检索/外部搜索及工具联网，允许本地题面和预置公共依赖的内容/API查找及本地工具反馈，不提供评审者的正确性或编译反馈。权限不增加使用工具或Lean的提示、义务或最低用量，原题交付要求不变；不同条件分别报告，不能混成同一成绩。

`execution_requirements` 在生成计划前冻结运行证据要求。`allowed_tools` 须与所选条件的精确白名单一致，上例的空列表对应默认无工具条件；`internal_tools` 只能列明实际存在的 `finish` / `manage_task` 内部功能。`tool_control_tool` 是用于独立正反能力对照的实际工具名称，不是考试允许的工具。必要读取例外以 `{ "kind": "literal", "path": "/absolute/login-file", "purpose": "具体启动需要" }` 等条目冻结，不能临时放宽。没有冻结这些要求的旧计划可继续暂定分析，但不能仅靠事后填写审核取得正式资格。可选provider与型号/effort别名映射也只能事前冻结；请求模型来自 `candidate_parameters.model`，显示标签不作为身份依据。工具联网禁令、文件隔离及固定依赖需由实际环境核实，配置声明不能替代证据。

分片续跑时，runner将所有显式 `--reuse-run` 的原始证据按生成身份去重，连同本次用量累计检查预算；不限于这次作为父节点的六个A1。没有提供的独立分片无法被自动计入，报告明确标记该边界。因此要约束已知计划累计花费，应传入全部先前分片，不能把单次预算声称为跨所有未知运行的全局上限。

实际配置确定后，将它写入新的冻结计划；这一步仍不调用模型：

```sh
python3 -m math_gauge benchmark-plan --target all \
  --runtime /absolute/path/to/runtime.json --out runs/frozen-plan.json
```

实际执行仍需明确授权。若希望分开跑后合看，应使用同一个已冻结的 `frozen-plan.json`，执行前选择它的分项投影，例如：

```sh
python3 -m math_gauge benchmark-run --plan runs/frozen-plan.json \
  --target core --out runs/core-part \
  --command-json '["python3", "/absolute/path/to/conversation-adapter.py"]'
python3 -m math_gauge benchmark-run --plan runs/frozen-plan.json \
  --target neutral --reuse-run runs/core-part --out runs/neutral-part \
  --command-json '["python3", "/absolute/path/to/conversation-adapter.py"]'
```

第二次原样复用第一份记录中同一计划的六个A1，不重新生成或选择起点。适配器须按冻结角色历史传递候选消息并保证上下文隔离，不能把评审元数据扩展成提示。普通单轮适配器若只读task、不传完整messages，不能直接充当多轮适配器。独立初答之间、三个分支之间互不可见，也不共享工具状态或文件；后续轮不接收评审评分或评审端编译反馈，本地工具反馈按所选条件处理。

每个执行目录保持独立，不覆盖先前结果。相同原始证据重复作为依赖可去重；同名槽位被独立生成两次属于冲突，不能挑较好的一份汇总。分别生成的不同局部计划不能事后拼成全套。只希望做局部研究时，可直接生成该子计划并明确报告范围。

## 外部 harness：统一接收返回包

外部运行端的完整准备、取题、记录和打包流程只维护在[任务包 README](release-consumer-README-v0.3.0.md)。按新配置构建的0.3.0中性任务包包含32题及约定附件，后备11题不进入默认包，根目录仅一份指南；可选工具 `tools/benchmark.py` 自动保存原始尝试、构造精确分支历史并打包 `answers.zip`。它不调用候选模型，也不需要执行端取得完整评审计划、手写散列或提交JSON。

评审端保留可信的完整主计划和原题集。以下示例在取得0.3.0构建输出及返回包后使用，一条命令完成完整性核验与导入：

```sh
python3 -m math_gauge benchmark-import --input answers.zip \
  --plan runs/releases/v0.3.0/evaluator-plan.json --out runs/external-imported
```

导入只读取数据，不执行下载包中的工具，不调用模型或编译Lean。包内含冻结运行、原始尝试及每个选定槽位的完成、失败、跳过或待执行状态。导入器核验可信计划、题集、请求历史、原始文件与顺序，接入同一多轮证据和审核入口。输出目录必须是新路径；未知平台字段保持未知，缺测继续按完整计划的固定分母报告。

接下来生成 `benchmark-review-template` 并完成实际数学、交付及适用的候选Lean审核，再使用下一节的审核、收集与报告入口。来源另记为 `external_import`，不会把导入伪装成runner现场调用。fixture/replay保留各自标签，外部声明或审核勾选不能单独取得正式比较资格。新的真实外部环境需要验证其来源和隔离合同；完整题库43题的人审状态也不因导入改变。

### 维护接口与历史交换

仓库直接导出的旧交换接口继续保留，使用同一候选投影、数学和审核合同。已有完整计划可原样导出，不临时替换runtime/profile：

```sh
python3 -m math_gauge benchmark-export --plan runs/frozen-plan.json \
  --target lean-audit --out runs/external-legacy
python3 -m math_gauge benchmark-export-check --bundle runs/external-legacy \
  --plan runs/external-legacy.evaluator/plan.json
```

未冻结runtime的导出只用于准备与离线检查。v1直接交换及历史v0.1.0发布运行的v2提交仍可使用 `benchmark-import --bundle BUNDLE --input SUBMISSION_JSON --plan PLAN --out NEW_RUN`；旧字段与绑定规则见[外部交换合同](../protocol/external-harness.md)，历史发布操作见[v0.1.0包内指南](release-consumer-README.md)。普通0.3.0运行不需要走手写JSON或祖先答案映射流程。

独立数据集、控制材料与完整评审材料分别保存。操作者工具不是候选解题工具，候选仅收到完整消息及允许的本分支历史。整章题约定的含证明原文和语义审计源码保留为合法输入；公开参考与Git历史仍可见，不把本开发集说成隐藏留出集。

## 多轮审核与汇总

```sh
python3 -m math_gauge benchmark-check --run runs/core-part
python3 -m math_gauge benchmark-review-template --run runs/core-part \
  --out runs/core-review.json
# 逐项实际审核并填写原始证据绑定后：
python3 -m math_gauge benchmark-review --run runs/core-part --input runs/core-review.json
python3 -m math_gauge benchmark-report --run runs/core-part --out runs/core-report
# neutral-part 等分片同样独立审核，再按同主计划合并：
python3 -m math_gauge benchmark-report --run runs/core-part \
  --run runs/neutral-part --out runs/combined-report
```

模板不是成绩。审核仍需实际阅读整份答案，逐阶段裁定数学、交付与Lean要求；重点数学和整卷数学分别记录。KEEP继承紧邻上一版主体，但本轮理由也须审；FULL不能从旧答卷自动补齐。审核绑定当前原始响应、角色历史、完整材料、父节点及固定规则，变更任一材料会使旧审核失效。

待审后来得到裁决时，使用显式修订并保留原审核快照：

```sh
python3 -m math_gauge benchmark-review --run runs/core-part \
  --input runs/core-review-revised.json --revise \
  --expected-review-snapshot CURRENT_ACTIVE_SNAPSHOT_SHA256
python3 -m math_gauge benchmark-report --run runs/core-part \
  --review-snapshot 1 --out runs/report-at-review-1
```

当前快照身份从check/collect结果读取；期望身份不匹配时拒绝覆盖。report默认使用当前快照并冻结实际版本/散列，也可显式读取旧版本；审核更新不是模型自查改善。合并分片时同源答卷的两个不同已审快照须先统一裁决，不能自动选更高分的一份。

`benchmark-collect --run DIR --out FILE` 导出已经过绑定核验的评分输入。报告入口自行读取并核验原始run与审核，不能通过手写几个总分绕过证据门槛。生成 `report.json` 和 `report.md`，包括七个分项、能力分、综合分、严格完成、覆盖、未知区间与轨迹诊断。缺失立场分片时综合精确值仍为null；不会把core+neutral重新缩成100%。

报告中的暂定数值与正式资格分别显示。默认32卷及后备11卷仍待人工审定；AI审核和离线fixture只能产生其明确标注的诊断或测试数据，不能称为正式模型成绩。权重与分母的完整说明见[综合评分标准](../protocol/benchmark-scoring.md)。

## 运行证据与正式资格

下列命令只处理已经存在的运行与原始证据，不调用模型。先按[隔离流程](../protocol/isolated-cli-runs.md)记录真实调用、返回信息、全部尝试和实际边界；再为一个槽位生成待填写表单：

```sh
python3 -m math_gauge benchmark-evidence-template --run runs/core-part \
  --slot 'MG-GR002:A1' --out runs/gr002-a1-evidence.json
# 具名审核者核对原始材料，填写来源、观察和审核后：
python3 -m math_gauge benchmark-evidence-import --run runs/core-part \
  --slot 'MG-GR002:A1' --input runs/gr002-a1-evidence.json
python3 -m math_gauge benchmark-evidence-check --run runs/core-part \
  --out runs/core-execution-check.json
python3 -m math_gauge benchmark-report --run runs/core-part \
  --out runs/core-report-with-execution-audit
```

指定 `--slot` 时导出可直接填后导入的单份表单；省略时导出全部表单集合。原始文件路径相对于表单所在目录，必须在该目录内；显式清单记录文件用途、来源、字节数与SHA-256。每项观察指向原始JSON/NDJSON中的具体位置，或原始响应字节。不能用模板、模型自述、请求回显或一个“通过”勾选代替材料。导入器复制清单内的原始文件，并在以后每次check/collect/report时重新核验。

`benchmark-evidence-check` 检查所选槽位的运行资格，缺项时返回非零并保存具体原因；它不裁定数学正确性。`benchmark-check` 检查完整运行与审核绑定，并报告运行资格数量。报告中的各分项另检查题目原始人审来源、答卷human审核、覆盖和适用Lean要求。满足全部条件才输出 `formal_score`；有内容审核但缺运行证据时仍可得到明确标注的暂定分。旧版177槽已有真实provisional试跑，新版32卷/80槽尚未运行；题目仍待人审，真实试跑与离线软件测试都不能替代正式资格。

运行审核修订必须引用当前快照；包括将先前通过改为拒绝：

```sh
python3 -m math_gauge benchmark-evidence-import --run runs/core-part \
  --slot 'MG-GR002:A1' --input runs/gr002-a1-evidence-revised.json \
  --revise --expected-audit-snapshot CURRENT_AUDIT_SNAPSHOT_SHA256
python3 -m math_gauge benchmark-report --run runs/core-part \
  --audit-snapshot RETAINED_AUDIT_SHA256 --out runs/historical-audit-report
```

旧快照显式标为historical，保留其所支持的 `historical_formal_score`；当前比较用的 `formal_score` 不把已被新审核取代的结论当作有效资格。数学分数与原答卷不因运行审核修订而改变。合并多个分片默认分别使用各自当前快照；重现多个分片的历史报告时，用 `--audit-snapshots /absolute/path/to/audit-map.json`，其中JSON对象的键为本次所有run的完整真实路径，值为各自保留的快照SHA-256，不得漏项、多项或混用单个 `--audit-snapshot`。

复用父答卷时连同原审核证据一起保存，源目录移除后仍可核对这份保留证据。合并时相同原始生成可以去重，不同已审快照发生冲突则停止；不同生成复用同一会话、状态或请求身份也不能通过独立性检查。可用的观察范围与人工来源责任见[运行证据标准](../protocol/execution-evidence.md)，实际适配器须保存的字段见[证据交换格式](../protocol/execution-evidence-format.md)。

## 作者与候选Lean

作者证据的只读身份核验：

```sh
python3 scripts/formal/check_evidence.py
```

该检查复核已保存的编译、源码、公理与语义覆盖绑定，不调用模型、不重编未变源码。需要重编时，按[固定工具链说明](../scripts/formal/README.md)使用受影响题目的manifest和新的输出目录；不混用Lean/Mathlib/TauCeti配置。

候选源码由 `math_gauge.execution.verify_candidate_lean` 从冻结答卷提取，在明确的固定依赖和受限环境中原样核验。它不补import、不改定理、不修proof。候选生成/修复与整章严格通过还需逐义务语义审核；章节清单和冻结背景合同见[候选Lean协议](../protocol/candidate-lean.md)。

多轮答卷使用绑定材料来源的入口；只有显式调用此命令才编译，执行器不会把结果反馈给模型：

```sh
python3 -m math_gauge benchmark-check-lean --run runs/core-part \
  --slot 'MG-GF104:A1' --out runs/gf104-a1-lean \
  --dependency-root /absolute/path/to/pinned-lean-project
```

后续KEEP的数学理由仍需本轮审核，不能因为继承源码编译通过便自动通过本轮。更换源码、背景、编译器或公理审计身份会使旧收据失效。

## 维护检查

```sh
python3 scripts/catalog.py --check
python3 scripts/validate_protocol.py
python3 -m unittest discover -s tests
python3 -m math_gauge validate
```

分类或源绑定有意更新后，先核对完整材料，再运行 `python3 scripts/catalog.py` 生成目录。协议身份变更后用 `python3 scripts/validate_protocol.py --refresh` 更新当前计划绑定；该操作不能授权执行或填入候选结果。真实编译测试若因缺少指定环境而跳过，应如实报告。
