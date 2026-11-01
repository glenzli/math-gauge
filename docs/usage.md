# 使用与复核

在仓库根目录执行。共享runner需要Python 3.10+，无第三方运行依赖。所有输出目录使用新路径；Lean核验与实际模型调用另需对应环境。

## 当前题集与候选材料

```sh
python3 -m math_gauge validate
python3 -m math_gauge list
python3 -m math_gauge prepare --case MG-GR001 --out runs/gr001
python3 -m math_gauge prepare --case MG-GF101 --out runs/gf101
python3 -m math_gauge prepare --case MG-C002 --out runs/chapter02
```

默认题集为 `cases`，是包含全部43份的公开开发题集。参考答案继续公开以供透明复核，但属于 evaluator 出题材料，不能交给 solver。`validate` 检查合同、来源和身份，`prepare` 只导出材料；二者不调用模型。题目路径、分类和版本见[目录](../cases/README.md)。

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
python3 -m math_gauge run --case MG-GR001 --out runs/model-gr001 \
  --model 'actual requested model and settings' \
  --command-json '["python3", "/absolute/path/to/adapter.py"]'
python3 -m math_gauge review-template --run runs/model-gr001 \
  --out runs/review-gr001.json
# 完成真实审核后应用该文件：
python3 -m math_gauge review --run runs/model-gr001 --input runs/review-gr001.json
python3 -m math_gauge report --run runs/model-gr001 --out runs/report-gr001
```

审核模板不是完成评分。reviewer、reviewer_kind、decision和各数学轴必须按实际证据填写，并绑定答卷散列。私有题通过同一 `--suite /absolute/path/to/private-suite` 运行，私有位置不复制runner。

[单轮比较工具](../protocol/full-comparison-run.md)是共享runner之上的薄调度层；[隔离流程](../protocol/isolated-cli-runs.md)核验真实文件、进程与工具边界。单轮run不自动执行三次作答或177槽位方案。以下benchmark入口共享同一套案例合同、原始证据和审核规则。

## 七个分项与完整计划

只准备计划，不调用模型：

```sh
python3 -m math_gauge benchmark-plan --target all --out runs/full-plan.json
python3 -m math_gauge benchmark-check --plan runs/full-plan.json
# 也可只准备一类，不会生成其他方向的精确总分：
python3 -m math_gauge benchmark-plan --target lean-audit --out runs/audit-plan.json
```

可选目标为 `proofs`、`lean-audit`、`lean-construction`、`chapters`、`repeat`、`neutral`、`stance`、`core`、`all`；可重复传入 `--target`。默认配置为 [benchmark-profile.json](../protocol/benchmark-profile.json)。完整计划177槽，中性分项单独需24槽，立场分项40槽；两者一起56槽，因为共享同八个A1。这些是计划调用数，不含传输重试。

`benchmark-plan` 保存评审侧范围、权重、阶段合同、消息和顺序。未提供真实runtime时是未冻结的准备材料，只可检查或离线fixture验收，不能发起真实候选调用。将已核实的模型配置、适配器、预算和隔离条件写入runtime，再用 `--runtime /absolute/path/to/runtime.json` 生成用于执行的新计划。运行前应查明每个参数的实际后端含义；请求的型号标签不等于独立身份核验。

runtime的字段结构示例（替换示例身份和预算后才能用于实际运行）：

```json
{
  "model_label": "REPLACE_WITH_REQUESTED_MODEL_AND_SETTINGS",
  "adapter_identity": {"name": "REPLACE_WITH_ADAPTER", "version": "1"},
  "candidate_parameters": {"model": "REPLACE_WITH_ACTUAL_MODEL"},
  "budget": {"timeout_seconds": 120, "output_tokens": 4096, "max_transport_attempts": 354},
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

这里的120秒与4096输出token仅演示字段，不是对整章题的推荐预算。可用 `budget.case_parameters` 事前指定各题的 `max_output_tokens` 等生成参数；同题独立轮与对应复核轮保持一致。timeout限制适配器进程时间，output_tokens传为请求的max_output_tokens，实际后端是否遵守仍需验证；max_transport_attempts限制真正发出的传输尝试。可选max_total_tokens依赖适配器返回真实usage：达到阈值后停止新请求，单个在途请求可能超过阈值；若用量缺失则停止后续调度并明记无法核实，不能称为硬费用上限。

`execution_requirements` 在生成计划前冻结运行证据要求。候选工具须与本版计划的空白名单一致；`internal_tools` 只能列明实际存在的 `finish` / `manage_task` 内部功能。`tool_control_tool` 是用于独立正反能力对照的实际工具名称，不是考试允许的工具。必要读取例外以 `{ "kind": "literal", "path": "/absolute/login-file", "purpose": "具体启动需要" }` 等条目冻结，不能临时放宽。没有冻结这些要求的旧计划可继续暂定分析，但不能仅靠事后填写审核取得正式资格。可选provider与型号/effort别名映射也只能事前冻结；请求模型来自 `candidate_parameters.model`，显示标签不作为身份依据。

分片续跑时，runner将所有显式 `--reuse-run` 的原始证据按生成身份去重，连同本次用量累计检查预算；不限于这次作为父节点的八个A1。没有提供的独立分片无法被自动计入，报告明确标记该边界。因此要约束已知计划累计花费，应传入全部先前分片，不能把单次预算声称为跨所有未知运行的全局上限。

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

第二次原样复用第一份记录中同一计划的八个A1，不重新生成或选择起点。适配器须按冻结角色历史传递候选消息并保证上下文隔离，不能把评审元数据扩展成提示。普通单轮适配器若只读task、不传完整messages，不能直接充当多轮适配器。独立初答之间、三个分支之间互不可见；后续轮没有评分或编译反馈。

每个执行目录保持独立，不覆盖先前结果。相同原始证据重复作为依赖可去重；同名槽位被独立生成两次属于冲突，不能挑较好的一份汇总。分别生成的不同局部计划不能事后拼成全套。只希望做局部研究时，可直接生成该子计划并明确报告范围。

## 外部 harness：独立题包与提交

外部模式与上面的共享命令适配器复用同一计划、消息、审核和评分，不依赖 Codex。只需在评审侧准备题包；独立执行端只需要 Python 3.10+ 和所选平台的调用能力，无需本仓库或安装 Math Gauge。完整格式、控制器接口与结果模板见[外部 harness 协议](../protocol/external-harness.md)。

一次命令同时冻结计划并导出题包，不调用模型：

```sh
python3 -m math_gauge benchmark-export --target all \
  --runtime /absolute/path/to/runtime.json --out runs/external-bundle
python3 -m math_gauge benchmark-export-check --bundle runs/external-bundle \
  --plan runs/external-bundle.evaluator/plan.json
```

省略 `--runtime` 时仍可导出供检查和离线验收的材料，但标记为 `preparation_only`，不能据此开始真实候选运行。已有冻结计划可原样导出或选择其分项，不能同时替换 runtime/profile：

```sh
python3 -m math_gauge benchmark-export --plan runs/frozen-plan.json \
  --target lean-audit --out runs/external-audit
```

`--suite` 和 `--profile` 可在创建计划时指定自定义题集与配置；既有计划的分母和身份保持不变。默认完整评审计划写入独立的 `runs/external-bundle.evaluator/plan.json`；`--evaluator-out /absolute/path/to/evaluator-directory` 可改用另一处新目录。它不能位于交付题包内。只把 `external-bundle/` 交给外部平台，评审目录和本仓库都不交付。

题包中 solver 内容是各题完整题面、instruction、白名单附件及合成后的 `candidate-message.md`；controller 另有脱敏槽位、父子关系、冻结调用条件和提交模板。控制器不能把调度元数据变成模型提示。完整题面与附件共同组成实际提示，不能只读 `task.md` 而忽略文件。每个槽位可用独立助手生成精确 JSON 请求，例如在交付主机上：

```sh
python3 /delivery/external-bundle/controller.py check --bundle /delivery/external-bundle
python3 /delivery/external-bundle/controller.py request --bundle /delivery/external-bundle \
  --slot 'MG-GF101:A1' --out /delivery/requests/gf101-a1.json
```

后续轮用 `--answers /absolute/path/to/ancestor-answers.json` 提供本槽位所需祖先的原始答卷，JSON 对象的键为祖先槽位 ID，值为原样响应文本。助手只构造该分支完整角色历史，拒绝不相关或跨分支历史。把生成请求的完整 `messages` 与允许的冻结生成参数交给实际平台，保留实际请求、原始响应、失败、重试、用量和返回的后端信息。三个初答须使用全新独立上下文；中性、支持、怀疑各从同一 A1 展开两轮，不共享其他分支内容，也不加入评分、正确性或编译反馈。

当前为无工具轨道。检索、代码执行或 Lean 工具的实验须另外冻结版本、工具与预算，并单独报告。隔离控制及原始运行证据仍须按[运行证据标准](../protocol/execution-evidence.md)核实。

外部控制器依据题包内的 `submission-template.json` 写一份新的提交 JSON，按清单中的冻结顺序列出已执行槽位、精确请求和每次尝试；响应与其他原始文件用相对提交文件的路径、字节数及 SHA-256 引用。不得改写原答卷或把失败当作未发生；未执行槽位保持明确缺测。回收目录与题包保持分开。

以下例子仅用已构造的请求生成一份离线交换样例，实际模型调用为零。它展示完整提交字段和散列算法；实际试验须保留真实原始字节，使用 `origin="external"`、`fixture_only=false` 和真实的调用总数。先在交付主机的新目录写样例：

```python
import hashlib
import json
from pathlib import Path

bundle = Path("/delivery/external-bundle")
returned = Path("/delivery/results/offline-example")
returned.mkdir(parents=True, exist_ok=False)
request = json.loads(Path("/delivery/requests/gf101-a1.json").read_text(encoding="utf-8"))
manifest = json.loads((bundle / "manifest.json").read_text(encoding="utf-8"))
submission = json.loads((bundle / "submission-template.json").read_text(encoding="utf-8"))

def file_record(name, raw):
    (returned / name).write_bytes(raw)
    return {"path": name, "bytes": len(raw), "sha256": hashlib.sha256(raw).hexdigest()}

request_bytes = json.dumps(request, ensure_ascii=False, sort_keys=True,
                          separators=(",", ":"), allow_nan=False).encode("utf-8")
submission.update(
    bundle_sha256=manifest["bundle_sha256"], origin="fixture", fixture_only=True,
    declared_external_calls=0,
    slots=[{
        "slot_id": "MG-GF101:A1", "projected_request": request,
        "attempts": [{
            "number": 1, "status": "ok", "exit_code": 0,
            "response": file_record("answer.txt", b"Offline fixture; no model answer.\r\n"),
            "stderr": file_record("stderr.txt", b""), "usage": {},
            "projected_request_sha256": hashlib.sha256(request_bytes).hexdigest(),
        }],
    }],
)
(returned / "submission.json").write_text(
    json.dumps(submission, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
```

将回收目录原样带回评审端，再导入其 `submission.json`。下面路径可指向上述离线样例或实际外部提交；标签随原提交保留：

```sh
python3 -m math_gauge benchmark-import --bundle runs/external-bundle \
  --input /absolute/path/to/results/submission.json \
  --plan runs/external-bundle.evaluator/plan.json --out runs/external-imported
python3 -m math_gauge benchmark-check --run runs/external-imported
python3 -m math_gauge benchmark-review-template --run runs/external-imported \
  --out runs/external-review.json
# 逐项完成实际审核后：
python3 -m math_gauge benchmark-review --run runs/external-imported \
  --input runs/external-review.json
python3 -m math_gauge benchmark-report --run runs/external-imported \
  --out runs/external-report
```

导出、check、导入与审核模板命令均不调用模型。导入把原始提交绑定到共享多轮证据，不单独确认外部来源真实、人工审核完成或正式比较资格。`fixture` / `replay` 提交保持测试标签，缺测保持固定分母。本版通用 `external_import` 用于暂定分析；正式来源合同目前绑定本地调用与隔离材料，外部声明或审核勾选不能替代这条证据链，不能据此取得 `formal_score`。真实答卷的数学裁决与适用候选 Lean 核验仍需完成，新的外部环境另行验证来源和隔离合同。公开开发题集的参考与历史不因独立导出而变成秘密，报告须说明已知暴露与访问条件。

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

报告中的暂定数值与正式资格分别显示。当前43卷仍待人工审定；AI审核和离线fixture只能产生其明确标注的诊断或测试数据，不能称为正式模型成绩。权重与分母的完整说明见[综合评分标准](../protocol/benchmark-scoring.md)。

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

`benchmark-evidence-check` 检查所选槽位的运行资格，缺项时返回非零并保存具体原因；它不裁定数学正确性。`benchmark-check` 检查完整运行与审核绑定，并报告运行资格数量。报告中的各分项另检查题目原始人审来源、答卷human审核、覆盖和适用Lean要求。满足全部条件才输出 `formal_score`；有内容审核但缺运行证据时仍可得到明确标注的暂定分。当前基准尚无真实候选运行，题目仍待人审，不能从离线测试生成正式成绩。

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
