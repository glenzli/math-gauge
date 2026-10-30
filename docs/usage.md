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

默认题集为 `cases`，包含全部43份。`validate` 检查合同、来源和身份，`prepare` 只导出材料；二者不调用模型。题目路径、分类和版本见[目录](../cases/README.md)。

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
  "fresh_context": true
}
```

这里的120秒与4096输出token仅演示字段，不是对整章题的推荐预算。可用 `budget.case_parameters` 事前指定各题的 `max_output_tokens` 等生成参数；同题独立轮与对应复核轮保持一致。timeout限制适配器进程时间，output_tokens传为请求的max_output_tokens，实际后端是否遵守仍需验证；max_transport_attempts限制真正发出的传输尝试。可选max_total_tokens依赖适配器返回真实usage：达到阈值后停止新请求，单个在途请求可能超过阈值；若用量缺失则停止后续调度并明记无法核实，不能称为硬费用上限。

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

当前新入口尚未接入独立的后端身份与进程隔离实证验收，因此即使填了human审核，`formal_score`仍保守为空。完整数值可作为其证据标签下的暂定报告；不能把runtime中的声明当作正式榜单资格。实际执行的隔离实证沿用[隔离流程](../protocol/isolated-cli-runs.md)记录，后续接入验收需另经测试。

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
