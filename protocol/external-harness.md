# 外部 harness 交换协议

本协议规定题目导出、外部独立执行和原始答卷导入。外部 harness 可以使用自己的模型接入和会话管理，不需要 Codex 调度。导出、检查和导入本身不调用候选模型，也不执行候选提交的程序。

当前 `cases/` 是 **43 份公开开发试卷**。题目、参考论证与作者证据已公开，用于接入、回归和可复现实验；不得声称这些题或答案从未公开。公开开发集与将来未公开的保留集共用案例合同、runner 和评分实现，分开报告。

直接使用已发布数据时，从 [v0.1.0 Release](https://github.com/glenzli/math-gauge/releases/tag/v0.1.0) 下载命名候选 ZIP 与 SHA256SUMS，按[下载运行指南](release-distribution.md)校验、解压并冻结本次模型和预算。无需 clone、安装 runner 或使用 Codex。GitHub 自动生成的 Source code 压缩包含公开评审材料，不是候选交付物。发布版本0.1.0与题集版本0.2.0分别记录。

下载包的不可变数据集与每次 runtime 分开：`math-gauge.release-dataset/v1` 保留候选内容与脱敏完整调度，`math-gauge.harness-run/v2` 在新目录绑定所选runtime与执行范围。运行散列、UUID与本地时间只描述材料身份和声明，不认证第三方执行。下文原有 `benchmark-export` 仍支持从仓库直接冻结并导出；两条路径使用同一数学、消息、提交和审核合同。

## 三种材料与访问者

| 材料 | 内容 | 访问者 |
| --- | --- | --- |
| 候选输入 | 原始题面、可选统一指令、显式附件，以及本轮允许的对话历史 | 当前作答模型 |
| harness 控制材料 | 选中槽位、依赖、预算、固定后续消息、提交格式和完整性记录 | 外部调度端 |
| 评审材料 | 完整主计划、参考答案、逐项判准、预期真假、选择理由、作者证明和审核记录 | 评审端 |

控制材料不是新增题面。不能把完整调度说明、清单、分类、实验机制或评审材料放进作答上下文。完整 `benchmark-plan` 含评审信息，不能作为外部执行包直接发送。

发布仓库是公开开发集的编写与复核环境，包含候选材料和评审材料；它不是候选工作目录。导出时依据显式白名单生成新包。评审侧文件另存于包外，不能为了方便把仓库或导出包的父目录整体交给作答进程。目录分开只说明材料边界，实际文件、网络、工具和历史隔离仍须由执行环境保证。

整章题允许提供含证明的原文及跨章 Lean 定义，这是题目约定的输入。Lean 审计题中故意失配的源码也属于输入。不得以隐藏答案为由删除这些材料；作者完成的本题 Lean 不属于候选输入。

## 发布数据集与每次运行

命名 ZIP 的 `payload/` 不预选模型和预算。先执行 `controller.py check`，再用 `freeze --runtime ... --out NEW_RUN` 创建根目录含控制器、运行清单与提交模板、子目录含原样 `dataset/` 的新运行。只有冻结后的运行可构造真实候选请求，原题包不改写。执行端只需下载包和 Python 标准库。

发布路径使用 `math-gauge.harness-submission/v2`，提交绑定 `dataset_sha256`、`run_sha256` 和 `runtime_sha256`。`controller.py template` 从运行目录生成已填绑定的独立文件；不能改写被清单哈希绑定的原模板。完整评审计划在评审端从对应标签及 `releases/v0.1.0/config.json` 恢复，导入器再结合原样 runtime 重建评审计划，不伪造旧版 `plan_sha256`。该恢复锚点与完整计划不进入候选 ZIP。

runtime 使用发布控制器的显式白名单，不能原样套用带额外运行证据字段的仓库配置；格式及全部命令见[下载运行指南](release-distribution.md)。公开与未来私有数据复用相同实现。

## 从仓库直接导出（v1交换）

在仓库根目录准备完整开发集：

```sh
python3 -m math_gauge benchmark-export --target all --out runs/external-dev
```

交给外部调度端的目录为 `runs/external-dev/`；完整评审计划默认写到独立的 `runs/external-dev.evaluator/plan.json`。可以通过 `--evaluator-out` 指定另一个独立目录。两个输出目录必须是新路径，不允许互相包含；不覆盖已有导出。

准备阶段尚未指定真实模型与预算时，包明确标为未冻结运行配置。真实执行前应先准备配置文件，再生成新包：

```sh
python3 -m math_gauge benchmark-export --target lean-construction \
  --runtime /absolute/path/to/runtime.json --out runs/external-lean
```

配置采用[使用指南](../docs/usage.md)中的 runtime 合同，不在生成包后临时改模型、预算或工具条件。导出时不会试调模型或检查凭据。也可以用 `--plan /absolute/path/to/plan.json` 导出已有冻结计划的选定分项；同计划的分片沿用完整分母。

每份候选消息包含题面及附件全文，与共享 `candidate_message(request)` 一致。旧的单题 `prepare` 仍可使用，但其 `prompt.md` 不展开附件；不要把旧单题文件与完整消息混淆。

包内布局如下。评审目录与交付包是同级的独立目录；`cases/` 内的传输元数据同样不能扩展为解题提示。

```text
external-dev/
  CONTROLLER.md
  controller.py
  manifest.json
  submission-template.json
  cases/<case-id>/
    request.json
    task.md
    instruction.txt
    candidate-message.md
    files/<declared-attachment-path>
external-dev.evaluator/
  plan.json
  receipt.json
```

## 不依赖仓库的控制端

导出包自带执行说明、机器清单、提交模板和仅依赖 Python 标准库的 `controller.py`。把整个包移动到另一台机器后，控制工具仍能检查文件并构造本轮请求，不需要 `math_gauge` 包、原仓库或评审答案。具体命令见包内执行说明和 `controller.py --help`。

请求构造工具不连接任何模型，也不接受外部命令让它代执行。harness 负责将构造出的 `messages` 和冻结生成参数交给实际后端，并保存真实请求、返回文本及调用记录。作答模型不应获得控制工具或调度说明作为额外上下文。

哈希用于发现材料变更并绑定输入、历史与答卷；拥有一组自洽哈希不等于证明后端身份、调用真实性或隔离成立。对外传包时，应通过独立可信渠道保留导出身份，导入时再与评审侧计划和实际题集核对。

## 执行顺序与上下文

所有题有 `A1`、`A2`、`A3` 三次独立作答。每次必须使用新的上下文，不包含同题其他答案、先前审核、跨题记忆或自定义解题提示。不能在一个长会话里让模型连答三次来代替独立运行。

固定八题的自查从同一份锁定 `A1` 分别展开 `neutral`、`affirm`、`deny` 三条分支，每条两轮。第一轮只使用题目、该 `A1` 和本分支的固定提示；第二轮再接上本分支第一轮的原始回答及第二轮提示。不得混入另一个分支的回答、其他独立轮或真实正确性反馈。支持或怀疑的提示是冻结实验输入，不是评审结论。

复核保持既有 `KEEP` / `FULL` 合同：`KEEP` 维持紧邻父节点的完整答卷，说明仅供本轮审核；`FULL` 是重新交付覆盖全题的答案和所需文件。不能跳过错误格式的父节点直接继承 `A1`，也不能用修改摘要替代完整交付。见[复核交付格式](reliability/reply-format.md)。

当前版本是禁用候选工具的文本作答条件。使用 Lean 交互编译、联网检索或额外 agent 的实验需要另行冻结、命名并报告，不能把改变后的条件登记成当前轨道。harness 本身进行传输、文件保存和调度不属于候选获得解题工具。

## 原始答卷与失败记录

提交必须保留实际执行顺序、每次尝试、原始响应字节、错误信息、可观察的用量和时间、实际消息及生成配置。未知值保持未知，不用导入时间代替生成时间，不把请求的型号名当作后端身份的独立核验。

本版按冻结槽位顺序执行。提交的 `slots` 可以省略未执行节点，但已提交节点必须保持计划中的相对顺序；导入器不把乱序记录默默重排后计算预算。分阶段运行可持续收集同一包的答卷，最终按原计划汇集成一次提交。重复导入同一次生成不会自动建立原始证据复用关系，不能靠复制同一 `A1` 到多个独立运行来冒充多次作答或无冲突分片。

遵守已有重试合同：只有没有可读答卷的传输暂时失败或超时，才允许在冻结上限内重试；第一份可读答卷立即锁定。拒答、数学错误、交付不完整以及超时前已经返回的可读文本，都不能成为换一份更好答案的理由。

没有执行、执行失败和缺失答卷必须显式保留。导入不会补跑模型、补写证明、修复源码或删除失败槽位。部分提交继续使用完整计划的固定分母，不能把提交子集的平均数改称全基准成绩。

所需 Lean 文件继续以题面约定的命名代码块交付。额外交回的文件必须绑定原始答卷，不能悄悄替换其中的代码。原始输出、提取源码、编译结果和语义审核分别保存；导入成功不表示 Lean 编译成功，更不表示题意对齐。

从仓库直接导出的交换 JSON 使用 `math-gauge.harness-submission/v1`，绑定 `bundle_sha256`、`plan_sha256` 与 `runtime_sha256`。复制包内模板到新的结果目录后，从 `manifest.json` 填入 `bundle_sha256`；不可修改被哈希绑定的原模板。发布数据集另使用上述 v2运行绑定，两个版本均进入同一导入与审核实现。`origin` 为 `external`、`fixture` 或 `replay`，并显式填写 `fixture_only` 和 `declared_external_calls`。离线模板默认 `fixture_only: true`、真实调用数为 0。

每个已执行槽位提交 `slot_id`、完整 `projected_request` 和有序 `attempts`；每次尝试包含序号、状态、请求散列、响应与标准错误文件的路径/字节数/SHA-256，以及实际可知的用量。响应为空时也保存显式的空文件。时间、退出状态及附属原始材料按实际提供。完整可执行的提交构造示例见[使用指南](../docs/usage.md)，包内说明是交付端的独立格式入口。

## 导入与审核

评审端保留原始导出包、外部提交及对应主计划，运行：

```sh
python3 -m math_gauge benchmark-export-check --bundle runs/external-dev \
  --plan runs/external-dev.evaluator/plan.json
python3 -m math_gauge benchmark-import --bundle runs/external-dev \
  --input /absolute/path/to/submission.json \
  --plan runs/external-dev.evaluator/plan.json --out runs/imported-dev
python3 -m math_gauge benchmark-check --run runs/imported-dev
python3 -m math_gauge benchmark-review-template --run runs/imported-dev \
  --out runs/imported-dev-review.json
```

最后一条只生成待填写的审核模板。完成真实数学与交付审核后，再沿用 `benchmark-review`、`benchmark-collect` 和 `benchmark-report`。候选 Lean 核验仍使用现有入口，不能用作者编译记录代替。

导入保存可独立复查的原始提交快照，并验证包、计划、题集、请求历史、响应和父节点绑定。未知题号、重复槽位、分支交叉、正文或附件篡改、路径越界及锁定后重试应被拒绝。输出目录必须是新目录；失败导入不能留下可误当作完成结果的运行。

外部答卷的来源单独记为 `external_import`，不会伪装成 runner 现场调用，也不会把导入重标成一次真实候选调用。离线合成提交须显式标记为 fixture，测试不能成为模型成绩。

本版通用外部导入支持原始材料核验、数学审核和暂定分项分析。现有[正式运行证据审定](execution-evidence.md)绑定了本地调用及隔离探测合同，通用外部提交不会仅凭声明取得正式资格；缺少可审定来源时保留未核实原因，`formal_score` 保持空值。接入一种新的真实运行环境，需要为该环境验证来源与隔离证据，而不是放宽数学标准或制造本地进程记录。

对外报告采用共享 `benchmark-report` 输出，并说明：题集与主计划/导出包身份、公开开发集或保留集身份、请求的模型与可核实的运行来源、冻结工具和预算、各分项计划数与实测覆盖、缺失及失败数、数学与 Lean 审核状态、暂定成绩与正式资格。缺测方向显示空值或固定分母区间；fixture 仅报告软件验收，不报告模型能力。不要把准备包、调用声明或未填审核模板当作完成评测。

## 开发集与未来保留集

本次不删除当前公开参考解、不重写 Git 历史，也不把现有题标成秘密测试题。公开解答便于独立复核，替代正确证明仍可获认可。后续保留集须使用未公开题目与独立评审材料，冻结版本并支持具名复核；仅隐藏公开论文题的本地参考解不保证题目未被见过。

评分维度、总体权重和执行规则可以公开，具体题目的预期真假与关键错误定位仍不得进入候选输入。对未来私有题集也只调用同一导出器、导入器和评分实现，不维护另一套 runner。
