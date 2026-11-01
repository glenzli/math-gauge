# Math Gauge 0.2.0

本包提供43份数学与 Lean 任务，可接入任意外部 harness。版本0.2.0也是题集版本。所有题都是公开开发题，仍待人工审定；本包没有真实模型成绩，也不声称题目或公开参考从未被模型见过。

需要 Python 3.10+，无需安装第三方 Python 包、Math Gauge 或 Codex。`tools/benchmark.py` 是可选的操作者工具：检查材料、准备运行、构造消息、保存尝试和打包；它不调用模型或编译 Lean。模型接入和上下文隔离由你的 harness 完成。自行实现控制端时，也必须保留下文相同的完整消息、原始请求、全部尝试和分支历史合同。

解压后的目录只有一份操作说明：

```text
math-gauge-v0.2.0/
  README.md
  cases/<题号>/
    task.md
    files/<题目约定的附件路径>
  tools/benchmark.py
  manifest.json
  LICENSE
  THIRD_PARTY_NOTICES.md
```

`files/` 仅在该题有附件时出现。所有43题都已包含，无需另外下载题目。整章形式化题约定提供的含证明原文和跨章 Lean 定义，以及语义审计题的给定源码，都保留在附件中。

README、工具、清单、运行配置和调度只供操作者使用。候选题目输入使用下文 `request` 输出的完整 `messages`；其中已包含本题的题面、约定附件和本轮允许的历史，工具反馈另按事前冻结的运行条件处理。不要把整个目录、其他题、控制说明、参考、评分或作者证明交给模型。GitHub 自动生成的 Source code 压缩包含公开评审材料，不能代替本任务包。

## 1. 检查并准备一次运行

以下命令均在解压后的 `math-gauge-v0.2.0/` 内执行。运行目录、每次请求文件和最终ZIP均使用新路径，不覆盖旧记录。若同时取得 `SHA256SUMS`，先在 ZIP 所在目录用 `shasum -a 256 -c SHA256SUMS` 核对下载；Linux 也可用 `sha256sum`。

```sh
python3 tools/benchmark.py check
```

在题包旁创建 `../runtime.json`，将模型和平台替换为实际选择：

```json
{
  "model_label": "所选模型与设置的显示名称",
  "adapter_identity": {"provider": "实际平台", "kind": "external-harness"},
  "candidate_parameters": {"model": "实际请求的模型ID"},
  "budget": {"timeout_seconds": 120, "output_tokens": 16000},
  "fresh_context": true
}
```

`model_label`、`adapter_identity`、`candidate_parameters.model`、正的 `budget.timeout_seconds` 和 `fresh_context: true` 必填。预算数字仅演示格式，尤其不是整章任务的推荐预算。示例中的 `budget.output_tokens: 16000` 只适用于实际传输支持且会执行该输出上限的情况；执行前须核实。

仅当实际传输没有受支持的输出上限时，才可省略 `budget.output_tokens`。省略表示使用平台默认输出策略，实际限制未知；必须在 `adapter_identity` 及运行前冻结的操作者说明中明确记录。不得发送会被忽略的上限字段，也不能仅凭配置声称上限已生效。允许的其他生成参数可放入 `candidate_parameters`，可选预算包括 `max_transport_attempts`、`max_total_tokens` 和按题号指定的 `case_parameters`。

`max_total_tokens` 只根据真实返回的 `total_tokens` 在达到阈值后停止新请求；用量缺失时停止后续调度并记录无法核实。单个在途请求仍可能超过阈值，因此它不是硬费用上限。

上例未设置 `execution_track`，保留默认无候选工具条件。选择本地工具、禁止联网检索/外部搜索的条件时，在同一 runtime 对象中增加以下字段：

```json
{"execution_track": "math-gauge.local-tools-no-search/v1"}
```

该条件只开放 `exec_command`、`write_stdin`、`apply_patch`，禁止联网检索/外部搜索和工具联网；本地题面与预置公共依赖中的内容/API查找仍允许。可读取本地工具输出，包括本地编译反馈；不提供评审者的正确性或编译反馈。这是权限声明，不增加使用工具或 Lean 的提示、义务或最低用量，原题的 Lean 交付要求不变。两种条件使用相同题目与177槽历史安排，分别标记和报告，不能混成同一条件的成绩。实际工具权限、离线文件边界和固定依赖仍由操作者核实。

原题面与附件保持原样。后续自查提示则在运行时按冻结条件投影：默认无工具条件保留原始字节；本地工具条件仅将末句“本轮不能调用工具或查询外部资料。”替换为“本轮不得访问网络或进行联网检索。”。数学断言、立场措辞及 KEEP/FULL 格式不变，不另加使用 Lean 的建议。题包中的原始提示不修改，运行清单绑定 `followup_prompt_projection` 版本，记录分别保存原始与实际提示的散列。因此不能把本地工具轨道描述成所有消息均未经投影。

没有投影版本的旧本地工具运行须由其封存的原控制器和源码解释；不要在旧运行目录升级或重写提示。新条件必须另建带明确投影版本的运行。

```sh
python3 tools/benchmark.py prepare --runtime ../runtime.json \
  --target all --out ../run-model
```

这只创建新的运行目录，不发起模型调用。原题包保持不变。换模型、预算或实验条件时，另建运行目录。`--target all` 运行完整计划；四类任务可分别选 `proofs`（书面论证）、`lean-audit`（语义审计）、`lean-construction`（生成与修复）、`chapters`（整章形式化）。`core` 或 `repeat` 选择全部独立初答，`neutral` 选择中性复核，`stance` 选择支持与怀疑复核，所需A1自动包含。可重复传入 `--target`。部分运行的未测部分保留缺测，不能重新归一化成完整成绩。

`../run-model/manifest.json` 的 `selected_slot_ids` 给出必须遵守的槽位顺序，`execution` 保存冻结调用条件。完整计划有177槽：43题各三次独立初答，预选八题再各开三种两轮复核分支。

## 2. 取得完整消息，保存每次原始答卷

先建立题包外的工作目录。下面以完整计划的第一个槽位为例：

```sh
mkdir -p ../requests ../raw
python3 tools/benchmark.py request --run ../run-model --responses ../answers-model \
  --slot 'MG-GF101:A1' --out ../requests/gf101-a1.json
```

将请求中的完整 `messages` 和冻结生成参数原样交给实际平台；不能只发送 `task.md`，也不要添加解题提示。工具同时保留这份构造的请求，记录答卷时会检查绑定。实际发送过程及平台返回信息仍须由 harness 如实保存，工具生成请求本身不能证明平台收到了什么。

模型返回后，把完整原始响应按原字节保存到 `../raw/gf101-a1.md`，再执行：

```sh
python3 tools/benchmark.py record --run ../run-model --responses ../answers-model \
  --slot 'MG-GF101:A1' --request ../requests/gf101-a1.json \
  --response ../raw/gf101-a1.md --status ok
```

不要删改解释、代码块、拒答或未完成部分。Lean 源码按题面要求保留在命名代码块内，不能在记录前修复。工具自动复制原始字节、计算完整性字段并累计尝试，无需手写散列或提交 JSON。

按实际情况可加 `--stderr ../raw/error.txt`、`--usage ../raw/usage.json`、`--metadata ../raw/provider.json`、`--exit-code 数值`。`usage` 只含实际已知的非负数值字段，总 token 用量使用 `total_tokens`；带嵌套结构的平台原始返回可原样放入 metadata JSON 对象。平台返回的模型、请求标识、时间及原始请求/响应记录也保存在该对象中。没有返回的信息保持未知，不填猜测值、不用本地保存时间代替生成时间，也不把请求型号当成平台身份的独立核验。省略的用量保持空对象。

按 `selected_slot_ids` 对其余槽位重复取请求、调用和记录。`A1`、`A2`、`A3` 必须分别使用全新上下文，不含其他初答、其他题、评审反馈或跨题记忆。

有失败也要记录：`--status` 可用 `ok`、`transient_error`、`timeout`、`permanent_error`、`budget_exhausted`。无响应时保存并引用一个空文件；仍有文本的超时要保留全部文本。只有没有可读答卷的暂时传输失败或超时，才可重试；第一份可读答卷立即锁定，数学错误、拒答或格式不全不能重抽。每槽固定最多两次尝试；runtime 的 `retry.max_attempts` 只能为2，等待时间 `wait_seconds` 和可重试退出码 `retryable_exit_codes` 可在允许范围内事前配置。

重试时先对同一槽位再次 `request`，为 `--out` 使用新文件名，再用对应请求文件记录这次返回；不覆盖第一次请求或失败记录。

决定不执行某槽位时，明确留下原因后继续：

```sh
python3 tools/benchmark.py skip --run ../run-model --responses ../answers-model \
  --slot 'MG-GF102:A1' --reason '实际未执行的原因'
```

这个例子仅用于确实未执行的第二槽，不能用来隐去已发生的失败。缺少可读父答卷的后续节点会保留阻塞状态，不制造答案。中途结束也可直接打包，其余槽位继续明确标为待执行或阻塞。

## 3. 复核分支只使用自己的历史

预选八题的 `neutral`、`affirm`、`deny` 分支都从同一份锁定 `A1` 独立开始，各有两轮；互相不可见。到达相应槽位时，工具自动从已记录的原始答卷取出所需父节点，例如：

```sh
python3 tools/benchmark.py request --run ../run-model --responses ../answers-model \
  --slot 'MG-GR002:neutral:1' --out ../requests/gr002-neutral-1.json
```

不能跳过前序槽位运行此例。仍将完整 `messages` 交给一个只见到该分支历史的上下文，再像初答一样记录该轮原始返回。第二轮换为 `MG-GR002:neutral:2`；其他分支同理。不要手工拼接答案映射，也不要加入评审者的正确性或编译反馈。

复核返回 `KEEP` 时继承紧邻父节点的完整答卷；`FULL` 时重新交付整份答案和所需源码，不能只写修改摘要。固定提示会告诉模型具体格式。候选工具按已冻结条件配置，不把权限说明增补为解题提示；三条分支之间不共享工具状态或文件。harness 的取题、传输和保存工具本身不属于候选工具权限。

## 4. 一条命令打包返回结果

完成或停止后，把 `N` 替换为实际平台调用总数，包含失败和重试；仅在确实执行了真实外部调用时使用 `--origin external`：

```sh
python3 tools/benchmark.py pack --run ../run-model --responses ../answers-model \
  --out ../answers.zip --origin external --declared-external-calls N
```

若只是离线测试，不写这两个选项，默认保留 fixture、真实调用数0；复放用 `--origin replay`，不能把合成或复放结果标成真实调用。

**交回 `answers.zip` 即可**，执行端不需要评审计划。ZIP 内含 `answers.json`、冻结的 `run/` 和 `submission/` 中的原始尝试及提交，评审端可统一核验。无需另填模板或挑选最好答卷；保留本地原始材料，未执行、失败及缺失都不会被打包抹去。

## 5. 评审端统一接收

本节供持有原题集和可信完整评审计划的评审者使用。把收到的 `answers.zip` 放入仓库根目录；以本地0.2.0构建输出为例：

```sh
python3 -m math_gauge benchmark-import --input answers.zip \
  --plan runs/releases/v0.2.0/evaluator-plan.json --out runs/imported-model
```

这一条命令核验包内路径、材料、冻结配置、顺序、历史、全部尝试和原始文件，并导入共享运行记录。它不运行包中程序，不调用模型，不编译 Lean，也不判断证明正确。输出目录必须是新路径；单纯导入成功不能成为分数。

继续通过同一审核与报告入口完成实际审核：

```sh
python3 -m math_gauge benchmark-review-template --run runs/imported-model \
  --out runs/imported-model-review.json
# 实际逐项审核并填写后：
python3 -m math_gauge benchmark-review --run runs/imported-model \
  --input runs/imported-model-review.json
python3 -m math_gauge benchmark-report --run runs/imported-model \
  --out runs/imported-model-report
```

原始来源核验、数学审核、适用的候选 Lean 核验和人工批准分别记录；AI 复核或作者 Lean 编译不能替代它们。通用外部导入保留来源未核实状态，只能作明确标注的暂定分析，不能靠声明自动取得正式比较资格。缺测、执行失败和未决保留固定分母及未知值，不把部分完成报告成全基准分数。当前43题仍待人审，没有真实模型通过率或正式分数。
