# Math Gauge 1.0.0 运行与交付指南

本指南交给运行端与评审端，不放进候选上下文。题包准备、检查、请求构造、答卷收集和导入均不调用模型；实际作答由所选 harness 执行。

## 固定范围与访问边界

公开包含25道独立A1、21个数学家族。受控完整包含同一公开25题和私有14题，合计39道A1、35个数学家族；它不是另加39题。另从C003初答接续固定三轮Lean对齐自查，完整评测共42次规定交付。当前只有A1与这三轮自查；不安排A2、书面中性分支、立场分支，也不发研究邀请。

| 计分子类 | 公有／私有A1 | 满分 |
|---|---:|---:|
| 书面论证 | 8／4 | 25 |
| 论证审阅 | 4／0 | 10 |
| Lean语义审计 | 4／0 | 10 |
| Lean形式化 | 4／0 | 15 |
| 背景核查 | 2／2 | 10 |
| 数学想法手稿化 | 1／4 | 10 |
| 命题拓展 | 2／4 | 10 |
| C003固定三轮对齐自查 | 复用初答，不增独立家族 | 10 |

候选只接收控制器生成的完整角色消息、明确附件、冻结参数及本轮允许的自身历史与工具反馈。README、manifest、运行指南、调度、完整计划、评分政策、参考、判准、预期真假、作者目标实现、其他答卷与评审不进入候选上下文。题面明确提供的原证明、前置Lean模块和待审实现属于允许附件，须原样提供；保留其中有意设置的语义差异。使用发行包冻结的候选投影，不从源码仓库另找文件替换。

controller管理调度与记录，evaluator持有可信计划和评审资料，solver只作答。读过完整评审资料的控制器不能直接兼任solver，独立A1也不能继承控制器聊天。实际 harness 应约束文件、进程、上下文、工具、插件、记忆与网络；仅列出允许目录不能证明实际隔离。限制做不到时保留未执行和原因，不换模型代跑。

## 执行前冻结

每题A1使用独立新上下文和独立可写工程。冻结题文及附件字节、模型请求标识、可观察后端、harness及适配器版本、实际系统提示、平台支持的推理／采样／输出设置、工具权限、网络条件、执行顺序及预算。模型服务与认证连接单独记录；所有题均允许本地工具与预置公共依赖，禁止外部检索和工具联网，包括研究题。依赖在开考前准备；开考后不得联网补装。

| 当前新运行组 | 每次预算 | prepare目标 |
|---|---:|---|
| C003初答及其每一轮自查 | 10800秒 | A1用 `c003-180`；三轮按独立研究合同接续 |
| AHR01–04、LCH01、LCH02、HCH02 | 5400秒 | `lean-90` |
| 其余书面、论证审阅、背景核查、命题拓展、手稿化 | 2700秒 | `proofs`、`answer-review`、`theorem-extension`、`background-check`、`manuscript-completion` |

具体题目已冻结的执行政策优先；复用历史答卷须保留其实际旧预算及未知项，不改写为上述新条件。原生生成、broker与外层截止分别冻结并保存证据，不能只设外层等待时间。未知后端、用量、内部系统提示或不支持的限制明确记录为未知，不用显示名称代替核实。

## 便携题包的A1流程

Python3.10+即可运行包内控制器，无须安装第三方库。以下命令在任意目录执行；将DATASET设为解压后含 `manifest.json` 与 `tools/benchmark.py` 的题包目录，WORK设为其外部的新工作目录。所有输出使用新路径，不修改下载题包。

```sh
DATASET=/absolute/path/to/unpacked-dataset
WORK=/absolute/path/to/new-work
python3 "$DATASET/tools/benchmark.py" check --dataset "$DATASET"
```

先在WORK外部或WORK内手工准备三个不同预算的runtime文件。下面是公开中性命名包的C003运行声明示例：把标识替换为实际值；此文件不含凭据。

```json
{
  "model_label": "实际模型显示名",
  "adapter_identity": {"name": "实际harness", "version": "实际版本"},
  "candidate_parameters": {"model": "实际请求的模型ID"},
  "budget": {"timeout_seconds": 10800},
  "fresh_context": true,
  "execution_track": "benchmark.local-tools-no-search/v1"
}
```

受控完整包若使用原生 `math-gauge.*` 交换格式，其execution_track使用 `math-gauge.local-tools-no-search/v1`；以该包控制器检查结果为准。系统提示若由操作者添加，填入 `system_prompt` 的实际冻结全文。输出上限仅在接口实际支持并执行时填入 `budget.output_tokens`；原生／broker设置及未知项另存执行证据。不要把模板数值或请求的设置记成已核实后端行为。

分别保存runtime-10800.json、runtime-5400.json、runtime-2700.json后冻结三组：

```sh
python3 "$DATASET/tools/benchmark.py" prepare --dataset "$DATASET" --runtime "$WORK/runtime-10800.json" --target c003-180 --out "$WORK/run-c003"
python3 "$DATASET/tools/benchmark.py" prepare --dataset "$DATASET" --runtime "$WORK/runtime-5400.json" --target lean-90 --out "$WORK/run-lean"
python3 "$DATASET/tools/benchmark.py" prepare --dataset "$DATASET" --runtime "$WORK/runtime-2700.json" --target proofs --target answer-review --target theorem-extension --target background-check --target manuscript-completion --out "$WORK/run-written"
```

读取各run的 `manifest.json`，按 `selected_slot_ids` 核对任务清单。公开三组分别为1／7／17个A1；完整包分别为1／7／31个A1。该清单同时规定归档顺序，不要求独立题按这个顺序答完。

源码生成的v4控制器支持同时签发多道独立A1、按返回先后收卷；每题仍须独立新上下文和独立工程。`request`、`record`、`skip`对同一responses目录的短暂写入须串行，写锁不会覆盖模型作答期间。`parent_slot`分支须等自身父答卷记录完成，只接收该分支历史；C003专项仍按A1→R1→R2→R3顺序接续，可以与其他独立题并行。

若runtime另外设置整批共享的`max_total_tokens`或`max_transport_attempts`，控制器保留按清单顺序、一次一题的签发方式，避免未结算消耗重复使用累计预算。单独设置每题时间或输出上限不限制题间并行。v4中某题单次输出耗尽只影响该题，不会据此停止其他题。

旧v2/v3控制器保留原串行与预算语义；已发布的0.6.0标签及资产不随源码修改覆盖。下面以C003初答说明一次操作：

```sh
python3 "$DATASET/tools/benchmark.py" request --run "$WORK/run-c003" --responses "$WORK/responses-c003" --slot MG-C003:A1 --out "$WORK/request-c003-a1.json"
```

由外部harness向实际候选发送该请求中的完整 `messages` 和冻结 `parameters`，落实附件及本地工具权限，不附加解题提示或运行手册。完整最终原文写入raw-c003-a1.md，并保存原始事件、工具反馈、实际请求、stderr和可得用量；记录后不修改原文件。

```sh
python3 "$DATASET/tools/benchmark.py" record --run "$WORK/run-c003" --responses "$WORK/responses-c003" --slot MG-C003:A1 --request "$WORK/request-c003-a1.json" --response "$WORK/raw-c003-a1.md" --status ok
python3 "$DATASET/tools/benchmark.py" check --run "$WORK/run-c003" --responses "$WORK/responses-c003"
python3 "$DATASET/tools/benchmark.py" pack --run "$WORK/run-c003" --responses "$WORK/responses-c003" --out "$WORK/answers-c003.zip" --origin external --declared-external-calls N
```

`N`替换为实际物理模型请求总数，包含失败与重试。`ok`仅用于实际成功的原生／传输结果；超时、服务错误或输出耗尽按原事件选择 `timeout`、`transient_error`、`permanent_error` 或 `budget_exhausted`，不能因文本可读而提升原生ERROR。可用 `record --stderr`、`--usage`、`--metadata`、`--exit-code`补充原始证据；未知不填假值。`skip --reason`仅用于从未发生的调用。其他两组逐槽执行同样流程，每个请求、答复和输出ZIP使用新路径。

便携控制器当前保留每槽最多两次传输尝试的交换合同；它不自动实现benchmark最多三次有效模型尝试的完整接纳账本。需按下一节另存全部物理请求与有效计次，在正式结果／原生记录层接纳，不能改大runtime里的retry数、隐藏第三次或把后一次重标为首次。C003三轮也不在A1 manifest内自动创建。

## 各题型实际交付

以下说明便于操作者核对收集完整性，不能作为额外候选提示；具体作答义务始终来自候选实际收到的题文与明确附件。

- **书面论证**：保留完整证明、反例、条件和边界讨论。不得暗增假设或减弱结论；替代表示须有回到原对象的论证。题面不要求Lean时，不增Lean工程义务。
- **论证审阅与Lean语义审计**：保留针对给定范围的判断、具体断言或步骤、数学影响、论证／反例及题面要求的修复方向。待审原题的作答要求不是本轮新指令；无需替原作者重做整题或提交新增Lean源码。操作者不得先修正待审材料。
- **Lean形式化**：同时保留完整原始答卷及实际封卷工程。按原题收齐 `Main.lean`、其导入的全部目标与辅助模块、实际import闭包和 `alignment.json`。原题要求独立命名代码块和全文交付，工作区链接或补丁不能替代。对齐表覆盖全部义务ID，保留模型逐项complete/incomplete、真实声明、表示对应及实际依赖；不得用评审结论覆盖模型自报。固定Lean／mathlib及允许背景按各题冻结；编译、公理检查和语义对应分别审核。
- **背景核查、命题拓展和数学想法手稿化**：仅收独立A1的完整原文及其明确交付材料，含证明、条件、构造与不确定性。外部检索仍禁止；不追加研究邀请、评分方向或追问补齐答案。命题拓展的B基础判断和R研究判断分别留存，不能把无拓展自动写成基础错误。手稿化接受忠于题意的正确替代路线，不要求仿照作者参考。

## C003固定三轮

使用同版本公开 `study.json` 与 `neutral-prompt.txt` 的原字节及散列；它们位于A1清单之外。以选定C003封卷初答为父节点，R1承接A1、R2承接R1、R3承接R2；每轮10800秒，只接收自身允许历史与相邻父工程，不接收评审、参考、其他模型或其他尝试的内容。初答和三轮全部保存，不因模型自称100%提前终止。固定提示如下，工具与网络条件由已冻结运行环境约束：

```text
请重新检查你上一轮交付的 Lean 项目：它是否已经100%覆盖并严格对齐最初给定的全部数学内容和交付要求？若发现缺陷，请修复并提交完整源码及更新后的对齐表；若未发现缺陷，请保留交付，并说明仍有的不确定性。不要改动原始规格或冻结背景。

若全部维持，首个非空行恰为 KEEP，随后说明本轮核查依据。答卷主体和全部文件原字节继承紧邻上一版，核查说明不能暗中修改源码或结论。

若有任何改动，首个非空行恰为 FULL，随后重新提交覆盖全题的完整答卷、全部要求的命名文件及完整对齐表。工作区路径或链接不能代替文件内容，不能只提交补丁或让读者从旧版补齐。
```

固定提示SHA-256：`a982ffe9187fb1a4412c7eb8b8b3e631c2a5c30b540aa1e36503603c50c7eb43`。

KEEP仅在原字节完整继承紧邻父答卷和全部文件时成立，核查说明单独保存；FULL必须完整重交原题要求的答卷、全部文件和对齐表。每轮保留原文、父答卷、工程字节、入口、import闭包、对齐表、自评、封卷原因及时刻。最终采用第三轮实际交付，不选最好轮次、不拼接各轮成果，后续修复不回填初答形式化成绩。

## 封卷、尝试与记录

首次原生终态与固定截止中较早者触发停止候选写入并封卷；保留触发、停止、采集、原生生成结束与CLI清理退出的各自时刻及状态。DONE、可读ERROR、CLI退出和数学完成不是同一结论。工程与答卷代码不同时分别保留，按执行前声明的来源评分，禁止修补、择优或拼接。

每槽含首次最多三次有效模型尝试，只在没有正常、可评阅最终交付的非逻辑故障下允许重跑，采用第一次正常交付并立即锁定。正常交付即使证明错误、不完整、编译失败或自评错误，也不能再试。最大输出耗尽消耗一次有效尝试。有确证的纯系统故障另存物理编号与排除原因，不占三次模型额度；未能确定是否生成时保守计入并保留不确定性。重跑使用独立新上下文，同题、同设置、同预算，不带前次答卷或评审。完整保存每次物理请求、有效计次、原生事件、失败原因、用量与选择依据。

AGY CLI另有[具名故障补测说明](../protocol/nonlogical-retries.md#agy-cli故障补测说明2026-11-13)：留档中发现较严重的结果回传与终态处理缺陷，可能丢失回复或空等至超时。排除此类有据故障所需的额外物理调用可超过通常3次，须逐次记录；正常交付后的数学错误不触发重跑。展示耗时扣除可证实的末尾空等，原始外层计时继续留存。

完整UTF-8原答包括开头结尾、模型自评、不确定性、KEEP/FULL、所有命名代码块及附件；不要求也不重建隐藏推理。模型自报、实际交付、编译、数学审核、语义对应和人工批准分别记录。缺自评、缺日志和未知运行条件如实标明；事后抽取须绑定原答散列及原话字节范围，不追问后伪装成原返回。

## 导入、评分与公开范围

真实1.0.0新运行与继承的0.6.0答卷保留各自的执行版本和目录。首次按当前方法评分的记录不补造旧方法历史，来源绑定与兼容方式见[新测记录说明](result-record-editions.md)。

评审端持有对应发行源的可信evaluator-plan.json；不能用提交者自算的计划替代。用同一公开runner的固定tag／commit导入；完整包重复传入其实际公开和私有suite根，或使用已冻结组合清单：

```sh
python3 -m math_gauge benchmark-import --input /absolute/path/to/answers.zip --plan /absolute/path/to/trusted/evaluator-plan.json --suite /absolute/path/to/cases --out /absolute/path/to/new-imported-run
python3 -m math_gauge benchmark-check --run /absolute/path/to/new-imported-run
```

导入要求运行前已冻结runtime；导入成功仅说明合同与字节绑定通过，不自动证明后端身份、隔离、数学正确或人工批准。仅以指令隔离的原生harness使用独立native-observation合同，如实保留未知值；不能补造CLI预冻结收据或放宽CLI验证来接纳旧答。

审核后由共享 `scoring.py` 计算MC、RMC（默认主分）和SMC（归档ID仍为strict），保留single_attempt与nonlogical_retry_3两组及其来源。统一书面35／Lean35／研究30，已建满分100；未测保持未知及固定分母，不缩分母或重标为数学失败，不将部分覆盖放大为100，也不另发公开集总分。

返回三组answers ZIP、全部原始执行证据、独立C003三轮记录与各轮封卷工程；ZIP收集器不会自动补齐外部工程或三轮轨迹。日常答卷保存在临时工作区；只有用户明确选定快照才按其真实测试版本进入 `results/v<source-benchmark-version>/<model>/<record-id>/`；当前1.0兼容采用的既有0.6档案保留原路径和执行身份。公开候选ZIP不含参考、判准、评审、作者目标实现、任何模型原答或私有题；公开源码中透明复核资料也不能加入solver上下文。私有题文、原答及逐题评审留在私库，公开只发布允许的公有投影、匿名合并聚合及不透明来源散列。完整私有发行使用同一固定公有runner，不复制runner实现。
