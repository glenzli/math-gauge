# R005 竞争函数范围澄清与单列补测方案

状态：仅准备方案。2026-10-30；编写者 `/root/alignment_research`。本文不改题集、catalog、首轮冻结代码或运行证据，不发送模型请求。R011–R020 的新答卷初审优先。首轮全部运行、评分、证据归档和离线复算完成后，才实施下列新版本工作；数学请求还须独立的新 release。

## 当前问题与不变的首轮

MG-R005 当前版本为 `0.3.0`。可见题面给出了 `f,G:E→[0,+∞]`，但“所有不超过 f 的下半连续凸函数”没有单独写出竞争函数 h 的值域。参考与现有作者 Lean 已处理允许负无穷的扩展实数竞争者；可见文字仍应明确这个范围，不能让考生依靠隐藏参考推断。

首轮保留原始 task/reference/rubric、两个原答卷、原始执行收据、全部审核及最终裁定。原题解释敏感性在首轮报告中单列，不用新题面回改旧题的字节或事前评分依据；也不用补测答案替换任何首轮分数。新版本补测只回答澄清后的题面，属于观察到首轮后安排的补充实验，不能称事前独立样本。

首轮 freeze SHA-256：`df6ae5742b9609cb634eba026f478614b39207743b205c7465d62a14d1f23d73`。当前材料只读身份如下：

| 文件 | SHA-256 |
|---|---|
| task.md | cda77a5ed5e6ece09a0159cff60b232092fb1c20c0ce8eec669fe832bc23f0bb |
| reference.md | e95b3aa010968a109248e39a018c3d712257ff41da8384a3b5551141bd318d09 |
| rubric.json | 1ef16c8932393e82ac8e5cbb2b5caab07d9f0921cd7699e59f6c93df5490595f |
| formal/ConvexCostExtras.lean | 67dd03c1c597eae297f0fcd81a67528a498abb2751d09f8bace1c7f9d7dac4a3 |
| formal/COVERAGE.md | b8c23465c228852e0a69920bbf592b652c7c6cd6c0a990dd0fc48afb6d552995 |
| formal/manifest.json | 9d37e2409cb0dc97ef054b1cf1163947dd81fdaf85768bee38db1e3c7fa4cb2e |
| formal/current-formal.json | 163d20994bea279c1d7fa3a63d15eec3b4337d017730d43e38196fef0ffa1929 |

## 候选可见的最小澄清

保留原空间、f 的非负值域及有限点、全部有限维观测、原始纤维下确界、记录关系和 G 的非负值域。只把最大性的竞争类和扩展值约定明确写入题面。拟替换的目标文字为：

> 从这些记录构造下半连续凸函数 (G:E\to[0,+\infty])，满足 (G\le f)，并使对每个函数 (h:E\to[-\infty,+\infty])，只要 (h\le f) 且 h 下半连续、凸，就有 (h\le G)。这里 h 允许取负无穷，不要求 h 正规或非负。本文以实高度上图
> 
> \[
> \operatorname{epi}_{\mathbb R}(h)=\{(x,t)\in E\times\mathbb R:h(x)\le t\}
> \]
> 
> 的闭性与凸性分别定义下半连续性与凸性。建立观测空间扩大时记录之间的关系，并说明整族记录如何确定 G。请给出主定理、构造及完整论证。

该定义用扩展实数的序关系和实高度上图，避免对 (+\infty+(-\infty)) 的加法作未约定运算。它不是要求考生必须采用上图证明路线。题面不加上一轮答卷、失误提示、参考证明或“用 max(h,0)”等解题提示。

新 rubric 明确要求最大性覆盖上述完整竞争类，同时继续接受有效的直接上图、仿射分离、共轭、或先规约到非负竞争者的证明。不能仅以“proper Fenchel–Moreau 已证明”为由略过非正规竞争者；但任何正确处理完整竞争类的短论证都可通过。可选精细投影等式和例子仍不是最低完成要求。

## 版本、数学与作者 Lean

1. 首轮归档核验后，按 root 已确认的正式修订，将 `cases/public/MG-R005` 从 `0.3.0` 提升到 `0.3.1`、public suite 提升到 `0.4.1`；case ID 和母题身份不变。旧版本逐字节保存在首轮 archive，当前 41 题 catalog 刷新后指向新版本。补测另用仅含 R005 的单题 catalog，它可指向包含 20 题的 public suite 并只选择 R005；不复制整套题或 runner 到新 draft。为保持 Suite 指纹，执行证据快照仍按共享 Suite 的显式文件集合保存，其余 19 题不会提交给候选。先完成 task/reference/rubric/COVERAGE/review 及作者 Lean 的复核，再冻结单题补测。
2. 数学复核须确认完整竞争类、所有无穷端点、闭凸上图约定及原始记录关系。参考可直接保留闭上图包含论证：h≤f 给 epi(f)⊆epi(h)，闭性给 closure(epi(f))⊆epi(h)，从而 h≤G。无需断言每个可取−∞的竞争者都有实值仿射下界。
3. 已存在 `MathGauge.ConvexCost.reconstruct_maximal_ereal`：输入 `h:E→EReal`、`LowerSemicontinuous h`、`h≤f`，结论 `h≤reconstruct f`；没有 h 正规、非负或不取−∞的假设，甚至不需额外的 h 凸性。其证明用真实实高度上图，G=+∞时按序关系直接处理，G有限时取闭上图高度。因此不能把新任务描述成“现有作者 Lean 只处理 proper h”。
4. 新题采用实高度闭上图约定，仍须核对它与该 Lean `LowerSemicontinuous` 假设的对应。可证明二者等价，或增加接受 `IsClosed {p:E×ℝ | h p.1≤p.2}` 的直接包装声明；是否需要新增 Lean 源码由精确语义复核决定，不能只凭编译通过宣称对应。COVERAGE 必须明确 h 的 EReal 值域和两个无穷端点。
5. task/reference/rubric 改变后，重建新 manifest 的输入散列、模块散列、顺序与 CurrentAudit 绑定。现有 coverage-only `rebind_coverage.py` 不适用，因为变更不止 COVERAGE；不得把旧报告改写成核验新题面的报告。用共享 `scripts/formal/verify.py` 对新 R005 清单定向核验，保留旧报告和新输出。复用只读 Mathlib 缓存，不全库重编：Lean 4.29.1、Mathlib `5e932f97dd25535344f80f9dd8da3aab83df0fe6`。检查全部 MathGauge 声明公理依赖，仅允许既有三公理。
6. 新数学/语义复核、作者编译与人审状态分别登记，human 仍 pending。与新题面绑定的完整作者覆盖确认后，才冻结补测。

## 单题双模型补测

建议使用全新的 `/private/tmp/math-gauge-r005-clarified-20261030/` 和独立持久结果目录，例如 `results/r005-clarified-v0.3.1-20261030/`。每个模型各一个全新 session、一个标准单题 run、一次数学提交；顺序仍先 Terra 后 Gemini，候选超时仍为 2700 秒，不重试、不替换型号、不购买额度或自动使用重置券。只有一个题目，因此每阶段实际并发为 1，原并发上限无需扩大。

沿用请求配置 `gpt-6.1-terra/max` 与 `gemini-3.8-flash-high/high`。复查二进制身份和非推理型号清单；能保留原固定 CLI 字节时保存其精确散列及新固定路径。二进制或支持档位若变化，记录并停止自动沿用，不静默改模型。请求型号与实际回显分开；Terra未回显字段、Gemini effort未回显字段仍保留未知，不能因请求参数而补成观察值。

隔离机制保持首轮：双方纯文字、无浏览/搜索/文件/命令/MCP/协作能力，无现场 Lean 或评分反馈；AGY strict/text-only agent只允许finish，内部manage_task事件单独记录。AGY拒绝loopback；Terra仅沿用已授权且重新核验的系统代理127.0.0.1:7897例外，其余loopback负probe不放开。新session重做实际文件打开和网络拒绝probe，启动时核对父/worker PID策略；所有旧题、旧答案、参考、rubric、历史、记忆和新版本作者工件均在拒读根内。只复用必要认证机制，不复制旧session或对话，不读凭据正文，不修改原凭据。必要的非数学能力预检独立计数，不混入两次数学提交。

所有候选输入仍由 `Suite.load`/`Suite.request` 和共享 `candidate_message` 生成，双方新版本的排序JSON请求及UTF-8消息散列须完全相同。无附件仍只发task；不给首轮反馈或修题说明。新 freeze 绑定单题版本、suite指纹、request/message/rubric散列、源码、CLI与隔离证据；root独立签出新 release，绑定新freeze与单题catalog，不能复用首轮release。

**当前41题薄调度器不能直接当作单题入口。** `catalog_suites` 要求恰好41题，旧队列结束统计固定82条。补测时另建最小单题调度入口，只调用共享 `math_gauge.execution.run`，可复用现有独立session准备、探测及 `cli_adapter.py`；不复制runner，也不修改已冻结的首轮调度代码。新的薄入口自身散列也纳入新冻结绑定。统计基数从补测清单实际取得：1题、2模型、最多2次数学请求。

每次提交保留原始事件、stdout答案、stderr、账本、PID/probe、run_id、request/response/record及绑定run_id+model_label的执行收据。基础设施或工具条件失败则停新请求、保留所有尝试；过滤未答也保留为本次终端输出，不换题面再试。缺证据的请求数保持未知，不能补写零。

## 独立评分与验收

补测评分只用冻结的新版本义务和原样新答卷，另存初审及争议复核。候选没有提交Lean义务，不能因未给Lean失败；作者Lean也不能替候选证明。每模型的一次答案分别绑定新版本、响应散列和执行收据，不因结果好坏选样。

用保存的共享 `compare_models` 生成单题补测报告，清楚列出原 `0.3.0` 与澄清后 `0.3.1` 的版本关系、澄清缘由及新旧两轮结果。首轮完整41题分母与原评分不动；补测只在自己的1题分母中报告。不得拼成“修正后的首轮41题成绩”，也不得把同母题两版本视为独立能力样本。补测完成后同样白名单归档并离线复算，排除state与凭据。

开始实施的门槛：首轮运行终止；全部首轮评分与报告冻结；首轮白名单归档、82条执行完整性审核及离线复算完成；新题面的数学/语义/作者Lean证据通过；新session预检通过；root发布新的release。本文只规定这些后续动作，当前没有执行它们。
