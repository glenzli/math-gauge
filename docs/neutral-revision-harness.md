# 中性续答的外部交付

此工具只整理来源和回交证据，不调用模型、不接触凭据、不评分。按当前选定的完整来源报告选题；任一 MC／RMC／SMC 已知失分即续答整题，首答全满、Lean 与 C003 不进入本流程。已完成并接纳的续答保留来源，不重跑。未知原文不视为数学错误。

在公共仓库之外生成本地完整包：

```bash
python3 scripts/export_revision_bundles.py --private-root /PRIVATE/REPOSITORY --out /PRIVATE/NEW-OUTPUT
```

每个模型及effort配置有独立目录及压缩包。`candidate/`仅含通用标准／中性邀请，以及各题原题、全部提供材料、自己的完整原答（含自评）和明确交付附件。`operator/`保留题号与别名映射及不透明来源散列；真实源路径、原成绩与完整选择依据保存在不外发的 `evaluator/` 索引。执行时只向候选提供单题材料或构造的请求。私有原题和原答不进入公共仓库、网站或公开发行包。GLM 默认列为 `excluded_partial`；Dot保留未知后端与未核实的effort，不推断型号。

2026-11-20的外部交付选中11个尚未完成续答的配置，共200题，每个配置单独回交一份`RETURN.zip`。9个GPT配置的68份续答已在本地采用，不进入这次外部待跑包；GLM跳过。总包只便于下载分发，不能把各模型原答混入同一候选上下文。具体文件、题数和散列以随包`INDEX.json`为准，执行者从`README.zh.md`开始。

两个通用候选文本的唯一来源是 [标准](../protocol/neutral-revision-candidate-standards.md)及[邀请](../protocol/neutral-revision-candidate-invitation.md)，与19份新调用研究中的文本逐字相同。3份复用旧中性试验保留其自身真实提示，差异由接纳记录说明。

可用原生来源会话时记录真实会话身份、上下文和运行参数；否则显式使用来源绑定材料重放。不得继承评审聊天、其他模型答卷或未提供历史。原答没有正常交卷时，原截止内容保持该状态，不补造成最终答复。每题一次有效续答，上限2700秒，允许本地工具／预置公共依赖，禁止检索和工具联网；不新增Lean义务。第一份正常最终回复即停；输出耗尽不能触发质量重试；纯系统故障须保留原生证据与物理请求，按现行规则另审。

包内 `tools/revision.py` 是共享实现生成的 Python 标准库工具，移动包后可直接使用：

```bash
python3 tools/revision.py check
python3 tools/revision.py request --task R001 --runtime ACTUAL-RUNTIME.json --out REQUEST.json
python3 tools/revision.py collect --returns RETURNS --request REQUEST.json --status normal_final --response COMPLETE-RAW-REPLY.md --attachment DELIVERED-FILE.md --metadata ACTUAL-METADATA.json
python3 tools/revision.py pack --returns RETURNS --out RETURN.zip
python3 tools/revision.py import --archive RETURN.zip --out IMPORTED
```

实际调用继续使用已有原生界面或控制器，不要求各家实现新runner。`--attachment`只接收明确交付文件，`--evidence`保存原生事件及运行凭据。正常答卷保留全部原文，不截去自评；失败状态可用 `cutoff_without_final` 或 `maximum_output_exhausted`。运行信息缺失保留null，不以声明认证后端或隔离。

回交格式为 `benchmark.neutral-revision-return/v1`：每题保留实际物理请求序列、完整原文及文件描述符。导入结果 `benchmark.neutral-revision-import/v1` 绑定原包、来源答卷、实际新请求和回交文件，状态为数学与运行审核待审；不冒充旧CLI记录或人工批准，不自行改变三评分。

This offline helper exports source-bound neutral revisions and preserves original
returns. Candidate and operator projections are separate. Every package remains
local/private; only per-model counts and opaque hashes form its public-safe
summary. Imported answers await source and mathematical review and do not alter
scores automatically.
