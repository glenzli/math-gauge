# 扩展工程准备 · MG-R011–MG-R020

本目录目前只做整合与运行准备。canonical `/Users/g4i/lab/math-gauge` 仅读，未提交、未推送。根基线为 `73a358afe3657fbee731adea6ef0ba5ce3e53bda`。

当前 R011–R020 全部已接入并核验。R017/R018 使用最终 v2，R019 使用二阶段最终 v2。`integration-state.json` 是可读状态；每份 `frozen-cases/MG-Rnnn.json` 记录来源、白名单、逐文件散列与原 fresh build 复用检查。数学材料原字节不改；根/Astra提供的语义审核只更新 case/review 工程元数据，作者原元数据保存在 integration/results/expansion-v0.4/author-metadata。

当前入口是 `PRETRIAL_READY.json`。二十题索引的53项测试（含3个真实Lean工程fixture，无skip）及validate均通过。十个实际运行目录已准备，逐题12个负文件打开均EPERM，网络探测均通过。尚无推理放行、CLI worker或答卷。

锁定身份：pretrial-freeze SHA256 `d2efede259df8e9090e4664de0a43f9f619f301395e0333406d7ea84f50de895`；suite SHA256 `68a223f0a697fc02d0b4ac20f0be8f88b45d8e0906b6cd8bbaad138832efddde`。219份评审快照文件、110份准备文件及12份流程文件都已绑定。

`receipts/baseline.json` 记录1088个原受跟踪文件；原十题的397个case文件和原输入投影、0.3.0版本及原 suite fingerprint 单独保留。canonical 两个无归属目录 `drafts/true-goal-six-20261029/`、`drafts/public-proof-extractions-20261029/` 原样保留且不入任何操作清单。

已完成一次零推理实际 OS 预探测：11个负文件打开均 EPERM，输入正探测散列一致；现有代理的 loopback7897 可连接，其余测试本机端口均 EPERM。证据在 `policy-preflight/runtime/` 和 `preflight-report.json`。此结果不替代每题实际新配置与实际CLI PID的验收。

实际 CLI 再检查为 CodexCLI `0.165.0-alpha.1.2`，SHA256 `d84a54b031085f01e3ad915ea7c72ebea4dcf69e90f0d1e0e4a637e8280991d2`。当前非推理型号缓存支持请求 `gpt-6.1-terra` / `max`。这不构成后端型号的独立回显。

本轮未另做有推理请求的工具能力 canary；沿用前轮同一二进制的严格工具/上下文关闭设置，重新实测文件/网络策略，并在答题进程中监控全部工具事件。这些证据不应被称作已完成独立能力 canary。

执行顺序（1–4已完成，5以后等待明确放行；所有命令均从本目录或使用绝对路径）：

1. 用 `import_frozen_case.py` 只接入 owner 已冻结、fresh build 通过的逐题交付；用 `apply_semantic_review.py` 绑定明确给出的独立审阅。两者不作数学判断。
2. 全十题冻结后运行 `assemble.py`，追加 suite0.4.0 的20题索引、sources、README与正式Lean索引；原十题仍为0.3.0且逐字节不变。
3. 运行工程单元测试与 validate；用 `finalize_integration.py --dependency-root <既有依赖工程> --lean <固定Lean>` 汇总身份不变的构建证据。无需重编已经证明相同源码的题目。
4. `prepare_trial.py` 冻结 evaluator snapshot、suite/runner指纹与所有运行策略，生成十个全新独立目录，但不启动CLI。随后在宿主执行 `probe_runs.py` 做逐题真实打开/连接探测。
5. 必须等 root 明确放行后才写 `inference-release.json`，绑定 `pretrial-freeze.json` SHA、suite SHA、十题ID、`gpt-6.1-terra`、`max`。没有该放行或任何散列变化，`start_queue.py` / `run_cases.py` 均拒绝启动。
6. 宿主运行 `start_queue.py` 后会启动持久的两并发队列；`queue-supervisor.json` 记录PID和脚本身份，`monitor.py` 只看进程及事件类型/答卷大小，不读取答卷正文。所有失败入账，不自动重试；所有模型会话仅一次task字节stdin。
7. 运行后由root/Astra做独立AI数学审核，工程不评分。审核者知道题面、参考与模型请求标签，不称双盲；先前仅task材料的题面审校另记。按显式白名单打包所有失败、有效答卷、冻结/隔离/身份/账本；state、凭据与编译产物不得进入证据。
8. 最终用 `make_whitelist.py --final --out <新plan>` 生成源SHA和canonical preimage SHA。root同意后才新开DevMesh Run/Claim并受控复制；本轮新增题保持未提交、不推送。

`PROMOTION_PRETRIAL.json` 是298项、尚无模型证据的不完整草案，不能用于落地。更早 `PROMOTION_DRAFT.json` 保留七题阶段。不会删除任何原受跟踪路径，也不对整个drafts或cases目录做镜像删除。

队列运行期间保持绑定的case、operator和prepared文件不变；答卷评审写入新的results记录，避免改变下一题启动所需的冻结身份。
