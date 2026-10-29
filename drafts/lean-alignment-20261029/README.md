# Lean 对齐：首批六个母题、十二个版本

这批题把原文—Lean 对齐拆成判定、生成和修复三个任务，共用 Math Gauge 的 runner，已纳入[现行 41 题目录](../../exercises/README.md)及[首轮双模型比较](../../results/full-comparison-20261030/comparison.md)。所有题目仍为 draft / human pending。作者形式化、自检、非作者 AI 审核与人工审定分别记录；作者核验阶段的证据见[审核清单](reviews/status.json)，实际候选成绩见比较报告。

## 题目布局（出题侧）

| 母题 | 判定版本 | 另一版本 | 所测数学义务 |
| --- | --- | --- | --- |
| 商环中的理想幂零 | [F101](MG-F101/task.md)，失配 | [F102](MG-F102/task.md)，生成 | 在实际商环中建立理想幂零及商映射性质，识别把结论移入假设 |
| 生成拓扑的泛性质 | [F103](MG-F103/task.md)，正确 | [F104](MG-F104/task.md)，修复 | 最粗拓扑、连续性方向与泛性质是否完整对应 |
| 陪集切片与有限覆盖 | [F105](MG-F105/task.md)，正确 | [F106](MG-F106/task.md)，生成 | 从实际非空切片和 Ruzsa 覆盖得到定量陪集代表，不暗加群的有限性 |
| 加权序列乘子 | [F107](MG-F107/task.md)，失配 | [F108](MG-F108/task.md)，修复 | 真实解、唯一性与精确阶数估计，区分加强输入后的弱实现 |
| 有限记录下的轨道筛选 | [F109](MG-F109/task.md)，失配 | [F110](MG-F110/task.md)，修复 | 停顿条件下安全包含、等价失败与附加条件下恢复 |
| 扩展非负值上界 | [F111](MG-F111/task.md)，正确 | [F112](MG-F112/task.md)，生成 | 零值、有限正值和无穷值的不同作用，以及最小系数是否取到 |

共 6 道判定（3 正控、3 负例）、3 道生成、3 道修复。每个母题的两份任务有共同数学内容，不能作为相互独立的十二个数学样本，也不能跨训练/测试划分。同源答案必须在独立会话投放。表中标签与全部评审材料不进入候选请求。

## 来源与范围

- F101–104 由 ProofNetVerif 中真实形式化候选的错误机制出发，保留具体来源并独立扩展数学任务；不把改编后的每个模块说成原模型原始输出。
- F105–106 抽取 RLM25 所选 PFR 工程中的有限集覆盖步骤。题目给定子群及非空切片，不测熵论如何构造该子群，也不声称覆盖整个 PFR 定理。
- F107–108 借鉴公开原文与形式化估计阶数差异，独立构造可完整核验的序列乘子模型。它是可控机制题，不是原 PDE 的重证明，也不据此否定原论文。
- F109–112 使用公开数学结构独立构造，受 OET 对定义域、条件和扩展值边界的审阅经验启发；不抽取未发布正文，不指称当前 OET 工件存在失配。

逐题 source-notes.md 和 [来源清单](sources.json) 记录固定版本、取材范围、许可与独立改编。公开材料可能已进入模型训练；本批尚不能说明未见数据上的能力或实测难度。

## 如何使用

在仓库根目录使用现有入口：

```sh
python3 -m math_gauge validate --suite drafts/lean-alignment-20261029
python3 -m math_gauge prepare --suite drafts/lean-alignment-20261029 \
  --case MG-F105 --out /absolute/path/to/new-candidate-directory
```

生成与修复题在最终回答中交付带文件名的完整 Lean 代码块；runner 将回答冻结为 response.md。评审者从冻结答卷提取源码并记录文件身份，不能把临时工作目录里的文件或作者参考编译当作候选成绩。详见 [题包协议](protocol.md) 与 [runner 边界](runner-requirements.md)。

作者参考及固定候选输入使用公共验证器。`MG-F` 题号支持及合同测试已接入；2026-10-30 通过下列正式入口，在每题独立的新目录中重新编译十二题，全部通过。引擎、依赖和原始命令见 [本次核验记录](validation/canonical-20261030/invocation.json)，接入状态见 [兼容记录](validation/canonical-20261030/integration.json)。此前的临时预览报告保留为历史证据。

```sh
python3 scripts/formal/verify_suite.py \
  --suite drafts/lean-alignment-20261029/formal-suite.json \
  --dependency-root /absolute/path/to/pinned-dependency-project \
  --lean /absolute/path/to/lean-4.29.1 \
  --out /absolute/path/to/new-alignment-verification --jobs 2
```

Lean 固定为 4.29.1，Mathlib 固定为 `5e932f97dd25535344f80f9dd8da3aab83df0fe6`。各题 manifest 绑定题面、参考、rubric、COVERAGE 和全部 Lean 源码；共享审计器检查所有 MathGauge 声明的公理依赖。输入失配题也应能通过内核检查，失配判断来自单独的数学与覆盖审核。

## 审核与验证记录

- 十二题的非作者 AI 数学与对齐审核通过；191 条审核文件哈希、12 条 manifest 哈希、55 份编译日志及其编译产物均与当前工件匹配。
- 最终作者核验通过 43 个源模块及 12 个生成审计模块，审计 370 个声明；没有发现标准公理白名单以外的依赖。此结论不表示原文自动对齐，也不是候选模型成绩。
- 本批作者核验阶段的仓库测试运行 74 项：69 项通过，5 项需要另一套 4.36 环境的测试跳过。本批 4.29.1 的实际编译、公理拒绝和导入隔离测试已运行，F 系列的两项合同测试通过；当时默认二十题和本批十二题验证均通过。后续全题集工程检查另见[最终验收](../../results/full-comparison-20261030/validation/finalization/README.md)。
- [非作者审核协议](reviews/PROTOCOL.md) 与 [最终审核状态](reviews/status.json)。
- [实际候选投影校验](validation/canonical-20261030/projection.json)：通过同一 Suite.prepare 导出，检查题面原字节、附件身份和评审材料隔离。
- [共同核验清单](formal-suite.json) 与 [最终作者编译报告](validation/canonical-20261030/formal/report.json)：绑定固定版本的作者工件；编译前后公共引擎身份一致。
- [工程测试](validation/canonical-20261030/repository-checks.json) 与 [证据绑定](validation/canonical-20261030/evidence-binding.json)。

本批继续使用独立 suite，不自动替换默认题集。上面的作者核验与工程检查不能当作候选模型成绩；后续试跑的答卷、原样候选编译和评分另见全题集比较。编译通过、对齐审核通过与题目具有区分度是不同结论，AI 审核仍不等于人工批准。
