# 贡献指南

先读[项目首页](README.md)、[评测协议](protocol/evaluation.md)及相关题目的完整材料。当前基准为43份完整试卷，所有公开与私有题集使用同一runner。

## 数学材料

保留实际对象、结构、量词、定义域与结论强度。不得默默增加分离性、完备性、紧性、有限维、统一常数或额外公理，也不得把目标结论放进假设后取回。假设或结论有意变化时，明确记录变化并检查引用、后续依赖及Lean对应。

每题需要明确public/private来源、完整参考证明或满足全部前提的反例、具体审核标准及数学/人工审核状态。有效短证、替代构造和等价形式化均可接受；参考组织不是唯一解法。新发现和条件化贡献单独验证，不根据答卷新增必答义务。

## 当前目录合同

`cases/suite.json` 显式列出四类中的全部case.json，`cases/sources.json`登记来源。每题用 `path_base="case"`；task、reference、rubric、group_contract、solver_files源路径和evaluator_files均相对题目目录。新题须有版本、唯一ID、family_id、task_kind及完整逐阶段合同。

题面保留数学目标、全部必答范围、合法公理与交付格式。分值、通过规则、真假、关键错误、选题理由和实验机制留在评审侧。candidate_instruction不得泄露这些信息；附件只通过显式solver_files投影。编译成功但语义失配的给定Lean可以是题目设计的一部分，未经设计和版本变更不得将其修正。

`cases/taxonomy.json`维护九项考察重点、一个主重点和2–4个次重点，每个标签必须指向真实阶段/义务及实际题面位置。分类不改变数学要求，也不增加候选Lean义务。完整材料改变后先重审标签，再更新源绑定和生成目录：

```sh
python3 scripts/catalog.py
python3 scripts/catalog.py --check
```

## 证据与版本

AI起草、作者自查、独立AI数学审核、真实Lean编译、逐义务语义对应、候选考试和人工批准分别记录。不得标造human-approved或模型结果。部分覆盖明确列出缺口，不能由模块数量、声明存在或编译成功推断完整数学覆盖。

作者Lean位于各题formal/，固定manifest、alignment、COVERAGE、源码、工具链及依赖。用[统一验证器](scripts/formal/README.md)编译改变的题或依赖组；未变源码通过[证据检查](scripts/formal/check_evidence.py)复核并明确复用。候选Lean须从冻结答卷原样提取，作者工程不能代替候选交付。

任何数学、候选输入或评分变化均另立题目版本和审核记录。目录路径整理可保留数学字节，但必须核对候选消息及固定证据的身份；不把工程重绑称为新数学复核。

## 软件职责与验收

执行属于math_gauge/execution.py，题库合同属于catalog.py，审核和报告属于review.py。scripts/benchmark只组织共享runner，不另实现执行或评分。可靠性计划的多轮调度、历史绑定及KEEP/FULL组合尚未实现验收。

受影响runner合同须运行：

```sh
python3 -m unittest discover -s tests
python3 -m math_gauge validate
python3 scripts/catalog.py --check
python3 scripts/validate_protocol.py
```

只编译改变的Lean及依赖组；记录文件散列和实际工具链。显式环境测试跳过时如实列明。协议或固定计划身份变化后可用 `python3 scripts/validate_protocol.py --refresh` 更新工程绑定，不能授权运行或生成成绩。模型运行、提交、push、发布分别需要相应授权。

保留共享工作区中他人的修改，按Dev Mesh登记边界。`.dev-mesh/`、`runs/`、缓存、私有材料与凭据不进入提交。历史由[Git基线](docs/repository-map.md)恢复，当前工具不依赖本地旧目录。
