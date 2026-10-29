# 本批题包与现有 runner 的边界

本批是可由现有 suite/prepare/run/review/report 入口投放的草稿。没有复制或分叉 runner，也未替换默认公开题集。task_kind 细分记录在题包中，传输仍使用 alignment。

## 当前可用

- catalog.py 冻结题目合同，并只输出 task 和 solver_files。平铺多文件 Lean 足以承载本批模块。
- execution.py 保留完整标准输出和 response_sha256。生成及修复任务通过回答中的完整 Lean 源码块交付，人工/独立审核可以直接核对冻结答卷。
- review.py 保留对齐、条件、论证、范围和审核身份。rubric.expected 在生成/修复题表示交付目标，不能当作已有模型结果。
- scripts/formal/verify.py 是作者固定工件的编译及全声明公理检查入口。参考证明和故意失配输入都可以在内核上成立。

## 本轮不声称已实现

- 自动收集候选工作目录内任意文件，并将多文件产物与答卷冻结为不可变整体。
- 自动从任意 Markdown 答卷可靠提取 Lean 文件或修复格式。
- 仅凭编译、签名相似度、自动等价证明或生成者自评裁定语义对齐。
- 将判定、生成和修复压成统一能力总分。

后续若新增候选文件产物合同，应由 catalog.py 定义可交付路径与输入不可变边界，execution.py 收集/冻结产物并记录逐文件身份，review.py 绑定同一产物指纹及独立判决。依然使用公共 runner；私有题库只携带数据与配置。
