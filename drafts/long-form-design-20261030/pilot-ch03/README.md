# OET 卷1第3章整章 Lean 化：第二份草案

- `candidate/`：第3章全文，第1/2章文字背景，6个外部Lean模块，以及task、依赖说明、署名、LICENSE。保留自然语言证明，属于autoformalization轨。
- `review/coverage-registry.json`：30个源单元；尚未拆完所有子结论/原子证明义务，不能称为冻结后的最终评分表。
- `review/reference.md`：参考路线、作者实现边界与正式化门槛。
- `review/source-provenance.json`、`import-leak-audit.json`、`candidate-projection.json`：逐章来源hash、导入闭包和候选投影。
- `review/background-compilation.json`：前置包最小增量编译证据；背景通过不等于目标章或候选解答通过。
- `review/build/`：临时编译目录，含缓存链接，不属于可分发/候选输入。

状态：draft / human pending；没有模型答题，没有注册正式case，不进入既有41题，不改变既有分数。难度是设计预期，尚未通过模型实验验证。discovery轨需另建删证明投影后单独冻结。
