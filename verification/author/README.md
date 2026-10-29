# 作者 Lean 与独立语义审核

现行43份试卷共372项义务。**42份试卷、369项义务**完成作者形式化及逐项独立AI语义复核。43份作者工程的447个显式模块已通过实际编译和完整本地声明公理审计；11029个声明按题重复计数。人工批准仍为pending，候选模型运行数为0。

**GP003的S1/S2/S5仍为partial。** S1/S2已闭合真实仿射情形，尚缺原题一般概形的表示连接；S5尚缺实际转移几何及相关比较。详见[精确缺口](../../cases/proofs/MG-GP003/formal/GAPS.md)与[非作者外部库评估](gp003-frontier/README.md)。未完成项保留在完整分母中。

## 每题的验收路径

从[分类目录](../../cases/README.md)进入题目，读取完整题面、候选附件、reference、rubric和contract，再核对`formal/alignment.json`和`formal/COVERAGE.md`。逐项检查实际定义、条件、量词、对象之间的表示对应、结论强度、依赖及反例的全部前提。声明名称、作者自述或编译成功不能替代这种核对。

[逐题验收目录](cases.md)提供直接阅读入口，[当前账本](ledger.json)绑定原始编译证据和独立语义审核。作者工程位于各题`formal/`，包含显式模块、真实编译报告、日志及所有本地声明的公理闭包；允许的公理仅为`propext`、`Classical.choice`和`Quot.sound`。独立审核保存在`semantic-reviews/`，由不同于该题作者的审核者完成。AI审核和内核检查不等于人工批准。

## 为什么保留checked输入

本次只调整目录、评审附件引用和由覆盖表导出的形式化状态，题面、参考、评分、合同、候选附件和Lean源码都保持原字节。原编译报告及独立审核没有被改写或回填新的执行时间。

各题的`formal/checked-case.json`、`checked-manifest.json`以及本目录的[checked-ledger.json](checked-ledger.json)保存实际编译时的身份；`input-binding.json`把这些身份与当前目录逐项连接。它们是当前证明的必要输入收据，不是另一套历史题库。验证器仅允许明确定义的元数据变换，任何数学文件、Lean源码、人工状态或义务变化都不能通过此路径继承旧证据。

```sh
python3 scripts/formal/check_evidence.py
```

该检查不调用Lean或模型，不依赖旧目录或Git对象；它核对当前清单、原始清单、全部源码和日志散列、真实审计输出、独立审核散列，以及372项义务的完成边界。数学正确性仍须阅读真实题面和证明。需要重新编译时使用[共享作者验证器](../../scripts/formal/README.md)及对应固定依赖；GP001单独采用Lean4.36.0-rc1/TauCeti profile，其余采用Lean4.29.1。

[返回验证目录](../README.md) · [题目分类](../../cases/README.md)
