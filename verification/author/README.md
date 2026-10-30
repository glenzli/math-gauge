# 作者 Lean 与独立语义审核

现行43份试卷共372项义务。**42份试卷、371项义务**完成作者形式化及逐项独立AI语义复核。43份作者工程的452个显式模块已通过实际编译和完整本地声明公理审计；11147个声明按题重复计数。人工批准仍为pending，候选模型运行数为0。

**GP003的S5仍为partial。** S1/S2已补齐原环境概形的表示比较，S1非开局部化反例也已证明；S5已完成条件式有限点归纳及原单位装配，仍缺实际转移几何及大/小位点比较。详见[精确缺口](../../cases/proofs/MG-GP003/formal/GAPS.md)与[非作者外部库评估](gp003-frontier/README.md)。未完成项保留在完整分母中。

## 每题的验收路径

从[分类目录](../../cases/README.md)进入题目，读取完整题面、候选附件、reference、rubric和contract，再核对`formal/alignment.json`和`formal/COVERAGE.md`。逐项检查实际定义、条件、量词、对象之间的表示对应、结论强度、依赖及反例的全部前提。声明名称、作者自述或编译成功不能替代这种核对。

[逐题验收目录](cases.md)提供直接阅读入口，[当前账本](ledger.json)绑定原始编译证据和独立语义审核。作者工程位于各题`formal/`，包含显式模块、真实编译报告、日志及所有本地声明的公理闭包；允许的公理仅为`propext`、`Classical.choice`和`Quot.sound`。独立审核保存在`semantic-reviews/`。不同作者的模块交叉复核，并在逐项记录中注明作者、审核者和未变源码的复用范围；作者自己的审阅不充当其模块的独立复核。AI审核和内核检查不等于人工批准。

## 为什么保留checked输入

42份未变题目继续使用目录迁移时的严格绑定：其数学输入、Lean源码、原编译报告和独立审核均保持原字节。GP003已重新编译26个模块并重新逐项复核；其题面、评分和合同不变，参考开头仅更新证据状态及当前来源入口。

各题的`formal/checked-case.json`、`checked-manifest.json`与[checked-ledger.json](checked-ledger.json)保留先前身份。`input-binding.json`显式区分`metadata-only-layout-migration`与`recompiled-author-evidence`。后者绑定真正的新编译、完整声明及日志、当前源码和独立语义审核；不能用重算旧报告散列吸收源码变化。先前内容保存在Git中，不新增历史题库。

```sh
python3 scripts/formal/check_evidence.py
```

该检查不调用Lean或模型，不依赖旧目录或Git对象；它核对当前清单、原始清单、全部源码和日志散列、真实审计输出、独立审核散列，以及372项义务的完成边界。数学正确性仍须阅读真实题面和证明。需要重新编译时使用[共享作者验证器](../../scripts/formal/README.md)及对应固定依赖；GP001单独采用Lean4.36.0-rc1/TauCeti profile，其余采用Lean4.29.1。

[返回验证目录](../README.md) · [题目分类](../../cases/README.md)
