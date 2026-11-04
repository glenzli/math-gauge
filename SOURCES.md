# 来源与作者说明

当前46份数学卷与4份相关AR、共50条任务的来源登记在 [cases/sources.json](cases/sources.json)，每题另有provenance.json及相关来源闭包。公开题只使用明确公开的材料与独立构造；私有材料使用相同runner并留在对应私有范围。公开来源不保证模型训练未见。

## 数学材料

题材从公开《算子演化论》（OET）出发，涵盖分析、代数、拓扑、范畴与几何。OET作者为Zhe Li（Glen Li / glenzli），[ORCID](https://orcid.org/0009-0006-6536-3453)，[公开作品](https://glenzli.com/books/oet/)，CC BY 4.0。确切修订、章节、取材范围和候选章节原文以当前来源登记及逐题provenance为准。

公开证明机制题的来源可能是成立定理、证明缺口、错误陈述或修订/撤回；这些事实分别记录，不能把某处证明错误自动改写为整篇主定理为假。参考论证和反例需要在实际题设下独立核对，不能仅凭来源标题确定适用性。

## 作者Lean与AI协作

当前作者工程使用逐义务映射、真实编译、公理审计及非作者AI语义复核，见[证据账本](verification/author/README.md)。源码闭包、固定外部库、许可证和必要适配由各题SOURCE-CLOSURE.json、provenance.json或vendor/记录。固定依赖的声明名称不能代替原文对应证明。

完整作者Lean覆盖仍仅原43/43份、372/372项义务及470个已编译模块。新增GR021–023为3份同族书面加强稿，15项证明判准没有作者Lean证据、人审pending；其参考证明、有限验算与AI复核不能替代形式化或人工批准。MG-GP003现使用固定Motivic/Aglib实际转移接口，完成S1–S6；上游源码身份、实际导入闭包与公理审计随正式编译报告保存。依赖修订、复现方式、改编源归属及Apache-2.0完整许可证见[环境说明](verification/environments/motivic-4.34.1/README.md)与[第三方署名](verification/environments/motivic-4.34.1/THIRD_PARTY_NOTICES.md)。这些材料只供作者核验，不进入候选附件。先前[外部库复查](verification/author/gp003-frontier/README.md)保留其检查时点的来源边界，当前覆盖以新证明和审核收据为准。

作者与审核者的AI协作不计候选考试。已有历史候选答卷与新三稿原生初答，现行聚合复用相容旧答并加入既有矩阵答和两题新实考；选题重算在观察结果之后，不是全套同步新考试。原答与旧审核保留，所有human状态仍为pending。原材料中起草时点的未完成描述由当前证据接续，不改写冻结参考制造事前已经完成的记录。Astra Max的数学起草/独立审核与Sol 6.1 Max的工程整理按实际逐项记录区分，工程迁移不冒称新数学审核。

## 许可与历史

本仓库代码采用[MIT](LICENSE)。复用的OET、Lean背景、第三方库与外部原文保留各自许可和署名，不因仓库MIT而统一改许可。来源链接只是核对依据，不表示许可复制整篇内容。

历史来源、设计审核和实验由Git基线 `6a48027baa33e06e913a554fb8bac9394a82b480` 保留，恢复见[仓库地图](docs/repository-map.md)。这些历史记录只按其真实身份使用；显式相容复用不新增执行，选题和合并规则见[本地0.5.0说明](docs/selection-v0.5.0.md)。已发布0.4.0资产和原操作指南保持不可变。

## 本地0.6历史材料

AHR01–04及HCH02保留精确历史commit、源blob、正文、许可和作者署名；中间版本公开状态未核实。public-development是本地选题计划，不是来源公开证明或hidden holdout。新增范围及审计不继承原43卷作者Lean账本。逐文件身份在case的evaluator-only provenance、source handoff与integration review中。
