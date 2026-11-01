# 任务包分发合同

当前本地任务包为 **0.2.0，与 `cases/suite.json` 的题集版本一致**。新任务发布沿用题集版本；内部提交格式或工具实现可以有各自版本。0.2.0目前只在本地准备，未创建远端 Release、标签或下载地址。已发布的[v0.1.0](https://github.com/glenzli/math-gauge/releases/tag/v0.1.0)保持原样，其软件/题集分开编号和旧目录只作为历史约定，见[历史发布说明](../docs/release-notes-v0.1.0.md)与[历史包内指南](../docs/release-consumer-README.md)。

交付端只需阅读包根目录的一份 README，其当前源文件为[0.2.0运行与返回说明](../docs/release-consumer-README-v0.2.0.md)。完整操作集中在那里，不再另发 CONTROLLER 指南或要求操作者填提交模板。外部运行端不需要仓库、完整评审计划、Math Gauge 安装或 Codex。

## 交付边界

命名资产 `math-gauge-v0.2.0.zip` 解压为一个同名根目录：

```text
math-gauge-v0.2.0/
  README.md
  cases/<case-id>/task.md
  cases/<case-id>/files/<declared-attachment-path>
  tools/benchmark.py
  manifest.json
  LICENSE
  THIRD_PARTY_NOTICES.md
```

任务正文只保留一份，附件保持显式候选白名单和原始字节；含证明的章节原文、跨章定义及故意语义失配的 Lean 审计源码不得删改。清单及工具属于控制端，不能作为提示交给模型。参考、rubric、真假、选择理由、审批、作者证明、完整profile和评审计划均不入ZIP；GitHub自动Source code压缩包含这些公开材料，不是候选交付物。

全部43题均为公开开发题，当前仍为draft / human pending，没有真实候选结果。独立题包不使已公开题目成为隐藏留出集。

下载数据集不预选模型、预算或任务范围。操作者用工具在新目录冻结选择，按固定顺序取得完整消息、保存所有原始尝试，再打包一个 `answers.zip`。请求历史只来自允许的父节点；未知平台字段保持未知。记录与打包工具自动生成身份及文件字段，不要求操作者手写散列或完整提交JSON。普通返回包由同一 `benchmark-import --input answers.zip --plan ... --out ...` 统一核验并接入共享运行记录，来源、数学、候选Lean和人工审核仍分别完成。

## 本地构建与核验

在仓库根目录执行，输出路径必须是新的：

```sh
python3 scripts/release.py build --version 0.2.0 --local-preview \
  --out runs/releases/v0.2.0
```

落盘输出为命名ZIP、`SHA256SUMS` 和包外的 `evaluator-plan.json`。构建身份保存在ZIP内清单的 `release_provenance` 及命令标准输出的回执中，不另生成第四个文件。该评审文件同时保存完整基础计划和期望的精确数据集身份；ZIP导入必须与它匹配，不能只接受提交方自洽重算的清单。完整计划由评审端保留，不发给候选或要求外部运行端取得。`releases/v0.2.0/config.json` 指定套件版本、命名、指南和许可来源；任务版本与Release版本不一致时拒绝构建。历史v0.1.0仍可按自身配置显式构建和检查，不改写已发布资产。

本地预览记录父提交和实际输入身份，不把未提交源码冒称为发布提交。发布构建仍需其对应源码身份及干净状态合同。构建、只读检查和评审计划恢复都不调用模型；本地打包不等于提交、推送或远端发布。

ZIP内的题目字节及清单保持不可变；每次模型或预算选择产生新运行。完整性散列绑定材料，不认证平台、第三方执行时间或隔离真实性。普通外部导入继续标记 `external_import`；fixture/replay不能变成模型结果，声明也不自动开放正式比较资格。

[外部交换实现合同](external-harness.md) · [仓库评审操作](../docs/usage.md) · [运行证据标准](execution-evidence.md)
