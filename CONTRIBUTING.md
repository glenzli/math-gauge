# 贡献与新增题目

先读 [项目说明](README.md)、[评测协议](protocol/evaluation.md) 和拟修改题目的完整材料。保留数学对象、假设、量词、定义域与结论强度；有效的替代证明和完整反例同样可以完成任务。

本指南面向出题、审核和运行器维护。候选模型只能收到每题明确允许的投影，不能收到本指南、目录标签、参考解、评分标准或历史答卷。

当前43份主试卷与已测原41道单题分开登记。完整阅读路径见[文档导航](docs/README.md)，各目录职责见[仓库地图](docs/repository-map.md)。递进题组和整章题的义务、含证明原文、逐项判卷及新增材料状态另遵循[题组合同](protocol/question-groups.md)；三次作答及自查仍是[待实现验收的执行规格](protocol/reliability-execution.md)。

## 题目放在哪里

原41道单题统一索引四个 suite，实际文件仍各有唯一来源：

| Suite 根目录 | 当前范围 | 用途 |
| --- | --- | --- |
| [cases/public](cases/public/README.md) | MG-R001–MG-R020 | 默认二十道研究式数学题 |
| [drafts/true-goal-six-20261029](drafts/true-goal-six-20261029/README.md) | MG-R101–MG-R106 | 六道成立的构造与恢复任务 |
| [drafts/public-proof-extractions-20261029](drafts/public-proof-extractions-20261029/README.md) | MG-P001–MG-P003 | 从公开证明机制独立编排的数学任务 |
| [drafts/lean-alignment-20261029](drafts/lean-alignment-20261029/README.md) | MG-F101–MG-F112 | Lean 对齐判定、生成与修复 |

目录中的 `drafts/` 不表示没有参考或验证；生命周期以题目及审核记录为准。当前所有题目仍为 `draft / human pending`。私有题集另放在受控目录，使用相同的 `Suite` 和 runner，通过 `--suite` 选择；不复制一套私有运行器。

新43份试卷放在`drafts/progressive-groups-20261030`和`drafts/chapter-exams-20261030`，使用同一runner；逐题版本以case和修订记录为准，不与原41题重复计数。原`exercises/catalog.json`的固定范围不随它们自动扩展。

## 每道新题的材料

| 材料 | 必须说明的内容 |
| --- | --- |
| `case.json` | 唯一题号、版本、类型、公开范围、文件路径、候选附件、来源 ID 和真实审核状态 |
| `task.md` | 完整实际条件及主要目标；明确必要约定，避免把证明路线、缺失条件清单或答案提示写进题面 |
| `reference.md` | 覆盖原题全部必需义务的参考论证或满足全部前提的完整反例；区分引用定理、证明本身和可选强化 |
| `rubric.json` | 具体必需证据、致命错误及可接受替代路线；不能把作者独有路线或非必答旁支加成评分义务 |
| 来源记录 | 在 suite 的 `sources.json` 注册并由题目引用；记录公开出处、确切版本或提交、独立改编范围及可核实的使用边界 |
| 审核记录 | 作者自检、非作者数学审核、原文与 Lean 语义对应、实际编译及人工审定分别记录，并绑定被审文件散列 |

需要附带 Lean 时，另提供固定工具链、依赖版本、显式模块清单、`COVERAGE.md` 和编译／公理证据。题面要求候选生成或修复 Lean 时，还须明确输出文件及允许修改的范围，遵循 [候选 Lean 验收合同](protocol/candidate-lean.md)。

来源取自公开论文、公开题库或公开纠错记录时，说明借用了哪一段数学机制，哪些部分是独立构造。只有可核实的纠错证据才能支持“原论断有误”的描述。私有草稿、未公开历史和内部答卷不得因改编成题而自动转为公开材料；公开来源与署名范围见 [SOURCES.md](SOURCES.md)。

## 输入与评分的边界

`solver_files` 是候选附件白名单，`evaluator_files` 是评审专用材料。参考与 rubric 不得作为本题或其他题的候选附件。附件目标可使用安全相对目录；禁止绝对路径、父目录穿越、大小写重复和文件/目录遮蔽。由共享 runner 生成输入，避免手工拼接参考或标签。

`candidate_instruction` 缺省会使用兼容旧题的通用提示；设为空字符串才表示不追加该提示。当前二十道默认研究题只有题面，准备后的 `prompt.md` 与 `task.md` 相同。Lean 题可能另有明确附件；通用适配器应使用共享的 `candidate_message(request)`，完整传递这些附件，不自行概括。

三类证据不能互相替代：数学 AI 审核说明其审查结论；Lean 编译及公理审计说明实际编码命题；人工批准须有实际审阅人的记录。故意失配的 Lean 输入可以编译通过，修改它属于题目设计变更。部分形式化应列出缺口，不缩小数学题面来制造“全覆盖”。人工审定使用 [记录模板](protocol/case-review-template.md)，AI 不代填人类署名或批准状态。

## 修订与目录登记

改变题意、候选附件、参考义务或评分标准时，先保留旧文件、版本、来源与审核身份，再更新题目及所属 suite 的版本。旧模型答卷、编译报告和评分继续绑定旧字节。新版本重新核对相应数学与形式化证据；补测单独保存，不能回填旧轮成绩。可参照 [R005 修订记录](cases/public/MG-R005/revision.json) 和 [版本索引](exercises/history.md)。

将题目加入所属 `suite.json` 的显式清单后，在 [exercises/structure.json](exercises/structure.json) 登记当前 suite、唯一主章节以及同源／变体关系。题号可以保留原路径；不要复制题面到章节目录。相关母题在数据划分和统计解释时应保持关联，不能当作完全独立样本。

[索引生成器](exercises/refresh_catalog.py) 当前针对固定范围的 41 题编写，含题数断言、各题族审核记录映射和特定覆盖边界。扩充范围时须同步维护这些合同与生成文字，经过相应验证；它不是任意新题的自动注册器，也不会代做数学审查。

只核对当前目录时，使用只读入口：

```sh
python3 exercises/refresh_catalog.py --check
```

实际修订目录时，为新一轮资格记录选择仓库内尚不存在或为空的目录，例如：

```sh
python3 exercises/refresh_catalog.py --final \
  --qualification-dir results/new-catalog-review/qualification
python3 exercises/refresh_catalog.py --check
```

运行前将示例路径换成本次独立目录。`--final` 只固定目录快照，不批准题目，也不启动模型。省略 `--qualification-dir` 会沿用当前目录中的资格记录位置；已有冻结证据时，不用默认重建覆盖它。历史比较保存其原始目录快照，新目录不改变既有比较的样本或分母。

## 验证改动

在仓库根目录使用 Python 3.10+。先验证受影响 suite；四个现行入口为：

```sh
python3 -m math_gauge validate
python3 -m math_gauge validate --suite drafts/true-goal-six-20261029
python3 -m math_gauge validate --suite drafts/public-proof-extractions-20261029
python3 -m math_gauge validate --suite drafts/lean-alignment-20261029
```

核对候选投影时，为每次准备选择新的输出目录；它必须位于题集根目录之外。例如：

```sh
python3 -m math_gauge prepare \
  --suite drafts/lean-alignment-20261029 --case MG-F102 \
  --out runs/inspect-f102
```

检查实际题面、附件与请求，确认没有评审材料。该命令只准备文件，不调用模型。输入目录分离不等于进程访问隔离，真实闭卷运行另按 [隔离 CLI 流程](protocol/isolated-cli-runs.md) 和 [完整比较运行方案](protocol/full-comparison-run.md)执行。

影响 runner 合同时，运行项目规定的检查：

```sh
python3 -m unittest discover -s tests
python3 -m math_gauge validate
```

报告实际执行和跳过的测试；默认测试环境可能跳过需要固定 Lean 依赖的实机检查。Lean 源码改变时，只重新编译受影响题目或依赖组，并将结果绑定到精确源码与环境。作者形式化使用 [参考 Lean 复核](scripts/formal/README.md)；候选原始源码使用独立验收合同。纯文档变更核对链接与相关身份，已经通过且输入未变的编译证据可以复用。

## 保存与提交

运行前冻结题面、评分与环境，保留实际请求、原始答卷、失败及超时、工具条件、独立审核和散列绑定。运行器的成功退出不代表数学通过；若需要重新运行或改用工具条件，应作为明确的新样本保存。程序生成的 fixture/replay 不是实际模型答题结果。

`runs/`、`.dev-mesh/`、凭据、客户端会话状态、依赖缓存及安装副本保留本地。经核对的公开成果进入 `results/`，按明确清单保留复核所需的答卷、收据、日志与源码身份。不要删除证明链中的文件来缩小提交，也不要把私有原题或可还原原题的完整回答混入公开结果。发布前检查引用能在新检出中解析，并说明离线复算与重新调用模型的区别。

提交与推送需要本次工作的明确授权；多人共享工作区时，只处理已协调的路径。代码职责保持为 `catalog.py` 管题目与投影、`execution.py` 管执行证据、`review.py` 管审核与报告、`cli.py` 管命令入口。
