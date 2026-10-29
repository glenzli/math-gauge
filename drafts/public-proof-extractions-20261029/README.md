# 公开证明机制抽取：首批三题

从有公开来源的研究论证、勘误和形式化差异中抽取机制，独立编写可作答的数学任务。三题已纳入[现行 41 题目录](../../exercises/README.md)，继续使用独立 suite 和共享 runner，不自动并入默认公开二十题。原始作者与核验阶段记录保留，当前人审仍待定。

## 候选材料

| 题目 | 抽取方向 | 题面与评审材料 |
| --- | --- | --- |
| MG-P001 | 有限复形的局部拼接与整体同伦分类 | [题面](MG-P001/task.md) · [参考](MG-P001/reference.md) · [来源](MG-P001/source-notes.md) · [评分](MG-P001/rubric.json) |
| MG-P002 | 环面方向微分算子的小除数与正则性损失 | [题面](MG-P002/task.md) · [参考](MG-P002/reference.md) · [来源](MG-P002/source-notes.md) · [评分](MG-P002/rubric.json) |
| MG-P003 | 半局部值的层化比较：弱引理如何保住应用 | [题面](MG-P003/task.md) · [参考](MG-P003/reference.md) · [来源](MG-P003/source-notes.md) · [评分](MG-P003/rubric.json) |

来源、历史结果、参考与评审仅供出题侧使用。题面不预告错误位置或真假；实际候选输入以每题 `case.json` 的显式投影为准。

## 来源与抽取边界

- Biss 的公开勘误和 Mnëv 的说明指出开集与闭集的错误同伦拼接。本题独立研究有限复形中的同伦分类；不能把新题答案冒充对原 Grassmannian 主定理的证明或反证。
- Navier–Stokes 审查指出特定估计的原文与 Lean 输入导数阶数不同。本题研究真实环面算子的正则性，既不假定原文估计为假，也不复核整个 Navier–Stokes 证明。
- Voevodsky 原命题 4.23 的错误强引理由允许缩小开集的 MVW 引理 22.10 替代。本题保留实际几何对象，证明半局部值的层化比较同构。参考完整展开应用，但依赖三个精确引用的几何定理；未重建标准三元组的全部几何，也未构造原错误命题的具体几何反例。

[来源清单](sources.json) 保存公开资料与版本，[审核范围](reviews/PROTOCOL.md) 区分数学审校、候选输入、形式化、人工审核与实测难度。

## 验证与使用

三题均完成第一轮非作者 AI 数学审核和另一个全新上下文的题面盲审。第二轮进一步复核数学论证、实现实际对象上的 Lean 证明，并核对二者的语义。记录绑定确切文件散列；编译通过、独立 AI 审核、人工批准和候选试跑分别记录。

| 题目 | 第二轮数学／Lean 状态 | 使用边界 |
| --- | --- | --- |
| MG-P001 | 一般悬挂分类、全部实现、整数同调与有限局部矩阵判据均通过 Lean 核验与独立语义复核 | 可作完整 Lean 参考；含约化零阶同调、整数挠信息与高阶截断，见 [覆盖表](MG-P001/formal/COVERAGE.md) 和 [独立复核](reviews/MG-P001-round2-semantic.md) |
| MG-P002 | 全部题面结论已通过 Lean 核验与独立语义复核 | 可作完整 Lean 参考；参考稿中的可选旁支不计入全题覆盖，见 [第二轮审核](MG-P002/round2-review.json) 和 [独立复核](reviews/MG-P002-round2-semantic.md) |
| MG-P003 | 相对于三个精确引用的几何定理，完整应用论证通过复核；七个实际对象辅助模块已核验 | 可作明确引用已知定理的数学评测；完整半局部几何比较尚未形式化，见 [第二轮审核](MG-P003/round2-review.json) 与 [缺口清单](MG-P003/formal/GAPS.md) |

- 非作者数学审核：[MG-P001](reviews/MG-P001-independent.json)、[MG-P002](reviews/MG-P002-independent.json)、[MG-P003](reviews/MG-P003-independent.json)。第三题的审核范围是相对于明示几何输入的完整应用证明。
- [三题题面盲审](reviews/task-only.json)：确认定义与范围，认可合法短解；不作经验难度结论。
- [第二轮共享验证器检查](validation/round2-formal-profiles/archive.json)：完整 72 项测试及随后新增的 2 项合同测试通过；先前输入散列未变，两种固定 Lean 环境的 9 项实际编译测试全部运行。校验时默认公开题集为 20 题。本批三题继续使用独立草稿 suite。
- [本批整合校验](validation/integration.json)：三题 suite 校验通过；实际逐题导出后，`prompt.md` 与各自 `task.md` 字节一致，目录仅有题面和请求记录，未导出评审材料。
- [当前状态](reviews/status.json) 与 [文件快照](validation/snapshot.json)：题面、参考稿、评分和设计保留经过审核的原字节；作者阶段记录由第二轮证据接续。第一轮整合记录保存在 [历史目录](reviews/round1/README.md)。

所有题仍为 `draft`、`human: pending`。作者核验阶段没有候选试跑，随后三题已参加[首轮全题集双模型比较](../../results/full-comparison-20261030/comparison.md)；实际答卷和评分以该轮冻结证据为准。历史影响、参考证明长度、原论文的模型或 Lean 记录不构成本批的实测难度。第三题正确引用已知主定理并核对假设就是合法完成；第一、二题的紧凑标准论证同样应被接受。

公开 Lean 证明可以复用，但须落实到精确对象和目标。第二题保留 OpenAI 原始三模块、Apache-2.0 许可证及移植差异；第一题保留悬挂实现的来源与 NOTICE，并核验固定版本的 Tau Ceti 拓扑／同调基础。来源清单及逐题覆盖表说明实际借用了什么。外部库的独立编译和公理审计只有在本题连接定理也通过后，才构成本题的完整证明。

[第二轮形式证据复查](validation/round2-formal-evidence-recheck.json) 同时核对当前源码、冻结题面、编译器、依赖、日志和编译产物。第一题证明有限整数矩阵判据的正确性；可执行的 Smith 正规形求解程序未实现，也不是本题要求的交付。

在仓库根目录使用同一 runner：

```sh
python3 -m math_gauge validate --suite drafts/public-proof-extractions-20261029
python3 -m math_gauge prepare --suite drafts/public-proof-extractions-20261029 \
  --case MG-P001 --out /absolute/path/to/new-solver-directory
```

草稿目录分离只控制文件投影，不代替候选运行时的访问隔离。
