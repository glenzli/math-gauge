# 公开证明机制抽取：首批三题

从有公开来源的研究论证、勘误和形式化差异中抽取机制，独立编写可作答的数学任务。它们是本地草稿，复用 Math Gauge 的 runner；尚未并入默认公开集合。

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

三题均完成非作者 AI 数学审核和另一个全新上下文的题面盲审，结论均为通过。数学审核核对完整材料和来源；盲审只接收题面及项目通用约定，不接收参考与评分。记录绑定确切文件散列。

- 非作者数学审核：[MG-P001](reviews/MG-P001-independent.json)、[MG-P002](reviews/MG-P002-independent.json)、[MG-P003](reviews/MG-P003-independent.json)。第三题的审核范围是相对于明示几何输入的完整应用证明。
- [三题题面盲审](reviews/task-only.json)：确认定义与范围，认可合法短解；不作经验难度结论。
- [共享程序基线](validation/runner-baseline.json)：52 项测试完成，3 项跳过；默认十题校验通过，相关代码和默认题集指纹保持不变。
- [本批整合校验](validation/integration.json)：三题 suite 校验通过；实际逐题导出后，`prompt.md` 与各自 `task.md` 字节一致，目录仅有题面和请求记录，未导出评审材料。
- [当前状态](reviews/status.json) 与 [文件快照](validation/snapshot.json)：作者目录中的 pending 字段保留作者交付阶段的状态；后续独立审核以此处记录和匹配散列为准。

所有题仍为 `draft`、`human: pending`。本批没有候选模型试跑，也没有新增 Lean 形式化或编译证据。历史影响、参考证明长度、原论文中的 Lean 证据都不构成本批的实测难度或形式化证明。第三题正确引用已知主定理并核对假设就是合法完成；第一、二题的紧凑标准论证同样应被接受。

在仓库根目录使用同一 runner：

```sh
python3 -m math_gauge validate --suite drafts/public-proof-extractions-20261029
python3 -m math_gauge prepare --suite drafts/public-proof-extractions-20261029 \
  --case MG-P001 --out /absolute/path/to/new-solver-directory
```

草稿目录分离只控制文件投影，不代替候选运行时的访问隔离。
