# 已退役的第 2/3 章试点题包

旧 `drafts/long-form-design-20261030/pilot-ch02/`、`pilot-ch03/` 已由当前整章考试接替。它们不再作为当前取卷、运行器或材料校验的文件输入；[现行两章目录](../../drafts/chapter-exams-20261030/README.md)保存完整候选材料、参考、合同、来源及冻结背景记录。

旧试点共 **60 个文件、312049 字节**，保存在 Math Gauge 的精确 Git 提交 **`9e536ad5ebce182ffcb6bcaabdc24c7fbec221c3`**。[逐文件清单](manifest.json)记录原路径、SHA-256、字节数和 Git blob 身份；退役前已逐项确认工作区字节与该提交相同。

| 旧路径 | 当时用途 | 当前入口 |
| --- | --- | --- |
| `drafts/long-form-design-20261030/pilot-ch02/` | 第 2 章早期候选材料、26 证明义务及背景检查 | [MG-C002](../../drafts/chapter-exams-20261030/MG-C002/candidate/task.md)，34 项完整义务 |
| `drafts/long-form-design-20261030/pilot-ch03/` | 第 3 章早期候选材料、30 源单元及背景检查 | [MG-C003](../../drafts/chapter-exams-20261030/MG-C003/candidate/task.md)，92 项完整义务 |

当前来源记录的 `parent_draft`、早期审查中的旧相对路径或临时绝对路径保留其产生时的含义，按上述提交及原路径追溯。它们是历史来源字符串，不要求退役目录仍在当前工作区；不能为修链接改写冻结 provenance、数学审查或编译收据。

## 从归档恢复

在含上述提交的仓库中，可读取一个原文件：

```sh
git show 9e536ad5ebce182ffcb6bcaabdc24c7fbec221c3:drafts/long-form-design-20261030/pilot-ch02/candidate/task.md
```

恢复两份完整题包时，先选择一个尚不存在的输出目录，将下例的绝对路径替换为该位置：

```sh
mkdir /absolute/path/to/new-pilot-recovery
git archive --format=tar 9e536ad5ebce182ffcb6bcaabdc24c7fbec221c3 \
  drafts/long-form-design-20261030/pilot-ch02 \
  drafts/long-form-design-20261030/pilot-ch03 \
  | tar -xf - -C /absolute/path/to/new-pilot-recovery
```

导出后按 manifest 的原路径逐项核对 SHA-256；不要将旧题包覆盖到当前题集。归档包括旧 task、依赖说明、参考、义务清单、来源、许可证、背景检查日志和回执，恢复不启动模型或 Lean。

此次退役只移除已被接替的试点副本。上层[研究设计及独立复核](../../drafts/long-form-design-20261030/README.md)、当前 43 份试卷、原 41 题及所有真实模型答卷、失败、冻结成绩和复算证据均保留。
