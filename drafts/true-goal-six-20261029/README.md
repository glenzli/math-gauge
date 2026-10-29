# 六道真目标与证明路径候选题

这组六题的主目标均成立。设计重点是多个相依步骤中的条件忠实性：熟悉环境中合法的中间推断，在题目的实际环境下可能失败，而最终结论仍须通过有效路径得到。

六题都有完整题面、参考证明、错误路径的具体反例、评分依据、公开来源、作者 Lean 和逐项正文对应表。当前是 **0.1.1 草案题集**（R103 评分措辞为 0.1.1，其余题为 0.1.0），人工审定 pending。三位新 AI 审稿者的题面盲审与对抗复核已完成，六题均可进入试跑；首次 Terra 6.1 Max 隔离试跑已完成，六题逐题 AI 双审为 6/6 pass，详见 [Terra 试跑](../../results/true-goal-six-terra/README.md)。本轮未显示对该配置的经验区分度。

## 六题

| 题目 | 成立的主目标与相依构造 | 容易越过的条件边界 |
| --- | --- | --- |
| [R101 三份同余记录的整体恢复](MG-R101/task.md) | 部分实现 → 选择无关的障碍类 → 记录商上的线性映射 → 短正合列 → 全部原始实现 | 子模格分配律；两两相容等同于整体可实现；商中的唯一性回填到原空间 |
| [R102 逐点有限轨道的规范分解](MG-R102/task.md) | 逐点周期尾部 → 局部幂零与周期分量 → 唯一性导出线性投影 → 周期自同构 → 交织自然性 | 逐点有限变成统一指数；有限长度 Fitting 定理；迭代像的交误当周期部分 |
| [R103 参数化耦合系统的最小解与结构传递](MG-R103/task.md) | 参数化最小解 → 约化映射的单调性 → 分块最小性 → 任意重组 → 沿伴随关系精确传递 | 单调变成可数连续；不动点误当最小不动点；普通半共轭误当最小解传递 |
| [R104 幂等分解在增厚逆系中的恢复](MG-R104/task.md) | 逐层提升唯一性 → 转移相容 → 极限提升 → 正交与完整家族 → 商环乘积分解 → 自然性 | 层核幂零变成极限核幂零；层增广满射变成极限满射；逐元素指数变成统一指数 |
| [R105 线性观测的完整载体与最优恢复](MG-R105/task.md) | 核商的观测范数 → 实际完备化 → 闭像等距实现 → 唯一最优完成态 → 原空间下确界、取到与核纤维 | 给原空间偷加 Hilbert 结构；给观测像偷加闭性；完成态存在误当原向量存在 |
| [R106 稠密观测与完成域上的整族恢复](MG-R106/task.md) | 完成域延拓 → 稠密 Cauchy 传递 → 任意真滤子的极限 → 紧集上一致收敛 → 同步移动输入 | 任意滤子变成序列；逐点变成全域一致；整族值集被默认为相对紧 |

R101 的真目标是障碍及实现的完整分类，**并不声称每条两两相容记录都可实现**。其余题也以各自题面精确列出的目标为准。

每题目录中的 `reference.md` 给出完整论证，`rubric.json` 给出具体判断标准，`formal/COVERAGE.md` 说明实际 Lean 对象与每项义务的对应。参考中的错误路径反例均经文字论证；它们没有全部单独形式化，也不是候选额外必答题。

## 审核与形式化

- 六份作者主模块均通过固定 **Lean 4.29.1 / Mathlib 5e932f97dd25535344f80f9dd8da3aab83df0fe6** 的独立源码编译及全声明公理审计。逐题证据在 `formal/current-formal.json`、`manifest.json`、`verification-report.json` 和日志中。
- 验证器为仓库现有的 `scripts/formal/verify_suite.py`。每题使用新的独立构建目录；不使用兄弟题的构建产物、源码旁旧 olean 或依赖项目自身的数学库。Mathlib 的固定依赖缓存可复用。
- 数学与正文—Lean 对应由非作者 AI 审阅者交叉复核，先读题面、再读完整材料。最终逐题状态与精确散列记在 `review.json`；完整报告在 [reviews](reviews)。审查继承一般项目背景，不能当作隔离模型答题。
- 主任务形式化与旁支范围逐项区分；没有把目标作为证书输入。内核只允许标准依赖 `propext`、`Quot.sound`、`Classical.choice`，不使用未证明占位符或自定义数学公理。
- 起草阶段共享 runner 回归测试执行 52 项，49 项通过、3 项环境相关集成测试跳过；试跑收尾执行 54 项，51 项通过、3 项跳过。六题的实际 Lean 编译及审计另行运行通过，不能用测试数量代替数学证据。

所有合法短证明、适用的标准定理和替代路线均可获得完整通过。R101、R102 存在直接的元素论证；R103 可由 Bekić 与伴随不动点定理压缩。其余题也可能被熟悉相应理论的模型简洁完成。依赖链的存在不等于最短证明必然很长，更不等于模型必然失败。

## 使用与边界

本目录是独立题集，复用同一个 runner，没有修改默认题集。候选只收到 `task.md`；准备后的 `prompt.md` 必须逐字节相同。参考、真假、rubric、来源、审核记录和作者 Lean 均不进入候选请求。此次“包含 Lean”指作者参考形式化，不额外要求候选提交 Lean。

```sh
python3 -m math_gauge validate --suite drafts/true-goal-six-20261029
python3 -m math_gauge list --suite drafts/true-goal-six-20261029
python3 -m math_gauge prepare --suite drafts/true-goal-six-20261029 \
  --case MG-R104 --out /absolute/path/to/new-question-directory
```

全部六题的共用 Lean 复核入口：

```sh
python3 scripts/formal/verify_suite.py \
  --suite drafts/true-goal-six-20261029/formal-suite.json \
  --dependency-root /absolute/path/to/pinned-dependency-project \
  --out /absolute/path/to/new-verification-directory --jobs 2
```

依赖项目的版本、缓存要求及验证边界见仓库 [形式化验证说明](../../scripts/formal/README.md)。公开来源和独立改编范围记在 [sources.json](sources.json)；未使用未公开 OET 内容。公开题面不意味着相关数学未出现在训练材料中。

本轮新增 [试跑资格审核](reviews/qualification-20261029/gate.json)：无数学阻塞；修正 R103 把序连续性写作必要条件的评分措辞，旧版本与独立关闭记录保留。题面、参考和 Lean 源码未改变；内核证据经身份核对复用。合法短证、通常分块回代解释和一致的零环约定均接受。

隔离校准在以上记录冻结后开展，详见 [运行与评分](../../results/true-goal-six-terra/README.md)。六题随后已纳入[现行 41 题目录](../../exercises/README.md)及[首轮全题集双模型比较](../../results/full-comparison-20261030/comparison.md)，两轮结果分别保存。早期验证快照、作者文件中的“未试跑”“未提交”等文字均保留其形成时的历史状态；当前人工审定仍为 pending。
