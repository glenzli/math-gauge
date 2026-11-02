# 备选试卷

这里保存11份书面备选卷、66个必答阶段。默认32卷的四类目录保留在上一级；本目录的题目仅在显式选择 `cases/reserve-suite.json` 时运行，不进入默认题包或80槽计划。

`reserve` 表示选卷安排，`proofs` 表示书面证明、反例、构造与分类的交付类型。下面按数学主题辅助浏览；同题仍只有一份原始材料，主题不改变假设、判准、分值或样本单位。备选不表示题目简单，取舍依据见[0.3.0选卷说明](../../docs/selection-v0.3.0.md#11道备选题)。

## 递归、迭代与恢复

| 试卷 | 考察内容 | 完整材料 |
| --- | --- | --- |
| [MG-GR001 · 递归系统的固定族、稳定分支与终止](proofs/MG-GR001/task.md) | 扩展距离、固定族、有限残差分支与终止界 | [目录](proofs/MG-GR001/) |
| [MG-GR003 · 平均恢复、迭代误差与一致速度](proofs/MG-GR003/task.md) | 平均恢复、逐点与一致速度的边界 | [目录](proofs/MG-GR003/) |
| [MG-GR102 · 有限轨道、规范投影与统一公式](proofs/MG-GR102/task.md) | 局部有限轨道与统一多项式的量词范围 | [目录](proofs/MG-GR102/) |
| [MG-GR106 · 整族恢复、固定点与一致性的范围](proofs/MG-GR106/task.md) | 整族恢复、同步复合与一致范围 | [目录](proofs/MG-GR106/) |

## 函数分析、变分与谱

| 试卷 | 考察内容 | 完整材料 |
| --- | --- | --- |
| [MG-GR004 · Hilbert复形的精确消元与近似消元](proofs/MG-GR004/task.md) | Hilbert复形、闭像与正则化边界 | [目录](proofs/MG-GR004/) |
| [MG-GR011 · 凸投影的恢复、复合与变分方程](proofs/MG-GR011/task.md) | 凸投影、仿射性与变分恢复 | [目录](proofs/MG-GR011/) |
| [MG-GR013 · 多项式记录、预解与谱的连续比较](proofs/MG-GR013/task.md) | 多项式与谱记录、预解和极限次序 | [目录](proofs/MG-GR013/) |
| [MG-GR105 · 观测完成、噪声误差与原空间极小点](proofs/MG-GR105/task.md) | 观测完成、极小值取到与正则化 | [目录](proofs/MG-GR105/) |

## 塔、分裂与整体实现

| 试卷 | 考察内容 | 完整材料 |
| --- | --- | --- |
| [MG-GR006 · 逆向塔的前缀、整体提升与选择](proofs/MG-GR006/task.md) | 有限前缀、整体提升、选择与障碍 | [目录](proofs/MG-GR006/) |
| [MG-GR007 · 等变分裂空间的稳定与自然性](proofs/MG-GR007/task.md) | 仿射分裂塔、稳定像与自然性 | [目录](proofs/MG-GR007/) |
| [MG-GR101 · 从同余记录到有限族的整体实现](proofs/MG-GR101/task.md) | 有限同余族的整体实现与逐项障碍 | [目录](proofs/MG-GR101/) |

各题目录完整保留 `case.json`、题面、参考、合同、评分、来源、审核和作者 Lean 证据。数学材料与附件均为原字节，状态仍为 **draft / human pending**；作者编译、AI审核和人工批准分别记录。[完整考察重点索引](../by-focus.md)同时覆盖默认与备选，并标明成员身份。

## 显式使用

在仓库根目录运行，例如：

```sh
python3 -m math_gauge validate --suite cases/reserve-suite.json
python3 -m math_gauge list --suite cases/reserve-suite.json
python3 -m math_gauge prepare --suite cases/reserve-suite.json --case MG-GR001 --out runs/reserve-gr001
```

这些命令不调用模型。默认综合评分配置绑定32卷，不适用于备选集；专项运行需要另行事前冻结成员、次数和计分方案。完整题面与白名单附件仍由共享 runner 导出，参考、分类和本页说明留在评审侧。

## 历史证据路径

[显式迁移表](relocations.json)只列这11个目录从 `cases/proofs/` 到 `cases/reserve/proofs/` 的移动。原作者账本、输入绑定和历史43卷/177槽配置继续保留记录时的逻辑路径与散列；离线核验按迁移表定位现存文件，历史配置恢复时重建原逻辑位置。旧题包和旧答卷不改写，迁移不代表重新编译或新候选运行。

[返回默认32卷](../README.md) · [备选成员清单](../reserve-suite.json)
