import formal_oet.vol_01.ch_02_operator_bounds.channel_matrix
import formal_oet.vol_01.ch_02_operator_bounds.lip_matrix
import formal_oet.vol_01.ch_02_operator_bounds.colip_matrix
import formal_oet.vol_01.ch_02_operator_bounds.component_channel
import formal_oet.vol_01.ch_02_operator_bounds.colip_reflection
import formal_oet.vol_01.ch_02_operator_bounds.exercise_02_02

/-!
# LCH01 · 通道接口节群 —— 第 2 章义务清单总入口

导入 `formal_oet/vol_01/ch_02_operator_bounds/` 下全部目标模块，
覆盖 obligations.json 的 8 项义务：

| 义务        | 模块与声明                                                                    |
|:------------|:------------------------------------------------------------------------------|
| `CH02-D01`  | `lip_matrix.lean`：全域/受限 Lip 矩阵谓词与证书族                              |
| `CH02-D02`  | `colip_matrix.lean`：含非空条件的受限 co-Lip 矩阵及证书族                     |
| `CH02-D03`  | `channel_matrix.lean`：输入/输出矩阵指标约定与乘法                            |
| `CH02-D07`  | `component_channel.lean`：分量通道、单行稀疏与对角特例                        |
| `CH02-P19`  | `component_channel.lean`：单一输入项行化简（含对角特例）                      |
| `CH02-P20`  | `colip_reflection.lean`：正 co-Lip 通道保持正距离                             |
| `CH02-P21`  | `colip_reflection.lean`：全对角正 co-Lip 反射族零距（不可加强为点相等）        |
| `CH02-P25`  | `exercise_02_02.lean`：习题 2.2 标量双侧界                                    |

冻结前置模块为 `formal_oet.vol_01.ch_01_foundations`
（`gauge_space.lean`、`operator_space.lean`），保持原样导入。
-/
