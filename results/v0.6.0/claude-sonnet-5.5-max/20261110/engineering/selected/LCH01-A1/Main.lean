import formal_oet.vol_01.ch_02_operator_bounds.channel_matrix
import formal_oet.vol_01.ch_02_operator_bounds.lip_colip_families
import formal_oet.vol_01.ch_02_operator_bounds.component_channels
import formal_oet.vol_01.ch_02_operator_bounds.colip_distinguishability
import formal_oet.vol_01.ch_02_operator_bounds.scalar_two_sided_bound
import formal_oet.vol_01.ch_02_operator_bounds.textbook_forms

/-!
# LCH01：第 2 章（算子界）选段形式化

模块与义务对应：

* `channel_matrix`            ：CH02-D03（输入/输出矩阵指标约定与乘法）
* `lip_colip_families`        ：CH02-D01（Lip 谓词与证书族）、CH02-D02（含非空条件的 co-Lip 谓词与证书族）
* `component_channels`        ：CH02-D07（分量通道、单输入通道、对角特例）、CH02-P19（单一输入项行化简）
* `colip_distinguishability`  ：CH02-P20（正 co-Lip 通道保持正距离）、
                                 CH02-P21（全对角正 co-Lip 反射族零距；不加强为点相等）
* `scalar_two_sided_bound`    ：CH02-P25（习题 2.2：标量双侧界）
* `textbook_forms`            ：P19、P20、P21、P25 的正文同形封装（含有限非空指标集与伪度量语境）
-/
