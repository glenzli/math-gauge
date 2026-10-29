# MG-GR010 作者 Lean 覆盖

六阶段实际对象证明齐全；作者数学自查、独立语义复核和内核验证分开记录。Human review pending；未运行候选模型。

原八个数学模块和旧审计逐字复制；新增 LocalCompact、ProbeRecognition、JointComposition 补齐延伸阶段。旧题编译/模型成绩不继承，当前全部显式模块重新编译并审计所有本地声明。

| 阶段 | 原条件与实际结论 |
|---|---|
| S1 | 仅 X 局部紧；题定 Hausdorff Y/Z 可任意，不假设 Z 局部紧。 通常评价连续；实际 curry/uncurry 双射及三变量自然公式。 借用 Mathlib 原生紧开评价证明中的紧邻域论证；仅要外层连续函数集合的双射，不偷用须 Z 局部紧的外层函数空间 Homeomorph。 |
| S2 | 任意同一宇宙小 Hausdorff X/Y；全部 profinite 或 CompHaus 探针。 两种探针拓扑相同；全部 Nat 等同 C(kX,kY)；所有目标原连续实现 iff X 紧生成。 点值自然性决定实际函数，紧探针检测证明连续；必要性由真实 hX→hkX 的恒等变换恢复 X→kX 的连续恒等。 |
| S3 | 任意原 Hausdorff X/Y/Z，不要求原 X 局部紧或紧生成。 M 表示全部参数化记录，实际评价诱导全部参数双射；大小、自然性及空对象边界。 八个完整母题数学模块逐字重编译；不是把指数律当数据输入，已有连续 curry/uncurry、真实 compact-open 与所有探针桥。 |
| S4 | 第一可数 Hausdorff；实际 Q/R 标准拓扑反例。 第一可数确实推出 kX=X；通常评价却可以不连续。 Mathlib 第一可数→sequential→compactly generated 的收敛序列探针证明；有限紧开约束合并紧 K，再在 V\K 取点用 Urysohn 构造零于 K、值 2 的实际连续函数。 |
| S5 | 任意 Hausdorff 原空间；反例 D=P(N) 由 Cantor 定理实际证明不可数。 连续底集恒等 kX→X 的实际 h_f 为同构，但 f 不是原拓扑同胚。 所有紧子集有限的证明使用任意无限集的可数无限子集；有限像探针实际提升到离散空间；不连续逆由 infinity 单点非开。 |
| S6 | X/Y/Z Hausdorff；M 为 S3 的紧生成实现，复合源是真实 k 积；识别结论针对原给定连续 f。 联合连续复合、结合与单位；h_f IsIso iff 存在同胚的逐点函数恰为 kf；第一可数时逐点函数恰为原 f 的 Homeomorph。 反柯里化两次连续 k-evaluation 构造联合连续三变量映射，再用指数律；不是只检查固定因子的预/后复合。 |

题面使用的两个集合宇宙由原 MappingUniverse 的实际 ULift 自然变换双射处理，不删去较大宇宙中的任何自然变换；所有实际空间及 profinite 覆盖仍小。所有题面、参考、合同、候选投影与作者源码哈希绑定到 v2 manifest。编译本身不自动证明语义对齐。
