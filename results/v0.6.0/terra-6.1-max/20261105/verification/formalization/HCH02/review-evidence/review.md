# Terra HCH02 原始封存工程独立复审

结论：核实通过 **40/40**；未完成 **0**；未知 **0**。维持当前 40/40 数学完成数。此结论是 AI 评审，人工批准仍待定。

本次唯一评分来源是新标准槽 HCH02:A1 的 actual-project 原字节。result.json 与当前正式答卷的响应 SHA-256 一致；reservation.json 显示首次独立上下文、无前轮工程、无外部候选反馈。没有运行候选模型、修补候选源码或引用作者第2章实现。

- 原始主源码：`/private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/terra/jobs/HCH02-A1/actual-project/Main.lean`
- Main SHA-256：`76ebc1e8883123320e0e50f5bc51c6f048d4c5e15163b11d833ca3cf024c3006`
- 原始映射 SHA-256：`0def5aeeeeb1f2711e3e6014a6f83383e4b46a6a3c9154e34fabfa57986a60d6`
- 当前答卷 SHA-256：`184fbea416fda08e8b977ea313b40b1edd65968a24f3c694c40f3a583667d0c3`

封存 Main.lean、alignment.json、lakefile.lean、lean-toolchain 与答复对应代码块逐字节一致。lake-manifest.json 仅 JSON 空白不同，解析值相同；这不改变任何证明。全部封存 manifest 文件的字节数及散列均核实。

编译使用 Lean 4.29.1（f72c35b3f637c8c6571d353742168ab66cc22c00）及干净的 mathlib 5e932f97dd25535344f80f9dd8da3aab83df0fe6。两份冻结 CH1 源码先按实际 native 输入字节重新编译，再编译 Main 和可信审计模块；所有命令退出码为 0。编译器只能读取这些材料及固定公共依赖，禁止联网、子进程及读取仓库或封存原目录，隔离探针实际通过。

250 个本地声明均纳入公理闭包核查（Main 194、operator_space 40、gauge_space 16），并覆盖原始映射中全部 95 个唯一声明。公理并集恰为 Classical.choice、Quot.sound、propext，无额外公理。编译仅产生风格/弃用警告。此项仅证明所编码命题的内核有效性；以下逐项语义评审另行核对原文。

模型原始自评为 40/40 complete，并明确声称整章无已知数学缺口；原话及响应字节区间保存在 review.json。此次数学审计支持该声称，执行终态、格式、编译、语义及人工状态仍分开记录。

## 逐项结论

| ID | 结论 | 原始 Main.lean 声明起始行 | 语义核对 |
| --- | --- | --- | --- |
| HC02-D01 | 通过 | LipOn:44, LipFamily:49, LipFamilyOn:52 | LipOn 直接合取 U⊆dom f 及 U 内所有 x,y、所有输出 j 的 ENNReal 有限求和上界。LipFamily 把 U 取为完整 dom f，LipFamilyOn 是真实 Set；没有加入非空、有限距离或最优矩阵假设，空 U 正确保持真。 |
| HC02-D02 | 通过 | CoLipOn:55, CoLipFamilyOn:60 | CoLipOn 明确包含 U.Nonempty、U⊆dom f 和全点对全输出的求和下界；CoLipFamilyOn 为相应 Set。系数类型为 ENNReal，0 与∞均允许，空 U 被排除。 |
| HC02-D03 | 通过 | Coeff:20, displayMatrix:24, displayMatrix_apply:30, matMul:26, matMul_apply:33 | Coeff I 使用输入 i、输出 j；displayMatrix M j i 定义为 M i j。matMul B A i j 的实际定义是 Σk B k j*A i k，正是显示矩阵第 j 行第 i 列的普通乘法；直接函数/有限和表示已给所需对应，不以缺少同名 Matrix.mul 包装扣分。 |
| HC02-D04 | 通过 | matId:28, matrixProduct:435, matrixProduct_nil:439, matrixProduct_singleton:441, matrixProduct_cons:444 | matId 是 δij，matrixProduct 对施行顺序列表递归为 tailProduct 在左、首矩阵在右。nil、singleton、cons 等式和 matMul_one_left/right 均真实证明，故空乘积、单项及任意顺序边界保持。 |
| HC02-D05 | 通过 | opChain:431, reached:447, chain_domain_iff:469, domain_at_step:478, chain_image:487, chain_eq_frozen_reverse:785, LipSteps:496, CoLipSteps:501, lipSteps_iff_all:556, colipSteps_iff_all:586 | opChain 与 reached 按正向逐次施行并取真实集合像；subset_dom_comp、chain_domain_iff、domain_at_step 由全链定义域条件推出每步实际域合法，chain_image 证明全像等于逐次像。LipSteps/CoLipSteps 只存单步实际像域上的界，两个 iff_all 双向连接任意列表分解处的原始逐步数据；chain_eq_frozen_reverse 证明与冻结 OperatorChain 记法的反序对应，未把最终界藏入字段。 |
| HC02-D06 | 通过 | Paths:607, pathWeight:616, pathHasZero:620, pathAllPositive:624, pathsEquivSequence:683, pathWeight_eq_sequence:716, pathHasZero_iff_sequence:728, pathAllPositive_iff_sequence:740, one_step_path_unique:676 | 非空矩阵列表 M::Ms 的全部中间指标编码为 Paths I Ms.length，起点 i 与终点 j 单独传入，编码不附正性条件。pathsEquivSequence 是到 Fin (n−1)→I 的真正双射，逐权重与含零/全正谓词的对应均证明；Unit 表示 n=1 的唯一空中间序列。 |
| HC02-D07 | 通过 | Channel:22, Row:63, Col:65, Diagonal:67, RowDecoupled:69, ColDecoupled:72 | Channel=I×I；Row 固定输出 j 并允许任意唯一输入 i，Col 固定输入 i 并允许任意输出 j，Diagonal 对所有 i≠j 归零。RowDecoupled/ColDecoupled 各有合法证书及存在支撑指标的完整量词，没有把交叉位置强制为 i=j 或把证书解释成实际依赖的完整刻画。 |
| HC02-D08 | 通过 | ScalarFeasible:75, channelInf:79, LegalDomain:83, ScalarFeasibleLegal:85, channelInfLegal:88, legal_scalar_correspondence:91, channelInf_of_empty:399 | ScalarFeasible 的集合恰为所有点对的单输入 i、单输出 j 上界，channelInf 是该 Set 的 sInf，channelInf_of_empty 给空族∞。LegalDomain 明确把 U⊆dom f 编入子类型并证明与总定义的对应；这是合法域上相同对象的保守延拓，与 entryInf 保持分离。 |
| HC02-P01 | 通过 | singleton_lip_of_eq:129 | singleton_lip_of_eq 使用任意 i 与 ∀k,k=i 表达单元素指标集，对任意合法 U 点对将有限和化为 Lii*di。没有增加唯一元素必须是某个指定默认值、系数有限等前提。 |
| HC02-P02 | 通过 | global_lip_restrict:108 | global_lip_restrict 由 U⊆dom f 将任意全域证书限制到 U，得到真实 Set 包含关系。证明保留全部 x,y,j 的范围。 |
| HC02-P03 | 通过 | lip_restrict:102, lip_family_antitone:113 | lip_restrict 传递 U⊆V 与证书中的 V⊆dom f，并将全部点对条件限制到 U；lip_family_antitone 给出相应集合包含。无额外非空假设。 |
| HC02-P04 | 通过 | entryInf:96, entryInf_antitone:118 | entryInf 定义为合法矩阵条目取值集合的 sInf；entryInf_antitone 由证书限制得到 V 取值集合⊆U 取值集合并用完全格单调性。没有假定取到、可行族非空或各坐标下确界组成合法矩阵。 |
| HC02-P05 | 通过 | sum_matMul:141, lip_comp:151 | lip_comp 的下游证书域精确为实际像集 f(U)，显式保留全复合定义域条件。先用下游界，再逐中间指标使用上游界，sum_matMul 展开并交换有限和，结论为指定 matMul B A 的上界。 |
| HC02-P06 | 通过 | term_le_sum:185, colip_zero_of_collapsed:189 | colip_zero_of_collapsed 在任意合法受限 U 上证明单项≤总和≤零，利用 ENNReal 的零积性质与正输入距推出 Kij=0。取 U=dom f 即原全域目标，∞系数与∞输入距也覆盖。 |
| HC02-P07 | 通过 | colip_comp:168 | colip_comp 在相同实际像域 U 与 f(U) 组合两个真正的 co-Lip 下界，使用非负乘法、求和单调性及 sum_matMul。结论直接保留首步的 U.Nonempty，没有误用上界方向。 |
| HC02-P08 | 通过 | perturb_forward:310 | perturb_forward 从逐分量 symm、triangle 与 U 内逐点 δ 控制两次三角放缩，得到 g 像距≤f 像距+δj+δj。原文的扩展伪度量前提提供这些性质；定理对更宽集合也成立，故没有收窄公共定义域目标。 |
| HC02-P09 | 通过 | perturb_backward:330 | perturb_backward 用对称性交换逐点扰动前提，再调用正向界。得到原 f 像距≤g 像距+δj+δj，保留全部 U 内点对和指标。 |
| HC02-P10 | 通过 | perturb_lip:341 | perturb_lip 将 f 在同一 U 上的真实 Lip 求和上界代入正向像距扰动界。结论保留 2δ 的加性项，没有误报 g 具有相同纯 Lip 矩阵。 |
| HC02-P11 | 通过 | perturb_colip:350 | perturb_colip 从真实 co-Lip 求和下界≤f 像距，再接反向扰动界，得到指定加性方向。允许∞，没有使用减法。 |
| HC02-P12 | 通过 | lip_chain:506, lipSteps_iff_all:556 | lip_chain 对任意配对列表归纳，只从每步实际输入域上的 LipSteps 和全链定义域条件推出指定 matrixProduct 的全链上界。lipSteps_iff_all 证明逐步数据桥；定理还涵盖空链，因此包含所有 k≥1，顺序与 D04/D05 保持一致。 |
| HC02-P13 | 通过 | colip_nonempty_chain:536, colip_chain:520, colipSteps_iff_all:586 | colip_nonempty_chain 从首步真实 co-Lip 证书提取 U 非空，再调用独立下界归纳 colip_chain；各递归像的非空性由 image 保持。CoLipSteps 的双向逐步数据桥与指定矩阵积都存在，没有增添外部非空假设或最终下界证书。 |
| HC02-P14 | 通过 | opId_lip:297, matId_sum:282 | opId_lip 用 matId_sum 把单位矩阵求和精确化为 dj(x,y)，对任意 U⊆dom id 给出合法上界。它覆盖空 U 的更强版本，因此保留原非空情形。 |
| HC02-P15 | 通过 | opId_colip:303 | opId_colip 在显式 U.Nonempty 与 U⊆dom id 条件下使用同一求和恒等式给下界；co-Lip 的三项条件全部构造。 |
| HC02-P16 | 通过 | matrixProduct_paths:648, matrixProduct_zero_iff_sequences:752, one_step_path_unique:676 | matrixProduct_paths 真正展开为所有无约束路径权重的有限和；零和 iff 每项零、零积 iff 含零边，再经 D06 双射得到对所有普通中间序列的判据。纯 ENNReal 矩阵序列定理比合法 Lip 证书情形更强，n=1 由唯一 Unit 路径处理。 |
| HC02-P17 | 通过 | matrixProduct_pos_iff_sequences:763, one_step_path_unique:676 | 正有限和 iff 存在正项、正积 iff 每因子正，配合到普通 Fin 序列的双射得到存在全正路径 iff 指定乘积条目正。任意矩阵序列版本直接适用于正文实际 co-Lip 证书序列，并保留单步唯一空序列。 |
| HC02-P18 | 通过 | scalar_infeasible_of_zero:387 | scalar_infeasible_of_zero 对任意 λ 包括∞使用 λ*0=0，在给定 U 内零输入正输出点对处得到矛盾。显式证明整个 ScalarFeasible=∅，再得 channelInf=∞。 |
| HC02-P19 | 通过 | scalar_inf_attained:403 | scalar_inf_attained 用 a<∞取得非空可行族，将 sInf 写为可行常数的 iInf，并对每点对使用 ENNReal.iInf_mul。所需零下确界异常分支由 a>0 排除，得到 a 本身对所有 U 点对可行；未假定目标可行性。 |
| HC02-P20 | 通过 | scalar_feasible_upward:358 | scalar_feasible_upward 对每个点对用 ENNReal 右乘单调性将 λ0 的上界扩大到 λ1。没有有限或严格正限制。 |
| HC02-P21 | 通过 | scalar_above_inf:364 | scalar_above_inf 从 sInf<λ 找到更小的实际可行常数，并用向上封闭性得到 λ 可行。这比 0<a<∞ 的原文条件更一般，包含 λ=∞，没有误用下确界取到。 |
| HC02-P22 | 通过 | scalar_zero_inf_positive:370 | scalar_zero_inf_positive 将 a=0 与任意 λ>0 代入 P21，故包含全部有限正常数。没有把 0 也声明为可行。 |
| HC02-P23 | 通过 | exampleDist:794, example_metric:799, exampleDomain:797, example_domain_nonempty:811, example_domain_subset:814, example_channelInf_zero:832, example_zero_not_feasible:825 | 实际构造 X=Option Bool、bot=none、I=Bool；两分量的自距、对称、三角、bot 隔离及非吸收点均由 example_metric 证明。取合法恒等算子和全部非吸收点 U，false 分量异点距∞、true 分量异点距1；证明所有正标量可行、0 不可行且 inf=0，是真正非取到反例。 |
| HC02-P24 | 通过 | scalar_inf_lt_top_iff:376 | scalar_inf_lt_top_iff 直接用 sInf<∞ iff 存在更小的可行值给正向，反向用 sInf≤任意可行值。覆盖 a=0，不依赖 inf 取到。 |
| HC02-P25 | 通过 | zero_term:234, zero_term_erase:237 | zero_term 对系数0、任意包括∞的输入距离证明乘积0；zero_term_erase 用 Finset.sum_erase 明确删除相应求和项。没有推出整个输出距离为0。 |
| HC02-P26 | 通过 | row_sum:220, row_lip:229 | row_sum 保留任意输入 i 与输出 j，把 Row 条件下的有限和化成唯一可能非零项；row_lip 将合法证书界连接到该单项。没有施加 i=j 或全矩阵对角条件。 |
| HC02-P27 | 通过 | col_contribution:243 | col_contribution 对任意 k≠j 使用 Col L i j 得 Lik=0，再证明该证书贡献 Lik*di 为0。只描述固定输入列的上界求和贡献，未提升为算子的实际依赖刻画。 |
| HC02-P28 | 通过 | diagonal_lip:247 | diagonal_lip 对任意 j 将 Diagonal L 特化为 Row L j j，再使用一般单行结果，得到全部分量的标量上界。 |
| HC02-P29 | 通过 | two_sided:255 | two_sided 只对 L 的第 j 行施加 Row L j j；下界用 K 的单项≤总和≤输出距。K 不要求稀疏、对角、有限或正，精确保留历史修订后的条件与∞情形。 |
| HC02-P30 | 通过 | diagonal_two_sided:262, finite_diagonal_two_sided:272 | diagonal_two_sided 对任意 j 实例化双侧结果；finite_diagonal_two_sided 将同一上下界与明确假定的全部对角 L、K 系数有限性一起返回。没有误推所有距离有限或系数正。 |
| HC02-P31 | 通过 | colip_channel_pos:202 | colip_channel_pos 以 Kij>0 与输入距>0 得 ENNReal 乘积正，再由单项≤总和≤输出距推出输出距正。输入和系数可为∞，没有除法或有限逆。 |
| HC02-P32 | 通过 | colip_reflect_zero:209 | colip_reflect_zero 对每个 j，以 Kjj>0 和若输入该分量距非零则正的反证得到输入距0。结论正是冻结 GaugeZeroRelated，未增加族分离或提升为 x=y。 |

## 证据与边界

- `review.json`：40 项完整结论、原始自评与逐源码行对应。
- `kernel-report.json`：真实隔离编译命令、日志、输入散列、依赖身份、声明清单与公理闭包。
- `alignment.original.json`：原始封存模型映射，未改写模型字段。
- `actual-project-manifest.original.json`：原始工程清单原字节副本。
- `sources/Main.lean`：实际封存主源码的原字节编译副本。

有效替代证明和直接函数表示按其实际语义接受；没有要求与参考同名的包装声明。完整链、实际像域、普通有限序列路径桥、正有限下确界取到及零下确界非取到反例均在原始工程中真实存在。当前形式比较资格与人工批准不由本报告自动提升。
