# OET 卷1第2章候选包：独立只读复核

**结论：可作为 `design_draft` 继续校准，未发现26项主要义务的实质遗漏、无关新增或循环证书输入。不能据此升为正式题。** 两章正文、两个背景 Lean 文件与 LICENSE 均和公开提交 `539b40cec73184d98e06d54fbd10e4b4698bd6e7` 的 Git 对象逐字节一致；最终快照列出的26个文件全部哈希一致。

本报告绑定最终 `review-snapshot.json` SHA256 `e0be48f98546847a83d167e2a81c3f4caf45d8f8c79515609d3ca60a9830008b`，候选投影 SHA256 `a4adadf7a88f7e5b82af752eefedc1b50abcac5ecccfa08251ccab123767b611`，task SHA256 `91ed0561ff82fc70e26bc995c73335302cad7b3ed1bc29d923425f1b22d3cfb5`。这是独立 AI 复核；`human_approved=false`。没有修改题包、重编译 Lean、调用模型或运行整章解答。

**覆盖与数学契约。** 章内8个编号结果、3个带证明注记、2道习题，加未编号的单行化简，共14个源单元。26项分为25个正文/习题结论和1个具体实例合法性义务；另有8组定义/表示检查，已在包内列出。P26检查给定两种规范和剪切算子的结构合法性，是“完整形式化具体例子”所需内容，不是额外出了一道独立题。[义务口径](/private/tmp/math-gauge-next-design-20261030/pilot-ch02/review/reference.md:7)。

| 义务 | 原文行 | 独立核对 |
|---|---:|---|
| CH02-P01 | [45–55](/private/tmp/math-gauge-next-design-20261030/pilot-ch02/candidate/source/02-operator-bounds.md:45) | 单指标集退化为标量 Lip 条件；采用一般 singleton/subsingleton 表示均可，不要求复刻原声明名。 |
| CH02-P02 | [58–64](/private/tmp/math-gauge-next-design-20261030/pilot-ch02/candidate/source/02-operator-bounds.md:58) | U⊆V⊆dom 的矩阵族包含方向为 L(V)⊆L(U)；Lip 不强加域非空。 |
| CH02-P03 | [66–72](/private/tmp/math-gauge-next-design-20261030/pilot-ch02/candidate/source/02-operator-bounds.md:66) | 全域证书在任意 U⊆dom 上仍合法；是 P02 的实例，但保留正文分项。 |
| CH02-P04 | [75–119](/private/tmp/math-gauge-next-design-20261030/pilot-ch02/candidate/source/02-operator-bounds.md:75) | 两步复合使用 U2=φ1(U1) 的实际像域；矩阵次序为 L2·L1。扩展非负数有限和分配有效。 |
| CH02-P05 | [132–138](/private/tmp/math-gauge-next-design-20261030/pilot-ch02/candidate/source/02-operator-bounds.md:132) | co-Lip 限制要求 U 非空，包含方向与 Lip 相同。 |
| CH02-P06 | [140–146](/private/tmp/math-gauge-next-design-20261030/pilot-ch02/candidate/source/02-operator-bounds.md:140) | 全域 co-Lip 在非空 U 上限制；不能丢掉 co-Lip 定义的域非空。 |
| CH02-P07 | [149–167](/private/tmp/math-gauge-next-design-20261030/pilot-ch02/candidate/source/02-operator-bounds.md:149) | 由 0≥ΣKd≥Kij di 且 di>0 得 Kij=0；di 或其他系数可为∞，不需有限性。 |
| CH02-P08 | [171–189](/private/tmp/math-gauge-next-design-20261030/pilot-ch02/candidate/source/02-operator-bounds.md:171) | co-Lip 两步复合保持实际像域、乘积次序和域非空；不另加可逆性。 |
| CH02-P09 | [198–219](/private/tmp/math-gauge-next-design-20261030/pilot-ch02/candidate/source/02-operator-bounds.md:198) | 任意正长度链的 Lip 连乘界；逐步数据必须足以构造链证书，不能仅输入最终结论。 |
| CH02-P10 | [198–219](/private/tmp/math-gauge-next-design-20261030/pilot-ch02/candidate/source/02-operator-bounds.md:198) | 任意正长度链的 co-Lip 连乘界；与 Lip 分支独立，不应要求同时有两种证书。 |
| CH02-P11 | [222–226](/private/tmp/math-gauge-next-design-20261030/pilot-ch02/candidate/source/02-operator-bounds.md:222) | 非空 U⊆dom(id) 下单位矩阵给 Lip；可证更一般的空域 Lip，但须覆盖正文。 |
| CH02-P12 | [222–226](/private/tmp/math-gauge-next-design-20261030/pilot-ch02/candidate/source/02-operator-bounds.md:222) | 同一单位矩阵给 co-Lip；保留正文非空 U。 |
| CH02-P13 | [231–260](/private/tmp/math-gauge-next-design-20261030/pilot-ch02/candidate/source/02-operator-bounds.md:231) | 任意非空矩阵序列，乘积条目为0 iff 每条固定端点路径至少有一个零因子；含 n=1。 |
| CH02-P14 | [231–260](/private/tmp/math-gauge-next-design-20261030/pilot-ch02/candidate/source/02-operator-bounds.md:231) | 乘积条目正 iff 存在所有层条目均正的路径；非空序列、固定端点和 n=1 空中间序列明确。 |
| CH02-P15 | [266–289](/private/tmp/math-gauge-next-design-20261030/pilot-ch02/candidate/source/02-operator-bounds.md:266) | 点对输出距离正向 ≤ 原输出距离+2ε；不把扩展非负误差改写为实数绝对差。 |
| CH02-P16 | [266–289](/private/tmp/math-gauge-next-design-20261030/pilot-ch02/candidate/source/02-operator-bounds.md:266) | 交换算子给反向加性界；同域扰动与伪度量对称性保证可交换。 |
| CH02-P17 | [291–298](/private/tmp/math-gauge-next-design-20261030/pilot-ch02/candidate/source/02-operator-bounds.md:291) | Lip 证书与正向扰动拼接；ε 可为∞，不需额外有限性。 |
| CH02-P18 | [300–308](/private/tmp/math-gauge-next-design-20261030/pilot-ch02/candidate/source/02-operator-bounds.md:300) | co-Lip 证书与反向扰动拼接；交换算子的对应分项可由泛型定理实例化覆盖。 |
| CH02-P19 | [348–364](/private/tmp/math-gauge-next-design-20261030/pilot-ch02/candidate/source/02-operator-bounds.md:348) | 指定输出行只有一个输入非零时，有限求和化为该单项；包括对角特例。 |
| CH02-P20 | [367–397](/private/tmp/math-gauge-next-design-20261030/pilot-ch02/candidate/source/02-operator-bounds.md:367) | 正 co-Lip 通道和正输入距离给正输出距离；不得假设点分离或有限距离。 |
| CH02-P21 | [367–399](/private/tmp/math-gauge-next-design-20261030/pilot-ch02/candidate/source/02-operator-bounds.md:367) | 所有对角 co-Lip 条目为正时反射族零距；结论不是点相等或一般单射。 |
| CH02-P22 | [409–430](/private/tmp/math-gauge-next-design-20261030/pilot-ch02/candidate/source/02-operator-bounds.md:409) | 重叠规范 d2=|Δs|+|Δt| 下剪切有 diag(1,2)，由 |Δs+Δt|≤|Δs|+|Δt|。 |
| CH02-P23 | [432–438](/private/tmp/math-gauge-next-design-20261030/pilot-ch02/candidate/source/02-operator-bounds.md:432) | 坐标规范下构造合法矩阵，通常输出行/输入列写法为 [[1,0],[1,1]]。 |
| CH02-P24 | [432–438](/private/tmp/math-gauge-next-design-20261030/pilot-ch02/candidate/source/02-operator-bounds.md:432) | 对任意合法矩阵，用 x=(1,0),y=(0,0) 迫使 M1→2≥1；无需所有条目有限。 |
| CH02-P25 | [444–458](/private/tmp/math-gauge-next-design-20261030/pilot-ch02/candidate/source/02-operator-bounds.md:444) | 标量双侧界只需 Lip 指定行稀疏；下界用 co-Lip 非负和的对角单项，不加 co-Lip 对角假设。 |
| CH02-P26 | [409–438](/private/tmp/math-gauge-next-design-20261030/pilot-ch02/candidate/source/02-operator-bounds.md:409) | 本题具体规范与剪切是合法数据的构造义务，含吸收元延拓、伪度量和保持吸收元；不是额外独立题。 |

原文的有限非空指标集、扩展非负值含∞、`0·∞=0`、伪度量可不分离、受限 co-Lip 域非空和矩阵输出行/输入列约定均需要保留；没有发现需要额外有限性、可逆性或点分离假设的目标。参考 DAG 有26个节点、10条边、最长2条边，只是一种实现路线。本章是一个相关的整章样本，不是26个独立难题，也不能宣称有26层推理依赖。

**证书没有直接循环，桥接仍是正式评审重点。** 已追踪固定提交的 `matrix_composition.lean`：29–35行的 `RightChainLipBounded` 和107–113行的 co-Lip 版本，递归只保存更短链证书及下一步在短链实际像域上的单步条件；全链结论由40–101行、118–183行的归纳证明建立。193–203行的最终包装很薄，它不能独自证明原文逐步数据与有序乘积已经对齐。应继续要求“原文逐步矩阵/实际域 → 链证书 → 指定有序乘积”的显式对应。

`path_algebra.lean` 的72–124行给列表乘积、列表证书和归纳正路径，131–197行证明乘积正/零与该谓词的关系。未发现把矩阵结论直接塞进字段，但 `ExistsPositivePath` 与原文固定端点、n−1个中间指标的等价，以及“无正路径”到“每条路径有零因子”的桥接，仍须在最终目标参考中核验。尤其要覆盖 n=1 的空中间序列。作者源码的准确路径、commit、hash和行号已存 JSON。[包内已保留这项边界](/private/tmp/math-gauge-next-design-20261030/pilot-ch02/review/reference.md:30)。

**候选输入与前置充分性。** 实际 candidate/ 只有投影列出的8个普通文件，无符号链接、目标第2章 Lean、评审文件、习题解答文件或编译产物。两份 Lean 只导入 mathlib 与已提供的第1章 gauge_space。原文自然语言证明按 task 明示属于 autoformalization 输入，因此它们的存在不是泄漏。

第1章提供本章需要的扩展伪度量、族零距、算子/定义域/实际像、有限复合和零步恒等约定；两个背景模块提供相应 Lean 基础及受限评估。没有统一的捆绑 GaugeSpace 类型不妨碍候选自行按原文封装；不能因此偷偷换成分离度量。第1章第162行的第4章链接只是前瞻导航，有限复合已经在本章定义，背景 `OperatorChain` 也只是幺半群复合辅助，不提供目标矩阵定理。[依赖边界](/private/tmp/math-gauge-next-design-20261030/pilot-ch02/candidate/dependencies.md:5)。

**编译证据的准确范围。** 核对了4条既有命令记录、4份日志哈希、两个候选背景源与实际编译源的哈希，以及固定的 Lean/mathlib 身份。记录覆盖版本检查、两个第1章模块编译和一次导入 smoke，退出码均为0；未重跑。smoke 只打印了 `gauge_zero_related_equivalence` 与 `operator_chain_eq_prod` 两个声明的公理依赖，不能称为全部声明的公理闭包审计。没有目标第2章、完整参考或模型解答编译通过的证据。[既有编译范围](/private/tmp/math-gauge-next-design-20261030/pilot-ch02/review/background-compilation.json:2)。

**本轮已澄清的项目。** 八组定义清单已移入题包；h-/oet- 锚点关系在包内说明且全部26项与8组可解析；任意 n 的泛型 Fin n 表示明确允许；候选 task 已固定编译器提交 `f72c35b3f637c8c6571d353742168ab66cc22c00` 和 mathlib 提交 `5e932f97dd25535344f80f9dd8da3aab83df0fe6`，与现有背景编译环境相符。

**正式冻结前剩余说明。**

- **N01：** task 的“全部正文数学断言”还需与原子分母形成可执行判定；26项覆盖全部主要结论，但 L40 的∞算术说明、L262 的证书序列实例、L308 的交换算子实例不应被判题人临时新增为独立失分项。 在最终评审合同声明这些语义通过 D01/D02/D03 与 P13/P14/P17/P18 的定义、通用定理实例或简短补充声明检查；任何实质未覆盖分项仍须记录，禁止以没有同名定理直接判遗漏。 [具体位置](/private/tmp/math-gauge-next-design-20261030/pilot-ch02/candidate/task.md:3)。

- **N02：** package-manifest 同时保留 compile_performed:false 与 background_compile_performed:true；具体 scope 已准确解释，未发现冒充目标编译，但无作用域字段会让单字段消费者误读。 正式化时去掉或弃用无作用域 compile_performed，仅保留 background/target 的明确字段及对应哈希。 [具体位置](/private/tmp/math-gauge-next-design-20261030/pilot-ch02/review/package-manifest.json:79)。

- **N03：** 候选投影目录正确，但目录分离本身不能证明模型进程无法读取 review、作者目标 Lean 或通过网络下载答案。 正式运行前实现并验证候选接收、允许导入、文件系统与网络输入边界；固定相同工具/修复预算。 [具体位置](/private/tmp/math-gauge-next-design-20261030/pilot-ch02/review/tracks.md:6)。

- **N04：** 原作者两类链证书和正路径谓词非循环，但本审查不是完整目标 Lean 验证；正文逐步数据到证书/指定连乘及固定端点路径的桥接仍须进入最终参考核验。 在完整目标参考中验证相应桥接与最终公理依赖，并保留独立人工审定状态。 [具体位置](/private/tmp/math-gauge-next-design-20261030/pilot-ch02/review/reference.md:30)。

N01 是细粒度评分合同的澄清，不是发现26项主要结论少了一条；N02 仅元数据整洁性；N03–N04 是包内已公开的正式化门槛。本次独立复核可以计为一次 AI 审阅证据，仍不能置人工批准、改动现有41题分母或产生模型成绩。

原文身份核对：

| 候选文件 | SHA256 | 公开提交字节相同 |
|---|---|---|
| candidate/source/01-foundations.md | `e6c5fc230ffa4099166bb789f90264ac8bbc5e6e78467c7aec3ac072dbef1526` | 是 |
| candidate/source/02-operator-bounds.md | `481e3e6ac6d021e7c56c6453831bf2e6e0b795b2e7e93dece4e61ef0488c86c3` | 是 |
| candidate/background/formal_oet/vol_01/ch_01_foundations/gauge_space.lean | `a34d6169c0424eafb6dc6d9844f7704fddb44b370d86c546d2ff130221a9bd0c` | 是 |
| candidate/background/formal_oet/vol_01/ch_01_foundations/operator_space.lean | `7171e02afc2742ce6ba266b40e6c9aa01f72c3ec5e42e4b1db9bdfd9b04a2060` | 是 |
| candidate/LICENSE | `4d2ea5dcaf833d41947541479bda77bd84f918f351af7ea7fbe404d56296f0cf` | 是 |

完整结构化证据、26项映射、最终快照文件哈希及引用范围见 [ch02-independent-review.json](/private/tmp/math-gauge-next-design-20261030/ch02-independent-review.json)。
