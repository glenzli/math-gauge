GP003 S5 的独立结论：在本次查验的固定 Mathlib 和上游 Motivic 源码范围内，没有找到能直接闭合题目全部量词的现成定理。剩余工作包含实质性的有限点转移几何，不只是漏导入一个文件或补一个同构重写。数学命题仍由 MVW Lemma 22.12 支持；这是 Lean 实现边界，不是题目被证伪。

本次只读检查了当前题面、两份合同、参考、GAPS、SOURCE-RECHECK、实际邻域比较定义及引用的 external-library-review。重新查询上游默认分支得到的 HEAD 仍为 `a6805c4a87cdfd7717dd7a94039246a167f15380`。该提交的完整树含 4,314 条记录、2,414 个 `Motivic/` 下 Lean 文件；读取了 16 份相关源码/说明并逐个核对 Git blob 身份。没有执行上游 Lean 编译、传递公理审计、增加 profile 或修改仓库文件。`external-sources.json` 与 `local-source-hashes.json` 固定本次证据。

| 已有实际接口 | 为什么没有直接完成 S5 |
| --- | --- |
| `Motivic.Cor k` 和 `PresheafWithTransfers k` | 是真实有限对应范畴和加性函子，值得复用。但使用 Lean 4.34.1、另一 Mathlib/Aglib；当前 4.29.1 项目未集成或核验其闭包。即使集成，下面的有限点论证仍未提供。 |
| `nisnevichSheafify_isA1Invariant` | 任意域范围正确，但证明的是实际 Nisnevich 层化自身的同伦不变性，不是原预层到 Zariski 层化在半局部邻域余极限上的单位同构。 |
| `integralAffineLocalZero_of_field` | 给出每个点各自的原预层零邻域：`∀ x, ∃ U_x`。S5 注入性需要同一个邻域包含全部指定点；不能把量词换成 `∃ U, Σ ⊆ U`。 |
| `section_eq_zero_of_dense_open_of_separated` | 显式需要分离性。将它用于原始 F 来建立分离化前的半局部注入性会循环。 |
| `nisnevichImage` 的 transfers、HI、分离性 | 这是 Nisnevich 单位的像；必须另证它与 Zariski 局部零商的实际比较及单位相容。不能仅改名字替代 G2。 |
| `ModelWholeCylinderLifting` | 结论仅要求底部开集非空，未保持指定有限点集。它不能通过 S3 的邻域余终性替代保点收缩。 |
| `exists_zeroPoint_original_lifting` | 明确保留一个选定点，未保留任意有限点集。其 `Smooth` 有限型底也不能直接换成一般本质光滑半局部化。 |
| `twoLocalization_standardTriple_geometry` | 验证已选定正规化、边界和两次局部化的几何性质；没有构造任意有限点的成功选择，也没有给出 PST 的 Mayer–Vietoris 零同伦/正合性。 |

以上边界由实际签名确认，特别可参看 [DenseDetection](https://github.com/kangxyz/motivic/blob/a6805c4a87cdfd7717dd7a94039246a167f15380/Motivic/Cohomology/A1/Sheafification/DenseDetection.lean)、[CylinderCriterion](https://github.com/kangxyz/motivic/blob/a6805c4a87cdfd7717dd7a94039246a167f15380/Motivic/Cohomology/A1/Sheafification/CylinderCriterion.lean) 和 [OriginalPointLifting](https://github.com/kangxyz/motivic/blob/a6805c4a87cdfd7717dd7a94039246a167f15380/Motivic/Cohomology/A1/LocalVanishing/ZeroNeighborhood/OriginalPointLifting.lean)。

“逐点为零”与“同时有限点为零”的差别不是纯技术细节。作为普通预层的逻辑诊断，取半局部曲线的三点空间 `{η,p,q}`，令预层在全空间取 Z，在所有真开集取 0，限制为零。它在每个点的茎为零，但包含两个闭点的邻域系统只有全空间，因而半局部值为 Z。这里没有声称此预层带转移或同伦不变；这个例子只说明不能省掉恰要证明的额外几何。

确实存在可复用的更强下层结果：`Frames/FiniteNeighborhood.lean` 的 `exists_principal_unitIso_around_finset` 在一个实际主开集上同时保留任意有限素点集，并平凡化真实线丛；无环境闭点、Noetherian 或非空点集假设。它可以减少标准三元组路线中的线丛工作，不能直接消去一个 HI PST 截面或产生所需覆盖正合性。[实际源码](https://github.com/kangxyz/motivic/blob/a6805c4a87cdfd7717dd7a94039246a167f15380/Motivic/Aglib/AlgebraicGeometry/Modules/Invertible/Frames/FiniteNeighborhood.lean)

据此将工作区分如下：G0 是真实外部依赖集成与核验；G4 的普通邻域、局部化、纤维积、位点及归纳桥属于可继续完成的数学工程；G1 的同时有限点检测、G3 的成功保点收缩及其转移作用/有限域消灭论证，是当前不可由现有端点直接推出的核心几何。G2 也需要真实的转移相容与单位比较；已有 Nisnevich image 提供潜在材料，但本次未找到已证明的 Zariski 商比较。即使 G4 全部补完，也不能据此将 S5 改为 complete。

这与上游仍列出的标准三元组分裂、相容边界修正、有限点几何存在及有限域转移下降的待完成范围一致；该清单是支持证据，结论同时基于上述实际源码，而非仅相信 README。[上游说明](https://github.com/kangxyz/motivic/blob/a6805c4a87cdfd7717dd7a94039246a167f15380/Motivic/AlgebraicGeometry/Correspondences/README.md)

重新阅读的 [MVW 作者版](https://sites.math.rutgers.edu/~weibel/MVWnotes/prova-hyperlink.pdf) 印刷页 185–187 明确采用有限点半局部化，22.10 保留成功收缩并另处理有限域，22.12 以 11.1、22.9、22.11 和闭点数归纳得出目标。引用它可以完成本题的书面作答要求；把该结论或它的全部后果装成 Lean 假设，不能完成作者 Lean 核验。

搜索结论只限本次明确记录的仓库/提交/查询，不宣称全球不存在别的证明。没有把公共代码声明当成已在本仓库通过的 Lean 证据，没有改变题目条件，也没有运行候选模型。
