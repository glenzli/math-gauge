# MG-GP001 作者 Lean 与题面对齐

冻结题面 0.1.1；S1–S6 全部完成作者 Lean 与逐项题面对齐。AI 作者/独立审核、编译、公理闭包和 human approval 是不同证据：本组 human pending，未运行候选模型。

固定 Lean 4.36.0-rc1 / Mathlib 2cabef97b63d3275776b8b060d802de6a6fa1055 / TauCeti ab0153c648bc0f1364ea268fc806793beb01473a。64 个显式本地模块见 modules.json 与 manifest.json。fresh 当前源码与全部本地声明（含私有、借用原命名空间）的证据保存在 verification-report.json、declarations.json、logs/，只允许 propext、Quot.sound、Classical.choice。没有源目录 olean 或其他题目的编译产物复用。

21 个冻结母题模块保留原字节，来源在 SOURCE-CLOSURE.json；CW 子复形、RP² 和三角边界球面所需额外闭包及许可证分别在 vendor/。显式源码、题面各输入及 alignment 均由 v2 manifest 绑定。

| 阶段 | 状态 | 已证明 |
| --- | --- | --- |
| S1 | complete | 证明 q 本身是某同伦等价的正向映射；两个复合均有实际连续同伦。 |
| S2 | complete | 对题给包含构造实际 ConeAttachment ≃ₕ D∨Susp L；楔点为给定零伦的终点和悬挂 south，不同 d0 经路径得到同伦等价。 |
| S3 | complete | Nonempty and contractible punctured K; B ≤ K and v ∈ B; actual punctured-edge inclusion is a homotopy equivalence. An explicit integer linear equivalence H₂(Realization K;ℤ) ≃ₗ[ℤ] ZMod 2. All reduced rational homology groups vanish, and Realization K is not contractible. |
| S4 | complete | 推出 link 非空、|K|≃Susp |link|；每种非空有限 link 的悬挂类型均给满足原前提的构造；可缩充要条件是有限个实际整数增广边界矩阵正合，且仅依赖包含 v 的面关联。 |
| S5 | complete | 完整分类新增类型恰为两点离散空间的同伦型；非空 link 仍是悬挂。两点例满足去 v 可缩，因路径连通性不可能同伦等价任何非空空间的悬挂。 |
| S6 | complete | 悬挂信息不能逆向恢复同伦型；两个明确非空有限复形的悬挂实际同伦等价，而原实现不同伦。 |

完整假设、量词、域、表示、真实声明映射和阶段依赖见 alignment.json。

S2 的 ConeAttachment 和 BaseSuspensionWedge 是实际等价关系所定义的商，前者保留非可缩 D。给定零伦通过真实映射空间路径拼接，路径与逆路径相消给两复合同伦；楔点取零伦终点与悬挂 south。S5 单独覆盖空 link 和孤立顶点，不继承不存在的 B。

S3 对任意有限 RP² 三角剖分，利用真正双锥开覆盖的系数泛化 Mayer–Vietoris，把实际 RP² 的胞腔/奇异同调计算移到 K。约化有理零次由真实路径连通性处理；整数 H₂≃ZMod 2 排除可缩。有限重标记不限制输入 universe。

S6 使用题目允许的另一组有效反例：L₁=(三角圆∨三角圆)⊔{点}，L₂=三角圆⊔三角圆，均明确给出 Fin 6 上的面。对双锥删去顶点 3，link 是四边圆；其包含由对每个面插入 a=0/5 的真实线性同伦变为常值。其余复形的顶点 4 向 a 收缩，得到同一个有限悬挂核心。两次收缩固定所选楔点，共同核心路径连通，link 又由交换 0/5 的实际坐标同胚识别，因此得到实际悬挂同伦等价。原图不同伦则由图一孤立点分支与图二两个真实非可缩圆周分支推出；证明直接使用假设同伦等价的两个逆同伦。未引用缺失的有限 CW→有限单纯模型定理，也没有把群/矩阵计算当作空间结论。
