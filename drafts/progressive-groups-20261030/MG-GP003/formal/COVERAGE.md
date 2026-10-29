# MG-GP003 作者 Lean 与题面对齐

冻结题面 0.1.1。S3、S4、S6 完整。S1 已闭合给定仿射半局部化呈现的真实概形等化子，原拟射影 X 的共同仿射呈现接口仍缺；S2 的真实仿射邻域延拓比较也已完成；S1/S2 的一般原 X 接口及 S5 几何保留明确边界。编译通过不等于全题已完成。未运行候选模型，未获人工批准。

固定 Lean 4.29.1 / Mathlib 5e932f97dd25535344f80f9dd8da3aab83df0fe6。21 个显式本地模块见 modules.json / manifest.json；fresh 全部本地声明（含私有）闭包证据在 verification-report.json、declarations.json、logs/，只允许三个基础公理。七个母题模块原字节和哈希见 SOURCE-CLOSURE.json；新增八个模块为本批作者证明，没有引入额外外部库或目标假设。

| 阶段 | 状态 | 已证明与边界 |
| --- | --- | --- |
| S1 | partial | `affine_semilocal_descent_exact` 已证明真实 S、局部谱 S_i、Scheme.pullback S_i×_S S_j 的邻域呈现值及实际限制箭头满足等化子。原光滑拟射影 X 的共同仿射邻域存在性与原 X 到该图的完整呈现比较尚缺。 |
| S2 | partial | `actual_affine_two_closed_comparison` 已证明真实仿射 S 上原 H/G 的邻域延拓比较，只使用题给成功收缩及单射/局部同构条件；仍缺一般原 X 到仿射呈现的完整接口。 |
| S3 | complete | 实际 restricted inclusion 在限制方向为 final；典范 colimit comparison 的 isIso、同构、代表元公式均已证明。 |
| S4 | complete | 任意域上的实际 X=Spec k[t]、Σ={原点}、W=D(t)，满足平滑/积分/仿射/稠密；受限邻域类别为空，故非 final。 |
| S5 | partial | 已构造真实 finite-neighborhood canonical comparison、单点同构、逐邻域单射保持；任意域 HI PST 的全有限点比较仍缺实际转移几何。 |
| S6 | complete | 每阶段 ℤ --2→ ℤ 均不满射而极限微分双射；每类分别最终为零蕴含极限正合，无统一阶段偷换。 |

## S1 新增证明的对象与映射

`FiniteNeighborhoodDescent` 直接在原环境空间的有限点邻域余极限中粘合，不假设选点覆盖环境空间。
`LocalizationNeighborhoods` 证明有限局部化的实际谱像与所选点有同一开邻域系统；单点值典范等于真正 stalk，允许环境非闭点。
`PairLocalizationNeighborhoods` 用实际素理想不交定理证明共同一般化的任意开邻域可由 U_i∩U_j 细化，并证明 finality 和真正 colimit 同构；共同一般化为空也在范围内。

`ActualSemilocalGeometry` 构造真正的 S_i=Spec((M⁻¹A)_q)、与 A_(q∩A) 的基环兼容代数等价、真正 Scheme.pullback 及其 Spec tensor product 同构和投影公式；证明 pullback 的环境像确实是两个局部谱像的交。
`SchemeNeighborhoodValues` 用实际 T→U→X 开概形因子分解定义呈现范畴，通过开浸入唯一提升与像的邻域系统建立等价；因此不是把 T 的几何对象偷偷替换为像。全部 colimit 比较有代表元公式。
`ActualSemilocalDescent` 中 `actualRestrictionFamily_germ`、`fiberLeftRestriction_overlap`、`fiberRightRestriction_overlap` 明确证明真正限制箭头与先前 stalk / overlap 箭头交换，再给 `affine_semilocal_descent_exact`。

该端点不假设层的延拓先验在 S 上为层，直接通过原层的有限邻域粘合证明下降。它没有证明任意原光滑拟射影 X 的共同仿射邻域存在，也没有构造 S5 的有限对应、HI PST 或成功收缩几何；这些仍在 GAPS.md 中，阶段不会仅凭仿射子结论标为完整。

S5 原始定理范围已核对，详见 SOURCE-RECHECK.md。GAPS.md 区分数学定理有效性、冻结库对象缺失和 G1–G4 真正待证义务；外部文献没有成为 Lean 公理或证书假设。

## S2 新增实际延拓比较

`SchemeNeighborhoodMaps` 从原预层态射构造真正 `colim.map`，给所有实际 T→X 上的比较，并证明对实际 scheme maps 的自然性。实际 S 开子概形的值由 `schemeOpenValue` 给出，其限制、复合、二开限制和交叠差均由真实开浸入诱导。
`ActualOpenComparison.actual_local_representative` 从题给真实 S_i 比较满射选出实际 S 开集及 H(U) 邻域类；G(S) 的目标是任意邻域余极限类，不被加强为原环境全空间截面。局部环同构与原η的自然性明确连接实际 stalk。

`actual_affine_two_closed_comparison` 在真实仿射 S 的两个不同闭点穷尽条件下，先除去另一闭点构造分离覆盖，仅调用题给成功缩小后的正合行。交叠上的原η单射给相容性，已证明的 S1 下降给全局两开限制唯一性，从而原η_S双射。没有把“邻域延拓是层”补成假设，也没有假定原覆盖正合或交叠满射。整个阶段仍保留任意原光滑拟射影 X 到共同仿射呈现的接口边界。
