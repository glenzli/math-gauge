# 四个固定关注断言的独立核查（身份复核修订）

四个真值仍为 **假、假、真、真**。前两项为 subclaim，后两项为 stage；数学结论没有因题面清理而改变。未修改仓库、运行模型或编译 Lean，人工审核仍待完成。

## 两个核验时点与本次纠正

1. **初次完整阅读：0.1.0。** 当时完整读取了四组 task/reference/contract；工具输出显示旧版本及评分标题。精确 UTC 时间没有单独保存，不能事后编造。归档中的 12 文件与初读身份一致。

2. **当前保存及绑定的快照：0.1.1。** 此次重新读取确认 selection-review-b-snapshot 的全部 12 文件与现行源逐字节一致；当前合同实际版本为 0.1.1，题面已去除旧分值和机器题型。此前报告把初读旧版的固定叙述套在最终新版散列上，叙述不一致。

3. **本次最终独立差分复核：2026-10-30T05:32:34.433412+00:00。** 校验 0.1.0.tar.gz 的归档散列后，逐项比较全部旧/新文件：四份 reference 完全未变；四份 contract 只改 version；四份 task 的全部差异仅是版本、评分标签和中性作答说明。23 个阶段的数学主体逐字节相同，共同数学设定未改。由此将此前完整数学审查明确关联到最终 0.1.1。

不能只凭快照推断中间具体写入者或精确变更瞬间，本报告不作该归因。参考解内沿用的 0.1.0 作者页眉属于未改的评审文本，不是最终 case/contract 版本。

| 关注项 | 范围 | 真值 | 关键区别 |
|---|---|---|---|
| GR002 S6 | subclaim | 假 | 精确范数 C 的取到，不否定 C+ε 有限匹配 |
| GR004 S4 | subclaim | 假 | 算子范数收敛，不否定强收敛 |
| GR007 S4 | stage | 真 | 全部四类结论；自然运输不等于自然首选 |
| GR014 S6 | stage | 真 | 任意离散域的有限坐标闭方程，不依赖紧性 |

## MG-GR002 S6

**最终合同版本：0.1.1；范围：** subclaim；**真值：** false。

独立陈述：

设 E 为实 Banach 空间，E′ 为其连续对偶。对 E′ 的每个有限维线性子空间 F，给定线性映射 λ_F:F→ℝ；当 F⊆G 时 λ_G|_F=λ_F。给定有限 C≥0，且 |λ_F(φ)|≤C‖φ‖ 对所有 F 和 φ∈F 成立。定义 q_F:E→F*，q_F(x)(φ)=φ(x)。判定以下断言是否成立：对每个这样的 F，都存在 x∈E，使 q_F(x)=λ_F 且 ‖x‖≤C。

量词核验：对所有合法 E、记录族与给定界 C，要求 ∀有限维F ∃x_F；并非要求一个共同 x 同时匹配全部 F。反例只需在一个合法完整记录族中给出一个失败 F。

必须保留：实 Banach E；E′ 是连续对偶；全部有限维子空间上的线性记录及包含相容性；有限且非负的同一给定界 C；精确匹配 q_F x=λ_F；上界恰为 C；允许匹配向量依赖 F。

不能继承或偷加：S2/S3 的 E 自反；S5 的 z_λ 弱星连续；S6 正向分支中的 ε>0；本子断言已无 ε 变量，不能同时假设 ε>0 和 ε=0。

阶段边界：整个 S6 为 synthesize/classification：C+ε 下的精确有限匹配为真；ε=0 的普遍可取性为假；还要求解释有限匹配与整体原空间实现的差别。不能将整个阶段标成 false，也不能把否定解释为 C+ε 分支失败。

论证核验：

1. 取 E=c₀(ℕ_{≥1};ℝ)，范数为上确界；它是 ℓ∞ 的闭子空间，故 Banach。其连续对偶等距为 ℓ¹：泛函在坐标向量上的值绝对可和，有限符号向量给范数等式，有限截断给评价公式。

2. 在 E′=ℓ¹ 上定义 z(a)=Σ_j a_j，令 λ_F=z|_F。级数绝对收敛，z 线性且 |z(a)|≤‖a‖₁，故记录对全部有限维 F 线性、相容并统一满足 C=1。

3. 取 φ=(2^{-j})_{j≥1}∈ℓ¹，F=span{φ}。有 ‖φ‖₁=1、λ_F(φ)=1。若 x∈c₀ 且 ‖x‖∞≤1、q_Fx=λ_F，则 Σ_j 2^{-j}(1−x_j)=0。每项非负，故全部 x_j=1，矛盾于 x∈c₀。

4. 因此 ε=0 子断言为假。对照正向分支：q_F 满射，E/ker q_F 的商范数在 λ_F 对应类上的值为 sup_{φ∈F,‖φ‖≤1}|λ_Fφ|≤C，给每个 ε>0 的原像范数≤C+ε；下确界未必取到恰是失败机制。

参考判断：可靠；反例给出完整记录族而非孤立任意数据，并保持实标量、Banach、统一界、精确匹配和 ∀F∃x 的量词。

实际清理差分：Update visible version 0.1.0 to 0.1.1 and remove total score；Remove per-stage header scores；Remove candidate-facing alternative-proof grading reassurance。全部 6 个阶段数学主体未变，reference 未变，contract 仅版本改变。

| 文件 | 初读 0.1.0 SHA-256 | 最终 0.1.1 绑定 SHA-256 |
|---|---|---|
| `task.md` | `07d7d71f1464e7f9f16c6b6f4119e15347a3f779ca59f83649bb2ac66d3fe088` | `919538d38d1904d79b25bf93437f5921d85962bcaad026af2735090da39b0f27` |
| `reference.md` | `6349cfc29883c26e03c9e853b4417dd58e4a40c8f40014cb05811a9d613bc5dd` | `6349cfc29883c26e03c9e853b4417dd58e4a40c8f40014cb05811a9d613bc5dd` |
| `contract.json` | `ad1e6f234e0e50d5da3f6fe80edb7236cc3c51f7522929cc88873b9900703e87` | `8c2875d3e8ab39ba65f9914441af3c02aa85ae1e0258915d85bb11fc8b2f2dd2` |

## MG-GR004 S4

**最终合同版本：0.1.1；范围：** subclaim；**真值：** false。

独立陈述：

给定有限长复 Hilbert 复形 0→H₀→⋯→Hᵣ→0，r≥1，各 d_j:H_j→H_{j+1} 为有界复线性映射且 d_{j+1}d_j=0；约定 H_{−1}=H_{r+1}=0、d_{−1}=d_r=0。假设对所有 0≤j≤r 都有 ker d_j=closure(ran d_{j−1})。令 L_j=d_{j−1}d_{j−1}*+d_j*d_j。对 ε>0 使用有界逆 (L_j+εI)⁻¹。判定是否对每个 j 都有 ‖ε(L_j+εI)⁻¹‖→0，极限为 ε↓0，范数为算子范数。

量词核验：全称量化有限长有界复 Hilbert 复形及全部度数，层空间可无限维；约化无环用像的闭包，不能改成精确无环。ε 取正实数趋于 0。有限长度不表示层有限维。

必须保留：有限长 r≥1，复 Hilbert 层与有界复线性微分；全部复形关系及两个端点零微分；每个度数 ker d_j=closure(ran d_{j−1})；L_j 的准确伴随公式；ε>0、ε↓0、算子范数而非强算子收敛。

不能继承或偷加：S1 每层有限维；S2 的严格正能量下界 λ_j>0；S5 待比较的闭值域或有界逆条件。

阶段边界：S4 同时要求证明正则化逆存在、近似收缩恒等式和强收敛，并判断范数收敛。前三项为真，最后全称子断言为假。contract.stages[S4].expected=true 对应主证明任务，turns 的 scope=subclaim/expected_truth=false 才是本次关注标签，不能拿 stage.expected 直接推断子问真值。

论证核验：

1. 取 r=1，H₀=H₁=ℓ²(ℕ_{≥1};ℂ)，d₀=diag(1/n)，d_{−1}=d₁=0。d₀ 有界、单射、自伴且范数 1；值域含全部有限支撑向量，故稠密。因此 R₀=0、R₁=0，且全部复形关系成立。

2. 两层 L₀=L₁=diag(1/n²)。对每个 ε>0，L_j+εI 可逆，逆为 diag((1/n²+ε)⁻¹)，算子有界且范数≤1/ε。

3. ε(L_j+εI)⁻¹=diag(ε/(1/n²+ε))。所有对角系数≤1，并随 n→∞ 趋于 1，故算子范数恰为 1，对每个 ε>0 都如此。所选子断言为假，而且两个度数都失败。

4. 同一例中每个固定 n 的系数随 ε↓0 趋于 0；由系数统一≤1 和 ℓ² 尾部控制，对每个向量强趋于 0。这正说明它不反驳 S4 的强收敛结论。一般情形亦由 ker L_j=0、ran L_j 稠密与一致范数界得到强收敛。

参考判断：可靠；反例同时验证复标量、有限长度、端点与全部约化无环条件，并精确计算范数为 1。

实际清理差分：Update visible version 0.1.0 to 0.1.1 and remove total score；Remove per-stage header scores；Remove candidate-facing alternative-proof grading reassurance。全部 5 个阶段数学主体未变，reference 未变，contract 仅版本改变。

| 文件 | 初读 0.1.0 SHA-256 | 最终 0.1.1 绑定 SHA-256 |
|---|---|---|
| `task.md` | `20302e219b66c7abd53e3f00a24ddd8377e80d853c2ac65d08ae467e7f80a7c7` | `0003d1abc69107fd900e85fe46980851dae6010838ac2f825372160633eee92a` |
| `reference.md` | `e08e6c2d8d46c46965997e8743cd602eb9594a842f9af76cde4bcec798bb13d7` | `e08e6c2d8d46c46965997e8743cd602eb9594a842f9af76cde4bcec798bb13d7` |
| `contract.json` | `9aa0c2adbf93ea48d202dba80ce5c0ce7c9aa0c91b29744363aaf03b812797fb` | `fd48d7bd2c5849ddf6dc0709d84942d4b01c3dc0db2c3f215898d9fcb2a9f4f3` |

## MG-GR007 S4

**最终合同版本：0.1.1；范围：** stage；**真值：** true。

独立陈述：

采用 ZFC。设 G 为有限群，k 为任意域，C 为有限维 k 线性 G 表示。对 n≥1 给定 G 表示短正合列 0→A_n→^{i_n}B_n→^{q_n}C→0，且每行已存在 G 等变线性分裂。给定等变线性过渡 α_n:A_{n+1}→A_n、β_n:B_{n+1}→B_n，满足 β_n i_{n+1}=i_n α_n、q_n β_n=q_{n+1}。令 S_n={s∈Hom_G(C,B_n):q_ns=I_C}、W_n=Hom_G(C,A_n)，只要求每个 W_n 有限维，A_n、B_n 允许无限维。A_∞、B_∞ 均为实际相容序列空间，q_∞ 为各坐标的共同 C 值。判定下列目标是否全部成立：存在 β_n s_{n+1}=s_n 的等变分裂族；由此得到保持包含及投影的等变同构 B_∞≅A_∞⊕C；全部相容分裂及这些直和同构以 lim W_n≅Hom_G(C,A_∞) 为平移空间分类；对任意各层与 C 上均为等变同构且全部结构图交换的整塔同构，整个选择空间及其平移空间可自然双射运输。

量词核验：共同设定全部保留，尤其逐行等变可分裂、同一个商 C、可数 n≥1 的塔及交换关系。仅放宽 A_n/B_n 的维数；每个 W_n 有限维不要求共同维数上界、过渡满射或统一稳定时刻。

必须保留：ZFC、有限群 G、任意域 k、有限维表示 C；每行短正合且已有等变线性分裂；α_n、β_n 的方向、等变性与两类交换关系；每个 W_n 有限维；实际相容序列的极限；自然性只量化整个解空间在整塔同构下的运输。

不能继承或偷加：S2 的 A_n/B_n 有限维；S3 的最终 T_n 双射；S6 所讨论的自然首选截面；char(k) 不整除 |G|、过渡满射或有限集合/拓扑紧性。

阶段边界：此项 scope=stage，四项结论整体为真。仅证明相容分裂存在仍未完成其余分类和运输要求。自然运输不是对全部整塔自同构自然选择某个首选分裂；后一个不同断言在 S6 中为假。

论证核验：

1. 每个 S_n 非空。两个分裂差唯一经 i_n 写成 i_n u，u∈W_n；因此 S_n 是以 W_n 为方向的有限维仿射空间。T_n(s)=β_ns 为仿射映射，其线性部分为 u↦α_nu。

2. 固定 n，非空仿射像 I_{m,n}=T_{m,n}(S_m) 随 m 下降。严格包含迫使维数严格下降，故最终稳定为非空 I_n。取共同足够大的 m，使 n 和 n+1 的像都稳定；一个在 S_m 的原像经 T_{m,n+1} 给 T_n:I_{n+1}→I_n 的原像，所以稳定像间确实满射。ZFC 中逐次选择得到相容分裂族。

3. 定义 s_∞(c)=(s_n(c))，q_∞s_∞=I_C。逐坐标用 i_n 单射及交换关系证明 ker q_∞=im i_∞。Φ(a,c)=i_∞a+s_∞c 的逆由 c=q_∞b 和 b−s_∞c 的唯一 A_∞ 原像给出，得到保持包含及投影的等变直和。

4. 两个相容分裂差对应唯一族 u_n∈W_n，其相容条件正是 u_n=α_nu_{n+1}。所以全部相容分裂是非空 lim W_n 挠子，全部合规直和同构与它双射。逐坐标给 lim Hom_G(C,A_n)≅Hom_G(C,A_∞)，无需附加极限交换定理。

5. 若整塔同构记为 a_n:A_n→A′_n、b_n:B_n→B′_n、d:C→C′，则 s_n↦b_ns_nd⁻¹、u_n↦a_nu_nd⁻¹。结构图交换逐项保证右逆、相容、等变及平移；逆同构给反向双射，复合公式保证自然运输。整个论证没有使用 A_n/B_n 有限维。

参考判断：可靠；有限维性只在实际仿射参数空间下降链处使用。稳定像间满射、极限核、全部选择和同构运输均已证明，无 Maschke 假设或自然首选偷换。

实际清理差分：Update visible version 0.1.0 to 0.1.1 and remove total score；Remove per-stage header scores；Remove candidate-facing alternative-proof grading reassurance。全部 6 个阶段数学主体未变，reference 未变，contract 仅版本改变。

| 文件 | 初读 0.1.0 SHA-256 | 最终 0.1.1 绑定 SHA-256 |
|---|---|---|
| `task.md` | `0237eaebb74c5c16d815ae962621790a14b04217f0e9eddfd1f005fb4c53b350` | `4ae139bae167e5538dae0928fe76f4f4064cfcdafe6e06f1b41bf1e645c48728` |
| `reference.md` | `1ac4cd253ce9aec24f13d1b08f9924c56e51792d4bde09e867735ba405ca0c50` | `1ac4cd253ce9aec24f13d1b08f9924c56e51792d4bde09e867735ba405ca0c50` |
| `contract.json` | `32c7fdc26457dbe71fa446041d0a354df87dcc715ecf7d9434d917cfcfc0afdd` | `02d2be78c329c7f4453d10d98760095f02a16c3d3c0cb86810ca6b4cb1de2092` |

## MG-GR014 S6

**最终合同版本：0.1.1；范围：** stage；**真值：** true。

独立陈述：

采用 ZFC。设 k 为任意域并赋离散拓扑，I、J 为任意集合。对每个 j∈J 给定有限支撑行 a_j∈k^{(I)} 和常数 b_j∈k，且每个有限 F⊆J 都存在全赋值 x∈k^I，使 Σ_i a_j(i)x_i=b_j 对 j∈F 成立。令 S={x∈k^I:∀j∈J, Σ_i a_j(i)x_i=b_j}。对每个 A⊆I，令 π_A:S→k^A 为坐标限制，k^A 赋乘积拓扑。判定是否每个 π_A(S) 都闭；若成立，给出只涉及有限坐标的闭方程描述。

量词核验：所有行各自有限支撑，解变量在全积 k^I；I/J/A 可任意且允许空集。k 可有限也可无限。有限可解仅 ∀有限F∃x_F，不假定已选有限解相容。

必须保留：ZFC；任意域 k 的离散拓扑与乘积拓扑；任意 I/J 及 A⊆I；每行有限支撑，常数给定；每个有限子系统在全积 k^I 中可解；目标是坐标像闭及有限坐标闭方程描述。

不能继承或偷加：S3 的 k 有限或 k^I 紧；S5 对解要求有限支撑；I/J 可数、统一行支撑界或全解集紧性。

阶段边界：此项 scope=stage，闭性断言为真，题面还要求具体的有限坐标闭方程描述。不能把只说投影连续当作闭性证明，也不能以原紧性证明失效认定命题为假。

论证核验：

1. 设 V=k^{(I)}，W=span{a_j}。有限可解性使 β(Σ_j λ_j a_j)=Σ_j λ_j b_j 良定义：对有限行关系选择一个对应有限子系统解并配对即可。全部组合有限。

2. 给 A⊆I，令 U_A=span{e_i:i∈A}。对 y∈k^A，定义 g_y(Σ z_i e_i)=Σ z_i y_i。若 y 来自整体解，则 g_y 与 β 在 W∩U_A 上相等。

3. 反之，交空间上的一致性使 β 与 g_y 拼成 W+U_A 上的线性泛函；在 ZFC 中补基延拓至 V，取各 e_i 值得到真实整体解且 A 坐标为 y。因此投影像恰为这些一致性方程的解集。

4. 明确地 π_A(S)=∩_{w∈W∩U_A}{y:Σ_{i∈supp w}w_i y_i=β(w)}。每个 w 有限支撑，每个评价只看有限坐标且到离散 k 连续；右端单点闭，故每个方程闭、任意交闭。

5. 空 A 时方程仅为 0=0，投影是唯一空记录；空行系统时像为整个 k^A。无限 k 不保证全解紧，但不影响上述闭像结论。

参考判断：可靠；参考用 S4 的有限关系代数延拓给必要与充分性，未把连续投影误认为自动闭映射。

实际清理差分：Remove six header score and machine-kind suffixes；Neutral public delivery instructions；Neutral S4 decision wrapper; original mathematical statements unchanged。全部 6 个阶段数学主体未变，reference 未变，contract 仅版本改变。

| 文件 | 初读 0.1.0 SHA-256 | 最终 0.1.1 绑定 SHA-256 |
|---|---|---|
| `task.md` | `6f47da8c5228f12968be11045f6cf47991fa4093e20794e7a0cbad1d4c9d4d3f` | `dea93393ad89196a1b8980f25e795c92713bc0b155e2d78b609d0ea64d9a2e3f` |
| `reference.md` | `fd7154006d160cbac4b482d98e631e60bc3d86686807b08a372652e889af9b15` | `fd7154006d160cbac4b482d98e631e60bc3d86686807b08a372652e889af9b15` |
| `contract.json` | `45d2b265345c0a7d41ce491a0843d897c3a77c44defbbbc52bebe18ee0431e96` | `6ec6c601b860f4518149c654d78ee15f571cc0850d8f2d451b6fd759f02d9d1d` |

## 使用边界

Standalone statements below are scope-checking expansions, not authorization to replace the complete group task or silently remove mandatory stages.

If executing a whole group/stage, all original required outputs remain mandatory; if executing only a separately versioned focus claim, extra stage branches must not become hidden scoring requirements.

Do not infer subclaim truth directly from stage.expected: GR002 S6 is classification; GR004 S4 includes true proof obligations and a false norm-convergence subclaim.

Initial full reading was v0.1.0. The 12 currently bound and saved files are the cleaned v0.1.1 task/contract snapshot plus byte-identical evaluator references. The archive-to-final cleanup has now been independently reviewed; all 23 stage mathematical bodies and all stage/turn contracts are unchanged.

Any later task/provenance/version update needs identity reconciliation; current report hashes bind only the inspected bytes.

最终快照位于 selection-review-b-snapshot；从已验证归档重建的初读字节位于 selection-review-b-initial-0.1.0。逐题真实 diff、纠正前报告及其散列位于 selection-review-b-reconciliation，同名 JSON 记录全部核验信息。
