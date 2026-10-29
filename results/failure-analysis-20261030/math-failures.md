# 本轮数学论证未通过项：逐题诊断

本报告只诊断原41题运行中的9份 Gemini written 未严格通过答卷，并单列旧 R005 的0.3.1补测。完整阅读各冻结题面、参考、rubric和原答卷，逐项核验关键推理后对照已有初审、二审与裁定。没有重评分、改题、改答卷、调用模型或重编译 Lean。全部结论仍为AI审核，人工审定待完成。

原29道 written：Terra 29/29，Gemini 20/29。Gemini的9项不能统称“数学错了”：5项数学主干失败、1项分类证明缺口（R008）、1项证明边界错误叠加题面歧义（旧R005）、2项服务过滤。两项 partial 都宣称完整完成，不是明确承认的诚实未完成。written答卷不要求Lean，因此本范围内没有候选Lean编译错误。

结果身份：[冻结比较](/Users/g4i/lab/math-gauge/results/full-comparison-20261030/comparison.json:1)；[packet映射](/Users/g4i/lab/math-gauge/results/full-comparison-20261030/reviews/packet-map.json:1)；[运行审计](/Users/g4i/lab/math-gauge/results/full-comparison-20261030/runtime/audit-final-20261030.json:1)。

| 题号 | 既有裁定 | 本次诊断 | 题目/评分边界 |
|---|---|---|---|
| MG-R001 | fail | 存在/唯一性和有限距离条件越界 | 未发现决定性题目缺陷 |
| MG-R004 | fail | 把稠密像当闭值域 | 未发现决定性题目缺陷 |
| MG-R005 | partial | proper定理误用，旧题值域不明确 | 旧题存在值域歧义；新版另测 |
| MG-R006 | fail | 有限商分支误作原群元素 | 未发现决定性题目缺陷 |
| MG-R008 | partial | 固定层稳定像回缩不存在 | 未发现决定性题目缺陷 |
| MG-R009 | fail | 服务过滤，无数学答卷 | 服务原因未知 |
| MG-R013 | fail | Runge条件及阈值量词交换 | 未发现决定性题目缺陷 |
| MG-R015 | fail | 服务过滤，无数学答卷 | 服务原因未知 |
| MG-P003 | fail | 缩小丢点、几何输入和对应作用缺口 | 未发现决定性题目缺陷 |

## MG-R001：递归算子闭合：从衰减界跳到原空间固定点

原响应 SHA-256：`8c48f4aae85b1b76481fdbabbe6a3e9d032ad43cf28cdce9f49e3cbf44d85d2d`。既有裁定 **fail**；本次诊断不改分。

**首个决定性步骤。** 答卷 L75：由路径矩阵乘积趋零，直接断言任意尾值截断在原 X° 内收敛到唯一、与尾族无关的极限。

**独立核验。** 单步及迭代扩展距离估计有效，但趋零的有限矩阵不能消除无限距离，尾值亦可随截断层数增长。没有 Cauchy 控制、原空间完备性和分离性，就不能从完备化措辞取得原空间点值固定解。L104 将几何收敛限制到有限 Δ(H,F*)，这是有价值的条件结论；L237–247 又把任意固定族代入有限误差界，并把零伪距离当作点值相等。题面要求每个 H 有有限 C_H，未被完成。

**可检查的见证或缺失义务。** 取一个节点一个自环，X°=(0,∞)，通常距离，另加与所有非底值距离∞的吸收元；U=D={1}，S=∅，b(1)=1，a(y)=y/2，a(⊥)=⊥，L=M=[1/2]。全部题设成立，固定值须 u=u/2，唯有0而0不在X°，故不存在。独立边界：X°=R、U=N_{≥1}、b(n)=n+1、a(y)=y/2 时，每个 F_c(n)=c·2^n 都固定，不同c间统一距离∞；即便输出空间完备且分离仍非唯一。取H(n)=n，其第k次展开2^{-k}(n+k)对F_0的统一误差仍∞。两点零伪度量加交换返回还可单独否定零距推出点值相等。

**有效贡献。** 有限终止轨道的代数组合、单步矩阵估计、Neumann 权重构造及有限距离分支上的条件几何界。

**题目与评分。** 未发现决定性的题面/评分缺陷。假全称目标是有意的边界题，合法短反例即可完成；不能把“目标为假”当出题错误。本题当前短反例很便宜，长答卷不是长链难度的证据。

**出题启发。** 下一批可保留局部衰减引理，继续要求构造不变的有限距离分支、证明完备与分离条件、区分商空间/完备化中的结论和原空间返回，并在同一依赖链中标出哪些结论需要新增前提。

定位：[task.md L41](/Users/g4i/lab/math-gauge/results/full-comparison-20261030/reviews/packets/f43405e0f988/task.md:41)；[response.md L68](/Users/g4i/lab/math-gauge/results/full-comparison-20261030/reviews/packets/f43405e0f988/response.md:68)；[response.md L100](/Users/g4i/lab/math-gauge/results/full-comparison-20261030/reviews/packets/f43405e0f988/response.md:100)；[response.md L237](/Users/g4i/lab/math-gauge/results/full-comparison-20261030/reviews/packets/f43405e0f988/response.md:237)；[reference.md L153](/Users/g4i/lab/math-gauge/results/full-comparison-20261030/reviews/packets/f43405e0f988/reference.md:153)；[既有最终裁定](/Users/g4i/lab/math-gauge/results/full-comparison-20261030/reviews/adjudication/f43405e0f988.json:1)。


## MG-R004：Hilbert 复形：约化无环被升格为闭值域

原响应 SHA-256：`a5c75ce0a46b0e00e0608497b177523c61f209f3c780ad92bbd97de2eff0bec8`。既有裁定 **fail**；本次诊断不改分。

**首个决定性步骤。** 主定理 L28–31 已把闭值域/正最小模数称为给定数据下均成立；第一处实际使用未证前提是 L62“由值域闭性”。

**独立核验。** R_j=0 只给 ker d_j=closure(im d_{j-1})，不能去掉闭包。候选其实证明了闭值域、有界链收缩及 Laplace 可逆的条件化等价，但没有证明条件在原题中成立，也没有明确反驳原强目标；结尾又无条件说所有 L_j 双侧可逆。因此不能把它解读成已经完成一个诚实的条件分类答案。

**可检查的见证或缺失义务。** 长度1复形 H_0=H_1=ℓ²(N_{≥1};C)，d_0(x)_n=x_n/n，端点微分为0。d_0有界、单射，像包含有限支撑向量而稠密，故两端约化上同调均0。若s_1d_0=I，则s_1e_n=ne_n，违反有界性。L_0=L_1=diag(1/n²)；若有有界右逆G，则Ge_n=n²e_n，亦不可能。这里约化最小模数α_0=0。

**有效贡献。** 闭值域条件下的正交分解、链收缩和 Green 算子公式；从有界收缩推出闭值域的方向。

**题目与评分。** 题面明确为有限长度，不是各层有限维，未发现决定性歧义。短反例足以完成原目标；不应要求候选必须沿作者的完整分类路线。

**出题启发。** 适合连续考 exact、reduced-exact、闭值域、谱隙、有界逆、扰动稳定的差别，每一步保留此前实际证明出的前提，避免先给谱隙再让后续题只机械计算。

定位：[task.md L1](/Users/g4i/lab/math-gauge/results/full-comparison-20261030/reviews/packets/5eba4b3d8afb/task.md:1)；[response.md L26](/Users/g4i/lab/math-gauge/results/full-comparison-20261030/reviews/packets/5eba4b3d8afb/response.md:26)；[response.md L58](/Users/g4i/lab/math-gauge/results/full-comparison-20261030/reviews/packets/5eba4b3d8afb/response.md:58)；[response.md L288](/Users/g4i/lab/math-gauge/results/full-comparison-20261030/reviews/packets/5eba4b3d8afb/response.md:288)；[既有最终裁定](/Users/g4i/lab/math-gauge/results/full-comparison-20261030/reviews/adjudication/5eba4b3d8afb.json:1)。


## MG-R005：旧0.3.0凸恢复：竞争函数值域和最大性

原响应 SHA-256：`0b4a1d50ec428f3d5bced90deee00112794590ca0f2f18f762c904c519680e3c`。既有裁定 **partial**；本次诊断不改分。

**首个决定性步骤。** L133–137 从 h 不恒为±∞跳到可应用 proper Fenchel–Moreau，并写 h=h**；候选主定理 L98 明确量化 h:E→[-∞,+∞]。

**独立核验。** 记录关系、G的构造和 proper 竞争者下的最大性都成立。缺口只在全扩展值竞争类：不恒±∞不保证在某处取有限实数。真实错误是把 proper-only 定理用于允许同时取两端无穷的函数，不是一般局部凸空间中的 Fenchel–Moreau 不成立。原题可见文字未单列 h 的值域，故这一题必须同时标记评分敏感性。

**可检查的见证或缺失义务。** E=R，f(0)=0、f(x)=+∞(x≠0)，h(0)=−∞、h(x)=+∞(x≠0)。epi_R(h)={0}×R闭凸，h≤f且不恒±∞；然而h*≡+∞，h**≡−∞，所以h=h**在x≠0失败。原最大性结论仍真，可用max(h,0)归约或直接闭上图包含来证明；这些不能由评审补入旧答卷。

**有效贡献。** 原始纤维投影关系、共轭限制关系、有限记录重构、非负下半连续凸包和 proper 竞争者下最大性。

**题目与评分。** 确认题面问题：旧题 L15 的“所有下半连续凸函数”未定义竞争者值域；若事前约定只能取R∪{+∞}，原答案已覆盖必需最大性。旧partial有真实的自扩全域主张错误，也有题目约定不充分，不能当纯能力失分。0.3.1已显式修清并另做补测，不能回填旧41题。

**出题启发。** 扩展值、零维、空集等约定必须在题面冻结前写清；难度应来自构造/依赖，而不是让评审事后决定函数类别。主任务与候选自加旁支的正确性应分列。

定位：[task.md L15](/Users/g4i/lab/math-gauge/results/full-comparison-20261030/reviews/packets/078776bdf876/task.md:15)；[response.md L96](/Users/g4i/lab/math-gauge/results/full-comparison-20261030/reviews/packets/078776bdf876/response.md:96)；[response.md L130](/Users/g4i/lab/math-gauge/results/full-comparison-20261030/reviews/packets/078776bdf876/response.md:130)；[既有最终裁定](/Users/g4i/lab/math-gauge/results/full-comparison-20261030/reviews/adjudication/078776bdf876.json:1)。


## MG-R006：逆极限提升：有限商中的分支不等于原群元素

原响应 SHA-256：`c455b2e8421a2fe546ebbd42ab8525ed7b844df721b5d8d579740d3a55257ac2`。既有裁定 **fail**；本次诊断不改分。

**首个决定性步骤。** L137 把固定层相关障碍的大小说成由固定 C_n 控制，L140 将有限商树的无穷分支直接当作原纤维 π_n^{-1}(c_n) 中的元素。

**独立核验。** 差分方程及 coker Δ_A 障碍已被候选正确写出。Snake 引理只使 A_n/α_{n,k}(A_k) 对每个固定k有限，其阶可随k增长；无限提升纤维未被证明有限或紧。König 分支至多构造完备化中的相容模类，不能保证在原 B_n 内有共同代表。结尾用这个错误满射性推出 lim¹ A=0 是同一缺口的下游，不是独立验证。

**可检查的见证或缺失义务。** A_n=2^nZ⊂B_n=Z→C_n=Z/2^nZ，α为包含、β=id、γ为约化。所有原条件成立。令c_n为3的模2^n逆元，则相容且每个有限前缀都有整数提升。若存在全局β相容b_n，则全为一个整数b；3b−1被所有2^n整除，故3b=1，矛盾。固定n的指数[A_n:α_{n,k}(A_k)]=2^{k−n}，正好揭示不存在统一有限控制。

**有效贡献。** 局域缺陷的定义、修正差分方程、非空解集作为lim A的torsor、左端/中间正合和自然性。

**题目与评分。** 原假全称目标有明确合法反例，未发现题意或评分缺陷。并非答卷不知道lim¹，而是已识别障碍后又无证消除它，适合研究依赖追踪。

**出题启发。** 多阶段题可让同一塔依次经过局部解、有限前缀、完备化解、原群解、自由度和自然性；要求说明每个存在性结论在哪个对象中，最后给精确障碍或必要充分条件。

定位：[response.md L54](/Users/g4i/lab/math-gauge/results/full-comparison-20261030/reviews/packets/2a18e0b1bfbe/response.md:54)；[response.md L118](/Users/g4i/lab/math-gauge/results/full-comparison-20261030/reviews/packets/2a18e0b1bfbe/response.md:118)；[response.md L225](/Users/g4i/lab/math-gauge/results/full-comparison-20261030/reviews/packets/2a18e0b1bfbe/response.md:225)；[reference.md L41](/Users/g4i/lab/math-gauge/results/full-comparison-20261030/reviews/packets/2a18e0b1bfbe/reference.md:41)；[既有最终裁定](/Users/g4i/lab/math-gauge/results/full-comparison-20261030/reviews/adjudication/2a18e0b1bfbe.json:1)。


## MG-R008：可表示性分类：稳定像未必在当前层为直和项

原响应 SHA-256：`08d9ff4f4188ed4c5c0cbdd7937c3e978d098160cc207ad86138a1627ba9b125`。既有裁定 **partial**；本次诊断不改分。

**首个决定性步骤。** 必要性 L116–126 先得到饱和像稳定，未完成实际像稳定的分裂核对；首个可直接证伪的必需断言是充分性 L147 对任意固定n≥n0选取 P_n→I_n 回缩。

**独立核验。** 其稳定像准则R可证明为正确，不能因不同于参考的M有限生成路线而扣分。错误发生在证明桥梁：R只给最终像稳定及稳定像间同构，不保证所选起点每个I_n都是P_n的纯子群。必要性中在已假设可表示后得到的纯性不能供充分性循环引用。L175的可数极限充分性依赖同一桥梁。答卷宣称全分类完成，因此partial不是“诚实未完成”。

**可检查的见证或缺失义务。** P_n=Z，ρ_0=×2，ρ_n=id(n≥1)。取n0=0满足R；I_0=2Z，I_n=Z(n≥1)，限制ρ_0:Z→2Z为同构，但2Z不是Z的直和项。f′:2Z→Z，f′(2)=1不能延拓到Z，因为2u(1)=1无整数解。此例只反驳固定层延拓断言，不反驳主分类或全局Θ满射。正确修复是先取足够后层m使im ρ_{n0,m}=I_n0，再用(ρ_{n0,m}|I_m)^{-1}ρ_{n0,m}构造P_m→I_m回缩；候选没有完成这一步。

**有效贡献。** 张量模型F≅M⊗−、无挠性、可数积检测有限生成、R下逆极限到稳定像的同构及Θ单射、自然变换的完整方向和恒等/复合公式。

**题目与评分。** 未发现题面或主判据缺陷；这是正确目标中的实质证明缺口。现有partial保留正确贡献是合理的，不能把评审能补出的短桥梁计作候选已交付。

**出题启发。** 本题最直接支持用户的长依赖题设想：在真分类目标中，某一步看似自然的延拓可同时破坏表示性与极限保持，其他分支仍正确。设计应记录受影响的下游节点，并允许从独立路线完成任务。

定位：[response.md L66](/Users/g4i/lab/math-gauge/results/full-comparison-20261030/reviews/packets/fee14fd21c58/response.md:66)；[response.md L110](/Users/g4i/lab/math-gauge/results/full-comparison-20261030/reviews/packets/fee14fd21c58/response.md:110)；[response.md L140](/Users/g4i/lab/math-gauge/results/full-comparison-20261030/reviews/packets/fee14fd21c58/response.md:140)；[response.md L173](/Users/g4i/lab/math-gauge/results/full-comparison-20261030/reviews/packets/fee14fd21c58/response.md:173)；[response.md L246](/Users/g4i/lab/math-gauge/results/full-comparison-20261030/reviews/packets/fee14fd21c58/response.md:246)；[既有最终裁定](/Users/g4i/lab/math-gauge/results/full-comparison-20261030/reviews/adjudication/fee14fd21c58.json:1)。


## MG-R009：群作用下降分类：过滤通知，没有数学答卷

原响应 SHA-256：`4ac7197dd8cf58f332d417035ce90e35180b008f3e1b6815602b5c615bb28f2b`。既有裁定 **fail**；本次诊断不改分。

**首个决定性步骤。** response.md L1 仅有请求被 Gemini filters 阻止的通知；不存在可定位的数学致命步骤。

**独立核验。** 运行收据为一次计划请求、一次成功终端返回，响应身份相符；返回文字自称服务过滤。未构造商层、未给稳定子判据、未说明对象/态射的等价或任意层基变换。数学有效性不能从这段通知推断。

**可检查的见证或缺失义务。** 不适用：没有模型论证。题目本身的关键数学边界是必须在所有测试对象检验稳定子，而不是只看单点；本轮过滤没有测到这项能力。

**有效贡献。** 无可评估的数学贡献。

**题目与评分。** 未从题目全文和参考中发现导致过滤的数学或安全问题。后台过滤原因未知；交付失败保留在原分母中，但不能写成“模型证明错了”或“该题太难”。

**出题启发。** 后续报告同时给交付通过率和有数学答卷子集诊断；新版本/重复运行应预注册，不能重试后覆盖原样本。下降分类是适合长链的候选题，但本次未获得其难度信号。

定位：[task.md L1](/Users/g4i/lab/math-gauge/results/full-comparison-20261030/reviews/packets/284156682c95/task.md:1)；[response.md L1](/Users/g4i/lab/math-gauge/results/full-comparison-20261030/reviews/packets/284156682c95/response.md:1)；[既有最终裁定](/Users/g4i/lab/math-gauge/results/full-comparison-20261030/reviews/adjudication/284156682c95.json:1)。

服务证据：[单次执行收据](/Users/g4i/lab/math-gauge/results/full-comparison-20261030/runtime/evidence-final/records/gemini/MG-R009/MG-R009/execution-assessment.json:1)。原文自称过滤，后台原因未知。


## MG-R013：谱恢复：带孔紧集的逼近与幂阈值交换

原响应 SHA-256：`4cb109f146238166e16dd7e2c78633ac9a76c6cf74ee4612af24f6b4e6afcf24`。既有裁定 **fail**；本次诊断不改分。

**首个决定性步骤。** 第一处决定性必需错误为L171–177：对可能带孔的K_δ宣称可用统一多项式逼近1/(λ−z)。另有独立错误L185–195：固定n后对只在n≥N_m成立的式子令m→∞。

**独立核验。** 有限秩使各T_n代数化，却不给统一的谱半径收敛速度。题设为∀p∃N_p∀n≥N_p，不允许推出∃n∀m n≥N_m。即使某个λ使Runge步骤可以修复，后一个量词交换仍足以使反证失效。先前关于预解范数的讨论未提供所缺的一致估计。

**可检查的见证或缺失义务。** 局部反例：λ=1/2、δ=1/4，圆|z−λ|=δ⊂K_δ。任意多项式h(z)=1−(λ−z)p(z)满足h(λ)=1，最大模原理禁止sup_{K_δ}|h|≤1/2。全题合法反例：E=c0(N0;C)，S为右移，N_n为输出仅保留j<n的截断右移。收缩、有限秩、强收敛成立；对p(z)=Σ_{k=0}^d a_kz^k，n>d时两算子多项式范数恰为Σ|a_k|，用有限支撑相位向量v_{d−k}=|a_k|/a_k取得下界，常数项保留I_E。每个N_n幂零故谱{0}；(I−S)x=e0强迫x恒1，不在c0，所以1∈σ(S)而不能由模型谱点逼近。

**有效贡献。** 有限秩算子代数性、最小多项式检测谱、谱映射不等式、无限维零谱点特例与有限维谱连续特例。

**题目与评分。** 未发现决定性题目缺陷；特别强的“每个多项式最终精确范数相等”已明确写出并被反例核验。比只考强收敛不保谱更有辨识力，但当前仍是单个反例即可完成的假目标。

**出题启发。** 可扩成相同模型中的多项式记录、谱半径、预解、伪谱与谱恢复连续链；每次统一化都要求写清参数依赖。无需用更多同类常识反例凑题数。

定位：[task.md L5](/Users/g4i/lab/math-gauge/results/full-comparison-20261030/reviews/packets/e91453b9092d/task.md:5)；[response.md L167](/Users/g4i/lab/math-gauge/results/full-comparison-20261030/reviews/packets/e91453b9092d/response.md:167)；[reference.md L7](/Users/g4i/lab/math-gauge/results/full-comparison-20261030/reviews/packets/e91453b9092d/reference.md:7)；[既有最终裁定](/Users/g4i/lab/math-gauge/results/full-comparison-20261030/reviews/adjudication/e91453b9092d.json:1)。


## MG-R015：可数自由模完备化：过滤通知，没有数学答卷

原响应 SHA-256：`4ac7197dd8cf58f332d417035ce90e35180b008f3e1b6815602b5c615bb28f2b`。既有裁定 **fail**；本次诊断不改分。

**首个决定性步骤。** response.md L1 与R009为同一过滤通知，无数学步骤。

**独立核验。** 运行审计确认单次已完成请求；不能把无答案解释为模型错误使用Noetherian完备化或不懂直和。当前题目明确使用实际M/t^nM的逆极限，参考给出保持A、B自由的真实中间不正合例。

**可检查的见证或缺失义务。** 非模型错误见证、仅用于核对题目合法性：A=⊕Rf_i，B=⊕Re_i，ι(f_i)=t^ie_i，C=coker ι。y_m=Σ_{i<m}t^ie_i mod t^mB相容且在q̂的核；若来自Â，则模t的有限支撑代表每个坐标常数项都必须1，矛盾。因此题目假目标有完整合法反例。

**有效贡献。** 无可评估的数学贡献。

**题目与评分。** 过滤原因未知；未发现题目缺陷，不把服务拦截计作数学推理失败。

**出题启发。** 这类题可以与R006连接为“抽象塔→来自同一模的幂塔→完成中的支持约束”，但单次过滤未提供模型能力证据；不能根据两题都过滤便推测数学主题触发机制。

定位：[task.md L1](/Users/g4i/lab/math-gauge/results/full-comparison-20261030/reviews/packets/4fd59098a33e/task.md:1)；[response.md L1](/Users/g4i/lab/math-gauge/results/full-comparison-20261030/reviews/packets/4fd59098a33e/response.md:1)；[reference.md L5](/Users/g4i/lab/math-gauge/results/full-comparison-20261030/reviews/packets/4fd59098a33e/reference.md:5)；[既有最终裁定](/Users/g4i/lab/math-gauge/results/full-comparison-20261030/reviews/adjudication/4fd59098a33e.json:1)。

服务证据：[单次执行收据](/Users/g4i/lab/math-gauge/results/full-comparison-20261030/runtime/evidence-final/records/gemini/MG-R015/MG-R015/execution-assessment.json:1)。原文自称过滤，后台原因未知。


## MG-P003：半局部层化：缩小邻域丢失指定点与未证几何输入

原响应 SHA-256：`452fa2ba71bb3f79aeb1086824173b4922b6ac29a81d40df4817b32e44857b58`。既有裁定 **fail**；本次诊断不改分。

**首个决定性步骤。** 首个可直接证伪且被后续复用的步骤为L106：由稠密V推出Σ⊂V，并说可缩小仍包含Σ的U0修正。前面的曲线构造也未交付所需精确几何输入。

**独立核验。** 泛点为零只给某个稠密开上为零，不保证它保留指定有限点；这个缺口正是半局部泛点单射所需的几何内容。L151–154又无证断言覆盖的有限对应同伦分割；命题2只处理整体Σ避开一个补集，无法推出对每个U_x的对应。L159把ξ∈F(k(X))置于一般Cor(η,U_x)的拉回之下，未证明目标支撑落入泛点或承载ξ的稠密开，因此操作未良定。末尾把普通S当半局部Hensel环的理由也无题设依据。

**可检查的见证或缺失义务。** X=A¹_k、Σ={0}、V=D(t)是稠密开但不含0；任何仍含Σ的U0缩小都不能使0进入V。此例反驳候选的拓扑推理，不反驳原同构定理。缺失的几何输入可用准确适用的MVW命题11.1、引理22.9、收缩版22.10及余终性论证承担，或直接正确引用引理22.12并核对任意域、有限点集、邻域余极限的对象。

**有效贡献。** 层化保持茎、连通分支归约、在已给合法泛点单射和像交公式前提下的最后图追。

**题目与评分。** 主目标是真且存在合法短引用解；不能强迫复现作者路线。候选只把目标冠名“Voevodsky定理”后提供错误重构，没有给可核验的独立定理应用，因此不等同于正确引用22.12。外部几何输入和题目作者部分Lean覆盖的界限见下方专项。

**出题启发。** 适合做源依赖审核/修复链：给出带精确假设的几何输入，检查收缩后仍在同一余终系统、滤过极限、分离化、图追和归纳。若允许直接引用完整终点，就测的是正确应用/核对而非独立重建全部几何；两种任务应事前分轨。

定位：[response.md L98](/Users/g4i/lab/math-gauge/results/full-comparison-20261030/reviews/packets/177e5006f00b/response.md:98)；[response.md L145](/Users/g4i/lab/math-gauge/results/full-comparison-20261030/reviews/packets/177e5006f00b/response.md:145)；[response.md L201](/Users/g4i/lab/math-gauge/results/full-comparison-20261030/reviews/packets/177e5006f00b/response.md:201)；[reference.md L7](/Users/g4i/lab/math-gauge/results/full-comparison-20261030/reviews/packets/177e5006f00b/reference.md:7)；[reference.md L102](/Users/g4i/lab/math-gauge/results/full-comparison-20261030/reviews/packets/177e5006f00b/reference.md:102)；[既有最终裁定](/Users/g4i/lab/math-gauge/results/full-comparison-20261030/reviews/adjudication/177e5006f00b.json:1)。


## R005 0.3.1补测单列，不回填旧结果

新版响应 SHA-256：`5956fe0c618fd6a5746acb54d0b92f19da78d1cb944deb9d8a7717b6c07cdf39`；既有裁定 **pass**。两模型在这项单独补测均通过；这不是重写原41题成绩。

明确h:E→[-∞,+∞]，以下半连续/凸的实高度上图约定允许−∞；原旧题0.3.0范围歧义被公开澄清。

新版答卷L140–171通过闭上图定义G0并直接证明全竞争域最大性，补上旧答卷实质缺口。记录关系正确。L240–251已独立说明凸集强弱闭包相同、有限观测柱状邻域构成弱拓扑基，结合先前实高度投影和有限维正规化，支持从记录恢复闭上图；这是已有独立路线，不需替候选修改错误分离式。

L199 λ=0支路写φ_k=φ_0+kψ，方向错误。取f为[0,∞)的指示成本，ψ=id，φ0=0，x1<0可被ψ分离，但任意k>0的f*(kψ)=∞，不能取得所需仿射下界。

pass表示必需义务有有效路线，不表示整篇无错误。审查允许有限投影上图与inf记录闭包相同的定义性ε步骤省略；该尺度应事前记录。不能把新版pass倒算为旧版pass，亦不能凭一次澄清补测声称旧差异全部由措辞造成。

定位：[task.md L15](/Users/g4i/lab/math-gauge/results/r005-clarified-v0.3.1-20261030/reviews/packets/1d676bc005fd/task.md:15)；[response.md L140](/Users/g4i/lab/math-gauge/results/r005-clarified-v0.3.1-20261030/reviews/packets/1d676bc005fd/response.md:140)；[response.md L194](/Users/g4i/lab/math-gauge/results/r005-clarified-v0.3.1-20261030/reviews/packets/1d676bc005fd/response.md:194)；[response.md L240](/Users/g4i/lab/math-gauge/results/r005-clarified-v0.3.1-20261030/reviews/packets/1d676bc005fd/response.md:240)；[补测裁定](/Users/g4i/lab/math-gauge/results/r005-clarified-v0.3.1-20261030/reviews/adjudication/1d676bc005fd.json:1)。


## P003：外部几何输入、候选证明与作者 Lean 三层证据

参考论证的完整展开范围是“精确几何输入之后的半局部化、分离化、收缩余终性、滤过余极限及图追”，不是从基础重建动机几何。G1=MVW命题11.1（半局部泛点单射），G2=22.9（分离商仍有转移且同伦不变），G3=修正后的22.10（允许U0收缩但仍与V覆盖的正合性）；任意域和有限非闭点都必须保持。直接引用适用的22.12并核对对象本来就是合法短解。

作者 Lean 冻结覆盖账本明确为“实质辅助模块已形式化；完整题面尚未形式化”。已覆盖：有限素理想补集、半局部化及闭点识别；分离闭点的邻域系统、收缩余终性；真实阿贝尔群DirectLimit正合性辅助结果；小位点真实层化箭头、单点基例；最后的阿贝尔群交换图双射论证。尚缺：G1半局部泛点单射；G2分离商的转移及同伦不变性；G3含有限底域的收缩正合性；完整有限对应/转移结构在固定依赖中的集成；光滑大位点与小Zariski位点比较；所有自然箭头与闭点数归纳组装为任意域/任意有限点集的完整典范同构。当前并无完整量化题面全部对象的Lean同构定理。

Written题不要求候选提交Lean；允许精确引用已知主定理或给独立有效证明。作者辅助Lean通过不能替代候选缺失的几何输入，也不能说原主命题已完全形式化。
本次独立阅读冻结reference/source-notes中的精确G1–G3与页码/文件身份；未重新下载整本第三方文献，未重放作者Lean构建。反例与候选推理缺口在本次直接核验。

证据：[冻结Lean覆盖账本](/Users/g4i/lab/math-gauge/results/full-comparison-20261030/runtime/evidence-final/frozen-suites/2/MG-P003/formal/COVERAGE.md:1)；[冻结来源与抽取边界](/Users/g4i/lab/math-gauge/results/full-comparison-20261030/runtime/evidence-final/frozen-suites/2/MG-P003/source-notes.md:1)。


## 对10–20个相互依赖证明的判断

1. 九个written未严格通过中，五个fail是数学主干错误，R008是正确主判据中的关键证明缺口，旧R005是边界证明错误叠加题面竞争域歧义，R009/R015是服务过滤。没有一份可归为明确承认未完成的诚实残缺答卷。

2. 四个假目标R001/R004/R006/R013都可被短反例完成；把参考证明或题面加长到20个断言，不会自动增加有效难度。应改为已冻结的一组必须共同交付的真分类/构造义务，或明确的查错、最小修复、下游重建任务。

3. R008已经提供长依赖测验的实证候选：同一错误回缩跨表示性和极限保持传播，正确自然变换分支仍应单独保留。P003展示失效的几何输入、邻域收缩条件和未定义对应作用如何传播至最终同构。

4. 建议每个长任务记录依赖节点的声明、实际使用的前提、局部证据、首次致命错误、受影响下游，以及是否存在独立有效路线。给出整体严格通过与节点完成/关键桥梁通过，避免一个早期错误让后续十题全被视作同一种独立失败。

5. 允许标准定理引用时核对实际假设；若专门考10–20步论证，先冻结可调用库和待建立目标，不能交卷后禁止正确短解。合规引用完整终点的测验和从中间几何输入重建的测验应分开。

6. 旧R005说明题面约定明确性是正式题质量的一部分；新版pass仍保留错误旁支说明“主目标完成”和“全文每个断言正确”是两种不同指标。两者应预先说明并分别报告。

7. 本报告不覆盖F系列编译错误，不新增评分，不推断模型总体能力；全部模型比较仍为冻结单次样本及AI暂定审核，相关题族也不是独立统计样本。


全部材料、审核记录和重点行号的完整SHA-256绑定保存在同目录 `math-failures.json`。上述反例是本次诊断见证，不是替换模型答卷。
