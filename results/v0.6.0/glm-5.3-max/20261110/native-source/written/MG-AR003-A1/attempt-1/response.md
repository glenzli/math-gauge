# 审阅报告：《探针映射空间与连续性层级》

**审阅对象**：`original-task.md`（S1–S6 全部阶段）与 `original-answer.md`（待审答卷）。

## 一、总体结论

| 阶段 | 最终判断/构造 | 论证完整性 |
|---|---|---|
| S1 | 正确 | 完整 |
| S2 | 正确 | 基本完整（一处不成立的中间断言，未被证明使用，不影响结论） |
| S3 | 正确（$M=k(C_{co}(kX,kY))$ 是标准的紧生成内 Hom 构造） | **不完整**：验证链第 4 步属**错误援引**；核心事实（k 化求值连续 / CGHaus 笛卡儿闭）只断言未证 |
| S4 | 正确（否 / 是） | 完整（一处可忽略的表述不严） |
| S5 | 正确（否） | 完整 |
| S6 | 正确 | 6.2、6.3 完整；6.1 依赖 S3 的同一未证事实 |

**裁定**：答卷的**全部最终结论与构造均正确**（逐项核查依据见 §二）；但作为证明文书，S3 存在一处实质性缺口：S3.1 第 4 步把 S1 的局部紧性条件错置到参数空间 $S$ 上（条件实际须加在 $kX$ 上，而 $kX$ 一般不局部紧），并且 S3.2、S3.3、S6.1 反复依赖的“CGHaus 的典范求值连续 / 笛卡儿闭性”从未被证明。该缺口**可以完全修复**（§三给出仅用卷内工具的证明），修复后全卷成立。按题面“援引结果须说明条件为何适用、未完成内容须标记”的要求，这是答卷的形式与实质双重不足之处。

## 二、逐阶段核查

### S1 —— 正确、完整

1. **ev 连续性**：各步核对无误。“存在开 $V\ni x_0$ 使 $\bar V$ 紧且 $\bar V\subseteq f_0^{-1}(W)$”是局部紧 Hausdorff 空间的标准事实（LCH $\Rightarrow$ 正则，可经单点紧化的正则性得出），引用合法。$[K,W]$ 是子基开集且含 $f_0$；$V\subseteq\bar V=K$ 给出 $[K,W]\times V\subseteq ev^{-1}(W)$。✓
2. **柯里化**：$\Phi$ 经 $g\times\mathrm{id}$ 与 $ev$ 的复合；$\Psi$ 经管状引理——注意 $\Psi$ 方向的论证**只用到 $K$ 紧**，与 $X$ 的局部紧性无关（此观察对 §三的修复关键）。互逆性在底集层面显然。✓
3. **自然性**：对 $Z$（拉回）、$Y$（推前）、$X$（预复合，正确地限制在 LCH 之间）三个变量的逐点等式全部成立。✓

### S2 —— 基本正确；一处不成立的中间断言（不影响结论）

**2.1 ✓**。单调方向显然。反向的 $\beta D$ 论证逐项核验：$\beta D$ 是 $\mathcal P(D)$ 的 Stone 谱，具闭开基，故紧 Hausdorff 全不连通（紧 Hausdorff 时全不连通 $\Leftrightarrow$ 零维）；离散源上恒等映射经 Stone-Čech 泛性质延拓为 $\pi:\beta D\to K$，$\pi(D)=|K|$ 故满射；紧 $\to$ Hausdorff 的连续满射是闭映射，故为商映射；于是 $p^{-1}(A)=\pi^{-1}(f^{-1}(A))$ 闭 $\Rightarrow$ $f^{-1}(A)$ 闭（商判别）。**小遗漏**：$\beta D\in\mathrm{Prof}_U$ 的 U-小性未验证——它为真：$D\in U\Rightarrow\mathcal P(\mathcal P(D))\in U$，而 $\beta D\subseteq\mathcal P(\mathcal P(D))$，$U$ 对子集封闭。

**2.2 ✓**。点态表示（用 $*\in\mathrm{Prof}_U$ 与 $i_s:*\to S$ 的自然性推出 $\alpha_S(f)=g\circ f$）正确；$C(S,Y)=C(S,kY)$（$S$ 紧 Hausdorff，按 $k$ 拓扑定义直接得出）正确；把探针类缩到 profinite（引用第 1 小节）后再用终拓扑泛性质（$h:kX\to W$ 连续 $\Leftrightarrow$ 对一切结构探针 $p$，$h\circ p$ 连续）正确——所需事实“$\tau_{kX}$ 恰是诸探针的终拓扑”成立（满足条件的 $O$ 全体本身是拓扑，且是最细者）。双向互逆 ✓。

**2.3 结论与两个方向的论证正确**，但含一处**不成立的断言**（问题 3，见 §四）：“连续映射 $f:X\to Y$ 诱导的自然变换对应于集合 $C(X,kY)$”。诱导者实际对应（作为函数集）$C(X,Y)\cap C(kX,kY)$，而 $C(X,kY)$ 只是它的真子集。反例：取 $X=Y=Z$ 为任一非紧生成 Hausdorff 空间，$f=\mathrm{id}_Z$：$\mathrm{id}\in C(X,Y)$，且 $\mathrm{id}\in C(kX,kY)$（$kZ\to kZ$ 恒等连续），但 $\mathrm{id}\notin C(X,kY)$（否则 $\tau_{kZ}\subseteq\tau_Z$，与 $Z$ 非紧生成矛盾）。**所幸该认定未被证明实际使用**：充分性（$kX=X$ 时 $C(kX,kY)=C(X,kY)\subseteq C(X,Y)$）直接成立；必要性取 $Y=kX$，从原始假设（该自然变换由原拓扑连续映射诱导、且 NT 由底层函数决定）直接得出 $\mathrm{id}:X\to kX$ 连续 $\Rightarrow\tau_{kX}\subseteq\tau_X$。故结论不受影响。另：幂等性 $k(kX)=kX$ 被使用而未证（一行可证：对紧 Hausdorff $K$，$C(K,kX)=C(K,X)$，故二者探针相同）；此事实在 S3、S6 多处隐性使用。

### S3 —— 构造正确；核心验证有实质缺口

**已核为正确的部分**：
- 底集 $C(kX,kY)\cong\mathrm{Nat}(h_X,h_Y)$（由 S2）与拓扑 $k(C_{co}(kX,kY))$ 的选定正确；Hausdorff 性（以单点紧集 $\{x\}$ 的子基 $[\{x\},W_f],[\{x\},W_g]$ 分离 $f\ne g$；加细保持 Hausdorff）✓；$M$ 紧生成 ✓。
- 链条第 1 步（$h_S\times h_X\cong h_{S\times X}$，自然于 $T$；经函子同构搬运后用 S2 于 $(S\times X,Y)$）✓。
- 第 2 步 $k(S\times X)=k(S\times kX)$：探针逐分量重合（$K$ 紧 Hausdorff 时 $C(K,X)=C(K,kX)$）✓。
- 第 3 步 Cohen 定理（LCH $\times$ $k$ 空间是 $k$ 空间）为**真**且条件说明到位（$S$ 紧 Hausdorff $\Rightarrow$ LCH；$kX$ 是 $k$ 空间）。为可核查起见给出梗概：$k$ 空间 $Y$ 是其诸探针不交并的商；$X$ 为 LCH 时 $X\times-$ 保持商映射（Whitehead 定理）；故 $X\times Y$ 是 $\coprod(X\times K_i)$ 的商，各 $X\times K_i$ 是 LCH 因而是 $k$ 空间，不交并是 $k$ 空间，且（Hausdorff 目标的）商保持 $k$ 空间。∎
- 第 5 步 $C(S,C_{co}(kX,kY))=C(S,M)$（$S$ 紧 Hausdorff：$k$ 空间域上映入 $V$ 连续 $\Rightarrow$ 映入 $k(V)$ 连续）✓。

**第 4 步：错误援引（全卷最主要的缺口）**——详见 §三。

**S3.2（ev 的构造）**：$ev_T$ 的定义与 $T$-自然性逐点核对无误 ✓；但连续性被归约到“CGHaus 典范求值 $M\times_k kX\to kY$ 连续”，此即未证的核心事实。实际上此处存在**不需要**笛卡儿闭性的直接证明（§三·推论 2），说明缺口并非必要，只是答卷未给。

**S3.3（$Z$-伴随）**：链条 $\mathrm{Nat}(h_Z,h_M)\cong C(kZ,M)$、$\mathrm{Nat}(h_Z\times h_X,h_Y)\cong C(kZ\times_k kX,kY)$ 均正确；但最后一环引用“CGHaus 笛卡儿闭”——未证，也未按题面要求说明条件（所涉对象 $kZ,kX,kY,M$ 均为紧生成 Hausdorff、内 Hom 恰为 $k(C_{co}(kX,kY))$）；且“恰由 $\alpha\mapsto ev\circ(\alpha\times I)$ 实现”未验证（它为真：若 $\alpha\leftrightarrow g\in C(kZ,M)$，则在底层函数上算得 $ev\circ(\alpha\times I)$ 对应 $(z,x)\mapsto g(z)(x)$，恰为 CG 伴随的展平）。步骤 2 的 $k(Z\times X)=kZ\times_k kX$ 未论证（与第 2 步同法，对任意 $Z$ 成立）。

**自然性**：$C(S,M)\cong H_{X,Y}(S)$ 在 $S$ 上的自然性、S2 同构在 $X,Y$ 上的自然性、$M(u,Y)/M(X,v)$ 的连续性（$(−\circ k(u))^{-1}([K,W])=[k(u)(K),W]$；$k$ 化的函子性）——均为真、均为一行验证，但答卷以断言代替。ev 与 $M(u,Y),M(X,v)$ 的相容性以逐点等式给出，正确（NT 由底层函数决定）。✓（思路对，细节欠）

### S4 —— 正确、完整

**4.1 反例核验通过**：$\mathbb Q$ 第一可数 Hausdorff ✓；$\mathbb Q$ 的紧子集在 $\mathbb R$ 中紧、闭、含于 $\mathbb Q$ 故无内点（若 $\mathrm{int}_{\mathbb Q}K\ne\emptyset$，取 $\mathbb Q\cap(a,b)\subseteq K$，则 $[a,b]=\overline{\mathbb Q\cap(a,b)}\subseteq K$，与 $K\subseteq\mathbb Q$ 无 $\mathbb R$-内点矛盾）✓；故 $V\setminus K\ne\emptyset$；$K$ 闭且 $q\notin K\Rightarrow\delta=\mathrm{dist}(q,K)>0$ ✓；$f(x)=2\max(0,1-|x-q|/\delta)$ 连续、$f|_K\equiv0$、$f(q)=2$ ✓；得 $(f,q)\in U\times V$ 而 $ev(f,q)=2\notin(-1,1)$，矛盾 ✓。**表述不严（问题 5）**：紧开拓扑基本开集是子基的**有限交**，答卷直接写成单个 $[K,(-\epsilon,\epsilon)]$。标准约化可修复：设 $0\in U\supseteq\bigcap_{i\le n}[K_i,W_i]$（各 $W_i\ni0$ 开），取 $K=\bigcup K_i$ 与 $\epsilon>0$ 使 $(-\epsilon,\epsilon)\subseteq\bigcap W_i$，则 $0\in[K,(-\epsilon,\epsilon)]\subseteq U$，以其替代 $U$ 即可。不影响反例有效性。

**4.2 ✓**：这是标准的“第一可数 $\Rightarrow$ 序列式 $\Rightarrow$ $k$ 空间”论证。递降可数局部基选出 $x_n\to x_0$ ✓；$K=\{x_n\}\cup\{x_0\}$ 紧（含 $x_0$ 的开集含几乎所有 $x_n$）✓；$K$ 紧 Hausdorff 子空间的含入本身是探针，故 $A$ $k$-闭 $\Rightarrow A\cap K$ 在 $K$ 中闭（此方向由题面的探针定义**直接**给出，无须“探针版 $\Leftrightarrow$ 紧子集版”等价性）✓；闭集对序列极限封闭在任意空间成立 $\Rightarrow x_0\in A$，矛盾 ✓。与 4.1 无矛盾（S1 需要的是局部紧性而非 $k$ 性）。

### S5 —— 正确、完整

一般机制核验：$C(S,kZ)=C(S,Z)$（$S$ 紧 Hausdorff）$\Rightarrow h_f(S)$ 为恒等双射、自然 ✓；$f$ 连续双射而 $f^{-1}=\mathrm{id}:Z\to kZ$ 不连续 $\Rightarrow$ 非同胚 ✓。

超滤子空间逐项核验：(i) Hausdorff：自由超滤不含有限集（否则含单点而为主超滤），故 $\mathbb N\setminus\{n\}\in\mathcal U$（余有限）✓；两类基元相交仍为基元 ✓。(ii) 紧集必有限：$p\notin K$ 时 $K$ 离散紧故有限 ✓；$p\in K$ 且 $K\cap\mathbb N$ 无限时，分拆为无穷 $A_1\sqcup A_2$，因 $A_1\cap A_2=\emptyset$ **至多一个**属于 $\mathcal U$，可设 $A_1\notin\mathcal U$，则 $\mathbb N\setminus A_1\in\mathcal U$，$W=(\mathbb N\setminus A_1)\cup\{p\}$ 开、含 $p$、不交 $A_1$，$\{W\}\cup\{\{n\}:n\in A_1\}$ 是无有限子覆盖的开覆盖 ✓（答卷“恰有一个集合不属于 $\mathcal U$”措辞不准，但 WLOG 论证有效）。(iii) 一切子集 $k$-开：任一探针 $p:P\to Z$ 的像有限，$A\cap p(P)$ 有限故在 Hausdorff 的 $Z$ 中闭，$p^{-1}(A)$ 闭、$p^{-1}(Z\setminus A)$ 开 $\Rightarrow kZ$ 离散 ✓。(iv) $\{p\}$ 非开（$\emptyset\notin\mathcal U$）$\Rightarrow Z$ 非离散、非紧生成 ✓。**小遗漏**：$Z$ 的 U-小性（取 $p:=\mathbb N$ 即 $Z=\mathbb N\cup\{\mathbb N\}\in U$、$\mathcal U\in\mathcal P(\mathcal P(\mathbb N))\in U$）与自由超滤子的存在性（ZFC 中由选择公理/超滤引理给出）未置评；均可满足。

### S6 —— 6.2、6.3 正确；6.1 依赖 S3 的同一未证事实

**6.1**：在“CGHaus 笛卡儿闭（$k$ 积、内 Hom $=k\circ C_{co}$、求值连续）”前提下，构造与两律的论证有效：复合求值链连续 ✓；伴随转置得 $\circ$ ✓；结合律、单位律以逐点等式验证且“逐点相等 $\Rightarrow$ 态射相等”成立（态射即连续映射）✓；$j_X$ 连续平凡 ✓。$\times_k$ 的结合性同构为真（两侧都等于 $k(A\times B\times C)$，探针逐分量重合）；“$\circ$ 的底集行为是通常复合”为真（由伴随刻画 $ev\circ(\circ\times\mathrm{id})=$ 复合求值，逐点展开即得）但未验证。**唯一问题是前提本身未证**（同 S3）。

**6.2 ✓**：充要条件“$k(f):kX\to kY$ 是同胚”正确。必要性：$h_f$ 是函子范畴中的同构 $\Rightarrow$ 有逆 NT $\alpha\leftrightarrow g\in C(kY,kX)$（S2）；在“对应与复合相容”之下互逆给出 $g\circ k(f)=\mathrm{id}$、$k(f)\circ g=\mathrm{id}$。充分性同理。两处隐性使用未证/未示的一行事实：$f:X\to Y$ 连续 $\Rightarrow f\in C(kX,kY)$（终拓扑泛性质）；S2 对应对复合的兼容性（$(\alpha\circ\beta)_S(u)=g_\alpha\circ g_\beta\circ u$）。

**6.3 ✓**：由 6.2 与 S4.2（$kX=X,\ kY=Y$）立得 $f$ 本身是同胚。正确。

## 三、主要缺口：S3.1 第 4 步的定位、为何错、及修复

**答卷断言**：由 S1 的指数律（“由于 $S$ 局部紧 Hausdorff，置于紧开拓扑第一变量”）得 $C(S\times kX,\,kY)\cong C(S,\,C_{co}(kX,kY))$。

**为何该援引不成立**：S1 的定律是 $C(Z,C_{co}(X,Y))\cong C(Z\times X,Y)$，其条件是**函数空间的源 $X$** 局部紧 Hausdorff——在 S1 的证明中局部紧性恰好只用于 $ev$ 的连续性（即 $\Phi$ 方向；$\Psi$ 方向的管状引理论证对任意源成立），且 $ev$ 连续与该定律（对一切 $Z$）等价（取 $Z=C_{co}(X,Y),\,g=\mathrm{id}$）。第 4 步中源的角色由 $kX$ 扮演，故所需条件是 **$kX$ 局部紧**。$S$ 的局部紧只能给出另一侧的柯里化 $C(kX,C_{co}(S,kY))\cong C(kX\times S,kY)$——函数空间不同，得不出所写的双射；无论按哪种读法，“$S$ 局部紧”都不能证此步。

**该条件一般不满足，且未 $k$ 化的版本确实失败**：取 $X=\mathbb Q$。由答卷自己的 S4.2（经核验正确），$k\mathbb Q=\mathbb Q$，而 $\mathbb Q$ 非局部紧（S4.1 已证其紧子集无内点）。更进一步，取 $X=\mathbb Q,\,Y=\mathbb R,\,Z=C_{co}(\mathbb Q,\mathbb R)$，S4.1 的反例恰说明 $ev:C_{co}(\mathbb Q,\mathbb R)\times\mathbb Q\to\mathbb R$ 不连续，即未经 $k$ 化的指数律在此**为假**。可见第 4 步的真值实质依赖“$S$ 是 profinite”与“$k$ 化”，绝非 S1 的直接推论；这也恰是题面“各阶段附加条件只在指定范围内生效、援引须说明条件适用性”所针对的错误类型（对比：答卷对 Cohen 定理的条件说明是到位的）。

**该等式本身为真，且可用卷内工具补证**。记 $B=kY$。

- **$(\Psi)$** $F\in C(S\times kX,B)\mapsto\big(s\mapsto F(s,-)\big)\in C(S,C_{co}(kX,B))$：对子基 $[K,W]$ 的原像 $\{s:\{s\}\times K\subseteq F^{-1}(W)\}$ 由管状引理开。不需要任何条件。∎
- **$(\Phi)$（困难方向）** 设 $g:S\to C_{co}(kX,B)$ 连续，$F(s,x)=g(s)(x)$，证 $F:S\times kX\to B$ 连续：
  1. 由第 3 步（Cohen），$S\times kX$ 是 $k$ 空间，即 $S\times kX=k(S\times kX)$ 是其全部探针的终拓扑，故 $F$ 连续 $\Leftrightarrow$ 对每个探针 $q=(q_1,q_2):K\to S\times kX$，$F\circ q:K\to B$ 连续。
  2. 令 $A=q_2(K)\subseteq kX$：$kX$ Hausdorff，故 $A$ 紧 Hausdorff，从而**局部紧**。限制映射 $r:C_{co}(kX,B)\to C_{co}(A,B)$ 连续：$r^{-1}([L,W])=[L,W]$，而 $L\subseteq A$ 在 $kX$ 中仍紧。
  3. 由 **S1 施于 $A$**（条件成立），$ev_A:C_{co}(A,B)\times A\to B$ 连续；逐点验证 $F\circ q=ev_A\circ(r\circ g\circ q_1,\ q_2)$（因 $q_2(k)\in A$）。故 $F\circ q$ 连续。∎

**推论 1（CG 求值连续，即 S3.2/S3.3/S6.1 的前提）**：$ev:M\times_k kX=k(C_{co}(kX,kY)\times kX)\to kY$ 连续——对任一探针 $p=(p_1,p_2):K\to C_{co}(kX,kY)\times kX$，同样的 $A=p_2(K)$ 与 $r$ 给出 $ev\circ p=ev_A\circ(r\circ p_1,p_2)$ 连续。

**推论 2（S3.2 的更省证明）**：对 $T\in\mathrm{Prof}_U$、$\varphi:T\to M$、$\psi:T\to X$ 连续（$\psi$ 自动连续到 $kX$），取 $A=\psi(T)$，则 $t\mapsto\varphi(t)(\psi(t))=(\mathrm{id}:kY\to Y)\circ ev_A\circ(r\circ\varphi,\psi)(t)$ 连续。

修复只用了：管状引理（S1 已有）、S1 施于紧 Hausdorff 子集、Cohen（答卷已引）、终拓扑泛性质（S2 已有）。**故缺口是局部的、可修复的，且不改变任何构造或结论**；另一修复方式是把第 4 步改为正确引用 CGHaus 的伴随（此时须按题面要求说明该定理的条件在此适用）。

## 四、问题清单汇总

| # | 位置 | 问题 | 性质 | 影响 |
|---|---|---|---|---|
| 1 | S3.1 第 4 步 | 误引 S1：局部紧条件错置于 $S$；$kX$ 一般非局部紧（$X=\mathbb Q$ 即反例），且未 $k$ 化版本恰被 S4.1 否定 | **错误援引（实质）** | 该步失去论证；可按 §三修复 |
| 2 | S3.2/3.3、S6.1 | “CGHaus 求值连续 / 笛卡儿闭”只断言未证，未说明条件适用性 | 实质缺口（可视为对标准定理的不当引用） | 相应结论未获证；可按 §三修复 |
| 3 | S2.3 | “诱导 NT 对应 $C(X,kY)$”不成立（应为 $C(X,Y)\cap C(kX,kY)$；反例 $X=Y=$ 非紧生成 $Z$，$f=\mathrm{id}$） | 不准确断言 | 无（两方向论证未用到它） |
| 4 | S2/S3/S6 | $k$ 的幂等性、S2 对应的复合兼容性、同构在各变量的自然性、$M(u,Y)/M(X,v)$ 连续性、$\times_k$ 结合性、"$\circ$" 的底集行为——均为真但被断言 | 完整性瑕疵 | 无（皆一行可证） |
| 5 | S4.1 | “基开邻域形如 $[K,(-\epsilon,\epsilon)]$”（实为有限交，需标准约化） | 表述不严 | 无 |
| 6 | S5 | 分拆处措辞（应为“至多一个属于 $\mathcal U$”）；U-小性、选择公理未置评 | 表述/完备性 | 无 |
| 7 | S2.1、S3 | $\beta D$、$M(X,Y)$、超滤子空间等的 U-小性未核验（均为真） | 完备性 | 无 |

## 五、最终裁定

1. **正确性（结论层面）**：S1–S6 的全部判断与构造**正确**——S1 的定律、S2 的两条定理与刻画、S3 的 $M=k(C_{co}(kX,kY))$、S4 的“否/是”、S5 的“否”（机制与超滤子反例均核验通过）、S6 的充要条件与“可升级”，均经逐项核查成立。
2. **完整性（论证层面）**：S1、S4、S5 完整；S2 基本完整（问题 3 不影响结论）；**S3.1 第 4 步为明确的错误援引**，且 S3.2、S3.3、S6.1 依赖同一未证核心事实。若审阅标准允许把“CGHaus（$k$ 积、内 Hom $=k\circ C_{co}$）笛卡儿闭”当作黑箱标准定理，则硬错误仅为第 4 步的误引（局部性错误）；若要求自足证明，则 S3 与 S6.1 不完整。
3. **可修复性**：缺口可按 §三完全补上（仅用卷内已有工具），修复后全卷构造与结论不变且全部成立。答卷未按题面要求把未完成内容显式标记，是形式上的不足。