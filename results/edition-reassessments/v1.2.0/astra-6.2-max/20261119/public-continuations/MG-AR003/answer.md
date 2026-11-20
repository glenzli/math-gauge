**原答卷覆盖了 S1–S6，六个阶段的最终结论均成立，但证明按原文尚不完全正确。** 三处需要修正的推理是 S2.3 对原连续映射的识别、S3.1 第 4 步对指数律的引用，以及 S5.2 关于超滤子的“恰有一个”断言。三处均可局部修正，S3 的映射空间和 S4、S5 的反例都有效。[完整独立审阅稿（Markdown）](/private/tmp/math-gauge-neutral-revisions-gpt-20261120/engineering/sessions/astra-6.2-max--MG-AR003/output/review.md)

### S1　求值、柯里化及自然性正确

局部紧 Hausdorff 性保证可取 \(x_0\in V\subseteq K=\overline V\subseteq f_0^{-1}(W)\)，其中 \(V\) 开、\(K\) 紧。因此 \([K,W]\times V\) 是求值落在 \(W\) 中的乘积邻域。反方向，对连续 \(F:Z\times X\to Y\)，由 \(K\) 紧和管道引理，满足 \(F(\{z\}\times K)\subseteq W\) 的 \(z\) 构成开集。这给出了柯里化所需的连续性。

两个方向逐点互逆。由 \(j:X'\to X\) 和 \(v:Y\to Y'\) 所定的预、后复合映射，对紧开子基的原像分别为 \([j(K'),W]\) 和 \([K,v^{-1}(W')]\)，均为开集。答卷在 S1 范围内对三个变量所写的自然性等式成立。

### S2　前两小节正确，第三小节把原连续映射的像写小了

对紧 Hausdorff 空间 \(K\)，将其底集离散化为 \(D\)。离散空间的 \(\beta D\) 可用 \(D\) 上的全体超滤子实现，其底集包含于 \(\mathcal P(\mathcal P(D))\)，故可取为 \(U\)-小。它紧 Hausdorff 且有闭开基。底集恒等映射 \(D\to K\) 延拓为连续满射 \(\beta D\to K\)，由紧性和 Hausdorff 性，这是商映射。因此 profinite 探针确实能检验每个紧 Hausdorff 探针所检验的开性。

沿点 \(*\to S\) 的自然性强制 \(\alpha_S(p)=g\circ p\)，其中 \(g\) 是 \(\alpha_*\) 给出的底集函数。结合 \(kX\) 的终拓扑以及对紧 Hausdorff 源 \(L\) 成立的 \(C(L,Y)=C(L,kY)\)，可得保持恒等与复合的双射
\[
\operatorname{Nat}(h_X,h_Y)\cong C(kX,kY).
\]

在这个双射下，原连续映射的像是
\[
\{k(f)\mid f\in C(X,Y)\}\subseteq C(kX,kY).
\]
S2.3 写成的 \(C(X,kY)\) 可以严格更小。取 S5 的空间 \(Z\)，令 \(X=Y=Z\)。恒等映射 \(Z\to Z\) 连续并诱导恒等自然变换，但同一底集函数 \(Z\to kZ\) 不连续。

原题的充要条件仍成立。若 \(X=kX\)，将任意 \(g:kX\to kY\) 与 \(kY\to Y\) 复合即可。反之，取允许的 \(U\)-小 Hausdorff 目标 \(Y=kX\)。由 \(k(kX)=kX\)，可考察 \(\mathrm{id}_{kX}\) 对应的自然变换。若它由原连续映射诱导，单点分量就迫使该映射为 \(\mathrm{id}:X\to kX\)。这给出 \(\tau_{kX}\subseteq\tau_X\)，从而 \(X=kX\)。

### S3　映射空间正确，第 4 步用错了局部紧变量

\(M(X,Y)=kC_{co}(kX,kY)\) 是合法的 \(U\)-小紧生成 Hausdorff 空间。其底集是 \(U\) 内函数集的子集，不同函数可用某个单点紧集上的取值分离。

S3.1 第 4 步从连续族 \(a:S\to C_{co}(kX,kY)\) 推出 \((s,x)\mapsto a(s)(x)\) 在通常积上连续。直接引用 S1 需要函数的定义域 \(kX\) 局部紧。已知的是参数 \(S\) 局部紧，利用这一条件交换积因子，S1 给出的函数空间是 \(C(kX,C_{co}(S,kY))\)。另一方向，即从联合连续推出函数族连续，仍可用管道引理。

答卷在 S3.2 引用的**紧生成 Hausdorff 空间指数律**足以补上这一步。其适用对象 \(S,kX,kY\) 均紧生成且 Hausdorff，故
\[
C(S,C_{co}(kX,kY))
=C(S,M)
\cong C(S\times_k kX,kY)
=C(S\times kX,kY).
\]
第一个等号用到紧源 \(S\) 的映射自动提升到目标的 \(k\) 化。最后一个等号用到局部紧 Hausdorff 空间 \(S\) 与紧生成空间 \(kX\) 的通常积仍紧生成。因此原文所写的双射本身成立。

对任意 Hausdorff 参数 \(Z\)，紧探针到积的连续性可按坐标检验，故 \(k(Z\times X)=kZ\times_k kX\)。由 \(h_{Z\times X}\cong h_Z\times h_X\)、S2 和上述指数律，得到
\[
\operatorname{Nat}(h_Z,h_M)
\cong C(kZ,M)
\cong C(kZ\times_k kX,kY)
\cong \operatorname{Nat}(h_Z\times h_X,h_Y).
\]
这个对应将 \(a\) 送到 \((z,x)\mapsto a(z)(x)\)，正是题给的 \(\alpha\mapsto ev\circ(\alpha\times I)\)。取 profinite 的 \(Z=S\) 即得所需的 \(C(S,M)\cong H_{X,Y}(S)\)。

求值分量也可直接检验。对探针 \((\phi,\psi)\)，像 \(L=\psi(T)\subseteq kX\) 紧 Hausdorff。把 \(\phi(t)\) 限制到 \(L\) 是紧开函数空间之间的连续操作，在 \(L\) 上应用 S1 即知 \(t\mapsto\phi(t)(\psi(t))\) 连续。该式与参数预复合交换。对连续的 \(u:X'\to X\)、\(v:Y\to Y'\)，预、后复合在紧开拓扑及其 \(k\) 化上连续，两边都将族 \(F(s,x)\) 送到 \(v(F(s,u(x')))\)，故所要求的自然性成立。

### S4　两个判断都正确

在 \(C_{co}(\mathbb Q,\mathbb R)\) 的零函数处，任意子基有限交邻域 \(\bigcap_i[K_i,W_i]\) 都**包含**一个 \([K,(-\epsilon,\epsilon)]\)。取 \(K=\{0\}\cup\bigcup_iK_i\)，忽略空 \(K_i\) 的约束，再取足够小的 \(\epsilon>0\) 即可。这说明原文使用的特殊形状确实构成邻域基。

紧集 \(K\subseteq\mathbb Q\) 在 \(\mathbb R\) 中闭。如果 \(I\cap\mathbb Q\subseteq K\) 对某非空开区间 \(I\) 成立，取实数中的闭包便得 \(I\subseteq K\)，矛盾。因此任意 \(0\) 的有理数邻域 \(V\) 都含有 \(q\notin K\)。令 \(\delta=d(q,K)>0\)，则答卷的函数
\[
f(x)=2\max(0,1-|x-q|/\delta)
\]
在 \(K\) 上为零，在 \(q\) 处为 \(2\)。这排除了求值在 \((0,0)\) 处连续的可能。

第一可数 Hausdorff 空间满足 \(kX=X\) 的证明也完整。若 \(x\in\overline A\setminus A\)，递降可数邻域基给出 \(A\) 中收敛于 \(x\) 的序列。序列连同极限构成紧 Hausdorff 子空间，其包含探针检测到 \(A\) 的原像不闭。

### S5　超滤子反例成立，“至少一个”已足够

在 ZFC 中，\(\mathbb N\) 上的余有限滤子可扩张为超滤子 \(\mathcal F\)。它含每个单点的补集，故为自由超滤子，且 \(\mathcal F\in\mathcal P(\mathcal P(\mathbb N))\in U\)。取 \(U\) 内的新点 \(p\)，令自然数孤立，令 \(p\) 的开邻域为 \(\{p\}\cup A\)（\(A\in\mathcal F\)）。滤子的有限交及向上封闭性保证这定义了拓扑。单点 \(\{n\}\) 及其补集分离 \(n\) 与 \(p\)，而 \(\{p\}\) 不开。

原文分割的是 \(B=K\cap\mathbb N\)。两块不交只保证**至少一块**不属于 \(\mathcal F\)。若 \(B\notin\mathcal F\)，两块都不属于它。对含 \(p\) 且 \(B\) 无限的候选紧集 \(K\)，将 \(B\) 分成两块无限集，选一块 \(A_i\notin\mathcal F\)。开集 \(\{p\}\cup(\mathbb N\setminus A_i)\) 与 \(A_i\) 中各点的单点集覆盖 \(K\)，且没有有限子覆盖。不含 \(p\) 的紧子集因离散也只能有限。

因此每个紧探针到 \(Z\) 的像都是有限离散子空间，任意子集在每个探针下的原像都开，故 \(kZ\) 离散。恒等双射 \(kZ\to Z\) 在每个 profinite 的 \(S\) 上诱导 \(C(S,kZ)=C(S,Z)\) 的恒等映射，而其逆函数在开集 \(\{p\}\) 处不满足连续性。反例完整。

### S6　连续复合与同胚判据正确

两次紧生成求值给出连续映射 \(((g,f),x)\mapsto g(f(x))\)，其指数伴随即为所需的连续复合 \(c\)。单位是 \(\mathrm{id}_{kX}\)，两侧单位律逐点成立。结合律中的“严格相等”要补入积的典范结合子 \(a((h,g),f)=(h,(g,f))\)。同源的等式为
\[
c\circ(c\times_k I)=c\circ(I\times_k c)\circ a,
\]
两边均给出 \(h\circ g\circ f\)。

S2 对形如 \(h_A,h_B\) 的预层之间的态射给出保持复合与恒等的双射，故 \(h_f\) 可逆当且仅当 \(k(f):kX\to kY\) 是同胚。这只用到 S2 前两小节的有效结果。若 \(X,Y\) 均第一可数，再由 S4 得 \(kX=X,\ kY=Y\)，于是 \(f\) 是原拓扑的同胚。

### 修订与自评

- **保留**前稿对六项最终结论的判断、三处误步的定位，以及 S4 的邻域基和 S6 的结合子说明。
- **新增或补明**自由超滤子的存在与相关空间的 \(U\)-小性、S3 中需要另证的指数律方向，以及求值分量在紧探针上的直接核验。
- **未完成或不确定项**在本次审阅范围内无。六项判断、两个反例、所用定理的条件及误步的影响均已核验，按答卷审阅标准自评达到严格完成要求。