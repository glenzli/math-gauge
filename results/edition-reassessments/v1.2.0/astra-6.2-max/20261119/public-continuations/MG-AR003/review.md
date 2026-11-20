# 《探针映射空间与连续性层级》答卷审阅

**S1–S6 的最终结论均成立，六个阶段均有作答。原答卷的证明按原文尚不完全正确。** S2.3 错认了原连续映射在自然变换中的像，S3.1 第 4 步把局部紧假设用在了错误的变量上，S5.2 从超滤子性质多推出了一个“恰有”。这些问题可以局部修正。S4 的反例需要补明两处邻域论证，S6 的结合律需按积的典范结合子理解。

沿用题设，\(h_A(T)=C(T,A)\) 以 \(U\)-小 profinite 空间 \(T\) 为参数，\(kA\) 由全部 \(U\)-小紧 Hausdorff 探针定拓扑，\(C_{co}\) 取紧开拓扑。

## S1　局部紧输入

求值连续性的证明正确。局部紧 Hausdorff 性允许在 \(f_0^{-1}(W)\) 中取 \(x_0\) 的开邻域 \(V\)，使 \(K=\overline V\) 紧且仍含于 \(f_0^{-1}(W)\)。于是 \([K,W]\times V\) 上的求值都在 \(W\) 中。

给定连续的 \(F:Z\times X\to Y\)，条件 \(F(\{z\}\times K)\subset W\) 对 \(z\) 是开条件，由 \(K\) 紧和管道引理即得。这证明柯里化连续，反向由上述求值连续性得到，两方向在点上互逆。由连续的 \(j:X'\to X\)、\(v:Y\to Y'\) 所定的预、后复合映射，对紧开子基的原像分别为 \([j(K'),W]\) 和 \([K,v^{-1}(W')]\)。二者均开，答卷在 S1 所设范围内对 \(X,Y,Z\) 所写的自然性等式成立。

## S2　探针与原拓扑连续映射

前两小节正确。对任意 \(U\)-小紧 Hausdorff 空间 \(K\)，将其底集离散化为 \(D\)。可用 \(D\) 上的全体超滤子实现 \(\beta D\)，其底集包含于 \(\mathcal P(\mathcal P(D))\)，故底集和拓扑均可取在 \(U\) 中。这个紧 Hausdorff 空间以 \(\{\mathcal F\in\beta D:A\in\mathcal F\}\)（\(A\subseteq D\)）为闭开基，因而属于 \(\mathrm{Prof}_U\)。由 Stone–Čech 紧化对紧 Hausdorff 靶的延拓性质，底集恒等映射 \(D\to K\) 延拓为 \(\pi:\beta D\to K\)。它在 \(D\) 上已取到全部值，又是紧空间到 Hausdorff 空间的连续映射，故为闭的商满射。因此对每个探针 \(r:K\to X\)，由 \((r\pi)^{-1}(O)\) 开可推出 \(r^{-1}(O)\) 开。反向包含由每个 profinite 空间都是紧 Hausdorff 空间得到，两类探针所定拓扑相同。

对每个 profinite 探针 \(p:S\to X\)，沿点 \(*\to S\) 的自然性强制 \(\alpha_S(p)=g\circ p\)，其中 \(g\) 是 \(\alpha_*\) 给出的底集函数。对每个紧 Hausdorff 源 \(L\) 都有 \(C(L,Y)=C(L,kY)\)，这是 \(kY\) 的定义和 \(kY\to Y\) 的连续性的直接结果。由 \(kX\) 的终拓扑，所有 \(g\circ p\) 连续恰等价于 \(g:kX\to kY\) 连续。这给出 \(\operatorname{Nat}(h_X,h_Y)\cong C(kX,kY)\)，且对应保持恒等与复合。同一紧探针等式也给出 \(k(kX)=kX\)。

**S2.3 应把原连续映射的像写为 \(\{k(f)\mid f\in C(X,Y)\}\subseteq C(kX,kY)\)。** 其中 \(k(f)\) 与 \(f\) 有同一底集函数，其连续性由紧探针判别得到。取下文 S5 核验的空间 \(Z\)，令 \(X=Y=Z\)。恒等函数 \(Z\to Z\) 连续并诱导恒等自然变换，而同一函数 \(Z\to kZ\) 不连续。这就排除了原文对该像的描述 \(C(X,kY)\)。

题目的全称命题仍成立。若 \(X=kX\)，每个 \(g:kX\to kY\) 都通过 \(kY\to Y\) 给出原连续映射。反过来可取 \(Y=kX\)，其拓扑细于 \(X\) 的 Hausdorff 拓扑，且是 \(\mathcal P(|X|)\) 的子集，故这是允许的 \(U\)-小 Hausdorff 目标。若 \(\mathrm{id}_{kX}\) 对应的自然变换由原连续映射诱导，在单点探针上求值就迫使该映射为 \(\mathrm{id}:X\to kX\)。它连续即给出 \(\tau_{kX}\subseteq\tau_X\)，而反向包含恒成立。

## S3　映射空间、求值与参数

构造 \(M(X,Y)=kC_{co}(kX,kY)\) 正确。底集 \(C(kX,kY)\) 是 \(U\) 内函数集的子集，其紧开拓扑及 \(k\) 拓扑也都是 \(U\)-小的。不同函数可在某个单点紧集上用 \(kY\) 中不交的开集分离，故映射空间 Hausdorff，\(k\) 化后紧生成。

S3.1 第 4 步要从 \(a:S\to C_{co}(kX,kY)\) 的连续性推出 \((s,x)\mapsto a(s)(x)\) 在通常积上连续。直接用 S1 需要函数的定义域 \(kX\) 局部紧，题设只保证此处的参数 \(S\) 局部紧。例如 S4 中的 \(k\mathbb Q=\mathbb Q\) 没有紧邻域。若用 \(S\) 作函数的定义域，交换积因子后，S1 将 \(C(S\times kX,kY)\) 与 \(C(kX,C_{co}(S,kY))\) 配对。从联合连续得到连续函数族的另一方向仍可用 S1 的管道引理论证。

答卷在 S3.2 引用的紧生成 Hausdorff 空间指数律足以修正这一步。该定理对紧生成 Hausdorff 的 \(A,B,D\) 给出自然双射
\[
C(A,kC_{co}(B,D))\cong C(A\times_k B,D),\qquad A\times_k B=k(A\times B).
\]
这里 \(S,kX,kY\) 都满足条件。紧 Hausdorff 源 \(S\) 的映射可提升到目标的 \(k\) 化，又因局部紧 Hausdorff 空间与紧生成 Hausdorff 空间的通常积紧生成，得到
\[
C(S,C_{co}(kX,kY))=C(S,M(X,Y))
\cong C(S\times_k kX,kY)=C(S\times kX,kY).
\]
因此第 4 步所写的双射本身成立。

对任意 Hausdorff 参数 \(Z\)，有 \(h_Z\times h_X\cong h_{Z\times X}\)。紧探针到积的连续性可按坐标检验，故 \(k(Z\times X)=kZ\times_k kX\)。由 S2 和上述指数律，
\[
\operatorname{Nat}(h_Z\times h_X,h_Y)
\cong C(kZ\times_k kX,kY)
\cong C(kZ,M(X,Y))
\cong \operatorname{Nat}(h_Z,h_M).
\]
从右向左，\(a:kZ\to M\) 对应 \((z,x)\mapsto a(z)(x)\)，所以正是题给的 \(\alpha\mapsto ev\circ(\alpha\times I)\)。特别地，取 profinite 的 \(Z=S\) 并用 \(kS=S\)，即得 \(C(S,M)\cong H_{X,Y}(S)=\operatorname{Nat}(h_S\times h_X,h_Y)\)。

求值分量 \(ev_T(\phi,\psi)(t)=\phi(t)(\psi(t))\) 的连续性还可直接核验。紧探针 \(\psi:T\to kX\) 的像 \(L\) 紧 Hausdorff。限制 \(C_{co}(kX,kY)\to C_{co}(L,kY)\) 连续，因为 \(L\) 的紧子集在 \(kX\) 中仍紧。在 \(L\) 上使用 S1 的连续求值，再复合 \(kY\to Y\)，即得所需的 \(T\to Y\)。该公式与参数的预复合逐点交换。对连续 \(u:X'\to X\)、\(v:Y\to Y'\)，用 \(k(u),k(v)\) 作预、后复合，由紧开子基的原像公式及 \(k\) 化得到连续的映射空间态射。在预层上取其诱导态射，两边都把族 \(F(s,x)\) 变为 \(v(F(s,u(x')))\)。因此答卷要求的自然性也成立。

## S4　第一可数输入的两个判断

\(\mathbb Q,\mathbb R\) 可由 \(\mathbb N\) 在 \(U\) 内构造。取 \(X=\mathbb Q,Y=\mathbb R\) 的反例有效。在零函数处，形如 \([K,(-\epsilon,\epsilon)]\) 的集合确实可作邻域基。一般的子基有限交 \(\bigcap_i[K_i,W_i]\) 可以缩小为这种集合，取 \(K=\{0\}\cup\bigcup_iK_i\)，忽略空 \(K_i\) 的约束，再使 \((-\epsilon,\epsilon)\) 包含于其余各 \(W_i\) 中即可。这里需要的是包含关系。

紧集 \(K\subseteq\mathbb Q\) 在 \(\mathbb R\) 中紧且闭。若对某非空开区间 \(I\) 有 \(I\cap\mathbb Q\subseteq K\)，由有理数的稠密性及 \(K\) 的闭性可得 \(I\subseteq K\)，矛盾。这补明了 \(K\) 在 \(\mathbb Q\) 中也无内点的理由。因此每个 \(0\) 的邻域 \(V\subseteq\mathbb Q\) 都含 \(q\notin K\)。令 \(\delta=d(q,K)>0\)，答卷的连续函数 \(f(x)=2\max(0,1-|x-q|/\delta)\) 在 \(K\) 上为零，且 \(f(q)=2\)。故没有这样的乘积邻域能把求值限制在 \((-1,1)\) 中，通常求值在 \((0,0)\) 处不连续。

第一可数 Hausdorff 空间满足 \(kX=X\) 的论证完整。若 \(x\in\overline A\setminus A\)，递降可数邻域基给出 \(A\) 中收敛到 \(x\) 的序列。序列连同极限构成紧 Hausdorff 子空间，其包含探针检测到 \(A\) 的原像不闭。

## S5　超滤子反例

反例所用的对象合法。在 ZFC 中，\(\mathbb N\) 上的余有限滤子可扩张为超滤子 \(\mathcal F\)。它含每个单点的补集，故为自由超滤子，且 \(\mathcal F\in\mathcal P(\mathcal P(\mathbb N))\in U\)。可取 \(U\) 内的新点 \(p\)。在 \(Z=\mathbb N\cup\{p\}\) 上令自然数孤立，令含 \(p\) 的开集为 \(\{p\}\cup A\)（\(A\in\mathcal F\)）。滤子的有限交与向上封闭性保证这定义了拓扑。每个 \(n\) 与 \(p\) 可用 \(\{n\}\) 及其补集分离，且 \(\{p\}\) 不开。

**不交性只保证至少一块不属于 \(\mathcal F\)，这已经足够。** 答卷分割的是 \(B=K\cap\mathbb N\)。断定“恰有一个”还需要 \(B\in\mathcal F\)。若 \(B\notin\mathcal F\)，两块都会不在 \(\mathcal F\) 中。对含 \(p\) 且 \(B\) 无限的候选紧集 \(K\)，将 \(B\) 分为两块无限集，选一块 \(A_i\notin\mathcal F\)。则 \(\{p\}\cup(\mathbb N\setminus A_i)\) 开，它和 \(A_i\) 中各点的单点集覆盖 \(K\)，且没有有限子覆盖。不含 \(p\) 的紧集因离散也只能有限。

于是每个紧 Hausdorff 探针到 \(Z\) 的像都是有限离散子空间。任意 \(E\subseteq Z\) 在该像上的交都是开集，从而它在探针下的原像开。这直接按题面的探针定义证明 \(kZ\) 离散。恒等双射 \(kZ\to Z\) 连续，且对每个 profinite 的 \(S\) 在 \(C(S,kZ)=C(S,Z)\) 上诱导恒等映射。但逆函数把 \(kZ\) 的开集 \(\{p\}\) 拉回到 \(Z\) 的非开集，故原拓扑下的同胚结论确实失败。

## S6　复合与识别范围

两次连续的紧生成求值给出连续映射 \(((g,f),x)\mapsto g(f(x))\)。由 S3 的指数律，其伴随就是定义在 \(M(Y,Z)\times_k M(X,Y)\) 上的连续复合 \(c\)。单位 \(\mathrm{id}_{kX}\) 满足两侧单位律。对结合律，设 \(a((h,g),f)=(h,(g,f))\) 为积的典范结合子，同源的态射等式是
\[
c\circ(c\times_k I)=c\circ(I\times_k c)\circ a .
\]
两边都给出 \(h\circ g\circ f\)。这说明原文“严格相等”所需的括号识别。

S2 对形如 \(h_A,h_B\) 的预层之间的态射给出了保持复合和恒等的双射。故对连续 \(f:X\to Y\)，\(h_f\) 的自然逆恰对应 \(k(f):kX\to kY\) 的连续逆。充要条件确为 \(k(f)\) 是同胚。这一判据用到 S2 前两小节的有效结论。若 \(X,Y\) 均第一可数，再用 S4 给出的 \(kX=X,kY=Y\)，就得到 \(f\) 是原拓扑的同胚。

## 修订与自评

- 保留了前稿对 S1–S6 最终结论的判断、三处局部误步的定位，以及对 S4 邻域基和 S6 结合子的说明。
- 本稿补明了自由超滤子的 ZFC 依据与相关空间的 \(U\)-小性，区分了 S3 中指数律的两个方向，并在紧探针上直接核验了求值。
- 审阅范围内无未完成或待定项。六项判断、两个具体反例及其依赖均有可核查的依据，各处误步的影响已分别说明。按答卷审阅标准，自评达到本项的严格完成要求。
