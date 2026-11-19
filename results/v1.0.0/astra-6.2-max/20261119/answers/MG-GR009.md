## S1　有限群的自由作用

给轨道集 \(P=T/\Gamma\) 赋予商拓扑，记投影为 \(p:T\to P\)。空间 \(P\) 紧。对于两个不同的轨道 \(O,O'\)，由于它们有限且 \(T\) 有开闭基，可取开闭集 \(W\) 包含 \(O\) 并与 \(O'\) 不交。饱和集 \(\bigcup_{\gamma\in\Gamma}\gamma W\) 仍是开闭集，其像是 \(P\) 中分开这两个轨道的开闭集。因此 \(P\) 是 Hausdorff 全不连通空间。其底集是 \(U\)-小集合，故 \(P\in\mathrm{Prof}_U\)。

自由性给出 \(p\) 的连续截面。固定 \(t\in T\)，为互异的点 \(\gamma t\) 选取两两不交的开闭邻域 \(V_\gamma\)。令
\[
W_t=\bigcap_{\gamma\in\Gamma}\gamma^{-1}V_\gamma .
\]
各个 \(\gamma W_t\) 两两不交，且它们的并是 \(p^{-1}p(W_t)\)，所以 \(p(W_t)\) 开闭。限制 \(W_t\to p(W_t)\) 是从紧空间到 Hausdorff 空间的连续双射，故为同胚。这些 \(p(W_t)\) 覆盖 \(P\)。取有限子覆盖，逐项减去此前各项的并，得到有限开闭分割。在各片上拼接上述局部逆便得到连续截面 \(s:P\to T\)。于是有等变同胚
\[
\Gamma\times P\xrightarrow{\ \sim\ }T,\qquad
(\gamma,z)\longmapsto\gamma s(z).
\]
这里用到了自由性给出的双射性，以及源紧、目标 Hausdorff。

本站点上可表示预层都是层，因为有限联合满射族诱导的映射 \(\coprod_i S_i\to S\) 是紧空间到 Hausdorff 空间的满射，因而是商映射，相容的连续映射能唯一粘合。空覆盖还给出每个层 \(Y\) 的 \(Y(\varnothing)\) 是单点集。由上述有限开闭分解，
\[
Y(T)\cong\prod_{\gamma\in\Gamma}Y(P).
\]
群作用传递地置换各因子，不变元恰是对角元，也就是 \(p^*\) 的像。由 Yoneda 引理，\(h_p\) 自然给出
\[
\operatorname{Hom}(h_P,Y)\cong\operatorname{Hom}(H,Y)^\Gamma.
\]
故 \(h_P\) 是层商。

给定等变层 \(E\to H\)，取 \(D=h_s^*E\to h_P\)。在 \(T\) 的分量 \(\gamma s(P)\) 上，\(a_\gamma\) 给出 \(D\) 到 \(E\) 在该分量上之限制的同构，逆由 \(a_{\gamma^{-1}}\) 给出。它们拼成 \(H\times_{h_P}D\simeq E\)，因为每个测试映射 \(S\to\Gamma\times P\) 都按其 \(\Gamma\) 坐标给出有限开闭分割。等式 \(a_\delta a_\gamma=a_{\delta\gamma}\) 保证拼成的同构等变。这就实现了每个 \(E\)。

## S2　有限集合上的纤维分类

记代表元集为 \(I\)。取纤维 \(X\mapsto(X_t)_{t\in I}\) 给出范畴等价
\[
(\Gamma\text{-}\mathbf{FinSet})/T
\ \simeq\
\prod_{t\in I}(\Gamma_t\text{-}\mathbf{FinSet}).
\]
具体地，给定有限 \(\Gamma_t\)-集合 \(A_t\)，重构的对象为
\[
\coprod_{t\in I}\Gamma\times_{\Gamma_t}A_t\longrightarrow T,\qquad
[\gamma,x]\longmapsto\gamma t,
\]
其中 \((\gamma k,x)\sim(\gamma,kx)\) 对 \(k\in\Gamma_t\) 成立。取 \(A_t=X_t\) 时，映射 \([\gamma,x]\mapsto\gamma x\) 是等变双射。事实上，每个元素都可这样表示，而同一轨道基点的两种写法 \(\gamma t=\gamma't\) 恰满足 \(\gamma^{-1}\gamma'\in\Gamma_t\)，上述等价关系正好识别相应表示。态射由各个 \(\Gamma_t\)-等变映射 \(f_t:A_t\to A'_t\) 唯一决定，重构公式为 \([\gamma,x]\mapsto[\gamma,f_t(x)]\)。

**可实现的充要条件是每个 \(\Gamma_t\) 在 \(X_t\) 上作用平凡。** 必要性可在单点上看出。若 \(x\in X_t\) 在实现中对应 \((t,d)\)，则每个 \(k\in\Gamma_t\) 都固定 \((t,d)\)，从而固定 \(x\)。

反过来，令 \(P=T/\Gamma\)，取有限集合 \(Y\to P\)，其在 \([t]\) 上的纤维为 \(X_t\)。稳定子作用平凡保证
\[
T\times_P Y\longrightarrow X,\qquad (\gamma t,x)\longmapsto\gamma x
\]
与 \(\gamma\) 的选择无关。由纤维分类，这是等变双射，故可取 \(D=h_Y\)。代表元还给出 \(P\to T\) 的截面，沿此截面拉回任一实现便得到 \(h_Y\)。由态射分类和 Yoneda 引理，可实现对象的自同构群为
\[
\operatorname{Aut}_{\Gamma/H}(h_X)
\cong \prod_{t\in I}\operatorname{Sym}(X_t)
\cong \operatorname{Aut}_{/h_P}(h_Y).
\]

## S3　一般层的完整下降

对任意带 \(\Gamma\) 作用的层 \(F\)，记
\[
F_\Gamma=a\bigl(S\longmapsto F(S)/\Gamma\bigr),\qquad r_F:F\to F_\Gamma,
\]
其中 \(a\) 表示层化。本站点可在 \(V\) 中取小骨架，故可作上述 \(\mathrm{Set}_V\) 值层化。映射 \(r_F\) 局部满射，且对 \(x,x'\in F(S)\)，有
\[
r_F(x)=r_F(x')
\quad\Longleftrightarrow\quad
\text{存在有限覆盖 }(S_i\to S)_i\text{ 和 }\gamma_i\in\Gamma
\text{，使 }x'|_{S_i}=a_{\gamma_i}(x|_{S_i}).
\tag{1}
\]
这是层化的局部表示与局部相等性质。每个层化截面局部来自原预层，两个预层截面在层化中相等恰当它们局部相等。这里有限覆盖在拉回和复合下封闭，所以所需的细化仍是有限覆盖。

取 **\(Q=H_\Gamma\)，\(q=r_H\)**。一个 \(F\to Y\) 的不变态射在每个 \(S\) 上唯一通过 \(F(S)/\Gamma\) 分解，且这些分解与限制相容。由层化的泛性质，取 \(F=H\) 即得自然双射
\[
\operatorname{Hom}(Q,Y)\xrightarrow{\ \sim\ }\operatorname{Hom}(H,Y)^\Gamma,\qquad
u\longmapsto uq.
\]

**可实现性判据**为
\[
\boxed{\quad
\forall S\in\mathrm{Prof}_U,\ e\in E(S),\ \gamma\in\Gamma,\qquad
\gamma\pi(e)=\pi(e)\ \Longrightarrow\ a_\gamma(e)=e .
\quad}
\tag{2}
\]
等价地，对每个 \(\gamma\)，\(a_\gamma\) 在 \(E\times_H h_{T^\gamma}\) 上是恒等。这里固定点集 \(T^\gamma\) 是 Hausdorff 空间 \(T\) 中的闭子空间，因而仍是 profinite，而 \(\gamma\pi(e)=\pi(e)\) 恰表示 \(\pi(e):S\to T\) 通过 \(T^\gamma\) 分解。

为证此判据，令 \(D_E=E_\Gamma\)，由不变映射 \(q\pi\) 赋予它到 \(Q\) 的态射。考虑等变比较映射
\[
c_E=(\pi,r_E):E\longrightarrow H\times_Q D_E.
\]
它总是局部满射。给定右端的截面 \((t,d)\)，局部把 \(d\) 提升为 \(e\)。由于 \(q\pi(e)=q(t)\)，由 (1)，再细化覆盖后可写 \(t=\gamma\pi(e)\)。于是 \(a_\gamma(e)\) 提升 \((t,d)\)。

若 (2) 成立且 \(c_E(e)=c_E(e')\)，则 \(\pi(e)=\pi(e')\)，并且由 (1) 局部有 \(e'=a_\gamma(e)\)。在每一这样的覆盖成员上，\(\gamma\) 固定共同的基底截面，故 \(e'=e\)。层的分离性给出全局相等。因此 \(c_E\) 为单态射。单且局部满射的层态射是同构，因为局部提升在交叠上由单性相等，因而唯一粘合。反过来，在任一实现 \(H\times_Q D\) 中，固定 \(t\) 的 \(\gamma\) 固定每个 \((t,d)\)，故 (2) 必要。

为说明分类及其基变换，先记录一个自然同构。若 \(F\to Z\) 不变且 \(Z'\to Z\) 任意，则
\[
(F\times_Z Z')_\Gamma \xrightarrow{\ \sim\ } F_\Gamma\times_Z Z',
\qquad [(x,z')]\longmapsto([x],z').
\tag{3}
\]
右端截面 \((d,z')\) 局部可将 \(d\) 提升为 \(x\)，此时 \((x,z')\) 就是相容的提升。为证单性，在共同覆盖上为左端的两个截面取代表。若像相等，则其 \(Z'\) 坐标相等，而两个 \(F\) 坐标由 (1) 局部相差某个 \(\gamma\)。于是代表的有序对也局部相差同一 \(\gamma\)，给出左端截面相等。

记 \(\mathcal A\) 为满足 (2) 的等变对象及其在 \(H\) 上的等变态射所成的满子范畴。有等价
\[
\mathcal C/Q \simeq \mathcal A,\qquad
D\longmapsto H\times_Q D,\qquad E\longmapsto D_E.
\]
一个方向的复合由 \(c_E\) 识别为恒等，另一个方向由 (3) 取 \(F=H,\ Z=Q,\ Z'=D\) 得到 \((H\times_QD)_\Gamma\simeq D\)。具体到态射，对任意等变 \(E\) 都有
\[
\operatorname{Hom}_{\Gamma/H}(E,H\times_Q D)
\cong \operatorname{Hom}_{/Q}(D_E,D),
\]
因为左端态射的第一坐标是 \(\pi\)，第二坐标恰是 \(Q\) 上的不变态射。故对可实现的 \(E,E'\)，等变态射一一对应于 \(D_E\to D_{E'}\) 的 \(Q\) 上态射。固定可实现的 \(E\) 后，每个实现同构都唯一写为
\[
E\xrightarrow{c_E}H\times_Q D_E
 \xrightarrow{1_H\times_Q\alpha}H\times_Q D,\qquad
\alpha:D_E\xrightarrow{\sim}D\ \text{在 }Q\text{ 上}.
\]
因此，带有所给识别的任意两个实现之间有唯一与识别相容的同构。

对于**任意** \(B\to Q\)，置 \(H_B=H\times_Q B\)，群只作用于 \(H\) 坐标。由 (3)，\((H_B)_\Gamma\simeq B\)。上述比较映射的证明只使用轨道层的局部描述 (1)，所以也适用于 \(H_B\to B\)。具体地，令 \(\mathcal A_B\) 的对象为等变的 \(\rho:F\to H_B\)，要求对每个测试空间上的截面 \(f\) 都有 \(\gamma\rho(f)=\rho(f)\Rightarrow a_\gamma(f)=f\)，态射取 \(H_B\) 上的等变态射。便有
\[
\mathcal C/B\simeq\mathcal A_B,\qquad
D\longmapsto H_B\times_B D,\qquad F\longmapsto F_\Gamma\to B.
\]
沿 \(B'\to B\) 拉回时，正向构造由纤维积结合律相容，逆向构造由 (3) 给出的 \((F\times_B B')_\Gamma\simeq F_\Gamma\times_B B'\) 相容。这些识别与连续两次拉回相容，因为在局部代表上都保留同一个轨道类和最后的基底坐标。

## S4　单点上的检验

**否。** 取 \(T=*\)、\(\Gamma=C_2\)，于是 \(H=Q=h_*\)。令 \(K=(\mathbb Z/3)^{\mathbb N}\) 取乘积拓扑。它是无限的 \(U\)-小 profinite 群，这里用到了 \(\mathbb N\in U\)。对每个 \(S\) 定义预层
\[
P(S)=\operatorname{Cont}(S,K)/L(S),
\qquad L(S)=\{S\to K\text{ 的局部常值映射}\}.
\]
局部常值映射构成子群且在预合成下封闭。取 \(E=aP\)，由取负映射定义 \(C_2\) 在 \(E\) 上的作用，结构映射为 \(E\to h_*\)。

有 \(E(*)=\{0\}\)。事实上，\(P(*)=\{0\}\)，而每个 \(E(*)\) 中的截面都在某覆盖上来自 \(P\)。该覆盖有一个非空成员，选其中一点，沿此点拉回局部代表就得到原截面在 \(P(*)\) 中的代表。因此题设的单点条件成立。

在 \(E(K)\) 中考虑 \(\xi=[\operatorname{id}_K]\) 的层化像。若 \(\xi=-\xi\)，由层化的局部相等性质，存在有限覆盖 \(u_i:S_i\to K\)，使得每个 \(2u_i\) 局部常值。乘 \(2\) 是 \(K\) 的自同构，所以每个 \(u_i\) 局部常值。由于 \(S_i\) 紧，其像有限，有限多个这样的像无法覆盖无限集 \(K\)。故 \(\xi\ne-\xi\)。在 \(H=Q=h_*\) 上的实现中，群作用必为恒等，而此处群元移动 \(\xi\)，故 \(E\) 不可实现。

## S5　局部满射的基底检验

**是。** 取 \(e\in E(S)\) 和满足 \(\gamma\pi(e)=\pi(e)\) 的 \(\gamma\)。由 \(B\to Q\) 局部满射，\(q\pi(e)\) 在某有限覆盖 \(S_i\to S\) 上有提升 \(b_i\in B(S_i)\)。记 \(e_i=e|_{S_i}\)。在拉回对象中，\(\gamma\) 固定 \((e_i,b_i)\) 的基底截面 \((\pi(e_i),b_i)\)。因该对象可在 \(B\) 上实现，\(\gamma\) 也固定 \((e_i,b_i)\)。从而 \(a_\gamma(e_i)=e_i\) 对每个 \(i\) 成立。由层的分离性，\(a_\gamma(e)=e\)。这验证了 S3 的判据 (2)，故 \(E\) 可在 \(Q\) 上实现。

## S6　非空基底与全局结论

**否。** 取 \(\Gamma=C_2\) 平凡作用于 \(T=\{0,1\}\)，故 \(Q=H=h_T\)。取有限等变集合
\[
X_0=\{x\},\qquad X_1=\{y,z\},\qquad X=X_0\amalg X_1\longrightarrow T,
\]
其中非平凡群元固定 \(x\) 并交换 \(y,z\)。取 \(E=h_X\)，以及选取 \(0\in T\) 的非空可表示基底 \(B=h_*\to Q\)。此时 \(H_B=B\)，而 \(E\times_Q B=h_{\{x\}}\simeq B\)，作用平凡，由 \(D_B=B\to B\) 实现。全局上，点 \(1\) 的稳定子是整个 \(C_2\)，它在 \(X_1\) 上作用非平凡。由 S2，\(E\) 不可实现。

综上，可用的检验原则如下。

- **稳定子检验。** 对一般层，逐个 \(\gamma\) 检查其在 \(E\times_H h_{T^\gamma}\) 上是否为恒等，这是充要条件。若 \(E\) 可表示，截面是由逐点值决定的连续映射，此时 S4 的单点条件也充分。有限集合情形只需检查轨道代表的纤维。
- **基底检验。** 实现沿任意基变换保留。反向检验可用任一联合局部满射的基底族，因为 S5 的证明允许各覆盖成员分别提升到族中的不同基底。特别地，\(H\to Q\) 本身就足够，也可使用全体 \(h_S\to Q\)，因为每个 \(Q(S)\) 中的截面自身就给出这样的态射。单个可表示基底的非空性不足以保证反向检验成立。