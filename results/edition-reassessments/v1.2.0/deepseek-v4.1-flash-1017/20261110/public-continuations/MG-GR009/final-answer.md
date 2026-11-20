# 群作用下降、稳定子与基底检验：完整终稿

以下始终在层范畴

\[
\mathbf C=\mathbf{Sh}(\mathbf{Prof}_U;\mathbf{Set}_V)
\]

中工作。纤维积都在 \(\mathbf C\) 中取，终对象记为 \(*\)。固定 \(T\in\mathbf{Prof}_U\)、\(H=h_T\)，以及 \(U\)-小离散群 \(\Gamma\) 在 \(T\) 上的作用；相应层映射记为 \(h_\gamma:H\to H\)。对测试对象 \(U\) 和 \(x\in H(U)=\operatorname{Hom}(U,T)\)，记

\[
E_x(U)=\{e\in E(U):\pi_U(e)=x\}.
\]

“\(E\to H\) 上的群作用”始终指切片中的群同态 \(\Gamma\to\operatorname{Aut}_{\mathbf C/H}(E)\)，从而 \(\pi a_\gamma=h_\gamma\pi\)。本稿先证明一个反复使用的商同余引理，以免把层商误认为逐对象轨道商。

## 0. 群作用、商与局部满射

先写清本节使用的范畴约定。对象 \(X\) 上的离散群 \(G\)-作用可写成切片中群对象
\(G\times X\to X\) 的作用；其核对的商记为 \(p:X\to X/G\)。
层范畴中的商是余等化子，而不是逐测试对象上的轨道集合。下面的引理描述它在测试截面上的精确关系。

**引理 0.1.** 设 \(G\) 是 \(\mathbf C\) 中离散的 \(U\)-小群，\(X\) 带 \(G\)-作用，并令

\[
p:X\longrightarrow X/G:=\operatorname{coeq}(G\times X\rightrightarrows X)
\]

为作用映射 \((g,x)\mapsto gx\) 与投影到 \(X\) 的 \((g,x)\mapsto x\) 的余等化子。则 \(p\) 局部满；并且对任意 \(U\) 及 \(x,y\in X(U)\)，

\[
p_U(x)=p_U(y)
\tag{0.1}
\]

当且仅当存在 \(U\) 的有限覆盖 \(\{u_i:U_i\to U\}_{i=1}^m\) 及元素 \(g_i\in G\)，使

\[
g_i\cdot x|_{U_i}=y|_{U_i}\qquad(i=1,\ldots,m).
\tag{0.2}
\]

证明：令

\[
R=\operatorname{im}\left(G\times X\xrightarrow{(g x,x)}X\times X\right).
\]

单位元、逆元及乘法分别使 \(R\) 自反、对称、传递，故 \(R\) 是 \(X\) 上的内等价关系。Grothendieck topos 中的等价关系有效；有效商 \(X\to X/G\) 的核对正是 \(R\)。另一方面，一个截面向局部沿有限覆盖提升到 \(G\times X\)，正是 (0.2)。这就是商映射的局部刻画。下文把 \(X/G\) 同时也用作商对象，不把它和逐测试对象上的集合商混淆。

还会使用：在 topos 中，一个态射若在所有测试截面上都局部有提升，则它是满态射；同时为单态射的满态射是同构。凡下文从“单态射加局部满射”得到同构，皆使用这一标准事实。

---

## S1 有限群的自由作用

### S1.1 轨道空间

设 \(\Gamma\) 有限且自由作用在 \(T\) 上。S1 内把轨道空间记为 \(Q_0\)，以免与 S3 的一般商 \(Q\) 混淆。令

\[
Q_0=T/\Gamma,
\qquad q:T\longrightarrow Q_0
\]

分别为轨道集合赋商拓扑及其商映射。

固定 \(t\in T\)。对每个 \(\gamma\neq e\)，由 \(T\) 紧 Hausdorff 全不连通，可以在 \(t\) 与 \(\gamma t\) 周围取不交的 clopen 邻域。因为 \(\Gamma\) 有限，再缩小并取交，得到 \(t\) 的 clopen 邻域 \(V_t\)，使诸 \(\gamma V_t\) 两两不交。于是

\[
q^{-1}q(V_t)=\coprod_{\gamma\in\Gamma}\gamma V_t
\]

是开集，故 \(q(V_t)\) 开。限制 \(q|_{V_t}\) 是紧空间到 Hausdorff 空间的连续双射，因此为同胚；所以 \(q(V_t)\) 也闭。由此商空间有 clopen 基；它作为紧 Hausdorff 空间的商仍紧 Hausdorff，从而全不连通。因此

\[
Q_0\in\mathbf{Prof}_U.
\]

每个纤维是一个有限自由轨道，而上述限制是局部同胚，所以 \(q\) 是有限覆盖。同一轨道内连接两点的群元素唯一，因而

\[
T\times_{Q_0}T\cong\Gamma\times T,\qquad
(t,\gamma t)\longleftrightarrow(t,\gamma).
\tag{1.1}
\]

### S1.2 层商

任取层 \(Y\)。由 \(q\) 是覆盖，层公理给出

\[
Y(Q_0)\cong
\operatorname{Eq}\left(
Y(T)\rightrightarrows Y(T\times_{Q_0}T)
\right).
\]

用 (1.1) 及层对有限乘积的性质，右端恰为

\[
Y(T)^\Gamma
=\{s\in Y(T):Y(h_\gamma)s=s\text{ 对所有 }\gamma\in\Gamma\}.
\]

再由 Yoneda，

\[
\begin{aligned}
\operatorname{Hom}_{\mathbf C}(h_{Q_0},Y)
&\cong Y(Q_0)
\cong Y(T)^\Gamma\\
&\cong\operatorname{Hom}_{\mathbf C}(H,Y)^\Gamma.
\end{aligned}
\tag{1.2}
\]

这些双射自然。因此 \(h_{Q_0}\) 表示 \(H\) 关于 \(\Gamma\) 的层余等化子；等价地，

\[
h_{Q_0}\cong\operatorname{coeq}\left(
\coprod_{\gamma\in\Gamma}H\rightrightarrows H
\right),
\tag{1.3}
\]

且 \(h_q:H\to h_{Q_0}\) 是层商。特别地，从 \(h_{Q_0}\) 出发的态射正好是 \(\Gamma\)-不变的层映射。

### S1.3 每个等变层都在 \(Q_0\) 上实现

设 \(\pi:E\to H\) 带等变作用 \(a_\gamma\)。令

\[
d:E\longrightarrow D:=E/\Gamma
\]

为作用商。由 \(q\pi a_\gamma=qh_\gamma\pi=q\pi\)，映射 \(q\pi\) 过 \(D\)，得到 \(\bar\pi:D\to Q_0\)。定义

\[
\kappa:E\longrightarrow H\times_{Q_0}D,
\qquad \kappa(e)=(\pi(e),[e]).
\tag{1.4}
\]

在右端取作用

\[
\gamma\cdot(x,d)=(h_\gamma x,d).
\tag{1.5}
\]

则 \(\kappa(a_\gamma e)=\gamma\cdot\kappa(e)\)。

先证 \(\kappa\) 单。若 \(\kappa(u)=\kappa(v)\)，则 \(\pi(u)=\pi(v)=:x\) 且 \([u]=[v]\)。由引理 0.1，存在有限覆盖及 \(\gamma_i\) 使 \(v|_{U_i}=a_{\gamma_i}(u|_{U_i})\)。比较基映射，

\[
x|_{U_i}=\pi(v|_{U_i})=h_{\gamma_i}x|_{U_i}.
\]

自由性迫使 \(\gamma_i=e\)。故每块上 \(u=v\)，由分离性得全局 \(u=v\)。

再证局部满。任取 \((x,d)\in(H\times_{Q_0}D)(U)\)。因为 \(d:E\to D\) 局部满，局部取 \(e_i\in E(U_i)\) 提升 \(d|_{U_i}\)。又 \(q\pi(e_i)=qx|_{U_i}\)，由 \(h_{Q_0}\) 是商，再细覆盖后可取 \(\gamma_i\) 使

\[
\pi(e_i)=h_{\gamma_i}x|_{U_i}.
\]

于是 \(a_{\gamma_i^{-1}}e_i\) 覆盖 \(x|_{U_i}\)，并在 \(D\) 中仍覆盖 \(d|_{U_i}\)。所以 \(\kappa\) 局部满。它既单又局部满，从而是同构：

\[
E\cong H\times_{Q_0}D,
\]

并且作用只改变 \(H\) 坐标。S1 完成。

---

## S2 有限集合上的纤维分类

设 \(\Gamma,T\) 有限，\(T\) 的轨道分解为

\[
T=\coprod_{i=1}^r O_i,\qquad O_i=\Gamma t_i,
\qquad K_i=\Gamma_{t_i}=\operatorname{Stab}_\Gamma(t_i).
\]

于是 \(O_i\cong\Gamma/K_i\)。令

\[
Q_2=T/\Gamma,\qquad q_2:T\to Q_2.
\]

以下所有有限集合都作为离散 profinite 空间看待。原题所说的“等变层”在本阶段就是离散 profinite 空间切片中带
\(\Gamma\)-作用的映射；Yoneda 后，不带这个作用的对象不在分类范围内。

### S2.1 对象与态射

设 \(f:X\to T\) 是有限 \(\Gamma\)-集之间的等变映射。令

\[
X_i=f^{-1}(O_i),\qquad S_i=f^{-1}(t_i).
\]

每个 \(S_i\) 是有限 \(K_i\)-集，并有 \(T\) 上的等变同构

\[
\Gamma\times_{K_i}S_i
\xrightarrow{\ \sim\ }X_i,
\qquad [\gamma,s]\longmapsto\gamma s.
\tag{2.1}
\]

其基映射为 \([\gamma,s]\mapsto\gamma t_i\)。反过来，任意有限 \(K_i\)-集 \(S_i\) 经 (2.1) 给出一个对象。因此

\[
\bigl\{X\to T\text{ 有限等变}\bigr\}
\simeq
\prod_{i=1}^r\{\text{有限 }K_i\text{-集 }S_i\}.
\tag{2.2}
\]

若 \(Y\to T\) 在 \(t_i\) 上的纤维为 \(R_i\)，态射 \(F:X\to Y\) 不混合不同的 \(T\)-轨道；它由其代表点纤维映射

\[
F_{t_i}:S_i\to R_i
\]

唯一决定，而后者恰为 \(K_i\)-等变映射。故

\[
\operatorname{Hom}^{\Gamma}_{T}(X,Y)
\cong
\prod_{i=1}^r\operatorname{Hom}_{K_i}(S_i,R_i).
\tag{2.3}
\]

Yoneda 将这些集合映射等同于切片层 \(h_T\) 上的等变态射。

### S2.2 可实现性的充要条件

\[
\boxed{
h_X\text{ 在 }Q_2\text{ 上可实现}
\iff
\forall i,\ K_i\text{ 在 }S_i\text{ 上作用平凡}.
}
\tag{2.4}
\]

等价地，对每个 \(x\in X\),

\[
\Gamma_x=\Gamma_{f(x)}.
\tag{2.5}
\]

又等价于存在有限集 \(S\to Q_2\)，使

\[
X\cong T\times_{Q_2}S
\tag{2.6}
\]

在 \(T\) 上等变。此时可取 \(S=X/\Gamma\)。

必要性：若 \(h_X\cong h_T\times_{Q_2}D\)，则在 \(t_i\)-纤维上，元素 \(k\in K_i\) 只改变 \(h_T\)-坐标，而 \(t_i\) 被固定，故 \(k\) 在 \(S_i\) 上恒等。

充分性：若 \(K_i\) 在 \(S_i\) 上平凡，则 \(X_i\cong(\Gamma/K_i)\times S_i\)，且 \(\Gamma\) 只作用在第一个因子上。于是

\[
h_X\cong h_T\times_{Q_2}h_{X/\Gamma}.
\]

取 \(D=h_{X/\Gamma}\) 即得实现。

### S2.3 等变自同构

设 (2.4) 成立。在

\[
X_i\cong\Gamma\times_{K_i}S_i
\]

上，一个保持基点的等变自同构，其作用必须在 \(\Gamma/K_i\) 的每个点上使用同一个 \(S_i\)-置换；否则不能与整个 \(\Gamma\)-作用相容。反过来，每个 \(S_i\)-置换唯一延拓。因此

\[
\boxed{
\operatorname{Aut}^{\Gamma}_{\mathbf C/H}(h_X)
\cong
\prod_{i=1}^r\operatorname{Sym}(S_i)
\cong
\prod_{i=1}^r\mathfrak S_{|S_i|}.
}
\tag{2.7}
\]

在基底层上，这同时是下降层 \(D=h_{X/\Gamma}\) 在 \(\mathbf C/Q_2\) 中的自同构群。若不要求等变而只计算 \(\mathbf C/h_T\) 中的自同构，所得是各点纤维置换的乘积 \(\prod_{t\in T}\operatorname{Sym}(X_t)\)，不是本阶段所问的群。

---

## S3 一般层的完整下降

回到共同设定。此时 \(\Gamma\) 可以是任意 \(U\)-小离散群，且 \(T\) 上作用无需自由。

### S3.1 商层 \(Q\)

在 \(\mathbf C\) 中定义商对象时，取余等化子，不把它逐点等同于集合轨道商。令

\[
Q:=\operatorname{coeq}\left(
\Gamma\times H\rightrightarrows H
\right),
\tag{3.1}
\]

其中箭头为 \((\gamma,x)\mapsto h_\gamma x\) 与投影 \((\gamma,x)\mapsto x\)。显式地说，先取预层轨道商

\[
P(U)=H(U)/\Gamma,
\]

再令 \(Q=P^\#\)。令 \(q:H\to Q\) 为典范商，则 \(qh_\gamma=q\)。这个预层轨道商的层化就是 (3.1) 的余等化子。对任何层 \(Y\)，余极限的 Hom 公式给出

\[
\begin{aligned}
\operatorname{Hom}_{\mathbf C}(Q,Y)
&\cong
\operatorname{Eq}\left(
\operatorname{Hom}(H,Y)\rightrightarrows
\prod_{\gamma\in\Gamma}\operatorname{Hom}(H,Y)
\right)\\
&\cong
\{f:H\to Y:fh_\gamma=f\text{ 对所有 }\gamma\}\\
&=\operatorname{Hom}_{\mathbf C}(H,Y)^\Gamma.
\end{aligned}
\tag{3.2}
\]

这正是所要求的自然同构。商 \(q\) 局部满；它的截面同余关系由引理 0.1 描述。特别地，一般不能直接宣称 \(Q(U)=H(U)/\Gamma\)，因为层化可以在有限覆盖上识别截面。

### S3.2 不预选 \(D\) 的判据

对等变对象 \(E\to H\)，定义逐局部稳定子条件：

\[
\boxed{
\begin{array}{l}
\textbf{(LS) 对每个 }U,\ x\in H(U),\ \gamma\in\Gamma,\\
h_\gamma x=x\Longrightarrow
a_\gamma|_{E_x(U)}=\operatorname{id}_{E_x(U)}.
\end{array}}
\tag{3.3}
\]

**定理 3.1.** \(E\) 在 \(Q\) 上可实现，当且仅当 \(E\) 满足 (LS)。

这里的前提“\(E\) 在 \(Q\) 上可实现”严格指：存在某个 \(D\to Q\)，使 \(E\) 在 \(H\) 上与
\(H\times_QD\) **等变同构**，并且 \(H\times_QD\) 上的作用为
\(\gamma\cdot(x,d)=(h_\gamma x,d)\)。仅有一个普通的层同构而作用不同，不构成本义下的实现。

必要性：若 \(E\cong H\times_QD\) 且 \(\gamma\cdot(x,d)=(h_\gamma x,d)\)，则在 \(h_\gamma x=x\) 时，作用在整根 \(E_x(U)\) 上都是恒等。

充分性：令

\[
d:E\longrightarrow D:=E/\Gamma
\]

为作用商。映射 \(q\pi:E\to Q\) 在 \(\Gamma\)-作用下不变，故过 \(d\)，记为 \(\bar\pi:D\to Q\)。构造

\[
\kappa:E\longrightarrow H\times_QD,
\qquad \kappa(e)=(\pi(e),[e]).
\tag{3.4}
\]

先证单。若 \(\kappa(u)=\kappa(v)\)，则 \(\pi(u)=\pi(v)=:x\) 且 \([u]=[v]\)。由引理 0.1，局部有 \(v|_{U_i}=a_{\gamma_i}u|_{U_i}\)。比较基映射，

\[
x|_{U_i}=\pi(v|_{U_i})=h_{\gamma_i}x|_{U_i}.
\]

由 (LS)，\(a_{\gamma_i}\) 在 \(E_x(U_i)\) 上恒等，故 \(v|_{U_i}=u|_{U_i}\)。有限覆盖后由分离性得 \(u=v\)。

再证局部满。任取 \((x,d)\in(H\times_QD)(U)\)。由 \(d:E\to D\) 局部满，局部取 \(e_i\in E(U_i)\) 提升 \(d|_{U_i}\)。因为 \(q\pi(e_i)=qx|_{U_i}\)，再细一层有限覆盖后可取 \(\gamma_i\)，使

\[
\pi(e_i)=h_{\gamma_i}x|_{U_i}.
\]

于是 \(a_{\gamma_i^{-1}}e_i\) 有基映射 \(x|_{U_i}\)，且商到 \(D\) 后仍为 \(d|_{U_i}\)。故每个目标截面局部提升。于是 \(\kappa\) 单且局部满，从而是同构：

\[
E\cong H\times_Q(E/\Gamma),
\tag{3.5}
\]

且作用只改变 \(H\) 坐标。证毕。

因此任何实现的下降对象必典范地取为 \(E/\Gamma\)。不预选 \(D\) 不会漏掉其他实现。

### S3.3 所有实现与态射

令 \(\operatorname{Eq}(H)\) 为所有覆盖 \(H\) 并带 \(\Gamma\)-作用的对象，\(\operatorname{Real}_Q\) 为其中满足 (LS) 的全子范畴。定义

\[
\Phi_Q:\mathbf C/Q\longrightarrow\operatorname{Real}_Q,
\]

\[
D\longmapsto
\left(
H\times_QD\to H,\quad
\gamma\cdot(x,d)=(h_\gamma x,d)
\right).
\tag{3.6}
\]

由定理 3.1，\(\Phi_Q\) 本质满；拟逆为 \(E\mapsto E/\Gamma\)。所以

\[
\Phi_Q:\mathbf C/Q\xrightarrow{\ \simeq\ }\operatorname{Real}_Q
\tag{3.7}
\]

是范畴等价，并且

\[
\boxed{
\operatorname{Hom}_{\mathbf C/Q}(D_1,D_2)
\cong
\operatorname{Hom}^{\Gamma}_{\operatorname{Eq}(H)}
(H\times_QD_1,H\times_QD_2).
}
\tag{3.8}
\]

从一个切片映射 \(f:D_1\to D_2\) 给出 \(\operatorname{id}_H\times f\)。反过来，对任一等变态射，其第二坐标只沿 \(H\)-纤维局部不变；由 \(q:H\to Q\) 的有效商性质，这些局部资料下降为唯一的 \(f:D_1\to D_2\)。

固定可实现 \(E\)，令 \(D_E=E/\Gamma\)。这里 \(D_E	o Q\) 本身只是下降对象，并不处在上面的等变切片 \(\mathbf C/H\) 中；它也是后续所有实现的共同基底。一个实现是一个切片同构

\[
\theta:H\times_QD\xrightarrow{\ \sim\ }E.
\]

商掉 \(\Gamma\) 得到 \(D\cong D_E\)。所以所有实现中的下降对象在典范意义下同一；任意两个实现相差一个 \(\operatorname{Aut}_{\mathbf C/Q}(D_E)\)-自同构。固定 \(E\) 的实现范畴非空、连通，并等价于以自同构群

\[
\operatorname{Aut}^{\Gamma}_{\operatorname{Eq}(H)}(E)
\cong
\operatorname{Aut}_{\mathbf C/Q}(D_E)
\tag{3.9}
\]

为唯一对象自同构群的单对象群胚。它的所有对象都典范同构于 \(D_E\)，因此非空且连通；不能把它误称为“可缩”，因为一般 \(\operatorname{Aut}(D_E)\) 可以非平凡。

若把固定对象的全部实现按“实现之间的同构”取群胚，所得正是上述单对象群胚。若把实现只按“是否存在”看待，则当然只剩真值；上面的群胚计法保留了实现之间的自同构信息。

### S3.4 任意基底及拉回

固定任意切片 \(f:B\to Q\)，令

\[
H_B=H\times_QB,\qquad q_B:H_B\to B.
\tag{3.10}
\]

在切片 topos 中，群作用商与拉回交换，故

\[
\Gamma\times H_B\rightrightarrows H_B\longrightarrow B
\]

就是 \(H_B\) 的 \(\Gamma\)-商。定义 \(\operatorname{Eq}_B(H_B)\) 为覆盖 \(H_B\) 的等变对象，\(\mathrm{LS}_B\) 为对应的逐局部稳定子恒等条件。令 \(\operatorname{Real}_B\) 为满足它的全子范畴。与定理 3.1 完全相同的证明给出

\[
\Phi_B:\mathbf C/B\xrightarrow{\ \simeq\ }\operatorname{Real}_B,
\qquad
D\mapsto H_B\times_BD,
\tag{3.11}
\]

以及

\[
\operatorname{Hom}_{\mathbf C/B}(D_1,D_2)
\cong
\operatorname{Hom}^{\Gamma}_{\operatorname{Eq}_B(H_B)}
(H_B\times_BD_1,H_B\times_BD_2).
\tag{3.12}
\]

若 \(f:B'\to B\) 是切片映射，记 \(f_H:H_{B'}\to H_B\)。则对任意 \(D\) 及等变 \(E\to H_B\)，

\[
f_H^*(H_B\times_BD)
\cong H_{B'}\times_{B'}f^*D,
\tag{3.13}
\]

并且

\[
f_H^*(E/\Gamma)\cong(f_H^*E)/\Gamma.
\tag{3.14}
\]

故实现、态射、下降对象及自同构群都与基底拉回相容。若 \(E\) 满足 \(\mathrm{LS}_B\)，其拉回自动满足 \(\mathrm{LS}_{B'}\)。式 (3.13) 本身只给出正向保持；反向反射需要 S5、S6 讨论的附加条件。


---

## S4 单点上的检验

结论：**不充分。** 条件只检查 \(U=*\) 的整体截面，不能控制一般测试对象上的局部截面。

令

\[
T=*,\qquad \Gamma=\{1,\sigma\}\cong C_2,
\]

其中 \(\sigma\) 在唯一的点上作用平凡。因此

\[
H=h_*=*,\qquad Q=*.
\]

在 \(Q=*\) 上的实现就是存在层同构 \(\theta:E\cong D\)，且 \(\theta a_\sigma\theta^{-1}\) 等于 \(D\) 上的平凡作用；因此 \(a_\sigma\) 必须本身为恒等。

令 \(K=\{0,1\}^{\mathbb N}\) 为 Cantor 空间，并令

\[
\phi:K\to K,\qquad
\phi(x_0,x_1,x_2,\ldots)
=(1-x_0,x_1,x_2,\ldots).
\tag{4.1}
\]

这里 \(\phi\) 是无不动点的对合同胚。记 \(\underline K\) 为常层，\(h_K\) 为可表示层。令

\[
i:\underline K\hookrightarrow h_K
\]

是把 \(k\) 送到常数映射 \(k\) 的子层包含，再令 \(j=\phi i\)。定义

\[
E:=\operatorname{coeq}(i,j:\underline K\rightrightarrows h_K).
\tag{4.2}
\]

直观而言，\(E\) 把每根局部常值截面 \(s\) 与 \(\phi s\) 等同。以下只使用这个商映射的局部满性以及生成关系来自 \(\underline K\)；这两件事由层余等化子的构造直接保证。

映射

\[
\tau:h_K\to h_K,\qquad\tau(f)=\phi\circ f
\]

满足 \(\tau i=j\)、\(\tau j=i\)、\(\tau^2=\operatorname{id}\)。这里不能只引用余等化子的普通泛性质（那通常要求 \(\tau i=\tau j\)）；要使用的是商是有效等价关系这一更强事实。令 \(R\subset h_K\times h_K\) 为由关系 \((i(x),j(x))\) 生成的内部等价关系。\(\tau\) 把生成子
\((i(x),j(x))\) 送到 \((j(x),i(x))\)，故 \(\tau(R)=R\)。于是 \(\tau\) 下降为商
\(E=h_K/R\) 上的自同构：

\[
a_\sigma:E\to E,\qquad a_\sigma^2=\operatorname{id}.
\]

因为 \(T=*\) 是终对象，唯一的投影 \(\pi:E\to*\) 自动满足等变性。

### S4.1 条件在 \(E(*)\) 上成立

任取 \(e\in E(*)\)。商 \(q:h_K\to E\) 局部满，故 \(e\) 在某个非空测试对象 \(V\) 上提升为 \(f:V\to K\)。取点 \(v:*\to V\)，便有

\[
e=q(f(v))=q(f(v)(*)).
\]

故 \(e\) 是某个常数 \(k\in K\) 的类。常数层已经在余等化子中给出 \(k\sim\phi(k)\)，所以

\[
a_\sigma([k])=[\phi(k)]=[k]\qquad(k\in K).
\tag{4.3}
\]

于是对 \(E(*)\) 中的每个截面 \(e\)，尽管 \(\gamma\pi(e)=\pi(e)\) 自动成立，仍有 \(a_\sigma(e)=e\)。S4 的假设成立。

### S4.2 局部截面显示不可实现

下面的证明使用生成关系来自常层这一事实。把 \(\Gamma\)-作用为平凡作用的离散集 \(K\) 作为常层 \(\underline K\)，则 \(\phi\) 定义从 \(\underline K\) 到自身的置换。底部关系只是
\(\{(\phi^j s,s):s\in\underline K(U),\ j\in\{0,1\}\}\)。

取 \(s\in h_K(U)\)。若它在 \(U\) 的某个有限覆盖的每一块上都是局部常值，那么每块上都可以沿上述生成关系移动；沿覆盖粘接，得到 \(q(s)=q(\phi s)\)。

反过来，若层化后 \(q(s)=q(\phi s)\)，取这个等式的一个见证：在 \(U\) 的某个有限覆盖 \(\{p_i:U_i\to U\}\) 上，各块限制的预层类相同。若 \(s|_{U_i}\) 不是局部常值，则它不属于生成关系 \(i,j\) 的源或目标，因为两端都必须经过常层 \(\underline K\)。因此它在单块 \(U_i\) 的预层余等化子中沿不了任何非平凡关系。层化只把已经逐块相容的预层截面粘成整体截面；它不会在某一单块上新增关系。故 \(s|_{U_i}\) 必须局部常值。按块重新细分即得下面的判据：

\[
q(s)=q(\phi s)\text{ 在 }E(U)
\Longleftrightarrow
\text{存在 }U\text{ 的有限覆盖，使每块上的 }s\text{ 都是局部常值}.
\tag{4.3'}
\]

令

\[
[\operatorname{id}_K],[\phi]\in E(K)
\]

分别为恒等映射及其与 \(\phi\) 的复合在商中的类。显然

\[
a_\sigma([\operatorname{id}_K])=[\phi].
\tag{4.4}
\]

断言

\[
[\operatorname{id}_K]\ne[\phi]\qquad\text{在 }E(K)\text{ 中}.
\tag{4.5}
\]

按照 (4.3')，若
\(q(\operatorname{id}_K)=q(\phi)\)，则存在 \(K\) 的有限覆盖 \(\{U_i\to K\}\)，使每个限制 \(\operatorname{id}_K|_{U_i}\) 在某个更细的有限覆盖上是局部常值映射。于是每个

\[
\operatorname{id}_K|_{U_i}:U_i\to K
\]

在 \(U_i\) 的每块上局部常值。这些更细紧块覆盖 \(K\)，且每块上的恒等限制取有限像；有限多个有限像之并就是整个 \(K\)。所以 \(K\) 会是有限集；这和 Cantor 空间无限矛盾。于是 (4.5) 成立。

因此 \(a_\sigma\) 在局部截面 \([\operatorname{id}_K]\in E(K)\) 上非平凡。若 \(E\) 能在 \(Q=*\) 上实现，则它的作用必须平凡，矛盾。反例完成，S4 的条件不足。

---

## S5 局部满射的基底检验

结论：**必然可以。**

设 \(f:B\to Q\) 局部满，\(E_B=E\times_QB\) 是 \(H_B=H\times_QB\) 上的拉回等变对象。假定 \(E_B\) 在 \(B\) 上可实现，我们证明 \(E\) 满足 S3 的 (LS)。

取任意 \(U\)、\(x\in H(U)\)、\(\gamma\in\Gamma\)，设 \(h_\gamma x=x\)，再取 \(e\in E_x(U)\)。令 \(y=qx:U\to Q\)。因为 \(f\) 局部满，存在有限覆盖

\[
\{u_i:U_i\to U\}_{i=1}^m
\]

和截面 \(b_i\in B(U_i)\)，使

\[
fb_i=y|_{U_i}=qx|_{U_i}.
\]

把 \((x|_{U_i},b_i)\) 视为 \(H_B(U_i)\) 的截面 \(\widetilde x_i\)。于是

\[
\gamma\widetilde x_i=(h_\gamma x|_{U_i},b_i)=\widetilde x_i.
\]

\(E_B\) 满足 \(\mathrm{LS}_B\)，所以其作用在纤维

\[
(E_B)_{\widetilde x_i}(U_i)
\]

上恒等。截面 \(e|_{U_i}\) 沿 \(H_B\to H\) 拉回成为该纤维的元素；拉回纤维与 \(E_x(U_i)\) 典范同构，且同构与群作用相容。因此

\[
a_\gamma(e|_{U_i})=e|_{U_i}\qquad(i=1,\ldots,m).
\]

层的分离性给出 \(a_\gamma(e)=e\)。\(x,\gamma,e\) 任意，故 \(E\) 满足 (LS)。由定理 3.1，\(E\) 在 \(Q\) 上可实现。

与 S3.4 的拉回相容性（原实现必推出拉回实现）合并，得到

\[
\boxed{
E\text{ 在 }Q\text{ 上可实现}
\iff
E\times_QB\text{ 在 }B\text{ 上可实现}.
}
\tag{5.1}
\]

---

## S6 非空基底与全局结论

结论：**不必反映。** 仅要求 \(B\) 非空、可表示以及 \(B\to Q\) 存在，不足以从拉回实现推出原对象实现。关键差别是该映射是否在层拓扑下局部满。

### S6.1 完整反例

令

\[
\Gamma=\{1,\sigma\}\cong C_2,
\qquad T=\{a,b,p\},
\]

作用为

\[
\sigma a=b,\qquad\sigma b=a,\qquad\sigma p=p.
\]

则 \(T\) 有两个轨道

\[
O_0=\{a,b\}\cong\Gamma,
\qquad O_1=\{p\}\cong\Gamma/\Gamma,
\]

商空间为

\[
Q=T/\Gamma=\{q_0,q_1\},
\qquad q_0=O_0,\quad q_1=O_1.
\]

取有限 \(\Gamma\)-集

\[
X=\{\widetilde a,\widetilde b,u,v\}
\]

及作用

\[
\sigma\widetilde a=\widetilde b,\quad
\sigma\widetilde b=\widetilde a,\quad
\sigma u=v,\quad
\sigma v=u.
\]

定义等变映射 \(f:X\to T\) 为

\[
f(\widetilde a)=a,\quad f(\widetilde b)=b,\quad
f(u)=f(v)=p.
\]

令

\[
E:=h_X\longrightarrow h_T=H.
\]

在固定点 \(p\) 处，稳定子 \(\Gamma_p=\Gamma\) 在纤维 \(X_p=\{u,v\}\) 上交换两点，作用非平凡。由 S2 的判据 (2.4)，\(E\) 不能在 \(Q\) 上实现。

现在取

\[
B=h_*=*,
\qquad
\beta:B\to Q=h_{\{q_0,q_1\}}
\]

为在唯一点处取值为 \(q_0\) 的态射。\(B\) 显然非空且可表示。因为 \(Q\) 是有限离散集，

\[
H_B=H\times_QB
\cong h_{T_{q_0}}
\cong h_{\{a,b\}},
\]

\[
E_B=E\times_QB
\cong h_{X_{q_0}}
\cong h_{\{\widetilde a,\widetilde b\}}.
\]

映射 \(X_{q_0}\to T_{q_0}\) 是等变双射，并且 \(\Gamma\) 在两边都是正则作用。因此

\[
E_B\cong H_B
\]

在 \(H_B\) 上等变。等价地，\(E_B\cong H_B\times_B\mathbf 1_B\)，其中 \(\mathbf 1_B\) 是切片 \(\mathbf C/B\) 的终对象。所以 \(E_B\) 在 \(B\) 上实现。

但 \(E\) 本身不能在 \(Q\) 上实现，故拉回可实现不反映原 \(E\) 可实现。这里 \(\beta\) 不是局部满射：它只取 \(q_0\)，不覆盖 \(q_1\)，因此不触发 S5 的双向检验。

### S6.2 全局检验原则

由前述结果可整理出以下可核查原则。

1. **通用充要判据。** 先构造

   \[
   Q=\operatorname{coeq}(\Gamma\times H\rightrightarrows H),
   \]

   然后在每个测试对象 \(U\)、每个局部基截面 \(x\in H(U)\) 上检查

   \[
   h_\gamma x=x\Longrightarrow
   a_\gamma|_{E_x(U)}=\operatorname{id}.
   \]

   它既充分又必要，见定理 3.1。

2. **单点整体截面不够。** 只检查 \(E(*)\) 不控制测试对象上的局部截面，S4 给出完整反例。

3. **有限可表示情形用轨道-稳定子。** 对有限 \(X\to T\)，选 \(t_i\) 和 \(K_i=\Gamma_{t_i}\)，把 \(X\) 分解为 \(X_i\cong\Gamma\times_{K_i}S_i\)。可实现当且仅当每个 \(K_i\) 在 \(S_i\) 上平凡。等变自同构群是 \(\prod_i\operatorname{Sym}(S_i)\)。

4. **局部满基底可双向检验。** 若 \(B\to Q\) 局部满，则拉回可实现与原可实现等价。因此可以取覆盖 \(B\to Q\) 做局部检验；正反结果都能退回全局。

5. **任意基底只有单向保持。** 对任意 \(B\to Q\)，原 \(E\) 可实现必然推出 \(E\times_QB\) 可实现；反向一般失败。若某个拉回不可实现，可以断定原 \(E\) 不可实现；但拉回成功只有在另证基底映射局部满时才能推出原实现。

6. **非空可表示基底的条件。** “\(B\) 非空”只说明它至少看见 \(Q\) 的一个点或局部区域；并不保证看见稳定子出现的重要区域。S6 的 \(h_*\to Q\) 就是最小反例。

  若 \(Q\) 有限离散、\(B=h_S\)，且 \(S\to Q\) 将每个 \(Q\)-点都取到，则它局部满；若漏掉某个 \(q\in Q\)，则不是。因此在这种可表示情形下，双向检验恰可归纳为：这个基底是否在层拓扑意义下覆盖整个 \(Q\)。

---

## 保留、新增/修正与自评

**保留。** S1 的自由作用轨道商、层商及 torsor 下降；S2 的有限轨道-稳定子分类、可实现判据和等变自同构群；S3 的逐局部稳定子充要判据及基底分类；S4 的层余等化子反例；S5 的局部满基底双向检验；S6 的非空可表示但不覆盖的基底反例。以上主结论均经重新核验后保留。

**新增/完善。** 在第 0 节增加了适用于任意 \(U\)-小离散群的商同余引理，并在共同设定中用以统一 S1、S3、S5 的局部提升论证；S3 明确给出了实现范畴与 \(\mathbf C/Q\) 的等价、实现对象之间的唯一性结论，以及任意基底拉回下的自然相容式。S6 还给出了有限离散商上可表示基底何时具备双向检验能力的判据。

**修正与补充。** 补入了层商同余关系的引理，明确只有在一个有限覆盖上才能把一个商中的等式提升为各局部群作用关系，避免把 \(Q(U)\) 错误等同于 \(H(U)/\Gamma\)。修正了历史稿中对固定实现的“可缩群胚”表述：应改为非空连通的群胚，其单个对象的自同构群是 \(\operatorname{Aut}(D_E)\)，可以非平凡。进一步写明了 S1、S3、S5 中每个有限覆盖的细化方向，以及 S2 自同构群只在可实现对象上计算的依据。S4 中的局部层余等化子也改用覆盖判据逐层核验，避免把不同测试对象上的粘接误当成一条全局作用关系。

**未完成或不确定部分。** 在原题 S1 至 S6 的要求范围内，没有发现阻塞性缺口。所有“当且仅当”均写明了双向证明；所有判断均有证明或完整反例；所有构造均核对了对象、态射及拉回性质。唯一需要依赖的标准事实已在第 0 节说明：有限极限、余等化子及群作用商的核对在 Grothendieck topos 中具有所用的有效性。与题面“只用共同设定”一致，S3–S6 中如果不特别说明，不再额外要求有限性；S1、S2 的有限性条件仅在各自阶段使用。

**自评。** 相对原题，数学内容完整且各阶段结论已闭合，基线记为 **B2**。历史稿中的一个群胚术语错误已经修正，没有保留已知错误断言。研究等级方面，本稿在共同设定的全范围（任意 \(U\)-小离散群、任意 \(T\)、任意切片基底 \(B\to Q\)）内完成了可实现对象与下降对象的等价及双向桥接，并闭环说明了局部满与非满基底检验的差别。按题面“完整解决原题未要求的一项新问题”的锚点，**R=3、B=2**；这是本人有依据的档位判断，最终评级仍以按标准审阅为准。



