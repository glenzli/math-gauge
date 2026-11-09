以下始终在 \(\mathbf C=\mathbf{Sh}(\mathbf{Prof}_U;\mathbf{Set}_V)\) 中取纤维积；终对象记为 \(*\)。对 \(x\in H(U)=\operatorname{Hom}(U,T)\)，记
\[
E_x(U):=\{e\in E(U):\pi_U(e)=x\}.
\]
“作用”均指群同态 \(\Gamma\to \operatorname{Aut}_{\mathbf C/H}(E)\)。

---

## S1 有限群的自由作用

设 \(\Gamma\) 有限，且在 profinite 空间 \(T\) 上自由作用。

### 1. 构造 \(T/\Gamma\)

令
\[
q:T\longrightarrow T/\Gamma
\]
为轨道集合上的商映射，赋予商拓扑。断言 \(T/\Gamma\in \mathbf{Prof}_U\)，且 \(q\) 是有限覆盖。

事实上，对任意 \(t\in T\)，因为 \(\Gamma\) 有限且作用自由，可取 clopen 邻域 \(U_t\ni t\)，使得诸 \(\gamma U_t\;(\gamma\in\Gamma)\) 两两不交：先分开有限集 \(\Gamma t\)，再利用作用连续性缩小成 clopen 邻域即可。于是
\[
q^{-1}q(U_t)=\coprod_{\gamma\in\Gamma}\gamma U_t,
\]
且 \(q|_{U_t}:U_t\to q(U_t)\) 是紧空间到 Hausdorff 空间的双连续双射，从而是同胚；\(q(U_t)\) 为 clopen。因此 \(T/\Gamma\) 有 clopen 基，是紧 Hausdorff 全不连通空间，即 profinite。又 \(q\) 的每个纤维就是一个有限轨道，故 \(q\) 是有限覆盖。并且有自然同胚
\[
T\times_{T/\Gamma}T\cong T\times\Gamma,\qquad
(t,\gamma)\longmapsto (t,\gamma t).
\tag{1.1}
\]

### 2. \(h_{T/\Gamma}\) 是层商

记 \(Q=T/\Gamma,\ H=h_T\)。对任意层 \(Y\)，利用 \(q:T\to Q\) 这个覆盖及层公理，
\[
Y(Q)\cong \operatorname{Eq}\bigl(Y(T)\rightrightarrows Y(T\times_QT)\bigr).
\]
由 (1.1)，右端是
\[
\{s\in Y(T):Y(h_\gamma)(s)=s\ \ \forall\gamma\in\Gamma\}
=Y(T)^\Gamma .
\]
由 Yoneda，
\[
\operatorname{Hom}_{\mathbf C}(h_Q,Y)
\cong Y(Q)
\cong Y(T)^\Gamma
\cong \operatorname{Hom}_{\mathbf C}(H,Y)^\Gamma .
\]
故 \(h_Q\) 表示 \(H\) 关于 \(\Gamma\) 的层余等化子；等价地，
\[
h_Q\cong \operatorname{coeq}\Bigl(\coprod_{\gamma\in\Gamma}H
\rightrightarrows H\Bigr),
\qquad
H=h_T.
\]
特别地，\(h_q:H\to h_Q=h_{T/\Gamma}\) 是层商映射。

### 3. 任何等变层都在 \(Q=T/\Gamma\) 上实现

设 \(E\to H\) 带等变作用 \(a_\gamma\)。令
\[
D:=E/\Gamma
\]
为 \(\mathbf C\) 中群作用的余等化子，即层商；因为
\[
q\pi a_\gamma=q h_\gamma\pi=q\pi,
\]
映射 \(q\pi:E\to Q\) 过 \(D\)，得到 \(\bar\pi:D\to Q\)。于是可作典范映射
\[
\kappa:E\longrightarrow H\times_QD,\qquad
e\longmapsto \bigl(\pi(e),[e]\bigr).
\tag{1.2}
\]
它覆盖 \(H\)，且对 \(\gamma\in\Gamma\)，
\[
\kappa(a_\gamma e)
=\bigl(h_\gamma\pi(e),[e]\bigr).
\]
另一方面，\(H\times_QD\) 上的作用取为只改变 \(H\)-坐标：
\[
\gamma\cdot(h,d)=(h_\gamma h,d).
\]
因此若 \(\kappa\) 为同构，就得到所要求的实现。

先证 \(\kappa\) 是单射。若 \(\kappa(u)=\kappa(v)\)，则 \(\pi(u)=\pi(v)=:x\)，且 \([u]=[v]\in D\)。群作用商的基本性质给出：存在有限覆盖 \(\{U_i\to U\}\) 及 \(\gamma_i\in\Gamma\)，使
\[
v|_{U_i}=a_{\gamma_i}(u|_{U_i}).
\]
但
\[
x=\pi(v|_{U_i})=h_{\gamma_i}\pi(u|_{U_i})=h_{\gamma_i}x|_{U_i}.
\]
由于 \(T\) 上作用自由，逐点得到 \(\gamma_i=e\)。故 \(v|_{U_i}=u|_{U_i}\)，覆盖后 \(u=v\)。

再证 \(\kappa\) 局部满。任取 \(s\in (H\times_QD)(U)\)，写 \(s=(x,d)\)，其中 \(x:U\to H,\ d:U\to D\)，且二者在 \(Q\) 中同像。因 \(E\to D\) 局部满，有有限覆盖 \(\{U_i\to U\}\) 及 \(e_i\in E(U_i)\) 提升 \(d|_{U_i}\)。又因 \(Q=H/\Gamma\)，\(x|_{U_i}\) 与 \(\pi(e_i)\) 在 \(Q\) 中同像，故再细覆盖后有 \(\gamma_i\) 使
\[
\pi(e_i)=h_{\gamma_i}x|_{U_i}.
\]
于是 \(a_{\gamma_i^{-1}}e_i\) 覆盖 \(x|_{U_i}\)，且与 \(e_i\) 在 \(D\) 中同类，故局部提升 \(s\)。所以 \(\kappa\) 局部满。

因 \(\mathbf C\) 是 topos，单态射且局部满射即为同构。因此
\[
E\cong H\times_QD
\]
且右端作用只改变 \(H\)-坐标。证毕。

---

## S2 有限集合上的纤维分类

设 \(\Gamma,T\) 有限。取 \(T\) 的轨道代表
\[
T=\coprod_{i=1}^r O_i,\qquad
O_i=\Gamma t_i,\qquad
K_i:=\Gamma_{t_i}.
\]
于是 \(O_i\simeq \Gamma/K_i\)。设 \(X\) 为有限 \(\Gamma\)-集，且有等变映射 \(f:X\to T\)。

### 1. 分类 \(X\to T\)

对每个 \(i\)，令
\[
X_i:=f^{-1}(O_i),\qquad S_i:=X_{t_i}=f^{-1}(t_i).
\]
则 \(S_i\) 是有限 \(K_i\)-集，并且
\[
X_i\cong \Gamma\times_{K_i}S_i,
\qquad
[\gamma,s]\longmapsto \gamma s.
\tag{2.1}
\]
反之，任意有限 \(K_i\)-集 \(S_i\) 都给出
\[
\Gamma\times_{K_i}S_i\longrightarrow \Gamma/K_i\simeq O_i,
\]
从而给出 \(X\to T\)。所以
\[
\bigl\{\,X\to T\text{ 等变}\,\bigr\}
\;\simeq\;
\prod_{i=1}^r\{\text{有限 }K_i\text{-集 }S_i\}.
\tag{2.2}
\]

更明确地，给定 \(X\to T\) 与 \(Y\to T\)，其等变态射不能混合不同的 \(T\)-轨道，且由 \(t_i\)-纤维上的 \(K_i\)-等变映射唯一决定：
\[
\operatorname{Hom}^{\Gamma}_T(X,Y)
\cong
\prod_i\operatorname{Hom}_{K_i}(S_i,R_i),
\qquad
S_i=X_{t_i},\ R_i=Y_{t_i}.
\tag{2.3}
\]
这就是全部对象与态射的分类。

### 2. \(h_X\) 在 \(Q=h_{T/\Gamma}\) 上可实现的充要条件

令
\[
Q:=T/\Gamma.
\]
则 \(h_X\) 可在 \(Q\) 上实现，当且仅当
\[
\boxed{\quad
\forall i,\quad K_i\text{ 在 }S_i=X_{t_i}\text{ 上作用平凡.}
\quad}
\tag{2.4}
\]
等价地，
\[
\boxed{\quad
\forall x\in X,\qquad
\Gamma_x=\Gamma_{f(x)}.
\quad}
\tag{2.5}
\]
也等价于存在有限集 \(S\to Q\)，使
\[
X\cong T\times_QS
\quad\text{over }T.
\tag{2.6}
\]
此时可取
\[
S=X/\Gamma
\]
以及
\[
D=h_{X/\Gamma},
\qquad
h_X\cong h_T\times_{h_Q}h_{X/\Gamma}.
\]

必要性：若 \(h_X\cong h_T\times_QD\)，则在任意固定点 \(t\in T\) 处，\(\gamma\in\Gamma_t\) 只作用在 \(h_T\)-坐标上，而 \(h_\gamma\) 固定该点，故它在纤维 \(X_t\) 上作用平凡。取 \(t=t_i\) 得 \(K_i\) 在 \(S_i\) 上平凡。

充分性：若 \(K_i\) 在 \(S_i\) 上平凡，则
\[
X_i\cong (\Gamma/K_i)\times S_i
\]
且 \(\Gamma\) 只作用在第一个因子。于是
\[
X\cong T\times_Q(X/\Gamma),
\]
所以取 \(D=h_{X/\Gamma}\) 即得实现。

### 3. 可实现对象的自同构群

若 (2.4) 成立，则在等变切片中
\[
\boxed{
\operatorname{Aut}_{\mathbf C/H}^{\Gamma}(h_X)
\cong
\prod_{i=1}^r \operatorname{Sym}(S_i)
\cong
\prod_{i=1}^r \mathfrak S_{|S_i|}.
}
\tag{2.7}
\]
理由：在 \(X_i\cong(\Gamma/K_i)\times S_i\) 上，一个保持轨道基点的 \(\Gamma\)-等变自同构只能在整个 \(\Gamma/K_i\)-因子上取同一个 \(S_i\)-置换；因为 \(\Gamma\) 在底轨道上传递。

等价地，实现对象 \(D=h_{X/\Gamma}\) 在 \(\mathbf C/Q\) 中的自同构群也是
\[
\operatorname{Aut}_{\mathbf C/Q}(D)
\cong\prod_i\operatorname{Sym}(S_i).
\]
若忽略等变性而只看 \(h_X\) 在 \(\mathbf C/h_T\) 中的自同构，则为
\[
\prod_{t\in T}\operatorname{Sym}(X_t).
\]
这与上面的等变自同构群不同；本阶段按等变范畴计算，结论为 (2.7)。

---

## S3 一般层的完整下降

### 1. 构造层 \(Q\) 与不变映射 \(q:H\to Q\)

令 \(H=h_T\)。在 \(\mathbf C\) 中定义
\[
Q:=\operatorname{coeq}\left(
\coprod_{\gamma\in\Gamma}H
\rightrightarrows H
\right),
\tag{3.1}
\]
其中一个映射在第 \(\gamma\)-分量上为 \(h_\gamma:H\to H\)，另一个为恒等映射。等价地，先取预层
\[
P(U):=H(U)/\Gamma=\operatorname{Hom}(U,T)/\Gamma
\]
的逐点轨道商，再令
\[
Q:=P^\#.
\]
令
\[
q:H\longrightarrow Q
\]
为典范商映射。则 \(q h_\gamma=q\)，且对任意层 \(Y\)，
\[
\begin{aligned}
\operatorname{Hom}_{\mathbf C}(Q,Y)
&\cong
\operatorname{Eq}\left(
\operatorname{Hom}(H,Y)
\rightrightarrows
\prod_{\gamma\in\Gamma}\operatorname{Hom}(H,Y)
\right)\\
&\cong
\{\,f:H\to Y:\ f\circ h_\gamma=f\ \ \forall\gamma\in\Gamma\,\}\\
&=\operatorname{Hom}_{\mathbf C}(H,Y)^\Gamma.
\end{aligned}
\tag{3.2}
\]
这里 \(\Gamma\) 在 \(\operatorname{Hom}(H,Y)\) 上通过预复合作用。故 (3.2) 就是所求的自然同构。由预层轨道商经层化得到的描述还直接看出：\(q\) 在通常意义下局部满射，即 \(q\) 是覆盖。

### 2. 不预选 \(D\) 的可实现性判据

对等变对象 \(E\to H\)，定义以下条件：

\[
\boxed{
\begin{array}{l}
(T)\quad\text{对每个测试对象 }U,\ \text{每个 }x\in H(U)
=\operatorname{Hom}(U,T),\ \text{每个 }\gamma\in\Gamma,\\
\text{若 }h_\gamma x=x,\text{ 则 }a_\gamma\text{ 在纤维 }
E_x(U)\text{ 上为恒等映射.}
\end{array}}
\tag{3.3}
\]

也就是说，稳定子必须在所有局部截面上平凡作用。

**定理 3.1.** \(E\) 可在 \(Q\) 上实现，当且仅当 (T) 成立。

**证明.**

必要性是显然的：若 \(E\cong H\times_QD\)，且作用只改变 \(H\)-坐标，则当 \(h_\gamma x=x\) 时，
\[
a_\gamma(x,d)=(x,d).
\]

充分性：仍然定义
\[
D:=E/\Gamma
\]
为群作用的层余等化子，并令 \(d:E\to D\) 为商映射。由于 \(q\pi:E\to Q\) 在 \(\Gamma\)-作用下不变，它过 \(D\)，得到 \(\bar\pi:D\to Q\)。作典范映射
\[
\kappa:E\longrightarrow H\times_QD,\qquad
e\longmapsto(\pi(e),[e]).
\tag{3.4}
\]

我们证明 \(\kappa\) 为同构。

首先，群作用商的基本局部刻画是：
\[
d(u)=d(v)
\iff
\text{有有限覆盖 }\{U_i\to U\}\text{ 及 }\gamma_i
\text{ 使 }v|_{U_i}=a_{\gamma_i}(u|_{U_i}).
\tag{3.5}
\]
若 \(\kappa(u)=\kappa(v)\)，则 \(\pi(u)=\pi(v)=x\)，且由 (3.5) 局部有 \(v=a_\gamma u\)。于是
\[
x=\pi(v)=h_\gamma x.
\]
由 (T)，\(a_\gamma\) 在 \(E_x\) 上为恒等，故局部 \(u=v\)，覆盖后 \(u=v\)。因此 \(\kappa\) 是单态射。

再看局部满性。任取 \(s\in(H\times_QD)(U)\)，写 \(s=(x,d)\)。因 \(E\to D\) 局部满，取有限覆盖 \(\{U_i\to U\}\) 及 \(e_i\in E(U_i)\) 提升 \(d|_{U_i}\)。又因 \(Q=H/\Gamma\)，\(x|_{U_i}\) 与 \(\pi(e_i)\) 在 \(Q\) 中同像；再细覆盖后有 \(\gamma_i\) 使
\[
\pi(e_i)=h_{\gamma_i}x|_{U_i}.
\]
则 \(a_{\gamma_i^{-1}}e_i\) 覆盖 \(x|_{U_i}\)，且其 \(D\)-类仍为 \(d|_{U_i}\)。故 \(s\) 局部来自 \(E\)。所以 \(\kappa\) 局部满。\(\mathbf C\) 为 topos，单且局部满的态射为同构，故
\[
E\cong H\times_QD.
\]

于是 (T) 充分。证毕。\(\square\)

此外，若 \(E\) 可实现，则其唯一（在典范同构意义下）的下降对象就是 \(D=E/\Gamma\)。

### 3. 所有实现及态射的分类

令
\[
\operatorname{Eq}(H):=
\{\,E\to H\text{ 带 }\Gamma\text{-作用，且覆盖 }H\text{ 上的 }\Gamma\text{-作用}\,\}.
\]
定义
\[
\operatorname{Real}_Q:=
\{\,E\in\operatorname{Eq}(H):\ E\text{ 满足 (T)}\,\}.
\]
则有范畴等价
\[
\Phi_Q:\mathbf C/Q\longrightarrow \operatorname{Real}_Q,\qquad
D\longmapsto \bigl(H\times_QD\to H\bigr),
\tag{3.6}
\]
其中作用为
\[
\gamma\cdot(h,d)=(h_\gamma h,d).
\]
其拟逆为
\[
E\longmapsto E/\Gamma.
\]
并且对 \(D_1,D_2\in\mathbf C/Q\)，
\[
\boxed{
\operatorname{Hom}_{\mathbf C/Q}(D_1,D_2)
\cong
\operatorname{Hom}_{\operatorname{Eq}(H)}
(H\times_QD_1,H\times_QD_2).
}
\tag{3.7}
\]
满性来自 \((H\times_QD_1)/\Gamma\cong D_1\)；单性来自 \(q:H\to Q\) 局部满。

对固定的 \(E\in\operatorname{Real}_Q\)，令
\[
D_E:=E/\Gamma.
\]
典范映射
\[
\theta_E:H\times_QD_E\longrightarrow E
\]
是 \(E\) 的一个实现。任意其它实现
\[
\theta:H\times_QD\xrightarrow{\ \sim\ }E
\]
都通过商掉 \(\Gamma\) 给出唯一的同构
\[
D\xrightarrow{\ \sim\ }D_E,
\]
使 \(\theta\) 与 \(\theta_E\) 相应。因此固定 \(E\) 的实现范畴是可缩群胚；特别地
\[
\operatorname{Aut}_{\operatorname{Eq}(H)}(E)
\cong
\operatorname{Aut}_{\mathbf C/Q}(D_E).
\tag{3.8}
\]

### 4. 任意基底 \(B\to Q\) 及与拉回的相容性

固定任意层 \(B\to Q\)，令
\[
H_B:=H\times_QB,
\qquad
q_B:H_B\to B.
\tag{3.9}
\]
因为拉回沿 \(B\to Q\) 保持余等化子，\(\Gamma\times H\rightrightarrows H\to Q\) 拉回后给出
\[
\Gamma\times H_B\rightrightarrows H_B\longrightarrow B,
\]
故 \(q_B\) 正是 \(H_B\) 关于 \(\Gamma\) 的层商。

在切片 \(\mathbf C/B\) 中，仍定义
\[
\operatorname{Eq}_B(H_B):=
\{\,E\to H_B\text{ 带覆盖 }H_B\text{ 上作用的 }\Gamma\text{-作用}\,\},
\]
以及局部稳定子条件 (T\(_B\))：对每个 \(x\in H_B(U)\) 和 \(\gamma\in\Gamma\)，若 \(\gamma x=x\)，则 \(a_\gamma\) 在 \(E_x(U)\) 上为恒等。令
\[
\operatorname{Real}_B
\]
为该条件成立的对象构成的全子范畴。与 (3.6) 完全相同的论证给出范畴等价
\[
\boxed{
\Phi_B:\mathbf C/B\longrightarrow \operatorname{Real}_B,
\qquad
D\longmapsto H_B\times_BD,
}
\tag{3.10}
\]
作用只改变 \(H_B\)-坐标。拟逆为
\[
E\longmapsto E/\Gamma.
\]
特别地，
\[
\operatorname{Hom}_{\mathbf C/B}(D_1,D_2)
\cong
\operatorname{Hom}_{\operatorname{Eq}_B(H_B)}
(H_B\times_BD_1,H_B\times_BD_2).
\tag{3.11}
\]

若 \(f:B'\to B\) 是切片中的态射，令
\[
f_H:H_{B'}=H_B\times_BB'\longrightarrow H_B .
\]
则拉回与实现函子相容：
\[
\boxed{
f_H^*\bigl(H_B\times_BD\bigr)
\cong
H_{B'}\times_{B'}f^*D,
}
\tag{3.12}
\]
并且
\[
\boxed{
f_H^*(E/\Gamma)
\cong
(f_H^*E)/\Gamma.
}
\tag{3.13}
\]
因此 (T\(_B\)) 拉回后给出 (T\(_{B'}\))；实现、态射、下降对象 \(D=E/\Gamma\) 以及自同构群都随基底拉回而相容。另一方面，式 (3.12) 只说明“实现可拉回”；拉回能否反过来反映实现，需要额外条件，见 S5、S6。

---

## S4 单点上的检验

结论：**不必然。** 条件只说每个整体截面 \(e\in E(*)\) 在稳定子下不动，不能控制所有局部截面 \(E(U)\)。

构造反例。

取
\[
T=*,
\qquad
\Gamma=\{1,\sigma\}\cong C_2,
\]
其中 \(\sigma\) 在 \(T=*\) 上作用平凡。于是
\[
H=h_*=*,
\qquad
Q=*
\]
（因为群作用平凡）。因而 \(Q\) 上的实现就是：\(E\cong D\)，且 \(\Gamma\)-作用平凡。所以若 \(E\) 上 \(\sigma\) 的作用非平凡，则 \(E\) 不能在 \(Q\) 上实现。

取 Cantor 空间
\[
K=\{0,1\}^{\mathbb N}
\]
及无不动点的对合同胚
\[
\phi:K\to K,\qquad
\phi(x_0,x_1,x_2,\dots)
=(1-x_0,x_1,x_2,\dots).
\]
令 \(\underline K\) 为常层，\(h_K\) 为可表示层。令
\[
i:\underline K\hookrightarrow h_K
\]
为“局部常值映射”这一子层包含，令
\[
j:=\phi\circ i:\underline K\to h_K.
\]
定义层
\[
E:=\operatorname{coeq}(i,j).
\tag{4.1}
\]
直观地，\(E\) 把每个局部常值截面 \(s\) 与 \(\phi s\) 等同。

\(h_K\) 上的对合
\[
\tau:h_K\to h_K,\qquad \tau(f)=\phi\circ f
\]
满足 \(\tau i=j,\ \tau j=i\)，所以 \( \tau\) 下降到 \(E\) 上，给出
\[
a_\sigma:E\to E,\qquad a_\sigma^2=\operatorname{id}.
\]
因 \(T=*\)，唯一的映射 \(\pi:E\to*\) 自动满足等变性。

检查 S4 的条件。由于 \(q:h_K\to E\) 局部满，而 \(*\) 是终对象，任何整体截面 \(e\in E(*)\) 都可在某个非空对象上提升为 \(f:U\to K\)；取一点 \(u:*\to U\)，则 \(e=q(f(u))\)，即 \(e\) 是常数截面 \(f(u)\in K\) 的类。故 \(E(*)\) 由常数截面生成；且在 \(*\) 处定义关系已经给出
\[
k\sim\phi(k)\qquad(k\in K).
\]
于是
\[
a_\sigma([k])=[\phi(k)]=[k].
\]
所以对每个 \(e\in E(*)\) 和每个 \(\gamma\in\Gamma\)（这里 \(\gamma\pi(e)=\pi(e)\) 自动成立），都有
\[
a_\gamma(e)=e.
\tag{4.2}
\]
S4 的假设成立。

但 \(E\) 不能在 \(Q=*\) 上实现。因为如果实现，则有 \(E\cong D\)，且 \(\Gamma\)-作用平凡，特别 \(a_\sigma=\operatorname{id}\)。

现在看 \(E(K)\)。令
\[
\operatorname{id}_K\in h_K(K)
\]
为恒等映射，记其类为 \([\operatorname{id}_K]\in E(K)\)。则
\[
a_\sigma([\operatorname{id}_K])
=[\phi].
\]
断言
\[
[\operatorname{id}_K]\ne[\phi]\quad\text{in }E(K).
\tag{4.3}
\]
事实上，若二者在层余等化子中相等，则存在有限覆盖 \(\{p_i:U_i\to K\}\)，使得在每个 \(U_i\) 上，\(p_i\) 与 \(\phi p_i\) 在相应预层商中同类。预层商只由关系
\[
s\sim\phi s,\qquad s\text{ 局部常值}
\]
生成。因此若某个 \(p_i\) 不是局部常值，则它的类在预层商中是孤立的，不可能等于 \(\phi p_i\)（且因 \(\phi\) 无不动点，\(p_i\ne\phi p_i\)）。所以所有 \(p_i\) 都必须局部常值。但紧空间到离散空间的局部常值映射只有有限像；有限多个有限像的并仍是有限集，不能覆盖无限（不可数）的 \(K\)，与 \(\{p_i\}\) 是覆盖矛盾。故 (4.3) 成立。

于是 \(a_\sigma\) 在局部截面 \(E(K)\) 上非平凡，故 \(E\) 不能实现。反例完成。

**结论：S4 的条件不足以保证可下降。**

---

## S5 局部满射的基底检验

结论：**必然可。** 即若 \(B\to Q\) 局部满射，且
\[
E_B:=E\times_QB
\]
作为 \(H_B=H\times_QB\) 上的等变对象可在 \(B\) 上实现，则 \(E\) 可在 \(Q\) 上实现。

证明。设
\[
f:B\to Q
\]
局部满射。用 S3 的判据。假定 \(E_B\) 可在 \(B\) 上实现，则 \(E_B\) 满足条件 (T\(_B\))。我们要证 \(E\) 满足 (T)。

取任意 \(U\)、任意 \(x\in H(U)=\operatorname{Hom}(U,T)\)、任意 \(\gamma\in\Gamma\)，设
\[
h_\gamma x=x,
\]
并取任意
\[
e\in E_x(U).
\]
令 \(y:=qx:U\to Q\)。因 \(f:B\to Q\) 局部满，存在有限覆盖
\[
\{u_i:U_i\to U\}_{i}
\]
及截面
\[
b_i\in B(U_i)
\]
使得
\[
f b_i=y|_{U_i}=q x|_{U_i}.
\]
定义
\[
\widetilde x_i:=(x|_{U_i},b_i)\in H_B(U_i).
\]
由于 \(h_\gamma x=x\)，有
\[
\gamma\widetilde x_i=(h_\gamma x|_{U_i},b_i)=\widetilde x_i.
\]
把 \(e|_{U_i}\) 拉回到 \(E_B\)，得到
\[
e_i\in (E_B)_{\widetilde x_i}(U_i).
\]
由 \(E_B\) 满足 (T\(_B\))，并且 \(\widetilde x_i\) 在 \(\gamma\) 下固定，得到
\[
a^B_\gamma(e_i)=e_i.
\]
而 \(H_B\to H\) 在 \(\widetilde x_i\) 上的纤维拉回正是 \(E_{x|_{U_i}}\) 到 \((E_B)_{\widetilde x_i}\) 的典范同构；故
\[
a_\gamma(e|_{U_i})=e|_{U_i}.
\]
对所有 \(i\) 成立，覆盖后由层的分离性得
\[
a_\gamma(e)=e.
\]
因此 \(E\) 满足 (T)，由 S3 的定理 3.1，\(E\) 可在 \(Q\) 上实现。证毕。

这说明“可实现性”在局部满射的基底扩张下是局部性质：沿覆盖检验既能推出必要失败，也能推出充分成功。

---

## S6 非空基底与全局结论

结论：**拉回后可实现不必反映原 \(E\) 可实现。** 仅仅“\(B\) 非空、可表示且有 \(B\to Q\)”不够；关键是该映射是否局部满射地覆盖整个 \(Q\)。

### 1. 完整反例

取
\[
\Gamma=\{1,\sigma\}\cong C_2.
\]
令 \(T\) 为三点集合
\[
T=\{a,b,p\},
\]
其中
\[
\sigma a=b,\qquad \sigma b=a,\qquad \sigma p=p.
\]
所以 \(T\) 有两个轨道：
\[
O_0=\{a,b\}\cong \Gamma,
\qquad
O_1=\{p\}\cong \Gamma/\Gamma.
\]
商为
\[
Q=T/\Gamma=\{q_0,q_1\},
\qquad
q_0=O_0,\quad q_1=O_1.
\]

取有限 \(\Gamma\)-集
\[
X=\{\widetilde a,\widetilde b,u,v\},
\]
作用为
\[
\sigma\widetilde a=\widetilde b,\quad
\sigma\widetilde b=\widetilde a,\quad
\sigma u=v,\quad
\sigma v=u,
\]
并定义等变映射 \(f:X\to T\) 为
\[
f(\widetilde a)=a,\quad
f(\widetilde b)=b,\quad
f(u)=f(v)=p.
\]
令
\[
E:=h_X\longrightarrow h_T=H.
\]

在固定点 \(p\) 处，稳定子
\[
\Gamma_p=\Gamma
\]
在纤维
\[
X_p=f^{-1}(p)=\{u,v\}
\]
上交换 \(u,v\)，作用非平凡。由 S2 的判据 (2.4)，\(h_X\) 不可在
\[
Q=T/\Gamma
\]
上实现。

现在取
\[
B:=h_*
\]
为终对象 \(*\) 的可表示层。它当然非空。令
\[
\beta:B=h_*\longrightarrow Q=h_{\{q_0,q_1\}}
\]
为对应于点 \(q_0\in Q\) 的映射。

计算拉回。因为 \(Q\) 是有限离散集，
\[
H_B=H\times_QB
=h_T\times_{h_Q}h_*
\cong h_{T\times_Q*}
\cong h_{T_{q_0}}
\cong h_{\{a,b\}}.
\]
同理，
\[
E_B=E\times_QB
=h_X\times_{h_Q}h_*
\cong h_{X\times_Q*}
\cong h_{X_{q_0}}
\cong h_{\{\widetilde a,\widetilde b\}}.
\]
而映射
\[
X_{q_0}=\{\widetilde a,\widetilde b\}
\longrightarrow
T_{q_0}=\{a,b\}
\]
是等变的双射；\(\Gamma\) 在两边的作用都是正则作用。因此
\[
E_B\cong H_B
\cong H_B\times_B*,
\]
其中 \(*\) 表示 \(B=h_*\) 上的终对象层。故 \(E_B\) 在 \(B\) 上实现，对应的下降对象为 \(D:=*\)。

但 \(E=h_X\) 本身不能在 \(Q\) 上实现。故拉回可实现不反映原对象可实现。

注意：\(\beta:B\to Q\) 不是局部满射；它的像只含 \(q_0\)，漏掉了 \(q_1\)。这与 S5 的正面结论完全一致。

### 2. 可用的检验原则

由 S1–S5 可整理如下。

1. **局部稳定子判据（通用、充要）**  
   对任意等变对象 \(E\to H\)，构造 \(Q=H/\Gamma\)，则 \(E\) 可实现当且仅当：对每个测试对象 \(U\)、每个 \(x\in H(U)\)、每个 \(\gamma\in\Gamma\)，若 \(h_\gamma x=x\)，则
   \[
   a_\gamma|_{E_x(U)}=\operatorname{id}.
   \]
   这是 S3 的判据 (T)。它必须在所有局部截面上验证，不能只验整体截面。

2. **点检验一般不够（S4）**  
   仅检查 \(E(*)\) 不够。即使所有整体截面在稳定子下不动，\(E\) 仍可能因某个局部截面上稳定子作用非平凡而不可下降。反例见 S4。

3. **有限可表示情形可用轨道—稳定子检验（S2）**  
   若 \(E=h_X\) 且 \(X,T\) 有限，则可把 \(X\to T\) 分解为
   \[
   X_i\cong \Gamma\times_{K_i}S_i,
   \qquad
   S_i=X_{t_i}.
   \]
   可实现当且仅当所有 \(K_i\) 在 \(S_i\) 上作用平凡。此时
   \[
   \operatorname{Aut}(h_X)\cong\prod_i\operatorname{Sym}(S_i)
   \]
   在等变范畴中成立。

4. **局部满射基底可以双向检验（S5）**  
   若 \(B\to Q\) 局部满射，则
   \[
   E\text{ 可实现}
   \iff
   E\times_QB\text{ 在 }B\text{ 上可实现}.
   \]
   因此遇到复杂的 \(Q\) 时，可取一个覆盖 \(B\to Q\)，把问题拉到 \(B\) 上逐局部检验；成功与失败都能反映回 \(Q\)。

5. **非覆盖的非空可表示基底只能作单边检验（S6）**  
   对任意 \(B\to Q\)，总有
   \[
   E\text{ 可实现}
   \Longrightarrow
   E\times_QB\text{ 在 }B\text{ 上可实现}.
   \]
   因而若某个拉回不可实现，可断定 \(E\) 不可实现。但反过来通常不成立，除非该 \(B\to Q\) 局部满射。仅“\(B\) 非空可表示”不够；S6 的例子中 \(B=h_*\) 只看到 \(Q\) 的一个点，完全漏掉了带有非平凡稳定子的另一个轨道。

6. **有限离散商上的实用判别**  
   特别地，在 S2 的有限情形，\(Q=T/\Gamma\) 是有限离散的。若取可表示基底 \(B=h_S\) 及映射 \(h_S\to h_Q\)，则它在层意义下局部满射当且仅当 \(S\to Q\) 在点上满射。因此：
   \[
   B=h_S\text{ 可以用来作双向检验}
   \iff
   S\to Q\text{ 满射}.
   \]
   单个非空点 \(B=h_*\) 只能检验其像所在的那个轨道；若 \(Q\) 还有别的轨道，就不能据此推出全局可实现。

以上六阶段均已完成。