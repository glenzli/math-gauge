**S1　有限群的自由作用**

先固定一个以后会反复使用的构造。记层化为 \(a\)。对于任意带 \(\Gamma\) 作用的层 \(F\)，定义
\[
F/\Gamma:=a\bigl(S\longmapsto F(S)/\Gamma\bigr).
\]
层化的局部描述给出：

- \(F\to F/\Gamma\) 局部满射；
- \(x,y\in F(S)\) 在商中相等，当且仅当存在有限覆盖 \(\{S_i\to S\}\) 及 \(\gamma_i\in\Gamma\)，使
  \[
  y|_{S_i}=a_{\gamma_i}(x|_{S_i}).
  \tag{1}
  \]

这里可以使用有限覆盖，因为站点的覆盖由所给有限覆盖生成，而有限覆盖的复合仍是有限覆盖。由层化的伴随性质，
\[
\operatorname{Hom}(F/\Gamma,Y)
\cong \operatorname{Hom}(F,Y)^\Gamma.
\tag{2}
\]

令 \(Z=T/\Gamma\) 为集合轨道空间，赋予商拓扑。轨道关系是有限个作用同胚的图之并，因而是 \(T\times T\) 中的闭等价关系。紧 Hausdorff 空间除以闭等价关系仍为紧 Hausdorff 空间，所以 \(Z\) 紧 Hausdorff。

它还有闭开集基。事实上，若 \(V\subseteq T\) 是包含某条轨道的 invariant 开集，可以在 \(V\) 内选取包含该有限轨道的闭开集 \(C\)。则
\[
\bigcup_{\gamma\in\Gamma}\gamma C
\]
是 invariant 闭开集，包含该轨道且仍包含于 \(V\)。这些集合下降为 \(Z\) 的闭开集基。因此 \(Z\) 是 \(U\) 小 profinite 空间。

下面证明 \(h_Z\) 是层商。记
\[
R=T\times_ZT.
\]
映射
\[
\Gamma\times T\longrightarrow R,\qquad
(\gamma,t)\longmapsto(t,\gamma t)
\tag{3}
\]
连续满射，故是站点覆盖。对任意层 \(Y\)，由覆盖 \(T\to Z\) 的层条件，
\[
Y(Z)=\operatorname{Eq}\bigl(Y(T)\rightrightarrows Y(R)\bigr).
\]
借助覆盖 (3)，右侧的相容条件恰好等价于 \(\Gamma\) 不变性。因此自然地有
\[
\operatorname{Hom}(h_Z,Y)
\cong\operatorname{Hom}(h_T,Y)^\Gamma.
\]
故 \(h_Z\cong H/\Gamma\)。这部分证明事实上不需要自由性。

现在假设作用自由。给定等变层 \(E\to H\)，取
\[
D=E/\Gamma,\qquad D\longrightarrow h_Z,
\]
其中后一映射由 invariant 映射 \(E\to H\to h_Z\) 诱导。构造
\[
\theta:E\longrightarrow H\times_{h_Z}D,\qquad
e\longmapsto(\pi(e),[e]).
\tag{4}
\]

它局部满射：给定 \((t,d)\)，先局部提升 \(d\) 为 \(e_0\)。由于 \(\pi(e_0)\) 与 \(t\) 的商像相同，由 (1)，进一步有限覆盖后有
\[
t=\gamma\pi(e_0).
\]
于是 \(a_\gamma(e_0)\) 提升 \((t,d)\)。

它也是单射：若 \(\theta(e)=\theta(e')\)，则局部有 \(e'=a_\gamma(e)\)，且
\[
\gamma\pi(e)=\pi(e).
\]
在非空测试空间上，自由性迫使 \(\gamma=1\)；空测试空间上的层截面唯一。因此局部有 \(e=e'\)，再由层的分离性得全局相等。

局部满射且单射的层态射是同构：局部提升因唯一性而能粘合。故 (4) 是等变同构，给出了所需实现。

---

**S2　有限集合上的纤维分类**

对每个轨道选代表 \(t\)，记
\[
G_t=\Gamma_t,\qquad F_t=X_t.
\]
纤维 \(F_t\) 自然是有限 \(G_t\)-集合，并且有范畴等价
\[
\operatorname{Fin}\Gamma\operatorname{Set}/T
\simeq
\prod_{[t]\in T/\Gamma}\operatorname{Fin}G_t\operatorname{Set}.
\tag{5}
\]

逆构造为
\[
(F_t)_t\longmapsto
\bigsqcup_{[t]}\Gamma\times_{G_t}F_t,
\qquad [g,x]\longmapsto gt,
\tag{6}
\]
其中 \((gk,x)\sim(g,kx)\)。对原来的 \(X\)，映射
\[
[g,x]\longmapsto gx
\]
给出 (6) 与 \(X\) 的同构：每个元素都可移回代表纤维，而不同选择恰好相差稳定子作用。

态射对应于各纤维上的稳定子等变映射：
\[
\operatorname{Hom}_{\Gamma/T}(X,X')
\cong
\prod_{[t]}\operatorname{Hom}_{G_t}(F_t,F'_t).
\tag{7}
\]
逆向延拓为 \([g,x]\mapsto[g,f_t(x)]\)。

令 \(Q=h_{T/\Gamma}\)。则
\[
\boxed{\ h_X\text{ 在 }Q\text{ 上可实现}
\iff \forall t,\ G_t\text{ 在 }F_t\text{ 上作用平凡。}\ }
\tag{8}
\]

必要性：在 \(H\times_QD\) 中，固定 \(t\) 的群元素同时固定两个坐标，故固定该纤维的全部元素。

充分性：若稳定子作用平凡，令
\[
Y=\bigsqcup_{[t]}F_t\longrightarrow T/\Gamma.
\]
由 (6) 得到等变同构
\[
X\cong T\times_{T/\Gamma}Y,
\]
从而
\[
h_X\cong H\times_Qh_Y.
\]

一般对象的自同构群为
\[
\operatorname{Aut}_{\Gamma/T}(X)
\cong\prod_{[t]}\operatorname{Aut}_{G_t}(F_t).
\]
特别地，若对象可实现，令 \(n_t=|F_t|\)，则
\[
\boxed{\operatorname{Aut}_{\Gamma/T}(X)
\cong\prod_{[t]}\mathfrak S_{n_t}.}
\tag{9}
\]
由 Yoneda，这也是对应等变层的自同构群。

---

**S3　一般层的完整下降**

此阶段不假设 \(\Gamma\) 有限或作用自由。

定义
\[
Q=H/\Gamma
=a\bigl(S\longmapsto C(S,T)/\Gamma\bigr),
\]
并令 \(q:H\to Q\) 为商映射。由 (2)，对每个层 \(Y\)，自然地有
\[
\boxed{\operatorname{Hom}(Q,Y)
\cong\operatorname{Hom}(H,Y)^\Gamma.}
\tag{10}
\]
特别地，\(q\) invariant 且局部满射。此处不要求 \(Q\) 可表示。

给定等变 \(E\to H\)，构造
\[
D_0=E/\Gamma\longrightarrow Q,\qquad
\theta_E:E\longrightarrow H\times_QD_0.
\tag{11}
\]
与 S1 相同，先提升商截面、再局部调整群元素的论证证明：**\(\theta_E\) 总是局部满射**。这一论证只使用商的局部描述 (1)。

不预选实现层的充要判据是：
\[
\boxed{
\begin{gathered}
\text{对每个 profinite }S,\ e\in E(S),\ \gamma\in\Gamma,\\
\gamma\pi(e)=\pi(e)\quad\Longrightarrow\quad a_\gamma(e)=e.
\end{gathered}}
\tag{12}
\]

它也可写成层态射条件。令
\[
T^\gamma=\{t\in T:\gamma t=t\}.
\]
因为 \(T\) Hausdorff，\(T^\gamma\) 是闭子空间，仍是 profinite。条件 (12) 等价于
\[
a_\gamma=\mathrm{id}
\quad\text{在 }E\times_Hh_{T^\gamma}\text{ 上成立，}\qquad
\forall\gamma\in\Gamma.
\tag{13}
\]

证明必要性：若 \(E\cong H\times_QD\)，作用只改变 \(H\) 坐标；固定该坐标就固定整个截面。

证明充分性：若 \(\theta_E(e)=\theta_E(e')\)，由商的局部描述，局部有
\[
e'=a_\gamma(e),\qquad
\gamma\pi(e)=\pi(e).
\]
由 (12) 得局部 \(e=e'\)，因此全局相等。故 \(\theta_E\) 单射，结合其局部满射性，得到同构。

因此有等价条件
\[
\boxed{
E\text{ 可实现}
\iff (12)
\iff\theta_E\text{ 单射}
\iff\theta_E\text{ 是同构}.}
\tag{14}
\]
条件成立时，规范实现就是 \(D_0=E/\Gamma\)。

所有实现及态射可统一描述如下。设 \(\mathcal A\) 为满足 (12) 的等变对象所成的满子范畴，则
\[
\mathcal C/Q\xrightarrow{\ \sim\ }\mathcal A,
\qquad
D\longmapsto H\times_QD
\tag{15}
\]
是范畴等价，逆函子为 \(E\mapsto E/\Gamma\)。

为验证这一点，注意对任何 \(D\to Q\)，投影
\[
H\times_QD\longrightarrow D
\]
局部满射；两个截面有相同的 \(D\) 坐标，当且仅当它们局部相差一个群元素。因此
\[
(H\times_QD)/\Gamma\cong D.
\tag{16}
\]
结合 (14)，得到两个函子的自然逆同构。

具体而言：

- 任意实现层都与 \(D_0\) 同构；
- 若把 \(E\cong H\times_QD\) 的识别也计入实现数据，则任意两个实现之间有唯一保持该识别的同构；
- 对两个可实现对象，
  \[
  \operatorname{Hom}_{\Gamma/H}(E,E')
  \cong\operatorname{Hom}_Q(E/\Gamma,E'/\Gamma).
  \tag{17}
  \]

现在取任意层 \(B\to Q\)，记
\[
H_B=H\times_QB.
\]
投影 \(H_B\to B\) 局部满射，而且同一 \(B\) 截面上的两个 \(H_B\) 截面局部相差群元素，故
\[
H_B/\Gamma\cong B.
\tag{18}
\]
因此，对 \(H_B\) 上的任意等变层 \(F\)，完全相同的证明给出
\[
\mathcal C/B
\simeq
\left\{
\begin{array}{c}
H_B\text{ 上的等变对象 }F，\\
\text{满足所有测试空间上的稳定子作用平凡}
\end{array}
\right\},
\tag{19}
\]
正向函子为 \(D\mapsto H_B\times_BD\)，逆向函子为 \(F\mapsto F/\Gamma\)。

这个分类与任意基底拉回相容。特别地，对原来的任意 \(E\)，即使它不可实现，也有自然同构
\[
\boxed{
(E\times_QB)/\Gamma
\cong(E/\Gamma)\times_QB.}
\tag{20}
\]
证明仍是局部检验：右侧截面局部提升为 \((e,b)\)；两个这样的提升具有相同商像，恰好意味着 \(b\) 相同且 \(e\) 局部相差群元素。

在 (20) 下，\(\theta_{E\times_QB}\) 就是 \(\theta_E\) 的基底拉回。对任意 \(B'\to B\)，还自然地有
\[
(H_B\times_BD)\times_BB'
\cong
H_{B'}\times_{B'}(D\times_BB'),
\]
且这些同构保持群作用及态射，给出了所需相容性。

---

**S4　单点上的检验**

**结论：不成立。即使 \(\Gamma\) 有限且 \(T=*\)，也有反例。**

取无限 profinite 阿贝尔群
\[
K=(\mathbf F_3)^{\mathbb N}\in U.
\]
对每个测试空间 \(S\)，令 \(L(S)\subseteq C(S,K)\) 为局部常值映射组成的子群，定义预层
\[
P(S)=C(S,K)/L(S),\qquad A=aP.
\]
点态运算使 \(P\) 为 \(\mathbf F_3\)-向量空间预层；层化后，\(A\) 仍是向量空间层。

先验证两个性质。

第一，
\[
A(*)=0.
\tag{21}
\]
因为 \(P(*)=K/K=0\)，而层化在 \(*\) 处不改变取值：任何覆盖 \(*\) 的族都有非空成员，选其中一点便给出该成员到 \(*\) 的映射的截面。因此每个覆盖筛都包含 \(\mathrm{id}_*\)。

第二，恒等映射定义的截面
\[
x=[\mathrm{id}_K]\in A(K)
\]
非零。否则由层化的局部相等性质，存在有限覆盖
\[
\{f_i:S_i\to K\}
\]
使每个 \(f_i\) 在 \(P(S_i)\) 中为零，即每个 \(f_i\) 局部常值。紧空间上的局部常值映射具有有限像，所以有限个 \(f_i\) 的像之并有限，不可能覆盖无限空间 \(K\)。矛盾。

现在取
\[
T=*,\qquad \Gamma=C_2=\{1,\sigma\},\qquad E=A,
\]
令 \(\Gamma\) 在 \(T\) 上平凡作用，在 \(A\) 上令
\[
a_\sigma=-\mathrm{id}.
\]
由 (21)，\(E(*)\) 只有零截面，它被所有群元素固定。因此题设的单点条件成立。

但 \(a_\sigma\) 非平凡：因 \(x\ne0\) 且特征为 \(3\)，有 \(-x\ne x\)。另一方面，此时 \(H=Q=*\)，任何在 \(Q\) 上实现的对象，其群作用都必须平凡。因此 \(E\) 不可实现。

---

**S5　局部满射的基底检验**

**结论：成立。**

设 \(B\to Q\) 局部满射，且
\[
E_B=E\times_QB
\]
在 \(B\) 上可实现。用 S3 的判据证明 \(E\) 可实现。

任取 profinite \(S\)、\(e\in E(S)\) 和 \(\gamma\in\Gamma\)，满足
\[
\gamma\pi(e)=\pi(e).
\]
由 \(B\to Q\) 局部满射，存在有限覆盖 \(\{S_i\to S\}\)，使 \(q\pi(e)\) 在每个 \(S_i\) 上提升为 \(b_i\in B(S_i)\)。

于是 \((e|_{S_i},b_i)\) 是 \(E_B(S_i)\) 的截面，且 \(\gamma\) 固定它的 \(H_B\) 坐标。由于 \(E_B\) 可实现，S3 的必要条件给出
\[
a_\gamma(e)|_{S_i}=e|_{S_i}.
\]
由层的分离性，全局有 \(a_\gamma(e)=e\)。故 \(E\) 满足 (12)，从而可实现。

等价地，(20) 表明 \(\theta_{E_B}\) 是 \(\theta_E\) 的拉回，而沿局部满射基底的拉回能够反映同构。

---

**S6　非空基底与全局结论**

**结论：仅有非空可表示基底，不足以反映可实现性。**

取
\[
\Gamma=C_2=\{1,\sigma\},\qquad T=\{0,1\},
\]
令 \(\Gamma\) 在 \(T\) 上平凡作用。于是
\[
Q=h_T.
\]
令
\[
X=\{x_0,x_1,x_2\},\qquad
\pi(x_0)=0,\quad \pi(x_1)=\pi(x_2)=1,
\]
并规定
\[
\sigma x_0=x_0,\qquad
\sigma x_1=x_2,\qquad
\sigma x_2=x_1.
\]
这是有限等变集合 \(X\to T\)，故给出等变层 \(E=h_X\to H\)。

取非空可表示基底
\[
B=h_*\longrightarrow Q
\]
对应于 \(0\in T\)。则
\[
H_B\cong h_*,
\qquad E_B\cong h_{\{x_0\}}\cong h_*,
\]
作用平凡，因此 \(E_B\) 在 \(B\) 上可实现。

但 \(E\) 不可实现：稳定子 \(\Gamma_1=\Gamma\) 非平凡地交换纤维中的 \(x_1,x_2\)，违反 S2 的条件，也违反 S3 的判据。这个基底没有检验到轨道 \(1\)。

由以上结果，可用的检验原则是：

- **完整判据：**在所有 profinite 测试空间上，稳定子作用平凡，当且仅当对象可实现；规范实现为 \(E/\Gamma\)。
- **有限集合情形：**只需检查代表点的稳定子在有限纤维上的作用。一般层不能仅检查 \(E(*)\)，如 S4。
- **基底检验：**任意基底拉回保持可实现性；局部满射基底还反映可实现性。联合局部满射的基底族也能检验，证明与 S5 相同。
- **非空性：**非空可表示基底本身不足够。若 \(Q=*\)，则任意非空可表示 \(B\to Q\) 都有点截面，因而局部满射，此时可以使用 S5。
- **自由作用：**自由性使 S3 的稳定子判据自动成立，所以对层商 \(Q\)，任意自由作用都允许完整下降；S1 的有限群条件进一步保证这个商由 profinite 轨道空间表示。