# S1　有限群的自由作用

记 (Z=T/\Gamma) 为轨道集，赋予商拓扑，记商映射为 (p:T\to Z)。有限群作用的轨道关系是 (T\times T) 中有限个图像的并，因而是闭关系；所以 (Z) 紧且 Hausdorff。

它还是零维的。事实上，若一个轨道包含于不变开集 (O\subseteq T)，先选取包含该轨道且包含于 (O) 的开闭集 (C)，再令
\[
C'=\bigcup_{\gamma\in\Gamma}\gamma C.
\]
这是包含该轨道、包含于 (O) 的不变开闭集。其像在 (Z) 中开闭。这给出了 (Z) 的开闭邻域基，故 (Z) 是 profinite。商集及其拓扑均为 (U)-小。

有限联合满射族是有效的连续映射粘合族：若 (S_i\to S) 是这样的族，则 (\coprod_i S_i\to S) 是紧空间到 Hausdorff 空间的连续满射，故是商映射。因此，匹配的连续映射 (S_i\to W) 唯一粘合为连续映射 (S\to W)。这也证明本题的拓扑是次典范的。

自由性给出同构
\[
\Gamma\times T\xrightarrow{\sim}T\times_ZT,
\qquad(\gamma,t)\longmapsto(\gamma t,t).
\]
这里左边是有限个 (T) 的不交并；该映射是紧 Hausdorff 空间间的连续双射，因而是同胚。又 (p) 本身是覆盖，故对任意层 (Y)，覆盖的层条件给出
\[
\operatorname{Hom}(h_Z,Y)
\cong
\operatorname{Eq}\bigl(Y(T)\rightrightarrows Y(T\times_ZT)\bigr)
\cong \operatorname{Hom}(h_T,Y)^\Gamma.
\]
最后一个等式也使用了层把有限不交并变成有限乘积。因此 (h_Z) 正是层商。

下面直接构造下降。对每个 (S\to Z)，令 (W=S\times_ZT)，以 (b_\gamma(s,t)=(s,\gamma t)) 表示其作用。定义 (D\to h_Z) 在 (S) 上的截面为所有对
\[
(u:S\to Z,\ e\in E(W))
\]
组成的集合，其中
\[
\pi(e)=\operatorname{pr}_T,
\qquad b_\gamma^*e=a_\gamma(e)\quad(\gamma\in\Gamma).
\]
这确实是层：先粘合 (u)，再在它的基变换覆盖上粘合 (e)；上述等式是可以在覆盖上检验的。

有自然同构 (E\cong h_T\times_{h_Z}D)。给定右边的截面 ((t,(u,e)))，沿图映射 (S\to S\times_ZT, s\mapsto(s,t(s))) 拉回 (e)，即得左边截面。反过来，给定 (e_0\in E(S))，置 (t=\pi(e_0))、(u=pt)。在 (W=S\times_ZT) 上，每一点唯一写成 ((s,\gamma t(s)))。由上述主丛同构，按这些 (\gamma) 划分的部分是有限开闭分解；在相应部分取 (a_\gamma(e_0|_W)) 并粘合。这给出所需的 (e)。两种构造互逆，并且等变，其中右边的作用仅改变 (h_T) 坐标。这证明每个等变层均可实现。空空间的情形也由同一构造成立。

# S2　有限集合上的纤维分类

为每个轨道 (o\in T/\Gamma) 选代表 (t_o)，令 (K_o=\Gamma_{t_o})。纤维函子给出范畴等价
\[
\{\text{有限 }\Gamma\text{-集合 }X\to T\}
\simeq\prod_{o\in T/\Gamma}\operatorname{FinSet}^{K_o}.
\]
它把 (X\to T) 送到纤维 (F_o=X_{t_o})，其上的 (K_o) 作用是原作用的限制。

反向构造是
\[
X=\coprod_o\Gamma\times_{K_o}F_o,
\qquad [g,f]\longmapsto gt_o,
\]
其中 ((gk,f)\sim(g,kf))，(\Gamma) 在第一个坐标上左乘。映射 ([g,f]\mapsto gf) 给出与原 (X) 的同构。等变态射恰好对应于一族 (K_o)-等变映射 (F_o\to F'_o)，故这个描述同时分类对象与全部态射。

令 (Q=h_{T/\Gamma})。则
\[
h_X\text{ 可在 }Q\text{ 上实现}
\quad\Longleftrightarrow\quad
\text{每个 }K_o\text{ 在 }F_o\text{ 上的作用平凡}.
\]
必要性：在 (h_T\times_QD) 中，固定 (t_o) 的群元素对位于该点上的截面不作改变，特别是对 (F_o=h_X(*)_{t_o}) 不作改变。

充分性：若所有这些作用平凡，令有限集合
\[
A=\coprod_oF_o\longrightarrow T/\Gamma
\]
把第 (o) 个部分映到 (o)。则有等变同构 (X\cong T\times_{T/\Gamma}A)，所以可以取 (D=h_A)。也可将 (A) 典范地写成 (X/\Gamma)。即使事先允许任意层作为 (D)，实现对象也必与这个 (h_A\to Q) 同构；这由 S3 的唯一性，或沿覆盖 (h_T\to Q) 的局部同构检验得到。

一般对象的自同构群为
\[
\prod_o\operatorname{Aut}_{K_o}(F_o).
\]
对可实现对象，它是
\[
\boxed{\operatorname{Aut}_{\Gamma,T}(X)
\cong\operatorname{Aut}_{Q}(D)
\cong\prod_o\operatorname{Sym}(F_o).}
\]
这里全部自同构均在指定基底之上，因此不允许置换不同的轨道；空纤维贡献平凡群。

# S3　一般层的完整下降

## 1. 商的构造与局部描述

以下均不对 (\Gamma) 的有限性、作用的自由性作额外假设。若层 (F) 带 (\Gamma) 作用，记
\[
F/\Gamma:=a\bigl(S\longmapsto F(S)/\Gamma\bigr),
\]
其中 (a) 是集合值预层的层化。由于站点是 (V)-小的、所有所涉及集合都属于 (V)，此层化及商存在于给定大小范围内。

这个商具有以下局部描述：

1. 每个商截面在某有限覆盖上可由 (F) 的截面表示。
2. 两个 (F(S)) 中的截面在商中相等，当且仅当存在有限覆盖 (S_i\to S)，使得在每个 (S_i) 上二者相差某个常值群元素 (\gamma_i\in\Gamma)。

这是层化的局部表示与局部相等性质。层化中出现的连续细化可以合成为本题允许的有限覆盖，因为有限覆盖在拉回与复合下封闭。不同覆盖成员上允许使用不同的群元素；这里并没有把“局部属于同一轨道”误当成“全局相差一个群元素”。

取
\[
Q=H/\Gamma,\qquad q:H\longrightarrow Q.
\]
预层轨道商的泛性质与层化的伴随性质给出自然双射
\[
\operatorname{Hom}_{\mathcal C}(Q,Y)
\cong\operatorname{Hom}_{\mathcal C}(H,Y)^\Gamma.
\]
特别地 (q) 不变且局部满射。这构造不要求拓扑轨道空间是 Hausdorff，或是 profinite。

## 2. 不预选下降对象的判据

对等变对象 (E\to H)，考虑以下条件：
\[
\tag{I}
\begin{gathered}
\text{对每个 }S\in\operatorname{Prof}_U、e\in E(S)、\gamma\in\Gamma,\\
\gamma\pi(e)=\pi(e)\quad\Longrightarrow\quad a_\gamma(e)=e.
\end{gathered}
\]
这是所有广义截面上的稳定子平凡性，不能只检验 (S=*)。等价地，对每个 (\gamma)，(a_\gamma) 在
\[
E\times_Hh_{T^\gamma}
\]
上为恒等，其中 (T^\gamma\subseteq T) 是闭的固定点子空间，因而仍是 (U)-小 profinite 空间。

结论为：
\[
\boxed{E\text{ 可在 }Q\text{ 上实现}\iff\text{条件 (I) 成立}.}
\]

为证明它，令
\[
P=E/\Gamma,
\]
由 (E\to H\to Q) 得到 (P\to Q)。有典范等变映射
\[
\theta:E\longrightarrow H\times_QP,
\qquad e\longmapsto(\pi(e),[e]).
\]

首先，(\theta) 总是局部满射。给定 ((x,p)\in(H\times_QP)(S))，先在覆盖上将 (p) 提升为 (e\in E)。由于 (q(x)=q(\pi(e)))，再细化覆盖后可以找到群元素 (\gamma)，使 (x=\gamma\pi(e))。于是 (a_\gamma(e)) 就是所求提升。

其次，(I) 蕴含 (\theta) 为单射。若 (\theta(e)=\theta(e'))，则 (\pi(e)=\pi(e')=x)，而商的局部描述给出覆盖上 (e'=a_\gamma(e))。此时 (\gamma x=x)，故 (I) 给出局部的 (e'=e)，从而由层的分离性得到全局相等。

层间一个单态射若局部满射就是同构：任意目标截面的局部提升由单射性在交上相等，因而唯一粘合。故 (I) 时 (\theta) 是同构，并可取 (D=P)。

反过来，若 (E\cong H\times_QD) 且群只改变 (H) 坐标，那么固定 (\pi(e)) 的 (\gamma) 也固定整个截面 (e)。所以 (I) 必要。

## 3. 所有实现与态射的分类

令 (\mathcal A_H\) 为满足 (I) 的等变对象构成的满子范畴。有范畴等价
\[
\mathcal C/Q\xrightarrow{\sim}\mathcal A_H,
\qquad
D\longmapsto H\times_QD,
\]
其拟逆是 (E\mapsto E/\Gamma)。

为验证另一个方向的同构，考虑
\[
(H\times_QD)/\Gamma\longrightarrow D.
\]
它局部满射，因为 (H\to Q) 局部满射。若两个局部表示有相同 (D) 坐标，它们的 (H) 坐标在 (Q) 中相等，故局部相差群元素；因此它也是单射，遂为同构。

等变态射 (f:E\to E') 在商上唯一诱导 (\bar f:E/\Gamma\to E'/\Gamma)，且典范同构把 (f) 识别为 (\operatorname{id}_H\times\bar f)。反向拉回则给出所有等变态射。这证明满忠实性及态射分类。

准确地说，一个实现是带指定等变同构的对
\[
(D,\alpha:E\xrightarrow{\sim}H\times_QD).
\]
若 (I) 不成立，则没有实现；若成立，则这些对组成的群胚非空且任意两对象之间恰有一个与指定同构相容的同构。其典范代表为 ((E/\Gamma,\theta))。若不指定 (\alpha)，下降对象只有一个同构类，但当然可能有非平凡自同构，其自同构群对应于 (E) 的等变自同构群。

## 4. 任意层基底及基变换相容性

现在给定任意层 (B\to Q)，置
\[
H_B=H\times_QB,
\]
群在 (B) 坐标上作用平凡。则 (H_B\to B) 局部满射，且其两截面有相同 (B) 坐标，当且仅当它们局部相差群元素。前者由 (H\to Q) 的局部提升性质得到；后者由 (Q) 的局部轨道描述得到。因此
\[
H_B/\Gamma\cong B.
\]

对任意等变对象 (F\to H_B)，要求它在所有测试对象上的稳定子作用平凡，即
\[
\gamma\pi_F(f)=\pi_F(f)\Longrightarrow\gamma f=f.
\]
完全相同的 (\theta) 证明给出等价
\[
\mathcal C/B\simeq
\{F\to H_B:\text{上述稳定子条件成立}\},
\]
分别由 (D_B\mapsto H_B\times_BD_B) 与 (F\mapsto F/\Gamma) 实现。这里对任意层 (B) 都成立，不需要它可表示或局部满射到 (Q)。

更进一步，对任何 (B'\to B)，有自然同构
\[
(F\times_BB')/\Gamma
\xrightarrow{\sim}(F/\Gamma)\times_BB'.
\]
证明仍用局部表示：右边的截面局部由一个 (F) 截面及给定 (B') 截面表示，二者在 (B) 中相容，故来自左边；两个这样的表示有相同像时，局部相差一个群元素，且群不改变 (B') 坐标，所以在左边也相等。因此该映射局部满射且单射。

特别地，对原来的 (E)，
\[
(E\times_QB)/\Gamma\cong(E/\Gamma)\times_QB.
\]
以上同构与拉回复合及恒等拉回相容，因为它们都由同一个取轨道的典范映射诱导。于是对象、实现和态射的全部分类都与任意基变换相容。

# S4　单点上的检验

**结论：不一定。** 即使 (T=*)、(\Gamma=C_2)，也有反例。

取 profinite 加法群 (A=\mathbb Z_3)。令 (\underline{A_{\mathrm{disc}}}) 为抽象群 (A) 的常值层；在 profinite 测试空间 (S) 上，它由局部常值映射 (S\to A_{\mathrm{disc}}) 组成。这些映射在紧空间上具有有限像。将它们视为取值于 profinite 群 (A) 的连续映射，得到阿贝尔群层的单态射
\[
\underline{A_{\mathrm{disc}}}\hookrightarrow h_A.
\]
这里局部常值映射确实成层：沿有限联合满射族粘合后，所得映射的像有限，每个值的原像由商拓扑判定为开闭。

取阿贝尔群层商
\[
E=h_A/\underline{A_{\mathrm{disc}}},
\]
并把它的底层集合层作为所求 (E\to h_*)。它也可直接由预层
\(S\mapsto C(S,A)/C(S,A_{\mathrm{disc}})\)
层化构造。令 (C_2) 的非平凡元素在 (E) 上作用为取负号。

先验证单点条件。任何到 (*) 的覆盖都有某个非空成员 (S_i)，而 (S_i) 有一个点，从而该成员到 (*) 的映射有截面。因此 (h_A\to E) 的局部满射性蕴含
\[
h_A(*)=A\longrightarrow E(*)
\]
满射。但 (A\to E(*)) 的所有元素都被常值层的 (A\) 杀掉，所以 (E(*)=\{0\})。故题设对每个 (e\in E(*)) 的条件完全满足。

再验证此作用并不平凡。取测试空间 (S=A)，令
\[
u=[\operatorname{id}_A]\in E(A).
\]
若 (u=-u)，则连续映射 (2\operatorname{id}_A:A\to A) 在商中为零。由层化的局部相等性质，存在有限覆盖 (S_i\to A)，使得每个复合
\[
S_i\longrightarrow A\xrightarrow{\times2}A
\]
是局部常值映射，因而具有有限像。由于这些 (S_i\to A) 联合满射，(\times2:A\to A) 的像也必有限。然而 (2\) 在 (\mathbb Z_3\) 中是单位，所以该映射满射到无限集合 (A)，矛盾。因此 (u\ne-u)。

这里 (Q=*)。一个 (E\to h_*) 在 (Q) 上实现，恰好意味着其群作用平凡。上述作用不平凡，故不可实现。这也明确展示了单点截面无法代替 S3 中全部广义截面的检验。

# S5　局部满射的基底检验

**结论：一定可以实现。**

设 (B\to Q) 局部满射，且 (E_B=E\times_QB\to H_B) 可在 (B) 上实现。检验 S3 的条件 (I)：取任意 (S\)、(e\in E(S))、(\gamma\in\Gamma)，满足
\[
\gamma\pi(e)=\pi(e).
\]
由 (B\to Q) 局部满射，可取有限覆盖 (S_i\to S)，使 (q\pi(e)|_{S_i}) 提升为 (b_i\in B(S_i))。于是
\[
(e|_{S_i},b_i)\in E_B(S_i)
\]
的 (H_B) 坐标被 (\gamma) 固定。由于 (E_B) 可实现，必要的稳定子条件给出
\[
a_\gamma(e)|_{S_i}=e|_{S_i}.
\]
由层的分离性，(a_\gamma(e)=e)。故 (I) 成立，S3 给出实现
\[
E\cong H\times_Q(E/\Gamma).
\]
该论证不要求 (B) 可表示，也不要求它有全局截面。

# S6　非空基底与全局结论

**结论：仅有非空可表示基底，不足以反映可实现性。**

给出完全有限的例子。令
\[
\Gamma=C_2=\{1,\sigma\},\qquad T=\{0,1\},
\]
且 (\Gamma) 在 (T) 上作用平凡。因此 (H=Q=h_T)，商映射是恒等映射。

令有限 (\Gamma)-集合 (X\to T) 的纤维为
\[
X_0=\{a\},\qquad X_1=\{b,c\},
\]
其中 (\sigma a=a\)，(\sigma b=c\)，(\sigma c=b\)。此映射显然等变，令 (E=h_X)。取非空可表示层
\[
B=h_*\longrightarrow Q
\]
对应于点 (0\in T)。则
\[
H_B\cong h_*,\qquad E_B\cong h_{\{a\}},
\]
且两者的作用均平凡，所以 (E_B) 可在 (B) 上实现，取 (D_B=h_*\to B) 即可。

但是 (\sigma) 固定 (\pi(b)=1) 而不固定 (b)，违反 S3 的必要条件，故 (E) 不可在 (Q) 上实现。该基底映射不是局部满射：截面 (1\in Q(*)) 不可能在任何覆盖上提升到仅映入 (0) 的 (B)。

综上，可用的检验原则为：

- **完整内在判据：** 在每个 profinite 测试对象上检验稳定子作用平凡；等价地，检验所有 (E\times_Hh_{T^\gamma}) 上的 (a_\gamma) 为恒等。
- **任意拉回保持可实现性。** 下降对象相应拉回，且其商的描述与拉回相容。
- **局部满射拉回反映可实现性。** 更一般地，一族基底若联合具有局部提升性质，则可在该族上检验同一稳定子等式，再局部粘合。
- **非空性不能代替覆盖性。** 一个非空可表示基底可能完全看不到发生障碍的轨道，如本阶段的例子。
- **只检验单点截面一般不够。** S4 给出即使群和 (T) 都有限也失败的一般层例子。S2 中的单点纤维分类有效，是因为 (E=h_X) 来自有限集合；不能将这一额外假设移用于一般层。

所有阶段均已完成。
