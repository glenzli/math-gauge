**S1　有限群的自由作用**

先记录两个后续也会使用的事实。

有限联合满射族 \(\{S_i\to S\}\) 的总映射 \(\coprod_iS_i\to S\) 是紧空间到 Hausdorff 空间的连续满射，因而是商映射。因此，兼容的连续映射 \(S_i\to Z\) 唯一粘合成连续映射 \(S\to Z\)。这证明每个 \(h_Z\) 都是层；空覆盖条件也成立。

记层化为 \(a\)。对于任意带 \(\Gamma\) 作用的层 \(F\)，定义
\[
F/\Gamma:=a\bigl(S\longmapsto F(S)/\Gamma\bigr).
\]
层化存在：可取 \(\mathrm{Prof}_U\) 的一个 \(V\)-小骨架，并在 \(\mathrm{Set}_V\) 中层化。由层化的局部提升、局部相等性质，商映射 \(p_F:F\to F/\Gamma\) 局部满射，且对 \(u,v\in F(S)\)，
\[
p_F(u)=p_F(v)
\iff
\begin{gathered}
\text{存在有限覆盖 }\{S_i\to S\}\text{ 及 }\gamma_i\in\Gamma,\\
v|_{S_i}=\gamma_i(u|_{S_i}).
\end{gathered}
\tag{1}
\]
这些性质可由层化的两次加号构造得到；覆盖的复合仍是有限覆盖，所以这里的“局部”符合题设。

现在令 \(K=T/\Gamma\)，赋予商拓扑。轨道等价关系是有限个闭图
\[
\bigcup_{\gamma\in\Gamma}\{(t,\gamma t):t\in T\}
\]
之并，故为闭关系。紧 Hausdorff 空间关于闭等价关系的商仍为紧 Hausdorff 空间，因此 \(K\) 紧 Hausdorff。

它还有闭开基：给定 \([t]\in O\subseteq K\)，其中 \(O\) 开，利用 \(T\) 的闭开基选取
\[
t\in C\subseteq p^{-1}(O),\qquad C\text{ 闭开}.
\]
则 \(\bigcup_{\gamma\in\Gamma}\gamma C\) 是不变闭开集，其像是包含 \([t]\) 且包含于 \(O\) 的闭开集。于是 \(K\) 是 \(U\)-小 profinite 空间。

令 \(q:h_T\to h_K\)。对任意 \(S\to K\)，满射
\[
S\times_KT\longrightarrow S
\]
是站点中的覆盖，并给出局部提升，所以 \(q\) 局部满射。若 \(x,y:S\to T\) 在 \(K\) 中像相同，则
\[
S_\gamma=\{s\in S:y(s)=\gamma x(s)\}
\]
是闭子空间，且有限族 \(\{S_\gamma\to S\}_{\gamma\in\Gamma}\) 联合满射。在 \(S_\gamma\) 上有 \(y=\gamma x\)。结合 (1)，得到
\[
h_T/\Gamma\cong h_K.
\]
特别地，\(h_K\) 是所要求的层商。上述层商结论对任意有限群作用都成立。

给定等变层 \(E\to H\)，取
\[
D=E/\Gamma,\qquad D\longrightarrow h_K
\]
及自然等变态射
\[
\eta:E\longrightarrow H\times_{h_K}D,\qquad
e\longmapsto(\pi(e),[e]).
\]

它局部满射：对目标截面 \((x,d)\)，先局部提升 \(d=[e]\)，再利用 \(q(x)=q(\pi(e))\)，进一步局部选取 \(\gamma\) 使 \(x=\gamma\pi(e)\)；此时 \(a_\gamma(e)\) 是所需提升。

它也是单射：若两个截面有相同像，则它们基底相同，且由 (1) 局部满足 \(e'=a_\gamma(e)\)。于是 \(\gamma\pi(e)=\pi(e)\)。作用自由，故在非空测试空间上必有 \(\gamma=1\)；空空间上的层截面唯一。因此 \(e'=e\)。

局部满射且单射的层态射是同构，因为局部提升在重叠处唯一，因而可以粘合。故
\[
E\cong H\times_{h_{T/\Gamma}}(E/\Gamma),
\]
且右侧作用仅改变 \(H\) 坐标。

---

**S2　有限集合上的纤维分类**

选取轨道代表集合 \(R\subseteq T\)，记 \(G_t=\Gamma_t\)。取纤维给出范畴等价
\[
\{\text{有限等变集合 }X\to T\}
\simeq
\prod_{t\in R}\mathrm{FinSet}^{G_t}.
\tag{2}
\]
其逆构造为
\[
(A_t)_{t\in R}\longmapsto
\bigsqcup_{t\in R}\Gamma\times_{G_t}A_t,
\]
其中
\[
[\gamma g,a]=[\gamma,ga],\qquad
[\gamma,a]\longmapsto\gamma t.
\]
这些集合有限，因为 \(\Gamma,T,A_t\) 均有限。对原来的 \(X\)，映射
\[
[\gamma,x]\longmapsto\gamma x,\qquad x\in X_t,
\]
是良定义的等变双射。等变态射恰好对应各纤维上的 \(G_t\)-等变映射，因此 (2) 同时分类了对象和态射。

可实现性的充要条件是
\[
\boxed{\quad G_t\text{ 在 }X_t\text{ 上作用平凡，对每个 }t\in R.\quad}
\tag{3}
\]

必要性：若 \(h_X\cong H\times_QD\)，则在单点截面上，\(G_t\) 固定第一坐标 \(t\)，也固定第二坐标，故固定整个纤维 \(X_t\)。

充分性：条件 (3) 也使每个其他基点的稳定子在其纤维上作用平凡。于是
\[
X\longrightarrow T\times_{T/\Gamma}(X/\Gamma),
\qquad x\longmapsto(\pi(x),[x])
\tag{4}
\]
是双射：

- 给定右侧元素，可以沿群作用把其轨道代表移动到指定基点，故满射；
- 同轨道且同基点的两个元素相差一个稳定子元素，故由 (3) 相等。

这是有限离散空间的等变同构。因此可取
\[
D=h_{X/\Gamma}\longrightarrow h_{T/\Gamma}.
\]

一般对象的自同构群为
\[
\operatorname{Aut}_{\Gamma,T}(X)
\cong\prod_{t\in R}\operatorname{Aut}_{G_t}(X_t).
\]
对于可实现对象，令 \(n_t=|X_t|\)，则
\[
\boxed{\quad
\operatorname{Aut}_{\Gamma,T}(X)
\cong\prod_{t\in R}\operatorname{Sym}(X_t)
\cong\prod_{t\in R}\mathfrak S_{n_t}.
\quad}
\]
由 Yoneda，这也计算了 \(h_X\) 在 \(H\) 上的等变自同构群。

---

**S3　一般层的完整下降**

定义
\[
Q:=H/\Gamma
=a\bigl(S\longmapsto H(S)/\Gamma\bigr),
\qquad q:H\to Q.
\]
由预层轨道商的泛性质及层化的伴随性质，对任意层 \(Y\)，自然地有
\[
\operatorname{Hom}_{\mathscr C}(Q,Y)
\cong
\{f:H\to Y:\ f\circ h_\gamma=f\ \text{对所有 }\gamma\in\Gamma\}.
\tag{5}
\]
因此 \(Q,q\) 满足要求。由 (1)，\(q\) 局部满射，且两个 \(H\)-截面在 \(Q\) 中相等，当且仅当它们局部相差群元素。这里不需要 \(\Gamma\) 有限，\(Q\) 也不必可表示。

对给定的 \(E\)，定义规范候选
\[
D_E:=E/\Gamma,\qquad
\bar\pi:D_E\to Q,
\]
以及
\[
\eta_E:E\longrightarrow H\times_QD_E,
\qquad e\longmapsto(\pi(e),[e]).
\tag{6}
\]

不预选 \(D\) 的充要判据是：
\[
\boxed{
\begin{aligned}
(\mathrm{St})\quad&
\text{对每个 }S\in\mathrm{Prof}_U,\ e\in E(S),\ \gamma\in\Gamma,\\
&h_\gamma(\pi(e))=\pi(e)
\ \Longrightarrow\ a_\gamma(e)=e.
\end{aligned}}
\tag{7}
\]
它也可以写成层态射条件。固定点空间
\[
T^\gamma=\{t\in T:\gamma t=t\}
\]
是 \(T\) 的闭子空间，故仍为 profinite；条件 (7) 等价于 \(a_\gamma\) 在
\[
E\times_Hh_{T^\gamma}
\]
上诱导恒等自同构，对每个 \(\gamma\) 都如此。

证明如下。任何实现都满足 (7)，因为稳定子固定第一坐标，而作用不改变第二坐标。另一方面，S1 中证明 \(\eta_E\) 局部满射的论证只用了 (1)，所以在此仍成立。

若 (7) 成立，而 \(\eta_E(e)=\eta_E(e')\)，则
\[
\pi(e)=\pi(e'),\qquad [e]=[e'].
\]
由 (1)，局部有 \(e'=a_\gamma(e)\)，且该 \(\gamma\) 固定 \(\pi(e)\)。由 (7)，这些局部截面相等，再由层的分离性得 \(e=e'\)。所以 \(\eta_E\) 单射，进而为同构。这证明了
\[
E\text{ 可实现}
\iff(\mathrm{St})
\iff\eta_E\text{ 是同构}.
\tag{8}
\]

下面给出对象、实现和态射的完整分类。记
\(\mathsf{Eq}^0_\Gamma(H)\) 为满足 (7) 的等变对象所成的满子范畴。则
\[
\Phi_Q:\mathscr C/Q\xrightarrow{\ \sim\ }\mathsf{Eq}^0_\Gamma(H),
\qquad
D\longmapsto H\times_QD
\tag{9}
\]
是范畴等价，逆函子为 \(E\mapsto E/\Gamma\)。

为验证这一点，对任意 \(D\to Q\)，投影
\[
H\times_QD\longrightarrow D
\]
局部满射；同一纤维中的两个截面，其 \(H\) 坐标由 (1) 局部相差群元素。因此
\[
(H\times_QD)/\Gamma\cong D.
\tag{10}
\]
另一方向的自然同构正是 (6)、(8)。于是，对可实现对象 \(E,F\)，
\[
\operatorname{Hom}_{\Gamma,H}(E,F)
\cong
\operatorname{Hom}_{Q}(E/\Gamma,F/\Gamma).
\tag{11}
\]
特别地，所有实现的底层对象都同构于 \(D_E\)。若把指定的实现同构
\(\alpha:E\overset{\sim}{\to}H\times_QD\) 也作为数据，则任意两个这样的实现对之间存在唯一保持该数据的同构。

现在取任意层 \(B\to Q\)，令
\[
H_B=H\times_QB.
\]
作用保持 \(B\) 坐标不变。由 (10)，
\[
H_B/\Gamma\cong B.
\]
而且 \(H_B\to B\) 局部满射，同一纤维的截面局部相差群元素。因此上述证明完全适用，得到
\[
\Phi_B:\mathscr C/B\xrightarrow{\ \sim\ }\mathsf{Eq}^0_\Gamma(H_B),
\qquad
D\longmapsto H_B\times_BD.
\tag{12}
\]
这里右侧的条件是：对所有测试空间和截面，固定其 \(H_B\) 基底的群元素必须固定该截面。逆函子仍为 \(F\mapsto F/\Gamma\)，规范实现为
\[
F\overset{\sim}{\longrightarrow}
H_B\times_B(F/\Gamma).
\]

这些分类与任意基底拉回相容。具体地，对 \(f:B'\to B\)，自然地有
\[
(F\times_BB')/\Gamma
\cong(F/\Gamma)\times_BB',
\tag{13}
\]
以及
\[
\Phi_{B'}(D\times_BB')
\cong\Phi_B(D)\times_BB'.
\tag{14}
\]
为验证 (13)，其自然比较映射局部满射，因为商截面局部可以提升到 \(F\)；它单射，因为两个提升具有相同商像时，由 (1) 局部相差群元素，同时 \(B'\) 坐标保持不变。因此它是同构。(14) 则来自纤维积的结合律。这些同构均由自然映射给出，故也相容于基底映射的恒等和复合。

---

**S4　单点上的检验**

**结论：不一定可实现，即使 \(\Gamma\) 有限且 \(T\) 是单点也不成立。**

取
\[
\Gamma=C_2=\{1,\sigma\},\qquad T=*,
\]
作用平凡，所以 \(H=Q=1\)。

令
\[
K=\mathbb N\cup\{\infty\}
\]
为离散 \(\mathbb N\) 的一点紧化：各自然数孤立，\(\infty\) 的邻域包含除有限多个自然数以外的所有点。它紧 Hausdorff，且单点 \(\{n\}\) 与余有限的无穷远邻域构成闭开基，故是无限 profinite 空间。由 \(\mathbb N\in U\)，它可取为 \(U\)-小。

定义子层
\[
L(S)=\operatorname{Cont}(S,K_{\mathrm{disc}})
\subseteq h_K(S).
\]
这里 \(K_{\mathrm{disc}}\) 表示同一集合的离散拓扑。\(L\) 是层：有限覆盖的总映射是商映射，所以兼容的局部连续映射到 \(K_{\mathrm{disc}}\) 可以唯一连续粘合。每个 \(L(S)\) 中的映射都有有限像，因为 \(S\) 紧而目标离散。

在层范畴中构造推出
\[
E=h_K\amalg_Lh_K.
\tag{15}
\]
交换两份 \(h_K\) 给出自同构 \(\sigma\)，且 \(\sigma^2=1\)。取唯一的 \(\pi:E\to1\)。

先核验单点条件。单点的每个覆盖都有某个非空成员，选取其中一点即可得到该覆盖成员到单点映射的截面。因此单点上的每个覆盖筛都是最大筛，层化不改变预层在 \(*\) 上的值。于是
\[
E(*)=K\amalg_KK=K,
\]
而交换两份的作用在这里是恒等。题设的单点稳定子条件完全成立。

但 \(\sigma\) 不是 \(E\) 的恒等自同构。令 \(u,v\in E(K)\) 分别为两份中的 \(\mathrm{id}_K\) 的像。假设 \(u=v\)。根据层化的局部相等性质，存在有限覆盖
\[
\{r_i:S_i\to K\}
\]
使两份中的 \(r_i\) 在预层推出中相等。由于该推出沿子集 \(L(S_i)\) 粘合，这恰好意味着
\[
r_i\in L(S_i).
\]
于是每个 \(r_i\) 都有有限像，有限多个这样的像无法覆盖无限集合 \(K\)，矛盾。因此
\[
u\ne v,\qquad \sigma(u)=v.
\]

若 \(E\) 在 \(Q=1\) 上可实现，则 \(E\cong1\times_1D\)，其群作用必为恒等，这与上述非平凡作用矛盾。反例核验完毕。

---

**S5　局部满射的基底检验**

**结论：必可在 \(Q\) 上实现。**

设 \(B\to Q\) 局部满射，且
\[
E_B:=E\times_QB
\]
在 \(B\) 上可实现。使用 S3 的判据即可验证原来的 \(E\)。

取任意 \(S,e\in E(S),\gamma\in\Gamma\)，满足
\[
h_\gamma(\pi(e))=\pi(e).
\]
由 \(B\to Q\) 的局部满射性，存在有限覆盖 \(\{S_i\to S\}\) 和
\(b_i\in B(S_i)\)，使 \(b_i\) 的像为 \(q\pi(e)|_{S_i}\)。于是
\[
(e|_{S_i},b_i)\in E_B(S_i),
\]
且 \(\gamma\) 固定它的 \(H_B\) 基底。

由于 \(E_B\) 可实现，其稳定子作用平凡，故
\[
(a_\gamma(e)|_{S_i},b_i)=(e|_{S_i},b_i).
\]
由层的分离性，\(a_\gamma(e)=e\)。所以 \(E\) 满足 (7)，从而可实现。

规范实现为 \(D=E/\Gamma\)。由 (13) 及实现的分类，任何给定的局部实现 \(D_B\) 都同构于
\[
D\times_QB.
\]

---

**S6　非空基底与全局结论**

**结论：仅有非空可表示基底不足以反映可实现性。**

取 \(\Gamma=C_2=\{1,\sigma\}\)，令
\[
T=\{0,1\}
\]
具有平凡作用。因此
\[
H=Q=h_T,\qquad q=\mathrm{id}.
\]
令
\[
X=\{u,v,w\},\qquad
\pi(u)=0,\quad \pi(v)=\pi(w)=1,
\]
并规定
\[
\sigma(u)=u,\qquad \sigma(v)=w,\qquad \sigma(w)=v.
\]
这是有限等变集合 \(X\to T\)，取 \(E=h_X\)。

令 \(B=h_*\to Q\) 选取 \(0\)。它是非空可表示层，且
\[
H\times_QB\cong B,\qquad
E\times_QB\cong h_{\{u\}}\cong B,
\]
作用平凡，因此拉回对象在 \(B\) 上可实现，可取 \(D_B=B\)。

然而原对象不可实现：基点 \(1\) 的稳定子是整个 \(\Gamma\)，它非平凡地交换纤维中的 \(v,w\)，违反 S2 的条件，也违反 S3 的判据。这里 \(B\to Q\) 不局部满射，因为截面 \(1\in Q(*)\) 无法在任何覆盖上提升到 \(B\)。

由以上结果，可用的检验原则如下：

- **完整判据：**检查所有 profinite 测试空间上的稳定子作用，即 (7)。
- **基底检验：**可实现性沿任意基底拉回保持；沿局部满射基底拉回也被反映。因此局部满射基底上的检验充要。
- **较弱检验：**单点稳定子条件通常只是必要条件；非空可表示基底通常也不足以检验全局可实现性。
- **截面由点值决定时：**若每个映射
  \[
  E(S)\longrightarrow\prod_{s\in S}E(*)
  \]
  都单射，则单点条件足够。因为 (7) 中的两截面在每一点相等，便必整体相等。可表示层满足这一条件，因而适用于 S2。
- **自由作用时：**稳定子判据自动成立。S1 中有限性的作用还包括保证轨道商可由 profinite 空间表示。