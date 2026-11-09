记 \(a\) 为层化，测试对象一律记为 \(S\in\mathrm{Prof}_U\)。该站点可取 \(V\)-小骨架，故以下层化与商均存在于给定宇宙内。有限联合满射族的并是紧空间到 Hausdorff 空间的商映射，因此连续映射可沿覆盖下降，所有 \(h_T\) 都是层。空覆盖还保证每个层 \(F\) 都满足 \(F(\varnothing)=\{*\}\)。

先记录一个通用事实。若层 \(F\) 带有 \(\Gamma\)-作用，定义
\[
F_\Gamma:=a\bigl(S\longmapsto F(S)/\Gamma\bigr).
\]
由层化的伴随性质，\(F_\Gamma\) 是层范畴中的作用商。层化的局部描述给出：

- \(F_\Gamma\) 的每个截面都在某有限覆盖上来自 \(F\)；
- 对 \(x,x'\in F(S)\)，其商中像相等，当且仅当存在有限覆盖 \(\{u_i:S_i\to S\}\) 及 \(\gamma_i\in\Gamma\)，使
  \[
  u_i^*x'=a_{\gamma_i}(u_i^*x).
  \tag{L}
  \]

这是层化中“局部有代表、相等可局部检验”的直接应用；覆盖的复合仍是有限覆盖。

**S1　有限群的自由作用**

令 \(Z=T/\Gamma\) 为轨道集合，赋予商拓扑，记 \(r:T\to Z\)。

轨道等价关系是有限个作用映射之图的并，因而在 \(T\times T\) 中闭。紧 Hausdorff 空间的闭等价关系商仍紧 Hausdorff，故 \(Z\) 紧 Hausdorff。

它还有 clopen 基：若 \(W\subset T\) 是包含 \(t\) 的不变开集，利用 profinite 空间的 clopen 基，取
\[
t\in C\subset W,\qquad C\text{ clopen}.
\]
则 \(\bigcup_{\gamma\in\Gamma}\gamma C\) 是包含整个轨道的、不变的 clopen 子集，其像在 \(Z\) 中 clopen。这证明 \(Z\) 全不连通。其集合与拓扑均为 \(U\)-小，所以 \(Z\in\mathrm{Prof}_U\)。

由于作用自由，
\[
\Gamma\times T\xrightarrow{\sim}T\times_ZT,
\qquad
(\gamma,t)\longmapsto(t,\gamma t)
\tag{1}
\]
是连续双射；源紧、目标 Hausdorff，故是同胚。

\(h_T\to h_Z\) 局部满射：对任意 \(S\to Z\)，满射
\[
S\times_ZT\longrightarrow S
\]
就是一个覆盖，并提供所需提升。对任意层 \(Y\)，沿覆盖 \(T\to Z\) 的层条件及 (1) 给出
\[
\operatorname{Hom}(h_Z,Y)
\cong
\{f:h_T\to Y:\ f h_\gamma=f\ \forall\gamma\in\Gamma\}.
\]
这里匹配条件等价于逐个 \(\gamma\) 的不变性，是因为
\(Y(\Gamma\times T)\cong\prod_{\gamma\in\Gamma}Y(T)\)。
因此 \(h_Z\) 正是层商。

现在给定等变层 \(E\to H\)，令 \(D=E_\Gamma\)。不变映射 \(E\to h_Z\) 诱导 \(D\to h_Z\)，并有典范等变映射
\[
j:E\longrightarrow H\times_{h_Z}D,
\qquad e\longmapsto(\pi(e),[e]).
\]

证明它是同构：

- 给定右侧截面 \((t,d)\)，先局部将 \(d\) 提升为 \(e\)。此时 \(\pi(e)\) 与 \(t\) 有相同轨道像。由 (1)，再作有限 clopen 分割后有 \(t=\gamma\pi(e)\)，于是 \(a_\gamma(e)\) 是所需提升。
- 若 \(j(e)=j(e')\)，由 (L)，局部有 \(e'=a_\gamma(e)\)，且 \(\gamma\pi(e)=\pi(e)\)。在非空测试对象上，自由性迫使 \(\gamma=1\)；在空对象上截面唯一。因此局部、进而全局有 \(e=e'\)。

局部存在且唯一的提升可由层条件粘合，所以 \(j\) 是同构。每个等变层都在 \(h_{T/\Gamma}\) 上实现。

**S2　有限集合上的纤维分类**

对所选轨道代表 \(t\)，令 \(F_t=X_t\)。它是有限 \(\Gamma_t\)-集合。取纤维给出范畴等价
\[
\{\text{有限 }\Gamma\text{-集合 }X\to T\}
\simeq
\prod_{[t]\in T/\Gamma}\mathrm{FinSet}^{\Gamma_t}.
\tag{2}
\]
逆构造是
\[
(F_t)_t\longmapsto
\bigsqcup_t\Gamma\times_{\Gamma_t}F_t,
\qquad [g,f]\longmapsto gt,
\]
其中 \((gk,f)\sim(g,kf)\)。映射 \([g,f]\mapsto gf\) 将该构造同构到原来的 \(X\)。

态射完全由代表纤维上的映射决定：
\[
\operatorname{Hom}_{\Gamma/T}(X,X')
\cong
\prod_t\operatorname{Hom}_{\Gamma_t}(F_t,F'_t).
\tag{3}
\]
逆向延拓公式为 \([g,f]\mapsto[g,u_t(f)]\)，其良定义性正是 \(u_t\) 的 \(\Gamma_t\)-等变性。若需按同构类描述，每个 \(F_t\) 又唯一分解为若干传递集合 \(\Gamma_t/K\)，其中 \(K\) 按共轭类计。

这里 \(Q=h_{T/\Gamma}\) 是层商：有限离散空间的可表示层是有限个终对象的余积，取商就是把这些分量按轨道合并。

可实现性的充要条件为
\[
\boxed{\text{每个 }\Gamma_t\text{ 在 }F_t\text{ 上作用平凡。}}
\tag{4}
\]

必要性：在 \(H\times_QD\) 中，固定 \(t\) 的元素只改变第一坐标，故固定整个 \(t\)-纤维。

充分性：令 \(Y=X/\Gamma\)，带有自然映射 \(Y\to T/\Gamma\)。典范映射
\[
X\longrightarrow T\times_{T/\Gamma}Y,\qquad
x\longmapsto(\pi(x),[x])
\]
总是满射。若两个元素有相同像，它们相差某个固定其底点的群元素；由 (4)，它们相等。因此该映射是等变双射，给出实现 \(D=h_Y\)。

任意实现层也必同构于这个有限可表示层：在轨道 \([t]\) 上，其纤维由拉回确定为 \(h_{F_t}\)，而有限离散基底上的层由这些纤维的余积恢复。

可实现对象的自同构群为
\[
\boxed{
\operatorname{Aut}_{\Gamma/T}(X)
\cong
\operatorname{Aut}_{\Gamma/H}(h_X)
\cong
\operatorname{Aut}_Q(D)
\cong
\prod_t\operatorname{Sym}(F_t).
}
\]
第一项到第二项使用 Yoneda 的全忠实性；最后一项也直接来自 (3) 与平凡稳定子作用。

**S3　一般层的完整下降**

不再假设 \(\Gamma\) 或 \(T\) 有限。定义
\[
Q=H_\Gamma
=a\bigl(S\longmapsto\operatorname{Cont}(S,T)/\Gamma\bigr),
\]
并令 \(q:H\to Q\) 为商映射。它不变且局部满射。由层化的伴随性质，
\[
\operatorname{Hom}_{\mathcal C}(Q,Y)
\cong
\{f:H\to Y:\ f h_\gamma=f\ \forall\gamma\in\Gamma\},
\]
且此对应关于 \(Y\) 自然。这构造不要求 \(Q\) 可表示。

不预选实现层的充要判据是
\[
\boxed{
\begin{gathered}
\forall S\in\mathrm{Prof}_U,\quad
\forall e\in E(S),\quad\forall\gamma\in\Gamma,\\
\gamma\pi(e)=\pi(e)\quad\Longrightarrow\quad a_\gamma(e)=e.
\end{gathered}}
\tag{Stab}
\]
也可表述为：对每个 \(\gamma\)，\(a_\gamma\) 在
\[
E\times_Hh_{T^\gamma},
\qquad T^\gamma=\{t\in T:\gamma t=t\}
\]
上的限制为恒等。这里 \(T^\gamma\) 是两个连续映射的等化子，因而是闭 profinite 子空间。

为证明判据并构造实现，令
\[
D=E_\Gamma,\qquad
j_E:E\longrightarrow H\times_QD,\quad
e\longmapsto(\pi(e),[e]).
\tag{5}
\]
映射 \(D\to Q\) 由不变映射 \(q\pi\) 诱导，且 \(j_E\) 等变。

首先，\(j_E\) 总是局部满射。给定 \((h,d)\)，局部提升 \(d\) 为 \(e\)。由
\(q(h)=q(\pi(e))\) 及 (L)，进一步局部有
\(h=\gamma\pi(e)\)，故 \(a_\gamma(e)\) 提供提升。

若 (Stab) 成立且 \(j_E(e)=j_E(e')\)，则由 (L)，局部有
\[
e'=a_\gamma(e),\qquad \gamma\pi(e)=\pi(e).
\]
所以局部 \(e'=e\)，再由层的分离性得全局相等。因此 \(j_E\) 是单态且局部满射，从而是同构。

反之，任何实现 \(E\simeq H\times_QD'\) 都满足 (Stab)：固定第一坐标的群元素固定整个有序对。因此以下三条等价：

1. \(E\) 可在 \(Q\) 上实现；
2. (Stab) 成立；
3. 典范映射 \(j_E\) 是同构。

这也给出完整的对象及态射分类。令 \(\mathscr R(H,\Gamma)\) 为满足 (Stab) 的等变对象所成的全子范畴，则
\[
\boxed{
\mathcal C/Q\simeq\mathscr R(H,\Gamma),
\qquad
D\longmapsto H\times_QD,\quad
E\longmapsto E_\Gamma.
}
\tag{6}
\]
事实上，对任意 \(D\to Q\)，投影 \(H\times_QD\to D\) 局部满射；两个具有相同 \(D\)-坐标的截面，由 (L) 局部相差群作用。因此
\[
(H\times_QD)_\Gamma\simeq D.
\]
结合 (5)，两个函子互逆。特别地，
\[
\operatorname{Hom}_{\Gamma/H}(E,E')
\cong
\operatorname{Hom}_Q(E_\Gamma,E'_\Gamma)
\]
对所有可实现对象成立。

对固定的 \(E\)，若 (Stab) 失败，实现不存在；若成立，实现层必同构于 \(E_\Gamma\)。若把指定同构
\(E\simeq H\times_QD\) 也作为实现数据，则任意两个实现之间存在唯一相容同构。

现在取任意层 \(B\to Q\)，置
\[
H_B=H\times_QB.
\]
作用只改变 \(H\)-坐标。由局部提升及 (L)，
\[
(H_B)_\Gamma\simeq B.
\]
因此同样得到
\[
\boxed{
\mathcal C/B\simeq\mathscr R(H_B,\Gamma),
}
\tag{7}
\]
其中右侧条件仍是在所有测试对象上，固定底截面的群元素固定其上的截面。逆函子仍是取作用商。

这些分类与任意基底拉回相容。若 \(B'\to B\)，则自然有
\[
(H_B\times_BD_B)\times_BB'
\simeq H_{B'}\times_{B'}(D_B\times_BB').
\]
此外，对任意等变 \(F\to H_B\)，包括尚不可实现的对象，都有
\[
(F\times_BB')_\Gamma
\simeq F_\Gamma\times_BB'.
\tag{8}
\]
证明是：右侧截面局部可将 \(F_\Gamma\)-坐标提升到 \(F\)，得到左侧代表；两个代表相等恰由 (L) 局部相差群作用，且作用保持 \(B'\)-坐标。特别地，
\[
(E\times_QB)_\Gamma\simeq E_\Gamma\times_QB,
\]
而拉回后的典范映射正是 \(j_E\) 的基变。

**S4　单点上的检验**

结论：**不一定可实现**，即使 \(\Gamma,T\) 都有限。

取
\[
T=*,\qquad \Gamma=C_2,\qquad
P=(\mathbb Z/3)^{\mathbb N}.
\]
因 \(\mathbb N\in U\)，\(P\) 是 \(U\)-小无限 profinite 阿贝尔群。

定义 \(h_P\) 的阿贝尔群子层
\[
L(S)=\operatorname{Cont}(S,P_{\mathrm{disc}}).
\]
它是层，因为到离散空间的连续映射可沿有限联合满射下降；每个这样的映射又因 \(S\) 紧而具有有限像。令
\[
A=a\bigl(S\longmapsto h_P(S)/L(S)\bigr)
\]
为商阿贝尔群层。

核验两个关键性质。

首先，\(A(*)=0\)。任意 \(a\in A(*)\) 可在某有限覆盖上提升到 \(h_P\)。覆盖中至少有一个非空对象，选择其一点并拉回，就把 \(a\) 提升成 \(P=h_P(*)\) 中的元素。但
\(L(*)=P\)，故该像为零。

其次，\(A\ne0\)。考虑 \(\operatorname{id}_P\) 在 \(A(P)\) 中的像。若它为零，则局部相等性给出有限覆盖
\(\{u_i:S_i\to P\}\)，使每个 \(u_i\) 属于 \(L(S_i)\)，因而具有有限像。联合满射便迫使
\[
P=\bigcup_i u_i(S_i)
\]
有限，矛盾。

\(A\) 满足 \(3A=0\)，故取负自同构并非恒等：否则还有 \(2A=0\)，从而 \(A=0\)，矛盾。

令 \(E=A\to h_*\)，并让 \(C_2\) 的生成元按取负作用。单点截面只有零，所以题设条件全部成立。然而 \(Q=h_*\)，在 \(Q\) 上实现的作用必须平凡，而此作用不平凡。因此 \(E\) 不可实现。

**S5　局部满射的基底检验**

结论：**必可实现**。

设 \(B\to Q\) 局部满射，且 \(E_B=E\times_QB\) 可在 \(B\) 上实现。验证原对象的 (Stab)。

取 \(e\in E(S)\) 及满足 \(\gamma\pi(e)=\pi(e)\) 的 \(\gamma\)。将截面
\(q\pi(e)\in Q(S)\) 沿 \(B\to Q\) 局部提升，得到有限覆盖
\(\{S_i\to S\}\) 和 \(b_i\in B(S_i)\)。于是
\[
(e|_{S_i},b_i)\in E_B(S_i).
\]
\(\gamma\) 固定它的 \(H_B\)-底截面。由于 \(E_B\) 可实现，S3 的必要条件给出
\[
a_\gamma(e)|_{S_i}=e|_{S_i}.
\]
由层的分离性，\(a_\gamma(e)=e\)。因此 (Stab) 成立，S3 给出原对象的实现。

任意拉回又显然保持实现，所以沿局部满射 \(B\to Q\) 有
\[
E\text{ 可实现}
\quad\Longleftrightarrow\quad
E\times_QB\text{ 可在 }B\text{ 上实现}.
\]

**S6　非空基底与全局结论**

结论：**非空可表示基底不足以反映可实现性**。

取
\[
\Gamma=C_2=\{1,\sigma\},\qquad T=\{0,1\},
\]
让 \(\Gamma\) 在 \(T\) 上平凡作用。因此 \(Q=H=h_T\)。

令
\[
X=\{a,b,c\},\qquad
\pi(a)=0,\quad \pi(b)=\pi(c)=1,
\]
并令 \(\sigma(a)=a,\ \sigma(b)=c,\ \sigma(c)=b\)。这是有限等变映射，取 \(E=h_X\)。

选择非空可表示层 \(B=h_*\to Q\)，对应点 \(0\)。此时
\[
H\times_QB\simeq h_*,
\qquad
E\times_QB\simeq h_{\{a\}},
\]
作用平凡，故拉回后可在 \(B\) 上实现。

但原对象不可实现：\(\sigma\) 固定 \(\pi(b)=1\)，却不固定 \(b\)，违反 S2 或 S3 的判据。这里 \(B\to Q\) 不是局部满射，因为截面 \(1\in Q(*)\) 在任何覆盖上都不能提升到只映入 \(0\) 的 \(B\)。

可用的检验原则如下：

- **稳定子检验：**在所有测试 profinite 空间上检验 (Stab)，是完整的充要条件。仅检验单点一般不足；S2 的有限可表示对象则可用普通纤维检验。
- **基底检验：**任意拉回保持可实现性，局部满射拉回反映可实现性。同样可沿一个联合局部满射的基底族检验，证明逐局部提升应用 S5。
- **非空性的作用：**一般不能代替局部满射。不过当 \(Q=*\) 时，每个非空可表示 \(B\to *\) 都因选取一点而成为分裂满射，所以此时 S5 适用。
- **自由作用：**若底空间上的作用自由，(Stab) 自动成立，故所有等变层都在层商上实现；当群有限时，S1 进一步保证该商由 profinite 轨道空间表示。