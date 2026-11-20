# 审阅结论

原答卷各阶段的**最终判断和主要构造均正确**，S1、S4 第二问、S6 的论证基本完整。但原答卷还不能原样认定为完全严谨，主要有四处需要修正：

1. **S3 对 S1 指数律的引用不成立**，这是表示性证明中的关键缺口；
2. **S2 第 3 小节错误转述了“由原连续映射诱导”的自然变换**；
3. **S4 的反例遗漏了基本邻域归约，并不准确地使用了点集距离**；
4. **S5 关于超滤子的“恰有一个不属于”断言错误**。

这些问题均可局部修复，不需要更换最终结论、主要构造或反例。

---

## S1：正确

求值连续性的证明成立。局部紧 Hausdorff 空间是正则的，因而对 \(x_0\in f_0^{-1}(W)\)，可以取开邻域 \(V\)，使
\[
K=\overline V\subset f_0^{-1}(W)
\]
且 \(K\) 紧。随后
\[
[K,W]\times V\subset ev^{-1}(W)
\]
即给出所需连续性。

柯里化双射也正确：

- \(\Phi(g)=ev\circ(g\times\mathrm{id}_X)\) 连续；
- 反向柯里化时，固定 \(z\) 所得切片连续，而 \(Z\to C_{co}(X,Y)\) 的连续性由管道引理和 \(K\) 的紧性推出，不要求 \(Z\) 局部紧；
- 关于 \(Z,X,Y\) 的自然性等式均正确。

未发现实质问题。

---

## S2：主定理正确，第 3 小节有一处概念错误

### 1. 两种探针给出相同的 \(k\)-拓扑：正确

对紧 Hausdorff 空间 \(K\)，取其底集的离散拓扑 \(D\)，并利用
\[
\pi:\beta D\twoheadrightarrow K
\]
是有效的证明。

\(\beta D\) 是紧 Hausdorff 且零维的空间，故为 profinite；\(\pi\) 是紧空间到 Hausdorff 空间的连续闭满射，因而是商映射。于是由
\[
\pi^{-1}(f^{-1}(A))\ \text{闭}
\]
可推出 \(f^{-1}(A)\) 闭。

\(\beta D\) 的 \(U\)-小型性也没有障碍：其底集可实现为 \(D\) 上超滤子的集合，即 \(\mathcal P(\mathcal P(D))\) 的子集；由 \(D\in U\) 及宇宙的封闭性可得。

### 2. \(\mathrm{Nat}(h_X,h_Y)\cong C(kX,kY)\)：正确

单点空间上的求值定义底集映射 \(g\)，再沿点包含 \(i_s:*\to S\) 使用自然性，确实得到
\[
\alpha_S(f)=g\circ f.
\]
因此 \(\alpha\) 完全由 \(g\) 决定。

由于 \(kX\) 的拓扑是关于这些探针的最终拓扑，所有 \(g\circ f\) 连续恰好等价于
\[
g:kX\longrightarrow kY
\]
连续。反向由后复合构造自然变换也成立。

### 3. “由原拓扑连续映射诱导”的转述不准确

原答卷称：

> 连续映射 \(f:X\to Y\) 诱导的自然变换对应于集合 \(C(X,kY)\subset C(kX,kY)\)。

这一般不成立。原连续映射 \(f:X\to Y\) 在 S2 的同构下对应的是
\[
k(f):kX\longrightarrow kY.
\]
准确地说，\(g\in C(kX,kY)\) 所对应的自然变换由原连续映射诱导，当且仅当其底集映射
\[
g:X\longrightarrow Y
\]
在原拓扑下连续。

例如，若 \(X\) 非紧生成，恒等映射 \(\mathrm{id}_X:X\to X\) 当然原拓扑连续，并诱导恒等自然变换；但
\[
\mathrm{id}:X\longrightarrow kX
\]
不连续，否则就会有 \(kX=X\)。

这不影响最终充要条件。必要性可修复为：取 \(Y=kX\)，考虑
\(\mathrm{id}:kX\to kX=kY\) 所对应的自然变换。若它由原连续映射 \(f:X\to kX\) 诱导，单点求值迫使 \(f=\mathrm{id}\)，故 \(\mathrm{id}:X\to kX\) 连续。结合恒有连续的 \(\mathrm{id}:kX\to X\)，得到 \(kX=X\)。充分性仍按原思路成立。

---

## S3：构造正确，但表示性证明有关键缺口

### 1. 空间构造及前几步正确

取
\[
M(X,Y)=k\bigl(C_{co}(kX,kY)\bigr)
\]
是正确的实现。其底集为 \(C(kX,kY)\)。

紧开拓扑因 \(kY\) Hausdorff 而 Hausdorff：若 \(f(x)\ne g(x)\)，以不相交开集 \(O,O'\) 分离这两点，则
\[
[\{x\},O],\qquad [\{x\},O']
\]
分离 \(f,g\)。再作 \(k\)-化仍 Hausdorff，且自动紧生成。

表示性证明中的
\[
h_S\times h_X\cong h_{S\times X},\qquad
k(S\times X)=k(S\times kX)
\]
以及利用 \(S\) 紧 Hausdorff、\(kX\) 为 \(k\)-空间得到
\[
k(S\times kX)=S\times kX
\]
均可成立。最后一步使用 Cohen 定理时，其局部紧 Hausdorff 与 \(k\)-空间的条件在此满足。

### 2. 第 4 步不能由 S1 推出

原答卷声称由 S1 得到
\[
C(S\times kX,kY)\cong C(S,C_{co}(kX,kY)).
\]
这不是 S1 的直接结论。

S1 中被柯里化、并作为紧开拓扑定义域的变量必须局部紧；在这里该变量是 \(kX\)，而题目没有假设 \(kX\) 局部紧。若把 S1 的局部紧变量取为 \(S\)，得到的反而是
\[
C(kX,C_{co}(S,kY))\cong C(kX\times S,kY),
\]
并非所需形式。

因此，原答卷在这里给出的书面论证无效，而这一步正是表示性同构链的核心。

### 3. 用标准指数伴随即可修复

可直接使用原答卷后面已经援引的标准定理：**紧生成 Hausdorff 空间范畴 \(\mathbf{CGHaus}\) 是笛卡尔闭范畴**，其指数对象正是
\[
kC_{co}(A,B).
\]
这里 \(S,kX,kY\) 都属于该范畴：\(S\) 紧 Hausdorff，因而紧生成；\(kX,kY\) 由构造紧生成。因此
\[
C(S,M(X,Y))
\cong C(S\times_k kX,kY).
\]
再由 Cohen 定理，
\[
S\times_k kX=k(S\times kX)=S\times kX.
\]
结合前面的恒等式及 S2，得到
\[
\begin{aligned}
C(S,M(X,Y))
&\cong C(S\times kX,kY)\\
&\cong C(k(S\times X),kY)\\
&\cong \mathrm{Nat}(h_{S\times X},h_Y)\\
&\cong H_{X,Y}(S).
\end{aligned}
\]
各步均为柯里化或预复合，故关于 profinite \(S\) 自然。

在该指数结构下，原答卷随后关于连续求值、任意 Hausdorff \(Z\) 的伴随同构，以及 \(X,Y\) 中连续映射的自然性，方向与公式均正确。需要修正的是第 4 步的依据，而不是 \(M(X,Y)\) 的选取或最终表示性结论。

---

## S4：两个判断正确，反例证明需补细节

### 1. 求值不必连续：反例有效

取 \(X=\mathbb Q\)、\(Y=\mathbb R\) 确实给出反例，但原证明有两处不严谨。

**基本邻域问题。** 零函数的一般基本邻域是有限交
\[
U=\bigcap_{i=1}^n[K_i,O_i],
\]
不一定是单个 \([K,(-\varepsilon,\varepsilon)]\)。可忽略 \(K_i=\varnothing\) 的平凡项，令
\[
K=\bigcup_iK_i,
\]
并取 \(\varepsilon>0\) 使
\[
(-\varepsilon,\varepsilon)\subset\bigcap_iO_i.
\]
则 \(K\) 紧且
\[
[K,(-\varepsilon,\varepsilon)]\subset U.
\]
所以只需排除单个这种邻域即可。

**正距离问题。** 一般由“\(K\) 闭且 \(q\notin K\)”不能推出
\(\operatorname{dist}(q,K)>0\)。这里应使用 \(K\subset\mathbb Q\) 紧，故其在 \(\mathbb R\) 中也紧；当 \(K\ne\varnothing\) 时，
\[
\delta=\min_{k\in K}|q-k|>0.
\]
\(K=\varnothing\) 的情形可任意取 \(\delta>0\)。

完成上述补充后，原构造
\[
f(x)=2\max\left(0,1-\frac{|x-q|}{\delta}\right)
\]
连续，满足 \(f|_K=0\)，而 \(f(q)=2\)。因此任何所述 \(U\times V\) 都不可能映入 \((-1,1)\)，求值在 \((0,0)\) 处不连续。

### 2. 第一可数蕴含 \(kX=X\)：证明正确

若 \(A\) 为 \(k\)-闭集而 \(x_0\in\overline A\setminus A\)，第一可数性给出 \(x_n\in A\) 且 \(x_n\to x_0\)。集合
\[
K=\{x_0\}\cup\{x_n:n\ge1\}
\]
是紧 Hausdorff 子空间。由 \(k\)-闭性，\(A\cap K\) 在 \(K\) 中闭，故 \(x_0\in A\)，矛盾。论证完整。

---

## S5：结论和反例正确，有一处超滤子断言错误

一般反例
\[
f=\mathrm{id}:kZ\longrightarrow Z
\]
正确。对任意紧 Hausdorff 来源 \(S\)，都有
\[
C(S,kZ)=C(S,Z),
\]
所以 \(h_f\) 是自然同构；而当 \(kZ\ne Z\) 时，逆映射 \(Z\to kZ\) 不连续，故 \(f\) 不是原拓扑同胚。

具体的自由超滤子空间也可行，但原答卷称，对两个不交无限集 \(A_1,A_2\)：

> 由超滤子性质，恰有一个集合不属于 \(\mathcal U\)。

这不正确。二者可能都不属于 \(\mathcal U\)，因为它们不是互补集合。

正确且足够的事实是：由于 \(A_1\cap A_2=\varnothing\)，它们**不可能同时属于** \(\mathcal U\)，故至少一个不属于。记该集为 \(A_1\)，则
\[
\mathbb N\setminus A_1\in\mathcal U.
\]
于是
\[
W=(\mathbb N\setminus A_1)\cup\{p\}
\]
是 \(p\) 的开邻域，而
\[
\{W\}\cup\{\{n\}:n\in A_1\}
\]
构成没有有限子覆盖的开覆盖。其余论证照常成立，因而所有紧子集有限、\(kZ\) 离散以及 \(\{p\}\) 非开的结论均正确。

---

## S6：正确，依赖于修复后的 S3 指数结构

由 \(\mathbf{CGHaus}\) 的笛卡尔闭性，将底集上为
\[
((g,f),x)\longmapsto g(f(x))
\]
的连续复合求值映射取伴随，得到连续映射
\[
\circ:M(Y,Z)\times_kM(X,Y)\longrightarrow M(X,Z).
\]
结合律和单位律由底集函数逐点相等推出；单点选取 \(\mathrm{id}_{kX}\) 的映射连续。因此这部分论证合法。

关于可识别范围，原答卷的结论正确：
\[
h_f\text{ 为自然同构}
\iff
k(f):kX\to kY\text{ 为同胚}.
\]
S2 已将自然变换及其复合对应到 \(k\)-化后的连续映射及其复合，所以自然逆恰好给出 \(k(f)\) 的连续逆。

若 \(X,Y\) 第一可数，S4 给出 \(kX=X\)、\(kY=Y\)，故 \(k(f)\) 的同胚就是原映射 \(f:X\to Y\) 的同胚。“能升级为普通同胚”的判断正确。

---

## 保留、新增/修正、未完成情况及自评

- **保留**：上一版对 S1—S6 最终结论的判断，以及对四处问题的定位。
- **新增/修正**：进一步明确 S2 中正确的对应对象是 \(k(f)\)，并在 S3 修复中逐项写明 \(\mathbf{CGHaus}\) 指数伴随与 Cohen 定理的适用条件；S4 补充了空紧集情形的处理。
- **仍未完成/不确定**：本审阅没有未解决的数学疑点。修复所用的是标准定理，未在此重新证明这些定理本身。
- **自评**：本审阅逐阶段覆盖了原答卷，区分了正确结论与无效论证，并给出了可核查的修复路径。原答卷应判为“主要结论正确、证明尚需局部修正”，不应原样背书为完全严谨。