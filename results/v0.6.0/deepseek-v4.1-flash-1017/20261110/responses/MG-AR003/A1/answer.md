## 总评

答卷的多数**最终数学结论**是正确的，但作为完整证明答卷，**不能判为完全正确/完整**。主要问题有：

1. **S2 第三部分**把“由原拓扑连续映射诱导的自然变换”误认成集合 \(C(X,kY)\)，这是实质性的集合识别错误；最终充要条件虽仍成立，但答卷的必要性证明不能按原文成立。
2. **S3 第 4 步**错误援引 S1：S1 要求被指数化的空间 \(kX\) 局部紧，而题中只能保证 \(S\) 紧；该步的双射实际应由 \(\mathbf{CGHaus}\) 的笛卡尔闭性得到，不能用 S1 直接推出。
3. **S6 结合律**的点态证明少写了典范结合子（associator），严格说不完整；补上后结论正确。
4. 还有一些小的表述/边缘情形问题，见下。

---

## S1　局部紧输入

**判断：正确。**

- 求值映射连续性：局部紧 Hausdorff 空间 \(X\) 中，给定 \(x_0\in f_0^{-1}(W)\)，可取紧邻域 \(K\) 使
  \[
  x_0\in \operatorname{int}K\subset K\subset f_0^{-1}(W).
  \]
  于是 \([K,W]\times \operatorname{int}K\) 是 \((f_0,x_0)\) 的邻域并映入 \(W\)。这与答卷论证一致。
- 柯里化双射：
  \[
  \Phi:C(Z,C_{co}(X,Y))\to C(Z\times X,Y),\qquad
  \Phi(g)(z,x)=g(z)(x).
  \]
  其连续性用求值映射连续性；逆向 \(\Psi\) 的连续性用管道引理：对紧集 \(K\subset X\)，
  \[
  \Psi(F)^{-1}([K,W])
  =\{z:F(\{z\}\times K)\subset W\},
  \]
  由 \(F^{-1}(W)\) 开及 \(K\) 紧，可得每点有邻域 \(V\) 使 \(V\times K\subset F^{-1}(W)\)。
- 关于 \(Z,Y,X\) 的自然性公式均正确。

---

## S2　探针能检测的映射

### 1. Profinite 探针与紧 Hausdorff 探针

**结论正确。**

对任意紧 Hausdorff \(K\)，取 \(D=K\) 赋离散拓扑，\(\beta D\) 为 profinite，恒等映射 \(D\to K\) 延拓为连续满射
\[
\pi:\beta D\to K.
\]
紧空间到 Hausdorff 空间的连续满射是商映射。若 \(A\) 被所有 profinite 探针检测为闭，则对任意紧 Hausdorff 探针 \(f:K\to X\)，有 profinite 探针 \(p=f\circ\pi\)，且
\[
p^{-1}(A)=\pi^{-1}(f^{-1}(A))
\]
闭，故 \(f^{-1}(A)\) 闭。反向显然。因此两种探针给出同一 \(k\) 拓扑。

小问题：答卷中 \(\tau_k\subset \tau_{\rm prof}\) 与 \(\tau_{\rm prof}\subset\tau_k\) 的标签，若把 \(\tau\) 理解为开集拓扑，则与闭集论证方向相反；闭集论证本身正确，最终等式也正确。

### 2. \(\operatorname{Nat}(h_X,h_Y)\cong C(kX,kY)\)

**正确。**

用单点 \(*\) 和点包含 \(i_s:*\to S\)，可得任意自然变换 \(\alpha\) 由其底集映射
\[
g(x)=\alpha_*(c_x)(*)
\]
完全决定，并且
\[
\alpha_S(f)=g\circ f.
\]
再由 profinite 探针生成 \(kX\)，以及紧 Hausdorff \(S\) 满足
\[
C(S,Y)=C(S,kY),
\]
可得 \(g:kX\to kY\) 连续；反之连续 \(g:kX\to kY\) 通过后复合给出自然变换。

### 3. 充要条件

最终结论
\[
\Big(\forall Y,\ \text{所有 }h_X\to h_Y\text{ 都由原拓扑连续 }X\to Y\text{ 诱导}\Big)
\iff kX=X
\]
**是正确的**，但答卷证明有实质错误。

答卷断言：

> 连续映射 \(f:X\to Y\) 诱导的自然变换对应于集合 \(C(X,kY)\subset C(kX,kY)\)。

这是错误的。正确地说，由原拓扑连续映射 \(f:X\to Y\) 诱导的自然变换对应于集合 \(C(X,Y)\)，并且
\[
C(X,Y)\subset C(kX,kY).
\]
包含关系的证明：若 \(f:X\to Y\) 连续，则对任意紧 Hausdorff 探针 \(p:K\to X\)，\(f\circ p:K\to Y\) 连续；因 \(U\) 为 \(kY\)-开当且仅当所有紧探针拉回开，故 \(f^{-1}(U)\) 为 \(kX\)-开。因此 \(f:kX\to kY\) 连续。

**反例说明 \(C(X,kY)\) 不是诱导变换集合：**取 S5 中的非紧生成 Hausdorff 空间 \(Z\)，令
\[
X=Y=Z,\qquad f=\mathrm{id}_Z.
\]
则 \(f\) 连续，\(h_f\) 是恒等自然变换，按 S2 对应到
\[
\mathrm{id}_{kZ}\in C(kZ,kZ).
\]
但 \(kZ\) 离散而 \(Z\) 不离散，故
\[
\mathrm{id}_Z:Z\to kZ
\]
不连续，即
\[
\mathrm{id}_Z\notin C(Z,kZ)=C(X,kY).
\]
所以答卷的集合识别确实错误。

**如何修补必要性：**若所有自然变换都由原拓扑连续映射诱导，取 \(Y=kX\)，考虑对应 \(\mathrm{id}_{kX}\) 的自然变换。它必须由某个连续 \(f:X\to kX\) 诱导；按 S2 对应关系，\(f\) 的 \(k\)-化就是 \(\mathrm{id}_{kX}\)，故 \(f=\mathrm{id}\)。于是
\[
\mathrm{id}:X\to kX
\]
连续，故 \(kX=X\)。

因此：**S2 的最终结论正确，但答卷的必要性证明不成立，需要按上述方式修补。**

---

## S3　全部参数化映射记录

### 1. \(M(X,Y)\) 的构造

答卷取
\[
M(X,Y)=C(kX,kY)
\]
为底集，拓扑取
\[
k\bigl(C_{co}(kX,kY)\bigr).
\]
这是正确的；它正是 \(\mathbf{CGHaus}\) 中的内蕴 hom 空间。Hausdorff 性论证也正确：\(C_{co}(kX,kY)\) Hausdorff，而 \(k\)-化细化拓扑后仍 Hausdorff。

### 2. 同构 \(C(S,M)\cong H_{X,Y}(S)\)

主要链条正确：
\[
H_{X,Y}(S)
\cong \operatorname{Nat}(h_{S\times X},h_Y)
\cong C(k(S\times X),kY).
\]
又因 \(S\) 紧、\(kX\) 紧生成，
\[
k(S\times X)=k(S\times kX)=S\times kX,
\]
最后一步用了“局部紧 Hausdorff 空间与紧生成空间的积仍紧生成”的 Cohen 定理。然后
\[
C(S\times kX,kY)\cong C(S,M).
\]

**但答卷第 4 步的援引错误。**答卷写：

> 由 S1 的指数律（由于 \(S\) 是局部紧 Hausdorff，置于紧开拓扑第一变量）：
> \[
> C(S\times kX,kY)\cong C(S,C_{co}(kX,kY)).
> \]

这是不对的。S1 要求被指数化的空间 \(kX\) 局部紧，而题中 \(kX\) 只保证紧生成，未必局部紧。正确理由是 \(\mathbf{CGHaus}\) 的笛卡尔闭性：
\[
C(S\times_k kX,kY)
\cong C(S,kC_{co}(kX,kY)).
\]
由于 \(S\) 紧 Hausdorff 且 \(kX\) 紧生成，\(S\times_k kX=S\times kX\)，并且
\[
C(S,kC_{co}(kX,kY))=C(S,C_{co}(kX,kY)),
\]
因为紧 Hausdorff 定义域到 \(C_{co}\) 的连续映射自动进入其 \(k\)-化。故该双射成立，但**不是由 S1 在所述条件下推出的**。

另外，答卷在第 2 步只明确写了
\[
k(S\times X)=k(S\times kX)
\]
的一个方向。完整论证还需反向：任意紧探针 \(K\to S\times kX\) 的第二坐标 \(K\to kX\) 复合 \(\mathrm{id}:kX\to X\) 连续，故给出紧探针 \(K\to S\times X\)。两个方向的探针族相同，才有最终拓扑相等。

### 3. \(ev\) 与伴随同构

答卷构造
\[
ev_T(\phi,\psi)(t)=\phi(t)(\psi(t))
\]
是合理的。连续性可由 \(\mathbf{CGHaus}\) 中的内蕴求值
\[
M(X,Y)\times_k kX\to kY
\]
以及 \(T\) 紧得到。

随后证明
\[
\operatorname{Nat}(h_Z,h_M)
\cong C(kZ,M)
\cong C(kZ\times_k kX,kY)
\cong \operatorname{Nat}(h_Z\times h_X,h_Y)
\]
也正确；最后一步用 S2 及 \(k(Z\times X)=kZ\times_k kX\)。映射确由
\[
\alpha\longmapsto ev\circ(\alpha\times I)
\]
实现，即指数伴随的转置。

关于 \(X,Y\) 中连续映射的自然性，答卷给出的两条求值相容式方向正确：
\[
ev_{X'}\circ(M(u,Y)\times I)
=ev_X\circ(I\times h_u),
\]
\[
h_v\circ ev_Y
=ev_{Y'}\circ(M(X,v)\times I).
\]
严格说还应说明 \(M(u,Y),M(X,v)\) 在 \(k C_{co}\) 拓扑下连续；这由紧开拓扑下前/后复合连续，再取 \(k\)-化得到。

**S3 结论：构造和最终表示结论正确；第 4 步援引 S1 是实质性证明错误，但可用 \(\mathbf{CGHaus}\) 笛卡尔闭性修补。**

---

## S4　可数邻域基的输入

### 1. 通常求值是否必连续？

**结论正确：不必连续。**

反例 \(X=\mathbb Q\)、\(Y=\mathbb R\) 有效。要点：

- \(\mathbb Q\) 中紧集 \(K\) 在 \(\mathbb R\) 中紧且 \(K\subset\mathbb Q\)，故不含任何非退化区间，因而在 \(\mathbb Q\) 中无内点。
- 给定 \(0\) 在 \(\mathbb Q\) 中的邻域 \(V\)，可取 \(q\in V\setminus K\)。因 \(K\) 在 \(\mathbb R\) 中紧闭，\(\delta=\operatorname{dist}(q,K)>0\)。
- 取三角形函数
  \[
  f(x)=2\max\left(0,1-\frac{|x-q|}{\delta}\right).
  \]
  则 \(f|_K\equiv 0\)，故 \(f\in[K,(-\varepsilon,\varepsilon)]\)，但 \(f(q)=2\notin(-1,1)\)。
- 任意 \(0\) 在 \(C_{co}(\mathbb Q,\mathbb R)\) 中的基本邻域都包含某个形如 \([K,(-\varepsilon,\varepsilon)]\) 的子邻域，故上述论证给出求值在 \((0,0)\) 处不连续。

小边缘：若 \(K=\varnothing\)，则 \(\delta\) 无定义；此时 \([K,(-\varepsilon,\varepsilon)]\) 是整个函数空间，直接取常数函数即可得到同样矛盾。

### 2. 第一可数性是否保证 \(kX=X\)？

**结论正确：是。**

第一可数 Hausdorff 空间是序列空间；序列空间是紧生成空间。答卷的序列证明正确：

设 \(A\) 为 \(k\)-闭。若 \(x_0\in\overline A\setminus A\)，取递减可数邻域基 \(V_n\ni x_0\)，选
\[
x_n\in A\cap V_n.
\]
则 \(x_n\to x_0\)，且
\[
K=\{x_n:n\ge1\}\cup\{x_0\}
\]
紧 Hausdorff。由 \(A\) 为 \(k\)-闭，\(A\cap K\) 在 \(K\) 中闭；但序列 \((x_n)\subset A\cap K\) 在 \(K\) 中收敛于 \(x_0\)，故 \(x_0\in A\cap K\subset A\)，矛盾。因此 \(A\) 原闭。

---

## S5　空间实现的识别

**结论正确：\(f\) 不必为原拓扑同胚。**

一般机制成立：取非紧生成 Hausdorff \(Z\)，令
\[
X=kZ,\qquad Y=Z,\qquad f=\mathrm{id}_Z:kZ\to Z.
\]
因 \(kZ\) 拓扑细于 \(Z\)，\(f\) 连续。对任意 profinite \(S\)，任意连续 \(\phi:S\to Z\) 自动连续为 \(\phi:S\to kZ\)，因为 \(S\) 本身是紧 Hausdorff 探针；故
\[
C(S,kZ)=C(S,Z),
\]
从而 \(h_f\) 的每个分量都是恒等双射，\(h_f\) 是自然同构。但 \(f^{-1}:Z\to kZ\) 不连续，因为 \(kZ\) 严格细于 \(Z\)。

具体超滤子空间 \(Z=\mathbb N\cup\{p\}\) 的构造也有效：

- \(Z\) Hausdorff；
- 任意紧子集 \(K\subset Z\) 必有限；
- 因而任意 \(A\subset Z\) 与任意紧 \(K\) 的交有限，在 \(K\) 中闭，故 \(A\) 是 \(k\)-闭；于是 \(kZ\) 离散；
- \(\{p\}\) 在 \(Z\) 中不开，故 \(Z\) 不离散。

小问题：论证中写“恰有一个集合不属于 \(\mathcal U\)”不准确。对两个不交无限集 \(A_1,A_2\)，超滤子至多含其中一个；应改为“至少有一个不属于 \(\mathcal U\)”。这不影响结论。

---

## S6　复合与可识别范围

### 1. 复合、结合律、单位律

复合构造正确。由 \(\mathbf{CGHaus}\) 的笛卡尔闭性，
\[
M(Y,Z)\times_k M(X,Y)\times_k kX
\to M(Y,Z)\times_k kY
\to kZ
\]
连续，转置得到
\[
\circ:M(Y,Z)\times_k M(X,Y)\to M(X,Z),
\]
底集上就是通常的函数复合。

**结合律证明有小缺口。**答卷写
\[
\circ\circ(\circ\times_k\mathrm{id})
=
\circ\circ(\mathrm{id}\times_k\circ),
\]
但两边严格来说定义在不同的乘积结合方式上。正确写法应插入典范结合同构
\[
\alpha:
(M(Z,W)\times_k M(Y,Z))\times_k M(X,Y)
\xrightarrow{\ \cong\ }
M(Z,W)\times_k(M(Y,Z)\times_k M(X,Y)),
\]
然后证明
\[
\circ\circ(\circ\times_k\mathrm{id})
=
\circ\circ(\mathrm{id}\times_k\circ)\circ\alpha.
\]
在底集上两边都是
\[
((h,g),f)\longmapsto h\circ g\circ f,
\]
而 \(\mathbf{CGHaus}\) 的遗忘函子忠实，故连续映射相等。补上 \(\alpha\) 后结合律成立。

单位律图表方向正确：\(j_X:*\to M(X,X)\) 取 \(\mathrm{id}_{kX}\)，并利用
\[
*\times_k M(X,Y)\cong M(X,Y),\qquad
M(X,Y)\times_k *\cong M(X,Y).
\]
左、右单位均成立。

### 2. \(h_f\) 为自然同构的充要条件

**结论正确：**
\[
h_f\text{ 是自然同构}
\iff
k(f):kX\to kY\text{ 是拓扑同胚}.
\]

理由：S2 给出自然变换与 \(k\)-空间连续映射的双射，并且该双射与复合相容：
\[
\operatorname{Nat}(h_X,h_Y)\cong C(kX,kY).
\]
因此 \(h_f\) 对应 \(k(f)\)，自然同构对应 \(k(f)\) 为同构，即拓扑同胚。

答卷的充分性、必要性论证基本正确；只需注意这里用到了 S2 对应的**函子性**，而不只是逐对象双射。

### 3. 第一可数时能否升级为普通同胚？

**结论正确：能。**

由 S4，第一可数 Hausdorff 空间 \(X,Y\) 满足
\[
kX=X,\qquad kY=Y.
\]
又由上面的充要条件，\(k(f):kX\to kY\) 是同胚。于是
\[
f:X\to Y
\]
本身就是原拓扑意义下的同胚。

---

## 最终判断

- **S1：正确。**
- **S2：前两部分正确；第三部分最终结论正确，但证明中有实质错误：把诱导变换集合误认为 \(C(X,kY)\)，必要性论证需重写。**
- **S3：构造和最终表示结论正确；第 4 步错误援引 S1，须改用 \(\mathbf{CGHaus}\) 笛卡尔闭性；第 2 步还应补全 \(k(S\times X)=k(S\times kX)\) 的反向包含。**
- **S4：正确。**
- **S5：正确；仅有“恰有一个”应为“至少有一个”的措辞问题。**
- **S6：主要结论正确；结合律证明需补典范结合子，单位律和充要条件、第一可数升级均正确。**

因此，**答卷的核心数学结论大多成立，但作为严格证明答卷并不完全正确、完整**；若按证明题标准审阅，S2 和 S3 需要实质性修补，S6 需要补足结合律细节。