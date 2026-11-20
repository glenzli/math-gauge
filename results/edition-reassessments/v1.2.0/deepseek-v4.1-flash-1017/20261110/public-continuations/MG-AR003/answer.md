## 总体判断

原答卷的**最终数学结论基本都正确**，但没有达到“完整证明、无关键缺口”的严格标准。主要问题集中在：

- S2 把原拓扑连续映射诱导的自然变换误写成 \(C(X,kY)\)；
- S3 在 \(kX\) 未必局部紧时错误援引 S1，且乘积 \(k\)-化等式少写了一个方向；
- S6 的结合律证明没有处理乘积结合子；
- S4、S5 有少量需要补充或修正的技术细节。

因此，不能判为完全正确、完整；但也不能因这些局部缺口否定其余独立成立的结论。

| 阶段 | 最终结论 | 原答卷证明完整性 |
|---|---|---|
| S1 | 正确 | 完整 |
| S2 | 三个结论均正确 | 第三部分有实质集合识别错误，但可局部修补 |
| S3 | \(M(X,Y)\)、求值及伴随结论正确 | 指数律援引错误，乘积等式论证不完整 |
| S4 | 两个判断均正确 | 基本正确，需说明零函数处的基本邻域合并与空集边界 |
| S5 | 正确 | 正确；“恰有一个”应改为“至少有一个” |
| S6 | 复合、结合、单位及识别条件正确 | 结合律缺少典范结合子，不能直接称两边相等 |

---

## S1：局部紧输入

原答卷正确。

给定 \(f_0(x_0)\in W\)，由 \(X\) 局部紧 Hausdorff，可以取 \(x_0\) 的紧邻域 \(K\) 满足
\[
x_0\in \operatorname{int}K\subset K\subset f_0^{-1}(W).
\]
于是
\[
[K,W]\times \operatorname{int}K
\]
是 \((f_0,x_0)\) 的邻域，并映入 \(W\)，所以通常求值映射连续。

逆向柯里化的连续性确实使用管道引理：对紧集 \(K\subset X\)，
\[
\Psi(F)^{-1}([K,W])
=\{z\in Z:F(\{z\}\times K)\subset W\}.
\]
由于 \(F^{-1}(W)\) 在 \(Z\times X\) 中开且 \(K\) 紧，每一个满足条件的 \(z_0\) 都有邻域 \(V\) 使得
\[
V\times K\subset F^{-1}(W).
\]
因此该原像开。

关于 \(Z,Y,X\) 的三个自然性公式也都直接正确。故 S1 可以保留。

---

## S2：探针检测与自然变换

### 1. Profinite 探针与全部紧 Hausdorff 探针

原答卷的证明正确，包含方向标签也正确。前一版审阅曾怀疑这里的包含方向写反，经重新核验，该怀疑应予撤销。

设 \(O\subset X\)。

- 如果 \(O\) 是 \(k_X\)-开集，则它对所有紧 Hausdorff 探针的拉回都开，特别对 profinite 探针的拉回都开，因此 \(O\) 是 profinite-开集。故
  \[
  \tau_k\subset \tau_{\mathrm{prof}}.
  \]
- 反过来，给定任意紧 Hausdorff \(K\)，在底层集合上取离散拓扑 \(D\)。由
  \[
  D\to K
  \]
  得连续延拓 \(\pi:\beta D\twoheadrightarrow K\)。紧空间到 Hausdorff 空间的连续满射是商映射。对探针 \(f:K\to X\)，\(f\circ\pi:\beta D\to X\) 是 profinite 探针。因此 \(f^{-1}(O)\) 闭当 \((f\circ\pi)^{-1}(O)\) 闭。于是
  \[
  \tau_{\mathrm{prof}}\subset\tau_k.
  \]

所以两种探针确实给出相同拓扑。

### 2. \(\operatorname{Nat}(h_X,h_Y)\cong C(kX,kY)\)

原证明正确。对单点 \(*\in\mathrm{Prof}_U\) 取
\[
g(x)=\alpha_*(c_x)(*).
\]
再取点包含 \(i_s:*\to S\)，自然性给出
\[
\alpha_S(f)(s)=g(f(s)).
\]
因此 \(\alpha\) 由底层映射 \(g\) 唯一决定，并且必须在每一个 profinite 探针上产生连续复合。

由于 profinite 探针已经生成 \(kX\)，\(g:kX\to kY\) 连续当且仅当对每个 profinite \(f:S\to X\)，都有连续映射
\[
g\circ f:S\to kY.
\]
而紧 Hausdorff 空间满足集合等式
\[
C(S,kY)=C(S,Y),
\]
故等价于 \(g\circ f:S\to Y\) 连续。反向自然变换就是后复合。最终得到
\[
\operatorname{Nat}(h_X,h_Y)\cong C(kX,kY).
\]

### 3. 由原拓扑连续映射诱导的充要条件

最终充要条件正确，但原答卷中的集合识别错误。

原答卷说：

> 由原拓扑连续映射 \(X\to Y\) 诱导的自然变换对应于 \(C(X,kY)\)。

这是错误的。正确的诱导集合是
\[
C(X,Y)
\]
的底层函数族，并且
\[
C(X,Y)\subset C(kX,kY).
\]
反之，\(C(X,kY)\) 通常更大，其中的映射未必连续进入 \(Y\)。

例如取 S5 中的非紧生成空间 \(Z\)，令 \(X=Y=Z\)。恒等映射 \(f=\mathrm{id}_Z\) 连续，并且 \(h_f\) 是恒等自然变换，对应于
\[
\mathrm{id}_{kZ}\in C(kZ,kZ).
\]
但
\[
\mathrm{id}_Z:Z\to kZ
\]
不连续，所以
\[
\mathrm{id}_Z\notin C(Z,kZ).
\]
这直接说明原答卷的 \(C(X,kY)\) 识别不对。

正确的必要性证明如下。假设所有自然变换都由原拓扑连续映射诱导。取
\[
Y=kX
\]
及对应的自然变换 \(\mathrm{id}_{kX}:h_X\to h_Y\)。它必须由某个连续映射
\[
g:X\to kX
\]
诱导。单点分量表明 \(g=\mathrm{id}_X\)。因此
\[
\mathrm{id}_X:X\to kX
\]
连续，故原拓扑比 \(kX\) 细；但恒有原拓扑比 \(kX\) 粗，所以两者相等，\(kX=X\)。

反过来，若 \(kX=X\)，取任意 \(g:kX\to kY\)。对任意原拓扑开集 \(O\subset Y\)，由于 \(O\in\tau_{kY}\)，
\[
g^{-1}(O)\in\tau_{kX}=\tau_X.
\]
故 \(g:X\to Y\) 连续。因此每个自然变换都由原拓扑连续映射诱导。

所以 S2 的最终充要条件正确，但原答卷第三部分必须按上述方式修补。

---

## S3：全部参数化映射记录

原答卷选取
\[
M(X,Y)=k\,C_{co}(kX,kY)
\]
作为同胚型模型，底集为 \(C(kX,kY)\)，这是正确的。因为 \(kY\) Hausdorff，\(C_{co}(kX,kY)\) Hausdorff，\(k\)-化后仍 Hausdorff。

证明
\[
C(S,M(X,Y))\cong H_{X,Y}(S)
\]
的总体链条也正确：
\[
H_{X,Y}(S)
\cong \operatorname{Nat}(h_{S\times X},h_Y)
\cong C(k(S\times X),kY).
\]

乘积 \(k\)-化等式应完整写成
\[
k(S\times X)=k(S\times kX).
\]
两个探针族相同：

- 紧 Hausdorff \(K\to S\times X\) 的两个分量给出 \(K\to S\) 和 \(K\to X\)；
- 因为 \(K\) 紧 Hausdorff，\(K\to X\) 连续当且仅当 \(K\to kX\) 连续；
- 因而紧凑探针族完全相同。

原答卷只明确写了其中一个方向。虽然结论正确，但应补上反向，才能严格推出拓扑相等。

然后，由于 \(S\) 紧 Hausdorff，\(kX\) 紧生成 Hausdorff，标准乘积定理给出
\[
S\times kX
\]
紧生成；也就是
\[
k(S\times kX)=S\times kX.
\]

原答卷下一步错误地援引了 S1。S1 要求被指数的空间 \(kX\) 局部紧，而题面只保证它紧生成。正确的理由是紧生成 Hausdorff 空间范畴 \(\mathbf{CGHaus}\) 的笛卡尔闭性：
\[
C(S\times_k kX,kY)
\cong C\bigl(S,kC_{co}(kX,kY)\bigr)
=C(S,M(X,Y)).
\]
这里 \(S\times_k kX=S\times kX\)。又因为 \(S\) 是紧 Hausdorff，所以
\[
C(S,M(X,Y))=C(S,C_{co}(kX,kY)).
\]
因此原答卷 S3 第 4 步的结论可以保留，但援引 S1 的理由错误。

求值自然变换
\[
ev_T(\phi,\psi)(t)=\phi(t)(\psi(t))
\]
的连续性和自然性均正确。由 \(\mathbf{CGHaus}\) 的内部 hom 与指数伴随也可得到
\[
\operatorname{Nat}(h_Z,h_M)
\cong \operatorname{Nat}(h_Z\times h_X,h_Y),
\]
且对应映射正是
\[
\alpha\longmapsto ev\circ(\alpha\times I).
\]

关于 \(X,Y\) 中连续映射的自然性，原答卷给出的两个求值恒等式正确。为完整起见，还应说明：

- 前复合 \(M(X,Y)\to M(X',Y)\) 连续，因为紧开拓扑下的逆像可写成
  \([K,W]\mapsto[u(K),W]\)；
- 后复合 \(M(X,Y)\to M(X,Y')\) 连续，因为
  \([K,W]\mapsto[K,v^{-1}(W)]\)。

这些只是需要补充的核验，不改变结论。

---

## S4：第一可数输入

原答卷的两个结论均正确。

取
\[
X=\mathbb Q,\qquad Y=\mathbb R.
\]
\(\mathbb Q\) 第一可数且 Hausdorff。在 \((0,0)\) 处，若通常求值连续，则对
\[
W=(-1,1)
\]
存在零函数在 \(C_{co}(\mathbb Q,\mathbb R)\) 中的邻域 \(U\) 和 \(0\in\mathbb Q\) 的邻域 \(V\)，使得
\[
ev(U\times V)\subset W.
\]
紧开拓扑的一般基本邻域是有限交。对零函数，可以使用
\[
[K_i,(-\varepsilon_i,\varepsilon_i)]
\]
的有限交；取
\[
K=\bigcup_iK_i,\qquad \varepsilon=\min_i\varepsilon_i
\]
后可归结为形如
\[
[K,(-\varepsilon,\varepsilon)]
\]
的邻域。

\(\mathbb Q\) 中的紧集在 \(\mathbb R\) 中紧且没有内部区间。因此 \(V\setminus K\ne\varnothing\)。取 \(q\in V\setminus K\)，则 \(d(q,K)>0\)。定义非空 \(K\) 时的三角形函数
\[
f(x)=2\max\left(0,1-\frac{|x-q|}{d(q,K)}\right).
\]
它在 \(K\) 上为 \(0\)，但 \(f(q)=2\)。于是
\[
f\in[K,(-\varepsilon,\varepsilon)],\qquad f(q)\notin W,
\]
矛盾。若 \(K=\varnothing\)，可直接取常数函数 \(f\equiv2\)。

所以第一可数性不保证通常求值映射连续。

第二部分关于 \(kX=X\) 的序列空间证明正确。若 \(A\) 不原闭而仅为 \(k\)-闭，取
\[
x_0\in\overline A\setminus A.
\]
第一可数性给出递减邻域基 \(V_n\)，选择
\[
x_n\in A\cap V_n.
\]
则
\[
K=\{x_0\}\cup\{x_n:n\ge1\}
\]
紧 Hausdorff，且 \(x_n\to x_0\)。由于 \(A\) 是 \(k\)-闭，\(A\cap K\) 在 \(K\) 中闭；但序列给出了 \(x_0\in A\cap K\)，矛盾。因此 \(A\) 原闭，\(kX=X\)。

S4 的结论正确，以上只是补全原答卷压缩掉的技术点。

---

## S5：空间实现的识别

原答卷结论正确。

取非紧生成 Hausdorff 空间 \(Z\)，令
\[
X=kZ,\qquad Y=Z,\qquad f=\mathrm{id}_Z:kZ\to Z.
\]
因为 \(kZ\) 的拓扑比 \(Z\) 细，所以 \(f\) 连续。

对任意 profinite \(S\)，紧 Hausdorff 探针定义给出
\[
C(S,kZ)=C(S,Z).
\]
故对每个 \(S\)，
\[
h_f(S):C(S,kZ)\to C(S,Z)
\]
是恒等双射，并自然构成自然同构。但
\[
f^{-1}:Z\to kZ
\]
不连续，所以 \(f\) 不是原拓扑下的同胚。

具体超滤子构造 \(Z=\mathbb N\cup\{p\}\) 也有效：

- \(Z\) Hausdorff；
- 每个紧子集有限；
- 因而任一子集在每个紧子集上的交有限闭集，所以 \(kZ\) 离散；
- \(\{p\}\) 不是原开集。

原证明中唯一需要修正的是：把
\[
K\cap\mathbb N=A_1\sqcup A_2
\]
分成两个不交无限集后，应说“至少一个不属于超滤子”，而不是“恰有一个不属于”。因为这里只分割了 \(K\cap\mathbb N\)，两个集合可能都不属于超滤子。至少确实有一个不属于，因为两者不能同时属于超滤子，这已经足以完成反证。

修补后，S5 成立。

---

## S6：复合与可识别范围

由 S3 的内部 hom 结构，可以利用两个求值映射先构造
\[
(M(Y,Z)\times_k M(X,Y))\times_k kX
\to M(Y,Z)\times_k kY
\to kZ,
\]
再经 \(\mathbf{CGHaus}\) 的指数伴随转置，得到连续复合
\[
\mu:M(Y,Z)\times_k M(X,Y)\to M(X,Z),
\qquad \mu(g,f)=g\circ f.
\]
这一步正确。

结合律证明有缺口。左边和右边定义在不同的乘积组合上，不能直接写成相等。设
\[
a:(A\times_k B)\times_k C
\xrightarrow{\ \cong\ }
A\times_k(B\times_k C)
\]
为典范结合子，其中
\[
A=M(Z,W),\quad B=M(Y,Z),\quad C=M(X,Y).
\]
结合律应写成
\[
\mu\circ(\mu\times_k\mathrm{id})
=
\mu\circ(\mathrm{id}\times_k\mu)\circ a.
\]
插入 \(a\) 后，两边底层函数都是
\[
((h,g),f)\longmapsto h\circ g\circ f.
\]
紧生成 Hausdorff 空间的遗忘函子忠实，所以底层函数相等即连续映射相等。

单位律同样应在典范单位同构下理解：
\[
*\times_k M(X,Y)\cong M(X,Y),
\qquad
M(X,Y)\times_k *\cong M(X,Y).
\]
取 \(j_X:*\to M(X,X)\) 为 \(\mathrm{id}_{kX}\)，左、右单位律均成立。原答卷的结论正确，只需补上交换图表中的单位同构。

关于空间识别，充要条件
\[
h_f\text{ 是自然同构}
\iff
k(f):kX\to kY\text{ 是拓扑同胚}
\]
正确。使用 S2 的对应时，还应说明该对应与后复合相容：在底层映射上，\(h_f\) 对应 \(f\) 本身，因此对应的就是
\[
k(f):kX\to kY.
\]
自然同构对应同构，即拓扑同胚。

最后，若 \(X,Y\) 均第一可数 Hausdorff，则由 S4 得
\[
kX=X,\qquad kY=Y.
\]
于是 \(k(f)\) 是原拓扑 \(f:X\to Y\) 的同胚。因此第一可数时确实可以升级为普通同胚。

---

## 对前次审阅的修正

保留的内容包括：

- S1 完整正确；
- S2 的最终充要条件、S3 的 \(M(X,Y)\) 构造与伴随结论、S4、S5、S6 的最终判断；
- S2 中 \(C(X,kY)\) 的实质错误；
- S3 错误援引 S1 的问题；
- S6 缺少典范结合子的问题。

本轮新增或修正的内容包括：

- **撤销前一版关于 S2.1 包含方向标反的判断。** 使用闭集族核验后，原答卷的
  \[
  \tau_k\subset\tau_{\mathrm{prof}},
  \qquad
  \tau_{\mathrm{prof}}\subset\tau_k
  \]
  标签与论证一致。
- 补全 S2.3 中正确的 \(C(X,Y)\subset C(kX,kY)\) 识别和充要条件证明。
- 显式补全 \(k(S\times X)=k(S\times kX)\) 的双向探针论证。
- 将 S3 中错误的 S1 援引替换为 \(\mathbf{CGHaus}\) 的笛卡尔闭性和标准乘积定理。
- 修正 S5 的“恰有一个”为“至少一个”。
- 补入 S6 的典范结合子与单位同构。

原答卷仍有未完成部分：S2 第三部分、S3 指数律步骤和 S6 结合律不能按原文视为严格证明。除此之外，没有发现最终数学结论层面的不确定性；所需修补均可在原题框架内完成。

自评：本轮已经覆盖六个阶段的全部实质判断，区分了“最终结论正确”与“原证明严格完整”，并核验了所依赖的乘积紧生成性、\(k\)-化、自然性和超滤子构造。本任务是答卷审阅，不主张新的研究等级增量。