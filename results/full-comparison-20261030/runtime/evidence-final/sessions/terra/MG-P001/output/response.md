**可能的同伦类型恰好是**
\[
\Sigma |L|,
\]
其中 \(L\) 是几何实现非空的有限单纯复形，\(\Sigma\) 表示非约化悬挂。对于给定的三元组，可以取 \(L=\operatorname{lk}_K(v)\)。例如，\(L\) 为两个点时得到 \(S^1\)，所以这些空间不一定单连通。

先说明假设对顶点 \(v\) 的作用。由于 \(v\in B\)，如果 \(v\) 不属于 \(B\) 的任何边，那么 \(\{v\}\) 是 \(C\) 的一个孤立连通分支，而 \(C\setminus\{v\}=O\cap C\) 不与这个分支相交。这与包含映射 \(O\cap C\to C\) 是同伦等价矛盾。因此，\(v\) 至少属于 \(B\) 的一条边；特别地，\(L=\operatorname{lk}_K(v)\) 的几何实现非空。

令
\[
D=\{\sigma\in K:v\notin\sigma\},\qquad L=\operatorname{lk}_K(v).
\]
空间 \(O\) 强变形收缩到 \(|D|\)。事实上，对 \(x\in O\)，记其重心坐标为 \(\lambda_w(x)\)，则 \(\lambda_v(x)<1\)，并且
\[
H_t(x)=
\frac{(1-t)\lambda_v(x)v+\sum_{w\ne v}\lambda_w(x)w}
     {1-t\lambda_v(x)}
\qquad(0\le t\le1)
\]
给出所需的强变形收缩。因此 \(|D|\) 非空且可缩。

又有
\[
K=D\cup(v*L),\qquad D\cap(v*L)=L.
\]
因为 \(|D|\) 是可缩子复形，商映射 \(X\to X/|D|\) 是同伦等价。这里可用同伦延拓性质直接验证：把 \(|D|\) 在自身内收缩到一点，并将此收缩延拓为 \(X\) 上的同伦；其终点映射通过商空间分解，得到商映射的同伦逆。于是
\[
X\simeq X/|D|
\cong |v*L|/|L|
\cong \Sigma |L|.
\]
这证明了所列类型包含所有可能的 \(X\)。

反过来，任取几何实现非空的有限单纯复形 \(L\)。取两个新顶点 \(u,v\)，令
\[
K=(u*L)\cup(v*L).
\]
这是两个锥沿公共底面粘合，故 \(|K|\cong\Sigma|L|\)。取 \(L\) 的任一顶点 \(a\)，令 \(B\) 为边 \(\{v,a\}\) 及其面组成的子复形。删除 \(v\) 后，\(O\) 强变形收缩到锥 \(|u*L|\)，因此可缩且非空。另一方面，\(C\) 是一条闭线段，\(C\setminus\{v\}\) 是删去一个端点的线段；两者都能收缩到端点 \(a\)，所以包含映射
\[
O\cap C=C\setminus\{v\}\longrightarrow C
\]
是同伦等价。这就实现了上述全部类型。

对于可缩性的判据，先用链表示为
\[
\boxed{\quad X\text{ 可缩}
\iff
\widetilde H_i(\operatorname{lk}_K(v);\mathbb Z)=0
\text{ 对所有 }i\ge0.\quad}
\]
必要性来自 \(X\simeq\Sigma|L|\) 及悬挂同调公式
\[
\widetilde H_n(\Sigma|L|;\mathbb Z)
\cong \widetilde H_{n-1}(|L|;\mathbb Z)\qquad(n\ge1).
\]
反过来，若这些约化同调群全为零，则非空的 \(|L|\) 连通，因而 \(\Sigma|L|\) 单连通；悬挂同调公式又表明其约化整系数同调全为零。由 Hurewicz 定理和 Whitehead 定理，这个单连通 CW 复形可缩。

最后把判据写成只涉及包含 \(v\) 的单形及其面关系的有限计算。对 \(q\ge0\)，令 \(A_q\) 为以 \(K\) 中包含 \(v\) 的有向 \(q\)-单形为基的自由阿贝尔群。选定顶点次序并把 \(v\) 排在首位，定义
\[
\partial_v[v,w_1,\ldots,w_q]
=
\sum_{i=1}^{q}(-1)^i
[v,w_1,\ldots,\widehat{w_i},\ldots,w_q],
\qquad
\partial_v[v]=0.
\]
这些边界只保留仍含 \(v\) 的面。若 \(d\) 是包含 \(v\) 的单形的最大维数，则所求充要条件是有限链复形
\[
0\longrightarrow A_d\xrightarrow{\partial_v}\cdots
\xrightarrow{\partial_v}A_1\xrightarrow{\partial_v}A_0
\longrightarrow0
\]
**在每个位置都正合**。

确实，\(A_q\) 对应于链 \(L\) 的增广单形链群 \(\widetilde C_{q-1}(L;\mathbb Z)\)，上述边界与增广边界只差一个统一的负号。由于 \(|L|\ne\varnothing\)，该链复形正合恰好等价于上述链的约化整系数同调全部为零。所有矩阵都有限，可用 Smith 标准形检验正合性；必须使用整系数，以免漏掉挠同调。