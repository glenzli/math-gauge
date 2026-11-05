## S1　层的半局部拼接

取包含给定有限点集的仿射邻域 \(\operatorname{Spec}A\)，记对应素理想为
\(\mathfrak p_1,\ldots,\mathfrak p_n\)。去掉其中包含于另一个素理想的冗余项后，它们对应 \(S\) 的闭点。于是
\[
S=\operatorname{Spec}(M^{-1}A),\qquad
M=A\setminus\bigcup_i\mathfrak p_i,\qquad
S_i=\operatorname{Spec}A_{\mathfrak p_i}.
\]

对层 \(G\)，按题目的邻域余极限约定，
\[
G(S_i)=\varinjlim_{a\notin\mathfrak p_i}G(D(a)).
\]
而
\[
S_i\times_S S_j
 \simeq
\operatorname{Spec}\bigl(A[(A\setminus\mathfrak p_i)^{-1},
                              (A\setminus\mathfrak p_j)^{-1}]\bigr),
\]
因此
\[
G(S_i\times_S S_j)
 =\varinjlim_{\substack{a\notin\mathfrak p_i\\ b\notin\mathfrak p_j}}
       G(D(a)\cap D(b)).
\]

先证唯一性。若 \(g\in G(S)\) 在每个 \(G(S_i)\) 中为零，可将 \(g\) 表示在某个包含所有 \(x_i\) 的开邻域上。对每个 \(i\)，缩小到 \(x_i\) 的开邻域 \(U_i\)，使 \(g|_{U_i}=0\)。则 \(U=\bigcup_iU_i\) 仍包含所有 \(x_i\)，且由层的分离性，\(g|_U=0\)。故 \(G(S)\to\prod_iG(S_i)\) 单射。

再设 \(g_i\in G(S_i)\) 在所有
\(G(S_i\times_S S_j)\) 中相容。将 \(g_i\) 表示为 \(x_i\) 的某个开邻域 \(U_i\) 上的截面。对每对 \((i,j)\)，上述余极限公式表明，可以分别缩小 \(U_i,U_j\)，使两个截面在交上相等。由于点和点对都只有有限个，可以同时完成这些缩小。层公理遂将它们拼成
\[
g\in G\Bigl(\bigcup_iU_i\Bigr),
\]
后者给出 \(G(S)\) 的元素，其在各 \(S_i\) 上的限制正是 \(g_i\)。这证明
\[
G(S)\;\cong\;
\operatorname{Eq}\!\left(
\prod_iG(S_i)\rightrightarrows
\prod_{i,j}G(S_i\times_S S_j)\right).
\]

**局部化不必是开子概形。** 例如取 \(X=\mathbb A_k^2\)，两点为
\((0,0)\) 和 \((1,0)\)，令 \(S\) 为其半局部化。第一点处的局部化在 \(S\) 中的像由包含于 \((x,y)\) 的素理想构成。任意包含 \((x,y)\) 的基本开集都包含某个素理想
\[
(x-1+y^m)\subset (x-1,y),\qquad m\geq1,
\]
但该素理想不包含于 \((x,y)\)。这里使用这些多项式是无限多个互异的不可约因子，而一个给定非零多项式只能被其中有限个整除。因此该局部化的像不是开集。

## S2　分离预层的比较图

单射已由题设给出，只需证满射。

取 \(g\in G(S)\)。由
\[
H(S_i)\xrightarrow{\sim}G(S_i)
\]
及邻域余极限的定义，对 \(i=1,2\)，可取 \(x_i\) 的开邻域 \(W_i\) 和截面 \(h_i\in H(W_i)\)，使 \(\eta(h_i)\) 与 \(g|_{W_i}\) 在 \(S_i\) 上相等。进一步缩小 \(W_i\)，可使它们在 \(W_i\) 上就相等。

再令
\[
U_0=W_1\setminus\{x_2\},\qquad
V=W_2\setminus\{x_1\}.
\]
这两个开集分别只包含指定的那个闭点。它们覆盖 \(S\)：否则其闭补集非空，便包含 \(S\) 的一个闭点，这与两个闭点均已被覆盖矛盾。

按题设，可将 \((U_0,V)\) 缩为 \((U,V)\)，仍覆盖 \(S\)，并且
\[
0\longrightarrow H(S)\longrightarrow H(U)\oplus H(V)
 \longrightarrow H(U\cap V)
\]
正合。在 \(U\cap V\) 上，\(h_1|_U\) 与 \(h_2|_V\) 的 \(\eta\)-像都等于 \(g\) 的限制；由题设在该处的单射性，它们相等。故正合性给出 \(h\in H(S)\)，其限制分别为这两个截面。层 \(G\) 的分离性给出 \(\eta(h)=g\)。因此 \(H(S)\to G(S)\) 是同构。

## S3　含指定点的开集

对任意包含 \(\Sigma\) 的开集 \(V\)，
\[
\Sigma\subset V\cap W\subset V,\qquad V\cap W\subset W.
\]
故包含 \(\Sigma\) 且包含于 \(W\) 的开邻域，在按缩小方向排列的全部 \(\Sigma\)-邻域中余终。

具体地，对反变阿贝尔群预层 \(P\)，典范映射
\[
\varinjlim_{\Sigma\subset U\subset W}P(U)
 \longrightarrow
\varinjlim_{\Sigma\subset V\subset X}P(V)
\]
的逆映射把由 \(s\in P(V)\) 表示的类送到
\[
[s|_{V\cap W}].
\]
共同缩小邻域即可验证它良定义且与原映射互逆。这给出所求典范同构。

## S4　稠密开与邻域系统

**不总是余终。** 例如
\[
X=\mathbb A_k^1,\qquad \Sigma=\{0\},\qquad
W=\mathbb A_k^1\setminus\{0\}.
\]
\(W\) 是稠密开集，但不存在满足 \(\Sigma\subset U\subset W\) 的开集。

事实上，所列开集余终的充要条件正是 \(\Sigma\subset W\)：必要性显然；充分性由 S3 给出。

## S5　整体对象与恢复目标

**结论成立。** 证明中需要以下两个关于带有限对应的同伦不变预层的标准定理；它们是本题中实质性的输入，不能由普通层公理或 S1–S4 代替。

1. **Zariski 层化定理。** 对任意域 \(k\)，若 \(P\) 是 \(\mathrm{Cor}_k\) 上的加性反变函子且 \(\mathbb A^1\)-同伦不变，则其底层预层的 Zariski 层化典范地带有相容的有限对应作用，层化映射与对应相容，而且层化仍是 \(\mathbb A^1\)-同伦不变的。

2. **半局部注入定理。** 对任意域 \(k\)，若 \(P\) 是这样的同伦不变带转移预层，\(T\) 是光滑 \(k\)-概形在有限非空点集处的半局部化，则限制到各不可约分支的泛点给出单射
   \[
   P(T)\longrightarrow\prod_{\xi\in T^{(0)}}P(k(\xi)).
   \]
   这里在局部化和函数域上的值均按开邻域滤过余极限定义。此处使用的是对**预层**的半局部版本，而不仅是对已经层化的对象的版本。

这两个定理在上述表述中适用于任意域；本证明不额外假定 \(k\) 无限或完美。

先核对半局部对象。由有限素理想的素理想回避，\(A\) 中与 \(M\) 不交的素理想恰好是包含于某个 \(\mathfrak p_x\) 的素理想。因此 \(S\) 的闭点对应于 \(\{\mathfrak p_x\}\) 中极大的那些素理想。又由素理想回避，包含 \(\Sigma\) 的主开集 \(D(f)\)、\(f\in M\)，在全部 \(\Sigma\)-邻域中余终；故题目给定的 \(H(S)\) 正是上述两个定理使用的半局部值。光滑性还保证 \(S\) 正则；其有限多个不可约分支互不相交，因而半局部注入定理适用。

记
\[
G=F_{\mathrm{Zar}}.
\]
由第一个定理，\(\eta:F\to G\) 是带转移预层的态射，且 \(G\) 同伦不变。在带转移预层范畴中逐对象取
\[
K=\ker(\eta),\qquad Q=\operatorname{coker}(\eta).
\]
投影在 \(F\) 和 \(G\) 上都诱导同构，所以在核及余核上也诱导同构；因此 \(K,Q\) 都是同伦不变带转移预层。

对 \(S\) 的任一泛点 \(\xi\)，典范映射
\[
F(k(\xi))\longrightarrow G(k(\xi))
\]
是同构：两边分别是底层预层及其层化在原光滑概形的点 \(\xi\) 处的茎，而预层到其层化在每个点的茎上都是同构。滤过余极限在阿贝尔群中正合，故
\[
K(k(\xi))=0,\qquad Q(k(\xi))=0.
\]
将半局部注入定理分别用于 \(K\) 和 \(Q\)，得到
\[
K(S)=0,\qquad Q(S)=0.
\]
再次使用滤过余极限的正合性，这两个群分别是
\[
\ker\bigl(F(S)\to G(S)\bigr),\qquad
\operatorname{coker}\bigl(F(S)\to G(S)\bigr).
\]
故
\[
\boxed{\eta_S:F(S)\xrightarrow{\ \sim\ }F_{\mathrm{Zar}}(S)}.
\]

此论证没有把“余极限中的正合性”提升为某个固定邻域阶段上的正合性；后一提升一般不成立，见 S6。

## S6　极限正合与阶段正合

**余极限复形正合不蕴含所有充分后阶段正合。** 令每个阶段的二项复形都是
\[
C_n:\quad \mathbb Z\longrightarrow 0,
\]
其中 \(\mathbb Z\) 位于次数 \(1\)，转移映射在 \(\mathbb Z\) 上全部取零。每个 \(C_n\) 都有非零的 \(H_1\)，但其余极限是零复形，因此正合。

现在设每个阶段的每个同调类都在某个后阶段变为零。取余极限复形中的一个闭元素，由某阶段元素 \(z_i\) 表示。因为它的微分在余极限中为零，滤过余极限中元素为零的判据表明：在某个后阶段 \(j\)，\(z_i\) 的像 \(z_j\) 已是闭元素。按假设，\([z_j]\) 在再后面的某阶段变为零，即该阶段的 \(z_j\) 已是边界。因此原余极限中的闭元素也是边界。

所以余极限复形正合。等价地，这也是滤过阿贝尔群余极限正合性给出的同构
\[
H_r\!\left(\varinjlim_i C_i\right)
 \cong \varinjlim_i H_r(C_i)
\]
的直接应用。