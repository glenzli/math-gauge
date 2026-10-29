所述结论一般不成立。下面在 ZFC 中构造反例：两个因子都满足题设的提升性质，但它们的乘积不满足。

令 \(P=\beta\mathbb N\)，具体地，将它定义为 \(\mathbb N\) 上全体超滤子的空间。对 \(A\subseteq\mathbb N\)，记
\[
\widehat A=\{p\in P:A\in p\},
\]
并以这些集合为拓扑基。每个 \(\widehat A\) 都是开闭集，不同超滤子可由这样的集合分开。该空间是紧的：若一族基本开集没有有限子覆盖，则相应集合的补集具有有限交性质，可由超滤子引理扩充为一个超滤子；这个超滤子不在该族开集中。因此 \(P\) 是 profinite 空间。

把 \(n\in\mathbb N\) 等同于由 \(n\) 生成的主超滤子。于是每个 \(\{n\}=\widehat{\{n\}}\) 都是开集，且 \(\mathbb N\) 在 \(P\) 中稠密。

**\(P\) 满足题设的提升性质。** 给定 profinite 空间之间的连续满射 \(q:Y\to Z\) 和连续映射 \(f:P\to Z\)，对每个 \(n\in\mathbb N\) 选择
\[
y_n\in Y,\qquad q(y_n)=f(n).
\]
由于 \(Y\) 紧 Hausdorff，对每个超滤子 \(p\in P\)，序列 \((y_n)\) 有唯一的 \(p\)-极限；记它为 \(g(p)\)。这里 \(p\)-极限的意思是，对 \(g(p)\) 的每个邻域 \(O\)，都有
\[
\{n:y_n\in O\}\in p.
\]

这些极限确实存在：对 \(A\in p\)，闭集
\[
\overline{\{y_n:n\in A\}}
\]
组成具有有限交性质的族，所以有公共点；该公共点就是所需极限，而 Hausdorff 性保证其唯一性。

映射 \(g:P\to Y\) 连续。事实上，若 \(g(p)\in O\)，由紧 Hausdorff 空间的正则性，可取开集 \(W\) 使
\[
g(p)\in W\subseteq\overline W\subseteq O.
\]
令 \(A=\{n:y_n\in W\}\)，则 \(A\in p\)。对任意 \(p'\in\widehat A\)，有
\[
g(p')\in\overline{\{y_n:n\in A\}}\subseteq O.
\]
故 \(\widehat A\subseteq g^{-1}(O)\)。

对主超滤子 \(n\)，有 \(g(n)=y_n\)，所以 \(qg\) 与 \(f\) 在稠密子集 \(\mathbb N\) 上相等。由 \(Z\) 的 Hausdorff 性，二者在整个 \(P\) 上相等。

现在取
\[
P_1=P_2=P,\qquad X=P\times P.
\]
在 \(X\) 中定义两个不相交的开集
\[
U=\{(n,m)\in\mathbb N^2:n<m\},\qquad
V=\{(n,m)\in\mathbb N^2:n>m\}.
\]
它们是开集，因为每个主超滤子 \(n\) 都是开点。

取一个非主超滤子 \(p\)；例如将余有限滤子扩充为超滤子即可。则
\[
(p,p)\in\overline U\cap\overline V.
\]
确实，\((p,p)\) 的任意基本邻域形如 \(\widehat A\times\widehat B\)，其中 \(A,B\in p\)。由于 \(A\cap B\in p\)，而非主超滤子不包含有限集，可取 \(a<b\) 都属于 \(A\cap B\)。于是该邻域同时包含 \((a,b)\in U\) 和 \((b,a)\in V\)。

最后令
\[
F=X\setminus U,\qquad G=X\setminus V,
\]
并赋予
\[
Y=(F\times\{0\})\cup(G\times\{1\})\subseteq X\times\{0,1\}
\]
子空间拓扑。\(Y\) 是 profinite 空间。投影
\[
q:Y\longrightarrow X,\qquad q(x,i)=x
\]
是连续满射，因为 \(F\cup G=X\)。取 \(f=\operatorname{id}_X\)。

假设存在连续提升 \(g:X\to Y\)，即 \(qg=\operatorname{id}_X\)。则
\[
A=g^{-1}(F\times\{0\}),\qquad
B=g^{-1}(G\times\{1\})
\]
是 \(X\) 的两个不相交开闭子集。对 \(x\in U\)，它在 \(Y\) 中的唯一原像是 \((x,1)\)，故 \(U\subseteq B\)；同理，\(V\subseteq A\)。由于 \(A,B\) 都是闭集，便有
\[
\overline U\subseteq B,\qquad \overline V\subseteq A,
\]
这与 \(\overline U\cap\overline V\ne\varnothing\) 矛盾。

因此，这个具体的连续满射 \(q\) 没有截面；所要求的乘积提升性质不成立。