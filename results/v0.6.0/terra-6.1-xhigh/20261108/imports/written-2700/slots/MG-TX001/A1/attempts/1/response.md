这个结论成立。关键是证明：任取三个不同的 \(N\) 次单位根 \(z_1,z_2,z_3\)，矩阵
\[
\bigl(z_j^{a_i}\bigr)_{1\le i,j\le3}
\]
的行列式都不为零。

令
\[
D(X_1,X_2,X_3)=\det\bigl(X_j^{a_i}\bigr)_{1\le i,j\le3}.
\]
这是一个交替多项式，因此可以在 \(\mathbb Z[X_1,X_2,X_3]\) 中写成
\[
D(X_1,X_2,X_3)
=\prod_{1\le i<j\le3}(X_j-X_i)\,Q(X_1,X_2,X_3),
\]
其中 \(Q\) 的系数都是整数。

先计算 \(Q(1,1,1)\)。将 \(X_j=1+tY_j\) 代入行列式，并按 \(t\) 展开。最低次非零项来自次数 \(0,1,2\)，所以
\[
D(1+tY_1,1+tY_2,1+tY_3)
=t^3
\det\begin{pmatrix}
1&a_1&\binom{a_1}{2}\\
1&a_2&\binom{a_2}{2}\\
1&a_3&\binom{a_3}{2}
\end{pmatrix}
\prod_{i<j}(Y_j-Y_i)+O(t^4).
\]
与上面的分解比较，得到
\[
Q(1,1,1)
=\det\begin{pmatrix}
1&a_1&\binom{a_1}{2}\\
1&a_2&\binom{a_2}{2}\\
1&a_3&\binom{a_3}{2}
\end{pmatrix}
=\frac{(a_2-a_1)(a_3-a_1)(a_3-a_2)}{2}.
\]
由于 \(p\) 是奇素数，且三个指数模 \(p\) 两两不同，这个整数不被 \(p\) 整除。

现在取一个本原 \(N\) 次单位根 \(\zeta\)。有环同态
\[
\mathbb Z[\zeta]\longrightarrow\mathbb F_p,\qquad \zeta\longmapsto 1.
\]
这是良定义的：\(\zeta\) 的最小多项式是
\[
\Phi_{p^r}(X)=1+X^{p^{r-1}}+\cdots+X^{(p-1)p^{r-1}},
\]
而 \(\Phi_{p^r}(1)=p\)。

于是，每个 \(N\) 次单位根在此同态下都映为 \(1\)。因此
\[
Q(z_1,z_2,z_3)\longmapsto Q(1,1,1)\ne0
\quad\text{于 }\mathbb F_p,
\]
从而 \(Q(z_1,z_2,z_3)\ne0\)。又因为 \(z_1,z_2,z_3\) 两两不同，
\[
D(z_1,z_2,z_3)
=\prod_{i<j}(z_j-z_i)\,Q(z_1,z_2,z_3)\ne0.
\]

最后，若 \(P\) 在三个不同的 \(N\) 次单位根 \(z_1,z_2,z_3\) 上均为零，那么
\[
(c_1,c_2,c_3)\bigl(z_j^{a_i}\bigr)_{i,j}=0.
\]
上面证明的行列式非零迫使 \(c_1=c_2=c_3=0\)，与假设矛盾。因此，\(P\) 在全部 \(N\) 次单位根中至多有两个不同的零点。