结论成立。关键在于证明一个三阶“广义 Vandermonde 行列式”非零。

设 \(\zeta\) 是 primitive \(N\) 次单位根。反设 \(P\) 在三个不同的 \(N\) 次单位根 \(z_1,z_2,z_3\) 处为零，则
\[
\begin{pmatrix}
z_1^{a_1}&z_1^{a_2}&z_1^{a_3}\\
z_2^{a_1}&z_2^{a_2}&z_2^{a_3}\\
z_3^{a_1}&z_3^{a_2}&z_3^{a_3}
\end{pmatrix}
\begin{pmatrix}c_1\\c_2\\c_3\end{pmatrix}=0.
\]
由于 \((c_1,c_2,c_3)\neq0\)，该矩阵的行列式为零。

令
\[
m=a_2-a_1,\qquad n=a_3-a_1,
\]
则 \(0<m<n<N\)。从第 \(i\) 行提出非零因子 \(z_i^{a_1}\)，得到
\[
D(z_1,z_2,z_3):=
\det\begin{pmatrix}
1&z_1^m&z_1^n\\
1&z_2^m&z_2^n\\
1&z_3^m&z_3^n
\end{pmatrix}=0.
\]

### 1. 广义 Vandermonde 行列式的一个性质

对不定元 \(x_1,x_2,x_3\)，记
\[
D=\det\begin{pmatrix}
1&x_1^m&x_1^n\\
1&x_2^m&x_2^n\\
1&x_3^m&x_3^n
\end{pmatrix},
\qquad
V=\prod_{1\le i<j\le3}(x_j-x_i).
\]
\(D\) 是关于 \(x_1,x_2,x_3\) 的交错多项式，故被 \(V\) 整除，即存在
\[
S\in\mathbb Z[x_1,x_2,x_3]
\]
使得
\[
D=VS.
\]
下面计算 \(S(1,1,1)\)。令 \(y_i=x_i-1\)，展开
\[
x_i^a=(1+y_i)^a=\sum_{k\ge0}\binom ak y_i^k,
\]
并利用行列式的多重线性。展开后的每一项含有
\(\det(y_i^{k_j})\)：若三个 \(k_j\) 有重复，该项为零；否则它仍被 \(V\) 整除。除以 \(V\) 后，在 \(y_1=y_2=y_3=0\) 处，只有指数集合为 \(\{0,1,2\}\) 的项有非零贡献。因此
\[
\begin{aligned}
S(1,1,1)
&=\binom m1\binom n2-\binom m2\binom n1\\
&=\frac{mn(n-1)-m(m-1)n}{2}
=\frac{mn(n-m)}2.
\end{aligned}
\]
（最后这个数确实是整数。）

因为 \(z_1,z_2,z_3\) 两两不同，\(V(z_1,z_2,z_3)\neq0\)，而 \(D(z_1,z_2,z_3)=0\)，所以
\[
S(z_1,z_2,z_3)=0. \tag{1}
\]

### 2. 模 \(p\) 约化得到矛盾

由于 \(N=p^r\)，有
\[
\Phi_N(X)
=1+X^{N/p}+X^{2N/p}+\cdots+X^{(p-1)N/p},
\qquad
\Phi_N(1)=p.
\]
而 \(\mathbb Z[\zeta]\cong\mathbb Z[X]/(\Phi_N(X))\)，因此存在环同态
\[
\rho:\mathbb Z[\zeta]\longrightarrow\mathbb F_p,\qquad \zeta\longmapsto1.
\]
每个 \(z_i\) 都是 \(\zeta\) 的幂，所以 \(\rho(z_i)=1\)。对式 (1) 应用 \(\rho\)，注意 \(S\) 具有整数系数，便得到
\[
0=S(1,1,1)\pmod p
=\frac{mn(n-m)}2\pmod p. \tag{2}
\]
但由 \(a_1,a_2,a_3\) 模 \(p\) 两两不同，
\[
m\equiv a_2-a_1,\qquad
n\equiv a_3-a_1,\qquad
n-m\equiv a_3-a_2\pmod p
\]
均不被 \(p\) 整除；又因 \(p\ge3\)，\(p\nmid2\)。故
\[
p\nmid\frac{mn(n-m)}2,
\]
与 (2) 矛盾。

因此 \(P\) 不可能在三个不同的 \(N\) 次单位根处同时为零，即这样的不同根**至多有两个**。 \(\square\)

实际上，上述证明只用到 \(N\) 是奇素数幂，因而对 \(r\ge1\) 也成立。