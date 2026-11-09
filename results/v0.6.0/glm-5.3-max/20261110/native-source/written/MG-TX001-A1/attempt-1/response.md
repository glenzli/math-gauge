结论成立。下面给出一个完整证明。

记 \(\mu_N=\{z\in\mathbb C:z^N=1\}\)。

## 一个引理

**引理.** 若 \(\eta_1,\dots,\eta_m\in\mu_N\)，且
\[
\eta_1+\cdots+\eta_m=0,
\]
则 \(p\mid m\)。这里 \(m\) 按项数计算，重复项也重复计数。

**证明.** 取本原 \(N\) 次单位根 \(\zeta\)，令 \(R=\mathbb Z[\zeta]\)。由于 \(N=p^r\)，
\[
\Phi_N(X)=\frac{X^{p^r}-1}{X^{p^{r-1}}-1}
=1+X^{p^{r-1}}+\cdots+X^{(p-1)p^{r-1}},
\]
故 \(\Phi_N(1)=p\)。于是
\[
R/(\zeta-1)
\cong \mathbb Z[X]/(\Phi_N(X),X-1)
\cong \mathbb Z/(p)
\cong \mathbb F_p.
\]
在这个商环中，\(\zeta\) 的像为 \(1\)，因此每个 \(N\) 次单位根 \(\eta_\nu=\zeta^{e_\nu}\) 的像也都是 \(1\)。把等式 \(\eta_1+\cdots+\eta_m=0\) 投到该商环中，得到
\[
m\cdot 1=0\in \mathbb F_p,
\]
即 \(p\mid m\)。引理证毕。

## 主证明

反设 \(P\) 在 \(\mu_N\) 中有三个不同零点 \(z_1,z_2,z_3\)。考虑矩阵
\[
M=\begin{pmatrix}
z_1^{a_1}&z_1^{a_2}&z_1^{a_3}\\
z_2^{a_1}&z_2^{a_2}&z_2^{a_3}\\
z_3^{a_1}&z_3^{a_2}&z_3^{a_3}
\end{pmatrix}.
\]
由 \(P(z_j)=0\) 知 \(M(c_1,c_2,c_3)^T=0\)，而 \((c_1,c_2,c_3)\neq 0\)，故
\[
\det M=0.
\]

令
\[
b=a_2-a_1,\qquad d=a_3-a_1.
\]
因为 \(a_1,a_2,a_3\) 模 \(p\) 两两不同，所以
\[
p\nmid b,\qquad p\nmid d,\qquad p\nmid(d-b).
\]
又 \(N=p^r\)，故 \(b,d\) 模 \(N\) 都可逆。取唯一的 \(t\in\{1,\dots,N-1\}\) 使得
\[
tb\equiv d\pmod N.
\]
则 \(t\) 模 \(N\) 可逆，特别地 \(p\nmid t\)；并且若 \(t\equiv 1\pmod p\)，则
\[
d\equiv tb\equiv b\pmod p,
\]
与 \(p\nmid(d-b)\) 矛盾。因此
\[
p\nmid t,\qquad p\nmid(t-1).
\]
特别地 \(t\neq 1\)，所以 \(t\ge 2\)。

令
\[
u_j=z_j^b,\qquad j=1,2,3.
\]
由于 \(b\) 模 \(N\) 可逆，映射 \(z\mapsto z^b\) 是 \(\mu_N\) 的一个置换，因此 \(u_1,u_2,u_3\) 仍两两不同。并且
\[
u_j^t=z_j^{bt}=z_j^d.
\]
于是从 \(\det M=0\) 得
\[
0=\det M=(z_1z_2z_3)^{a_1}
\det
\begin{pmatrix}
1&u_1&u_1^t\\
1&u_2&u_2^t\\
1&u_3&u_3^t
\end{pmatrix}.
\]
因 \((z_1z_2z_3)^{a_1}\neq0\)，故
\[
\Delta:=
\det
\begin{pmatrix}
1&u_1&u_1^t\\
1&u_2&u_2^t\\
1&u_3&u_3^t
\end{pmatrix}
=0.
\]

令
\[
A=\frac{u_2}{u_1},\qquad B=\frac{u_3}{u_1}.
\]
则 \(A,B\in\mu_N\)，且
\[
A\neq 1,\qquad B\neq 1,\qquad A\neq B.
\]
从第二、第三列分别提取公因子 \(u_1,u_1^t\)，得
\[
\Delta=u_1^{t+1}
\det
\begin{pmatrix}
1&1&1\\
1&A&A^t\\
1&B&B^t
\end{pmatrix}.
\]

现在定义
\[
S_t(X,Y)=\sum_{\substack{i,j\ge 0\\ i+j\le t-2}}X^iY^j.
\]
直接计算给出
\[
\det
\begin{pmatrix}
1&1&1\\
1&X&X^t\\
1&Y&Y^t
\end{pmatrix}
=(X-1)(Y^t-1)-(Y-1)(X^t-1)
=(X-1)(Y-1)(Y-X)S_t(X,Y).
\]
因此由 \(\Delta=0\)，且 \(u_1\neq0\)，\(A-1,B-1,B-A\) 均非零，得到
\[
S_t(A,B)=0.
\]

但 \(S_t(A,B)\) 是若干个 \(N\) 次单位根之和：
\[
S_t(A,B)=\sum_{\substack{i,j\ge0\\ i+j\le t-2}} A^iB^j,
\]
其项数为
\[
L=1+2+\cdots+(t-1)=\frac{t(t-1)}2.
\]
由引理，必有
\[
p\mid L.
\]
然而 \(p\nmid t\)，\(p\nmid(t-1)\)，且 \(p\ge3\)，故
\[
p\nmid \frac{t(t-1)}2.
\]
矛盾。

因此不存在三个不同的 \(N\) 次单位根使 \(P(z)=0\)。也就是说，在全部 \(N\) 次单位根中，\(P\) 的不同零点至多有两个。证毕。