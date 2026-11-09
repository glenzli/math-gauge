## 结论

按题面给出的位移、梯度和能量定义，实际结论是

\[
\boxed{e_0=0,}
\]

且**不存在** \(u\in\mathcal A\) 使 \(E(u)=0\)。对任意极小化序列 \(E(u_j)\to0\)，都有

\[
\boxed{
(\pi_1(u_j),\pi_2(u_j),\pi_3(u_j),\pi_4(u_j))
\longrightarrow
\left(\frac1{10},\frac3{10},\frac3{10},\frac3{10}\right).
}
\]

因此，题面中“没有两两秩一连接，所以四相系统仍有严格正间隙”的推断与所给定义不符：两两不相容并不排除借助井外中间矩阵的高阶循环层合。

---

## 1. 循环层合给出 \(e_0=0\)

记

\[
W(M)=\min_{1\le i\le4}\|M-A_i\|_F^2,
\]

并引入三个井外矩阵

\[
B_*=\operatorname{diag}(1,0),\qquad
C=\operatorname{diag}(0,1),\qquad
D=\operatorname{diag}(1,1).
\]

它们满足以下秩一分解：

\[
\begin{aligned}
0&=\frac14A_4+\frac34C,\\
C&=\frac13A_3+\frac23D,\\
D&=\frac12A_2+\frac12B_*,\\
B_*&=\frac13A_1+\frac23\cdot0.
\end{aligned}
\tag{1}
\]

事实上，相邻矩阵的差分别为

\[
\begin{gathered}
A_4-0=\operatorname{diag}(0,-3),\qquad
A_3-C=\operatorname{diag}(-2,0),\\
A_2-D=\operatorname{diag}(0,1),\qquad
A_1-B_*=\operatorname{diag}(2,0),
\end{gathered}
\]

它们全是秩一矩阵。因而可以按这些关系逐次作细层合。

前三次分解给出

\[
\mu_1=\frac14\delta_{A_4}+\frac14\delta_{A_3}
+\frac14\delta_{A_2}+\frac14\delta_{B_*}.
\]

其重心为零。每当残余原子 \(B_*\) 出现时，利用第四个分解 \(B_*=\frac13A_1+\frac23\cdot0\)，再对零矩阵重复前三次分解，就把单位质量的 \(B_*\) 替换为

\[
\frac13A_1+\frac16A_4+\frac16A_3+\frac16A_2
+\frac16B_*.
\tag{2}
\]

所以，每进行一轮，残余 \(B_*\) 的质量缩小为原来的 \(1/6\)，其余原子全部位于四井上。

经过 \(n\) 轮所得层合测度 \(\mu_n\) 的残余质量为

\[
\delta_n=\mu_n(\{B_*\})=\frac14\,6^{-(n-1)}.
\]

其各原子质量具体为，令 \(r_n=6^{-(n-1)}\)，

\[
\begin{aligned}
\mu_n(\{A_1\})&=\frac1{10}(1-r_n),\\
\mu_n(\{A_i\})&=\frac14+\frac1{20}(1-r_n)
=\frac3{10}-\frac{r_n}{20},
\qquad i=2,3,4,\\
\mu_n(\{B_*\})&=\frac{r_n}{4}.
\end{aligned}
\tag{3}
\]

又因为

\[
W(B_*)=\min\{4,4,10,10\}=4,
\]

所以

\[
\int W(M)\,d\mu_n(M)=4\delta_n=r_n=6^{-(n-1)}.
\tag{4}
\]

所有参与分解的矩阵 \(0,A_i,B_*,C,D\) 的 Frobenius 范数都不超过 \(3\)。下文给出的实际位移层合保留零边界，并可用剩余的范数余量把过渡层梯度控制在 \(4\) 内。因此对任意 \(\eta>0\)，可构造 \(u_{n,\eta}\in\mathcal A\)，使

\[
E(u_{n,\eta})\le 6^{-(n-1)}+\eta.
\tag{5}
\]

例如取 \(\eta=6^{-(n-1)}\)，便得到 \(u_n\in\mathcal A\)，满足

\[
E(u_n)\le2\cdot6^{-(n-1)}\longrightarrow0.
\]

由于显然 \(E\ge0\)，故 \(e_0=0\)。

---

## 2. 最小值不能达到

若 \(E(u)=0\)，则必须有

\[
\nabla u(x)\in\{A_1,A_2,A_3,A_4\}\qquad\text{a.e. }x\in\Omega.
\]

特别地，\(\nabla u\) 几乎处处为对角矩阵，即

\[
\partial_2u_1=0,\qquad \partial_1u_2=0
\qquad\text{a.e.在 }\Omega.
\]

于是存在一元函数 \(F,G\)，使得

\[
u_1(x_1,x_2)=F(x_1),\qquad
u_2(x_1,x_2)=G(x_2).
\]

利用零边界条件：在底边 \(x_2=0\) 上 \(u_1=0\)，故 \(F\equiv0\)；在左边 \(x_1=0\) 上 \(u_2=0\)，故 \(G\equiv0\)。因此只能有 \(u\equiv0\)。

但是

\[
E(0)=\min\{\|A_i\|_F^2:1\le i\le4\}
=\min\{9,5,5,9\}=5,
\]

矛盾。所以没有任何 \(u\in\mathcal A\) 达到 \(e_0=0\)。

---

## 3. 极小化序列的相体积分数

设 \(E(u_j)\to0\)，记 \(G_j=\nabla u_j\)，并令 \(\Omega_i^j\) 为被分配给井 \(A_i\) 的区域。于是 \(\pi_i(u_j)=|\Omega_i^j|\)，且

\[
\sum_{i=1}^4\int_{\Omega_i^j}\|G_j-A_i\|_F^2\,dx
=E(u_j)\to0.
\tag{6}
\]

零边界给出

\[
\int_\Omega G_j\,dx=0.
\tag{7}
\]

由 (6) 和有界性 \(\|G_j\|_F\le4\)，在 \(\Omega_i^j\) 上将 \(G_j\) 换成 \(A_i\) 只产生 \(o(1)\) 的积分误差。因此，对 \((\pi_1(u_j),\ldots,\pi_4(u_j))\) 的任意子列极限 \((\pi_1,\ldots,\pi_4)\)，由 (7) 得

\[
\sum_{i=1}^4\pi_iA_i=0,
\qquad \sum_i\pi_i=1,\qquad \pi_i\ge0.
\tag{8}
\]

还需要行列式矩条件。对零边界位移，\(\det\nabla u\) 是零 Lagrange 量；光滑情形可写成

\[
\det\nabla u
=\partial_1(u_1\partial_2u_2)
-\partial_2(u_1\partial_1u_2),
\]

积分后因 \(u_1=0\) 于边界而为零。通过逼近，对 \(u\in W^{1,\infty}\) 同样成立，所以

\[
\int_\Omega\det G_j\,dx=0.
\tag{9}
\]

另一方面，四井的行列式分别为

\[
\det A_1=0,\qquad \det A_2=2,\qquad
\det A_3=-2,\qquad \det A_4=0.
\]

利用 (6)、\(\|G_j\|_F\le4\) 以及

\[
|\det(A_i+R)-\det A_i|
\le C\|R\|_F+C\|R\|_F^2,
\]

可从 (9) 得到极限条件

\[
2\pi_2-2\pi_3=0.
\tag{10}
\]

联立 (8)、(10)，即

\[
\begin{aligned}
3\pi_1+\pi_2-2\pi_3&=0,\\
2\pi_2+\pi_3-3\pi_4&=0,\\
\pi_2&=\pi_3,\\
\pi_1+\pi_2+\pi_3+\pi_4&=1.
\end{aligned}
\]

令 \(\pi_2=\pi_3=t\)，则 \(t=3\pi_1\)，且 \(\pi_4=t\)。归一化给出

\[
10\pi_1=1.
\]

故唯一可能的子列极限为

\[
(\pi_1,\pi_2,\pi_3,\pi_4)
=\left(\frac1{10},\frac3{10},\frac3{10},\frac3{10}\right).
\]

由于四个相分数均有界，任意子列都有收敛子列，而所有子列极限又相同，所以整个序列必然收敛到该向量，不存在其他极限。

---

## 4. 具体近最优位移及三项验证

下面说明上述层合确实对应零边界位移，而不只是矩阵凸组合。

### 4.1 单个秩一分解的锯齿位移

设某个小长方体 \(R\) 上当前位移为 \(Bx+c\)，并有

\[
B=\lambda C+(1-\lambda)D,\qquad C-D=a\otimes\nu,
\qquad0<\lambda<1.
\]

定义一周期锯齿函数

\[
\phi_\lambda(t)=
\begin{cases}
(1-\lambda)t,&0\le t\le\lambda,\\[2mm]
\lambda(1-t),&\lambda\le t\le1,
\end{cases}
\]

并作周期延拓。其导数在长度为 \(\lambda\) 的区间上等于 \(1-\lambda\)，在长度为 \(1-\lambda\) 的区间上等于 \(-\lambda\)。

取 \(0\le\rho_R\le1\) 的分片线性截断函数，在 \(\partial R\) 上为零，在去掉很薄的边界层后等于 \(1\)。在 \(R\) 上定义

\[
v_{h,R}(x)
=Bx+c+\rho_R(x)\,h\phi_\lambda\!\left(\frac{x\cdot\nu}{h}\right)a.
\tag{11}
\]

在 \(\rho_R=1\) 处，其梯度只取 \(C,D\) 两个值；在 \(R\) 的边界上，\(v_{h,R}=Bx+c\)。因此可以逐格替换而保持位移连续，并保持原问题的零边界。

把 (1) 中的分解按顺序用公式 (11) 实现；每当出现残余矩阵 \(B_*\)，就按 (2) 再进行一轮。这样得到的 \(u_{n,\eta}\) 是明确的分片仿射位移构造。

### 4.2 零边界

每次替换在小长方体边界上都等于原仿射位移。最初从 \(u\equiv0\) 开始，所以整个构造过程中始终有

\[
u_{n,\eta}=0\qquad\text{在 }\partial\Omega.
\]

### 4.3 统一梯度上界

由 (11)，

\[
\nabla v_{h,R}
=B+\rho_R(\nabla w_h-B)
+h\phi_\lambda\,a\otimes\nabla\rho_R,
\]

其中 \(w_h=Bx+c+h\phi_\lambda(x\cdot\nu/h)a\)。

前两项是 \(B\) 与 \(C\) 或 \(D\) 的凸组合，其范数不超过 \(3\)。又因 \(|\phi_\lambda|\le1/4\)，只要对每个固定的 \(\rho_R\) 把 \(h\) 取得足够小，就有

\[
\|h\phi_\lambda\,a\otimes\nabla\rho_R\|_F\le1.
\]

故整个构造满足

\[
\|\nabla u_{n,\eta}\|_F\le4
\qquad\text{a.e.在 }\Omega.
\]

所以 \(u_{n,\eta}\in\mathcal A\)。

### 4.4 能量估计

截断层以外的梯度正好是相应层合原子。截断层内梯度范数不超过 \(4\)，而四井范数不超过 \(3\)，故那里恒有

\[
W(\nabla u_{n,\eta})\le(4+3)^2=49.
\]

把各轮截断层的总面积取得足够小，就能让其能量贡献小于 \(\eta\)。结合 (4)，得到

\[
E(u_{n,\eta})\le6^{-(n-1)}+\eta.
\]

取 \(\eta=6^{-(n-1)}\)，即得到一列满足全部约束的实际位移 \(u_n\)，且

\[
E(u_n)\le2\cdot6^{-(n-1)}\to0.
\]

由 (3)，其主体层合相分数也趋向

\[
\left(\frac1{10},\frac3{10},\frac3{10},\frac3{10}\right),
\]

与上述一般极小化序列的结论一致。