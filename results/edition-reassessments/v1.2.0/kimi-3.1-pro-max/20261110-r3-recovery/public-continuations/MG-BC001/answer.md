## 结论

题面中“两两没有秩一连接，因此四相系统仍有严格正间隙”的推断并不成立。两两不相容并不排除经过井外中间矩阵的高阶循环层合。实际结论为

\[
\boxed{e_0=0,}
\]

且没有 \(u\in\mathcal A\) 达到该下确界。对任意极小化序列 \(E(u_j)\to0\)，都有

\[
\boxed{
(\pi_1(u_j),\pi_2(u_j),\pi_3(u_j),\pi_4(u_j))
\longrightarrow
\pi_*:=\left(\frac1{10},\frac3{10},\frac3{10},\frac3{10}\right).
}
\]

下面给出完整证明及显式位移构造。

---

## 1. 循环层合及其位移实现

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

### 1.1 相容的循环分解

有以下四组凸分解：

\[
\begin{aligned}
0&=\frac14A_4+\frac34C,\\
C&=\frac13A_3+\frac23D,\\
D&=\frac12A_2+\frac12B_*,\\
B_*&=\frac13A_1+\frac23\cdot0.
\end{aligned}
\tag{1}
\]

每一层的两个端点之差均为秩一矩阵：

\[
\begin{aligned}
A_4-C&=\operatorname{diag}(0,-4)=-4e_2\otimes e_2,\\
A_3-D&=\operatorname{diag}(-3,0)=-3e_1\otimes e_1,\\
A_2-B_*&=\operatorname{diag}(0,2)=2e_2\otimes e_2,\\
A_1-0&=\operatorname{diag}(3,0)=3e_1\otimes e_1.
\end{aligned}
\tag{2}
\]

前三次分解给出

\[
\mu_1=\frac14\delta_{A_4}+\frac14\delta_{A_3}
+\frac14\delta_{A_2}+\frac14\delta_{B_*},
\]

其重心为零。每出现残余原子 \(B_*\)，先用第四个分解将其换成 \(A_1\) 和 \(0\)，再对新产生的零原子重复前三次分解。因此，单位质量的 \(B_*\) 被替换为

\[
\frac13\delta_{A_1}
+\frac16\delta_{A_4}+\frac16\delta_{A_3}
+\frac16\delta_{A_2}+\frac16\delta_{B_*}.
\tag{3}
\]

每进行一轮，残余 \(B_*\) 的质量缩小为原来的 \(1/6\)。令第 \(n\) 轮的层合测度为 \(\mu_n\)，并设

\[
r_n=6^{-(n-1)},\qquad \delta_n=\mu_n(\{B_*\})=\frac{r_n}{4}.
\]

由上述递推可得

\[
\begin{aligned}
\mu_n(\{A_1\})&=\frac1{10}(1-r_n),\\
\mu_n(\{A_i\})&=\frac3{10}-\frac{r_n}{20},
\qquad i=2,3,4,\\
\mu_n(\{B_*\})&=\frac{r_n}{4}.
\end{aligned}
\tag{4}
\]

只有 \(B_*\) 具有正能量。事实上，

\[
W(B_*)=\min\{4,4,10,10\}=4,
\]

故

\[
\int W(M)\,d\mu_n(M)=4\delta_n=r_n=6^{-(n-1)}.
\tag{5}
\]

### 1.2 一步层合的显式锯齿位移

下面证明这些测度确实能由满足全部约束的位移实现。

设 \(R\) 是一个轴平行矩形，当前位移在 \(R\) 上为 \(Bx+c\)，并且

\[
B=\lambda P+(1-\lambda)Q,\qquad
P-Q=a\otimes\nu,\qquad 0<\lambda<1,
\]

其中 \(\nu=e_1\) 或 \(e_2\)。定义一周期锯齿函数

\[
\phi_\lambda(t)=
\begin{cases}
(1-\lambda)t,&0\le t\le\lambda,\\[1mm]
\lambda(1-t),&\lambda\le t\le1,
\end{cases}
\]

并作周期延拓。于是 \(\phi_\lambda'\) 在长度为 \(\lambda\) 的区间上等于 \(1-\lambda\)，在长度为 \(1-\lambda\) 的区间上等于 \(-\lambda\)，且 \(|\phi_\lambda|\le1/4\)。

对 \(\sigma>0\)，取显式截断函数

\[
\rho_\sigma(x)=\min\left\{1,\frac{\operatorname{dist}(x,\partial R)}{\sigma}
\right\}.
\]

在 \(R\) 上定义

\[
w_{\sigma,h}(x)=Bx+c+
\rho_\sigma(x)\,h\phi_\lambda\!\left(\frac{x\cdot\nu}{h}\right)a.
\tag{6}
\]

由于 \(\rho_\sigma=0\) 于 \(\partial R\)，有

\[
w_{\sigma,h}=Bx+c\qquad\text{在 }\partial R.
\]

其梯度为

\[
\nabla w_{\sigma,h}
=B+\rho_\sigma\phi_\lambda'\,a\otimes\nu
+h\phi_\lambda\,a\otimes\nabla\rho_\sigma .
\tag{7}
\]

在 \(\rho_\sigma=1\) 的区域，利用 \(P-Q=a\otimes\nu\)，得到

\[
\nabla w_{\sigma,h}=
\begin{cases}
B+(1-\lambda)(P-Q)=P,\\[1mm]
B-\lambda(P-Q)=Q.
\end{cases}
\]

在截断层中，前两项分别等于

\[
(1-\rho_\sigma)B+\rho_\sigma P
\quad\text{或}\quad
(1-\rho_\sigma)B+\rho_\sigma Q.
\]

本构造中出现的所有矩阵均属于

\[
\mathcal S=\{0,A_1,A_2,A_3,A_4,B_*,C,D\},
\qquad
\max_{M\in\mathcal S}\|M\|_F=3.
\]

所以 (7) 的前两项范数不超过 \(3\)。又因为
\(|\nabla\rho_\sigma|\le\sigma^{-1}\)，有

\[
\|h\phi_\lambda a\otimes\nabla\rho_\sigma\|_F
\le \frac{h\|a\|}{4\sigma}.
\]

固定 \(\sigma\) 后取 \(h\) 足够小，即可使该项不超过 \(1\)，从而

\[
\|\nabla w_{\sigma,h}\|_F\le4
\qquad\text{a.e.在 }R.
\tag{8}
\]

截断层面积不超过 \(\sigma\,\operatorname{Per}(R)\)。在截断层以外，每个完整锯齿周期严格以面积比例 \(\lambda,1-\lambda\) 取梯度 \(P,Q\)；端部不完整周期的面积误差为 \(O(h)\)。因此，依次令 \(\sigma,h\) 足够小，可以同时使：

- 截断层面积任意小；
- 实际相面积比例与 \(\lambda,1-\lambda\) 的误差任意小；
- 梯度上界 (8) 始终成立。

### 1.3 逐轮替换并估计能量

从 \(u\equiv0\) 开始，在 \(\Omega\) 上按 (1) 的第一式应用公式 (6)；随后在所有梯度为 \(C\) 的矩形带中应用第二式，在梯度为 \(D\) 的带中应用第三式。每当出现梯度为 \(B_*\) 的带，就按 (3) 进行下一轮。

由于所有层合方向均为 \(e_1\) 或 \(e_2\)，每一步需要继续细分的区域都是轴平行矩形，故上述构造可以逐格进行。每次替换在原矩形边界上等于原位移，因此全局位移连续并属于 \(W^{1,\infty}\)，且始终保持

\[
u=0\qquad\text{在 }\partial\Omega.
\]

梯度上界由 (8) 在每一步保持，故最终位移仍属于 \(\mathcal A\)。

经过 \(n\) 轮后，截断层以外的梯度只取 \(A_1,\dots,A_4,B_*\)。截断层内虽有其他梯度，但由 \(\|\nabla u\|_F\le4\) 和 \(\|A_i\|_F\le3\)，恒有

\[
W(\nabla u)\le(4+3)^2=49.
\]

构造只有有限多个细分阶段，所以可以把各阶段新增的截断层面积及相面积误差之和取得任意小。结合 (5)，对任意 \(\eta>0\)，可得到实际位移 \(u_{n,\eta}\in\mathcal A\)，满足

\[
E(u_{n,\eta})\le r_n+\eta=6^{-(n-1)}+\eta.
\tag{9}
\]

取 \(\eta=r_n\)，便得到 \(u_n\in\mathcal A\)，使

\[
E(u_n)\le2\cdot6^{-(n-1)}\longrightarrow0.
\]

另一方面 \(E\ge0\)，故

\[
\boxed{e_0=0.}
\]

---

## 2. 最小值不能达到

假设存在 \(u\in\mathcal A\) 使 \(E(u)=0\)。则

\[
\nabla u(x)\in\{A_1,A_2,A_3,A_4\}
\qquad\text{a.e. }x\in\Omega.
\]

四个井均为对角矩阵，因此

\[
\partial_2u_1=0,\qquad \partial_1u_2=0
\qquad\text{a.e.在 }\Omega.
\]

于是存在一元函数 \(F,G\)，使

\[
u_1(x_1,x_2)=F(x_1),\qquad
u_2(x_1,x_2)=G(x_2).
\]

在底边 \(x_2=0\) 上，零迹条件给出 \(u_1=0\)，故 \(F\equiv0\)；在左边 \(x_1=0\) 上，零迹条件给出 \(u_2=0\)，故 \(G\equiv0\)。因此只能有 \(u\equiv0\)。

但是

\[
E(0)=W(0)=\min\{9,5,5,9\}=5,
\]

矛盾。因此

\[
\boxed{\text{不存在 }u\in\mathcal A\text{ 使 }E(u)=e_0.}
\]

---

## 3. 任意极小化序列的相体积分数

### 3.1 两个零边界积分恒等式

对任意零边界位移 \(u\in W^{1,\infty}(\Omega;\mathbb R^2)\)，有

\[
\int_\Omega\nabla u\,dx=0.
\tag{10}
\]

此外，\(\det\nabla u\) 是零 Lagrange 量。光滑时有

\[
\det\nabla u
=\partial_1(u_1\partial_2u_2)
-\partial_2(u_1\partial_1u_2),
\]

积分后的边界项因 \(u_1=0\) 于 \(\partial\Omega\) 而消失；通过标准逼近，对 \(W^{1,\infty}\) 零迹位移同样成立。因此

\[
\int_\Omega\det\nabla u\,dx=0.
\tag{11}
\]

### 3.2 由低能量得到相分数方程

固定 \(u\in\mathcal A\)，记 \(G=\nabla u\)，\(\Omega_i\) 为被分配给 \(A_i\) 的区域，\(p_i=\pi_i(u)=|\Omega_i|\)。在这些区域上定义

\[
R=G-A_i\qquad\text{于 }\Omega_i.
\]

根据最近井分配规则，

\[
\sum_{i=1}^4\int_{\Omega_i}\|R\|_F^2\,dx=E(u).
\tag{12}
\]

由 (10) 及 Cauchy–Schwarz 不等式，

\[
\left\|\sum_{i=1}^4p_iA_i\right\|_F
=\left\|\int_\Omega(G-\widehat G)\,dx\right\|_F
\le E(u)^{1/2},
\tag{13}
\]

其中 \(\widehat G=\sum_iA_i\mathbf1_{\Omega_i}\)。

另一方面，在 \(\Omega_i\) 上写成 \(G=A_i+R\)，有

\[
\det(A_i+R)-\det A_i
=\operatorname{cof}(A_i):R+\det R.
\]

由于 \(\|\operatorname{cof}(A_i)\|_F\le3\)，且对 \(2\times2\) 矩阵有
\(|\det R|\le\frac12\|R\|_F^2\)，结合 (11)、(12) 得

\[
\left|\sum_{i=1}^4p_i\det A_i\right|
\le3E(u)^{1/2}+\frac12E(u).
\tag{14}
\]

现在设 \(E(u_j)\to0\)，并取其相分数向量的任意子列极限
\(p=(p_1,p_2,p_3,p_4)\)。由 (13)、(14)，该极限必须满足

\[
\sum_{i=1}^4p_iA_i=0,\qquad
\sum_{i=1}^4p_i\det A_i=0,\qquad
\sum_{i=1}^4p_i=1,\qquad p_i\ge0.
\]

代入四个井的具体数值，得到

\[
\begin{aligned}
3p_1+p_2-2p_3&=0,\\
2p_2+p_3-3p_4&=0,\\
2p_2-2p_3&=0,\\
p_1+p_2+p_3+p_4&=1.
\end{aligned}
\tag{15}
\]

由第三式 \(p_2=p_3=:t\)。第一式给出 \(t=3p_1\)，第二式给出 \(p_4=t\)。故

\[
p_1+3t=p_1+9p_1=1,
\]

从而

\[
p=\left(\frac1{10},\frac3{10},\frac3{10},\frac3{10}\right).
\]

相分数向量位于紧致单纯形中，任意子列都有收敛子列，而所有子列极限均等于上述同一个向量，所以整个序列必然收敛。因此全部可能的极限组成单点集

\[
\boxed{
\left\{\left(\frac1{10},\frac3{10},\frac3{10},\frac3{10}\right)\right\}.
}
\]

### 3.3 定量稳定性补充

上述估计还给出一个更强的定量结论。方程组 (15) 对应的四个线性泛函线性无关，因此由 (13)、(14) 及有限维线性可逆性，存在仅由四个井决定的常数 \(C\)，使对任意 \(u\in\mathcal A\)，

\[
\boxed{
|\pi(u)-\pi_*|
\le C\bigl(E(u)^{1/2}+E(u)\bigr).
}
\]

特别地，当 \(E(u)\le1\) 时，

\[
|\pi(u)-\pi_*|\le2C\,E(u)^{1/2}.
\]

---

## 修订说明与自评

- **保留**：\(e_0=0\)、最小值不可达、唯一相分数极限以及循环锯齿层合路线。
- **新增/修正**：明确写出每一层真正所需的两个端点之差为秩一矩阵；给出截断函数、锯齿位移公式及参数选择，并补足截断层面积、相面积误差和统一梯度上界的控制；增加了低能相分数的定量稳定性估计。
- **未完成/不确定部分**：无。原题三项要求均已给出证明，且近最优构造是具体的零边界位移，而非仅矩阵凸组合。

自评：原题范围完整正确；另有一项已证明的局部定量加强。