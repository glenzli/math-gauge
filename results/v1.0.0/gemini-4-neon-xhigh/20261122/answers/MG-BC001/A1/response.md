### 核心结论与对前期相容性估计的纠偏

首先检查题面中的前期相容性计算：六个两井差的行列式确为
$$
\begin{aligned}
\det(A_1-A_2)&=\det\mathrm{diag}(2,-2)=-4, & \det(A_1-A_3)&=\det\mathrm{diag}(5,-1)=-5,\\
\det(A_1-A_4)&=\det\mathrm{diag}(3,3)=9, & \det(A_2-A_3)&=\det\mathrm{diag}(3,1)=3,\\
\det(A_2-A_4)&=\det\mathrm{diag}(1,5)=5, & \det(A_3-A_4)&=\det\mathrm{diag}(-2,4)=-8,
\end{aligned}
$$
均非零，故任意两井之间确实不存在秩一连接。

**然而，前期据此推论“零边界下不能形成能量趋零的混相序列，单元能保留严格正的间隙”是错误的。** 原因在于：二相系统的秩一不相容刚性**不能**逐相外推至四相系统。这里的四井集合 $K=\{A_1,A_2,A_3,A_4\}$ 恰好构成一个 **Tartar 方块（$T_4$ 构型）**：尽管任意两井无秩一连接，但存在四个辅助对角矩阵
$$
B_1=\mathrm{diag}(1,0),\quad B_2=\mathrm{diag}(1,1),\quad B_3=\mathrm{diag}(0,1),\quad B_4=\mathrm{diag}(0,0)=0,
$$
它们沿坐标轴方向首尾相接，将 $0=B_4$ 纳入 $K$ 的层合凸包 $K^{lc}$（从而也在秩一凸包与拟凸包 $K^{qc}$ 中）。因此，即使同时保持零边界条件与统一梯度上界 $\operatorname{ess\,sup}_\Omega\|\nabla u\|_F\le 4$，仍然可以构造出显式多尺度层合位移序列使能量趋于 $0$。

另一方面，四井的对角结构叠加零边界条件确实阻止了**精确零能量解**的存在。三项任务的完整结论如下：

1. **单元能精确值与可达性**：$e_0 = 0$，且**不存在**任何 $u\in\mathcal{A}$ 使 $E(u)=0$（最小值不可达到）。
2. **相体积分数极限**：对任意满足 $E(u_j)\to e_0=0$ 的序列 $u_j\in\mathcal{A}$，向量 $(\pi_1(u_j),\pi_2(u_j),\pi_3(u_j),\pi_4(u_j))$ **必然收敛到同一个唯一极限**
   $$
   \pi^* = \left(\frac{1}{10},\,\frac{3}{10},\,\frac{3}{10},\,\frac{3}{10}\right).
   $$
   全部可能极限组成的集合为单点集 $\left\{\left(\frac{1}{10},\frac{3}{10},\frac{3}{10},\frac{3}{10}\right)\right\}$。
3. **具体近最优位移构造**：见第四部分显式构造的自相似四阶段层合位移序列 $u_j\in\mathcal{A}$，严格满足零边界条件、统一上界 $\operatorname{ess\,sup}_\Omega\|\nabla u_j\|_F \le \sqrt{153/16} < \sqrt{10} < 4$ 及能量估计 $E(u_j) < 185\cdot 6^{-j}\to 0$。

---

### 一、预备引理：零迹 $W^{1,\infty}$ 映射的积分恒等式

**引理 1.** 对任意 $u=(u_1,u_2)\in\mathcal{A}$，以下结论成立：
1. $u$ 在 $\overline{\Omega}=[0,1]^2$ 上有唯一的 Lipschitz 连续代表元（仍记作 $u$），其在 $\partial\Omega$ 上处处为零；且其零延拓
   $$
   \tilde u(x):=\begin{cases}u(x), & x\in\Omega,\\ 0, & x\in\mathbb{R}^2\setminus\Omega,\end{cases}
   $$
   在 $\mathbb{R}^2$ 上全局 Lipschitz 连续，弱梯度满足 $\nabla\tilde u = (\nabla u)\mathbf{1}_\Omega$ a.e. 于 $\mathbb{R}^2$，并且存在序列 $\varphi_k\in C_c^\infty(\Omega;\mathbb{R}^2)$ 使得 $\varphi_k\to u$ 强收敛于 $W^{1,2}(\Omega;\mathbb{R}^2)$。
2. $\displaystyle\int_\Omega \nabla u(x)\,dx = 0$。
3. $\displaystyle\int_\Omega \det(\nabla u(x))\,dx = 0$。

**证明.**
1. 因 $\Omega=(0,1)^2$ 为有界凸区域，任意 $u\in W^{1,\infty}(\Omega;\mathbb{R}^2)$ 在 $\overline{\Omega}$ 上有唯一的 Lipschitz 连续代表元（Lipschitz 常数至多为 $\operatorname{ess\,sup}_\Omega\|\nabla u\|_F\le 4$）。在 Lipschitz 区域上，Sobolev 迹算子与连续函数在边界的逐点限制一致，故 $u|_{\partial\Omega}\equiv 0$。对任意 $x\in\overline{\Omega}$ 和 $y\notin\Omega$，取线段 $[x,y]$ 与 $\partial\Omega$ 的交点 $z$，有 $|\tilde u(x)-\tilde u(y)|=|u(x)-u(z)|\le 4|x-z|\le 4|x-y|$，故 $\tilde u$ 在 $\mathbb{R}^2$ 上全局 Lipschitz，从而 $\tilde u\in W^{1,\infty}(\mathbb{R}^2;\mathbb{R}^2)$ 且 $\nabla\tilde u = (\nabla u)\mathbf{1}_\Omega$ a.e.（在 $\Omega$ 外 $\tilde u\equiv 0$，而 $\partial\Omega$ 测度为零）。

   令中心 $c=(\frac{1}{2},\frac{1}{2})$，对整数 $k\ge 3$ 定义向内收缩的映射
   $$
   v_k(x):=\tilde u\!\left(c+\frac{k}{k-1}(x-c)\right),\qquad x\in\mathbb{R}^2.
   $$
   当 $x\notin\left[\frac{1}{2k},1-\frac{1}{2k}\right]^2$ 时，必有某个分量满足 $|x_i-\frac{1}{2}|>\frac{k-1}{2k}$，从而 $c+\frac{k}{k-1}(x-c)\notin[0,1]^2$，故 $v_k(x)=0$。因此 $\operatorname{supp}(v_k)\subset\left[\frac{1}{2k},1-\frac{1}{2k}\right]^2\Subset\Omega$。由链式法则，$\nabla v_k(x)=\frac{k}{k-1}(\nabla\tilde u)\!\left(c+\frac{k}{k-1}(x-c)\right)$；利用 $L^2(\mathbb{R}^2)$ 中伸缩平移的强连续性，有 $v_k\to u$ 强收敛于 $W^{1,2}(\Omega;\mathbb{R}^2)$。再取标准磨光子 $\rho_\delta$（支集在 $B_\delta(0)$ 内），选充分小的 $\delta_k\in(0,\frac{1}{4k})$ 使 $\varphi_k:=\rho_{\delta_k}*v_k\in C_c^\infty(\Omega;\mathbb{R}^2)$ 满足 $\|\varphi_k-v_k\|_{W^{1,2}(\Omega)}<\frac{1}{k}$，即得 $\varphi_k\to u$ 强收敛于 $W^{1,2}(\Omega;\mathbb{R}^2)$。

2. 取截断函数 $\zeta\in C_c^\infty(\mathbb{R}^2)$ 使 $\zeta\equiv 1$ 于 $[0,1]^2$。由 $\nabla\tilde u = (\nabla u)\mathbf{1}_\Omega$ 及 $\tilde u\,\partial_m\zeta\equiv 0$（在 $\overline{\Omega}$ 上 $\partial_m\zeta=0$，在 $\overline{\Omega}$ 外 $\tilde u=0$），对任意 $l,m\in\{1,2\}$ 有
   $$
   \int_\Omega \partial_m u_l(x)\,dx = \int_{\mathbb{R}^2} (\partial_m \tilde u_l)(x)\,\zeta(x)\,dx = -\int_{\mathbb{R}^2} \tilde u_l(x)\,\partial_m\zeta(x)\,dx = 0.
   $$
   故 $\int_\Omega \nabla u\,dx = 0$。

3. 先证一个对任意 $2\times 2$ 实矩阵 $A,B$ 均成立的精确估计：记 $\operatorname{cof}\begin{pmatrix}a&b\\c&d\end{pmatrix}:=\begin{pmatrix}d&-c\\-b&a\end{pmatrix}$ 并以 $\langle X,Y\rangle:=\operatorname{tr}(X^T Y)$ 表示 Frobenius 内积。直接展开可知 $\langle X,\operatorname{cof}(Y)\rangle=\langle Y,\operatorname{cof}(X)\rangle$，$\langle X,\operatorname{cof}(X)\rangle=2\det X$，且 $\|\operatorname{cof}(X)\|_F=\|X\|_F$。于是
   $$
   \det A - \det B = \frac{1}{2}\big\langle A-B,\,\operatorname{cof}(A)+\operatorname{cof}(B)\big\rangle,
   $$
   由 Cauchy–Schwarz 不等式得
   $$
   |\det A - \det B| \le \frac{1}{2}\|A-B\|_F\big(\|A\|_F+\|B\|_F\big). \tag{1}
   $$
   对 1 中构造的任意 $\varphi_k=(\varphi_{k,1},\varphi_{k,2})\in C_c^\infty(\Omega;\mathbb{R}^2)$，因混合二阶偏导相等，有散度恒等式
   $$
   \det(\nabla\varphi_k) = \partial_1\varphi_{k,1}\partial_2\varphi_{k,2}-\partial_2\varphi_{k,1}\partial_1\varphi_{k,2} = \partial_1(\varphi_{k,1}\partial_2\varphi_{k,2})-\partial_2(\varphi_{k,1}\partial_1\varphi_{k,2}).
   $$
   由 Fubini 定理与微积分基本定理（$\varphi_k$ 在 $\partial\Omega$ 附近恒为零），得 $\int_\Omega \det(\nabla\varphi_k)\,dx = 0$。结合 $(1)$ 与 Cauchy–Schwarz 不等式：
   $$
   \left|\int_\Omega \det(\nabla u)\,dx\right| = \left|\int_\Omega \big(\det(\nabla u)-\det(\nabla\varphi_k)\big)\,dx\right| \le \frac{1}{2}\|\nabla u-\nabla\varphi_k\|_{L^2(\Omega)}\big(\|\nabla u\|_{L^2(\Omega)}+\|\nabla\varphi_k\|_{L^2(\Omega)}\big)\xrightarrow{k\to\infty} 0,
   $$
   因此 $\int_\Omega \det(\nabla u)\,dx = 0$。$\square$

---

### 二、任务 1 的证明：$e_0 = 0$ 且不可达到

**命题 1.** $e_0 = 0$，且对任意 $u\in\mathcal{A}$ 均有 $E(u)>0$，故最小值 $e_0$ 不能在 $\mathcal{A}$ 中达到。

**证明.**
1. **$e_0 = 0$ 的确定**：被积函数 $\min_{1\le i\le 4}\|\nabla u(x)-A_i\|_F^2\ge 0$，故对所有 $u\in\mathcal{A}$ 有 $E(u)\ge 0$，从而 $e_0\ge 0$。另一方面，第四部分构造了具体序列 $u_j\in\mathcal{A}$ 满足 $E(u_j) < 185\cdot 6^{-j}\to 0$，故 $e_0\le \lim_{j\to\infty} E(u_j)=0$。因此 $e_0 = 0$。

2. **不可达性**：反设存在 $u=(u_1,u_2)\in\mathcal{A}$ 使 $E(u)=0$。则对几乎处处的 $x\in\Omega$，有
   $$
   \min_{1\le i\le 4}\|\nabla u(x)-A_i\|_F^2 = 0 \implies \nabla u(x)\in K = \{A_1,A_2,A_3,A_4\}.
   $$
   由于四个矩阵 $A_1,A_2,A_3,A_4$ 全为对角矩阵，其非对角元均为零，故
   $$
   \partial_2 u_1(x)=0,\qquad \partial_1 u_2(x)=0 \qquad \text{a.e. } x\in\Omega.
   $$
   取引理 1 中的零延拓 $\tilde u=(\tilde u_1,\tilde u_2)\in W^{1,\infty}(\mathbb{R}^2;\mathbb{R}^2)$，则 $\partial_2\tilde u_1 = (\partial_2 u_1)\mathbf{1}_\Omega = 0$ 且 $\partial_1\tilde u_2 = (\partial_1 u_2)\mathbf{1}_\Omega = 0$ a.e. 于 $\mathbb{R}^2$。用标准磨光子 $\rho_\varepsilon$（$0<\varepsilon<1$）做卷积，令 $\tilde u_\varepsilon := \rho_\varepsilon*\tilde u\in C_c^\infty(\mathbb{R}^2;\mathbb{R}^2)$，其支集含于 $[-1,2]^2$。由弱导数与卷积的交换性质，对所有 $x\in\mathbb{R}^2$ 处处成立
   $$
   \partial_2\tilde u_{\varepsilon,1}(x) = (\rho_\varepsilon*\partial_2\tilde u_1)(x) = 0,\qquad \partial_1\tilde u_{\varepsilon,2}(x) = (\rho_\varepsilon*\partial_1\tilde u_2)(x) = 0.
   $$
   因 $\tilde u_{\varepsilon,1}(x_1,-2)=0$ 且 $\tilde u_{\varepsilon,2}(-2,x_2)=0$，沿坐标轴积分立得
   $$
   \tilde u_{\varepsilon,1}(x_1,x_2)=\int_{-2}^{x_2}\partial_2\tilde u_{\varepsilon,1}(x_1,t)\,dt=0,\qquad
   \tilde u_{\varepsilon,2}(x_1,x_2)=\int_{-2}^{x_1}\partial_1\tilde u_{\varepsilon,2}(t,x_2)\,dt=0.
   $$
   故 $\tilde u_\varepsilon\equiv 0$。令 $\varepsilon\to 0^+$，由 $\tilde u_\varepsilon\to\tilde u$ 一致收敛得 $u\equiv 0$ 于 $\overline{\Omega}$。由此 $\nabla u\equiv 0$，于是
   $$
   E(u) = \int_\Omega \min_{1\le i\le 4}\|0-A_i\|_F^2\,dx = \min\{9,5,5,9\} = 5 \ne 0,
   $$
   矛盾！因此没有任何 $u\in\mathcal{A}$ 可以达到 $e_0=0$。$\square$

---

### 三、任务 2 的证明：相体积分数必然收敛到唯一极限

**命题 2.** 对任意 $u\in\mathcal{A}$，记 $\pi(u)=(\pi_1(u),\pi_2(u),\pi_3(u),\pi_4(u))^T$ 及 $\pi^*=\left(\frac{1}{10},\frac{3}{10},\frac{3}{10},\frac{3}{10}\right)^T$，有定量稳定性估计
$$
\begin{aligned}
\left|\pi_1(u)-\frac{1}{10}\right|&\le\frac{23}{20}\sqrt{E(u)}, &
\left|\pi_2(u)-\frac{3}{10}\right|&\le\frac{5}{4}\sqrt{E(u)},\\
\left|\pi_3(u)-\frac{3}{10}\right|&\le\frac{9}{10}\sqrt{E(u)}, &
\left|\pi_4(u)-\frac{3}{10}\right|&\le\frac{4}{5}\sqrt{E(u)}.
\end{aligned}
$$
特别地，对任意满足 $E(u_j)\to e_0=0$ 的序列 $u_j\in\mathcal{A}$，整个序列 $(\pi_1(u_j),\pi_2(u_j),\pi_3(u_j),\pi_4(u_j))$ **必然收敛**到同一个向量 $\pi^*=\left(\frac{1}{10},\frac{3}{10},\frac{3}{10},\frac{3}{10}\right)$；结合任务 3 中满足 $E(u_j)\to 0$ 序列的存在性，全部可能的极限构成的集合恰为单点集 $\left\{\left(\frac{1}{10},\frac{3}{10},\frac{3}{10},\frac{3}{10}\right)\right\}$。

**证明.**
任取 $u\in\mathcal{A}$，选取 $\nabla u$ 的一个处处有定义的 Lebesgue 可测代表元。按题设的最近井（等距取最小编号）规则，定义集合
$$
\Omega_i:=\left(\bigcap_{1\le k<i}\big\{x\in\Omega:\|\nabla u(x)-A_i\|_F<\|\nabla u(x)-A_k\|_F\big\}\right)\cap\left(\bigcap_{i<k\le 4}\big\{x\in\Omega:\|\nabla u(x)-A_i\|_F\le\|\nabla u(x)-A_k\|_F\big\}\right),
$$
$i=1,2,3,4$。这四个集合均 Lebesgue 可测、两两不相交且并集为 $\Omega$，故 $\pi_i(u)=|\Omega_i|\ge 0$ 满足
$$
\pi_1(u)+\pi_2(u)+\pi_3(u)+\pi_4(u)=|\Omega|=1. \tag{2}
$$
定义分段常值可测矩阵场 $M:\Omega\to K$ 为 $M(x):=A_i$（若 $x\in\Omega_i$）。按定义，对几乎处处的 $x\in\Omega$，
$$
\|\nabla u(x)-M(x)\|_F^2 = \min_{1\le i\le 4}\|\nabla u(x)-A_i\|_F^2,
$$
从而 $\int_\Omega \|\nabla u(x)-M(x)\|_F^2\,dx = E(u)$。由 $|\Omega|=1$ 及 Cauchy–Schwarz 不等式，
$$
\int_\Omega \|M(x)-\nabla u(x)\|_F\,dx \le \sqrt{E(u)}. \tag{3}
$$

**第一步：平均梯度约束。** 由引理 1(2)，$\int_\Omega \nabla u\,dx = 0$，于是
$$
\sum_{i=1}^4 \pi_i(u)A_i = \int_\Omega M(x)\,dx = \int_\Omega\big(M(x)-\nabla u(x)\big)\,dx.
$$
比较 $(1,1)$ 元与 $(2,2)$ 元，记
$$
\begin{aligned}
\varepsilon_1(u)&:=3\pi_1(u)+\pi_2(u)-2\pi_3(u)=\int_\Omega (M-\nabla u)_{11}\,dx,\\
\varepsilon_2(u)&:=2\pi_2(u)+\pi_3(u)-3\pi_4(u)=\int_\Omega (M-\nabla u)_{22}\,dx.
\end{aligned}
$$
因对任意矩阵有 $|X_{11}|,|X_{22}|\le\|X\|_F$，结合 $(3)$ 立得
$$
|\varepsilon_1(u)|\le\sqrt{E(u)},\qquad |\varepsilon_2(u)|\le\sqrt{E(u)}. \tag{4}
$$

**第二步：行列式（零拉格朗日量）约束。** 计算四个井的行列式：
$$
\det A_1=0,\qquad \det A_2=2,\qquad \det A_3=-2,\qquad \det A_4=0.
$$
由引理 1(3)，$\int_\Omega \det(\nabla u)\,dx = 0$，故
$$
\varepsilon_3(u):=\sum_{i=1}^4 \pi_i(u)\det A_i = 2\pi_2(u)-2\pi_3(u) = \int_\Omega\big(\det M(x)-\det\nabla u(x)\big)\,dx.
$$
由于 $\|M(x)\|_F\le \max_{1\le i\le 4}\|A_i\|_F = 3$ 且 $\|\nabla u(x)\|_F\le 4$ a.e. 于 $\Omega$，利用 $(1)$ 与 $(3)$ 得
$$
|\varepsilon_3(u)|\le \frac{1}{2}\int_\Omega \|M(x)-\nabla u(x)\|_F\big(\|M(x)\|_F+\|\nabla u(x)\|_F\big)\,dx \le \frac{7}{2}\sqrt{E(u)}. \tag{5}
$$

**第三步：求解 $4\times 4$ 满秩线性方程组。** 综合 $(2)$ 与 $\varepsilon_1,\varepsilon_2,\varepsilon_3$ 的定义，得到
$$
L\,\pi(u) = \begin{pmatrix}1\\ \varepsilon_1(u)\\ \varepsilon_2(u)\\ \varepsilon_3(u)\end{pmatrix},\qquad
L:=\begin{pmatrix}
1 & 1 & 1 & 1\\
3 & 1 & -2 & 0\\
0 & 2 & 1 & -3\\
0 & 2 & -2 & 0
\end{pmatrix}.
$$
直接计算 $\det(L)$：将第 1 行的 $-3$ 倍加到第 2 行，得
$$
\det(L)=\det\begin{pmatrix}-2&-5&-3\\2&1&-3\\2&-2&0\end{pmatrix}
=\det\begin{pmatrix}-2&-5&-3\\0&-4&-6\\0&-7&-3\end{pmatrix}
=-2\big((-4)(-3)-(-6)(-7)\big)=60\ne 0.
$$
故 $L$ 可逆。直接矩阵乘法可验证其逆矩阵为
$$
L^{-1}=\frac{1}{30}\begin{pmatrix}
3 & 9 & 1 & -7\\
9 & -3 & 3 & 9\\
9 & -3 & 3 & -6\\
9 & -3 & -7 & 4
\end{pmatrix}
$$
（核验 $L\cdot(30L^{-1})$：第 1 行与各列内积依次为 $3+9+9+9=30,9-3-3-3=0,1+3+3-7=0,-7+9-6+4=0$；第 2 行依次为 $9+9-18=0,27-3+6=30,3+3-6=0,-21+9+12=0$；第 3 行依次为 $18+9-27=0,-6-3+9=0,6+3+21=30,18-6-12=0$；第 4 行依次为 $18-18=0,-6+6=0,6-6=0,18+12=30$，恰为 $30I_4$）。

因此
$$
\pi(u) = L^{-1}\begin{pmatrix}1\\ \varepsilon_1(u)\\ \varepsilon_2(u)\\ \varepsilon_3(u)\end{pmatrix}
= \begin{pmatrix}1/10\\ 3/10\\ 3/10\\ 3/10\end{pmatrix}
+ \frac{1}{30}\begin{pmatrix}
9 & 1 & -7\\
-3 & 3 & 9\\
-3 & 3 & -6\\
-3 & -7 & 4
\end{pmatrix}
\begin{pmatrix}\varepsilon_1(u)\\ \varepsilon_2(u)\\ \varepsilon_3(u)\end{pmatrix}.
$$
将估计 $(4)$、$(5)$ 代入每一行，即得：
$$
\begin{aligned}
\left|\pi_1(u)-\frac{1}{10}\right|&\le\frac{1}{30}\left(9+1+7\cdot\frac{7}{2}\right)\sqrt{E(u)}=\frac{69}{60}\sqrt{E(u)}=\frac{23}{20}\sqrt{E(u)},\\
\left|\pi_2(u)-\frac{3}{10}\right|&\le\frac{1}{30}\left(3+3+9\cdot\frac{7}{2}\right)\sqrt{E(u)}=\frac{75}{60}\sqrt{E(u)}=\frac{5}{4}\sqrt{E(u)},\\
\left|\pi_3(u)-\frac{3}{10}\right|&\le\frac{1}{30}\left(3+3+6\cdot\frac{7}{2}\right)\sqrt{E(u)}=\frac{54}{60}\sqrt{E(u)}=\frac{9}{10}\sqrt{E(u)},\\
\left|\pi_4(u)-\frac{3}{10}\right|&\le\frac{1}{30}\left(3+7+4\cdot\frac{7}{2}\right)\sqrt{E(u)}=\frac{48}{60}\sqrt{E(u)}=\frac{4}{5}\sqrt{E(u)}.
\end{aligned}
$$
当 $E(u_j)\to 0$ 时，四个分量分别一致收敛于 $\frac{1}{10},\frac{3}{10},\frac{3}{10},\frac{3}{10}$，无需抽取子列。$\square$

---

### 四、任务 3 的证明：具体近最优位移构造与全面验证

#### 步骤 1：$T_4$ 构型的四步秩一分解

引入四个内部对角矩阵
$$
B_1=\mathrm{diag}(1,0),\qquad B_2=\mathrm{diag}(1,1),\qquad B_3=\mathrm{diag}(0,1),\qquad B_4=\mathrm{diag}(0,0)=0.
$$
直接验证以下四条秩一凸组合恒等式：
$$
\begin{aligned}
\text{(S1)}\quad B_4 &= \frac{1}{4}A_4 + \frac{3}{4}B_3, && A_4 - B_3 = \mathrm{diag}(0,-4)\quad (\text{秩一，竖直层合}),\\
\text{(S2)}\quad B_3 &= \frac{1}{3}A_3 + \frac{2}{3}B_2, && A_3 - B_2 = \mathrm{diag}(-3,0)\quad (\text{秩一，水平层合}),\\
\text{(S3)}\quad B_2 &= \frac{1}{2}A_2 + \frac{1}{2}B_1, && A_2 - B_1 = \mathrm{diag}(0,2)\quad\ \ (\text{秩一，竖直层合}),\\
\text{(S4)}\quad B_1 &= \frac{1}{3}A_1 + \frac{2}{3}B_4, && A_1 - B_4 = \mathrm{diag}(3,0)\quad\ \ (\text{秩一，水平层合}).
\end{aligned}
$$
注意四个井和四个内部矩阵的 Frobenius 范数平方分别为：
$$
\|A_1\|_F^2=\|A_4\|_F^2=9,\quad \|A_2\|_F^2=\|A_3\|_F^2=5,\quad \|B_1\|_F^2=\|B_3\|_F^2=1,\quad \|B_2\|_F^2=2,\quad \|B_4\|_F^2=0.
$$
全部矩阵的 Frobenius 范数均 $\le 3$，离上界 $4$ 有充足余量。下面我们将这四步秩一分解转化为显式的零边界位移场。

---

#### 步骤 2：矩形上的秩一层合扰动引理

**引理 2（矩形秩一替换模块）.** 设 $R=(x_1^0,x_1^0+L_1)\times(x_2^0,x_2^0+L_2)\subset\mathbb{R}^2$ 为开矩形（$L_1,L_2>0$），$B,P,B'$ 为对角矩阵满足 $B=\theta P+(1-\theta)B'$（$\theta\in(0,1)$）且 $\operatorname{rank}(P-B')=1$。给定 $\alpha\in(0,\frac{1}{2})$ 与正整数 $N\ge 1$，可显式构造全局 Lipschitz 映射 $\phi_R:\mathbb{R}^2\to\mathbb{R}^2$，支集含于 $\overline{R}$（特别地在 $\mathbb{R}^2\setminus R$ 及 $\partial R$ 上恒为零），满足以下性质：

- **情形 V（竖直层合，$P-B'=\mathrm{diag}(0,p_2-b'_2)$）**：写 $B=\mathrm{diag}(b_1,b_2)$，$P=\mathrm{diag}(b_1,p_2)$，$B'=\mathrm{diag}(b_1,b'_2)$（$b_2=\theta p_2+(1-\theta)b'_2$）。
  定义支集在 $[0,L_1]$ 内的梯形截断函数 $\eta:\mathbb{R}\to[0,1]$：
  $$
  \eta(s_1):=\begin{cases}
  \dfrac{s_1}{\alpha L_1}, & 0\le s_1\le \alpha L_1,\\[6pt]
  1, & \alpha L_1 < s_1 < (1-\alpha)L_1,\\[6pt]
  \dfrac{L_1-s_1}{\alpha L_1}, & (1-\alpha)L_1\le s_1\le L_1,\\[6pt]
  0, & s_1\notin[0,L_1],
  \end{cases}
  $$
  以及周期 $\delta:=L_2/N$、支集在 $[0,L_2]$ 内的锯齿函数 $h:\mathbb{R}\to\mathbb{R}$：对 $k=0,1,\dots,N-1$ 与 $s_2=k\delta+t$（$t\in[0,\delta]$），令
  $$
  h(k\delta+t):=\begin{cases}
  (p_2-b_2)\,t, & 0\le t\le \theta\delta,\\[4pt]
  (p_2-b_2)\theta\delta + (b'_2-b_2)(t-\theta\delta), & \theta\delta < t\le \delta,
  \end{cases}
  $$
  并在 $s_2\notin[0,L_2]$ 上令 $h(s_2):=0$。显式定义
  $$
  \phi_R(x_1,x_2):=\begin{pmatrix}0\\[2pt]\eta(x_1-x_1^0)\,h(x_2-x_2^0)\end{pmatrix}.
  $$
  则：
  1. $h(k\delta)=0$ 对所有 $k=0,1,\dots,N$ 成立，故 $\eta,h$ 均在 $\mathbb{R}$ 上有界且全局 Lipschitz，$\phi_R\in W^{1,\infty}(\mathbb{R}^2;\mathbb{R}^2)$ 且 $\operatorname{supp}(\phi_R)\subset\overline{R}$；
  2. 存在 $N$ 个两两不相交的开子矩形 $R_k^{(P)}:=(x_1^0+\alpha L_1,x_1^0+(1-\alpha)L_1)\times(x_2^0+k\delta,x_2^0+(k+\theta)\delta)$，其上 $B+\nabla\phi_R\equiv P$，总面积为 $(1-2\alpha)\theta|R|$；
  3. 存在 $N$ 个两两不相交的开子矩形 $R_k^{(B')}:=(x_1^0+\alpha L_1,x_1^0+(1-\alpha)L_1)\times(x_2^0+(k+\theta)\delta,x_2^0+(k+1)\delta)$，每个尺寸均为 $\big((1-2\alpha)L_1,\,(1-\theta)\frac{L_2}{N}\big)$，其上 $B+\nabla\phi_R\equiv B'$，总面积为 $(1-2\alpha)(1-\theta)|R|$；
  4. 除去上述子矩形及有限条坐标线段（零测集）后，剩余过渡带
     $$
     T_R:=\Big((x_1^0,x_1^0+\alpha L_1)\cup(x_1^0+(1-\alpha)L_1,x_1^0+L_1)\Big)\times(x_2^0,x_2^0+L_2)
     $$
     的面积为 $|T_R|=2\alpha|R|$；在 $R$ 上几乎处处有
     $$
     \|B+\nabla\phi_R(x)\|_F^2 \le \max\!\big(\|P\|_F^2,\|B'\|_F^2\big) + \left(\frac{\theta(1-\theta)|p_2-b'_2|\,L_2}{\alpha L_1 N}\right)^2. \tag{6V}
     $$

- **情形 H（水平层合，$P-B'=\mathrm{diag}(p_1-b'_1,0)$）**：写 $B=\mathrm{diag}(b_1,b_2)$，$P=\mathrm{diag}(p_1,b_2)$，$B'=\mathrm{diag}(b'_1,b_2)$（$b_1=\theta p_1+(1-\theta)b'_1$）。对称地交换 $(x_1,L_1,u_1)$ 与 $(x_2,L_2,u_2)$ 的角色，取 $[0,L_1]$ 上周期为 $L_1/N$、斜率为 $p_1-b_1$（占 $\theta$）与 $b'_1-b_1$（占 $1-\theta$）的锯齿函数 $h$，以及 $[0,L_2]$ 上的梯形截断函数 $\eta$，显式定义
  $$
  \phi_R(x_1,x_2):=\begin{pmatrix}h(x_1-x_1^0)\,\eta(x_2-x_2^0)\\[2pt]0\end{pmatrix}.
  $$
  则 $\phi_R\in W^{1,\infty}(\mathbb{R}^2;\mathbb{R}^2)$ 且 $\operatorname{supp}(\phi_R)\subset\overline{R}$；$R$ 除去零测集后分解为：
  - $N$ 个不相交的 $P$-开子矩形，总面积 $(1-2\alpha)\theta|R|$，其上 $B+\nabla\phi_R\equiv P$；
  - $N$ 个不相交的 $B'$-开子矩形，每个尺寸均为 $\big((1-\theta)\frac{L_1}{N},\,(1-2\alpha)L_2\big)$，总面积 $(1-2\alpha)(1-\theta)|R|$，其上 $B+\nabla\phi_R\equiv B'$；
  - 过渡带 $T_R:=(x_1^0,x_1^0+L_1)\times\big((x_2^0,x_2^0+\alpha L_2)\cup(x_2^0+(1-\alpha)L_2,x_2^0+L_2)\big)$，面积 $|T_R|=2\alpha|R|$；
  且在 $R$ 上几乎处处有
  $$
  \|B+\nabla\phi_R(x)\|_F^2 \le \max\!\big(\|P\|_F^2,\|B'\|_F^2\big) + \left(\frac{\theta(1-\theta)|p_1-b'_1|\,L_1}{\alpha L_2 N}\right)^2. \tag{6H}
  $$

**引理 2 的证明（以情形 V 为例，情形 H 完全对称）.**
在每个周期 $[k\delta,(k+1)\delta]$ 的右端点 $t=\delta$ 处，
$$
h((k+1)\delta) = (p_2-b_2)\theta\delta + (b'_2-b_2)(1-\theta)\delta = \big(\theta p_2 + (1-\theta)b'_2 - b_2\big)\delta = 0,
$$
且在 $t=\theta\delta$ 处左右极限一致，故 $h$ 在 $\mathbb{R}$ 上连续且分段线性，支集在 $[0,L_2]$ 内。由 $p_2-b_2=(1-\theta)(p_2-b'_2)$，对所有 $s_2\in\mathbb{R}$ 有
$$
|h(s_2)| \le |p_2-b_2|\theta\delta = \theta(1-\theta)|p_2-b'_2|\frac{L_2}{N}.
$$
又 $\eta\in[0,1]$ 在 $\mathbb{R}$ 上连续分段线性且支集在 $[0,L_1]$ 内，$|\eta'(s_1)|\le\frac{1}{\alpha L_1}$ a.e.。两个有界全局 Lipschitz 函数的乘积仍全局 Lipschitz，故 $\phi_R\in W^{1,\infty}(\mathbb{R}^2;\mathbb{R}^2)$ 且 $\operatorname{supp}(\phi_R)\subset\overline{R}$。

按分离变量乘积求导（直接用 Fubini 定理对任意 $\varphi\in C_c^\infty(\mathbb{R}^2)$ 分部积分即可验证），对几乎处处的 $(x_1,x_2)\in R$（记 $s_1=x_1-x_1^0,\ s_2=x_2-x_2^0$），有
$$
B+\nabla\phi_R(x) = \begin{pmatrix}b_1 & 0\\ \eta'(s_1)h(s_2) & b_2+\eta(s_1)h'(s_2)\end{pmatrix}.
$$
当 $s_1\in(\alpha L_1,(1-\alpha)L_1)$ 时，$\eta(s_1)=1$ 且 $\eta'(s_1)=0$：在 $R_k^{(P)}$ 上 $h'(s_2)=p_2-b_2$，得 $B+\nabla\phi_R=P$；在 $R_k^{(B')}$ 上 $h'(s_2)=b'_2-b_2$，得 $B+\nabla\phi_R=B'$。而在 $R$ 上几乎处处，因 $\eta(s_1)\in[0,1]$ 且 $h'(s_2)\in\{p_2-b_2,\,b'_2-b_2\}$，元素 $b_2+\eta(s_1)h'(s_2)$ 必为 $b_2$ 与 $p_2$ 或 $b_2$ 与 $b'_2$ 的凸组合，故落在区间 $[\min(p_2,b'_2),\max(p_2,b'_2)]$ 内，从而
$$
b_1^2 + \big(b_2+\eta(s_1)h'(s_2)\big)^2 \le \max\!\big(b_1^2+p_2^2,\,b_1^2+(b'_2)^2\big) = \max\!\big(\|P\|_F^2,\|B'\|_F^2\big).
$$
对非对角元，有
$$
|\eta'(s_1)h(s_2)| \le \frac{1}{\alpha L_1}\cdot \theta(1-\theta)|p_2-b'_2|\frac{L_2}{N}.
$$
将两项平方相加即得 $(6\text{V})$。$\square$

---

#### 步骤 3：单轮四阶段“元胞位移” $\Phi_\alpha$ 的构造与正方形无剩余剖分

固定任意参数 $\alpha\in\left(0,\frac{1}{2}\right)$，记 $c:=1-2\alpha\in(0,1)$。在 $\Omega=(0,1)^2$（尺寸 $L_1^{(0)}=1,L_2^{(0)}=1$，初始常梯度 $B_4=0$）上，依次执行对应于 (S1)–(S4) 的四个层合阶段，定义全局 Lipschitz 映射
$$
\Phi_\alpha := \psi_1 + \psi_2 + \psi_3 + \psi_4 \in W^{1,\infty}(\mathbb{R}^2;\mathbb{R}^2).
$$
各阶段的参数与结果显式规定如下：

1. **阶段 1（竖直层合 $B_4=\frac{1}{4}A_4+\frac{3}{4}B_3$）**：
   取 $N_1:=\left\lceil\dfrac{1}{\alpha}\right\rceil$。对 $\Omega$ 应用引理 2（情形 V，取 $B=B_4,P=A_4,B'=B_3,\theta=\frac{1}{4}$），令 $\psi_1:=\phi_\Omega$。
   - 由 $\theta(1-\theta)|-3-1|=\frac{3}{4}$ 及 $N_1\ge\frac{1}{\alpha}$，式 $(6\text{V})$ 给出
     $$
     \|\nabla\psi_1\|_F^2 \le \max(9,1) + \left(\frac{3}{4\alpha N_1}\right)^2 \le 9 + \frac{9}{16} = \frac{153}{16} < 10.
     $$
   - 过渡带 $T_1$ 面积为 $2\alpha$；$A_4$-矩形集合并记为 $G_{A_4}$，面积为 $\frac{1}{4}c$；产生 $N_1$ 个两两不相交的 $B_3$-开矩形，记其集合为 $\mathcal{R}_1$，每个尺寸均为
     $$
     L_1^{(1)} = c,\qquad L_2^{(1)} = \frac{3}{4N_1},
     $$
     总面积为 $\frac{3}{4}c$，且在每个 $R\in\mathcal{R}_1$ 上 $\nabla\psi_1\equiv B_3$。

2. **阶段 2（水平层合 $B_3=\frac{1}{3}A_3+\frac{2}{3}B_2$）**：
   取
   $$
   N_2:=\left\lceil\frac{L_1^{(1)}}{\alpha L_2^{(1)}}\right\rceil = \left\lceil\frac{4cN_1}{3\alpha}\right\rceil.
   $$
   对每个 $R\in\mathcal{R}_1$ 应用引理 2（情形 H，取 $B=B_3,P=A_3,B'=B_2,\theta=\frac{1}{3},N=N_2$），令 $\psi_2:=\sum_{R\in\mathcal{R}_1}\phi_R$。因各 $R\in\mathcal{R}_1$ 两两不相交，在每个 $R\in\mathcal{R}_1$ 上 $\nabla(\psi_1+\psi_2)=B_3+\nabla\phi_R$，在 $\bigcup_{R\in\mathcal{R}_1}R$ 外 $\nabla\psi_2=0$ a.e.。
   - 由 $\theta(1-\theta)|-2-1|=\frac{2}{3}$ 及 $N_2\ge\frac{L_1^{(1)}}{\alpha L_2^{(1)}}$，式 $(6\text{H})$ 给出在每个 $R\in\mathcal{R}_1$ 上
     $$
     \|\nabla(\psi_1+\psi_2)\|_F^2 \le \max(5,2) + \left(\frac{2L_1^{(1)}}{3\alpha L_2^{(1)}N_2}\right)^2 \le 5 + \frac{4}{9} = \frac{49}{9} < 10.
     $$
   - 新增过渡带 $T_2$ 总面积为 $2\alpha\cdot\frac{3}{4}c$；$A_3$-矩形并集 $G_{A_3}$ 面积为 $\frac{1}{3}c\cdot\frac{3}{4}c=\frac{1}{4}c^2$；产生 $N_1N_2$ 个两两不相交的 $B_2$-开矩形（集合记为 $\mathcal{R}_2$），每个尺寸均为
     $$
     L_1^{(2)} = \frac{2c}{3N_2},\qquad L_2^{(2)} = \frac{3c}{4N_1},
     $$
     总面积为 $\frac{1}{2}c^2$，且其上 $\nabla(\psi_1+\psi_2)\equiv B_2$。

3. **阶段 3（竖直层合 $B_2=\frac{1}{2}A_2+\frac{1}{2}B_1$）**：
   取
   $$
   N_3:=\left\lceil\frac{L_2^{(2)}}{\alpha L_1^{(2)}}\right\rceil = \left\lceil\frac{9N_2}{8\alpha N_1}\right\rceil.
   $$
   对每个 $R\in\mathcal{R}_2$ 应用引理 2（情形 V，取 $B=B_2,P=A_2,B'=B_1,\theta=\frac{1}{2},N=N_3$），令 $\psi_3:=\sum_{R\in\mathcal{R}_2}\phi_R$。
   - 由 $\theta(1-\theta)|2-0|=\frac{1}{2}$ 及 $N_3\ge\frac{L_2^{(2)}}{\alpha L_1^{(2)}}$，式 $(6\text{V})$ 给出在每个 $R\in\mathcal{R}_2$ 上
     $$
     \|\nabla(\psi_1+\psi_2+\psi_3)\|_F^2 \le \max(5,1) + \left(\frac{L_2^{(2)}}{2\alpha L_1^{(2)}N_3}\right)^2 \le 5 + \frac{1}{4} = \frac{21}{4} < 10.
     $$
   - 新增过渡带 $T_3$ 总面积为 $2\alpha\cdot\frac{1}{2}c^2$；$A_2$-矩形并集 $G_{A_2}$ 面积为 $\frac{1}{2}c\cdot\frac{1}{2}c^2=\frac{1}{4}c^3$；产生 $N_1N_2N_3$ 个两两不相交的 $B_1$-开矩形（集合记为 $\mathcal{R}_3$），每个尺寸均为
     $$
     L_1^{(3)} = \frac{2c^2}{3N_2},\qquad L_2^{(3)} = \frac{3c}{8N_1N_3},
     $$
     总面积为 $\frac{1}{4}c^3$，且其上 $\nabla(\psi_1+\psi_2+\psi_3)\equiv B_1$。

4. **阶段 4（水平层合 $B_1=\frac{1}{3}A_1+\frac{2}{3}B_4$，并精确配准正方形比例）**：
   取正整数
   $$
   N_4 := 32 N_1 N_3.
   $$
   对每个 $R\in\mathcal{R}_3$ 应用引理 2（情形 H，取 $B=B_1,P=A_1,B'=B_4,\theta=\frac{1}{3},N=N_4$），令 $\psi_4:=\sum_{R\in\mathcal{R}_3}\phi_R$，并定义 $\Phi_\alpha:=\psi_1+\psi_2+\psi_3+\psi_4$。
   - **检验非对角梯度项**：因 $\theta(1-\theta)|3-0|=\frac{2}{3}$，且由阶段 2 知 $N_2\ge\frac{4cN_1}{3\alpha}$，直接计算得
     $$
     \frac{2}{3}\cdot\frac{L_1^{(3)}}{\alpha L_2^{(3)} N_4}
     = \frac{2}{3}\cdot\frac{\frac{2c^2}{3N_2}}{\alpha\cdot\frac{3c}{8N_1N_3}\cdot 32N_1N_3}
     = \frac{c}{27\alpha N_2}
     \le \frac{c}{27\alpha\cdot\frac{4cN_1}{3\alpha}}
     = \frac{1}{36N_1} \le \frac{1}{36}.
     $$
     于是式 $(6\text{H})$ 给出在每个 $R\in\mathcal{R}_3$ 上
     $$
     \|\nabla\Phi_\alpha\|_F^2 \le \max(9,0) + \frac{1}{36^2} < \frac{153}{16} < 10.
     $$
   - 新增过渡带 $T_4$ 总面积为 $2\alpha\cdot\frac{1}{4}c^3$；$A_1$-矩形并集 $G_{A_1}$ 面积为 $\frac{1}{3}c\cdot\frac{1}{4}c^3=\frac{1}{12}c^4$；产生 $N_1N_2N_3N_4=32N_1^2N_2N_3^2$ 个两两不相交的 $B_4$-开矩形（集合记为 $\mathcal{R}_4$），其上 $\nabla\Phi_\alpha\equiv B_4=0$，每个尺寸均为
     $$
     L_1^{(4)} = \frac{2}{3N_4}L_1^{(3)} = \frac{c^2}{72N_1N_2N_3},\qquad
     L_2^{(4)} = c L_2^{(3)} = \frac{3c^2}{8N_1N_3}.
     $$
   - **精确正方形剖分**：计算每个 $B_4$-矩形的高宽比，恰好为正整数：
     $$
     \frac{L_2^{(4)}}{L_1^{(4)}} = \frac{3}{8N_1N_3}\cdot 72N_1N_2N_3 = 27 N_2 \in \mathbb{Z}_{>0}.
     $$
     记 $s:=L_1^{(4)}=\frac{c^2}{72N_1N_2N_3}$。用 $27N_2-1$ 条等距水平线段把每个 $R\in\mathcal{R}_4$ 无剩余面积地切成 $27N_2$ 个边长为 $s$ 的开正方形，共得
     $$
     M := (32N_1^2N_2N_3^2)\cdot(27N_2) = 864 N_1^2 N_2^2 N_3^2
     $$
     个两两不相交的开正方形 $S_r = x^{(r)}+(0,s)^2 \subset \Omega$（$r=1,\dots,M$），它们的总面积为
     $$
     \rho := \sum_{r=1}^M |S_r| = M s^2 = 864 N_1^2 N_2^2 N_3^2 \cdot \frac{c^4}{5184 N_1^2 N_2^2 N_3^2} = \frac{1}{6}c^4 = \frac{1}{6}(1-2\alpha)^4 < \frac{1}{6}.
     $$

**汇总 $\Phi_\alpha$ 的性质：**
1. $\Phi_\alpha=\psi_1+\psi_2+\psi_3+\psi_4$ 是有限个支集含于 $\overline{\Omega}$ 的全局 Lipschitz 映射之和，故 $\Phi_\alpha\in W^{1,\infty}(\mathbb{R}^2;\mathbb{R}^2)$ 且在 $\mathbb{R}^2\setminus\Omega$（特别是 $\partial\Omega$）上恒为零。
2. 结合四个阶段的估计，有
   $$
   \operatorname{ess\,sup}_\Omega \|\nabla\Phi_\alpha\|_F \le \sqrt{\frac{153}{16}} < \sqrt{10} < 4. \tag{7}
   $$
3. 除去零测集（有限条线段）外，$\Omega$ 分解为三个两两不相交的开集：
   - 精确取井区 $G_{\mathrm{well}}:=G_{A_1}\cup G_{A_2}\cup G_{A_3}\cup G_{A_4}$，其上 $\nabla\Phi_\alpha\in K$，能量密度恒为 $0$，各相面积分别为
     $$
     |G_{A_1}|=\frac{1}{12}c^4,\quad |G_{A_2}|=\frac{1}{4}c^3,\quad |G_{A_3}|=\frac{1}{4}c^2,\quad |G_{A_4}|=\frac{1}{4}c;
     $$
   - 剩余零梯度区 $G_{\mathrm{rem}}:=\bigcup_{r=1}^M S_r$，总面积 $\rho=\frac{1}{6}c^4<\frac{1}{6}$，在每个正方形 $S_r$ 上 $\nabla\Phi_\alpha\equiv 0$；
   - 过渡区 $G_{\mathrm{trans}}:=T_1\cup T_2\cup T_3\cup T_4$，总面积满足
     $$
     |G_{\mathrm{trans}}| = 2\alpha\left(1+\frac{3}{4}c+\frac{1}{2}c^2+\frac{1}{4}c^3\right) < 2\alpha\left(1+\frac{3}{4}+\frac{1}{2}+\frac{1}{4}\right) = 5\alpha.
     $$
4. 在 $G_{\mathrm{trans}}$ 上，由 $(7)$ 有 $\|\nabla\Phi_\alpha\|_F^2 < 10$ a.e.，结合 $\|F-A_2\|_F^2\le 2\|F\|_F^2+2\|A_2\|_F^2$（$\|A_2\|_F^2=5$）得
   $$
   \min_{1\le i\le 4}\|\nabla\Phi_\alpha(x)-A_i\|_F^2 \le \|\nabla\Phi_\alpha(x)-A_2\|_F^2 \le 2(10)+2(5) = 30 \qquad \text{a.e. } x\in G_{\mathrm{trans}},
   $$
   因此单轮过渡区的能量贡献满足
   $$
   E_{\mathrm{trans}}(\alpha):=\int_{G_{\mathrm{trans}}}\min_{1\le i\le 4}\|\nabla\Phi_\alpha(x)-A_i\|_F^2\,dx \le 30\,|G_{\mathrm{trans}}| < 150\alpha. \tag{8}
   $$

---

#### 步骤 4：自相似迭代位移序列与完整验证

对任意给定的 $\alpha\in(0,\frac{1}{2})$，在 $\mathbb{R}^2$ 上递推定义映射序列 $\{u_\alpha^{(m)}\}_{m=0}^\infty$：
$$
u_\alpha^{(0)}(x) := 0,\qquad
u_\alpha^{(m+1)}(x) := \Phi_\alpha(x) + \sum_{r=1}^M s\,u_\alpha^{(m)}\!\left(\frac{x-x^{(r)}}{s}\right)\quad (m\ge 0). \tag{9}
$$
下面对 $m\ge 0$ 用数学归纳法同时验证零边界条件、统一梯度上界与精确能量递推公式：

1. **正则性与零边界条件**：
   $u_\alpha^{(0)}\equiv 0$ 在 $\mathbb{R}^2$ 上全局 Lipschitz 且在 $\mathbb{R}^2\setminus\Omega$ 上恒为零。设 $u_\alpha^{(m)}$ 亦具有此性质。对每个 $r=1,\dots,M$，因 $S_r=x^{(r)}+(0,s)^2\subset\Omega$，映射 $x\mapsto s\,u_\alpha^{(m)}\!\left(\frac{x-x^{(r)}}{s}\right)$ 在 $\mathbb{R}^2$ 上全局 Lipschitz 且在 $\mathbb{R}^2\setminus S_r$（从而在 $\mathbb{R}^2\setminus\Omega$）上恒为零。又 $\Phi_\alpha$ 全局 Lipschitz 且在 $\mathbb{R}^2\setminus\Omega$ 上恒为零，故有限和 $u_\alpha^{(m+1)}$ 同样在 $\mathbb{R}^2$ 上全局 Lipschitz 且在 $\mathbb{R}^2\setminus\Omega$ 上恒为零。将其限制于 $\Omega$，即得 $u_\alpha^{(m+1)}\in W^{1,\infty}(\Omega;\mathbb{R}^2)$ 且在 $\partial\Omega$ 上的迹为 $0$。

2. **统一梯度上界（$\le 4$）**：
   开集 $\Omega\setminus\bigcup_{r=1}^M\overline{S_r}$ 与 $S_1,\dots,S_M$ 两两不相交，其并集与 $\Omega$ 只差零测集 $\bigcup_{r=1}^M\partial S_r$。
   - 当 $x\in\Omega\setminus\bigcup_{r=1}^M\overline{S_r}$ 时，$(9)$ 中的求和项在 $x$ 的某邻域内恒为零，故 $\nabla u_\alpha^{(m+1)}(x)=\nabla\Phi_\alpha(x)$ a.e.。
   - 当 $x\in S_r$ 时，因 $\nabla\Phi_\alpha\equiv 0$ 于 $S_r$ 且对所有 $r'\ne r$ 有 $u_\alpha^{(m)}\!\left(\frac{\cdot-x^{(r')}}{s}\right)\equiv 0$ 于 $S_r$，由链式法则得
     $$
     \nabla u_\alpha^{(m+1)}(x) = \nabla\!\left[s\,u_\alpha^{(m)}\!\left(\frac{x-x^{(r)}}{s}\right)\right] = (\nabla u_\alpha^{(m)})\!\left(\frac{x-x^{(r)}}{s}\right)\qquad \text{a.e. } x\in S_r.
     $$
   因此，结合 $(7)$ 与归纳假设 $\operatorname{ess\,sup}_\Omega\|\nabla u_\alpha^{(m)}\|_F\le\sqrt{153/16}$，立得
   $$
   \operatorname{ess\,sup}_\Omega\|\nabla u_\alpha^{(m+1)}\|_F = \max\!\left(\operatorname{ess\,sup}_{\Omega\setminus G_{\mathrm{rem}}}\|\nabla\Phi_\alpha\|_F,\ \operatorname{ess\,sup}_\Omega\|\nabla u_\alpha^{(m)}\|_F\right) \le \sqrt{\frac{153}{16}} < \sqrt{10} < 4.
   $$
   由此 $u_\alpha^{(m)}\in\mathcal{A}$ 对一切 $\alpha\in(0,\frac{1}{2})$ 和 $m\ge 0$ 成立。

3. **能量估计**：
   利用上述梯度分块表达式，并注意到在 $G_{\mathrm{well}}$ 上被积函数为 $0$，在每个 $S_r$ 上作变量代换 $y=\frac{x-x^{(r)}}{s}\in\Omega$（$dx=s^2\,dy$），可得精确递推关系：
   $$
   \begin{aligned}
   E\big(u_\alpha^{(m+1)}\big)
   &= \int_{G_{\mathrm{trans}}}\min_{1\le i\le 4}\|\nabla\Phi_\alpha(x)-A_i\|_F^2\,dx
      + \sum_{r=1}^M \int_{S_r}\min_{1\le i\le 4}\left\|(\nabla u_\alpha^{(m)})\!\left(\frac{x-x^{(r)}}{s}\right)-A_i\right\|_F^2 dx\\
   &= E_{\mathrm{trans}}(\alpha) + \left(\sum_{r=1}^M s^2\right)E\big(u_\alpha^{(m)}\big)
    = E_{\mathrm{trans}}(\alpha) + \rho\,E\big(u_\alpha^{(m)}\big).
   \end{aligned}
   $$
   初值 $E(u_\alpha^{(0)})=E(0)=\min\{9,5,5,9\}=5$。迭代求解上述线性递推式，并利用 $\rho=\frac{1}{6}(1-2\alpha)^4<\frac{1}{6}$ 与 $(8)$，对一切 $m\ge 0$ 有
   $$
   E\big(u_\alpha^{(m)}\big) = 5\rho^m + E_{\mathrm{trans}}(\alpha)\frac{1-\rho^m}{1-\rho} < 5\cdot 6^{-m} + 150\alpha\cdot\frac{1}{1-\frac{1}{6}} = 5\cdot 6^{-m} + 180\alpha. \tag{10}
   $$

4. **具体近最优序列与相分数核对**：
   对每个正整数 $j\ge 1$，取 $\alpha_j:=6^{-j}\in\left(0,\frac{1}{6}\right]$（此时阶段 1 周期数恰为 $N_1=6^j$）并令
   $$
   u_j := u_{\alpha_j}^{(j)} \in \mathcal{A}.
   $$
   则对一切 $j\ge 1$：
   - **零边界条件**：$u_j\in W^{1,\infty}(\Omega;\mathbb{R}^2)$ 且在 $\partial\Omega$ 上的迹为 $0$；
   - **统一梯度上界**：$\operatorname{ess\,sup}_\Omega \|\nabla u_j\|_F \le \sqrt{\frac{153}{16}} < \sqrt{10} < 4$；
   - **能量估计**：由 $(10)$ 得
     $$
     0 < E(u_j) < 5\cdot 6^{-j} + 180\cdot 6^{-j} = 185\cdot 6^{-j} \xrightarrow{j\to\infty} 0.
     $$
   此外，可直接从构造核对相体积分数：在 $u_j$ 中，梯度**精确等于** $A_i$ 的开子矩形总面积为
   $$
   \mu_i^{(j)} = |G_{A_i}(\alpha_j)|\cdot\frac{1-\rho_j^j}{1-\rho_j},
   $$
   其中 $c_j=1-2\cdot 6^{-j}\to 1$，$\rho_j=\frac{1}{6}c_j^4\to\frac{1}{6}$。于是当 $j\to\infty$ 时，
   $$
   \mu_1^{(j)}\to\frac{1/12}{5/6}=\frac{1}{10},\qquad
   \mu_2^{(j)},\,\mu_3^{(j)},\,\mu_4^{(j)}\to\frac{1/4}{5/6}=\frac{3}{10},
   $$
   剩余过渡区与末级零梯度区总面积小于 $6\alpha_j+6^{-j}=7\cdot 6^{-j}\to 0$，故 $\pi(u_j)\to\left(\frac{1}{10},\frac{3}{10},\frac{3}{10},\frac{3}{10}\right)$，与任务 2 的唯一性证明完全一致。$\square$