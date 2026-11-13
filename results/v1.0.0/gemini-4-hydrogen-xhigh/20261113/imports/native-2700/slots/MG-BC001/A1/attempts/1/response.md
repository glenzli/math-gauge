下面从题目给出的位移空间 $\mathcal{A}$、梯度与能量 $E(u)$ 定义出发，给出完整解答与证明，并先对题中“前期相容性结论”的适用性作严格辨析。

---

### 预备辨析：两两无秩一连接与四相 $T_4$ 构型

直接计算六个两井差的行列式（与题中一致）：
$$
\begin{aligned}
\det(A_1-A_2)&=\det\operatorname{diag}(2,-2)=-4, &
\det(A_1-A_3)&=\det\operatorname{diag}(5,-1)=-5,\\
\det(A_1-A_4)&=\det\operatorname{diag}(3,3)=9, &
\det(A_2-A_3)&=\det\operatorname{diag}(3,1)=3,\\
\det(A_2-A_4)&=\det\operatorname{diag}(1,5)=5, &
\det(A_3-A_4)&=\det\operatorname{diag}(-2,4)=-8.
\end{aligned}
$$
它们均非零，故任意两井 $A_i, A_j$ ($i\ne j$) 之间确无秩一连接。

然而，题中后续推论——“没有一对井能够开始相容层合，而位移又有统一 Lipschitz 上界，故零边界下不能形成能量趋零的混相序列，单元能保留严格正的间隙”——**不成立**。原因在于：二相（以及三星形无秩一连接）刚性结论不能逐相外推到四相系统。事实上，$K=\{A_1,A_2,A_3,A_4\}$ 构成经典的 **$T_4$ 构型**：引入四个中间对角矩阵
$$
P_4=\operatorname{diag}(0,0)=0,\quad
P_3=\operatorname{diag}(0,1),\quad
P_2=\operatorname{diag}(1,1),\quad
P_1=\operatorname{diag}(1,0),
$$
它们满足四步逐级秩一凸组合关系：
$$
\begin{aligned}
P_4 &= \frac{1}{4}A_4 + \frac{3}{4}P_3, & A_4 - P_3 &= \operatorname{diag}(0,-4) \quad(\text{秩 }1),\\
P_3 &= \frac{1}{3}A_3 + \frac{2}{3}P_2, & A_3 - P_2 &= \operatorname{diag}(-3,0) \quad(\text{秩 }1),\\
P_2 &= \frac{1}{2}A_2 + \frac{1}{2}P_1, & A_2 - P_1 &= \operatorname{diag}(0,2) \quad(\text{秩 }1),\\
P_1 &= \frac{1}{3}A_1 + \frac{2}{3}P_4, & A_1 - P_4 &= \operatorname{diag}(3,0) \quad(\text{秩 }1).
\end{aligned}
$$
而且 $\|A_1\|_F=\|A_4\|_F=3$，$\|A_2\|_F=\|A_3\|_F=\sqrt{5}$，$\|P_1\|_F=\|P_3\|_F=1$，$\|P_2\|_F=\sqrt{2}$，$\|P_4\|_F=0$，均严格小于梯度上界 $4$。因此即使两两无秩一连接，仍可从零边界条件 $u=0$（即初始梯度 $P_4=0$）出发通过循环嵌套的有限阶层合与矩形截断构造能量趋于 $0$ 且满足 $\|\nabla u\|_F \le 4$ 的容许序列。

---

### 1. $e_0$ 的精确值及是否可达到

**结论：**
$$e_0 = 0,$$
且**不存在**任何 $u\in\mathcal{A}$ 达到最小值 $e_0=0$。

**证明：**

1. **证明 $e_0 = 0$：**
   对任意 $u\in\mathcal{A}$，被积函数 $\min_{1\le i\le 4}\|\nabla u(x)-A_i\|_F^2\ge 0$ a.e. 于 $\Omega$，故 $E(u)\ge 0$，从而 $e_0 \ge 0$。另一方面，第 3 节将显式构造一列容许位移 $\{u_j\}_{j\ge 1}\subset\mathcal{A}$，满足 $E(u_j)\to 0$（$j\to\infty$）。因此
   $$0 \le e_0 = \inf_{u\in\mathcal{A}} E(u) \le \lim_{j\to\infty} E(u_j) = 0 \implies e_0 = 0.$$

2. **证明不存在 $u\in\mathcal{A}$ 使 $E(u)=0$：**
   反设存在 $u=(u_1,u_2)\in\mathcal{A}$ 使得 $E(u)=0$。则
   $$\min_{1\le i\le 4}\|\nabla u(x)-A_i\|_F^2 = 0 \quad \text{a.e. } x\in\Omega,$$
   即 $\nabla u(x)\in K$ a.e. 于 $\Omega$。由于 $A_1,A_2,A_3,A_4$ 全为对角矩阵，必有非对角元几乎处处为零：
   $$\partial_2 u_1 = 0,\qquad \partial_1 u_2 = 0 \qquad \text{a.e. 于 } \Omega=(0,1)^2.$$
   又因 $u\in W^{1,\infty}(\Omega;\mathbb{R}^2)\subset W^{1,2}(\Omega;\mathbb{R}^2)$ 且在 Lipschitz 边界 $\partial\Omega$ 上的迹为 $0$，故 $u\in W_0^{1,2}(\Omega;\mathbb{R}^2)$。取序列 $\psi^{(n)}=(\psi_1^{(n)},\psi_2^{(n)})\in C_c^\infty(\Omega;\mathbb{R}^2)$ 使 $\psi^{(n)}\to u$ 于 $W^{1,2}(\Omega;\mathbb{R}^2)$。对每个 $n$ 及 $(x,y)\in(0,1)^2$，由牛顿–莱布尼茨公式和 Cauchy–Schwarz 不等式有
   $$|\psi_1^{(n)}(x,y)|^2 = \left|\int_0^y \partial_2 \psi_1^{(n)}(x,t)\,dt\right|^2 \le \int_0^1 |\partial_2 \psi_1^{(n)}(x,t)|^2\,dt,$$
   在 $(0,1)^2$ 上积分得 $\|\psi_1^{(n)}\|_{L^2(\Omega)} \le \|\partial_2 \psi_1^{(n)}\|_{L^2(\Omega)}$。令 $n\to\infty$ 得
   $$\|u_1\|_{L^2(\Omega)} \le \|\partial_2 u_1\|_{L^2(\Omega)} = 0 \implies u_1 = 0 \quad \text{a.e. 于 }\Omega.$$
   同理，由 $\|\psi_2^{(n)}\|_{L^2(\Omega)} \le \|\partial_1 \psi_2^{(n)}\|_{L^2(\Omega)}$ 令 $n\to\infty$ 得 $u_2 = 0$ a.e. 于 $\Omega$。

   于是 $u=0$ a.e. 于 $\Omega$，从而其弱梯度 $\nabla u = 0$ a.e. 于 $\Omega$。但 $\|0-A_1\|_F^2=9$，$\|0-A_2\|_F^2=5$，$\|0-A_3\|_F^2=5$，$\|0-A_4\|_F^2=9$，故
   $$E(u) = E(0) = \int_\Omega \min_{1\le i\le 4}\|A_i\|_F^2\,dx = 5 > 0,$$
   与 $E(u)=0$ 矛盾。因此没有任何 $u\in\mathcal{A}$ 达到 $e_0=0$。$\square$

---

### 2. 相体积分数 $\pi(u_j)$ 的收敛性及全部可能极限

**结论：**
对任意满足 $E(u_j)\to e_0=0$ 的序列 $\{u_j\}\subset\mathcal{A}$，相体积分数向量 $(\pi_1(u_j),\pi_2(u_j),\pi_3(u_j),\pi_4(u_j))$ **必然收敛到同一个向量**，全部可能的极限构成的集合为单点集：
$$\left\{\left(\frac{1}{10},\,\frac{3}{10},\,\frac{3}{10},\,\frac{3}{10}\right)\right\}.$$

**证明：**

先说明可测性与误差分解。在 $\mathbb{R}^{2\times 2}$ 上按题目分配规则定义 Voronoi 划分：
$$V_i := \Big\{ M\in\mathbb{R}^{2\times 2} : \|M-A_i\|_F < \|M-A_k\|_F\ (\forall k<i),\ \|M-A_i\|_F \le \|M-A_k\|_F\ (\forall k>i) \Big\},$$
$i=1,2,3,4$。每个 $V_i$ 是有限个开半空间与闭半空间的交，为 Borel 集，且 $\{V_1,V_2,V_3,V_4\}$ 构成 $\mathbb{R}^{2\times 2}$ 的两两不交划分。令 $S_{i,j}:=(\nabla u_j)^{-1}(V_i)\subset\Omega$，则 $S_{i,j}$ Lebesgue 可测，且
$$\sum_{i=1}^4 \mathbf{1}_{S_{i,j}}(x) = 1 \quad \text{a.e. }x\in\Omega,\qquad \pi_i(u_j) = |S_{i,j}| = \int_\Omega \mathbf{1}_{S_{i,j}}(x)\,dx.$$
记
$$M_j(x) := \sum_{i=1}^4 \mathbf{1}_{S_{i,j}}(x) A_i,\qquad R_j(x) := \nabla u_j(x) - M_j(x).$$
由分配规则，即使发生等距情形，所有最小距离仍相等，故几乎处处有
$$\|R_j(x)\|_F^2 = \min_{1\le i\le 4}\|\nabla u_j(x)-A_i\|_F^2,\qquad \text{从而 }\ \|R_j\|_{L^2(\Omega)} = \sqrt{E(u_j)} \to 0.$$
同时，由于 $\{S_{1,j},\dots,S_{4,j}\}$ 划分 $\Omega$，几乎处处有 $\det(M_j(x)) = \sum_{i=1}^4 \mathbf{1}_{S_{i,j}}(x)\det(A_i)$。利用矩阵行列式的双线性差恒等式：对任意 $2\times 2$ 矩阵 $A,B$，
$$\det(A)-\det(B) = (A_{11}-B_{11})A_{22}+B_{11}(A_{22}-B_{22})-(A_{12}-B_{12})A_{21}-B_{12}(A_{21}-B_{21}),$$
由 Cauchy–Schwarz 不等式得 $|\det(A)-\det(B)| \le (\|A\|_F+\|B\|_F)\|A-B\|_F$。因 $\|\nabla u_j(x)\|_F\le 4$ 且 $\|M_j(x)\|_F\le \max_i\|A_i\|_F=3$ a.e.，于是在 $\Omega=(0,1)^2$（面积为 $1$）上有
$$\left\|\det(\nabla u_j) - \sum_{i=1}^4 \mathbf{1}_{S_{i,j}}\det(A_i)\right\|_{L^1(\Omega)} \le 7\int_\Omega \|R_j(x)\|_F\,dx \le 7\|R_j\|_{L^2(\Omega)} = 7\sqrt{E(u_j)} \to 0. \tag{1}$$

现在任取 $\{u_j\}$ 的一个子列（仍记为 $\{u_j\}$）。由 $\|\nabla u_j\|_{L^\infty(\Omega)}\le 4$ 与第 1 节已证的 Poincaré 不等式 $\|u_j\|_{L^2(\Omega)} \le \|\nabla u_j\|_{L^2(\Omega)} \le 4$，序列 $\{u_j\}$ 在 $W_0^{1,2}(\Omega;\mathbb{R}^2)$ 中有界；又 $\|\mathbf{1}_{S_{i,j}}\|_{L^2(\Omega)}\le 1$。由 Rellich–Kondrachov 紧嵌入定理及 $L^2(\Omega)$ 有界集的弱列紧性，可进一步抽取子列（仍记为 $\{u_j\}$），使得存在 $u\in W_0^{1,2}(\Omega;\mathbb{R}^2)$ 及 $\theta_1,\theta_2,\theta_3,\theta_4\in L^2(\Omega)$，满足
$$u_j \to u \ \text{强收敛于 } L^2(\Omega;\mathbb{R}^2),\qquad \nabla u_j \rightharpoonup \nabla u \ \text{弱收敛于 } L^2(\Omega;\mathbb{R}^{2\times 2}),$$
$$\mathbf{1}_{S_{i,j}} \rightharpoonup \theta_i \ \text{弱收敛于 } L^2(\Omega)\quad (i=1,2,3,4).$$
由此立得以下四条性质：

1. **概率权重与极限体积分数：** 对任意非负 $\phi\in L^2(\Omega)$，由 $0\le \mathbf{1}_{S_{i,j}}\le 1$ 及 $\sum_{i=1}^4 \mathbf{1}_{S_{i,j}}=1$ a.e. 传到弱极限，得
   $$0\le \theta_i(x)\le 1 \ \text{a.e.},\qquad \sum_{i=1}^4 \theta_i(x) = 1 \ \text{a.e. 于 }\Omega.$$
   再取检验函数 $1\in L^2(\Omega)$，即得沿该子列
   $$\pi_i(u_j) = \int_\Omega \mathbf{1}_{S_{i,j}}(x)\,dx \to \int_\Omega \theta_i(x)\,dx\qquad (i=1,2,3,4). \tag{2}$$

2. **极限位移与线性矩约束：** 因 $R_j = \nabla u_j - \sum_{i=1}^4 \mathbf{1}_{S_{i,j}}A_i \to 0$ 强收敛于 $L^2(\Omega;\mathbb{R}^{2\times 2})$，而 $\nabla u_j \rightharpoonup \nabla u$ 且 $\sum_{i=1}^4 \mathbf{1}_{S_{i,j}}A_i \rightharpoonup \sum_{i=1}^4 \theta_i A_i$ 弱收敛于 $L^2$，由弱极限唯一性得
   $$\nabla u(x) = \sum_{i=1}^4 \theta_i(x) A_i \qquad \text{a.e. 于 }\Omega.$$
   由于每个 $A_i$ 都是对角矩阵，所以 $\partial_2 u_1=0$ 且 $\partial_1 u_2=0$ a.e. 于 $\Omega$。由 $u\in W_0^{1,2}(\Omega;\mathbb{R}^2)$ 及第 1 节相同论证，必有 $u = 0$ a.e. 于 $\Omega$，从而 $\nabla u = 0$ a.e. 于 $\Omega$。即几乎处处成立
   $$\sum_{i=1}^4 \theta_i(x) A_i = 0 \qquad \text{a.e. 于 }\Omega. \tag{3}$$

3. **行列式的弱连续性与二次零拉格朗日约束：** 任取 $\varphi\in C_c^\infty(\Omega)$。对每个 $j$，在包含 $\operatorname{supp}\varphi$ 且紧支于 $\Omega$ 内的开集 $\Omega'$ 上用标准磨光核作 $v^{(\varepsilon)}:=u_j*\rho_\varepsilon\in C^\infty(\Omega';\mathbb{R}^2)$（$0<\varepsilon<\frac{1}{2}\operatorname{dist}(\operatorname{supp}\varphi,\partial\Omega)$）。由散度结构分部积分（光滑函数二阶混合偏导交换 $\partial_1\partial_2 v_2^{(\varepsilon)}=\partial_2\partial_1 v_2^{(\varepsilon)}$）得
   $$\int_\Omega \varphi\det(\nabla v^{(\varepsilon)})\,dx = -\int_\Omega v_1^{(\varepsilon)}\big(\partial_1(\varphi\,\partial_2 v_2^{(\varepsilon)}) - \partial_2(\varphi\,\partial_1 v_2^{(\varepsilon)})\big)\,dx = \int_\Omega v_1^{(\varepsilon)}\big(\partial_2\varphi\,\partial_1 v_2^{(\varepsilon)} - \partial_1\varphi\,\partial_2 v_2^{(\varepsilon)}\big)\,dx.$$
   令 $\varepsilon\to 0^+$，因 $v^{(\varepsilon)}\to u_j$ 于 $W^{1,2}(\Omega';\mathbb{R}^2)$，上式两端乘积项均在 $L^1(\Omega')$ 中收敛，故
   $$\int_\Omega \varphi\det(\nabla u_j)\,dx = \int_\Omega u_{j,1}\big(\partial_2\varphi\,\partial_1 u_{j,2} - \partial_1\varphi\,\partial_2 u_{j,2}\big)\,dx.$$
   由于 $\|\partial_1 u_{j,2}\|_{L^\infty},\|\partial_2 u_{j,2}\|_{L^\infty}\le 4$，利用 Cauchy–Schwarz 不等式并注意到 $\|u_{j,1}\|_{L^2(\Omega)}\to \|u_1\|_{L^2(\Omega)}=0$，有
   $$\left|\int_\Omega \varphi\det(\nabla u_j)\,dx\right| \le \|u_{j,1}\|_{L^2(\Omega)} \cdot 8\|\nabla\varphi\|_{L^\infty(\Omega)} \to 0 \qquad (j\to\infty).$$
   结合 (1) 式及 $\mathbf{1}_{S_{i,j}}\rightharpoonup \theta_i$（用 $\varphi\in L^2(\Omega)$ 检验），即得
   $$\int_\Omega \varphi(x)\sum_{i=1}^4 \theta_i(x)\det(A_i)\,dx = \lim_{j\to\infty}\int_\Omega \varphi(x)\sum_{i=1}^4 \mathbf{1}_{S_{i,j}}(x)\det(A_i)\,dx = \lim_{j\to\infty}\int_\Omega \varphi(x)\det(\nabla u_j(x))\,dx = 0.$$
   由 $\varphi\in C_c^\infty(\Omega)$ 的任意性及 $C_c^\infty(\Omega)$ 在 $L^2(\Omega)$ 中的稠密性，得
   $$\sum_{i=1}^4 \theta_i(x)\det(A_i) = 0 \qquad \text{a.e. 于 }\Omega. \tag{4}$$

4. **唯一解与整列收敛：** 注意到 $\det(A_1)=0$、$\det(A_2)=2$、$\det(A_3)=-2$、$\det(A_4)=0$。联立方程 $\sum_{i=1}^4 \theta_i=1$、(3) 式的两个对角分量及 (4) 式，对 a.e. $x\in\Omega$ 有线性方程组：
   $$
   \begin{cases}
   \theta_1(x)+\theta_2(x)+\theta_3(x)+\theta_4(x)=1,\\
   3\theta_1(x)+\theta_2(x)-2\theta_3(x)=0,\\
   2\theta_2(x)+\theta_3(x)-3\theta_4(x)=0,\\
   2\theta_2(x)-2\theta_3(x)=0.
   \end{cases}
   $$
   由第四式得 $\theta_2(x)=\theta_3(x)=:t$；代入第二式得 $3\theta_1(x)-t=0$ 即 $\theta_1(x)=\frac{t}{3}$；代入第三式得 $3t-3\theta_4(x)=0$ 即 $\theta_4(x)=t$；代入第一式得 $\frac{10}{3}t=1$，唯一解出 $t=\frac{3}{10}$，即
   $$(\theta_1(x),\theta_2(x),\theta_3(x),\theta_4(x)) = \left(\frac{1}{10},\frac{3}{10},\frac{3}{10},\frac{3}{10}\right) \qquad \text{a.e. 于 }\Omega.$$
   由 (2) 式知沿该子列 $\pi(u_j)\to (\frac{1}{10},\frac{3}{10},\frac{3}{10},\frac{3}{10})$。

由于 $\{\pi(u_j)\}$ 的任意子列都存在进一步的子列收敛到同一个常向量 $(\frac{1}{10},\frac{3}{10},\frac{3}{10},\frac{3}{10})$，整个序列必然收敛到 $(\frac{1}{10},\frac{3}{10},\frac{3}{10},\frac{3}{10})$。又第 3 节的构造给出了满足 $E(u_j)\to 0$ 的真实序列 $\{u_j\}\subset\mathcal{A}$，从而该极限确可实现，全部可能极限构成的集合就是 $\{(\frac{1}{10},\frac{3}{10},\frac{3}{10},\frac{3}{10})\}$。$\square$

---

### 3. 具体近最优位移构造与逐项验证

下面构造具体的函数列 $\{u_j\}_{j\ge 1}\subset\mathcal{A}$，并逐项验证零边界迹、一致梯度上界 $\|\nabla u_j\|_F\le 4$、能量 $E(u_j)\to 0$（以及相体积分数趋于 $(\frac{1}{10},\frac{3}{10},\frac{3}{10},\frac{3}{10})$）。

#### 3.1 矩形单步层合截断引理

设 $R=(x_a,x_b)\times(y_a,y_b)\subset\Omega$ 是宽 $W=x_b-x_a>0$、高 $H=y_b-y_a>0$ 的开矩形。设 $v=(v_1,v_2)\in W^{1,\infty}(\Omega;\mathbb{R}^2)$ 在 $\overline{R}$ 上为仿射映射
$$v(x,y) = (m_1 x + c_1,\, m_2 y + c_2),\qquad \nabla v|_R = M := \operatorname{diag}(m_1,m_2).$$
取截断比例参数 $\delta\in(0,1/4)$ 与正整数频数 $k\ge 1$。定义标准一维梯形截断函数 $\eta_{[a,b],\delta}:[a,b]\to[0,1]$：
$$\eta_{[a,b],\delta}(t) :=
\begin{cases}
\dfrac{t-a}{\delta(b-a)}, & a \le t \le a+\delta(b-a),\\[6pt]
1, & a+\delta(b-a) \le t \le b-\delta(b-a),\\[6pt]
\dfrac{b-t}{\delta(b-a)}, & b-\delta(b-a) \le t \le b,
\end{cases}$$
以及一维 $k$-周期锯齿函数 $s_{[a,b],k,\lambda,d_1,d_2}:[a,b]\to\mathbb{R}$（其中 $\lambda\in(0,1)$ 且 $\lambda d_1 + (1-\lambda)d_2 = 0$）：令 $h=\frac{b-a}{k}$，对每个 $p\in\{0,1,\dots,k-1\}$ 和 $t\in[a+ph,\, a+(p+1)h]$，记 $\tau = t - (a+ph)\in[0,h]$，定义
$$s_{[a,b],k,\lambda,d_1,d_2}(t) :=
\begin{cases}
d_1 \tau, & 0 \le \tau \le \lambda h,\\
d_1\lambda h + d_2(\tau - \lambda h), & \lambda h \le \tau \le h.
\end{cases}$$
由于 $\lambda d_1 + (1-\lambda)d_2 = 0$，$s$ 在每个周期端点 $a+ph$ ($p=0,\dots,k$) 处均连续且取值为 $0$（特别地 $s(a)=s(b)=0$），且在 $[a,b]$ 上满足
$$\max_{t\in[a,b]}|s(t)| = \lambda |d_1| h = \lambda |d_1|\frac{b-a}{k}.$$

按分裂方向分两种情形定义在 $\Omega$ 上的新映射 $\tilde{v}$：

- **情形 V（沿 $y$ 方向分裂 $m_2=\lambda\alpha+(1-\lambda)\beta$）：**
  在 $\Omega\setminus R$ 上令 $\tilde{v}=v$；在 $\overline{R}$ 上令 $\eta=\eta_{[x_a,x_b],\delta}$、$s=s_{[y_a,y_b],k,\lambda,\alpha-m_2,\beta-m_2}$，定义
  $$\tilde{v}_1(x,y) = m_1 x + c_1,\qquad \tilde{v}_2(x,y) = m_2 y + c_2 + \eta(x)s(y).$$
- **情形 H（沿 $x$ 方向分裂 $m_1=\lambda\alpha+(1-\lambda)\beta$）：**
  在 $\Omega\setminus R$ 上令 $\tilde{v}=v$；在 $\overline{R}$ 上令 $\eta=\eta_{[y_a,y_b],\delta}$、$s=s_{[x_a,x_b],k,\lambda,\alpha-m_1,\beta-m_1}$，定义
  $$\tilde{v}_1(x,y) = m_1 x + c_1 + s(x)\eta(y),\qquad \tilde{v}_2(x,y) = m_2 y + c_2.$$

**引理性质验证（以情形 V 为例，情形 H 完全对称）：**
1. **保持边界与 Lipschitz 连续性：** 在 $\partial R$ 上，若 $x\in\{x_a,x_b\}$ 则 $\eta(x)=0$，若 $y\in\{y_a,y_b\}$ 则 $s(y)=0$，故 $\tilde{v}|_{\partial R}=v|_{\partial R}$。又 $\eta$、$s$ 均为 Lipschitz 函数，其乘积 $\eta(x)s(y)$ 在 $\overline{R}$ 上 Lipschitz 连续，从而 $\tilde{v}$ 在 $\overline{\Omega}$ 上连续且在将 $R$ 划为 $3\times (2k)$ 个小开矩形后在每个小开矩形上均光滑（次数 $\le 2$ 的多项式）。由分部积分跨边连续抵消知 $\tilde{v}\in W^{1,\infty}(\Omega;\mathbb{R}^2)$，且弱梯度 $\nabla\tilde{v}$ 几乎处处等于各小开矩形上的经典梯度。
2. **内部精确子矩形分解：** 记内部开矩形 $R_{\mathrm{int}} := (x_a+\delta W,\,x_b-\delta W)\times(y_a,y_b)$，面积为 $(1-2\delta)|R|$。在其上 $\eta\equiv 1,\ \eta'\equiv 0$，故对每个周期 $p=0,\dots,k-1$：
   - 在开矩形 $(x_a+\delta W,\,x_b-\delta W)\times(y_a+ph,\, y_a+(p+\lambda)h)$ 上，$\tilde{v}$ 是**精确仿射映射**，梯度恒为 $M_1:=\operatorname{diag}(m_1,\alpha)$，这 $k$ 个不交矩形总面积为 $\lambda(1-2\delta)|R|$；
   - 在开矩形 $(x_a+\delta W,\,x_b-\delta W)\times(y_a+(p+\lambda)h,\, y_a+(p+1)h)$ 上，$\tilde{v}$ 是**精确仿射映射**，梯度恒为 $M_2:=\operatorname{diag}(m_1,\beta)$，这 $k$ 个不交矩形总面积为 $(1-\lambda)(1-2\delta)|R|$，且每个宽为 $(1-2\delta)W$、高为 $(1-\lambda)\frac{H}{k}$。
   （情形 H 中，$R_{\mathrm{int}}=(x_a,x_b)\times(y_a+\delta H,\,y_b-\delta H)$，$M_1=\operatorname{diag}(\alpha,m_2)$ 占面积 $\lambda(1-2\delta)|R|$，$M_2=\operatorname{diag}(\beta,m_2)$ 占面积 $(1-\lambda)(1-2\delta)|R|$，后者每个宽为 $(1-\lambda)\frac{W}{k}$、高为 $(1-2\delta)H$。）
3. **截断带上的梯度范数上界：** 在两条边截断带 $R_{\mathrm{cut}}:=\big((x_a,x_a+\delta W)\cup(x_b-\delta W,x_b)\big)\times(y_a,y_b)$（总面积 $2\delta|R|$）上，除有限条线段外有
   $$\nabla \tilde{v}(x,y) = \begin{pmatrix} m_1 & 0 \\ \eta'(x)s(y) & m_2+\eta(x)s'(y) \end{pmatrix}.$$
   由于 $\eta(x)\in[0,1]$ 且 $m_2+s'(y)\in\{\alpha,\beta\}$，对角元 $m_2+\eta(x)s'(y)$ 介于 $m_2$ 与 $\alpha$ 或 $\beta$ 之间，故 $|m_2+\eta(x)s'(y)|\le \max(|m_2|,|\alpha|,|\beta|)$。又 $|\eta'(x)|=\frac{1}{\delta W}$，故
   $$|\eta'(x)s(y)| \le \frac{1}{\delta W}\cdot \lambda|\alpha-m_2|\frac{H}{k}.$$
   因此若取正整数 $k \ge \frac{H}{\delta W}$（情形 H 取 $k \ge \frac{W}{\delta H}$），则 $|\eta'(x)s(y)|\le \lambda|\alpha-m_2|$，从而在 $R_{\mathrm{cut}}$ 上 a.e. 成立
   $$\|\nabla\tilde{v}(x,y)\|_F^2 \le \max\big(\|M\|_F^2,\,\|M_1\|_F^2,\,\|M_2\|_F^2\big) + \lambda^2(\alpha-m_2)^2. \tag{5}$$
   （情形 H 完全同理，将上式末项换为 $\lambda^2(\alpha-m_1)^2$。）

#### 3.2 递归构造序列 $\{u_j\}_{j\ge 1}$

固定轮数 $M\in\mathbb{N}_+$ 与截断参数 $\delta\in(0,1/4)$。从 $u^{(0)}\equiv 0$（即初始唯一活跃矩形集合 $\mathcal{R}_0=\{\Omega\}$，其上 $\nabla u^{(0)}=P_4=0$，尺寸 $W_0=1, H_0=1$）出发，依次做 $4M$ 步递归替换。对第 $m=1,2,\dots,4M$ 步，设 $\mathcal{R}_{m-1}$ 为当前所有两两不交的活跃开矩形之集，每个 $R\in\mathcal{R}_{m-1}$ 具有相同尺寸 $W_{m-1}\times H_{m-1}$，且 $u^{(m-1)}$ 在每个 $\overline{R}$ 上均为仿射映射，梯度为同一个节点矩阵 $P^{(m-1)}$。按 $m\bmod 4$ 的余数同时对每个 $R\in\mathcal{R}_{m-1}$ 独立施行如下单步替换（生成 $u^{(m)}$，并把新生成的非井分支矩形记为 $\mathcal{R}_m$）：

- **$m\equiv 1\pmod 4$（情形 V，分裂 $P_4 = \frac{1}{4}A_4 + \frac{3}{4}P_3$）：**
  $\lambda=\frac{1}{4},\alpha=-3,\beta=1,m_1=m_2=0$。取 $k_m=\lceil \frac{H_{m-1}}{\delta W_{m-1}}\rceil$。生成冻结的 $A_4$-矩形与活跃的 $P_3$-矩形 $\mathcal{R}_m$，尺寸 $W_m=(1-2\delta)W_{m-1},\ H_m=\frac{3H_{m-1}}{4k_m}$。
- **$m\equiv 2\pmod 4$（情形 H，分裂 $P_3 = \frac{1}{3}A_3 + \frac{2}{3}P_2$）：**
  $\lambda=\frac{1}{3},\alpha=-2,\beta=1,m_1=0,m_2=1$。取 $k_m=\lceil \frac{W_{m-1}}{\delta H_{m-1}}\rceil$。生成冻结的 $A_3$-矩形与活跃的 $P_2$-矩形 $\mathcal{R}_m$，尺寸 $W_m=\frac{2W_{m-1}}{3k_m},\ H_m=(1-2\delta)H_{m-1}$。
- **$m\equiv 3\pmod 4$（情形 V，分裂 $P_2 = \frac{1}{2}A_2 + \frac{1}{2}P_1$）：**
  $\lambda=\frac{1}{2},\alpha=2,\beta=0,m_1=m_2=1$。取 $k_m=\lceil \frac{H_{m-1}}{\delta W_{m-1}}\rceil$。生成冻结的 $A_2$-矩形与活跃的 $P_1$-矩形 $\mathcal{R}_m$，尺寸 $W_m=(1-2\delta)W_{m-1},\ H_m=\frac{H_{m-1}}{2k_m}$。
- **$m\equiv 4\pmod 4$（情形 H，分裂 $P_1 = \frac{1}{3}A_1 + \frac{2}{3}P_4$）：**
  $\lambda=\frac{1}{3},\alpha=3,\beta=0,m_1=1,m_2=0$。取 $k_m=\lceil \frac{W_{m-1}}{\delta H_{m-1}}\rceil$。生成冻结的 $A_1$-矩形与活跃的 $P_4$-矩形 $\mathcal{R}_m$，尺寸 $W_m=\frac{2W_{m-1}}{3k_m},\ H_m=(1-2\delta)H_{m-1}$。

记最终映射为 $u^{(M,\delta)} := u^{(4M)}$。对每个 $j=1,2,\dots$，令
$$M_j := j,\qquad \delta_j := \frac{1}{5j} \in \left(0,\frac{1}{4}\right),\qquad u_j := u^{(M_j,\delta_j)}.$$

#### 3.3 容许性、能量估计与相分数验证

1. **验证 $u_j\in W^{1,\infty}(\Omega;\mathbb{R}^2)$ 且在 $\partial\Omega$ 上迹为 $0$：**
   在第 1 步，在 $\partial\Omega$ 上均有 $u^{(1)}=u^{(0)}=0$。其后各步 $m\ge 2$ 仅在若干严格含于 $\Omega$ 内的活跃矩形内部修改，且在每个 $R\in\mathcal{R}_{m-1}$ 的边界 $\partial R$ 上保持 $u^{(m)}=u^{(m-1)}$。因为共有有限步（$4j$ 步），由单步引理归纳即得 $u_j$ 在 $\overline{\Omega}$ 上 Lipschitz 连续（从而 $u_j\in W^{1,\infty}(\Omega;\mathbb{R}^2)$）且 $u_j|_{\partial\Omega}\equiv 0$，因此 $u_j$ 在 $\partial\Omega$ 上的迹为 $0$。

2. **验证一致梯度上界 $\operatorname{ess\,sup}_\Omega \|\nabla u_j\|_F \le 4$：**
   在任何已被冻结的 $A_i$-矩形上，$\nabla u_j \equiv A_i$，故 $\|\nabla u_j\|_F \le 3$；在最终剩余的 $P_4$-矩形上，$\nabla u_j \equiv 0$，故 $\|\nabla u_j\|_F = 0$；在任一步 $m$ 产生的截断带 $R_{\mathrm{cut}}$ 上，一旦生成便不再被后续步骤修改，由 (5) 式逐一检验四种余数：
   - $m\equiv 1\pmod 4$：$\max(\|P_4\|_F^2,\|A_4\|_F^2,\|P_3\|_F^2)+\big(\frac{1}{4}\cdot 3\big)^2 = 9+\frac{9}{16}=\frac{153}{16}$；
   - $m\equiv 2\pmod 4$：$\max(\|P_3\|_F^2,\|A_3\|_F^2,\|P_2\|_F^2)+\big(\frac{1}{3}\cdot 2\big)^2 = 5+\frac{4}{9}=\frac{49}{9}$；
   - $m\equiv 3\pmod 4$：$\max(\|P_2\|_F^2,\|A_2\|_F^2,\|P_1\|_F^2)+\big(\frac{1}{2}\cdot 1\big)^2 = 5+\frac{1}{4}=\frac{21}{4}$；
   - $m\equiv 4\pmod 4$：$\max(\|P_1\|_F^2,\|A_1\|_F^2,\|P_4\|_F^2)+\big(\frac{1}{3}\cdot 2\big)^2 = 9+\frac{4}{9}=\frac{85}{9}$。

   四者均不超过 $\frac{153}{16}$。因此几乎处处在 $\Omega$ 上有
   $$\|\nabla u_j(x)\|_F \le \frac{\sqrt{153}}{4} < 4 \qquad (\text{因 } 153 < 256).$$
   故 $\operatorname{ess\,sup}_\Omega \|\nabla u_j\|_F \le 4$，从而确有 $u_j\in\mathcal{A}$。

3. **验证能量估计 $E(u_j)\to 0$：**
   设 $\gamma:=1-2\delta\in(\frac{1}{2},1)$，$r:=\frac{\gamma^4}{6}\in(0,\frac{1}{6})$。在任意一轮（4 步）开始时，若该轮初始 $P_4$-矩形总面积为 $A$，则本轮结束时：
   - 冻结的 $A_4, A_3, A_2, A_1$ 矩形总面积依次为 $\frac{1}{4}\gamma A$、$\frac{1}{4}\gamma^2 A$、$\frac{1}{4}\gamma^3 A$、$\frac{1}{12}\gamma^4 A$；
   - 本轮四个步骤的截断带总面积为
     $$2\delta\left(1 + \frac{3}{4}\gamma + \frac{1}{2}\gamma^2 + \frac{1}{4}\gamma^3\right)A \le 2\delta\cdot\frac{5}{2}A = 5\delta A;$$
   - 留到下一轮的 $P_4$-矩形总面积为 $\frac{3}{4}\gamma\cdot\frac{2}{3}\gamma\cdot\frac{1}{2}\gamma\cdot\frac{2}{3}\gamma A = \frac{\gamma^4}{6}A = r A$。

   于是经历 $M$ 轮后（初始面积 $A=1$）：
   - 所有冻结的 $A_i$-矩形上，$\nabla u^{(M,\delta)}=A_i$，对能量 $E(u^{(M,\delta)})$ 的贡献为 $0$；
   - 剩余的 $P_4$-矩形总面积为 $r^M \le 6^{-M}$，其上 $\nabla u^{(M,\delta)}=0$，能量密度为 $\min_i\|A_i\|_F^2=5$；
   - 所有 $4M$ 步截断带之并 $U_{\mathrm{cut}}$ 的总面积为
     $$|U_{\mathrm{cut}}| \le \sum_{c=0}^{M-1} 5\delta r^c \le \frac{5\delta}{1-1/6} = 6\delta,$$
     而在 $U_{\mathrm{cut}}$ 上有 $\|\nabla u^{(M,\delta)}\|_F^2 \le \frac{153}{16}$，故利用 $\|A_2\|_F^2=5$ 得能量密度上界
     $$\min_{1\le i\le 4}\|\nabla u^{(M,\delta)}(x)-A_i\|_F^2 \le \|\nabla u^{(M,\delta)}(x)-A_2\|_F^2 \le 2\big(\|\nabla u^{(M,\delta)}(x)\|_F^2+\|A_2\|_F^2\big) \le 2\left(\frac{153}{16}+5\right)=\frac{233}{8}<30.$$

   综合以上三部分区域，对任意 $M\ge 1$ 和 $\delta\in(0,1/4)$ 均有
   $$E(u^{(M,\delta)}) \le 5\cdot 6^{-M} + 30\cdot 6\delta = 5\cdot 6^{-M} + 180\delta.$$
   代入 $M=j,\ \delta=\delta_j=\frac{1}{5j}$，即得
   $$E(u_j) \le 5\cdot 6^{-j} + \frac{36}{j} \to 0 \qquad (j\to\infty).$$

4. **与第 2 节相体积分数的一致性检验：**
   记 $F_i^{(j)}$ 为 $u_j$ 中被冻结在井 $A_i$ 上的矩形区域之并（其上 $\nabla u_j\equiv A_i$，故必全部分配给 $A_i$）。由上面积计算（取 $\gamma_j=1-\frac{2}{5j},\ r_j=\frac{\gamma_j^4}{6}$）：
   $$
   \begin{aligned}
   |F_1^{(j)}| &= \frac{\gamma_j^4}{12}\cdot\frac{1-r_j^j}{1-r_j} \to \frac{1/12}{1-1/6} = \frac{1}{10},\\
   |F_2^{(j)}| &= \frac{\gamma_j^3}{4}\cdot\frac{1-r_j^j}{1-r_j} \to \frac{1/4}{1-1/6} = \frac{3}{10},\\
   |F_3^{(j)}| &= \frac{\gamma_j^2}{4}\cdot\frac{1-r_j^j}{1-r_j} \to \frac{1/4}{1-1/6} = \frac{3}{10},\\
   |F_4^{(j)}| &= \frac{\gamma_j}{4}\cdot\frac{1-r_j^j}{1-r_j} \to \frac{1/4}{1-1/6} = \frac{3}{10},
   \end{aligned}
   $$
   其余区域总面积 $|U_{\mathrm{cut}}|+r_j^j \le 6\delta_j + 6^{-j} \to 0$，故
   $$\lim_{j\to\infty} \big(\pi_1(u_j),\pi_2(u_j),\pi_3(u_j),\pi_4(u_j)\big) = \left(\frac{1}{10},\,\frac{3}{10},\,\frac{3}{10},\,\frac{3}{10}\right),$$
   与第 1、2 节的证明结论完全相符。$\square$
