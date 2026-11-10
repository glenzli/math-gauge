以下给出该四相材料零边界单元问题的完整解答与严格证明。

---

### 前期相容性结论的辨析（二相刚性 vs. 四相 Tartar 方块）

题目给出的两井差行列式计算完全正确：
$$
\begin{aligned}
\det(A_1-A_2)&=\det\operatorname{diag}(2,-2)=-4,&
\det(A_1-A_3)&=\det\operatorname{diag}(5,-1)=-5,&
\det(A_1-A_4)&=\det\operatorname{diag}(3,3)=9,\\
\det(A_2-A_3)&=\det\operatorname{diag}(3,1)=3,&
\det(A_2-A_4)&=\det\operatorname{diag}(1,5)=5,&
\det(A_3-A_4)&=\det\operatorname{diag}(-2,4)=-8.
\end{aligned}
$$
因此 $K=\{A_1,A_2,A_3,A_4\}$ 中确实没有任何一对井具有秩一连接（$\operatorname{rank}(A_i-A_j)=2,\ \forall i\ne j$）。

然而，**把二相刚性估计逐相外推到四相系统并断言 $e_0>0$ 是不成立的**：
- 对**精确解**（$E(u)=0$），无秩一连接确实带来刚性，不存在 $u\in\mathcal{A}$ 使 $\nabla u\in K$ a.e.；
- 但对**近似解 / 极小化序列**（$E(u_j)\to 0$），无秩一连接的刚性仅在二井（Ball–James）和三井（Šverák）下成立；到四井时，$K=\{A_1,A_2,A_3,A_4\}$ 在对角矩阵平面中恰好构成经典的 **Tartar 四点构型（$T_4$ 方块）**。引入四个辅助对角矩阵
  $$
  J_1=\operatorname{diag}(1,0),\quad
  J_2=\operatorname{diag}(1,1),\quad
  J_3=\operatorname{diag}(0,1),\quad
  J_4=\operatorname{diag}(0,0)=0,
  $$
  它们满足循环秩一连接关系：
  $$
  \begin{aligned}
  J_4 &= \frac{1}{4}A_4+\frac{3}{4}J_3, && A_4-J_3=\operatorname{diag}(0,-4)=-4\,e_2\otimes e_2,\\
  J_3 &= \frac{1}{3}A_3+\frac{2}{3}J_2, && A_3-J_2=\operatorname{diag}(-3,0)=-3\,e_1\otimes e_1,\\
  J_2 &= \frac{1}{2}A_2+\frac{1}{2}J_1, && A_2-J_1=\operatorname{diag}(0,2)=2\,e_2\otimes e_2,\\
  J_1 &= \frac{1}{3}A_1+\frac{2}{3}J_4, && A_1-J_4=\operatorname{diag}(3,0)=3\,e_1\otimes e_1.
  \end{aligned}
  $$
  零矩阵 $0=J_4$ 本身就是内层循环方块的顶点之一，落在层合包壳 $K^{lc}\subset K^{qc}$ 中，且所有井与辅助矩阵的 Frobenius 范数均不超过 $3<4$。因此可以通过多尺度循环层合构造出满足零边界和 $\|\nabla u_j\|_{L^\infty(\Omega)}\le 4$ 的位移序列使能量趋于 $0$。

下面分别对三项任务给出严格证明。

---

### 任务 1：$e_0$ 的精确值及极小元存在性

**结论：**
$$
e_0 = \inf_{u\in\mathcal{A}} E(u) = 0,
$$
且**不存在** $u\in\mathcal{A}$ 达到该最小值。

#### 1.1 证明 $e_0 = 0$
由非负性知对任意 $u\in\mathcal{A}$ 有 $E(u)\ge 0$，故 $e_0\ge 0$。在任务 3 中，我们将显式构造序列 $\{u_j\}_{j=1}^\infty\subset\mathcal{A}$，满足
$$
E(u_j) \le 299\cdot 6^{-j} \xrightarrow{j\to\infty} 0.
$$
因此 $0\le e_0 \le \lim_{j\to\infty} E(u_j)=0$，即 $e_0=0$。

#### 1.2 证明不存在 $u\in\mathcal{A}$ 达到 $E(u)=0$
假设存在 $u=(u_1,u_2)\in\mathcal{A}$ 使得 $E(u)=0$。由定义
$$
\int_\Omega \min_{1\le i\le 4}\|\nabla u(x)-A_i\|_F^2\,dx = 0
\implies \nabla u(x)\in K=\{A_1,A_2,A_3,A_4\} \quad \text{a.e. } x\in\Omega.
$$
由于 $A_1,A_2,A_3,A_4$ 均为对角矩阵，其非对角元恒为 $0$，因此在 $\Omega=(0,1)^2$ 上几乎处处有
$$
\partial_2 u_1(x_1,x_2) = 0,\qquad \partial_1 u_2(x_1,x_2) = 0.
$$
因为 $u\in W^{1,\infty}(\Omega;\mathbb{R}^2)\subset C(\overline{\Omega};\mathbb{R}^2)$ 且在 $\partial\Omega$ 上迹为 $0$（特别地 $u_1(x_1,0)=0$，$u_2(0,x_2)=0$），沿坐标方向积分立得：对任意 $(x_1,x_2)\in[0,1]^2$，
$$
u_1(x_1,x_2) = u_1(x_1,0) + \int_0^{x_2} \partial_2 u_1(x_1,s)\,ds = 0,
$$
$$
u_2(x_1,x_2) = u_2(0,x_2) + \int_0^{x_1} \partial_1 u_2(s,x_2)\,ds = 0.
$$
（注：即便不借用边界条件，由 $\partial_2 u_1=0,\ \partial_1 u_2=0$ 也知 $\nabla u(x_1,x_2)=\operatorname{diag}(f'(x_1),g'(x_2))$，而 $A_1,\dots,A_4$ 的 $(1,1)$ 元 $\{3,1,-2,0\}$ 与 $(2,2)$ 元 $\{0,2,1,-3\}$ 均互不相同，这迫使相指标同时仅依赖于 $x_1$ 和仅依赖于 $x_2$，从而在连通集 $\Omega$ 上恒为常矩阵。）

故 $u\equiv 0$，从而 $\nabla u(x)\equiv 0$。但 $0\notin K$，且
$$
E(0) = \min_{1\le i\le 4}\|A_i\|_F^2 = \min\{9,\,5,\,5,\,9\} = 5 \ne 0,
$$
矛盾！因此不存在 $u\in\mathcal{A}$ 使 $E(u)=e_0=0$。

---

### 任务 2：极小化序列相体积分数的收敛性与唯一极限

**结论：**
对任意满足 $E(u_j)\to e_0=0$ 的序列 $\{u_j\}\subset\mathcal{A}$，相体积分数向量必然收敛到**同一个唯一极限**：
$$
\lim_{j\to\infty}\big(\pi_1(u_j),\pi_2(u_j),\pi_3(u_j),\pi_4(u_j)\big)
= \left(\frac{1}{10},\,\frac{3}{10},\,\frac{3}{10},\,\frac{3}{10}\right).
$$

#### 证明
对任意 $u\in\mathcal{A}$，记被分配给 $A_i$ 的可测集为 $\Omega_i(u)$（$i=1,2,3,4$），则 $\{\Omega_i(u)\}_{i=1}^4$ 构成 $\Omega=(0,1)^2$ 的不交可测剖分，$\pi_i(u)=|\Omega_i(u)|$，且在 $\Omega_i(u)$ 上 $\|\nabla u(x)-A_i\|_F^2=\min_{1\le k\le 4}\|\nabla u(x)-A_k\|_F^2$。

定义分片常值矩阵场
$$
W_u(x) := \sum_{i=1}^4 A_i \mathbf{1}_{\Omega_i(u)}(x).
$$
由 $|\Omega|=1$ 及 Cauchy–Schwarz 不等式，有
$$
\|\nabla u - W_u\|_{L^1(\Omega)}
= \int_\Omega \|\nabla u(x)-W_u(x)\|_F\,dx
\le \left(\int_\Omega \|\nabla u(x)-W_u(x)\|_F^2\,dx\right)^{1/2}
= \sqrt{E(u)}.
\tag{1}
$$

下面建立 $(\pi_1(u),\pi_2(u),\pi_3(u),\pi_4(u))$ 所满足的四个独立约束方程：

1. **总体积归一：**
   $$
   \pi_1(u) + \pi_2(u) + \pi_3(u) + \pi_4(u) = |\Omega| = 1.
   \tag{2}
   $$

2. **一阶零拉格朗日量（梯度积分恒等式）：**
   因为 $u\in W_0^{1,\infty}(\Omega;\mathbb{R}^2)$，由散度定理有 $\int_\Omega \nabla u(x)\,dx = 0$。结合 (1) 得
   $$
   \left\|\sum_{i=1}^4 \pi_i(u) A_i\right\|_F
   = \left\|\int_\Omega \big(W_u(x)-\nabla u(x)\big)\,dx\right\|_F
   \le \|\nabla u - W_u\|_{L^1(\Omega)} \le \sqrt{E(u)}.
   $$
   取对角元的 $(1,1)$ 和 $(2,2)$ 分量，记 $r_1(u):=3\pi_1(u)+\pi_2(u)-2\pi_3(u)$，$r_2(u):=2\pi_2(u)+\pi_3(u)-3\pi_4(u)$，则
   $$
   |r_1(u)| \le \sqrt{E(u)},\qquad |r_2(u)| \le \sqrt{E(u)}.
   \tag{3}
   $$

3. **二阶零拉格朗日量（雅可比行列式积分恒等式）：**
   对任意 $v\in C_c^\infty(\Omega;\mathbb{R}^2)$，由 $\det\nabla v = \partial_1(v_1\partial_2 v_2)-\partial_2(v_1\partial_1 v_2)$ 及散度定理有 $\int_\Omega \det\nabla v\,dx=0$。由 $C_c^\infty(\Omega;\mathbb{R}^2)$ 在 $W_0^{1,2}(\Omega;\mathbb{R}^2)$ 中的稠密性，对任意 $u\in\mathcal{A}\subset W_0^{1,\infty}(\Omega;\mathbb{R}^2)$ 仍有
   $$
   \int_\Omega \det\nabla u(x)\,dx = 0.
   $$
   另一方面，对任意 $X,Y\in\mathbb{R}^{2\times 2}$，由代数恒等式
   $$
   \det X - \det Y = X_{11}(X_{22}-Y_{22}) + Y_{22}(X_{11}-Y_{11}) - X_{12}(X_{21}-Y_{21}) - Y_{21}(X_{12}-Y_{12})
   $$
   及 Cauchy–Schwarz 不等式，有
   $$
   |\det X - \det Y| \le \sqrt{X_{11}^2+Y_{22}^2+X_{12}^2+Y_{21}^2}\,\|X-Y\|_F
   \le \sqrt{\|X\|_F^2+\|Y\|_F^2}\,\|X-Y\|_F.
   $$
   对几乎处处 $x\in\Omega$，有 $\|\nabla u(x)\|_F\le 4$ 且 $\|W_u(x)\|_F\le \max_{1\le i\le 4}\|A_i\|_F=3$，故 $\sqrt{\|\nabla u(x)\|_F^2+\|W_u(x)\|_F^2}\le\sqrt{16+9}=5$。注意到
   $$
   \det(A_1)=0,\quad \det(A_2)=2,\quad \det(A_3)=-2,\quad \det(A_4)=0,
   $$
   记 $r_3(u):=2\pi_2(u)-2\pi_3(u)=\sum_{i=1}^4 \pi_i(u)\det(A_i)$，则
   $$
   |r_3(u)| = \left|\int_\Omega \big(\det W_u(x)-\det\nabla u(x)\big)\,dx\right|
   \le 5\int_\Omega \|W_u(x)-\nabla u(x)\|_F\,dx \le 5\sqrt{E(u)}.
   \tag{4}
   $$

联立 (2)–(4)，向量 $\pi(u)=(\pi_1(u),\pi_2(u),\pi_3(u),\pi_4(u))^T$ 满足线性方程组
$$
M \pi(u) = \begin{pmatrix} 1 \\ r_1(u) \\ r_2(u) \\ r_3(u) \end{pmatrix},\qquad
M := \begin{pmatrix}
1 & 1 & 1 & 1 \\
3 & 1 & -2 & 0 \\
0 & 2 & 1 & -3 \\
0 & 2 & -2 & 0
\end{pmatrix}.
$$
直接计算得 $\det M = 60 \ne 0$，故 $M$ 可逆。当 $r_1=r_2=r_3=0$ 时，唯一解为
$$
\left\{
\begin{aligned}
2\pi_2 - 2\pi_3 = 0 &\implies \pi_3 = \pi_2,\\
3\pi_1 + \pi_2 - 2\pi_3 = 0 &\implies \pi_2 = 3\pi_1,\\
2\pi_2 + \pi_3 - 3\pi_4 = 0 &\implies \pi_4 = 3\pi_1,\\
\pi_1+\pi_2+\pi_3+\pi_4=1 &\implies 10\pi_1 = 1
\end{aligned}
\right.
\implies
\pi^* = \left(\frac{1}{10},\,\frac{3}{10},\,\frac{3}{10},\,\frac{3}{10}\right)^T.
$$
进一步由 $M(\pi(u)-\pi^*)=(0,r_1(u),r_2(u),r_3(u))^T$ 及 (3)、(4) 可得定量稳定性估计：
$$
\|\pi(u) - \pi^*\|_2 \le \|M^{-1}\|_2 \sqrt{r_1(u)^2+r_2(u)^2+r_3(u)^2} \le C\sqrt{E(u)}.
$$
因此，对任意满足 $E(u_j)\to 0$ 的序列 $u_j\in\mathcal{A}$，必有 $\pi(u_j)\to \left(\frac{1}{10},\frac{3}{10},\frac{3}{10},\frac{3}{10}\right)$，极限唯一。

---

### 任务 3：具体近最优位移构造及条件验证

我们给出完全显式的分片光滑（在有限个轴对齐矩形网格上分片双线性/仿射）位移序列 $u_j\in\mathcal{A}$ 的构造。

#### 3.1 矩形上的单步秩一层合替换引理

设 $R=(a_1,b_1)\times(a_2,b_2)\subset\Omega$ 为任一开矩形，边长为 $L_1=b_1-a_1>0$，$L_2=b_2-a_2>0$。给定截断比 $\tau\in(0,1/4)$ 与层合周期数 $N\in\mathbb{N}_+$：

- **一维梯形截断函数：** 对区间 $[a,b]$（长度 $L=b-a$）及 $\delta=\tau L$，定义 $\eta_{[a,b],\delta}:[a,b]\to[0,1]$ 为
  $$
  \eta_{[a,b],\delta}(t) := \begin{cases}
  \dfrac{t-a}{\delta}, & t\in[a,a+\delta],\\[6pt]
  1, & t\in[a+\delta,b-\delta],\\[6pt]
  \dfrac{b-t}{\delta}, & t\in[b-\delta,b].
  \end{cases}
  $$
  则 $\eta_{[a,b],\delta}\in W_0^{1,\infty}((a,b))$，$0\le \eta_{[a,b],\delta}\le 1$，在 $(a+\delta,b-\delta)$ 上 $\eta'=0$，在两端截断带 $|\eta'|=\frac{1}{\tau L}$。

- **一维锯齿函数：** 设斜率参数 $c_+,c_->0$，权重 $\lambda_+=\frac{c_-}{c_++c_-}$，$\lambda_-=\frac{c_+}{c_++c_-}$（满足 $\lambda_++\lambda_-=1$，$\lambda_+c_+-\lambda_-c_-=0$）。将 $[a,b]$ 等分为 $N$ 个周期小区间 $I_m=[t_{m-1},t_m]$（$t_m=a+mh$，$h=L/N$，$m=1,\dots,N$），并在每个周期内取分界点 $s_m=t_{m-1}+\lambda_+ h$，记 $I_m^+=(t_{m-1},s_m)$，$I_m^-=(s_m,t_m)$。定义 $\phi_{[a,b],N,c_+,c_-}:[a,b]\to\mathbb{R}$ 在每个周期 $I_m$ 上为
  $$
  \phi_{[a,b],N,c_+,c_-}(t) := \begin{cases}
  c_+(t-t_{m-1}), & t\in[t_{m-1},s_m],\\[4pt]
  c_-(t_m-t), & t\in[s_m,t_m].
  \end{cases}
  $$
  由于 $c_+\lambda_+ h = \frac{c_+c_-}{c_++c_-}h = c_-\lambda_- h$，该函数在 $[a,b]$ 上连续且分片线性，在所有节点 $t_m$（含端点 $a,b$）处取值为 $0$，且满足
  $$
  0 \le \phi_{[a,b],N,c_+,c_-}(t) \le \frac{c_+c_-}{c_++c_-}\frac{L}{N},\qquad
  \phi'_{[a,b],N,c_+,c_-}(t) = \begin{cases}
  c_+, & t\in I_m^+,\\
  -c_-, & t\in I_m^-.
  \end{cases}
  $$

由此定义两种方向的局部层合微扰 $w_R\in W_0^{1,\infty}(R;\mathbb{R}^2)$：

1. **水平分裂（对应 $e_1\otimes e_1$ 秩一连接）：**
   设背景矩阵 $J=\operatorname{diag}(d_1,d_2)$，目标矩阵 $M_+=\operatorname{diag}(d_1+c_+,d_2)$，$M_-=\operatorname{diag}(d_1-c_-,d_2)$。取 $\delta_2=\tau L_2$，定义
   $$
   w_R^{\mathrm{H}}(x_1,x_2) := \begin{pmatrix}
   \phi_{[a_1,b_1],N,c_+,c_-}(x_1)\,\eta_{[a_2,b_2],\delta_2}(x_2)\\[4pt]
   0
   \end{pmatrix}.
   $$
   则 $w_R^{\mathrm{H}}|_{\partial R}=0$，且：
   - 在 $N$ 个内部开矩形 $R_m^+ = I_m^+\times(a_2+\delta_2,b_2-\delta_2)$ 上，$J+\nabla w_R^{\mathrm{H}}(x)\equiv M_+$，总面积为 $\lambda_+(1-2\tau)|R|$；
   - 在 $N$ 个内部开矩形 $R_m^- = I_m^-\times(a_2+\delta_2,b_2-\delta_2)$ 上，$J+\nabla w_R^{\mathrm{H}}(x)\equiv M_-$，总面积为 $\lambda_-(1-2\tau)|R|$；
   - 在上下两条截断带 $B_R = (a_1,b_1)\times\big((a_2,a_2+\delta_2)\cup(b_2-\delta_2,b_2)\big)$（面积 $2\tau|R|$）上，
     $$
     J + \nabla w_R^{\mathrm{H}}(x) = \begin{pmatrix}
     d_1 + \phi'(x_1)\eta(x_2) & \phi(x_1)\eta'(x_2)\\
     0 & d_2
     \end{pmatrix}.
     $$
     由于 $\eta(x_2)\in[0,1]$，对角部分 $\operatorname{diag}(d_1+\phi'\eta,d_2)=(1-\eta)J+\eta M_\pm$ 是 $J$ 与 $M_\pm$ 的凸组合；非对角元满足
     $$
     |\phi(x_1)\eta'(x_2)| \le \frac{c_+c_-}{c_++c_-}\frac{L_1}{N\tau L_2}.
     $$
     取整数 $N = \left\lceil \frac{c_+c_-}{c_++c_-}\frac{L_1}{\tau L_2} \right\rceil$，即有 $|\phi(x_1)\eta'(x_2)|\le 1$，从而在整個 $R$ 上几乎处处成立：
     $$
     \|J + \nabla w_R^{\mathrm{H}}(x)\|_F
     \le \sqrt{\max\big(\|J\|_F,\|M_+\|_F,\|M_-\|_F\big)^2 + 1}.
     \tag{5}
     $$

2. **竖直分裂（对应 $e_2\otimes e_2$ 秩一连接）：**
   设背景矩阵 $J=\operatorname{diag}(d_1,d_2)$，目标矩阵 $M_+=\operatorname{diag}(d_1,d_2+c_+)$，$M_-=\operatorname{diag}(d_1,d_2-c_-)$。取 $\delta_1=\tau L_1$ 及 $N = \left\lceil \frac{c_+c_-}{c_++c_-}\frac{L_2}{\tau L_1} \right\rceil$，交换坐标角色定义
   $$
   w_R^{\mathrm{V}}(x_1,x_2) := \begin{pmatrix}
   0\\[4pt]
   \eta_{[a_1,b_1],\delta_1}(x_1)\,\phi_{[a_2,b_2],N,c_+,c_-}(x_2)
   \end{pmatrix}.
   $$
   同理 $w_R^{\mathrm{V}}|_{\partial R}=0$，在 $R_m^+=(a_1+\delta_1,b_1-\delta_1)\times I_m^+$（总面积 $\lambda_+(1-2\tau)|R|$）上 $J+\nabla w_R^{\mathrm{V}}\equiv M_+$，在 $R_m^-=(a_1+\delta_1,b_1-\delta_1)\times I_m^-$（总面积 $\lambda_-(1-2\tau)|R|$）上 $J+\nabla w_R^{\mathrm{V}}\equiv M_-$，在面积为 $2\tau|R|$ 的左右截断带 $B_R$ 上同样满足上界 (5)。

---

#### 3.2 四步循环层合组装位移 $u_j$

对任意固定的 $j\in\mathbb{N}_+$，取截断参数
$$
\tau_j := 6^{-j} \in \left(0,\frac{1}{6}\right].
$$
从初始区域 $\mathcal{R}_{0,1}=\{\Omega\}=\{(0,1)^2\}$ 和初始位移 $u^{(0)}(x)\equiv 0 = J_4 x$ 出发，递归进行 $j$ 轮循环（$m=0,1,\dots,j-1$）。在第 $m$ 轮循环中，设 $\mathcal{R}_{m,1}$ 为当前梯度恒等于 $J_4=0$ 的两两不交开矩形族，依次执行以下四步：

- **第 1 步（$J_4\to \{J_3,A_4\}$，竖直分裂）：**
  因 $J_4=\operatorname{diag}(0,0)$，$M_+=J_3=\operatorname{diag}(0,1)$，$M_-=A_4=\operatorname{diag}(0,-3)$，参数为 $c_+=1,c_-=3$，$\lambda_+=3/4,\lambda_-=1/4$。对每个 $R\in\mathcal{R}_{m,1}$ 叠加 $w_R^{\mathrm{V}}$：
  - 得到梯度恒为 $A_4$ 的矩形族（面积占 $\frac{1}{4}(1-2\tau_j)|R|$），此后不再修改；
  - 得到梯度恒为 $J_3$ 的内部矩形族，汇总记为 $\mathcal{R}_{m,2}$，总面积 $|\mathcal{R}_{m,2}|=\frac{3}{4}(1-2\tau_j)|\mathcal{R}_{m,1}|$；
  - 截断带汇总记为 $\mathcal{B}_{m,1}$，总面积 $2\tau_j|\mathcal{R}_{m,1}|$。

- **第 2 步（$J_3\to \{J_2,A_3\}$，水平分裂）：**
  因 $J_3=\operatorname{diag}(0,1)$，$M_+=J_2=\operatorname{diag}(1,1)$，$M_-=A_3=\operatorname{diag}(-2,1)$，参数为 $c_+=1,c_-=2$，$\lambda_+=2/3,\lambda_-=1/3$。对每个 $R\in\mathcal{R}_{m,2}$ 叠加 $w_R^{\mathrm{H}}$：
  - 得到梯度恒为 $A_3$ 的矩形族（面积占 $\frac{1}{3}(1-2\tau_j)|R|$），不再修改；
  - 得到梯度恒为 $J_2$ 的内部矩形族 $\mathcal{R}_{m,3}$，总面积 $|\mathcal{R}_{m,3}|=\frac{2}{3}(1-2\tau_j)|\mathcal{R}_{m,2}|=\frac{1}{2}(1-2\tau_j)^2|\mathcal{R}_{m,1}|$；
  - 截断带 $\mathcal{B}_{m,2}$，总面积 $2\tau_j|\mathcal{R}_{m,2}| \le \frac{3}{2}\tau_j|\mathcal{R}_{m,1}|$。

- **第 3 步（$J_2\to \{J_1,A_2\}$，竖直分裂）：**
  因 $J_2=\operatorname{diag}(1,1)$，$M_+=A_2=\operatorname{diag}(1,2)$，$M_-=J_1=\operatorname{diag}(1,0)$，参数为 $c_+=1,c_-=1$，$\lambda_+=1/2,\lambda_-=1/2$。对每个 $R\in\mathcal{R}_{m,3}$ 叠加 $w_R^{\mathrm{V}}$：
  - 得到梯度恒为 $A_2$ 的矩形族（面积占 $\frac{1}{2}(1-2\tau_j)|R|$），不再修改；
  - 得到梯度恒为 $J_1$ 的内部矩形族 $\mathcal{R}_{m,4}$，总面积 $|\mathcal{R}_{m,4}|=\frac{1}{2}(1-2\tau_j)|\mathcal{R}_{m,3}|=\frac{1}{4}(1-2\tau_j)^3|\mathcal{R}_{m,1}|$；
  - 截断带 $\mathcal{B}_{m,3}$，总面积 $2\tau_j|\mathcal{R}_{m,3}| \le \tau_j|\mathcal{R}_{m,1}|$。

- **第 4 步（$J_1\to \{A_1,J_4\}$，水平分裂）：**
  因 $J_1=\operatorname{diag}(1,0)$，$M_+=A_1=\operatorname{diag}(3,0)$，$M_-=J_4=\operatorname{diag}(0,0)$，参数为 $c_+=2,c_-=1$，$\lambda_+=1/3,\lambda_-=2/3$。对每个 $R\in\mathcal{R}_{m,4}$ 叠加 $w_R^{\mathrm{H}}$：
  - 得到梯度恒为 $A_1$ 的矩形族（面积占 $\frac{1}{3}(1-2\tau_j)|R|$），不再修改；
  - 得到梯度重新回到 $J_4=0$ 的内部矩形族 $\mathcal{R}_{m+1,1}$，总面积
    $$
    |\mathcal{R}_{m+1,1}| = \frac{2}{3}(1-2\tau_j)|\mathcal{R}_{m,4}| = \frac{1}{6}(1-2\tau_j)^4|\mathcal{R}_{m,1}| \le \frac{1}{6}|\mathcal{R}_{m,1}|;
    \tag{6}
    $$
  - 截断带 $\mathcal{B}_{m,4}$，总面积 $2\tau_j|\mathcal{R}_{m,4}| \le \frac{1}{2}\tau_j|\mathcal{R}_{m,1}|$。

经过 $j$ 轮循环后，定义位移 $u_j:\overline{\Omega}\to\mathbb{R}^2$ 为上述有限个局部微扰之和：
$$
u_j(x) := \sum_{m=0}^{j-1}\left(
\sum_{R\in\mathcal{R}_{m,1}} w_R^{\mathrm{V}}(x)
+ \sum_{R\in\mathcal{R}_{m,2}} w_R^{\mathrm{H}}(x)
+ \sum_{R\in\mathcal{R}_{m,3}} w_R^{\mathrm{V}}(x)
+ \sum_{R\in\mathcal{R}_{m,4}} w_R^{\mathrm{H}}(x)
\right).
$$

---

#### 3.3 严格验证三项性质

1. **正则性与零边界条件验证：**
   对固定 $j$，上述求和为有限和，且每一项 $w_R\in W_0^{1,\infty}(R;\mathbb{R}^2)$ 在 $\Omega\setminus R$ 上恒为 $0$。因此 $u_j\in W_0^{1,\infty}(\Omega;\mathbb{R}^2)$，在 $\partial\Omega$ 上的迹恒为 $0$。

2. **统一梯度上界 $\|\nabla u_j\|_F \le 4$ 验证：**
   关键观察是：**每一步的微扰 $w_R$ 仅添加在前一步内部常数梯度子矩形 $R\in\mathcal{R}_{m,s}$ 上（在该矩形上之前所有微扰之和的梯度恒为 $J_{5-s}$），而前序步骤产生的截断带 $\mathcal{B}_{m',s'}$ 与井矩形与后续所有微扰的支集互不相交！** 因此不同步骤的截断误差绝不叠加。
   对几乎处处 $x\in\Omega$，$x$ 必属于以下三类互不相交区域之一：
   - 某一步生成的井矩形（梯度为 $A_i$）：此时 $\|\nabla u_j(x)\|_F = \|A_i\|_F \le \max\{3,\sqrt{5},\sqrt{5},3\} = 3 \le 4$；
   - 第 $j$ 轮结束后的剩余矩形 $\mathcal{R}_{j,1}$（梯度为 $J_4=0$）：此时 $\|\nabla u_j(x)\|_F = 0 \le 4$；
   - 某一步的截断带 $\mathcal{B}_{m,s}$：此时 $\nabla u_j(x) = J_{5-s} + \nabla w_R(x)$。由上界 (5) 及
     $$
     \begin{aligned}
     s=1:&\quad \max(\|J_4\|_F,\|J_3\|_F,\|A_4\|_F) = \max(0,1,3) = 3,\\
     s=2:&\quad \max(\|J_3\|_F,\|J_2\|_F,\|A_3\|_F) = \max(1,\sqrt{2},\sqrt{5}) = \sqrt{5},\\
     s=3:&\quad \max(\|J_2\|_F,\|J_1\|_F,\|A_2\|_F) = \max(\sqrt{2},1,\sqrt{5}) = \sqrt{5},\\
     s=4:&\quad \max(\|J_1\|_F,\|A_1\|_F,\|J_4\|_F) = \max(1,3,0) = 3,
     \end{aligned}
     $$
     可知在所有截断带上均有
     $$
     \|\nabla u_j(x)\|_F \le \sqrt{3^2 + 1} = \sqrt{10} \approx 3.162 < 4.
     $$
   综上，$\operatorname*{ess\,sup}_{x\in\Omega}\|\nabla u_j(x)\|_F \le \sqrt{10} < 4$，故 $u_j\in\mathcal{A}$ 对一切 $j\ge 1$ 成立。

3. **能量估计与体积分数核验：**
   - 在所有井矩形 $A_1,A_2,A_3,A_4$ 上，$\min_{1\le i\le 4}\|\nabla u_j(x)-A_i\|_F^2 = 0$。
   - 由 (6) 归纳可知 $|\mathcal{R}_{m,1}|\le 6^{-m}$。在剩余矩形族 $\mathcal{R}_{j,1}$ 上，面积 $|\mathcal{R}_{j,1}|\le 6^{-j}$，且 $\nabla u_j(x)=0$，故被积函数恒为 $\min_i\|0-A_i\|_F^2=5$。
   - 在第 $m$ 轮的四类截断带 $\mathcal{B}_{m}=\bigcup_{s=1}^4 \mathcal{B}_{m,s}$ 上，总面积为
     $$
     |\mathcal{B}_m| \le \left(2 + \frac{3}{2} + 1 + \frac{1}{2}\right)\tau_j |\mathcal{R}_{m,1}| = 5\tau_j |\mathcal{R}_{m,1}| \le 5\tau_j\cdot 6^{-m}.
     $$
     全部 $j$ 轮截断带的总面积满足
     $$
     |\mathcal{B}| = \sum_{m=0}^{j-1}|\mathcal{B}_m| \le 5\tau_j \sum_{m=0}^{j-1} 6^{-m} < 5\tau_j\cdot\frac{6}{5} = 6\tau_j = 6\cdot 6^{-j}.
     $$
     而在 $\mathcal{B}$ 上，由 $\|\nabla u_j(x)\|_F\le 4$ 及 $\|A_i\|_F\le 3$，有 $\min_{1\le i\le 4}\|\nabla u_j(x)-A_i\|_F^2 \le (4+3)^2 = 49$。

   因此总能量满足
   $$
   E(u_j) = \int_{\mathcal{B}} \min_{1\le i\le 4}\|\nabla u_j(x)-A_i\|_F^2\,dx
   + \int_{\mathcal{R}_{j,1}} \min_{1\le i\le 4}\|0-A_i\|_F^2\,dx
   \le 49\cdot(6\cdot 6^{-j}) + 5\cdot 6^{-j} = 299\cdot 6^{-j} \xrightarrow{j\to\infty} 0.
   $$
   同时，第 $m$ 轮中进入各井 $A_1,A_2,A_3,A_4$ 的精确面积分别为 $\frac{1}{12}(1-2\tau_j)^4|\mathcal{R}_{m,1}|$、$\frac{1}{4}(1-2\tau_j)^3|\mathcal{R}_{m,1}|$、$\frac{1}{4}(1-2\tau_j)^2|\mathcal{R}_{m,1}|$、$\frac{1}{4}(1-2\tau_j)|\mathcal{R}_{m,1}|$；当 $j\to\infty$（$\tau_j\to 0$）时，对公比为 $1/6$ 的几何级数求和即得各相体积分数收敛至
   $$
   \sum_{m=0}^\infty \left(\frac{1}{6}\right)^m \left(\frac{1}{12},\,\frac{1}{4},\,\frac{1}{4},\,\frac{1}{4}\right)
   = \frac{6}{5}\left(\frac{1}{12},\,\frac{1}{4},\,\frac{1}{4},\,\frac{1}{4}\right)
   = \left(\frac{1}{10},\,\frac{3}{10},\,\frac{3}{10},\,\frac{3}{10}\right),
   $$
   与任务 2 的唯一极限结论完全吻合。证毕。
