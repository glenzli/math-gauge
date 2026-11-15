{}
### 记号约定与前期相容性推理的勘误

对位移 $u=(u_1,u_2)\in W^{1,\infty}(\Omega;\mathbb{R}^2)$，采用标准 Jacobi 梯度记号
$$\nabla u(x)=\begin{pmatrix}\partial_1 u_1(x) & \partial_2 u_1(x)\\ \partial_1 u_2(x) & \partial_2 u_2(x)\end{pmatrix},$$
矩阵 Frobenius 范数为 $\|M\|_F=\big(\sum_{p,q=1}^2 M_{pq}^2\big)^{1/2}$，张量积 $(a\otimes b)_{pq}=a_p b_q$，标准基 $e_1=(1,0)^T,\,e_2=(0,1)^T$（注：由于四个井均为对角矩阵且 $\|\cdot\|_F$、$\det$ 在矩阵转置下不变，即便采用转置梯度记号，以下全部结论、公式与显式位移构造也完全不变）。

**对前期相容性推理的勘误：**
前期计算中，六个两井差依次为
$$A_1-A_2=\operatorname{diag}(2,-2),\quad A_1-A_3=\operatorname{diag}(5,-1),\quad A_1-A_4=\operatorname{diag}(3,3),$$
$$A_2-A_3=\operatorname{diag}(3,1),\quad A_2-A_4=\operatorname{diag}(1,5),\quad A_3-A_4=\operatorname{diag}(-2,4),$$
其行列式确为 $-4,-5,9,3,5,-8$，均不为零，故 $K$ 中任意两井之间**确实没有秩一连接**。

然而，“任意两井无秩一连接 + 统一 Lipschitz 上界 $\implies$ 不能形成能量趋零的混相序列、$e_0>0$”这一步推理**不成立**。二相（乃至三相）无秩一连接时的近似刚性定理不能逐相推广到四相系统：这里的 $K=\{A_1,A_2,A_3,A_4\}$ 构成经典的 **Tartar 四态构型（$T_4$ 构型）**。具体地，引入四个内圈辅助对角矩阵
$$B_1=\operatorname{diag}(1,0),\quad B_2=\operatorname{diag}(1,1),\quad B_3=\operatorname{diag}(0,1),\quad B_4=\operatorname{diag}(0,0)=0,$$
它们与四井之间形成首尾相接的秩一凸组合闭链：
$$B_4=\frac{3}{4}B_3+\frac{1}{4}A_4,\quad B_3=\frac{2}{3}B_2+\frac{1}{3}A_3,\quad B_2=\frac{1}{2}B_1+\frac{1}{2}A_2,\quad B_1=\frac{2}{3}B_4+\frac{1}{3}A_1.$$
沿此闭链迭代消去辅助态即知零矩阵 $0=B_4$ 属于 $K$ 的无限阶层合包（从而属于秩一凸包与拟凸包）；同时 $\max_{1\le i\le 4}\|A_i\|_F=3<4$，梯度上界 $4$ 为截断边界层留出了严格正的余量（下文构造满足 $\|\nabla u_k\|_F\le\sqrt{10}<4$）。因此：
- **近似层面上刚性失效**：存在零边界混相序列使能量趋于 $0$，即 **$e_0=0$**（无正能量间隙）；
- **精确层面上刚性仍成立**：不存在 $u\in\mathcal{A}$ 使 $E(u)=0$。

为保证证明逻辑完全无循环：**第 3 节**仅从 $\mathcal{A}$ 与 $E$ 的定义出发，独立给出满足 $u_k\in\mathcal{A}$ 且 $E(u_k)<35\cdot 6^{-k}\to 0$ 的显式序列 $\{u_k\}_{k=1}^\infty$；**第 1 节**与**第 2 节**在此基础上完成精确值、不可达性与相体积分数唯一极限的证明。

---

### 1. 单元能 $e_0$ 的精确值及极小元存在性证明

**结论：** $e_0=0$，且**不存在** $u\in\mathcal{A}$ 达到 $e_0$（即对一切 $u\in\mathcal{A}$ 均有 $E(u)>0$）。

**证明：**
1. **$e_0=0$ 的证明：**
   首先 $u\equiv 0$ 满足 $0\in W^{1,\infty}(\Omega;\mathbb{R}^2)$、边界迹为 $0$ 且 $\|\nabla 0\|_F=0\le 4$，故 $\mathcal{A}\neq\emptyset$。对任意 $u\in\mathcal{A}$，被积函数 $\min_{1\le i\le 4}\|\nabla u(x)-A_i\|_F^2\ge 0$ 处处非负，积分得 $E(u)\ge 0$，从而 $e_0=\inf_{u\in\mathcal{A}}E(u)\ge 0$。
   另一方面，由第 3 节独立构造的序列 $\{u_k\}_{k=1}^\infty\subset\mathcal{A}$ 知 $E(u_k)<35\cdot 6^{-k}$（$\forall k\ge 1$）。令 $k\to\infty$ 得
   $$0\le e_0\le \inf_{k\ge 1}E(u_k)=0,$$
   故 $e_0=0$。

2. **极小值不可达到的证明：**
   反设存在 $u=(u_1,u_2)\in\mathcal{A}$ 使 $E(u)=0$。由非负可积函数积分为零可知
   $$\min_{1\le i\le 4}\|\nabla u(x)-A_i\|_F^2=0 \quad\text{对 a.e. }x\in\Omega\text{ 成立},$$
   即对几乎处处 $x\in\Omega$ 有 $\nabla u(x)\in K=\{A_1,A_2,A_3,A_4\}$。由于 $A_1,A_2,A_3,A_4$ 均为对角矩阵，其非对角元全为 $0$，故在 $\Omega$ 上几乎处处有
   $$\partial_2 u_1(x)=0,\qquad \partial_1 u_2(x)=0.$$
   因为 $\Omega=(0,1)^2$ 是有界 Lipschitz 区域，$u\in W^{1,\infty}(\Omega;\mathbb{R}^2)\subset H^1(\Omega;\mathbb{R}^2)$ 且在 $\partial\Omega$ 上迹为 $0$，故 $u_1,u_2\in H^1_0(\Omega)$。对任意检验函数 $\varphi\in C_c^\infty(\Omega)$，由微积分基本定理与 Cauchy–Schwarz 不等式，对一切 $(x_1,x_2)\in(0,1)^2$ 有
   $$|\varphi(x_1,x_2)|^2=\left|\int_0^{x_2}\partial_2\varphi(x_1,t)\,dt\right|^2\le x_2\int_0^1|\partial_2\varphi(x_1,t)|^2\,dt\le\int_0^1|\partial_2\varphi(x_1,t)|^2\,dt.$$
   对 $(x_1,x_2)$ 在 $\Omega=(0,1)^2$ 上积分得 $\|\varphi\|_{L^2(\Omega)}^2\le\|\partial_2\varphi\|_{L^2(\Omega)}^2$；同理 $\|\varphi\|_{L^2(\Omega)}^2\le\|\partial_1\varphi\|_{L^2(\Omega)}^2$。利用 $C_c^\infty(\Omega)$ 在 $H^1_0(\Omega)$ 中的稠密性取极限，立得
   $$\|u_1\|_{L^2(\Omega)}\le\|\partial_2 u_1\|_{L^2(\Omega)}=0,\qquad \|u_2\|_{L^2(\Omega)}\le\|\partial_1 u_2\|_{L^2(\Omega)}=0.$$
   因此 $u=0$ a.e. 于 $\Omega$，进而弱梯度 $\nabla u=0$ a.e. 于 $\Omega$。然而直接计算各井范数平方得
   $$\|A_1\|_F^2=9,\quad \|A_2\|_F^2=5,\quad \|A_3\|_F^2=5,\quad \|A_4\|_F^2=9,$$
   故
   $$E(u)=E(0)=\int_\Omega\min_{1\le i\le 4}\|A_i\|_F^2\,dx=\min\{9,5,5,9\}=5\neq 0,$$
   与 $E(u)=0$ 矛盾。因此 $\mathcal{A}$ 中不存在达到 $e_0$ 的位移。$\blacksquare$

---

### 2. 极小化序列相体积分数的收敛性与全部可能极限

**结论：** 对**任意**满足 $E(u_j)\to e_0=0$ 的序列 $\{u_j\}\subset\mathcal{A}$，相体积分数向量 $(\pi_1(u_j),\pi_2(u_j),\pi_3(u_j),\pi_4(u_j))$ **必然收敛到同一个向量**；全部可能的极限仅有唯一向量
$$p^*=\left(\frac{1}{10},\;\frac{3}{10},\;\frac{3}{10},\;\frac{3}{10}\right).$$

**证明：**
**第一步：Voronoi 剖分与逐段常值逼近矩阵场。**
按“就近分配、等距取最小编号”的规则，定义矩阵空间 $\mathbb{R}^{2\times 2}$ 的四个 Borel 子集（$i=1,2,3,4$）：
$$V_i:=\Big\{M\in\mathbb{R}^{2\times 2}:\ \forall m<i,\ \|M-A_i\|_F<\|M-A_m\|_F;\ \text{且}\ \forall m>i,\ \|M-A_i\|_F\le\|M-A_m\|_F\Big\}.$$
易见 $\{V_1,V_2,V_3,V_4\}$ 两两不交且构成 $\mathbb{R}^{2\times 2}$ 的剖分，并在每个 $V_i$ 上恒有 $\|M-A_i\|_F^2=\min_{1\le m\le 4}\|M-A_m\|_F^2$。对任意 $u\in\mathcal{A}$，令 $\Omega_i(u):=\{x\in\Omega:\nabla u(x)\in V_i\}$，则 $\{\Omega_i(u)\}_{i=1}^4$ 是 $\Omega$ 的可测剖分（相差零测集，故 $\pi_i(u)=|\Omega_i(u)|$ 不依赖于 $\nabla u$ 的几乎处处代表元），且满足
$$\sum_{i=1}^4\pi_i(u)=\sum_{i=1}^4|\Omega_i(u)|=|\Omega|=1. \tag{2.1}$$
定义逐段常值矩阵场 $M_u(x):=\sum_{i=1}^4 A_i\mathbf{1}_{\Omega_i(u)}(x)$，则对 a.e. $x\in\Omega$ 有 $\|\nabla u(x)-M_u(x)\|_F^2=\min_{1\le m\le 4}\|\nabla u(x)-A_m\|_F^2$，积分即得
$$\|\nabla u-M_u\|_{L^2(\Omega)}^2=\int_\Omega\|\nabla u(x)-M_u(x)\|_F^2\,dx=E(u). \tag{2.2}$$

**第二步：零边界梯度的两个积分恒等式（均值与行列式零拉格朗日量）。**
任取 $u\in\mathcal{A}\subset H^1_0(\Omega;\mathbb{R}^2)$，存在序列 $\varphi_n=(\varphi_{n,1},\varphi_{n,2})\in C_c^\infty(\Omega;\mathbb{R}^2)$ 使得 $\|\nabla\varphi_n-\nabla u\|_{L^2(\Omega)}\to 0$（$n\to\infty$）。
1. 对每个 $n$，因 $\varphi_n$ 在 $\Omega$ 内紧支，分部积分得 $\int_\Omega\nabla\varphi_n(x)\,dx=0$。由 $\|\nabla\varphi_n-\nabla u\|_{L^1(\Omega)}\le\|\nabla\varphi_n-\nabla u\|_{L^2(\Omega)}\to 0$，得
   $$\int_\Omega\nabla u(x)\,dx=0. \tag{2.3}$$
2. 对任意 $X,Y\in\mathbb{R}^{2\times 2}$，由代数恒等式
   $$\det X-\det Y=(X_{11}-Y_{11})X_{22}+Y_{11}(X_{22}-Y_{22})-(X_{12}-Y_{12})X_{21}-Y_{12}(X_{21}-Y_{21})$$
   及 $\mathbb{R}^4$ 上的 Cauchy–Schwarz 不等式，有
   $$|\det X-\det Y|\le\|X-Y\|_F\sqrt{X_{22}^2+X_{21}^2+Y_{11}^2+Y_{12}^2}\le\|X-Y\|_F\big(\|X\|_F+\|Y\|_F\big). \tag{2.4}$$
   对每个 $\varphi_n\in C_c^\infty(\Omega;\mathbb{R}^2)$，利用光滑函数混合偏导相等 $\partial_1\partial_2\varphi_{n,2}=\partial_2\partial_1\varphi_{n,2}$，可将行列式写成散度形式：
   $$\det(\nabla\varphi_n)=\partial_1\varphi_{n,1}\,\partial_2\varphi_{n,2}-\partial_2\varphi_{n,1}\,\partial_1\varphi_{n,2}=\partial_1(\varphi_{n,1}\partial_2\varphi_{n,2})-\partial_2(\varphi_{n,1}\partial_1\varphi_{n,2}).$$
   因括号内两项均属于 $C_c^\infty(\Omega)$，在 $\Omega$ 上积分得 $\int_\Omega\det(\nabla\varphi_n(x))\,dx=0$。再对 $X=\nabla\varphi_n(x),\,Y=\nabla u(x)$ 应用 (2.4) 与 $L^2(\Omega)$ 上的 Cauchy–Schwarz 不等式：
   $$\left|\int_\Omega\det(\nabla\varphi_n)\,dx-\int_\Omega\det(\nabla u)\,dx\right|\le\|\nabla\varphi_n-\nabla u\|_{L^2(\Omega)}\big(\|\nabla\varphi_n\|_{L^2(\Omega)}+\|\nabla u\|_{L^2(\Omega)}\big)\longrightarrow 0,$$
   从而得到
   $$\int_\Omega\det(\nabla u(x))\,dx=0. \tag{2.5}$$

**第三步：关于 $\pi(u)$ 的定量稳定性估计与唯一极限求解。**
对任意 $u\in\mathcal{A}$：
- 由 (2.2)、(2.3) 及 $|\Omega|=1$，
  $$\left\|\sum_{i=1}^4\pi_i(u)A_i\right\|_F=\left\|\int_\Omega\big(M_u(x)-\nabla u(x)\big)\,dx\right\|_F\le\int_\Omega\|M_u(x)-\nabla u(x)\|_F\,dx\le\sqrt{E(u)}. \tag{2.6}$$
- 因 $\{\Omega_i(u)\}_{i=1}^4$ 互不相交，几乎处处有 $\det(M_u(x))=\sum_{i=1}^4\det(A_i)\mathbf{1}_{\Omega_i(u)}(x)$，且 $\|M_u(x)\|_F\le\max_{1\le i\le 4}\|A_i\|_F=3$，而 $u\in\mathcal{A}$ 满足 $\|\nabla u(x)\|_F\le 4$ a.e.。结合 (2.4)、(2.5) 与 (2.2) 得
  $$\left|\sum_{i=1}^4\pi_i(u)\det(A_i)\right|=\left|\int_\Omega\big(\det(M_u(x))-\det(\nabla u(x))\big)\,dx\right|\le 7\int_\Omega\|M_u(x)-\nabla u(x)\|_F\,dx\le 7\sqrt{E(u)}. \tag{2.7}$$

注意到 $\det(A_1)=0,\,\det(A_2)=2,\,\det(A_3)=-2,\,\det(A_4)=0$，将 (2.1)、$\sum_{i=1}^4\pi_i(u)A_i$ 的两个对角分量以及 $\sum_{i=1}^4\pi_i(u)\det(A_i)$ 合并写成线性映射。记 $\pi(u)=(\pi_1(u),\pi_2(u),\pi_3(u),\pi_4(u))^T$ 及
$$L:=\begin{pmatrix}
1 & 1 & 1 & 1\\
3 & 1 & -2 & 0\\
0 & 2 & 1 & -3\\
0 & 2 & -2 & 0
\end{pmatrix},\qquad b:=\begin{pmatrix}1\\0\\0\\0\end{pmatrix},\qquad r(u):=L\pi(u)-b=\begin{pmatrix}0\\ r_2(u)\\ r_3(u)\\ r_4(u)\end{pmatrix}.$$
由 (2.6) 与 (2.7) 知 $|r_2(u)|\le\sqrt{E(u)}$，$|r_3(u)|\le\sqrt{E(u)}$，$|r_4(u)|\le 7\sqrt{E(u)}$。按第 4 行展开计算得
$$\det(L)=2\det\begin{pmatrix}1&1&1\\3&-2&0\\0&1&-3\end{pmatrix}+2\det\begin{pmatrix}1&1&1\\3&1&0\\0&2&-3\end{pmatrix}=2\times 18+2\times 12=60\neq 0,$$
故 $L$ 可逆，直接求逆（可直接验证 $L^{-1}L=I_4$）得
$$L^{-1}=\frac{1}{30}\begin{pmatrix}
3 & 9 & 1 & -7\\
9 & -3 & 3 & 9\\
9 & -3 & 3 & -6\\
9 & -3 & -7 & 4
\end{pmatrix},\qquad p^*:=L^{-1}b=\left(\frac{1}{10},\;\frac{3}{10},\;\frac{3}{10},\;\frac{3}{10}\right)^T.$$
由 $\pi(u)-p^*=L^{-1}r(u)$ 对每一分量估计，对一切 $u\in\mathcal{A}$ 成立显式定量不等式：
$$\max_{1\le i\le 4}|\pi_i(u)-p_i^*|\le\frac{3+3+9\times 7}{30}\sqrt{E(u)}=\frac{23}{10}\sqrt{E(u)}. \tag{2.8}$$
因此，对**任意**满足 $E(u_j)\to e_0=0$ 的序列 $\{u_j\}\subset\mathcal{A}$，由 (2.8) 必有 $\lim_{j\to\infty}\pi(u_j)=p^*$。反之，第 3 节构造的序列 $\{u_k\}\subset\mathcal{A}$ 满足 $E(u_k)\to 0$，其相体积分数确实收敛到 $p^*$。综上，全部可能的极限集合恰为单点集 $\big\{(\frac{1}{10},\frac{3}{10},\frac{3}{10},\frac{3}{10})\big\}$。$\blacksquare$

> **注（梯度场约束的作用）：** 若将 $\nabla u$ 放宽为仅满足均值 $\int_\Omega M\,dx=0$ 的一般矩阵场，则仅保留前三行约束，$\sum_{i=1}^4 p_i A_i=0$ 在单纯形上的解集为一维线段 $p(t)=\big(\frac{5-15t}{8},\frac{15t-3}{8},\frac{3-6t}{4},t\big)$（$t\in[\frac{1}{5},\frac{1}{3}]$）。正是梯度场的旋度相容性与零边界共同导出的行列式恒等式 (2.5) 给出 $2p_2-2p_3=0$，从该线段中唯一确定了 $t=\frac{3}{10}$。

---

### 3. 具体近最优位移构造及零边界、梯度上界与能量估计验证

本节完全从 $\mathcal{A}$ 和 $E$ 的定义出发，显式构造序列 $\{u_k\}_{k=1}^\infty\subset\mathcal{A}$。

#### 3.1 四步秩一分解参数表

令 $B_1=\operatorname{diag}(1,0)$，$B_2=\operatorname{diag}(1,1)$，$B_3=\operatorname{diag}(0,1)$，$B_4=\operatorname{diag}(0,0)$。注意 $K\cup\{B_1,B_2,B_3,B_4\}$ 中所有矩阵均为对角矩阵，且 Frobenius 范数均不超过 $3$：
$$\|A_1\|_F=3,\ \|A_2\|_F=\sqrt{5},\ \|A_3\|_F=\sqrt{5},\ \|A_4\|_F=3,\ \|B_1\|_F=1,\ \|B_2\|_F=\sqrt{2},\ \|B_3\|_F=1,\ \|B_4\|_F=0.$$
下表列出四步循环（$r=1,2,3,4$）的秩一凸分解 $B^{(r)}=\lambda_r P^{(r)}+(1-\lambda_r)Q^{(r)}$ 及秩一差 $P^{(r)}-Q^{(r)}=\alpha_r e_{d_r}\otimes e_{d_r}$，其中记 $\gamma_{r,+}:=(1-\lambda_r)\alpha_r$，$\gamma_{r,-}:=-\lambda_r\alpha_r$：

| 步序 $r$ | 母态 $B^{(r)}$ | 活跃子态 $P^{(r)}$ | 冻结井态 $Q^{(r)}$ | 比例 $\lambda_r$ | 振荡方向 $x_{d_r}$ / 截断方向 | $\alpha_r$ | $(\gamma_{r,+},\,\gamma_{r,-})$ | $\lambda_r(1-\lambda_r)\|\alpha_r\|$ |
| :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| $1$ | $B_4=\operatorname{diag}(0,0)$ | $B_3=\operatorname{diag}(0,1)$ | $A_4=\operatorname{diag}(0,-3)$ | $3/4$ | 竖直振荡 $x_2$ / 水平截断 $x_1$ | $4$ | $(1,\,-3)$ | $3/4$ |
| $2$ | $B_3=\operatorname{diag}(0,1)$ | $B_2=\operatorname{diag}(1,1)$ | $A_3=\operatorname{diag}(-2,1)$ | $2/3$ | 水平振荡 $x_1$ / 竖直截断 $x_2$ | $3$ | $(1,\,-2)$ | $2/3$ |
| $3$ | $B_2=\operatorname{diag}(1,1)$ | $B_1=\operatorname{diag}(1,0)$ | $A_2=\operatorname{diag}(1,2)$ | $1/2$ | 竖直振荡 $x_2$ / 水平截断 $x_1$ | $-2$ | $(-1,\,1)$ | $1/2$ |
| $4$ | $B_1=\operatorname{diag}(1,0)$ | $B_4=\operatorname{diag}(0,0)$ | $A_1=\operatorname{diag}(3,0)$ | $2/3$ | 水平振荡 $x_1$ / 竖直截断 $x_2$ | $-3$ | $(-1,\,2)$ | $2/3$ |

对每一步 $r\in\{1,2,3,4\}$，直接验算均有 $\lambda_r P^{(r)}+(1-\lambda_r)Q^{(r)}=B^{(r)}$，$P^{(r)}-B^{(r)}=\gamma_{r,+}e_{d_r}\otimes e_{d_r}$，以及 $Q^{(r)}-B^{(r)}=\gamma_{r,-}e_{d_r}\otimes e_{d_r}$。

#### 3.2 矩形上的单步截断层合引理

**引理 3.1（单步局部层合扰动）：**
设开矩形 $R=(a_1,b_1)\times(a_2,b_2)\subset\Omega$ 的边长为 $\ell_1=b_1-a_1>0,\,\ell_2=b_2-a_2>0$，给定参数 $\delta\in(0,\frac{1}{4})$ 及上表中的任一步参数 $(B,P,Q,\lambda,\alpha,\gamma_+,\gamma_-)$。
1. 定义 $[0,1]$ 上的梯形截断函数 $\eta_\delta:[0,1]\to[0,1]$：
   $$\eta_\delta(s):=\begin{cases}
   s/\delta, & 0\le s\le\delta,\\
   1, & \delta<s<1-\delta,\\
   (1-s)/\delta, & 1-\delta\le s\le 1;
   \end{cases}$$
2. 定义 $\mathbb{R}$ 上以 $1$ 为周期的连续逐段仿射锯齿函数 $\psi:\mathbb{R}\to\mathbb{R}$，它在 $[0,1]$ 上由
   $$\psi(t):=\begin{cases}
   \gamma_+ t, & 0\le t\le\lambda,\\
   \gamma_+\lambda+\gamma_-(t-\lambda), & \lambda<t\le 1
   \end{cases}$$
   给出，并按 $\psi(t+m)=\psi(t)$（$m\in\mathbb{Z}$）延拓至 $\mathbb{R}$。因 $\gamma_+\lambda+\gamma_-(1-\lambda)=(1-\lambda)\alpha\lambda-\lambda\alpha(1-\lambda)=0=\psi(0)$，$\psi$ 在 $\mathbb{R}$ 上全局连续且逐段仿射，其最大振幅为
   $$\max_{t\in\mathbb{R}}|\psi(t)|=|\psi(\lambda)|=\lambda|\gamma_+|=\lambda(1-\lambda)|\alpha|.$$
3. 按振荡方向显式选取正整数频率 $N$ 并定义扰动位移 $v_R:\overline{\Omega}\to\mathbb{R}^2$（在 $\overline{\Omega}\setminus R$ 上令 $v_R(x):=(0,0)$）：
   - **情形 H（水平振荡 $d_r=1$，即 $r\in\{2,4\}$）：** 取正整数
     $$N:=\left\lceil\frac{\lambda(1-\lambda)|\alpha|\,\ell_1}{\delta\,\ell_2}\right\rceil\ge 1,$$
     对 $x=(x_1,x_2)\in\overline{R}$ 定义
     $$v_R(x_1,x_2):=\left(\eta_\delta\!\left(\frac{x_2-a_2}{\ell_2}\right)\frac{\ell_1}{N}\,\psi\!\left(N\frac{x_1-a_1}{\ell_1}\right),\;0\right).$$
   - **情形 V（竖直振荡 $d_r=2$，即 $r\in\{1,3\}$）：** 取正整数
     $$N:=\left\lceil\frac{\lambda(1-\lambda)|\alpha|\,\ell_2}{\delta\,\ell_1}\right\rceil\ge 1,$$
     对 $x=(x_1,x_2)\in\overline{R}$ 定义
     $$v_R(x_1,x_2):=\left(0,\;\eta_\delta\!\left(\frac{x_1-a_1}{\ell_1}\right)\frac{\ell_2}{N}\,\psi\!\left(N\frac{x_2-a_2}{\ell_2}\right)\right).$$

则 $v_R$ 满足以下性质：
- **(i) 全局 Lipschitz 正则性与零边界：** 在 $\overline{R}$ 上，$v_R$ 为两个有界单变量 Lipschitz 函数的乘积，故在 $\overline{R}$ 上 Lipschitz 连续。在边界 $\partial R$ 上：当截断变量取端点时 $\eta_\delta(0)=\eta_\delta(1)=0$；当振荡变量取端点时 $\psi$ 的自变量为 $0$ 或正整数 $N$，由 $1$-周期性知 $\psi(0)=\psi(N)=0$。故 $v_R|_{\partial R}\equiv 0$。将其在 $\overline{\Omega}\setminus R$ 上零延拓后（对任意 $x\in\overline{R},\,y\in\overline{\Omega}\setminus R$，连接线段 $[x,y]$ 与 $\partial R$ 交于某点 $z$，有 $|v_R(x)-v_R(y)|=|v_R(x)-v_R(z)|\le\operatorname{Lip}(v_R|_{\overline{R}})|x-z|\le\operatorname{Lip}(v_R|_{\overline{R}})|x-y|$），得到 $v_R\in C^{0,1}(\overline{\Omega};\mathbb{R}^2)=W^{1,\infty}(\Omega;\mathbb{R}^2)$，特别地 $v_R|_{\partial\Omega}\equiv 0$，且在 $\Omega\setminus R$ 上几乎处处 $\nabla v_R=0$。
- **(ii) 子矩形剖分与测度：** $R$ 内含 $2N$ 个两两不交的开子矩形 $\{R_m^P\}_{m=0}^{N-1}$ 与 $\{R_m^Q\}_{m=0}^{N-1}$：
  - 在情形 H 下，对 $m=0,\dots,N-1$，
    $$R_m^P:=\left(a_1+\frac{m}{N}\ell_1,\;a_1+\frac{m+\lambda}{N}\ell_1\right)\times(a_2+\delta\ell_2,\;b_2-\delta\ell_2),$$
    $$R_m^Q:=\left(a_1+\frac{m+\lambda}{N}\ell_1,\;a_1+\frac{m+1}{N}\ell_1\right)\times(a_2+\delta\ell_2,\;b_2-\delta\ell_2);$$
  - 在情形 V 下，对 $m=0,\dots,N-1$，
    $$R_m^P:=(a_1+\delta\ell_1,\;b_1-\delta\ell_1)\times\left(a_2+\frac{m}{N}\ell_2,\;a_2+\frac{m+\lambda}{N}\ell_2\right),$$
    $$R_m^Q:=(a_1+\delta\ell_1,\;b_1-\delta\ell_1)\times\left(a_2+\frac{m+\lambda}{N}\ell_2,\;a_2+\frac{m+1}{N}\ell_2\right).$$
  在每个开矩形 $R_m^P$ 上 $\eta_\delta\equiv 1,\,\psi'\equiv\gamma_+$，故恒有 $B+\nabla v_R(x)=P$；在每个开矩形 $R_m^Q$ 上 $\eta_\delta\equiv 1,\,\psi'\equiv\gamma_-$，故恒有 $B+\nabla v_R(x)=Q$。各 $R_m^P$ 彼此全等，且有精确测度
  $$\sum_{m=0}^{N-1}|R_m^P|=\lambda(1-2\delta)|R|,\qquad \sum_{m=0}^{N-1}|R_m^Q|=(1-\lambda)(1-2\delta)|R|.$$
  除有限条线段（二维测度为 $0$）外，剩余部分为截断带 $C_R:=R\setminus\overline{\bigcup_{m=0}^{N-1}(R_m^P\cup R_m^Q)}$，其测度为 $|C_R|=2\delta|R|$。
- **(iii) 逐点 Frobenius 梯度上界：** 在 $R$ 内除去上述有限条折线后的全测度开集上，$v_R$ 光滑，且 $B+\nabla v_R(x)=D(x)+E_{\mathrm{off}}(x)$：
  - 对角部分 $D(x)=B+\eta_\delta\psi'\,e_{d_r}\otimes e_{d_r}$：当 $\psi'=\gamma_+$ 时 $D(x)=(1-\eta_\delta)B+\eta_\delta P$；当 $\psi'=\gamma_-$ 时 $D(x)=(1-\eta_\delta)B+\eta_\delta Q$。因 $\eta_\delta\in[0,1]$ 且 $\|B\|_F,\|P\|_F,\|Q\|_F\le 3$，由范数凸性知 $\|D(x)\|_F\le 3$。
  - 非对角部分 $E_{\mathrm{off}}(x)$ 仅含唯一非零非对角元（情形 H 在 $(1,2)$ 位，情形 V 在 $(2,1)$ 位），结合 $|\eta_\delta'|\le 1/\delta$、$|\psi|\le\lambda(1-\lambda)|\alpha|$ 及 $N$ 的取法，有
    $$\|E_{\mathrm{off}}(x)\|_F\le\frac{\ell_{\mathrm{osc}}}{N\ell_{\mathrm{cut}}}\cdot\frac{1}{\delta}\cdot\lambda(1-\lambda)|\alpha|\le 1.$$
  因对角矩阵与纯非对角矩阵在 Frobenius 内积下正交，对 a.e. $x\in R$ 有
  $$\|B+\nabla v_R(x)\|_F=\sqrt{\|D(x)\|_F^2+\|E_{\mathrm{off}}(x)\|_F^2}\le\sqrt{3^2+1^2}=\sqrt{10}<4.$$

**证明：** 以上各项已由直接求导与逐段估计给出。$\blacksquare$

#### 3.3 序列 $\{u_k\}_{k=1}^\infty$ 的归纳定义

对任意给定的正整数 $k\ge 1$，固定截断参数
$$\delta:=6^{-k-1}\in\left(0,\frac{1}{36}\right].$$
我们归纳构造有限步位移序列 $w_0,w_1,\dots,w_{4k}$ 及两两不交的全等活跃开矩形有限族 $\mathcal{R}_0,\mathcal{R}_1,\dots,\mathcal{R}_{4k}$：
- **初值（$n=0$）：** 令 $w_0(x):=(0,0)$（$\forall x\in\overline{\Omega}$），$\mathcal{R}_0:=\{\Omega\}$。此时在唯一的矩形 $R\in\mathcal{R}_0$ 上恒有 $\nabla w_0(x)=B_4=0$，活跃总测度 $a_0:=|\Omega|=1$。
- **归纳步（$n=1,2,\dots,4k$）：** 设 $n=4m+r$，其中 $m\in\{0,\dots,k-1\},\,r\in\{1,2,3,4\}$。归纳假设 $\mathcal{R}_{n-1}$ 为有限个两两不交的全等开矩形族，且在每个 $R\in\mathcal{R}_{n-1}$ 上恒有 $\nabla w_{n-1}(x)=B^{(r)}$。对每个 $R\in\mathcal{R}_{n-1}$，以参数 $\delta=6^{-k-1}$ 和 3.1 节表中第 $r$ 步参数应用引理 3.1，得到局部扰动 $v_R$、子矩形 $\{R_p^P\},\{R_p^Q\}$ 与截断带 $C_R$。令
  $$w_n:=w_{n-1}+\sum_{R\in\mathcal{R}_{n-1}}v_R,\qquad \mathcal{R}_n:=\bigcup_{R\in\mathcal{R}_{n-1}}\{R_0^P,\dots,R_{N-1}^P\},$$
  并记第 $n$ 步冻结井相开集为 $F_n:=\bigcup_{R\in\mathcal{R}_{n-1}}\bigcup_{p=0}^{N-1}R_p^Q$（其上梯度恒为 $Q^{(r)}\in K$），第 $n$ 步截断层为 $C_n:=\bigcup_{R\in\mathcal{R}_{n-1}}C_R$。因 $F_n\cup C_n$ 与 $\bigcup_{R'\in\mathcal{R}_n}R'$ 互不相交，后续第 $n+1,\dots,4k$ 步的所有扰动在 $F_n\cup C_n$ 上恒为零。
- **定义 $u_k$：** 完成 $4k$ 步后，令 $u_k:=w_{4k}$。

#### 3.4 零边界、统一梯度上界与能量估计的验证

1. **正则性与零边界验证：**
   对每个固定的 $k\ge 1$，$u_k=w_{4k}$ 是 $w_0\equiv 0$ 与**有限个**属于 $C^{0,1}(\overline{\Omega};\mathbb{R}^2)\cap W^{1,\infty}(\Omega;\mathbb{R}^2)$ 且在 $\partial\Omega$ 上恒为 $0$ 的函数 $v_R$ 的有限线性求和。由线性空间封闭性立得 $u_k\in W^{1,\infty}(\Omega;\mathbb{R}^2)$，且在 $\partial\Omega$ 上逐点恒有 $u_k|_{\partial\Omega}=0$（迹为 $0$）。

2. **统一梯度上界验证：**
   对 $n=0,1,\dots,4k$ 用数学归纳法验证 $\operatorname{ess\,sup}_\Omega\|\nabla w_n\|_F\le\sqrt{10}<4$：
   - $n=0$ 时 $\|\nabla w_0\|_F=0\le\sqrt{10}$。
   - 设 $n-1$ 时成立。在第 $n$ 步，因 $\mathcal{R}_{n-1}$ 是有限个互不相交的开矩形族，且当 $R\in\mathcal{R}_{n-1}$ 时 $\nabla v_R=0$ a.e. 于 $\Omega\setminus R$：
     - 对 a.e. $x\in\Omega\setminus\bigcup_{R\in\mathcal{R}_{n-1}}R$，有 $\nabla w_n(x)=\nabla w_{n-1}(x)$，故 $\|\nabla w_n(x)\|_F\le\sqrt{10}$；
     - 对每个 $R\in\mathcal{R}_{n-1}$ 及 a.e. $x\in R$，因 $R$ 上恒有 $\nabla w_{n-1}=B^{(r)}$ 而其余 $R'\neq R$ 满足 $\nabla v_{R'}=0$ a.e. 于 $R$，故 $\nabla w_n(x)=B^{(r)}+\nabla v_R(x)$，由引理 3.1(iii) 知 $\|\nabla w_n(x)\|_F\le\sqrt{10}$。
   归纳即得对每个 $k\ge 1$ 有
   $$\operatorname{ess\,sup}_\Omega\|\nabla u_k\|_F\le\sqrt{10}<4,$$
   故对一切 $k\ge 1$ 均有 $u_k\in\mathcal{A}$。

3. **能量估计验证：**
   记 $a_n:=\sum_{R\in\mathcal{R}_n}|R|$（$0\le n\le 4k$）。由引理 3.1(ii) 知 $a_n=\lambda_n(1-2\delta)a_{n-1}$，$|F_n|=(1-\lambda_n)(1-2\delta)a_{n-1}$，$|C_n|=2\delta a_{n-1}$。对每个四步周期 $m\in\{0,\dots,k-1\}$，因 $\lambda_1\lambda_2\lambda_3\lambda_4=\frac{3}{4}\cdot\frac{2}{3}\cdot\frac{1}{2}\cdot\frac{2}{3}=\frac{1}{6}$，记 $\theta_\delta:=\frac{(1-2\delta)^4}{6}\in(0,\frac{1}{6})$，则
   $$a_{4m}=\theta_\delta^m,\quad a_{4m+1}=\frac{3}{4}(1-2\delta)\theta_\delta^m,\quad a_{4m+2}=\frac{1}{2}(1-2\delta)^2\theta_\delta^m,\quad a_{4m+3}=\frac{1}{4}(1-2\delta)^3\theta_\delta^m.$$
   由此估计各区域测度：
   - 第 $4k$ 步剩余活跃集 $R_{\mathrm{rem}}:=\bigcup_{R\in\mathcal{R}_{4k}}R$ 的测度为 $a_{4k}=\theta_\delta^k<6^{-k}$；
   - 全部截断层并集 $C_{\mathrm{tot}}:=\bigcup_{n=1}^{4k}C_n$ 的总测度满足
     $$|C_{\mathrm{tot}}|\le\sum_{n=1}^{4k}|C_n|=2\delta\sum_{m=0}^{k-1}\theta_\delta^m\Big(1+\frac{3}{4}(1-2\delta)+\frac{1}{2}(1-2\delta)^2+\frac{1}{4}(1-2\delta)^3\Big)<2\delta\cdot\frac{5}{2}\sum_{m=0}^\infty 6^{-m}=6\delta=6^{-k};$$
   - 在冻结井相并集 $F_{\mathrm{tot}}:=\bigcup_{n=1}^{4k}F_n$ 上，后续各步从未修改 $w_n$，故对一切 $x\in F_{\mathrm{tot}}$ 恒有 $\nabla u_k(x)\in K$，能量被积函数恒为 $0$。

   由于 $\Omega$ 除去零测折线网后恰分解为互不相交的 $F_{\mathrm{tot}}\cup R_{\mathrm{rem}}\cup C_{\mathrm{tot}}$：
   - 在 $R_{\mathrm{rem}}$ 上恒有 $\nabla u_k(x)=B_4=0$，故 $\min_{1\le i\le 4}\|\nabla u_k(x)-A_i\|_F^2=\min_{1\le i\le 4}\|A_i\|_F^2=5$；
   - 在 $C_{\mathrm{tot}}$ 上几乎处处有 $\|\nabla u_k(x)\|_F\le\sqrt{10}$，结合 $\|A_2\|_F=\sqrt{5}$，由三角不等式得
     $$\min_{1\le i\le 4}\|\nabla u_k(x)-A_i\|_F^2\le\|\nabla u_k(x)-A_2\|_F^2\le(\sqrt{10}+\sqrt{5})^2=15+10\sqrt{2}<30.$$
   将三部分积分相加，对一切 $k\ge 1$ 有显式上界：
   $$E(u_k)=0+\int_{R_{\mathrm{rem}}}5\,dx+\int_{C_{\mathrm{tot}}}\min_{1\le i\le 4}\|\nabla u_k(x)-A_i\|_F^2\,dx<5\cdot 6^{-k}+30\cdot 6^{-k}=35\cdot 6^{-k}\longrightarrow 0\quad(k\to\infty).$$

4. **相体积分数直接核算（与第 2 节印证）：**
   在每个周期 $m\in\{0,\dots,k-1\}$ 中，四个冻结井相集依次为 $F_{4m+1}$（对应 $A_4$）、$F_{4m+2}$（对应 $A_3$）、$F_{4m+3}$（对应 $A_2$）、$F_{4m+4}$（对应 $A_1$），测度分别为 $\frac{1}{4}(1-2\delta)\theta_\delta^m$、$\frac{1}{4}(1-2\delta)^2\theta_\delta^m$、$\frac{1}{4}(1-2\delta)^3\theta_\delta^m$、$\frac{1}{12}(1-2\delta)^4\theta_\delta^m$。在冻结集上 $\nabla u_k\equiv A_i$ 严格被分配给 $A_i$，而冻结集之外余集的测度为 $a_{4k}+|C_{\mathrm{tot}}|<2\cdot 6^{-k}\to 0$。当 $k\to\infty$（$\delta=6^{-k-1}\to 0$）时，$\sum_{m=0}^{k-1}\theta_\delta^m=\frac{1-\theta_\delta^k}{1-\theta_\delta}\to\frac{6}{5}$，故
   $$\lim_{k\to\infty}\pi_1(u_k)=\frac{1}{12}\cdot\frac{6}{5}=\frac{1}{10},\qquad \lim_{k\to\infty}\pi_i(u_k)=\frac{1}{4}\cdot\frac{6}{5}=\frac{3}{10}\quad(i=2,3,4),$$
   与第 2 节的唯一极限结论完全吻合。$\blacksquare$
