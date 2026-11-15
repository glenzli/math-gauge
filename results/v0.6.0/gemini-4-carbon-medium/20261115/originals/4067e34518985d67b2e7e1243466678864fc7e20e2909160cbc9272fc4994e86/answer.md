{}
### 对前期相容性估计的修正与结论总览

在进入正式证明之前，先指出题目中“前期相容性估计”的关键推理漏洞：

1. 六个两井差的行列式计算无误：
   $$\det(A_1-A_2)=-4,\quad \det(A_1-A_3)=-5,\quad \det(A_1-A_4)=9,$$
   $$\det(A_2-A_3)=3,\quad \det(A_2-A_4)=5,\quad \det(A_3-A_4)=-8,$$
   均不为零，因此 $K=\{A_1,A_2,A_3,A_4\}$ 中任意两井确实**不存在秩一连接**（一阶层合壳 $L_1(K)=K$）。
2. 然而，**二相刚性估计（及二维三相刚性）不能逐相套用到四相系统**。这四个对角矩阵在二维对角矩阵子空间中构成经典的 **Tartar 四方构型（$T_4$ 构型）**：尽管 $K$ 内部没有任何秩一连接，但引入四个辅助对角矩阵
   $$J_1=\operatorname{diag}(1,0),\quad J_2=\operatorname{diag}(1,1),\quad J_3=\operatorname{diag}(0,1),\quad J_4=\operatorname{diag}(0,0)=0,$$
   它们之间形成首尾闭合的秩一分解循环，使零矩阵 $0=J_4$ 落在 $K$ 的无穷阶层合壳（从而拟凸壳）中；并且通过分片双线性的局部截断层合，可以在严格满足零边界条件与统一梯度上界 $\operatorname{ess\,sup}_\Omega\|\nabla u\|_F\le \sqrt{10}<4$ 的前提下构造出能量趋于 $0$ 的位移序列。因此**单元能不存在正间隙**。

三项任务的精确结论如下：

1. **单元能与可达性**：$e_0 = 0$，且 $\mathcal{A}$ 中**不存在**位移 $u$ 达到该最小值。
2. **相体积分数的极限**：对**任意**满足 $E(u_j)\to e_0=0$ 的序列 $\{u_j\}\subset\mathcal{A}$，相体积分数向量 $(\pi_1(u_j),\pi_2(u_j),\pi_3(u_j),\pi_4(u_j))$ **必然收敛到同一个唯一向量**：
   $$\pi^* = \left(\frac{1}{10},\,\frac{3}{10},\,\frac{3}{10},\,\frac{3}{10}\right).$$
   全部可能极限的集合为单点集 $\left\{\left(\frac{1}{10},\frac{3}{10},\frac{3}{10},\frac{3}{10}\right)\right\}$。
3. **显式近最优位移构造**：利用 $T_4$ 循环在轴对齐矩形族上的有限步递归锯齿–梯形截断构造，可给出显式分片双线性序列 $\{u_j\}_{j=1}^\infty\subset\mathcal{A}$，满足 $u_j|_{\partial\Omega}=0$，$\operatorname{ess\,sup}_\Omega\|\nabla u_j\|_F\le \sqrt{10}<4$，且 $E(u_j)<5\cdot 6^{-j}+30\cdot 2^{-j}\to 0$。

---

### 记号约定与基本性质

对 $u=(u_1,u_2)^\top \in W^{1,\infty}(\Omega;\mathbb{R}^2)$，梯度矩阵记为
$$\nabla u(x) = \begin{pmatrix} \partial_{x_1} u_1(x) & \partial_{x_2} u_1(x) \\ \partial_{x_1} u_2(x) & \partial_{x_2} u_2(x) \end{pmatrix}, \qquad \|F\|_F = \left(\sum_{a,b=1}^2 F_{ab}^2\right)^{1/2}.$$
将每个 $u\in W^{1,\infty}(\Omega;\mathbb{R}^2)$ 等同于其在 $\overline{\Omega}=[0,1]^2$ 上的唯一 Lipschitz 连续代表元；于是“$u$ 在 $\partial\Omega$ 上的迹为 $0$”等价于在 $\partial\Omega$ 上逐点成立 $u(x)=0$。由 Rademacher 定理，$\nabla u(x)$ 在 $\Omega$ 上几乎处处古典存在且有界可测。四个井的 Frobenius 范数与行列式分别为：
$$\|A_1\|_F=3,\quad \|A_2\|_F=\sqrt{5},\quad \|A_3\|_F=\sqrt{5},\quad \|A_4\|_F=3,$$
$$\det A_1 = 0,\quad \det A_2 = 2,\quad \det A_3 = -2,\quad \det A_4 = 0.$$

> **注（逻辑依赖说明）**：下文第 3 节对显式序列 $\{u_j\}_{j=1}^\infty\subset\mathcal{A}$ 的构造与验证完全独立于第 1、2 节；第 1 节直接引用第 3 节的序列给出上界 $e_0\le 0$，无任何循环论证。

---

### 1. 单元能 $e_0$ 的精确值与最小值不可达性证明

**定理 1.** $e_0 = \inf_{u\in\mathcal{A}} E(u) = 0$，且不存在 $u\in\mathcal{A}$ 使得 $E(u)=0$。

**证明.**

**(1) 证明 $e_0 = 0$。**
一方面，对任意 $u\in\mathcal{A}$，被积函数 $\min_{1\le i\le 4}\|\nabla u(x)-A_i\|_F^2 \ge 0$ 在 $\Omega$ 上几乎处处非负，故 $E(u)\ge 0$，从而 $e_0 \ge 0$。
另一方面，由下文第 3 节（完全不依赖本节与第 2 节结论）显式构造的位移序列 $\{u_j\}_{j=1}^\infty \subset \mathcal{A}$，对一切 $j\ge 1$ 成立
$$0 \le e_0 \le E(u_j) < 5\cdot 6^{-j} + 30\cdot 2^{-j}.$$
令 $j\to\infty$，得 $e_0 = 0$。

**(2) 证明不存在 $u\in\mathcal{A}$ 达到 $e_0=0$。**
反证法。假设存在 $u=(u_1,u_2)^\top \in \mathcal{A}$ 使得 $E(u)=0$。由非负可测函数积分为零的性质，对几乎处处的 $x\in\Omega=(0,1)^2$ 有
$$\min_{1\le i\le 4}\|\nabla u(x)-A_i\|_F^2 = 0, \quad \text{即} \quad \nabla u(x) \in K = \{A_1,A_2,A_3,A_4\}.$$
由于 $K$ 中的四个矩阵全部是对角矩阵，其非对角元均为 $0$，因此在 $\Omega=(0,1)^2$ 上几乎处处成立
$$\partial_{x_2} u_1(x_1,x_2) = 0, \qquad \partial_{x_1} u_2(x_1,x_2) = 0.$$
因为 $u_1 \in W^{1,\infty}(\Omega)$ 在 $\overline{\Omega}=[0,1]^2$ 上 Lipschitz 连续，由 Fubini 定理可知：对几乎处处的 $x_1\in(0,1)$，一元函数 $t\mapsto u_1(x_1,t)$ 在 $[0,1]$ 上绝对连续，且其导数对几乎处处的 $t\in(0,1)$ 等于 $\partial_{x_2}u_1(x_1,t)=0$。结合下边界零迹条件 $u_1(x_1,0)=0$，对几乎处处的 $x_1\in(0,1)$ 及任意 $x_2\in[0,1]$ 有
$$u_1(x_1,x_2) = u_1(x_1,0) + \int_0^{x_2} \partial_{x_2}u_1(x_1,t)\,dt = 0.$$
再由 $u_1$ 在 $\overline{\Omega}$ 上的连续性，得 $u_1 \equiv 0$ 于 $\overline{\Omega}$。

完全同理，对几乎处处的 $x_2\in(0,1)$，一元函数 $s\mapsto u_2(s,x_2)$ 在 $[0,1]$ 上绝对连续且导数几乎处处为 $\partial_{x_1}u_2(s,x_2)=0$；结合左边界零迹条件 $u_2(0,x_2)=0$ 及 $u_2$ 的连续性，得 $u_2 \equiv 0$ 于 $\overline{\Omega}$。

于是 $u\equiv 0$，$\nabla u\equiv 0$。代入能量泛函得
$$E(u) = E(0) = \int_\Omega \min_{1\le i\le 4}\|A_i\|_F^2\,dx = \min\{9,5,5,9\} = 5 \ne 0,$$
与 $E(u)=0$ 矛盾！故不存在 $u\in\mathcal{A}$ 达到 $e_0$。$\blacksquare$

---

### 2. 极小化序列相体积分数的收敛性与唯一极限

**定理 2.** 对任意 $u\in\mathcal{A}$，记 $\pi(u)=(\pi_1(u),\pi_2(u),\pi_3(u),\pi_4(u))^\top$ 及
$$\pi^* := \left(\frac{1}{10},\,\frac{3}{10},\,\frac{3}{10},\,\frac{3}{10}\right)^\top.$$
则存在正常数 $C>0$（与 $u$ 无关），使得对一切 $u\in\mathcal{A}$ 成立定量稳定性估计
$$\|\pi(u) - \pi^*\|_2 \le C\sqrt{E(u)}.$$
特别地，对**任意**满足 $E(u_j)\to e_0=0$ 的序列 $\{u_j\}\subset\mathcal{A}$，整列 $(\pi_1(u_j),\dots,\pi_4(u_j))$ 必然收敛到同一个向量 $\left(\frac{1}{10},\frac{3}{10},\frac{3}{10},\frac{3}{10}\right)$；结合第 3 节存在满足 $E(u_j)\to 0$ 的序列，全部可能的极限仅有唯一向量 $\left(\frac{1}{10},\frac{3}{10},\frac{3}{10},\frac{3}{10}\right)$。

**证明.**

**第一步：可测相划分与分片常值近似场。**
任取 $u\in\mathcal{A}$。设 $\Omega'\subset\Omega$ 为 $\nabla u(x)$ 存在的全测度可测集（$|\Omega\setminus\Omega'|=0$，零测集不影响各相 Lebesgue 测度）。令 $d_i(x):=\|\nabla u(x)-A_i\|_F$（$i=1,2,3,4$），按“取最近井、距离相同时取最小编号”的分配规则，四个相集可显式写为：
$$\Omega_1(u) = \bigl\{x\in\Omega' : d_1(x) \le \min\{d_2(x),d_3(x),d_4(x)\}\bigr\},$$
$$\Omega_i(u) = \Bigl\{x\in\Omega'\setminus\bigcup_{k=1}^{i-1}\Omega_k(u) : d_i(x) \le \min_{i\le \ell\le 4} d_\ell(x)\Bigr\}, \qquad i=2,3,4.$$
因各 $d_i$ 在 $\Omega'$ 上可测，故 $\Omega_1(u),\dots,\Omega_4(u)$ 为两两不交的可测集，且 $\bigsqcup_{i=1}^4 \Omega_i(u)=\Omega'$。因此 $\pi_i(u)=|\Omega_i(u)|\ge 0$ 且满足归一化关系：
$$\sum_{i=1}^4 \pi_i(u) = |\Omega'| = |\Omega| = 1.$$

定义分片常值矩阵场 $W_u : \Omega' \to K$ 为
$$W_u(x) := \sum_{i=1}^4 A_i \mathbf{1}_{\Omega_i(u)}(x).$$
对任意 $x\in\Omega_i(u)$，由分配规则知 $d_i(x)=\min_{1\le \ell\le 4} d_\ell(x)$（即使发生距离平局，所选最小编号 $i$ 依然实现该最小距离），因此逐点成立
$$\|\nabla u(x) - W_u(x)\|_F^2 = \min_{1\le \ell\le 4}\|\nabla u(x)-A_\ell\|_F^2,$$
在 $\Omega$ 上积分即得
$$\int_\Omega \|\nabla u(x) - W_u(x)\|_F^2\,dx = E(u).$$

**第二步：一阶矩（梯度均值）估计。**
因 $u\in W^{1,\infty}(\Omega;\mathbb{R}^2)$ 且 $u|_{\partial\Omega}=0$，由散度定理（或对每个分量应用 Fubini 定理与一维微积分基本定理）有
$$\int_\Omega \nabla u(x)\,dx = 0.$$
注意到 $\int_\Omega W_u(x)\,dx = \sum_{i=1}^4 \pi_i(u) A_i$ 且 $|\Omega|=1$，由三角不等式与 Cauchy–Schwarz 不等式得
$$\left\|\sum_{i=1}^4 \pi_i(u) A_i\right\|_F = \left\|\int_\Omega \bigl(W_u(x) - \nabla u(x)\bigr)\,dx\right\|_F \le \int_\Omega \|W_u(x) - \nabla u(x)\|_F\,dx \le \sqrt{E(u)}.$$

**第三步：二阶子式（行列式零拉格朗日量）估计。**
先证对任意 $u\in\mathcal{A}$ 有
$$\int_\Omega \det(\nabla u(x))\,dx = 0.$$
事实上，$u\in W^{1,\infty}(\Omega;\mathbb{R}^2)$ 在有界 Lipschitz 区域 $\Omega=(0,1)^2$ 的边界上迹为 $0$，故 $u\in H_0^1(\Omega;\mathbb{R}^2)$，存在光滑紧支集函数列 $\varphi_k=(\varphi_{k,1},\varphi_{k,2})^\top \in C_c^\infty(\Omega;\mathbb{R}^2)$ 使得 $\varphi_k \to u$ 于 $H^1(\Omega;\mathbb{R}^2)$（即 $\nabla\varphi_k \to \nabla u$ 于 $L^2(\Omega;\mathbb{R}^{2\times 2})$）。对每个 $\varphi_k$，利用光滑函数二阶混合偏导数相等，可将行列式写成散度形式：
$$\det(\nabla\varphi_k) = \partial_{x_1}\varphi_{k,1}\,\partial_{x_2}\varphi_{k,2} - \partial_{x_2}\varphi_{k,1}\,\partial_{x_1}\varphi_{k,2} = \partial_{x_1}\bigl(\varphi_{k,1}\partial_{x_2}\varphi_{k,2}\bigr) - \partial_{x_2}\bigl(\varphi_{k,1}\partial_{x_1}\varphi_{k,2}\bigr).$$
因 $\operatorname{supp}(\varphi_k)\Subset\Omega$，积分立得 $\int_\Omega \det(\nabla\varphi_k(x))\,dx = 0$。又双线性泛函 $(F,G)\mapsto \int_\Omega (F_{11}G_{22}-F_{12}G_{21})\,dx$ 在 $L^2(\Omega;\mathbb{R}^{2\times 2})$ 上连续，令 $k\to\infty$ 即得 $\int_\Omega \det(\nabla u(x))\,dx = 0$。

再估计 $\det(W_u)-\det(\nabla u)$。对任意 $2\times 2$ 矩阵 $F,G\in\mathbb{R}^{2\times 2}$，记代数余子式映射 $\operatorname{cof}\begin{pmatrix}a&b\\c&d\end{pmatrix}=\begin{pmatrix}d&-c\\-b&a\end{pmatrix}$，则 $\|\operatorname{cof}(M)\|_F=\|M\|_F$，且直接展开可验证恒等式
$$\det(F) - \det(G) = \frac{1}{2}\bigl\langle F-G,\,\operatorname{cof}(F+G)\bigr\rangle_F.$$
由 Cauchy–Schwarz 不等式得
$$|\det(F) - \det(G)| \le \frac{1}{2}\|F-G\|_F \|F+G\|_F \le \frac{\|F\|_F + \|G\|_F}{2}\|F-G\|_F.$$
对几乎处处的 $x\in\Omega$，由 $u\in\mathcal{A}$ 知 $\|\nabla u(x)\|_F\le 4$，且 $\|W_u(x)\|_F \le \max_{1\le i\le 4}\|A_i\|_F = 3$，故
$$|\det(W_u(x)) - \det(\nabla u(x))| \le \frac{3+4}{2}\|W_u(x) - \nabla u(x)\|_F = \frac{7}{2}\|W_u(x) - \nabla u(x)\|_F.$$
结合 $\int_\Omega \det(W_u(x))\,dx = \sum_{i=1}^4 \pi_i(u)\det(A_i)$ 与 $\int_\Omega \det(\nabla u(x))\,dx = 0$，积分并用 Cauchy–Schwarz 不等式得
$$\left|\sum_{i=1}^4 \pi_i(u)\det(A_i)\right| = \left|\int_\Omega \bigl(\det(W_u(x)) - \det(\nabla u(x))\bigr)\,dx\right| \le \frac{7}{2}\sqrt{E(u)}.$$

**第四步：满秩四元线性系统求解与唯一极限。**
把 $\sum_{i=1}^4 \pi_i(u)=1$、$\sum_{i=1}^4 \pi_i(u)A_i$ 的两个对角分量以及 $\sum_{i=1}^4 \pi_i(u)\det(A_i)$ 写成矩阵形式：令
$$M := \begin{pmatrix}
1 & 1 & 1 & 1 \\
3 & 1 & -2 & 0 \\
0 & 2 & 1 & -3 \\
0 & 2 & -2 & 0
\end{pmatrix}, \qquad b := \begin{pmatrix} 1 \\ 0 \\ 0 \\ 0 \end{pmatrix}.$$
先解线性方程组 $M\theta = b$，其中 $\theta=(\theta_1,\theta_2,\theta_3,\theta_4)^\top$：
- 由第 4 行 $2\theta_2 - 2\theta_3 = 0$ 得 $\theta_2 = \theta_3$；
- 代入第 2 行 $3\theta_1 + \theta_2 - 2\theta_3 = 0$ 得 $3\theta_1 - \theta_2 = 0$，即 $\theta_2 = \theta_3 = 3\theta_1$；
- 代入第 3 行 $2\theta_2 + \theta_3 - 3\theta_4 = 0$ 得 $9\theta_1 - 3\theta_4 = 0$，即 $\theta_4 = 3\theta_1$；
- 代入第 1 行 $\theta_1 + \theta_2 + \theta_3 + \theta_4 = 1$ 得 $10\theta_1 = 1$。

上述消元过程同时证明 $\det(M)=60\ne 0$（$M$ 可逆），且方程 $M\theta=b$ 有**唯一解**
$$\pi^* = M^{-1}b = \left(\frac{1}{10},\,\frac{3}{10},\,\frac{3}{10},\,\frac{3}{10}\right)^\top.$$
对任意 $u\in\mathcal{A}$，残差向量 $r(u):=M\pi(u)-b = M(\pi(u)-\pi^*)$ 的各分量满足：
$$r_1(u) = 0, \qquad r_2(u)^2 + r_3(u)^2 = \left\|\sum_{i=1}^4 \pi_i(u)A_i\right\|_F^2 \le E(u), \qquad |r_4(u)| = \left|\sum_{i=1}^4 \pi_i(u)\det(A_i)\right| \le \frac{7}{2}\sqrt{E(u)}.$$
因此
$$\|M(\pi(u)-\pi^*)\|_2 = \|r(u)\|_2 \le \sqrt{E(u) + \frac{49}{4}E(u)} = \frac{\sqrt{53}}{2}\sqrt{E(u)},$$
两边左乘 $M^{-1}$ 得
$$\|\pi(u) - \pi^*\|_2 \le \frac{\sqrt{53}}{2}\|M^{-1}\|_2\sqrt{E(u)}.$$
故对任意满足 $E(u_j)\to e_0=0$ 的序列 $\{u_j\}\subset\mathcal{A}$，无需抽取子列即有 $\lim_{j\to\infty}\pi(u_j) = \pi^* = \left(\frac{1}{10},\frac{3}{10},\frac{3}{10},\frac{3}{10}\right)$。结合第 3 节极小化序列的存在性，该唯一极限确实可达。$\blacksquare$

---

### 3. 具体近最优位移构造及逐项验证

本节基于 $T_4$ 秩一循环给出完全显式的分片双线性位移序列 $\{u_j\}_{j=1}^\infty \subset \mathcal{A}$。

#### 3.1 $T_4$ 辅助循环与秩一分解参数

定义四个辅助对角矩阵：
$$J_1 = \operatorname{diag}(1,0),\quad J_2 = \operatorname{diag}(1,1),\quad J_3 = \operatorname{diag}(0,1),\quad J_4 = \operatorname{diag}(0,0) = 0.$$
注意 $K\cup\{J_1,J_2,J_3,J_4\}$ 中所有矩阵均为对角矩阵，且 Frobenius 范数全部不超过 $3$（$\|J_1\|_F=1$，$\|J_2\|_F=\sqrt{2}$，$\|J_3\|_F=1$，$\|J_4\|_F=0$）。验证以下四步闭合秩一凸分解循环：

1. **步骤 S1（沿 $x_2$ 层合）**：$J_4 = \dfrac{1}{4}A_4 + \dfrac{3}{4}J_3$，且 $A_4 - J_3 = \operatorname{diag}(0,-4) = (-4e_2)\otimes e_2$（参数 $\lambda_1=\frac{1}{4}$，$\alpha_1=-4$）；
2. **步骤 S2（沿 $x_1$ 层合）**：$J_3 = \dfrac{1}{3}A_3 + \dfrac{2}{3}J_2$，且 $A_3 - J_2 = \operatorname{diag}(-3,0) = (-3e_1)\otimes e_1$（参数 $\lambda_2=\frac{1}{3}$，$\alpha_2=-3$）；
3. **步骤 S3（沿 $x_2$ 层合）**：$J_2 = \dfrac{1}{2}A_2 + \dfrac{1}{2}J_1$，且 $A_2 - J_1 = \operatorname{diag}(0,2) = (2e_2)\otimes e_2$（参数 $\lambda_3=\frac{1}{2}$，$\alpha_3=2$）；
4. **步骤 S4（沿 $x_1$ 层合）**：$J_1 = \dfrac{1}{3}A_1 + \dfrac{2}{3}J_4$，且 $A_1 - J_4 = \operatorname{diag}(3,0) = (3e_1)\otimes e_1$（参数 $\lambda_4=\frac{1}{3}$，$\alpha_4=3$）。

每完成一轮 S1$\to$S2$\to$S3$\to$S4，剩余 $J_4$ 态的比例因子为 $(1-\lambda_1)(1-\lambda_2)(1-\lambda_3)(1-\lambda_4)=\frac{3}{4}\cdot\frac{2}{3}\cdot\frac{1}{2}\cdot\frac{2}{3}=\frac{1}{6}$。

#### 3.2 单步矩形局部替换引理（基本构造模块）

给定任意 $\lambda\in(0,1)$，定义 $\mathbb{R}$ 上以 $1$ 为周期的连续分片线性锯齿函数 $\sigma_\lambda : \mathbb{R}\to\mathbb{R}$：在 $[0,1]$ 上令
$$\sigma_\lambda(t) := \begin{cases}
(1-\lambda)t, & t\in[0,\lambda], \\
\lambda(1-t), & t\in[\lambda,1],
\end{cases}$$
并按周期 $1$ 延拓到 $\mathbb{R}$。易见 $\sigma_\lambda(0)=\sigma_\lambda(1)=0$，$0\le \sigma_\lambda(t)\le \lambda(1-\lambda)$ 对一切 $t\in\mathbb{R}$ 成立，且对 $t-\lfloor t\rfloor \in (0,\lambda)$ 有 $\sigma_\lambda'(t)=1-\lambda$，对 $t-\lfloor t\rfloor \in (\lambda,1)$ 有 $\sigma_\lambda'(t)=-\lambda$。

**引理（轴对齐矩形上的零边界层合扰动）.**
设开矩形 $R=(a_1,b_1)\times(a_2,b_2)\subset\Omega$ 的边长为 $L_1=b_1-a_1>0$，$L_2=b_2-a_2>0$。设对角矩阵 $J,M_+,M_-$ 满足 $\max\{\|J\|_F,\|M_+\|_F,\|M_-\|_F\}\le 3$ 及 $J=\lambda M_+ + (1-\lambda)M_-$（$\lambda\in(0,1)$），且 $M_+-M_-$ 属于下列两种情形之一：
- **情形 X**：$M_+ - M_- = \operatorname{diag}(\alpha,0)$（$\alpha\ne 0$）；
- **情形 Y**：$M_+ - M_- = \operatorname{diag}(0,\alpha)$（$\alpha\ne 0$）。

任给过渡层面积比例参数 $\tau\in(0,\frac{1}{2})$，如下显式定义局部扰动函数 $w_R : \overline{\Omega}\to\mathbb{R}^2$：

- **在情形 X 下**：取 $x_2$ 方向截断宽度 $\delta := \frac{\tau}{2}L_2$，定义梯形截断函数 $\eta_R : [a_2,b_2]\to[0,1]$ 为
  $$\eta_R(x_2) := \begin{cases}
  \dfrac{x_2-a_2}{\delta}, & x_2\in[a_2,\,a_2+\delta], \\[6pt]
  1, & x_2\in[a_2+\delta,\,b_2-\delta], \\[6pt]
  \dfrac{b_2-x_2}{\delta}, & x_2\in[b_2-\delta,\,b_2],
  \end{cases}$$
  并固定正整数
  $$N := \left\lceil \frac{2\lambda(1-\lambda)|\alpha|L_1}{\tau L_2} \right\rceil \ge 1.$$
  令 $\phi_R(x_1) := \dfrac{\alpha L_1}{N}\sigma_\lambda\!\left(\dfrac{N(x_1-a_1)}{L_1}\right)$（$x_1\in[a_1,b_1]$），定义
  $$w_R(x_1,x_2) := \begin{cases}
  \bigl(\phi_R(x_1)\eta_R(x_2),\,0\bigr)^\top, & (x_1,x_2)\in\overline{R}, \\
  (0,0)^\top, & (x_1,x_2)\in\overline{\Omega}\setminus\overline{R}.
  \end{cases}$$
  同时将 $R$ 内部划分为两族两两不交的开子矩形（$r=0,1,\dots,N-1$）：
  $$\mathcal{R}^+(R) := \left\{ \left(a_1+\frac{rL_1}{N},\,a_1+\frac{(r+\lambda)L_1}{N}\right)\times(a_2+\delta,\,b_2-\delta) \right\}_{r=0}^{N-1},$$
  $$\mathcal{R}^-(R) := \left\{ \left(a_1+\frac{(r+\lambda)L_1}{N},\,a_1+\frac{(r+1)L_1}{N}\right)\times(a_2+\delta,\,b_2-\delta) \right\}_{r=0}^{N-1},$$
  以及过渡层开集（模去有限条线段）$B(R) := R \setminus \overline{\bigcup_{Q\in\mathcal{R}^+(R)\cup\mathcal{R}^-(R)} Q}$。

- **在情形 Y 下**：将 $x_1,x_2$ 角色完全对调，取 $\delta := \frac{\tau}{2}L_1$，$\eta_R : [a_1,b_1]\to[0,1]$ 为同样的梯形截断函数，$N := \left\lceil \dfrac{2\lambda(1-\lambda)|\alpha|L_2}{\tau L_1} \right\rceil$，$\phi_R(x_2) := \dfrac{\alpha L_2}{N}\sigma_\lambda\!\left(\dfrac{N(x_2-a_2)}{L_2}\right)$，并在 $\overline{R}$ 上令 $w_R(x_1,x_2):=\bigl(0,\,\eta_R(x_1)\phi_R(x_2)\bigr)^\top$（在 $\overline{\Omega}\setminus\overline{R}$ 上取 $0$），相应定义子矩形族 $\mathcal{R}^+(R),\mathcal{R}^-(R)$ 与过渡层 $B(R)$。

则 $w_R$ 满足以下四条性质：
1. **正则性与零边界延拓**：$w_R \in W^{1,\infty}(\Omega;\mathbb{R}^2)$，在 $\overline{\Omega}\setminus R$（含 $\partial R$ 与 $\partial\Omega$）上恒为 $0$；
2. **核心子矩形上的精确常梯度**：在每个 $Q\in\mathcal{R}^+(R)$ 上恒有 $J+\nabla w_R(x) = M_+$；在每个 $Q\in\mathcal{R}^-(R)$ 上恒有 $J+\nabla w_R(x) = M_-$；
3. **测度精确分配**：
   $$\sum_{Q\in\mathcal{R}^+(R)} |Q| = \lambda(1-\tau)|R|,\qquad \sum_{Q\in\mathcal{R}^-(R)} |Q| = (1-\lambda)(1-\tau)|R|,\qquad |B(R)| = \tau|R|;$$
4. **一致梯度范数上界**：在 $R$ 上几乎处处成立 $\|J + \nabla w_R(x)\|_F \le \sqrt{10} < 4$。

**引理证明.** 仅证情形 X（情形 Y 将坐标下标 $1,2$ 对调即可）。
1. 在 $\overline{R}$ 上，$\phi_R$ 与 $\eta_R$ 均为连续分片线性函数，故乘积 $\phi_R(x_1)\eta_R(x_2)$ 在 $\overline{R}$ 上连续且在有限网格上分片双线性（从而 Lipschitz 连续）。在边界 $\partial R$ 上：当 $x_1\in\{a_1,b_1\}$ 时，$\frac{N(x_1-a_1)}{L_1}\in\{0,N\}\subset\mathbb{Z}$，由 $\sigma_\lambda$ 的周期性与零点性质知 $\phi_R(x_1)=0$；当 $x_2\in\{a_2,b_2\}$ 时，$\eta_R(x_2)=0$。故 $w_R|_{\partial R}\equiv 0$，在 $\overline{\Omega}\setminus\overline{R}$ 上零延拓后仍保持全局 Lipschitz 连续，即 $w_R\in W^{1,\infty}(\Omega;\mathbb{R}^2)$ 且在 $\overline{\Omega}\setminus R$ 上恒为 $0$。
2. 在任意 $Q\in\mathcal{R}^+(R)$ 上，$\eta_R(x_2)\equiv 1$（从而 $\eta_R'(x_2)=0$）且 $\phi_R'(x_1)=(1-\lambda)\alpha$，于是
   $$J + \nabla w_R(x) = J + \begin{pmatrix}(1-\lambda)\alpha & 0\\ 0 & 0\end{pmatrix} = J + (1-\lambda)(M_+ - M_-) = M_+.$$
   同理，在任意 $Q\in\mathcal{R}^-(R)$ 上，$\eta_R\equiv 1$ 且 $\phi_R'(x_1)=-\lambda\alpha$，故 $J+\nabla w_R(x) = J - \lambda(M_+ - M_-) = M_-$。
3. $[a_2+\delta,b_2-\delta]$ 的长度为 $L_2-2\delta=(1-\tau)L_2$；$N$ 个左子区间的总长度为 $N\cdot\frac{\lambda L_1}{N}=\lambda L_1$，右子区间总长度为 $(1-\lambda)L_1$。相乘即得 $\mathcal{R}^+(R)$、$\mathcal{R}^-(R)$ 的总测度分别为 $\lambda(1-\tau)|R|$、$(1-\lambda)(1-\tau)|R|$，余集 $B(R)$ 的测度为 $\tau|R|$。
4. 在 $\mathcal{R}^+(R)\cup\mathcal{R}^-(R)$ 上 $\|J+\nabla w_R\|_F\in\{\|M_+\|_F,\|M_-\|_F\}\le 3<\sqrt{10}$。对几乎处处的 $x=(x_1,x_2)\in B(R)$，有
   $$J + \nabla w_R(x) = \underbrace{\bigl(J + \eta_R(x_2)\phi_R'(x_1)\,e_1\otimes e_1\bigr)}_{=:D(x)} + \phi_R(x_1)\eta_R'(x_2)\,e_1\otimes e_2.$$
   由于 $D(x)$ 为对角矩阵，而 $e_1\otimes e_2$ 仅有 $(1,2)$ 非对角元，两者在 Frobenius 内积下正交：
   $$\|J + \nabla w_R(x)\|_F^2 = \|D(x)\|_F^2 + |\phi_R(x_1)\eta_R'(x_2)|^2.$$
   当 $\phi_R'(x_1)=(1-\lambda)\alpha$ 时，$D(x)=(1-\eta_R(x_2))J + \eta_R(x_2)M_+$；当 $\phi_R'(x_1)=-\lambda\alpha$ 时，$D(x)=(1-\eta_R(x_2))J + \eta_R(x_2)M_-$。因 $\eta_R(x_2)\in[0,1]$，由范数凸性得 $\|D(x)\|_F\le \max\{\|J\|_F,\|M_+\|_F,\|M_-\|_F\}\le 3$。同时由 $|\sigma_\lambda|\le\lambda(1-\lambda)$、$|\eta_R'|\le \frac{1}{\delta}=\frac{2}{\tau L_2}$ 及 $N$ 的选取，有
   $$|\phi_R(x_1)\eta_R'(x_2)| \le \frac{|\alpha|L_1}{N}\lambda(1-\lambda)\cdot\frac{2}{\tau L_2} \le 1.$$
   故 $\|J+\nabla w_R(x)\|_F \le \sqrt{3^2+1^2} = \sqrt{10} < 4$。$\blacksquare$

#### 3.3 递归构造近最优位移序列 $\{u_j\}_{j=1}^\infty$

对每个正整数 $j\ge 1$，我们执行 $j$ 轮完整的四步 $T_4$ 循环（共 $4j$ 个单步，$m=1,2,\dots,4j$），固定各步过渡层比例参数为
$$\tau_m := 2^{-j-m} \in \left(0,\frac{1}{4}\right], \qquad m=1,2,\dots,4j.$$
按如下有限步归纳构造位移 $v^{(0)},v^{(1)},\dots,v^{(4j)}$ 与两两不交的活跃开矩形族 $\mathcal{R}_J^{(m)}$：

- **初值（$m=0$）**：令 $v^{(0)}(x)\equiv (0,0)^\top$，初始活跃矩形族为 $\mathcal{R}_J^{(0)} := \{\Omega\} = \{(0,1)^2\}$。此时在 $\Omega$ 上恒有 $\nabla v^{(0)} \equiv J_4 = 0$。
- **第 $m$ 步（$1\le m\le 4j$）**：记 $m \equiv s \pmod 4$（$s\in\{1,2,3,4\}$），对应第 3.1 节中的步骤 $\text{S}s$：
  - $s=1$：$J=J_4$，$M_+=A_4$，$M_-=J_3$，$\lambda=\frac{1}{4}$，$\alpha=-4$（情形 Y）；
  - $s=2$：$J=J_3$，$M_+=A_3$，$M_-=J_2$，$\lambda=\frac{1}{3}$，$\alpha=-3$（情形 X）；
  - $s=3$：$J=J_2$，$M_+=A_2$，$M_-=J_1$，$\lambda=\frac{1}{2}$，$\alpha=2$（情形 Y）；
  - $s=4$：$J=J_1$，$M_+=A_1$，$M_-=J_4$，$\lambda=\frac{1}{3}$，$\alpha=3$（情形 X）。

  由归纳假设，在每个开矩形 $R\in\mathcal{R}_J^{(m-1)}$ 上恒有 $\nabla v^{(m-1)}(x) = J$。对每个 $R\in\mathcal{R}_J^{(m-1)}$ 以参数 $\tau=\tau_m$ 应用上述局部替换引理得到局部扰动 $w_R$，令
  $$v^{(m)}(x) := v^{(m-1)}(x) + \sum_{R\in\mathcal{R}_J^{(m-1)}} w_R(x), \qquad \mathcal{R}_J^{(m)} := \bigcup_{R\in\mathcal{R}_J^{(m-1)}} \mathcal{R}^-(R).$$
  同时记录本步生成的目标井子矩形族 $\mathcal{R}_A^{(m)} := \bigcup_{R\in\mathcal{R}_J^{(m-1)}} \mathcal{R}^+(R)$（其上 $\nabla v^{(m)}\equiv M_+ = A_{5-s}$）以及本步过渡层 $B_m := \bigcup_{R\in\mathcal{R}_J^{(m-1)}} B(R)$。

完成 $4j$ 步后，定义第 $j$ 个近最优位移为
$$u_j(x) := v^{(4j)}(x) = \sum_{m=1}^{4j} \sum_{R\in\mathcal{R}_J^{(m-1)}} w_R(x), \qquad x\in\overline{\Omega}.$$

#### 3.4 零边界、统一梯度上界与能量估计的严格验证

**(1) 验证 $u_j \in W^{1,\infty}(\Omega;\mathbb{R}^2)$ 与零边界条件 $u_j|_{\partial\Omega}=0$。**
对固定的 $j\ge 1$，每一步 $\mathcal{R}_J^{(m-1)}$ 均为**有限个**两两不交的开子矩形（由归纳易见 $|\mathcal{R}_J^{(m)}|=N_1 N_2\cdots N_m < \infty$）。由引理性质 1，每一项 $w_R \in W^{1,\infty}(\Omega;\mathbb{R}^2)$ 且在 $\partial\Omega$ 上恒为 $0$。作为有限个属于 $W^{1,\infty}(\Omega;\mathbb{R}^2)$ 且在 $\partial\Omega$ 上为零的函数之和，必有 $u_j \in W^{1,\infty}(\Omega;\mathbb{R}^2)$ 且在 $\partial\Omega$ 上逐点成立 $u_j(x)=0$。

**(2) 验证统一梯度上界 $\operatorname{ess\,sup}_\Omega\|\nabla u_j\|_F \le 4$。**
记 $\Omega_J^{(m)} := \bigcup_{R\in\mathcal{R}_J^{(m)}} R$，并记四相核心开集为
$$\Omega_{A_{5-s}}^{(4j)} := \bigcup_{\substack{1\le m\le 4j \\ m\equiv s\!\!\pmod 4}} \bigcup_{Q\in\mathcal{R}_A^{(m)}} Q \qquad (s=1,2,3,4).$$
根据构造，对任意 $m'>m$，一切 $R'\in\mathcal{R}_J^{(m'-1)}$ 均满足 $R'\subset \Omega_J^{(m)}$，而 $\Omega_J^{(m)}$ 与第 $1,\dots,m$ 步已经生成的井区域及过渡层 $B_1,\dots,B_m$ 两两不交；又 $w_{R'}$ 在 $R'$ 外部恒为 $0$，故第 $m$ 步之后的一切扰动在 $\Omega\setminus\overline{\Omega_J^{(m)}}$ 上恒等于 $0$（梯度几乎处处不发生任何累加！）。
由于有限个矩形边界的并集在 $\mathbb{R}^2$ 中二维 Lebesgue 测度为 $0$，$\Omega$ 模去一个零测集后被不交分解为：
$$\Omega \stackrel{\text{a.e.}}{=} \left(\bigsqcup_{i=1}^4 \Omega_{A_i}^{(4j)}\right) \sqcup \Omega_J^{(4j)} \sqcup \left(\bigsqcup_{m=1}^{4j} B_m\right).$$
在各部分上逐块检验 $\nabla u_j(x)$：
- 在 $\Omega_{A_i}^{(4j)}$（$i=1,2,3,4$）上，$\nabla u_j(x) \equiv A_i$，故 $\|\nabla u_j(x)\|_F = \|A_i\|_F \le 3 < 4$；
- 在剩余集 $\Omega_J^{(4j)}$ 上，$\nabla u_j(x) \equiv J_4 = 0$，故 $\|\nabla u_j(x)\|_F = 0 < 4$；
- 在每个过渡层 $B_m$（$1\le m\le 4j$）上，对包含该连通分支的唯一 $R\in\mathcal{R}_J^{(m-1)}$ 有 $\nabla u_j(x) = \nabla v^{(m)}(x) = J + \nabla w_R(x)$，由引理性质 4 知几乎处处有 $\|\nabla u_j(x)\|_F \le \sqrt{10} < 4$。

综上，$\operatorname{ess\,sup}_\Omega\|\nabla u_j\|_F \le \sqrt{10} < 4$，故对一切 $j\ge 1$ 严格有 $u_j\in\mathcal{A}$。

**(3) 验证能量估计 $E(u_j)\to 0$（及相体积分数核验）。**
先计算各区域测度：
- 由引理性质 3，每一步过渡层测度满足 $|B_m| = \tau_m |\Omega_J^{(m-1)}| \le \tau_m = 2^{-j-m}$，于是全部过渡层总测度满足
  $$\sum_{m=1}^{4j} |B_m| \le \sum_{m=1}^{4j} 2^{-j-m} < 2^{-j}.$$
- 每经过一轮四步循环，$\Omega_J$ 的测度乘以因子 $\frac{3}{4}(1-\tau_{4c+1})\cdot\frac{2}{3}(1-\tau_{4c+2})\cdot\frac{1}{2}(1-\tau_{4c+3})\cdot\frac{2}{3}(1-\tau_{4c+4}) < \frac{1}{6}$，故经过 $j$ 轮循环后：
  $$|\Omega_J^{(4j)}| = 6^{-j}\prod_{m=1}^{4j}(1-\tau_m) \le 6^{-j}.$$

再逐块估计能量被积函数 $g_j(x):=\min_{1\le i\le 4}\|\nabla u_j(x)-A_i\|_F^2$：
- 在 $\bigsqcup_{i=1}^4 \Omega_{A_i}^{(4j)}$ 上，$\nabla u_j(x)\in K$，故 $g_j(x) = 0$；
- 在 $\Omega_J^{(4j)}$ 上，$\nabla u_j(x)=0$，故 $g_j(x) = \min_{1\le i\le 4}\|A_i\|_F^2 = \|A_2\|_F^2 = 5$；
- 在 $\bigsqcup_{m=1}^{4j} B_m$ 上几乎处处有 $\|\nabla u_j(x)\|_F\le \sqrt{10}$，与 $A_2$（$\|A_2\|_F=\sqrt{5}$）比较并用三角不等式得
  $$g_j(x) \le \|\nabla u_j(x)-A_2\|_F^2 \le \bigl(\|\nabla u_j(x)\|_F + \|A_2\|_F\bigr)^2 \le (\sqrt{10}+\sqrt{5})^2 = 15 + 10\sqrt{2} < 30.$$

积分合并即得显式能量上界：
$$0 < E(u_j) = \int_{\Omega_J^{(4j)}} 5\,dx + \sum_{m=1}^{4j}\int_{B_m} g_j(x)\,dx \le 5|\Omega_J^{(4j)}| + (15+10\sqrt{2})\sum_{m=1}^{4j}|B_m| < 5\cdot 6^{-j} + 30\cdot 2^{-j} \xrightarrow{j\to\infty} 0.$$

最后也可从构造直接核验相体积分数：在第 $c$ 轮循环（$c=0,1,\dots,j-1$）中，利用 $1-2^{-j} < \prod_{m=1}^{4j}(1-\tau_m) < 1$，并入 $\Omega_{A_4}^{(4j)},\Omega_{A_3}^{(4j)},\Omega_{A_2}^{(4j)},\Omega_{A_1}^{(4j)}$ 的精确面积渐近等于 $\frac{1}{4}\cdot 6^{-c},\frac{1}{4}\cdot 6^{-c},\frac{1}{4}\cdot 6^{-c},\frac{1}{12}\cdot 6^{-c}$。对等比级数 $\sum_{c=0}^{j-1} 6^{-c} = \frac{6}{5}(1-6^{-j})$ 求和，并注意到 $\Omega_{A_i}^{(4j)}$ 上的点唯一分配给 $A_i$ 且余集测度 $|\Omega\setminus\bigsqcup_{i=1}^4\Omega_{A_i}^{(4j)}|<6^{-j}+2^{-j}\to 0$，立得
$$\lim_{j\to\infty}\bigl(\pi_1(u_j),\pi_2(u_j),\pi_3(u_j),\pi_4(u_j)\bigr) = \frac{6}{5}\left(\frac{1}{12},\,\frac{1}{4},\,\frac{1}{4},\,\frac{1}{4}\right) = \left(\frac{1}{10},\,\frac{3}{10},\,\frac{3}{10},\,\frac{3}{10}\right),$$
与第 2 节的一般唯一性定理完全一致。$\blacksquare$
