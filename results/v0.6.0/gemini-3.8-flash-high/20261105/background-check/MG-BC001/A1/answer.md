下面给出该四相材料零边界单元问题的完整数学证明与构造。

---

### 一、 核心结论概述

对于所给的四个对角应变井：
$$A_1 = \operatorname{diag}(3,0),\quad A_2 = \operatorname{diag}(1,2),\quad A_3 = \operatorname{diag}(-2,1),\quad A_4 = \operatorname{diag}(0,-3),$$
允许位移类为：
$$\mathcal{A} = \left\{u \in W^{1,\infty}(\Omega;\mathbb{R}^2) : u|_{\partial\Omega} = 0,\ \operatorname{ess\,sup}_\Omega \|\nabla u\|_F \le 4\right\},\quad \Omega = (0,1)^2,$$
能量定义为 $E(u) = \int_\Omega \min_{1 \le i \le 4} \|\nabla u(x) - A_i\|_F^2 \,dx$，$e_0 = \inf_{u \in \mathcal{A}} E(u)$。

前期的相容性计算虽然正确地指出了六个两井之差的行列式均非零（即任意两井之间均无直接的秩一连接，二相层合无法发生），但**二相刚性不能直接推广到四相系统**。这四个井恰好构成了变分法与微结构理论中著名的 **Tartar $T_4$ 构型**（Tartar 1979 / Šverák 1993 / Müller 1999）：虽然井与井之间没有秩一连接（秩一凸包 $K^{rc} = K$），但通过四个辅助矩阵可构成一个首尾闭合的循环相容层合链，从而 $0$ 属于其拟凸包（$0 \in K^{qc}$）。

由此得出本题的全部结论：
1. **单元能的精确值为 $e_0 = 0$**；该极小值在 $\mathcal{A}$ 中**不可达**（不存在极小元）。
2. 对任意满足 $E(u_j) \to e_0$ 的序列，相体积分数向量 $(\pi_1(u_j), \dots, \pi_4(u_j))$ **必然收敛到同一个向量**，唯一的极限为：
   $$\lim_{j \to \infty} (\pi_1(u_j), \pi_2(u_j), \pi_3(u_j), \pi_4(u_j)) = \left(\frac{1}{10},\, \frac{3}{10},\, \frac{3}{10},\, \frac{3}{10}\right) = (0.1, 0.3, 0.3, 0.3).$$
3. 可显式构造具细微尺度循环层合与边界层截断的近最优位移场，严格满足零边界条件、统一梯度界 $\|\nabla u\|_F \le 3 + o(1) \le 4$，并使能量任意接近 $0$。

---

### 二、 任务一：$e_0$ 的精确值与不可达性证明

#### 1. 精确值 $e_0 = 0$
由于对任意 $u \in \mathcal{A}$，被积函数为非负距离平方，故显然 $E(u) \ge 0$，从而 $e_0 \ge 0$。
另一方面，由任务三中给出的显式位移场构造，对任意 $\varepsilon > 0$，存在 $u_\varepsilon \in \mathcal{A}$ 使得 $E(u_\varepsilon) < \varepsilon$。
因此：
$$e_0 = \inf_{u \in \mathcal{A}} E(u) = 0.$$

#### 2. 不可达性证明（不存在 $u \in \mathcal{A}$ 使得 $E(u) = 0$）
用反证法。假设存在 $u \in \mathcal{A}$ 达到极小值，即 $E(u) = 0$。

因为被积函数 $\min_{1 \le i \le 4} \|\nabla u(x) - A_i\|_F^2 \ge 0$，积分值为 $0$ 意味着对几乎处处的 $x \in \Omega$：
$$\nabla u(x) \in K = \{A_1, A_2, A_3, A_4\}.$$

注意到四个应变井 $A_1, A_2, A_3, A_4$ 全部是对角矩阵：
$$A_i = \begin{pmatrix} a_i & 0 \\ 0 & b_i \end{pmatrix},\quad i=1,2,3,4.$$
将其写成分量：设 $u(x) = (u_1(x_1, x_2), u_2(x_1, x_2))$，则梯度的非对角元为：
$$\partial_2 u_1(x_1, x_2) = 0 \quad \text{a.e.},\qquad \partial_1 u_2(x_1, x_2) = 0 \quad \text{a.e.}$$
由于区域 $\Omega = (0,1)^2$ 是连通开集，这表明：
- $u_1$ 几乎处处仅依赖于 $x_1$，即存在一维局部 Lipschitz 函数 $f$ 使得 $u_1(x_1, x_2) = f(x_1)$ a.e.；
- $u_2$ 几乎处处仅依赖于 $x_2$，即存在一维局部 Lipschitz 函数 $g$ 使得 $u_2(x_1, x_2) = g(x_2)$ a.e.。

因此，梯度的形式必为：
$$\nabla u(x_1, x_2) = \begin{pmatrix} f'(x_1) & 0 \\ 0 & g'(x_2) \end{pmatrix} \quad \text{a.e. in } \Omega.$$
对几乎处处的 $(x_1, x_2) \in (0,1)^2$，必须满足：
$$(f'(x_1), g'(x_2)) \in \{(3,0), (1,2), (-2,1), (0,-3)\}.$$

根据 Fubini 定理，固定一个使得 $f'(x_1)$ 存在的横坐标 $x_1$。
观察四个井的第一主应变（第一个对角元）：
$$a_1 = 3,\quad a_2 = 1,\quad a_3 = -2,\quad a_4 = 0.$$
这四个数值**互不相同**。
因此，对于选定的 $x_1$，$f'(x_1)$ 最多只能与集合 $\{3, 1, -2, 0\}$ 中的**某一个数**相等。
这就意味着在集合 $K$ 中，**至多只有一个点**的第一个分量等于 $f'(x_1)$。
从而对应几乎处处所有的 $x_2$，$g'(x_2)$ 只能取由该唯一匹配确定的那个常数值，不能随 $x_2$ 变动。
同理，反过来对称可得 $f'(x_1)$ 也必须为常数。

故 $\nabla u(x)$ 在 $\Omega$ 上几乎处处为常数矩阵：
$$\nabla u(x) \equiv C \in K \quad \text{a.e.}$$
由于 $u \in W^{1,\infty}(\Omega;\mathbb{R}^2)$ 且在 $\partial\Omega$ 上的迹为 $0$，由高斯散度定理（或分部积分）：
$$\int_\Omega \nabla u(x) \,dx = \int_{\partial\Omega} u \otimes \nu \,d\sigma = 0.$$
因此该常数矩阵必须为：
$$C = \frac{1}{|\Omega|} \int_\Omega \nabla u(x) \,dx = 0.$$
然而，零矩阵 $0 \notin K$（四个井的 Frobenius 范数分别为 $3, \sqrt{5}, \sqrt{5}, 3$，均不为 $0$）。这产生矛盾！

故不存在任何 $u \in \mathcal{A}$ 能使 $E(u) = 0$。**极小值 $e_0 = 0$ 不可达。**

---

### 三、 任务二：极小化序列相体积分数的唯一极限证明

设 $\{u_j\}_{j=1}^\infty \subset \mathcal{A}$ 为任意满足 $E(u_j) \to 0$ 的序列。我们将证明其相体积分数向量 $(\pi_1(u_j), \dots, \pi_4(u_j))$ 必收敛于唯一向量 $(0.1, 0.3, 0.3, 0.3)$。

#### 1. 分区与阶梯矩阵场近似
按最近井规则，对每个 $j$，$\Omega$ 被划分为四个互不相交的可测集：
$$E_i^{(j)} = \left\{x \in \Omega : x \text{ 被分配给 } A_i\right\},\quad i=1,2,3,4.$$
由定义可知：
$$\pi_i(u_j) = |E_i^{(j)}|,\quad \sum_{i=1}^4 \pi_i(u_j) = |\Omega| = 1.$$
定义分片常值矩阵场 $V_j(x) = \sum_{i=1}^4 A_i \mathbf{1}_{E_i^{(j)}}(x)$。根据能量定义：
$$\|\nabla u_j - V_j\|_{L^2(\Omega;\mathbb{R}^{2\times 2})}^2 = \sum_{i=1}^4 \int_{E_i^{(j)}} \|\nabla u_j(x) - A_i\|_F^2 \,dx = E(u_j) \to 0.$$
根据容许集条件，$\operatorname{ess\,sup}_\Omega \|\nabla u_j\|_F \le 4$；同时对所有的井，$\|A_i\|_F \le 3 < 4$。因此 $\nabla u_j$ 与 $V_j$ 在 $L^\infty(\Omega)$ 中均被常数 $4$ 统一控制。

#### 2. 平均梯度约束（零边界条件）
由 $u_j \in W_0^{1,\infty}(\Omega;\mathbb{R}^2)$，平均梯度恒等于零：
$$\int_\Omega \nabla u_j(x) \,dx = 0.$$
利用 Cauchy-Schwarz 不等式：
$$\left\| \int_\Omega V_j(x) \,dx \right\|_F = \left\| \int_\Omega (V_j - \nabla u_j) \,dx \right\|_F \le \|\nabla u_j - V_j\|_{L^1} \le \|\nabla u_j - V_j\|_{L^2} \to 0.$$
而 $V_j(x)$ 的积分为：
$$\int_\Omega V_j(x) \,dx = \sum_{i=1}^4 \pi_i(u_j) A_i = \operatorname{diag}\left(3\pi_1(u_j) + \pi_2(u_j) - 2\pi_3(u_j), \quad 2\pi_2(u_j) + \pi_3(u_j) - 3\pi_4(u_j)\right).$$
令 $j \to \infty$，得到两个渐近方程：
$$\lim_{j \to \infty} \left[ 3\pi_1(u_j) + \pi_2(u_j) - 2\pi_3(u_j) \right] = 0,$$
$$\lim_{j \to \infty} \left[ 2\pi_2(u_j) + \pi_3(u_j) - 3\pi_4(u_j) \right] = 0.$$

#### 3. 行列式约束（零拉格朗日量 Null-Lagrangian）
在二维空间中，行列式 $\det(\nabla u)$ 具有发散形式：
$$\det(\nabla u) = \partial_1(u_1 \partial_2 u_2) - \partial_2(u_1 \partial_1 u_2).$$
由于 $u_j|_{\partial\Omega} = 0$，由散度定理，**对任意 $u_j \in \mathcal{A}$ 均严格有**：
$$\int_\Omega \det(\nabla u_j(x)) \,dx = 0.$$
注意到映射 $M \mapsto \det(M)$ 在有界球 $B_F(0,4)$ 上是局部 Lipschitz 的：
$$|\det(M) - \det(N)| \le C \|M - N\|_F,\quad \forall M, N \in B_F(0,4).$$
从而：
$$\left| \int_\Omega \det(V_j(x)) \,dx - \int_\Omega \det(\nabla u_j(x)) \,dx \right| \le C \int_\Omega \|\nabla u_j - V_j\|_F \,dx \le C \|\nabla u_j - V_j\|_{L^2} \to 0.$$
因此：
$$\lim_{j \to \infty} \int_\Omega \det(V_j(x)) \,dx = 0.$$
将 $V_j$ 在各子集上的取值代入：
$$\int_\Omega \det(V_j(x)) \,dx = \sum_{i=1}^4 \pi_i(u_j) \det(A_i).$$
直接计算四个井的行列式：
$$\det(A_1) = 3 \times 0 = 0,$$
$$\det(A_2) = 1 \times 2 = 2,$$
$$\det(A_3) = -2 \times 1 = -2,$$
$$\det(A_4) = 0 \times (-3) = 0.$$
于是：
$$\int_\Omega \det(V_j(x)) \,dx = 2 \pi_2(u_j) - 2 \pi_3(u_j) \to 0 \implies \lim_{j \to \infty} [\pi_2(u_j) - \pi_3(u_j)] = 0.$$

#### 4. 极限方程组的唯一解
由于序列 $(\pi_1(u_j), \dots, \pi_4(u_j))$ 包含在紧集 $\Delta_4 = \{\lambda \in \mathbb{R}^4 : \lambda_i \ge 0, \sum \lambda_i = 1\}$ 中，任何子列极限 $\lambda = (\lambda_1, \lambda_2, \lambda_3, \lambda_4)^T$ 都必须满足联立线性方程组：
$$\begin{cases}
\lambda_1 + \lambda_2 + \lambda_3 + \lambda_4 = 1 & (\text{总体积为 } 1) \\
3\lambda_1 + \lambda_2 - 2\lambda_3 = 0 & (\text{平均梯度 } (1,1) \text{ 元为 } 0) \\
2\lambda_2 + \lambda_3 - 3\lambda_4 = 0 & (\text{平均梯度 } (2,2) \text{ 元为 } 0) \\
\lambda_2 - \lambda_3 = 0 & (\text{平均行列式为 } 0)
\end{cases}$$
写成矩阵形式 $M \lambda = b$：
$$M = \begin{pmatrix} 1 & 1 & 1 & 1 \\ 3 & 1 & -2 & 0 \\ 0 & 2 & 1 & -3 \\ 0 & 1 & -1 & 0 \end{pmatrix},\quad b = \begin{pmatrix} 1 \\ 0 \\ 0 \\ 0 \end{pmatrix}.$$
计算系数矩阵的行列式：
$$\det(M) = 1 \cdot \begin{vmatrix} 1 & -2 & 0 \\ 2 & 1 & -3 \\ 1 & -1 & 0 \end{vmatrix} - 3 \cdot \begin{vmatrix} 1 & 1 & 1 \\ 2 & 1 & -3 \\ 1 & -1 & 0 \end{vmatrix}.$$
对第一个小行列式按第三列展开：
$$-(-3) \cdot [1(-1) - (-2)(1)] = 3(1) = 3.$$
对第二个小行列式：
$$1(0 - (-3)) - 1(0 - (-3)) + 1(-2 - 1) = 3 - 3 - 3 = -3.$$
从而：
$$\det(M) = 3 - 3(-3) = 12 \ne 0.$$
矩阵 $M$ 严格非奇异，解唯一。代入验证求解：
由第 4 式，$\lambda_3 = \lambda_2$；
代入第 2 式：$3\lambda_1 + \lambda_2 - 2\lambda_2 = 0 \implies 3\lambda_1 = \lambda_2 \implies \lambda_1 = \frac{1}{3}\lambda_2$；
代入第 3 式：$2\lambda_2 + \lambda_2 - 3\lambda_4 = 0 \implies 3\lambda_4 = 3\lambda_2 \implies \lambda_4 = \lambda_2$；
代入第 1 式：
$$\frac{1}{3}\lambda_2 + \lambda_2 + \lambda_2 + \lambda_2 = 1 \implies \frac{10}{3}\lambda_2 = 1 \implies \lambda_2 = \frac{3}{10}.$$
从而求得唯一的极限向量：
$$\lambda_1 = \frac{1}{10} = 0.1,\quad \lambda_2 = \frac{3}{10} = 0.3,\quad \lambda_3 = \frac{3}{10} = 0.3,\quad \lambda_4 = \frac{3}{10} = 0.3.$$
由于紧集中每个收敛子列均收敛到该同一点，全序列必然收敛到 $(0.1, 0.3, 0.3, 0.3)$。**不存在其他极限。**

---

### 四、 任务三：近最优位移的具体显式构造与验证

我们构造显式的近最优位移序列 $u^{(k)} \in \mathcal{A}$，使得当 $k \to \infty$ 时 $E(u^{(k)}) \to 0$。

#### 1. $T_4$ 构型的循环相容几何
引入四个辅助对角矩阵：
$$P_1 = \operatorname{diag}(0,0),\quad P_2 = \operatorname{diag}(1,0),\quad P_3 = \operatorname{diag}(1,1),\quad P_4 = \operatorname{diag}(0,1).$$
注意到 $P_1 = 0$ 正好对应零边界条件下的平庸梯度。

这四个辅助矩阵与四个井之间存在精确的**秩一凸分解环路**（全部沿坐标轴方向）：
1. **从 $P_1$ 到 $\{A_4, P_4\}$：**
   $$P_1 = \frac{1}{4} A_4 + \frac{3}{4} P_4,\quad P_4 - A_4 = \operatorname{diag}(0, 4) = \begin{pmatrix} 0 \\ 4 \end{pmatrix} \otimes e_2 \quad (\text{法向 } e_2=(0,1))$$
2. **从 $P_4$ 到 $\{A_3, P_3\}$：**
   $$P_4 = \frac{1}{3} A_3 + \frac{2}{3} P_3,\quad P_3 - A_3 = \operatorname{diag}(3, 0) = \begin{pmatrix} 3 \\ 0 \end{pmatrix} \otimes e_1 \quad (\text{法向 } e_1=(1,0))$$
3. **从 $P_3$ 到 $\{A_2, P_2\}$：**
   $$P_3 = \frac{1}{2} A_2 + \frac{1}{2} P_2,\quad A_2 - P_2 = \operatorname{diag}(0, 2) = \begin{pmatrix} 0 \\ 2 \end{pmatrix} \otimes e_2 \quad (\text{法向 } e_2=(0,1))$$
4. **从 $P_2$ 到 $\{A_1, P_1\}$：**
   $$P_2 = \frac{1}{3} A_1 + \frac{2}{3} P_1,\quad A_1 - P_1 = \operatorname{diag}(3, 0) = \begin{pmatrix} 3 \\ 0 \end{pmatrix} \otimes e_1 \quad (\text{法向 } e_1=(1,0))$$

**体积分数几何收缩机制：**
在一个完整循环后，未转化（仍处于 $P_1$ 态）的体积比率为：
$$\rho = \frac{3}{4} \times \frac{2}{3} \times \frac{1}{2} \times \frac{2}{3} = \frac{1}{6}.$$
在一个周期内生成的各井体积分数分别为：
- 相 $A_4$：$\frac{1}{4}$；
- 相 $A_3$：$\frac{3}{4} \times \frac{1}{3} = \frac{1}{4}$；
- 相 $A_2$：$\frac{3}{4} \times \frac{2}{3} \times \frac{1}{2} = \frac{1}{4}$；
- 相 $A_1$：$\frac{3}{4} \times \frac{2}{3} \times \frac{1}{2} \times \frac{1}{3} = \frac{1}{12}$；
- 剩余 $P_1$：$\frac{1}{6}$。
对剩余的 $P_1$ 区域自相似递归迭代 $k$ 次，未转化为井的区域测度指数衰减为 $(1/6)^k$。
各相累积占有的体积分数比值为：
$$|A_1| : |A_2| : |A_3| : |A_4| = \frac{1}{12} : \frac{1}{4} : \frac{1}{4} : \frac{1}{4} = 1 : 3 : 3 : 3,$$
经归一化即为 $(0.1, 0.3, 0.3, 0.3)$。

#### 2. 显式位移场函数构造
定义标准周期一维分段线性剖面函数 $h_t: \mathbb{R} \to \mathbb{R}$（以 $1$ 为周期，$t \in (0,1)$）：
$$h_t(s) = \begin{cases} (1-t)s, & 0 \le s < t \\ -t(s-1), & t \le s < 1 \end{cases},\quad s \in [0,1).$$
其导数几乎处处为：在 $(0,t)$ 上为 $1-t$，在 $(t,1)$ 上为 $-t$。且 $|h_t(s)| \le t(1-t) \le \frac{1}{4}$。

若某区域原本梯度为 $M = (1-t)A + tB$，且 $B - A = a \otimes n$（$|n|=1$），则位移修正项定义为：
$$w(x) = M x + \varepsilon h_t\left(\frac{x \cdot n}{\varepsilon}\right) a.$$
其梯度满足：
$$\nabla w(x) = M + h_t'\left(\frac{x \cdot n}{\varepsilon}\right) a \otimes n = \begin{cases} M + (1-t)(B-A) = B, & \text{测度占比 } t \\ M - t(B-A) = A, & \text{测度占比 } 1-t \end{cases}.$$
且位移微扰满足 $\|w(x) - M x\|_\infty \le \frac{1}{4} \varepsilon |a|$。

##### 单周期内部四层层合构造
设当前区域的初始梯度为 $P_1 = 0$：
1. **第 1 层（$P_1 \to \{A_4, P_4\}$）：**
   法向为 $e_2$，$t_1 = 3/4$，$a_1 = (0, 4)^T$。选取特征尺度 $\varepsilon_1 > 0$：
   $$v_1(x) = \varepsilon_1 h_{3/4}\left(\frac{x_2}{\varepsilon_1}\right) \begin{pmatrix} 0 \\ 4 \end{pmatrix}.$$
   在占比 $1/4$ 的水平条带上 $\nabla v_1 = A_4$；在占比 $3/4$ 的水平条带 $S_{P_4}$ 上 $\nabla v_1 = P_4$。
2. **第 2 层（$P_4 \to \{A_3, P_3\}$）：**
   在条带 $S_{P_4}$ 内，引入光滑截断函数 $\psi_1(x_2)$，在条带内部为 $1$，并在边界层 $\delta_1 \ll \varepsilon_1$ 内平滑过渡到 $0$（满足 $|\psi_1'| \le C/\delta_1$）。
   选取极细尺度 $\varepsilon_2 \ll \delta_1$。叠加修正：
   $$v_2(x) = v_1(x) + \psi_1(x_2) \varepsilon_2 h_{2/3}\left(\frac{x_1}{\varepsilon_2}\right) \begin{pmatrix} 3 \\ 0 \end{pmatrix}.$$
   在 $\psi_1=1$ 的主区域上，梯度沿坚直条带精确分裂为 $A_3$（占比 $1/3$）与 $P_3$（占比 $2/3$）。因截断产生的附加交叉梯度项为：
   $$\|\psi_1'(x_2) \varepsilon_2 h_{2/3} a_2\| \le C \frac{\varepsilon_2}{\delta_1} \to 0.$$
3. **第 3 层（$P_3 \to \{A_2, P_2\}$）：**
   同理，选取 $\varepsilon_3 \ll \delta_2 \ll \varepsilon_2$，在 $P_3$ 子区域叠加水平振荡：
   $$v_3(x) = v_2(x) + \psi_2(x_1) \varepsilon_3 h_{1/2}\left(\frac{x_2}{\varepsilon_3}\right) \begin{pmatrix} 0 \\ -2 \end{pmatrix}.$$
   在有效区域分裂为 $A_2$（占比 $1/2$）与 $P_2$（占比 $1/2$）。
4. **第 4 层（$P_2 \to \{A_1, P_1\}$）：**
   选取 $\varepsilon_4 \ll \delta_3 \ll \varepsilon_3$，在 $P_2$ 子区域叠加竖直振荡：
   $$v_4(x) = v_3(x) + \psi_3(x_2) \varepsilon_4 h_{2/3}\left(\frac{x_1}{\varepsilon_4}\right) \begin{pmatrix} -3 \\ 0 \end{pmatrix}.$$
   在有效区域分裂为 $A_1$（占比 $1/3$）与剩余的 $P_1$（占比 $2/3$）。

##### 多周期递归与全域构建
对剩余的 $P_1$ 连通块重复上述四步构造，共迭代 $k$ 次，得到函数 $v^{(k)}(x)$。
各级尺度参数满足：
$$\varepsilon_{4m+4} \ll \delta_{4m+3} \ll \varepsilon_{4m+3} \ll \dots \ll \varepsilon_1.$$
由此可使各级过渡层引起的交叉导数模长总和小于任意预给小量 $\sigma > 0$，且过渡层测度占 $\Omega$ 的比率小于 $\sigma$。
由于每一级位移微扰均受控于其波长，全场位移满足一致小估计：
$$\|v^{(k)}\|_{L^\infty(\Omega)} \le C \varepsilon_1.$$

##### 零边界层截断
引入标准边界截断函数 $\eta \in C_c^\infty(\Omega; [0,1])$：
$$\eta(x) = 1 \quad \text{在 } \Omega_{\delta_0} = \{x \in \Omega : \operatorname{dist}(x, \partial\Omega) \ge \delta_0\} \text{ 上},\quad |\nabla \eta| \le \frac{C_0}{\delta_0}.$$
定义最终近最优位移场为：
$$u^{(k)}(x) = \eta(x) v^{(k)}(x).$$

#### 3. 约束与能量估计的严格验证

##### (1) 零边界条件
因 $\eta \in C_c^\infty(\Omega)$，其在 $\partial\Omega$ 的邻域内恒为 $0$，故 $u^{(k)} \in W^{1,\infty}(\Omega;\mathbb{R}^2)$ 且在 $\partial\Omega$ 上的迹严格为 $0$。

##### (2) 统一梯度上界验证
计算其梯度场：
$$\nabla u^{(k)}(x) = \eta(x) \nabla v^{(k)}(x) + v^{(k)}(x) \otimes \nabla \eta(x).$$
- 在四个井及四个辅助状态处，Frobenius 范数分别为：
  $$\|A_1\|_F = 3,\quad \|A_2\|_F = \sqrt{5} \approx 2.236,\quad \|A_3\|_F = \sqrt{5} \approx 2.236,\quad \|A_4\|_F = 3,$$
  $$\|P_1\|_F = 0,\quad \|P_2\|_F = 1,\quad \|P_3\|_F = \sqrt{2} \approx 1.414,\quad \|P_4\|_F = 1.$$
  所有井与辅助矩阵的模长最大值仅为 $3$。
- 在内部层合的过渡区域，各层交叉导数满足 $\|\nabla v^{(k)} - \text{State}\|_F \le \sigma$。
- 对于边界过渡项，预先选取足够小的 $\varepsilon_1$，使得：
  $$\|v^{(k)} \otimes \nabla \eta\|_{L^\infty} \le \|v^{(k)}\|_\infty \|\nabla \eta\|_\infty \le C \varepsilon_1 \cdot \frac{C_0}{\delta_0} \le \sigma.$$
取 $\sigma = 0.2$，则对几乎处处的 $x \in \Omega$：
$$\|\nabla u^{(k)}(x)\|_F \le \max_{i} \|A_i\|_F + 2\sigma \le 3 + 0.4 = 3.4 \le 4.$$
严格满足 $\operatorname{ess\,sup}_\Omega \|\nabla u^{(k)}\|_F \le 4$。

##### (3) 能量估计
将区域 $\Omega$ 划分为三部分：
1. **纯相有效区 $\Omega_{\text{wells}}$**：梯度已落入四个井的 $\sigma$-邻域内，能量密度不超过 $\sigma^2$。
2. **剩余未转化区 $\Omega_{\text{rem}}$**：梯度仍处于 $P_1 = 0$ 的 $\sigma$-邻域内。其测度为 $|\Omega_{\text{rem}}| \le (1/6)^k$。
   在该区域内，距离最近的井为 $A_2$ 或 $A_3$：
   $$\min_{1 \le i \le 4} \|0 - A_i\|_F^2 = \min\{9, 5, 5, 9\} = 5.$$
   能量贡献不超过 $(5 + O(\sigma)) \cdot (1/6)^k$。
3. **边界与过渡层 $\Omega_{\text{trans}}$**：包括外边界层（测度 $O(\delta_0)$）和各层合内部过渡层（测度 $O(\sigma)$）。
   在该区域上，梯度模长受控于 $4$，被积函数受控于 $(4 + 3)^2 = 49$。其总能量贡献为 $49 \cdot (O(\delta_0) + O(\sigma))$。

综合以上三部分：
$$E(u^{(k)}) \le \sigma^2 |\Omega| + 6 \left(\frac{1}{6}\right)^k + 49 \cdot [C \delta_0 + \sigma].$$
对任意给定的容许误差 $\varepsilon > 0$：
- 首先选取充分大的循环次数 $k$，使得 $6(1/6)^k < \varepsilon / 3$；
- 其次选取充分小的边界层宽度 $\delta_0$ 和参数 $\sigma$，使得 $49 C \delta_0 < \varepsilon / 3$ 且 $\sigma^2 + 49 \sigma < \varepsilon / 3$；
- 最后按上述层次不等式逐级确定极细层合波长 $\varepsilon_1, \dots, \varepsilon_{4k}$。

即得到：
$$E(u^{(k)}) < \varepsilon.$$
这证明了 $e_0 = \inf_{u \in \mathcal{A}} E(u) = 0$。

同时，在该构造中，相 $A_1, A_2, A_3, A_4$ 占据的主区域测度比严格为 $1 : 3 : 3 : 3$，未分配至四个井的过渡层与剩余层测度总和为 $O(\delta_0) + O(\sigma) + (1/6)^k \to 0$。因此其相体积分数：
$$\lim_{k \to \infty} (\pi_1(u^{(k)}), \pi_2(u^{(k)}), \pi_3(u^{(k)}), \pi_4(u^{(k)})) = (0.1, 0.3, 0.3, 0.3),$$
与任务二的理论唯一极限完全吻合。

---

### 五、 结论汇总表

| 考察项 | 数学结论 | 判定 / 极限值 | 核心依据 |
| :--- | :--- | :--- | :--- |
| **单元能最小值 $e_0$** | 精确下确界 | **$e_0 = 0$** | 存在高阶循环层合序列使能量趋于 $0$（Tartar $T_4$ 构型） |
| **可达性** | 是否达到 | **不可达**（不存在极小元） | 对角梯度场必退化为常值场，零边界迫使梯级为零矩阵，而 $0 \notin K$ |
| **相体积分数极限** | 是否必然收敛 | **必然收敛到唯一向量** | 由平均梯度为零与零拉格朗日量 $\det(\nabla u)$ 守恒构成的非奇异线性系统锁定 |
| **相体积分数取值** | $(\pi_1, \pi_2, \pi_3, \pi_4)$ | **$(0.1,\, 0.3,\, 0.3,\, 0.3)$** | 唯一解 $\lambda_1 = 1/10,\ \lambda_2 = \lambda_3 = \lambda_4 = 3/10$ |
| **位移构造** | 容许性验证 | **严格成立** | $u|_{\partial\Omega}=0$，$\|\nabla u\|_F \le 3.4 \le 4$，$E(u^{(k)}) < \varepsilon$ |
