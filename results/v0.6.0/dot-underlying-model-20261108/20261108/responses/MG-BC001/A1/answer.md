结论为
\[
\boxed{e_0=0,\qquad\text{下确界不被达到},\qquad
(\pi_1(u_j),\pi_2(u_j),\pi_3(u_j),\pi_4(u_j))
\longrightarrow (1/10,3/10,3/10,3/10).}
\]
最后一个结论适用于任意近最优序列。因此全部可能的相分数极限只有上述一个向量。

两两没有秩一连接的计算是正确的，但题中由此推导出的四相正能隙结论不成立。下面给出实际位移构造，并证明各项结论。

## 一、四步秩一分裂

引入四个辅助矩阵
\[
P_0=\operatorname{diag}(0,0),\quad
P_1=\operatorname{diag}(1,0),\quad
P_2=\operatorname{diag}(1,1),\quad
P_3=\operatorname{diag}(0,1).
\]
直接计算得
\[
\begin{aligned}
P_0&=\tfrac14 A_4+\tfrac34 P_3,\\
P_3&=\tfrac13 A_3+\tfrac23 P_2,\\
P_2&=\tfrac12 A_2+\tfrac12 P_1,\\
P_1&=\tfrac13 A_1+\tfrac23 P_0.
\end{aligned} \tag{1}
\]
每一行右边两矩阵之差的秩均为一，且只有一个对角元不同。这里并不是在两口应变井之间直接层合，而是在一口井和一个辅助矩阵之间分裂。

从 (P_0) 开始，依次执行四行分裂，每次保留产生的应变井，只继续分裂辅助矩阵。一个循环中，进入 (A_4,A_3,A_2,A_1) 的理想比例依次为
\[
\frac14,\quad\frac14,\quad\frac14,\quad\frac1{12},
\]
剩下的 (P_0) 比例为
\[
q=\frac34\frac23\frac12\frac23=\frac16.
\]
但仅有这些矩阵等式还不够；下面将其实现为零边界位移。

## 二、带零边界扰动的具体分裂方法

设 (R\) 是一个开矩形，当前位移在 (R\) 上为 (u(x)=Px+b\)，且
\[
P=\theta B+(1-\theta)C,\qquad B-C=a\otimes e_k,
\quad 0<\theta<1.
\]
以下只使用式 (1) 中的分裂，所以 (P,B,C\) 的 Frobenius 范数均不超过 (3\)。

给定周期 \(\ell>0\)，定义连续的 \(\ell\)-周期锯齿函数 \(f_\ell\)：在一个周期上，
\[
f_\ell(s)=
\begin{cases}
(1-\theta)s,&0\le s\le\theta\ell,\\
\theta(\ell-s),&\theta\ell\le s\le\ell.
\end{cases}
\]
因此
\[
0\le f_\ell\le \ell\theta(1-\theta)\le\ell/4,
\qquad
f_\ell'=\begin{cases}1-\theta,&\text{占每周期的 }\theta\text{ 部分},\\-\theta,&\text{其余部分}.
\end{cases}
\]
取小于矩形短边一半的 \(t>0\)，令
\[
\chi_R(x)=\min\{1,\operatorname{dist}(x,\partial R)/t\},
\qquad R_t=\{x\in R:\operatorname{dist}(x,\partial R)>t\}.
\]
用下式替换 (R\) 中的位移：
\[
\widetilde u(x)=Px+b+a\,\chi_R(x)f_\ell(x_k). \tag{2}
\]
在 \(\partial R\) 上扰动为零，故可以与外部位移连续拼接。几乎处处有
\[
\nabla\widetilde u
=P+\chi_R f_\ell'(x_k)a\otimes e_k
 +f_\ell(x_k)a\otimes\nabla\chi_R.
\]
前两项是 (P\) 与 (B\) 或 (P\) 与 (C\) 的凸组合，范数不超过 (3\)。最后一项满足
\[
\bigl\|f_\ell a\otimes\nabla\chi_R\bigr\|_F
\le\frac{|a|\ell}{4t}.
\]
选择 \(\ell\) 足够小，使右边不超过 \(1/2\)，便得到
\[
\|\nabla\widetilde u\|_F\le\frac72<4. \tag{3}
\]
在内矩形 (R_t\) 上，梯度严格等于 (B\) 或 (C\)，这些区域是有限个开矩形条带，且位移在各条带上是仿射的。

更具体地，对任意预先指定的 \(\eta_R>0\)，先选 (t\) 使
\[
|R\setminus R_t|<\eta_R,
\]
再选足够小的 \(\ell\)。若 (L_\perp\) 是 (R_t\) 在垂直于 (e_k\) 方向上的边长，则周期条带在 (R_t\) 中的比例误差至多为 \(2\ell L_\perp\)。因而还可以保证
\[
\bigl|\{x\in R_t:\nabla\widetilde u=C\}\bigr|
\le(1-\theta)|R|+\eta_R. \tag{4}
\]
这样，边界过渡层可以任意小，核心区为精确的两种梯度，同时满足固定的梯度上界。所有选择均可按上述不等式直接进行。

## 三、近最优位移及其能量估计

对每个正整数 (N\)，设置
\[
\delta_N=\frac{6^{-N}}{8N}.
\]
从 \(u=0\) 和唯一的活动矩形 \(\Omega\) 开始，执行式 (1) 的 (N\) 个循环，共 (4N\) 个阶段。在每个阶段，对当前所有活动矩形使用式 (2)：

- (B\) 取该行产生的应变井，其核心条带此后保持不变；
- (C\) 取该行的下一个辅助矩阵，其核心条带成为下一阶段的活动矩形；
- 边界过渡层此后保持不变，不再进行分裂。

每个阶段只有有限个活动矩形。为它们分配正数 \(\eta_R\)，使 \(\sum_R\eta_R\le\delta_N\)，然后按第二节选择各自的 (t,\ell\)。这完整指定了一类有限步骤的位移构造，记结果为 \(u_N\)。

所有局部扰动在对应矩形边界上都为零。它们的零延拓属于 (W^{1,\infty}\)，有限次拼接仍属于这个空间。因此 \(u_N\in W^{1,\infty}(\Omega;\mathbb R^2)\)，且在 \(\partial\Omega\) 上迹为零。

每次修改仅发生在梯度恰为当前辅助矩阵的活动条带内，不会叠加到此前的过渡层中。因此式 (3) 给出全局而非逐层累加的估计：
\[
\operatorname*{ess\,sup}_{\Omega}\|\nabla u_N\|_F
\le\frac72<4.
\]
故 \(u_N\in\mathcal A\)。

令 \(m_s\) 为第 (s\) 阶段结束后的活动区域面积，初始 \(m_0=1\)。由式 (4)，
\[
m_s\le r_s m_{s-1}+\delta_N,
\]
其中 (r_s\) 依次周期性地取 \(3/4,2/3,1/2,2/3\)。于是
\[
m_{4N}\le6^{-N}+4N\delta_N.
\]
全部过渡层总面积至多 \(4N\delta_N\)。除最终活动区域和这些过渡层外，梯度严格属于 (K\)，所以
\[
|\{x:\nabla u_N(x)\notin K\}|
\le6^{-N}+8N\delta_N=2\cdot6^{-N}.
\]
在剩余区域，利用 \(\|\nabla u_N\|_F\le4\)、\(\|A_1\|_F=3\)，有
\[
\min_i\|\nabla u_N-A_i\|_F^2\le49.
\]
因此
\[
0\le E(u_N)\le98\cdot6^{-N}\longrightarrow0. \tag{5}
\]
能量非负，故 \(e_0=0\)。这也给出了满足全部原始约束的具体近最优位移。

## 四、下确界不能达到

如果存在 \(u\in\mathcal A\) 满足 \(E(u)=0\)，则 \(\nabla u\in K\) 几乎处处。四口井都是对角矩阵，所以
\[
\partial_2u_1=0,\qquad\partial_1u_2=0
\quad\text{几乎处处}.
\]
由 Sobolev 函数的切片性质，存在一维 Lipschitz 函数 (g,h\)，使
\[
u_1(x_1,x_2)=g(x_1),\qquad u_2(x_1,x_2)=h(x_2).
\]
第一分量在水平边上的零迹给出 (g=0\)，第二分量在竖直边上的零迹给出 (h=0\)。因此 (u=0\)、\(\nabla u=0\)，但 (0\notin K\)，矛盾。故没有位移达到下确界。

## 五、任意近最优序列的相分数

对任意 \(u\in\mathcal A\)，零边界条件给出
\[
\int_\Omega\nabla u\,dx=0,
\qquad
\int_\Omega\det\nabla u\,dx=0. \tag{6}
\]
第一式由弱导数积分得到。第二式可先对光滑紧支集位移使用
\[
\det\nabla u
=\partial_1(u_1\partial_2u_2)
 -\partial_2(u_1\partial_1u_2),
\]
再用 (W^{1,2}_0\) 中的光滑逼近证明；二维行列式在梯度的 (L^2\) 强收敛下于 (L^1\) 连续。

现在设 \(E(u_j)\to e_0=0\)。按照题中的最近井及平局规则定义矩阵场 \(V_j\)，于是
\[
V_j(x)\in K,\qquad
\|\nabla u_j-V_j\|_{L^2}^2=E(u_j)\longrightarrow0.
\]
记 \(p_{i,j}=\pi_i(u_j)\)。因 \(|\Omega|=1\)，式 (6) 和 Cauchy–Schwarz 不等式给出
\[
\sum_i p_{i,j}A_i=\int_\Omega V_j\,dx\longrightarrow0. \tag{7}
\]
另外，对二阶矩阵有
\[
|\det F-\det G|\le(\|F\|_F+\|G\|_F)\|F-G\|_F.
\]
这里 \(\|\nabla u_j\|_F\le4\)、\(\|V_j\|_F\le3\)，所以
\[
\sum_i p_{i,j}\det A_i
=\int_\Omega\det V_j\,dx\longrightarrow0. \tag{8}
\]
由于
\[
(\det A_1,\det A_2,\det A_3,\det A_4)=(0,2,-2,0),
\]
任何相分数聚点 \(p=(p_1,p_2,p_3,p_4)\) 必须满足
\[
\begin{cases}
p_1+p_2+p_3+p_4=1,\\
3p_1+p_2-2p_3=0,\\
2p_2+p_3-3p_4=0,\\
2p_2-2p_3=0.
\end{cases}
\]
末式给出 (p_2=p_3\)，第二式给出 (p_2=3p_1\)，第三式给出 (p_4=p_2\)。归一化后唯一解为
\[
p=(1/10,3/10,3/10,3/10).
\]
相分数向量位于紧单纯形内，且所有聚点均相同，因此整个序列必然收敛到这个向量。第三节构造的序列确实是近最优序列，故这个唯一极限也确实能够实现。

综上，四相循环分裂可以在统一 Lipschitz 上界和严格零边界条件下产生趋零能量；两井之间不存在秩一连接，并不排除这种四相机制。
