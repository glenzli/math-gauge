单元能 \(e_0=0\)，但在 \(\mathcal A\) 中不能达到。每个近最优序列的相体积分数都收敛到 \(\frac1{10}(1,3,3,3)\)，这是唯一可能的极限。

## 位移构造与单元能

取四个辅助梯度
\[
P_0=0,\qquad P_1=\operatorname{diag}(1,0),\qquad
P_2=\operatorname{diag}(1,1),\qquad P_3=\operatorname{diag}(0,1).
\]
它们满足
\[
\begin{aligned}
P_0&=\tfrac14 A_4+\tfrac34 P_3,\\
P_3&=\tfrac13 A_3+\tfrac23 P_2,\\
P_2&=\tfrac12 A_2+\tfrac12 P_1,\\
P_1&=\tfrac13 A_1+\tfrac23 P_0.
\end{aligned}
\]
每行右侧的两个矩阵只在一个对角元上有差别，因此相差秩一。按这四行依次分裂，每步产生一个井梯度，余下的辅助梯度在第四步回到 \(P_0\)。

先给出每一步的局部位移公式。设当前位移 \(u\) 在一个轴平行矩形 \(Q\) 上是仿射的，梯度为 \(P\)。把该步的分裂写成
\[
P=\theta B+(1-\theta)C,\qquad B-C=d\,e_k\otimes e_k,
\]
其中 \(B\) 是井梯度，\(C\) 是下一辅助梯度，\(e_k\) 是坐标单位向量。记 \(Q\) 沿第 \(k\) 个坐标的局部坐标为 \(t\in(0,L)\)，沿另一坐标的局部坐标为 \(s\in(0,H)\)，并记另一坐标的指标为 \(\ell\)。

给定 \(0<\delta<1\)，选正整数 \(N\)，使 \(h=L/N\) 满足 \(2|d|h/(\delta H)\le1\)。取连续的 \(h\)-周期锯齿函数 \(\varphi\)，令 \(\varphi(0)=0\)，并在每周期的前 \(\theta h\) 段取斜率 \((1-\theta)d\)，在余下部分取斜率 \(-\theta d\)。两段的总增量为零，所以 \(\varphi(L)=0\)，且 \(|\varphi|\le |d|h\)。令
\[
\eta(s)=\min\left\{1,\frac{2s}{\delta H},\frac{2(H-s)}{\delta H}\right\},
\qquad
v(x)=u(x)+e_k\,\eta(s)\varphi(t)\quad (x\in Q).
\]
在 \(Q\) 外令 \(v=u\)。修正项在 \(\partial Q\) 上为零，延拓到 \(Q\) 外仍是 Lipschitz 函数，因而这一步保持了原位移的边界迹。

在 \(Q\) 内几乎处处有
\[
\nabla v=P+\eta\varphi' e_k\otimes e_k+\eta'\varphi e_k\otimes e_\ell.
\]
前两项之和是 \(P\) 与 \(B\) 或 \(C\) 的凸组合。所有井和辅助梯度的 Frobenius 范数都至多为 \(3\)，所以
\[
\|\nabla v\|_F\le 3+\frac{2|d|h}{\delta H}\le4.
\]
在中央带 \(\delta H/2<s<H-\delta H/2\) 上，\(\eta=1\)。锯齿的各线性段把中央带分成有限个开矩形，\(v\) 在这些矩形上是仿射的，梯度为 \(B\) 和 \(C\) 的面积分别为 \((1-\delta)\theta|Q|\) 和 \((1-\delta)(1-\theta)|Q|\)。两侧过渡带的总面积为 \(\delta|Q|\)。

对每个整数 \(m\ge1\)，从 \(\Omega\) 上的零位移出发，取 \(\delta=6^{-m}/(4m)\)，按表中顺序做 \(m\) 轮分裂。每一步只在上一分裂得到的辅助梯度矩形内继续修改，井梯度区域和过渡带此后保持原样。每一步涉及有限个矩形。由于每次修正都在各自矩形的边界上为零，所得 \(u_m\) 的边界迹为零，且上述梯度估计在每一步都成立。因此 \(u_m\in\mathcal A\)。

每轮结束时，尚待分裂的面积至多为本轮开始时的
\[
\tfrac34\cdot\tfrac23\cdot\tfrac12\cdot\tfrac23=\tfrac16
\]
倍。每一步留下的过渡带总面积至多为 \(\delta\)。因此，除去总面积至多 \(6^{-m}+4m\delta\) 的区域，\(\nabla u_m\) 恰好落在 \(K\) 中。在其余区域，能量密度至多为 \((4+3)^2=49\)，故
\[
0\le E(u_m)\le49(6^{-m}+4m\delta)=98\,6^{-m}\longrightarrow0.
\]
这证明 \(e_0=0\)。六个两井差的行列式确实都非零。上述构造用井与辅助梯度之间的秩一连接完成循环，给出了对四相正间隙推断的反例。

## 下确界不能达到

若 \(E(u)=0\)，则 \(\nabla u\in K\) 几乎处处，因而 \(\partial_2u_1=\partial_1u_2=0\) 几乎处处。沿几乎每条竖直线，\(u_1\) 由底边的零迹和 \(\partial_2u_1=0\) 得到恒为零。沿几乎每条水平线，\(u_2\) 由左边的零迹和 \(\partial_1u_2=0\) 得到恒为零。因此 \(u=0\)，其梯度为零，而零矩阵不在 \(K\) 中，矛盾。

## 近最优序列的相体积分数

任意 \(u\in\mathcal A\) 都满足两个积分恒等式
\[
\int_\Omega \nabla u\,dx=0,\qquad
\int_\Omega \det\nabla u\,dx=0.
\]
事实上，零迹给出 \(u\in W^{1,2}_0(\Omega;\mathbb R^2)\)，可用紧支撑光滑位移在 \(W^{1,2}\) 中逼近。对这样的光滑位移 \(w\)，一阶导数的积分为零，且
\[
\det\nabla w
=\partial_1(w_1\partial_2w_2)-\partial_2(w_1\partial_1w_2),
\]
故行列式的积分也为零。逼近时，梯度收敛于 \(L^2\)，行列式中的导数乘积由 Hölder 不等式收敛于 \(L^1\)，从而得到这两个恒等式。

设 \(E(u_j)\to e_0=0\)，并令 \(M_j(x)\) 为按题定最近井规则选出的井矩阵。于是
\[
\|M_j-\nabla u_j\|_{L^2(\Omega)}^2=E(u_j)\longrightarrow0.
\]
由第一个积分恒等式及 \(|\Omega|=1\)，有
\[
\sum_{i=1}^4\pi_i(u_j)A_i=\int_\Omega M_j\,dx\longrightarrow0.
\]
对两个 \(2\times2\) 矩阵 \(F,G\)，按列展开行列式之差可得
\[
|\det F-\det G|\le(\|F\|_F+\|G\|_F)\|F-G\|_F.
\]
由于 \(\|\nabla u_j\|_F\le4\) 且 \(\|M_j\|_F\le3\)，第二个积分恒等式给出
\[
\left|\sum_{i=1}^4\pi_i(u_j)\det A_i\right|
\le 7\sqrt{E(u_j)}\longrightarrow0.
\]

因此，任一相体积分数的子序列极限 \(p=(p_1,p_2,p_3,p_4)\) 都满足
\[
p_1+p_2+p_3+p_4=1,\qquad
3p_1+p_2-2p_3=0,\qquad
2p_2+p_3-3p_4=0,\qquad
2p_2-2p_3=0.
\]
最后一个等式给出 \(p_2=p_3\)，两个梯度矩条件进一步给出 \(p_2=p_4=3p_1\)。归一化后得到 \(p=\frac1{10}(1,3,3,3)\)。相体积分数向量始终位于紧的概率单纯形中，所以唯一的子序列极限就是整个序列的极限。上面构造的 \(u_m\) 实现了这一极限。