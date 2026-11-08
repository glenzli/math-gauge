结论是

\[
\boxed{e_0=0,\qquad e_0\text{ 不被任何 }u\in\mathcal A\text{ 达到}.}
\]

虽然任意两个井都没有秩一连接，四个井可以通过循环的多相微结构使能量趋零。因此，题目中由二相刚性直接推出四相正能隙的相容性结论不成立。

而且，对**每一个**满足 \(E(u_j)\to0\) 的序列，其相体积分数都收敛，且唯一可能的极限为

\[
\boxed{\lim_{j\to\infty}(\pi_1(u_j),\pi_2(u_j),\pi_3(u_j),\pi_4(u_j))
=\left(\frac1{10},\frac3{10},\frac3{10},\frac3{10}\right).}
\]

下面构造位移并证明这些结论。

### 循环分解

记

\[
P_1=\operatorname{diag}(0,0),\quad
P_2=\operatorname{diag}(1,0),\quad
P_3=\operatorname{diag}(1,1),\quad
P_4=\operatorname{diag}(0,1).
\]

它们满足

\[
\begin{aligned}
P_1&=\tfrac14 A_4+\tfrac34 P_4,\\
P_4&=\tfrac13 A_3+\tfrac23 P_3,\\
P_3&=\tfrac12 A_2+\tfrac12 P_2,\\
P_2&=\tfrac13 A_1+\tfrac23 P_1.
\end{aligned} \tag{1}
\]

每一行右侧的两个矩阵只有一个对角元不同，所以它们的差都是秩一矩阵。沿四行依次分解后，未到达井的部分回到 \(P_1=0\)，其体积比例乘以

\[
\frac34\cdot\frac23\cdot\frac12\cdot\frac23=\frac16.
\]

接下来把这些矩阵分解实现为零边界位移。

### 局部分层及近最优位移

先说明如何在任意矩形 \(R=(a_1,a_1+L_1)\times(a_2,a_2+L_2)\) 上实现式 (1) 的一行。设该行写作

\[
M=\theta B+(1-\theta)C,\qquad 0<\theta<1,
\]

其中 \(B,C\) 是对角矩阵，只在第 \(k\) 个对角元不同。定义

\[
s_B=B_{kk}-M_{kk},\qquad s_C=C_{kk}-M_{kk}.
\]

令 \(F\) 为连续的 1 周期函数，在一个周期上取

\[
F(t)=
\begin{cases}
s_Bt,&0\le t\le\theta,\\
s_B\theta+s_C(t-\theta),&\theta\le t\le1.
\end{cases}
\]

因为 \(\theta s_B+(1-\theta)s_C=0\)，这个周期延拓连续。

取 \(0<\delta<1/4\)，写 \(\ell=\min(L_1,L_2)\)，并令

\[
\eta(x)=\min\left\{1,\frac{\operatorname{dist}(x,\partial R)}{\delta\ell}\right\}.
\]

对正整数 \(n\)，在原有仿射位移 \(Mx+b\) 上加入扰动

\[
v(x)=Mx+b+
\frac{L_k}{n}\,
F\!\left(n\frac{x_k-a_k}{L_k}\right)\eta(x)e_k. \tag{2}
\]

这里 \(e_k\) 是第 \(k\) 个坐标向量。由于 \(\eta=0\) 于 \(\partial R\)，式 (2) 在矩形边界上仍等于 \(Mx+b\)，因而可与外面的位移拼接。

在 \(\eta=1\) 的区域，\(\nabla v\) 恰好等于 \(B\) 或 \(C\)。这些区域是有限个矩形；在每个这样的矩形上，\(v\) 也是仿射的。整个矩形中，周期条纹本应分别占比例 \(\theta\) 和 \(1-\theta\)；被边界层去掉的面积至多为 \(4\delta |R|\)。所以得到的 \(B\) 区域和 \(C\) 区域分别至少有面积

\[
(\theta-4\delta)|R|,
\qquad
(1-\theta-4\delta)|R|. \tag{3}
\]

此外，几乎处处

\[
\nabla v
=M+\eta F' e_k\otimes e_k+
\frac{L_k}{n}F\, e_k\otimes\nabla\eta.
\]

前两项位于从 \(M\) 到 \(B\) 或从 \(M\) 到 \(C\) 的线段上。式 (1) 中所有矩阵的 Frobenius 范数都不超过 \(\sqrt{10}\)。选择充分大的整数 \(n\)，使

\[
\frac{L_k\|F\|_\infty}{n\delta\ell}
<\frac{4-\sqrt{10}}2,
\]

就得到整个矩形上 \(\|\nabla v\|_F<4\)。

现在对每个正整数 \(j\) 构造 \(u_j\)。从 \(u_j=0\) 开始，将整个 \(\Omega\) 视为梯度为 \(P_1\) 的活动矩形。令

\[
\delta_j=\frac{1}{32j^2}.
\]

在每个活动矩形上，用上述公式依次实施式 (1) 的四行：每次把其中到达井 \(A_i\) 的矩形保留，把到达下一个 \(P_i\) 的矩形作为下一步的活动矩形；边界层不再修改。每个矩形都选取足够大的整数 \(n\)，使刚才的梯度上界成立。完成四步称为一轮，共进行 \(j\) 轮。

这个过程每一步只产生有限个矩形，且扰动在各矩形边界为零。因此最终

\[
u_j\in W^{1,\infty}(\Omega;\mathbb R^2),\qquad
u_j|_{\partial\Omega}=0,\qquad
\|\nabla u_j\|_F\le4\quad\text{几乎处处}.
\]

每轮结束时仍为活动区域的面积至多乘以 \(1/6\)，所以第 \(j\) 轮后其面积至多为 \(6^{-j}\)。每次分层产生的边界层面积至多是当时活动区域面积的 \(4\delta_j\)。总共有 \(4j\) 个分层步骤，因此全部边界层面积至多为

\[
4j\cdot4\delta_j=\frac1{2j}.
\]

在活动区域和这些边界层之外，梯度恰好是某个井。又因为所有地方 \(\|\nabla u_j\|_F\le4\)，并且 \(\|A_2\|_F=\sqrt5\)，能量密度处处至多为 \((4+\sqrt5)^2<49\)。于是

\[
E(u_j)\le49\left(6^{-j}+\frac1{2j}\right)\longrightarrow0. \tag{4}
\]

能量非负，故 \(e_0=0\)。

### 下确界不被达到

假设某个 \(u\in\mathcal A\) 达到能量零，则

\[
\nabla u(x)\in K\qquad\text{几乎处处}.
\]

四个井都是对角矩阵，所以

\[
\partial_2u_1=0,\qquad \partial_1u_2=0
\quad\text{几乎处处}.
\]

因此 \(u_1\) 只依赖 \(x_1\)，而 \(u_2\) 只依赖 \(x_2\)。零边界迹分别在下边和左边给出 \(u_1=0\)、\(u_2=0\)，故 \(u=0\)。但

\[
E(0)=\min_i\|A_i\|_F^2=5,
\]

矛盾。所以 \(e_0\) 不被达到。

### 任意近最优序列的相体积分数

设 \(E(u_j)\to0\)，并按题目的最近井规则定义矩阵场 \(V_j(x)=A_i\)。则

\[
\|\nabla u_j-V_j\|_{L^2(\Omega)}^2=E(u_j)\to0. \tag{5}
\]

零边界条件给出

\[
\int_\Omega\nabla u_j\,dx=0,
\qquad
\int_\Omega\det\nabla u_j\,dx=0. \tag{6}
\]

第二式是行列式的零拉格朗日性质；例如可先对紧支撑光滑位移分部积分证明，再用 \(W^{1,2}_0\) 逼近。由于 \(\nabla u_j\) 和 \(V_j\) 一致有界，式 (5) 还意味着

\[
\int_\Omega\det V_j\,dx\to0.
\]

写 \(\pi_i^j=\pi_i(u_j)\)。由式 (5)、(6) 和 \(|\Omega|=1\)，得到

\[
\sum_{i=1}^4\pi_i^jA_i\to0,
\qquad
\sum_{i=1}^4\pi_i^j\det A_i\to0,
\qquad
\sum_{i=1}^4\pi_i^j=1.
\]

任取一个收敛子列，设其极限为 \(p=(p_1,p_2,p_3,p_4)\)。上式给出

\[
\begin{aligned}
3p_1+p_2-2p_3&=0,\\
2p_2+p_3-3p_4&=0,\\
2p_2-2p_3&=0,\\
p_1+p_2+p_3+p_4&=1.
\end{aligned}
\]

唯一解是

\[
p_1=\frac1{10},\qquad p_2=p_3=p_4=\frac3{10}.
\]

相分数向量始终位于紧的概率单纯形中，而它的每个收敛子列都有同一极限，因此整个序列都收敛到该向量。特别地，上述具体构造的 \(u_j\) 也具有这个相分数极限。