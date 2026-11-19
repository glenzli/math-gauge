下确界为 **\(e_0=0\)**，且没有 \(u\in\mathcal A\) 达到它。每个满足 \(E(u_j)\to e_0\) 的序列都有相同的相分数极限
\[
\left(\frac1{10},\frac3{10},\frac3{10},\frac3{10}\right).
\]

### 秩一分解与近最优位移

取四个中间矩阵
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
每一行右侧的两个矩阵只在一个对角元上不同，因而有秩一连接。从零矩阵开始，每一步都可以分出一个井，再对余下的中间矩阵继续分解。经过四步，回到 \(P_0\) 的权重为
\[
\tfrac34\cdot\tfrac23\cdot\tfrac12\cdot\tfrac23=\tfrac16.
\]
这就是逐对应用二相刚性估计时遗漏的相容结构。

为把每一步实现为位移，设当前位移在轴平行矩形 \(R\) 上为 \(Mx+d\)，相应的一行分解为 \(M=\lambda B+(1-\lambda)C\)，其中 \(B\) 是井，\(C\) 是下一个中间矩阵。设变化的对角元为第 \(k\) 个，写成
\[
B-M=b\,e_k\otimes e_k,\qquad C-M=c\,e_k\otimes e_k.
\]
于是 \(\lambda b+(1-\lambda)c=0\)，且上述四步均有 \(\max(|b|,|c|)\le3\)。

在 \(R\) 中用 \(t\in(0,L)\) 表示沿 \(e_k\) 的局部坐标，用 \(s\in(0,H)\) 表示沿 \(e_{3-k}\) 的局部坐标。给定 \(0<\delta<1\)，令 \(h=\delta H/2\)，并取
\[
\eta(s)=\min\{1,s/h,(H-s)/h\}.
\]
取正整数 \(m\) 使 \(3L/m\le h\)，记 \(T=L/m\)。定义连续分段线性函数 \(g\)，令 \(g(0)=0\)，在每个长度为 \(T\) 的周期内，前 \(\lambda T\) 段斜率为 \(b\)，其余段斜率为 \(c\)。由斜率的加权和为零，\(g\) 在每个周期端点都为零，且 \(\|g\|_\infty\le3T\le h\)。

把 \(R\) 上的位移改为
\[
v(x)=Mx+d+e_k\,\eta(s)g(t).
\]
扰动在 \(R\) 的四条边上均为零，因此与原位移连续拼接。其梯度几乎处处为
\[
\nabla v=M+\eta(s)g'(t)e_k\otimes e_k
              +g(t)\eta'(s)e_k\otimes e_{3-k}.
\]
前两项之和位于 \(M\) 到 \(B\) 或 \(C\) 的线段上，Frobenius 范数至多为 \(3\)。末项位于非对角位置，范数至多为 \(h/h=1\)。由正交性，
\[
\|\nabla v\|_F\le\sqrt{10}<4.
\]
在中部 \(h<s<H-h\)，位移在各条带上都是仿射的，梯度分别为 \(B\) 和 \(C\)。这两组矩形条带的面积分别为 \((1-\delta)\lambda|R|\) 和 \((1-\delta)(1-\lambda)|R|\)。两侧过渡层的总面积为 \(\delta|R|\)。

现在固定 \(n\ge1\)，取 \(\delta=1/(4n^2)\)，从 \(\Omega\) 上的零位移开始，按上述顺序做 \(n\) 轮、共 \(4n\) 步。每一步只在中部梯度为下一个中间矩阵 \(C\) 的矩形上继续构造，已分出的井和两侧过渡层都保留。每步只有有限个矩形，扰动在各自矩形边界上为零，故拼接所得 \(u_n\in W^{1,\infty}\) 在 \(\partial\Omega\) 上为零。每次修改所在矩形的原梯度恰为 \(M\)，所以上述 \(\sqrt{10}\) 的界在每一步都成立，\(u_n\in\mathcal A\)。

每步处理的总面积至多为 \(1\)，故全部过渡层的面积至多为 \(4n\delta=1/n\)。每轮结束时，留待继续分解的面积至多为该轮开始时的 \(1/6\)，故最后剩余的矩形总面积至多为 \(6^{-n}\)。其余区域的梯度均在井中。由于 \(\|A_i\|_F\le3\)，得到
\[
0\le E(u_n)\le (4+3)^2\bigl(n^{-1}+6^{-n}\bigr)\longrightarrow0.
\]
因此 \(e_0=0\)。

### 下确界无法达到

若 \(E(u)=0\)，则 \(\nabla u\in K\) 几乎处处成立。四个井都是对角矩阵，故 \(\partial_2u_1=0\) 且 \(\partial_1u_2=0\)。沿几乎每条竖直线，\(u_1\) 为常数，由底边的零迹知该常数为零。同理，沿水平线利用左边的零迹得到 \(u_2=0\) 几乎处处。因此 \(u=0\)，而 \(E(0)=5\)，矛盾。

### 任意近最优序列的相分数

零迹给出两个积分恒等式
\[
\int_\Omega\nabla u\,dx=0,\qquad \int_\Omega\det\nabla u\,dx=0.
\]
对光滑紧支撑位移，第一个恒等式由分部积分得到，第二个由
\[
\det\nabla u
=\partial_1(u_1\partial_2u_2)-\partial_2(u_1\partial_1u_2)
\]
得到。一般的 \(u\in\mathcal A\) 可在 \(W^{1,2}_0(\Omega)\) 中用光滑紧支撑位移逼近。梯度的 \(L^2\) 收敛给出行列式的 \(L^1\) 收敛，因为
\[
|\det F-\det G|\le(\|F\|_F+\|G\|_F)\|F-G\|_F .
\]

设 \(E(u_j)\to0\)，令 \(G_j(x)\) 为题设最近井规则选出的矩阵，则
\[
\|G_j-\nabla u_j\|_{L^2}^2=E(u_j).
\]
由上述积分恒等式、行列式估计及统一梯度界，
\[
\sum_{i=1}^4\pi_i(u_j)A_i=\int_\Omega G_j\,dx\longrightarrow0,\qquad
\sum_{i=1}^4\pi_i(u_j)\det A_i=\int_\Omega\det G_j\,dx\longrightarrow0.
\]
相分数向量位于紧的概率单纯形中。对任一子列极限 \(\theta\)，取平均矩阵的两个对角元及平均行列式，得到
\[
3\theta_1+\theta_2-2\theta_3=0,\qquad
2\theta_2+\theta_3-3\theta_4=0,\qquad
2\theta_2-2\theta_3=0.
\]
所以 \(\theta_2=\theta_3=\theta_4=3\theta_1\)。再由 \(\sum_i\theta_i=1\)，得 \(\theta=(1,3,3,3)/10\)。子列极限唯一，故整个相分数序列收敛到该向量，上面构造的 \(u_n\) 也实现了这一极限。