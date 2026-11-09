## 结论

设  
\[
\pi^*=\left(\frac1{10},\frac3{10},\frac3{10},\frac3{10}\right).
\]
则

\[
\boxed{e_0=0.}
\]

并且：

1. \(e_0=0\)，但不存在 \(u\in\mathcal A\) 使 \(E(u)=0\)；即下确界不达到。
2. 对任意满足 \(E(u_j)\to e_0\) 的序列，
   \[
   \boxed{\pi(u_j)\longrightarrow \pi^*=\left(\frac1{10},\frac3{10},\frac3{10},\frac3{10}\right).}
   \]
   因而所有可能的极限向量只有一个，即 \(\pi^*\)。

关键点是：六个两两行列式均非零，只能排除两相简单层合；它不能排除多井的无限层合。下面给出四井无限层合，它使能量趋于零。

---

## 1. 四井无限层合

把对角矩阵 \(\operatorname{diag}(a,b)\) 记为点 \((a,b)\)，则
\[
A_1=(3,0),\quad A_2=(1,2),\quad A_3=(-2,1),\quad A_4=(0,-3).
\]

考虑如下循环平均：
\[
M_0=(0,0),
\]
\[
M_0=\frac14 A_4+\frac34 M_1,\qquad M_1=(0,1),
\]
\[
M_1=\frac13 A_3+\frac23 M_2,\qquad M_2=(1,1),
\]
\[
M_2=\frac12 A_2+\frac12 M_3,\qquad M_3=(1,0),
\]
\[
M_3=\frac13 A_1+\frac23 M_0.
\]

逐项检查秩一条件：
\[
A_4-M_1=\begin{pmatrix}0&0\\0&-4\end{pmatrix},\quad
A_3-M_1=\begin{pmatrix}-2&0\\0&0\end{pmatrix},
\]
\[
A_2-M_2=\begin{pmatrix}0&0\\0&1\end{pmatrix},\quad
A_1-M_3=\begin{pmatrix}2&0\\0&0\end{pmatrix}.
\]
这些差均为秩一矩阵，因此每一步都是合法的秩一层合。

设该无限层合对应的概率测度为 \(\nu\)。一次完整循环给出
\[
\nu
=\frac14\delta_{A_4}
+\frac14\delta_{A_3}
+\frac14\delta_{A_2}
+\frac1{12}\delta_{A_1}
+\frac16\nu .
\]
因为剩余质量为
\[
\frac34\cdot\frac23\cdot\frac12\cdot\frac23=\frac16,
\]
所以
\[
\frac56\nu
=\frac14\delta_{A_4}
+\frac14\delta_{A_3}
+\frac14\delta_{A_2}
+\frac1{12}\delta_{A_1},
\]
从而
\[
\nu
=\frac3{10}\delta_{A_2}
+\frac3{10}\delta_{A_3}
+\frac3{10}\delta_{A_4}
+\frac1{10}\delta_{A_1}.
\]
因此
\[
\pi^*=\left(\frac1{10},\frac3{10},\frac3{10},\frac3{10}\right).
\]

该层合的重心为
\[
\sum_{i=1}^4\pi_i^*A_i
=
\frac1{10}\begin{pmatrix}3&0\\0&0\end{pmatrix}
+\frac3{10}\begin{pmatrix}1&0\\0&2\end{pmatrix}
+\frac3{10}\begin{pmatrix}-2&0\\0&1\end{pmatrix}
+\frac3{10}\begin{pmatrix}0&0\\0&-3\end{pmatrix}
=0.
\]
故它给出平均梯度为零的相容微结构。

---

## 2. 近最优位移构造

下面用标准层合实现引理，把上述概率测度实现为位移梯度。

**层合实现引理.** 设 \(K\) 是有限矩阵集，\(\nu\) 是可由有限或无限秩一层合得到、且重心的概率测度。则对任意 \(\eta>0\)，存在
\[
u_\eta\in W^{1,\infty}_0(\Omega;\mathbb R^2)
\]
使得
\[
\|\nabla u_\eta\|_{L^\infty(\Omega)}
\le \max_{A\in K}\|A\|_F+\eta,
\]
并且
\[
E(u_\eta)\le \eta,
\qquad
|\pi_i(u_\eta)-\nu_i|\le \eta.
\]

其构造方式如下。若某一步是
\[
M=\lambda A+(1-\lambda)M',
\qquad
A-M'=a\otimes n,
\]
则在相应子矩形内取一周期函数 \(h_{\lambda,\delta}\)，使其导数在比例 \(\lambda\) 的部分取 \(1\)、其余部分取 \(0\)，并在宽度 \(\delta\) 的过渡带内光滑过渡，置
\[
u(x)=M'x+h_{\lambda,\delta}(x\cdot n)\,a.
\]
于是除过渡带外，
\[
\nabla u=A\quad\text{或}\quad \nabla u=M'.
\]
逐层递归，并把最内层剩余区域用零梯度填充；再在最外层用宽度可任意小的零迹修正层实现 \(u|_{\partial\Omega}=0\)。所有梯度均为 \(K\cup\{0\}\) 中矩阵的凸组合，故其 Frobenius 范数不超过
\[
\max_{1\le i\le4}\|A_i\|_F=3<4,
\]
再取 \(\eta<1\)，即得统一梯度上界 \(4\)。

把上述测度 \(\nu\) 截断到第 \(N\) 层。一次循环的剩余质量比例为
\[
R=\frac16.
\]
截断后的测度可写成
\[
\nu_N
=\sum_{k=0}^{N-1}R^k\left(
\frac14\delta_{A_4}
+\frac14\delta_{A_3}
+\frac14\delta_{A_2}
+\frac1{12}\delta_{A_1}
\right)
+R^N\delta_0.
\]
其中最后一项目的为剩余零梯度区域。于是
\[
\pi_i(\nu_N)
=
(1-R^N)\pi_i^*,
\qquad i=1,2,3,4,
\]
而剩余区域的梯度为零。由
\[
\operatorname{dist}(0,K)^2=5,
\]
其能量贡献至多
\[
5R^N.
\]
取过渡带总测度不超过 \(\delta_N\)，则构造出的 \(u_{N,\delta_N}\in\mathcal A\) 满足
\[
E(u_{N,\delta_N})
\le
5\left(\frac16\right)^N+C\delta_N.
\]
令 \(N\to\infty\)、\(\delta_N\to0\)，得到
\[
E(u_{N,\delta_N})\longrightarrow0.
\]
同时
\[
\pi_i(u_{N,\delta_N})\longrightarrow\pi_i^*.
\]
故
\[
e_0=0.
\]

---

## 3. 下确界不达到

需要区分“梯度 Young 测度”与“真正的梯度场”。上面的无限层合只给出 \(E(u_j)\to0\) 的逼近序列；它不自动给出 \(E(u)=0\) 的位移。

使用如下标准有限井刚性引理：

> 若 \(K\subset\mathbb R^{2\times2}\) 是有限集，且任意两不同矩阵之差不是秩一矩阵，则任意
> \[
> u\in W^{1,\infty}(\Omega;\mathbb R^2),
> \qquad
> \nabla u(x)\in K\quad\text{a.e.}
> \]
> 必为仿射映射。

这里六个差
\[
A_i-A_j
\]
的行列式依次为
\[
-4,-5,9,3,5,-8,
\]
均非零，故任意两井之间都没有秩一连接，刚性引理适用。

若存在 \(u\in\mathcal A\) 使 \(E(u)=0\)，则
\[
\operatorname{dist}(\nabla u(x),K)=0\quad\text{a.e.},
\]
即
\[
\nabla u(x)\in K\quad\text{a.e.}
\]
由刚性引理，\(\nabla u\equiv A_i\) 为常数。但
\[
u\in W^{1,\infty}_0(\Omega;\mathbb R^2)
\]
给出
\[
\int_\Omega \nabla u\,dx=0.
\]
于是 \(A_i=0\)，与四个井均非零矛盾。

所以
\[
\boxed{\text{不存在 }u\in\mathcal A\text{ 使 }E(u)=0=e_0.}
\]
即 \(e_0=0\) 不达到。

---

## 4. 任意极小化序列的相体积分数唯一

设
\[
E(u_j)\to0,
\qquad
u_j\in\mathcal A.
\]
因
\[
E(u_j)=\int_\Omega \operatorname{dist}(\nabla u_j,K)^2\,dx,
\]
故
\[
\nabla u_j\longrightarrow K
\]
在 \(L^2\) 中，从而按测度收敛到 \(K\)。

取任一子列（仍记作 \(j\)），令
\[
\nu_j=(\nabla u_j)_\#\,dx
\]
为梯度在 \(\Omega\) 上诱导的经验测度。由梯度的一致 \(L^\infty\) 界，可抽子列使
\[
\nu_j\rightharpoonup\nu
\]
弱星收敛。因为 \(\operatorname{dist}(\nabla u_j,K)\to0\) 按测度，极限测度满足
\[
\operatorname{supp}\nu\subset K.
\]
记
\[
\nu_i=\nu(\{A_i\}).
\]

由零边界条件，
\[
\int_\Omega \nabla u_j\,dx=0.
\]
令 \(j\to\infty\)，得
\[
\sum_{i=1}^4\nu_i A_i=0.
\]
写成分量形式：
\[
3\nu_1+\nu_2-2\nu_3=0, \tag{1}
\]
\[
2\nu_2+\nu_3-3\nu_4=0. \tag{2}
\]

此外，对
\[
u_j=(u_j^1,u_j^2),
\]
Jacobi 行列式可写成散度形式：
\[
\det\nabla u_j
=
\partial_x(u_j^1\partial_yu_j^2)
-\partial_y(u_j^1\partial_xu_j^2).
\]
由于 \(u_j=0\) 在 \(\partial\Omega\) 上，故
\[
\int_\Omega \det\nabla u_j\,dx=0.
\]
令 \(j\to\infty\)，得
\[
2\nu_2-2\nu_3=0,
\]
即
\[
\nu_2=\nu_3. \tag{3}
\]

由 (1)、(3)，
\[
3\nu_1+\nu_2-2\nu_2=0
\quad\Longrightarrow\quad
\nu_1=\frac13\nu_2.
\]
由 (2)、(3)，
\[
2\nu_2+\nu_2-3\nu_4=0
\quad\Longrightarrow\quad
\nu_4=\nu_2.
\]
又
\[
\nu_1+\nu_2+\nu_3+\nu_4=1,
\]
故
\[
\frac13\nu_2+\nu_2+\nu_2+\nu_2
=\frac{10}{3}\nu_2=1,
\]
从而
\[
\nu_2=\nu_3=\nu_4=\frac3{10},
\qquad
\nu_1=\frac1{10}.
\]
于是
\[
(\nu_1,\nu_2,\nu_3,\nu_4)
=
\left(\frac1{10},\frac3{10},\frac3{10},\frac3{10}\right)
=\pi^*.
\]

最后说明最近井分配 \(\pi_i(u_j)\) 与测度质量一致。由于
\[
\int_\Omega\operatorname{dist}(\nabla u_j,K)^2\to0,
\]
对任意小 \(\varepsilon\), 除一个测度趋于零的集合外，\(\nabla u_j\) 落在某个 \(A_i\) 的互不相交的小邻域内。各井间有正的分离距离，故最近井分配不会在这些邻域之间产生歧义；等距情形只可能出现在测度趋于零的集合上。因此任一子列的相分数极限都等于相应的 \(\nu_i\)。

所以任意子列都有同一极限，因而整个序列收敛，并且
\[
\boxed{
(\pi_1(u_j),\pi_2(u_j),\pi_3(u_j),\pi_4(u_j))
\longrightarrow
\left(\frac1{10},\frac3{10},\frac3{10},\frac3{10}\right).
}
\]

---

## 最终答案汇总

\[
\boxed{e_0=0.}
\]

\[
\boxed{\text{下确界不达到；不存在 }u\in\mathcal A\text{ 使 }E(u)=0.}
\]

对任意极小化序列 \(E(u_j)\to0\)，相体积分数必然收敛，并且全部可能的极限只有一个：
\[
\boxed{
\lim_{j\to\infty}(\pi_1,\pi_2,\pi_3,\pi_4)
=
\left(\frac1{10},\frac3{10},\frac3{10},\frac3{10}\right).
}
\]

近最优位移可由四步秩一循环
\[
M_0
\xrightarrow[\;1/4\;]{A_4}M_1
\xrightarrow[\;1/3\;]{A_3}M_2
\xrightarrow[\;1/2\;]{A_2}M_3
\xrightarrow[\;1/3\;]{A_1}M_0
\]
的有限截断层合实现；其梯度保持在 \(K\cup\{0\}\) 的凸包内，故统一满足
\[
\|\nabla u\|_F\le3<4,
\]
零边界由标准零迹修正层实现，能量满足
\[
E(u_{N,\delta_N})
\le
5\left(\frac16\right)^N+C\delta_N
\longrightarrow0.
\]
相分数随截断层数增加趋于上述唯一向量 \(\pi^*\)。