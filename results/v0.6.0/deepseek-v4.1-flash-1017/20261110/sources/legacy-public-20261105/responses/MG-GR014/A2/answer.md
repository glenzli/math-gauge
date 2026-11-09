下面统一记
\[
\langle a,x\rangle=\sum_{i\in I}a_i x_i,
\]
其中 \(a\in k^{(I)}\)，所以右边总是有限和。

---

## S1 有限系统的坐标纤维

设 \(B=I\setminus A\)，取一解 \(x^0\in\mathcal S\)。则齐次解空间为
\[
W^\perp=\{z\in k^I:\langle a,z\rangle=0\ \forall a\in W\},
\]
故
\[
\boxed{\mathcal S=x^0+W^\perp},\qquad 
\dim_{\mathrm{aff}}\mathcal S=|I|-\dim W.
\]

对 \(y\in\pi_A(\mathcal S)\)，取 \(x_y\in\mathcal S\) 使 \(x_y|_A=y\)。若 \(x\in\mathcal S\) 且 \(x|_A=y\)，则
\[
x-x_y\in W^\perp,\qquad (x-x_y)|_A=0.
\]
而
\[
W^\perp\cap\{z:z|_A=0\}=(W+U_A)^\perp,
\]
其中 \(U_A=\operatorname{span}\{e_i:i\in A\}\)。因此
\[
\boxed{
\pi_A^{-1}(y)\cap\mathcal S
=x_y+(W+U_A)^\perp
}
\]
并且任一非空纤维的仿射维数为
\[
\boxed{
\dim\bigl(\pi_A^{-1}(y)\cap\mathcal S\bigr)
=|I|-\dim(W+U_A).
}
\]
所有非空纤维有同一维数。

下面给出 \(y\in k^A\) 可延拓的充要条件。记
\[
\beta:W\to k,\qquad \beta\Bigl(\sum_j\lambda_j a_j\Bigr)=\sum_j\lambda_j b_j
\]
（由相容性，\(\beta\) 良定义）。则
\[
\boxed{
y\in\pi_A(\mathcal S)
\iff
\langle u,y\rangle=\beta(u)\quad\text{对一切 }u\in W\cap U_A.
}
\tag{1.1}
\]
等价地，对任意有限线性关系 \(\sum_{j\in F}\lambda_j a_j\)，若
\[
\sum_{j\in F}\lambda_j a_j(i)=0\qquad(i\in I\setminus A),
\]
即该组合只在 \(A\) 上有支撑，则必须有
\[
\boxed{
\sum_{j\in F}\lambda_j b_j
=
\sum_{i\in A}
\Bigl(\sum_{j\in F}\lambda_j a_j(i)\Bigr)y_i.
}
\tag{1.2}
\]

证明：若 \(x\in\mathcal S\) 延拓 \(y\)，且 \(u\in W\cap U_A\)，则
\[
\langle u,y\rangle=\langle u,x\rangle=\beta(u),
\]
必要性成立。

反之，设 (1.1) 成立。令 \(d=y-x^0|_A\in k^A\)。需要找 \(n\in W^\perp\) 使 \(n|_A=d\)。在有限维空间中
\[
\bigl(\pi_A(W^\perp)\bigr)^\perp=W\cap U_A.
\]
事实上，若 \(u\in W\cap U_A\)，则对 \(n\in W^\perp\) 有 \(\langle u,\pi_A(n)\rangle=\langle u,n\rangle=0\)，故 \(W\cap U_A\subseteq(\pi_A(W^\perp))^\perp\)。反向由 \((W^\perp)^\perp=W\) 得到。因此 \(d\in\pi_A(W^\perp)\) 当且仅当对一切 \(u\in W\cap U_A\)，\(\langle u,d\rangle=0\)。但
\[
\langle u,d\rangle
=\langle u,y\rangle-\langle u,x^0\rangle
=\beta(u)-\beta(u)=0.
\]
所以确有 \(n\in W^\perp\) 使 \(n|_A=d\)，从而 \(x^0+n\in\mathcal S\) 延拓 \(y\)。证毕。

---

## S2 有限域下的精确计数

沿用 S1 的假设，\(|k|=q\)，并令
\[
d=\dim W,\qquad e=\dim(W+U_A).
\]
由于每个非空仿射空间 \(k^r\) 有 \(q^r\) 个元素，S1 给出
\[
\boxed{|\mathcal S|=q^{\,|I|-d}}.
\]
像空间 \(\pi_A(\mathcal S)\) 的仿射维数为
\[
\dim\pi_A(\mathcal S)
=|A|-\dim(W\cap U_A)
=e-d,
\]
故可实现的 \(A\)-坐标个数为
\[
\boxed{
|\pi_A(\mathcal S)|=q^{\,e-d}
=q^{\,\dim(W+U_A)-\dim W}.
}
\]
每个可实现坐标 \(y\in\pi_A(\mathcal S)\) 的完成数为纤维大小，即
\[
\boxed{
|\pi_A^{-1}(y)\cap\mathcal S|
=q^{\,|I|-e}
=q^{\,|I|-\dim(W+U_A)}.
}
\]
这三个公式只用到 \(|I|,|A|,d=\dim W,e=\dim(W+U_A)\)。

---

## S3 有限域的无限坐标拓扑

设 \(k\) 有限且取离散拓扑。对每个 \(j\in J\)，令
\[
\mathcal S_j=\{x\in k^I:\langle a_j,x\rangle=b_j\}.
\]
因为 \(a_j\) 有限支撑，\(\langle a_j,\cdot\rangle:k^I\to k\) 连续，故 \(\mathcal S_j\) 闭。于是
\[
\mathcal S=\bigcap_{j\in J}\mathcal S_j
\]
也是闭集。

有限域 \(k\) 紧，故由 Tychonoff 定理，\(k^I\) 紧。题设说任意有限个方程可解，即任意有限交
\[
\mathcal S_{j_1}\cap\cdots\cap\mathcal S_{j_m}\neq\varnothing.
\]
所以闭集族 \(\{\mathcal S_j\}_{j\in J}\) 具有有限交性质。由 \(k^I\) 的紧性，
\[
\mathcal S=\bigcap_{j\in J}\mathcal S_j\neq\varnothing.
\]
于是 \(\mathcal S\) 是非空紧空间 \(k^I\) 的闭子集，故紧。

再证全不连通。任取 \(x\neq z\in\mathcal S\)，选 \(i\in I\) 使 \(x_i\neq z_i\)。由于 \(k\) 离散，\(\{x_i\}\) 是 \(k\) 中的 clopen 集。于是
\[
U=\pi_i^{-1}(\{x_i\})
\]
是 \(k^I\) 中的 clopen 集，且 \(x\in U\)，\(z\notin U\)。因此 \(U\cap\mathcal S\) 是 \(\mathcal S\) 中分离 \(x,z\) 的 clopen 集。故 \(\mathcal S\) 全不连通。

对任意 \(A\subseteq I\)，\(\pi_A:k^I\to k^A\) 连续，而 \(\mathcal S\) 紧，故 \(\pi_A(\mathcal S)\) 紧；\(k^A\) 是 Hausdorff 空间，紧子集闭。因此
\[
\boxed{\pi_A(\mathcal S)\text{ 在 }k^A\text{ 中是闭集}.}
\]

最后刻画 \(\pi_A(\mathcal S)\)。断言
\[
\boxed{
\pi_A(\mathcal S)
=
\left\{
y\in k^A:
\begin{array}{l}
\text{对每个有限 }F\subseteq J
\text{ 和每个有限 }B\subseteq A,\\
\text{方程组 }\langle a_j,x\rangle=b_j\ (j\in F)
\text{ 与 }x_i=y_i\ (i\in B)
\text{ 在 }k^I\text{ 中同时可解}
\end{array}
\right\}.
}
\tag{3.1}
\]
必要性显然。反之，固定满足右端条件的 \(y\)。对有限 \(F\subseteq J\)、有限 \(B\subseteq A\)，令
\[
C_{F,B}
=
\{x\in k^I:
\langle a_j,x\rangle=b_j\ (j\in F),\ 
x_i=y_i\ (i\in B)\}.
\]
每个 \(C_{F,B}\) 是闭集且非空。该集族具有有限交性质：任意有限多个 \(C_{F_s,B_s}\) 的交等于
\[
C_{\bigcup_s F_s,\bigcup_s B_s},
\]
而由假设它非空。由 \(k^I\) 紧，存在
\[
x\in\bigcap_{F,B}C_{F,B}.
\]
于是 \(x\) 满足所有方程，且对每个 \(i\in A\) 取 \(B=\{i\}\) 得 \(x_i=y_i\)。所以 \(x\in\mathcal S\)，\(\pi_A(x)=y\)。故 (3.1) 成立。

---

## S4 整体对象与全部恢复目标

**结论：S4 所列目标全部成立，不存在反例。** 关键在于
\[
k^I\cong (k^{(I)})^*
\]
作为 \(k\)-向量空间，因此 \(k^I\) 对有限行线性方程组是“代数紧”的。

### 4.1 整体解的存在与分类

令
\[
W=\operatorname{span}_k\{a_j:j\in J\}\subseteq k^{(I)}.
\]
定义
\[
\beta:W\to k,\qquad \beta(a_j)=b_j.
\tag{4.1}
\]
题设的有限可解性等价于 \(\beta\) 良定义。事实上，若
\[
\sum_{j\in F}\lambda_j a_j=0
\]
是有限线性关系，取 \(x\in k^I\) 解有限子系统 \(F\)，则
\[
\sum_{j\in F}\lambda_j b_j
=
\sum_{j\in F}\lambda_j\langle a_j,x\rangle
=
\Bigl\langle\sum_{j\in F}\lambda_j a_j,x\Bigr\rangle
=0.
\]
所以 \(\beta\) 不依赖有限表示。反向由下面的构造立刻得到。

取 \(W\) 的一组 Hamel 基，并扩充为 \(k^{(I)}\) 的一组 Hamel 基。将 \(\beta\) 线性延拓为
\[
\widetilde\beta\in (k^{(I)})^*.
\]
令
\[
x^0_i=\widetilde\beta(e_i)\qquad(i\in I).
\tag{4.2}
\]
则对任意 \(a\in W\)，由于 \(a\) 有限支撑，
\[
\langle a,x^0\rangle
=
\sum_{i\in I}a_i x^0_i
=
\widetilde\beta(a)
=
\beta(a).
\]
特别地
\[
\langle a_j,x^0\rangle=\beta(a_j)=b_j
\qquad(j\in J).
\]
所以 \(\mathcal S\neq\varnothing\)，而且整体解被构造出来了。

定义求值映射
\[
E_W:k^I\to W^*,\qquad
E_W(x)(a)=\langle a,x\rangle.
\]
其核为
\[
\ker E_W=W^\perp
=
\{x\in k^I:\langle a,x\rangle=0\ \forall a\in W\}.
\]
并且 \(E_W\) 是满射：任给 \(\ell\in W^*\)，先把 \(\ell\) 延拓为 \(k^{(I)}\) 上的线性泛函，再如 (4.2) 用它在 \(e_i\) 上的值定义一个 \(x\in k^I\)，便有 \(E_W(x)=\ell\)。于是
\[
\boxed{
\mathcal S=E_W^{-1}(\beta)=x^0+W^\perp.
}
\tag{4.3}
\]
这给出了完整分类：所有解构成一个仿射空间，方向为齐次解空间 \(W^\perp\)。两个解 \(x,x'\) 满足
\[
x-x'\in W^\perp.
\]
还有短正合列
\[
0\longrightarrow W^\perp\longrightarrow k^I
\xrightarrow{\ E_W\ }W^*\longrightarrow 0.
\tag{4.4}
\]
特别地，\(\mathcal S\) 的仿射维数为 \(\dim_k W^\perp\)；若 \(I\) 有限，则它等于 \(|I|-\dim W\)。

### 4.2 每个 \(\pi_A(\mathcal S)\) 的完整描述

设
\[
U_A=\operatorname{span}_k\{e_i:i\in A\}\subseteq k^{(I)},
\qquad
K_A=W\cap U_A.
\]
则
\[
\boxed{
\pi_A(\mathcal S)
=
\left\{
y\in k^A:
\langle u,y\rangle=\beta(u)
\ \text{对一切 }u\in K_A
\right\}.
}
\tag{4.5}
\]
这里 \(u\in K_A\) 在 \(A\) 上有限支撑，所以 \(\langle u,y\rangle\) 是有限和。

必要性：若 \(x\in\mathcal S\) 且 \(x|_A=y\)，\(u\in K_A\)，则
\[
\langle u,y\rangle=\langle u,x\rangle=\beta(u).
\]

充分性：设 \(y\) 满足 (4.5)。令 \(B=I\setminus A\)，并令
\[
\rho_B:W\to k^{(B)},\qquad \rho_B(w)=w|_B,
\qquad W_B=\rho_B(W).
\]
在 \(W_B\) 上定义
\[
\gamma(\rho_B(w))
=
\beta(w)-\langle w|_A,y\rangle.
\tag{4.6}
\]
若 \(\rho_B(w)=0\)，则 \(w\in W\cap U_A=K_A\)，由 (4.5) 得
\[
\beta(w)-\langle w|_A,y\rangle=0,
\]
故 \(\gamma\) 良定义，且显然线性。把 \(\gamma\) 延拓为 \(k^{(B)}\) 上的线性泛函，并由 \(k^B\cong(k^{(B)})^*\) 找到 \(z\in k^B\)，使
\[
\langle v,z\rangle=\gamma(v)\qquad(v\in W_B).
\]
于是对一切 \(w\in W\)，
\[
\langle w|_B,z\rangle
=
\beta(w)-\langle w|_A,y\rangle.
\]
取 \(w=a_j\)，得到
\[
\langle a_j|_B,z\rangle
=
b_j-\langle a_j|_A,y\rangle,
\]
即
\[
\langle a_j,(y,z)\rangle=b_j.
\]
所以 \(x=(y,z)\in\mathcal S\) 且 \(\pi_A(x)=y\)。故 (4.5) 成立。

令
\[
K_A^\perp
=
\{d\in k^A:\langle u,d\rangle=0\ \forall u\in K_A\}.
\]
取 \(y^0=\pi_A(x^0)\)。则
\[
\boxed{
\pi_A(\mathcal S)
=
y^0+K_A^\perp.
}
\tag{4.7}
\]
因此 \(\pi_A(\mathcal S)\) 是一个仿射子空间，其方向为 \(K_A^\perp\)。

把 (4.5) 用给定的有限行写出来就是：
\[
\boxed{
\begin{aligned}
y\in\pi_A(\mathcal S)
\iff{}&
\text{对每个有限 }F\subseteq J
\text{ 和每个 }\lambda\in k^F,\\
&\sum_{j\in F}\lambda_j a_j(i)=0\quad(i\in B)
\\
&\Longrightarrow\quad
\sum_{j\in F}\lambda_j b_j
=
\sum_{i\in A}
\Bigl(\sum_{j\in F}\lambda_j a_j(i)\Bigr)y_i.
\end{aligned}
}
\tag{4.8}
\]
因为每个 \(a_j\) 有限支撑，所以每个方程只涉及有限个坐标。

### 4.3 所有非空纤维的完整描述

固定 \(y\in\pi_A(\mathcal S)\)，取 \(x_y\in\mathcal S\) 使 \(\pi_A(x_y)=y\)。则纤维
\[
F_y=\pi_A^{-1}(y)\cap\mathcal S
\]
满足
\[
\boxed{
F_y=x_y+N_A,
\qquad
N_A=\{n\in W^\perp:n|_A=0\}.
}
\tag{4.9}
\]
事实上，若 \(x\in F_y\)，则 \(x-x_y\in W^\perp\) 且 \(x-x_y\) 在 \(A\) 上为零；反之加上 \(N_A\) 中元素仍解方程且保持 \(A\)-坐标不变。

用 \(B=I\setminus A\) 描述：
\[
\boxed{
N_A\cong (W_B)^\perp
=
\{z\in k^B:\langle b,z\rangle=0\ \forall b\in W_B\}.
}
\tag{4.10}
\]
同构由 \(n\mapsto n|_B\) 给出。于是
\[
\boxed{
F_y
=
\left\{
(y,z_y+n):\ n\in (W_B)^\perp
\right\},
}
\tag{4.11}
\]
其中 \(z_y\in k^B\) 是调整后系统
\[
\langle a_j|_B,z\rangle
=
b_j-\langle a_j|_A,y\rangle
\qquad(j\in J)
\tag{4.12}
\]
的任意一个解。由 (4.5) 可知，(4.12) 当且仅当 \(y\in\pi_A(\mathcal S)\) 时有解。

因此：

- 空纤维恰好是 \(y\notin\pi_A(\mathcal S)\)；
- 每个非空纤维都是同一个向量空间 \((W_B)^\perp\) 的平移；
- 所有非空纤维两两不交，并划分整个 \(\mathcal S\)；
- 每个非空纤维的仿射维数为
\[
\boxed{
\dim_k F_y=\dim_k (W_B)^\perp.
}
\]
若 \(I\) 有限，则
\[
\dim F_y=|I|-|A|-\dim W_B
=|I|-\dim(W+U_A),
\]
与 S1 一致。

此外还有短正合列
\[
0\longrightarrow N_A\longrightarrow W^\perp
\xrightarrow{\ \pi_A\ } K_A^\perp\longrightarrow 0,
\tag{4.13}
\]
以及
\[
W/K_A\cong W_B.
\tag{4.14}
\]
这些空间和映射只由给定的系数 \(a_j\) 和常数 \(b_j\) 决定（\(W,\beta,K_A,W_B\) 都由它们定义），所以 S4 要求的整体解、解集、像和全部纤维均已构造并分类完毕。

---

## S5 赋值空间 \(k^{(\mathbb N)}\) 上的支持问题

**结论：不一定。反例对所有域 \(k\) 都成立。**

取变量 \(x_0,x_1,x_2,\dots\)，考虑系统
\[
x_0=1,
\qquad
x_n-x_{n+1}=0\quad(n=0,1,2,\dots).
\tag{5.1}
\]
每行显然有限支撑。

任取有限子系统。设其中涉及的等式的指标集合为有限集 \(E\)，并可能含有方程 \(x_0=1\)。在无向图 \(\mathbb N\) 上画出边 \(\{n,n+1\}\)（\(n\in E\)）。令 \(C\) 为顶点 \(0\) 在该有限图中的连通分量（若子系统不含 \(x_0=1\)，则令 \(C=\varnothing\)）。定义
\[
x_n=
\begin{cases}
1,&n\in C,\\
0,&n\notin C.
\end{cases}
\]
因为图有限，\(C\) 有限，所以 \(x=(x_n)\in k^{(\mathbb N)}\)。它满足所选的所有等式；若 \(x_0=1\) 被选中，则 \(0\in C\)，故 \(x_0=1\)。因此每个有限子系统在 \(k^{(\mathbb N)}\) 中都有解。

但全系统 (5.1) 迫使
\[
x_0=x_1=x_2=\cdots,
\qquad x_0=1,
\]
即 \(x_n=1\) 对所有 \(n\) 成立。这不是有限支撑函数。因此
\[
\boxed{
\text{全体解在 }k^{(\mathbb N)}\text{ 中不存在}.
}
\]
故 S5 的命题为假。

---

## S6 无限域下的坐标像

**结论：即使 \(k\) 无限，\(\pi_A(\mathcal S)\) 仍在 \(k^A\) 的乘积拓扑中闭。**

继续使用 S4 的记号：
\[
K_A=W\cap U_A.
\]
由 S4 的 (4.5)，
\[
\pi_A(\mathcal S)
=
\bigcap_{u\in K_A}
\left\{
y\in k^A:
\ell_u(y)=\beta(u)
\right\},
\tag{6.1}
\]
其中
\[
\ell_u(y)=\langle u,y\rangle
=
\sum_{i\in A}u(i)y_i.
\]
因为 \(u\in W\subseteq k^{(I)}\) 有限支撑，\(\ell_u:k^A\to k\) 只依赖于有限个坐标，所以连续。\(k\) 离散，\(\{\beta(u)\}\) 闭，因此
\[
\ell_u^{-1}(\beta(u))
\]
在 \(k^A\) 中闭。任意多个闭集的交仍闭，所以
\[
\boxed{\pi_A(\mathcal S)\text{ 在 }k^A\text{ 中闭}.}
\]

这就是只涉及有限坐标的闭方程描述：
\[
\boxed{
y\in\pi_A(\mathcal S)
\iff
\sum_{i\in A}u(i)y_i=\beta(u)
\quad\text{对一切 }u\in W\cap U_A.
}
\tag{6.2}
\]
每一条方程只涉及 \(\operatorname{supp}u\subseteq A\) 这有限个坐标。等价地，也可写成 S4 的 (4.8)：对每个有限 \(F\subseteq J\) 和 \(\lambda\in k^F\)，若
\[
\sum_{j\in F}\lambda_j a_j(i)=0
\qquad(i\in I\setminus A),
\]
则
\[
\sum_{j\in F}\lambda_j b_j
=
\sum_{i\in A}
\Bigl(\sum_{j\in F}\lambda_j a_j(i)\Bigr)y_i.
\tag{6.3}
\]
这也是一族每条只涉及有限个 \(A\)-坐标的闭方程。

这里不需要 \(k^A\) 紧；当 \(k\) 无限时 \(k^A\) 一般不紧，S3 的紧性论证不能直接使用，但上面的线性方程描述仍然给出闭性。

此外，S3 中“有限行与有限 \(A\)-坐标限制同时可实现”的刻画在无限域下也仍然成立：
\[
y\in\pi_A(\mathcal S)
\iff
\begin{array}{l}
\text{对每个有限 }F\subseteq J\text{ 和有限 }B\subseteq A,\\
\{x:\langle a_j,x\rangle=b_j\ (j\in F),\ x_i=y_i\ (i\in B)\}
\neq\varnothing.
\end{array}
\]
证明可由 (4.5) 得到：取 \(u\in W\cap U_A\) 的有限表示 \(u=\sum_{j\in F}\lambda_j a_j\)，再取 \(B=\operatorname{supp}u\)，有限可实现性即给出 \(\langle u,y\rangle=\beta(u)\)。