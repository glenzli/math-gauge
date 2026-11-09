下面给出一种统一表述：用**扩展非负矩阵**描述各输入、输出伪度量分量之间的上、下 Lipschitz 估计；再用**布尔零化矩阵**描述“某类输入之间的差异在输出中消失”。两者可以通过零距离关系联系起来。

## 1. 距离向量与矩阵作用

设
\[
(\mathcal X,\mathcal G=\{d_i\}_{i\in I},\bot_{\mathcal X}),\qquad
(\mathcal Y,\mathcal H=\{e_j\}_{j\in J},\bot_{\mathcal Y})
\]
为两个扩展规范空间，其中 \(I,J\) 均有限非空。考虑保吸收元的总函数
\[
f:\mathcal X\to\mathcal Y,\qquad f(\bot_{\mathcal X})=\bot_{\mathcal Y}.
\]
当 \(\mathcal X=\mathcal Y\) 时，这就是题设中的算子。

记输入、输出距离向量为
\[
\mathbf d(x,y):=(d_i(x,y))_{i\in I}\in\bar{\mathbb R}_+^I,
\]
\[
\mathbf e_f(x,y):=(e_j(fx,fy))_{j\in J}\in\bar{\mathbb R}_+^J.
\]

对矩阵 \(A=(a_{ji})\in\bar{\mathbb R}_+^{J\times I}\)，定义
\[
(A\mathbf d(x,y))_j:=\sum_{i\in I}a_{ji}d_i(x,y).
\]
这里严格采用题设约定，特别是 \(0\cdot(+\infty)=0\)。

以下只使用扩展非负实数加法、乘法的单调性和有限分配律，不使用减法或除法。

---

## 2. 上、下 Lipschitz 矩阵

### 定义 1：上 Lipschitz 矩阵

称 \(U=(u_{ji})\in\bar{\mathbb R}_+^{J\times I}\) 是 \(f\) 的一个**上 Lipschitz 矩阵**，如果
\[
\boxed{\ \mathbf e_f(x,y)\le U\mathbf d(x,y)\ }
\qquad(x,y\in\mathcal X),
\]
即对每个 \(j\in J\)，
\[
e_j(fx,fy)\le \sum_{i\in I}u_{ji}d_i(x,y).
\]

其第 \(j\) 行描述：输入各分量的距离如何共同控制第 \(j\) 个输出分量。

### 定义 2：下 Lipschitz 矩阵

称 \(L=(\ell_{ji})\in\bar{\mathbb R}_+^{J\times I}\) 是 \(f\) 的一个**下 Lipschitz 矩阵**，如果
\[
\boxed{\ L\mathbf d(x,y)\le \mathbf e_f(x,y)\ }
\qquad(x,y\in\mathcal X),
\]
即
\[
\sum_{i\in I}\ell_{ji}d_i(x,y)\le e_j(fx,fy).
\]

若同时有
\[
L\mathbf d(x,y)\le \mathbf e_f(x,y)\le U\mathbf d(x,y),
\]
则称 \((L,U)\) 给出 \(f\) 的一组**双边矩阵 Lipschitz 估计**。这不预设 \(f\) 是双射。

当 \(I,J\) 都只有一个元素时，以上恰好退化为
\[
\ell\,d(x,y)\le e(fx,fy)\le u\,d(x,y),
\]
即通常的上、下 Lipschitz 常数，只是现在允许取 \(+\infty\)。

### 线性例子

把 \(\mathbb R^n,\mathbb R^m\) 分别配上坐标距离
\[
d_i(x,y)=|x_i-y_i|,\qquad e_j(u,v)=|u_j-v_j|,
\]
并各添加一个与所有非吸收点距离为 \(+\infty\) 的吸收元。对线性映射 \(T:\mathbb R^n\to\mathbb R^m\)，令其在吸收元上保持不变。由三角不等式，
\[
|(Tx-Ty)_j|
\le \sum_i |t_{ji}|\,|x_i-y_i|,
\]
所以绝对值矩阵
\[
U=|T|=(|t_{ji}|)
\]
是上 Lipschitz 矩阵。若 \(T=\operatorname{diag}(\lambda_1,\dots,\lambda_n)\)，则
\[
L=U=\operatorname{diag}(|\lambda_1|,\dots,|\lambda_n|)
\]
同时也是下 Lipschitz 矩阵。

---

## 3. 序、恒等映射与复合

矩阵采用逐项偏序：
\[
A\le B\quad\Longleftrightarrow\quad a_{ji}\le b_{ji}\ \forall j,i.
\]

记
\[
\mathcal U(f):=\{U:U\text{ 是 }f\text{ 的上矩阵}\},\qquad
\mathcal L(f):=\{L:L\text{ 是 }f\text{ 的下矩阵}\}.
\]

### 命题 1：单调性

1. 若 \(U\in\mathcal U(f)\) 且 \(U\le U'\)，则 \(U'\in\mathcal U(f)\)。
2. 若 \(L\in\mathcal L(f)\) 且 \(L'\le L\)，则 \(L'\in\mathcal L(f)\)。

因此 \(\mathcal U(f)\) 是向上封闭的，\(\mathcal L(f)\) 是向下封闭的。特别地，零矩阵永远是下矩阵。

**证明。** 由扩展非负实数运算的单调性，
\[
U\mathbf d\le U'\mathbf d,\qquad L'\mathbf d\le L\mathbf d,
\]
代入定义即可。 \(\square\)

所以一般应谈“一个可容许矩阵”，而不是预设存在唯一的“Lipschitz 矩阵”。

### 命题 2：恒等映射

单位矩阵
\[
(\mathrm I)_{ii'}=
\begin{cases}
1,&i=i',\\
0,&i\neq i'
\end{cases}
\]
既是恒等映射的上矩阵，也是下矩阵。

**证明。** 此时矩阵作用后只留下 \(1\cdot d_i(x,y)\)，其余项均为 \(0\cdot d_{i'}(x,y)=0\)，故两边实际都是等式。 \(\square\)

### 命题 3：复合对应矩阵乘积

再设第三个规范空间具有距离分量 \(h_k\)，\(k\in K\)。若
\[
f:\mathcal X\to\mathcal Y,\qquad g:\mathcal Y\to\mathcal Z
\]
均保吸收元，则：

- \(U\in\mathcal U(f)\)、\(V\in\mathcal U(g)\) 蕴含 \(VU\in\mathcal U(g\circ f)\)；
- \(L\in\mathcal L(f)\)、\(M\in\mathcal L(g)\) 蕴含 \(ML\in\mathcal L(g\circ f)\)。

矩阵乘积按通常公式定义：
\[
(VU)_{ki}=\sum_{j\in J}v_{kj}u_{ji}.
\]

**证明。** 上界情形，对每个 \(k\)，
\[
\begin{aligned}
h_k(gfx,gfy)
&\le \sum_j v_{kj}e_j(fx,fy)\\
&\le \sum_jv_{kj}\sum_i u_{ji}d_i(x,y)\\
&=\sum_i\left(\sum_jv_{kj}u_{ji}\right)d_i(x,y).
\end{aligned}
\]
最后一步使用有限和的交换及扩展非负乘法的分配律。下界情形把所有不等号反向即可。 \(\square\)

因此，双边估计也按
\[
(L,U),\ (M,V)\quad\longmapsto\quad(ML,VU)
\]
复合。

---

## 4. \(+\infty\) 的准确含义

扩展系数并非简单的“忽略此约束”，因为 \(0\cdot(+\infty)=0\)。

- 若 \(u_{ji}=+\infty\) 且 \(d_i(x,y)>0\)，则该输出行的右端为 \(+\infty\)，这一行对该对点不再有上界限制。
- 若 \(u_{ji}=+\infty\) 且 \(d_i(x,y)=0\)，该项贡献仍为 \(0\)。
- 若 \(\ell_{ji}=+\infty\) 且 \(d_i(x,y)>0\)，下界条件强制
  \[
  e_j(fx,fy)=+\infty.
  \]

### 定理 1：扩展上矩阵存在的充要条件

令 \(\boldsymbol\infty\) 表示所有元素均为 \(+\infty\) 的 \(J\times I\) 矩阵。则以下三命题等价：

1. \(f\) 至少有一个上 Lipschitz 矩阵；
2. \(f\) 保持“族不可区分性”，即
   \[
   \mathbf d(x,y)=0
   \quad\Longrightarrow\quad
   \mathbf e_f(x,y)=0;
   \]
3. \(\boldsymbol\infty\in\mathcal U(f)\)。

**证明。** 对任意矩阵 \(A\)，若 \(\mathbf d(x,y)=0\)，则
\[
(A\mathbf d(x,y))_j=\sum_i a_{ji}\cdot0=0.
\]
故任何上矩阵都强制 \(\mathbf e_f(x,y)=0\)，得到 \(1\Rightarrow2\)。

另一方面，直接由题设算术可得
\[
(\boldsymbol\infty\mathbf d(x,y))_j=
\begin{cases}
0,&\mathbf d(x,y)=0,\\[2pt]
+\infty,&\mathbf d(x,y)\neq0.
\end{cases}
\]
因此条件 2 正好保证 \(\boldsymbol\infty\) 是上矩阵，即 \(2\Rightarrow3\)；而 \(3\Rightarrow1\) 显然。 \(\square\)

特别地：

- 若输入族 \(\mathcal G\) 分离点，则 \(\mathbf d(x,y)=0\Rightarrow x=y\)，条件 2 自动成立，所以**每个保吸收元映射都有扩展上矩阵**，至少可以取 \(\boldsymbol\infty\)。
- 若不预设族分离性，则任意映射未必有上矩阵。例如，若
  \[
  d_i(x,y)=0\ \forall i,\qquad e_j(fx,fy)>0
  \]
  对某对点和某个 \(j\) 成立，那么即使允许所有系数为 \(+\infty\)，也不可能满足上界条件。

这不是定义缺陷，而是伪度量零距离和 \(0\cdot\infty=0\) 共同决定的必要兼容性。

---

## 5. 吸收元对上、下矩阵的强制作用

吸收元隔离会使某些看似普通的矩阵条件变得很强。

### 命题 4：上矩阵的零行

若 \(U\in\mathcal U(f)\) 的第 \(j_0\) 行全为零，则
\[
f(x)=\bot_{\mathcal Y}\qquad(x\in\mathcal X).
\]
即 \(f\) 只能是恒取吸收元的映射。

**证明。** 零行给出
\[
e_{j_0}(fx,fy)\le0,
\]
故对所有 \(x,y\) 都有 \(e_{j_0}(fx,fy)=0\)。取 \(y=\bot_{\mathcal X}\)，则 \(fy=\bot_{\mathcal Y}\)。若某个 \(x\neq\bot_{\mathcal X}\) 满足 \(fx\neq\bot_{\mathcal Y}\)，吸收元隔离给出
\[
e_{j_0}(fx,\bot_{\mathcal Y})=+\infty,
\]
矛盾。因此所有非吸收输入也都映到 \(\bot_{\mathcal Y}\)。 \(\square\)

反之，若 \(f\equiv\bot_{\mathcal Y}\)，则任何矩阵都是它的上矩阵。

### 命题 5：非零下矩阵强制完全有定义

若 \(L\in\mathcal L(f)\) 且 \(L\neq0\)，则
\[
\mathcal X\setminus\{\bot_{\mathcal X}\}\subseteq\operatorname{dom}(f).
\]
换言之，对任意 \(x\neq\bot_{\mathcal X}\)，都有 \(fx\neq\bot_{\mathcal Y}\)。

**证明。** 取 \(\ell_{j_0i_0}>0\)。对任意 \(x\neq\bot_{\mathcal X}\)，有 \(d_{i_0}(x,\bot_{\mathcal X})=+\infty\)，从而
\[
e_{j_0}(fx,\bot_{\mathcal Y})
\ge \sum_i\ell_{j_0i}d_i(x,\bot_{\mathcal X})
\ge \ell_{j_0i_0}\cdot(+\infty)=+\infty.
\]
若 \(fx=\bot_{\mathcal Y}\)，左端为 \(0\)，矛盾。 \(\square\)

等价地，如果某个非吸收输入被 \(f\) 映为吸收元，那么 \(f\) 的下矩阵只有零矩阵。

---

## 6. 不可区分性的零化矩阵

这里把“输入落入一定范畴”形式化为输入区域 \(S_\alpha\subseteq\mathcal X\)。更一般地，可以直接给定一族输入关系
\[
\mathscr R=\{R_\alpha\}_{\alpha\in\mathfrak A},\qquad
R_\alpha\subseteq\mathcal X\times\mathcal X.
\]
取 \(R_\alpha=S_\alpha\times S_\alpha\) 即表示“两个输入都属于第 \(\alpha\) 类”。

### 定义 3：零化矩阵

称布尔矩阵
\[
C=(c_{j\alpha})\in\{0,1\}^{J\times\mathfrak A}
\]
是 \(f\) 关于 \(\mathscr R\) 的一个**零化矩阵**或**不可区分矩阵**，如果
\[
\boxed{
c_{j\alpha}=1
\quad\Longrightarrow\quad
\bigl((x,y)\in R_\alpha\Rightarrow e_j(fx,fy)=0\bigr).
}
\]
元素 \(0\) 不作任何断言。

当 \(R_\alpha=S_\alpha\times S_\alpha\) 时，\(c_{j\alpha}=1\) 就表示：
\[
x,y\in S_\alpha\quad\Longrightarrow\quad e_j(fx,fy)=0.
\]
若某一列全为 \(1\)，则该关系下的两个输出对所有 \(e_j\) 都不可区分。

由于没有预设族分离性，这里的“不可区分”**不等于输出相等**；只有 \(\mathcal H\) 分离点时，才能进一步推出 \(fx=fy\)。

### 最大零化矩阵

存在逐项最大的零化矩阵 \(C_f^{\mathscr R}\)：
\[
(C_f^{\mathscr R})_{j\alpha}=1
\quad\Longleftrightarrow\quad
R_\alpha\subseteq
\{(x,y):e_j(fx,fy)=0\}.
\]
一个布尔矩阵是零化矩阵，当且仅当它逐项不超过 \(C_f^{\mathscr R}\)。因此零矩阵总是成立，而增加一个 \(1\) 就是增加一条实质断言。

若 \(S_\alpha\) 含有 \(\bot_{\mathcal X}\)，且 \(c_{j\alpha}=1\)，则对任意 \(x\in S_\alpha\)，由 \((x,\bot_{\mathcal X})\in R_\alpha\) 得
\[
e_j(fx,\bot_{\mathcal Y})=0.
\]
吸收元隔离遂强制 \(fx=\bot_{\mathcal Y}\)。所以含吸收元的输入区域上的零化，实际上意味着该区域全部被映为吸收元。

---

## 7. 零化矩阵的复合与 Lipschitz 矩阵的联系

### 7.1 布尔矩阵乘积描述复合

设 \(f:\mathcal X\to\mathcal Y\)、\(g:\mathcal Y\to\mathcal Z\)。令
\[
Z_j^{\mathcal Y}:=\{(u,v)\in\mathcal Y^2:e_j(u,v)=0\}.
\]
取 \(\Gamma^g\in\{0,1\}^{K\times J}\) 为 \(g\) 关于关系族 \(\{Z_j^{\mathcal Y}\}_{j\in J}\) 的零化矩阵，即
\[
\Gamma^g_{kj}=1
\Longrightarrow
\bigl(e_j(u,v)=0\Rightarrow h_k(gu,gv)=0\bigr).
\]
若 \(C^f\) 是 \(f\) 关于 \(\mathscr R\) 的零化矩阵，定义布尔乘积
\[
(\Gamma^g\star C^f)_{k\alpha}
:=\bigvee_{j\in J}
\bigl(\Gamma^g_{kj}\wedge C^f_{j\alpha}\bigr).
\]
则 \(\Gamma^g\star C^f\) 是 \(g\circ f\) 关于 \(\mathscr R\) 的零化矩阵。

**证明。** 若乘积的某元素为 \(1\，则存在 \(j\) 使两个因子均为 \(1\)。于是
\[
(x,y)\in R_\alpha
\Longrightarrow e_j(fx,fy)=0
\Longrightarrow h_k(gfx,gfy)=0.
\]
这正是所需结论。 \(\square\)

这与数值 Lipschitz 矩阵在复合下做普通矩阵乘积形成了直接类比。

### 7.2 从上 Lipschitz 矩阵提取零化信息

上矩阵的零化信息由每行的支撑决定。注意到
\[
(U\mathbf d(x,y))_j=0
\quad\Longleftrightarrow\quad
\forall i,\quad u_{ji}=0\ \text{或}\ d_i(x,y)=0.
\]
因此，若 \(U\in\mathcal U(f)\)，并且
\[
R_\alpha\subseteq
\bigcap_{i:\,u_{ji}>0}\{(x,y):d_i(x,y)=0\},
\]
则可以令零化矩阵的 \(c_{j\alpha}=1\)。因为此时上界右端为零，故 \(e_j(fx,fy)=0\)。

特别地，零行的支撑为空，所以它对每个输出分量都给出全局零化；这与命题 4 的强结论一致。

此外，取单一关系
\[
R_{\mathcal G}:=\{(x,y):\mathbf d(x,y)=0\},
\]
则定理 1 可以重新表述为：
\[
\mathcal U(f)\neq\varnothing
\quad\Longleftrightarrow\quad
f\text{ 在 }R_{\mathcal G}\text{ 上对所有输出分量零化}
\quad\Longleftrightarrow\quad
\boldsymbol\infty\in\mathcal U(f).
\]

### 7.3 下 Lipschitz 矩阵对零化的限制

若 \(L\in\mathcal L(f)\)，且某零化矩阵满足 \(c_{j\alpha}=1\)，则对 \((x,y)\in R_\alpha\)，
\[
0\le \sum_i\ell_{ji}d_i(x,y)
\le e_j(fx,fy)=0.
\]
故必须有
\[
\ell_{ji}d_i(x,y)=0\qquad\forall i.
\]
等价地，只要 \(\ell_{ji}>0\)，就必有
\[
R_\alpha\subseteq\{(x,y):d_i(x,y)=0\}.
\]
因此，正的下界系数会排除相应正距离输入对上的输出零化。

---

## 总结

这套定义把三种信息放在同一个分量式框架中：

\[
\boxed{
\begin{array}{ll}
\text{上矩阵 }U:&
\mathbf e_f\le U\mathbf d,\\[2pt]
\text{下矩阵 }L:&
L\mathbf d\le\mathbf e_f,\\[2pt]
\text{零化矩阵 }C:&
c_{j\alpha}=1\Rightarrow
R_\alpha\subseteq\{e_j(fx,fy)=0\}.
\end{array}}
\]

它们分别满足：

- 上矩阵向上封闭，下矩阵向下封闭；
- 上、下矩阵在复合下均按普通非负矩阵乘积传播；
- 零化矩阵在适当复合下按布尔矩阵乘积传播；
- 允许 \(+\infty\) 后，上矩阵存在恰好等价于保持输入族不可区分性；
- 吸收元使“上矩阵零行”和“非零下矩阵”分别具有全局未定义、全局有定义的强含义；
- 所有“不可区分”结论都只用零距离表述，不偷偷使用未预设的族分离性。