# 扩展规范空间上的矩阵 Lipschitz 估计与零化矩阵

下面用**扩展非负矩阵**统一描述各输入、输出伪度量分量之间的上、下 Lipschitz 估计，再用**布尔零化矩阵**描述“某类输入之间的差异在输出中消失”。两者可以通过零距离关系直接联系。

## 1. 距离向量与矩阵作用

设
\[
(\mathcal X,\mathcal G=\{d_i\}_{i\in I},\bot_{\mathcal X}),\qquad
(\mathcal Y,\mathcal H=\{e_j\}_{j\in J},\bot_{\mathcal Y})
\]
为两个扩展规范空间，其中 \(I,J\) 有限非空。考虑保吸收元的总函数
\[
f:\mathcal X\to\mathcal Y,\qquad f(\bot_{\mathcal X})=\bot_{\mathcal Y}.
\]
当 \(\mathcal X=\mathcal Y\) 时，这就是题设中的算子。

记输入、输出距离向量为
\[
\mathbf d(x,y):=(d_i(x,y))_{i\in I}\in\bar{\mathbb R}_+^I,
\qquad
\mathbf e_f(x,y):=(e_j(fx,fy))_{j\in J}\in\bar{\mathbb R}_+^J.
\]

对 \(A=(a_{ji})\in\bar{\mathbb R}_+^{J\times I}\)，定义
\[
(A\mathbf d(x,y))_j:=\sum_{i\in I}a_{ji}d_i(x,y).
\]
这里严格采用题设扩展算术，特别是 \(0\cdot(+\infty)=0\)。以下只使用扩展非负实数加法、乘法的单调性及有限分配律。

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
e_j(fx,fy)\le\sum_{i\in I}u_{ji}d_i(x,y).
\]

第 \(j\) 行描述输入各分量距离如何共同控制第 \(j\) 个输出分量。

### 定义 2：下 Lipschitz 矩阵

称 \(L=(\ell_{ji})\in\bar{\mathbb R}_+^{J\times I}\) 是 \(f\) 的一个**下 Lipschitz 矩阵**，如果
\[
\boxed{\ L\mathbf d(x,y)\le\mathbf e_f(x,y)\ }
\qquad(x,y\in\mathcal X),
\]
即
\[
\sum_{i\in I}\ell_{ji}d_i(x,y)\le e_j(fx,fy).
\]

若同时有
\[
L\mathbf d(x,y)\le\mathbf e_f(x,y)\le U\mathbf d(x,y),
\]
则称 \((L,U)\) 给出 \(f\) 的一组**双边矩阵 Lipschitz 估计**。这不预设 \(f\) 是双射。

当 \(I,J\) 均只有一个元素时，定义退化为
\[
\ell\,d(x,y)\le e(fx,fy)\le u\,d(x,y),
\]
只是现在允许系数取 \(+\infty\)。

扩展系数的准确含义是：

- 若 \(u_{ji}=+\infty\) 且 \(d_i(x,y)>0\)，该行右端为 \(+\infty\)，对这一对点不再给出有限上界；
- 若 \(u_{ji}=+\infty\) 但 \(d_i(x,y)=0\)，该项仍贡献 \(0\)；
- 若 \(\ell_{ji}=+\infty\) 且 \(d_i(x,y)>0\)，下界条件强制 \(e_j(fx,fy)=+\infty\)。

---

## 3. 序、恒等映射与复合

矩阵采用逐项偏序：
\[
A\le B\quad\Longleftrightarrow\quad a_{ji}\le b_{ji}\quad\forall j,i.
\]
记 \(\mathcal U(f)\)、\(\mathcal L(f)\) 分别为 \(f\) 的上、下矩阵集合。

### 命题 1：单调性

1. 若 \(U\in\mathcal U(f)\) 且 \(U\le U'\)，则 \(U'\in\mathcal U(f)\)。
2. 若 \(L\in\mathcal L(f)\) 且 \(L'\le L\)，则 \(L'\in\mathcal L(f)\)。

因此 \(\mathcal U(f)\) 向上封闭，\(\mathcal L(f)\) 向下封闭。特别地，零矩阵永远是下矩阵。

**证明。** 由扩展非负运算的单调性，
\[
U\mathbf d\le U'\mathbf d,\qquad L'\mathbf d\le L\mathbf d,
\]
代入定义即可。 \(\square\)

所以通常应谈“一个可容许矩阵”，而不是预设存在唯一的“Lipschitz 矩阵”。

### 命题 2：恒等映射

当输入、输出规范空间相同时，单位矩阵既是恒等映射的上矩阵，也是下矩阵。

**证明。** 单位矩阵作用后只留下 \(1\cdot d_i(x,y)\)，其余项均为 \(0\cdot d_{i'}(x,y)=0\)，故两边实际都是等式。 \(\square\)

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
&\le\sum_jv_{kj}e_j(fx,fy)\\
&\le\sum_jv_{kj}\sum_i u_{ji}d_i(x,y)\\
&=\sum_i\left(\sum_jv_{kj}u_{ji}\right)d_i(x,y).
\end{aligned}
\]
最后一步使用有限和交换及扩展非负乘法的分配律。下界情形将所有不等号反向即可。 \(\square\)

因此双边估计按
\[
(L,U),\ (M,V)\quad\longmapsto\quad(ML,VU)
\]
复合。

---

## 4. 扩展上矩阵存在的充要条件

令
\[
Z_{\mathcal G}:=\{(x,y)\in\mathcal X^2:\mathbf d(x,y)=0\}.
\]
每个单独零距离关系 \(\{d_i=0\}\) 都是等价关系：自反、对称由定义可得，传递性来自三角不等式。因此 \(Z_{\mathcal G}\) 也是等价关系，称为输入的**族不可区分关系**。

令 \(\boldsymbol\infty\) 表示所有元素均为 \(+\infty\) 的 \(J\times I\) 矩阵。

### 定理 1

以下三命题等价：

1. \(f\) 至少有一个上 Lipschitz 矩阵；
2. \(f\) 保持族不可区分性，即
   \[
   \mathbf d(x,y)=0\quad\Longrightarrow\quad\mathbf e_f(x,y)=0;
   \]
3. \(\boldsymbol\infty\in\mathcal U(f)\)。

**证明。** 对任意矩阵 \(A\)，若 \(\mathbf d(x,y)=0\)，则
\[
(A\mathbf d(x,y))_j=\sum_i a_{ji}\cdot0=0.
\]
故任何上矩阵都强制 \(\mathbf e_f(x,y)=0\)，得到 \(1\Rightarrow2\)。

另一方面，由扩展算术，
\[
(\boldsymbol\infty\mathbf d(x,y))_j=
\begin{cases}
0,&\mathbf d(x,y)=0,\\[2pt]
+\infty,&\mathbf d(x,y)\neq0.
\end{cases}
\]
所以条件 2 正好保证 \(\boldsymbol\infty\) 是上矩阵，即 \(2\Rightarrow3\)；而 \(3\Rightarrow1\) 显然。 \(\square\)

特别地：

- 若输入族 \(\mathcal G\) 分离点，则 \(\mathbf d(x,y)=0\Rightarrow x=y\)，条件 2 自动成立，所以**每个保吸收元映射都有扩展上矩阵**，至少可以取 \(\boldsymbol\infty\)。
- 若不预设族分离性，则任意映射未必有上矩阵。若某对点满足 \(\mathbf d(x,y)=0\) 而某个 \(e_j(fx,fy)>0\)，即使所有系数都允许取 \(+\infty\)，上界右端仍为零，不可能满足要求。

因此，允许 \(+\infty\) 并没有绕过零距离兼容性，而是把这一必要条件精确显现出来。

---

## 5. 吸收元作用的充要化简

记
\[
\mathcal X^\circ:=\mathcal X\setminus\{\bot_{\mathcal X}\},\qquad
\mathcal Y^\circ:=\mathcal Y\setminus\{\bot_{\mathcal Y}\}.
\]
吸收元隔离使上、下矩阵在混合点对 \((x,\bot_{\mathcal X})\) 上具有很强、但可以完全分类的条件。

### 定理 2

1. **上矩阵。** 若 \(f\equiv\bot_{\mathcal Y}\)，则任何矩阵都是它的上矩阵。若 \(f\) 不恒等于吸收元，则 \(U\) 是上矩阵，当且仅当：
   - \(U\) 没有全零行；
   - 对所有 \(x,y\in\mathcal X^\circ\)，有
     \[
     \mathbf e_f(x,y)\le U\mathbf d(x,y).
     \]

2. **下矩阵。** 零矩阵总是下矩阵。若 \(L\neq0\)，则 \(L\) 是下矩阵，当且仅当：
   - \(f(\mathcal X^\circ)\subseteq\mathcal Y^\circ\)，即 \(\mathcal X^\circ\subseteq\operatorname{dom}(f)\)；
   - 对所有 \(x,y\in\mathcal X^\circ\)，有
     \[
     L\mathbf d(x,y)\le\mathbf e_f(x,y).
     \]

**证明。**

先证上矩阵情形。若 \(f\) 不恒等于吸收元，可取 \(x_0\in\mathcal X^\circ\) 使 \(fx_0\neq\bot_{\mathcal Y}\)。若 \(U\) 的第 \(j_0\) 行全零，则在点对 \((x_0,\bot_{\mathcal X})\) 上有
\[
e_{j_0}(fx_0,\bot_{\mathcal Y})=+\infty,\qquad
(U\mathbf d(x_0,\bot_{\mathcal X}))_{j_0}=0,
\]
矛盾。故上矩阵不能有零行。

反之，若 \(U\) 没有零行，且非吸收点对上的不等式成立，则对 \(x\in\mathcal X^\circ\)，每一行都至少有一个正系数 \(u_{ji}\)，从而
\[
(U\mathbf d(x,\bot_{\mathcal X}))_j=+\infty.
\]
所以混合点对上的上界自动成立；\((\bot_{\mathcal X},\bot_{\mathcal X})\) 处两边均为零。

再证下矩阵情形。若 \(L\neq0\)，取 \(\ell_{j_0i_0}>0\)。如果某个 \(x\in\mathcal X^\circ\) 满足 \(fx=\bot_{\mathcal Y}\)，则
\[
\sum_i\ell_{j_0i}d_i(x,\bot_{\mathcal X})
\ge \ell_{j_0i_0}\cdot(+\infty)=+\infty,
\]
但
\[
e_{j_0}(fx,f\bot_{\mathcal X})
=e_{j_0}(\bot_{\mathcal Y},\bot_{\mathcal Y})=0,
\]
与下界条件矛盾。因此 \(f\) 必须在所有非吸收输入上有定义。

反之，若这一有定义条件成立，则对任意 \(x\in\mathcal X^\circ\)，都有 \(fx\neq\bot_{\mathcal Y}\)，故
\[
e_j(fx,\bot_{\mathcal Y})=+\infty.
\]
混合点对上的下界自动成立，而吸收元自身点对处两边均为零。 \(\square\)

由此直接得到：

- 上矩阵只要有一个零行，就强制 \(f\equiv\bot_{\mathcal Y}\)；
- 非零下矩阵强制所有非吸收输入都属于 \(\operatorname{dom}(f)\)；
- 反过来，完全有定义并不保证存在非零下矩阵，因为非吸收点对之间仍可能不存在正下界。

### 线性例子及其吸收元条件

在 \(\mathbb R^n,\mathbb R^m\) 上分别使用坐标距离
\[
d_i(x,y)=|x_i-y_i|,\qquad e_j(u,v)=|u_j-v_j|,
\]
并各添加一个与所有非吸收点距离为 \(+\infty\) 的吸收元。将线性映射 \(T:\mathbb R^n\to\mathbb R^m\) 延拓为吸收元保持映射。

在非吸收点对上，
\[
|(Tx-Ty)_j|
\le\sum_i|t_{ji}|\,|x_i-y_i|.
\]
由定理 2：

- 若 \(T\) 的每一行都非零，则绝对值矩阵
  \[
  U=|T|=(|t_{ji}|)
  \]
  是上矩阵；
- 若 \(T\) 有零行，则 \(|T|\) **不是**上矩阵，因为 \(T\) 把非吸收输入映为普通向量，而不是吸收元，混合点对处上界失败；
- 不过坐标距离族分离点，所以任何这样的 \(T\) 都有上矩阵，至少可以取 \(\boldsymbol\infty\)。

若 \(T=\operatorname{diag}(\lambda_1,\dots,\lambda_n)\)，则
\[
L=\operatorname{diag}(|\lambda_1|,\dots,|\lambda_n|)
\]
总是下矩阵；当所有 \(\lambda_i\neq0\) 时，
\[
L=U=\operatorname{diag}(|\lambda_1|,\dots,|\lambda_n|)
\]
同时是上、下矩阵。

---

## 6. 不可区分性的零化矩阵

把“输入落入一定范畴”最一般地形式化为一族输入关系
\[
\mathscr R=\{R_\alpha\}_{\alpha\in\mathfrak A},\qquad
R_\alpha\subseteq\mathcal X\times\mathcal X.
\]
若第 \(\alpha\) 类由输入区域 \(S_\alpha\subseteq\mathcal X\) 给出，取
\[
R_\alpha=S_\alpha\times S_\alpha
\]
即可表示“两个输入都属于该区域”。

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

当 \(R_\alpha=S_\alpha\times S_\alpha\) 时，\(c_{j\alpha}=1\) 表示
\[
x,y\in S_\alpha\quad\Longrightarrow\quad e_j(fx,fy)=0.
\]
若某一列全为 \(1\)，则该关系下的两个输出对整个输出族 \(\mathcal H\) 都不可区分。

由于没有预设族分离性，“不可区分”不等于输出相等；只有 \(\mathcal H\) 分离点时，才能进一步推出 \(fx=fy\)。

### 最大零化矩阵

存在逐项最大的零化矩阵 \(C_f^{\mathscr R}\)：
\[
(C_f^{\mathscr R})_{j\alpha}=1
\quad\Longleftrightarrow\quad
R_\alpha\subseteq\{(x,y):e_j(fx,fy)=0\}.
\]
一个布尔矩阵是零化矩阵，当且仅当它逐项不超过 \(C_f^{\mathscr R}\)。因此零矩阵总成立，而增加一个 \(1\) 就是增加一条实质断言。

若 \(S_\alpha\) 含有 \(\bot_{\mathcal X}\)，且 \(c_{j\alpha}=1\)，则对任意 \(x\in S_\alpha\)，由 \((x,\bot_{\mathcal X})\in R_\alpha\) 得
\[
e_j(fx,\bot_{\mathcal Y})=0.
\]
吸收元隔离遂强制 \(fx=\bot_{\mathcal Y}\)。所以含吸收元的输入区域上的零化，实际上意味着该区域全部被映为吸收元。

---

## 7. 零化矩阵的复合

设 \(f:\mathcal X\to\mathcal Y\)、\(g:\mathcal Y\to\mathcal Z\)，并令
\[
Z_j^{\mathcal Y}:=\{(u,v)\in\mathcal Y^2:e_j(u,v)=0\}.
\]
取 \(\Gamma^g\in\{0,1\}^{K\times J}\) 为 \(g\) 关于关系族 \(\{Z_j^{\mathcal Y}\}_{j\in J}\) 的零化矩阵，即
\[
\Gamma^g_{kj}=1
\quad\Longrightarrow\quad
\bigl(e_j(u,v)=0\Rightarrow h_k(gu,gv)=0\bigr).
\]
若 \(C^f\) 是 \(f\) 关于 \(\mathscr R\) 的零化矩阵，定义布尔乘积
\[
(\Gamma^g\star C^f)_{k\alpha}
:=\bigvee_{j\in J}\bigl(\Gamma^g_{kj}\wedge C^f_{j\alpha}\bigr).
\]

### 命题 4

\(\Gamma^g\star C^f\) 是 \(g\circ f\) 关于 \(\mathscr R\) 的零化矩阵。

**证明。** 若乘积的某元素为 \(1\)，则存在 \(j\) 使两个因子均为 \(1\)。于是
\[
(x,y)\in R_\alpha
\Longrightarrow e_j(fx,fy)=0
\Longrightarrow h_k(gfx,gfy)=0.
\]
这正是所需结论。 \(\square\)

这与数值 Lipschitz 矩阵在复合下使用普通非负矩阵乘积形成了直接类比。

---

## 8. 零化矩阵与 Lipschitz 矩阵的联系

### 8.1 从上矩阵提取零化信息

对任意 \(U\)，有
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

这里使用空交约定：零行的支撑为空，所以它形式上给出全局零化；定理 2 进一步说明，这只可能在 \(f\equiv\bot_{\mathcal Y}\) 时发生。

取单一关系 \(R_{\mathcal G}=Z_{\mathcal G}\)，定理 1 也可改写为
\[
\mathcal U(f)\neq\varnothing
\quad\Longleftrightarrow\quad
f\text{ 在 }Z_{\mathcal G}\text{ 上对所有输出分量零化}
\quad\Longleftrightarrow\quad
\boldsymbol\infty\in\mathcal U(f).
\]

### 8.2 下矩阵对零化的限制

若 \(L\in\mathcal L(f)\)，且某零化矩阵满足 \(c_{j\alpha}=1\)，则对 \((x,y)\in R_\alpha\)，
\[
0\le\sum_i\ell_{ji}d_i(x,y)
\le e_j(fx,fy)=0.
\]
因此
\[
\ell_{ji}d_i(x,y)=0\qquad\forall i.
\]
等价地，只要 \(\ell_{ji}>0\)，就必有
\[
R_\alpha\subseteq\{(x,y):d_i(x,y)=0\}.
\]
所以正的下界系数会排除相应正距离输入对上的输出零化。

---

## 结论

三种信息可以放在同一个分量式框架中：
\[
\boxed{
\begin{array}{ll}
\text{上矩阵 }U:&\mathbf e_f\le U\mathbf d,\\[2pt]
\text{下矩阵 }L:&L\mathbf d\le\mathbf e_f,\\[2pt]
\text{零化矩阵 }C:&c_{j\alpha}=1\Rightarrow
R_\alpha\subseteq\{e_j(fx,fy)=0\}.
\end{array}}
\]

它们满足：

- 上矩阵向上封闭，下矩阵向下封闭；
- 上、下矩阵在复合下均按普通扩展非负矩阵乘积传播；
- 零化矩阵在适当复合下按布尔矩阵乘积传播；
- 上矩阵存在恰好等价于保持输入族不可区分性；
- 吸收元使上矩阵零行和非零下矩阵分别具有“全局映为吸收元”和“所有非吸收输入有定义”的强含义；
- 所有不可区分结论均只用零距离表述，不暗中使用未预设的族分离性。

---

## 本轮修订说明与自评

- **保留：** 上、下扩展矩阵的定义，复合公式，上矩阵存在的充要条件，以及布尔零化矩阵及其与 Lipschitz 支撑的联系。
- **修正：** 上一版线性例子只验证了非吸收点对，却笼统宣称 \(U=|T|\) 总是上矩阵；当 \(|T|\) 含零行时，这一断言在混合点对 \((x,\bot)\) 上不成立。本稿已给出正确条件，并明确含零行时 \(|T|\) 不是上矩阵。
- **新增：** 定理 2 将吸收元条件化为非吸收点对不等式、零行条件和有效定义域条件的充要组合；同时补充了零距离关系是等价关系的说明。
- **未完成或范围边界：** 未研究一般可容许 Lipschitz 矩阵的最优选择，也未把“范畴”额外解释为范畴论对象；本稿解决的是原想法所需的定义、存在性、复合和零化性质，不声称给出最优矩阵理论。
- **自评：** 就原题的手稿化要求，自评 **B2**；新增内容主要是吸收元条件的充要细化和零化支撑演算，若附按研究增量尺度评价，自评 **R1**，不主张更高档推广。