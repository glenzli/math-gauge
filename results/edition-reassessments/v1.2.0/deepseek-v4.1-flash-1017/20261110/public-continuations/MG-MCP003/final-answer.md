# 扩展伪度量空间上的上、下 Lipschitz 矩阵与不可分辨矩阵

## 0. 交付范围

下面给出一份可独立阅读的完整稿。它把原想法落实为四个对象：

1. 有限距离上的**精确上斜率矩阵**；
2. 带无限距离边界的**下 Lipschitz 矩阵**；
3. 记录零距离传播、因而记录“输入不可分辨时输出是否仍可分辨”的 Boolean 矩阵；
4. 用来处理零距离与无限距离边界的**全局上控包络**。

关键修正是：有限距离上的上斜率矩阵只刻画 \(0<d_i(x,y)<+\infty\) 的输入；它不能在不附加零类和无限距离信息时，无条件地满足纳入了全体的 max-plus 复合式。下文会给出精确成立的范围、有限距离上的条件次可乘，以及反例。

全文保持题面规定的扩展非负实数算术，特别是

\[
a+(+\infty)=+\infty,\qquad
0\cdot(+\infty)=0,\qquad
a\cdot(+\infty)=+\infty\quad(a>0).
\]

---

## 1. 成对距离的三种状态

固定扩展规范空间 \((\mathcal X,\mathcal G,\bot)\)，其中
\(\mathcal G=\{d_i\}_{i\in I}\)，且 \(I\ne\varnothing\) 有限。
固定算子 \(\phi\in\mathcal X_{\mathrm{op}}\)，记

\[
D_\phi:=\operatorname{dom}(\phi)
=\{x\in\mathcal X:\phi(x)\ne\bot\}.
\]

所有涉及 \(\phi\) 的距离比较都取 \(x,y\in D_\phi\)。因此
\(\phi(x),\phi(y)\ne\bot\)。为每个分量 \(i\) 把成对距离分成三类：

\[
\begin{aligned}
Z_i(\phi):&=\{(x,y)\in D_\phi^2:d_i(x,y)=0\},\\
F_i(\phi):&=\{(x,y)\in D_\phi^2:0<d_i(x,y)<+\infty\},\\
\infty_i(\phi):&=\{(x,y)\in D_\phi^2:d_i(x,y)=+\infty\}.
\end{aligned}
\]

这种区分不是技术性装饰。若 \(d_i(x,y)=0\)，则即使上常数取
\(+\infty\)，题面算术仍给出
\(+\infty\cdot0=0\)；若 \(d_i(x,y)=+\infty\) 而输出距离有限，则任何正下界都失效，但上界的取值规律又取决于是否把上常数取为 \(0\)。因此 \(0\) 和 \(+\infty\) 必须作为独立边界记录。

对 \(i\in I\) 定义

\[
x\sim_i y\iff d_i(x,y)=0,
\qquad
x\sim_S y\iff \forall i\in S,\ x\sim_i y,
\]

其中 \(S\subseteq I\)。三角不等式说明每个 \(\sim_i\) 是等价关系，并且

\[
\sim_S\,=\bigcap_{i\in S}\sim_i.
\]

这里不假设 \((x\sim_i y\ \forall i)\Rightarrow x=y\)。由于 \(\phi\) 把吸收元映到吸收元且吸收元被每个伪度量隔离，\(D_\phi\subseteq\mathcal X\setminus\{\bot\}\)。

以下还采用约定：若某个距离商的分母不属于 \((0,+\infty)\)，该商不参与定义中的上确界或下确界；空上确界取 \(0\)，空下确界取 \(+\infty\)。

为了避免把未定义算子输出当作可比较距离，定义中的 \(d_j(\phi(x),\phi(y))\) 都只用于 \(x,y\in D_\phi\)；因此两个输出均非 \(\bot\)。

若 \(\phi,\psi\in\mathcal X_{\mathrm{op}}\)，则

\[
D_{\psi\circ\phi}
=\{x\in D_\phi:\phi(x)\in D_\psi\}.
\]

---

## 2. 有限距离上的精确上斜率矩阵

### 定义 2.1

对 \(i,j\in I\)，定义

\[
u^{\mathrm{fin}}_{ji}(\phi)
:=\sup_{\substack{x,y\in D_\phi\\0<d_i(x,y)<+\infty}}
\frac{d_j(\phi(x),\phi(y))}{d_i(x,y)},
\qquad \sup\varnothing:=0.
\]

矩阵

\[
U^{\mathrm{fin}}(\phi)
:=\bigl(u^{\mathrm{fin}}_{ji}(\phi)\bigr)_{j,i\in I}
\in\overline{\mathbb R}_+^{I\times I}
\]

称为 \(\phi\) 的**有限距离上斜率矩阵**。第 \(j\) 行对应输出分量，第 \(i\) 列对应输入分量。

### 命题 2.2（逐分量精确性）

若 \(0<d_i(x,y)<+\infty\)，则

\[
d_j(\phi(x),\phi(y))
\le u^{\mathrm{fin}}_{ji}(\phi)\,d_i(x,y).
\tag{2.1}
\]

此外，\(u^{\mathrm{fin}}_{ji}\) 是所有在该有限正距离区域上有效的上常数的最小值：任意
\(a\in\overline{\mathbb R}_+\) 若满足

\[
d_j(\phi(x),\phi(y))\le a\,d_i(x,y)
\qquad
\bigl(0<d_i(x,y)<+\infty\bigr),
\]

就有 \(a\ge u^{\mathrm{fin}}_{ji}\)。

**证明.** 上确界的定义直接给出 (2.1)。若 \(a<u^{\mathrm{fin}}_{ji}\)，则由上确界的定义，存在一个有限正距离对使
\(d_j(\phi(x),\phi(y))/d_i(x,y)>a\)；若 \(a=+\infty\)，则不存在比它更小的上界。故最小性成立。\(\square\)

具体地，\(u^{\mathrm{fin}}_{ji}<+\infty\) 表示第 \(i\) 个输入分量到第 \(j\) 个输出分量在有限正距离上有有限线性控制；
\(u^{\mathrm{fin}}_{ji}=+\infty\) 表示这一控制不存在。

但 (2.1) 明确排除了零距离和无限输入距离。零距离被拆开时，不存在任何矩阵常数能借助乘法修复它；例如输入距离为 \(0\) 时，右边总是 \(a\cdot0=0\)。所以零类传播必须由独立的 Boolean 矩阵记录。有限正输入被送到无限输出时，(2.1) 正确地取 \(u^{\mathrm{fin}}=+\infty\)，表示这种有限的逐分量线性上控不存在。

---

## 3. 下 Lipschitz 矩阵

### 定义 3.1

先令

\[
s_{ji}(\phi):=
\inf_{\substack{x,y\in D_\phi\\0<d_i(x,y)<+\infty}}
\frac{d_j(\phi(x),\phi(y))}{d_i(x,y)},
\qquad \inf\varnothing:=+\infty.
\]

再并入无限输入边界：

\[
\ell_{ji}(\phi):=
\begin{cases}
0,&\text{若存在 }x,y\in D_\phi\text{ 使 }
d_i(x,y)=+\infty\text{ 且 }d_j(\phi(x),\phi(y))<+\infty,\\[1mm]
s_{ji}(\phi),&\text{否则}.
\end{cases}
\]

矩阵

\[
L(\phi):=(\ell_{ji}(\phi))_{j,i\in I}
\]

称为 \(\phi\) 的**下 Lipschitz 矩阵**。

### 命题 3.2（全体成对下界与最大性）

对任意 \(x,y\in D_\phi\) 和 \(i,j\in I\)，均有

\[
d_j(\phi(x),\phi(y))
\ge \ell_{ji}(\phi)\,d_i(x,y).
\tag{3.1}
\]

并且，对每个固定 \((j,i)\)，只要相应的有限正距离或无限输入区域非空，\(\ell_{ji}(\phi)\) 就是使 (3.1) 在该区域成立的逐项最大常数。

**证明.** 若 \(d_i(x,y)=0\)，右边为 \(0\)，结论显然。

若 \(0<d_i(x,y)<+\infty\)，若 \(\ell_{ji}\) 没有被无限边界改成 \(0\)，下确界的定义直接给出
\(\ell_{ji}\le d_j/d_i\)；若它被改成了 \(0\)，结论也显然。

若 \(d_i(x,y)=+\infty\) 且 \(d_j(\phi(x),\phi(y))<+\infty\)，定义已经强制
\(\ell_{ji}=0\)。若 \(d_j(\phi(x),\phi(y))=+\infty\)，则对任意
\(\ell_{ji}\in(0,+\infty]\) 都有
\(\ell_{ji}\cdot(+\infty)=+\infty\)，而 \(\ell_{ji}=0\) 时右边为 \(0\)，故仍成立。

最大性在一个非空区域上理解如下。若 \(\ell_{ji}=0\) 来自无限输入的有限输出边界，则任何 \(b>0\) 都在那一对上失败；若来自有限正距离下确界，由下确界的定义，(3.1) 对全体成立，且任何 \(b>0\) 都不可能更大。若 \(\ell_{ji}=+\infty\)，任何有限系数都小于它；扩展数值范围内也没有更大的可取值。若有限正距离集合为空，则 \(+\infty\) 只是空下确界的约定，正文不把它解释为函数值域中的最大常数。\(\square\)

因此对所有输入列的控制同时成立，可以写成

\[
d_j(\phi(x),\phi(y))\ge\ell_{ji}(\phi)d_i(x,y),
\qquad
d_j(\phi(x),\phi(y))
\ge \max_{i\in I}\ell_{ji}(\phi)d_i(x,y)
\qquad\bigl(x,y\in D_\phi\bigr),
\tag{3.2}
\]

前一式对每个固定的 \((j,i)\) 成立；后一式同时使用全部输入列。

特别地，\(\ell_{ji}>0\) 排除了“正输入距离被压成零输出距离”；
\(\ell_{ji}=0\) 表示没有正下界；
\(\ell_{ji}=+\infty\) 表示每个正的有限输入距离都产生无限输出距离，并且没有无限输入被送到有限输出。

---

## 4. 零类传播与不可分辨矩阵

### 定义 4.1（Boolean 矩阵）

定义

\[
K(\phi)=(k_{ji}(\phi))_{j,i\in I}\in\{0,1\}^{I\times I}
\]

为

\[
k_{ji}(\phi)=1
\iff
\left[
x,y\in D_\phi,\ d_i(x,y)=0
\Longrightarrow
d_j(\phi(x),\phi(y))=0
\right].
\]

它记录：输入在第 \(i\) 分量上不可分辨时，输出是否必在第 \(j\) 分量上不可分辨。

### 命题 4.2（诱导映射）

\(k_{ji}(\phi)=1\) 当且仅当

\[
\overline\phi_{ji}:D_\phi/\!\sim_i\longrightarrow \mathcal X/\!\sim_j,
\qquad [x]_i\longmapsto[\phi(x)]_j
\]

是良定义的。也就是说，\(\phi\) 把每个 \(i\)-零类确定地送到某个 \(j\)-零类。

**证明.** 良定义性恰为：\(x\sim_i y\) 时必有
\(\phi(x)\sim_j\phi(y)\)。这正是 \(k_{ji}=1\) 的定义。\(\square\)

### 命题 4.3（与上、下控制的关系）

若 \(\ell_{ji}(\phi)>0\)，则由命题 3.2，任意 \(x,y\in D_\phi\) 只要 \(d_i(x,y)>0\) 就有 \(d_j(\phi(x),\phi(y))>0\)。

故\(\ell_{ji}>0\)记录“正向不压零类”；若再有
\(k_{ji}(\phi)=1\)，则

\[
d_i(x,y)=0\iff d_j(\phi(x),\phi(y))=0.
\tag{4.1}
\]

若此外还有\(u^{\mathrm{fin}}_{ji}(\phi)<+\infty\)，则对
\(0<d_i(x,y)<+\infty\)，

\[
\ell_{ji}d_i(x,y)
\le d_j(\phi(x),\phi(y))
\le u^{\mathrm{fin}}_{ji}d_i(x,y).
\tag{4.2}
\]

这三个条件还保持零、有限正、无限三种状态：

\[
d_i(x,y)=0\iff d_j(\phi(x),\phi(y))=0,
\quad
d_i(x,y)<+\infty\iff d_j(\phi(x),\phi(y))<+\infty.
\tag{4.3}
\]

因此相应的诱导映射是零类上的单射，并且保持三种距离状态。

**证明.** 先证 (4.1)。若 \(d_i(x,y)>0\)，由 \(\ell_{ji}>0\) 和命题 3.2，
\(d_j(\phi(x),\phi(y))>0\)。反方向正是 \(k_{ji}=1\)。

再证有限与无限状态。若 \(d_i(x,y)<+\infty\) 但\(d_j(\phi(x),\phi(y))=+\infty\)，则由定义 2.1 可知
\(u^{\mathrm{fin}}_{ji}=+\infty\)，与假设矛盾。若\(d_i(x,y)=+\infty\)但
\(d_j(\phi(x),\phi(y))<+\infty\)，则定义 3.1 会强制\(\ell_{ji}=0\)，亦与假设矛盾。故 (4.3) 成立。
(4.2) 就是命题 2.2 与 3.2 的合并。\(\square\)

注意 (4.1) 的反方向必须同时使用 \(k_{ji}=1\)。仅有下界 \(\ell_{ji}>0\) 只能排除正输入被压成零，不能保证原本为零的输入仍被映为零。

---

## 5. 同时落入多个零类的范畴矩阵

\(K(\phi)\) 只记录单个输入分量的零类。若“若干输入分量同时不可分辨”的范畴也要编码，可对 \(S,T\subseteq I\) 定义

\[
C_\phi(T,S)=1
\iff
\left[
\begin{array}{l}
x,y\in D_\phi,\\[1mm]
\forall i\in S,\ d_i(x,y)=0
\end{array}
\Longrightarrow
\forall j\in T,\ d_j(\phi(x),\phi(y))=0
\right].
\tag{5.1}
\]

这是一个\(2^{|I|}\times2^{|I|}\)的 Boolean 矩阵。它也常称为**范畴不可分辨矩阵**：输入同时落入 \(S\)-零范畴，强制输出同时落入 \(T\)-零范畴。原 Boolean 矩阵是它的单点限制：

\[
k_{ji}(\phi)=C_\phi(\{j\},\{i\}).
\]

空集按通常全称量词约定处理：\(C_\phi(\varnothing,S)=1\)，因为输出范畴为空时全称命题为空真；\(S=\varnothing\)时，前件自动成立，故 \(C_\phi(T,\varnothing)=1\) 恰表示 \(\phi\) 在全部 \(T\) 分量上的像是零直径的。

若把 \(C_\phi\) 看成由列范畴到行范畴的关系，则 \(S\subseteq S'\) 时
\(C_\phi(T,S)\le C_\phi(T,S')\)；而 \(T\subseteq T'\) 时
\(C_\phi(T',S)\le C_\phi(T,S)\)。

---

## 6. 全局上控包络：修正 \(0\cdot+\infty\) 边界

命题 2.2 是精确的，但只用 \(U^{\mathrm{fin}}\) 无法写出覆盖全部距离对的单常数不等式。原因有两个：

- 若输入距离为\(0\)而输出距离为正，任何\(a\)都给出右边\(a\cdot0=0\)，无法上控；
- 若有限正距离上的上确界为\(0\)，却存在无限输入被送到正输出，则常数\(0\)不覆盖无限输入，而任何正常数都比\(0\)保守；通常非负实数中又没有最小正数。

把定性零控制交给 \(K\) 后，第二个边界可用下面一个规范的全局包络记录。这个包络是用于覆盖全体距离对的**充分包络**；精确的有限距离数据仍由 \(U^{\mathrm{fin}}\) 无损保存。

### 定义 6.1

对\(i,j\in I\)，定义

\[
U^\sharp(\phi)=(u^\sharp_{ji}(\phi))_{j,i\in I},
\]

其中

\[
u^\sharp_{ji}(\phi):=
\begin{cases}
u^{\mathrm{fin}}_{ji}(\phi),&u^{\mathrm{fin}}_{ji}(\phi)>0,\\[1mm]
+\infty,&u^{\mathrm{fin}}_{ji}(\phi)=0\text{ 且存在 }(x,y)\in\infty_i(\phi)
\text{ 使 }d_j(\phi(x),\phi(y))>0,\\[1mm]
0,&\text{其余情形}.
\end{cases}
\tag{6.1}
\]

这里的中间情形用一个 \(+\infty\) 作为“不能在扩展非负标量中选择统一的正系数”的标记；精确的有限距离斜率仍从 \(U^{\mathrm{fin}}\) 读取。定义 6.1 不声称在每一种边界情形下都是逐项最小的上常数。

### 命题 6.2（K 行条件与逐对上界）

若 \(k_{ji}(\phi)=1\)，则对全体 \(x,y\in D_\phi\)，

\[
d_j(\phi(x),\phi(y))
\le u^\sharp_{ji}(\phi)\,d_i(x,y).
\tag{6.2}
\]

若进一步 \(k_{ji}(\phi)=1\) 对每个 \(i\in I\) 都成立，则

\[
d_j(\phi(x),\phi(y))
\le\max_{i\in I}u^\sharp_{ji}(\phi)d_i(x,y)
\le\sum_{i\in I}u^\sharp_{ji}(\phi)d_i(x,y).
\tag{6.3}
\]

**证明.** 先证 (6.2)。若\(d_i(x,y)=0\)，由\(k_{ji}=1\)知输出分量为\(0\)。若\(d_i(x,y)\in(0,+\infty)\)，当\(u^\sharp_{ji}=0\)时定义 (6.1) 给出输出为\(0\)；否则由命题 2.2，右边至少为\(u^{\mathrm{fin}}_{ji}d_i\)。若\(d_i(x,y)=+\infty\)，当\(u^\sharp_{ji}=0\)时(6.1)保证该输出为\(0\)；当\(u^\sharp_{ji}>0\)时右边为\(+\infty\)。故结论成立。

对 (6.3)，若某个 \(d_i(x,y)>0\)，用对应的 (6.2)；若所有 \(d_i(x,y)=0\)，由任一行零控制条件知输出也为 \(0\)。最后一个不等式由非负性给出。\(\square\)

因此，在所记录的输入分量上，零分裂不能发生是使用上控矩阵的必要条件；一旦\(k_{ji}=0\)，就连取值为\(+\infty\)的上常数也不能修复\(0\cdot+\infty=0\)。

---

## 7. 复合

定义 max-plus 矩阵乘法

\[
(A\boxtimes B)_{ki}:=\max_{j\in I}A_{kj}B_{ji},
\qquad A,B\in\overline{\mathbb R}_+^{I\times I}.
\]

### 定理 7.1（下矩阵无条件次可乘）

设 \(\psi\circ\phi\) 有意义。则

\[
L(\psi\circ\phi)
\succeq L(\psi)\boxtimes L(\phi),
\tag{7.1}
\]

即

\[
\ell^{\psi\circ\phi}_{ki}
\ge\max_{j\in I}\ell^\psi_{kj}\ell^\phi_{ji}.
\]

**证明.** 取 \(x,y\in D_{\psi\circ\phi}\)，并令
\(z=\phi(x),w=\phi(y)\)。对每个 \(j\)，命题 3.2 分别给出

\[
d_k(\psi(z),\psi(w))\ge\ell^\psi_{kj}d_j(z,w),
\]

以及

\[
d_j(z,w)\ge\ell^\phi_{ji}d_i(x,y).
\]

若 \(d_j(z,w)>0\)，扩展非负乘法的单调性允许把两式相乘；若 \(d_j(z,w)=0\)，则两个中间像在 \(j\) 分量上不可分辨。此时若 \(d_i(x,y)=0\)，两边都为 \(0\)；若 \(d_i(x,y)>0\)，右侧乘积也是 \(0\)，而不等式只声称非负输出大于等于零，结论仍成立。因此每个 \(j\) 都给出一个有效下界。

\[
d_k(\psi\phi x,\psi\phi y)
\ge\ell^\psi_{kj}\ell^\phi_{ji}d_i(x,y).
\]

因此右端对每个 \(j\) 都是复合算子输出下界中的一个有效常数。对 \(j\) 取最大值后仍有效；对有限正输入距离取下确界，再按定义 3.1 核对无限输入边界，就得到 (7.1)。\(\square\)

### 命题 7.2（有限部分的条件次可乘）

固定 \(k,i\in I\)。若

\[
k^\phi_{ji}=1\quad\text{对每个 }j\in I,
\qquad
k^\psi_{kj}=1\quad\text{对每个 }j\in I,
\tag{7.3}
\]

则

\[
u^{\mathrm{fin},\,\psi\circ\phi}_{ki}
\le\max_{j\in I}u^{\sharp,\,\psi}_{kj}u^{\sharp,\,\phi}_{ji}.
\tag{7.4}
\]

**证明.** 记 \(M_{ki}:=\max_{j\in I}u^{\sharp,\,\psi}_{kj}u^{\sharp,\,\phi}_{ji}\)。
对任意 \(x,y\in D_{\psi\circ\phi}\)，令
\(z=\phi(x),w=\phi(y)\)。固定任一 \(j\in I\)。由命题 6.2，条件
\(k^\phi_{ji}=1\) 与 \(k^\psi_{kj}=1\) 分别给出

\[
d_j(z,w)\le u^{\sharp,\,\phi}_{ji}d_i(x,y),
\qquad
d_k(\psi(z),\psi(w))\le u^{\sharp,\,\psi}_{kj}d_j(z,w).
\tag{7.5}
\]

若 \(d_j(z,w)=0\)，由 \(k^\psi_{kj}=1\) 知输出 \(k\) 也为 \(0\)。若 \(d_j(z,w)>0\)，则题面扩展乘法允许把 (7.5) 的两式连起来，得到

\[
d_k(\psi\phi x,\psi\phi y)
\le u^{\sharp,\,\psi}_{kj}u^{\sharp,\,\phi}_{ji}d_i(x,y)
\le M_{ki}d_i(x,y).
\tag{7.6}
\]

两种情况都对每个 \(j\) 成立。对有限正输入距离除以后取下确界，即得
\(u^{\mathrm{fin},\,\psi\circ\phi}_{ki}\le M_{ki}\)。\(\square\)

**有限部分之外的无限距离。** 下面的检查说明无限输入在复合中的传播。取 \(|I|=1\)，令所有非对角距离为 \(1\)，只在输入点 \(c,d\) 上改取
\(d(c,d)=d(d,c)=+\infty\)。于是所有零点仍只在对角线上，故所有 \(K\)-项均为 \(1\)。另取互不相同的非吸收点
\(a,b,u,z,r,s,p,q,w\)，定义

\[
\phi(c)=r,\quad\phi(d)=s,
\]

\[
\psi(r)=q,\quad\psi(s)=w,
\]

并把全部其余非吸收点（包括 \(a,b,u,z\)）的像定为 \(p\)。于是 \(\phi\) 把每个有限正距离对映为零，且把唯一的无限输入对 \(c,d\) 送到距离为正的像对 \(r,s\)。则

\[
u^{\mathrm{fin}}(\phi)=0,\qquad u^{\sharp}(\phi)=+\infty,
\qquad
 u^{\mathrm{fin}}(\psi)=u^{\sharp}(\psi)=1.
\]

现在 \(\psi\) 把唯一距离为无限的像对 \(r,s\) 送到另一个无限距离点对 \(q,w\)，因此两个端点包络都是有限数。对复合算子，任一有限正距离对经 \(\phi\) 后的两个像在 \(\psi\) 下都映为 \(p\)，所以
\(u^{\mathrm{fin}}(\psi\circ\phi)=0\)；但无限输入对 \(c,d\) 被送到距离为无限的像对 \(q,w\)，复合包络为 \(1\)。这个例子说明无限距离类型可以从输入传播到复合输出，复合结论需要按定义逐类核对。

### 定理 7.3（不可分辨矩阵的复合）

有

\[
K(\psi\circ\phi)
\succeq K(\psi)\odot K(\phi),
\tag{7.7}
\]

其中

\[
(P\odot Q)_{ki}:=\bigvee_{j\in I}(P_{kj}\wedge Q_{ji}).
\]

更完整地，对范畴矩阵有

\[
C_{\psi\circ\phi}(T,S)
\succeq
\bigvee_{S'\subseteq I}C_\psi(T,S')\wedge C_\phi(S',S).
\tag{7.8}
\]

**证明.** 若 \(x\sim_S y\) 且 \(C_\phi(S',S)=1\)，则
\(\phi(x)\sim_{S'}\phi(y)\)。再由 \(C_\psi(T,S')=1\)，得到
\(\psi\phi(x)\sim_T\psi\phi(y)\)。故右边任意一条全为 \(1\) 的路径都推出左边为 \(1\)。取 \(S=\{i\}\)、\(S'=\{j\}\)、\(T=\{k\}\)，即得式(7.7)。\(\square\)

### 7.4 为什么不能把有限斜率矩阵的复合写成无条件次可乘

即使所有零类都被保持，\(U^{\mathrm{fin}}\) 也不能无条件服从 max-plus 次可乘。取 \(|I|=1\)，并在
\(\mathcal X\setminus\{\bot\}\) 中取八个互不相同的点 \(a,b,c,d,u,v,r,s,p\)。令所有非对角距离为
\(1\)，只有 \(d(u,v)=d(v,u)=d(r,s)=d(s,r)=+\infty\)。这是只在对角线上取 \(0\) 的距离，因而所有 \(K\)-项均为 \(1\)。令

\[
\phi(a)=u,\quad\phi(b)=v,\quad\phi(c)=\phi(d)=p,
\]

\[
\psi(u)=r,\quad\psi(v)=s,\quad\psi(a)=\psi(b)=\psi(c)=\psi(d)=p,
\]

其中 \(p\) 是上述固定的非吸收点；把全部未在上述公式中命名的非吸收点的像都定为 \(p\)，并令 \(\phi(\bot)=\psi(\bot)=\bot\)。则

- \(d(a,b)=1\)，但 \(d(\phi(a),\phi(b))=+\infty\)，所以
  \(u^{\mathrm{fin}}(\phi)=+\infty\)；
- 所有有限正距离对在 \(\psi\) 下都映为零，所以
  \(u^{\mathrm{fin}}(\psi)=0\)；
- 但 \((\psi\circ\phi)(a)=r\)、\((\psi\circ\phi)(b)=s\)，故
  \(u^{\mathrm{fin}}(\psi\circ\phi)=+\infty\)。

于是

\[
u^{\mathrm{fin}}(\psi\circ\phi)=+\infty
\not\le 0=u^{\mathrm{fin}}(\psi)u^{\mathrm{fin}}(\phi),
\]

因为题面算术规定 \(0\cdot(+\infty)=0\)。采用定义 6.1 的全局包络后，\(u^\sharp(\psi)=+\infty\)，所以上式的边界矛盾消失。这说明有限斜率矩阵与全局上控包络必须分开解释。

---

## 8. 单位算子与基本退化

设\(\mathrm{id}\)为\(\mathcal X\)上的恒等算子。

恒等算子的有限上斜率满足

\[
u^{\mathrm{fin}}_{ji}(\mathrm{id})
=\sup_{\substack{x,y\in\mathcal X\\0<d_i(x,y)<+\infty}}
\frac{d_j(x,y)}{d_i(x,y)},
\]

其下矩阵在无限输入没有被送到有限输出时满足

\[
\ell_{ji}(\mathrm{id})
=\inf_{\substack{x,y\in\mathcal X\\0<d_i(x,y)<+\infty}}
\frac{d_j(x,y)}{d_i(x,y)}.
\]

若存在\(d_i(x,y)=+\infty\)而\(d_j(x,y)<+\infty\)，则按定义
\(\ell_{ji}(\mathrm{id})=0\)。零矩阵满足

\[
k_{ji}(\mathrm{id})=1
\iff
\sim_i\,\subseteq\,\sim_j,
\]

即第\(i\)个伪度量比第\(j\)个更细；范畴矩阵满足

\[
C_{\mathrm{id}}(T,S)=1
\iff
\bigcap_{i\in S}\sim_i
\;\subseteq\;
\bigcap_{j\in T}\sim_j.
\]

因此即使只有一个指标，\(U^{\mathrm{fin}}(\mathrm{id})\)也未必是标量\(1\)：它衡量同一组点上不同分量的相互粗细。

当 \(|I|=1\) 时，记唯一的伪度量为 \(d\)。若 \(0<d(x,y)<+\infty\) 的区域非空，则有限部分正是通常的上、下 Lipschitz 常数中的对应部分；\(u^{\mathrm{fin}}=+\infty\) 表示没有有限 Lipschitz 控制，\(\ell=0\) 表示没有正下界（特别包括正输入距离被压成零的情况），\(k=1\) 表示保持零距离关系。

若 \(\phi\) 在 \(D_\phi\) 上取常值非吸收点，则 \(U^\sharp(\phi)=0\)，\(K(\phi)=\mathbf1\)。对于每个 \((j,i)\)，只要存在任一有限正 \(d_i(x,y)\)，就有 \(\ell_{ji}=0\)；若存在无限 \(d_i(x,y)\)，因为输出距离为零，按无限边界规则仍有 \(\ell_{ji}=0\)。若所有成对 \(d_i\) 都为零，则按空下确界约定 \(\ell_{ji}=+\infty\)，但这只表示在该零距离区域没有正斜率可测。若 \(D_\phi\) 本身为空，以上商也取空上、下确界的约定。

取 \(\mathcal X=\mathbb R\cup\{\bot\}\)，令非吸收点之间的 \(d\) 为通常距离，并令 \(d(x,\bot)=+\infty\) 对 \(x\ne\bot\) 成立，\(\phi(x)=x^2\)。则 \(D_\phi=\mathbb R\)，且 \(u^{\mathrm{fin}}=+\infty\)、\(\ell=0\)、\(k=1\)：无界增长与把正距离压成零是两项独立信息。

---

## 9. 与加法型矩阵的联系

在命题 6.2 的行条件成立时，\(U^\sharp\) 直接给出加法上界

\[
d_j(\phi(x),\phi(y))
\le\sum_{i\in I}u^\sharp_{ji}(\phi)d_i(x,y).
\]

由(3.2)，令\(n=|I|\)，则

\[
d_j(\phi(x),\phi(y))
\ge\max_{i\in I}\ell_{ji}(\phi)d_i(x,y)
\ge\frac1n\sum_{i\in I}\ell_{ji}(\phi)d_i(x,y).
\]

所以 \(L(\phi)/n\) 给出一个加法型下界矩阵。若实际模型采用
\(d_j\le\sum_iA_{ji}d_i\)，可选择满足逐项比较的
\(A_{ji}\ge u^\sharp_{ji}\)；反之，任何满足该加法不等式的非负矩阵也给出同样的上控信息。主文采用 max-plus 是因为它逐个分量保留精确斜率，并且不会把不同分量的作用混成一个和。

---

## 10. 结构小结

- \(U^{\mathrm{fin}}(\phi)\)：每个输入分量到每个输出分量在有限正距离上的精确上斜率；
- \(L(\phi)\)：相应的下 Lipschitz 控制，并显式处理无限输入被送到有限输出的边界；
- \(K(\phi)\)：单个零类的传播关系；
- \(C_\phi\)：多个零类同时不可分辨时的范畴传播关系；
- \(U^\sharp(\phi)\)：把有限斜率与零/无限边界接起来、可用于全局上控的规范包络。

下标 \((j,i)\) 始终表示“从输入分量\(i\)到输出分量\(j\)”；上述矩阵因此能同时表达不同输入、输出分量之间的依赖，而不依赖一个失真的单一 Lip 常数。

---

## 11. 本轮检查、保留、修正与自评

**保留.** 保留了原来的核心设计：上、下 Lipschitz 矩阵、Boolean 零传播矩阵、集合格上的范畴矩阵，以及逐分量精确斜率、常值算子、无界算子和单分量退化等例子。

**新增或修正.**

1. 明确区分零、有限正、无限三类输入距离，避免把 \(0\cdot+\infty\) 当成有效的斜率控制；
2. 用 \(U^\sharp\) 补上有限斜率矩阵在无限输入边界上的缺失；
3. 把上矩阵的复合限制在明确的零类行条件下，仅证明有限部分的次可乘，并给出有限斜率矩阵无条件复合失效的反例；
4. 修正下矩阵在无限输入被送到有限输出时取 \(0\)，并证明它在全体距离对上的最大下界性；
5. 补上零、有限、无限三状态保持条件及范畴矩阵的复合。

**仍未声称的部分.** 没有声称对所有非分离伪度量和所有无限距离算子都存在一个无需附件的、逐项最小的有限上斜率矩阵；实际上零类分裂使这种统一标量上界不可能存在。没有声称 \(U^\sharp\) 的精确复合，只证明了命题 7.2 中的有限部分，并保留了无限边界的传播例子。也没有声称零类行条件是必要条件。

**自评.** 按本题“把想法严格化为自洽定义并给出必要论证”的要求，核心概念、边界、精确性、有限部分的条件复合、反例和退化情形均已交付，故保守自评为 **B2**。作为研究增量，全局上控包络与三类距离边界处理提供了可用信息，但没有另行建立一个大范围的新理论，故仍按 **R1** 自评。本稿未声称已解决全部端点包络的复合问题，因此不自我标为 R3 或严格完成档 SMC；这是对研究范围与完成度的保守判断。
