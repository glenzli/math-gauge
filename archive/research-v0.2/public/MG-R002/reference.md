# 参考审核：兼容线性记录的整体实现

原强目标为假。兼容且一致有界的记录给出 $E''$ 中的唯一元素；它不必属于规范嵌入 $J:E\to E''$ 的像。Banach 完备性不能代替自反性。以下完整基线同时说明记录可以怎样实现、怎样有限观测逼近，以及哪一步不能提升。

## 兼容族的实际实现对象

定义 $z_\lambda(\varphi)=\lambda_F(\varphi)$，其中任选包含 $\varphi$ 的有限维 $F$。两个选择同时包含于 $F+G$，相容性保证值相同。在包含 $\varphi,\psi$ 的共同有限维子空间内计算，得到 $z_\lambda$ 的实线性。给定界说明 $z_\lambda\in E''$ 且 $\|z_\lambda\|\le C$。

反过来，每个 $z\in E''$ 的有限维限制给出这种族。这两种操作互逆，且

$$\|z_\lambda-z_\mu\|=d(\lambda,\mu).$$

因此记录空间按题内距离等距实现于双对偶，完全不需要挑选有限维子空间的基。记录逐泛函收敛正是 $\sigma(E'',E')$ 收敛。固定界 $C$ 的记录集合可嵌入
$\prod_{\varphi\in E'}[-C\|\varphi\|,C\|\varphi\|]$；线性关系是闭条件，所以由乘积紧性它是紧空间。紧的是这个记录空间，不是原空间中的范数球。

对有界 $T$，实际计算为

$$z_{\lambda^T}(\varphi)=z_\lambda(T'\varphi)=(T''z_\lambda)(\varphi).$$

由此记录变换与双对偶作用严格相容，且范数至多乘 $\|T\|$。对 $x\in E$，$T''Jx=JTx$，所以原空间确实作为稳定子空间嵌入。

## 原空间中的有限观测逼近

任给 $\varphi_1,\ldots,\varphi_k$，令 $Qx=(\varphi_i(x))_i$、$b=(z_\lambda(\varphi_i))_i$。断言 $b\in\overline{Q(CB_E)}$。否则有限维严格分离给出 $a\in\mathbb R^k$，使

$$a\cdot b>\sup_{\|x\|\le C}a\cdot Qx=C\Big\|\sum_i a_i\varphi_i\Big\|,$$

与 $|z_\lambda(\sum_i a_i\varphi_i)|\le C\|\sum_i a_i\varphi_i\|$ 矛盾。因此任意有限组记录可以由范数至多 $C$ 的原空间向量任意精度逼近。以有限观测组和误差容限为有向指标，得到 $J(CB_E)$ 弱星稠密于 $CB_{E''}$；$C=0$ 时取零向量即可。

这里一般得到网，不是预先有一个万能序列；也没有得到范数收敛或 $E$ 中的弱极限。有限组记录其实可以精确插值，但未必能保留尖锐范数界 $\|x\|\le C$。

具体地，$Q(E)$ 是有限维空间中的线性子空间，故闭，因而 $b\in Q(E)$。在 $Q(E)$ 上选一个线性右逆 $R:Q(E)\to E$：取有限基并为每个基向量选择一个原像即可，有限维性保证 $R$ 有界。若 $\|x_k\|\le C$ 且 $Qx_k\to b$，则

$$\widetilde x_k=x_k+R(b-Qx_k)$$

满足 $Q\widetilde x_k=b$、$\limsup_k\|\widetilde x_k\|\le C$。因此对每个 $\varepsilon>0$ 都有精确插值且 $\|\widetilde x\|<C+\varepsilon$。

尖锐界确可失败：在下节 $c_0$ 的常数一记录中，单个观测 $\varphi(x)=\sum_{j\ge1}2^{-j}x_j$ 的目标值为 $1$。若 $\|x\|\le1$ 且 $\varphi(x)=1$，正权重迫使所有 $x_j=1$，与 $x\in c_0$ 矛盾。这不否定带任意小范数余量的精确有限插值，也不否定范数不超过 $C$ 的近似插值。

## 合法反例

取 $E=c_0(\mathbb N)$，范数为上确界范数。其对偶为 $\ell^1$：若 $\varphi\in c_0'$，设 $a_j=\varphi(e_j)$；对有限支撑符号向量应用范数界，得 $\sum_j|a_j|\le\|\varphi\|$。有限截断在 $c_0$ 中范数稠密，故 $\varphi(x)=\sum_j a_jx_j$；反向估计给出对偶范数等于 $\|a\|_1$。

对每个有限维 $F\subset\ell^1$ 定义

$$\lambda_F(a)=\sum_{j=1}^\infty a_j.$$

绝对收敛、线性、限制相容及 $|\lambda_F(a)|\le\|a\|_1$ 全部成立，取 $C=1$。若存在目标中的 $x\in c_0$，用坐标泛函 $e_j\in\ell^1$ 测试便得 $x_j=1$ 对所有 $j$，矛盾。

截断向量 $x^{(n)}=(1,\ldots,1,0,\ldots)$ 范数均为 $1$，对每个 $a\in\ell^1$ 有 $a(x^{(n)})\to\sum_j a_j$。它们实现了所有有限记录的逼近，但没有 $c_0$ 中的实现向量。这也排除了把弱星紧性当作原空间的弱紧性。

## 条件化恢复及边界

若恰有 $z_\lambda\in J(E)$，恢复向量存在且唯一：连续对偶由 Hahn–Banach 分离原空间点，$J$ 是等距嵌入。因此在可实现记录子空间上，距离稳定实际上为等式，并与 $T$ 相容。所有一致有界的记录都可实现，当且仅当 $J$ 满射，即 $E$ 自反；这是对**所有记录**的刻画，不是单个记录可实现的必要假设。

有限维、Hilbert 或自反空间提供了熟悉的强结论；题面只给了 Banach 结构。不得调用 Riesz 表示把任意 Banach 空间替换为 Hilbert 空间。

## 来源及审核范围

背景核对：[Math 7321 的 Goldstine 与自反性讲义](https://www.math.uh.edu/~bgb/Courses/Math7321S17/Math7321-20170209.pdf)。题面和上述有限观测分离论证为独立编写，没有复制讲义习题。AI 数学审核；人工待定；本题尚未 Lean 形式化。反例足以否定强目标，其他构造推进另记。
