# 参考论证：无限凸约束的有限问题恢复

作者目标成立。本稿为 AI 作者参考，独立语义审核及人工审核待定；未运行候选模型。Lean 覆盖见 `formal/COVERAGE.md`。

## 投影工具

在实 Hilbert 空间中，非空闭凸集 $K$ 的距离最小点 $p=P_Kx$ 存在且唯一。这里使用 Hilbert 投影定理；其构造是取距离趋于下确界的极小化序列，由平行四边形恒等式和中点凸性证明该序列 Cauchy，再用完备性及闭性取极限。唯一性同样来自中点比较。这个标准定理在所用 Mathlib 中已有实际证明，形式化直接调用它。

最小性等价于

$$\langle x-p,z-p\rangle\le0\qquad(z\in K).\tag{1}$$

正向可把 $p+t(z-p)$ 代入最小性，展开平方后令 $t\downarrow0$；反向展开 $\|x-z\|^2$ 即得最小性。由同一展开得到

$$\|p-z\|^2\le\|x-z\|^2-\|x-p\|^2\qquad(z\in K).\tag{2}$$

令 $u=P_Kx,v=P_Ky$。分别在 (1) 代入 $v,u$ 并相加，得到

$$\|u-v\|^2\le\langle x-y,u-v\rangle\le\|x-y\|\|u-v\|.$$

当 $u=v$ 时非扩张结论直接成立，否则除以正数 $\|u-v\|$。这也给出投影的稳定性，未假设 $K$ 是线性子空间。

## 从全部有限问题构造极限

每个 $C_F$ 闭凸且非空，包括 $F=\varnothing$。因此 $p_F=P_Fx$ 已由投影定理构造。固定 $x\in H$，置

$$a_F=\|x-p_F\|^2.$$

若 $F\subseteq G$，则 $C_G\subseteq C_F$，从而 $a_F\le a_G$。题设的 $z_F$ 给出

$$\|x-p_F\|\le\|x-z_F\|\le\|x\|+B.$$

故有限实数

$$L=\sup_F a_F\le(\|x\|+B)^2$$

存在。由 (2)，

$$\|p_F-p_G\|^2\le a_G-a_F\qquad(F\subseteq G).\tag{3}$$

给定 $\varepsilon>0$，由上确界定义选有限集 $F_0$ 使

$$L-a_{F_0}<(\varepsilon/2)^2.$$

对任意 $F,G\supseteq F_0$，令 $J=F\cup G$。式 (3) 及能量单调性给出

$$\|p_F-p_J\|<\varepsilon/2,\qquad\|p_G-p_J\|<\varepsilon/2.$$

三角不等式于是给出 $\|p_F-p_G\|<\varepsilon$。这是整个有限子集网的 Cauchy 性；没有选择一个被假定为共尾的可数约束族。Hilbert 空间完备，所以此网存在范数极限 $p$。

任取 $i\in I$。只要 $F\supseteq\{i\}$，便有 $p_F\in C_i$。由 $C_i$ 闭得 $p\in C_i$。对每个 $i$ 分别成立，故 $p\in C$，特别地 $C$ 非空。对任意 $z\in C$，有限最小性给出 $\|x-p_F\|\le\|x-z\|$；取极限得

$$\|x-p\|\le\|x-z\|.$$

因此 $p$ 是全约束的最小点。集合 $C$ 闭凸，前述唯一性表明该点唯一，定义 $Px=p$。这同时证明完整网 $P_Fx\to Px$。

## 最优值与稳定性

由于递增网 $a_F$ 趋于其上确界，且 $P_Fx\to Px$，有精确恒等式

$$\|x-Px\|^2=\sup_{F\subseteq I\ \mathrm{finite}}\|x-P_Fx\|^2.\tag{4}$$

并且对每个有限 $F$，把 $z=Px\in C_F$ 代入 (2)，得到

$$\|P_Fx-Px\|^2\le\|x-Px\|^2-\|x-P_Fx\|^2.\tag{5}$$

式 (5) 是参考中提供的误差关系，候选无需采用它作为指定证明路线。将投影非扩张性用于已证明非空的闭凸集 $C$，即得题面要求的 $\|Px-Py\|\le\|x-y\|$。

上述论证允许 $I$ 为空：此时只有空有限集，$C=H$，全部投影均为恒等映射。零 Hilbert 空间也无须排除。所构造的对象是闭凸集的距离投影，题设没有给出线性子空间结构，证明亦不使用投影线性。

## 审核范围

完整完成要求包含：全约束非空与唯一最小点、全有限子集网的范数收敛、有限最优值对全局值的精确确定，以及非扩张稳定性。可用弱紧性先证明非空，再证明强收敛；也可采用其他有效路线。不得因没有使用本稿的 Cauchy 网构造、没有逐字复现 (5)，或证明较短而扣分。

公开来源只用于 Hilbert 投影定理和其变分表述：Nicholas Hu, *Projections and least squares problems*, UCLA 官方个人页面，访问于 2026-10-29：<https://www.math.ucla.edu/~njhu/notes/nla/lsq/leastsquares/>。有限约束网的组合、量词安排与本稿完整推导独立编写。未使用未公开 OET 内容。
