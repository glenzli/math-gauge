# 凸投影的恢复、复合与变分方程：逐阶段参考与判准

本组 version 0.1.0；AI 作者自查完成，human pending。未调用候选模型，未为本组生成或编译 Lean。既有母题参考只作为本组完整数学论证的来源，不继承其模型成绩或形式化覆盖。每阶段均 mandatory；分值用于诊断，整组 pass 必须全部阶段实质完成。

## S1 仿射投影

判定：true。

对闭子空间 L，取极小化序列，平行四边形恒等式和中点留在 L 使序列 Cauchy；闭性与完备性给唯一最小点 P_Lx。对任意 h∈L，沿双向直线变分得到 x−P_Lx⊥L，故分解 H=L⊕L⊥ 唯一且 P_L 线性。平移变量给公式。若 0∈K，则 K=L 而投影线性；若投影线性，P_K0=0∈K，故该条件必要。

判准：实际投影及唯一性；线性的充要条件。

## S2 嵌套仿射约束

判定：true。

取 p∈K_2 同时平移成 L_2⊂L_1。P_{L_1} 固定 L_2；x−P_{L_1}x∈L_1⊥⊂L_2⊥，所以向 L_2 的投影不变。分解 x−P_{L_2}x=(x−P_{L_1}x)+(P_{L_1}x−P_{L_2}x)，两项正交，勾股恒等式给结论。

判准：两个复合方向；精确能量恒等式。

## S3 交换投影的有限复合

判定：true。

每个 P_j 自伴、幂等。交换使乘积自伴幂等，并且其像在每个 L_j 中；它固定交空间，故像恰为交空间。自伴幂等算子 A 满足 x−Ax 与其像正交，因为 ⟨x−Ax,Ay⟩=⟨A(x−Ax),y⟩=0，因此为正交投影。逆向若 P_1P_2 为正交投影，则等于其伴随 P_2P_1。m=0 的空乘积为恒等、交为 H。

判准：像等于交空间；必要方向用自伴性；空族。

## S4 整体对象与全部恢复目标

判定：true。

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

判准：Construct the unique global nearest point for every x and prove the whole intersection is nonempty under the exact uniform finite-feasibility hypothesis.；Prove norm convergence of the full finite-subset net, with no assumption of a countable cofinal constraint family.；Determine the global optimal value exactly from the finite optimal values and prove the stated nonexpansive estimate.。

## S5 恢复映射的代数性质

判定：false。

否。取 H=R、单一闭凸约束 C=[0,∞)，B=0 即满足全部有限可行条件。最近点是 P(x)=max(x,0)，但 P(0)=0、(P(−1)+P(1))/2=1/2，不保持中点，故非仿射。S1 的仿射结构不能从闭凸性获得。

判准：核验统一有限可行界；明确违反仿射恒等式。

## S6 一个后续变分恢复

判定：construction。

投影变分式为 p=P_Cu 当且仅当 ⟨u−p,z−p⟩≤0 对所有 z∈C；由最小性沿线段变分及平方展开分别证明两向。令 T(x)=P_C(x−γAx)。S4 非扩张性给 ||Tx−Ty||²≤(1−2γm+γ²L²)||x−y||²。若 H 有两个不同点，则 Cauchy–Schwarz 给 m≤L，括号非负且小于 1，取 q 为其平方根。C 为非空完备空间，Banach 不动点定理给唯一 x_*，||x_n−x_*||≤q^n||x_0−x_*||（n≥0，q=0 单独解释一步后已到点）。不动点与上述变分式等价，故给所需唯一解。若 H 为零空间，则 C 仅一点，结论直接成立，不对可能为负的括号开方。

判准：实际压缩迭代；变分式双向；唯一性及零空间。
