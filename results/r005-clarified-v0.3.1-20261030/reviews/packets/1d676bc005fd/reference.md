# 参考审核：有限观测下的凸成本恢复

主目标成立。竞争函数的值域明确为 $[-\infty,+\infty]$，下半连续性与凸性采用题面的实高度上图约定。这里的最大性是精确的主结论；它不等于恢复未经下半连续化的 $f$。仿射分离可用于证明，但题面没有指定共轭或对偶路线。

## 1. 原始记录与投影

每个 $q_F$ 连续线性。由 $f\ge0$ 得 $g_F\ge0$；取 $f(x_0)<\infty$，则 $g_F(q_Fx_0)<\infty$。若两个记录值有限，在相应纤维内选择成本不超过下确界加 $\varepsilon$ 的原像，作凸组合，再令 $\varepsilon\downarrow0$，得 $g_F$ 凸。凸组合系数为 $0$ 或 $1$ 时为恒等式；两个端值中有 $+\infty$ 且系数严格在 $(0,1)$ 时，不等式右端为 $+\infty$。这覆盖全部情形，不需要下确界取到。

对 $F\subset K$，有 $q_F=r_{KF}q_K$，因而纤维分解给出

$$g_F(y)=\inf_{z\in K^*:\ r_{KF}z=y}g_K(z).\tag{1}$$

这只是对同一批 $x$ 分组取下确界；即使某个集合为空，按题设的约定仍成立。

## 2. 非负凸函数的闭上图

设 $V$ 为实 Hausdorff 局部凸空间，$u:V\to[0,+\infty]$ 凸，且至少一点有限。令

$$D=\overline{\operatorname{epi}u}\subset V\times\mathbb R.$$

$D$ 非空、闭、凸，包含于 $t\ge0$，并且沿正的垂直方向稳定。每个非空垂直截面因此是 $[a,+\infty)$，其中 $a\ge0$；空截面对应函数值 $+\infty$。由此唯一确定 $\bar u:V\to[0,+\infty]$，使 $D=\operatorname{epi}\bar u$。它下半连续且凸，并满足 $\bar u\le u$；在 $u$ 的任一有限点仍有限。

若 $h:V\to[-\infty,+\infty]$ 满足 $h\le u$ 且实高度上图闭，则 $\operatorname{epi}_{\mathbb R}u\subset\operatorname{epi}_{\mathbb R}h$，进而 $D\subset\operatorname{epi}_{\mathbb R}h$。若 $\bar u(v)<+\infty$，则 $(v,\bar u(v))\in D$ 给出 $h(v)\le\bar u(v)$；若 $\bar u(v)=+\infty$，同一不等式直接由扩展实数序成立。因此 $h\le\bar u$，包括 $h$ 取负无穷以及同时取两个无穷端点的情况。最大性于是对题面要求的所有下半连续凸竞争者成立；这一步甚至不需要额外使用 $h$ 的凸性，不要求 $h$ 正规、非负或有实值仿射下界。

还需要一个分离事实：$\bar u$ 是 $u$ 的所有连续实值仿射下界的上确界。为证明它，取 $(v_0,t_0)\notin D$。Hahn–Banach 的点与闭凸集严格分离给出 $\ell\in V'$、$\beta\in\mathbb R$ 和 $a\in\mathbb R$，使

$$\ell(v)+\beta t\ge a>\ell(v_0)+\beta t_0\qquad((v,t)\in D).$$

垂直向上稳定迫使 $\beta\ge0$。若 $\beta=0$，由 $t\ge0$ 可把左侧系数改成足够小的 $\varepsilon>0$：左侧仍不小于 $a$，而 $a>\ell(v_0)+\varepsilon t_0$ 仍成立。因此可取 $\beta>0$。于是

$$a_0(v)=\frac{a-\ell(v)}\beta$$

为连续仿射函数，满足 $a_0\le u$ 且 $a_0(v_0)>t_0$。反过来，每个连续仿射下界的不等式都保持到上图闭包，所以它不超过 $\bar u$。对每个实数 $t_0<\bar u(v_0)$ 应用上述分离，便得所称上确界公式，包括 $\bar u(v_0)=+\infty$ 的情形。

## 3. 从有限记录重构

在 $F^*$ 上应用第 2 节，得到 $\bar g_F$。它完全由记录 $g_F$ 决定。定义

$$G(x)=\sup_{F\subset E'\ \mathrm{finite\ dim}}\bar g_F(q_Fx).\tag{2}$$

每个被取上确界的函数都下半连续、凸、非负，且不超过 $f$；因此 $G$ 也有这些性质，并在 $f(x_0)<\infty$ 处有限。

若 $F\subset K$，由 (1) 得 $\bar g_F(r_{KF}z)\le g_K(z)$。左侧是 $K^*$ 上的下半连续凸函数，所以由 $\bar g_K$ 的最大性得

$$\bar g_F(r_{KF}z)\le\bar g_K(z).\tag{3}$$

因此式 (2) 是随观测空间扩大而递增的有向上确界。任意两个有限维观测空间包含于它们的有限维和，故所用族确实有向。

为证明 $G$ 的最大性，对 $f$ 应用第 2 节，记其闭上图函数为 $\bar f$。已知 $G\le\bar f$。任取连续仿射下界 $a(x)=\varphi(x)+b\le f(x)$，取 $F=\operatorname{span}\{\varphi\}$，并令 $a_F(y)=y(\varphi)+b$。纤维定义给出 $a_F\le g_F$，所以 $a_F\le\bar g_F$。于是

$$a(x)\le\bar g_F(q_Fx)\le G(x).$$

第 2 节的仿射分离结论说明 $\bar f$ 是所有这类 $a$ 的上确界，所以 $\bar f\le G$。故 $G=\bar f$，证明主目标，且式 (2) 明确说明了整族记录如何决定它。这一证明不要求模型使用共轭记号。

## 4. 可选的更精确记录关系

这一节不是完成题面所必需的指定路线。它说明投影与闭上图之间的准确关系。

令 $h(y)=\inf_{r_{KF}z=y}\bar g_K(z)$。纤维凸组合证明 $h$ 凸，且 $h\ge0$、至少一点有限。由 (1)、(3) 得

$$\bar g_F\le h\le g_F.$$

对这些函数取最大下半连续凸下界，利用第 2 节的最大性两次，得

$$\overline{\left(y\longmapsto\inf_{r_{KF}z=y}\bar g_K(z)\right)}=\bar g_F.\tag{4}$$

通常不能删去式 (4) 左侧的横线。取 $E=\mathbb R^2$，并令 $f$ 为集合

$$D=\{(x,y):x>0,\ y\ge 1/x\}$$

的指示成本：在 $D$ 上为零，其余点为 $+\infty$。函数 $x\mapsto1/x$ 的二阶导数为 $2/x^3>0$，故它在 $(0,+\infty)$ 上凸，从而 $D$ 凸。若 $(x_j,y_j)\in D$ 收敛到有限点 $(x,y)$，则 $x,y\ge0$ 且 $xy\ge1$，故 $x>0$ 且 $y\ge1/x$；所以 $D$ 闭。取 $K=E'$，$F$ 仅观测第一坐标。此时 $\bar g_K=f$，而 $h$ 在 $x>0$ 为零、在 $x\le0$ 为 $+\infty$；$\bar g_F$ 则在 $x\ge0$ 为零。因此 $h(0)=+\infty$ 而 $\bar g_F(0)=0$。

## 5. 边界与可接受的替代证明

在 $E=\mathbb R$ 取 $f=0$ 于 $(0,+\infty)$，其余为 $+\infty$，得到 $G=0$ 于 $[0,+\infty)$，其余为 $+\infty$。这证明原函数的边界值未必恢复。若 $f$ 已下半连续，则其上图已闭，故 $G=f$；反之 $G=f$ 也蕴含 $f$ 下半连续。

下确界不必取到。例如 $f(x)=e^x$ 非负、连续且凸，$\inf_{x\in\mathbb R}f(x)=0$，而每个 $f(x)>0$。当 $F=0$ 时，这就是原始记录的唯一纤维。

候选可以使用 Fenchel–Moreau 定理、直接上图分离或其他严格等价方法；必须核对一般局部凸空间及扩展值条件，并把恢复对象与有限记录联系起来。无需复述本稿的可选反例、式 (4) 或每个辅助步骤。

## 来源与审核范围

公开背景为 [Bertsekas 的 MIT 6.253 官方讲义](https://ocw.mit.edu/courses/6-253-convex-analysis-and-optimization-spring-2012/6c63c6219c60378bc27d5b4a9167f1bc_MIT6_253S12_lec_comp.pdf)中的凸上图与共轭观点。一般局部凸空间上的分离、有限记录重构及本稿见证均独立展开；没有把有限维讲义结论直接无条件搬到一般空间。未使用未公开 OET 材料。

本稿为改版参考证明。AI 独立数学审核、人工审定、模型校准和形式化证据分别以本题 review.json 及其引用记录为准；不能由参考论证或空的 Lean 检查清单推出模型难度或形式化通过。
