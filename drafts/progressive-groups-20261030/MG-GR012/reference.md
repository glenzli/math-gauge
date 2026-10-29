# 凸势、对偶与有限记录逼近：逐阶段参考与判准

本组 version 0.1.0；AI 作者自查完成，human pending。未调用候选模型，未为本组生成或编译 Lean。既有母题参考只作为本组完整数学论证的来源，不继承其模型成绩或形式化覆盖。每阶段均 mandatory；分值用于诊断，整组 pass 必须全部阶段实质完成。

## S1 二次记录与循环兼容

判定：true。

h(z)−h(x)−(Qx+b)ᵀ(z−x)=(z−x)ᵀQ(z−x)/2≥0，相加得循环不等式。若 y∈∂h(x)，令 z=x+tv 并分别 t→0±，得 yᵀv=(Qx+b)ᵀv，故次梯度唯一。对 g，Γ 全定义使 g 处处有限；在线段 x_j=jx/n 上用相邻两点的支持不等式夹住 g(x_{j+1})−g(x_j)。求和是同一连续线性梯度沿线段积分的上下 Riemann 和，两者趋于 h(x)−h(0)，故 g(x)=h(x)。

判准：支持差平方公式；循环及次梯度唯一；潜势唯一性。

## S2 对偶问题的整体求解

判定：construction。

令 v=Q^{-1}(y−b)。配方 yᵀx−h(x)=vᵀQv/2−(x−v)ᵀQ(x−v)/2，故 h*(y)=(y−b)ᵀQ^{-1}(y−b)/2，唯一最大点 v。h(x)+h*(y)−yᵀx=(x−v)ᵀQ(x−v)/2，等号当且仅当 y=Qx+b；于是 ∇h*(y)=Q^{-1}(y−b) 与 ∇h 互逆。

判准：完整配方与最优点；等号和双向逆。

## S3 退化二次型

判定：false。

总主张为假，例如 Q=0、b=0 时 y≠0 给无穷值，y=0 的任意 x 均最优。一般若 y−b 不在 im Q=(ker Q)⊥，取 w∈ker Q 且 (y−b)ᵀw≠0，沿 ±tw 令目标趋∞。若 Qv=y−b，则同样配方给 h*(y)=vᵀQv/2，全部最优点为 v+ker Q；换一个 v 不改该值。故有限值域是 b+im Q，唯一最大点仅当 ker Q=0。

判准：有限域与无穷域；全部最优点及值无关性。

## S4 整体对象与全部恢复目标

判定：true。

## 有限路径定义

每条路径从所选记录 $(\bar x,\bar y)$ 出发，随后是任意有限列 $(x_1,y_1),\ldots,(x_n,y_n)\in\Gamma$，允许 $n=0$。令 $(x_0,y_0)=(\bar x,\bar y)$，定义实值仿射函数

$$
A_{\pi}(z)=\sum_{j=0}^{n-1}y_j(x_{j+1}-x_j)
+y_n(z-x_n).
$$

空和取零。定义

$$f(z)=\sup_{\pi}A_{\pi}(z).\tag{1}$$

零长度路径给出 $f(z)\ge\bar y(z-\bar x)$，所以此上确界绝不为 $-\infty$，允许为 $+\infty$。每个记录的第二坐标是连续线性泛函，因此每个 $A_\pi$ 连续仿射，故其上确界下半连续；其上图是各闭仿射半空间 $t\ge A_\pi(z)$ 的交，因而凸。此处凸性使用实高度上图，等价于通常的扩展值凸性约定，不需要对 $+\infty-\infty$ 作运算。

当 $z=\bar x$ 时，循环单调性逐条给出 $A_\pi(\bar x)\le0$，而零长度路径取零。因此 $f(\bar x)=0$，从而 $f$ 正规。



## 图上的有限性与次梯度

固定 $(x,y)\in\Gamma$。在任意路径后接上 $(x,y)$，再闭合到 $\bar x$，由循环单调性有

$$A_\pi(x)+y(\bar x-x)\le0.$$

对 $\pi$ 取上确界得到

$$\bar y(x-\bar x)\le f(x)\le y(x-\bar x)<+\infty.\tag{2}$$

故每个图记录的第一坐标处都有真实的有限函数值。

同样的路径拼接，不闭合而以任意 $z\in E$ 结束，给出

$$f(z)\ge A_\pi(x)+y(z-x).$$

式 (2) 确保 $f(x)$ 有限。对所有路径取上确界，便得到

$$f(z)\ge f(x)+y(z-x).$$

这正是 $y\in\partial f(x)$。拼接构造使用的是题设图上的有限记录，没有预先假定存在势函数，也没有假定上确界由某一条路径取得。



## 逐点最小性与唯一性

设 $g$ 是任意满足题面全部条件的函数。对一条从所选基点出发的路径，次梯度条件依次给出

$$g(x_{j+1})\ge g(x_j)+y_j(x_{j+1}-x_j).$$

这些中间值均有限，因为每个 $(x_j,y_j)\in\Gamma$ 都属于 $\partial g$ 的图。最后再用

$$g(z)\ge g(x_n)+y_n(z-x_n)$$

并逐步相加，利用 $g(\bar x)=0$，得到 $g(z)\ge A_\pi(z)$。对所有有限路径取上确界即得 $g(z)\ge f(z)$。

这个比较实际只使用了规范化和全部次梯度不等式；竞争函数的下半连续性与凸性不必额外用于比较步骤。构造出的 $f$ 本身已满足这两项性质，因此它属于指定的竞争类并在其中最小。若有两个逐点最小者，互相比较得到逐点相等，故唯一性是函数的严格相等。

判准：Construct a proper lower semicontinuous convex potential on the exact stated real topological vector space, normalized at the supplied base record.；Prove each original graph record gives a finite base value and the full global subgradient support inequality.；Prove pointwise minimality in the entire stated admissible class and uniqueness as equality of extended-valued functions.。

## S5 势的图是否恰好等于输入

判定：false。

否。取 E=R、Γ={(0,0)}，所有条件成立。次梯度条件强迫任何竞争 g 满足 g(z)≥g(0)=0，而零函数可行，故最小势 f≡0。每个 (x,0) 都在 graph ∂f，特别 (1,0) 不在 Γ。最小函数的唯一性并不等于输入图已最大。

判准：合法规范化最小势；严格图包含见证。

## S6 有限记录的恢复极限

判定：true。

有限路径公式中每条路径只用有限记录，故交换两个上确界得 f_Γ=sup_Λf_Λ；增加记录使路径集增加。有限 Λ 的路径若重复某记录，重复点之间的闭路径权重≤0，删去该段使终点仿射值不减；反复删去后只有不重复路径，有限多条，所以 f_Λ 是有限个实值仿射函数之最大，处处有限且连续。处处有限凸函数 f_Γ 在 R^d 连续（可由围住一点的小立方体顶点值界住函数再用凸性给局部斜率界）。在紧集 K 上，对 ε>0，开集 {x:f_Γ(x)−f_Λ(x)<ε} 随 Λ 有向增加且覆盖 K。取有限子覆盖并合并这几份 Λ 得共同指标，此后所有差在 K 上小于 ε。若 K 空结论自动成立。

判准：有限路径覆盖全部记录；有限势连续的证明；有向 Dini 论证。
