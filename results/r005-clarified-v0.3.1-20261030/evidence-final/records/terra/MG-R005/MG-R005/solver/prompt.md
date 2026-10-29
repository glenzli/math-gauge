# 有限观测下的凸成本恢复

设 $E$ 为实 Hausdorff 局部凸空间，$E'$ 为连续对偶。给定凸函数 $f:E\to[0,+\infty]$，且至少在一点取有限值。

对每个有限维线性子空间 $F\subset E'$，令 $F^*$ 为其线性对偶，赋予有限维拓扑，并定义

$$q_F:E\to F^*,\qquad q_F(x)(\varphi)=\varphi(x),$$

以及局域成本记录

$$g_F(y)=\inf\{f(x):q_F(x)=y\},\qquad\inf\varnothing=+\infty.$$

当 $F\subset K$ 时，以 $r_{KF}:K^*\to F^*$ 表示限制映射。

从这些记录构造下半连续凸函数 $G:E\to[0,+\infty]$，满足 $G\le f$，并使对每个函数 $h:E\to[-\infty,+\infty]$，只要 $h\le f$ 且 $h$ 下半连续、凸，就有 $h\le G$。

这里扩展实值函数 $u$ 的下半连续性和凸性分别指其实高度上图

$$\operatorname{epi}_{\mathbb R}(u)=\{(x,t)\in E\times\mathbb R:u(x)\le t\}$$

是闭集和凸集；$h$ 允许取负无穷值。建立观测空间扩大时记录之间的关系，并说明整族记录如何确定 $G$。请给出主定理、构造及完整论证。
