# 循环兼容记录的凸势

设 $E$ 是实向量空间，其上给定一个使加法与标量乘法连续的拓扑。记 $E′$ 为所有连续实线性泛函 $E\to\mathbb R$ 组成的空间。给定非空集合 $\Gamma\subseteq E\times E′$。假定 $\Gamma$ 循环单调：对任意 $n\ge0$ 及任意 $(x_0,y_0),\ldots,(x_n,y_n)\in\Gamma$，令 $x_{n+1}=x_0$，有

$$\sum_{j=0}^{n}y_j(x_{j+1}-x_j)\le0.$$

固定一个记录 $(\bar x,\bar y)\in\Gamma$。对于函数 $f:E\to\mathbb R\cup\{+\infty\}$，定义

$$
\partial f(x)=\bigl\{y\in E′:\ f(x)<+\infty,\quad
f(z)\ge f(x)+y(z-x)\ \text{对所有 }z\in E\bigr\}.
$$

称 $f$ 为正规函数，是指它至少在一点取有限值。

从 $\Gamma$ 与所选记录构造正规、下半连续、凸函数 $f$，使

$$f(\bar x)=0,\qquad (x,y)\in\Gamma\Longrightarrow y\in\partial f(x),$$

并使 $f$ 在满足这些条件的全部函数中逐点最小。请给出构造、最小性及唯一性的完整论证。
