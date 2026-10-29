# 作者参考：参数化最小解、消元与伴随传递

主目标成立。本文为 AI 原创组合与证明；公共背景是完备格不动点理论和 Galois 连接。独立数学复核、Lean 编译和人工审定分别记录，不能互相替代。所有反例仅供评审识别错误证明，不是候选额外必答项。

## 实际结构与最小性

仅使用题给完备格、偏序和联合单调性。特别地，参数集 $P$ 无须完备。对于完备格上的单调自映射 $T$，定义
$$
\mu T=\bigwedge\{x:T(x)\le x\}.
$$
这一定义中的集合非空，因为顶元属于它。若 $T(x)\le x$，单调性给出 $T(\mu T)\le T(x)\le x$，故 $T(\mu T)\le\mu T$。再由单调性，$T(T(\mu T))\le T(\mu T)$，所以 $T(\mu T)$ 本身属于被取下确界的集合，因而 $\mu T\le T(\mu T)$。两边合并得到不动性。

因此 $\mu T$ 是最小不动点，并且满足更有用的性质：每个前不动点 $T(x)\le x$ 都满足 $\mu T\le x$。如果 $T\le U$ 点态成立，则 $\mu U$ 是 $T$ 的前不动点，从而 $\mu T\le\mu U$。

取 $\sigma(p)=\mu\Phi_p$。联合单调性使 $p\le q$ 蕴含 $\Phi_p\le\Phi_q$，故 $\sigma$ 单调。这同时证明其定义和所要求的最小性；并没有通过某个未经证明的迭代极限定义它。

## 两块消元是关键桥梁

设 $X,Y$ 为任意完备格，$f:X\times Y\to X$、$g:X\times Y\to Y$ 联合单调。令
$$
b(x)=\mu(y\mapsto g(x,y)),\qquad
a_* = \mu(x\mapsto f(x,b(x))),\qquad
b_*=b(a_*).
$$
由上一段的比较性质，$b$ 单调，因而约化自映射 $x\mapsto f(x,b(x))$ 也单调。两个不动点等式分别给出
$$
f(a_*,b_*)=a_*,\qquad g(a_*,b_*)=b_*.
$$

关键还在于最小性，不能从“不动”直接得出它。若 $(x,y)$ 是联合映射的前不动点，即 $f(x,y)\le x$、$g(x,y)\le y$，则
$$
b(x)\le y,\quad f(x,b(x))\le f(x,y)\le x,\quad a_*\le x.
$$
再由 $b$ 的单调性得 $b_*=b(a_*)\le b(x)\le y$。所以 $(a_*,b_*)$ 小于每个联合前不动点；它恰是联合映射的最小不动点。这证明了消元法，而不是把消元正确性放入定义。

## 三块、分组及参数

固定 $p$，先把 $B\times C$ 看作一块。对每个 $a$，上面的两块论证构造并识别 $(b,c)$ 子系统的最小解，并证明它随 $a$ 单调。再将这一函数代入 $A$ 方程，第二次使用两块论证，结果便是 $\mu\Phi_p$。

交换 $A,B,C$ 的角色，或把任意两者先组成一块，完全相同的论证仍适用，因为交换、结合乘积坐标是序同构。每一种合法消元最终都给出同一联合系统的最小不动点；偏序中最小元唯一，故所有最终三元组相同。中间约化函数的单调性必须由参数化最小不动点的比较性质验证，不能仅因为原始三个映射单调就省去这一依赖。

## 沿 Galois 连接传递

固定 $p$，写 $T=\Phi_p$、$U=\Psi(p,-)$、$s=\mu T$、$t=\mu U$。由题给逐点等式和 $T(s)=s$，
$$
U(\alpha s)=\alpha T(s)=\alpha s.
$$
因此 $t\le\alpha s$。反方向需要实际使用伴随关系，而不是把这一不等式倒转。

伴随关系给出 $\alpha\gamma(t)\le t$。于是
$$
\alpha T\gamma(t)=U\alpha\gamma(t)\le U(t)=t.
$$
再用伴随关系得到 $T\gamma(t)\le\gamma(t)$。最小前不动点性质推出 $s\le\gamma(t)$，再一次伴随转换便得 $\alpha s\le t$。故 $\alpha\sigma(p)=\tau(p)$。

这一等式与所有分块计算一致，因为前一部分已把每种分块结果识别为同一个 $s$。题给假设只是一次更新在两个结构之间交换；最小解的交换是刚刚证明的结论。

## 对错误中间断言的具体检查

1. **单调不推出可数迭代得到最小解。** 取 $X=\mathbb N\sqcup\{\omega\}$，完备格为 $\mathcal P(X)$，定义
   $$
   T(U)=\{0\}\cup\{n+1:n\in U\cap\mathbb N\}\cup
   \begin{cases}\{\omega\},&\mathbb N\subseteq U,\\\varnothing,&\text{否则}.\end{cases}
   $$
   它单调；从空集迭代第 $n$ 次得到 $\{0,\ldots,n-1\}$。可数次迭代的并是 $\mathbb N$，但 $T(\mathbb N)=X\ne\mathbb N$，而最小不动点是 $X$。它可作为三块系统的一个分量，另两格取单点格，完全满足题目结构。
2. **将其他变量永久固定于底元后分别求解，不是消元。** 在二元链 $0<1$ 上，令 $f(x,y)=y$、$g(x,y)=1$。分别把另一变量冻结在 $0$ 得到 $(0,1)$，但联合更新将它送到 $(1,1)$。正确消元得到 $(1,1)$。增加一个单点块即可嵌入题面。
3. **普通单调半共轭不保存最小解。** 在同一二元链上令 $T=U=\mathrm{id}$、$\alpha\equiv1$。则 $\alpha T=U\alpha$，但 $\alpha(\mu T)=1\ne0=\mu U$。该 $\alpha$ 没有右伴随：若有，伴随条件在 $x=y=0$ 处会要求假命题 $1\le0$ 等价于真命题 $0\le\gamma(0)$。这说明参考证明中的伴随步骤确实承担作用，并非装饰假设。
4. **不动点不等于最小不动点。** 二元链上的恒等映射同时固定 $0,1$，但最小解只可能是 $0$。因此只校验代回方程不足以验证任何一次消元。

这些反例不否定本题目标，也不要求候选写出它们。一个合法的简短 Bekić 定理加伴随不动点传递证明可以完整完成本题。尚无候选模型试跑，不能由参考链长度宣称经验难度。

## 来源与原创范围

- Mathlib 的 [FixedPoints](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/FixedPoints.html) 提供实际使用的最小不动点背景；本地形式化固定到指定 Mathlib 提交，网页最新版仅作公共出处。
- Mathlib 的 [GaloisConnection.Basic](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/GaloisConnection/Basic.html) 提供伴随关系的公理接口。
- 三块参数问题、消元与精确传递的组合、候选题面和评审反例为本题独立组织；没有复制现成习题或来源证明文字。
