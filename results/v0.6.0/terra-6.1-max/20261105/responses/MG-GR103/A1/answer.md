## S1　参数与消元

先证明一个供各阶段使用的事实。设 \(X\) 是完备格，\(T:X\to X\) 单调，令
\[
E_T=\{x\in X:T(x)\le x\},\qquad m=\bigwedge E_T.
\]
由于 \(\top_X\in E_T\)，该集合非空。对每个 \(e\in E_T\)，由单调性，
\[
T(m)\le T(e)\le e,
\]
故 \(T(m)\le m\)。再由单调性，\(T(T(m))\le T(m)\)，所以 \(T(m)\in E_T\)，从而 \(m\le T(m)\)。因此 \(T(m)=m\)，且 \(m\) 小于每个前不动点，特别小于每个不动点。这证明了 \(\mu T\) 的存在，并给出
\[
\mu T=\bigwedge\{x:T(x)\le x\}. \tag{1}
\]

还有一个参数单调性结论：若 \(Q\) 是偏序集，\(K:Q\times X\to X\) 联合单调，则
\[
q\longmapsto \mu(x\mapsto K(q,x))
\]
单调。事实上，若 \(q\le q'\)，则 \(K(q,-)\le K(q',-)\)；因此 \(\mu K(q',-)\) 是 \(K(q,-)\) 的前不动点，由 (1) 得到所需比较。

有限完备格积仍是完备格，故可构造
\[
\boxed{\displaystyle
\sigma(p)=\bigwedge\{z\in L:\Phi_p(z)\le z\}.}
\]
每个 \(\Phi_p\) 单调，所以 (1) 给出 \(\sigma(p)=\mu\Phi_p\)；上述参数结论又表明 \(\sigma:P\to L\) 单调。

### 一般两块消元

将任意一些变量组成块 \(X\)，其余变量组成块 \(Y\)。二者都是完备格的有限积。把系统写成
\[
(x,y)\longmapsto \bigl(f(p,x,y),g(p,x,y)\bigr),
\]
其中 \(f:P\times X\times Y\to X\)、\(g:P\times X\times Y\to Y\) 联合单调。定义
\[
a(p,y)=\mu_x f(p,x,y),\qquad
k(p,y)=g(p,a(p,y),y),\qquad
b(p)=\mu_y k(p,y). \tag{2}
\]
这里的最小不动点均良定义：相应自映射的定义域是完备格，且自映射单调。以 \(P\times Y\) 为参数集应用上面的参数结论，\(a\) 联合单调；于是 \(k\) 联合单调，进而 \(b\) 单调。

我们证明
\[
\boxed{\displaystyle
\mu_{(x,y)}(f,g)=\bigl(a(p,b(p)),b(p)\bigr).} \tag{3}
\]
右端是不动点：\(a(p,b(p))\) 固定 \(f(p,-,b(p))\)，而 \(b(p)\) 固定 \(k(p,-)\)。若 \((x,y)\) 是原系统的任意前不动点，则
\[
a(p,y)\le x,\qquad
k(p,y)=g(p,a(p,y),y)\le g(p,x,y)\le y.
\]
因此 \(b(p)\le y\)，再由 \(a\) 的单调性，
\[
a(p,b(p))\le a(p,y)\le x.
\]
故 (3) 的右端小于每个前不动点，确为最小不动点。

公式 (2)–(3) 可反复应用：每消去一个块，尚未消去的变量与 \(p\) 一起充当参数；约化系统仍联合单调，而每个中间参数最小解都由上述参数结论保证良定义且单调。之后按消元的反序代回即可。由归纳，**任意变量分块及其任意逐块消元顺序都得到 \(\sigma(p)\)**；各重建表达式也是单调映射。

例如，依次消去 \(A,B,C\) 时，可令
\[
\begin{aligned}
a(p,b,c)&=\mu_a F(p,a,b,c),\\
b(p,c)&=\mu_b G(p,a(p,b,c),b,c),\\
c(p)&=\mu_c H\bigl(p,a(p,b(p,c),c),b(p,c),c\bigr).
\end{aligned}
\]
这些中间映射均单调，最后
\[
\sigma(p)=
\bigl(a(p,b(p,c(p)),c(p)),\ b(p,c(p)),\ c(p)\bigr).
\]

## S2　伴随结构的精确传递

由 \(\alpha\dashv\gamma\)，有
\[
\alpha\gamma(y)\le y,\qquad x\le\gamma\alpha(x). \tag{4}
\]
固定 \(p\)，记 \(T=\Phi_p\)、\(U=\Psi_p\)、\(m=\mu U\)。两者都是完备格上的单调自映射，故最小不动点存在。

由精确关系 \(\alpha T=U\alpha\)、(4) 及 \(U\) 的单调性，
\[
\alpha T\gamma(m)=U\alpha\gamma(m)\le U(m)=m.
\]
伴随关系给出 \(T\gamma(m)\le\gamma(m)\)。于是
\[
\mu T\le\gamma(m)
\quad\Longleftrightarrow\quad
\alpha(\mu T)\le m.
\]
另一方面，
\[
U\alpha(\mu T)=\alpha T(\mu T)=\alpha(\mu T),
\]
所以 \(\alpha(\mu T)\) 是 \(U\) 的不动点，故 \(m\le\alpha(\mu T)\)。因此
\[
\boxed{\alpha(\sigma(p))=\mu\Psi_p.}
\]

S1 的每种分块、消元顺序均重建出同一个 \(\sigma(p)\)，所以对任何一种结果施加 \(\alpha\) 都得到同一个 \(\mu\Psi_p\)。并且 \(\Psi\) 联合单调，故 \(p\mapsto\mu\Psi_p\) 由 S1 的参数结论单调；这也与 \(p\mapsto\alpha(\sigma(p))\) 的单调性一致。这里不需要、也不声称 \(\alpha\) 能逐块分解。

## S3　单边更新关系

本阶段只使用各小项指定的单边不等式，而不沿用 S2 的精确等式。由于 \(\mu T\in L\)、\(\mu U\in M\)，比较通过 \(\alpha\) 或 \(\gamma\) 表述。

### 1. 假设 \(\alpha T\le U\alpha\)

令 \(m=\mu U\)。由伴随关系的余单位、\(U\) 的单调性和单边假设，
\[
\alpha T\gamma(m)\le U\alpha\gamma(m)\le U(m)=m.
\]
故 \(T\gamma(m)\le\gamma(m)\)，从而
\[
\boxed{\mu T\le\gamma(\mu U)
\quad\Longleftrightarrow\quad
\alpha(\mu T)\le\mu U.}
\]

严格有限例子：取 \(L=M=\{0<1\}\)，\(\alpha=\gamma=\mathrm{id}\)，令 \(T\equiv0\)、\(U\equiv1\)。则
\[
\alpha T\le U\alpha,\qquad
\alpha(\mu T)=0<1=\mu U.
\]
故反向比较不能普遍推出。

### 2. 假设 \(U\alpha\le\alpha T\)

因为
\[
U\alpha(\mu T)\le\alpha T(\mu T)=\alpha(\mu T),
\]
\(\alpha(\mu T)\) 是 \(U\) 的前不动点，所以
\[
\boxed{\mu U\le\alpha(\mu T).}
\]

严格有限例子：仍取两元素链及恒等伴随，但令 \(T\equiv1\)、\(U\equiv0\)。则
\[
U\alpha\le\alpha T,\qquad
\mu U=0<1=\alpha(\mu T).
\]
故反向比较不能普遍推出。

注意，第二种结论不等价于 \(\gamma(\mu U)\le\mu T\)。例如取两元素链，
\[
\alpha\equiv0,\qquad \gamma\equiv1,\qquad T\equiv0,\qquad U\equiv0.
\]
此时 \(\alpha\dashv\gamma\)，也满足 \(U\alpha\le\alpha T\)，但
\(\gamma(\mu U)=1>0=\mu T\)。而上一严格例子又表明第二种假设下不一定有 \(\mu T\le\gamma(\mu U)\)。

这些两元素链例子也可嵌入原设定，取 \(A=\{0<1\}\)、\(B,C\) 为单元素格、\(P\) 为单元素偏序集即可。

## S4　单调半共轭

精确等式**不必成立**。但总有
\[
\boxed{\mu U\le\alpha(\mu T).}
\]
因为半共轭给出
\[
U\alpha(\mu T)=\alpha T(\mu T)=\alpha(\mu T),
\]
故 \(\alpha(\mu T)\) 是 \(U\) 的不动点，必大于等于 \(\mu U\)。

反例取 \(L=M=\{0<1\}\)、\(T=U=\mathrm{id}\)，以及常值映射 \(\alpha\equiv1\)。所有映射均单调，且 \(\alpha T=U\alpha\)，但
\[
\alpha(\mu T)=\alpha(0)=1>0=\mu U.
\]

## S5　连续递推的传递

**可以精确传递。** 先对 \(T\) 证明递推公式。令
\[
x_n=T^n(\bot_L),\qquad x_\omega=\bigvee_{n<\omega}x_n.
\]
由 \(T\) 单调，\((x_n)\) 递增；由其 \(\omega\)-链上确界保持性，
\[
T(x_\omega)=\bigvee_n T(x_n)
=\bigvee_n x_{n+1}
=x_\omega.
\]
又由归纳 \(x_n\le\mu T\)，故 \(x_\omega\le\mu T\)；结合 \(x_\omega\) 是不动点，得到
\[
\mu T=\bigvee_n T^n(\bot_L).
\]
同理，本阶段的 \(U\) 满足
\[
\mu U=\bigvee_n U^n(\bot_M).
\]

由半共轭及 \(\alpha(\bot_L)=\bot_M\)，归纳得到
\[
\alpha(T^n\bot_L)=U^n\bot_M.
\]
因此利用 \(\alpha\) 对递增 \(\omega\) 链上确界的保持性，
\[
\alpha(\mu T)
=\alpha\left(\bigvee_nT^n\bot_L\right)
=\bigvee_n\alpha(T^n\bot_L)
=\bigvee_nU^n\bot_M
=\mu U.
\]

此机制确实不要求右伴随。例如取
\[
L=\mathcal P(\{1,2\}),\qquad M=\{0<1\},\qquad
\alpha(X)=
\begin{cases}
1,&X=\{1,2\},\\
0,&\text{其他情况},
\end{cases}
\]
并令 \(T,U\) 均为恒等映射。有限偏序集中的递增 \(\omega\) 链最终稳定，所以 \(\alpha\) 保持此类链的上确界，也保持底元。但 \(\alpha\) 无右伴随：否则由 \(\alpha(\{1\})=\alpha(\{2\})=0\)，伴随关系将推出 \(\{1,2\}\le\gamma(0)\)，进而推出 \(\alpha(\{1,2\})\le0\)，矛盾。

## S6　可数阶段与边界

\(x_\omega\) **不必**是 \(\mu T\)。仅由单调性，总有
\[
x_\omega\le\mu T
\quad\text{且}\quad
x_\omega
=\bigvee_nT^{n+1}\bot
\le T(x_\omega).
\]
第一式逐项由 \(T^n\bot\le\mu T\) 得出；第二式由
\(T^{n+1}\bot\le T(x_\omega)\) 得出。因此一个必要充分条件是
\[
\boxed{T(x_\omega)\le x_\omega.} \tag{5}
\]
事实上，若 (5) 成立，则它与上述反向不等式合起来说明 \(x_\omega\) 是不动点，故 \(x_\omega=\mu T\)；反之，若 \(x_\omega=\mu T\)，则 (5) 必成立。等价地，\(T\) 只需在这条特定迭代链上满足
\[
T\left(\bigvee_nT^n\bot\right)
=\bigvee_nT^{n+1}\bot,
\]
不必在所有递增 \(\omega\) 链上连续。

失败例子取序数链
\[
L=\{0,1,2,\ldots,\omega,\omega+1\},
\]
按通常次序排列。这是完备格：每个子集的上界集合非空，且有最小元；下确界同样存在。定义
\[
T(n)=n+1\quad(n<\omega),\qquad
T(\omega)=\omega+1,\qquad T(\omega+1)=\omega+1.
\]
\(T\) 单调，且 \(T^n(0)=n\)，所以
\[
x_\omega=\omega,\qquad T(x_\omega)=\omega+1>x_\omega.
\]
唯一不动点是 \(\omega+1\)，故 \(\mu T=\omega+1\)。

最后，前述精确传递有两个**充分机制**：

1. **伴随机制（S2）：** \(T,U\) 单调，\(\alpha\dashv\gamma\)，且 \(\alpha T=U\alpha\)。不要求 \(\omega\)-连续性。
2. **连续递推机制（S5）：** \(T,U,\alpha\) 保持递增 \(\omega\) 链的上确界，\(\alpha\) 保持底元，且 \(\alpha T=U\alpha\)。不要求右伴随。

二者都不是必要条件。例如取 \(L=M=\{0<1\}\)，令
\[
T\equiv1,\qquad U\equiv1,\qquad \alpha\equiv1.
\]
则 \(\alpha T=U\alpha\)，且 \(\alpha(\mu T)=1=\mu U\)；但 \(\alpha\) 不保持底元，也没有右伴随。因此，即使两种机制的条件都不满足，精确传递仍可能成立。