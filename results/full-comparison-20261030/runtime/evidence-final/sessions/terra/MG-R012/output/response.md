对每个整数 \(n\ge 0\)，取有限记录链
\[
(x_0,y_0)=(\bar x,\bar y),\qquad
(x_1,y_1),\ldots,(x_n,y_n)\in\Gamma,
\]
并定义相应的连续仿射函数
\[
A_{(x_j,y_j)_{j=0}^n}(z)
=
\sum_{j=0}^{n-1}y_j(x_{j+1}-x_j)+y_n(z-x_n).
\]
当 \(n=0\) 时，空和取 \(0\)，所以相应的函数是
\(z\mapsto\bar y(z-\bar x)\)。令
\[
\boxed{\displaystyle
f(z)=\sup_{\substack{n\ge 0,\ (x_0,y_0)=(\bar x,\bar y)\\
(x_1,y_1),\ldots,(x_n,y_n)\in\Gamma}}
\left[
\sum_{j=0}^{n-1}y_j(x_{j+1}-x_j)+y_n(z-x_n)
\right].}
\]

首先验证归一化和正规性。对任意上述记录链，循环单调性给出
\[
\sum_{j=0}^{n-1}y_j(x_{j+1}-x_j)
+y_n(\bar x-x_n)\le 0.
\]
因此每个参与上确界的仿射函数在 \(\bar x\) 处都不超过 \(0\)。而 \(n=0\) 的函数在那里恰好等于 \(0\)，故
\[
f(\bar x)=0.
\]
又因为 \(n=0\) 的项对每个 \(z\) 都是有限值，
\[
f(z)\ge \bar y(z-\bar x)>-\infty.
\]
所以 \(f\) 的取值属于 \(\mathbb R\cup\{+\infty\}\)，且它在 \(\bar x\) 处有限，因而正规。

每个参与上确界的函数都是连续仿射函数。因此，它们的逐点上确界 \(f\) 是凸函数；并且对每个 \(a\in\mathbb R\)，
\[
\{z:f(z)>a\}
=
\bigcup_{\text{上述记录链}}\{z:A_{(x_j,y_j)_{j=0}^n}(z)>a\}
\]
是开集，故 \(f\) 下半连续。

接着证明所有记录都是次梯度。固定 \((x,y)\in\Gamma\)。将它接在任意记录链之后，再以 \((\bar x,\bar y)\) 闭合，循环单调性蕴含
\[
\sum_{j=0}^{n-1}y_j(x_{j+1}-x_j)
+y_n(x-x_n)+y(\bar x-x)\le 0.
\]
取上确界得到
\[
f(x)\le y(x-\bar x)<+\infty.
\]
另一方面，把 \((x,y)\) 接在任意记录链之后，构造式对每个 \(z\in E\) 给出
\[
f(z)\ge
\sum_{j=0}^{n-1}y_j(x_{j+1}-x_j)
+y_n(x-x_n)+y(z-x).
\]
对原记录链取上确界，便有
\[
f(z)\ge f(x)+y(z-x)\qquad(z\in E).
\]
结合 \(f(x)<+\infty\)，可知 \(y\in\partial f(x)\)。

最后证明最小性。设 \(g:E\to\mathbb R\cup\{+\infty\}\) 满足 \(g(\bar x)=0\)，且对每个 \((x,y)\in\Gamma\) 都有 \(y\in\partial g(x)\)。对任意上述记录链，依次应用次梯度不等式并求和，得到
\[
\begin{aligned}
g(z)
&\ge g(\bar x)
+\sum_{j=0}^{n-1}y_j(x_{j+1}-x_j)+y_n(z-x_n)\\
&=\sum_{j=0}^{n-1}y_j(x_{j+1}-x_j)+y_n(z-x_n).
\end{aligned}
\]
对所有记录链取上确界，即 \(g(z)\ge f(z)\)。这对每个 \(z\in E\) 成立，所以 \(f\) 是所要求函数中的逐点最小者。这个最小性论证甚至不需要额外假设 \(g\) 凸或下半连续。

若另有函数 \(\tilde f\) 也是满足题设条件的逐点最小者，则由各自的最小性，\(f\le\tilde f\) 且 \(\tilde f\le f\)。因此 \(\tilde f=f\)，逐点最小函数唯一。