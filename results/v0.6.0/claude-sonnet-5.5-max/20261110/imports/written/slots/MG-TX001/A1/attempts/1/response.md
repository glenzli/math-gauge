这个结论成立。下面是完整证明；我还把它整个在 Lean 4/Mathlib 里形式化并通过了检查。

**记号。** 设 $N=p^r$，$M=N/p=p^{r-1}$，$\zeta=e^{2\pi i/N}$。$N$ 次单位根就是 $\zeta^k$，$k\in\mathbb Z/N$。

## 第 0 步：化为行列式

假设 $P$ 在三个不同的 $N$ 次单位根 $z_j=\zeta^{k_j}$ ($j=1,2,3$) 处为零。这里 $k_1,k_2,k_3\in\mathbb Z/N$ 两两不同。

令 $A=(z_j^{a_i})_{i,j}$。条件即 $c^{T}A=0$，而 $c\neq 0$，所以 $\det A=0$。下面证明 $\det A\ne 0$，由此得到矛盾。

展开得
$$\det A=\sum_{\sigma\in S_3}\operatorname{sgn}(\sigma)\,\zeta^{e(\sigma)},\qquad e(\sigma)=\sum_{i=1}^3 a_i k_{\sigma(i)}\in\mathbb Z/N .$$
记 $E^+=\{e(\sigma):\sigma\text{ 偶}\}$，$E^-=\{e(\sigma):\sigma\text{ 奇}\}$，各含 3 个指数。

## 第 1 步（关键）：$E^+\cap E^-=\emptyset$

设 $\sigma$ 为偶置换，$\sigma'$ 为奇置换。$\sigma^{-1}\sigma'$ 是奇置换，所以是一个对换 $(i\ i')$，即 $\sigma'=\sigma\circ(i\ i')$。直接计算得
$$e(\sigma)-e(\sigma')=(k_{\sigma(i)}-k_{\sigma(i')})(a_i-a_{i'}).$$
因为 $a_i\not\equiv a_{i'}\pmod p$，所以 $a_i-a_{i'}$ 与 $p^r$ 互素，在 $\mathbb Z/N$ 中可逆。又 $k_{\sigma(i)}\neq k_{\sigma(i')}$。于是差不为 $0$。

这一步用到了"模 $p$ 两两不同"这个条件。

## 第 2 步：引理（$p$ 的幂次单位根的消失和）

**引理。** 设 $\alpha:\mathbb Z/N\to\mathbb Z$ 满足 $\sum_m\alpha(m)\zeta^m=0$，则对所有 $m$ 有 $\alpha(m+M)=\alpha(m)$。

*证明。* 取 $f(x)=\sum_{m=0}^{N-1}\alpha(m)x^m$，则 $f(\zeta)=0$。

多项式 $\Phi(x)=\sum_{j=0}^{p-1}x^{jM}=\frac{x^N-1}{x^M-1}$ 在 $\mathbb Q$ 上不可约。这是标准结论，对 $\Phi(x+1)$ 用 Eisenstein 判别法即可。因此 $\Phi$ 是 $\zeta$ 的极小多项式，$f=\Phi g$，且 $\deg g\le (N-1)-(N-M)=M-1$。

于是 $(x^M-1)f=g\,(x^N-1)=gx^N-g$。比较 $x^m$（$M\le m<N$）的系数：

- 左边是 $\alpha(m-M)-\alpha(m)$。
- 右边为 $0$，因为 $m<N$，且 $m\ge M>\deg g$。

所以 $\alpha(m)=\alpha(m-M)$ 对 $M\le m<N$ 成立。这给出 $\alpha(t)=\alpha(t+M)=\dots=\alpha(t+(p-1)M)$，绕回一圈也成立。$\square$

## 第 3 步：收尾

令 $\alpha(m)=\#\{\sigma\text{ 偶}:e(\sigma)=m\}-\#\{\sigma\text{ 奇}:e(\sigma)=m\}$。则 $\det A=\sum_m\alpha(m)\zeta^m=0$，由引理，$\alpha$ 在平移 $m\mapsto m+M$ 下不变。

由第 1 步，$\alpha>0$ 恰在 $E^+$ 上，$\alpha<0$ 恰在 $E^-$ 上。所以 $E^+$ 与 $E^-$ 都在 $m\mapsto m+M$ 下封闭。

任取 $m_0\in E^+$，则 $m_0,\,m_0+M,\dots,m_0+(p-1)M$ 是 $E^+$ 中 $p$ 个不同的元素。但 $|E^+|\le 3$，所以 $p\le3$。

- **$p\ge5$：** 已经矛盾。
- **$p=3$：** 此时 $N=3M$，$E^+=\{x,x+M,x+2M\}$ 恰是三个不同元素，且三个偶置换给出的指数两两不同。同理 $E^-=\{y,y+M,y+2M\}$。

对 $p=3$ 再作如下推导：

1. 对固定的 $i$，当 $\sigma$ 取遍三个偶置换时，$\sigma(i)$ 取遍 $\{1,2,3\}$ 各一次。三个奇置换（三个对换）同样如此。
2. 因此 $\sum_{\sigma\text{ 偶}}e(\sigma)=\sum_{\sigma\text{ 奇}}e(\sigma)=(\sum_i a_i)(\sum_j k_j)$。
3. 另一方面，前一个和等于 $3x+3M=3x$，因为 $3M=N=0$。同理后一个和等于 $3y$。
4. 所以 $3(x-y)=0$ 在 $\mathbb Z/3M$ 中成立，于是 $M\mid x-y$，即 $x\in\{y,y+M,y+2M\}=E^-$。

这与 $E^+\cap E^-=\emptyset$ 矛盾。

因此 $\det A\neq0$，不可能有三个不同的 $N$ 次单位根都是 $P$ 的零点，即至多两个。$\blacksquare$

## 补充说明

- **$r\ge2$ 用不到。** 证明对 $r\ge1$ 都成立（$r=1$ 就是三项情形的 Chebotarev 型结论）。
- **"模 $p$ 两两不同"不能去掉。** 例如 $N=9$，$a=(0,3,6)$，$c=(1,1,1)$，这时 $1+z^3+z^6$ 在 9 次单位根中有 6 个零点。
- **数值检验。** 对 $N=9,25,27,49,81,125$ 以及 $r=1$ 的 $p=3,5,7,11$，我穷举了所有满足条件的 $(a_i)$ 与三个不同的单位根。精确判据下没有一个行列式为零，浮点行列式（最大到 $N=49$）也都远离零。
- **形式化验证。** 文件 `ThreeTermRoots.lean` 在工作区根目录。其中的 `ThreeTerm.main_theorem` 是原命题：`{z : ℂ | z^(p^r)=1 ∧ ∑ i, c i * z^(a i)=0}.encard ≤ 2`。它在本地 Lean/Mathlib 下编译通过，没有 `sorry`，只依赖标准公理 `propext`、`Classical.choice`、`Quot.sound`。
- **检验脚本。** `work/verify_bruteforce.py` 与 `work/verify_numeric.py` 是上面两项检验的脚本。