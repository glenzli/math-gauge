# 完整最终稿

记
\[
\mu_N=\{z\in\mathbb C:z^N=1\},\qquad N=p^r.
\]
本文完整证明题目，并给出同一机制下的自然 \(k\) 项推广及其锐性例。

## 1. 主要结论

**定理.** 设 \(p\ge3\) 为素数，\(N=p^r\)。令 \(2\le k\le p\)，并取
\[
0\le a_1<a_2<\cdots<a_k<N,
\]
其中 \(a_1,\ldots,a_k\) 模 \(p\) 两两不同。若复数向量
\((c_1,\ldots,c_k)\) 非零，则
\[
P(z)=\sum_{j=1}^k c_jz^{a_j}
\]
在 \(\mu_N\) 中至多有 \(k-1\) 个不同的零点。

取 \(k=3\) 即得原题。系数即使有零项也无需排除，只要整个系数向量非零。

## 2. 单位根在唯一 \(p\)-素理想下的同余

令 \(K=\mathbb Q(\zeta_N)\)，其中 \(\zeta_N\) 是本原 \(N\) 次单位根。
对于奇素数 \(p\)，\(p\) 在 \(K\) 中完全分歧：存在唯一的素理想
\(\mathfrak P\mid p\)，并且
\[
\mathcal O_K/\mathfrak P\cong\mathbb F_p.
\]

若 \(\xi\in\mu_N\)，记它在剩余域中的像为 \(\overline\xi\)。则
\(\overline\xi^N=1\)。但 \(\mathbb F_p^\times\) 的阶为 \(p-1\)，且
\[
\gcd(N,p-1)=\gcd(p^r,p-1)=1,
\]
所以剩余域中没有非平凡的 \(N\) 次单位根。故
\[
\xi\equiv1\pmod{\mathfrak P}
\qquad\text{对所有 }\xi\in\mu_N.\tag{1}
\]

## 3. Vandermonde–Schur 非零性

**引理.** 设 \(\xi_1,\ldots,\xi_k\in\mu_N\) 两两不同，\(2\le k\le p\)，
且 \(a_1,\ldots,a_k\) 模 \(p\) 两两不同。则
\[
D=\det\bigl(\xi_i^{a_j}\bigr)_{1\le i,j\le k}
\]
不为零。

**证明.** 令
\[
\lambda=\bigl(a_k-(k-1),a_{k-1}-(k-2),\ldots,a_1\bigr).
\]
因为 \(a_1<\cdots<a_k\)，所以 \(\lambda\) 是一个分拆。由标准
Vandermonde–Schur 恒等式，
\[
D=\pm\left(\prod_{1\le i<j\le k}(\xi_j-\xi_i)\right)
 s_\lambda(\xi_1,\ldots,\xi_k),\tag{2}
\]
其中 \(s_\lambda\) 是 Schur 多项式。（这里用了完整 Vandermonde 的指数
\(0,1,\ldots,k-1\)，因而确实得到它的标准前置因子。）

由 (1)，把 \(s_\lambda\) 的整数系数和各项一起约化到
\(\mathcal O_K/\mathfrak P\cong\mathbb F_p\)，可得
\[
s_\lambda(\xi_1,\ldots,\xi_k)
\equiv s_\lambda(1,\ldots,1)\pmod{\mathfrak P}.\tag{3}
\]
由 Weisenböck 公式，
\[
s_\lambda(1,\ldots,1)
=\prod_{1\le i<j\le k}
\frac{\lambda_i-\lambda_j+j-i}{j-i}.\tag{4}
\]
而
\[
\lambda_i-\lambda_j+j-i=a_{k-i+1}-a_{k-j+1}.\tag{5}
\]
题设保证 (5) 的每个分子在模 \(p\) 下非零；同时
\(1\le j-i\le k-1<p\)，所以每个分母在模 \(p\) 下也非零。因此
\[
s_\lambda(1,\ldots,1)\not\equiv0\pmod p.\tag{6}
\]
这里 (4) 是整数值公式；将 (6) 的同一约化用于 (3) 即可。于是由 (3)，
\(s_\lambda(\xi_1,\ldots,\xi_k)\ne0\)。

由于 \(\xi_1,\ldots,\xi_k\) 两两不同，(2) 中的前置积也不为零。于是
由 (2) 得 \(D\ne0\)。引理得证。

## 4. 证明原题和一般版本

反设 \(P\) 在 \(\mu_N\) 中至少有 \(k\) 个不同零点
\(\xi_1,\ldots,\xi_k\)。代入 \(k\) 个式子得
\[
\sum_{j=1}^k c_j\xi_i^{a_j}=0\qquad(1\le i\le k).
\]
于是
\[
\bigl(\xi_i^{a_j}\bigr)_{1\le i,j\le k}
\begin{pmatrix}c_1\\ \vdots\\ c_k\end{pmatrix}=0.
\]
非零系数向量在矩阵的核中，故矩阵奇异，其行列式 \(D=0\)。这与引理
\(D\ne0\) 矛盾。因此 \(P\) 在 \(\mu_N\) 中至多有 \(k-1\) 个不同零点。

特别地，取 \(k=3\)，得到原题所要求的结论。

## 5. 界的锐性

在 \(k=p\) 时，取
\[
P_0(z)=1+z+\cdots+z^{p-1}.
\]
指数 \(0,1,\ldots,p-1\) 模 \(p\) 两两不同。若
\(z^p=1\) 且 \(z\ne1\)，则
\[
(z-1)P_0(z)=z^p-1=0,
\]
所以 \(P_0(z)=0\)。这表明 \(P_0\) 在 \(\mu_N\) 中恰有 \(p-1\) 个不同
零点，恰好达到一般界。原题的三项情形在 \(p=3\) 时也取到两个零点，例如
\(1+z+z^2\) 在两个非平凡三次单位根处为零。

## 6. 保留、修正、新增与自评

- **保留：** 从三个零点导出指数矩阵奇异，再利用指数模 \(p\) 的差异
  排除奇异，这一总体路线正确，原题核心结论已完整成立。
- **修正：** 历史稿件在“\(x,y\) 同阶”情形错误地使用了“\(x/y\) 仍有同样的
  \(p\)-幂阶”。该命题不成立。本稿不依赖它：三项情形可统一用
  \((G_t(x)-G_t(y))/(x-y)\) 的剩余域约化来判别，其中
  \(G_t=1+z+\cdots+z^{t-1}\)；一般 \(k\) 项则用 Vandermonde–Schur 分解。
- **新增：** 完整证明自然参数族 \(2\le k\le p\) 上的“\(k\) 项至多
  \(k-1\) 个零点”定理，并证明端点 \(k=p\) 的界可以达到。
- **仍未完成或不确定：** 原题没有未完成部分。一般定理限制在 \(k\le p\)，
  因为模 \(p\) 两两不同这一条件本身至多允许 \(p\) 个指数；本文不对违反
  该条件的多项式另作断言。
- **自评：** 原题完整证明为 \(B2\)。一般 \(k\) 项定理加锐性检查是在自然
  参数族上的完整扩展；按给定尺度，我保守地自评为
  \(R2\)，不声称 \(R3\)。未发现剩余错误断言或无根据的验证承诺，故没有
  另外的可靠性扣罚。由于 \(SMC\) 要求 \(B2\) 且 \(R3\)，本文不声称达到
  \(SMC\)。
