## S1　记录的完整载体

定义
\[
z_\lambda(\varphi):=\lambda_{\mathbb R\varphi}(\varphi),
\qquad \varphi\in E'.
\]
兼容性说明，只要 \(\varphi\in F\)，就有
\[
z_\lambda(\varphi)=\lambda_F(\varphi).
\]
因此，对任意 \(\varphi,\psi\in E'\)，在包含它们的有限维空间上使用 \(\lambda_F\) 的线性性，可得 \(z_\lambda\) 线性。统一界又给出
\[
|z_\lambda(\varphi)|\le C\|\varphi\|,
\]
故 \(z_\lambda\in E''\)。

反过来，对任意 \(z\in E''\)，令
\[
\lambda_F=z|_F.
\]
所得记录族线性、兼容，并以 \(\|z\|\) 为统一界。这两个构造互逆；逐分量的线性运算也被保留。此外，
\[
d(\lambda,\mu)
=\sup_{\|\varphi\|\le1}|(z_\lambda-z_\mu)(\varphi)|
=\|z_\lambda-z_\mu\|.
\]
所以合法记录空间与 \(E''\) 线性等距同构。

定义规范映射
\[
J:E\longrightarrow E'',\qquad (Jx)(\varphi)=\varphi(x).
\]
它显然线性，且 \(\|Jx\|\le\|x\|\)。若 \(x\ne0\)，在 \(\mathbb Rx\) 上定义 \(f(tx)=t\|x\|\)，它的范数为 \(1\)。由 Hahn–Banach 定理将其等范数延拓到 \(E\)，得到范数为 \(1\) 且在 \(x\) 处取值 \(\|x\|\) 的泛函。因此
\[
\|Jx\|=\|x\|,
\]
对 \(x=0\) 也成立，故 \(J\) 是线性等距映射。

对有界算子 \(T:E\to E\)，\(T'F\) 有限维，且 \(F\subset G\) 蕴含 \(T'F\subset T'G\)，所以 \(\lambda^T\) 仍是兼容记录；其统一界可取 \(C\|T\|\)。并且
\[
\begin{aligned}
z_{\lambda^T}(\varphi)
&=\lambda_{T'(\mathbb R\varphi)}(T'\varphi)\\
&=z_\lambda(T'\varphi)
=(T''z_\lambda)(\varphi).
\end{aligned}
\]
故记录变换在上述识别下正是 \(T''\)。特别地，
\[
T''J=JT.
\]

## S2　可恢复记录的稳定性

由自反性，\(J:E\to E''\) 是满射；由 S1，它又是单射和等距映射。定义
\[
x_\lambda:=J^{-1}z_\lambda.
\]
于是对每个 \(\varphi\in E'\)，
\[
\varphi(x_\lambda)=z_\lambda(\varphi),
\]
所以 \(x_\lambda\) 实现全部记录，且由 \(J\) 的单射性唯一。还有
\[
\|x_\lambda\|=\|z_\lambda\|\le C,
\qquad
\|x_\lambda-x_\mu\|=d(\lambda,\mu).
\]

由 S1 的 \(T''J=JT\)，
\[
Jx_{\lambda^T}=z_{\lambda^T}
=T''z_\lambda=T''Jx_\lambda=JTx_\lambda.
\]
因此
\[
x_{\lambda^T}=Tx_\lambda.
\]
同理 \(x_{\mu^U}=Ux_\mu\)，于是
\[
\begin{aligned}
\|x_{\lambda^T}-x_{\mu^U}\|
&=\|Tx_\lambda-Ux_\mu\|\\
&\le \|T\|\,\|x_\lambda-x_\mu\|
   +\|T-U\|\,\|x_\mu\|\\
&=\|T\|d(\lambda,\mu)+\|T-U\|\,\|x_\mu\|.
\end{aligned}
\]

## S3　子空间约束

令 \(\pi:E\to E/Y\) 为商映射。由于 \(Y\) 闭，商范数满足
\[
\|\pi x\|=\operatorname{dist}(x,Y).
\]
商空间对偶与 \(Y^\perp\) 等距对应：\(f\in(E/Y)'\) 对应 \(f\circ\pi\in Y^\perp\)；反过来，每个 \(\varphi\in Y^\perp\) 唯一地分解为 \(\varphi=f\circ\pi\)。由商范数的定义，这一对应保持范数。

因此，在赋范空间 \(E/Y\) 上应用 Hahn–Banach 定理得到的对偶范数公式，有
\[
\boxed{\;
\operatorname{dist}(x_\lambda,Y)
=\sup_{\substack{\varphi\in Y^\perp\\ \|\varphi\|\le1}}
|z_\lambda(\varphi)|
=\sup_{\substack{\varphi\in Y^\perp\\ \|\varphi\|\le1}}
|\lambda_{\mathbb R\varphi}(\varphi)|.
\;}
\]
若 \(x_\lambda\in Y\)，右边显然为零。反之，若 \(z_\lambda|_{Y^\perp}=0\)，公式给出 \(\operatorname{dist}(x_\lambda,Y)=0\)；由 \(Y\) 闭，\(x_\lambda\in Y\)。故
\[
x_\lambda\in Y
\quad\Longleftrightarrow\quad
z_\lambda|_{Y^\perp}=0.
\]

## S4　一般 Banach 空间

**结论：不一定。** 对一个固定的 Banach 空间 \(E\)，每份合法记录都能在 \(E\) 中实现，当且仅当 \(E\) 自反。事实上，由 S1，每个 \(z\in E''\) 都对应合法记录；所有记录可实现恰好意味着 \(J(E)=E''\)，即自反性。

反例取实 Banach 空间 \(E=c_0\)。其对偶等距识别为 \(\ell^1\)，配对为
\[
\varphi_a(x)=\sum_{n=1}^\infty a_nx_n.
\]
这里的标准识别也可直接验证：对 \(f\in c_0'\)，令 \(a_n=f(e_n)\)，用有限支撑的符号向量可得
\(\sum_{n\le N}|a_n|\le\|f\|\)；再用 \(c_0\) 中的截断逼近，即得 \(a\in\ell^1\)、\(f=\varphi_a\)，且范数相等。

在 \(\ell^1=E'\) 上定义
\[
z(a)=\sum_{n=1}^\infty a_n.
\]
它属于 \(E''\)，且 \(\|z\|=1\)。令各 \(\lambda_F=z|_F\)，就得到统一界 \(C=1\) 的合法记录。若它由 \(x\in c_0\) 实现，对每个坐标泛函 \(e_n^*\) 都有
\[
x_n=e_n^*(x)=z(e_n^*)=1,
\]
这与 \(x\in c_0\) 矛盾。

不过，在任意 Banach 空间中，**已经可实现**的记录仍有唯一实现点：\(J\) 单射保证唯一性，且 \(\|x_\lambda\|=\|z_\lambda\|\le C\)。对于两份可实现记录，
\(\|x_\lambda-x_\mu\|=d(\lambda,\mu)\)；S1 的 \(T''J=JT\) 也保证其恢复与所有有界 \(T\) 相容。

## S5　单条记录的拓扑条件

**结论：必可实现；而且可实现性等价于 \(z_\lambda\) 的弱星连续性。**

先设 \(z_\lambda\) 关于 \(\sigma(E',E)\) 连续。由零点处连续及弱星拓扑的基本邻域形式，存在 \(x_1,\ldots,x_m\in E\) 和 \(\delta>0\)，使得
\[
|\varphi(x_j)|<\delta\quad(1\le j\le m)
\quad\Longrightarrow\quad
|z_\lambda(\varphi)|<1.
\]
若 \(\varphi(x_j)=0\) 对所有 \(j\) 成立，则对每个实数 \(t\)，\(t\varphi\) 都满足左边条件。因此
\[
|t\,z_\lambda(\varphi)|<1\quad(t\in\mathbb R),
\]
从而 \(z_\lambda(\varphi)=0\)。

令
\[
A:E'\to\mathbb R^m,\qquad
A\varphi=(\varphi(x_1),\ldots,\varphi(x_m)).
\]
上面的结论使
\[
h(A\varphi):=z_\lambda(\varphi)
\]
在子空间 \(A(E')\) 上良定义且线性。将 \(h\) 线性延拓到有限维空间 \(\mathbb R^m\)，可写为
\(h(y_1,\ldots,y_m)=\sum_{j=1}^m a_jy_j\)。令
\[
x=\sum_{j=1}^m a_jx_j,
\]
便有
\[
z_\lambda(\varphi)=\sum_{j=1}^m a_j\varphi(x_j)=\varphi(x)
\quad(\varphi\in E').
\]
故 \(z_\lambda=Jx\)，即记录由 \(x\) 实现。

反之，若 \(z_\lambda=Jx\)，则 \(z_\lambda\) 正是评价映射 \(\varphi\mapsto\varphi(x)\)，按 \(\sigma(E',E)\) 的定义连续。实现点由 \(J\) 的单射性唯一，并满足
\[
\|x\|=\|z_\lambda\|\le C.
\]

## S6　有限观测的精确匹配

先证明 \(q_F:E\to F^*\) 满射。否则，有限维空间 \(F^*\) 的真子空间 \(q_F(E)\) 有非零湮灭泛函。利用有限维识别 \(F^{**}=F\)，这意味着存在非零 \(\varphi\in F\)，使得
\[
\varphi(x)=(q_Fx)(\varphi)=0\quad(x\in E),
\]
与 \(\varphi\ne0\) 矛盾。

对 \(\xi\in F^*\) 定义
\[
p(\xi):=\inf\{\|x\|:q_Fx=\xi\}.
\]
由于 \(q_F\) 满射，\(p\) 处处有限。它是范数：绝对齐次性及三角不等式由下确界定义得到；而对 \(q_Fx=\xi\)，
\[
|\xi(\varphi)|=|\varphi(x)|
\le\|\varphi\|\,\|x\|,
\]
取下确界及上确界得 \(\|\xi\|_{F^*}\le p(\xi)\)，故 \(p\) 非退化。

对 \(\varphi\in F\)，令 \(L_\varphi(\xi)=\xi(\varphi)\)。上式给出
\(\|L_\varphi\|_{p,*}\le\|\varphi\|\)。反过来，由 \(p(q_Fx)\le\|x\|\)，
\[
|\varphi(x)|=|L_\varphi(q_Fx)|
\le\|L_\varphi\|_{p,*}\|x\|,
\]
故 \(\|\varphi\|\le\|L_\varphi\|_{p,*}\)。于是
\[
\|L_\varphi\|_{p,*}=\|\varphi\|.
\]
因为 \(F\) 有限维，\((F^*)^*\) 中每个泛函都是某个 \(L_\varphi\)。对赋范空间 \((F^*,p)\) 应用对偶范数公式，得到
\[
p(\xi)
=\sup_{\substack{\varphi\in F\\\|\varphi\|\le1}}|\xi(\varphi)|
=\|\xi\|_{F^*}.
\]
特别地，
\[
\inf_{q_Fx=\lambda_F}\|x\|
=p(\lambda_F)=\|\lambda_F\|_{F^*}\le C.
\]
因此对每个 \(\varepsilon>0\)，按下确界定义可选取 \(x_{F,\varepsilon}\in E\)，使
\[
q_Fx_{F,\varepsilon}=\lambda_F,
\qquad
\|x_{F,\varepsilon}\|<C+\varepsilon.
\]

**一般不能取 \(\varepsilon=0\)。** 沿用 S4 的 \(E=c_0\)、\(z(a)=\sum a_n\) 和 \(C=1\)。令
\[
\varphi_0=(2^{-n})_{n\ge1}\in\ell^1=E',
\qquad F=\mathbb R\varphi_0.
\]
此时 \(\|\varphi_0\|=1\)，且 \(\lambda_F(\varphi_0)=1\)。若 \(q_Fx=\lambda_F\) 且 \(\|x\|_\infty\le1\)，则
\[
0=1-\sum_{n=1}^\infty2^{-n}x_n
=\sum_{n=1}^\infty2^{-n}(1-x_n).
\]
各项非负，故每个 \(x_n=1\)，这不可能属于 \(c_0\)。另一方面，取
\[
x_n^{(N)}=
\begin{cases}
(1-2^{-N})^{-1},&n\le N,\\
0,&n>N,
\end{cases}
\]
则 \(q_Fx^{(N)}=\lambda_F\)，而
\(\|x^{(N)}\|_\infty=(1-2^{-N})^{-1}\to1\)。这也直接显示了下确界可以不取到。

最后，有限匹配不能替代 S5 的弱星连续性：S4 的反例依上述证明对**每个**有限维 \(F\) 和每个 \(\varepsilon>0\) 都有有限匹配点，但没有统一实现点。事实上，坐标泛函 \(e_n^*\) 在 \(\sigma(\ell^1,c_0)\) 下趋于零，因为对每个 \(x\in c_0\)，\(e_n^*(x)=x_n\to0\)；然而 \(z(e_n^*)=1\)。所以该 \(z\) 不弱星连续。有限匹配点可以随 \(F,\varepsilon\) 改变，因而不必拼合成同一个原空间点。