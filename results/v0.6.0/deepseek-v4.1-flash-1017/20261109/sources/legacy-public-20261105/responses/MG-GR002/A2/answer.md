以下逐 S 作答。始终记
\[
\mathbb R\varphi=\operatorname{span}\{\varphi\}\qquad(\varphi\in E').
\]

## S1　记录的完整载体

### 1. 从记录到 \(E''\)

对兼容有界记录 \(\lambda=(\lambda_F)_F\)，定义
\[
\widehat\lambda(\varphi):=\lambda_{\mathbb R\varphi}(\varphi),
\qquad \varphi\in E'.
\]
先证 \(\widehat\lambda\) 线性。若 \(\varphi,\psi\in E'\)，令 \(F=\operatorname{span}\{\varphi,\psi\}\)。由兼容性及 \(\lambda_F\) 的线性，
\[
\begin{aligned}
\widehat\lambda(\varphi+\psi)
&=\lambda_{\mathbb R(\varphi+\psi)}(\varphi+\psi)
=\lambda_F(\varphi+\psi)\\
&=\lambda_F(\varphi)+\lambda_F(\psi)
=\lambda_{\mathbb R\varphi}(\varphi)+\lambda_{\mathbb R\psi}(\psi)\\
&=\widehat\lambda(\varphi)+\widehat\lambda(\psi).
\end{aligned}
\]
齐次性同理：\(a\neq0\) 时
\[
\widehat\lambda(a\varphi)=\lambda_{\mathbb R(a\varphi)}(a\varphi)
=\lambda_{\mathbb R\varphi}(a\varphi)
=a\widehat\lambda(\varphi),
\]
\(a=0\) 时两边均为 \(0\)。并且
\[
|\widehat\lambda(\varphi)|
=|\lambda_{\mathbb R\varphi}(\varphi)|
\le C\|\varphi\|.
\]
故 \(\widehat\lambda\in E''\)，且
\[
\|\widehat\lambda\|_{E''}
=\sup_{\|\varphi\|\le1}|\widehat\lambda(\varphi)|
\le C. \tag{1.1}
\]

### 2. 从 \(E''\) 到记录

反之，给定 \(z\in E''\)，定义
\[
\lambda^z_F(\varphi):=z(\varphi),\qquad \varphi\in F.
\]
显然 \(\lambda^z_G|_F=\lambda^z_F\)，且
\[
|\lambda^z_F(\varphi)|\le \|z\|\,\|\varphi\|.
\]
同时
\[
\widehat{\lambda^z}(\varphi)
=\lambda^z_{\mathbb R\varphi}(\varphi)
=z(\varphi),
\]
故
\[
\widehat{\lambda^z}=z. \tag{1.2}
\]
反过来，若从 \(\lambda\) 出发，则对任意有限维 \(F\) 和 \(\varphi\in F\)，由兼容性
\[
\widehat\lambda(\varphi)
=\lambda_{\mathbb R\varphi}(\varphi)
=\lambda_F(\varphi).
\]
因此
\[
\lambda^{\widehat\lambda}_F=\widehat\lambda|_F=\lambda_F,
\]
即
\[
\lambda^{\widehat\lambda}=\lambda. \tag{1.3}
\]
于是 \(\lambda\mapsto\widehat\lambda\) 是兼容有界记录与 \(E''\) 之间的双射。

进一步，
\[
\begin{aligned}
d(\lambda,\mu)
&=\sup_{\|\varphi\|\le1}
|\lambda_{\mathbb R\varphi}(\varphi)-\mu_{\mathbb R\varphi}(\varphi)|\\
&=\sup_{\|\varphi\|\le1}
|\widehat\lambda(\varphi)-\widehat\mu(\varphi)|
=\|\widehat\lambda-\widehat\mu\|_{E''}. \tag{1.4}
\end{aligned}
\]
特别地，满足统一界 \(C\) 的记录恰好对应闭球
\[
\{z\in E'':\|z\|\le C\}.
\tag{1.5}
\]

### 3. 规范嵌入 \(J:E\to E''\)

定义
\[
(Jx)(\varphi):=\varphi(x),\qquad x\in E,\ \varphi\in E'.
\]
线性显然。并且
\[
|(Jx)(\varphi)|=|\varphi(x)|
\le \|x\|\,\|\varphi\|,
\]
故 \(\|Jx\|\le\|x\|\)。若 \(x\neq0\)，由 Hahn–Banach 定理（实 Banach 空间；\(x\neq0\)）存在 \(\varphi\in E'\)，\(\|\varphi\|=1\)，且
\[
\varphi(x)=\|x\|.
\]
于是 \(\|Jx\|\ge\|x\|\)。所以
\[
\|Jx\|_{E''}=\|x\|_E, \tag{1.6}
\]
即 \(J\) 是线性等距嵌入。

### 4. 记录变换就是 \(T''\)

对有界线性算子 \(T:E\to E\)，令 \(T'\varphi=\varphi\circ T\)。按定义
\[
\lambda^T_F(\varphi)=\lambda_{T'F}(T'\varphi).
\]
于是对 \(\varphi\in E'\)，
\[
\begin{aligned}
\widehat{\lambda^T}(\varphi)
&=\lambda^T_{\mathbb R\varphi}(\varphi)
=\lambda_{T'(\mathbb R\varphi)}(T'\varphi)\\
&=\lambda_{\mathbb R(T'\varphi)}(T'\varphi)
=\widehat\lambda(T'\varphi)
=(T''\widehat\lambda)(\varphi).
\end{aligned}
\]
因此
\[
\widehat{\lambda^T}=T''\widehat\lambda. \tag{1.7}
\]
另外
\[
(T''Jx)(\varphi)
=(Jx)(T'\varphi)
=(T'\varphi)(x)
=\varphi(Tx)
=(JTx)(\varphi),
\]
故
\[
T''J=JT. \tag{1.8}
\]
所以在 S1 的识别下，\(\lambda\mapsto\lambda^T\) 恰为 \(T''\)。

---

## S2　可恢复记录的稳定性

设 \(E\) 自反，即
\[
J(E)=E''.
\]
对任意合法记录 \(\lambda\)，由 S1 得 \(\widehat\lambda\in E''\)。定义
\[
x_\lambda:=J^{-1}\widehat\lambda\in E. \tag{2.1}
\]
由于 \(J\) 是等距双射，\(x_\lambda\) 唯一，并且
\[
\|x_\lambda\|=\|\widehat\lambda\|\le C. \tag{2.2}
\]
对任意有限维 \(F\) 及 \(\varphi\in F\)，
\[
\lambda_F(\varphi)=\widehat\lambda(\varphi)
=(Jx_\lambda)(\varphi)
=\varphi(x_\lambda),
\]
所以 \(x_\lambda\) 实现全部记录。

若 \(y\in E\) 也实现全部记录，则对一切 \(\varphi\in E'\)，
\[
(Jy)(\varphi)=\varphi(y)
=\lambda_{\mathbb R\varphi}(\varphi)
=\widehat\lambda(\varphi),
\]
故 \(Jy=\widehat\lambda\)，从而 \(y=x_\lambda\)。唯一性得证。

### 与所有 \(T\) 相容

由 (1.7) 和 (1.8)，
\[
\widehat{\lambda^T}
=T''\widehat\lambda
=T''Jx_\lambda
=J(Tx_\lambda).
\]
由于 \(J\) 单射，
\[
x_{\lambda^T}=Tx_\lambda. \tag{2.3}
\]

### 稳定性不等式

对两份记录 \(\lambda,\mu\)，由 (1.4) 和 \(J\) 等距，
\[
\|x_\lambda-x_\mu\|
=\|\widehat\lambda-\widehat\mu\|
=d(\lambda,\mu). \tag{2.4}
\]
于是对 bounded \(T,U\)，
\[
\begin{aligned}
\|x_{\lambda^T}-x_{\mu^U}\|
&=\|Tx_\lambda-Ux_\mu\|\\
&\le \|T(x_\lambda-x_\mu)\|+\|(T-U)x_\mu\|\\
&\le \|T\|\,\|x_\lambda-x_\mu\|+\|T-U\|\,\|x_\mu\|\\
&=\|T\|\,d(\lambda,\mu)+\|T-U\|\,\|x_\mu\|.
\end{aligned}
\]
这就是所要求的不等式。

---

## S3　子空间约束

令
\[
Y^\perp=\{\varphi\in E':\varphi|_Y=0\}.
\]
记 \(z_\lambda:=\widehat\lambda=Jx_\lambda\)。

### 1. 等价条件

若 \(x_\lambda\in Y\)，则对一切 \(\varphi\in Y^\perp\)，
\[
z_\lambda(\varphi)=\varphi(x_\lambda)=0.
\]
反之，若 \(z_\lambda|_{Y^\perp}=0\)，则对一切 \(\varphi\in Y^\perp\)，
\[
\varphi(x_\lambda)=0.
\]
由于 \(Y\) 闭，Hahn–Banach 分离定理给出
\[
x_\lambda\in Y
\quad\Longleftrightarrow\quad
\varphi(x_\lambda)=0\ \ \forall\varphi\in Y^\perp.
\]
因此
\[
\boxed{x_\lambda\in Y
\iff z_\lambda|_{Y^\perp}=0
\iff \lambda_{\mathbb R\varphi}(\varphi)=0
\quad\forall\varphi\in Y^\perp.} \tag{3.1}
\]

### 2. 距离的准确对偶公式

对任意 \(x\in E\)，标准 Hahn–Banach 距离公式给出
\[
\operatorname{dist}(x,Y)
=\sup_{\substack{\varphi\in Y^\perp\\\|\varphi\|\le1}}|\varphi(x)|.
\tag{3.2}
\]
取 \(x=x_\lambda\)。因为
\[
\varphi(x_\lambda)=z_\lambda(\varphi)
=\lambda_{\mathbb R\varphi}(\varphi),
\]
得到
\[
\boxed{
\operatorname{dist}(x_\lambda,Y)
=\sup_{\substack{\varphi\in Y^\perp\\\|\varphi\|\le1}}
|\lambda_{\mathbb R\varphi}(\varphi)|
=\|z_\lambda|_{Y^\perp}\|_{(Y^\perp)^*}.} \tag{3.3}
\]
也可以写成
\[
\operatorname{dist}(x_\lambda,Y)
=
\sup_{\substack{F\subset Y^\perp\\ \dim F<\infty}}
\|\lambda_F\|_{F^*}. \tag{3.4}
\]
在自反情形，\(z_\lambda\in J(E)\) 是弱星连续的，而 \(B_{Y^\perp}\) 弱星紧，因此 (3.3) 中的上确界实际上可取到。

---

## S4　一般 Banach 空间

**结论：否。** 在一般 Banach 空间中，并非每份合法记录都能由某个 \(x_\lambda\in E\) 实现；因此更谈不上唯一性、稳定性及与所有 \(T\) 相容。

### 反例

取
\[
E=c_0,\qquad E'=\ell^1,\qquad E''=\ell^\infty.
\]
标准嵌入 \(J:c_0\to\ell^\infty\) 就是恒等包含，所以 \(J(c_0)=c_0\subsetneq \ell^\infty\)。

令
\[
z=(1,1,1,\dots)\in\ell^\infty,
\qquad \|z\|=1.
\]
对每个有限维 \(F\subset\ell^1\)，定义
\[
\lambda_F(\varphi):=z(\varphi)=\sum_{n=1}^\infty \varphi_n,
\qquad \varphi=(\varphi_n)\in F.
\]
由于
\[
|\lambda_F(\varphi)|
\le \sum_{n=1}^\infty|\varphi_n|
=\|\varphi\|_{\ell^1},
\]
该记录合法，统一界可取 \(C=1\)，且显然兼容。

若存在 \(x=(x_n)\in c_0\) 实现全部记录，则对每个标准基向量 \(e_n\in\ell^1\)，
\[
x_n=e_n(x)
=\lambda_{\mathbb R e_n}(e_n)
=z(e_n)=1.
\]
于是 \(x=(1,1,\dots)\)，但该序列不属于 \(c_0\)，矛盾。故不存在实现该记录的 \(x_\lambda\in c_0\)。

因此 S4 中所列性质不能对一般 Banach 空间成立。

需要说明的是：若某份记录对应的 \(z_\lambda\) 满足 \(z_\lambda\in J(E)\)，则令 \(x_\lambda=J^{-1}z_\lambda\)，S2 中的唯一性、范数估计、实现记录、\(x_{\lambda^T}=Tx_\lambda\) 及稳定性不等式仍然全部成立。一般空间中的唯一障碍正是
\[
J(E)\neq E''.
\]

---

## S5　单条记录的拓扑条件

**结论：必可实现。** 更精确地，
\[
\boxed{
z_\lambda \text{ 关于 }\sigma(E',E)\text{ 连续}
\iff z_\lambda\in J(E)
\iff \lambda \text{ 可由某个 }x\in E\text{ 实现}.} \tag{5.1}
\]

### 证明

假设 \(z_\lambda:E'\to\mathbb R\) 关于 \(\sigma(E',E)\) 连续。由弱星拓扑的定义，存在 \(x_1,\dots,x_m\in E\) 和 \(\delta>0\)，使得
\[
\max_{1\le j\le m}|\varphi(x_j)|<\delta
\quad\Longrightarrow\quad
|z_\lambda(\varphi)|\le 1.
\]
令
\[
N=\{\varphi\in E':\varphi(x_j)=0,\ j=1,\dots,m\}.
\]
若 \(\varphi\in N\)，则对一切整数 \(n\)，也有 \(n\varphi\in N\)，故
\[
|z_\lambda(n\varphi)|\le1\qquad(n=1,2,\dots),
\]
从而 \(z_\lambda(\varphi)=0\)。因此 \(N\subset\ker z_\lambda\)。

于是 \(z_\lambda\) 通过有限维映射
\[
\Phi:E'\to\mathbb R^m,\qquad
\Phi(\varphi)=(\varphi(x_1),\dots,\varphi(x_m))
\]
分解：存在线性泛函 \(L:\Phi(E')\to\mathbb R\)，使得
\[
z_\lambda(\varphi)=L(\Phi(\varphi)).
\]
因为 \(\Phi(E')\subset\mathbb R^m\) 有限维，\(L\) 可延拓为 \(\mathbb R^m\) 上的线性泛函，即存在 \(a_1,\dots,a_m\in\mathbb R\)，使
\[
L(y)=\sum_{j=1}^m a_j y_j.
\]
于是
\[
z_\lambda(\varphi)
=\sum_{j=1}^m a_j\varphi(x_j)
=\varphi\Bigl(\sum_{j=1}^m a_jx_j\Bigr).
\]
令
\[
x:=\sum_{j=1}^m a_jx_j\in E.
\]
则
\[
z_\lambda(\varphi)=\varphi(x)=(Jx)(\varphi)
\qquad(\varphi\in E'),
\]
即 \(z_\lambda=Jx\)。因此 \(z_\lambda\in J(E)\)。

反过来，若 \(z_\lambda=Jx\)，则
\[
z_\lambda(\varphi)=\varphi(x),
\]
显然关于弱星拓扑 \(\sigma(E',E)\) 连续。

最后，若记录由某个 \(x\in E\) 实现，则对一切 \(\varphi\in E'\)，
\[
z_\lambda(\varphi)=\lambda_{\mathbb R\varphi}(\varphi)=\varphi(x),
\]
所以 \(z_\lambda=Jx\)，从而弱星连续。反之，由上面的证明 \(z_\lambda=Jx\)，于是对任意有限维 \(F\) 和 \(\varphi\in F\)，
\[
\lambda_F(\varphi)=z_\lambda(\varphi)=\varphi(x).
\]
故该记录由 \(x\) 实现。由 \(J\) 单射，这个 \(x\) 唯一，且
\[
\|x\|=\|z_\lambda\|\le C.
\]
所以 (5.1) 成立。

---

## S6　有限观测的精确匹配

设 \(F\subset E'\) 有限维，定义
\[
q_F:E\to F^*,\qquad (q_Fx)(\varphi)=\varphi(x).
\]

### 1. 证明近似精确匹配

令
\[
N_F:=\ker q_F=\{x\in E:\varphi(x)=0\ \forall\varphi\in F\}.
\]
先说明 \(q_F\) 诱导 \(E/N_F\to F^*\) 的等距同构。

首先 \(q_F\) 满射。取 \(F\) 的一组基 \(\varphi_1,\dots,\varphi_n\)。由于这些泛函线性无关，赋值映射
\[
E\ni x\mapsto(\varphi_1(x),\dots,\varphi_n(x))\in\mathbb R^n
\]
是满射；否则会存在非零系数 \(c_i\) 使 \(\sum c_i\varphi_i=0\)，与基的线性无关性矛盾。因此任意给定 \(F\) 上线性泛函的值都可由某个 \(x\in E\) 实现，即 \(q_F(E)=F^*\)。

其次，对任意 \(x\in E\)，有
\[
\|q_Fx\|_{F^*}
=
\sup_{\substack{\varphi\in F\\\|\varphi\|\le1}}
|\varphi(x)|.
\tag{6.1}
\]
另一方面，商空间 \(E/N_F\) 的对偶是 \(N_F^\perp\)，且
\[
N_F^\perp:=\{\psi\in E':\psi|_{N_F}=0\}=F.
\]
事实上 \(F\subset N_F^\perp\)；若 \(g\notin F\)，由 \(F\) 有限维以及 \(g,\varphi_1,\dots,\varphi_n\) 线性无关，可找到 \(x\in E\) 使
\[
g(x)=1,\qquad \varphi_j(x)=0\quad(j=1,\dots,n),
\]
故 \(g\notin N_F^\perp\)。

于是由 Hahn–Banach 的商空间对偶公式，
\[
\|[x]\|_{E/N_F}
=
\sup_{\substack{\psi\in N_F^\perp\\\|\psi\|\le1}}
|\psi(x)|
=
\sup_{\substack{\varphi\in F\\\|\varphi\|\le1}}
|\varphi(x)|
=
\|q_Fx\|_{F^*}.
\tag{6.2}
\]
所以 \(q_F\) 是到 \(F^*\) 的商等距映射。

现在给定 \(\lambda_F\in F^*\)。由记录的统一界，
\[
\|\lambda_F\|_{F^*}
=
\sup_{\substack{\varphi\in F\\\|\varphi\|\le1}}
|\lambda_F(\varphi)|
\le C.
\]
由上面证明的商等距性质，存在唯一陪集 \([x_F]\in E/N_F\)，使得
\[
q_Fx_F=\lambda_F,
\qquad
\|[x_F]\|_{E/N_F}
=\|\lambda_F\|_{F^*}\le C.
\]
按商范数定义，对任意 \(\varepsilon>0\)，可在该陪集中取代表 \(x_{F,\varepsilon}\)，使
\[
\|x_{F,\varepsilon}\|\le \|[x_F]\|_{E/N_F}+\varepsilon
\le C+\varepsilon.
\]
同时
\[
q_Fx_{F,\varepsilon}=\lambda_F.
\]
因此对每个有限维 \(F\) 和每个 \(\varepsilon>0\)，存在 \(x_{F,\varepsilon}\in E\)，满足
\[
\boxed{
q_Fx_{F,\varepsilon}=\lambda_F,
\qquad
\|x_{F,\varepsilon}\|\le C+\varepsilon.} \tag{6.3}
\]

### 2. \(\varepsilon=0\) 是否总可取？

**不能。**

取
\[
E=c_0,\qquad E'=\ell^1,\qquad E''=\ell^\infty,
\]
并如上文一样取
\[
z=(1,1,\dots)\in\ell^\infty,
\qquad
\lambda_F(\varphi)=\sum_{n=1}^\infty\varphi_n,
\quad \varphi\in F\subset\ell^1\ \text{有限维}.
\]
这是统一界 \(C=1\) 的合法记录。

取
\[
\varphi=(2^{-n})_{n\ge1}\in\ell^1,
\qquad
F_0=\mathbb R\varphi.
\]
则
\[
\|\varphi\|_{\ell^1}=1,
\qquad
\lambda_{F_0}(\varphi)=1.
\]
若存在 \(x\in c_0\) 使
\[
q_{F_0}x=\lambda_{F_0},
\qquad
\|x\|\le1,
\]
则
\[
1=\varphi(x)=\sum_{n=1}^\infty 2^{-n}x_n
\le\sum_{n=1}^\infty 2^{-n}|x_n|
\le\sum_{n=1}^\infty2^{-n}=1.
\]
所有不等号必须取等号，于是
\[
|x_n|=1,\qquad x_n\ge0\quad(n\ge1),
\]
即 \(x_n=1\) 对所有 \(n\) 成立。但 \(x\in c_0\) 要求 \(x_n\to0\)，矛盾。因此即使对这一个有限维 \(F_0\)，也不能在范数不超过 \(C=1\) 的条件下精确匹配。

### 3. 为什么有限匹配不能替代 S5 的条件

S6 中的 (6.3) 只说明：对每个有限维 \(F\)，记录 \(\lambda_F\) 都在 \(q_F((C+\varepsilon)B_E)\) 中，等价地，\(z_\lambda|_F\) 的有限维限制可以用 \(E\) 中的元素在 \(F\) 上精确实现。但这只是有限维逼近。

- 商映射 \(q_F\) 是等距商映射，但陪集范数可能不由范数恰为 \(1\) 的代表达到；这正是上例中 \(\varepsilon=0\) 失败的原因。
- 不同有限维 \(F\) 得到的 \(x_{F,\varepsilon}\) 未必是同一个元素；\(B_E\) 在一般 Banach 空间中不是弱星紧的，不能由有限交性质推出全局解。
- 更强的整体对象始终是 \(z_\lambda\in E''\)。S6 本质上反映 Goldstine 型有限维逼近：\(J(B_E)\) 在 \(B_{E''}\) 中弱星稠密。但弱星稠密不等于属于 \(J(E)\)。
- S5 要求的是整个 \(z_\lambda\) 关于 \(\sigma(E',E)\) 连续，即 \(z_\lambda\in J(E)\)。这需要用一个有限观测组 \(x_1,\dots,x_m\) 控制所有 \(\varphi\in E'\)，而不能只逐个控制有限维子空间。

在 \(c_0\) 的例子中，\(z=(1,1,\dots)\notin c_0=J(c_0)\)，故 \(z\) 不弱星连续，记录不能由 \(c_0\) 中元素实现；同时，对每个有限维 \(F\)，S6 仍给出近似匹配。这说明有限观测的精确或近似匹配确实不能替代 S5 的弱星连续性条件。