下面按 S1–S6 逐段作答。

---

## S1　记录的完整载体

对任意 \(\varphi\in E'\)，定义
\[
z_\lambda(\varphi):=\lambda_{\mathbb R\varphi}(\varphi),
\]
其中 \(\mathbb R\varphi=\operatorname{span}\{\varphi\}\)；当 \(\varphi=0\) 时取值为 \(0\)。

### 1. 构造 \(z_\lambda\)

由兼容性，若 \(F\) 为任一包含 \(\varphi\) 的有限维子空间，则
\[
\lambda_F(\varphi)=\lambda_{\mathbb R\varphi}(\varphi)=z_\lambda(\varphi),
\]
故 \(z_\lambda\) 与所取 \(F\) 无关。

验证线性性：对 \(\varphi,\psi\in E'\)，取 \(F=\operatorname{span}\{\varphi,\psi\}\)。由于 \(\lambda_F\) 线性，
\[
z_\lambda(\varphi+\psi)
=\lambda_F(\varphi+\psi)
=\lambda_F(\varphi)+\lambda_F(\psi)
=z_\lambda(\varphi)+z_\lambda(\psi),
\]
数乘同理。因此 \(z_\lambda\) 是线性泛函。又由题设统一界，
\[
|z_\lambda(\varphi)|
=|\lambda_{\mathbb R\varphi}(\varphi)|
\le C\|\varphi\|,
\]
故
\[
z_\lambda\in E'',\qquad \|z_\lambda\|_{E''}\le C.
\]

反过来，若给定任意 \(z\in E''\)，定义
\[
\lambda_F:=z|_F,\qquad F\subset E'\text{ 有限维}.
\]
显然 \(F\subset G\) 时 \(\lambda_G|_F=\lambda_F\)，且
\[
|\lambda_F(\varphi)|\le \|z\|\,\|\varphi\|.
\]
所以 \(z\mapsto(\lambda_F)_{F}\) 给出一个合法的有界记录族。

上述两个构造互逆：
\[
z_{\lambda_F=z|_F}=z,
\]
以及
\[
(\lambda_F=z_{\lambda}|_F)_F=\lambda.
\]
因此所有兼容有界记录与 \(E''\) 一一对应；若固定统一界 \(C\)，则对应到闭球
\[
\{z\in E'':\|z\|\le C\}.
\]

此外，距离满足
\[
d(\lambda,\mu)
=\sup_{\|\varphi\|\le1}
\bigl|\lambda_{\mathbb R\varphi}(\varphi)
-\mu_{\mathbb R\varphi}(\varphi)\bigr|
=\sup_{\|\varphi\|\le1}|z_\lambda(\varphi)-z_\mu(\varphi)|
=\|z_\lambda-z_\mu\|_{E''}.
\]
故这是等距识别。

### 2. 规范嵌入 \(J:E\to E''\)

定义
\[
Jx(\varphi)=\varphi(x),\qquad x\in E,\ \varphi\in E'.
\]
显然 \(J\) 线性。由 Hahn–Banach 定理，对任意 \(x\ne0\)，存在 \(\varphi\in E'\)，\(\|\varphi\|=1\)，且 \(\varphi(x)=\|x\|\)。因此
\[
\|Jx\|_{E''}
=\sup_{\|\varphi\|\le1}|\varphi(x)|
=\|x\|.
\]
所以 \(J\) 是线性等距嵌入。\(J\) 的单射性由此立得；当且仅当 \(E\) 自反时 \(J\) 为满射。

### 3. 记录变换与 \(T''\)

设 \(T:E\to E\) 有界线性，令
\[
T'\varphi=\varphi\circ T\in E'.
\]
定义
\[
(\lambda^T)_F(\varphi)
=\lambda_{T'F}(T'\varphi),\qquad \varphi\in F.
\]
先验证这是合法记录族。若 \(F\subset G\)，则 \(T'F\subset T'G\)。对 \(\varphi\in F\)，
\[
(\lambda^T)_G(\varphi)
=\lambda_{T'G}(T'\varphi)
=\lambda_{T'F}(T'\varphi)
=(\lambda^T)_F(\varphi),
\]
故兼容。又有
\[
|(\lambda^T)_F(\varphi)|
\le C\|T'\varphi\|
\le C\|T\|\,\|\varphi\|.
\]
所以 \(\lambda^T\) 有界。

现在计算其对应的 \(E''\) 元素：
\[
\begin{aligned}
z_{\lambda^T}(\varphi)
&=(\lambda^T)_{\mathbb R\varphi}(\varphi)\\
&=\lambda_{T'(\mathbb R\varphi)}(T'\varphi).
\end{aligned}
\]
由于 \(T'(\mathbb R\varphi)=\mathbb R(T'\varphi)\)，故
\[
z_{\lambda^T}(\varphi)
=\lambda_{\mathbb R(T'\varphi)}(T'\varphi)
=z_\lambda(T'\varphi)
=(T''z_\lambda)(\varphi).
\]
因此
\[
\boxed{z_{\lambda^T}=T''z_\lambda.}
\]
换言之，在记录与 \(E''\) 的识别下，
\[
\lambda\longmapsto \lambda^T
\quad\text{恰为}\quad
z\longmapsto T''z.
\]

另外，对任意 \(x\in E\)、\(\varphi\in E'\)，
\[
(T''Jx)(\varphi)
=Jx(T'\varphi)
=(T'\varphi)(x)
=\varphi(Tx)
=J(Tx)(\varphi),
\]
所以
\[
\boxed{T''J=JT.}
\]

---

## S2　可恢复记录的稳定性

本阶段假设 \(E\) 自反，即 \(J:E\to E''\) 为满射。

对合法记录 \(\lambda\)，由 S1 得到 \(z_\lambda\in E''\)。定义
\[
\boxed{x_\lambda:=J^{-1}z_\lambda\in E.}
\]
这是本阶段所要求的原空间恢复。

### 1. 唯一性、范数与实现全部记录

若 \(x\in E\) 实现了全部记录，则对任意 \(\varphi\in E'\)，取有限维空间 \(\mathbb R\varphi\)，有
\[
Jx(\varphi)=\varphi(x)
=\lambda_{\mathbb R\varphi}(\varphi)
=z_\lambda(\varphi).
\]
因此 \(Jx=z_\lambda\)，从而 \(x=J^{-1}z_\lambda=x_\lambda\)。所以恢复唯一。

又有
\[
\|x_\lambda\|=\|Jx_\lambda\|=\|z_\lambda\|\le C.
\]
而对任意有限维 \(F\subset E'\) 和 \(\varphi\in F\)，
\[
\lambda_F(\varphi)
=z_\lambda(\varphi)
=Jx_\lambda(\varphi)
=\varphi(x_\lambda),
\]
即
\[
q_Fx_\lambda=\lambda_F.
\]
故 \(x_\lambda\) 实现了全部记录。

### 2. 与每个有界算子 \(T\) 相容

由 S1，
\[
z_{\lambda^T}=T''z_\lambda.
\]
而 \(z_\lambda=Jx_\lambda\)，且 \(T''J=JT\)，故
\[
z_{\lambda^T}
=T''Jx_\lambda
=J(Tx_\lambda).
\]
于是由 \(x_\mu\) 的唯一性，
\[
\boxed{x_{\lambda^T}=Tx_\lambda.}
\]
这正说明恢复与所有有界线性算子 \(T\) 相容。

### 3. 稳定性估计

由上面的相容性，
\[
x_{\lambda^T}=Tx_\lambda,\qquad
x_{\mu^U}=Ux_\mu.
\]
于是
\[
\begin{aligned}
\|x_{\lambda^T}-x_{\mu^U}\|
&=\|Tx_\lambda-Ux_\mu\|\\
&=\|T(x_\lambda-x_\mu)+(T-U)x_\mu\|\\
&\le \|T\|\,\|x_\lambda-x_\mu\|
+\|T-U\|\,\|x_\mu\|.
\end{aligned}
\]
又由 S1 的等距性，
\[
\|x_\lambda-x_\mu\|
=\|Jx_\lambda-Jx_\mu\|
=\|z_\lambda-z_\mu\|
=d(\lambda,\mu).
\]
因此
\[
\boxed{
\|x_{\lambda^T}-x_{\mu^U}\|
\le
\|T\|\,d(\lambda,\mu)
+\|T-U\|\,\|x_\mu\|.
}
\]
证毕。

---

## S3　子空间约束

设 \(Y\subset E\) 为闭线性子空间，且
\[
Y^\perp=\{\varphi\in E':\varphi|_Y=0\}.
\]
由于 \(E\) 自反，\(x_\lambda=J^{-1}z_\lambda\)，从而
\[
z_\lambda(\varphi)=\varphi(x_\lambda),
\qquad \varphi\in E'.
\]

### 1. \(x_\lambda\in Y\) 的充要条件

若 \(x_\lambda\in Y\)，则对任意 \(\varphi\in Y^\perp\)，
\[
z_\lambda(\varphi)=\varphi(x_\lambda)=0.
\]
所以
\[
z_\lambda|_{Y^\perp}=0.
\]

反过来，若 \(z_\lambda|_{Y^\perp}=0\) 但 \(x_\lambda\notin Y\)，由 Hahn–Banach 分离定理，存在 \(\varphi\in E'\) 使得
\[
\varphi|_Y=0,\qquad \varphi(x_\lambda)\ne0.
\]
于是 \(\varphi\in Y^\perp\)，但
\[
z_\lambda(\varphi)=\varphi(x_\lambda)\ne0,
\]
与 \(z_\lambda|_{Y^\perp}=0\) 矛盾。因此
\[
\boxed{x_\lambda\in Y
\iff
z_\lambda|_{Y^\perp}=0.}
\]
等价地，
\[
x_\lambda\in Y
\iff
\lambda_{\mathbb R\varphi}(\varphi)=0
\quad\text{对所有 }\varphi\in Y^\perp.
\]

### 2. 距离的准确对偶公式

对任意闭子空间 \(Y\)，Hahn–Banach 定理给出
\[
\operatorname{dist}(x_\lambda,Y)
=
\sup_{\substack{\varphi\in Y^\perp\\ \|\varphi\|\le1}}
|\varphi(x_\lambda)|.
\]
事实上，对 \(y\in Y\)，
\[
|\varphi(x_\lambda)|
=|\varphi(x_\lambda-y)|
\le \|\varphi\|\,\|x_\lambda-y\|,
\]
取下确界得 \(\le \operatorname{dist}(x_\lambda,Y)\)；若 \(x_\lambda\notin Y\)，再取单位泛函 \(\varphi\in Y^\perp\) 使 \(\varphi(x_\lambda)=\operatorname{dist}(x_\lambda,Y)\)，即得反向不等式。若 \(x_\lambda\in Y\)，两边均为 \(0\)。

代入 \(z_\lambda(\varphi)=\varphi(x_\lambda)\)，得到记录表达式
\[
\boxed{
\operatorname{dist}(x_\lambda,Y)
=
\|z_\lambda|_{Y^\perp}\|_{(Y^\perp)'}
=
\sup_{\substack{\varphi\in Y^\perp\\ \|\varphi\|\le1}}
|\lambda_{\mathbb R\varphi}(\varphi)|.
}
\]
这就是准确的对偶公式。

---

## S4　一般 Banach 空间

### 结论

**不是。** 对一般 Banach 空间，并非每一份合法记录都能由某个 \(x_\lambda\in E\) 实现。

一般判别原则是：
\[
\boxed{
\text{记录 }\lambda\text{ 可由某个 }x\in E\text{ 实现}
\iff
z_\lambda\in J(E).
}
\]
若 \(z_\lambda=Jx\)，则实现元唯一，且
\[
\|x\|=\|z_\lambda\|\le C,
\]
并且
\[
x_{\lambda^T}=Tx
\]
以及 S2 的稳定性估计都成立。因此问题完全归结为 \(z_\lambda\) 是否属于 \(J(E)\)；非自反空间中可以取到 \(z_\lambda\in E''\setminus J(E)\)。

### 反例

取实 Banach 空间
\[
E=c_0.
\]
则
\[
E'=\ell^1,\qquad E''=\ell^\infty.
\]
取
\[
z=(1,1,1,\dots)\in\ell^\infty,
\qquad \|z\|_{\ell^\infty}=1.
\]
对每个有限维 \(F\subset \ell^1\)，定义
\[
\lambda_F(\varphi)
=z(\varphi)
=\sum_{n=1}^{\infty}\varphi_n,
\qquad \varphi=(\varphi_n)\in F.
\]
由于
\[
|\lambda_F(\varphi)|
\le \sum_{n=1}^{\infty}|\varphi_n|
=\|\varphi\|_{\ell^1},
\]
统一界可取 \(C=1\)。兼容性显然成立，因此这是一个合法记录族。

若存在 \(x=(x_n)\in c_0\) 实现全部记录，则对每个 \(e_n\in \ell^1\)，
\[
x_n=e_n(x)
=\lambda_{\mathbb R e_n}(e_n)
=z(e_n)
=1.
\]
于是 \(x=(1,1,1,\dots)\)，但该序列不属于 \(c_0\)，矛盾。故不存在实现该记录的 \(x\in c_0\)。

因此一般 Banach 空间中，S4 所问的断言不成立。

### 何时对所有记录成立

对给定的 Banach 空间 \(E\)，若**每一份**合法记录都可实现，则取任意 \(z\in E''\)，定义
\[
\lambda_F=z|_F,\qquad C=\|z\|.
\]
由假设存在 \(x\in E\) 实现该记录，于是 \(Jx=z\)。因此 \(J\) 满射，即 \(E\) 自反。反过来，若 \(E\) 自反，则由 S2，每份记录都可实现。

所以：
\[
\boxed{
\text{所有合法记录均可唯一实现}
\iff E\text{ 自反}.
}
\]

---

## S5　单条记录的拓扑条件

### 结论

**是。** 若 \(z_\lambda:E'\to\mathbb R\) 关于弱星拓扑 \(\sigma(E',E)\) 连续，则它必可由某个 \(x\in E\) 实现。

更准确地说，对任意线性泛函 \(z:E'\to\mathbb R\)，有等价关系
\[
\boxed{
z\text{ 关于 }\sigma(E',E)\text{ 连续}
\iff
z\in J(E)
\iff
\exists x\in E\ \forall\varphi\in E',\ z(\varphi)=\varphi(x).
}
\]
在本问题中，最后一式又等价于记录 \(\lambda\) 可由 \(x\) 实现，因为
\[
z_\lambda(\varphi)=\lambda_{\mathbb R\varphi}(\varphi).
\]

### 证明

先证标准事实
\[
(E',\sigma(E',E))'=J(E).
\]

设 \(z:E'\to\mathbb R\) 关于 \(\sigma(E',E)\) 连续。由连续性于 \(0\) 处，存在
\[
x_1,\dots,x_n\in E,\qquad \delta>0,
\]
使得只要
\[
|\varphi(x_i)|<\delta,\qquad i=1,\dots,n,
\]
就有
\[
|z(\varphi)|<1.
\]
令
\[
N=\bigcap_{i=1}^n\ker(Jx_i)
=\{\varphi\in E':\varphi(x_i)=0,\ i=1,\dots,n\}.
\]
若 \(\varphi\in N\)，则对任意 \(t>0\)，\(t\varphi\) 仍满足 \(|\!t\varphi(x_i)|=0<\delta\)，故
\[
|z(t\varphi)|<1\qquad(\forall t>0).
\]
这迫使 \(z(\varphi)=0\)。因此
\[
N\subset\ker z.
\]
于是 \(z\) 通过有限秩映射
\[
\Phi:E'\to\mathbb R^n,\qquad
\Phi(\varphi)=(\varphi(x_1),\dots,\varphi(x_n))
\]
分解。由于 \(\Phi(E')\) 是有限维的，存在 \(a_1,\dots,a_n\in\mathbb R\)，使得
\[
z(\varphi)
=\sum_{i=1}^n a_i\varphi(x_i)
=\varphi\left(\sum_{i=1}^n a_i x_i\right).
\]
令 \(x=\sum_{i=1}^n a_i x_i\)，则
\[
z(\varphi)=\varphi(x)=Jx(\varphi).
\]
所以 \(z=Jx\in J(E)\)。

反过来，若 \(z=Jx\)，则
\[
z^{-1}((a,b))
=\{\varphi\in E':a<\varphi(x)<b\},
\]
这是 \(\sigma(E',E)\) 中的开集，故 \(z\) 弱星连续。

在本问题中，若 \(z_\lambda=Jx\)，则对任意有限维 \(F\) 和 \(\varphi\in F\)，
\[
\lambda_F(\varphi)
=z_\lambda(\varphi)
=\varphi(x),
\]
即 \(q_Fx=\lambda_F\)。因此 \(x\) 实现全部记录。由 S4 的判别原则，\(z_\lambda\in J(E)\) 正是可实现的充要条件。

所以 S5 的答案是：**弱星连续性保证可实现；并且弱星连续性与可实现性完全等价**。此时实现元唯一，且
\[
\|x\|=\|z_\lambda\|\le C.
\]

---

## S6　有限观测的精确匹配

### 1. 对每个有限维 \(F\) 和 \(\varepsilon>0\) 构造 \(x_{F,\varepsilon}\)

固定有限维子空间 \(F\subset E'\)，记
\[
q_F:E\to F^*,\qquad q_Fx(\varphi)=\varphi(x).
\]
令
\[
G=\ker q_F=\{x\in E:\varphi(x)=0\ \forall\varphi\in F\}.
\]
由于 \(q_F\) 为有限秩连续映射，\(G\) 是闭子空间。

先证明 \(q_F\) 是满射。取 \(F\) 的一组基 \(\varphi_1,\dots,\varphi_n\)，定义
\[
A:E\to\mathbb R^n,\qquad
Ax=(\varphi_1(x),\dots,\varphi_n(x)).
\]
若 \(A(E)\ne\mathbb R^n\)，则存在非零向量 \(a=(a_1,\dots,a_n)\) 与 \(A(E)\) 正交，即
\[
\sum_{i=1}^n a_i\varphi_i(x)=0
\qquad(\forall x\in E).
\]
于是 \(\sum_i a_i\varphi_i=0\)。但 \(\varphi_1,\dots,\varphi_n\) 线性无关，矛盾。因此 \(A\) 满射。于是任意给定 \(\lambda_F\in F^*\)，总存在 \(x_0\in E\) 使
\[
\varphi_i(x_0)=\lambda_F(\varphi_i),\qquad i=1,\dots,n,
\]
从而 \(q_Fx_0=\lambda_F\)。所以 \(q_F\) 满射。

由 \(A\) 满射，可取 \(u_1,\dots,u_n\in E\) 使得
\[
\varphi_i(u_j)=\delta_{ij}.
\]
对任意 \(x\in E\)，
\[
x-\sum_{j=1}^n\varphi_j(x)u_j\in G.
\]
因此若 \(\psi\in G^\perp\)，则
\[
\psi(x)
=\sum_{j=1}^n\varphi_j(x)\psi(u_j),
\]
故
\[
\psi=\sum_{j=1}^n\psi(u_j)\varphi_j\in F.
\]
反向包含 \(F\subset G^\perp\) 显然。因此
\[
G^\perp=F
\]
作为 \(E'\) 的子空间。

由商空间对偶的标准公式（\(G\) 闭，\(E\) Banach，故 \(E/G\) 为 Banach 空间），对任意 \(x\in E\)，
\[
\|x+G\|_{E/G}
=
\sup_{\substack{\psi\in G^\perp\\\|\psi\|\le1}}|\psi(x)|.
\]
又 \(G^\perp=F\)，所以
\[
\|x+G\|_{E/G}
=
\sup_{\substack{\varphi\in F\\\|\varphi\|\le1}}|\varphi(x)|
=
\|q_Fx\|_{F^*}.
\]
因此
\[
\inf_{\substack{x\in E\\q_Fx=\lambda_F}}\|x\|
=
\|x_0+G\|_{E/G}
=
\|\lambda_F\|_{F^*}.
\]
由题设统一界，
\[
\|\lambda_F\|_{F^*}\le C.
\]
于是对任意 \(\varepsilon>0\)，由下确界的定义，存在 \(x_{F,\varepsilon}\in E\) 满足
\[
q_Fx_{F,\varepsilon}=\lambda_F,
\qquad
\|x_{F,\varepsilon}\|
\le \|\lambda_F\|_{F^*}+\varepsilon
\le C+\varepsilon.
\]
即
\[
\boxed{
q_Fx_{F,\varepsilon}=\lambda_F,
\qquad
\|x_{F,\varepsilon}\|\le C+\varepsilon.
}
\]

证明还给出了最佳可能常数：
\[
\boxed{
\inf\{\|x\|:q_Fx=\lambda_F\}
=
\|\lambda_F\|_{F^*}.
}
\]
但该下确界不一定在 \(E\) 中达到。

### 2. 是否总能取 \(\varepsilon=0\)？

**不能。** 下面给出反例。

取
\[
E=c_0,\qquad E'=\ell^1,\qquad E''=\ell^\infty.
\]
取
\[
z=(1,1,1,\dots)\in\ell^\infty,
\qquad \|z\|=1.
\]
对每个有限维 \(G\subset\ell^1\)，定义
\[
\lambda_G=z|_G,
\qquad
\lambda_G(\varphi)=\sum_{n=1}^{\infty}\varphi_n.
\]
则统一界 \(C=1\)。

取
\[
F=\mathbb R\varphi,
\qquad
\varphi=\left(\frac1{n^2}\right)_{n\ge1}\in\ell^1.
\]
记
\[
A=\sum_{n=1}^{\infty}\frac1{n^2}.
\]
则
\[
\lambda_F(\varphi)=A.
\]
并且
\[
\|\lambda_F\|_{F^*}
=
\frac{|\lambda_F(\varphi)|}{\|\varphi\|_{\ell^1}}
=
\frac{A}{A}
=
1.
\]
若存在 \(x=(x_n)\in c_0\) 使得
\[
q_Fx=\lambda_F
\quad\text{且}\quad
\|x\|_{\infty}\le1,
\]
则特别有
\[
\sum_{n=1}^{\infty}\frac{x_n}{n^2}=A.
\]
另一方面，
\[
A
=
\sum_{n=1}^{\infty}\frac{x_n}{n^2}
\le
\sum_{n=1}^{\infty}\frac{|x_n|}{n^2}
\le
\sum_{n=1}^{\infty}\frac1{n^2}
=A.
\]
故所有不等式必须取等号，特别地
\[
|x_n|=1\qquad(\forall n).
\]
但这样的序列不趋于 \(0\)，不属于 \(c_0\)，矛盾。因此不存在满足条件的 \(x\)。

所以 \(\varepsilon=0\) 并非总能取到。

### 3. 为什么有限匹配不能替代 S5 的条件

S6 中的有限匹配只检验 \(z_\lambda\) 在单个有限维子空间 \(F\) 上的值：
\[
z_\lambda|_F=\lambda_F.
\]
而 S5 的弱星连续性是一个**全局条件**：
\[
z_\lambda\in J(E)
\iff
\exists x\in E\ \forall\varphi\in E',\ 
z_\lambda(\varphi)=\varphi(x).
\]

需要注意，实际上对任意 \(z\in E''\) 和任意有限维 \(F\subset E'\)，限制 \(z|_F\) 都已经可以由某个 \(x_F\in E\) 精确表示，因为 \(q_F:E\to F^*\) 是满射。因此仅凭“每个有限维限制都能精确匹配”不能区分 \(E''\) 与 \(J(E)\)。S6 的定量结论只是进一步把范数控制到 \(C+\varepsilon\)，但它仍然是逐 \(F\)、带 \(\varepsilon\) 的局部结论。

不同 \(F\) 对应的 \(x_{F,\varepsilon}\) 未必兼容；取一有界网时，其弱星极限可能只是 \(E''\) 中的元素，而不在 \(J(E)\) 中。上面的 \(c_0\) 例子正是如此：对每个有限维 \(F\) 和每个 \(\varepsilon>0\) 都可作近似匹配，却不存在一个 \(x\in c_0\) 同时实现全部记录；相应的 \(z=(1,1,\dots)\) 不弱星连续，也不属于 \(J(c_0)\)。

因此，S6 的有限维 Helly 型匹配不能替代 S5 的弱星连续性条件；后者恰好等价于全局可实现性 \(z_\lambda\in J(E)\)。