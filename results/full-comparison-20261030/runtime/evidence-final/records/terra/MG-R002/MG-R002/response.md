一般的 Banach 空间中，**这样的整体恢复不一定存在**。这些条件恰好确定一个双对偶元素 \(L_\lambda\in E''\)；它能由 \(E\) 中的点实现，当且仅当 \(L_\lambda\) 属于 \(E\) 在 \(E''\) 中的典范像。因此，所有记录族都能恢复的充要条件是 \(E\) 自反。

先定义
\[
L_\lambda(\varphi)
=\lambda_{\operatorname{span}\{\varphi\}}(\varphi),
\qquad \varphi\in E'.
\]
相容性保证，只要有限维子空间 \(F\) 包含 \(\varphi\)，就有
\[
L_\lambda(\varphi)=\lambda_F(\varphi).
\]
对任意 \(\varphi,\psi\in E'\)，在包含二者的有限维子空间上使用线性性，可知 \(L_\lambda\) 线性；给定的界则说明
\[
|L_\lambda(\varphi)|\le C\|\varphi\|,
\qquad \|L_\lambda\|\le C.
\]
反过来，任意 \(L\in E''\) 的限制 \(\lambda_F=L|_F\) 都构成这样的记录族。这个对应将记录族空间等距地对应到 \(E''\)，因为
\[
d(\lambda,\mu)=\|L_\lambda-L_\mu\|_{E''}.
\]

令典范嵌入 \(J:E\to E''\) 为
\[
(Jx)(\varphi)=\varphi(x).
\]
由 Hahn–Banach 定理，\(J\) 是线性等距映射。于是，单个记录族可实现的充要条件是
\[
L_\lambda\in J(E).
\]
在这个条件下，唯一可能的恢复映射是
\[
\boxed{\quad x_\lambda=J^{-1}L_\lambda.\quad}
\]
它满足全部记录，且
\[
\|x_\lambda\|=\|L_\lambda\|\le C.
\]
对于任意两个可实现的记录族，恢复实际上是等距的：
\[
\|x_\lambda-x_\mu\|
=\|L_\lambda-L_\mu\|
=d(\lambda,\mu).
\]
因此，它满足所要求的稳定性。由于 \(E\) 完备，\(J(E)\) 是 \(E''\) 的闭子空间，所以可实现记录在距离 \(d\) 下也构成闭子空间。

对任意有界线性算子 \(T:E\to E\)，其双伴随满足
\[
L_{\lambda^T}=T''L_\lambda,
\qquad T''J=JT.
\]
因而可实现记录经变换后仍可实现，并且
\[
x_{\lambda^T}=T x_\lambda.
\]
同时，对任意记录族都有
\[
d(\lambda^T,\mu^T)\le \|T\|\,d(\lambda,\mu).
\]
变换后的记录界可以取 \(\|T\|C\)。

如果 \(E\) 自反，\(J(E)=E''\)，上面的公式便对**每个**给定记录族提供所要求的恢复映射。反之，如果每个有界相容记录族都能在 \(E\) 中实现，那么每个 \(L\in E''\) 都属于 \(J(E)\)，故 \(E\) 自反。

下面是一般情形下的具体反例。取 \(E=c_0\)，记标准单位向量为 \(e_n\)。对每个 \(\varphi\in E'\)，定义
\[
L(\varphi)=\sum_{n=1}^{\infty}\varphi(e_n).
\]
这个级数绝对收敛：对任意 \(N\)，取各系数的符号，得到
\[
\sum_{n=1}^{N}|\varphi(e_n)|
=
\varphi\!\left(\sum_{n=1}^{N}
\operatorname{sgn}(\varphi(e_n))e_n\right)
\le \|\varphi\|.
\]
所以 \(L\in E''\) 且 \(\|L\|\le1\)。令 \(\lambda_F=L|_F\)，便得到满足题设且 \(C=1\) 的记录族。

设 \(\delta_n(x)=x_n\) 为第 \(n\) 个坐标泛函，则
\[
L(\delta_n)=1\qquad(n\ge1).
\]
如果存在 \(x\in c_0\) 实现全部记录，就必须有 \(x_n=1\) 对所有 \(n\) 成立，这与 \(x_n\to0\) 矛盾。因此，此记录族没有取值于原空间的恢复点。

这个反例仍可由有限观测逐项逼近：令 \(u^{(N)}=\sum_{n=1}^{N}e_n\)，则对每个 \(\varphi\in E'\)，
\[
\varphi(u^{(N)})\longrightarrow L(\varphi).
\]
但这些实现记录与 \(\lambda\) 的距离始终为 \(1\)。逐个有限观测的收敛，因而不足以推出题设记录距离下的整体恢复。