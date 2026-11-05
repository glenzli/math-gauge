## S1　记录的完整载体

令 \(\mathcal R(E)\) 表示所有兼容且具有某个有限统一界的记录族。对 \(\lambda\in\mathcal R(E)\)，定义
\[
z_\lambda(\varphi)
=\lambda_{\mathbb R\varphi}(\varphi),\qquad \varphi\in E'.
\]
若有限维 \(F\) 包含 \(\varphi\)，兼容性给出
\[
z_\lambda(\varphi)=\lambda_F(\varphi).
\]
对任意 \(\varphi,\psi\in E'\)，在 \(F=\operatorname{span}\{\varphi,\psi\}\) 上使用 \(\lambda_F\) 的线性性，可知 \(z_\lambda\) 线性。统一界又给出
\[
|z_\lambda(\varphi)|\le C\|\varphi\|,
\]
故 \(z_\lambda\in E''\)，且 \(\|z_\lambda\|\le C\)。

反过来，对任意 \(z\in E''\)，定义
\[
\lambda^z_F=z|_F.
\]
这些限制相互兼容，且统一界可取 \(\|z\|\)。上述两个构造互逆，并且
\[
d(\lambda,\mu)
=\sup_{\|\varphi\|\le1}|z_\lambda(\varphi)-z_\mu(\varphi)|
=\|z_\lambda-z_\mu\|_{E''}.
\]
因此，\(\mathcal R(E)\) 与 \(E''\) 线性等距对应。若事先固定统一界 \(C\)，则满足该界的记录对应 \(E''\) 的闭球 \(C B_{E''}\)。

规范映射定义为
\[
J:E\longrightarrow E'',\qquad (Jx)(\varphi)=\varphi(x).
\]
它显然线性，且 \(\|Jx\|\le\|x\|\)。当 \(x\ne0\) 时，在 \(\mathbb Rx\) 上定义 \(f(tx)=t\|x\|\)，其范数为 \(1\)。由 Hahn–Banach 定理将 \(f\) 延拓到 \(E\)，得到 \(\varphi\in E'\) 满足 \(\|\varphi\|=1\)、\(\varphi(x)=\|x\|\)。故 \(\|Jx\|\ge\|x\|\)；\(x=0\) 时也成立。因此 \(J\) 是线性等距映射。

对有界算子 \(T:E\to E\)，\(T'F\) 是有限维子空间。由原记录的兼容性，\(\lambda^T\) 兼容；其统一界可取 \(C\|T\|\)。并且
\[
z_{\lambda^T}(\varphi)
=\lambda_{T'(\mathbb R\varphi)}(T'\varphi)
=z_\lambda(T'\varphi)
=(T''z_\lambda)(\varphi).
\]
所以记录变换在上述识别下恰为 \(T''\)。此外，直接计算可得
\[
T''Jx=J(Tx). \tag{1}
\]

## S2　可恢复记录的稳定性

若 \(E\) 自反，则 \(J:E\to E''\) 满射。定义
\[
x_\lambda=J^{-1}z_\lambda.
\]
于是对每个 \(\varphi\in E'\)，
\[
\varphi(x_\lambda)=z_\lambda(\varphi)
=\lambda_{\mathbb R\varphi}(\varphi),
\]
故 \(x_\lambda\) 实现全部记录。\(J\) 的单射性保证其唯一，且
\[
\|x_\lambda\|=\|z_\lambda\|\le C.
\]

等距性还给出精确稳定关系
\[
\|x_\lambda-x_\mu\|=d(\lambda,\mu). \tag{2}
\]
由 S1 和式 (1)，
\[
Jx_{\lambda^T}=z_{\lambda^T}=T''z_\lambda
=T''Jx_\lambda=J(Tx_\lambda),
\]
故 \(x_{\lambda^T}=Tx_\lambda\)。因此
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

对任意 \(x\in E\)，有对偶距离公式
\[
\operatorname{dist}(x,Y)
=\sup_{\substack{\varphi\in Y^\perp\\ \|\varphi\|\le1}}
|\varphi(x)|. \tag{3}
\]
事实上，右侧不大于左侧，因为对任意 \(y\in Y\)，
\[
|\varphi(x)|=|\varphi(x-y)|\le\|\varphi\|\,\|x-y\|.
\]
反向不等式：令 \(Q:E\to E/Y\) 为商映射。由于 \(Y\) 闭，\(E/Y\) 是赋范空间，且
\(\|Qx\|=\operatorname{dist}(x,Y)\)。若此距离非零，由 Hahn–Banach 定理，存在 \(f\in(E/Y)'\) 满足
\(\|f\|=1\) 和 \(f(Qx)=\|Qx\|\)。取 \(\varphi=f\circ Q\)，则
\(\varphi\in Y^\perp\)、\(\|\varphi\|\le1\)，并达到所需下界。距离为零时，反向不等式显然。

代入 \(x=x_\lambda\)，得到完全由记录表示的公式
\[
\boxed{\displaystyle
\operatorname{dist}(x_\lambda,Y)
=\sup_{\substack{\varphi\in Y^\perp\\ \|\varphi\|\le1}}
\left|\lambda_{\mathbb R\varphi}(\varphi)\right|.
}
\]
若 \(x_\lambda\in Y\)，显然 \(z_\lambda|_{Y^\perp}=0\)。反之，若该限制为零，上式给出 \(\operatorname{dist}(x_\lambda,Y)=0\)；由 \(Y\) 闭，\(x_\lambda\in Y\)。因此
\[
x_\lambda\in Y\quad\Longleftrightarrow\quad
z_\lambda|_{Y^\perp}=0.
\]

## S4　一般 Banach 空间

**结论：不一定。**事实上，给定的 \(E\) 中每份合法记录都可实现，当且仅当 \(E\) 自反：由 S1，这等价于 \(J:E\to E''\) 满射。若记录可实现，则实现元唯一、满足范数界，并具有 S2 中的等距稳定性和算子相容性；但一般空间中可能不存在实现元。

反例取 \(E=c_0\)，配上上确界范数。其对偶等距识别为 \(\ell^1\)：若 \(\varphi\in(c_0)'\)，令 \(a_n=\varphi(u_n)\)，其中 \(u_n\) 是第 \(n\) 个单位向量。用有限支撑符号向量测试可得
\[
\sum_{n=1}^N|a_n|\le\|\varphi\|.
\]
故 \(a\in\ell^1\)；再由有限支撑序列在 \(c_0\) 中稠密，
\(\varphi(x)=\sum_n a_nx_n\)，且 \(\|\varphi\|=\|a\|_1\)。

定义 \(z\in(c_0)''\) 为
\[
z(a)=\sum_{n=1}^\infty a_n,\qquad a\in\ell^1.
\]
它的范数为 \(1\)，所以 \(\lambda_F=z|_F\) 是统一界为 \(C=1\) 的合法记录。令 \(\delta_n(x)=x_n\)。若某个 \(x\in c_0\) 实现该记录，则
\[
x_n=\delta_n(x)=z(\delta_n)=1\qquad(n\ge1),
\]
这与 \(x\in c_0\) 矛盾。

## S5　单条记录的拓扑条件

**结论：必可实现。**更准确地，对任意合法记录，
\[
\boxed{\quad
z_\lambda\text{ 关于 }\sigma(E',E)\text{ 连续}
\quad\Longleftrightarrow\quad
\exists x\in E:\ z_\lambda=Jx.
\quad}
\]

若 \(z_\lambda=Jx\)，则 \(z_\lambda(\varphi)=\varphi(x)\)，按弱星拓扑的定义连续。

反之，设线性泛函 \(z=z_\lambda\) 弱星连续。由其在零点的连续性，存在 \(x_1,\ldots,x_n\in E\) 和 \(\delta>0\)，使
\[
|\varphi(x_i)|<\delta\ (1\le i\le n)
\quad\Longrightarrow\quad |z(\varphi)|<1.
\]
令
\[
A:E'\to\mathbb R^n,\qquad
A\varphi=(\varphi(x_1),\ldots,\varphi(x_n)).
\]
若 \(A\varphi=0\)，则对每个实数 \(t\)，\(t\varphi\) 都满足上述邻域条件，因此 \(|t z(\varphi)|<1\) 对所有 \(t\) 成立，故 \(z(\varphi)=0\)。于是 \(z\) 可经 \(A(E')\) 分解为一个线性泛函。将其延拓到有限维空间 \(\mathbb R^n\)，可得实数 \(a_1,\ldots,a_n\) 使
\[
z(\varphi)=\sum_{i=1}^n a_i\varphi(x_i)
=\varphi\!\left(\sum_{i=1}^n a_i x_i\right).
\]
所以 \(z=Jx\)，其中 \(x=\sum_i a_i x_i\)。无坐标的平凡情形给出 \(z=0=J0\)。

由 S1，此 \(x\) 唯一，且 \(\|x\|=\|z_\lambda\|\le C\)。

## S6　有限观测的精确匹配

固定有限维 \(F\subset E'\)，令
\[
K=\ker q_F=\{x\in E:\varphi(x)=0\ \text{对所有 }\varphi\in F\}.
\]
首先 \(q_F:E\to F^*\) 满射。否则，其像是 \(F^*\) 的真线性子空间；由有限维线性代数，存在非零 \(\varphi\in F=(F^*)^*\) 消去该像，即 \(\varphi(x)=0\) 对所有 \(x\in E\) 成立，矛盾。

\(K\) 是闭子空间，故可赋予 \(E/K\) 商范数。由满射性，\(q_F\) 诱导线性同构
\[
\bar q_F:E/K\longrightarrow F^*.
\]
此外 \(K^\perp=F\)：包含关系 \(F\subset K^\perp\) 显然；若 \(\psi\in K^\perp\)，则 \(\psi\) 通过满射 \(q_F\) 分解为 \(F^*\) 上的线性泛函，而后者由有限维识别属于 \(F\)。

商空间对偶等距识别为 \(K^\perp=F\)。对
\(v=\bar q_F^{-1}(\lambda_F)\)，由 Hahn–Banach 的范数公式，
\[
\begin{aligned}
\inf_{q_Fx=\lambda_F}\|x\|
&=\|v\|_{E/K}\\
&=\sup_{\substack{\varphi\in F\\\|\varphi\|\le1}}
|\lambda_F(\varphi)|\\
&=\|\lambda_F\|_{F^*}\le C. \tag{4}
\end{aligned}
\]
因此，对每个 \(\varepsilon>0\)，可选一个代表元 \(x_{F,\varepsilon}\in E\)，使
\[
q_Fx_{F,\varepsilon}=\lambda_F,\qquad
\|x_{F,\varepsilon}\|<\|v\|+\varepsilon\le C+\varepsilon.
\]

### 不能总取 \(\varepsilon=0\)

沿用 S4 的 \(E=c_0\)、\(C=1\) 和 \(z(a)=\sum_n a_n\)。取
\[
a=(2^{-n})_{n\ge1}\in\ell^1,\qquad F=\operatorname{span}\{a\}.
\]
有 \(\|a\|_1=1\) 和 \(\lambda_F(a)=1\)。若 \(x\in c_0\)、\(\|x\|_\infty\le1\) 且 \(q_Fx=\lambda_F\)，则
\[
0=1-\sum_{n=1}^\infty2^{-n}x_n
=\sum_{n=1}^\infty2^{-n}(1-x_n).
\]
每项非负，故所有 \(x_n=1\)，与 \(x\in c_0\) 矛盾。

这里式 (4) 的下确界确实可由有限支撑向量逼近：令
\[
x^{(N)}=\frac{(1,\ldots,1,0,\ldots)}{1-2^{-N}},
\]
其中前 \(N\) 项非零，则 \(q_Fx^{(N)}=\lambda_F\)，且
\(\|x^{(N)}\|_\infty\to1\)。

### 为什么有限匹配不能替代 S5

有限匹配允许所用的 \(x_{F,\varepsilon}\) 随 \(F,\varepsilon\) 改变，不保证存在一个共同的 \(x\)。S4 的记录已给出反例：它满足本阶段对所有 \(F,\varepsilon\) 的匹配结论，却不能整体实现。也可直接看到其弱星不连续：在 \(\sigma(\ell^1,c_0)\) 下，
\[
\delta_n\longrightarrow0,
\]
因为对每个 \(x\in c_0\)，\(\delta_n(x)=x_n\to0\)；但 \(z(\delta_n)=1\)。

事实上，即使每个有限维 \(F\) 都能以**同一个界 \(C\)** 精确匹配，仍不能推出整体实现。为见此，仍取 \(E=c_0\)，定义
\[
z_b(a)=\sum_{n=1}^\infty\left(1-\frac1n\right)a_n,
\qquad C=1.
\]
对每个非零 \(a\in\ell^1\)，
\[
|z_b(a)|
\le\|a\|_1-\sum_{n=1}^\infty\frac{|a_n|}{n}
<\|a\|_1.
\]
故由有限维单位球的紧性，对每个非零有限维 \(F\)，
\(\|z_b|_F\|<1\)。由式 (4)，存在匹配 \(z_b|_F\) 的 \(x_F\in c_0\)，且 \(\|x_F\|<1\)；\(F=\{0\}\) 时取零即可。然而整体实现将要求
\(x_n=1-1/n\)，该序列不属于 \(c_0\)。