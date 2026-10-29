令
\[
F=\ker(I-T)\cap\ker(I-S),\qquad K=K_TK_S.
\]
把 \(F\) 看作共同不动点空间，并定义
\[
Q_{\mathrm{rec}}=q(F),\qquad
D=q^{-1}(Q_{\mathrm{rec}})=F+Y.
\]

主定理如下：

1. 单算子 \(R\) 具有完全相同的不动点和记录空间：
   \[
   \ker(I-R)=F,\qquad \overline{(I-R)E}=Y.
   \]
2. 对每个 \(x\in E\)，下列条件等价：
   \[
   \begin{aligned}
   &A_{N,M}x\quad\text{在 }\min(N,M)\to\infty\text{ 时范数收敛};\\
   &R^nx\quad\text{在 }n\to\infty\text{ 时范数收敛};\\
   &x\in D;\\
   &q(x)\in Q_{\mathrm{rec}}.
   \end{aligned}
   \]
   收敛时，两者的极限是唯一满足 \(f\in F,\ q(f)=q(x)\) 的状态 \(f\)。
3. \(F\cap Y=\{0\}\)，且 \(D=F\oplus Y\) 是闭子空间。\(Q_{\mathrm{rec}}\) 也是 \(Q\) 的闭子空间。恢复映射为
   \[
   \boxed{\quad G=(q|_F)^{-1}:Q_{\mathrm{rec}}\longrightarrow F,\qquad
   G(q(x))=\lim A_{N,M}x=\lim R^nx.\quad}
   \]
   它的值域恰为 \(F\)。同一条可恢复记录的所有代表元都收敛到同一个状态；域外记录的任何代表元都不收敛。
4. 恢复稳定：对 \(r,r'\in Q_{\mathrm{rec}}\)，
   \[
   \|r-r'\|_Q
   \le \|G(r)-G(r')\|
   \le K\,\|r-r'\|_Q.
   \]
   更精确地，若 \(F\ne\{0\}\)，最优 Lipschitz 常数是
   \[
   \boxed{\quad
   \|G\|
   =\sup_{f\in F\setminus\{0\}}
     \frac{\|f\|}{\operatorname{dist}(f,Y)}
   \le K_TK_S.
   \quad}
   \]
   若 \(F=\{0\}\)，则 \(G\) 是定义在零空间上的零映射。状态上的恢复算子
   \[
   P=Gq|_D:D\longrightarrow F
   \]
   是核为 \(Y\) 的有界投影，且 \(\|P\|=\|G\|\)。

此外，所有记录都可恢复当且仅当
\[
E=F\oplus Y.
\]
下面给出一个仅用 \(T,S\) 的对偶不动点即可检验的等价条件。

令
\[
\mathcal H_0=\{\varphi\in E^*:T^*\varphi=\varphi,\ S^*\varphi=\varphi\},
\qquad
\mathcal H=\{\varphi\in\mathcal H_0:\varphi|_F=0\}.
\]
那么
\[
\boxed{\quad
q(x)\in Q_{\mathrm{rec}}
\iff \varphi(x)=0\quad\text{对所有 }\varphi\in\mathcal H.
\quad}
\]
因此所有记录都可恢复，当且仅当 \(\mathcal H=\{0\}\)。对可恢复记录 \(q(x)\)，其恢复值也可表述为唯一的 \(f\in F\)，使得
\[
\varphi(f)=\varphi(x)\qquad(\varphi\in\mathcal H_0).
\]

**证明。** 先建立两个过程的消失估计。对幂有界算子 \(U\)，记
\[
B_n(U)=\left(\frac{I+U}{2}\right)^n
=\sum_{k=0}^n b_{n,k}U^k,\qquad
b_{n,k}=2^{-n}\binom nk,
\quad p_n=\max_k b_{n,k}.
\]
显然 \(\|B_n(U)\|\le K_U\)。二项式系数序列单峰，故
\[
\begin{aligned}
\|(I-U)B_n(U)\|
&\le K_U\left(
b_{n,0}+\sum_{k=1}^n|b_{n,k}-b_{n,k-1}|+b_{n,n}
\right)\\
&=2K_Up_n.
\end{aligned}
\]
并且 \(p_n\to0\)，例如
\[
p_n\le \frac1{\sqrt{\lfloor n/2\rfloor+1}}.
\]
最后一个估计可由
\[
p_{2m}=\prod_{k=1}^m\left(1-\frac1{2k}\right)
\le \exp\left(-\frac12\sum_{k=1}^m\frac1k\right)
\le\frac1{\sqrt{m+1}},
\qquad p_{2m+1}\le p_{2m}
\]
得到。

由于 \(T,S\) 交换，
\[
R^n=B_n(T)B_n(S),\qquad \|R^n\|\le K,
\]
以及
\[
\|R^n(I-T)\|\le2Kp_n,\qquad
\|R^n(I-S)\|\le2Kp_n. \tag{1}
\]
同样，由望远镜求和，
\[
\|A_{N,M}\|\le K,\quad
\|A_{N,M}(I-T)\|\le\frac{(1+K_T)K_S}{N},\quad
\|A_{N,M}(I-S)\|\le\frac{K_T(1+K_S)}{M}. \tag{2}
\]
所以两个过程都在 \((I-T)E+(I-S)E\) 上趋于零；再利用一致有界性和范数稠密性，它们都在 \(Y\) 上逐点趋于零。

由 \(q(Tx)=q(Sx)=q(x)\)，可知
\[
q(A_{N,M}x)=q(R^nx)=q(x). \tag{3}
\]
特别地，\((I-R)E\subseteq Y\)。反过来，对 \(y\in(I-T)E+(I-S)E\)，有 \(R^ny\to0\)，而
\[
y-R^ny=(I-R)\sum_{k=0}^{n-1}R^ky\in(I-R)E.
\]
因此 \(y\in\overline{(I-R)E}\)，取闭包即得
\[
Y=\overline{(I-R)E}.
\]

显然 \(F\subseteq\ker(I-R)\)。若 \(Rf=f\)，则由交换性及 (1)，
\[
(I-T)f=R^n(I-T)f\longrightarrow0,
\qquad
(I-S)f=R^n(I-S)f\longrightarrow0.
\]
故 \(f\in F\)，从而 \(\ker(I-R)=F\)。

现在设 \(x=f+y\)，其中 \(f\in F,\ y\in Y\)。两个过程固定 \(f\)，并使 \(y\) 趋于零，所以都收敛到 \(f\)。反之，若其中任一过程收敛到 \(f\)，由 (1) 或 (2) 可知 \(Tf=Sf=f\)；由 (3) 可知 \(q(f)=q(x)\)。于是 \(x-f\in Y\)，即 \(x\in F+Y\)。这证明了收敛等价及共同极限。相同论证还表明：只要任一过程存在趋向无穷指标的范数收敛子列，两个完整过程便都收敛。

若 \(f\in F\cap Y\)，则 \(R^nf=f\)，同时 \(R^nf\to0\)，故 \(f=0\)。对于任意 \(f\in F,\ y\in Y\)，
\[
\|f\|=\lim_{n\to\infty}\|R^n(f+y)\|\le K\|f+y\|.
\]
对 \(y\in Y\) 取下确界，得到
\[
\|f\|\le K\,\|q(f)\|_Q=K\,\operatorname{dist}(f,Y). \tag{4}
\]
因此 \(q|_F\) 单射且逆有界。由于 \(F\) 完备，(4) 还说明 \(q(F)\) 在 \(Q\) 中闭，进而 \(D=q^{-1}(q(F))\) 在 \(E\) 中闭。稳定性双边估计、最优常数公式，以及 \(\|P\|=\|G\|\)，均由商范数定义和
\[
P(f+y)=f\qquad(f\in F,\ y\in Y)
\]
直接得到。

最后，
\[
Y^\perp=\mathcal H_0,\qquad
D^\perp=(F+Y)^\perp=\mathcal H.
\]
由于 \(D\) 已证明为闭子空间，Hahn–Banach 定理给出
\[
D=\{x\in E:\varphi(x)=0\text{ 对所有 }\varphi\in\mathcal H\},
\]
这就证明了对偶判别条件及全记录可恢复的等价条件。唯一性表述则来自 \(Y=(Y^\perp)_\perp\)。

关于稳定性的边界，上述 Lipschitz 估计适用于**可恢复记录之间**的扰动。如果 \(Q_{\mathrm{rec}}\ne Q\)，它作为真线性子空间没有内点，因此任意小的记录扰动都可能落到恢复域外。逐点收敛也不保证在整个单位球上一致：例如在 \(E=\ell^1(\mathbb N_0)\) 上取右移 \(T\) 和 \(S=I\)，则
\[
F=\{0\},\qquad
Y=\left\{x:\sum_{k\ge0}x_k=0\right\},\qquad
Q_{\mathrm{rec}}=\{0\}.
\]
此时 \(e_0\) 的记录不可恢复；而在 \(Y\) 上，两个过程虽逐点趋于零，其算子范数始终为 \(1\)。因此一般不能从题设推出对所有可恢复状态一致的收敛速率。