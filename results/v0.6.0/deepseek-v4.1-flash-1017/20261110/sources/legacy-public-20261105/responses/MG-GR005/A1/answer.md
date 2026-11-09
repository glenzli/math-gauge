以下约定：空纤维的下确界为 \(+\infty\)；对非负凸函数 \(u\)，记 \(\bar u\) 为其最大下半连续凸下界。所有论证均按实高度上图理解。

---

## S1　原始记录

**结论：\(g_F\) 非负、凸、至少一点有限；且
\[
g_F(y)=\inf_{\substack{z\in K^*\\ r_{KF}z=y}}g_K(z).
\]
整个过程不需要纤维下确界取到。**

显然
\[
g_F(y)=\inf_{x:q_Fx=y}f(x)\ge 0.
\]
因 \(f\) 至少一点有限，取 \(x_0\in E\) 使 \(f(x_0)<\infty\)，令 \(y_0=q_Fx_0\)，则
\[
g_F(y_0)\le f(x_0)<\infty,
\]
故 \(g_F\) 至少一点有限。

下面证凸性。设 \(y_1,y_2\in F^*\)，\(\lambda\in[0,1]\)。若 \(g_F(y_1)\) 或 \(g_F(y_2)\) 为 \(+\infty\)，不等式自动成立；否则给定 \(\varepsilon>0\)，由下确界定义，取 \(x_i\) 使
\[
q_Fx_i=y_i,\qquad f(x_i)\le g_F(y_i)+\varepsilon,\quad i=1,2.
\]
令 \(x_\lambda=\lambda x_1+(1-\lambda)x_2\)。由 \(q_F\) 线性，
\[
q_Fx_\lambda=\lambda y_1+(1-\lambda)y_2.
\]
于是
\[
g_F(\lambda y_1+(1-\lambda)y_2)
\le f(x_\lambda)
\le \lambda f(x_1)+(1-\lambda)f(x_2)
\le \lambda g_F(y_1)+(1-\lambda)g_F(y_2)+\varepsilon.
\]
令 \(\varepsilon\downarrow 0\)，得凸性。

再证关系式。注意
\[
q_F=r_{KF}\circ q_K. \tag{1.1}
\]
若 \(z\in K^*\) 且 \(r_{KF}z=y\)，则对任意满足 \(q_Kx=z\) 的 \(x\)，有
\[
q_Fx=r_{KF}q_Kx=r_{KF}z=y.
\]
因此
\[
g_F(y)\le f(x),
\]
对所有这些 \(x\) 取下确界得
\[
g_F(y)\le g_K(z).
\]
再对 \(z\in r_{KF}^{-1}(y)\) 取下确界，得
\[
g_F(y)\le \inf_{r_{KF}z=y}g_K(z). \tag{1.2}
\]

反过来，若 \(q_Fx=y\)，令 \(z=q_Kx\)，则 \(r_{KF}z=y\)，且由 \(g_K\) 的定义
\[
g_K(z)\le f(x).
\]
于是
\[
\inf_{r_{KF}z=y}g_K(z)\le g_K(z)\le f(x).
\]
对所有满足 \(q_Fx=y\) 的 \(x\) 取下确界，得
\[
\inf_{r_{KF}z=y}g_K(z)\le g_F(y). \tag{1.3}
\]
由 (1.2)(1.3) 得等号。

上述凸性证明只取了近似极小点，关系式证明只用了下确界比较和线性性；**不需要任何纤维下确界达到**。

---

## S2　紧次水平集

**结论：在 \(f\) 下半连续且所有有限次水平集紧的假设下，每个 \(g_F\) 下半连续，且当 \(g_F(y)<\infty\) 时纤维下确界取到。**

先证取到性。固定 \(y\in F^*\)，设
\[
a:=g_F(y)<\infty.
\]
对 \(n\in\mathbb N\)，令
\[
C_n=\{x\in E:q_Fx=y,\ f(x)\le a+1/n\}.
\]
由下确界定义，\(C_n\neq\varnothing\)。又因 \(f\) 下半连续，\(\{f\le a+1/n\}\) 闭；因 \(q_F\) 连续，纤维 \(q_F^{-1}(y)\) 闭；故每个 \(C_n\) 闭。并且
\[
C_n\subset \{f\le a+1\},
\]
而 \(\{f\le a+1\}\) 紧。闭集族 \(\{C_n\}\) 具有有限交性质，故由紧性
\[
\bigcap_{n=1}^{\infty}C_n\neq\varnothing.
\]
取 \(x\in\bigcap_nC_n\)，则 \(q_Fx=y\)，且 \(f(x)\le a+1/n\) 对所有 \(n\) 成立，所以 \(f(x)\le a\)。另一方面由 \(g_F(y)\) 的定义 \(f(x)\ge a\)，故 \(f(x)=a=g_F(y)\)。因此下确界取到。

再证下半连续性。对任意有限实数 \(\alpha\)，考察次水平集
\[
\{y\in F^*:g_F(y)\le \alpha\}.
\]
当 \(\alpha<0\) 时它为空。设 \(\alpha\ge0\)。若 \(g_F(y)\le\alpha\)，则 \(g_F(y)<\infty\)，由上面的取到性存在 \(x\) 使
\[
q_Fx=y,\qquad f(x)=g_F(y)\le\alpha.
\]
因此
\[
\{g_F\le\alpha\}=q_F(\{f\le\alpha\}). \tag{2.1}
\]
事实上反向包含显然：若 \(x\in\{f\le\alpha\}\)，则对 \(y=q_Fx\) 有 \(g_F(y)\le f(x)\le\alpha\)。

由假设，\(\{f\le\alpha\}\) 紧；\(q_F\) 连续，故其像 \(q_F(\{f\le\alpha\})\) 在 \(F^*\) 中紧，从而是闭集。由 (2.1)，每个有限次水平集 \(\{g_F\le\alpha\}\) 闭，所以 \(g_F\) 下半连续。

---

## S3　兼容成本记录的实现

设已给每个有限维 \(F\subset E'\) 一点 \(y_F\in F^*\)，满足
\[
r_{KF}y_K=y_F\qquad(F\subset K),
\]
并设有限 \(c\ge0\) 满足
\[
g_F(y_F)\le c
\]
对所有有限维 \(F\) 成立。

**结论：存在唯一 \(x\in E\)，使得
\[
q_Fx=y_F\quad(\forall F),\qquad f(x)\le c.
\]**

令
\[
S_c=\{x\in E:f(x)\le c\}.
\]
由 S2 的假设，\(S_c\) 紧。对每个有限维 \(F\)，令
\[
C_F=\{x\in S_c:q_Fx=y_F\}.
\]
由于 \(g_F(y_F)\le c<\infty\)，由 S2 的取到性，存在 \(x\) 使
\[
q_Fx=y_F,\qquad f(x)=g_F(y_F)\le c.
\]
故 \(C_F\neq\varnothing\)。又 \(C_F\) 是 \(S_c\) 中闭集，因而紧。

验证有限交性质。取任意有限个有限维子空间 \(F_1,\dots,F_n\)，令
\[
K=\operatorname{span}(F_1\cup\cdots\cup F_n).
\]
则 \(K\) 仍有限维。若 \(x\in C_K\)，则 \(q_Kx=y_K\)，于是对每个 \(i\)，
\[
q_{F_i}x=r_{KF_i}q_Kx=r_{KF_i}y_K=y_{F_i}.
\]
所以
\[
C_K\subset C_{F_1}\cap\cdots\cap C_{F_n}.
\]
而 \(C_K\neq\varnothing\)，故有限交非空。于是紧集族 \(\{C_F\}\) 具有有限交性质，从而
\[
\bigcap_{F}C_F\neq\varnothing.
\]
取其中一点 \(x\)，则 \(q_Fx=y_F\) 对所有有限维 \(F\) 成立，且 \(x\in S_c\)，即 \(f(x)\le c\)。

唯一性：若 \(x,x'\) 都满足 \(q_Fx=y_F=q_Fx'\) 对所有有限维 \(F\) 成立，则对任意 \(\varphi\in E'\)，取 \(F=\operatorname{span}\varphi\)，得
\[
\varphi(x)=q_Fx(\varphi)=y_F(\varphi)=q_Fx'(\varphi)=\varphi(x').
\]
因此所有 \(\varphi\in E'\) 都湮灭 \(x-x'\)。因 \(E\) 为 Hausdorff 局部凸空间，\(E'\) 分离点，故 \(x=x'\)。

---

## S4　一般成本的恢复

**结论：可以。构造为
\[
u_F:=\bar g_F,\qquad
G(x):=\sup_{\substack{F\subset E'\\ \dim F<\infty}}u_F(q_Fx). \tag{4.1}
\]
则 \(G:E\to[0,+\infty]\) 下半连续、凸、\(G\le f\)，且它是所有下半连续凸函数 \(h\le f\) 的最大者。**

这个构造只用到各 \(g_F\)。下面验证性质。

每个 \(u_F\) 是下半连续凸函数，\(q_F\) 连续线性，故 \(u_F\circ q_F\) 下半连续凸。任意多个下半连续凸函数的上确界仍下半连续凸，所以 \(G\) 下半连续凸。又 \(u_F\le g_F\)，且对 \(x\) 与 \(y=q_Fx\)，
\[
g_F(q_Fx)=\inf_{q_Fz=q_Fx}f(z)\le f(x),
\]
故
\[
u_F(q_Fx)\le g_F(q_Fx)\le f(x).
\]
于是 \(G\le f\)。

再证最大性。令
\[
\Phi(x):=\sup\{h(x):h:E\to[-\infty,+\infty]\text{ 下半连续凸},\ h\le f\}.
\]
常数 \(0\) 是容许的，所以 \(\Phi\ge0\)；又每个 \(h\le f\)，故 \(\Phi\le f\)。逐点上确界保持下半连续性和凸性，所以 \(\Phi\) 是非负、真、下半连续凸函数，且为 \(f\) 的最大下半连续凸下界。

因 \(G\) 本身是下半连续凸且 \(G\le f\)，由 \(\Phi\) 的最大性得
\[
G\le\Phi. \tag{4.2}
\]
下面证反向。

对 \(\varphi\in E'\)，记 \(\Phi^*(\varphi)=\sup_{z\in E}[\varphi(z)-\Phi(z)]\)。由 Fenchel–Moreau 定理（\(E\) 为实 Hausdorff 局部凸空间，\(\Phi\) 为真、下半连续、凸），
\[
\Phi(x)=\sup_{\varphi\in E'}\{\varphi(x)-\Phi^*(\varphi)\}. \tag{4.3}
\]
只考虑 \(\Phi^*(\varphi)<\infty\) 的 \(\varphi\)。令 \(F=\operatorname{span}\varphi\)，\(y=q_Fx\)。Fenchel 不等式给出，对所有 \(z\in E\)，
\[
\Phi(z)\ge \varphi(z)-\Phi^*(\varphi).
\]
于是对任意满足 \(q_Fz=y\) 的 \(z\)，
\[
f(z)\ge \Phi(z)\ge \varphi(z)-\Phi^*(\varphi)
= y(\varphi)-\Phi^*(\varphi).
\]
对 \(z\) 取下确界得
\[
g_F(y)\ge y(\varphi)-\Phi^*(\varphi).
\]
右端是 \(F^*\) 上的连续仿射函数，因而是下半连续凸函数且不超过 \(g_F\)。由于 \(u_F=\bar g_F\) 是 \(g_F\) 的最大下半连续凸下界，
\[
u_F(y)\ge y(\varphi)-\Phi^*(\varphi)
=\varphi(x)-\Phi^*(\varphi).
\]
因此
\[
G(x)\ge u_F(q_Fx)\ge \varphi(x)-\Phi^*(\varphi).
\]
对 \(\varphi\) 取上确界，由 (4.3) 得
\[
G(x)\ge \Phi(x).
\]
结合 (4.2)，得到
\[
G=\Phi.
\]
于是任何下半连续凸的 \(h\le f\) 都满足 \(h\le\Phi=G\)。若 \(G_1,G_2\) 都满足这个最大性，则互相不超过，故 \(G\) 唯一。

### 扩大观测空间时的关系

设 \(F\subset K\)，\(r=r_{KF}:K^*\to F^*\)。记 \(u_H=\bar g_H\)。定义
\[
A_{K,F}(y):=\inf_{\substack{z\in K^*\\ rz=y}}u_K(z),
\qquad y\in F^*.
\]
则 \(A_{K,F}\) 非负凸（凸函数沿线性映射的下确界投影），且
\[
\boxed{\ u_F=\overline{A_{K,F}}\ } \tag{4.4}
\]
其中外层 \(\overline{\ \cdot\ }\) 表示最大下半连续凸下界。

证明如下。首先由 \(u_K\le g_K\) 和 S1，
\[
A_{K,F}(y)\le \inf_{rz=y}g_K(z)=g_F(y).
\]
所以 \(\overline{A_{K,F}}\le A_{K,F}\le g_F\)。因 \(\overline{A_{K,F}}\) 下半连续凸，而 \(u_F\) 是 \(g_F\) 的最大下半连续凸下界，故
\[
\overline{A_{K,F}}\le u_F. \tag{4.5}
\]
反过来，任取下半连续凸函数 \(h\le g_F\)，定义
\[
H(z):=h(rz),\qquad z\in K^*.
\]
则 \(H\) 下半连续凸。由 S1，
\[
H(z)=h(rz)\le g_F(rz)\le g_K(z).
\]
所以 \(H\) 是 \(g_K\) 的下半连续凸下界，从而 \(H\le u_K\)。于是对任意 \(y\in F^*\) 及任意 \(z\in r^{-1}(y)\)，
\[
h(y)=H(z)\le u_K(z).
\]
对 \(z\in r^{-1}(y)\) 取下确界，得
\[
h(y)\le A_{K,F}(y).
\]
故 \(h\le A_{K,F}\)；因 \(h\) 下半连续凸，所以
\[
h\le \overline{A_{K,F}}.
\]
取 \(h=u_F\)，得
\[
u_F\le \overline{A_{K,F}}. \tag{4.6}
\]
由 (4.5)(4.6) 得到 (4.4)。

特别地，若 \(y_K\in K^*\) 且 \(y_F=r_{KF}y_K\)，则
\[
u_F(y_F)
=\overline{A_{K,F}}(y_F)
\le A_{K,F}(y_F)
\le u_K(y_K).
\]
因此扩大观测空间时，在相容点上正则化投影值不下降：
\[
\boxed{\ u_F(q_Fx)\le u_K(q_Kx)\qquad(F\subset K).\ } \tag{4.7}
\]
所以 \(\sup_F u_F(q_Fx)\) 是沿有限维子空间包含关系的有向上确界；若取任意共尾子族 \(\mathcal A\)（即每个 \(F\) 都包含于某个 \(K\in\mathcal A\)），则
\[
G(x)=\sup_{F\in\mathcal A}u_F(q_Fx).
\]
也就是说，最终恢复 \(G\) 不因把观测空间扩大或换成共尾族而改变。

---

## S5　闭成本的有限投影

**结论：不必。即使 \(E=\mathbb R^2\)、\(f\) 下半连续凸、非负且真，某个有限维 \(F\) 的 \(g_F\) 仍可能不下半连续。**

反例。令
\[
C:=\{(x,y)\in\mathbb R^2:x>0,\ xy\ge1\},
\]
并令
\[
f(x,y)=
\begin{cases}
0,&(x,y)\in C,\\
+\infty,&(x,y)\notin C.
\end{cases}
\]
即 \(f\) 是 \(C\) 的指示函数。

先验证 \(C\) 闭凸。它是函数
\[
\psi(x)=
\begin{cases}
1/x,&x>0,\\
+\infty,&x\le0
\end{cases}
\]
的上图：
\[
C=\{(x,y):y\ge\psi(x)\}.
\]
在 \((0,\infty)\) 上 \(\psi''(x)=2/x^3>0\)，且 \(x\downarrow0\) 时 \(\psi(x)\to+\infty\)，故 \(\psi\) 为下半连续凸函数，\(C\) 闭凸。于是
\[
\operatorname{epi}_{\mathbb R}f=C\times[0,+\infty)
\]
闭凸，故 \(f\) 下半连续、凸、非负且真。

取一维有限维子空间
\[
F=\mathbb R e_1^*\subset(\mathbb R^2)^*,
\]
其中 \(e_1^*(x,y)=x\)。于是 \(F^*\cong\mathbb R\)，且
\[
q_F(x,y)=x e_1^*.
\]
对 \(t\in\mathbb R\)，
\[
g_F(t e_1^*)=\inf_{\eta\in\mathbb R}f(t,\eta).
\]
若 \(t>0\)，取 \(\eta\ge1/t\)，则 \((t,\eta)\in C\)，故 \(g_F(t e_1^*)=0\)。若 \(t\le0\)，则不存在 \(\eta\) 使 \((t,\eta)\in C\)，故 \(g_F(t e_1^*)=+\infty\)。因此
\[
g_F(t e_1^*)=
\begin{cases}
0,&t>0,\\
+\infty,&t\le0.
\end{cases}
\]
它在 \(t=0\) 处值为 \(+\infty\)，而沿 \(t\downarrow0\) 有 \(g_F(t e_1^*)=0\)，故
\[
g_F(0)=+\infty>0=\liminf_{t\to0+}g_F(t e_1^*),
\]
不满足下半连续性。故 \(g_F\) 不必下半连续。

---

## S6　恢复与投影的精确关系

### 1. \(G=f\) 当且仅当 \(f\) 下半连续

由 S4 的结论，\(G=\bar f\)，即 \(f\) 的最大下半连续凸下界。

若 \(f\) 下半连续，则 \(f\) 本身是下半连续凸函数且 \(f\le f\)，故最大下界至少为 \(f\)；另一方面最大下界不超过 \(f\)，所以
\[
G=f.
\]
反之，若 \(G=f\)，由 S4 构造可知 \(G\) 下半连续，故 \(f\) 下半连续。

### 2. 精确投影关系

设 \(F\subset K\) 为有限维子空间，\(r=r_{KF}:K^*\to F^*\)。断言
\[
\boxed{\
\bar g_F(y)
=\overline{\left(y'\mapsto
\inf_{\substack{z\in K^*\\ rz=y'}}\bar g_K(z)\right)}(y),
\qquad y\in F^*.
\ } \tag{6.1}
\]
这里外层 \(\overline{\ \cdot\ }\) 是对 \(F^*\) 上的函数取最大下半连续凸下界。

这是 S4 中 (4.4) 的直接改写：取 \(u_H=\bar g_H\) 即得
\[
\bar g_F(y)=\overline{\inf_{rz=y}\bar g_K(z)}.
\]
该证明只用到 S1 与 \(\bar u\) 的最大性，在 S6 的共同设定下完全适用。为完整起见再列出关键两步。

令
\[
A(y):=\inf_{\substack{z\in K^*\\ rz=y}}\bar g_K(z).
\]
首先，因 \(\bar g_K\le g_K\)，
\[
A(y)\le \inf_{rz=y}g_K(z)=g_F(y).
\]
所以 \(\bar A\le A\le g_F\)。由于 \(\bar A\) 下半连续凸，而 \(\bar g_F\) 是 \(g_F\) 的最大下半连续凸下界，故
\[
\bar A\le \bar g_F. \tag{6.2}
\]
反过来，取 \(h=\bar g_F\)，定义 \(H(z)=h(rz)\)。则 \(H\) 下半连续凸，且由 S1，
\[
H(z)=\bar g_F(rz)\le g_F(rz)\le g_K(z).
\]
故 \(H\) 是 \(g_K\) 的下半连续凸下界，从而 \(H\le\bar g_K\)。于是对任意 \(z\in r^{-1}(y)\)，
\[
\bar g_F(y)=h(y)=H(z)\le\bar g_K(z),
\]
对 \(z\) 取下确界得
\[
\bar g_F(y)\le A(y).
\]
因 \(\bar g_F\) 下半连续凸，故
\[
\bar g_F\le\bar A. \tag{6.3}
\]
由 (6.2)(6.3) 得
\[
\bar g_F=A_{K,F}
\]
的上图闭包，即 (6.1)。

等价的上图说法是
\[
\operatorname{epi}\bar g_F
=
\overline{(r_{KF}\times\mathrm{id}_{\mathbb R})
(\operatorname{epi}\bar g_K)}. \tag{6.4}
\]
外层 bar 正是在取这个投影的闭包。

### 3. 最外层 bar 不能总省去

**结论：不能总省去。**

沿用 S5 中的例子：
\[
E=\mathbb R^2,\qquad
C=\{(x,y):x>0,\ xy\ge1\},\qquad
f=\mathbf 1_C^{+\infty},
\]
取
\[
K=E'=\mathbb R^2,\qquad
F=\mathbb R e_1^*.
\]
这里 \(K\) 是有限维的，\(F\subset K\)。

因 \(K=E'\)，映射 \(q_K:E\to K^*\) 是线性同构，故在自然等同下
\[
g_K=f.
\]
而 \(f\) 已下半连续凸，所以
\[
\bar g_K=f.
\]
令
\[
A(t):=\inf_{\eta\in\mathbb R}f(t,\eta),\qquad t\in\mathbb R\cong F^*.
\]
则
\[
A(t)=
\begin{cases}
0,&t>0,\\
+\infty,&t\le0.
\end{cases}
\]
于是
\[
A(0)=+\infty.
\]
但
\[
\bar A(t)=
\begin{cases}
0,&t\ge0,\\
+\infty,&t<0,
\end{cases}
\]
故
\[
\bar A(0)=0.
\]
由 (6.1)，\(\bar g_F(0)=\bar A(0)=0\)。因此在 \(t=0\) 处
\[
\bar g_F(0)=0\neq+\infty=A(0).
\]
所以
\[
\bar g_F
\neq
\inf_{r_{KF}z=\,\cdot}\bar g_K(z)
\]
一般情况下不成立；(6.1) 最外层的 bar 不能省略。

事实上，当且仅当投影
\[
(r_{KF}\times\mathrm{id}_{\mathbb R})(\operatorname{epi}\bar g_K)
\]
在 \(F^*\times\mathbb R\) 中已经闭时，最外层 bar 才可以省去；一般的闭凸上图经有限维线性投影后不一定仍闭，S5/S6 中的 \(C\) 正是这样的例子。