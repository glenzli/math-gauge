# 凸成本记录、紧性与闭上图恢复：答卷

S1 到 S6 全部作答，没有未完成部分。各题结论：
- **S1**：成立，证明不需要纤维下确界取到。
- **S2、S3**：成立。
- **S4**：可以构造，取 $G=\sup_F\overline{g_F}\circ q_F$。
- **S5**：不一定，给出反例。
- **S6**：恒等式成立；最外层 bar 不能总省去，给出反例。

**记号。**
- $\mathcal F$ 是 $E'$ 的全部有限维子空间，按包含关系构成定向集（$F_1,F_2\subset F_1+F_2$），且 $\{0\}\in\mathcal F$。
- $\operatorname{epi}u:=\operatorname{epi}_{\mathbb R}(u)$，$\operatorname{dom}u:=\{u<+\infty\}$。
- $\iota_C$ 是集合 $C$ 的指示函数：在 $C$ 上取 $0$，其余取 $+\infty$。
- 对线性映射 $A:X\to Y$ 和 $u\ge0$，令 $(A_\#u)(y):=\inf\{u(x):Ax=y\}$，约定 $\inf\varnothing=+\infty$。于是 $g_F=(q_F)_\#f$。

## 0 预备事实

**P0.** 取 $F$ 的一组基 $\varphi_1,\dots,\varphi_n$。
- 映射 $y\mapsto(y(\varphi_i))_i$ 是线性同构 $F^*\to\mathbb R^n$。有限维空间上的 Hausdorff 线性拓扑唯一，所以它是同胚。
- 在这组坐标下 $q_Fx=(\varphi_i(x))_i$，因此 $q_F$ 连续线性，$F^*$ 是 Hausdorff 空间。
- $r_{KF}$ 以及 $F^*$ 上的线性泛函都连续。
- 对 $\varphi\in F\subset K$，$(r_{KF}q_Kx)(\varphi)=\varphi(x)=(q_Fx)(\varphi)$。故 $q_F=r_{KF}\circ q_K$，且 $r_{KF}r_{LK}=r_{LF}$。

**P1.** 设 $u$ 定义在拓扑空间上。
- (a) $\operatorname{epi}u$ 闭，当且仅当对每个实数 $c$，$\{u\le c\}$ 闭。
  - "⟹"：$\{u\le c\}\times\{c\}=\operatorname{epi}u\cap(X\times\{c\})$。
  - "⟸"：设 $u(x)>t$，取实数 $s\in(t,u(x))$。$U=X\setminus\{u\le s\}$ 是 $x$ 的开邻域，而 $U\times(-\infty,s)$ 是 $(x,t)$ 的邻域，与 $\operatorname{epi}u$ 不交。
- (b) $u\le v$ 当且仅当 $\operatorname{epi}v\subset\operatorname{epi}u$。"⟸"：若 $v(x)<\infty$，则对一切实数 $t\ge v(x)$ 有 $u(x)\le t$。
- (c) $\operatorname{epi}(\sup_iu_i)=\bigcap_i\operatorname{epi}u_i$。因此下半连续凸函数族的上确界仍下半连续凸。
- (d) 设 $A$ 连续线性，$w$ 下半连续凸。则 $\operatorname{epi}(w\circ A)=(A\times\mathrm{id})^{-1}(\operatorname{epi}w)$ 闭凸。

**P2（闭包与 bar）.** 设 $X$ 是拓扑向量空间，$u:X\to[0,\infty]$ 凸。令 $\operatorname{cl}u(x):=\inf\{t\in\mathbb R:(x,t)\in\overline{\operatorname{epi}u}\}$。则：
- (i) $\operatorname{epi}\operatorname{cl}u=\overline{\operatorname{epi}u}$；
- (ii) $\operatorname{cl}u$ 下半连续、凸，且 $0\le\operatorname{cl}u\le u$；
- (iii) 每个满足 $h\le u$ 的下半连续 $h:X\to[-\infty,\infty]$ 都满足 $h\le\operatorname{cl}u$。

所以最大下半连续凸下界 $\bar u$ 存在，且 $\bar u=\operatorname{cl}u$。此外 $u\le v\Rightarrow\bar u\le\bar v$；$\bar u=u$ 当且仅当 $u$ 下半连续。

证明：
- 竖直平移 $(x,t)\mapsto(x,t+s)$（$s\ge0$）是同胚，并把 $\operatorname{epi}u$ 映入自身，所以闭包是向上封闭的。
- (i)：若 $\operatorname{cl}u(x)\le t$，则对每个 $\varepsilon>0$ 有 $(x,t+\varepsilon)\in\overline{\operatorname{epi}u}$。令 $\varepsilon\to0$，由闭性得 $(x,t)\in\overline{\operatorname{epi}u}$。另一方向由定义直接得到。
- (ii)：凸集的闭包是凸的。$\operatorname{epi}u\subset X\times[0,\infty)$，后者是闭集，所以闭包也在其中，即 $\operatorname{cl}u\ge0$。
- (iii)：由 P1(b)，$\operatorname{epi}u\subset\operatorname{epi}h$，后者闭，所以 $\overline{\operatorname{epi}u}\subset\operatorname{epi}h$，即 $h\le\operatorname{cl}u$。
- 单调性：若 $u\le v$，则 $\bar u\le u\le v$ 是 $v$ 的下半连续凸下界，故 $\bar u\le\bar v$。

**P3（Hahn–Banach，标准定理）.**
- (a) 在 Hausdorff 局部凸空间中，$E'$ 分离点。
- (b) 在局部凸空间中，闭凸集 $A$ 与点 $p\notin A$ 可严格分离：存在 $L\in X'$ 使 $L(p)>\sup_AL$。
- (c) $E\times\mathbb R$ 是局部凸空间，其连续线性泛函恰为 $\varphi(x)+\beta s$，其中 $\varphi\in E'$，$\beta\in\mathbb R$。

## S1

**命题 1.** 设 $A:X\to Y$、$B:Y\to Z$ 线性，$u:X\to[0,\infty]$ 凸。则：
- (i) $A_\#u\ge0$，且 $A_\#u(Ax)\le u(x)$；
- (ii) $A_\#u$ 凸；
- (iii) $(BA)_\#u=B_\#(A_\#u)$；
- (iv) $u\le v\Rightarrow A_\#u\le A_\#v$。

证明：
- (i)：$A_\#u$ 是 $[0,\infty]$ 中数的下确界；且 $x$ 落在 $Ax$ 的纤维里。
- (ii)：设 $(y_i,t_i)\in\operatorname{epi}A_\#u$，$\lambda\in[0,1]$，$\varepsilon>0$。由下确界的定义，存在 $x_i$ 使 $Ax_i=y_i$ 且 $u(x_i)<t_i+\varepsilon$，即 $(x_i,t_i+\varepsilon)\in\operatorname{epi}u$。由 $\operatorname{epi}u$ 凸，$((1-\lambda)x_1+\lambda x_2,\ (1-\lambda)t_1+\lambda t_2+\varepsilon)\in\operatorname{epi}u$。又 $A((1-\lambda)x_1+\lambda x_2)=(1-\lambda)y_1+\lambda y_2$，故 $A_\#u((1-\lambda)y_1+\lambda y_2)\le(1-\lambda)t_1+\lambda t_2+\varepsilon$。令 $\varepsilon\to0$ 即得凸性。
- (iii)：$(BA)^{-1}(w)=\bigcup_{By=w}A^{-1}(y)$。
  - "≤"：对 $By=w$、$Ax=y$，有 $(BA)_\#u(w)\le u(x)$。先对 $x$、再对 $y$ 取下确界。
  - "≥"：对 $BAx=w$，有 $B_\#(A_\#u)(w)\le A_\#u(Ax)\le u(x)$。
  - 纤维为空时两边都是 $+\infty$。
- (iv)：逐纤维比较即可。∎

**应用。** 取 $u=f$、$A=q_F$：$g_F$ 非负且凸；若 $f(x_0)<\infty$，则 $g_F(q_Fx_0)\le f(x_0)<\infty$。再取 $A=q_K$、$B=r_{KF}$，由 P0 有 $BA=q_F$，于是
$$g_F(y)=\inf_{r_{KF}z=y}g_K(z).$$
推论：$g_F\circ r_{KF}\le g_K$，从而 $g_F\circ q_F\le g_K\circ q_K\le f$。

**不需要纤维下确界取到。** 证明只用到下确界的 $\varepsilon$-近似点和纤维的集合分解，没有选取任何极小点，也没有用到拓扑。这一点必须如此，因为在共同设定下下确界可能取不到。例如 $E=\mathbb R^2$，$f=e^{x_2}$，$F=\mathbb Re_1^*$：此时 $g_F\equiv0$，但在任何点都取不到。

## S2（附加假设只在 S2、S3 中使用）

设 $S_c=\{f\le c\}$。由 $f$ 下半连续和 P1(a)，$S_c$ 闭；按假设它也紧。

**下确界取到。** 设 $m=g_F(y)<\infty$。
1. 纤维 $\Pi=q_F^{-1}(y)$ 是闭集：$q_F$ 连续，且 $F^*$ 是 Hausdorff 空间。
2. 令 $A_n=\Pi\cap S_{m+1/n}$。由下确界的定义它非空；它是闭集、关于 $n$ 递减，且都含于紧集 $S_{m+1}$。
3. 由有限交性质，存在 $x\in\bigcap_nA_n$。于是 $q_Fx=y$，且 $m\le f(x)\le m$。

**$g_F$ 下半连续。** 对每个实数 $c$，$\{g_F\le c\}=q_F(S_c)$：
- "⊇"：由命题 1(i)。
- "⊆"：由上一步的下确界取到。

紧集在连续映射下的像是紧的，在 Hausdorff 空间 $F^*$ 中紧集闭。由 P1(a)，$g_F$ 下半连续。∎

## S3

令 $M_F:=q_F^{-1}(y_F)\cap S_c$。
1. **非空。** S2 的条件成立且 $g_F(y_F)\le c<\infty$。由 S2 存在 $x_F$ 使 $q_Fx_F=y_F$ 且 $f(x_F)=g_F(y_F)\le c$，所以 $x_F\in M_F$。
2. **闭且在紧集中。** $M_F$ 是紧集 $S_c$ 中的闭集。
3. **单调。** 若 $F\subset K$ 且 $x\in M_K$，则 $q_Fx=r_{KF}q_Kx=r_{KF}y_K=y_F$。所以 $M_K\subset M_F$。
4. **有限交性质。** $M_{F_1}\cap\dots\cap M_{F_n}\supset M_{F_1+\dots+F_n}\neq\varnothing$。

由紧性，$\bigcap_FM_F\ne\varnothing$。其中任一点 $x$ 都满足：对一切 $F$ 有 $q_Fx=y_F$，且 $f(x)\le c$。

**唯一性。** 若 $x'$ 也满足 $q_Fx'=y_F$ 对一切 $F$ 成立，则对每个 $\varphi\in E'$，取 $F=\mathbb R\varphi$，得 $\varphi(x)=\varphi(x')$。由 P3(a)（$E$ 是 Hausdorff 局部凸空间），$x=x'$。所以 $\bigcap_FM_F=\{x\}$；唯一性甚至不需要成本约束。

**补充：$x$ 是网 $(x_F)$ 的极限。**
- 设 $\bar x$ 是网 $(x_F)$ 在紧集 $S_c$ 中的任一聚点。对 $F\supset\mathbb R\varphi$，有 $\varphi(x_F)=y_{\mathbb R\varphi}(\varphi)$，为常数。
- 由 $\varphi$ 连续，$\varphi(\bar x)=y_{\mathbb R\varphi}(\varphi)$。再由相容性，对一切 $F$ 有 $q_F\bar x=y_F$，且 $\bar x\in S_c$。
- 于是 $\bar x=x$。紧空间中只有唯一聚点的网收敛，所以 $x=\lim_Fx_F$。

**补充：$f(x)=\sup_Fg_F(y_F)$。**
- 由命题 1(i)，$f(x)\ge g_F(y_F)$ 对一切 $F$ 成立。
- 反过来，把 $c$ 换成 $\sup_Fg_F(y_F)$ 重复上面的构造，再用唯一性。

## S4

**结论：可以。** 取
$$G(x):=\sup_{F\in\mathcal F}\overline{g_F}(q_Fx).$$
这里用 P2，因为 $F^*$ 是拓扑向量空间，且由 S1 知 $g_F$ 非负凸。

**(1) $G$ 下半连续、凸，且 $0\le G\le f$。**
- 由 P2、P1(d)、P1(c)，$G$ 下半连续凸。
- $\overline{g_F}(q_Fx)\le g_F(q_Fx)\le f(x)$。

**(2) 最大性。** 设 $h$ 下半连续、凸，且 $h\le f$。取 $x_0$ 和实数 $t<h(x_0)$。

先做分离：
- 取 $x_1$ 使 $f(x_1)<\infty$。则对一切 $s\ge f(x_1)$，$(x_1,s)\in\operatorname{epi}h$，所以 $\operatorname{epi}h$ 是非空闭凸集，且 $(x_0,t)\notin\operatorname{epi}h$。
- 由 P3(b)(c)，存在 $\varphi\in E'$ 和 $\beta\in\mathbb R$，使 $\varphi(x_0)+\beta t>\sigma:=\sup_{\operatorname{epi}h}(\varphi(x)+\beta s)$。
- 让 $(x_1,s)$ 中 $s\to\infty$，得 $\beta\le0$。
- 令 $F=\mathbb R\varphi$。

*情形 $\beta<0$。*
1. 令 $a(x)=(\varphi(x)-\sigma)/(-\beta)$。由分离不等式，$(x,s)\in\operatorname{epi}h\Rightarrow s\ge a(x)$。
2. 因此 $h>-\infty$ 处处成立，且 $a\le h\le f$。另外 $t<a(x_0)$。
3. 在 $F^*$ 上令 $\tilde a(y)=(y(\varphi)-\sigma)/(-\beta)$。它是连续仿射函数，且 $\tilde a\circ q_F=a$。
4. 于是 $g_F\ge\tilde a$。由 P2(iii)，$\tilde a\le\overline{g_F}$。
5. 所以 $G(x_0)\ge a(x_0)>t$。

*情形 $\beta=0$。*
1. 在 $\operatorname{dom}h\supset\operatorname{dom}f$ 上有 $\varphi\le\sigma$，而 $\varphi(x_0)>\sigma$。
2. 令 $H=\{y:y(\varphi)\le\sigma\}$，它是闭集，且 $\operatorname{dom}g_F\subset H$。
3. 因此 $\iota_H\le g_F$。由 P2(iii)，$\iota_H\le\overline{g_F}$。
4. 而 $q_Fx_0\notin H$，所以 $G(x_0)=+\infty>t$。

两种情形都有 $G(x_0)>t$。由于 $t<h(x_0)$ 任意，得 $h\le G$。

**(3) 唯一性。** 满足 (1)(2) 的函数只有一个：两个这样的函数互为对方的竞争函数。因此 $G=\bar f$。

**扩大观测空间时的关系**（设 $F\subset K$）：
- **(a)** 由 P1(d)，$\overline{g_F}\circ r_{KF}$ 下半连续凸，且 $\le g_F\circ r_{KF}\le g_K$。由 P2(iii)，
$$\overline{g_F}\circ r_{KF}\le\overline{g_K},\qquad\text{从而}\qquad\overline{g_F}\circ q_F\le\overline{g_K}\circ q_K\le G.$$
- **(b)** 所以 $(\overline{g_F}\circ q_F)_F$ 是单调不减的网，且 $G=\lim_{F\uparrow}\overline{g_F}\circ q_F$。上确界可以只取在任一共尾子族上。也可以只取在一维子空间上：(2) 的证明只用到 $F=\mathbb R\varphi$，再由 (3) 得 $G=\sup_\varphi\overline{g_{\mathbb R\varphi}}\circ q_{\mathbb R\varphi}$。
- **(c)** 由 (a) 和命题 1(iii)(iv)：
$$\overline{g_F}\le(r_{KF})_\#\overline{g_K}\le(r_{KF})_\#g_K=g_F.$$
- **(d)** $\overline{g_F}\le(q_F)_\#G\le g_F$，因此 $\overline{(q_F)_\#G}=\overline{g_F}$：$G$ 和 $f$ 的闭记录相同。

**闭包不能省。** 若 $\dim E<\infty$，则 $q_{E'}$ 是双射，所以 $\sup_Fg_F\circ q_F=f$。取 $f=\iota_{(0,1)}$（$E=\mathbb R$），这个函数不下半连续。

## S5

**结论：不一定。**

**反例。** 令 $C=\{x_1>0,\ x_1x_2\ge1\}$，$f=\iota_C$。
- **$C$ 凸。** $C$ 是 $(0,\infty)$ 上凸函数 $1/x_1$ 的上图。
- **$C$ 闭。** 若 $C\ni(a_n,b_n)\to(a,b)$，则 $a\ge0$ 且 $ab\ge1$，所以 $a>0$。
- **$f$ 满足题设。** $\operatorname{epi}f=C\times[0,\infty)$ 闭且凸；$f(1,1)=0$ 有限。

**计算 $g_F$。** 取 $\varphi=e_1^*$，$F=\mathbb R\varphi$，并用同胚 $y\mapsto y(\varphi)=s$ 把 $F^*$ 等同于 $\mathbb R$。
- 当 $s>0$ 时，$(s,1/s)\in C$，所以 $g_F(s)=0$。
- 当 $s\le0$ 时，纤维与 $C$ 不交，所以 $g_F(s)=+\infty$。

因此 $g_F=\iota_{(0,\infty)}$。其下水平集 $\{g_F\le0\}=(0,\infty)$ 不闭；具体地，$(1/n,0)\in\operatorname{epi}g_F$ 收敛到 $(0,0)\notin\operatorname{epi}g_F$。由 P1(a)，$g_F$ 不下半连续。

这里 $S_0=C$ 不紧，所以与 S2 不矛盾。

## S6

**(a) $G=f$ 当且仅当 $f$ 下半连续。**
- 若 $G=f$：由 S4(1)，$G$ 下半连续，所以 $f$ 下半连续。
- 若 $f$ 下半连续：$f$ 凸、下半连续且 $f\le f$，所以它是 S4(2) 的竞争函数，得 $f\le G\le f$。∎

**(b) 恒等式。** 令 $\psi(y)=\inf_{r_{KF}z=y}\overline{g_K}(z)$。
1. 由 P2，$\overline{g_K}$ 非负凸；由命题 1，$\psi$ 非负凸，所以 $\bar\psi$ 有定义。
2. 由 S4 的 (c)（它只用到共同设定），$\overline{g_F}\le\psi\le g_F$。
3. 由 $\psi\le g_F$ 和 P2 的单调性：$\bar\psi\le\overline{g_F}$。
4. 由 $\overline{g_F}\le\psi$ 和 P2(iii)：$\overline{g_F}\le\bar\psi$。

故 $\overline{g_F}=\bar\psi$。∎

**(c) 最外层 bar 不能总省去。** 沿用 S5 的例子，它在共同设定之内；取 $K=E'$。
1. $q_K$ 是有限维空间之间的线性双射，因而是同胚，所以 $g_K=f\circ q_K^{-1}$。
2. 由 P1(d)，$g_K$ 下半连续，因此 $\overline{g_K}=g_K$。
3. 于是 $\psi=(r_{KF})_\#g_K=g_F$（由 S1）。
4. 在 $y=0$ 处：$\psi(0)=+\infty$，而 $\overline{g_F}=\iota_{[0,\infty)}$ 给出 $\overline{g_F}(0)=0$，两者不等。

只有当 $\psi$ 本身下半连续时，外层 bar 才能省去。例如在 S2 的附加假设下：此时 $\overline{g_K}=g_K$，且 $\psi=g_F$ 下半连续。