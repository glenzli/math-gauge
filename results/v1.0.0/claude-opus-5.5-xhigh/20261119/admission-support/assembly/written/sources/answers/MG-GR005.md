# 凸成本记录、紧性与闭上图恢复：S1–S6 解答

**结论一览**
- S1、S2、S3：已证明。S1 的证明不需要纤维下确界取到。
- S4：可以构造。取 $G(x)=\sup_F\bar g_F(q_Fx)$，它恰好是 $f$ 的最大下半连续凸下界。观测空间扩大时，$\bar g_F\circ q_F$ 关于 $F$ 单调不减。
- S5：不一定。有反例。
- S6：两个等式都已证明。最外层的 bar 不能总省去，有反例。

全部阶段均已作答，没有未完成的部分。

**记号.** 对 $u:X\to[-\infty,+\infty]$，记 $\operatorname{epi}u:=\operatorname{epi}_{\mathbb R}(u)$，$\operatorname{dom}u=\{u<+\infty\}$。约定 $\inf\varnothing=+\infty$。

## 预备

**(P0) 拓扑与映射.** 取有限维 $F\subset E'$ 的基 $\varphi_1,\dots,\varphi_n$。映射 $y\mapsto(y(\varphi_i))_i$ 是线性同构 $F^*\to\mathbb R^n$，而 $F^*$ 的有限维拓扑（唯一的 Hausdorff 向量拓扑）就是使它成为同胚的拓扑。

- $q_F$ 的坐标是 $x\mapsto\varphi_i(x)$，每个 $\varphi_i$ 都在 $E'$ 中，所以 $q_F:E\to F^*$ 是连续线性映射。
- 当 $F\subset K$ 时，$r_{KF}$ 是有限维空间之间的线性映射，因此连续。
- 对 $\varphi\in F$，$(r_{KF}q_Kx)(\varphi)=\varphi(x)=(q_Fx)(\varphi)$，所以 $r_{KF}\circ q_K=q_F$。

**引理 A.** 设 $X$ 是拓扑空间，$u:X\to[-\infty,\infty]$。
1. 若 $(x,t)\in\operatorname{epi}u$ 且 $s\ge t$，则 $(x,s)\in\operatorname{epi}u$。
2. $\operatorname{epi}u$ 闭，当且仅当对每个实数 $c$，$\{u\le c\}$ 闭。

*证.* 第 1 条显然。
- (⇒) $\{u\le c\}\times\{c\}=\operatorname{epi}u\cap(X\times\{c\})$，是闭集。
- (⇐) 设 $(x,t)\in\overline{\operatorname{epi}u}$ 但 $u(x)>t$。取实数 $s$ 使 $t<s<u(x)$。则 $(X\setminus\{u\le s\})\times(-\infty,s)$ 是含 $(x,t)$ 的开集，所以它含某个 $(x',t')\in\operatorname{epi}u$。于是 $u(x')\le t'<s$，与 $x'\notin\{u\le s\}$ 矛盾。∎

**引理 B.**
1. 若 $A:X\to Y$ 是连续线性映射，$u$ 在 $Y$ 上下半连续且凸，则 $u\circ A$ 下半连续且凸。理由：$\operatorname{epi}(u\circ A)=(A\times\mathrm{id})^{-1}(\operatorname{epi}u)$。
2. 一族下半连续凸函数的逐点上确界仍下半连续且凸。理由：$\operatorname{epi}\sup_iu_i=\bigcap_i\operatorname{epi}u_i$。
3. 连续仿射函数下半连续且凸。

**引理 C（闭包 bar）.** 设 $X$ 是拓扑向量空间（本文只用于 $X=E$ 或 $F^*$），$u:X\to[0,\infty]$ 凸。定义
$$\bar u(x):=\inf\{t\in\mathbb R:(x,t)\in\overline{\operatorname{epi}u}\}.$$
则以下各条成立。
- (a) $\operatorname{epi}\bar u=\overline{\operatorname{epi}u}$。
- (b) $\bar u$ 下半连续且凸，且 $0\le\bar u\le u$。
- (c) 若 $h:X\to[-\infty,\infty]$ 下半连续且 $h\le u$，则 $h\le\bar u$。因此 $\bar u$ 是 S6 所说的"最大下半连续凸下界"，并且唯一。
- (d) 若 $u\le v$，则 $\bar u\le\bar v$；若 $u$ 下半连续，则 $\bar u=u$。
- (e) $\bar u(x)=\sup_{U\ni x}\inf_Uu$，其中 $U$ 取遍 $x$ 的邻域。

*证.*
- (a) 平移 $(x,t)\mapsto(x,t+\delta)$（$\delta\ge0$）是同胚，并把 $\operatorname{epi}u$ 映入自身，所以 $\overline{\operatorname{epi}u}$ 向上封闭。若 $\bar u(x)\le t$，则对每个 $s>t$ 都有 $(x,s)\in\overline{\operatorname{epi}u}$；由闭性得 $(x,t)\in\overline{\operatorname{epi}u}$。反向包含由定义直接得到。
- (b) 凸集的闭包仍是凸集。$\operatorname{epi}u\subset X\times[0,\infty)$，后者闭，所以 $\bar u\ge0$。又 $\operatorname{epi}u\subset\overline{\operatorname{epi}u}$，所以 $\bar u\le u$。
- (c) $\operatorname{epi}u\subset\operatorname{epi}h$，而后者闭，所以 $\operatorname{epi}\bar u\subset\operatorname{epi}h$。
- (d) 由 (c) 直接得到。
- (e) 由 (a)，$(x,t)\in\overline{\operatorname{epi}u}$ 当且仅当对所有 $U$ 和 $\varepsilon>0$，存在 $x'\in U$ 使 $u(x')<t+\varepsilon$。这等价于 $\sup_U\inf_Uu\le t$。∎

**引理 D（像函数）.** 设 $X,Y$ 是向量空间，$A:X\to Y$ 线性，$u:X\to[0,\infty]$ 凸。令 $(Au)(y):=\inf\{u(x):Ax=y\}$。则 $Au\ge0$ 且凸，并且 $\operatorname{dom}Au=A(\operatorname{dom}u)$。

*证.* 非负性显然。$Au(Ax)\le u(x)$，且 $Au(y)<\infty$ 迫使纤维中有某点 $u<\infty$，所以 $\operatorname{dom}Au=A(\operatorname{dom}u)$。

凸性：设 $(y_i,t_i)\in\operatorname{epi}Au$，$\lambda\in[0,1]$，$\varepsilon>0$。因为 $Au(y_i)\le t_i<t_i+\varepsilon$，存在 $x_i$ 使 $Ax_i=y_i$ 且 $u(x_i)<t_i+\varepsilon$，即 $(x_i,t_i+\varepsilon)\in\operatorname{epi}u$。由 $\operatorname{epi}u$ 的凸性和 $A$ 的线性，
$$Au(\lambda y_1+(1-\lambda)y_2)\le u(\lambda x_1+(1-\lambda)x_2)\le\lambda t_1+(1-\lambda)t_2+\varepsilon.$$
令 $\varepsilon\to0$ 即得。∎

## S1

由定义 $g_F=q_Ff$（引理 D 的记号）。在引理 D 中取 $X=E$，$Y=F^*$，$A=q_F$，$u=f$：$q_F$ 线性，$f\ge0$ 且凸，条件满足。因此 $g_F\ge0$ 且凸。

取 $x_0$ 使 $f(x_0)<\infty$，则 $g_F(q_Fx_0)\le f(x_0)<\infty$，所以 $g_F$ 至少在一点有限。

**塔性质.** 由 $q_F=r_{KF}q_K$，
$$q_F^{-1}(y)=\bigsqcup_{z:\,r_{KF}z=y}q_K^{-1}(z).$$
对集合族 $S_z$，在 $[0,\infty]$ 中有 $\inf\bigcup_zS_z=\inf_z\inf S_z$：每个元素都不小于它所在的 $\inf S_z$，而每个 $S_z$ 都含于并集。约定 $\inf\varnothing=+\infty$ 时，这对空纤维和空指标集同样成立。所以
$$g_F(y)=\inf_{r_{KF}z=y}g_K(z).$$

**是否需要纤维下确界取到：不需要.** 凸性只用了 $\varepsilon$-近似极小点，塔性质只用了"并集上的下确界等于各部分下确界的下确界"这一集合恒等式。一般情形下下确界也确实取不到。例：$E=\mathbb R^2$，$f(a,b)=e^b$，$F=\operatorname{span}\{(a,b)\mapsto a\}$。此时 $g_F\equiv0$，但没有任何点使 $f=0$。

## S2

设 $g_F(y)=m<\infty$。对 $c\in(m,m+1]$，令
$$A_c=\{f\le c\}\cap q_F^{-1}(y).$$
- 由于 $\inf<c$，$A_c$ 非空。
- $f$ 下半连续，由引理 A 知 $\{f\le c\}$ 闭；$q_F$ 连续（P0），且 $F^*$ 中单点集闭，所以 $q_F^{-1}(y)$ 闭。因此 $A_c$ 是 $A_{m+1}$ 中的闭集。
- $A_{m+1}$ 是紧集 $\{f\le m+1\}$ 的闭子集，因而紧。

这族集合按包含全序，所以有有限交性质，于是 $\bigcap_cA_c\ne\varnothing$。任取其中一点 $x$，有 $q_Fx=y$ 且 $f(x)\le m=g_F(y)\le f(x)$。所以下确界在 $x$ 处取到。

**下半连续性.** 对实数 $c$，有 $\{g_F\le c\}=q_F(\{f\le c\})$。
- "⊃"：若 $f(x)\le c$，则 $g_F(q_Fx)\le f(x)\le c$。
- "⊂"：若 $g_F(y)\le c<\infty$，由上段取到 $x$，使 $q_Fx=y$ 且 $f(x)=g_F(y)\le c$。

右边是紧集在连续映射下的像，因而是 Hausdorff 空间 $F^*$ 中的紧集，故闭。由引理 A，$g_F$ 下半连续；凸性已由 S1 得到。

## S3

**存在性.** 对每个有限维 $F$，令
$$A_F=\{x:q_Fx=y_F,\ f(x)\le c\}.$$
- 由 S2（其条件即本阶段条件），因为 $g_F(y_F)\le c<\infty$，下确界取到，所以 $A_F\ne\varnothing$。
- 同 S2 的理由，$A_F$ 是紧集 $\{f\le c\}$ 的闭子集。
- 若 $F\subset K$ 且 $x\in A_K$，则 $q_Fx=r_{KF}q_Kx=r_{KF}y_K=y_F$，所以 $A_K\subset A_F$。
- 于是 $A_{F_1}\cap\dots\cap A_{F_n}\supset A_{F_1+\dots+F_n}\ne\varnothing$，其中 $F_1+\dots+F_n$ 仍是有限维的。

这是紧集中具有有限交性质的闭集族，所以 $\bigcap_FA_F\ne\varnothing$。任取 $x\in\bigcap_FA_F$，则对所有 $F$ 有 $q_Fx=y_F$，且 $f(x)\le c$。

**唯一性.** 设 $x,x'$ 都满足对所有 $F$ 有 $q_Fx=q_Fx'=y_F$。对任意 $\varphi\in E'$，取 $F=\operatorname{span}\{\varphi\}$，得
$$\varphi(x)=y_F(\varphi)=\varphi(x').$$
$E$ 是 Hausdorff 局部凸空间，由 Hahn–Banach 定理 $E'$ 分离点，所以 $x=x'$。唯一性甚至不需要 $f(x)\le c$ 这一条件。

## S4

**结论：可以.** 构造
$$G(x):=\sup_{F\subset E'\ \text{有限维}}\ \bar g_F(q_Fx).$$
由 S1，$g_F$ 非负且凸，因此 $\bar g_F$ 按引理 C 有定义（取 $X=F^*$）。

**(1) $G\le f$，取值于 $[0,\infty]$，且下半连续、凸.** 由引理 C，$0\le\bar g_F(q_Fx)\le g_F(q_Fx)\le f(x)$。由引理 B(1)（$q_F$ 连续线性）和 B(2)，$G$ 下半连续且凸。

**(2) 最大性.** 设 $h:E\to[-\infty,\infty]$ 下半连续、凸，且 $h\le f$。反设存在 $x_0$ 使 $G(x_0)<h(x_0)$，取实数 $t$ 满足 $G(x_0)<t<h(x_0)$。

由于 $\operatorname{epi}f\subset\operatorname{epi}h$ 且 $f$ 至少一点有限，$\operatorname{epi}h$ 是 $E\times\mathbb R$ 中的非空闭凸集，而 $(x_0,t)\notin\operatorname{epi}h$。$E\times\mathbb R$ 是 Hausdorff 局部凸空间，其对偶为 $\{(x,s)\mapsto\varphi(x)+\beta s:\ \varphi\in E',\ \beta\in\mathbb R\}$。由严格分离定理（局部凸空间中闭凸集与外点可严格分离），存在 $\varphi\in E'$、$\beta,\alpha\in\mathbb R$，使得
$$\varphi(x_0)+\beta t<\alpha\le\varphi(x)+\beta s\qquad\forall (x,s)\in\operatorname{epi}h.$$
由引理 A 的第 1 条，可令 $s\to+\infty$，因此 $\beta\ge0$。取 $F=\operatorname{span}\{\varphi\}$。

- **情形 $\beta>0$.** 不妨设 $\beta=1$。对 $f(x)<\infty$，有 $(x,f(x))\in\operatorname{epi}h$，所以 $f(x)\ge\alpha-\varphi(x)$。在 $q_F^{-1}(y)$ 上 $\varphi(x)=y(\varphi)$，所以
  $$g_F(y)\ge a(y):=\alpha-y(\varphi).$$
  $a$ 是连续仿射函数，由引理 B(3) 下半连续且凸；由引理 C(c)，$a\le\bar g_F$。于是 $G(x_0)\ge a(q_Fx_0)=\alpha-\varphi(x_0)>t$，矛盾。
- **情形 $\beta=0$.** 此时 $\varphi(x_0)<\alpha\le\varphi(x)$ 对所有 $x\in\operatorname{dom}h\supset\operatorname{dom}f$ 成立。于是在开半空间 $\{y:y(\varphi)<\alpha\}$ 上 $g_F=+\infty$，即 $\operatorname{epi}g_F\subset\{y(\varphi)\ge\alpha\}\times\mathbb R$，而后者是闭集。由引理 C(a)，$\bar g_F(q_Fx_0)=+\infty$，所以 $G(x_0)=+\infty$，与 $G(x_0)<t$ 矛盾。

因此 $h\le G$。特别地，在 $E$ 上取引理 C，得 $G=\bar f$，而且 $G$ 是唯一的。证明中只用到了 $\dim F\le1$ 的子空间，所以也有 $G=\sup_{\dim F\le1}\bar g_F\circ q_F$。

**(3) 扩大观测空间时的关系.** 设 $F\subset K$。
1. 由 S1，$g_F(r_{KF}z)=\inf_{r_{KF}z'=r_{KF}z}g_K(z')\le g_K(z)$。因此 $g_F\circ q_F\le g_K\circ q_K\le f$。
2. $\bar g_F\circ r_{KF}$ 下半连续且凸（引理 B(1)），并且 $\le g_F\circ r_{KF}\le g_K$。由引理 C(c)，$\bar g_F\circ r_{KF}\le\bar g_K$。因此
   $$\bar g_F\circ q_F\le\bar g_K\circ q_K\le G.$$
   有限维子空间按包含关系构成定向集（$F+K$ 仍是有限维的），所以 $G(x)=\lim_F\bar g_F(q_Fx)$ 是单调网的极限。
3. 令 $\mu=q_FG$。由引理 D，$\mu$ 非负且凸。
   - 由 $G\le f$ 得 $\mu\le g_F$，从而 $\bar\mu\le\bar g_F$。
   - 由 $\bar g_F\circ q_F\le G$ 得 $\bar g_F\le\mu$，从而 $\bar g_F\le\bar\mu$。

   所以 $\bar g_F=\overline{q_FG}$。$K$ 与 $F$ 之间的对应关系见 S6。

## S5

**结论：不一定.** 令
$$C=\{(a,b):a>0,\ ab\ge1\},\qquad f=\delta_C\ (\text{在 }C\text{ 上为 }0，\text{其余为 }+\infty).$$

- **$C$ 是闭集.** 若 $(a_n,b_n)\to(a,b)$ 且 $(a_n,b_n)\in C$，则 $ab\ge1$，于是 $a\ne0$；又 $a\ge0$，所以 $a>0$。
- **$C$ 是凸集.** $C=\{b\ge1/a,\ a>0\}$，而 $1/a$ 在 $(0,\infty)$ 上凸。
- **$f$ 满足题设.** 因为 $C$ 闭且凸，$\operatorname{epi}f=C\times[0,\infty)$ 闭且凸，所以 $f$ 下半连续、凸、取值非负，并且 $f(1,1)=0$ 有限。

取 $\varphi(a,b)=a$，$F=\operatorname{span}\{\varphi\}$。则
$$g_F(y)=\begin{cases}0,&y(\varphi)>0\quad(\text{取 }b=1/y(\varphi)),\\+\infty,&y(\varphi)\le0.\end{cases}$$
于是 $\{g_F\le0\}=\{y(\varphi)>0\}$ 不闭：$y_n(\varphi)=1/n\to0$，而极限点不在这个集合里。由引理 A，$g_F$ 不下半连续。

S2 的论证在这里失效，原因是 $\{f\le0\}=C$ 不紧。

## S6

**$G=f$ 当且仅当 $f$ 下半连续.**
- (⇒) 由 S4(1)，$G$ 下半连续，所以 $f=G$ 下半连续。
- (⇐) $f$ 本身是满足 $h\le f$ 的下半连续凸函数（凸性来自共同设定），由 S4(2) 得 $f\le G$。又由 S4(1)，$G\le f$。所以 $G=f$。

**等式 $\bar g_F=\bar m$.** 设 $F\subset K$，令
$$m(y):=\inf_{r_{KF}z=y}\bar g_K(z)=(r_{KF}\bar g_K)(y).$$
由引理 C，$\bar g_K$ 非负且凸；$r_{KF}$ 线性，所以引理 D 适用，$m$ 非负且凸，$\bar m$ 有定义。

- **$\bar m\le\bar g_F$：** 由 $\bar g_K\le g_K$ 和 S1，$m(y)\le\inf_{r_{KF}z=y}g_K(z)=g_F(y)$。再由引理 C(d)，$\bar m\le\bar g_F$。
- **$\bar g_F\le\bar m$：** 由 S4(3) 第 2 条，$\bar g_F(r_{KF}z)\le\bar g_K(z)$。对 $r_{KF}z=y$ 取下确界，得 $\bar g_F\le m$（纤维为空时右边为 $+\infty$）。$\bar g_F$ 下半连续且凸，由引理 C(c)，$\bar g_F\le\bar m$。

所以 $\bar g_F=\overline{\big(y\mapsto\inf_{r_{KF}z=y}\bar g_K(z)\big)}$。

**最外层 bar 能否总省去：不能.** 取 S5 的例子：$E=\mathbb R^2$，$f=\delta_C$，$F=\operatorname{span}\{\varphi\}$，$K=E'$（$F\subset K$）。

1. $q_K$ 线性且单射（$E'$ 分离点），并且 $\dim K^*=2=\dim E$，所以 $q_K$ 是有限维空间之间的线性同胚。
2. 于是 $g_K=f\circ q_K^{-1}$。由引理 B(1)，它下半连续，所以由引理 C(d)，$\bar g_K=g_K$。
3. 由 S1，$m=g_F$。由 S5，$m$ 不下半连续。

具体地，$\operatorname{epi}g_F=\{y(\varphi)>0\}\times[0,\infty)$，其闭包为 $\{y(\varphi)\ge0\}\times[0,\infty)$。因此在 $y(\varphi)=0$ 处，$\bar m(y)=\bar g_F(y)=0$，而 $m(y)=+\infty$。所以 $\bar g_F\ne m$，最外层的 bar 一般不能省去。

在 S2 的条件下，最外层 bar 可以省去，而且所有 bar 都可以去掉：此时 $g_K$ 与 $g_F$ 都下半连续，$\bar g_K=g_K$，$m=g_F=\bar g_F$。当 $F=K$ 时也可以省去，因为此时 $m=\bar g_F$。