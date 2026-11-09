 

## 誉0　预备设定与一般引理

**约定与记号。** 全文固定：$E$ 为实 Hausdorff 局部凸空间（lcs），$E'$ 为其连续对偶；
$$\mathcal F:=\{F\subseteq E'\;:\;F\text{ 为线性子空间，}\dim F<\infty\}.$$
对 $F\in\mathcal F$：$F^*$ 为 $F$ 的代数对偶，赋予有限维（Euclid）拓扑；$q_F:E\to F^*,\ q_F(x)(\phi)=\phi(x)$。对 $F\subseteq K$（均属 $\mathcal F$）：$r_{KF}:K^*\to F^*,\ r_{KF}\Theta=\Theta|_F$。$f:E\to[0,+\infty]$ 凸且至少一点有限。

对 $u:X\to[-\infty,+\infty]$（$X$ 为实拓扑向量空间）：
$$\operatorname{epi}(u):=\{(x,t)\in X\times\mathbb R:\ t\in\mathbb R,\ u(x)\le t\},\qquad S_c(u):=\{x:\ u(x)\le c\}.$$
“下半连续”指 $\operatorname{epi}(u)$ 闭，“凸”指 $\operatorname{epi}(u)$ 凸；竞争函数取值于 $[-\infty,+\infty]$。注意 $\operatorname{epi}(u)$ 在 $t$ 方向向上封闭。广义算术约定：对 $[0,+\infty]$ 值函数 $u$，$\phi(x)-u(x):=-\infty$ 当 $u(x)=+\infty$；空集上确界 $=+\infty$、下确界 $=-\infty$；$r+(\pm\infty)=\pm\infty$。下文所有运算均良定。

---

**P0（观测映射的性质）。** 设 $F,K\in\mathcal F$，$F\subseteq K$。
- (a) $q_F$、$r_{KF}$ 线性，$q_F$ 连续，$r_{KF}$ 连续（有限维自动）且**满**。
- (b) $q_F=r_{KF}\circ q_K$。
- (c)（附注）$q_F$ 满，故每个纤维非空，"$+\infty$（当纤维为空）"条款从不生效；但下文证明不依赖此事实。

**证明。** 线性性直接验证。$q_F$ 连续：取 $F$ 的基 $\phi_1,\dots,\phi_n$，坐标 $\Theta\mapsto\Theta(\phi_i)$ 在 $F^*$ 上连续（有限维空间上一切线性泛函连续），其与 $q_F$ 的复合为 $x\mapsto\phi_i(x)$，连续（$\phi_i\in E'$）；到有限维 Hausdorff 拓扑向量空间的线性映射连续当且仅当各坐标连续。$r_{KF}$ 满：任一 $\lambda\in F^*$（$F$ 上线性泛函）可扩张为 $K$ 上线性泛函 $\Lambda$（基扩张），$\Lambda\in K^*$ 且 $r\Lambda=\lambda$。(b)：对 $x\in E,\phi\in F$ 逐点验证。(c)：设 $\varphi_1,\dots,\varphi_n$ 为 $F$ 的基。断言 $T:E\to\mathbb R^n,\ Tx=(\varphi_1(x),\dots,\varphi_n(x))$ 满：否则 $\operatorname{im}T$ 为真子空间，存在 $0\ne\alpha\in\mathbb R^n$ 与 $\operatorname{im}T$ 正交，即 $\sum_i\alpha_i\varphi_i=0$ 于 $E$，与 $\varphi_i$ 线性无关矛盾。对 $\lambda\in F^*$，令 $\alpha_i:=\lambda(\varphi_i)$，取 $x$ 使 $Tx=\alpha$，则 $q_F(x)(\varphi_i)=\lambda(\varphi_i)$，故 $q_Fx=\lambda$。∎

---

**P1（上确界的上图）。** 对任意一族 $u_i:X\to[-\infty,+\infty]$：
$$\operatorname{epi}\big(\sup_i u_i\big)=\bigcap_i \operatorname{epi}(u_i).$$
从而实拓扑向量空间 $X$ 上任意一族下半连续（相应地，凸）函数的上确界下半连续（相应地，凸）。常数 $c\in\mathbb R$（上图 $=X\times[c,\infty)$）、$\equiv-\infty$（上图 $=X\times\mathbb R$）、$\equiv+\infty$（上图 $=\varnothing$）均下半连续且凸。

**证明。** 逐点等价：$\sup_iu_i(x)\le t\iff\forall i:u_i(x)\le t$。闭（凸）集之交闭（凸）；$X\times\mathbb R$ 为实拓扑向量空间。∎

---

**P2（凸性的取值形式）。** 若 $u$ 凸且 $u(x_0),u(x_1)\in\mathbb R$，则对 $\lambda\in[0,1]$：$u((1-\lambda)x_0+\lambda x_1)\le(1-\lambda)u(x_0)+\lambda u(x_1)$。

**证明。** $(x_i,u(x_i))\in\operatorname{epi}(u)$，其凸组合属于凸集 $\operatorname{epi}(u)$。∎

---

**P3（下半连续 $\iff$ 次水平集闭）。** 设 $X$ 为拓扑空间，$u:X\to[-\infty,+\infty]$。则 $\operatorname{epi}(u)$ 在 $X\times\mathbb R$ 中闭 $\iff$ 对每个 $c\in\mathbb R$，$S_c(u)$ 在 $X$ 中闭。

**证明。** ($\Rightarrow$) $S_c(u)=\iota_c^{-1}(\operatorname{epi}u)$，$\iota_c(x)=(x,c)$ 连续。（$\Leftarrow$）设网 $(x_\alpha,t_\alpha)\in\operatorname{epi}(u)$ 收敛于 $(x,t)$。任取 $s>t$：由 $t_\alpha\to t$，最终 $t_\alpha<s$，故最终 $x_\alpha\in S_s(u)$；网最终处于闭集中，则其极限亦然，故 $x\in S_s(u)$，即 $u(x)\le s$。对所有 $s>t$ 成立即得 $u(x)\le t$（否则取 $t<s<u(x)$，或当 $u(x)=+\infty$ 时任取 $s>t$，矛盾）。故 $(x,t)\in\operatorname{epi}(u)$。∎

---

**P4（复合）。** 设 $X,Y$ 为实拓扑向量空间，$T:Y\to X$ 连续（相应地线性）。若 $u:X\to[-\infty,+\infty]$ 下半连续（相应地凸），则 $u\circ T$ 亦然。若 $T$ 为线性同胚，则 $u$ 与 $u\circ T$ 同时下半连续（凸）。

**证明。** $\operatorname{epi}(u\circ T)=(T\times\mathrm{id}_\mathbb R)^{-1}(\operatorname{epi}u)$（逐点验证）。闭集在连续映射下的原像闭；凸集在线性映射下的原像凸。$T$ 为线性同胚时 $T\times\mathrm{id}$ 亦然，闭性与凸性双向保持。∎

---

**P5（Hahn–Banach 分离；标准定理）。** 设 $X$ 为实局部凸空间，$C\subseteq X$ 闭凸非空，$p\notin C$。则存在 $\Lambda\in X'$ 与 $\beta\in\mathbb R$ 使
$$\Lambda(p)<\beta\le\inf_{c\in C}\Lambda(c).$$
特别地（取相反数），存在 $\varphi\in X'$ 与 $\gamma\in\mathbb R$ 使 $\varphi(p)>\gamma\ge\sup_{C}\varphi$。又若 $X$ Hausdorff，则 $E'$（即 $X‘$）分离 $X$ 的点（取 $C=\{x’\}$）。

**援引理由。** 这是 Hahn–Banach 定理的标准分离推论：$C$ 闭且 $p\notin C$，由局部凸性与加法连续性存在 $0$ 的凸开邻域 $V$ 使 $(p+V)\cap C=\varnothing$；对不相交凸集 $p+V$（开）与 $C$，由 HB 分离存在非零连续线性 $\Lambda$ 及 $\beta$，使 $\Lambda(a)<\beta\le\Lambda(c)$（$\forall a\in p+V,c\in C$；开的一侧严格，因为非零线性泛函是开映射、开集上不能达到上确界），代入 $a=p$（$0\in V$）即得。每次使用处核验：空间为实 lcs（$E$、$F^*$、$K^*$、$E\times\mathbb R$、$F^*\times\mathbb R$ 均是，lcs 的有限积是 lcs，有限维空间是 lcs），$C$ 闭凸非空，$p\notin C$；Hausdorff 用于单点集闭（$T_1$）。∎

---

**P6（正常下半连续凸函数的 Fenchel–Moreau 型表示）。** 设 $X$ 为实 Hausdorff lcs，$h:X\to\mathbb R\cup\{+\infty\}$，$\operatorname{dom}h:=\{h<\infty\}\neq\varnothing$（即 $h$ 正常），且 $h$ 下半连续、凸。则对每个 $x\in X$：
$$h(x)=\sup\{a(x)\ :\ a:X\to\mathbb R\ \text{连续仿射}，\ a\le h\},$$
且该仿射族非空。

**证明。** "$\le$"显然。设 $\alpha<h(x)$，构造 $a\le h$ 且 $a(x)>\alpha$。$X\times\mathbb R$ 为实 Hausdorff lcs；$C:=\operatorname{epi}(h)$ 非空（$\operatorname{dom}h\ne\varnothing$）、凸、闭（$h$ 下半连续）；$p:=(x,\alpha)\notin C$。由 P5 存在 $\Lambda\in(X\times\mathbb R)'$ 与 $\beta\in\mathbb R$：$\Lambda(p)<\beta\le\inf_C\Lambda$。写 $\Lambda(x',t)=\phi(x')+\rho t$（$\phi\in X‘,\rho\in\mathbb R$）。若 $\rho>0$，则由 $\operatorname{epi}$ 在 $t$ 方向向上封闭，令 $t\to+\infty$ 矛盾，故 $\rho\le 0$。

*情形 A（$\rho<0$）*：定义 $a(x‘):=\dfrac{\varphi(x’)-\beta}{-\rho}$。对 $(x',t)\in C$：$\varphi(x')+\rho t\le\beta\Rightarrow t\ge a(x')$；取 $x‘\in\operatorname{dom}h$（$t=h(x’)$）得 $h(x')\ge a(x')$，$x'\notin\operatorname{dom}h$ 时 $h=+\infty\ge a$，故 $a\le h$，$a$ 连续仿射。又 $\Lambda(p)<\beta$ 即 $\varphi(x)+\rho\alpha<\beta$，即 $\varphi(x)-\beta<(-\rho)\alpha$，除以 $-\rho>0$ 得 $a(x)>\alpha$。

*情形 B（$\rho=0$）*：此时 $\varphi(x)<\beta\le\varphi(x‘)$ 对一切 $(x’,t)\in C$，特别地 $\varphi\ge\beta>\varphi(x)$ 于 $\operatorname{dom}h$。先证存在连续仿射 $a_0\le h$：取 $x_1\in\operatorname{dom}h$，对点 $(x_1,h(x_1)-1)\notin C$ 应用上述分离得 $\Lambda',\beta'$；若相应 $\rho'=0$，则 $\varphi‘(x_1)<\beta’\le\varphi'(x_1)$（因 $(x_1,h(x_1))\in C$）矛盾，故 $\rho'<0$，情形 A 给出 $a_0$。现令 $a_n:=a_0+n(\beta-\varphi)$（连续仿射）：在 $\operatorname{dom}h$ 上 $\beta-\varphi\le0$，故 $a_n\le a_0\le h$；在 $\operatorname{dom}h$ 外 $h=+\infty\ge a_n$。而 $a_n(x)=a_0(x)+n(\beta-\varphi(x))\to+\infty$（$\beta-\varphi(x)>0$），取 $n$ 充分大即 $a_n(x)>\alpha$。∎

---

**P7（取 $-\infty$ 的二分法）。** 设 $X$ 为实拓扑向量空间，$h:X\to[-\infty,+\infty]$ 下半连续且凸。若 $h(x_0)=-\infty$，则对每个满足 $h(x_1)<+\infty$ 的 $x_1$ 有 $h(x_1)=-\infty$。从而恰居其一：(i) $h$ 处处 $>-\infty$；(ii) $h=-\infty\cdot\mathbf 1_C+\infty\cdot\mathbf 1_{X\setminus C}$，其中 $C:=\{h=-\infty\}=\operatorname{dom}h$ 为非空闭凸集（$C=X$ 即 $h\equiv-\infty$，允许）。

**证明。** 设 $h(x_0)=-\infty$，$h(x_1)<+\infty$；不妨 $h(x_1)\in\mathbb R$（若已为 $-\infty$ 则无需证）。对 $\lambda\in(0,1)$：一切 $(x_0,t)\in\operatorname{epi}(h)$，且 $(x_1,h(x_1))\in\operatorname{epi}(h)$；由凸性 $(x_\lambda,(1-\lambda)t+\lambda h(x_1))\in\operatorname{epi}(h)$ 对一切 $t\in\mathbb R$。任给 $s\in\mathbb R$，取 $t\le\frac{s-\lambda h(x_1)}{1-\lambda}$，则由上图向上封闭得 $(x_\lambda,s)\in\operatorname{epi}(h)$。故 $h(x_\lambda)=-\infty$ 对一切 $\lambda\in(0,1)$。令 $\lambda\to1$：$(x_\lambda,s)\to(x_1,s)$，$\operatorname{epi}(h)$ 闭，故 $(x_1,s)\in\operatorname{epi}(h)$ 对一切 $s\in\mathbb R$，即 $h(x_1)=-\infty$。

若 $h$ 取 $-\infty$ 值，上段给出 $\{h=-\infty\}=\operatorname{dom}h=:C$。$C$ 闭：$C=\bigcap_n S_{-n}(h)$，诸 $S_c$ 闭（P3）。$C$ 凸：$x\in C\iff(x,0)\in\operatorname{epi}(h)$（$h(x)=-\infty\le0$；反之 $h(x)\le0<\infty\Rightarrow x\in\operatorname{dom}h=C$），故 $C\times\{0\}=\operatorname{epi}(h)\cap(X\times\{0\})$ 凸，投影 $C$ 凸。在 $C$ 上 $h=-\infty$；在 $X\setminus C$ 上 $h\ne-\infty$ 且 $h<\infty$ 将推出 $x\in C$，故 $h=+\infty$。∎

---

**P8（关键引理：最大下半连续凸下界）。** 设 $X$ 为实 Hausdorff lcs，$u:X\to[0,+\infty]$ 凸且有一点 $x_0$ 使 $u(x_0)<\infty$。定义
$$u^*(\varphi):=\sup_{x\in X}\big(\varphi(x)-u(x)\big)\in(-\infty,+\infty]\quad(\varphi\in X'),\qquad u^{**}(x):=\sup_{\varphi\in X'}\big(\varphi(x)-u^*(\varphi)\big).$$
则：
- (a) **（Fenchel–Young）** $u^{**}\le u$，$u^{**}\ge0$，且 $u^{**}$ 下半连续、凸；$u^*(0)=-\inf u\in(-\infty,0]$。
- (b) 每个下半连续凸的 $h:X\to[-\infty,+\infty]$（允许取 $\pm\infty$）若 $h\le u$，则 $h\le u^{**}$。
- (c) 令 $\mathcal M(u):=\{h:X\to[-\infty,+\infty]:h$ 下半连续、凸、$h\le u\}$，$\bar u:=\sup\mathcal M(u)$（逐点）。则 $\mathcal M(u)\ne\varnothing$（含常值 $0$），$\bar u\in\mathcal M(u)$（即 $\bar u$ 是 $u$ 的最大下半连续凸下界），且
$$\bar u=u^{**}=\sup\{a(x):a:X\to\mathbb R\ \text{连续仿射},\ a\le u\}\ (\text{此族非空})，\qquad (\bar u)^*=u^*.$$

**证明。** (a) 对每个 $\varphi,x$：$u^*(\varphi)\ge\varphi(x)-u(x)$，故 $\varphi(x)-u^*(\varphi)\le u(x)$（广义算术良定因 $u\ge0$）；取上确界得 $u^{**}\le u$。$u^*(0)=\sup(-u)=-\inf u$，且 $\inf u\in[0,u(x_0))$，故 $u^*(0)\in(-\infty,0]$，从而 $u^{**}(x)\ge0-u^*(0)=\inf u\ge0$。对每个 $\varphi$：$x\mapsto\varphi(x)-u^*(\varphi)$ 或为连续仿射（$u^*(\varphi)\in\mathbb R$），或 $\equiv-\infty$（$u^*(\varphi)=+\infty$；注意 $u^*(\varphi)\ge\varphi(x_0)-u(x_0)>-\infty$，故无其他情形），二者均下半连续凸（P1），故 $u^{**}$ 下半连续凸（P1）。

(b) *情形 0*：$h\equiv-\infty$，则 $h\le u^{**}$ 平凡。*情形 1*：$h$ 不取 $-\infty$。由 $h\le u$ 及 $u(x_0)<\infty$ 得 $h(x_0)<\infty$，故 $\operatorname{dom}h\ne\varnothing$，$h$ 正常；且 $h$ 下半连续凸，由 P6 得 $h=\sup\{a\le h\ \text{连续仿射}\}$。对每个这样的 $a=\varphi+c$：$a\le u$ 给 $c\le u(x)-\varphi(x)$ 对一切 $x$，故 $c\le\inf_x(u-\varphi)=-u^*(\varphi)$，于是 $a\le\varphi-u^*(\varphi)\le u^{**}$。取上确界得 $h\le u^{**}$。*情形 2*：$h$ 取 $-\infty$ 值。由 P7，$h=-\infty\cdot\mathbf 1_C+\infty\cdot\mathbf 1_{X\setminus C}$，$C=\operatorname{dom}h$ 闭凸非空。由 $h\le u$：在 $X\setminus C$ 上 $+\infty\le u$，故 $u=+\infty$ 于 $X\setminus C$，即 $\operatorname{dom}u\subseteq C$（特别 $x_0\in C$）。在 $C$ 上 $h=-\infty\le u^{**}$。设 $x\in X\setminus C$。由 P5（$X$ 实 Hausdorff lcs；$C$ 闭凸非空；$x\notin C$）存在 $\varphi\in X'$ 与 $\gamma\in\mathbb R$：$\varphi(x)>\gamma\ge\sup_C\varphi$。令 $a_n:=n(\varphi-\gamma)$（连续仿射）。则 $a_n\le u$：在 $C\supseteq\operatorname{dom}u$ 上 $\varphi\le\gamma$，故 $a_n\le0\le u$（用 $u\ge0$）；在 $\operatorname{dom}u$ 之外 $u=+\infty$。同情形 1 的推理，$a_n\le u\Rightarrow a_n\le\varphi-u^*(\varphi)\le u^{**}$，故 $u^{**}(x)\ge a_n(x)=n(\varphi(x)-\gamma)\to+\infty$，即 $u^{**}(x)=+\infty=h(x)$。

(c) 常值 $0\le u$（因 $u\ge0$）且下半连续凸（P1），故 $\mathcal M(u)\ne\varnothing$。$\bar u=\sup\mathcal M(u)$ 下半连续凸（P1）且 $\le u$（逐点），故 $\bar u\in\mathcal M(u)$，是最大元。由 (a)，$u^{**}\in\mathcal M(u)$（下半连续凸、$\le u$、且取值 $\subseteq[0,+\infty]\subseteq[-\infty,+\infty]$），故 $u^{**}\le\bar u$；由 (b)，每个 $h\in\mathcal M(u)$ 满足 $h\le u^{**}$，故 $\bar u\le u^{**}$。得 $\bar u=u^{**}$。连续仿射下确界——即“连续仿射下界之族的上确界”：每个连续仿射 $a=\varphi+c\le u$ 满足 $a\le\varphi-u^*(\varphi)\le u^{**}$（情形 1 的计算）；反之每个 $\varphi-u^*(\varphi)$（$u^*(\varphi)\in\mathbb R$）由 Fenchel–Young 是 $u$ 的连续仿射下界，$u^*(\varphi)=+\infty$ 时 $\equiv-\infty$。故该族的上确界 $=\sup_\varphi(\varphi-u^*(\varphi))=u^{**}$；族非空：常值 $\inf u\in[0,u(x_0)]\cap\mathbb R\le u$ 是连续仿射下界。最后 $(\bar u)^*=u^*$："$\ge$"：$\bar u\le u$ 给 $\varphi-\bar u\ge\varphi-u$ 逐点（若 $\bar u(x)=+\infty$ 则 $u(x)=+\infty$，两边 $-\infty$），取上确界；"$\le$"：由 Fenchel–Young，$\varphi(x)-u^*(\varphi)\le u^{**}(x)=\bar u(x)$ 对一切 $x$，故 $u^*(\varphi)\ge\varphi(x)-\bar u(x)$ 对一切 $x$，即 $u^*(\varphi)\ge(\bar u)^*(\varphi)$。∎

---

## S1　原始记录

设 $F\in\mathcal F$ 固定。

**(i) 非负性。** $g_F(y)=\inf\{f(x):q_Fx=y\}$ 是 $[0,+\infty]$ 值函数的下确界，故 $g_F(y)\in[0,+\infty]$（空纤维按约定为 $+\infty$）。∎

**(ii) 至少一点有限。** 取 $x_0\in E$ 使 $f(x_0)<\infty$（题设）。则 $x_0$ 属于 $q_Fx_0$ 的纤维，故
$$g_F(q_Fx_0)\le f(x_0)<\infty. $$特别地 $g_F$ 处处 $>-\infty$（由 (i)），即 $g_F$ 正常。∎

**(iii) 凸性。** 设 $(y_0,t_0),(y_1,t_1)\in\operatorname{epi}(g_F)\subseteq F^*\times\mathbb R$，$\lambda\in(0,1)$，记 $y_\lambda=(1-\lambda)y_0+\lambda y_1$，$t_\lambda=(1-\lambda)t_0+\lambda t_1$；要证 $(y_\lambda,t_\lambda)\in\operatorname{epi}(g_F)$。任给 $\varepsilon>0$。因 $g_F(y_i)\le t_i<\infty$：纤维 $\{x:q_Fx=y_i\}$ 非空（否则其上确界为 $+\infty> t_i$），且由下确界的 $\varepsilon$-特征，存在 $x_i$ 使 $q_Fx_i=y_i$ 且 $f(x_i)\le t_i+\varepsilon$；于是 $f(x_i)\in[0,\infty)$ 为实数。令 $x_\lambda:=(1-\lambda)x_0+\lambda x_1$。由 $q_F$ 线性：$q_Fx_\lambda=y_\lambda$。由 P2（$f$ 凸、$f(x_i)$ 实）：
$$f(x_\lambda)\le(1-\lambda)f(x_0)+\lambda f(x_1)\le(1-\lambda)(t_0+\varepsilon)+\lambda(t_1+\varepsilon)=t_\lambda+\varepsilon. $$
而 $x_\lambda$ 在 $y_\lambda$ 的纤维中，故 $g_F(y_\lambda)\le f(x_\lambda)\le t_\lambda+\varepsilon$。此对一切 $\varepsilon>0$ 成立，故 $g_F(y_\lambda)\le t_\lambda$（若 $g_F(y_\lambda)>t_\lambda$，取 $\varepsilon:=\frac{g_F(y_\lambda)-t_\lambda}{2}>0$ 即矛盾，$g_F(y_\lambda)=+\infty$ 时亦然）。故 $\operatorname{epi}(g_F)$ 凸。∎

**(iv) 记录的相容性（扩大观测空间）。** 设 $F\subseteq K$（$\in\mathcal F$）。由 P0(b)，$q_F=r_{KF}\circ q_K$，故对 $y\in F^*$：
$$\{x\in E:\ q_Fx=y\}=\{x:\ r_{KF}(q_Kx)=y\}=\bigsqcup_{z\in r_{KF}^{-1}(y)}\{x:\ q_Kx=z\}$$
（每个 $x$ 恰属于 $z=q_Kx$ 所对应的一块）。于是由“分划上的下确界 = 各块下确界的下确界”（含空指标集约定：若 $r_{KF}^{-1}(y)=\varnothing$ 则左侧集合亦空，两边均为 $+\infty$；事实上 $r_{KF}$ 满，此情形不发生，但未用到）：
$$g_F(y)=\inf_{z\in r_{KF}^{-1}(y)}\inf\{f(x):q_Kx=z\}=\inf\{g_K(z)\ :\ r_{KF}z=y\}. $$
特别地有单向估计 $g_F(r_{KF}z)\le g_K(z)$（$z$ 属于自己的纤维），后文将多次使用。∎

**(v) 是否需要纤维下确界取到？不需要。** 上述全部论证只用了：(i)(ii) 下确界的单调性；(iii) 下确界的 $\varepsilon$-特征（“$\inf S\le t<\infty\Rightarrow\forall\varepsilon>0\ \exists s\in S:\ s\le t+\varepsilon$”，由 “$t+\varepsilon>\inf S$ 故非下界” 得出，须先由 $\inf S\le t<\infty$ 排除 $S=\varnothing$）；(iv) 集合恒等式与“分划上取下确界可交换”。任何一步都不要求下确界在某点取到。事实上在共同设定下取到一般不成立（见 S5 的例子，其中 $g_F(0)=0$ 但纤维内无取到点，因达到集趋于无穷）。∎

---

## S2　紧次水平集

本阶段附加假设：$f$ 下半连续，且对每个 $c\in\mathbb R$，$S_c(f)=\{f\le c\}$ 紧。固定 $F\in\mathcal F$。

（附注：$E$ Hausdorff，故紧 $\Rightarrow$ 闭，于是诸 $S_c(f)$ 闭，由 P3 这已蕴含 $f$ 下半连续；题设中的下半连续性因此是冗余但无害的。）

**第一步（取到）。** 设 $y\in F^*$，$g_F(y)<\infty$；记 $c:=g_F(y)\in[0,\infty)$（S1(i)）。对 $n\ge1$ 令
$$A_n:=q_F^{-1}(\{y\})\cap S_{c+1/n}(f). $$
- $A_n\ne\varnothing$：$c<\infty$ 蕴含纤维非空（空纤维给 $+\infty$），且 $c=\inf_{\text{纤维}}f\le c+1/n$，由 $\varepsilon$-特征存在纤维中的 $x$ 使 $f(x)\le c+1/n$。
- $A_n$ 闭：$q_F$ 连续（P0），$\{y\}$ 在 Hausdorff 空间 $F^*$ 中闭；$S_{c+1/n}(f)$ 闭（下半连续 + P3，或紧 + Hausdorff）。
- $A_n\subseteq S_{c+1}(f)=:B$，$B$ 紧（$c+1\in\mathbb R$）。
- $\{A_n\}_{n\ge1}$ 递减，故具有限交性质（有限交 $=A_{\max n_i}\ne\varnothing$）。

紧性（闭集族 + 有限交性质 $\Rightarrow$ 全交非空，取 $B$ 的紧性）给出 $x^*\in\bigcap_nA_n$。则 $q_Fx^*=y$ 且 $f(x^*)\le c+1/n$ 对一切 $n$，故 $f(x^*)\le c$；又 $x^*$ 在纤维中，$f(x^*)\ge g_F(y)=c$。故
$$f(x^*)=g_F(y),\qquad q_Fx^*=y, $$
即纤维下确界取到。∎

**第二步（次水平集）。** 断言：对每个 $c'\in\mathbb R$，
$$S_{c'}(g_F)=q_F\big(S_{c'}(f)\big). $$
"$\supseteq$"：$y=q_F(x)$、$f(x)\le c‘$ 给 $g_F(y)\le f(x)\le c’$。"$\subseteq$"：设 $g_F(y)\le c'$。若 $c'<0$，由 $g_F\ge0$ 得左边为空，而 $f\ge0$ 给右边亦空，等式成立。若 $c'\ge0$ 或一般地 $g_F(y)\le c'<\infty$：由第一步（用于该 $y$），存在 $x$ 使 $q_Fx=y$、$f(x)=g_F(y)\le c‘$，即 $y\in q_F(S_{c’}(f))$。

于是 $S_{c'}(g_F)$ 是紧集 $S_{c'}(f)$（对每个实 $c‘$ 紧，$c’<0$ 时为空）在连续映射 $q_F$ 下的像，含于 Hausdorff 空间 $F^*$，故紧，从而闭。∎

**第三步（下半连续）。** 诸 $S_{c'}(g_F)$（$c'\in\mathbb R$）闭，由 P3 得 $\operatorname{epi}(g_F)$ 闭，即 $g_F$ 下半连续。∎

**结论。** 在本阶段假设下，每个 $g_F$ 下半连续，且 $g_F(y)<\infty$ 时纤维下确界取到。（顺带：诸 $S_c(g_F)$ 紧，即“紧次水平集”性质传递给了记录成本；而 S5 将说明，去掉紧性后下半连续性可以失效。）∎

---

## S3　兼容成本记录的实现

本阶段沿用 S2 的假设。给定：对每个 $F\in\mathcal F$ 有 $y_F\in F^*$，满足 $r_{KF}y_K=y_F$ 对所有 $F\subseteq K$；给定 $c\in[0,\infty)$ 有限，使 $g_F(y_F)\le c$ 对所有 $F\in\mathcal F$。

（结构性附注：相容族 $(y_F)$ 等价于 $E‘$ 上的一个线性泛函 $Y$：对 $\varphi\in E’$ 定义 $Y(\varphi):=y_{\mathrm{span}(\varphi)}(\varphi)$；由相容性，当 $\varphi\in F$ 时 $y_F(\varphi)=y_K(\varphi)=Y(\varphi)$，故 $Y$ 良定，且 $Y(a\varphi+b\psi)=aY(\varphi)+bY(\psi)$（在 $F=\mathrm{span}(\varphi,\psi)$ 中验证）。条件 $q_Fx=y_F\ (\forall F)$ 即 $\varphi(x)=Y(\varphi)\ (\forall\varphi\in E')$，即 $x$ 实现 $Y$。下面证这样的 $x$ 存在唯一。）

**构造。** 对每个 $F\in\mathcal F$ 令
$$C_F:=\{x\in E:\ q_Fx=y_F,\ f(x)\le c\}. $$
1. **$C_F\ne\varnothing$**：$g_F(y_F)\le c<\infty$，由 S2 第一步存在 $x$ 使 $q_Fx=y_F$、$f(x)=g_F(y_F)\le c$。
2. **$C_F$ 闭**：$q_F^{-1}(\{y_F\})$ 闭（P0 + $F^*$ Hausdorff），$S_c(f)$ 闭（下半连续 + P3）。
3. **$C_F\subseteq B:=S_c(f)$**，$B$ 紧。
4. **有限交性质**：给定 $F_1,\dots,F_n\in\mathcal F$，令 $K:=F_1+\cdots+F_n\in\mathcal F$。由 1，$C_K\ne\varnothing$；对 $x\in C_K$ 用 P0(b) 与相容性：$q_{F_i}x=r_{F_iK}(q_Kx)=r_{F_iK}y_K=y_{F_i}$，且 $f(x)\le c$，故 $x\in\bigcap_iC_{F_i}$。于是任意有限交非空。
5. **存在性**：紧空间 $B$ 中具有限交性质的闭集族 $\{C_F\}_{F\in\mathcal F}$ 有非空全交。取
$$x\in\bigcap_{F\in\mathcal F}C_F. $$
则 $q_Fx=y_F$ 对一切 $F\in\mathcal F$，且 $f(x)\le c$。
6. **唯一性**：设 $x,x'$ 均满足。对每个 $\varphi\in E‘$，取 $F=\mathrm{span}(\varphi)\in\mathcal F$：$q_Fx=q_Fx’=y_F$ 给 $\varphi(x)=(q_Fx)(\varphi)=(q_Fx')(\varphi)=\varphi(x')$。若 $x\ne x'$，则 $C=\{x'\}$ 闭凸非空（Hausdorff $\Rightarrow T_1$；单点集凸）且 $x\notin C$，由 P5 存在 $\varphi\in E‘$ 分离，与 $\varphi(x)=\varphi(x’)$ 矛盾。故 $x=x‘$。∎

**结论。** $x=\bigcap_F C_F$ 中的任一点（它是被唯一确定的）满足 $q_Fx=y_F\ (\forall F)$ 与 $f(x)\le c$，且这样的 $x$ 唯一。构造完毕并验证。（引用核验：S2 第一步的适用性——本阶段沿用 S2 全部假设；P5 的适用性——$E$ 实 Hausdorff lcs，$\{x’\}$ 闭凸非空，$x\notin\{x'\}$。）∎

---

## S4　一般成本的恢复

**问题**：仅用共同设定（不假设 $f$ 下半连续、不假设紧性），能否从全部 $g_F$ 构造 $G:E\to[0,+\infty]$，使 $G$ 下半连续、凸、$G\le f$，且对每个下半连续凸（取值 $[-\infty,+\infty]$）的 $h\le f$ 有 $h\le G$。

**答案：能。** 且这样的 $G$ 唯一（若 $G_1,G_2$ 均满足，把极大性条件互相应用于对方得 $G_1\le G_2\le G_1$）。

**先指出一个必要的警示。** 朴素的构造 $\tilde G:=\sup_{F\in\mathcal F}g_F\circ q_F$ 不行：若 $E‘$ 有限维（例如 $E=\mathbb R$，$f=\delta_{(0,\infty)}$：凸、$\ge0$、在 $(0,\infty)$ 有限、非下半连续），则 $F=E’\in\mathcal F$，$q_{E'}:E\to E''$ 为线性同胚且 $g_{E'}\circ q_{E'}=f$，故 $\tilde G\ge f$；又显然 $\tilde G\le f$，得 $\tilde G=f$，不是下半连续的。因此必须经由共轭来恢复。

**第一步（从 $g_F$ 恢复 $f^*$ 的值）。** 设 $F\in\mathcal F$，$\varphi\in F$。断言：
$$\sup_{y\in F^*}\big(y(\varphi)-g_F(y)\big)=\sup_{x\in E}\big(\varphi(x)-f(x)\big)=:f^*(\varphi). $$
证明：$\varphi\in F$ 在 $q_F$-纤维上常值（$q_Fx=q_Fx'\Rightarrow\varphi(x)=(q_Fx)(\varphi)=(q_Fx')(\varphi)=\varphi(x‘$）；对 $y=q_Fx$ 有 $y(\varphi)=\varphi(x)$。于是对每个 $y\in F^*$（含纤维空的情形，此时 $g_F(y)=+\infty$，左边贡献 $-\infty$；纤维非空但 $g_F(y)=+\infty$ 时右侧对应块的每一项 $\varphi(x)-f(x)=-\infty$）：
$$y(\varphi)-g_F(y)=y(\varphi)-\inf_{q_Fx=y}f(x)=\sup_{q_Fx=y}\big(y(\varphi)-f(x)\big)=\sup_{q_Fx=y}\big(\varphi(x)-f(x)\big). $$
$E$ 是诸纤维（$y$ 取遍 $q_F(E)$）的分划，故对 $y$ 取上确界即对 $x\in E$ 取上确界。∎（只用分划与广义算术，不需取到、不需 $q_F$ 满。）

**第二步（扩大观测空间的关系／共轭的粘合）。** 设 $F\subseteq K\in\mathcal F$，$\varphi\in F$。则
$$\sup_{y\in F^*}\big(y(\varphi)-g_F(y)\big)=\sup_{z\in K^*}\big(z(\varphi)-g_K(z)\big). $$
证明（仅用 S1）：由 S1(iv)，$g_F(y)=\inf_{r_{KF}z=y}g_K(z)$，故
$$y(\varphi)-g_F(y)=\sup_{r_{KF}z=y}\big(y(\varphi)-g_K(z)\big)=\sup_{r_{KF}z=y}\big(z(\varphi)-g_K(z)\big) $$
（用 $(r_{KF}z)(\varphi)=z(\varphi)$ 于 $\varphi\in F$）；诸块 $\{z:r_{KF}z=y\}$ 分划 $K^*$（$r$ 满，但同样不必需），对 $y$ 取上确界即对 $z$ 取上确界。∎

因此下述定义与 $F$ 的选取无关（在有限维恒同 $F^{**}\cong F$、$K^{**}\cong K$ 之下，即 $g_K^*|_F=g_F^*$，其中 $g_F^*(\varphi):=\sup_{y\in F^*}(y(\varphi)-g_F(y))$ 是 $g_F$ 的 Fenchel 共轭）：
$$f^*(\varphi):=\sup_{y\in F^*}\big(y(\varphi)-g_F(y)\big)\quad\text{对任一 }F\in\mathcal F,\ \varphi\in F\quad(\text{例如 }F=\mathrm{span}\,\varphi). $$
（从数据本身看：$g_F$ 至少一点有限（S1），故该上确界 $>-\infty$；由第一步它也 $<+\infty$ 或 $=+\infty$，总之 $f^*(\varphi)\in(-\infty,+\infty]$ 良定。）

**第三步（$G$ 的构造）。** 定义
$$\boxed{\,G(x):=\sup_{\varphi\in E'}\big(\varphi(x)-f^*(\varphi)\big)\,} $$
此公式只用到观测结构（$E'$、$q_F$、$F^*$）与全部记录 $(g_F)_{F\in\mathcal F}$，不引用 $f$ 本身。

**第四步（性质核验）。** 对 $(X,u):=(E,f)$ 核验 P8 的条件：$E$ 实 Hausdorff lcs ✓；$f:[0,+\infty]$ 值、凸、有一点有限 ✓。由第一步，第三步中的 $f^*$ 恰是 P8 中的共轭，故 $G=f^{**}$，且：
- $G$ 下半连续、凸（P8(a)，或直接：每个 $\varphi-f^*(\varphi)$ 是连续仿射或 $\equiv-\infty$，上确界由 P1 保持）。
- $0\le G\le f$（P8(a)）；特别地 $G:E\to[0,+\infty]$。
- 极大性：每个下半连续凸 $h:E\to[-\infty,+\infty]$，$h\le f$，满足 $h\le f^{**}=G$（P8(b)，含 $h$ 取 $\pm\infty$ 的各种病态情形——P7 的二分法与 P5 的分离恰为此设计）。

故此 $G$ 满足全部要求。∎

**第五步（恢复的显式形式与扩大关系汇总）。**
- 逐点地：$G(x)=\sup\{\varphi(x)+c\ :\ \varphi\in E',\ c\in\mathbb R,\ y(\varphi)+c\le g_F(y)\ \forall y\in F^*,\ \forall F\in\mathcal F,\ \varphi\in F\}$；且由第二步，条件中对每个 $\varphi$ 只需检验一个 $F\ni\varphi$。
- 扩大观测空间时：$g_K^*|_F=g_F^*$（第二步），即**在小的空间上已算得的共轭值不因扩大观测而改变**；$(g_F^*)_{F\in\mathcal F}$ 粘合成 $E‘$ 上单个函数 $f^*$，$G=f^{**}$。这就是构造的典范性（与辅助选取无关）的来源。
- 由此并可写 $G(x)=\sup_{F\in\mathcal F}\overline{g_F}(q_Fx)$：把 P8 用于 $(F^*,g_F)$（条件核验：$F^*$ 有限维 Hausdorff lcs ✓，$g_F\ge0$ 凸、有点有限——S1 ✓），得 $\overline{g_F}=(g_F)^{**}$，而由第一步 $(g_F)^*(\varphi)=f^*(\varphi)$ 于 $\varphi\in F$，故 $\overline{g_F}(y)=\sup_{\varphi\in F}(y(\varphi)-f^*(\varphi))$；再对 $F$ 取上确界并用“每个 $\varphi\in E’$ 属于某个有限维 $F$”即得。（此式与 S6(b) 相互印证。）

**结论。** 可以构造；$G=f^{**}=\bar f$（$f$ 的最大下半连续凸下界，见 S6 的记号）；扩大观测空间的相容关系即 S1(iv) 与第二步的共轭粘合。∎

---

## S5　闭成本的有限投影

**判断：不必。** 即使 $f$ 下半连续、凸、非负、有点有限，某个 $g_F$ 可以不下半连续。

**反例。** $E:=\mathbb R^2$（通常拓扑，实 Hausdorff lcs；$E'= (\mathbb R^2)^*$，一切线性泛函连续）。令
$$A:=\{(x_1,x_2)\in\mathbb R^2:\ x_1>0,\ x_2\ge1/x_1\},\qquad f:=\delta_A\ (A\ \text{上为}\ 0,\ \text{其余为}\ +\infty). $$

**(1) $A$ 凸。** 设 $(x_1,x_2),(x_1',x_2')\in A$，$\lambda\in[0,1]$，$\tilde x_1:=(1-\lambda)x_1+\lambda x_1'>0$；由 $t\mapsto1/t$ 在 $(0,\infty)$ 上凸（或 Cauchy–Schwarz：$(1-\lambda)\frac1{x_1}+\lambda\frac1{x_1'}\ge\frac{1}{(1-\lambda)x_1+\lambda x_1'}$）：
$$\tilde x_2\ \ge\ (1-\lambda)\tfrac1{x_1}+\lambda\tfrac1{x_1'}\ \ge\ \tfrac1{\tilde x_1}, $$
故 $(\tilde x_1,\tilde x_2)\in A$。

**(2) $A$ 闭。** 设 $A\ni(x_1^n,x_2^n)\to(x_1,x_2)$（度量空间，序列足够）。若 $x_1>0$：由连续性 $x_2\ge1/x_1$，故在 $A$ 中。若 $x_1=0$：则 $x_1^n\to0^+$，$1/x_1^n\to+\infty$，故 $x_2^n\to+\infty$，与收敛矛盾。若 $x_1<0$：最终 $x_1^n<0$，与 $x_1^n>0$ 矛盾。

**(3) $f$ 满足题设。** $f\ge0$ ✓；$\operatorname{epi}(f)=A\times[0,\infty)$ 凸（(1)）且闭（(2)），故 $f$ 凸且下半连续 ✓；$f(1,1)=0<\infty$ ✓（$1\ge1/1$）。

**(4) 取一维观测。** 令 $\psi(x_1,x_2):=x_2\in E'$，$F:=\mathbb R\psi\in\mathcal F$。$J:F^*\to\mathbb R,\ J(\Theta):=\Theta(\psi)$ 为线性同胚（$\dim F=1$，$F^*$ 有限维拓扑），且 $J(q_F(x_1,x_2))=\psi(x_1,x_2)=x_2$。

**(5) 计算记录。** 令 $\tilde g:=g_F\circ J^{-1}:\mathbb R\to[0,+\infty]$。因 $q_Fx=J^{-1}(t)\iff x_2=t$：
$$\tilde g(t)=\inf\{f(x_1,x_2):\ x_2=t\}. $$
若 $t>0$：$(1/t,t)\in A$（$1/t>0$，$t\ge t$），故 $\tilde g(t)=0$。若 $t\le0$：$(x_1,t)\in A$ 要求 $t\ge1/x_1>0$，不可能，纤维与 $A$ 不交，$\tilde g(t)=+\infty$。故
$$\tilde g=\delta_{(0,\infty)}. $$

**(6) $\tilde g$ 非下半连续。** $\operatorname{epi}(\tilde g)=\{(t,s):t>0,\ s\ge0\}$，序列 $(1/n,0)\in\operatorname{epi}(\tilde g)$ 收敛于 $(0,0)\notin\operatorname{epi}(\tilde g)$，故不闭。由 P4（$J$ 线性同胚），$g_F=\tilde g\circ J$ 亦非下半连续。

**结论。** 存在满足本阶段全部假设的 $f$ 与有限维 $F\subseteq E'$ 使 $g_F$ 不下半连续，故“每个 $g_F$ 必下半连续”不成立。∎

**机理说明。** $S_0(g_F)=q_F(S_0(f))=q_F(A)$，而 $A$ 闭非紧，线性投影下闭集的像可以不闭（此处像为 $(0,\infty)$）。这正是 S2 中紧性所排除的情形；本例中 $S_0(f)=A$ 非紧，与 S2 的假设不相容，二者不矛盾。（对 $F=E'$ 有 $g_{E'}\cong f$ 下半连续，$F=\{0\}$ 平凡；失效发生在一维观测上。）

---

## S6　恢复与投影的精确关系

本阶段只用共同设定。按题意，对非负凸（且至少一点有限）的 $u$，$\bar u$ 记其**最大下半连续凸下界**，即 $\bar u:=\sup\mathcal M(u)$、$\mathcal M(u):=\{h\ (\text{取值}[-\infty,+\infty]):h\ \text{下半连续、凸}，\ h\le u\}$；P8(c) 已证该上确界存在、属于 $\mathcal M(u)$（即为最大元），且 $\bar u=u^{**}$、$(\bar u)^*=u^*$、$\bar u=\sup\{u\ \text{的连续仿射下界}\}$。适用性：$f$ ✓（共同设定）；$g_F$ ✓（S1：非负、凸、有点有限）；下文 (b) 中的 $H$ 将逐一核验。$G$ 为 S4 的构造，且由 S4 第四步与 P8(c)（用于 $(E,f)$），$G=f^{**}=\bar f$。

**(a) $G=f\iff f$ 下半连续。**
（$\Leftarrow$）若 $f$ 下半连续：$f$ 凸且 $f\le f$，故 $f\in\mathcal M(f)$，从而 $\bar f\ge f$；又 $\bar f\le f$，故 $\bar f=f$，即 $G=f$。
（$\Rightarrow$）$G=f^{**}$ 是一族连续仿射函数（或 $\equiv-\infty$）的上确界，由 P1 下半连续；$G=f$ 时 $f$ 下半连续。∎

**(b) $\ \overline{g_F}=\overline{H}$，其中 $H(y):=\inf\{\overline{g_K}(z):r_{KF}z=y\}$（$F\subseteq K\in\mathcal F$）。**

$H$ 合法性的核验（使记号 $\overline H$ 有意义）：诸纤维非空（$r_{KF}$ 满，P0），故 $H$ 处处有定义；$H\ge0$（因 $\overline{g_K}\ge0$，后者由常值 $0\in\mathcal M(g_K)$）；$H$ 凸：与 S1(iii) 完全相同的论证，把 $f,q_F$ 换成 $\overline{g_K},r_{KF}$（$\overline{g_K}$ 凸、非负、纤维上的点使 $\overline{g_K}(z_i)\le t_i+\varepsilon<\infty$ 为实值，用 P2）；$H$ 有点有限：取 $f(x_0)<\infty$，$z_0:=q_Kx_0$，则 $H(r_{KF}z_0)\le\overline{g_K}(z_0)\le g_K(z_0)\le f(x_0)<\infty$。

*“$\le$”方向。* 设 $h\in\mathcal M(g_F)$。令 $h':=h\circ r_{KF}:K^*\to[-\infty,+\infty]$。由 P4（$r_{KF}$ 连续线性），$h‘$ 下半连续且凸。对 $z\in K^*$，用 S1(iv) 的单向估计：
$$h‘(z)=h(r_{KF}z)\ \le\ g_F(r_{KF}z)\ =\ \inf\{g_K(z’):\ r_{KF}z‘=r_{KF}z\}\ \le\ g_K(z), $$
故 $h’\in\mathcal M(g_K)$，于是 $h'\le\overline{g_K}$（$\overline{g_K}$ 是 $\mathcal M(g_K)$ 的最大元）。现设 $y\in F^*$，取 $z$ 使 $r_{KF}z=y$（满射性），则
$$h(y)=h(r_{KF}z)=h‘(z)\le\overline{g_K}(z)\quad\Longrightarrow\quad h(y)\le\inf_{r_{KF}z=y}\overline{g_K}(z)=H(y). $$
于是每个 $h\in\mathcal M(g_F)$ 属于 $\mathcal M(H)$（下半连续、凸、$\le H$），故 $h\le\overline H$；对 $h$ 取上确界得 $\overline{g_F}\le\overline H$。

*“$\ge$”方向。* $\overline{g_K}\le g_K$（$\mathcal M(g_K)$ 中每个 $h\le g_K$，上确界亦然），故由 S1(iv)：
$$H(y)=\inf_{r_{KF}z=y}\overline{g_K}(z)\ \le\ \inf_{r_{KF}z=y}g_K(z)=g_F(y), $$
即 $H\le g_F$，故 $\mathcal M(H)\subseteq\mathcal M(g_F)$，取上确界得 $\overline H\le\overline{g_F}$。

两方向合并不等式即 $\overline{g_F}=\overline H$。∎（证明只用了 P1、P4、S1(iv)、$\bar{\cdot}$ 的定义与最大性；引用条件均已就地核验。）

**(c) 最外层 $\bar$ 能否总省去？——不能。**

沿用 S5 的反例（它满足共同设定，甚至满足下半连续性）：$E=\mathbb R^2$，$f=\delta_A$，$A=\{x_1>0,\ x_2\ge1/x_1\}$；取 $K:=E‘\in\mathcal F$（$\dim K=2$），$F:=\mathbb R\psi$（$\psi$ 为第二坐标）。

- $q_{K}:E\to E''=K^*$（$K$ 有限维，$K^*=K’$ 的代数对偶与连续对偶一致）是线性双射（满：P0(c)；单：$q_Kx=0\Rightarrow\varphi(x)=0\ \forall\varphi\in E'\Rightarrow x=0$，Hausdorff 分离），故为线性同胚，且 $g_K=f\circ q_K^{-1}$：纤维是单点。由 P4 与 (3) 中 $f$ 下半连续凸，$g_K$ 下半连续凸，故 $\overline{g_K}=g_K$。
- 于是（代换 $Y=q_Kx$，并注意 $r_{FK}\circ q_K=q_F$，P0(b)）：
$$H(y)=\inf\{g_K(Y):r_{FK}Y=y\}=\inf\{f(x):q_Fx=y\}=g_F(y)\quad(\forall y\in F^*). $$
- 由 S5，$g_F$ 不下半连续，而 $\overline{g_F}$ 下半连续（P8），故 $H\ne\overline{g_F}$；具体地，在 $y_*:=q_F(0,0)$（即 $J(y_*)=0$）处：$H(y_*)=g_F(y_*)=+\infty$，而 $\overline{g_F}(y_*)=0$。后一数值的核验：由 P4，$\overline{g_F}\circ J^{-1}=\overline{\tilde g}=\overline{\delta_{(0,\infty)}}$；显然 $\delta_{[0,\infty)}\in\mathcal M(\delta_{(0,\infty)})$（在 $(0,\infty)$ 上 $0\le0$，在 $0$ 处 $0\le+\infty$，在 $(-\infty,0)$ 上 $+\infty\le+\infty$；且其上图 $=[0,\infty)\times[0,\infty)$ 闭凸）；反之对任一 $h\in\mathcal M(\delta_{(0,\infty)})$：$t>0$ 时 $h(t)\le0$；$h(0)\le0$，因为若 $h(0)>s>0$，则闭集 $S_s(h)$（P3）包含 $(0,\infty)$（其上 $h\le0<s$）而不含 $0$，与 $0\in\overline{(0,\infty)}$ 矛盾（$h(0)=+\infty$ 时取任一 $s>0$ 同理）。故 $\overline{\delta_{(0,\infty)}}=\delta_{[0,\infty)}$，其在 $0$ 处取值 $0$。

因此在 $(E,f,K,F)$ 此例中，$\overline{g_F}=\overline H$ 成立（(b)），但 $\overline{g_F}=H$ 不成立：**右式最外层的 $\bar$ 不能总省去**。∎

**补充观察。** (i) 在 S2 的紧性假设下外层 $\bar$ 可以省去：那时 $g_K$ 下半连续（S2），故 $\overline{g_K}=g_K$，$H=\inf_{rz=y}g_K(z)=g_F$（S1(iv)），而 $g_F$ 下半连续（S2），故 $H=g_F=\overline{g_F}$；本节反例中 $S_0(f)=A$ 非紧，正说明紧性是不可去的。(ii) 把 P8 用于 $(F^*,g_F)$ 并结合 S4 第一步（$(g_F)^*(\varphi)=f^*(\varphi)$，$\varphi\in F$）得显式公式
$$\overline{g_F}(y)=\sup_{\varphi\in F}\big(y(\varphi)-f^*(\varphi)\big),\qquad\text{从而}\quad G(x)=\sup_{F\in\mathcal F}\overline{g_F}(q_Fx), $$
即“恢复 = 各观测水平上恢复出的成本之并”；这与 (b)（水平间的相容）及 (a)（整体恢复恰为 $\bar f$）共同构成恢复与投影之间的完整关系。∎

---

## 完成情况

各阶段均已完整作答：S1（非负、凸、有点有限；相容恒等式；不需取到）、S2（下半连续 + 取到）、S3（构造唯一实现点）、S4（判断为**能**，构造 $G=f^{**}=\bar f$，含扩大观测空间的关系）、S5（判断为**不必**，反例 $\delta_{\{x_1>0,\,x_2\ge1/x_1\}}$）、S6（(a) $G=f\iff f$ 下半连续；(b) $\overline{g_F}=\overline{H}$；(c) 外层 $\bar$ **不能**总省去）。未完成的内容：无。