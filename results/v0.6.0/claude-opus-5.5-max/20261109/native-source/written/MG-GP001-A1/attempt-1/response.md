I（S1–S6）逐项作答如下。S4 中被检验的朴素结论"$X$ 必可缩"不成立，S3 给出满足全部条件的反例；S4 要求的刻画、实现和判据都能完成，证明见下。

## 记号与引用的标准定理

**记号。**
- 对空间 $Z$，锥记为 $CZ=Z\times[0,1]/Z\times\{1\}$，底 $Z\times 0$ 与 $Z$ 等同。
- 非约化悬挂 $\Sigma Z=Z\times[0,1]/(Z\times0,\ Z\times1$ 分别压成一点$)$。$Z\times0$ 的像叫南极 $s$，另一个叫北极。约定 $\Sigma\emptyset=S^0$。
- 若 $Z\ne\emptyset$，则 $\Sigma Z$ 道路连通：沿路径 $[y,(1-\lambda)t]$ 可把任一点连到 $s$。
- 若 $Z\ne\emptyset$，则 $CZ/Z\cong\Sigma Z$：两者都是 $Z\times[0,1]$ 对同一等价关系的商，而商映射的复合仍是商映射。

**单纯复形记号。** 设 $K$ 是有限单纯复形，$v$ 是顶点。
- 删除：$\mathrm{dl}_Kv=\{\sigma\in K:v\notin\sigma\}$。
- 链接：$\mathrm{lk}_Kv=\{\tau\in K:v\notin\tau,\ \tau\cup\{v\}\in K\}$。
- 闭星：$\overline{\mathrm{st}}_Kv=v*\mathrm{lk}_Kv$。
- 对新顶点 $a,b$，单纯悬挂 $M*\{a,b\}=M\cup\{\tau\cup\{a\},\tau\cup\{b\}:\tau\in M\cup\{\emptyset\}\}$。

**引用的标准定理（方括号内为适用条件）。**
- **(T1)** CW 对 $(Y,A)$ 有同伦扩张性质：$Y\times0\cup A\times I$ 是 $Y\times I$ 的强形变收缩核。[Hatcher Prop 0.16，任意 CW 对]
- **(T2)** 紧空间到 Hausdorff 空间的连续满射是闭映射，因而是商映射；连续双射是同胚。若 $q$ 是商映射，则 $q\times\mathrm{id}_I$ 仍是商映射。[$I$ 局部紧 Hausdorff]
- **(T3)** 设 $(X_1,A)$ 是 CW 对，$X_0$ 是任意空间，$f\simeq g:A\to X_0$。则 $X_0\cup_fX_1\simeq X_0\cup_gX_1$ rel $X_0$。[Hatcher Prop 0.18]
  - 证明要点：设 $F$ 是从 $f$ 到 $g$ 的同伦，令 $Z=X_0\cup_F(X_1\times I)$。
  - 由 (T1)，$X_1\times I$ 强形变收缩到 $X_1\times0\cup A\times I$，且这个形变在 $A\times I$ 上不动。
  - 借助 (T2)，它下降为 $Z$ 到 $X_0\cup_fX_1$ 的强形变收缩；对 $X_1\times 1$ 一端同理。
- **(T4)** Hurewicz 定理：单连通空间有 $\pi_2\cong H_2$；$(n-1)$-连通且 $n\ge2$ 时 $\pi_n\cong H_n$。Whitehead 定理：CW 复形之间的弱同伦等价是同伦等价。
- **(T5)** 悬挂同构 $\tilde H_{n+1}(\Sigma Z)\cong\tilde H_n(Z)$，对映射自然。[$Z\neq\emptyset$]
  - 来源：令 $U,V$ 为 $\Sigma Z$ 分别去掉北极、南极后的两个开锥，二者都可缩，且 $U\cap V\cong Z\times(0,1)$；对 $U,V$ 用 Mayer–Vietoris。
  - 对同一开覆盖用 van Kampen：$Z$ 道路连通蕴含 $\Sigma Z$ 单连通。
- **(T6)** 每个有限 CW 复形都同伦等价于某个有限单纯复形 [Hatcher Thm 2C.5]。$\Sigma$ 保持同伦等价：同伦 $H_t$ 诱导同伦 $\Sigma H_t$，连续性由 (T2) 保证。

### 引理 0（顶点处的局部结构）

记 $X=|K|$，$O=X\setminus\{v\}$，$D=|\mathrm{dl}_Kv|$，$L=|\mathrm{lk}_Kv|$。

- **(a)** $D$ 是 $O$ 的强形变收缩核，故 $O\simeq D$。
- **(b)** $X=D\cup|\overline{\mathrm{st}}v|$，且 $D\cap|\overline{\mathrm{st}}v|=L$。
  - 若 $L\ne\emptyset$，则 $(|\overline{\mathrm{st}}v|,L)\cong(CL,L)$，锥点为 $v$，同胚在 $L$ 上是恒等。因此 $X\cong D\cup_LCL$。
  - 若 $L=\emptyset$，则 $X=D\sqcup\{v\}$。
- **(c)** $|M*\{a,b\}|\cong\Sigma|M|$。
- **(d)** 取顶点全序使 $v$ 最小。令 $D_k(K,v)$ 为以含 $v$ 的 $k$ 维单形为基的自由 Abel 群（$k\ge0$），边界为
  $$\partial[v,u_1..u_k]=\sum_{i=1}^k(-1)^i[v,..\widehat{u_i}..].$$
  则对一切 $k\ge0$：
  $$H_k(D_*)\cong H_k(X,O)\cong\tilde H_{k-1}(\mathrm{lk}_Kv),$$
  这里约定 $\tilde H_{-1}(\emptyset)=\mathbb Z$，非空复形的 $\tilde H_{-1}=0$。

**证明。**

(a) 用重心坐标 $x=\sum x_uu$；$x\in O$ 当且仅当 $x_v<1$。
- 令 $r(x)=\sum_{u\ne v}\frac{x_u}{1-x_v}u$。若 $x$ 的支撑是 $\sigma$，则 $r(x)$ 落在非空面 $\sigma\setminus\{v\}$ 上，所以 $r(x)\in D$。
- 令 $H(x,t)=(1-t)x+t\,r(x)$。它留在凸集 $|\sigma|$ 内，且 $v$ 坐标为 $(1-t)x_v<1$，所以留在 $O$ 内。
- 当 $x\in D$ 时 $x_v=0$，故 $H(x,t)\equiv x$。
- 在每个 $|\sigma|\setminus\{v\}$ 上公式连续；对有限闭覆盖用粘接引理即得整体连续。

(b) 每个单形或者不含 $v$（属于删除），或者含 $v$（属于闭星）；两个子复形之交恰为链接。$X$ 是这两个闭集之并，所以它带粘合拓扑。
- 映射 $[y,t]\mapsto(1-t)y+tv$ 是从 $CL$ 到闭星实现的连续双射，逆映射为 $x\mapsto[r(x),x_v]$。
- 由 (T2) 它是同胚，并且在 $t=0$ 处是恒等。

(c) 在 $M*\{a,b\}$ 中，$\mathrm{lk}\,a=M$，$\mathrm{dl}\,a=b*M\cong CM$。由 (b) 得 $|M*\{a,b\}|\cong CM\cup_MCM=\Sigma|M|$。

(d) 不含 $v$ 的单形恰好组成 $\mathrm{dl}_Kv$，所以 $D_*=C_*(K)/C_*(\mathrm{dl}_Kv)$：单纯边界中 $i=0$ 那一项不含 $v$，被模掉。
- 于是 $H_*(D_*)=H_*(K,\mathrm{dl}_Kv)\cong H_*(X,O)$，用到单纯同调等于奇异同调、(a) 与五引理。
- 令 $\phi_k[v,u_1..u_k]=(-1)^k[u_1..u_k]$，且 $\phi_0[v]=\emptyset$。
- 直接计算：
  $$\phi_{k-1}\partial[v,u_1..u_k]=(-1)^{k-1}\sum_i(-1)^i[..\widehat{u_i}..]=(-1)^k\sum_i(-1)^{i-1}[..\widehat{u_i}..]=\tilde\partial\,\phi_k[v,u_1..u_k].$$
- 所以 $\phi$ 是到链接的增广链复形 $\tilde C_{*-1}(\mathrm{lk}_Kv)$ 的链同构。∎

---

## S1 可缩子复形的商

**命题。** 设 $Y$ 为有限 CW 复形，$A\subset Y$ 是非空可缩子复形。则商映射 $q:Y\to Y/A$ 是同伦等价。

**证明。**
1. 取收缩 $h:A\times I\to A$，使 $h_0=\mathrm{id}_A$，$h_1\equiv a_0$。
2. $(Y,A)$ 是 CW 对，由 (T1) 可把 $h$ 扩张为 $F:Y\times I\to Y$，满足 $F_0=\mathrm{id}_Y$ 且 $F_t|_A=h_t$。特别地，对每个 $t$ 有 $F_t(A)\subseteq A$。
3. 定义下降同伦。对每个 $t$，$q\circ F_t$ 把 $A$ 送到点 $q(A)$，因此 $q\circ F$ 在 $q\times\mathrm{id}_I$ 的每根纤维上取常值。
   - $Y\times I$ 紧，$(Y/A)\times I$ Hausdorff，故由 (T2) 知 $q\times\mathrm{id}_I$ 是商映射。
   - $Y/A$ 的 Hausdorff 性：$Y$ 紧 Hausdorff，因而正规。$A$ 外的一点与闭集 $A$ 可用不交开集分开；$A$ 外两点可用与 $A$ 不交的开集分开。这些开集都是饱和的。
   - 所以存在唯一连续的 $\bar F:(Y/A)\times I\to Y/A$，使 $\bar F_t\circ q=q\circ F_t$。
4. 构造逆映射。因为 $F_1(A)=\{a_0\}$，$F_1$ 经 $q$ 分解：存在连续的 $g:Y/A\to Y$ 使 $gq=F_1$。
5. 验证同伦等价：
   - $gq=F_1\simeq F_0=\mathrm{id}_Y$。
   - $qgq=qF_1=\bar F_1q$，而 $q$ 是满射，所以 $qg=\bar F_1\simeq\bar F_0=\mathrm{id}_{Y/A}$。∎

**同伦为何能下降到商。**
- 第一，下降的同伦不是任意取的。它是通过同伦扩张性质扩张 $A$ 内部的收缩得到的，所以每个时刻都有 $F_t(A)\subseteq A$，因而与等价关系相容。一个任意的同伦 $\mathrm{id}\simeq F_1$ 未必在每个时刻保持 $A$，那样就不能在 $Y/A$ 上定义。
- 第二，连续性依赖于 $q\times\mathrm{id}_I$ 是商映射。这里由紧性得到；一般情形可用"$I$ 局部紧 Hausdorff"。
- "$A$ 是子复形"这一条件正是为了保证同伦扩张性质。

## S2 非可缩底空间上的锥附着

**命题。** 设 $D$ 为道路连通有限 CW 复形，$L$ 为非空有限子复形，包含 $i:L\to D$ 零伦，$Y=D\cup_LCL$。则
$$Y\simeq D\vee\Sigma L,$$
楔点为 $D$ 中任意一点 $d_0$ 与 $\Sigma L$ 的南极 $s$ 粘合。

**证明。**
1. $i$ 零伦，即 $i\simeq c_{d_1}$（取常值 $d_1$ 的映射）。$D$ 道路连通，沿一条从 $d_1$ 到 $d_0$ 的道路得 $c_{d_1}\simeq c_{d_0}$。所以对任意 $d_0\in D$ 都有 $i\simeq c_{d_0}$。
2. $(CL,L)$ 是 CW 对（底 $L\times0$ 是子复形）。对 $X_0=D$，$(X_1,A)=(CL,L)$ 用 (T3)：
   $$Y=D\cup_iCL\ \simeq\ D\cup_{c_{d_0}}CL\quad(\text{rel }D).$$
3. 在 $D\cup_{c_{d_0}}CL$ 中，整个底 $L\times0$ 被粘到 $d_0$，所以它就是 $D\vee(CL/L)$，其中 $d_0$ 与 $[L]$ 粘合。两者是 $D\sqcup CL$ 对同一等价关系的商。
4. 而 $CL/L\cong\Sigma L$，$[L]$ 恰为南极 $s$。∎

**楔点的选择。**
- **$D$ 一侧。** $d_0$ 是零伦的终点。由于 $D$ 道路连通，它可以取 $D$ 中任意一点。
- **$\Sigma L$ 一侧。** 自然的选择是锥的底塌缩成的南极 $s$。用翻转 $t\mapsto1-t$ 也可取北极。
- 更一般地，若 $d_0$ 是 $D$ 的 0-胞腔，而 $p\in\Sigma L$ 是任意一点：对 $X_0=\Sigma L$，$(X_1,A)=(D,\{d_0\})$ 用 (T3)，粘合映射 $d_0\mapsto p$ 与 $d_0\mapsto s$ 同伦（因为 $L\neq\emptyset$ 时 $\Sigma L$ 道路连通）。所以同伦型与楔点选择无关。
- 若 $D$ 不连通，则 $d_0$ 必须取在零伦所在的分支。例如 $D=S^1\sqcup\{*\}$，$L=S^0\subset S^1$：在圆周上取楔点得到 $(S^1\vee S^1)\sqcup *$，正确；在孤立点 $*$ 处取楔点得到 $S^1\sqcup S^1$，错误。

## S3 整数扭结的实例

**构造。** 设 $L$ 是 $\mathbb{RP}^2$ 的任一有限三角剖分，顶点集为 $V$。取新顶点 $v,w$ 和 $u\in V$，令
$$K=L*\{v,w\},\qquad B=\{\{v\},\{u\},\{u,v\}\}.$$

**验证。**
- **$O$ 非空可缩。** $\mathrm{lk}_Kv=L$，$\mathrm{dl}_Kv=w*L$，其实现是锥 $C|L|$，非空可缩。由引理 0(a)，$O\simeq C|L|$。
- **$C\setminus\{v\}\to C$ 是同伦等价。** $C=|B|$ 是线段 $[u,v]$，$O\cap C=[u,v)$。两者都可缩，可缩空间之间的映射是同伦等价。
- **$X$ 的同伦型。** 由引理 0(c)，$X\cong\Sigma|L|\cong\Sigma\mathbb{RP}^2$。由 (T5)，$\tilde H_n(X)\cong\tilde H_{n-1}(\mathbb{RP}^2)$。
- **有理约化同调为零。** $\mathbb{RP}^2$ 的胞腔链复形为 $\mathbb Z\xrightarrow{2}\mathbb Z\xrightarrow{0}\mathbb Z$。系数取 $\mathbb Q$ 时乘 2 是同构，所以 $\tilde H_*(\mathbb{RP}^2;\mathbb Q)=0$，从而 $\tilde H_*(X;\mathbb Q)=0$。
- **$X$ 不可缩。** $\tilde H_2(X;\mathbb Z)\cong H_1(\mathbb{RP}^2)=\mathbb Z/2\neq0$。另外 $X$ 是单连通的。

**计算核对。** 对 6 顶点 $\mathbb{RP}^2$（三角形为 123, 134, 145, 156, 126, 235, 245, 246, 346, 356），我用脚本做了 Smith 标准形计算：$D_*(K,v)$ 的同调只在 2 维非零，为 $\mathbb Z/2$，与上述结果一致。

## S4 整体对象与全部恢复目标

**判定。** 朴素结论"$X$ 可缩"不成立，S3 是满足全部条件的反例。所列目标（刻画、实现、判据）都成立，下面给出证明。

### 定理 A（刻画）

在题设条件下，$\mathrm{lk}_Kv\ne\emptyset$，并且商映射
$$X\to X/|\mathrm{dl}_Kv|\cong\Sigma|\mathrm{lk}_Kv|$$
是同伦等价。于是 $X$ 的可能同伦类型恰为全体 $\Sigma Y$，其中 $Y$ 取遍非空有限 CW 复形（等价地，非空有限单纯复形）。

**证明。**
1. **$B$ 条件的真实内容。** 对 $(B,v)$ 用引理 0(d)：$H_k(C,C\setminus v)\cong\tilde H_{k-1}(\mathrm{lk}_Bv)$。
   - 包含 $C\setminus v\to C$ 是同伦等价，故诱导同调同构，从而 $H_*(C,C\setminus v)=0$。
   - 于是 $\mathrm{lk}_Bv$ 非空且 $\mathbb Z$-无环。特别地 $\emptyset\ne\mathrm{lk}_Bv\subseteq\mathrm{lk}_Kv$。
   - 初等的说法：若 $\mathrm{lk}_Bv=\emptyset$，则 $\{v\}$ 是 $C$ 的一个既开又闭的道路分支，$C\setminus v$ 碰不到它，与 $\pi_0$ 双射矛盾。
2. **主体。** $D=|\mathrm{dl}_Kv|\simeq O$，所以 $D$ 是非空可缩子复形。由 S1，$X\to X/D$ 是同伦等价。
   - 由引理 0(b)，$X=D\cup_LCL$ 且 $L\neq\emptyset$。
   - 复合 $CL\to X/D$ 是连续满射，它恰好把 $L$ 压成一点，因此诱导连续双射 $CL/L\to X/D$。由 (T2) 这是同胚，所以 $X/D\cong CL/L\cong\Sigma L$。
   - 另一种看法：用 S2，$D$ 可缩，所以 $L\to D$ 零伦，得 $X\simeq D\vee\Sigma L\simeq\Sigma L$。
3. 所有类型都能出现，由定理 B 与 (T6) 给出。∎

### 定理 B（实现）

对任意非空有限单纯复形 $L$，三元组 $(L*\{v,w\},\ v,\ \{\{v\},\{u\},\{u,v\}\})$（其中 $u$ 为 $L$ 的顶点）满足原条件，且 $X\cong\Sigma|L|$。

- 验证与 S3 逐字相同。
- $B$ 也可以取 $v*\sigma$，$\sigma\in L$ 为任一单形：$|v*\sigma|$ 可缩，去掉 $v$ 后仍可缩。
- 对一般类型 $\Sigma Y$（$Y$ 为有限 CW 复形），由 (T6) 取单纯复形 $L\simeq Y$，则 $\Sigma Y\simeq\Sigma|L|$。

### 关于这一类同伦型的补充

- **必要性质。** $X$ 道路连通；$\tilde H_n(X)\cong\tilde H_{n-1}(\mathrm{lk})$；正次数上同调类的杯积全为零。
  - 杯积为零的理由：取 (T5) 中的可缩开集 $U,V$。正次数类 $\alpha$ 在 $U$ 上限制为零，故来自 $H^*(X,U)$；同理 $\beta$ 来自 $H^*(X,V)$。于是 $\alpha\beta\in H^*(X,U\cup V)=0$。
- **不会出现的例子。** $S^0$、$T^2$、$\mathbb{RP}^2$、$\mathbb{CP}^2$。
- **会出现的例子。**

  | 链接 $L$ | $X$ 的同伦型 |
  |---|---|
  | 一点 | 可缩 |
  | $S^{n-1}$ | $S^n$（$n\ge1$） |
  | $m$ 个点 | $\bigvee_{m-1}S^1$ |
  | $\mathbb{RP}^2$ | $\Sigma\mathbb{RP}^2$ |
  | $T^2$ | $S^2\vee S^2\vee S^3$ |

- **$X$ 不决定链接的同伦型**（见 S6）。
- **$B$ 条件的作用。** 在 $O$ 可缩时，存在满足条件的 $B$ 当且仅当 $v$ 不是孤立点：必要性见定理 A 第 1 步，充分性取 $B$ 为过 $v$ 的一条闭边即可。$B$ 条件只约束 $\mathrm{lk}_Bv$，而它可以只是一个点。
- **修正版本。** 若加强为 $B\supseteq\overline{\mathrm{st}}_Kv$（即 $C$ 是 $v$ 的邻域），则 $\mathrm{lk}_Bv=\mathrm{lk}_Kv$，由第 1 步它是 $\mathbb Z$-无环的，再由定理 C 得 $X$ 可缩。这正是朴素命题的正确形式。

### 定理 C（可缩判据）

在题设条件下，以下各条等价：
1. $X$ 可缩；
2. 有限链复形 $D_*(K,v)$ 在 $\mathbb Z$ 上正合；
3. $\tilde H_*(\mathrm{lk}_Kv;\mathbb Z)=0$；
4. 记 $n_k$ 为含 $v$ 的 $k$ 维单形的个数，$M_k$ 为 $\partial_k$ 的关联矩阵（元素为 $0,\pm1$），$r_k=\mathrm{rank}\,M_k$。则对一切 $k$ 有 $n_k=r_k+r_{k+1}$，且每个 $M_k$ 的非零不变因子都等于 1。

这些条件只用到含 $v$ 的单形及其面之间的关联数，用 Smith 标准形即可有限地检验。条件 2 也等价于局部同调 $H_*(X,X\setminus v;\mathbb Z)=0$。

**证明。**
- **(2)⇔(3)。** 由引理 0(d)，且链接非空。
- **(2)⇔(4)。** 由 Smith 标准形，
  $$H_k(D_*)\cong\mathbb Z^{\,n_k-r_k-r_{k+1}}\oplus\bigoplus_j\mathbb Z/d_j(M_{k+1}).$$
  这里 $Z_k=\ker\partial_k$ 是 $D_k$ 的直和项，所以 $Z_k/B_k$ 的挠部分等于 $\mathrm{coker}\,M_{k+1}$ 的挠部分。
- **(1)⇔(3)。** 由定理 A，$X\simeq\Sigma L$，$L\ne\emptyset$。只需证明 $\Sigma L$ 可缩当且仅当 $\tilde H_*(L)=0$：
  - (⇒) 由 (T5)，$\tilde H_n(L)\cong\tilde H_{n+1}(\Sigma L)=0$。
  - (⇐) $\tilde H_0(L)=0$ 且 $L\neq\emptyset$，故 $L$ 道路连通。由 (T5)，$\Sigma L$ 单连通且约化同调为零。由 (T4) 的 Hurewicz 定理逐次得各 $\pi_n=0$。$\Sigma L\cong|L*\{a,b\}|$ 是 CW 复形，由 Whitehead 定理它可缩。∎

**注。**
- 系数不能换成 $\mathbb Q$：S3 中 $D_*\otimes\mathbb Q$ 正合，但 $H_2(D_*)=\mathbb Z/2$。
- "链接可缩"是充分条件但不是必要条件。标准例子：Poincaré 同调球去掉一个开 3-单形，它无环但 $\pi_1$ 是 120 阶群。以它为链接时 $X$ 可缩。

## S5 不提供子复形 B

**结论：不必。** 新增的同伦型恰好只有一种，即 $S^0$（两点）。它出现当且仅当 $v$ 是孤立顶点。

**证明。**
- **一般公式。** 若 $\mathrm{lk}_Kv\ne\emptyset$，定理 A 第 2 步没有用到 $B$，照样给出 $X\simeq\Sigma|\mathrm{lk}_Kv|$。若 $\mathrm{lk}_Kv=\emptyset$，则 $X=D\sqcup\{v\}\simeq S^0$，因为 $D\simeq O$ 可缩。合起来就是 $X\simeq\Sigma|\mathrm{lk}_Kv|$，其中约定 $\Sigma\emptyset=S^0$。
- **实现。** 取 $K=\{\{v\},\{w\}\}$，则 $O=\{w\}$ 非空可缩，$X=S^0$。
- **确实是新类型。** 对 $Y\ne\emptyset$，$\Sigma Y$ 道路连通，而 $S^0$ 不连通，所以 $S^0\not\simeq\Sigma Y$。
- 因此可能类型为 $\{\Sigma Y:Y\text{ 非空有限}\}\cup\{S^0\}$。
- 判据 (2) 在这里仍然逐字成立：若链接为空，则 $H_0(D_*)=\mathbb Z\ne0$，而此时 $X\simeq S^0$ 也确实不可缩。

## S6 悬挂信息的逆向恢复

**结论：不必。** 由 $\Sigma|L_1|\simeq\Sigma|L_2|$ 推不出 $|L_1|\simeq|L_2|$。

**反例的构造。**
- 设 $T$ 是环面的任一三角剖分（例如 7 顶点三角剖分，三角形为 $\{i,i+1,i+3\}$ 与 $\{i,i+2,i+3\}$，$i\in\mathbb Z/7$）。
- 取一个 2-单形 $\Delta$，令 $A=T\setminus\{\Delta\}$（只去掉 $\Delta$ 本身，保留它的面），$\gamma=\partial\Delta$。
- 设 $T'=A\cup c*\gamma$ 为在 $\Delta$ 上做星形细分所得，$|T'|\cong|T|$。由引理 0(a)，$|A|\simeq$ 去掉一点的环面 $\simeq S^1\vee S^1$。
- 再取 $\sigma\in A$ 为一个 2-单形，$c'$ 为新顶点，令 $W=A\cup c'*\partial\sigma$。
- 取 $L_1=T$，$L_2=W$。

**(i) $|T|\not\simeq|W|$。**
- $|W|$ 是在 $|A|$ 上沿圈 $\partial\sigma$ 粘一个 2-胞腔得到的，而 $\partial\sigma$ 在 $|A|$ 中零伦（它是 $|\sigma|\subseteq|A|$ 的边界）。
- 由 Hatcher Prop 1.26（在道路连通空间上粘 2-胞腔），$\pi_1|W|\cong\pi_1|A|\cong F_2$，非交换。
- 而 $\pi_1|T|\cong\mathbb Z^2$ 是交换群。

**(ii) $[\gamma]=0\in H_1(A)$。**
- $C_*(T)/C_*(A)$ 只有 2 维的 $\mathbb Z\Delta$，且 $\partial\Delta=\gamma$。
- 正合列 $H_2(T,A)\to H_1(A)\to H_1(T)\to H_1(T,A)=0$ 表明 $\mathbb Z^2=H_1(A)\to H_1(T)=\mathbb Z^2$ 是满射，因而是单射。
- 所以 $[\gamma]=\partial[\Delta]$ 落在零核中，即为零。
- 我用脚本对 7 顶点环面做了核对：$H_1(A)=\mathbb Z^2$，且 $\gamma$ 是 $A$ 中的整边界。

**(iii) $\Sigma|T|\simeq\Sigma|W|$。**
1. 令 $K_1=T'*\{a,b\}$，$K_2=W*\{a,b\}$。
2. 在顶点 $c$（对 $K_1$）和 $c'$（对 $K_2$）处，删除都等于 $A*\{a,b\}$，其实现记为 $E\cong\Sigma|A|$。两处的链接分别为 $S_1=|\gamma*\{a,b\}|$ 与 $S_2=|\partial\sigma*\{a,b\}|$，二者都同胚于 $S^2$。
3. 由引理 0(b)(c)，$\Sigma|T|\cong E\cup_{S_1}CS_1$，$\Sigma|W|\cong E\cup_{S_2}CS_2$。
4. **$S_2\subset E$ 零伦。** $S_2\subset|\sigma*\{a,b\}|\cong\Sigma|\sigma|$，而后者可缩。
5. **$S_1\subset E$ 零伦。**
   - 由 (T5)，$E$ 单连通，因为 $|A|$ 连通。
   - 由 (T4)，$\pi_2(E)\cong H_2(E)$。
   - 由悬挂同构的自然性，包含映射的 Hurewicz 像为 $\pm s(i_*[\gamma])$，由 (ii) 等于 0。所以包含映射零伦。
6. $E$ 道路连通，由 S2：$\Sigma|T|\simeq E\vee_{s}\Sigma S_1$，$\Sigma|W|\simeq E\vee_{s}\Sigma S_2$，两边在 $E$ 中取同一楔点。
7. 3-圈之间的同构 $\gamma\cong\partial\sigma$ 诱导保持南极的同胚 $\Sigma S_1\cong\Sigma S_2$。故 $\Sigma|T|\simeq\Sigma|W|$，两者都同伦等价于 $S^2\vee S^2\vee S^3$。

脚本核对两者的整同调相同。∎

**直观原因。** 环面顶胞腔的粘合映射是交换子：它在 $\pi_1$ 中非平凡，但在 $H_1$ 中为零。悬挂之后进入 $\pi_2=H_2$ 的范围，这个粘合映射就变成零伦。

**另一个反例。** 取 $L_1=$ 一点，$L_2=$ 无环但不可缩的复形（例如 S4 注中的 Poincaré 同调球去掉一个开 3-单形）。由 S4 的引理，两者的悬挂都可缩，但 $L_2$ 不可缩。

**悬挂能恢复的信息。** 一般只能恢复 $\tilde H_*(L)$（平移一维），由此得到连通分支数等。$\pi_1$、杯积和同伦型都恢复不出来。