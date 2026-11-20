# 审阅报告（修订稿）：《探针映射空间与连续性层级》答卷

## 一、总体结论

答卷对 S1–S6 全部作答，没有标记未完成的内容。逐项核对后，没有漏答的要求项。

1. **所有判断和构造的结论都正确。**
   - 判断题：S4(1) 为否，S4(2) 为是，S5 为否，S6(3) 为能。
   - S6(2) 的充要条件为：$k(f):kX\to kY$ 是同胚。
   - 构造：$M(X,Y)=k\,C_{co}(kX,kY)$、$ev$ 与复合映射都具备题目要求的性质。
2. **S1、S2、S4、S5、S6 的论证在原题条件下成立。** 只有可以直接补上的省略，以及两处错误但不影响结论的中间表述（S2(3) 与 S5）。
3. **S3 的结论全部正确，但书面证明不完整。**
   - (a) 第 1 小节第 4 步援引 S1 时，S1 的条件不满足，这一步论证无效。
   - (b) 题目明确要求的两项只有断言、没有验证：一是同构关于 $S$ 的自然性，二是"$\alpha\mapsto ev\circ(\alpha\times I)$ 恰好就是该双射"。

   第三节给出完整补证。S6 对 S3 的引用不依赖这些缺口。

| 阶段 | 答卷结论 | 审阅判断 |
|---|---|---|
| S1 | ev 连续；柯里化双射及其自然性 | 正确；自然性中诱导映射的连续性未说明 |
| S2 | $\tau_{prof}=\tau_k$；$\mathrm{Nat}(h_X,h_Y)\cong C(kX,kY)$；充要条件是 $X$ 紧生成 | 正确；(3) 有一个错误的中间断言，不影响结论 |
| S3 | $M=k\,C_{co}(kX,kY)$，ev，伴随同构，关于 $X,Y$ 的自然性 | 构造和结论正确；**第 4 步论证无效，两项要求未验证**，可补（第三节） |
| S4 | (1) 否（$\mathbb Q,\mathbb R$）；(2) 是 | 正确 |
| S5 | 否（$\mathrm{id}:kZ\to Z$，超滤空间） | 正确；一处措辞错误，无害 |
| S6 | 连续复合、结合律与单位律；$h_f$ 同构 ⟺ $k(f)$ 同胚；能升级 | 正确 |

## 二、逐阶段核查

### S1：正确

- **求值映射连续。** 局部紧 Hausdorff 空间是正则的，并且有紧邻域基，所以可以取开集 $V\ni x_0$，使 $K=\overline V$ 紧且 $K\subset f_0^{-1}W$。于是 $[K,W]\times V\subset ev^{-1}W$。论证正确。
- **柯里化。**
  - $\Phi(g)=ev\circ(g\times\mathrm{id})$ 连续。这个方向通过 ev 用到了 $X$ 局部紧。
  - $\Psi(F)$ 连续，用的是推广的管道引理：$\{z_0\}\times K\subset O$ 且 $K$ 紧，则存在 $V\times K\subset O$。**这个方向对任意空间都成立**，第三节会用到。
  - 两者互逆。
- **自然性。** 三个等式都正确。但答卷把 $C(X,k)\circ g$ 和 $C(j,Y)\circ g$ 当作 $C(Z,C_{co}(\cdot,\cdot))$ 的元素使用，却没有说明它们连续。下面两种补法任选其一：
  - 后复合与预复合在紧开拓扑下连续：$(k_*)^{-1}[K,O']=[K,k^{-1}O']$，$(j^*)^{-1}[K',O]=[j(K'),O]$，其中 $j(K')$ 紧。
  - 或者注意到 $z\mapsto k\circ g(z)$ 就是 $\Psi(k\circ\Phi(g))$，$z\mapsto g(z)\circ j$ 就是 $\Psi(\Phi(g)\circ(\mathrm{id}\times j))$，而 $\Psi$ 总给出连续映射。

  另外，答卷用字母 $k$ 表示映射 $Y\to Y'$，与 $k$ 化的记号冲突，属于表述问题。

### S2：结论正确

**(1) 正确。**
- $\tau_k\subset\tau_{prof}$：profinite 探针都是紧 Hausdorff 探针。
- 反方向：$\pi:\beta D\twoheadrightarrow K$ 是从紧空间到 Hausdorff 空间的连续满射，所以是闭映射，因此 $f^{-1}(A)=\pi(\pi^{-1}f^{-1}A)$ 是闭集。
- $\beta D$ 紧 Hausdorff 且零维，所以完全不连通。
- 省略：答卷没有说明 $\beta D$ 是 U 小的。补充：$\beta D$ 可以取为 $D$ 上全体超滤子的集合，它包含于 $\mathcal P(\mathcal P(D))\in U$，它的拓扑也属于 $U$。

**(2) 正确。** 要点有三条：
- 沿点包含 $i_s:*\to S$ 的自然性给出 $\alpha_S(f)=g\circ f$，所以 $\alpha$ 由底层函数 $g$ 决定；
- 对 $S\in\mathrm{Prof}_U$，有 $C(S,Y)=C(S,kY)$；
- 由 (1)，$kX$ 恰好是全体 profinite 探针给出的终拓扑。

因此，使所有 $g\circ f$ 都连续的 $g$ 恰好组成 $C(kX,kY)$，后复合给出逆映射。

**(3) 结论正确，但有一个错误的中间断言。** 答卷写道："连续 $f:X\to Y$ 诱导的自然变换对应于集合 $C(X,kY)$。"这是错的。在 (2) 的对应下 $h_f\leftrightarrow f$，所以诱导出的变换对应的集合是 $C(X,Y)$。由 $k$ 的函子性，$C(X,Y)\subset C(kX,kY)$。

- **反例：** 取 $Z$ 为 S5 中的超滤空间。$\mathrm{id}_Z\in C(Z,Z)$ 诱导恒等变换；但 $kZ$ 离散而 $Z$ 不离散，所以 $\mathrm{id}\notin C(Z,kZ)$。
- **影响：** 答卷实际证明的是"$\forall Y,\ C(kX,kY)=C(X,kY)$ ⟺ $kX=X$"，而题目要求的是"$\forall Y,\ C(kX,kY)=C(X,Y)$ ⟺ $kX=X$"。
  - 因为 $C(X,kY)\subset C(X,Y)\subset C(kX,kY)$，答卷的 ⇐ 方向直接给出题目的 ⇐ 方向。
  - 答卷的 ⇒ 方向只用到 $Y=kX$。这时 $kY=kX=Y$，从而 $C(X,kY)=C(X,Y)$，原论证不改一字即适用于题目的命题。

  所以结论不受影响。
- **幂等性 $k(kX)=kX$。** 答卷没有证明，但证明很直接：对 U 小紧 Hausdorff 空间 $K$，有 $C(K,X)=C(K,kX)$，所以两个空间的探针族相同。也可以完全不用幂等性：$h_X$ 与 $h_{kX}$ 作为预层逐字相同。若恒等变换 $h_X\to h_{kX}$ 由某个连续映射 $g:X\to kX$ 诱导，则 $g$ 在每一点上都是恒等，于是 $kX=X$。

### S3：构造与结论正确，书面证明有缺口

**正确的部分**

- **构造本身。** 底集为 $C(kX,kY)$，拓扑为 $k\,C_{co}(kX,kY)$。用单点紧集可以分离不同的函数，所以它是 Hausdorff 的；由幂等性，它是紧生成的。底集包含于 $\mathcal P(X\times Y)\in U$，所以是 U 小的（答卷没有提）。
- **第 1、2、3、5 步。**
  - 第 1 步：$h_S\times h_X\cong h_{S\times X}$（积的泛性质），再用 S2。
  - 第 2 步：$k(S\times X)=k(S\times kX)$。两边的探针都是坐标对 $(a,b)$，而 $b:K\to X$ 连续 ⟺ $b:K\to kX$ 连续。
  - 第 3 步：Cohen 定理（局部紧 Hausdorff 空间与 k 空间之积是 k 空间）的条件成立。$S$ 紧 Hausdorff，因而局部紧；$kX$ 是 Hausdorff k 空间。对 Hausdorff 空间，题面的探针定义与经典的紧子集定义等价。
  - 第 5 步：$S$ 紧 Hausdorff，所以 $C(S,C_{co})=C(S,k\,C_{co})$。
- **ev 的构造。** 答卷援引"CGHaus 中的求值映射 $k\,C_{co}(A,B)\times_k A\to B$ 连续"，其条件成立：$A=kX$、$B=kY$ 都是紧生成 Hausdorff 空间。自然性公式正确。
- **Z 部分的三个双射都合法：**
  - S2；
  - $k(Z\times X)=kZ\times_k kX$，与第 2 步同样的探针论证；
  - CGHaus 的笛卡尔闭性。

**缺口 (a)：第 4 步的援引失效。** 答卷称"由 S1 的指数律（由于 $S$ 局部紧 Hausdorff）"得到
$$C(S\times kX,kY)\cong C(S,C_{co}(kX,kY)).$$
- S1 的局部紧假设加在函数空间的**定义域**上，在这里就是 $kX$。而 $kX$ 一般不局部紧，例如 $X=\mathbb Q$ 时 $kX=\mathbb Q$。
- 由 $S$ 局部紧只能推出另一个式子：$C(kX\times S,kY)\cong C(kX,C_{co}(S,kY))$。

因此这一步作为写出的论证不成立。不过这个等式本身是对的，证明见命题 3.1。

**缺口 (b)：两项要求只有断言。**
- 题目要求 $C(S,M)\cong H_{X,Y}(S)$ 关于 $S$ 自然，答卷只写了"自然具备双射"。补证见 3.2。
- 题目要求证明的是**这个具体映射** $\alpha\mapsto ev\circ(\alpha\times I)$ 是双射。答卷只说明了两边分别与 $C(kZ,M)\cong C(kZ\times_k kX,kY)$ 对应，"恰由 $\alpha\mapsto ev\circ(\alpha\times I)$ 实现"这一句没有计算。缺了这一步，只能得出两个集合之间存在某个双射，得不出这个映射本身是双射。补证见 3.3。

**次要省略。** 答卷没有证明 $M(u,Y)$ 与 $M(X,v)$ 连续，补证见 3.5。关于 $X,Y$ 的两个自然性恒等式本身是正确的。

**影响范围**
- 缺口只涉及第 1 小节（可表示性）的推导，以及第 2 小节中把具体映射识别为该双射的那一步。
- ev 的构造、Z 部分的三个双射、S6 对 S3 的引用都不依赖第 4 步。S6 只用到 $M$ 紧生成以及 CGHaus 中的求值和伴随。
- 3.4 说明，可表示性及其关于 $S$ 的自然性，也可以由 Z 部分取 $Z=S$ 再用 Yoneda 引理得到。

所以 S3 的全部结论成立。

### S4：正确

**(1) 判断"否"，正确。** 答卷取 $X=\mathbb Q$，$Y=\mathbb R$。$\mathbb Q$ 是度量空间，所以第一可数且 Hausdorff；又因 $\mathbb N\in U$，它是 U 小的。逐步核对如下：
- **零函数处的邻域基。** 设 $\bigcap_{i\le n}[K_i,O_i]\ni 0$。略去 $K_i=\varnothing$ 的项后，其余每个 $O_i$ 都含 $0$。取 $(-\varepsilon,\varepsilon)\subset\bigcap O_i$，$K=\bigcup K_i$，则 $[K,(-\varepsilon,\varepsilon)]\subset\bigcap[K_i,O_i]$。答卷说"基开邻域形式为 $[K,(-\varepsilon,\varepsilon)]$"，措辞不精确；但这类集合确实构成邻域基，足以导出矛盾。
- **紧集无内点。** 紧集 $K\subset\mathbb Q$ 在 $\mathbb Q$ 中没有内点：若 $a<b$ 且 $(a,b)\cap\mathbb Q\subset K$，由于 $K$ 在 $\mathbb R$ 中闭，会得到 $[a,b]\subset K\subset\mathbb Q$，矛盾。
- **鼓包函数。** 取 $q\in V\setminus K$，令 $\delta=\mathrm{dist}(q,K)>0$（若 $K=\varnothing$，取 $f\equiv2$ 即可）。鼓包函数满足 $f\in[K,(-\varepsilon,\varepsilon)]$，但 $f(q)=2\notin(-1,1)$。

反例有效。

*附注（说明机制，不影响判断）。* 设 $X$ 是 Tychonoff（完全正则 Hausdorff）空间，则 $ev:C_{co}(X,\mathbb R)\times X\to\mathbb R$ 连续当且仅当 $X$ 局部紧。
- ⇐：即 S1。
- ⇒：在 $(0,x_0)$ 处对 $W=(-1,1)$ 使用连续性，按上面的邻域基得到紧集 $K$、$\varepsilon>0$ 和开集 $V\ni x_0$，使 $[K,(-\varepsilon,\varepsilon)]\times V\subset ev^{-1}W$。假设存在 $q\in V\setminus K$。$K$ 紧因而闭，由完全正则性，存在连续函数 $\varphi:X\to[0,1]$，$\varphi(q)=1$，$\varphi|_K=0$。于是 $2\varphi\in[K,(-\varepsilon,\varepsilon)]$，但 $ev(2\varphi,q)=2\notin W$，矛盾。所以 $x_0\in V\subset K$，即 $x_0$ 有紧邻域。∎

答卷的 $\mathbb Q$ 是这个命题的特例。完全正则不能减弱为正则：Hewitt（1946）构造了一个正则 $T_1$ 空间，其上的连续实函数全是常数。在这样的空间上 $C_{co}(X,\mathbb R)\cong\mathbb R$，ev 就是投影，因而连续；但这样的空间（多于一点时）不是 Tychonoff 的，所以不局部紧。

**(2) 判断"是"，正确。**
- 设 $x_0\in\overline A\setminus A$，取 $x_n\in A\cap V_n$，则 $x_n\to x_0$。
- $K=\{x_n\}\cup\{x_0\}$ 是紧 Hausdorff 子空间，其包含映射是 U 小探针。
- $A$ 是 k 闭集，所以 $A\cap K$ 在 $K$ 中闭，从而 $x_0\in A$，矛盾。

### S5：正确

- **一般机制正确。** 对 $S\in\mathrm{Prof}_U$，有 $C(S,kZ)=C(S,Z)$，所以 $h_{\mathrm{id}}$ 的每个分量都是恒等，它是自然同构。而 $\mathrm{id}:Z\to kZ$ 连续 ⟺ $kZ=Z$。另外，$kZ$ 是 U 小 Hausdorff 空间，满足题面对空间的要求。
- **具体例子正确。**
  - 拓扑良定：不含 $p$ 的子集都是开集；含 $p$ 的子集 $A$ 开 ⟺ $A\cap\mathbb N\in\mathcal U$。
  - 空间是 Hausdorff 的，紧集都是有限集。
  - 按题面的探针定义：任一探针 $f:K\to Z$ 的像是紧的，因而有限；$f^{-1}(A)$ 是有限个闭纤维的并，仍是闭集。所以 $kZ$ 离散。
  - $\{p\}$ 不是开集。
  - 自由超滤子的存在由选择公理保证，在 ZFC 中可用；并且 $Z\in U$。
- **措辞错误。** "恰有一个集合不属于 $\mathcal U$"应改为"至少有一个"。当 $K\cap\mathbb N\notin\mathcal U$ 时，$A_1$ 和 $A_2$ 都不属于 $\mathcal U$。论证只用到"至少一个"，所以无害。

### S6：正确

- **(1) 正确。** 在 CGHaus 中取 $ev_{Y,Z}\circ(\mathrm{id}\times_k ev_{X,Y})\circ(\text{结合同构})$，经伴随得到复合映射，其底层函数是 $(g,f)\mapsto g\circ f$。对结合律和单位律，两边的连续映射在底层函数上逐点相等，所以相等。
- **(2) 正确。** S2 的对应 $\alpha\leftrightarrow g$（$\alpha_S(f)=g\circ f$）保持复合与恒等：$(\beta\circ\alpha)_S(f)=g'\circ g\circ f$。所以 $h_f$ 可逆 ⟺ $k(f)$ 在紧生成空间范畴中可逆 ⟺ $k(f):kX\to kY$ 是同胚。

  交叉核验：预层之间的自然变换是同构，当且仅当每个分量都是双射。
  - 在 $S=*$ 处，这正是 $f$ 为双射。
  - 当 $f$ 是双射时，$h_f(S)$ 为满射 ⟺ 对每个 $p\in C(S,Y)$，都有 $f^{-1}\circ p\in C(S,X)$。由 S2(2) 的论证，这恰好等价于 $f^{-1}:kY\to kX$ 连续。

  与答卷给出的条件一致。
- **(3) 判断"能"，正确。** 由 S4(2)，$kX=X$ 且 $kY=Y$，所以 $f=k(f)$ 是同胚。

  附注：这个论证实际上只用到 $kY=Y$，因为此时 $f^{-1}:Y=kY\to kX\to X$ 连续。只假设 $X$ 第一可数是不够的：在 S5 的例子中，$X=kZ$ 离散，因而第一可数，但 $\mathrm{id}:kZ\to Z$ 不是同胚。由前一句还可知，该例中的 $Z$ 必定不是第一可数的。

## 三、S3 的补证

### 3.1 命题（替换第 4 步）

设 $S$ 是 U 小紧 Hausdorff 空间，$X,Y$ 是 Hausdorff 空间。则 $\Phi(g)(s,x)=g(s)(x)$ 给出双射
$$C(S,C_{co}(kX,kY))\ \xrightarrow{\ \cong\ }\ C(k(S\times X),kY).$$
结合答卷第 3 步的 $k(S\times X)=S\times kX$，这正是第 4 步所述的等式。

*证明。*
- **$\Phi(g)$ 连续。** $k(S\times X)$ 是全体紧 Hausdorff 探针 $(a,b):K\to S\times X$ 给出的终拓扑，所以只需证明每个 $\Phi(g)\circ(a,b)$ 连续。
  1. $b$ 作为映射 $K\to kX$ 是连续的。
  2. $b^*:C_{co}(kX,kY)\to C_{co}(K,kY)$，$\varphi\mapsto\varphi\circ b$，是连续的，因为 $(b^*)^{-1}[L,O]=[b(L),O]$。
  3. 于是 $\Phi(g)\circ(a,b)(t)=ev_K\big(b^*(g(a(t))),t\big)$。
  4. $K$ 是紧 Hausdorff 空间，此时 S1 的条件真正成立，所以 $ev_K:C_{co}(K,kY)\times K\to kY$ 连续。

  因此 $\Phi(g)\circ(a,b)$ 连续。
- **$\Psi(F)(s)=F(s,\cdot)$ 连续。** 映射 $x\mapsto(s,x)$ 从 $kX$ 到 $k(S\times X)$ 连续，因为它与任一探针 $b$ 的复合是探针 $(c_s,b)$。
- **$\Psi(F)$ 连续。** 设 $L\subset kX$ 紧，$O\subset kY$ 开。$S\times L$ 是紧 Hausdorff 空间，它到 $S\times X$ 的包含映射连续，因而是一个探针，所以 $F|_{S\times L}$ 连续。在 $S\times L$ 中使用管道引理，得到 $\{s:F(\{s\}\times L)\subset O\}$ 是开集。
- **互逆。** 显然。∎

这个证明不依赖 Cohen 定理。另一条路线是直接使用 CGHaus 的笛卡尔闭性：$C(S\times_k kX,kY)\cong C(S,k\,C_{co}(kX,kY))=C(S,M)$，其中 $S\times_k kX=k(S\times X)$。

### 3.2 关于 $S$ 的自然性

沿第 1–5 步追踪，$\varphi\in C(S,M)$ 对应的自然变换是
$$(\eta_\varphi)_T(a,b)=[t\mapsto\varphi(a(t))(b(t))].$$
对任意 $\sigma:S'\to S$，有 $\eta_{\varphi\circ\sigma}(a',b)=\eta_\varphi(\sigma\circ a',b)$，即
$$\eta_{\varphi\circ\sigma}=\eta_\varphi\circ(h_\sigma\times\mathrm{id})=H_{X,Y}(\sigma)(\eta_\varphi).$$

### 3.3 识别 $\alpha\mapsto ev\circ(\alpha\times I)$

设 $\alpha\in\mathrm{Nat}(h_Z,h_M)$ 在 S2 下对应 $g\in C(kZ,M)$，即 $\alpha_T(a)=g\circ a$。则
$$(ev\circ(\alpha\times I))_T(a,b)=[t\mapsto g(a(t))(b(t))]=g^\flat\circ(a,b),$$
其中 $g^\flat:kZ\times_k kX\to kY$，$g^\flat(z,x)=g(z)(x)$，是 $g$ 在 CGHaus 中的伴随。

经由 $h_Z\times h_X\cong h_{Z\times X}$ 与 $k(Z\times X)=kZ\times_k kX$，$g^\flat$ 在 S2 下对应的自然变换正是 $(a,b)\mapsto g^\flat\circ(a,b)$。所以 $\alpha\mapsto ev\circ(\alpha\times I)$ 等于三个双射的复合
$$\alpha\mapsto g\mapsto g^\flat\mapsto(g^\flat\circ-),$$
因而是双射。

### 3.4 另一条路线（绕过第 4 步）

对 $S\in\mathrm{Prof}_U$，Yoneda 引理给出 $C(S,M)=h_M(S)\cong\mathrm{Nat}(h_S,h_M)$，$\varphi\mapsto h_\varphi=(a\mapsto\varphi\circ a)$，并且关于 $S$ 自然。

再取 $Z=S$ 并应用 3.3，得到 $\varphi\mapsto ev\circ(h_\varphi\times I)=\eta_\varphi$。这一步同样关于 $S$ 自然：
$$ev\circ((\alpha\circ h_\sigma)\times I)=(ev\circ(\alpha\times I))\circ(h_\sigma\times I).$$

因此，可表示性及其自然性完全可以由答卷第 2 小节加上 3.3 推出，而且得到的映射与答卷第 1 小节所要的双射是同一个。

### 3.5 函子性映射的连续性

- $u:X'\to X$ 连续，则 $k(u):kX'\to kX$ 连续。这是 $k$ 的函子性：探针与 $u$ 复合后仍是探针。
- $u^*:C_{co}(kX,kY)\to C_{co}(kX',kY)$ 连续，因为 $(u^*)^{-1}[L',O]=[u(L'),O]$。再用 $k$ 的函子性，得到 $M(u,Y)$ 连续。
- 同理，由 $(v_*)^{-1}[L,O']=[L,v^{-1}O']$ 得到 $M(X,v)$ 连续。
- 两个自然性恒等式逐点成立：
  $$(\varphi(t)\circ u)(\psi'(t))=\varphi(t)(u(\psi'(t))),\qquad v(\varphi(t)(\psi(t)))=(v\circ\varphi(t))(\psi(t)).$$
- 由此得到 $\eta_{M(u,Y)\circ\varphi}=\eta_\varphi\circ(I\times h_u)$，$\eta_{M(X,v)\circ\varphi}=h_v\circ\eta_\varphi$。也就是说，3.2–3.4 中的双射关于 $X,Y$ 同样自然。

## 四、问题清单

| # | 位置 | 性质 | 影响 |
|---|---|---|---|
| 1 | S3 第 1 小节第 4 步 | 援引 S1 时条件不满足：需要 $kX$ 局部紧，$S$ 局部紧与此无关 | 该步论证无效；等式本身为真（3.1），可表示性也可由 3.4 得到 |
| 2 | S3 | 两项题目要求只有断言：关于 $S$ 的自然性；$\alpha\mapsto ev\circ(\alpha\times I)$ 就是复合双射 | 书面证明的缺口，容易补（3.2、3.3） |
| 3 | S2(3) | 把诱导变换的集合误写为 $C(X,kY)$，应为 $C(X,Y)$（有反例） | 无影响；两个方向的论证对正确命题仍然成立 |
| 4 | S5 | "恰有一个"应为"至少有一个" | 无影响 |
| 5 | S1、S3 | 函数空间之间诱导映射的连续性没有证明 | 常规验证，已补（S1 一节与 3.5） |
| 6 | S2(1)、S2(3)、S3、S4(1) | 未写出：$\beta D$ 与 $M$ 的 U 小性、$k$ 的幂等性、邻域基的说明 | 次要，已补 |

## 五、最终评定

在原题条件下：
- 答卷所有判断都正确，所给反例都经过完整核验；
- 所有构造都正确，并具备题目要求的性质；
- S1、S2、S4、S5、S6 的证明成立，只有次要的省略和两处无害的错误表述；
- S3 的结论全部正确，但书面证明不完整：第 4 步论证无效，两项要求只有断言。

按第三节补证后，答卷构成对原题的完整解答。

---

## 本轮修订说明与自评

**保留的部分：** 上一版对六个阶段的全部判断，即结论全对、主要缺陷在 S3 第 4 步、S2(3) 与 S5 的错误表述无害，以及各项省略的认定。第三节命题的证明思路也保留。

**修正的部分：**
1. 上一版在 S4 附注中写"对正则的 $X$，ev 连续 ⟺ $X$ 局部紧"，这是错的。现改为 Tychonoff 空间，补上证明，并说明只假设正则时为何不成立。
2. 上一版的最终评定写"各阶段完整"，与 S3 存在缺口相矛盾。现改为"S3 书面证明不完整，补证后完整"。
3. $\alpha\mapsto ev\circ(\alpha\times I)$ 的识别是题目明确要求证明的内容，现从"次要省略"上调为 S3 的书面缺口。
4. 上一版说答卷后文"只依赖 CGHaus 的笛卡尔闭性"，不准确。现改为：同时依赖 S2、$k(Z\times X)=kZ\times_k kX$ 和笛卡尔闭性。
5. 关于 S1，上一版说"否则 $C(X,k)\circ g$ 未必属于 $C(Z,C_{co}(X,Y'))$"，说法过强。它其实确实属于，因为它等于 $\Psi(k\circ\Phi(g))$；答卷缺的只是这条理由。

**新增的部分：**
- 3.1 改用不依赖 Cohen 定理的证明；
- 3.4 的 Yoneda 路线；
- 3.5 中关于 $X,Y$ 的自然性推论；
- S2(3) 不用幂等性的论证；
- S6(2) 的逐分量交叉核验；
- S6(3) 的附注：只需 $Y$ 紧生成，而只假设 $X$ 第一可数不够。

**仍不确定的部分：** Hewitt 空间的存在是凭记忆援引的文献结果，只用来说明附注为什么需要完全正则性，不影响任何审阅判断。其余断言都在文中给出了证明，或说明了所援引标准定理的适用条件，包括 Cohen 定理、CGHaus 的笛卡尔闭性、Yoneda 引理和管道引理。

**自评：** 本稿对答卷每一项结论都给出了可核查的依据，并把问题分为五类：
- 结论错误：未发现；
- 论证无效：S3 第 4 步；
- 要求项只有断言：S3 两处；
- 错误但无害的中间表述：S2(3)、S5；
- 常规省略。

所有缺口都给出了补证，并说明了影响范围；没有因为局部缺口而否定其他独立成立的结果。上一版中已发现的数学错误（S4 附注）已经修正。剩下的主观成分在于严重程度怎么划分，例如 S3 的两处断言算作"缺口"还是"省略"，这不改变任何数学事实。