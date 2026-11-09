# 审阅报告：《探针映射空间与连续性层级》答卷

## 一、总体结论

答卷六个阶段都已作答，未标记未完成内容。实际核对后也没有发现漏答的阶段。

**所有判断和构造的结论都正确。** 主体证明完整。只有一处实质性缺陷：S3 第 4 步援引 S1 时，S1 的条件并不满足。题面明确要求说明所援引结果的条件为何适用，所以这一步作为写出的证明不成立。不过它要证的等式本身是对的，可以用标准论证修复（见第三节）。其余问题都是错误的中间表述，或省略了常规验证，均不影响最终结论。

| 阶段 | 答卷结论 | 审阅判断 |
|---|---|---|
| S1 | ev 连续；柯里化双射及其自然性 | 正确；自然性一处省略 |
| S2 | $\tau_{prof}=\tau_k$；$\mathrm{Nat}(h_X,h_Y)\cong C(kX,kY)$；充要条件是 $X$ 紧生成 | 正确；第(3)小节有一个错误的中间断言，不影响结论 |
| S3 | $M(X,Y)=k\,C_{co}(kX,kY)$，ev 及伴随同构 | 构造和结论正确；**第 4 步对 S1 的援引失效**，需要补证 |
| S4 | (1) 否（反例 $X=\mathbb Q, Y=\mathbb R$）；(2) 是 | 正确 |
| S5 | 否（反例 $\mathrm{id}:kZ\to Z$） | 正确；一处措辞错误，无害 |
| S6 | 连续复合、结合律与单位律；$h_f$ 同构 ⟺ $k(f)$ 同胚；第一可数时能升级为普通同胚 | 正确 |

## 二、逐阶段核查

### S1：正确

- **求值连续。** 局部紧 Hausdorff 空间正则，且有紧邻域基，所以存在 $V\ni x_0$，使 $K=\overline V$ 紧且 $K\subset f_0^{-1}W$。于是 $[K,W]\times V\subset ev^{-1}(W)$。论证正确。
- **柯里化。** $\Phi(g)=ev\circ(g\times\mathrm{id})$ 连续。$\Psi(F)$ 的连续性用的是推广的管道引理：$\{z_0\}\times K\subset O$，$K$ 紧，得到 $V\times K\subset O$。这一方向**不需要**局部紧，S3 的修补会用到这一点。两者互逆。
- **省略。** 自然性要求诱导映射在函数空间之间连续，否则 $C(X,k)\circ g$ 未必属于 $C(Z,C_{co}(X,Y'))$。答卷没有验证。补证如下：
  - $(k_*)^{-1}[K,O']=[K,k^{-1}O']$；
  - $(j^*)^{-1}[K',O]=[j(K'),O]$，其中 $j(K')$ 紧。
  
  另外，答卷用字母 $k$ 记映射 $Y\to Y'$，与 $k$ 化记号冲突，这是表述问题。

### S2：结论正确

**(1) 两种探针给出相同的 k 拓扑。** $\beta D\twoheadrightarrow K$ 是紧空间到 Hausdorff 空间的连续满射，因此是闭映射，从而是商映射。由此 $f^{-1}(A)=\pi(\pi^{-1}f^{-1}A)$ 是闭集。论证正确。

省略：没有说明 $\beta D$ 是 U 小的。补充：$\beta D$ 可取为 $D$ 上超滤子的全体，它包含于 $\mathcal P(\mathcal P(D))\in U$。

**(2) $\mathrm{Nat}(h_X,h_Y)\cong C(kX,kY)$。** 论证正确，要点如下：
- 沿点包含 $i_s:*\to S$ 的自然性给出 $\alpha_S(f)=g\circ f$；
- 对紧 Hausdorff 的 $S$，有 $C(S,Y)=C(S,kY)$；
- 由 (1)，$kX$ 是 profinite 探针族的终拓扑。

**(3) 中间断言错误。** 答卷写道："连续 $f:X\to Y$ 诱导的自然变换对应于集合 $C(X,kY)$。"这是错的，正确的集合是 $C(X,Y)$。由 $k$ 的函子性，$C(X,Y)\subset C(kX,kY)$。

反例：取 $Z$ 为 S5 中的超滤空间。$\mathrm{id}_Z\in C(Z,Z)$ 诱导恒等变换，但 $kZ$ 离散而 $Z$ 不离散，所以 $\mathrm{id}\notin C(Z,kZ)$。

影响：答卷所写的"欲证"命题与原题命题不同，但两个方向的论证对原题命题依然成立。
- ⇐：$C(kX,kY)=C(X,kY)\subset C(X,Y)$。
- ⇒：取 $Y=kX$。此时 $C(X,Y)=C(X,kY)$，而且诱导映射的底层函数由点值唯一确定，因此 $\mathrm{id}:X\to kX$ 连续，得 $kX=X$。

所以结论不受影响。幂等性 $k(kX)=kX$ 答卷未证，但很直接：对紧 Hausdorff 的 $K$，$C(K,X)=C(K,kX)$，两个空间的探针族相同。

### S3：构造和结论正确，第 4 步需要补证

**正确的部分：**
- 底集 $C(kX,kY)$，拓扑 $k\,C_{co}(kX,kY)$。用单点紧集分离不同函数，可知它是 Hausdorff 的；由幂等性，它是紧生成的。
- 第 1 至 3 步正确：
  - $k(S\times X)=k(S\times kX)$，因为两边的探针都是坐标探针对，彼此对应；
  - 可以援引 Cohen 定理：$S$ 紧 Hausdorff，因而局部紧；$kX$ 是 Hausdorff 的 k 空间。对 Hausdorff 空间，题面的探针定义与经典的紧子集定义等价。
- 第 5 步正确。
- ev 的构造援引 CGHaus 中求值映射的连续性，条件（$kX,kY$ 是紧生成 Hausdorff 空间）成立。

**第 4 步援引失效（主要问题）。** 答卷声称"由 S1 的指数律（由于 $S$ 局部紧 Hausdorff）"得到
$$C(S\times kX,kY)\cong C(S,C_{co}(kX,kY)).$$

S1 的局部紧假设加在**函数空间的定义域**上，即 $C_{co}(X,Y)$ 中的 $X$。这里函数空间是 $C_{co}(kX,kY)$，它的定义域 $kX$ 一般不局部紧，例如 $kQ=\mathbb Q$。由 $S$ 局部紧只能推出另一个式子：$C(kX\times S,kY)\cong C(kX,C_{co}(S,kY))$。

这个等式本身是对的（补证见第三节），但答卷给出的理由不成立。

**影响有限。** 答卷后半部分在 $Z=S\in\mathrm{Prof}_U$ 时给出
$$C(S,M)=C(kS,kM)\cong\mathrm{Nat}(h_S,h_M)\cong\mathrm{Nat}(h_S\times h_X,h_Y)=H_{X,Y}(S),$$
只依赖 CGHaus 的笛卡尔闭性，而该定理的援引是正确的。因此可表示性结论实际上已由答卷自己的后文得到，只是答卷没有指出这一点。

**其他省略：**
- 关于 $S$ 的自然性没有验证。补证：对 $\sigma:S'\to S$，有 $\eta_{\varphi\circ\sigma}(a',b)=\eta_\varphi(\sigma a',b)$，即 $\eta_{\varphi\sigma}=\eta_\varphi\circ(h_\sigma\times\mathrm{id})$。
- 答卷断言复合双射"恰由 $\alpha\mapsto ev\circ(\alpha\times I)$ 实现"，但没有计算。补算：设 $\alpha\leftrightarrow g\in C(kZ,M)$，则 $(ev\circ(\alpha\times I))_T(a,b)=[t\mapsto g(a(t))(b(t))]=g^\flat\circ(a,b)$。这正是 CGHaus 伴随 $g^\flat$ 在 S2 同构下对应的自然变换，所以该映射是双射。
- $M(u,Y)$ 和 $M(X,v)$ 的连续性没有证明，补法同 S1 的省略，再加上 $k$ 的函子性。关于 $X,Y$ 自然性的两个恒等式本身正确。

### S4：正确

**(1) 判断"否"。** $X=\mathbb Q$，$Y=\mathbb R$，反例有效：
- 零函数处的邻域基：$\bigcap_{i\le n}[K_i,O_i]\supseteq[\bigcup K_i,(-\varepsilon,\varepsilon)]$，其中取 $(-\varepsilon,\varepsilon)\subset\bigcap O_i$。答卷说"基开邻域形式为 $[K,(-\varepsilon,\varepsilon)]$"，措辞不精确，但作为邻域基是对的。
- 紧集 $K\subset\mathbb Q$ 在 $\mathbb Q$ 中无内点：若 $(a,b)\cap\mathbb Q\subset K$，由于 $K$ 在 $\mathbb R$ 中闭，会得到 $[a,b]\subset K$，矛盾。
- 取 $q\in V\setminus K$，用以 $q$ 为中心的鼓包函数 $f$，有 $f\in U$ 但 $f(q)=2$。当 $K=\varnothing$ 时公式退化为常数 2，仍然可用。

这个结论与已知理论一致：对正则的 $X$，$C_{co}(X,\mathbb R)\times X\to\mathbb R$ 连续当且仅当 $X$ 局部紧。

**(2) 判断"是"。** 序列论证正确：$K=\{x_n\}\cup\{x_0\}$ 是紧 Hausdorff 子空间，包含映射是探针，所以 $A\cap K$ 在 $K$ 中闭，从而 $x_0\in A$。

### S5：正确

- 一般机制正确：对紧 Hausdorff 的 $S$，$C(S,kZ)=C(S,Z)$，所以 $h_{\mathrm{id}}$ 逐分量是恒等；$\mathrm{id}:Z\to kZ$ 不连续。
- 具体例子正确：紧集都有限，所以 $kZ$ 离散；$\{p\}$ 不是开集。按题面的探针定义：$f(K)$ 有限，$f^{-1}(A)$ 是有限个闭纤维之并，仍然成立。
- 措辞错误："恰有一个集合不属于 $\mathcal U$"应改为"至少一个"。当 $K\cap\mathbb N\notin\mathcal U$ 时，$A_1,A_2$ 都不属于 $\mathcal U$。论证只用到"至少一个"，所以无害。

### S6：正确

- **(1)** 用 CGHaus 伴随构造复合，结合律和单位律都由逐点相等加上态射由底层函数决定得到。正确。
- **(2)** S2 的对应保持复合和恒等：$\beta\circ\alpha\leftrightarrow g'\circ g$，恒等对应恒等。所以 $h_f$ 可逆 ⟺ $k(f)$ 是同胚。正确。
- **(3)** 判断"能"。由 S4(2)，$kX=X$ 且 $kY=Y$，所以 $f=k(f)$ 是同胚。正确。

## 三、S3 第 4 步的补证

**命题。** 设 $S$ 紧 Hausdorff，$X,Y$ Hausdorff。则
$$\Phi:C(S,C_{co}(kX,kY))\to C(S\times kX,kY),\qquad \Phi(g)(s,x)=g(s)(x)$$
是双射。

**证明。**
- **$\Psi$ 方向。** S1 中 $\Psi(F)$ 连续性的证明（管道引理）对任意空间都成立。
- **$\Phi$ 方向。** 由 Cohen 定理，$S\times kX$ 是 k 空间，所以只需对任意紧 Hausdorff 探针 $(a,b):K\to S\times kX$ 验证 $\Phi(g)\circ(a,b)$ 连续。
  1. 令 $b^*:C_{co}(kX,kY)\to C_{co}(K,kY)$，$\varphi\mapsto\varphi\circ b$。它连续，因为 $(b^*)^{-1}[L,O]=[b(L),O]$。
  2. 于是 $\Phi(g)\circ(a,b)(t)=ev_K\big(b^*(g(a(t))),\,t\big)$。
  3. $K$ 紧 Hausdorff，因而局部紧，此时 S1 的条件真正满足，所以 $ev_K:C_{co}(K,kY)\times K\to kY$ 连续。
  4. 因此 $\Phi(g)\circ(a,b)$ 连续，从而 $\Phi(g)$ 连续。
- 两者互逆。∎

也可以不走这条路，直接用 CGHaus 的笛卡尔闭性：
$$C(S\times_k kX,kY)\cong C(S,k\,C_{co}(kX,kY))=C(S,M),$$
其中 $S\times_k kX=k(S\times X)$。

## 四、问题清单

| # | 位置 | 性质 | 影响 |
|---|---|---|---|
| 1 | S3 第 4 步 | 援引 S1 时条件不满足（局部紧假设应加在 $kX$ 上） | 写出的证明在此处不成立；结论正确，可按第三节修复，答卷后文也已覆盖 |
| 2 | S2(3) | 把诱导变换集误写为 $C(X,kY)$，应为 $C(X,Y)$ | 没有影响，两个方向的论证仍然成立 |
| 3 | S5 | "恰有一个"应为"至少一个" | 没有影响 |
| 4 | S1、S3 | 没有验证函数空间之间诱导映射的连续性 | 常规验证，易补 |
| 5 | S3 | 关于 $S$ 的自然性、$\alpha\mapsto ev\circ(\alpha\times I)$ 与复合双射的一致性都只是断言 | 易补，补算见上 |
| 6 | S2(1)、S4(1)、S2(3) | $\beta D$ 的 U 小性、邻域基的说明、$k$ 的幂等性没有写出 | 次要省略 |

**最终评定：** 答卷在原题条件下结论全部正确，各阶段完整。S3 第 4 步需要按第三节替换论证，其余问题都是次要瑕疵，不改变任何结论。