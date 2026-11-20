# 审阅意见：半局部邻域、下降与层化的依赖比较

## 总评

这份答卷不能判为全部正确、完整。

- **S3、S4、S6** 正确。
- **S2** 正确，但有一处论证缺口，可以补上。
- **S1** 的等化子证明正确。"$S_i$ 不必是开子概形"这个结论也对，但支撑它的论证里有一条错误断言，另一条断言缺少必要前提。
- **S5** 是全卷的主目标，问题最严重：
  - 关键"定理"是错的。
  - 核心的 Mayer–Vietoris 收缩步骤只有断言，没有证明。
  - 套用 S2 所需的前提没有建立。
  - 对域 $k$ 的条件只字未提。

  $k$ 完满时，"$\eta_S$ 是同构"可以由标准定理推出（见 S5 第 7 点），但不能算作答卷已经证明。

S1–S4 和 S6 都不依赖 S5，所以 S5 的错误不影响对它们的评定。

| 阶段 | 答卷结论 | 评定 |
|---|---|---|
| S1 | 等化子成立；$S_i$ 不必为开 | 等化子部分正确，有小缺口可补；"不必为开"的结论正确，但论证含一条错误断言和一条前提不足的断言 |
| S2 | $\eta_S$ 同构 | 正确；没有验证所用覆盖构成有向系统、也没有验证余终性，可以补上 |
| S3 | 余终；两个余极限典范同构 | 正确 |
| S4 | 不一定余终（反例） | 正确 |
| S5 | $\eta_S$ 同构 | 论证不成立；S5 未被证明 |
| S6 | 否定（反例）；给出证明 | 正确 |

---

## 0. 预备事实（下文多处引用）

记号：$\operatorname{Spec}A\subset X$ 是包含 $\Sigma$ 的仿射开集，$\mathfrak p_i$ 是 $x_i$ 对应的素理想。

**(P1) $S$ 的点集与拓扑。**
- $\operatorname{Spec}(M^{-1}A)\to\operatorname{Spec}A$ 是到 $\{\mathfrak q:\mathfrak q\cap M=\emptyset\}$ 上的同胚，后者取子空间拓扑。
- 由素避免，$\mathfrak q\cap M=\emptyset \iff \mathfrak q\subset\bigcup_i\mathfrak p_i \iff$ 存在 $i$ 使 $\mathfrak q\subset\mathfrak p_i$。
- 因此 $|S|$ 恰好是 $\Sigma$ 的全部一般化，$S$ 的开集恰好是 $S\cap W$（$W\subset X$ 开）。同理 $|S_i|$ 是 $x_i$ 的全部一般化。
- "$x_i$ 是 $S$ 的闭点"意味着诸 $\mathfrak p_i$ 两两互不包含。

**(P2) 纤维积。** $S\to X$ 是局部化后接开浸入，所以是单态射。因此
$$S_i\times_S S_j=S_i\times_X S_j=\operatorname{Spec}\big(A\text{ 在 }(A\setminus\mathfrak p_i)(A\setminus\mathfrak p_j)\text{ 处的局部化}\big).$$
它的点恰好是 $x_i$ 与 $x_j$ 的公共一般化。特别地，$S_i\times_S S_i=S_i$。

**(P3) 邻域的余终性。** 设 $W\subset X$ 是开集，且包含 $x_i,x_j$ 的全部公共一般化。则存在开集 $U_i\ni x_i$、$U_j\ni x_j$，使 $U_i\cap U_j\subset W$。
- 证明：$X$ 是 noether 的。设 $Z=X\setminus W$ 的不可约分支为 $Z_1,\dots,Z_r$，一般点为 $z_k$。
- 由于 $z_k\notin W$，$z_k$ 不是两点的公共一般化，即 $x_i\notin Z_k$ 或 $x_j\notin Z_k$。
- 令 $U_i=X\setminus\bigcup_{x_i\notin Z_k}Z_k$，$U_j=X\setminus\bigcup_{x_i\in Z_k}Z_k$（后一类 $Z_k$ 都不含 $x_j$）。
- 于是 $U_i\cap U_j$ 与每个 $Z_k$ 都不相交，即 $U_i\cap U_j\subset W$。

由 (P2)(P3)，按题目的"开邻域余极限延拓"约定，有
$$G(S_i\times_S S_j)=\varinjlim_{(U_i,U_j)}G(U_i\cap U_j).$$

---

## S1

### 等化子部分：正确

- 指标集 $\mathcal I=\prod_i\mathcal I_{x_i}$ 按分量反向包含排序，是有向集。
- $(U_i)\mapsto\bigcup U_i$ 是余终的：对任意 $W\supset\Sigma$，取 $U_i=W$ 即可。所以左项的余极限是 $G(S)$。
- 投影 $\mathcal I\to\mathcal I_{x_i}$ 和 $\mathcal I\to\mathcal I_{x_i}\times\mathcal I_{x_j}$（$i\ne j$）都是满射单调映射，因而余终。所以中项和右项的余极限分别是 $\prod G(S_i)$ 和 $\prod G(S_i\times_S S_j)$。对角项 $(i,i)$ 的余极限就是 $G(S_i)$。
- 对每个 $\bigcup U_i$ 写出层公理给出的等化子，再取滤过余极限。在 Ab 中滤过余极限与有限极限交换，结论成立。

**小缺口：** 答卷用"仿射极限下对应张量积"一句话就把 $\varinjlim G(U_i\cap U_j)$ 认作 $G(S_i\times_S S_j)$，缺少论证。用 (P2)(P3) 可以补上，结论不受影响。

### "$S_i$ 不必是开子概形"：结论正确，论证有误

**(a) "概形层面"的断言是错的。** 答卷断言：$\dim\mathcal O_{X,x_i}\ge1$ 时，$\mathcal O_{X,x_i}$ 不是有限生成的 $\mathcal O_{X,\Sigma}$-代数。反例如下。
- 取 $X=\mathbb A^1=\operatorname{Spec}k[t]$，$\Sigma=\{0,1\}$。
- 任一不被 $t$ 整除的多项式都可写成 $(t-1)^m g$，其中 $g\in M$。所以 $\mathcal O_{X,0}=\mathcal O_{X,\Sigma}[1/(t-1)]$，是有限生成的。
- 在拓扑上，$S=\{\mathfrak m_0,\mathfrak m_1,\eta\}$，而 $S_1=\{\mathfrak m_0,\eta\}=D(t-1)$ 是开集。
- $n=1$ 时更是平凡地有 $S_1=S$。

**(b) 拓扑论证缺少前提，且有一步没有证明。**
- 答卷说"非零的 $f$ 只含于 $\mathfrak p_j$ 中有限多个高度 1 素理想"。这要求 $x_i$ 与 $x_j$ 在同一个不可约分支上（光滑时即同一连通分支）。
- 反例：$X=\mathbb A^2\sqcup\mathbb A^2$，$x_1,x_2$ 分别取两个分支的原点。此时 $S=S_1\sqcup S_2$，$S_1$ 是开集，完全符合答卷所列的维数条件。$f=(1,0)\notin\mathfrak p_1$ 落在第二个因子的所有素理想中。
- 即使在同一分支上，"有无穷多个高度 1 素理想，去掉有限个后必有 $\mathfrak q\not\subset\mathfrak p_i$"也不成立：同时含于 $\mathfrak p_i$ 和 $\mathfrak p_j$ 的高度 1 素理想本身就可以有无穷多个。
- 补法：
  1. 设 $\mathfrak q_1,\dots,\mathfrak q_r$ 是 $f$ 的极小素理想，它们的高度都是 1。
  2. 因为 $\operatorname{ht}\mathfrak p_j\ge2$ 且 $\mathfrak p_j\not\subset\mathfrak p_i$，素避免给出 $g\in\mathfrak p_j\setminus(\mathfrak p_i\cup\mathfrak q_1\cup\dots\cup\mathfrak q_r)$。
  3. 取 $g$ 的一个含于 $\mathfrak p_j$ 的极小素理想 $\mathfrak q$。由 Krull 主理想定理，$\operatorname{ht}\mathfrak q=1$。
  4. 若 $f\in\mathfrak q$，则 $\mathfrak q$ 是 $f$ 的极小素理想，与 $g\notin\mathfrak q_k$ 矛盾。所以 $f\notin\mathfrak q$；又 $g\notin\mathfrak p_i$，所以 $\mathfrak q\not\subset\mathfrak p_i$。

**(c) 正确的表述。** 若 $x_i$ 与某个 $x_j$（$j\ne i$）在同一不可约分支上，且 $\operatorname{ht}\mathfrak p_j\ge2$，则 $S_i$ 不是 $S$ 的开集。再由 EGA IV 17.9.1（局部有限表示的平坦单态射是开浸入），此时 $\mathcal O_{X,x_i}$ 不是有限型的 $\mathcal O_{X,\Sigma}$-代数。所以"不是有限生成"只在这些前提下成立，并且要从"非开"反推出来；答卷没有独立证明它。

**(d) 一个直接可验证的例子（对任意域 $k$ 成立）。**
- 取 $X=\mathbb A^2$，$x_1=(0,0)$，$x_2=(1,0)$。
- 假设 $S_1$ 是开集。由 (P1)，$S_1=S\cap W$，其中 $W\subset X$ 开且 $x_1\in W$。
- 对 $m\ge1$，令 $C_m=V(x-1-y^m)$。它关于 $x$ 是一次的，所以不可约；它过 $x_2$，不过 $x_1$。
- $C_m$ 的一般点属于 $S$，不属于 $S_1$，所以 $C_m\subset X\setminus W$。
- 诸 $C_m$ 两两不同。二维不可约 $X$ 的真闭子集只有有限个不可约分支，所以 $X\setminus W=X$，与 $x_1\in W$ 矛盾。

**影响范围：** 题目只要求说明 $S_i$"不必"是开子概形，结论成立，但答卷的论证需要按 (b)–(d) 修正。错误断言 (a) 在后文没有被使用，不影响其他部分。

---

## S2

**结论与图追逐正确。**
- 由 (P2)，$S_i\times_S S_i=S_i$，所以对角分量不提供任何条件。(1,2) 和 (2,1) 两个分量给出等价的条件。因此底行就是 S1 给出的核正合列。
- 中间竖直映射是同构，右侧竖直映射是单射。由此追图得到满射；单射性已在题设中给出。这一步无误。

**缺口：答卷第 2 步没有验证有向性与余终性。**

先说明如何读题。$H(S)\to H(U)$ 要有意义，$U,V$ 应理解为 $S$ 的开集（"分开"指 $x_1\in U\setminus V$，$x_2\in V\setminus U$），并且 $H(U):=\varinjlim_{W\supset U\ \text{开}}H(W)$。这与 S5 的约定一致。由 (P1)，任何 $W\supset\Sigma$ 都包含 $|S|\supset U$，所以限制映射有定义。下面补证：

1. **覆盖。** 由 (P1)，$S$ 的点都是 $x_1$ 或 $x_2$ 的一般化，而开集对一般化封闭。所以任意开集 $U\ni x_1$、$V\ni x_2$ 都覆盖 $S$。
2. **余终性。** 给定任意 $(U_1,V_1)$，先换成 $(U_1\setminus\{x_2\},\,V_1\setminus\{x_1\})$。由于 $x_i$ 是 $S$ 的闭点，这仍是分开两点的覆盖。再由题设缩成好覆盖 $(U,V_1\setminus\{x_1\})$，其中 $U\subset U_1$。
3. **有向性。** 给定两个好覆盖 $(U,V)$ 和 $(U',V')$，$(U\cap U',V\cap V')$ 仍是分开两点的覆盖。由题设可缩成好覆盖 $(U'',V\cap V')$，其中 $U''\subset U\cap U'$。
4. **识别余极限。** 结合第 2 点和 (P3)，在好覆盖上取余极限，得到 $\varinjlim H(U)=H(S_1)$，$\varinjlim H(V)=H(S_2)$，$\varinjlim H(U\cap V)=H(S_1\times_S S_2)$。

补上之后，答卷的结论成立。

---

## S3

正确。
- 对任意 $V\supset\Sigma$，$V\cap W$ 包含 $\Sigma$、含于 $W$，并且比 $V$ 小，这给出余终性。
- $\psi\circ\phi=\mathrm{id}$，因为对 $U\subset W$ 有 $U\cap W=U$。
- $\phi\circ\psi=\mathrm{id}$，因为在全邻域余极限中 $[s|_{V\cap W}]=[s]_V$。

---

## S4

正确。
- 取 $X=\mathbb A^1$，$\Sigma=\{0\}$，$W=D(t)$。它满足全部前提：光滑、整、仿射，$W$ 稠密开。
- 所论开集族是空集，而 $\Sigma$ 的开邻域族非空，所以不余终。
- 答卷补充的"余终 $\iff\Sigma\subset W$"也对：$\Sigma\not\subset W$ 时开集族为空；$\Sigma\subset W$ 时由 S3 得到余终。

---

## S5（主要问题）

### 1. "稠密开浸入单射性定理"是错的

答卷断言：对一切 $k$、一切满足题设的 $F$、一切连通光滑 $Y$ 和稠密开 $W\subset Y$，$F(Y)\to F(W)$ 是单射。只需在某个域上给出一个反例。

取 $k$ 完满（例如 $k=\mathbb C$），$F=\operatorname{Pic}$。
- **$F$ 是 $\mathrm{Cor}_k$ 上的加性反变函子。** 对光滑 $Y$，$\operatorname{Pic}(Y)\cong CH^1(Y)\cong H^{2,1}(Y,\mathbb Z)\cong\operatorname{Hom}_{\mathrm{DM}}(M(Y),\mathbb Z(1)[2])$，而 $M(-)$ 是 $\mathrm{Cor}_k$ 上的函子。具体地，有限对应 $\alpha$ 的作用是 $L\mapsto p_{Y*}\big(c_1(p_Z^*L)\cap[\alpha]\big)$；$\alpha$ 在 $Y$ 上有限，因而在 $Y$ 上是真的。
- **同伦不变性。** $Y$ 正则，所以 $\operatorname{Pic}=CH^1$；由 Fulton Thm 3.3(a)，$CH^1(Y)\cong CH^1(Y\times\mathbb A^1)$。
- **失败。** 取 $Y=\mathbb P^1$，$W=\mathbb A^1$：$\operatorname{Pic}(\mathbb P^1)=\mathbb Z\to\operatorname{Pic}(\mathbb A^1)=0$ 不是单射。

答卷自己的草图写的就是"在 $Y$ 的局部"构造标准三元组。这类构造、以及把对角线移开 $Z$ 的论证，都只在有限个点附近（半局部）成立，却被写成了整体结论 $s=\Phi^*(s|_W)$。

### 2. 由此推出的结论也都是错的

- **"$F$ 是 Zariski 分离预层"**：$\mathcal O(1)\in\operatorname{Pic}(\mathbb P^1)$ 在两片标准 $\mathbb A^1$ 上的限制都是 0，但它本身不是 0。
- **"对任意开集 $U$，$F(U)\to F_{\mathrm{Zar}}(U)$ 是单射"**：$\operatorname{Pic}$ 在每点的茎是 $\operatorname{Pic}(\mathcal O_{X,x})=0$，所以 $\operatorname{Pic}_{\mathrm{Zar}}=0$，于是 $\eta_{\mathbb P^1}:\mathbb Z\to0$ 不是单射。

注意，在这个例子里 $\operatorname{Pic}(S)=\operatorname{Pic}(\mathcal O_{X,\Sigma})=0=F_{\mathrm{Zar}}(S)$，$\eta_S$ 是同构。所以这个反例否定的是答卷的中间断言，而不是 S5 的目标结论。

### 3. 套用 S2 所需的前提没有建立

- **$\eta_S$ 单射。** 这本身是对的，但要用半局部单射性定理：$F(S)\hookrightarrow\prod_\xi F(\xi)$，$\xi$ 取 $S$ 的一般点。由于预层与层化在一般点处茎相同，若 $\eta_S(a)=0$，则 $a$ 在每个 $F(\xi)$ 中为 0，从而 $a=0$。答卷用的是上面那条错误的整体单射性。
- **$\eta_T$ 单射，$T=S_1\times_S S_2$（以及归纳中的 $S'\times_S S_n$）。** 唯一的依据是错误的分离性，因此没有证明。而且 $T$ 一般不是半局部的，所以半局部定理也不能直接给出：在 $\mathbb A^2$ 上取 $x_1=(0,0)$、$x_2=(1,0)$，$T$ 的点包括过这两点的所有不可约曲线（例如 $y=x^m(x-1)$，$m\ge1$）的一般点，有无穷多个闭点。这个前提在一般情形下是否成立，本审阅不作判定。
- **Mayer–Vietoris 收缩引理。** 这正是 S2 的核心题设，也是整题的核心，答卷只有"有限对应的移动技术"之类的描述。所引编号"MVW Lemma 4.22/5.7"无法核实，也没有写出被引结论的确切内容和适用条件。

### 4. 归纳步骤也有缺口

- 底行是用 $S'$ 和 $S_n$ 拼接 $S$。这不是 S1 的原样结论，要作类似的论证：覆盖取 $U'\cup U_n$，$U'\supset\Sigma'$，$U_n\ni x_n$。这一步可以补。
- 顶行同样依赖未证明的 MV 收缩，这次是把 $\Sigma$ 分成 $\Sigma'\sqcup\{x_n\}$。
- 右侧竖直映射是单射，同样依赖错误的分离性。
- 只有"中间竖直映射是同构，由归纳假设得到"这一步是对的。

### 5. 域的条件没有处理

题目允许任意域 $k$。答卷援引的 Voevodsky 结论（$F_{\mathrm{Zar}}$ 带转移、同伦不变、$F_{\mathrm{Zar}}=F_{\mathrm{Nis}}$、半局部单射性），通常的陈述都以 $k$ 完满为前提；标准三元组一类的论证还用到 $k$ 无限，有限域要另作转移论证。答卷对此只字未提。就我所知，文献中有到非完满域的推广（Suslin 关于非完满域上 motivic 复形的工作），但答卷既未援引，也未论证。

### 6. 答卷中正确的部分

- 图嵌入函子 $\mathrm{Sm}/k\to\mathrm{Cor}_k$。
- "$\mathbb A^1$-同伦的对应诱导相同映射"：$F(i_0)$ 和 $F(i_1)$ 都是 $F(p)$ 的逆。
- $n=1$ 情形：$F(S_x)$ 和 $F_{\mathrm{Zar}}(S_x)$ 都是 $x$ 处的茎，而预层与其层化的茎同构。
- 在 $k$ 完满时，答卷所述的 Voevodsky 层化性质本身成立。

### 7. 可行的修补路线（供核查用，不计作答卷内容）

设 $k$ 完满，并承认两条标准定理：
- **(T1)** $F_{\mathrm{Zar}}$ 有唯一的转移结构，使 $\eta$ 成为带转移预层之间的态射，并且 $F_{\mathrm{Zar}}$ 同伦不变。
- **(T2)** 同伦不变的带转移预层满足半局部单射性。

论证分三步：
1. 令 $K=\ker\eta$，$C=\operatorname{coker}\eta$（逐对象计算）。它们都是带转移预层；由五引理的自然性，它们也同伦不变。
2. 层化是正合的，且 $(F_{\mathrm{Zar}})_{\mathrm{Zar}}=F_{\mathrm{Zar}}$，所以 $K_{\mathrm{Zar}}=C_{\mathrm{Zar}}=0$。因此 $K$、$C$ 在一般点处的茎为 0，由 (T2) 得 $K(S)=C(S)=0$。
3. 对 $0\to K\to F\to F_{\mathrm{Zar}}\to C\to0$ 取滤过余极限，仍然正合，所以 $\eta_S$ 是同构。

这条路线完全不需要 S2 和 MV 收缩。

**S5 结论：** 答卷的最终论断在 $k$ 完满时可以由 (T1)(T2) 推出，但答卷自身的论证依赖一条错误定理和若干未证步骤，不能认定 S5 已被证明。

---

## S6

**第一问正确。**
- 各阶段为 $\mathbb Z\xrightarrow{2}\mathbb Z$，转移映射在两项上都是乘 2，链映射条件成立（$4x=4x$）。
- 余极限为 $\mathbb Z[1/2]\xrightarrow{2}\mathbb Z[1/2]$，这是同构，所以余极限复形正合。
- 但每个阶段都有 $H_0=\mathbb Z/2\ne0$。
- 顺带一提：$H_0$ 上的转移映射是零映射，与第二问的结论一致。

**第二问的两种证明都正确。**
- 方法一：同调与滤过余极限交换，任一类都在某个后阶段变为零。
- 方法二：逐元素追逐，利用"滤过余极限中的元为零，当且仅当它在某个后阶段为零"。

---

## 本轮修订说明与自评

**保留：**
- 各节的总体判定：S1 主体对、S2 对、S3/S4/S6 对、S5 论证失败。
- Pic 反例。
- S2 缺口的补法。
- S5 的修补路线。

**新增或修正：**
1. 修正了上一版的一条过强断言："维数 $\ge2$ 时'不是有限生成'确实成立"。它在 $\mathbb A^2\sqcup\mathbb A^2$ 上不成立，现改为"同一不可约分支且 $\operatorname{ht}\mathfrak p_j\ge2$"，经由 EGA IV 17.9.1 推出。
2. 补了预备事实 (P1)–(P3)，包括邻域余终性的证明，从而补全 S1 右项与 S2 余极限的识别。
3. 补了一个对任意域都可直接验证的例子（$\mathbb A^2$ 上的曲线族 $C_m$），说明 $S_i$ 不必为开。
4. 说明了 S2 中 $H(U)$ 的读法，使 $H(S)\to H(U)$ 有定义。
5. Pic 转移结构的依据改为"$k$ 完满时 $\operatorname{Pic}\cong H^{2,1}$，并由 $M(-)$ 的函子性得到"。由于答卷断言对一切 $k$ 成立，一个域上的反例就够了。
6. 新增两点：$T=S_1\times_S S_2$ 一般不是半局部的，所以 $\eta_T$ 单射这一缺口是实质性的；$\eta_S$ 单射只需对 $F$ 本身用半局部单射性。
7. 关于域条件和文献推广的表述加了保留。

**仍不确定：**
- 文献中定理的确切编号与精确前提（我没有逐条核对原文）。
- S5 的结论对一般域（非完满域、有限域）是否成立：我认为文献中有推广，但本轮未核实。
- $\eta_T$ 单射在一般情形下是否成立：没有判定。

**自评：** 对各节正误的判定，都有可核查的论证或具体反例支撑。用到外部标准定理的地方（S5 中的 Pic 转移结构和修补路线），都已注明所需条件（$k$ 完满）。我认为这份审阅意见没有已知的错误断言；剩下的不确定之处只在文献细节和一般域的情形。