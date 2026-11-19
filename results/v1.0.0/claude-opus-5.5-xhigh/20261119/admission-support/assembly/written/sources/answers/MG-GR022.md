# 对角呈示的完成与商拓扑：解答

**结论概要：** 设 $(\nu_n)_{n\ge1}$ 为任意给定的指数列。下面所有出现的充要条件都同一个条件等价，即 **$\nu$ 有界**（$\sup_n\nu_n<\infty$），也等价于 $E=0$。具体包括：完成列短正合；完成列在 $\widehat B$ 处正合；$p$ 有 $S$ 线性右逆；$j$ 为双射；$E$ 自身的 $t$ 进拓扑与子空间拓扑相同。

以下几条对每个 $\nu$ 都成立：
- $\widehat\iota$ 单，$\widehat q$ 满，$p$ 满；
- $j$ 单，且 $\operatorname{im}j$ 恰为 $Q$ 的挠部分；
- $E\cong W[[t]]$，它是无挠、分离且完备的 $S$ 模；
- 对每个 $m$，$p$ 诱导的 $Q/t^mQ\to\widehat C/t^m\widehat C$ 是同构；
- $\bigcap_m t^mQ=E$。

## 0. 记号

- $s\in S$ 记作 $s=\sum_{l\ge0}s_{[l]}t^l$，$\operatorname{ord}0=\infty$。$S$ 是整环。每个非零 $s$ 可写成 $t^ru$，其中 $u\in S^\times$。
- 对 $\nu\ge0$ 有 $R/(t^\nu)=S/(t^\nu)$。每个 $y$ 有唯一代表 $\tilde y\in R$，满足 $\deg\tilde y<\nu$。令 $\operatorname{ord}y:=\operatorname{ord}\tilde y$。于是 $y\in t^r(R/(t^\nu))\iff\operatorname{ord}y\ge r$，并且 $y\ne0\Rightarrow\operatorname{ord}y<\nu$。当 $\nu=0$ 时该模为 $0$。
- 记号"$z_n\to\infty$"指：对每个 $m$，集合 $\{n:z_n<m\}$ 有限。
- $c_0:=\{x\in S^{\mathbb N}:\operatorname{ord}x_n\to\infty\}$。
- $\mathcal C:=\{y\in\prod_nR/(t^{\nu_n}):\operatorname{ord}y_n\to\infty\}$。
- $H:=\operatorname{im}\widehat\iota$，$K:=\ker\widehat q$。
- $\ell(\nu):=\{w\in k^{\mathbb N}:\forall M,\ \{n\in\operatorname{supp}w:\nu_n\le M\}\text{ 有限}\}$，即沿 $w$ 的支集有 $\nu_n\to\infty$。
- $W:=\ell(\nu)/k^{(\mathbb N)}$。$W[[t]]=\prod_{i\ge0}Wt^i$，其上 $S$ 作用为 $(\sum s_jt^j)(\sum w_it^i)=\sum_i(\sum_{j\le i}s_jw_{i-j})t^i$。
- 若 $\nu$ 无界，则对每个 $M$ 有无穷多个 $n$ 满足 $\nu_n\ge M$。因此可取 $n_1<n_2<\cdots$ 使 $\nu_{n_i}\ge i$，记 $T=\{n_i\}$。

**引理 0.** $W=0\iff\nu$ 有界。

证明：若 $\nu_n\le N$ 对所有 $n$ 成立，在定义中取 $M=N$ 即得 $\ell(\nu)=k^{(\mathbb N)}$。若 $\nu$ 无界，则 $1_T\in\ell(\nu)\setminus k^{(\mathbb N)}$。∎

---

## 1. 完成的坐标模型与完成列

**各层的形状。** $A/t^mA=\bigoplus_n(R/t^m)f_n$，$B/t^mB=\bigoplus_n(R/t^m)e_n$，并且
$$C/t^mC=B/(t^mB+\iota A)=\bigoplus_nR/(t^{\min(m,\nu_n)}).$$

**定理 1.1（坐标模型）。**

(a) 映射 $\Phi_B:\widehat B\to c_0$ 把相容记录 $(\beta^{(m)})_m$ 送到 $(x_n)_n$，其中 $x_n=(\beta^{(m)}_n)_m\in\varprojlim R/t^m=S$。它是 $S$ 同构，逆映射为 $x\mapsto\big((x_n\bmod t^m)_n\big)_m$。对 $\widehat A$ 有同样的结论（按 $f_n$ 取坐标）。

(b) 映射 $\Phi_C:\widehat C\to\mathcal C$ 把 $(\gamma^{(m)})_m$ 送到 $(y_n)_n$，其中 $y_n:=\gamma^{(m)}_n$，$m\ge\nu_n$ 任取。它是 $S$ 同构，逆映射为 $y\mapsto\big((y_n\bmod t^{\min(m,\nu_n)})_n\big)_m$。

(c) 在上述模型下：
- $\eta_A,\eta_B$ 是包含 $R^{(\mathbb N)}\subset c_0$，$\eta_C$ 是包含 $\bigoplus_nR/(t^{\nu_n})\subset\mathcal C$。三者都是单射。
- 诱导映射为 $\widehat\iota(a)=(t^{\nu_n}a_n)_n$，$\widehat q(x)=(x_n\bmod t^{\nu_n})_n$。

*证明。*

(a) $\beta^{(m)}$ 的支集 $F_m$ 有限。对 $n\notin F_m$ 有 $t^m\mid x_n$，所以 $\{n:\operatorname{ord}x_n<m\}\subseteq F_m$，故 $x\in c_0$。反过来，若 $x\in c_0$，则 $(x_n\bmod t^m)_n$ 只有有限个非零坐标，且各层相容。两个映射按坐标互逆。第 $m$ 层上 $s$ 的作用是按坐标乘 $s\bmod t^m$，所以 $\Phi_B$ 是 $S$ 线性的。

(b) 当 $m\ge\nu_n$ 时，过渡映射 $R/t^{\min(m+1,\nu_n)}\to R/t^{\min(m,\nu_n)}$ 是恒等映射，所以 $y_n$ 定义良好，并且对所有 $m$ 都有 $\gamma^{(m)}_n=y_n\bmod t^{\min(m,\nu_n)}$。若 $n\notin\operatorname{supp}\gamma^{(m)}$，则 $y_n\in t^{\min(m,\nu_n)}(R/t^{\nu_n})=t^m(R/t^{\nu_n})$，即 $\operatorname{ord}y_n\ge m$，故 $y\in\mathcal C$。反过来，$y_n\bmod t^{\min(m,\nu_n)}\neq0$ 推出 $\operatorname{ord}y_n<m$，这样的 $n$ 只有有限个。两个映射互逆且 $S$ 线性。

(c) 逐层验证即可。∎

**命题 1.2（$t$ 进拓扑）。**
$$t^m\widehat B=\{x:t^m\mid x_n\ \forall n\}=\ker(\widehat B\to B/t^mB),$$
$$t^m\widehat C=\{y:\operatorname{ord}y_n\ge m\ \forall n\}=\ker(\widehat C\to C/t^mC).$$
因此 $\widehat B/t^m\widehat B\cong B/t^mB$，$\widehat C/t^m\widehat C\cong C/t^mC$。$\widehat B,\widehat C$ 分离且完备，即 $\eta_{\widehat B},\eta_{\widehat C}$ 是同构。$\widehat B$ 上的 $t$ 进拓扑与逆极限拓扑一致。

*证明。* 若 $t^m\mid x_n$ 对所有 $n$ 成立，则 $(x_n/t^m)\in c_0$，所以 $x\in t^m\widehat B$。若 $\operatorname{ord}y_n\ge m$ 对所有 $n$ 成立，令 $z_n$ 为 $\tilde y_n/t^m$ 的类（它的次数 $<\nu_n$），则 $\operatorname{ord}z_n=\operatorname{ord}y_n-m\to\infty$，且 $t^mz=y$。反向包含是显然的。∎

**定理 1.3（完成列的正合性、闭包与纤维）。**

(i) $\widehat q\widehat\iota=0$。$\widehat\iota$ 总是单射（$S$ 是整环）。$\widehat q$ 总是满射，并有 $k$ 线性截面 $\sigma(y)=(\tilde y_n)_n$；这里 $\operatorname{ord}\tilde y_n=\operatorname{ord}y_n\to\infty$。

(ii) $K=\{x\in c_0:t^{\nu_n}\mid x_n\ \forall n\}$，并且 $H=\{x\in K:(x_n/t^{\nu_n})_n\in c_0\}$。

(iii) 取 $t$ 进拓扑（等同于逆极限拓扑）时，$\overline H=K$。

(iv) 对 $y\in\widehat C$，有
$$\widehat q^{-1}(y)=\{x\in c_0:x_n\equiv\tilde y_n\pmod{t^{\nu_n}}\ \forall n\}=\sigma(y)+\overline{H}.$$
每个纤维都是 $\overline H$ 的闭陪集。它所含的 $H$ 陪集与 $E=K/H$ 一一对应，且每个这样的 $H$ 陪集在纤维中稠密。纤维恰为单个 $H$ 陪集，当且仅当 $\nu$ 有界。

(v) $H=K\iff\nu$ 有界。因此完成列在 $\widehat A$ 和 $\widehat C$ 处总正合；在 $\widehat B$ 处正合当且仅当 $\nu$ 有界。**完成列短正合当且仅当 $\sup_n\nu_n<\infty$。**

*证明。*

(ii) 由坐标形式直接读出。

(iii) 设 $x\in K$，取 $F=\{n:\operatorname{ord}x_n<m\}$，它是有限集。令 $h=x\cdot1_F$。则 $h\in H$（其对应的 $a$ 支集有限），且 $x-h\in t^m\widehat B$。所以 $K\subseteq\bigcap_m(H+t^m\widehat B)=\overline H$。反过来，若 $x\in H+t^m\widehat B$ 对所有 $m$ 成立，对每个 $n$ 取 $m>\nu_n$，得 $x_n\in t^{\nu_n}S+t^mS=t^{\nu_n}S$，所以 $x\in K$。

(iv) 由 (i) 和 (iii) 得到。稠密性来自 $\overline H=K$。

(v) 若 $\nu_n\le N$，则 $\operatorname{ord}(x_n/t^{\nu_n})\ge\operatorname{ord}x_n-N\to\infty$，故 $K=H$。若 $\nu$ 无界，令 $x_n=t^{\nu_n}1_T(n)$。则 $x\in K$，而它唯一的原像 $a=1_T$ 不在 $c_0$ 中，所以 $x\notin H$。∎

---

## 2. $E$、$j$ 与 $p$

由于 $p(x+H)=\widehat q(x)$，有 $E=K/H$。

**定理 2.1（$E$ 的坐标模型）。** 令
$$\mathcal D=\{a\in S^{\mathbb N}:\nu_n+\operatorname{ord}a_n\to\infty\}\supseteq c_0.$$
则 $a\mapsto(t^{\nu_n}a_n)+H$ 给出同构 $\mathcal D/c_0\cong E$。进一步，
$$\Theta:\ \mathcal D/c_0\xrightarrow{\ \sim\ }W[[t]],\qquad [a]\mapsto\sum_{i\ge0}\big[(a_{n,[i]})_{n\ge1}\big]\,t^i$$
是 $S$ 同构。把两者合起来，得到
$$E\cong W[[t]],\qquad x+H\mapsto\sum_i\big[(x_{n,[\nu_n+i]})_n\big]t^i .$$

*证明。* 因为 $\operatorname{ord}(t^{\nu_n}a_n)=\nu_n+\operatorname{ord}a_n$，由定理 1.3(ii) 得 $K=\{(t^{\nu_n}a_n):a\in\mathcal D\}$，且 $H$ 对应于 $c_0$。

- **列落在 $\ell(\nu)$ 中。** 对 $a\in\mathcal D$，若 $a_{n,[i]}\ne0$ 且 $\nu_n\le M$，则 $\nu_n+\operatorname{ord}a_n\le M+i$。这样的 $n$ 只有有限个，所以第 $i$ 列 $(a_{n,[i]})_n$ 属于 $\ell(\nu)$。
- **$S$ 线性。** $(sa)_{n,[i]}=\sum_{j\le i}s_ja_{n,[i-j]}$。
- **核等于 $c_0$。** $\{n:\operatorname{ord}a_n<m\}=\bigcup_{i<m}\operatorname{supp}(a_{\cdot,[i]})$。所以 $a\in c_0$ 当且仅当每一列都只有有限支集。
- **满射。** 给定 $w_i\in\ell(\nu)$，令 $a_n=\sum_iw_i(n)t^i$。若 $\nu_n+\operatorname{ord}a_n<m$，则存在 $i<m$ 使 $w_i(n)\ne0$ 且 $\nu_n<m$；这样的 $n$ 落在有限多个有限集的并中。所以 $a\in\mathcal D$，且 $\Theta[a]=\sum_i[w_i]t^i$。∎

**推论 2.2.**
- $E=0\iff\nu$ 有界（由引理 0）。
- $E$ 是无挠 $S$ 模：$t$ 在 $W[[t]]$ 上作移位，是单射，而单位元可逆。
- $t^mE\leftrightarrow t^mW[[t]]$，所以 $\bigcap_mt^mE=0$，$E/t^mE\cong\bigoplus_{i<m}Wt^i$，且 $E$ 是 $t$ 进完备的。

**定理 2.3（$j$ 的核与像；$Q$ 的挠元）。**

- $j$ 定义良好：$\eta_B\iota=\widehat\iota\,\eta_A$，所以 $\eta_B(\iota A)\subseteq H$。并且 $p\circ j=\eta_C$。
- 因此 $\ker j\subseteq\ker\eta_C=0$，**$j$ 是单射**，且 $\operatorname{im}j\cap E=0$。
- 像为
$$\operatorname{im}j=\{\xi\in Q:\exists r\ge1,\ t^r\xi=0\}=Q_{\rm tors},$$
用坐标写出来是
$$\operatorname{im}j=\{x+H:\exists F\text{ 有限},\ \forall n\notin F\ t^{\nu_n}\mid x_n,\ (x_n/t^{\nu_n})_{n\notin F}\to0\}.$$
- 更细地，$Q[t^r]=j(C[t^r])$，其中 $C[t^r]=\bigoplus_nt^{\max(\nu_n-r,0)}R/(t^{\nu_n})$。
- $p$ 把 $\operatorname{im}j$ 同构地映到 $\eta_C(C)$（$\mathcal C$ 中有限支集的元素），并且 $p^{-1}(\eta_CC)=j(C)\oplus E$。
- **$j$ 是双射当且仅当 $\nu$ 有界。**

*证明。*

- **$j(C)$ 是挠的。** $C$ 是挠模：元素 $c$ 被 $t^{\max_{\operatorname{supp}c}\nu_n}$ 杀死。
- **挠元落在 $j(C)$ 中。** 设 $t^r(x+H)=0$，即 $t^rx_n=t^{\nu_n}a_n$，其中 $a\in c_0$。令 $F=\{n:\operatorname{ord}a_n<r\}$，它是有限集。对 $n\notin F$，消去 $t^r$ 得 $x_n=t^{\nu_n}(a_n/t^r)$。对 $n\in F$，写 $x_n=b_n+t^{\nu_n}a''_n$，其中 $b_n\in R$，$\deg b_n<\nu_n$。于是 $x=\eta_B(b)+\widehat\iota(a'')$，其中 $b\in B$，$a''\in c_0$，所以 $x+H=j(q(b))$。
- **坐标刻画**正是 $\eta_B(B)+H$ 的描述，可用同样的分解验证。
- **$Q[t^r]$。** 由 $j$ 单射且 $t$ 线性得到。
- **$j$ 为双射的条件。** $j$ 满射要求 $E=0$ 且 $\eta_C(C)=\widehat C$。若 $\nu$ 无界，下面定理 2.4 证明中的元素 $y$ 有无限支集，所以两者都不成立；若 $\nu$ 有界，则两者都成立。∎

**定理 2.4（$p$ 的满射性与右逆）。**

- $p$ **总是满射**，因为 $\widehat q$ 是满射。它总有 $k$ 线性右逆 $y\mapsto\sigma(y)+H$。
- $E=0\iff\nu$ 有界。
- **$p$ 有 $S$ 线性右逆当且仅当 $\nu$ 有界。**

*证明。* 若 $\nu$ 有界，则 $E=0$，$p$ 本身是同构。若 $\nu$ 无界，令 $y_{n_i}=t^{\nu_{n_i}-1}$，其余坐标为 $0$。则 $\operatorname{ord}y_{n_i}=\nu_{n_i}-1\to\infty$，所以 $y\in\widehat C$；并且 $ty=0$，而 $y$ 的支集无限。假设存在 $t$ 线性的 $s$ 使 $ps=\mathrm{id}$，则 $ts(y)=s(ty)=0$，于是 $s(y)\in Q[t]\subseteq j(C)$，从而 $y=ps(y)\in pj(C)=\eta_C(C)$，与支集无限矛盾。所以甚至不存在 $R$ 线性右逆。∎

---

## 3. 商拓扑与再完成

**定理 3.1.** 对每个 $m\ge1$，诱导映射 $\bar p_m:Q/t^mQ\to\widehat C/t^m\widehat C$ 是**同构**。两边都由 $x\mapsto(x_n\bmod t^{\min(m,\nu_n)})_n$ 典范地等同于 $C/t^mC=\bigoplus_nR/(t^{\min(m,\nu_n)})$，在这一等同下 $\bar p_m$ 就是恒等映射。特别地，
$$t^mQ=p^{-1}(t^m\widehat C)=\{x+H:\ x_n\in t^{\min(m,\nu_n)}S\ \ \forall n\}.$$

*证明。* 映射 $\widehat B\to C/t^mC$ 是满射。下面验证它的核等于 $t^m\widehat B+H$。设 $x_n\in t^{\min(m,\nu_n)}S$ 对所有 $n$ 成立，令 $F=\{n:\operatorname{ord}x_n<m\}$，它是有限集。对 $n\in F$ 必有 $\nu_n<m$，从而 $x_n\in t^{\nu_n}S$。所以 $x=x1_F+x1_{F^c}\in H+t^m\widehat B$。反向包含是显然的。这给出 $Q/t^mQ\cong C/t^mC$。另一侧由命题 1.2 得 $\widehat C/t^m\widehat C\cong C/t^mC$。最后，$\widehat q(x)_n\bmod t^{\min(m,\nu_n)}=x_n\bmod t^{\min(m,\nu_n)}$，所以 $\bar p_m$ 对应于恒等映射。∎

**定理 3.2.**
$$\bigcap_mt^mQ=p^{-1}\Big(\bigcap_mt^m\widehat C\Big)=p^{-1}(0)=E\qquad(\text{也等于 }\overline H/H).$$
因此 $Q$ 分离当且仅当 $\nu$ 有界。

**定理 3.3（再完成）。**
- $\widehat p=\varprojlim\bar p_m:\widehat Q\to\widehat{\widehat C}$ 是**同构**，而 $\eta_{\widehat C}$ 也是同构。所以 $\widehat Q\cong\widehat C\cong\mathcal C$。
- 由自然性 $\widehat p\,\eta_Q=\eta_{\widehat C}\,p$，在此等同下 $\eta_Q=p$。即 $\eta_Q$ 是满射，且 $\ker\eta_Q=E$。
- 由推论 2.2，$\eta_E:E\to\widehat E$ 是**同构**，$\widehat E\cong E\cong W[[t]]$。
- 包含映射 $E\hookrightarrow Q$ 诱导的 $\widehat E\to\widehat Q$ 是**零映射**，因为对每个 $m$ 都有 $E\subseteq t^mQ$。所以完成 $0\to E\to Q\to\widehat C\to0$ 后得到 $\widehat E\xrightarrow{0}\widehat Q\xrightarrow{\sim}\widehat{\widehat C}$。当 $\nu$ 无界时，它在 $\widehat E$ 处不正合。

**定理 3.4（$E$ 上两种拓扑的比较）。**
- **自身的 $t$ 进拓扑**以 $t^mE$ 为零点邻域基。它**总是分离的**（$\bigcap_mt^mE=0$），而且是完备的。
- **子空间拓扑**的邻域为 $E\cap t^mQ=E$（对所有 $m$），所以它是平凡（不分离）拓扑。
- 自身拓扑总是更细，因为 $t^mE\subseteq E\cap t^mQ$。
- **两种拓扑相同当且仅当 $E=0$，即当且仅当 $\nu$ 有界。** 若 $E\neq0$，取 $e\ne0$ 和满足 $e\notin t^mE$ 的 $m$；则 $t^mE$ 是自身拓扑中的零点邻域，但不是子空间拓扑中的邻域。