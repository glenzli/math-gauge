# 对角呈示的完成与商拓扑：完整解答

**结论概要.** 设 $\nu^*=\sup_n\nu_n\in\mathbb Z_{\ge0}\cup\{\infty\}$。题中所有充要条件都归结为同一个条件：**$\nu^*<\infty$（指数列有界）**。在这个条件下，完成列短正合，$E=0$，$p$ 有 $S$ 线性右逆；三者等价。此外以下结论对任何指数列都成立：
- $\widehat\iota$ 是单射，$\widehat q$ 与 $p$ 是满射，$j$ 是单射，且 $j(C)=Q_{\rm tors}$；
- $E\cong W_\nu/\mathbf c_0$，它无挠、$t$ 进分离且完备；
- $\bigcap_m t^mQ=E$；
- 子空间拓扑是平凡拓扑，两种拓扑相同当且仅当 $\nu^*<\infty$。

## 0. 记号与基本事实

下文中 $n$ 跑遍 $\{1,2,\dots\}$。"几乎所有 $n$" 指除有限多个以外的所有 $n$。

**赋值.** $v$ 是 $S$ 上的 $t$ 进赋值，约定 $v(0)=\infty$。基本恒等式：$S=\varprojlim R/t^m$，$S/t^mS=R/t^mR$。对 $g\in R$，$t^r\mid g$ 在 $R$ 中成立当且仅当在 $S$ 中成立。

**代表元.** 对 $c\in R/t^{\nu}R$，记 $\tilde c\in R$ 为它唯一的次数 $<\nu$ 的代表元；$c\mapsto\tilde c$ 是 $k$ 线性的。

**(F)** 对一切 $m\ge0$，有 $c\in t^m(R/t^\nu)\iff v(\tilde c)\ge m$。并且约化映射 $R/t^\nu\to R/t^{\min(m,\nu)}$ 的核恰为 $t^m(R/t^\nu)$。

*证明.* 设 $m\le\nu$。若 $c=[t^mh]$，则 $\tilde c$ 是从 $t^mh$ 中删去次数 $\ge\nu\,(\ge m)$ 的单项所得，因此 $t^m\mid\tilde c$；反方向显然。设 $m>\nu$。此时 $t^m(R/t^\nu)=0$；又 $\deg\tilde c<\nu<m$，所以两边都等价于 $c=0$。关于核的论断可直接验证。∎

**四个 $S$ 子模.** 以下都按坐标运算；由 $v(x+y)\ge\min(v(x),v(y))$ 与 $v(sx)\ge v(x)$ 知它们确是子模：
$$\mathbf c_0=\{x\in S^{\mathbb N}:v(x_n)\to\infty\},\qquad \mathbf c_0^\nu=\{c\in\textstyle\prod_n R/t^{\nu_n}:v(\tilde c_n)\to\infty\},$$
$$W_\nu=\{a\in S^{\mathbb N}:\nu_n+v(a_n)\to\infty\}\supseteq\mathbf c_0,\qquad K=\{b\in\mathbf c_0:t^{\nu_n}\mid b_n\ \forall n\}.$$

**闭包.** 若拓扑以递减子群 $U_m$ 为零点邻域基，则子群 $X$ 的闭包为 $\overline X=\bigcap_m(X+U_m)$。

**引理 0.**
- (a) 若 $\nu$ 无界，则存在 $n_1<n_2<\cdots$ 使 $\nu_{n_i}\ge i$。
- (b) $W_\nu=\mathbf c_0\iff\nu^*<\infty$。

*证明.* (a) 无界序列去掉有限项后仍无界，归纳选取即可。(b) 若 $\nu_n\le N$，则 $v(a_n)\ge(\nu_n+v(a_n))-N\to\infty$。若 $\nu$ 无界，令 $a_{n_i}=1$，其余 $a_n=0$；则 $\nu_{n_i}+v(a_{n_i})=\nu_{n_i}\ge i$，故 $a\in W_\nu$，但 $a\notin\mathbf c_0$。∎

---

## 第一部分：完成的坐标模型与完成列

### 1.1 各层商

$A/t^mA=\bigoplus_n(R/t^m)\bar f_n$，$B/t^mB=\bigoplus_n(R/t^m)\bar e_n$。

由于 $\iota A+t^mB=\bigoplus_n t^{\min(m,\nu_n)}Re_n$，有
$$C/t^mC=\bigoplus_n\big(R/t^{\min(m,\nu_n)}\big)\bar e_n .$$

各层映射如下：
- $\iota_m(\bar f_n)=t^{\nu_n}\bar e_n$；
- $q_m$ 是逐坐标约化；
- 过渡映射都是逐坐标约化。

按定义，$\widehat M$ 是相容商记录 $(x_m)_m$（满足 $x_{m+1}\mapsto x_m$）之集。记 $\pi^M_m$ 为取第 $m$ 个分量。

### 定理 1（坐标模型）

定义
$$\Phi_B:\mathbf c_0\to\widehat B,\quad b\mapsto\Big(\sum_n(b_n\bmod t^m)\bar e_n\Big)_m,$$
$\Phi_A$ 同样定义（把 $\bar e_n$ 换成 $\bar f_n$），以及
$$\Phi_C:\mathbf c_0^\nu\to\widehat C,\quad c\mapsto\Big(\sum_n(c_n\bmod t^{\min(m,\nu_n)})\bar e_n\Big)_m .$$
它们都是 $S$ 模同构。

**逆映射.**
- 对记录 $x_m=\sum_n x_{m,n}\bar e_n$，令 $b_n=\varprojlim_m x_{m,n}\in S$。
- 对记录 $y_m=\sum_n y_{m,n}\bar e_n$，令 $c_n=y_{m,n}$，其中 $m\ge\nu_n$ 任取。

**诱导映射与典范映射（坐标形式）.**
- $\widehat\iota(a)=(t^{\nu_n}a_n)_n$，$\widehat q(b)=(b_n\bmod t^{\nu_n})_n$；
- $\eta_B(\sum g_ne_n)=(g_n)_n$，$\eta_A$ 同理；$\eta_C(\sum c_n\bar e_n)=(c_n)_n$；
- $\pi^B_m(b)=\sum_n(b_n\bmod t^m)\bar e_n$，$\pi^C_m(c)=\sum_n(c_n\bmod t^{\min(m,\nu_n)})\bar e_n$。

*证明.*

1. **良定义.** 和式都是有限和：$b_n\bmod t^m\ne0\iff v(b_n)<m$；由 (F)，$c_n\bmod t^{\min(m,\nu_n)}\neq0\iff v(\tilde c_n)<m$。这两类 $n$ 都只有有限多个。记录的相容性显然。
2. **$S$ 线性.** $S$ 在第 $m$ 层经 $S\to R/t^m$ 作用，且 $(sb_n)\bmod t^m=\bar s\,(b_n\bmod t^m)$。
3. **$\Phi_B$ 单.** 若 $\Phi_B(b)=0$，则 $b_n\in\bigcap_m t^mS=0$。
4. **$\Phi_B$ 满.** 给定相容记录，坐标 $(x_{m,n})_m$ 相容，确定 $b_n\in S$。由于 $\{n:v(b_n)<m\}=\{n:x_{m,n}\ne0\}$ 有限，$b\in\mathbf c_0$。
5. **$\Phi_C$ 双射.** 当 $m\ge\nu_n$ 时，过渡映射在第 $n$ 个坐标上是 $R/t^{\nu_n}$ 的恒等映射，所以 $c_n$ 良定义；相容性给出对一切 $m$ 都有 $y_{m,n}=c_n\bmod t^{\min(m,\nu_n)}$。再由 (F)，有限性条件恰好就是 $c\in\mathbf c_0^\nu$。单射：取 $m\ge\nu_n$ 即得 $c_n=0$。
6. **诱导映射.** 逐层验证：$\iota_m\big(\sum(a_n\bmod t^m)\bar f_n\big)=\sum(t^{\nu_n}a_n\bmod t^m)\bar e_n$；$q_m$ 把 $b_n\bmod t^m$ 送到 $(b_n\bmod t^{\nu_n})\bmod t^{\min(m,\nu_n)}$。
7. **$\eta$ 的公式**由定义直接得到。∎

下文把 $\widehat A,\widehat B$ 都等同于 $\mathbf c_0$，把 $\widehat C$ 等同于 $\mathbf c_0^\nu$。

### 引理 2（各层、拓扑与 $\eta_C$）

**(a)** $\pi^B_m$ 满，且
$$\ker\pi^B_m=t^m\widehat B=\{b:v(b_n)\ge m\ \forall n\}.$$
对 $A$ 同理。

**(b)** $\pi^C_m$ 满，且
$$\ker\pi^C_m=t^m\widehat C=\{c:v(\tilde c_n)\ge m\ \forall n\}.$$
因此 $\widehat C/t^m\widehat C\cong C/t^mC$。完成上的 $t$ 进拓扑与逆极限拓扑一致，$\widehat B$、$\widehat C$ 分离且完备，$\eta_{\widehat C}$ 是同构。

**(c)** $\eta_C$ 单，像为有限支撑元之集。$\eta_C$ 满当且仅当 $\nu^*<\infty$。若 $\nu$ 无界，令 $c^*_{n_i}=[t^{\nu_{n_i}-1}]$，其余坐标为 $0$。则 $c^*\in\widehat C$，$tc^*=0$，且 $c^*$ 有无限支撑。

*证明.*

(a) $\pi^B_m\circ\eta_B$ 是投影 $B\to B/t^mB$，故 $\pi^B_m$ 满。若对一切 $n$ 有 $v(b_n)\ge m$，则 $b=t^mb'$，其中 $b'_n=b_n/t^m$ 仍趋于 $0$。

(b) 满射性同理。由 (F)，$\ker\pi^C_m$ 就是所写的集合。若 $v(\tilde c_n)\ge m$ 对一切 $n$ 成立，令 $c'_n=[\tilde c_n/t^m]$；则 $\tilde c'_n=\tilde c_n/t^m$，$v(\tilde c_n')=v(\tilde c_n)-m\to\infty$，从而 $c=t^mc'$。$\eta_{\widehat C}$ 与同构 $\widehat C/t^m\widehat C\cong C/t^mC$ 复合后为 $c\mapsto(\pi^C_mc)_m=c$。

(c) $\eta_C$ 的单射性与像的描述由坐标公式直接得到。
- 若 $\nu_n\le N$：对几乎所有 $n$ 有 $v(\tilde c_n)\ge N>\deg\tilde c_n$，故 $\tilde c_n=0$，即 $c$ 有限支撑。
- 若 $\nu$ 无界：$v(\tilde c^*_{n_i})=\nu_{n_i}-1\to\infty$，故 $c^*\in\widehat C$，且它不是有限支撑的。∎

### 定理 3（完成列、闭包、纤维）

1. **单射性.** $\widehat\iota$ 是单射，因为 $S$ 是整环。
2. **满射性.** $\widehat q$ 是满射。$\sigma(c)=(\tilde c_n)_n$ 是一个 $k$ 线性截面：由定义 $\sigma(c)\in\mathbf c_0$，且 $\tilde c_n\bmod t^{\nu_n}=c_n$。
3. **核与像.** $\ker\widehat q=K$。映射 $\theta:K\to W_\nu$，$b\mapsto(b_n/t^{\nu_n})_n$，是 $S$ 同构，逆映射为 $a\mapsto(t^{\nu_n}a_n)_n$（因为 $v(t^{\nu_n}a_n)=\nu_n+v(a_n)$）。又 $\theta\circ\widehat\iota=\mathrm{id}$，所以
$$\operatorname{im}\widehat\iota=\theta^{-1}(\mathbf c_0)=\{b\in K:v(b_n)-\nu_n\to\infty\}.$$
4. **闭包.** $\overline{\operatorname{im}\widehat\iota}=\bigcap_m(\operatorname{im}\widehat\iota+t^m\widehat B)=K=\ker\widehat q$。甚至 $\eta_B(\iota A)$ 就已在 $K$ 中稠密。
   - *证明.* 取 $b\in K$ 与 $m$。令 $F=\{n:v(b_n)<m\}$（有限），$b_n=t^{\nu_n}a_n$；对 $n\in F$，令 $h_n$ 为 $a_n$ 低于 $m$ 次的截断。则 $b-\eta_B\iota(\sum_{n\in F}h_nf_n)$ 的每个坐标的赋值都 $\ge m$，故 $b\in\eta_B(\iota A)+t^m\widehat B$。
   - 反之，若 $b\in\bigcap_m(\operatorname{im}\widehat\iota+t^m\widehat B)$，取 $m=\nu_n$ 即得 $t^{\nu_n}\mid b_n$。
   - 推论：$\operatorname{im}\widehat\iota$ 是闭集当且仅当 $\nu^*<\infty$（由第 3 点与引理 0）。
5. **纤维.** 对每个 $c\in\widehat C$，
$$\widehat q^{-1}(c)=\{b\in\mathbf c_0:\ b_n\equiv\tilde c_n \ (\mathrm{mod}\ t^{\nu_n})\ \forall n\}=\sigma(c)+K .$$
   - 它是非空闭集；对其中任意 $b$，有 $\widehat q^{-1}(c)=\overline{b+\operatorname{im}\widehat\iota}$。
   - 纤维中的 $\operatorname{im}\widehat\iota$ 陪集与 $E=K/\operatorname{im}\widehat\iota$ 一一对应。
   - 因此：$\nu^*<\infty$ 时每个纤维恰是一个 $\operatorname{im}\widehat\iota$ 陪集；否则每个纤维含 $|E|\ge|S|$ 个陪集，是不可数多个。
6. **正合性.** 序列 $0\to\widehat A\to\widehat B\to\widehat C\to0$：
   - 在 $\widehat A$ 处与 $\widehat C$ 处总是正合；
   - 在 $\widehat B$ 处的同调为 $K/\operatorname{im}\widehat\iota\cong W_\nu/\mathbf c_0$，正合当且仅当 $W_\nu=\mathbf c_0$。

   **因此，完成列短正合 $\iff\sup_n\nu_n<\infty$。**

---

## 第二部分：$E$、$j$ 与 $p$

### 定理 4（$E$ 的坐标模型）

$\theta$ 诱导 $S$ 同构
$$E\;\cong\;\frac{W_\nu}{\mathbf c_0}=\frac{\{(a_n)\in S^{\mathbb N}:\ \nu_n+v(a_n)\to\infty\}}{\{(a_n)\in S^{\mathbb N}:\ v(a_n)\to\infty\}},\qquad (t^{\nu_n}a_n)_n+\operatorname{im}\widehat\iota\ \leftrightarrow\ [a].$$

例如，当 $\nu_n\to\infty$ 时 $E\cong S^{\mathbb N}/\mathbf c_0$。在 $\nu$ 有界的指标集上，坐标自动趋于 $0$。

### 引理 5（$t^mE$ 的刻画）

对 $a\in W_\nu$：$[a]\in t^mE\iff$ 对几乎所有 $n$ 有 $v(a_n)\ge m$。

*证明.*
- ($\Rightarrow$) 若 $a=t^ma'+d$，其中 $d\in\mathbf c_0$，则由 $d$ 的性质，几乎所有 $n$ 满足 $v(a_n)\ge m$。
- ($\Leftarrow$) 令 $F=\{n:v(a_n)<m\}$（有限）。在 $F$ 外令 $a'_n=a_n/t^m$，在 $F$ 上令 $a'_n=0$。则 $a'\in W_\nu$，且 $a-t^ma'$ 有限支撑，属于 $\mathbf c_0$。∎

### 定理 6（$j$ 与挠）

**(i) $p$ 与 $j$ 的基本性质.**
- $p$ 良定义、$S$ 线性，且是满射（因为 $\widehat q$ 是满射）。
- $j$ 良定义：若 $q(b)=0$，则 $b=\iota a$，从而 $\eta_B(b)=\widehat\iota\eta_A(a)\in\operatorname{im}\widehat\iota$。
- 由 $\eta$ 的自然性，$p\circ j=\eta_C$；而 $\eta_C$ 是单射，所以 **$\ker j=0$**。

**(ii) $j$ 的像与 $Q$ 的挠元.**
$$Q_{\rm tors}:=\{x\in Q:\exists r\ge1,\ t^rx=0\}=\operatorname{im}j=\{b+\operatorname{im}\widehat\iota:\ b\in\widehat B,\ v(b_n)-\nu_n\to+\infty\},$$
其中 $j\big(q(\sum g_ne_n)\big)=(g_n)_n+\operatorname{im}\widehat\iota$。条件 $v(b_n)-\nu_n\to+\infty$ 与代表元的选取无关，因为 $\operatorname{im}\widehat\iota$ 中的元素满足它。更细地，
$$Q[t^r]=j(C[t^r])=\{[b]:\ v(b_n)\ge\nu_n-r\ \forall n,\ v(b_n)-\nu_n\to\infty\},\qquad C[t^r]=\bigoplus_n t^{\max(\nu_n-r,0)}R/t^{\nu_n}R .$$

*证明.*
- $C$ 是挠模：$C$ 的元素被 $t^{\max(1,\max_F\nu_n)}$ 杀死，其中 $F$ 是它的支撑。因此 $j(C)\subseteq Q_{\rm tors}$。
- 反之，设 $t^rb=\widehat\iota(a)$。令 $F=\{n:v(a_n)<r\}$。对 $n\notin F$，有 $b_n=t^{\nu_n}(a_n/t^r)$。对 $n\in F$，令 $g_n$ 为 $b_n$ 低于 $\nu_n$ 次的截断。则 $b-\eta_B(\sum_Fg_ne_n)=\widehat\iota(a')$，其中 $a'\in\mathbf c_0$。故 $[b]=j(q(\sum_F g_n e_n))$。
- 坐标描述同理：若 $v(b_n)-\nu_n\to\infty$，只需在有限个满足 $v(b_n)<\nu_n$ 的 $n$ 处作同样的截断。
- 由于 $j$ 单，$Q[t^r]=j(C)[t^r]=j(C[t^r])$。∎

**(iii) $E$ 的挠性.** $E$ 是**无挠** $S$ 模。设 $0\ne s=ut^r$，$u\in S^\times$；若 $s[a]=0$，则 $t^ra\in\mathbf c_0$，从而 $a\in\mathbf c_0$。此外：
- $E\cap j(C)=0$；
- $j(C)\oplus E=p^{-1}(\eta_C(C))$。

### 定理 7（$E=0$ 与右逆的判据）

**(i)** $E=0\iff\nu^*<\infty$。这由定理 4 与引理 0 得到。

**(ii)** $p$ 有 $S$ 线性右逆 $\iff\nu^*<\infty$。
- ($\Leftarrow$) $p$ 是同构，$p^{-1}$ 即为右逆。此时 $j$ 与 $\eta_C$ 也都是同构。
- ($\Rightarrow$) 设 $\nu$ 无界而右逆 $s$ 存在。由 $ts(c^*)=s(tc^*)=0$ 得 $s(c^*)\in Q[t]\subseteq j(C)$。于是 $c^*=ps(c^*)\in\eta_C(C)$ 是有限支撑元，与引理 2(c) 矛盾。

**附注.** $k$ 线性右逆总是存在，例如 $c\mapsto\sigma(c)+\operatorname{im}\widehat\iota$。

---

## 第三部分：商拓扑与再完成

### 定理 8

**(i) 有限层上 $p$ 是同构.** 对每个 $m\ge1$，$\bar p_m:Q/t^mQ\to\widehat C/t^m\widehat C$ 是同构。在坐标下二者都等同于 $C/t^mC=\bigoplus_nR/t^{\min(m,\nu_n)}$：
- $\lambda_m:\ [b]+t^mQ\mapsto(b_n\bmod t^{\min(m,\nu_n)})_n$；
- $\mu_m:\ c+t^m\widehat C\mapsto(c_n\bmod t^{\min(m,\nu_n)})_n$；
- $\mu_m\bar p_m=\lambda_m$，即在坐标下 $\bar p_m$ 是恒等映射。

*证明.* $b\mapsto(b_n\bmod t^{\min(m,\nu_n)})_n$ 是满射，核为 $(\pi^B_m)^{-1}\big(\pi^B_m(\operatorname{im}\widehat\iota)\big)=\operatorname{im}\widehat\iota+t^m\widehat B$，所以 $\lambda_m$ 是同构；$\mu_m$ 是同构由引理 2(b) 得到。∎

此外，$j$ 诱导的映射 $C/t^mC\to Q/t^mQ$ 恰为 $\lambda_m^{-1}$，所以 $j(C)$ 在 $Q$ 中稠密。

**(ii) $\bigcap_m t^mQ=E$.**
- 由定理 3 第 4 点，$K\subseteq\operatorname{im}\widehat\iota+t^m\widehat B$，所以 $E\subseteq t^mQ$ 对一切 $m$ 成立。
- 反之，$\bigcap_m t^mQ$ 被 $p$ 映入 $\bigcap_m t^m\widehat C=0$，故含于 $\ker p=E$。

因此 $\widehat C\cong Q/\bigcap_m t^mQ$，即 $\widehat C$ 是 $Q$ 的分离商。

**(iii) $\widehat Q$、$\eta_Q$ 与 $\widehat p$.**
- $\Lambda=\varprojlim\lambda_m:\widehat Q\xrightarrow{\sim}\varprojlim C/t^mC=\widehat C$ 是同构，且 $\Lambda\circ\eta_Q=p$。所以 **$\eta_Q$ 是满射，$\ker\eta_Q=E$**。
- 完成映射 $\widehat p:\widehat Q\to\widehat{\widehat C}$ 满足 $\widehat p=\eta_{\widehat C}\circ\Lambda$，是**同构**，并且 $\widehat p\circ\eta_Q=\eta_{\widehat C}\circ p$。

**(iv) $\widehat E$ 与 $\eta_E$.** $\eta_E:E\to\widehat E$ 是**同构**；也就是说，$E$ 是 $t$ 进分离且完备的，$\widehat E\cong E\cong W_\nu/\mathbf c_0$。

*证明.*
1. **单射.** 由引理 5，$[a]\in\bigcap_m t^mE$ 推出 $a\in\mathbf c_0$，即 $[a]=0$。
2. **满射.** 给定相容的 $\xi_m=[a^{(m)}]+t^mE$。由引理 5，$a^{(m+1)}$ 与 $a^{(m)}$ 只在有限多个坐标上不满足 $v(a^{(m+1)}_n-a^{(m)}_n)\ge m$。修改有限多个坐标不改变 $E$ 中的类，因此可以归纳地使对一切 $n$ 都有 $v(a^{(m+1)}_n-a^{(m)}_n)\ge m$。
3. **取极限.** 令 $a_n=\lim_m a^{(m)}_n$，则 $v(a_n-a^{(m)}_n)\ge m$。
4. **$a\in W_\nu$.** 若 $\nu_n+v(a_n)<M$，则 $v(a_n)<M$，从而 $v(a^{(M)}_n)=v(a_n)$；这样的 $n$ 只有有限多个。
5. **结论.** $a-a^{(m)}=t^md$，其中 $d\in W_\nu$，所以 $\eta_E([a])=(\xi_m)$。∎

$E/t^mE$ 的显式模型为
$$E/t^mE\cong\{\bar a\in\textstyle\prod_n R/t^m:\ \nu\to\infty\text{ 沿 }\operatorname{supp}\bar a\}\Big/\textstyle\bigoplus_n R/t^m .$$

**附注.** 由 $E\subseteq t^mQ$，包含映射 $E\hookrightarrow Q$ 的完成为零映射。因此，把 $0\to E\to Q\to\widehat C\to0$ 完成后得到 $E\xrightarrow{0}\widehat C\xrightarrow{\sim}\widehat C$，它正合当且仅当 $E=0$。

**(v) 两种拓扑的比较.**
- **子空间拓扑.** 由于 $E\cap t^mQ=E$ 对一切 $m$ 成立，$E$ 从 $Q$ 继承的子空间拓扑是平凡拓扑（只有 $\emptyset$ 与 $E$ 两个开集）。
- **自身拓扑.** $E$ 自身的 $t$ 进拓扑**总是分离的**，而且是完备的（第 (iv) 点）。
- **何时相同.** 若 $E\ne0$，分离性迫使 $tE\ne E$，所以 $tE$ 是一个非平凡的开集，两种拓扑不同。

  **因此两种拓扑相同 $\iff E=0\iff\sup_n\nu_n<\infty$。**

| 问题 | 结论 |
|---|---|
| $\widehat A,\widehat B$ | $\mathbf c_0$；$\widehat\iota(a)=(t^{\nu_n}a_n)$ |
| $\widehat C$ | $\mathbf c_0^\nu$；$\widehat q(b)=(b_n\bmod t^{\nu_n})$ |
| 闭包 $\overline{\operatorname{im}\widehat\iota}$ | $K=\ker\widehat q$ |
| $\widehat q$ 的纤维 | $\sigma(c)+K$ |
| 短正合 | $\iff\nu^*<\infty$ |
| $E$ | $W_\nu/\mathbf c_0$，无挠、分离、完备 |
| $j$ | 单射，像为 $Q_{\rm tors}$ |
| $p$ | 总是满射；有右逆 $\iff\nu^*<\infty$ |
| $E=0$ | $\iff\nu^*<\infty$ |
| $\bar p_m$ | 对每个 $m$ 都是同构 |
| $\bigcap_m t^mQ$ | $E$ |
| $\widehat Q$ 与 $\eta_Q$ | $\widehat Q\cong\widehat C$，$\eta_Q=p$ |
| $\widehat p$ | 同构 |
| $\eta_E$ | 同构 |
| 两种拓扑相同 | $\iff\nu^*<\infty$ |