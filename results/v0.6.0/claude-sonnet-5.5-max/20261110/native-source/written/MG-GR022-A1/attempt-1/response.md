# 解答

## 0. 约定、记号、两个见证元、结论总览

**约定。** $\mathbb N=\{1,2,\dots\}$，$\bigoplus_n,\prod_n$ 均指 $n\in\mathbb N$ 上的和与积。"几乎所有 $n$"指除有限个 $n$ 外的所有 $n$。$v$ 是 $S$ 的 $t$ 进赋值（$v(0)=\infty$），$S/t^mS=R/t^mR$（$m=0$ 时为零环）。对取值于 $\mathbb Z\cup\{\infty\}$ 的序列 $\lambda_n$，"$\lambda_n\to\infty$"表示：对每个 $K$，几乎所有 $n$ 有 $\lambda_n\ge K$。

$\widehat M$ 的元素就是相容记录族 $x=(x_m)_{m\ge1}$（$x_m\in M/t^mM$，$x_{m+1}\mapsto x_m$）。$\pi^M_m:\widehat M\to M/t^mM$ 是第 $m$ 层投影。

称指数列**有界**，若 $\sup_n\nu_n<\infty$。这等价于 $t^NC=0$ 对某个 $N$ 成立，因为 $t^N C=\bigoplus_n t^N\bar S_n$（$\bar S_n$ 见下）。

**序列模。** 令
$$c_0(S)=\{a\in S^{\mathbb N}: v(a_n)\to\infty\},\quad \Lambda=\{a\in S^{\mathbb N}: v(a_n)+\nu_n\to\infty\},\quad \tau(a)=(t^{\nu_n}a_n)_n .$$
$\tau:S^{\mathbb N}\to S^{\mathbb N}$ 是 $S$ 线性单射。因 $\nu_n\ge 0$，有 $\bigoplus_nS\subseteq c_0(S)\subseteq\Lambda$ 和 $\tau(c_0(S))\subseteq c_0(S)$。又 $\tau^{-1}(c_0(S))=\Lambda$，所以
$$\tau(\Lambda)=\{b\in c_0(S): t^{\nu_n}\mid b_n\ \forall n\}.\tag{0.1}$$

**商环坐标。** 令 $\bar S_n=S/t^{\nu_n}S=R/t^{\nu_n}R$。每个 $\bar s\in \bar S_n$ 有唯一代表元 $\mathrm{rep}_n(\bar s)\in R$，次数 $<\nu_n$。令 $w_n(\bar s)=v(\mathrm{rep}_n(\bar s))$。

若 $s\in S$ 代表 $\bar s$，则当 $v(s)<\nu_n$ 时 $w_n(\bar s)=v(s)$，当 $v(s)\ge\nu_n$ 时 $w_n(\bar s)=\infty$。于是对 $m\ge0$：
$$\bar s\in t^m\bar S_n\iff v(s)\ge\min(m,\nu_n)\iff w_n(\bar s)\ge m,\qquad w_n(\bar s)\ge v(s).\tag{W}$$
令 $\mathcal C=\{c\in\prod_n\bar S_n: w_n(c_n)\to\infty\}$。

**引理 0（见证元）。**
(a) 若 $\nu$ 有界，则 $\Lambda=c_0(S)$，且 $\mathcal C=\bigoplus_n\bar S_n$。
(b) 若 $\nu$ 无界，则存在 $n_1<n_2<\cdots$ 使 $\nu_{n_i}\ge i$。令 $u_{n_i}=1$，其余 $u_n=0$。令 $\gamma_{n_i}=t^{\nu_{n_i}-1}\bmod t^{\nu_{n_i}}$，其余 $\gamma_n=0$。则 $u\in\Lambda\setminus c_0(S)$，$\gamma\in\mathcal C\setminus\bigoplus_n\bar S_n$，且 $t\gamma=0$。

*证明。* (a) 设 $\nu_n\le N$。若 $a\in\Lambda$，则 $v(a_n)\ge v(a_n)+\nu_n-N\to\infty$，故 $a\in c_0(S)$。若 $c\in\mathcal C$ 且 $c_n\ne0$，则 $w_n(c_n)\le\nu_n-1<N$；但几乎所有 $n$ 有 $w_n(c_n)\ge N$，所以几乎所有 $c_n=0$。

(b) 无界时每个 $\{n:\nu_n\ge i\}$ 无限，故 $n_i$ 存在。$\{n: v(u_n)+\nu_n<K\}\subseteq\{n_1,\dots,n_{K-1}\}$ 有限，所以 $u\in\Lambda$。$v(u_{n_i})=0$ 出现无穷多次，所以 $u\notin c_0(S)$。$w_{n_i}(\gamma_{n_i})=\nu_{n_i}-1\ge i-1\to\infty$，所以 $\gamma\in\mathcal C$。每个 $\gamma_{n_i}\neq 0$，而 $t\gamma_{n_i}=t^{\nu_{n_i}}=0$。∎

**总览（答案）。**

1. $\widehat A\cong\widehat B\cong c_0(S)$，$\widehat C\cong\mathcal C$。$\widehat\iota=\tau$，$\widehat q$ 是逐坐标模 $t^{\nu_n}$ 约化。
   - $\widehat\iota$ 恒单，$\widehat q$ 恒满，$\widehat q\widehat\iota=0$。
   - $\ker\widehat q=\tau(\Lambda)=\overline{\operatorname{im}\widehat\iota}$，所以 $\widehat q$ 的每个纤维是 $\operatorname{im}\widehat\iota$ 某个陪集的闭包。
   - 中间的同调 $\ker\widehat q/\operatorname{im}\widehat\iota\cong\Lambda/c_0(S)$。
   - 完成列短正合 $\iff$ $\nu$ 有界。
2. $E\cong\Lambda/c_0(S)$。$p$ 恒满。
   - $j$ 单，像是所有有限支撑类，且等于 $\bigcup_rQ[t^r]$。
   - $E$ 是 $S$ 无挠的。
   - $E=0\iff p$ 有 $S$ 线性右逆 $\iff \nu$ 有界。
3. $Q/t^mQ\to\widehat C/t^m\widehat C$ 恒为同构（两边都典范同构于 $C/t^mC$）。
   - $\bigcap_m t^mQ=E$。
   - $\widehat Q\cong\widehat C$，$\eta_Q$ 就是 $p$。$\widehat p$ 是同构。
   - $E$ 自身的拓扑分离且完备，$\eta_E:E\to\widehat E$ 是同构。
   - $E$ 的子空间拓扑是平凡拓扑。两种拓扑相同 $\iff E=0\iff\nu$ 有界。

---

## 1. 完成的坐标模型与完成列

**命题 1.1（$\widehat A,\widehat B$）。** 设 $x\in\widehat B$，$x_m=\sum_n\beta_{m,n}e_n$（有限和，$\beta_{m,n}\in S/t^m$）。相容性意味着对每个 $n$，$(\beta_{m,n})_m\in\varprojlim S/t^m=S$。故有唯一 $b_n\in S$ 使 $\beta_{m,n}=b_n\bmod t^m$。又 $x_m$ 为有限和 $\iff$ 几乎所有 $n$ 有 $b_n\in t^mS$。所以
$$\Phi_B:\widehat B\xrightarrow{\sim}c_0(S),\quad x\mapsto (b_n)_n,\qquad \Phi_B^{-1}(b)=\Big(\sum_n (b_n\bmod t^m)e_n\Big)_m ,$$
同理 $\widehat A\cong c_0(S)$。这些同构是 $S$ 线性的，因为 $S$ 在每层逐坐标作用。在此坐标下：

- $\eta_A,\eta_B$ 是包含 $\bigoplus_nR\subset c_0(S)$。
- 由 $\iota_m(\sum\alpha_nf_n)=\sum t^{\nu_n}\alpha_ne_n$ 得 $\widehat\iota=\tau|_{c_0(S)}$。
- $t^m\widehat B=\{b\in c_0(S): v(b_n)\ge m\ \forall n\}=\ker \pi^B_m$。（若 $b\in c_0(S)$ 且所有 $v(b_n)\ge m$，则 $(b_n/t^m)_n\in c_0(S)$。）所以 $\widehat B$ 的 $t$ 进拓扑就是逆极限拓扑。

**命题 1.2（$\widehat C$）。** $\iota(A)=\bigoplus t^{\nu_n}Re_n$，所以 $C=\bigoplus_n\bar S_n\bar e_n$，$C/t^mC=\bigoplus_n S/t^{\min(m,\nu_n)}\,\bar e_n$。$q_m$ 是 $\beta_n\mapsto\beta_n\bmod t^{\min(m,\nu_n)}$。

设 $(\gamma_m)\in\widehat C$。固定 $n$，系统 $(S/t^{\min(m,\nu_n)})_m$ 在 $m\ge\nu_n$ 时恒为 $\bar S_n$、过渡映射为恒等，故极限是 $\bar S_n$。于是有唯一 $c_n\in\bar S_n$ 使 $\gamma_{m,n}=c_n\bmod t^{\min(m,\nu_n)}$。由 (W)，$\gamma_{m,n}=0\iff c_n\in t^m\bar S_n\iff w_n(c_n)\ge m$。$\gamma_m$ 为有限和 $\iff$ 对该 $m$，几乎所有 $n$ 有 $w_n(c_n)\ge m$。因此
$$\Phi_C:\widehat C\xrightarrow{\sim}\mathcal C,\qquad \widehat q(b)=(b_n\bmod t^{\nu_n})_n,\qquad \eta_C(\textstyle\sum c_n\bar e_n)=(c_n)_n .$$
$\eta_C$ 是 $\bigoplus\bar S_n\subseteq\mathcal C$ 的包含，特别是单射。∎

**命题 1.3。**
(i) $\widehat\iota$ 恒单。
(ii) $\widehat q$ 恒满，有 $k$ 线性截面 $c\mapsto\tilde c=(\mathrm{rep}_n(c_n))_n$，且 $v(\tilde c_n)=w_n(c_n)$。
(iii) $\ker\widehat q=\tau(\Lambda)\supseteq\operatorname{im}\widehat\iota=\tau(c_0(S))$。因此 $\tau$ 诱导 $\ker\widehat q/\operatorname{im}\widehat\iota\cong\Lambda/c_0(S)$。

*证明。* (i) $\tau$ 单。(ii) $v(\tilde c_n)=w_n(c_n)\to\infty$，所以 $\tilde c\in c_0(S)$，且 $\widehat q(\tilde c)=c$。(iii) $b\in\ker\widehat q\iff t^{\nu_n}\mid b_n\ \forall n$，即 (0.1)。$\tau:\Lambda\to\ker\widehat q$ 是双射，且把 $c_0(S)$ 映到 $\operatorname{im}\widehat\iota$。∎

**命题 1.4（闭包与纤维）。** $\overline{\operatorname{im}\widehat\iota}=\bigcap_m(\operatorname{im}\widehat\iota+t^m\widehat B)=\ker\widehat q=\tau(\Lambda)$。

*证明。* "$\supseteq$"：设 $b=\tau(a)$，$a\in\Lambda$，$m\ge1$。$F=\{n:v(a_n)+\nu_n<m\}$ 有限。令 $a'=a$ 限制在 $F$ 上（其余为 0）。则 $\tau(a')\in\operatorname{im}\widehat\iota$，而 $b-\tau(a')\in c_0(S)$ 的所有坐标赋值 $\ge m$，故属于 $t^m\widehat B$。

"$\subseteq$"：若 $b\in\operatorname{im}\widehat\iota+t^m\widehat B$，取 $m=\max(\nu_n,1)$，则 $b_n\in t^{\nu_n}S+t^mS=t^{\nu_n}S$。对所有 $n$ 如此，故 $b\in\ker\widehat q$。∎

**纤维。** 对 $c\in\widehat C$ 与任一 $b$ 满足 $\widehat q(b)=c$：
$$\widehat q^{-1}(c)=b+\tau(\Lambda)=\overline{b+\operatorname{im}\widehat\iota}=\{b'\in c_0(S): b'_n\equiv\mathrm{rep}_n(c_n)\bmod t^{\nu_n}\ \forall n\}.$$
所以纤维恰是 $\operatorname{im}\widehat\iota$ 的陪集的闭包。每个纤维是 $\operatorname{im}\widehat\iota$ 的陪集的并，陪集集合与 $\Lambda/c_0(S)$ 一一对应。它是单个陪集 $\iff\Lambda=c_0(S)$。

**命题 1.5（正合性）。** 完成列 $0\to\widehat A\xrightarrow{\widehat\iota}\widehat B\xrightarrow{\widehat q}\widehat C\to0$ 满足：

- 在 $\widehat A$ 处恒正合，在 $\widehat C$ 处恒正合，$\widehat q\widehat\iota=0$。
- 在 $\widehat B$ 处的缺陷是 $\ker\widehat q/\operatorname{im}\widehat\iota\cong\Lambda/c_0(S)$。
- 短正合 $\iff\Lambda=c_0(S)\iff\nu$ 有界（引理 0）。

等价地：$\nu$ 有界 $\iff$ $\operatorname{im}\widehat\iota$ 在 $\widehat B$ 中闭 $\iff$ $\eta_C:C\to\widehat C$ 双射。最后一条由引理 0 和命题 1.2 得出。

---

## 2. $E$、$j$、挠性与右逆

**命题 2.1。** $p$ 由 $\widehat q$ 诱导，$\widehat q$ 满，故 **$p$ 恒为满射**，且 $E=\ker\widehat q/\operatorname{im}\widehat\iota$。于是
$$\theta:\ \Lambda/c_0(S)\xrightarrow{\ \sim\ }E,\qquad [a]\mapsto \tau(a)+\operatorname{im}\widehat\iota$$
是 $S$ 模同构，即
$$E=\{[b]: b\in c_0(S),\ t^{\nu_n}\mid b_n\ \forall n\}\cong\{a\in S^{\mathbb N}:v(a_n)+\nu_n\to\infty\}/\{a: v(a_n)\to\infty\}.$$
特例：若每个值只被取有限次（$\nu_n\to\infty$），则 $\Lambda=S^{\mathbb N}$，$E=S^{\mathbb N}/c_0(S)$。

**命题 2.2（$j$）。** $j$ 是单射，像为
$$\operatorname{im}j=\{[b]: b\in\textstyle\bigoplus_nS\}=(\textstyle\bigoplus_nS+\operatorname{im}\widehat\iota)/\operatorname{im}\widehat\iota .$$
又 $p\circ j=\eta_C$（逐坐标验证），所以 $j(C)\cap E=0$。

*证明。* 设 $b\in B$，$j(q(b))=0$，则 $\eta_B(b)=\tau(a)$，$a\in c_0(S)$。故 $b_n=t^{\nu_n}a_n$。由 $b_n\in R$ 得 $a_n\in R$，且 $a$ 有限支撑，所以 $b=\iota(\sum a_nf_n)$，$q(b)=0$。

像：$\operatorname{im}j=\{[b]:b\in\bigoplus R\}$。对有限支撑的 $b\in\bigoplus S$，写 $b_n=r_n+t^{\nu_n}s_n$（$r_n=\mathrm{rep}_n(b_n\bmod t^{\nu_n})\in R$，$s_n\in S$），则 $r,s$ 有限支撑，$[b]=[r]=j(q(r))$。$j(C)\cap E=0$ 由 $\eta_C$ 单得出。∎

**命题 2.3（挠）。** $\bigcup_{r\ge1}Q[t^r]=j(C)$，且 $Q[t^r]=j(C[t^r])$，其中 $C[t^r]=\bigoplus_n t^{\max(\nu_n-r,0)}\bar S_n\bar e_n$。$E$ 是 $S$ 无挠模。

*证明。* "$\supseteq$"：$j(C)$ 的元素是有限和，被某个 $t^r$ 杀死。

"$\subseteq$"：设 $x=[b]$，$t^rx=0$，即 $t^rb=\tau(a)$，$a\in c_0(S)$。取赋值得 $v(b_n)-\nu_n=v(a_n)-r\to\infty$。故 $F=\{n:v(b_n)<\nu_n\}$ 有限。令 $a'_n=b_n/t^{\nu_n}$（$n\notin F$），$a'_n=0$（$n\in F$）。则 $v(a'_n)\to\infty$，即 $a'\in c_0(S)$。而 $b-\tau(a')$ 是 $b$ 限制在 $F$ 上，有限支撑。由 2.2，$x\in\operatorname{im}j$。

$Q[t^r]=j(C[t^r])$ 由 $j$ 单且与 $t$ 交换得出。

无挠：设 $0\ne s=t^ru\in S$（$u$ 为单位），$a\in\Lambda$，$s[a]=0$。则 $sa\in c_0(S)$，即 $v(a_n)+r\to\infty$，故 $a\in c_0(S)$，$[a]=0$。∎

**命题 2.4。** 以下三条等价：(1) $\nu$ 有界；(2) $E=0$（$p$ 为同构）；(3) $p$ 有 $S$ 线性右逆。

*证明。* (1)⇔(2)：由 2.1 与引理 0(a)(b)。无界时 $[\tau(u)]\in E$ 非零。

(2)⇒(3)：取 $p^{-1}$。

(3)⇒(1)：设 $\sigma$ 是 $t$ 线性的（特别是 $S$ 线性的），$p\sigma=\mathrm{id}$。若 $\nu$ 无界，取引理 0(b) 的 $\gamma\in\widehat C$，$t\gamma=0$，$\gamma\notin\eta_C(C)$。则 $t\sigma(\gamma)=0$，由 2.3 得 $\sigma(\gamma)=j(y)$。于是 $\gamma=p\sigma(\gamma)=pj(y)=\eta_C(y)\in\eta_C(C)$，矛盾。∎

**注。** 由 $p(j(C)+E)=\eta_C(C)$ 得 $Q/(j(C)\oplus E)\cong\widehat C/C$。

---

## 3. 商拓扑与完成

**引理 3.1。**
(a) $t^m\widehat C=\{c\in\mathcal C:w_n(c_n)\ge m\ \forall n\}=\ker\pi^C_m$。
(b) $\pi^B_m,\pi^C_m$ 满，所以 $\widehat B/t^m\widehat B\cong B/t^mB$，$\widehat C/t^m\widehat C\cong C/t^mC$（记这些同构为 $\bar\pi^B_m,\bar\pi^C_m$）。
(c) $\bigcap_mt^m\widehat C=0$。
(d) $\eta_{\widehat C}:\widehat C\to\widehat{\widehat C}$ 是同构。

*证明。* (a) 由命题 1.2 和 (W)，$\ker\pi^C_m=\{c: c_n\in t^{\min(m,\nu_n)}\bar S_n=t^m\bar S_n\ \forall n\}=\{w_n(c_n)\ge m\ \forall n\}$。"$t^m\widehat C\subseteq$ 它"显然。反之，对这样的 $c$，$\tilde c\in c_0(S)$ 且 $v(\tilde c_n)=w_n(c_n)\ge m$，故 $\tilde c\in t^m\widehat B$，$c=\widehat q(\tilde c)\in t^m\widehat C$。

(b) $\pi^B_m\eta_B$ 与 $\pi^C_m\eta_C$ 是商映射，故满。

(c) 由 (a)。

(d) 同构 $\bar\pi^C_m$ 与过渡映射相容，故 $\widehat{\widehat C}=\varprojlim\widehat C/t^m\widehat C\cong\varprojlim C/t^mC=\widehat C$，在此认同下 $\eta_{\widehat C}$ 是恒等。∎

**命题 3.2。** 对每个 $m\ge1$，$\bar p_m:Q/t^mQ\to\widehat C/t^m\widehat C$ 是同构。更准确地，令 $\rho_m=\pi^C_m\circ p$，则 $\rho_m([b])=q_m(\pi^B_m(b))$，$\ker\rho_m=t^mQ=p^{-1}(t^m\widehat C)$，且 $\bar\pi^C_m\bar p_m=\bar\rho_m$。因此 $Q/t^mQ\cong C/t^mC\cong\widehat C/t^m\widehat C$，$\bar p_m$ 在这些认同下是恒等。

*证明。* $\rho_m$ 满（两个满射的复合）。$\rho_m([b])=0\iff\pi^B_m(b)\in\ker q_m=\operatorname{im}\iota_m=\pi^B_m(\operatorname{im}\widehat\iota)$（因 $\pi^A_m$ 满）。这等价于 $b\in\operatorname{im}\widehat\iota+t^m\widehat B$，即 $[b]\in t^mQ$。故 $\ker\rho_m=t^mQ$，同时 $\ker\rho_m=p^{-1}(\ker\pi^C_m)=p^{-1}(t^m\widehat C)$。$\bar\rho_m$ 和 $\bar\pi^C_m$ 都是同构，所以 $\bar p_m=(\bar\pi^C_m)^{-1}\bar\rho_m$ 是同构。∎

**命题 3.3。**
(i) $E\subseteq t^mQ$ 对一切 $m$ 成立，且 $\bigcap_{m\ge1}t^mQ=E$。即 $E$ 恰是 $Q$ 中 $0$ 的闭包，$Q/E=\widehat C$ 是 $Q$ 的分离商。
(ii) $\bar\rho=\varprojlim\bar\rho_m:\widehat Q\to\varprojlim C/t^mC=\widehat C$ 是同构，且 $\bar\rho\circ\eta_Q=p$。所以 $\widehat Q\cong\widehat C\cong\mathcal C$，$\eta_Q$ 满，$\ker\eta_Q=E$，$\eta_Q$ 单 $\iff E=0$。
(iii) $\widehat p=\varprojlim\bar p_m:\widehat Q\to\widehat{\widehat C}$ 是同构，且 $\widehat p=\eta_{\widehat C}\circ\bar\rho$。

*证明。* (i) 由 3.2，$t^mQ=p^{-1}(t^m\widehat C)\supseteq p^{-1}(0)=E$。又 $\bigcap_mt^mQ=p^{-1}(\bigcap_mt^m\widehat C)=p^{-1}(0)=E$（引理 3.1(c)）。

(ii) $\bar\rho$ 是同构的极限。$\bar\rho(\eta_Q(x))$ 的第 $m$ 分量为 $\rho_m(x)=\pi^C_m(p(x))$，即 $p(x)$ 的第 $m$ 分量。

(iii) $\varprojlim\bar p_m$ 是同构的极限。比较第 $m$ 分量：两边经 $\bar\pi^C_m$ 后都等于 $\bar\rho_m(x_m)$。再由引理 3.1(d)。∎

**命题 3.4（$E$ 自身的拓扑）。** 令 $\Lambda_m=t^m\Lambda+c_0(S)$。则

- $t^m\Lambda=\Lambda\cap(t^mS)^{\mathbb N}$。
- $\Lambda_m=\{a\in\Lambda: a_n\in t^mS\text{ 对几乎所有 }n\}$。
- $\theta$ 把 $t^mE$ 对应到 $\Lambda_m/c_0(S)$，所以 $E/t^mE\cong\Lambda/\Lambda_m$。

进而 $E$ 是 $t$ 进分离且完备的：$\bigcap_mt^mE=0$，$\eta_E:E\to\widehat E$ 是同构，即 $\widehat E=E$。

*证明。* 若 $d\in\Lambda$ 且所有 $d_n\in t^mS$，则 $(d_n/t^m)\in\Lambda$（赋值和减去 $m$ 不改变极限），所以 $d\in t^m\Lambda$。这给出第一式。

第二式："$\subseteq$"显然。反之，设 $a\in\Lambda$，$F=\{n:a_n\notin t^mS\}$ 有限。令 $e=a|_F\in c_0(S)$，$d=(a-e)/t^m\in\Lambda$。则 $a=t^md+e\in\Lambda_m$。

分离：$\bigcap_m\Lambda_m=\{a\in\Lambda: \forall m,\ a_n\in t^mS\text{ a.a. }n\}=\Lambda\cap c_0(S)=c_0(S)$。

完备：设 $(x_m)\in\widehat E$。归纳取 $y^{(m)}\in\Lambda$ 使 $\theta[y^{(m)}]+t^mE=x_m$ 且 $y^{(m+1)}-y^{(m)}\in t^m\Lambda$。具体地，取任一 $z\in\Lambda$ 代表 $x_{m+1}$。相容性给出 $z-y^{(m)}=t^md+e$（$d\in\Lambda$，$e\in c_0(S)$）。令 $y^{(m+1)}=z-e$。

对每个 $n$，$(y^{(m)}_n)_m$ 是 $S$ 中的柯西列，极限 $a_n$ 满足 $v(a_n-y_n^{(m)})\ge m$。对 $K\ge1$，$v(a_n)+\nu_n\ge\min(v(y^{(K)}_n)+\nu_n,K)$。因 $y^{(K)}\in\Lambda$，对几乎所有 $n$ 右端 $\ge K$。故 $a\in\Lambda$。又 $a-y^{(m)}\in\Lambda\cap(t^mS)^{\mathbb N}=t^m\Lambda$。于是 $\eta_E(\theta[a])=(x_m)$。∎

**命题 3.5（拓扑比较）。**

- $E$ 自身的 $t$ 进拓扑（基 $\{t^mE\}$）对每个指数列都是分离的（Hausdorff）且完备的。
- $E$ 从 $Q$ 继承的子空间拓扑，其基为 $E\cap t^mQ=E$（由 3.3(i)），所以是平凡（不分离）拓扑。
- 两者相同 $\iff E=0\iff\nu$ 有界。否则自身拓扑严格更细。

*证明。* 前两条由 3.4 和 3.3(i)。若两拓扑相同，则 $t^mE=E$ 对一切 $m$ 成立，于是 $E=\bigcap_m t^mE=0$。反之 $E=0$ 时显然相同。$E=0\iff\nu$ 有界由 2.4。

无界时的直接见证：$[u]\in E$（$u$ 来自引理 0(b)）不属于 $tE$。因为 $u\notin\Lambda_1$（$u_{n_i}=1$ 对无穷多个 $i$ 成立），所以 $tE\ne E$。∎

**推论（完成函子的失效）。** 内含映射 $E\hookrightarrow Q$ 诱导的 $\widehat E\to\widehat Q$ 为零，因为 $E\subseteq t^mQ$。所以完成 $0\to E\to Q\to\widehat C\to0$ 得到 $0\to\widehat E\xrightarrow{0}\widehat Q\xrightarrow{\sim}\widehat{\widehat C}\to0$，它在 $\widehat E\cong E$ 处不正合，除非 $E=0$。

---

## 综合：对每个指数列，以下十条等价

1. $\nu$ 有界（$\exists N\ \forall n:\ \nu_n\le N$，即 $t^NC=0$）。
2. 完成列短正合。
3. $\operatorname{im}\widehat\iota$ 在 $\widehat B$ 中闭。
4. $E=0$。
5. $p$ 是同构。
6. $p$ 有 $S$ 线性右逆。
7. $Q$ 是 $t$ 进分离的，即 $\bigcap t^mQ=0$。
8. $\eta_Q$ 是单射（此时为同构）。
9. $E$ 的两种拓扑相同。
10. $j:C\to Q$ 是同构。

前九条已由 1.5、2.4、3.3、3.5 得出。(10)：有界时，$p$ 同构且 $pj=\eta_C$ 同构（引理 0(a)），故 $j$ 同构。反之，若 $j$ 满，则 $E\subseteq j(C)$，由 $j(C)\cap E=0$ 得 $E=0$。

无论 $\nu$ 是否有界，下列总成立：

- $\widehat\iota$ 单，$\widehat q$ 满，$p$ 满。
- $j$ 单。
- $E$ 是 $S$ 无挠模。
- $Q/t^mQ\cong\widehat C/t^m\widehat C$。
- $\bigcap_mt^mQ=E$。
- $\widehat Q\cong\widehat C$，$\widehat E=E$，$\widehat p$ 是同构。