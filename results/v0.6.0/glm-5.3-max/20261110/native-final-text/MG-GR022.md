# 解答

以下所有结论对任意取定的非负整数列 $(\nu_n)_{n\ge 1}$ 成立；凡涉及充要条件处，均用 $(\nu_n)$ 直接表述。约定 $\mathbb N=\{0,1,2,\dots\}$。

## 0. 记号与预备

**赋值.** 设 $v:S\to\mathbb N\cup\{\infty\}$，$v(0)=\infty$，$v(t^d u)=d$（$u\in S^\times$）。则

* (V1) $v(xy)=v(x)+v(y)$（$S$ 整环）；
* (V2) $v(x+y)\ge\min(v(x),v(y))$，且当 $v(x)\ne v(y)$ 时取等。

对 $\nu\ge 0$ 记 $T_\nu:=S/t^\nu S$（$T_0=0$）。$T_\nu$ 中每个元素有唯一次数 $<\nu$ 的多项式代表 $\rho(c)\in k[t]_{<\nu}\subset S$，定义 $v(c):=v(\rho(c))\in\{0,\dots,\nu-1\}\cup\{\infty\}$，则 $v(c)=\infty\iff c=0$，且

* (F3) 对 $j\ge0$：$c\in t^jT_\nu\iff v(c)\ge j$（当 $j\ge\nu$ 时 $t^jT_\nu=0$）。
* (F4) 对 $x\in S$：$x\bmod t^j\in S/t^j$ 满足 $v(x\bmod t^j)=v(x)$（若 $v(x)<j$），$=\infty$（若 $v(x)\ge j$）。

**“$\to\infty$”.** 对序列 $u_n\in\mathbb N\cup\{\infty\}$，记 $u_n\to\infty$ 为：对每个 $m\ge1$，$\{n:u_n<m\}$ 是有限集（取值 $\infty$ 的项不计入）。显见：$u_n\to\infty,\ C\in\mathbb Z\Rightarrow u_n-C\to\infty$（在 $u_n-C\ge0$ 或 $=\infty$ 有意义的场合，因 $\{n:u_n-C<m\}\subseteq\{n:u_n<m+C\}$）。

**相容商记录与 $\eta$.** $\widehat M=\varprojlim_m M/t^mM$，其元素即相容系 $(\bar x_m)_{m\ge1}$（$\bar x_m\in M/t^mM$，$\bar x_{m+1}\bmod t^mM=\bar x_m$）；$\eta_M(x)=(x\bmod t^mM)_m$。$R$-线性映射 $f:M\to N$ 满足 $f(t^mM)\subseteq t^mN$，故诱导 $\widehat f$，且 $\eta_N\circ f=\widehat f\circ\eta_M$。$S$ 在 $\widehat M$ 上的作用由各层 $S/t^m$ 作用给出。另外 $\varprojlim_m S/t^mS\cong S$。

**引理 0.1（$C$ 及其商）.** (a) $C\cong\bigoplus_{n\ge1}T_{\nu_n}\bar e_n$（$R$-模且 $S$-模同构），$\bar e_n=q(e_n)$；$\ker\big(B\to\bigoplus T_{\nu_n}\big)=\iota(A)$。
(b) 对 $m\ge1$：$C/t^mC\cong\bigoplus_n\big(T_{\nu_n}/t^mT_{\nu_n}\big)\bar e_n\cong\bigoplus_n\big(S/t^{\min(\nu_n,m)}\big)\bar e_n$（典范）。

*证.* (a) $B=\bigoplus Re_n\to\bigoplus R/t^{\nu_n}$，$e_n\mapsto\bar e_n$，其核为 $\{(r_n)_{\text{有限支撑}}: r_n\in t^{\nu_n}R\ \forall n\}=\iota(A)$；$R/t^\nu\cong S/t^\nu=T_\nu$。(b) 直和与商交换；$T_\nu/t^mT_\nu=(S/t^\nu)/(t^mS/t^\nu)\cong S/t^{\min(\nu,m)}$。∎

**命题 0.2（坐标模型）.** 定义
$$\mathcal B:=\Big\{(x_n)_{n\ge1}\in S^{\mathbb N}: v(x_n)\to\infty\Big\},\qquad
\mathcal C:=\Big\{(c_n)\in\prod_n T_{\nu_n}: v(c_n)\to\infty\Big\}.$$

(a) $\Psi_B:\widehat B\to\mathcal B$，$(\bar b^{(m)})_m\mapsto(b_n)_n$，其中 $b_n:=\varprojlim_m(\bar b^{(m)}$ 的 $e_n$-系数$)\in S$，是 $S$-模同构，逆为 $(b_n)\mapsto\big(\bar b^{(m)}:=\sum_n(b_n\bmod t^m)e_n\big)_m$（注意 $\operatorname{supp}\bar b^{(m)}\subseteq\{n:v(b_n)<m\}$ 有限）。$\Psi_A$ 对 $\widehat A$（$f$-坐标）同理，模型同为 $\mathcal B$。
(b) $\Psi_C:\widehat C\to\mathcal C$，$(\bar c^{(m)})_m\mapsto(c_n)_n$，$c_n:=\varprojlim_m(\bar c^{(m)}$ 的 $\bar e_n$-系数，视作 $S/t^{\min(\nu_n,m)}$$)\in T_{\nu_n}$，是 $S$-模同构，逆为 $(c_n)\mapsto\big(\bar c^{(m)}:=\sum_n(c_n\bmod t^mT_{\nu_n})\bar e_n\big)_m$；此处 $\operatorname{supp}\bar c^{(m)}=\{n:c_n\ne0,\ v(c_n)<m\}$，故上述逆良定义当且仅当 $c\in\mathcal C$。
(c) 在上述模型下，$\eta_A,\eta_B,\eta_C$ 均为单射，且分别是有限支撑多项式族 $\bigoplus_n k[t]\,(\subset\mathcal B)$ 与有限支撑族 $\bigoplus_n T_{\nu_n}(\subset\mathcal C)$ 的包含映射。

*证.* (a)：相容性保证逐分量极限存在（$S$ 完备）；若 $v(b_n)<m$ 则 $b_n\bmod t^m\ne0$（F4），故 $n\in\operatorname{supp}\bar b^{(m)}$，有限；两个构造互逆是标准的；$S$-线性逐层验证。(b)：$T_{\nu_n}/t^mT_{\nu_n}\cong S/t^{\min(\nu_n,m)}$，且对 $c_n\ne0$ 有 $v(c_n)<\nu_n$，故 $c_n\bmod t^mT_{\nu_n}\ne0\iff v(c_n)<\min(\nu_n,m)\iff c_n\ne0\wedge v(c_n)<m$；这正是 $\mathcal C$ 的条件。其余同 (a)。(c) 直接验证。∎

**引理 0.3（完成上的 $t$-进滤）.** 对 $m\ge1$：
(a) $t^m\widehat B=\{b\in\mathcal B:\ v(b_n)\ge m\ \forall n\}=\ker(\widehat B\to B/t^mB)$；
(b) $t^m\widehat A$ 同理；
(c) $t^m\widehat C=\{c\in\mathcal C:\ v(c_n)\ge\min(\nu_n,m)\ \forall n\}=\ker(\widehat C\to C/t^mC)$。

特别地 $\widehat A,\widehat B,\widehat C$ 都是 $t$-进分离的，且其 $t$-进拓扑与逆极限拓扑（以 $\ker(\widehat M\to M/t^mM)$ 为基）一致。

*证.* (a) “$\subseteq$”显然。“$\supseteq$”：令 $x_n:=b_n/t^m$，则 $\{n:v(x_n)<M\}=\{n:v(b_n)<m+M\}$ 有限，故 $x\in\mathcal B$ 且 $t^mx=b$。核的刻画由 (F4)。(c) “$\subseteq$”：$c=t^mx$ 时 $v(c_n)\ge\min(m,\nu_n)$（若 $c_n\ne0$ 则 $v(c_n)=m+v(x_n)\ge m$）。"$\supseteq$"：若 $\nu_n\le m$ 则 $v(c_n)\ge\nu_n$ 故 $c_n\in t^{\nu_n}T_{\nu_n}=0$，令 $x_n=0$；若 $\nu_n>m$ 且 $c_n\ne0$，写 $\rho(c_n)=t^mh_n$（$h_n\in k[t]_{<\nu_n-m}$），令 $x_n:=h_n\bmod t^{\nu_n}$，则 $t^mx_n=c_n$ 且 $v(x_n)=v(c_n)-m$。于是 $\{n:v(x_n)<M\}\subseteq\{n:c_n\ne0,\ v(c_n)<\min(\nu_n,m+M)\}$ 有限，故 $x\in\mathcal C$。核的刻画由 (F3)。∎

## 1. 第一部分：三个完成、正合性、闭包与纤维

**命题 1.1（诱导映射的坐标公式）.** 在命题 0.2 的模型下：
$$\widehat\iota:\ (a_n)\mapsto(t^{\nu_n}a_n),\qquad \widehat q:\ (b_n)\mapsto(b_n\bmod t^{\nu_n}).$$
逐层公式为 $\iota_m:(a_n\bmod t^m)\mapsto(t^{\nu_n}a_n\bmod t^m)$，$q_m:(b_n\bmod t^m)\mapsto(b_n\bmod t^{\min(\nu_n,m)})$。且：

(i) $\widehat\iota$ 单（对一切 $\nu$）；(ii) $\widehat q$ 满（对一切 $\nu$）；(iii) $\widehat q\circ\widehat\iota=0$；$\eta_B\iota=\widehat\iota\eta_A$，$\eta_Cq=\widehat q\eta_B$。

*证.* 公式逐层验证。良定义：$v(t^{\nu_n}a_n)=\nu_n+v(a_n)\ge v(a_n)\to\infty$；(iii) $t^{\nu_n}a_n\equiv0\pmod{t^{\nu_n}}$。(i) $t^{\nu_n}a_n=0\Rightarrow a_n=0$（V1，$\nu_n<\infty$）。(ii) 给定 $c\in\mathcal C$，令 $b_n:=\rho(c_n)$（次数 $<\nu_n$ 的多项式代表），则 $v(b_n)=v(c_n)\to\infty$，故 $b\in\mathcal B$ 且 $\widehat q(b)=c$。∎

**命题 1.2（核与像）.**
$$\ker\widehat q=\{b\in\mathcal B:\ v(b_n)\ge\nu_n\ \forall n\},\qquad
\operatorname{im}\widehat\iota=\{b\in\mathcal B:\ v(b_n)\ge\nu_n\ \forall n\ \text{且}\ v(b_n)-\nu_n\to\infty\},$$
其中 $v(b_n)-\nu_n$ 当 $b_n=0$ 时理解为 $\infty$。

*证.* $\widehat q(b)=0\iff b_n\in t^{\nu_n}S\ \forall n$。$b=\widehat\iota(a)$ 时 $a$ 由 $a_n=b_n/t^{\nu_n}$ 唯一决定（V1），存在性即 $v(b_n)\ge\nu_n\ \forall n$，且 $v(a_n)=v(b_n)-\nu_n\to\infty$。∎

**定理 1.3（完成列的正合性）.** 完成列 $0\to\widehat A\xrightarrow{\widehat\iota}\widehat B\xrightarrow{\widehat q}\widehat C\to0$ 对每个 $\nu$ 都是复形，且在 $\widehat A$ 处正合（$\widehat\iota$ 单）、在 $\widehat C$ 处正合（$\widehat q$ 满）；在 $\widehat B$ 处正合当且仅当 $(\nu_n)$ **有界**。故完成列短正合 $\iff(\nu_n)$ 有界。无界时 $\ker\widehat q/\operatorname{im}\widehat\iota=E\ne0$（见第二部分）。

*证.* 只须证中间正合性。**($\Leftarrow$)** 设 $\nu_n\le N$。对 $b\in\ker\widehat q$，令 $a_n:=b_n/t^{\nu_n}$，则 $v(a_n)=v(b_n)-\nu_n\ge v(b_n)-N$，且 $\{n:v(a_n)<m\}\subseteq\{n:v(b_n)<m+N\}$ 有限，故 $a\in\mathcal A$，$\widehat\iota(a)=b$。**($\Rightarrow$ 反证)** 设 $(\nu_n)$ 无界，取 $1\le n_1<n_2<\cdots$ 使 $\nu_{n_k}\ge k$（无界时 $\{n:\nu_n\ge k\}$ 无限）。令
$$b_n:=t^{\nu_n}\ (n\in P:=\{n_k\}),\qquad b_n:=t^{\nu_n+n}\ (n\notin P).$$
则 $v(b_n)\ge\nu_n\ \forall n$，且 $\{n:v(b_n)<m\}\subseteq\{n_k:k<m\}\cup\{n:n<m\}$ 有限，故 $b\in\ker\widehat q$；但 $v(b_n)-\nu_n=0$ 于无穷集 $P$，不趋于 $\infty$，故 $b\notin\operatorname{im}\widehat\iota$。∎

**引理 1.4（关键引理）.** 记 $I:=\operatorname{im}\widehat\iota$。对 $m\ge1$：
$$I+t^m\widehat B=\{b\in\mathcal B:\ v(b_n)\ge\min(\nu_n,m)\ \forall n\}.$$

*证.* “$\subseteq$”：$I$ 中元满足 $v\ge\nu_n\ge\min(\nu_n,m)$；$t^m\widehat B$ 中元 $v\ge m\ge\min(\nu_n,m)$。“$\supseteq$”：给定 $b$ 满足右边条件。定义 $a\in S^{\mathbb N}$：当 $\nu_n\ge m$ 或 $v(b_n)\ge m$ 时 $a_n:=0$；否则（此时 $\nu_n<m$ 且 $\nu_n\le v(b_n)<m$）$a_n:=\pi_{[\nu_n,m)}(b_n)\cdot t^{-\nu_n}\in k[t]_{<m-\nu_n}$（即 $b_n$ 的 $[\nu_n,m)$ 次截断除以 $t^{\nu_n}$）。则 $t^{\nu_n}a_n=\pi_{[\nu_n,m)}(b_n)$，且 $b_n-t^{\nu_n}a_n=\pi_{<\nu_n}(b_n)+\pi_{\ge m}(b_n)=\pi_{\ge m}(b_n)$（因 $v(b_n)\ge\nu_n$），故 $v(b_n-t^{\nu_n}a_n)\ge m\ \forall n$，即 $b-\widehat\iota(a)\in t^m\widehat B$（引理 0.3(a)）。又 $a_n\ne0\Rightarrow v(b_n)<m$，故 $\{n:v(a_n)<M\}\subseteq\{n:v(b_n)<m\}$ 有限，$a\in\mathcal A$。∎

**定理 1.5（闭包）.** $\operatorname{im}\widehat\iota$ 在 $\widehat B$（$t$-进拓扑）中的闭包为
$$\overline{I}=\bigcap_m(I+t^m\widehat B)=\{b\in\mathcal B:\ v(b_n)\ge\nu_n\ \forall n\}=\ker\widehat q .$$
即 $\operatorname{im}\widehat\iota$ 在 $\ker\widehat q$ 中稠密。从而：$I$ 闭 $\iff I=\ker\widehat q\iff(\nu_n)$ 有界 $\iff$ 完成列中间正合。

*证.* 拓扑群中子群的闭包为 $\bigcap_m(I+t^m\widehat B)$（$x\in\overline I\iff\forall m:(x+t^m\widehat B)\cap I\ne\emptyset$）。由引理 1.4，$\bigcap_m\{v(b_n)\ge\min(\nu_n,m)\ \forall n\}=\{v(b_n)\ge\nu_n\ \forall n\}$（对固定的 $n$ 取 $m\ge\nu_n$）。再由命题 1.2 与定理 1.3 得后一等价。∎

**命题 1.7（$\widehat q$ 的纤维）.** 对 $c=(c_n)\in\mathcal C$：
$$\widehat q^{-1}(c)=\{b\in\mathcal B:\ b_n\equiv c_n\pmod{t^{\nu_n}}\ \forall n\}=\rho(c)+\ker\widehat q,\qquad \rho(c):=(\rho(c_n))_n\in\mathcal B .$$
故每个纤维非空，且是闭子群 $\ker\widehat q=\overline{\operatorname{im}\widehat\iota}$ 的一个陪集；纤维在商 $Q=\widehat B/I$ 中的像为 $p^{-1}(c)$，它是 $E=\ker\widehat q/I$ 在 $Q$ 中的陪集。

*证.* $\rho(c_n)\equiv c_n$；两个原像之差属于 $\ker\widehat q$。∎

## 2. 第二部分：$E$、$j$、挠元与分裂

记 $Q=\widehat B/I$，元素写作 $[b]$；由命题 1.2：
$$[b]=0\iff v(b_n)\ge\nu_n\ \forall n\ \text{且}\ v(b_n)-\nu_n\to\infty .\tag{2.0}$$

**命题 2.1（$E$ 的坐标模型）.** (a) $E=\ker p=\ker\widehat q/I=\{[b]\in Q:\ v(b_n)\ge\nu_n\ \forall n\}$。
(b) 令
$$\Gamma:=\{(a_n)\in S^{\mathbb N}:\ \nu_n+v(a_n)\to\infty\},\qquad \Gamma':=\{(a_n)\in S^{\mathbb N}:\ v(a_n)\to\infty\}$$
（$S$-子模，$\Gamma'\subseteq\Gamma$，$t$ 的作用为 $(a_n)\mapsto(ta_n)$）。则
$$\Theta:\Gamma/\Gamma'\xrightarrow{\ \cong\ }E,\qquad [(a_n)]\mapsto[(t^{\nu_n}a_n)]$$
是 $S$-模同构；在 $\Gamma/\Gamma'$ 中 $[(a)]=0\iff v(a_n)\to\infty$。
(c) $\Gamma$ 可改写为
$$\Gamma=\{(a_n):\ v(a_n)\to\infty\ \text{沿每个}\ Z_N:=\{n:\nu_n\le N\},\ \forall N\ge0\}.$$
即：$\Gamma$ 中的族沿每条 $\nu$ 有界的子列必须 $t$-进趋于 $0$，而沿 $\nu_n\to\infty$ 的子列可任意。

*证.* (a) $p([b])=\widehat q(b)$。(b) $\ker\widehat q\xrightarrow{\sim}\Gamma$，$(b_n)\mapsto(b_n/t^{\nu_n})$（其逆为 $(a)\mapsto(t^{\nu_n}a_n)$），在此之下 $I\leftrightarrow\Gamma'$。零化条件即 (2.0) 的翻译。(c) $\nu_n+v(a_n)\to\infty\Rightarrow$ 沿 $Z_N$：$\{n\in Z_N:v(a_n)<m\}\subseteq\{n:\nu_n+v(a_n)<N+m+1\}$ 有限。反之，$\{n:\nu_n+v(a_n)<m\}\subseteq\{n\in Z_{m-1}:v(a_n)<m\}$ 有限。∎

**命题 2.2（$j$）.** $j:C\to Q$ 良定义、加法、$S$-线性，且 $p\circ j=\eta_C$。并且：
$$\ker j=0\ (\text{\emph{$j$ 单}})，\qquad \operatorname{im}j=\{[b]\in Q:\ v(b_n)-\nu_n\to\infty\}. \tag{2.3}$$
且 $\operatorname{im}j$ 恰为 $Q$ 中有限支撑多项式族代表的类的集合。

*证.* 良定义：$q(b)=q(b')\Rightarrow b-b'\in\iota(A)\Rightarrow\eta_B(b)-\eta_B(b')=\widehat\iota(\eta_A(\cdot))\in I$。$S$-线性：设 $c=q(b)$（$b$ 有限支撑多项式族），$s\in S$；取 $N\ge\max_{\operatorname{supp}b}\nu_n$ 与多项式 $r\equiv s\pmod{t^N}$，则 $s\cdot c=r\cdot c=q(rb)$，故 $j(s c)=r\eta_B(b)+I$；而 $(s-r)\eta_B(b)$ 的第 $n$ 分量为 $(s-r)b_n$，满足 $v\ge N+v(b_n)\ge\nu_n$ 且在有限支撑外为 $0$，故属于 $I$，于是 $s\,j(c)=r\eta_B(b)+I=j(sc)$。

$\ker j$：$[b]=0$（$b\in B$ 有限支撑）$\iff v(b_n)\ge\nu_n\ \forall n$ $\iff b\in\iota(A)$（此时 $a_n=b_n/t^{\nu_n}$ 支撑含于 $\operatorname{supp}b$），故 $\ker j=q(\iota(A))=0$。

$\operatorname{im}j$：“$\subseteq$”：$b\in B$ 时 $v(b_n)-\nu_n=\infty$ 于支撑外。“$\supseteq$”：设 $v(b_n)-\nu_n\to\infty$。令 $b'_n:=\pi_{<\nu_n}(b_n)$（次数 $<\nu_n$ 的截断）。支撑 $\{n:b'_n\ne0\}=\{n:v(b_n)<\nu_n\}\subseteq\{n:v(b_n)-\nu_n<0\}$ 有限，故 $b'\in B$。又 $b_n-b'_n=\pi_{\ge\nu_n}(b_n)$ 满足 $v\ge\max(\nu_n,v(b_n))$，故 $a_n:=(b_n-b'_n)/t^{\nu_n}$ 满足 $v(a_n)\ge\max(0,v(b_n)-\nu_n)$，且 $\{n:v(a_n)<M\}\subseteq\{n:v(b_n)-\nu_n<M\}$ 有限，即 $a\in\mathcal A$，$\widehat\iota(a)=b-b'$。故 $[b]=[b']=j(q(b'))$。∎

**定理 2.4（$Q$ 的挠元）.** 对 $r\ge1$ 与 $b\in\mathcal B$：
$$t^r[b]=0\iff\big(v(b_n)\ge\nu_n-r\ \forall n\big)\ \wedge\ \big(v(b_n)-\nu_n\to\infty\big),$$
（其中当 $\nu_n\le r$ 时第一个条件为空）。而 $v(b_n)-\nu_n\to\infty$ 自动蕴涵 $v(b_n)-\nu_n$ 有下界（$\{n:v(b_n)-\nu_n<0\}$ 有限），故
$$Q_{\mathrm{tors}}:=\{x\in Q:\exists r\ge1,\ t^rx=0\}=\{[b]:\ v(b_n)-\nu_n\to\infty\}=\operatorname{im}j=j(C)\cong C .$$

*证.* $t^r[b]=0\iff(t^rb_n)\in I\iff\exists a\in\mathcal A:\ t^{\nu_n}a_n=t^rb_n\ \forall n$。由 V1 与 $\nu_n<\infty$，这样的 $a$ 唯一：$a_n=t^{r-\nu_n}b_n$，它属于 $S$ 当且仅当 $r+v(b_n)-\nu_n\ge0$；而 $v(a_n)=r+v(b_n)-\nu_n\to\infty\iff v(b_n)-\nu_n\to\infty$。再引用 (2.3)。∎

**定理 2.5（$E$ 的挠性）.** (a) $E$ 是无挠 $S$-模：$E\cap Q_{\mathrm{tors}}=\{0\}$。从而 $E$ 为挠模 $\iff E=0\iff(\nu_n)$ 有界。
(b) $E=0\iff(\nu_n)$ 有界；无界时可取定理 1.3 中的 $b$（$b_n=t^{\nu_n}$ 于 $P$，$t^{\nu_n+n}$ 于 $P$ 外），则 $0\ne[b]\in E$。
(c) $p$ 对每个 $\nu$ 都满（因 $\widehat q=p\circ\pi$ 满）。

*证.* (a) 若 $[b]\in E$（$v(b_n)\ge\nu_n\ \forall n$）且 $v(b_n)-\nu_n\to\infty$，则由 (2.0) 得 $[b]=0$。若 $t^r x=0$（$x\in E$），则 $x\in E\cap Q_{\mathrm{tors}}=\{0\}$。∎

**定理 2.6（右逆的充要条件）.** 下列等价：(i) $(\nu_n)$ 有界；(ii) $E=0$；(iii) $p$ 有 $S$-线性右逆。且 (iii) 成立时 $p$ 是同构，右逆唯一（$s=p^{-1}$）。

*证.* (i)$\Rightarrow$(ii)：定理 1.3。(ii)$\Rightarrow$(iii)：$p$ 满（定理 2.5(c)）且 $\ker p=E=0$，故 $p$ 双射。$\neg$(i)$\Rightarrow\neg$(iii)：设 $(\nu_n)$ 无界，取 $n_1<n_2<\cdots$ 使 $\nu_{n_k}\ge k$，定义 $z\in\mathcal C$：$z_{n_k}:=t^{\nu_{n_k}-1}\bmod t^{\nu_{n_k}}\in T_{\nu_{n_k}}$，其余 $z_n:=0$。则 $\{n:z_n\ne0,\ v(z_n)<m\}\subseteq\{n_k:k<m\}$ 有限，故 $z\in\widehat C$；且 $tz=0$（$t\cdot t^{\nu-1}=t^\nu=0\in T_\nu$）。设 $s$ 为右逆，写 $s(z)=[b]$。由 $p(s(z))=z$ 得 $b_{n_k}\equiv t^{\nu_{n_k}-1}\pmod{t^{\nu_{n_k}}}$。由 $t\,s(z)=s(tz)=0$ 得 $(t b_n)\in I$，即存在 $(a_n)\in\mathcal A$ 使 $t^{\nu_n}a_n=tb_n\ \forall n$。在 $n=n_k$ 处：$t^{\nu_{n_k}}a_{n_k}=tb_{n_k}\equiv t^{\nu_{n_k}}\pmod{t^{\nu_{n_k}+1}}$，故 $a_{n_k}\equiv1\pmod t$，即 $v(a_{n_k})=0$ 对一切 $k$。但 $v(a_n)\to\infty$ 蕴涵 $v(a_n)\ge1$ 对充分大的 $n$，而 $n_k\to\infty$，矛盾。∎

## 3. 第三部分：商的完成与拓扑

**定理 3.1（$p$ 诱导的 $Q/t^mQ\to\widehat C/t^m\widehat C$）.** 设 $m\ge1$。有典范同构
$$\alpha_m:\ Q/t^mQ\xrightarrow{\ \cong\ }C/t^mC=\bigoplus_n(S/t^{\min(\nu_n,m)})\bar e_n,\quad [b]\mapsto\sum_n\big(b_n\bmod t^{\min(\nu_n,m)}\big)\bar e_n,$$
$$\beta_m:\ \widehat C/t^m\widehat C\xrightarrow{\ \cong\ }C/t^mC,\quad c\mapsto\sum_n\big(c_n\bmod t^{\min(\nu_n,m)}\big)\bar e_n,$$
且 $p$ 诱导的映射满足 $\beta_m\circ\bar p_m=\alpha_m$。因此 **对每个 $m\ge1$，$\bar p_m:Q/t^mQ\to\widehat C/t^m\widehat C$ 是同构**（在上述两个典范同构下即为 $\operatorname{id}_{C/t^mC}$）。特别地 $(E+t^mQ)/t^mQ=\ker\bar p_m=0$，即 $E\subseteq t^mQ$ 对一切 $m$。

*证.* $Q/t^mQ=\widehat B/(I+t^m\widehat B)$。$\alpha_m$ 由 $\Theta_m:\widehat B\to C/t^mC$ 诱导，其核由引理 1.4 为 $I+t^m\widehat B$；$\Theta_m$ 满（有限支撑族可由多项式有限支撑族提升）。$\beta_m$ 由 $\Theta'_m:\widehat C\to C/t^mC$ 诱导，其核由引理 0.3(c) 为 $t^m\widehat C$；$\Theta'_m$ 满（把 $\gamma_n\in S/t^{\min(\nu_n,m)}$ 用次数 $<\min(\nu_n,m)\le\nu_n$ 的多项式代表嵌入 $T_{\nu_n}$）。$\beta_m\bar p_m([b])=\sum_n\big((b_n\bmod t^{\nu_n})\bmod t^{\min(\nu_n,m)}\big)\bar e_n=\alpha_m([b])$（因 $\min(\nu_n,m)\le\nu_n$）。∎

**定理 3.2（$\bigcap t^mQ$）.** $\displaystyle\bigcap_{m\ge1}t^mQ=E\ (=\ker p)$。从而 $Q$ 的 $t$-进拓扑分离 $\iff E=0\iff(\nu_n)$ 有界。

*证.* $[b]\in t^mQ\iff\alpha_m([b])=0\iff v(b_n)\ge\min(\nu_n,m)\ \forall n$；对一切 $m$ 成立 $\iff v(b_n)\ge\nu_n\ \forall n\iff[b]\in E$（命题 2.1(a)）。∎

**定理 3.3（$\widehat Q$ 与 $\eta_Q$）.** $\Phi:=\varprojlim_m\alpha_m:\widehat Q\to\varprojlim C/t^mC=\widehat C$ 是 $S$-模同构（各 $\alpha_m$ 与过渡映射相容），且
$$\Phi\circ\eta_Q=p .$$
故 $\eta_Q:Q\to\widehat Q$ 满、$\ker\eta_Q=\ker p=E$（与定理 3.2 一致）：**$Q$ 的 $t$-进分离完备化就是 $\widehat C$，且 $p$ 恰是 $Q$ 的完备化映射**。

*证.* 相容性：过渡均为“代同一公式”。$\Phi(\eta_Q([b]))=\big(\sum_n(b_n\bmod t^{\min(\nu_n,m)})\bar e_n\big)_m$，其第 $n$ 个分量的逐层极限为 $b_n\bmod t^{\nu_n}$，即 $\widehat q(b)=p([b])$。∎

**命题 3.4（$E$ 的 $t$-进滤）.** 在 $E\cong\Gamma/\Gamma'$ 下：
$$t^mE=\big\{[(a_n)]:\ v(a_n)\ge m\ \text{对除有限个外的所有}\ n\big\},\qquad \bigcap_{m\ge1}t^mE=0 .$$

*证.* 记 $\Gamma_m:=\{(a)\in\Gamma:\ v(a_n)\ge m\ \text{ eventual}\}$，断言它是 $t^mE$ 在 $\Gamma$ 中的原像。若 $[(a)]=[(t^ma'')]$（$(a'')\in\Gamma$），则 $v(a_n-t^ma''_n)\to\infty$，特别地对几乎一切 $n$ 有 $\ge m$，故 $v(a_n)\ge m$ eventual。反之设 $v(a_n)\ge m$ eventual，令 $a''_n:=a_n/t^m$ 于该余有限集、$a''_n:=0$ 于例外有限集，则 $(a'')\in\Gamma$ 且 $(a)-(t^ma'')\in\Gamma'$。最后 $\bigcap_m\Gamma_m\subseteq\Gamma'$：对每个 $m$，$v(a_n)\ge m$ eventual $\Rightarrow v(a_n)\to\infty$。∎

**命题 3.5（$E/t^mE$ 与 $\widehat E$）.** 令 $\Gamma^{(m)}:=\{(\beta_n)\in(S/t^m)^{\mathbb N}:\ \nu_n+v(\beta_n)\to\infty\ \text{沿}\ \operatorname{supp}\beta\}$（它包含所有有限支撑族），则
$$E/t^mE\ \cong\ \Gamma^{(m)}\Big/\bigoplus_n(S/t^m),\qquad [(a_n)]\mapsto[(a_n\bmod t^m)_n],$$
过渡映射为逐分量约化。**且 $\eta_E:E\to\widehat E$ 是同构**，即在上述模型下
$$\bar\theta:\ \Gamma/\Gamma'\xrightarrow{\ \cong\ }\widehat E=\varprojlim_m\Gamma^{(m)}\Big/\bigoplus_n(S/t^m),\quad [(a)]\mapsto\big([(a\bmod t^m)]\big)_m$$
是 $S$-模同构。特别地 **$E$ 是 $t$-进完备且分离的**。

*证.* 同构：由命题 3.4，核为 $\Gamma_m/\Gamma'$；截断 $(a)-(\pi_{<m}a)$ 满足 $v\ge\max(v(a_n),m)$ 且属于 $\Gamma$，故落在 $\Gamma_m$ 中，于是每类有 $\Gamma^{(m)}$ 代表（$\pi_{<m}a\in\Gamma$ 且是自身截断）；两个 $\Gamma^{(m)}$ 代表之差为 $\Gamma_m$ 中元且分量次数 $<m$，故几乎处处相等，即相差 $\bigoplus_n(S/t^m)$ 中元。良定义与满性由已证。$\bar\theta$ 良定义、单：$\bar\theta([a])=0\iff\forall m:\ a_n\bmod t^m$ 有限支撑 $\iff v(a_n)\to\infty\iff[a]=0$。满（严格化）：设 $(\xi_m)$ 相容，取代表 $\beta^{(m)}\in\Gamma^{(m)}$；相容性即 $F_m:=\{n:\beta^{(m+1)}_n\bmod t^m\ne\beta^{(m)}_n\}$ 有限。归纳构造 $\gamma^{(m)}\in\Gamma^{(m)}$：$\gamma^{(1)}:=\beta^{(1)}$；设 $\gamma^{(m)}$ 已给出且与 $\beta^{(m)}$ 只在有限集 $G_m$ 上不同，令 $\gamma^{(m+1)}_n:=\beta^{(m+1)}_n$（$n\notin F_m\cup G_m$），否则取 $\gamma^{(m)}_n$ 的任一 $S/t^{m+1}$ 提升。则 $\gamma^{(m+1)}\equiv\gamma^{(m)}\pmod{t^m}$ 对**一切** $n$ 成立，且 $\gamma^{(m+1)}-\beta^{(m+1)}$ 有限支撑（有限支撑族属 $\Gamma^{(m+1)}$，故 $\gamma^{(m+1)}\in\Gamma^{(m+1)}$）。令 $a_n:=\varprojlim_m\gamma^{(m)}_n\in S$，则 $a_n\equiv\gamma^{(m)}_n\pmod{t^m}$。证 $(a)\in\Gamma$：若 $\nu_n+v(a_n)<M$，则 $v(a_n)<M$，故 $\gamma^{(M)}_n\ne0$ 且 $v(\gamma^{(M)}_n)=v(a_n)$，于是 $n$ 落入有限集 $\{n:\gamma^{(M)}_n\ne0,\ \nu_n+v(\gamma^{(M)}_n)<M\}$。且 $\bar\theta([a])=(\xi_m)$（层 $m$ 上 $[(a\bmod t^m)]=[\gamma^{(m)}]=[\beta^{(m)}]=\xi_m$）。最后由构造，$\eta_E$ 在这些模型下正是 $\bar\theta$。∎

**定理 3.6（$p$ 诱导的完备化映射）.** $\eta_{\widehat C}:\widehat C\to\widehat{\widehat C}$ 是同构（$\widehat C$ 完备分离：由 $\beta_m$ 得 $\widehat{\widehat C}=\varprojlim\widehat C/t^m\widehat C\cong\varprojlim C/t^mC=\widehat C$，$\eta_{\widehat C}$ 对应恒等）。对 $p:Q\to\widehat C$ 诱导的 $\widehat p:\widehat Q\to\widehat{\widehat C}$，由 $\eta$ 的自然性 $\widehat p\circ\eta_Q=\eta_{\widehat C}\circ p$ 及定理 3.3 得
$$\widehat p=\eta_{\widehat C}\circ\Phi,$$
即在典范认同 $\widehat Q\cong\widehat C\cong\widehat{\widehat C}$ 下 **$\widehat p$ 就是 $\widehat C$ 的恒等映射；特别地 $\widehat p$ 是同构**。
另：包含 $\epsilon:E\hookrightarrow Q$ 诱导的 $\widehat\epsilon:\widehat E\to\widehat Q$ 是**零映射**，因为每层 $E/t^mE\to Q/t^mQ$ 由于 $E\subseteq t^mQ$ 而恒为零。于是完备化把正合列 $0\to E\to Q\to\widehat C\to0$ 变成 $0\to E\xrightarrow{0}\widehat C\xrightarrow{\cong}\widehat C\to0$：单射被完备化摧毁。

**定理 3.7（两种拓扑的比较）.**
(a) $E$ 自身的 $t$-进拓扑以 $t^mE$（命题 3.4）为基；它**恒分离**（$\bigcap t^mE=0$），且由命题 3.5 它完备。
(b) $E$ 从 $Q$ 继承的子空间拓扑以 $E\cap t^mQ$ 为基；由定理 3.2，$E\subseteq t^mQ\ \forall m$，故 $E\cap t^mQ=E\ \forall m$，从而任一基本开集 $E\cap(x+t^mQ)$ 或为空或为全 $E$（若含 $e_0$，则对 $e\in E$，$x-e=(x-e_0)+(e_0-e)\in t^mQ$）。即**子空间拓扑是平凡（不离散）拓扑 $\{\varnothing,E\}$**。
(c) 二者相同 $\iff E=0\iff(\nu_n)$ 有界。当 $(\nu_n)$ 无界时，子空间拓扑严格粗于自身拓扑（此时 $tE\subsetneq E$：否则 $E=t^mE\ \forall m$ 将给出 $E=\bigcap t^mE=0$）。

## 4. 结论汇总（均对任意 $(\nu_n)$ 成立；条件用 $(\nu_n)$ 表述）

| 对象 | 坐标模型 |
|---|---|
| $\widehat A,\widehat B$ | $\mathcal B=\{(x_n)\in S^{\mathbb N}:v(x_n)\to\infty\}$，同构 $(\bar x^{(m)})_m\mapsto(\varprojlim_m x^{(m)}_n)_n$，逆为逐层截断；$\eta$ = 有限支撑多项式族之包含 |
| $\widehat C$ | $\mathcal C=\{(c_n)\in\prod T_{\nu_n}:v(c_n)\to\infty\}$ |
| $\widehat\iota,\widehat q$ | $(a_n)\mapsto(t^{\nu_n}a_n)$；$(b_n)\mapsto(b_n\bmod t^{\nu_n})$ |
| $\ker\widehat q=\overline{\operatorname{im}\widehat\iota}$ | $\{v(b_n)\ge\nu_n\ \forall n\}$ |
| $\operatorname{im}\widehat\iota$ | 上者中再要求 $v(b_n)-\nu_n\to\infty$ |
| $\widehat q$ 的纤维 | $\rho(c)+\ker\widehat q$（非空闭陪集） |
| $E$ | $\Gamma/\Gamma'$，$\Gamma=\{\nu_n+v(a_n)\to\infty\}$（即沿每个有界 $\nu$ 子列 $v(a_n)\to\infty$），$\Gamma'=\{v(a_n)\to\infty\}$ |
| $Q_{\mathrm{tors}}=\operatorname{im}j$，$\ker j=0$ | $\{[b]:v(b_n)-\nu_n\to\infty\}=j(C)\cong C$；$t^r[b]=0\iff v(b_n)\ge\nu_n-r\ \forall n\wedge v(b_n)-\nu_n\to\infty$ |
| $Q/t^mQ,\ \widehat C/t^m\widehat C$ | 均 $\cong C/t^mC=\bigoplus_n(S/t^{\min(\nu_n,m)})\bar e_n$；$\bar p_m$ = 该认同 |
| $\bigcap t^mQ$ | $=E$ |
| $\widehat Q,\eta_Q$ | $\widehat Q\cong\widehat C$，$\Phi\eta_Q=p$；$\eta_Q$ 满，$\ker=E$ |
| $\widehat E,\eta_E$ | $\widehat E\cong E$（完备、分离）；$t^mE=\{v(a_n)\ge m\ \text{eventual}\}$，$\bigcap t^mE=0$ |
| $\widehat p$ | $=\eta_{\widehat C}\circ\Phi$，在认同下为 $\operatorname{id}_{\widehat C}$（同构）；$\widehat{\text{incl}}=0$ |

**各充要条件（均 $\iff(\nu_n)$ 有界）：** 完成列短正合；$\operatorname{im}\widehat\iota$ 闭；$E=0$；$p$ 有 $S$-线性右逆；$Q$ 分离；$E$ 的自身拓扑与子空间拓扑相同。

**无条件成立的结论：** $\widehat\iota$ 单、$\widehat q$ 满、$p$ 满；$\operatorname{im}\widehat\iota$ 稠密于 $\ker\widehat q$；$j$ 单且 $\operatorname{im}j=Q_{\mathrm{tors}}$；$E$ 无挠且 $E\cap Q_{\mathrm{tors}}=0$；$\bar p_m$ 对每 $m$ 为同构；$E$ 自身 $t$-进拓扑分离且完备，而从 $Q$ 继承的拓扑是平凡的。