下面在任意域 $k$ 与任意非负整数列 $(\nu_n)_{n\ge 1}$ 下完成全部三个目标并给出严格证明。

---

## 预备记号与关于主理想完成的基本引理

### 1. 赋值与 $S$ 模结构
由于 $k$ 为域，$S=k[[t]]$ 是离散赋值整环。对 $s=\sum_{d=0}^{\infty} c_d t^d\in S$，定义其 $t$ 进赋值 $v(s)\in \mathbb{Z}_{\ge 0}\cup\{\infty\}$：
$$
v(0)=\infty,\qquad v(s)=\min\{d\ge 0 : c_d\neq 0\}\quad (s\neq 0).
$$
对任意 $s_1,s_2\in S$ 与 $m\ge 0$，恒有：
- $v(s_1+s_2)\ge \min(v(s_1),v(s_2))$，$v(s_1 s_2)=v(s_1)+v(s_2)$；
- $s\in t^m S \iff v(s)\ge m$；
- 任意非零 $s\in S\setminus\{0\}$ 可唯一写为 $s=u t^{v(s)}$，其中 $u\in S^\times$（常数项非零的幂级数在 $k[[t]]$ 中可逆）。

对任意 $R$ 模 $M$ 与 $m\ge 1$，自然包含 $R=k[t]\hookrightarrow k[[t]]=S$ 诱导环同构 $R/t^m R\xrightarrow{\sim} S/t^m S$，从而 $M/t^m M$ 带有唯一的 $S/t^m S$ 模（进而 $S$ 模）结构：若 $s=\sum_{d=0}^{\infty} c_d t^d\in S$，则 $s\cdot(x+t^m M)=(\sum_{d=0}^{m-1} c_d t^d)x+t^m M$。若 $M$ 本身已是 $S$ 模，由于 $s-\sum_{d=0}^{m-1} c_d t^d\in t^m S$，上述作用与 $M$ 原有的 $S$ 作用在 $M/t^m M$ 上完全一致；由此，对任意 $S$ 模 $N$，典范映射 $\eta_N:N\to\widehat N$ 是 $S$ 线性的，且任意 $S$ 线性映射 $f:N_1\to N_2$ 诱导的完成映射 $\widehat f:\widehat N_1\to\widehat N_2$ 也是 $S$ 线性的。

### 2. 主理想 $(t)$ 完成的一般性质

**引理 0.** 设 $M$ 为任意 $R$ 模，对每个 $m\ge 1$ 记第 $m$ 层投影为 $\pi_m^M:\widehat M\to M/t^m M$。则：
1. $\pi_m^M$ 满射且 $\ker\pi_m^M = t^m\widehat M$，从而 $\pi_m^M$ 诱导 $S$ 模同构
   $$
   \overline{\pi}_m^M:\widehat M/t^m\widehat M \xrightarrow{\ \sim\ } M/t^m M.
   $$
2. $\bigcap_{m\ge 1} t^m\widehat M = \bigcap_{m\ge 1}\ker\pi_m^M = 0$，即 $\widehat M$ 的 $t$ 进拓扑总是分离的，且与 $\widehat M=\varprojlim_{m\ge 1} M/t^m M$ 的逆极限拓扑（以 $\{\ker\pi_m^M\}_{m\ge 1}$ 为零点邻域基）完全相同。
3. 典范映射 $\eta_{\widehat M}:\widehat M\to\widehat{\widehat M}$ 是 $S$ 模同构，其逆为 $\Pi_M:=\varprojlim_{m\ge 1}\overline{\pi}_m^M:\widehat{\widehat M}\xrightarrow{\sim}\widehat M$。

**证明.**
1. 对任意 $z+t^m M\in M/t^m M$，$\pi_m^M(\eta_M(z))=z+t^m M$，故 $\pi_m^M$ 满射。显然 $t^m\widehat M\subseteq\ker\pi_m^M$。反之，设 $x=(x_d+t^d M)_{d\ge 1}\in\ker\pi_m^M$（其中 $x_d\in M$）。由 $\pi_m^M(x)=0$ 知 $x_m\in t^m M$，可写 $x_m=t^m v_0$（$v_0\in M$）。对每个 $k\ge 0$，相容性 $x_{m+k+1}\equiv x_{m+k}\pmod{t^{m+k} M}$ 给出 $w_k\in M$ 使得
   $$
   x_{m+k+1}-x_{m+k}=t^{m+k} w_k.
   $$
   归纳定义 $y_1:=v_0+w_0$ 及 $y_{k+1}:=y_k+t^k w_k$（$k\ge 1$）。对一切 $k\ge 1$ 有 $y_{k+1}-y_k=t^k w_k\in t^k M$，故 $y:=(y_d+t^d M)_{d\ge 1}\in\widehat M$。对 $d\ge 1$ 归纳可得 $t^m y_d=x_{m+d}$：$d=1$ 时 $t^m y_1=t^m v_0+t^m w_0=x_m+(x_{m+1}-x_m)=x_{m+1}$；若 $t^m y_d=x_{m+d}$，则 $t^m y_{d+1}=t^m y_d+t^{m+d} w_d=x_{m+d}+(x_{m+d+1}-x_{m+d})=x_{m+d+1}$。因此对一切 $d\ge 1$，
   $$
   \pi_d^M(t^m y)=t^m y_d+t^d M=x_{m+d}+t^d M=x_d+t^d M=\pi_d^M(x)
   $$
   （因 $m+d>d$ 且 $x$ 相容），故 $x=t^m y\in t^m\widehat M$。因此 $\ker\pi_m^M=t^m\widehat M$，且由 $\pi_m^M$ 的 $S$ 线性性得同构 $\overline{\pi}_m^M$。
2. 直接由 (1) 及 $\bigcap_{m\ge 1}\ker\pi_m^M=0$ 得到。
3. 同构族 $(\overline{\pi}_m^M)_{m\ge 1}$ 与两边的自然约化过渡映射相容，故取逆极限得 $S$ 模同构 $\Pi_M=\varprojlim_{m\ge 1}\overline{\pi}_m^M:\widehat{\widehat M}\xrightarrow{\sim}\widehat M$。对任意 $x\in\widehat M$，$\Pi_M(\eta_{\widehat M}(x))=(\overline{\pi}_m^M(x+t^m\widehat M))_{m\ge 1}=(\pi_m^M(x))_{m\ge 1}=x$，故 $\eta_{\widehat M}=\Pi_M^{-1}$ 是 $S$ 模同构。$\square$

另外，对任意带 $t$ 进拓扑的 $R$ 模 $N$ 及子模 $L\subseteq N$，元素 $x\in N$ 属于 $L$ 的闭包 $\overline L$ 当且仅当对任意 $m\ge 1$ 邻域 $x+t^m N$ 与 $L$ 相交，即 $x\in L+t^m N$，因此总有
$$
\overline L=\bigcap_{m\ge 1}(L+t^m N).
$$

---

## 目标 1：$\widehat A,\widehat B,\widehat C$ 的坐标模型、诱导映射、正合性、闭包与纤维

### 1.1 $\widehat A,\widehat B,\widehat C$ 的坐标模型及与相容商记录的同构

定义 $S$ 模 $\mathcal{L}\subseteq \prod_{n\ge 1} S$ 为 $t$ 进趋零序列空间：
$$
\mathcal{L}:=\left\{(s_n)_{n\ge 1}\in \prod_{n\ge 1} S \;\middle|\; \lim_{n\to\infty} v(s_n)=\infty\right\}
=\left\{(s_n)_{n\ge 1}\in \prod_{n\ge 1} S \;\middle|\; \forall m\ge 1,\ s_n\in t^m S\text{ 对几乎所有 }n\text{ 成立}\right\}.
$$
（“几乎所有”均指“除有限个外的所有”。）再定义 $S$ 模 $\mathcal{C}\subseteq \prod_{n\ge 1}(S/t^{\nu_n} S)$：
$$
\mathcal{C}:=\left\{(u_n)_{n\ge 1}\in \prod_{n\ge 1}(S/t^{\nu_n} S) \;\middle|\; \forall m\ge 1,\ u_n\in t^m(S/t^{\nu_n} S)\text{ 对几乎所有 }n\text{ 成立}\right\}.
$$
（注意：当 $\nu_n=0$ 时，$t^0=1$，$S/t^0 S=0$，$u_n=0\in t^m(S/t^0 S)=0$ 自动满足，所有公式统一适用于 $\nu_n=0$。）

下面给出等价的多项式刻画以方便后续使用：对每个 $n\ge 1$ 与 $u_n\in S/t^{\nu_n} S$，存在唯一多项式 $r_n=\sum_{d=0}^{\nu_n-1} c_{n,d} t^d\in R$（$\nu_n=0$ 时约定为空和 $r_n=0$）满足 $r_n+t^{\nu_n} S=u_n$。验证对任意 $m\ge 1$，
$$
u_n\in t^m(S/t^{\nu_n} S)\iff v(r_n)\ge m.
$$
事实上：若 $u_n=0$（包括 $\nu_n=0$），两边均成立（$v(0)=\infty\ge m$）；若 $u_n\neq 0$，则 $\nu_n\ge 1$ 且 $v(r_n)\le\deg r_n<\nu_n$，此时若 $m\ge\nu_n$ 则 $t^m(S/t^{\nu_n} S)=0$ 且 $v(r_n)<\nu_n\le m$，两边皆假；若 $m<\nu_n$ 则 $t^m(S/t^{\nu_n} S)=t^m S/t^{\nu_n} S$，故 $u_n\in t^m(S/t^{\nu_n} S)\iff r_n\in t^m S+t^{\nu_n} S=t^m S\iff v(r_n)\ge m$。因此
$$
(u_n)_{n\ge 1}\in\mathcal{C}\iff (r_n)_{n\ge 1}\in\mathcal{L}.
$$

#### （1）$\widehat B\cong\mathcal{L}$ 与 $\widehat A\cong\mathcal{L}$
对每个 $m\ge 1$，有自然认同
$$
B/t^m B=\bigoplus_{n\ge 1}(R/t^m R)\,e_n \cong \bigoplus_{n\ge 1}(S/t^m S)\,e_n.
$$
构造映射 $\Phi_B:\mathcal{L}\to \widehat B=\varprojlim_{m\ge 1} B/t^m B$：对 $s=(s_n)_{n\ge 1}\in\mathcal{L}$ 与每个 $m\ge 1$，因 $s_n\in t^m S$ 对几乎所有 $n$ 成立，故
$$
x^{(m)}:=\sum_{n\ge 1}(s_n\bmod t^m S)\,e_n\in \bigoplus_{n\ge 1}(S/t^m S)\,e_n\cong B/t^m B
$$
为有限和；且显然 $x^{(m+1)}$ 约化模 $t^m$ 恰为 $x^{(m)}$，故 $\Phi_B(s):=(x^{(m)})_{m\ge 1}\in\widehat B$ 良定义，且按层检验立得其为 $S$ 线性映射。

构造逆映射 $\Psi_B:\widehat B\to\mathcal{L}$：任取相容族 $x=(x^{(m)})_{m\ge 1}\in\widehat B$，写 $x^{(m)}=\sum_{n\ge 1} x_n^{(m)} e_n$（$x_n^{(m)}\in S/t^m S$，对固定 $m$ 仅有限个 $n$ 非零）。对每个固定 $n\ge 1$，$(x_n^{(m)})_{m\ge 1}\in\varprojlim_{m\ge 1} S/t^m S\cong S$ 唯一确定幂级数 $s_n\in S$，使 $s_n\bmod t^m S=x_n^{(m)}$ 对一切 $m\ge 1$ 成立。对任意 $m\ge 1$，因 $x^{(m)}$ 有限支撑，故对几乎所有 $n$ 有 $x_n^{(m)}=0$，即 $s_n\in t^m S$，所以 $s=(s_n)_{n\ge 1}\in\mathcal{L}$。直接检验知 $\Phi_B\circ\Psi_B=\mathrm{id}_{\widehat B}$ 且 $\Psi_B\circ\Phi_B=\mathrm{id}_{\mathcal{L}}$，故 $\Phi_B:\mathcal{L}\xrightarrow{\sim}\widehat B$ 是 $S$ 模同构。

完全相同地，将 $e_n$ 换为 $f_n$，得到 $S$ 模同构 $\Phi_A:\mathcal{L}\xrightarrow{\sim}\widehat A$（逆为 $\Psi_A$）：
$$
\Phi_A\bigl((a_n)_{n\ge 1}\bigr)=\left(\sum_{n\ge 1}(a_n\bmod t^m S)\,f_n\right)_{m\ge 1}\in\varprojlim_{m\ge 1} A/t^m A=\widehat A.
$$
在这些坐标模型下，典范映射 $\eta_A:A\to\widehat A$、$\eta_B:B\to\widehat B$ 分别是自然包含 $\bigoplus_{n\ge 1} R\hookrightarrow\mathcal{L}$。

#### （2）$\widehat C\cong\mathcal{C}$
记 $\bar e_n:=q(e_n)\in C$。由定义 $C=B/\iota(A)=\bigoplus_{n\ge 1}(R/t^{\nu_n} R)\,\bar e_n$。对任意 $m\ge 1$，因
$$
(R/t^{\nu_n} R)/t^m(R/t^{\nu_n} R)\cong R/(t^{\nu_n} R+t^m R)=R/t^{\min(m,\nu_n)} R\cong S/t^{\min(m,\nu_n)} S,
$$
有自然认同
$$
C/t^m C\cong \bigoplus_{n\ge 1}\bigl(S/t^{\min(m,\nu_n)} S\bigr)\,\bar e_n,
$$
其过渡映射在每个坐标 $n$ 上是自然约化 $S/t^{\min(m+1,\nu_n)} S\to S/t^{\min(m,\nu_n)} S$。对每个 $n,m\ge 1$，记自然投射为
$$
\pi_{n,m}:S/t^{\nu_n} S\longrightarrow S/t^{\min(m,\nu_n)} S,
$$
其核恰为 $t^{\min(m,\nu_n)} S/t^{\nu_n} S=t^m(S/t^{\nu_n} S)$（检验：$m<\nu_n$ 时两端均为 $t^m S/t^{\nu_n} S$；$m\ge\nu_n$ 时两端均为 $0$）。

构造 $\Phi_C:\mathcal{C}\to\widehat C=\varprojlim_{m\ge 1} C/t^m C$：对 $u=(u_n)_{n\ge 1}\in\mathcal{C}$ 与每个 $m\ge 1$，由 $u_n\in t^m(S/t^{\nu_n} S)=\ker\pi_{n,m}$ 对几乎所有 $n$ 成立，知
$$
y^{(m)}:=\sum_{n\ge 1}\pi_{n,m}(u_n)\,\bar e_n\in \bigoplus_{n\ge 1}\bigl(S/t^{\min(m,\nu_n)} S\bigr)\,\bar e_n\cong C/t^m C
$$
是有限和，且对 $m$ 相容；故 $\Phi_C(u):=(y^{(m)})_{m\ge 1}\in\widehat C$ 良定义且 $S$ 线性。

构造逆映射 $\Psi_C:\widehat C\to\mathcal{C}$：任取 $y=(y^{(m)})_{m\ge 1}\in\widehat C$，写 $y^{(m)}=\sum_{n\ge 1} y_n^{(m)}\bar e_n$（$y_n^{(m)}\in S/t^{\min(m,\nu_n)} S$）。对每个固定 $n\ge 1$：
- 若 $\nu_n=0$，置 $u_n:=0\in S/t^0 S=0$；
- 若 $\nu_n\ge 1$，对一切 $m\ge\nu_n$ 有 $\min(m,\nu_n)=\nu_n$，过渡映射恒为恒等映射，故 $y_n^{(m)}$ 与 $m\ge\nu_n$ 无关，置 $u_n:=y_n^{(\nu_n)}\in S/t^{\nu_n} S$。

由相容性，对任意 $n,m\ge 1$ 均有 $\pi_{n,m}(u_n)=y_n^{(m)}$（$m\ge\nu_n$ 时 $y_n^{(m)}=u_n$；$m<\nu_n$ 时由第 $\nu_n$ 层约化到第 $m$ 层即得）。对固定 $m\ge 1$，$y^{(m)}$ 有限支撑，故几乎所有 $n$ 满足 $\pi_{n,m}(u_n)=y_n^{(m)}=0$，即 $u_n\in\ker\pi_{n,m}=t^m(S/t^{\nu_n} S)$，从而 $u=(u_n)_{n\ge 1}\in\mathcal{C}$。直接检验得 $\Phi_C\circ\Psi_C=\mathrm{id}_{\widehat C}$、$\Psi_C\circ\Phi_C=\mathrm{id}_{\mathcal{C}}$，故 $\Phi_C:\mathcal{C}\xrightarrow{\sim}\widehat C$ 是 $S$ 模同构。

在此坐标模型下，$\eta_C:C\to\widehat C$ 将 $\sum_{n\ge 1} u_n\bar e_n\in\bigoplus_{n\ge 1}(R/t^{\nu_n} R)\,\bar e_n$ 映为有限支撑序列 $(u_n)_{n\ge 1}\in\mathcal{C}$（经 $R/t^{\nu_n} R\xrightarrow{\sim} S/t^{\nu_n} S$ 认同）。

---

### 1.2 诱导映射 $\widehat\iota$ 与 $\widehat q$ 的坐标表达

在第 $m$ 层上，$\iota_m:A/t^m A\to B/t^m B$ 将 $a_n^{(m)} f_n$ 映为 $(t^{\nu_n} a_n^{(m)}\bmod t^m)e_n$，$q_m:B/t^m B\to C/t^m C$ 将 $b_n^{(m)} e_n$ 映为 $(b_n^{(m)}\bmod t^{\min(m,\nu_n)})\bar e_n$。因此经 $\Phi_A,\Phi_B,\Phi_C$ 认同后，诱导映射 $\widehat\iota:\mathcal{L}\to\mathcal{L}$ 与 $\widehat q:\mathcal{L}\to\mathcal{C}$ 分别为：
$$
\widehat\iota\bigl((a_n)_{n\ge 1}\bigr)=\bigl(t^{\nu_n} a_n\bigr)_{n\ge 1},\qquad
\widehat q\bigl((b_n)_{n\ge 1}\bigr)=\bigl(b_n\bmod t^{\nu_n} S\bigr)_{n\ge 1}.
$$
验证良定义：若 $(a_n)\in\mathcal{L}$，则 $v(t^{\nu_n} a_n)=\nu_n+v(a_n)\ge v(a_n)\to\infty$，故 $(t^{\nu_n} a_n)\in\mathcal{L}$；若 $(b_n)\in\mathcal{L}$，则对任意 $m\ge 1$ 几乎所有 $n$ 有 $b_n\in t^m S$，进而 $b_n\bmod t^{\nu_n} S\in t^m(S/t^{\nu_n} S)$，故 $(b_n\bmod t^{\nu_n} S)\in\mathcal{C}$；按层比较立即验证 $\Phi_B\circ\widehat\iota_{\text{坐标}}=\widehat\iota\circ\Phi_A$ 与 $\Phi_C\circ\widehat q_{\text{坐标}}=\widehat q\circ\Phi_B$。

---

### 1.3 完成列各处的正合性、$\operatorname{im}\widehat\iota$ 的闭包、$\widehat q$ 的纤维及短正合充要条件

考虑完成列
$$
0\longrightarrow \widehat A\xrightarrow{\ \widehat\iota\ }\widehat B\xrightarrow{\ \widehat q\ }\widehat C\longrightarrow 0.
$$

#### （1）在 $\widehat A$ 处的正合性（$\widehat\iota$ 的单射性）
**结论：对任意指数列 $(\nu_n)_{n\ge 1}$，完成列在 $\widehat A$ 处恒正合（$\widehat\iota$ 恒单射）。**

**证明.** 若 $\widehat\iota((a_n)_{n\ge 1})=(t^{\nu_n} a_n)_{n\ge 1}=0$，因 $S$ 是整环且 $t^{\nu_n}\neq 0$，必有 $a_n=0$（$\forall n\ge 1$）。$\square$

#### （2）在 $\widehat C$ 处的正合性（$\widehat q$ 的满射性）
**结论：对任意指数列 $(\nu_n)_{n\ge 1}$，完成列在 $\widehat C$ 处恒正合（$\widehat q$ 恒满射）。**

**证明.** 定义 $k$ 线性截面 $\sigma:\mathcal{C}\to\mathcal{L}$：对 $u=(u_n)_{n\ge 1}\in\mathcal{C}$，取每分量唯一的次数 $<\nu_n$ 多项式代表 $r_n\in R$（$\nu_n=0$ 时 $r_n=0$），置 $\sigma(u):=(r_n)_{n\ge 1}$。前已证明 $u\in\mathcal{C}\iff (r_n)_{n\ge 1}\in\mathcal{L}$，故 $\sigma(u)\in\mathcal{L}$ 且 $\widehat q(\sigma(u))=(r_n\bmod t^{\nu_n} S)_{n\ge 1}=u$。从而 $\widehat q$ 恒满射。$\square$

#### （3）$\ker\widehat q$、$\operatorname{im}\widehat\iota$ 与 $\widehat B$ 处的正合性
先定义 $S$ 模
$$
\mathcal{D}:=\left\{(c_n)_{n\ge 1}\in\prod_{n\ge 1} S \;\middle|\; \lim_{n\to\infty}\bigl(\nu_n+v(c_n)\bigr)=\infty\right\}.
$$
显然 $\mathcal{L}\subseteq\mathcal{D}\subseteq\prod_{n\ge 1} S$（因 $\nu_n\ge 0$）。在坐标模型 $\widehat B\cong\mathcal{L}$ 下：
- $b=(b_n)_{n\ge 1}\in\ker\widehat q \iff b\in\mathcal{L}$ 且 $\forall n\ge 1,\, t^{\nu_n}\mid b_n$。令 $b_n=t^{\nu_n} c_n$（$c_n\in S$ 唯一），则 $v(b_n)=\nu_n+v(c_n)$，于是
  $$
  \Psi_B(\ker\widehat q)=\bigl\{(t^{\nu_n} c_n)_{n\ge 1}\mid (c_n)_{n\ge 1}\in\mathcal{D}\bigr\};
  $$
- 另一方面，
  $$
  \Psi_B(\operatorname{im}\widehat\iota)=\bigl\{(t^{\nu_n} a_n)_{n\ge 1}\mid (a_n)_{n\ge 1}\in\mathcal{L}\bigr\}.
  $$

**结论：完成列在 $\widehat B$ 处正合（进而整个完成列短正合）的充要条件是 $(\nu_n)_{n\ge 1}$ 有界（即 $\sup_{n\ge 1}\nu_n<\infty$）。**

**证明.** 已知 $\operatorname{im}\widehat\iota\subseteq\ker\widehat q$ 且两处端项恒正合，故完成列短正合 $\iff$ 在 $\widehat B$ 处正合 $\iff\ker\widehat q=\operatorname{im}\widehat\iota\iff\mathcal{D}=\mathcal{L}$（因映射 $(c_n)\mapsto(t^{\nu_n} c_n)$ 单射）。
- **充分性：** 若存在 $M\ge 0$ 使 $\nu_n\le M$（$\forall n\ge 1$），则对任意 $(c_n)\in\mathcal{D}$，有 $v(c_n)\ge (\nu_n+v(c_n))-M\to\infty$，故 $(c_n)\in\mathcal{L}$。从而 $\mathcal{D}=\mathcal{L}$。
- **必要性：** 若 $(\nu_n)_{n\ge 1}$ 无界，取严格递增下标列 $n_1<n_2<\cdots$ 使 $\nu_{n_k}\ge k$（$\forall k\ge 1$）。定义 $c_n=1$（若 $n=n_k$），$c_n=0$（否则）。当 $n=n_k$ 时 $\nu_n+v(c_n)=\nu_{n_k}\ge k\to\infty$，其余 $n$ 有 $\nu_n+v(c_n)=\infty$，故 $(c_n)\in\mathcal{D}$；但 $v(c_{n_k})=0$ 对无穷多个 $k$ 成立，故 $(c_n)\notin\mathcal{L}$。于是 $(t^{\nu_n} c_n)_{n\ge 1}\in\Psi_B(\ker\widehat q)\setminus\Psi_B(\operatorname{im}\widehat\iota)$，完成列在 $\widehat B$ 处不正合。$\square$

#### （4）$\operatorname{im}\widehat\iota$ 在 $\widehat B$ 中的闭包
**结论：对任意指数列 $(\nu_n)_{n\ge 1}$，$\operatorname{im}\widehat\iota$ 在 $\widehat B$ 中的 $t$ 进闭包（亦即逆极限拓扑闭包，由引理 0 二者一致）恒为**
$$
\overline{\operatorname{im}\widehat\iota}=\ker\widehat q.
$$

**证明.**
- **$\overline{\operatorname{im}\widehat\iota}\subseteq\ker\widehat q$：** 对任意 $b\in\overline{\operatorname{im}\widehat\iota}=\bigcap_{m\ge 1}(\operatorname{im}\widehat\iota+t^m\widehat B)$ 与每个 $m\ge 1$，有 $\widehat q(b)\in \widehat q(\operatorname{im}\widehat\iota)+t^m\widehat q(\widehat B)\subseteq t^m\widehat C$。由引理 0 知 $\bigcap_{m\ge 1} t^m\widehat C=0$，故 $\widehat q(b)=0$，即 $b\in\ker\widehat q$。
- **$\ker\widehat q\subseteq\overline{\operatorname{im}\widehat\iota}$：** 在坐标模型 $\mathcal{L}\cong\widehat B$ 中，由引理 0（或直接验证）有
  $$
  t^m\mathcal{L}=\{(s_n)_{n\ge 1}\in\mathcal{L}\mid \forall n\ge 1,\ v(s_n)\ge m\}.
  $$
  任取 $b=(t^{\nu_n} c_n)_{n\ge 1}\in\Psi_B(\ker\widehat q)$（其中 $(c_n)\in\mathcal{D}$）及任意 $m\ge 1$。因 $v(b_n)=\nu_n+v(c_n)\to\infty$，存在 $N\ge 1$ 使对一切 $n>N$ 有 $v(b_n)\ge m$。分解 $b=b'+b''$，其中
  $$
  b'_n=\begin{cases} t^{\nu_n} c_n, & n\le N,\\ 0, & n>N,\end{cases}\qquad
  b''_n=\begin{cases} 0, & n\le N,\\ b_n, & n>N.\end{cases}
  $$
  令 $a_n=c_n$（$n\le N$），$a_n=0$（$n>N$），则 $a=(a_n)\in\mathcal{L}$（有限支撑）且 $b'=\widehat\iota(a)\in\Psi_B(\operatorname{im}\widehat\iota)$；同时 $b''\in\mathcal{L}$ 且对所有 $n\ge 1$ 有 $v(b''_n)\ge m$，故 $b''\in t^m\mathcal{L}$。因此 $b\in\Psi_B(\operatorname{im}\widehat\iota)+t^m\mathcal{L}$。由 $m\ge 1$ 的任意性即得 $b\in\Psi_B(\overline{\operatorname{im}\widehat\iota})$。$\square$

#### （5）$\widehat q$ 的每个纤维
**结论：对每个 $u=(u_n)_{n\ge 1}\in\mathcal{C}$（对应 $\Phi_C(u)\in\widehat C$），纤维 $\widehat q^{-1}(\Phi_C(u))$ 非空，是 $\ker\widehat q=\overline{\operatorname{im}\widehat\iota}$ 的闭陪集。在坐标模型 $\widehat B\cong\mathcal{L}$ 下，记 $\sigma(u)=(r_n)_{n\ge 1}\in\mathcal{L}$ 为 $u$ 的典范多项式提升（$\deg r_n<\nu_n$，$\nu_n=0$ 时 $r_n=0$），则**
$$
\begin{aligned}
\Psi_B\bigl(\widehat q^{-1}(\Phi_C(u))\bigr)
&=\sigma(u)+\Psi_B(\ker\widehat q) \\
&=\left\{(b_n)_{n\ge 1}\in\mathcal{L}\;\middle|\; \forall n\ge 1,\ b_n\equiv u_n\pmod{t^{\nu_n} S}\right\} \\
&=\left\{(r_n+t^{\nu_n} c_n)_{n\ge 1}\;\middle|\; (c_n)_{n\ge 1}\in\mathcal{D}\right\}.
\end{aligned}
$$
**证明.** 因 $\widehat q(\sigma(u))=u$ 且 $\widehat q$ 是 $S$ 模同态，纤维恰为 $\sigma(u)+\ker\widehat q$，第二、三个等式由 $\ker\widehat q$ 的坐标刻画直接得出。$\square$

---

## 目标 2：$E$ 的坐标模型、$j$ 的核与像、$Q$ 的 $t$ 幂挠、$E$ 的挠性、$p$ 的满射性与右逆

先验证 $p$ 与 $j$ 良定义：因 $\widehat q\circ\widehat\iota=\widehat{q\circ\iota}=0$，有 $\operatorname{im}\widehat\iota\subseteq\ker\widehat q$，故 $p:Q=\widehat B/\operatorname{im}\widehat\iota\to\widehat C$ 良定义且 $S$ 线性；对 $a\in A$，有 $\eta_B(\iota(a))=\widehat\iota(\eta_A(a))\in\operatorname{im}\widehat\iota$，故 $j:C=B/\iota(A)\to Q$ 良定义且 $R$ 线性（事实上 $C$ 作为 $t$ 幂挠 $R$ 模天然为 $S$ 模，且 $j$ 为 $S$ 线性），并且满足
$$
p\circ j=\eta_C.
$$
（检验：对 $b\in B$，$(p\circ j)(q(b))=p(\eta_B(b)+\operatorname{im}\widehat\iota)=\widehat q(\eta_B(b))=\eta_C(q(b))$。）

### 2.1 $E=\ker p$ 的明确坐标模型
由定义 $E=\ker p=\ker\widehat q/\operatorname{im}\widehat\iota$。在坐标模型 $\Phi_B:\mathcal{L}\xrightarrow{\sim}\widehat B$ 下，映射
$$
\widetilde\theta:\mathcal{D}\longrightarrow \ker\widehat q,\qquad (c_n)_{n\ge 1}\longmapsto \Phi_B\bigl((t^{\nu_n} c_n)_{n\ge 1}\bigr)
$$
是 $S$ 模同构（双射性已由 1.3(3) 给出），且 $\widetilde\theta(\mathcal{L})=\operatorname{im}\widehat\iota$。因此 $\widetilde\theta$ 诱导 $S$ 模同构
$$
\theta:\mathcal{D}/\mathcal{L}\xrightarrow{\ \sim\ } E,\qquad (c_n)_{n\ge 1}+\mathcal{L}\longmapsto \Phi_B\bigl((t^{\nu_n} c_n)_{n\ge 1}\bigr)+\operatorname{im}\widehat\iota,
$$
其中
$$
\mathcal{D}=\left\{(c_n)_{n\ge 1}\in\prod_{n\ge 1} S \;\middle|\; \lim_{n\to\infty}\bigl(\nu_n+v(c_n)\bigr)=\infty\right\},\qquad
\mathcal{L}=\left\{(a_n)_{n\ge 1}\in\prod_{n\ge 1} S \;\middle|\; \lim_{n\to\infty} v(a_n)=\infty\right\}.
$$

### 2.2 $j$ 的核和像
**结论：**
1. **$\ker j=0$**（$j$ 对任意 $(\nu_n)_{n\ge 1}$ 恒单射）。
2. **$\operatorname{im} j=(\eta_B(B)+\operatorname{im}\widehat\iota)/\operatorname{im}\widehat\iota\cong C$**；它在 $Q$ 中等于由 $\{\eta_B(e_n)+\operatorname{im}\widehat\iota\}_{n\ge 1}$ 生成的 $R$ 子模（亦即 $S$ 子模）$\bigoplus_{n\ge 1}(R/t^{\nu_n} R)(\eta_B(e_n)+\operatorname{im}\widehat\iota)$。在坐标模型 $\widehat B\cong\mathcal{L}$ 下，元素 $\Phi_B((b_n)_{n\ge 1})+\operatorname{im}\widehat\iota\in Q$ 属于 $\operatorname{im} j$ 当且仅当存在 $N\ge 1$ 及 $(a_n)_{n>N}$（$a_n\in S$ 且 $\lim_{n\to\infty} v(a_n)=\infty$）使得对一切 $n>N$ 有 $b_n=t^{\nu_n} a_n$。

**证明.**
1. 由 $p\circ j=\eta_C$，只需证明 $\eta_C:C\to\widehat C$ 单射。对 $c=\sum_{n=1}^N u_n\bar e_n\in C$（$u_n\in R/t^{\nu_n} R$），在坐标模型 $\widehat C\cong\mathcal{C}$ 下 $\Psi_C(\eta_C(c))=(u_n)_{n\ge 1}$（超过 $N$ 的坐标为 $0$），故 $\eta_C(c)=0\implies u_n=0\ (\forall n)\implies c=0$。由此 $\ker j\subseteq\ker(p\circ j)=\ker\eta_C=0$。
2. $\operatorname{im} j=(\eta_B(B)+\operatorname{im}\widehat\iota)/\operatorname{im}\widehat\iota$ 由定义立得；结合 $\ker j=0$ 知 $j:C\xrightarrow{\sim}\operatorname{im} j$ 是同构，故 $\operatorname{im} j=\bigoplus_{n\ge 1}(R/t^{\nu_n} R)(\eta_B(e_n)+\operatorname{im}\widehat\iota)$。对坐标刻画：
   - 若 $b=\eta_B(b')+\widehat\iota(a)$（$b'\in B$ 支撑于 $\{1,\dots,N\}$，$a=(a_n)\in\mathcal{L}$），则对 $n>N$ 有 $b_n=t^{\nu_n} a_n$ 且 $\lim_{n\to\infty} v(a_n)=\infty$。
   - 反之，若存在 $N\ge 1$ 及 $(a_n)_{n>N}$ 满足 $b_n=t^{\nu_n} a_n$（$n>N$）且 $\lim_{n\to\infty} v(a_n)=\infty$，则对每个 $1\le n\le N$ 在 $S$ 中作带余分解 $b_n=r_n+t^{\nu_n} a_n$（$r_n\in R$ 次数 $<\nu_n$，$a_n\in S$）。令 $a:=(a_n)_{n\ge 1}\in\mathcal{L}$ 与 $b':=\sum_{n=1}^N r_n e_n\in B$，则 $b=\Psi_B(\eta_B(b'))+\widehat\iota(a)$，从而 $\Phi_B(b)+\operatorname{im}\widehat\iota=j(q(b'))\in\operatorname{im} j$。$\square$

### 2.3 $Q$ 中所有被某个 $t^r$（$r\ge 1$）杀死的元素
记 $Q[t^r]:=\{x\in Q : t^r x=0\}$ 及 $Q[t^\infty]:=\bigcup_{r\ge 1} Q[t^r]$。

**结论：对任意指数列 $(\nu_n)_{n\ge 1}$，**
$$
Q[t^\infty]=\operatorname{im} j\cong C,
$$
且对每个固定的 $r\ge 1$，
$$
Q[t^r]=j\bigl(C[t^r]\bigr)=j\!\left(\bigoplus_{n\ge 1}\bigl(t^{\max(\nu_n-r,0)} R / t^{\nu_n} R\bigr)\,\bar e_n\right).
$$
（此外，因 $S$ 中任意非零元皆形如 $u t^r$（$u\in S^\times,r\ge 0$），$Q[t^\infty]=\operatorname{im} j$ 亦即 $Q$ 的全体 $S$ 挠子模。）

**证明.**
- **$\operatorname{im} j\subseteq Q[t^\infty]$：** 任取 $c=\sum_{n=1}^N u_n\bar e_n\in C$，取 $r:=\max(\{1\}\cup\{\nu_1,\dots,\nu_N\})\ge 1$，则 $t^r c=0$，于是 $t^r j(c)=j(t^r c)=0$，即 $j(c)\in Q[t^r]\subseteq Q[t^\infty]$。
- **$Q[t^\infty]\subseteq\operatorname{im} j$：** 设 $x=\Phi_B(b)+\operatorname{im}\widehat\iota\in Q[t^r]$（$r\ge 1$，$b=(b_n)\in\mathcal{L}$）。由 $t^r x=0$ 知存在 $a=(a_n)_{n\ge 1}\in\mathcal{L}$ 使得 $t^r b=\widehat\iota(a)$，即对一切 $n\ge 1$，
  $$
  t^r b_n = t^{\nu_n} a_n \quad\text{在 }S\text{ 中成立}.
  $$
  因 $a\in\mathcal{L}$，存在 $N\ge 1$ 使对一切 $n>N$ 有 $v(a_n)\ge r$，从而可写 $a_n=t^r\tilde a_n$（$\tilde a_n\in S$），且 $v(\tilde a_n)=v(a_n)-r\to\infty$（$n\to\infty$）。将 $a_n=t^r\tilde a_n$ 代入并在整环 $S$ 中消去 $t^r$，得
  $$
  b_n=t^{\nu_n}\tilde a_n \qquad (\forall n>N).
  $$
  由 2.2 的坐标刻画立即得出 $x\in\operatorname{im} j$！
- **对固定 $r\ge 1$：** 因 $Q[t^r]\subseteq Q[t^\infty]=\operatorname{im} j$ 且 $j:C\xrightarrow{\sim}\operatorname{im} j$ 是 $R$ 模同构，故 $Q[t^r]=j(C[t^r])$。在 $R/t^{\nu_n} R$ 中，$t^r u_n\equiv 0\pmod{t^{\nu_n} R}\iff u_n\in t^{\max(\nu_n-r,0)} R/t^{\nu_n} R$，从而得到 $Q[t^r]$ 的显式表达。$\square$

### 2.4 $E$ 的 $S$ 模挠性
**结论：对任意指数列 $(\nu_n)_{n\ge 1}$，$E$ 恒为无挠 $S$ 模（即 $E$ 的 $S$ 挠子模恒为 $0$：对任意 $s\in S\setminus\{0\}$ 与 $e\in E$，$s e=0\implies e=0$）。**
（特别地，当 $(\nu_n)$ 有界时 $E=0$；当 $(\nu_n)$ 无界时 $E$ 是非零无挠 $S$ 模，从而不是挠模。）

**证明.** 经同构 $\theta:\mathcal{D}/\mathcal{L}\xrightarrow{\sim} E$，设 $s\in S\setminus\{0\}$ 及 $c=(c_n)_{n\ge 1}\in\mathcal{D}$ 满足 $s(c+\mathcal{L})=0$，即 $sc=(s c_n)_{n\ge 1}\in\mathcal{L}$。因 $s\neq 0$，有 $v(s)<\infty$ 且对一切 $n\ge 1$ 有 $v(s c_n)=v(s)+v(c_n)$。故
$$
\lim_{n\to\infty}\bigl(v(s)+v(c_n)\bigr)=\infty \implies \lim_{n\to\infty} v(c_n)=\infty \implies c\in\mathcal{L}\implies c+\mathcal{L}=0. \qquad\square
$$

### 2.5 $p$ 的满射性、$E=0$ 的充要条件、$p$ 存在 $S$ 线性右逆的充要条件

**结论：**
1. **$p:Q\to\widehat C$ 对任意指数列 $(\nu_n)_{n\ge 1}$ 恒满射。**
2. **$E=0$ 的充要条件是 $(\nu_n)_{n\ge 1}$ 有界（$\sup_{n\ge 1}\nu_n<\infty$）。**
3. **$p$ 存在 $S$ 线性右逆的充要条件也是 $(\nu_n)_{n\ge 1}$ 有界（$\sup_{n\ge 1}\nu_n<\infty$）**；此时 $E=0$ 且 $p$ 是 $S$ 模同构（右逆唯一且即 $p^{-1}$）。

**证明.**
1. 由定义 $\operatorname{im} p=\operatorname{im}\widehat q$，而 1.3(2) 已证 $\widehat q$ 恒满射，故 $p$ 恒满射。
2. $E=\ker\widehat q/\operatorname{im}\widehat\iota=0 \iff \ker\widehat q=\operatorname{im}\widehat\iota$，由 1.3(3) 此等价于 $(\nu_n)_{n\ge 1}$ 有界。
3. **充分性：** 若 $(\nu_n)_{n\ge 1}$ 有界，由 (1)(2) 知 $p$ 既是满射又满足 $\ker p=E=0$，故 $p$ 是 $S$ 模同构，存在 $S$ 线性右逆 $p^{-1}$。

   **必要性：** 设 $(\nu_n)_{n\ge 1}$ 无界，反设存在 $S$ 线性映射 $s:\widehat C\to Q$ 满足 $p\circ s=\mathrm{id}_{\widehat C}$。取严格递增下标列 $1\le n_1<n_2<\cdots$ 使 $\nu_{n_k}\ge k$（$\forall k\ge 1$）。定义 $u=(u_n)_{n\ge 1}\in\prod_{n\ge 1}(S/t^{\nu_n} S)$：
   $$
   u_n:=\begin{cases} t^{\nu_{n_k}-1}+t^{\nu_{n_k}} S, & \text{若 }n=n_k\ (k\ge 1),\\ 0, & \text{否则.}\end{cases}
   $$
   （因 $\nu_{n_k}\ge k\ge 1$，此定义有意义且 $u_{n_k}\neq 0$。）
   - 检验 $u\in\mathcal{C}$：对任意 $m\ge 1$ 及任意 $n>n_m$，若 $n\notin\{n_k\}$ 则 $u_n=0$；若 $n=n_k$ 则 $k\ge m+1$，故 $\nu_{n_k}-1\ge k-1\ge m$，从而 $u_{n_k}\in t^m(S/t^{\nu_{n_k}} S)$。于是 $u\in\mathcal{C}$，对应元素 $\tilde u:=\Phi_C(u)\in\widehat C$。
   - 检验 $t\tilde u=0$：对所有 $k\ge 1$，$t u_{n_k}=t^{\nu_{n_k}}+t^{\nu_{n_k}} S=0$，其余坐标为 $0$，故 $t\tilde u=0$。

   于是 $s(\tilde u)\in Q$ 满足 $t\cdot s(\tilde u)=s(t\tilde u)=0$，即 $s(\tilde u)\in Q[t]\subseteq Q[t^\infty]=\operatorname{im} j$（由 2.3）。两边作用 $p$，得
   $$
   \tilde u = p(s(\tilde u))\in p(\operatorname{im} j)=\operatorname{im}(p\circ j)=\operatorname{im}\eta_C.
   $$
   然而 $\operatorname{im}\eta_C$ 在 $\mathcal{C}$ 中的所有元素都仅有有限个非零坐标，而 $u$ 在所有 $n=n_k$（$k\ge 1$）处非零，矛盾！因此当 $(\nu_n)_{n\ge 1}$ 无界时，$p$ 不存在 $S$ 线性右逆（甚至不存在 $R$ 线性右逆）。$\square$

---

## 目标 3：$p_m$、$\bigcap_{m\ge 1} t^m Q$、$\widehat Q$ 与 $\widehat E$ 及完成映射、$E$ 上两种拓扑的比较

### 3.1 由 $p$ 诱导的 $p_m:Q/t^m Q\to\widehat C/t^m\widehat C$
**结论：对每个 $m\ge 1$ 及任意指数列 $(\nu_n)_{n\ge 1}$，由 $p$ 诱导的映射**
$$
p_m:Q/t^m Q\longrightarrow \widehat C/t^m\widehat C,\qquad x+t^m Q\longmapsto p(x)+t^m\widehat C
$$
**恒为 $S$ 模同构**（与引理 0 的同构 $\overline{\pi}_m^C:\widehat C/t^m\widehat C\xrightarrow{\sim} C/t^m C$ 复合，给出 $Q/t^m Q\xrightarrow{\sim} C/t^m C\cong\bigoplus_{n\ge 1}(S/t^{\min(m,\nu_n)} S)\,\bar e_n$）。

**证明.**
- **满射性：** 因 $p:Q\to\widehat C$ 满射，$p_m$ 显然满射。
- **单射性：** 先注意由 1.3(4) 有 $\ker\widehat q=\overline{\operatorname{im}\widehat\iota}=\bigcap_{d\ge 1}(\operatorname{im}\widehat\iota+t^d\widehat B)\subseteq \operatorname{im}\widehat\iota+t^m\widehat B$，两边商去 $\operatorname{im}\widehat\iota$ 即得
  $$
  E=\ker\widehat q/\operatorname{im}\widehat\iota \subseteq (\operatorname{im}\widehat\iota+t^m\widehat B)/\operatorname{im}\widehat\iota = t^m Q \qquad (\forall m\ge 1).
  $$
  今设 $x\in Q$ 满足 $p_m(x+t^m Q)=0$，即 $p(x)\in t^m\widehat C$。因 $p$ 满射，有 $t^m\widehat C=p(t^m Q)$，故存在 $y\in Q$ 使 $p(x)=p(t^m y)$，从而 $x-t^m y\in\ker p=E\subseteq t^m Q$。因此 $x\in t^m Q$，即 $x+t^m Q=0$。故 $p_m$ 单射，从而是 $S$ 模同构。$\square$

### 3.2 计算 $\bigcap_{m\ge 1} t^m Q$
**结论：对任意指数列 $(\nu_n)_{n\ge 1}$，**
$$
\bigcap_{m\ge 1} t^m Q = E.
$$
（从而 $Q$ 的 $t$ 进拓扑分离当且仅当 $E=0$，即 $(\nu_n)_{n\ge 1}$ 有界。）

**证明.** 由 3.1 知 $p_m:Q/t^m Q\xrightarrow{\sim}\widehat C/t^m\widehat C$ 是同构，故对每个 $m\ge 1$，
$$
x\in t^m Q \iff p_m(x+t^m Q)=0 \iff p(x)\in t^m\widehat C,
$$
即 $t^m Q=p^{-1}(t^m\widehat C)$。取交并利用引理 0（$\bigcap_{m\ge 1} t^m\widehat C=0$），得
$$
\bigcap_{m\ge 1} t^m Q = \bigcap_{m\ge 1} p^{-1}(t^m\widehat C)=p^{-1}\!\left(\bigcap_{m\ge 1} t^m\widehat C\right)=p^{-1}(0)=\ker p=E. \qquad\square
$$
（也可直接由 1.3(4) 得出：对 $b\in\widehat B$，$b+\operatorname{im}\widehat\iota\in\bigcap_{m\ge 1} t^m Q\iff b\in\bigcap_{m\ge 1}(\operatorname{im}\widehat\iota+t^m\widehat B)=\overline{\operatorname{im}\widehat\iota}=\ker\widehat q\iff b+\operatorname{im}\widehat\iota\in E$。）

### 3.3 $\widehat Q$、$\eta_Q$ 及 $p$ 诱导的完成映射 $\widehat p$
**结论：对任意指数列 $(\nu_n)_{n\ge 1}$，**
1. $p$ 诱导的完成映射 $\widehat p:\widehat Q\to\widehat{\widehat C}$ **恒为 $S$ 模同构**。
2. 结合引理 0 的同构 $\eta_{\widehat C}:\widehat C\xrightarrow{\sim}\widehat{\widehat C}$，得到典范 $S$ 模同构
   $$
   \psi:=\eta_{\widehat C}^{-1}\circ\widehat p:\widehat Q\xrightarrow{\ \sim\ }\widehat C\ (\cong\mathcal{C}).
   $$
3. 在同构 $\psi:\widehat Q\xrightarrow{\sim}\widehat C$ 下，典范映射 $\eta_Q:Q\to\widehat Q$ 与 $p:Q\to\widehat C$ 对应，即
   $$
   \psi\circ\eta_Q=p\qquad (\text{等价地，}\eta_Q=\widehat p^{-1}\circ\eta_{\widehat C}\circ p).
   $$
   特别地，$\eta_Q:Q\to\widehat Q$ **恒为满射**，其核为 $\ker\eta_Q=\bigcap_{m\ge 1} t^m Q=E$；$\eta_Q$ 为同构当且仅当 $(\nu_n)_{n\ge 1}$ 有界。

**证明.** 3.1 所给同构族 $(p_m)_{m\ge 1}$ 显然与两边的自然约化过渡映射相容，故取逆极限得 $S$ 模同构 $\widehat p=\varprojlim_{m\ge 1} p_m:\widehat Q\xrightarrow{\sim}\widehat{\widehat C}$。由引理 0，$\eta_{\widehat C}:\widehat C\xrightarrow{\sim}\widehat{\widehat C}$ 也是 $S$ 模同构，故 $\psi=\eta_{\widehat C}^{-1}\circ\widehat p:\widehat Q\xrightarrow{\sim}\widehat C$ 为同构。由完成函子的自然性，$\widehat p\circ\eta_Q=\eta_{\widehat C}\circ p$，左乘 $\eta_{\widehat C}^{-1}$ 即得 $\psi\circ\eta_Q=p$。因 $p$ 满射且 $\ker p=E$，立得 $\eta_Q$ 满射且 $\ker\eta_Q=E$。$\square$

### 3.4 $\widehat E$ 及典范映射 $\eta_E$
**结论：对任意指数列 $(\nu_n)_{n\ge 1}$，典范映射**
$$
\eta_E:E\xrightarrow{\ \sim\ }\widehat E
$$
**恒为 $S$ 模同构**，从而 $E$ 总是 $t$ 进分离且完备的，且 $\widehat E\cong E\cong\mathcal{D}/\mathcal{L}$（特别地，$\widehat E=0\iff(\nu_n)_{n\ge 1}$ 有界）。

**证明.** 经同构 $\theta:\mathcal{D}/\mathcal{L}\xrightarrow{\sim} E$，对每个 $m\ge 1$ 有 $t^m(\mathcal{D}/\mathcal{L})=(t^m\mathcal{D}+\mathcal{L})/\mathcal{L}$。

**第一步：刻画 $t^m\mathcal{D}+\mathcal{L}$ 并证明 $\bigcap_{m\ge 1} t^m E=0$（$\eta_E$ 单射）。**
断言对每个 $m\ge 1$，
$$
t^m\mathcal{D}+\mathcal{L}=\left\{(c_n)_{n\ge 1}\in\mathcal{D}\;\middle|\; \exists N\ge 1,\ \forall n>N,\ v(c_n)\ge m\right\}.
$$
事实上：
- 若 $c=t^m d+a$（$d\in\mathcal{D},a\in\mathcal{L}$），因 $a\in\mathcal{L}$，存在 $N$ 使 $v(a_n)\ge m$（$\forall n>N$），又 $v(t^m d_n)\ge m$，故 $v(c_n)\ge m$（$\forall n>N$）。
- 反之，若 $c=(c_n)\in\mathcal{D}$ 满足 $v(c_n)\ge m$（$\forall n>N$），令 $a_n:=c_n$（$n\le N$）、$a_n:=0$（$n>N$），以及 $d_n:=0$（$n\le N$）、$d_n:=c_n/t^m\in S$（$n>N$）。则 $a=(a_n)\in\mathcal{L}$（有限支撑），且对 $n>N$ 有 $\nu_n+v(d_n)=\nu_n+v(c_n)-m\to\infty$，故 $d=(d_n)\in\mathcal{D}$ 且 $c=t^m d+a\in t^m\mathcal{D}+\mathcal{L}$。

由此，对任意 $c+\mathcal{L}\in\mathcal{D}/\mathcal{L}$，
$$
\begin{aligned}
c+\mathcal{L}\in\bigcap_{m\ge 1} t^m(\mathcal{D}/\mathcal{L})
&\iff \forall m\ge 1,\ c\in t^m\mathcal{D}+\mathcal{L} \\
&\iff \forall m\ge 1,\ \exists N_m\ge 1,\ \forall n>N_m,\ v(c_n)\ge m \\
&\iff \lim_{n\to\infty} v(c_n)=\infty \iff c\in\mathcal{L} \iff c+\mathcal{L}=0.
\end{aligned}
$$
故 $\ker\eta_E=\bigcap_{m\ge 1} t^m E=0$，即 $\eta_E$ 单射（同时证明了 $E$ 的自身 $t$ 进拓扑恒分离）。

（顺便可得每层商的显式坐标模型：模 $t^m$ 约化 $\mathcal{D}\to\prod_{n\ge 1}(S/t^m S)$ 诱导同构 $E/t^m E\xrightarrow{\sim}\mathcal{D}_m/\bigoplus_{n\ge 1}(S/t^m S)$，其中 $\mathcal{D}_m:=\{(u_n)\in\prod_{n\ge 1}(S/t^m S)\mid \forall M\ge 0,\ \{n:\nu_n\le M\text{ 且 }u_n\neq 0\}\text{ 有限}\}$。）

**第二步：证明 $\mathcal{D}$ 对 $t$ 进级数封闭，进而 $\eta_E$ 满射。**
先证：**对 $\mathcal{D}$ 中任意序列 $(z^{(j)})_{j\ge 0}$（记 $z^{(j)}=(z_n^{(j)})_{n\ge 1}$），按坐标定义的幂级数和**
$$
z_n:=\sum_{j=0}^{\infty} t^j z_n^{(j)}\in S \qquad (n\ge 1)
$$
**给出元素 $z=(z_n)_{n\ge 1}\in\mathcal{D}$。**
证明如下：因 $v(t^j z_n^{(j)})\ge j\to\infty$，每个 $z_n$ 在 $S=k[[t]]$ 中良定义。任取整数 $K\ge 1$，将 $z_n$ 分裂为
$$
z_n=s_n^{(K)}+w_n^{(K)},\qquad s_n^{(K)}:=\sum_{j=0}^{K-1} t^j z_n^{(j)},\qquad w_n^{(K)}:=\sum_{j=K}^{\infty} t^j z_n^{(j)}.
$$
因有限和 $s^{(K)}=\sum_{j=0}^{K-1} t^j z^{(j)}$ 属于 $S$ 子模 $\mathcal{D}$，存在 $N_K\ge 1$ 使对一切 $n>N_K$ 有 $\nu_n+v(s_n^{(K)})\ge K$。另一方面，对一切 $n\ge 1$ 均有 $w_n^{(K)}\in t^K S$，故 $v(w_n^{(K)})\ge K$，且因 $\nu_n\ge 0$ 有 $\nu_n+v(w_n^{(K)})\ge K$。从而对一切 $n>N_K$，
$$
\nu_n+v(z_n)\ge \nu_n+\min\bigl(v(s_n^{(K)}),v(w_n^{(K)})\bigr)=\min\bigl(\nu_n+v(s_n^{(K)}),\nu_n+v(w_n^{(K)})\bigr)\ge K.
$$
由 $K\ge 1$ 的任意性得 $\lim_{n\to\infty}(\nu_n+v(z_n))=\infty$，即 $z\in\mathcal{D}$。

今任取 $\xi=(e^{(m)}+t^m E)_{m\ge 1}\in\widehat E=\varprojlim_{m\ge 1} E/t^m E$（$e^{(m)}\in E$）。相容性给出 $e^{(r+1)}-e^{(r)}\in t^r E$（$\forall r\ge 1$）。选取 $x^{(0)}\in\mathcal{D}$ 使 $\theta(x^{(0)}+\mathcal{L})=e^{(1)}$，并对每个 $r\ge 1$ 选取 $x^{(r)}\in\mathcal{D}$ 使
$$
e^{(r+1)}-e^{(r)}=t^r\theta(x^{(r)}+\mathcal{L})=\theta(t^r x^{(r)}+\mathcal{L}).
$$
归纳得 $e^{(m)}=\theta\bigl(\sum_{r=0}^{m-1} t^r x^{(r)}+\mathcal{L}\bigr)$（$\forall m\ge 1$）。按坐标定义 $c=(c_n)_{n\ge 1}$ 与 $y^{(m)}=(y_n^{(m)})_{n\ge 1}$（$m\ge 1$）：
$$
c_n:=\sum_{r=0}^{\infty} t^r x_n^{(r)},\qquad y_n^{(m)}:=\sum_{j=0}^{\infty} t^j x_n^{(m+j)}.
$$
由上述性质，$c\in\mathcal{D}$ 且每个 $y^{(m)}\in\mathcal{D}$。在 $S=k[[t]]$ 中逐项比较 $t^d$ 系数立见对一切 $n,m\ge 1$ 有
$$
c_n-\sum_{r=0}^{m-1} t^r x_n^{(r)}=\sum_{r=m}^{\infty} t^r x_n^{(r)}=t^m\sum_{j=0}^{\infty} t^j x_n^{(m+j)}=t^m y_n^{(m)},
$$
即 $c-\sum_{r=0}^{m-1} t^r x^{(r)}=t^m y^{(m)}\in t^m\mathcal{D}$。作用 $\theta$ 得
$$
\theta(c+\mathcal{L})-e^{(m)}=t^m\theta(y^{(m)}+\mathcal{L})\in t^m E \qquad (\forall m\ge 1),
$$
故 $\eta_E(\theta(c+\mathcal{L}))=\xi$，从而 $\eta_E$ 满射。综合两步，对任意指数列 $(\nu_n)_{n\ge 1}$，$\eta_E:E\xrightarrow{\sim}\widehat E$ 恒为 $S$ 模同构。$\square$

---

### 3.5 $E$ 自身的 $t$ 进拓扑与子空间拓扑的比较、分离性及相等的充要条件

记 $\tau_{\mathrm{int}}$ 为 $E$ 自身的 $t$ 进拓扑（零点邻域基为 $\{t^m E\}_{m\ge 1}$），记 $\tau_{\mathrm{sub}}$ 为 $E$ 从 $Q$ 的 $t$ 进拓扑继承的子空间拓扑（零点邻域基为 $\{E\cap t^m Q\}_{m\ge 1}$）。

**结论：**
1. **子空间拓扑 $\tau_{\mathrm{sub}}$ 恒为密着（平凡）拓扑 $\{\emptyset,E\}$。**
2. **自身 $t$ 进拓扑 $\tau_{\mathrm{int}}$ 对任意指数列 $(\nu_n)_{n\ge 1}$ 恒为分离的**（$\bigcap_{m\ge 1} t^m E=0$），且恒细于或等于 $\tau_{\mathrm{sub}}$（即 $\tau_{\mathrm{sub}}\subseteq\tau_{\mathrm{int}}$）。
3. **$\tau_{\mathrm{int}}$ 与 $\tau_{\mathrm{sub}}$ 相同的充要条件是 $(\nu_n)_{n\ge 1}$ 有界（$\sup_{n\ge 1}\nu_n<\infty$）**：
   - 当 $(\nu_n)_{n\ge 1}$ 有界时，$E=0$，两种拓扑均为单点集上的唯一拓扑 $\{\emptyset,\{0\}\}$，故相同；
   - 当 $(\nu_n)_{n\ge 1}$ 无界时，$E\neq 0$，$\tau_{\mathrm{int}}$ 分离（且有严格递降链 $E\supsetneq t E\supsetneq t^2 E\supsetneq\cdots$），而 $\tau_{\mathrm{sub}}=\{\emptyset,E\}$ 不分离，故 $\tau_{\mathrm{int}}$ 严格细于 $\tau_{\mathrm{sub}}$（$\tau_{\mathrm{sub}}\subsetneq\tau_{\mathrm{int}}$）。

**证明.**
1. 由 3.2 知 $E=\bigcap_{m\ge 1} t^m Q$，故对每个 $m\ge 1$ 均有 $E\subseteq t^m Q$，即
   $$
   E\cap t^m Q = E \qquad (\forall m\ge 1).
   $$
   因此 $\tau_{\mathrm{sub}}$ 的零点邻域基仅为 $\{E\}$，从而唯一非空开集是 $E$ 本身，即 $\tau_{\mathrm{sub}}=\{\emptyset,E\}$。
2. $\tau_{\mathrm{int}}$ 的分离性 $\bigcap_{m\ge 1} t^m E=0$ 已在 3.4 第一步证毕。因 $t^m E\subseteq E=E\cap t^m Q$（$\forall m\ge 1$），恒有 $\tau_{\mathrm{sub}}\subseteq\tau_{\mathrm{int}}$。
3. **充分性：** 若 $(\nu_n)_{n\ge 1}$ 有界，由 2.5 知 $E=0$，显然 $\tau_{\mathrm{int}}=\tau_{\mathrm{sub}}$。

   **必要性：** 若 $\tau_{\mathrm{int}}=\tau_{\mathrm{sub}}$，由于 $t E$ 是 $\tau_{\mathrm{int}}$ 的零点邻域，它必包含 $\tau_{\mathrm{sub}}$ 的某个基本零点邻域 $E\cap t^m Q=E$，于是 $E\subseteq t E\subseteq E$，即 $t E=E$。对 $m\ge 1$ 归纳得 $t^m E=E$ 对一切 $m\ge 1$ 成立，从而
   $$
   E=\bigcap_{m\ge 1} t^m E=0.
   $$
   由 2.5 即得 $(\nu_n)_{n\ge 1}$ 有界。

   （补充：当 $(\nu_n)$ 无界时，取 $n_1<n_2<\cdots$ 使 $\nu_{n_k}\ge k$，对每个 $m\ge 0$ 令 $c_{n_k}^{(m)}=t^m$、其余 $c_n^{(m)}=0$，则 $c^{(m)}\in\mathcal{D}$ 且由 3.4 第一步知 $\theta(c^{(m)}+\mathcal{L})\in t^m E\setminus t^{m+1} E$，故 $E\supsetneq t E\supsetneq t^2 E\supsetneq\cdots$。）$\square$

---

## 核心结论汇总

对任意域 $k$ 及任意非负整数列 $(\nu_n)_{n\ge 1}$：

| 问题项 | 对所有 $(\nu_n)_{n\ge 1}$ 恒成立的结论 / 充要条件 |
|---|---|
| 坐标模型 | $\widehat A\cong\widehat B\cong\mathcal{L}$，$\widehat C\cong\mathcal{C}$，$E\cong\mathcal{D}/\mathcal{L}$ |
| 诱导映射 | $\widehat\iota((a_n))=(t^{\nu_n} a_n)$，$\widehat q((b_n))=(b_n\bmod t^{\nu_n} S)$ |
| 完成列正合性 | $\widehat A$ 处恒正合（$\widehat\iota$ 恒单）；$\widehat C$ 处恒正合（$\widehat q$ 恒满）；$\widehat B$ 处正合（即短正合）$\iff (\nu_n)$ 有界 |
| 闭包与纤维 | $\overline{\operatorname{im}\widehat\iota}=\ker\widehat q$ 恒成立；$\widehat q^{-1}(\Phi_C(u))=\Phi_B(\sigma(u))+\ker\widehat q$ 恒非空 |
| $j$ 与 $Q$ 的挠 | $\ker j=0$ 恒成立；$\operatorname{im} j=Q[t^\infty]=Q_{\mathrm{tors}}\cong C$ 恒成立 |
| $E$ 的挠性与 $p$ | $E$ 恒为无挠 $S$ 模；$p$ 恒满射；$E=0\iff p$ 有 $S$ 线性右逆 $\iff (\nu_n)$ 有界 |
| $p_m$ 与 $\bigcap t^m Q$ | $p_m:Q/t^m Q\xrightarrow{\sim}\widehat C/t^m\widehat C$ 恒同构（$\forall m\ge 1$）；$\bigcap_{m\ge 1} t^m Q=E$ 恒成立 |
| $\widehat Q,\widehat E,\widehat p$ | $\widehat p:\widehat Q\xrightarrow{\sim}\widehat{\widehat C}$ 恒同构，$\widehat Q\cong\widehat C$ 下 $\eta_Q$ 对应 $p$（恒满，核为 $E$）；$\eta_E:E\xrightarrow{\sim}\widehat E$ 恒同构 |
| $E$ 上两种拓扑 | 自身 $t$ 进拓扑 $\tau_{\mathrm{int}}$ 恒分离；子空间拓扑 $\tau_{\mathrm{sub}}=\{\emptyset,E\}$ 恒密着；$\tau_{\mathrm{int}}=\tau_{\mathrm{sub}}\iff (\nu_n)$ 有界 |