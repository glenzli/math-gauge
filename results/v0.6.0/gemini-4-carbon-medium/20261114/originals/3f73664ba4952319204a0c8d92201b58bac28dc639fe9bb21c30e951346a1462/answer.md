{}
以下对任意域 \(k\)、\(R=k[t]\)、\(S=k[[t]]\) 及任意非负整数列 \((\nu_n)_{n\ge1}\) 完整解决三个目标并给出全部证明。

---

## 预备记号与基本引理

1. **\(t\) 进赋值与典范多项式代表元**  
   对形式幂级数 \(s=\sum_{i\ge0}\alpha_i t^i\in S\)，定义其 \(t\) 进赋值
   \[
   v_t(s):=\inf\{i\ge0:\alpha_i\neq0\}\in\mathbb{Z}_{\ge0}\cup\{+\infty\}\qquad\bigl(v_t(0):=+\infty\bigr).
   \]
   对任意整数 \(\nu\ge0\)，自然嵌入 \(R\hookrightarrow S\) 诱导 \(R\) 模（及环）典范同构 \(R/t^\nu R\xrightarrow{\sim}S/t^\nu S\)（当 \(\nu=0\) 时，\(t^0=1\)，商环为零模 \(0\)）。记 \(k[t]_{<\nu}\subseteq R\subseteq S\) 为次数严格小于 \(\nu\) 的多项式构成的子空间（约定 \(0\in k[t]_{<\nu}\)，当 \(\nu=0\) 时 \(k[t]_{<0}:=\{0\}\)）。每个 \(c\in S/t^\nu S\) 有唯一的典范代表元 \(\tilde c\in k[t]_{<\nu}\) 使得 \(c=\tilde c+t^\nu S\)。在 \(S/t^\nu S\) 上定义
   \[
   v_t(c):=\sup\bigl\{m\ge0:c\in t^m(S/t^\nu S)\bigr\}\in\{0,1,\dots,\nu-1\}\cup\{+\infty\}.
   \]
   易见：当 \(c=0\) 时 \(v_t(c)=+\infty=v_t(\tilde c)\)；当 \(c\neq0\) 时（此时必有 \(\nu\ge1\)），对 \(c\) 的任意提升 \(u\in S\) 皆有 \(u\notin t^\nu S\)，故 \(v_t(c)=v_t(u)=v_t(\tilde c)<\nu\)。从而对一切 \(c\in S/t^\nu S\) 及一切 \(m\ge1\)，恒有
   \[
   v_t(c)=v_t(\tilde c),\qquad c\in t^m(S/t^\nu S)\iff v_t(c)\ge m.
   \]

2. **基元素记号与逆向极限投射**  
   记 \(\bar e_n:=q(e_n)\in C\)，则 \(C=\bigoplus_{n\ge1}R\bar e_n\) 且 \(\operatorname{Ann}_R(\bar e_n)=t^{\nu_n}R\)（当 \(\nu_n=0\) 时 \(\bar e_n=0\)），即 \(C\cong\bigoplus_{n\ge1}(R/t^{\nu_n}R)\bar e_n\)。对任意 \(R\) 模 \(M\) 及 \(m\ge1\)，记 \(\pi_{M,m}:\widehat M\to M/t^mM\) 为逆向极限的第 \(m\) 层自然投射。
   
   注意：若 \(M\) 本身已是 \(S\) 模（其限制到 \(R\) 的结构为给定 \(R\) 模结构），则对任意 \(s\in S\)、\(x\in M\) 及 \(m\ge1\)，写 \(s=r_m+t^m u_m\)（\(r_m\in k[t]_{<m}\subseteq R\)，\(u_m\in S\)），有 \(sx=r_m x+t^m(u_m x)\equiv r_m x\pmod{t^m M}\)。因此 \(\eta_M(sx)=(sx+t^mM)_{m\ge1}=(r_m x+t^mM)_{m\ge1}=s\cdot\eta_M(x)\)，即典范映射 \(\eta_M:M\to\widehat M\) 自动是 \(S\) 线性的。

---

## 目标 1：完成模的坐标模型、诱导映射、正合性、闭包与纤维

### 1.1 \(\widehat A,\widehat B,\widehat C\) 的坐标模型与同构

定义如下三个赋予逐坐标 \(S\) 模运算的乘积子模（\(t\) 进受限直积）：
\[
\begin{aligned}
A^\sharp &:=\Bigl\{(a_n)_{n\ge1}\in\prod_{n\ge1}S:\lim_{n\to\infty}v_t(a_n)=+\infty\Bigr\}
=\Bigl\{(a_n)_{n\ge1}\in\prod_{n\ge1}S:\forall m\ge1,\ \#\{n\ge1:t^m\nmid a_n\}<\infty\Bigr\},\\
B^\sharp &:=\Bigl\{(b_n)_{n\ge1}\in\prod_{n\ge1}S:\lim_{n\to\infty}v_t(b_n)=+\infty\Bigr\}
=\Bigl\{(b_n)_{n\ge1}\in\prod_{n\ge1}S:\forall m\ge1,\ \#\{n\ge1:t^m\nmid b_n\}<\infty\Bigr\},\\
C^\sharp &:=\Bigl\{(c_n)_{n\ge1}\in\prod_{n\ge1}S/t^{\nu_n}S:\lim_{n\to\infty}v_t(c_n)=+\infty\Bigr\}
=\Bigl\{(c_n)_{n\ge1}\in\prod_{n\ge1}S/t^{\nu_n}S:\forall m\ge1,\ \#\{n\ge1:c_n\notin t^m(S/t^{\nu_n}S)\}<\infty\Bigr\}.
\end{aligned}
\]
由 \(v_t(x+y)\ge\min(v_t(x),v_t(y))\) 及 \(v_t(sx)\ge v_t(x)\) 可知，\(A^\sharp,B^\sharp,C^\sharp\) 确为对应直积的 \(S\) 子模。

对每个 \(m\ge1\)，由直和与张量积可交换得自然同构：
\[
A/t^mA\cong\bigoplus_{n\ge1}(R/t^mR)(f_n+t^mA),\qquad
B/t^mB\cong\bigoplus_{n\ge1}(R/t^mR)(e_n+t^mB),
\]
\[
C/t^mC\cong\bigoplus_{n\ge1}\bigl(R/(t^{\nu_n}R+t^mR)\bigr)(\bar e_n+t^mC)
=\bigoplus_{n\ge1}(R/t^{\min(\nu_n,m)}R)(\bar e_n+t^mC).
\]
用典范同构 \(S/t^d S\cong R/t^d R\)（将 \(u+t^dS\) 等同于 \((u\bmod t^d)+t^dR\)），定义映射
\[
\begin{aligned}
\Phi_A:A^\sharp\longrightarrow\widehat A,\qquad &(a_n)_{n\ge1}\longmapsto\Bigl(\sum_{n\ge1}(a_n\bmod t^m)(f_n+t^mA)\Bigr)_{m\ge1},\\
\Phi_B:B^\sharp\longrightarrow\widehat B,\qquad &(b_n)_{n\ge1}\longmapsto\Bigl(\sum_{n\ge1}(b_n\bmod t^m)(e_n+t^mB)\Bigr)_{m\ge1},\\
\Phi_C:C^\sharp\longrightarrow\widehat C,\qquad &(c_n)_{n\ge1}\longmapsto\Bigl(\sum_{n\ge1}(\tilde c_n\bmod t^m)(\bar e_n+t^mC)\Bigr)_{m\ge1}.
\end{aligned}
\]

**命题 1.1.** \(\Phi_A,\Phi_B,\Phi_C\) 都是良定义的 \(S\) 模同构。

**证明.**  
- **关于 \(\Phi_B\)（\(\Phi_A\) 完全相同）：**  
  若 \(b=(b_n)_{n\ge1}\in B^\sharp\)，则对每个 \(m\ge1\)，至多有限个 \(n\) 满足 \(t^m\nmid b_n\)，故第 \(m\) 层之和为有限和；又 \((b_n\bmod t^{m+1})\bmod t^m=b_n\bmod t^m\)，故诸层关于自然约化相容，\(\Phi_B(b)\in\widehat B\)。对任意 \(s\in S\)，第 \(m\) 层上 \((sb_n)\bmod t^m=(s\bmod t^m)(b_n\bmod t^m)\)，与 \(\widehat B\) 上由 \(S/(t^m)\) 给出的 \(S\) 作用一致，故 \(\Phi_B\) 是 \(S\) 线性的。  
  反之，设 \(\xi=(\xi^{(m)})_{m\ge1}\in\widehat B\) 为相容商记录，唯一写为 \(\xi^{(m)}=\sum_{n\ge1}u_{m,n}(e_n+t^mB)\)，其中 \(u_{m,n}\in R/t^mR\) 且对固定的 \(m\) 关于 \(n\) 几乎全为零。相容性给出每个固定 \(n\) 的记录 \((u_{m,n})_{m\ge1}\in\varprojlim_{m\ge1}R/t^mR=S\)，定义唯一的 \(b_n\in S\) 使得 \(b_n\bmod t^m=u_{m,n}\)（\(\forall m\ge1\)）。于是 \(\{n\ge1:t^m\nmid b_n\}=\{n\ge1:u_{m,n}\neq0\}\) 对每个 \(m\ge1\) 有限，即 \((b_n)_{n\ge1}\in B^\sharp\)。定义 \(\Psi_B(\xi):=(b_n)_{n\ge1}\)，则 \(\Psi_B\) 与 \(\Phi_B\) 显然互逆。

- **关于 \(\Phi_C\)：**  
  在 \(C/t^mC\) 的第 \(n\) 个直和项中，\(\tilde c_n\bmod t^m\) 在 \(R/t^{\min(\nu_n,m)}R\cong S/t^{\min(\nu_n,m)}S\) 中的像为零当且仅当 \(\tilde c_n\in t^{\min(\nu_n,m)}S\)。由于 \(\deg\tilde c_n<\nu_n\)（或 \(\tilde c_n=0\)），这等价于 \(v_t(c_n)=v_t(\tilde c_n)\ge m\)，即 \(c_n\in t^m(S/t^{\nu_n}S)\)。因此，对 \(c=(c_n)_{n\ge1}\in C^\sharp\) 及每个 \(m\ge1\)，第 \(m\) 层仅有有限个非零项，且由 \((\tilde c_n\bmod t^{m+1})\bmod t^{\min(\nu_n,m)}=\tilde c_n\bmod t^{\min(\nu_n,m)}\) 知各层相容，故 \(\Phi_C(c)\in\widehat C\)。对任意 \(s\in S\)，因 \(s\tilde c_n\equiv\widetilde{sc_n}\pmod{t^{\nu_n}S}\)，二者在 \(S/t^{\min(\nu_n,m)}S\) 中相等，从而 \((s\bmod t^m)(\tilde c_n\bmod t^{\min(\nu_n,m)})=\widetilde{sc_n}\bmod t^{\min(\nu_n,m)}\)，证得 \(\Phi_C\) 是 \(S\) 线性的。  
  反之，给定相容商记录 \(\zeta=(\zeta^{(m)})_{m\ge1}\in\widehat C\)，唯一写为 \(\zeta^{(m)}=\sum_{n\ge1}w_{m,n}(\bar e_n+t^mC)\)，其中 \(w_{m,n}\in R/t^{\min(\nu_n,m)}R\cong S/t^{\min(\nu_n,m)}S\) 对每个 \(m\) 关于 \(n\) 几乎全为零。对每个固定的 \(n\ge1\)，取 \(m_n:=\max(\nu_n,1)\)，则当 \(m\ge m_n\) 时 \(\min(\nu_n,m)=\nu_n\)，过渡映射在第 \(n\) 坐标上是 \(S/t^{\nu_n}S\) 的恒等映射，故 \(w_{m,n}\) 在 \(m\ge m_n\) 时稳定于唯一元素 \(c_n:=w_{m_n,n}\in S/t^{\nu_n}S\)；再由 \(m_n\) 到任意 \(m<m_n\) 的相容性知对一切 \(m\ge1\) 都有 \(w_{m,n}=\tilde c_n\bmod t^{\min(\nu_n,m)}\)。于是对每个 \(m\ge1\)，
  \[
  \{n\ge1:v_t(c_n)<m\}=\{n\ge1:w_{m,n}\neq0\}
  \]
  是有限集，即 \((c_n)_{n\ge1}\in C^\sharp\)。令 \(\Psi_C(\zeta):=(c_n)_{n\ge1}\)，则 \(\Psi_C\) 与 \(\Phi_C\) 互逆。\(\blacksquare\)

---

### 1.2 典范映射与诱导映射的坐标表示

在上述同构下：
1. **典范映射 \(\eta_A,\eta_B,\eta_C\)：** 对有限和 \(\sum_n r_n f_n\in A\)、\(\sum_n r_n e_n\in B\)、\(\sum_n r_n\bar e_n\in C\)（\(r_n\in R\subseteq S\)），有
   \[
   \Phi_A^{-1}\Bigl(\eta_A\Bigl(\sum_{n\ge1}r_n f_n\Bigr)\Bigr)=(r_n)_{n\ge1},\qquad
   \Phi_B^{-1}\Bigl(\eta_B\Bigl(\sum_{n\ge1}r_n e_n\Bigr)\Bigr)=(r_n)_{n\ge1},
   \]
   \[
   \Phi_C^{-1}\Bigl(\eta_C\Bigl(\sum_{n\ge1}r_n\bar e_n\Bigr)\Bigr)=(r_n+t^{\nu_n}S)_{n\ge1}.
   \]
2. **诱导映射 \(\widehat\iota:\widehat A\to\widehat B\) 与 \(\widehat q:\widehat B\to\widehat C\)：**  
   在第 \(m\) 层上，\(\iota_m(f_n+t^mA)=t^{\nu_n}e_n+t^mB\)，\(q_m(e_n+t^mB)=\bar e_n+t^mC\)。因此在坐标模型中，\(\widehat\iota=\Phi_B\circ\iota^\sharp\circ\Phi_A^{-1}\)，\(\widehat q=\Phi_C\circ q^\sharp\circ\Phi_B^{-1}\)，其中 \(S\) 线性映射 \(\iota^\sharp:A^\sharp\to B^\sharp\) 与 \(q^\sharp:B^\sharp\to C^\sharp\) 为
   \[
   \iota^\sharp\bigl((a_n)_{n\ge1}\bigr)=(t^{\nu_n}a_n)_{n\ge1},\qquad
   q^\sharp\bigl((b_n)_{n\ge1}\bigr)=(b_n+t^{\nu_n}S)_{n\ge1}.
   \]
   （易核验 \(v_t(t^{\nu_n}a_n)=\nu_n+v_t(a_n)\ge v_t(a_n)\to+\infty\) 且 \(v_t(b_n+t^{\nu_n}S)\ge v_t(b_n)\to+\infty\)。）

---

### 1.3 完成列在各处的正合性与短正合充要条件

考察完成列
\[
0\longrightarrow\widehat A\xrightarrow{\;\widehat\iota\;}\widehat B\xrightarrow{\;\widehat q\;}\widehat C\longrightarrow0,
\]
等价地考察坐标列 \(0\to A^\sharp\xrightarrow{\iota^\sharp}B^\sharp\xrightarrow{q^\sharp}C^\sharp\to0\)。引入乘积子模
\[
A^\flat:=\Bigl\{(a_n)_{n\ge1}\in\prod_{n\ge1}S:\lim_{n\to\infty}\bigl(\nu_n+v_t(a_n)\bigr)=+\infty\Bigr\}.
\]

**定理 1.2.** 对任意非负整数列 \((\nu_n)_{n\ge1}\)：
1. **在 \(\widehat A\) 处恒正合：** \(\ker\widehat\iota=0\)。
2. **在 \(\widehat C\) 处恒正合：** \(\widehat q\) 恒为满射。
3. **在 \(\widehat B\) 处的正合性：** \(\operatorname{im}\widehat\iota\subseteq\ker\widehat q\) 恒成立，且 \(\operatorname{im}\widehat\iota=\ker\widehat q\) 当且仅当指数列 \((\nu_n)_{n\ge1}\) 有界（即 \(\sup_{n\ge1}\nu_n<\infty\)）。
4. **短正合充要条件：** 完成列 \(0\to\widehat A\xrightarrow{\widehat\iota}\widehat B\xrightarrow{\widehat q}\widehat C\to0\) 短正合当且仅当 \(\sup_{n\ge1}\nu_n<\infty\)。

**证明.**  
1. 若 \(\iota^\sharp((a_n)_{n\ge1})=(t^{\nu_n}a_n)_{n\ge1}=0\)，则对每个 \(n\ge1\) 在整环 \(S\) 中有 \(t^{\nu_n}a_n=0\)。因 \(t^{\nu_n}\neq0\)，故 \(a_n=0\)（\(\forall n\ge1\)），即 \(\ker\iota^\sharp=0\)。
2. 定义典范多项式提升映射（它是 \(k\) 线性的，一般非 \(S\) 线性）：
   \[
   \sigma:C^\sharp\longrightarrow B^\sharp,\qquad \sigma\bigl((c_n)_{n\ge1}\bigr):=(\tilde c_n)_{n\ge1}.
   \]
   对任意 \(c=(c_n)_{n\ge1}\in C^\sharp\)，因 \(v_t(\tilde c_n)=v_t(c_n)\to+\infty\)，故 \(\sigma(c)\in B^\sharp\)；又 \(\tilde c_n+t^{\nu_n}S=c_n\)，故 \(q^\sharp(\sigma(c))=c\)。因此 \(q^\sharp\)（从而 \(\widehat q\)）恒为满射。
3. 对 \(b=(b_n)_{n\ge1}\in B^\sharp\)，有 \(q^\sharp(b)=0\iff\forall n\ge1,\ t^{\nu_n}\mid b_n\)。因 \(S\) 是整环且 \(t^{\nu_n}\neq0\)，每个满足 \(t^{\nu_n}\mid b_n\) 的 \(b_n\) 唯一写作 \(b_n=t^{\nu_n}a_n\)（\(a_n\in S\)），此时 \(v_t(b_n)=\nu_n+v_t(a_n)\)。故
   \[
   \ker q^\sharp=\bigl\{(t^{\nu_n}a_n)_{n\ge1}:(a_n)_{n\ge1}\in A^\flat\bigr\},\qquad
   \operatorname{im}\iota^\sharp=\bigl\{(t^{\nu_n}a_n)_{n\ge1}:(a_n)_{n\ge1}\in A^\sharp\bigr\}.
   \]
   由于 \(A^\sharp\subseteq A^\flat\)，恒有 \(\operatorname{im}\iota^\sharp\subseteq\ker q^\sharp\)；再由 \(t^{\nu_n}\) 的消去律知 \(\operatorname{im}\iota^\sharp=\ker q^\sharp\iff A^\sharp=A^\flat\)。
   - 若 \(\sup_{n\ge1}\nu_n=M<\infty\)，则对任意 \((a_n)_{n\ge1}\in A^\flat\)，由 \(v_t(a_n)\ge(\nu_n+v_t(a_n))-M\to+\infty\) 知 \((a_n)_{n\ge1}\in A^\sharp\)，故 \(A^\sharp=A^\flat\)。
   - 若 \(\sup_{n\ge1}\nu_n=+\infty\)，可取严格递增指标子列 \(1\le n_1<n_2<\cdots\) 使得 \(\lim_{k\to\infty}\nu_{n_k}=+\infty\)。令
     \[
     a_n:=\begin{cases}1,&n\in\{n_1,n_2,\dots\},\\ 0,&n\notin\{n_1,n_2,\dots\}.\end{cases}
     \]
     当 \(n=n_k\) 时 \(\nu_n+v_t(a_n)=\nu_{n_k}\to+\infty\)；当 \(n\notin\{n_k\}\) 时 \(\nu_n+v_t(a_n)=+\infty\)。故 \((a_n)_{n\ge1}\in A^\flat\)。但对一切 \(k\ge1\) 有 \(v_t(a_{n_k})=0\)，故 \((a_n)_{n\ge1}\notin A^\sharp\)，从而 \(A^\sharp\subsetneq A^\flat\)。
4. 综合 (1)–(3) 即得短正合的充要条件为 \(\sup_{n\ge1}\nu_n<\infty\)。\(\blacksquare\)

---

### 1.4 \(\operatorname{im}\widehat\iota\) 在 \(\widehat B\) 中的闭包与 \(\widehat q\) 的全部纤维

先刻画 \(\widehat B\) 与 \(\widehat C\) 上的 \(t^m\) 子模：

**引理 1.3.** 对每个 \(m\ge1\)，有
\[
t^m\widehat B=\ker\pi_{B,m}=\Phi_B\Bigl(\bigl\{(b_n)_{n\ge1}\in B^\sharp:\forall n\ge1,\ t^m\mid b_n\bigr\}\Bigr),\qquad
t^m\widehat C=\ker\pi_{C,m}=\Phi_C\Bigl(\bigl\{(c_n)_{n\ge1}\in C^\sharp:\forall n\ge1,\ v_t(c_n)\ge m\bigr\}\Bigr).
\]
特别地，\(\bigcap_{m\ge1}t^m\widehat B=0\)，\(\bigcap_{m\ge1}t^m\widehat C=0\)（两者在 \(t\) 进拓扑下都是分离的）。

**证明.**  
在 \(B^\sharp\) 中，显然 \(t^mB^\sharp\subseteq\{(b_n)\in B^\sharp:\forall n,\ t^m\mid b_n\}=\Phi_B^{-1}(\ker\pi_{B,m})\)。反之，若 \(b=(b_n)\in B^\sharp\) 满足 \(b_n=t^m d_n\)（\(d_n\in S\)），则 \(v_t(d_n)=v_t(b_n)-m\to+\infty\)，故 \((d_n)\in B^\sharp\) 且 \(b=t^m(d_n)\in t^mB^\sharp\)。  
同理，在 \(C^\sharp\) 中，\(t^mC^\sharp\subseteq\{(c_n)\in C^\sharp:\forall n,\ c_n\in t^m(S/t^{\nu_n}S)\}=\Phi_C^{-1}(\ker\pi_{C,m})\)。反之，若 \(c=(c_n)\in C^\sharp\) 满足 \(v_t(\tilde c_n)=v_t(c_n)\ge m\)（\(\forall n\ge1\)），则在 \(S\) 中可写 \(\tilde c_n=t^m g_n\)（当 \(c_n=0\) 时取 \(g_n=0\)），有 \(v_t(g_n)=v_t(\tilde c_n)-m\to+\infty\) 且 \(\deg g_n<\nu_n-m<\nu_n\)（当 \(c_n\neq0\) 时），故 \(d_n:=g_n+t^{\nu_n}S\) 满足 \(v_t(d_n)=v_t(g_n)\to+\infty\)，即 \(d=(d_n)\in C^\sharp\) 且 \(t^m d=c\in t^mC^\sharp\)。  
由逆向极限定义知 \(\bigcap_{m\ge1}\ker\pi_{B,m}=0\) 且 \(\bigcap_{m\ge1}\ker\pi_{C,m}=0\)。\(\blacksquare\)

**定理 1.4（闭包与纤维）.** 对任意非负整数列 \((\nu_n)_{n\ge1}\)：
1. 在 \(\widehat B\) 的 \(t\) 进拓扑下，\(\operatorname{im}\widehat\iota\) 的闭包恒为 \(\ker\widehat q\)，即
   \[
   \overline{\operatorname{im}\widehat\iota}=\bigcap_{m\ge1}\bigl(\operatorname{im}\widehat\iota+t^m\widehat B\bigr)=\ker\widehat q=\Phi_B\Bigl(\bigl\{(b_n)_{n\ge1}\in B^\sharp:\forall n\ge1,\ t^{\nu_n}\mid b_n\bigr\}\Bigr).
   \]
   （特别地，\(\operatorname{im}\widehat\iota\) 在 \(\widehat B\) 中闭当且仅当 \(\sup_{n\ge1}\nu_n<\infty\)。）
2. 对每个 \(\hat c=\Phi_C(c)\in\widehat C\)（其中 \(c=(c_n)_{n\ge1}\in C^\sharp\)），纤维 \(\widehat q^{-1}(\hat c)\) 非空，且由如下等价表达式给出：
   \[
   \begin{aligned}
   \widehat q^{-1}(\hat c)
   &=\Phi_B\bigl(\sigma(c)\bigr)+\ker\widehat q\\
   &=\Phi_B\Bigl(\bigl\{(b_n)_{n\ge1}\in B^\sharp:\forall n\ge1,\ b_n+t^{\nu_n}S=c_n\bigr\}\Bigr)\\
   &=\Phi_B\Bigl(\bigl\{(\tilde c_n+t^{\nu_n}a_n)_{n\ge1}:(a_n)_{n\ge1}\in A^\flat\bigr\}\Bigr).
   \end{aligned}
   \]

**证明.**  
1. 对每个 \(m\ge1\)，因 \(\widehat q(\operatorname{im}\widehat\iota+t^m\widehat B)\subseteq t^m\widehat C\)，故由引理 1.3 得
   \[
   \widehat q\Bigl(\bigcap_{m\ge1}\bigl(\operatorname{im}\widehat\iota+t^m\widehat B\bigr)\Bigr)\subseteq\bigcap_{m\ge1}t^m\widehat C=0,
   \]
   从而 \(\overline{\operatorname{im}\widehat\iota}\subseteq\ker\widehat q\)。  
   反之，设 \(b=(t^{\nu_n}a_n)_{n\ge1}\in\ker q^\sharp\)（其中 \((a_n)_{n\ge1}\in A^\flat\)）。任取 \(m\ge1\)，因 \(\lim_{n\to\infty}(\nu_n+v_t(a_n))=+\infty\)，存在 \(N\ge0\) 使得对一切 \(n>N\) 都有 \(\nu_n+v_t(a_n)\ge m\)，即 \(t^m\mid t^{\nu_n}a_n\)。将 \(b\) 分解为 \(b=b^{(\le N)}+b^{(>N)}\)，其中
   \[
   b^{(\le N)}:=(t^{\nu_1}a_1,\dots,t^{\nu_N}a_N,0,0,\dots)=\iota^\sharp(a_1,\dots,a_N,0,0,\dots)\in\operatorname{im}\iota^\sharp,
   \]
   而 \(b^{(>N)}:=(0,\dots,0,t^{\nu_{N+1}}a_{N+1},t^{\nu_{N+2}}a_{N+2},\dots)\in B^\sharp\) 的每个坐标都被 \(t^m\) 整除，由引理 1.3 知 \(\Phi_B(b^{(>N)})\in t^m\widehat B\)。故对一切 \(m\ge1\) 有 \(\Phi_B(b)\in\operatorname{im}\widehat\iota+t^m\widehat B\)，即 \(\ker\widehat q\subseteq\overline{\operatorname{im}\widehat\iota}\)。
2. 由定理 1.2(2) 知 \(\widehat q(\Phi_B(\sigma(c)))=\hat c\)，故纤维非空且等于陪集 \(\Phi_B(\sigma(c))+\ker\widehat q\)。将 \(\sigma(c)=(\tilde c_n)_{n\ge1}\) 与 \(\ker q^\sharp=\{(t^{\nu_n}a_n)_{n\ge1}:(a_n)_{n\ge1}\in A^\flat\}\) 代入即得后两个坐标表达式。\(\blacksquare\)

---

## 目标 2：\(E\) 的坐标模型、\(j\) 的核与像、挠元结构、\(p\) 的满射性与右逆

### 2.1 \(E\) 的明确坐标模型

由 \(p(x+\operatorname{im}\widehat\iota)=\widehat q(x)\) 知 \(E=\ker p=\ker\widehat q/\operatorname{im}\widehat\iota\)。由定理 1.2(3) 的证明，\(A^\sharp\) 是 \(A^\flat\) 的 \(S\) 子模；置商 \(S\) 模
\[
E^\sharp:=A^\flat/A^\sharp
=\frac{\bigl\{(a_n)_{n\ge1}\in\prod_{n\ge1}S:\lim_{n\to\infty}\bigl(\nu_n+v_t(a_n)\bigr)=+\infty\bigr\}}{\bigl\{(a_n)_{n\ge1}\in\prod_{n\ge1}S:\lim_{n\to\infty}v_t(a_n)=+\infty\bigr\}}.
\]

**命题 2.1.** 映射
\[
\Phi_E:E^\sharp\longrightarrow E,\qquad (a_n)_{n\ge1}+A^\sharp\longmapsto\Phi_B\bigl((t^{\nu_n}a_n)_{n\ge1}\bigr)+\operatorname{im}\widehat\iota
\]
是良定义的 \(S\) 模同构。（若改用 \(\widehat B\) 的坐标 \(b_n=t^{\nu_n}a_n\)，则等价地有 \(E\cong\frac{\{(b_n)\in B^\sharp:\forall n,\ t^{\nu_n}\mid b_n\}}{\{(b_n)\in B^\sharp:\forall n,\ t^{\nu_n}\mid b_n\text{ 且 }\lim_{n\to\infty}(v_t(b_n)-\nu_n)=+\infty\}}\)。）

**证明.** 映射 \(\tau:A^\flat\to\ker\widehat q\)，\((a_n)_{n\ge1}\mapsto\Phi_B((t^{\nu_n}a_n)_{n\ge1})\) 是 \(S\) 线性满射（定理 1.2(3)），由 \(S\) 中 \(t^{\nu_n}\neq0\) 的消去律知 \(\tau\) 为单射，且 \(\tau(A^\sharp)=\Phi_B(\operatorname{im}\iota^\sharp)=\operatorname{im}\widehat\iota\)。由第一同构定理即得 \(\Phi_E:A^\flat/A^\sharp\xrightarrow{\sim}\ker\widehat q/\operatorname{im}\widehat\iota=E\)。\(\blacksquare\)

---

### 2.2 \(j:C\to Q\) 的良定义性、核与像

首先验证 \(j\) 良定义且与 \(p,\eta_C\) 相容：若 \(b\in\ker q=\iota(A)\)，写 \(b=\iota(a)\)（\(a\in A\)），则 \(\eta_B(b)=\eta_B(\iota(a))=\widehat\iota(\eta_A(a))\in\operatorname{im}\widehat\iota\)，故 \(j(q(b))=\eta_B(b)+\operatorname{im}\widehat\iota\) 良定义为 \(R\) 线性映射。对任意 \(b\in B\)，
\[
(p\circ j)(q(b))=p\bigl(\eta_B(b)+\operatorname{im}\widehat\iota\bigr)=\widehat q(\eta_B(b))=\eta_C(q(b)),
\]
即恒有 \(p\circ j=\eta_C\)。记 \(\hat e_n:=j(\bar e_n)=\eta_B(e_n)+\operatorname{im}\widehat\iota\in Q\)。

**定理 2.2（\(j\) 的核与像）.** 对任意非负整数列 \((\nu_n)_{n\ge1}\)：
1. \(\ker j=0\)（且 \(\operatorname{im}j\cap E=0\)）。
2. 在 \(Q=\widehat B/\operatorname{im}\widehat\iota\) 中，
   \[
   \operatorname{im}j=\bigl(\operatorname{im}\eta_B+\operatorname{im}\widehat\iota\bigr)/\operatorname{im}\widehat\iota
   =\bigoplus_{n\ge1}R\hat e_n=\bigoplus_{n\ge1}S\hat e_n.
   \]
   用 \(B^\sharp\) 的坐标表述：设 \(b=(b_n)_{n\ge1}\in B^\sharp\)，唯一分解 \(b_n=\tilde c_n+t^{\nu_n}a_n\)（其中 \(\tilde c_n\in k[t]_{<\nu_n}\)，\(a_n\in S\)），则 \(\Phi_B(b)+\operatorname{im}\widehat\iota\in\operatorname{im}j\) 当且仅当如下两条同时成立：
   - 对充分大的 \(n\) 有 \(t^{\nu_n}\mid b_n\)（等价于仅有限个 \(n\) 满足 \(\tilde c_n\neq0\)）；
   - \(\lim_{n\to\infty}\bigl(v_t(b_n)-\nu_n\bigr)=+\infty\)（等价于 \((a_n)_{n\ge1}\in A^\sharp\)）。

**证明.**  
1. 在 \(C\cong\bigoplus_{n\ge1}(R/t^{\nu_n}R)\bar e_n\) 中，任一元 \(c=\sum_{n=1}^N c_n\bar e_n\) 被 \(t^m\)（取 \(m=\max(1,\nu_1,\dots,\nu_N)\)）零化；反之若 \(c\in\bigcap_{m\ge1}t^mC\)，则对每个 \(n\le N\) 取 \(m=\max(1,\nu_n)\) 得 \(c_n\in t^m(R/t^{\nu_n}R)=0\)。故 \(\ker\eta_C=\bigcap_{m\ge1}t^mC=0\)，即 \(\eta_C\) 是单射。由 \(p\circ j=\eta_C\) 立得 \(\ker j=0\)，且若 \(j(c)\in E=\ker p\)，则 \(\eta_C(c)=p(j(c))=0\implies c=0\implies j(c)=0\)，故 \(\operatorname{im}j\cap E=0\)。
2. 由定义即有 \(\operatorname{im}j=(\operatorname{im}\eta_B+\operatorname{im}\widehat\iota)/\operatorname{im}\widehat\iota=\sum_{n\ge1}R\hat e_n\)；因 \(j\) 是单射且 \(C=\bigoplus_{n\ge1}R\bar e_n\)，该和为直和 \(\bigoplus_{n\ge1}R\hat e_n\)。对每个 \(n\ge1\) 及任意 \(s\in S\)，写 \(s=r+t^{\nu_n}u\)（\(r\in k[t]_{<\nu_n}\subseteq R\)，\(u\in S\)），则
   \[
   s\eta_B(e_n)=r\eta_B(e_n)+t^{\nu_n}u\eta_B(e_n)=r\eta_B(e_n)+\widehat\iota\bigl(u\eta_A(f_n)\bigr)\equiv r\eta_B(e_n)\pmod{\operatorname{im}\widehat\iota},
   \]
   故 \(S\hat e_n=R\hat e_n\)，从而 \(\operatorname{im}j=\bigoplus_{n\ge1}S\hat e_n\) 也是 \(Q\) 的 \(S\) 子模。  
   再证坐标刻画：设 \(b=(b_n)_{n\ge1}\in B^\sharp\)，\(b_n=\tilde c_n+t^{\nu_n}a_n\)。
   - 若 \(\Phi_B(b)\in\operatorname{im}\eta_B+\operatorname{im}\widehat\iota\)，则存在 \(r=(r_n)_{n\ge1}\in\bigoplus_{n\ge1}R\)（当 \(n>N\) 时 \(r_n=0\)）及 \(a'=(a'_n)_{n\ge1}\in A^\sharp\) 使 \(b_n=r_n+t^{\nu_n}a'_n\)。写 \(r_n=\tilde c'_n+t^{\nu_n}q_n\)（\(\tilde c'_n\in k[t]_{<\nu_n}\)，\(q_n\in R\)，且 \(n>N\) 时 \(\tilde c'_n=q_n=0\)），由唯一性得 \(\tilde c_n=\tilde c'_n\)（对 \(n>N\) 为 \(0\)，此时 \(v_t(b_n)-\nu_n=v_t(a_n)\)）及 \(a_n=q_n+a'_n\)。因 \(q_n\) 仅有限项非零且 \(a'\in A^\sharp\)，故 \((a_n)_{n\ge1}\in A^\sharp\)，从而 \(\lim_{n\to\infty}(v_t(b_n)-\nu_n)=\lim_{n\to\infty}v_t(a_n)=+\infty\)。
   - 反之，若 \(\tilde c_n\) 仅对 \(n\le N\) 可能非零且 \((a_n)_{n\ge1}\in A^\sharp\)，令 \(g:=\sum_{n=1}^N\tilde c_n e_n\in B\)，则 \(\Phi_B(b)=\eta_B(g)+\widehat\iota(\Phi_A((a_n)_{n\ge1}))\in\operatorname{im}\eta_B+\operatorname{im}\widehat\iota\)。\(\blacksquare\)

---

### 2.3 \(Q\) 中被某个 \(t^r\)（\(r\ge1\)）杀死的元素与 \(E\) 的 \(S\) 模挠性

对 \(r\ge1\)，记 \(\operatorname{Ann}_Q(t^r):=\{x\in Q:t^r x=0\}\)，并考察 \(t^\infty\) 挠子模 \(\bigcup_{r\ge1}\operatorname{Ann}_Q(t^r)\)。

**定理 2.3.** 对任意非负整数列 \((\nu_n)_{n\ge1}\)：
1. \(Q\) 中所有被某个 \(t^r\)（\(r\ge1\)）杀死的元素构成的子模恰好是 \(\operatorname{im}j\)：
   \[
   \bigcup_{r\ge1}\operatorname{Ann}_Q(t^r)=\operatorname{im}j.
   \]
   更精细地，对每个固定的 \(r\ge1\)，有 \(\operatorname{Ann}_Q(t^r)=j\bigl(\operatorname{Ann}_C(t^r)\bigr)=\bigoplus_{n\ge1}t^{\max(\nu_n-r,0)}R\hat e_n\)。
2. \(E\) 的 \(S\) 模挠子模恒为零：
   \[
   T_S(E):=\{e\in E:\exists\,0\neq s\in S,\ se=0\}=0,
   \]
   即 **\(E\) 恒为无挠 \(S\) 模**。（此外 \(T_S(Q)=\operatorname{im}j\)；而 \(E\) 为挠 \(S\) 模当且仅当 \(E=0\)，即 \(\sup_{n\ge1}\nu_n<\infty\)。）

**证明.**  
1. 任取 \(x=j(c)\in\operatorname{im}j\)，写 \(c=\sum_{n=1}^N c_n\bar e_n\in C\)。取 \(r=\max(\{1\}\cup\{\nu_1,\dots,\nu_N\})\ge1\)，则 \(t^r c=0\)，故 \(t^r x=j(t^r c)=0\)，证得 \(\operatorname{im}j\subseteq\bigcup_{r\ge1}\operatorname{Ann}_Q(t^r)\)。  
   反之，设 \(x=\Phi_B(b)+\operatorname{im}\widehat\iota\in Q\)（\(b=(b_n)_{n\ge1}\in B^\sharp\)）满足 \(t^r x=0\)（某 \(r\ge1\)）。则 \(t^r\Phi_B(b)\in\operatorname{im}\widehat\iota\)，即存在 \(a=(a_n)_{n\ge1}\in A^\sharp\) 使得
   \[
   t^r b_n=t^{\nu_n}a_n\qquad(\forall n\ge1).
   \]
   因 \(a\in A^\sharp\)，\(\lim_{n\to\infty}v_t(a_n)=+\infty\)，故存在 \(N\ge0\) 使得对一切 \(n>N\) 都有 \(v_t(a_n)\ge r\)，即 \(a_n=t^r d_n\)（\(d_n\in S\)），且 \(\lim_{n\to\infty}v_t(d_n)=\lim_{n\to\infty}(v_t(a_n)-r)=+\infty\)。对 \(n>N\) 代入上式得 \(t^r b_n=t^r(t^{\nu_n}d_n)\)，在整环 \(S\) 中消去 \(t^r\neq0\) 得
   \[
   b_n=t^{\nu_n}d_n\qquad(\forall n>N).
   \]
   对 \(1\le n\le N\)，作带余除法 \(b_n=\tilde c_n+t^{\nu_n}d_n\)（\(\tilde c_n\in k[t]_{<\nu_n}\)，\(d_n\in S\)），并对 \(n>N\) 置 \(\tilde c_n:=0\)。于是 \((d_n)_{n\ge1}\in A^\sharp\)，且 \(\tilde c_n\) 仅对 \(n\le N\) 可能非零。由定理 2.2(2) 立得 \(x\in\operatorname{im}j\)。  
   进一步，对固定的 \(r\ge1\)，若 \(x\in\operatorname{Ann}_Q(t^r)\)，则已知 \(x=j(c)\)（\(c\in C\)）；因 \(j\) 为单射，\(t^r j(c)=j(t^r c)=0\iff t^r c=0\)，故 \(\operatorname{Ann}_Q(t^r)=j(\operatorname{Ann}_C(t^r))=\bigoplus_{n\ge1}t^{\max(\nu_n-r,0)}R\hat e_n\)。
2. 在离散赋值环 \(S=k[[t]]\) 中，任意非零元 \(s\in S\) 皆有形式 \(s=ut^r\)，其中 \(u\in S^\times\) 可逆，\(r=v_t(s)\ge0\)。故对任意 \(S\) 模 \(M\) 及 \(y\in M\)，有 \(sy=0\iff t^r y=0\implies t^{\max(r,1)}y=0\)。从而
   \[
   T_S(Q)=\bigcup_{r\ge1}\operatorname{Ann}_Q(t^r)=\operatorname{im}j,\qquad
   T_S(E)=E\cap T_S(Q)=E\cap\operatorname{im}j=0,
   \]
   最后一式由定理 2.2(1) 给出。（亦可在 \(E^\sharp=A^\flat/A^\sharp\) 中直接验证：若 \(0\neq s=ut^r\in S\) 使 \(sa\in A^\sharp\)，则 \(v_t(a_n)=v_t(sa_n)-r\to+\infty\)，故 \(a\in A^\sharp\)。）因此 \(E\) 恒为无挠 \(S\) 模。\(\blacksquare\)

---

### 2.4 \(p\) 的满射性、\(E=0\) 与 \(p\) 存在 \(S\) 线性右逆的充要条件

**定理 2.4.** 对任意非负整数列 \((\nu_n)_{n\ge1}\)：
1. 映射 \(p:Q\to\widehat C\) **恒为满射**。
2. \(E=0\) 当且仅当 \((\nu_n)_{n\ge1}\) 有界（即 \(\sup_{n\ge1}\nu_n<\infty\)）。
3. \(p:Q\to\widehat C\) 存在 \(S\) 线性右逆（即存在 \(S\) 模同态 \(s:\widehat C\to Q\) 使 \(p\circ s=\operatorname{id}_{\widehat C}\)）当且仅当 \((\nu_n)_{n\ge1}\) 有界（即 \(\sup_{n\ge1}\nu_n<\infty\)）。

**证明.**  
1. 由定义 \(\operatorname{im}p=\operatorname{im}\widehat q\)，由定理 1.2(2) 知 \(\widehat q\) 恒满，故 \(p\) 恒为满射。
2. 因 \(E=\ker\widehat q/\operatorname{im}\widehat\iota\)，故 \(E=0\iff\operatorname{im}\widehat\iota=\ker\widehat q\)，由定理 1.2(3) 知这等价于 \(\sup_{n\ge1}\nu_n<\infty\)。
3. **充分性：** 若 \(\sup_{n\ge1}\nu_n<\infty\)，由 (1)(2) 知 \(p:Q\to\widehat C\) 是双射 \(S\) 模同态，其逆映射 \(p^{-1}:\widehat C\to Q\) 即为 \(S\) 线性右逆。  
   **必要性：** 反证法。设 \(\sup_{n\ge1}\nu_n=+\infty\)，且存在 \(S\) 线性（甚至只需 \(R\) 线性）映射 \(s:\widehat C\to Q\) 满足 \(p\circ s=\operatorname{id}_{\widehat C}\)。  
   因 \(\sup_{n\ge1}\nu_n=+\infty\)，可取严格递增正整数列 \(1\le n_1<n_2<\cdots\) 使得对每个 \(k\ge1\) 都有 \(\nu_{n_k}\ge k\ge1\)。在 \(\prod_{n\ge1}S/t^{\nu_n}S\) 中定义元素 \(c=(c_n)_{n\ge1}\)：
   \[
   c_n:=\begin{cases}
   t^{\nu_{n_k}-1}+t^{\nu_{n_k}}S,&n=n_k\ (k\ge1),\\
   0,&n\notin\{n_1,n_2,\dots\}.
   \end{cases}
   \]
   - 对每个 \(k\ge1\)，因 \(\nu_{n_k}\ge1\)，有 \(t^{\nu_{n_k}-1}\notin t^{\nu_{n_k}}S\)，故 \(c_{n_k}\neq0\) 且 \(v_t(c_{n_k})=\nu_{n_k}-1\ge k-1\to+\infty\)（\(k\to\infty\)）。从而 \(\lim_{n\to\infty}v_t(c_n)=+\infty\)，即 \(c\in C^\sharp\)，令 \(\hat c:=\Phi_C(c)\in\widehat C\)。
   - 注意 \(\Phi_C^{-1}(\operatorname{im}\eta_C)=\bigoplus_{n\ge1}S/t^{\nu_n}S\) 中每个元素仅有有限个非零坐标，而 \(c\) 有无穷多个非零坐标 \(c_{n_k}\neq0\)，故 \(\hat c\notin\operatorname{im}\eta_C\)。
   - 然而在 \(C^\sharp\) 中计算 \(t\cdot c\)：对每个 \(k\ge1\)，\(t\cdot c_{n_k}=t^{\nu_{n_k}}+t^{\nu_{n_k}}S=0\)；其余坐标亦为 \(0\)。故 \(t\hat c=0\in\widehat C\)。
   - 对 \(\hat c\) 作用右逆 \(s\)：由 \(s\) 的线性性得 \(t\cdot s(\hat c)=s(t\hat c)=s(0)=0\in Q\)，即 \(s(\hat c)\in\operatorname{Ann}_Q(t)\)。由定理 2.3(1) 知 \(\operatorname{Ann}_Q(t)\subseteq\operatorname{im}j\)，故存在 \(y\in C\) 使得 \(s(\hat c)=j(y)\)。两边作用 \(p\) 得
     \[
     \hat c=p\bigl(s(\hat c)\bigr)=p\bigl(j(y)\bigr)=\eta_C(y)\in\operatorname{im}\eta_C,
     \]
     与 \(\hat c\notin\operatorname{im}\eta_C\) 矛盾！故当 \(\sup_{n\ge1}\nu_n=+\infty\) 时 \(p\) 不存在 \(S\) 线性右逆。\(\blacksquare\)

---

## 目标 3：商层诱导映射、\(\bigcap_{m\ge1}t^mQ\)、\(\widehat Q\) 与 \(\widehat E\)、以及 \(E\) 上的两种拓扑

### 3.1 诱导映射 \(\bar p_m:Q/t^mQ\to\widehat C/t^m\widehat C\) 与 \(\bigcap_{m\ge1}t^mQ\)

**定理 3.1.** 对任意非负整数列 \((\nu_n)_{n\ge1}\)：
1. 对每个 \(m\ge1\)，恒有 \(E\subseteq t^mQ\)，且由 \(p\) 诱导的映射
   \[
   \bar p_m:Q/t^mQ\longrightarrow\widehat C/t^m\widehat C,\qquad x+t^mQ\longmapsto p(x)+t^m\widehat C
   \]
   是 \(S/t^mS\) 模（及 \(R/t^mR\) 模）**同构**。此外，\(j\) 与 \(\eta_C\) 诱导的映射 \(\bar j_m:C/t^mC\to Q/t^mQ\) 与 \(\overline{\eta_C}_m:C/t^mC\to\widehat C/t^m\widehat C\) 也都是同构，且满足 \(\bar p_m\circ\bar j_m=\overline{\eta_C}_m\)（其逆为 \(\bar\pi_{C,m}:\widehat C/t^m\widehat C\xrightarrow{\sim}C/t^mC\)）。
2. 交集公式恒成立：
   \[
   \bigcap_{m\ge1}t^mQ=E.
   \]
   （特别地，\(Q\) 的 \(t\) 进拓扑分离当且仅当 \(E=0\)，即 \(\sup_{n\ge1}\nu_n<\infty\)。）

**证明.**  
1. 在 \(Q=\widehat B/\operatorname{im}\widehat\iota\) 中，\(t^mQ=(\operatorname{im}\widehat\iota+t^m\widehat B)/\operatorname{im}\widehat\iota\)。由定理 1.4(1) 知对一切 \(m\ge1\) 有
   \[
   \ker\widehat q=\overline{\operatorname{im}\widehat\iota}\subseteq\operatorname{im}\widehat\iota+t^m\widehat B,
   \]
   商去 \(\operatorname{im}\widehat\iota\) 即得 \(E=\ker\widehat q/\operatorname{im}\widehat\iota\subseteq t^mQ\)。  
   因 \(p:Q\to\widehat C\) 是满射且为 \(S\) 线性的，故 \(p(t^mQ)=t^m\widehat C\)，从而 \(\bar p_m\) 是满射；又若 \(p(x)\in t^m\widehat C=p(t^mQ)\)，则存在 \(y\in t^mQ\) 使 \(p(x)=p(y)\)，于是 \(x-y\in\ker p=E\subseteq t^mQ\)，得 \(x\in t^mQ\)，故 \(\bar p_m\) 是单射，即 \(\bar p_m\) 为同构。  
   进一步，投射 \(\pi_{C,m}:\widehat C\to C/t^mC\) 满足 \(\pi_{C,m}\circ\eta_C=(C\twoheadrightarrow C/t^mC)\)（从而 \(\pi_{C,m}\) 为满射），且由引理 1.3 知 \(\ker\pi_{C,m}=t^m\widehat C\)，故 \(\pi_{C,m}\) 诱导同构 \(\bar\pi_{C,m}:\widehat C/t^m\widehat C\xrightarrow{\sim}C/t^mC\)，其逆即为 \(\overline{\eta_C}_m\)；再由 \(\bar p_m\circ\bar j_m=\overline{\eta_C}_m\) 知 \(\bar j_m\) 亦为同构。
2. 由 (1) 已知 \(E\subseteq\bigcap_{m\ge1}t^mQ\)。反之，若 \(x\in\bigcap_{m\ge1}t^mQ\)，则对一切 \(m\ge1\) 有 \(p(x)\in p(t^mQ)=t^m\widehat C\)；由引理 1.3 知 \(p(x)\in\bigcap_{m\ge1}t^m\widehat C=0\)，故 \(x\in\ker p=E\)。因此 \(\bigcap_{m\ge1}t^mQ=E\)。\(\blacksquare\)

---

### 3.2 \(\widehat Q\)、典范映射 \(\eta_Q\) 以及 \(p\) 诱导的完成映射 \(\widehat p\)

**定理 3.2.** 对任意非负整数列 \((\nu_n)_{n\ge1}\)：
1. \(p\) 诱导的完成映射 \(\widehat p:\widehat Q\to\widehat{\widehat C}\) **恒为 \(S\) 模同构**。
2. \(\widehat C\) 的典范映射 \(\eta_{\widehat C}:\widehat C\to\widehat{\widehat C}\) **恒为 \(S\) 模同构**，其逆同构为
   \[
   \Theta_C:\widehat{\widehat C}\longrightarrow\widehat C,\qquad (y_m+t^m\widehat C)_{m\ge1}\longmapsto\bigl(\pi_{C,m}(y_m)\bigr)_{m\ge1}.
   \]
3. \(j:C\to Q\) 诱导的完成映射 \(\widehat j:\widehat C\to\widehat Q\) **恒为 \(S\) 模同构**，其逆同构为 \(\Psi_Q:=\Theta_C\circ\widehat p:\widehat Q\xrightarrow{\sim}\widehat C\)（显式地，\(\Psi_Q\bigl((x_m+t^mQ)_{m\ge1}\bigr)=\bigl(\pi_{C,m}(p(x_m))\bigr)_{m\ge1}\)），从而复合 \(\Phi_C^{-1}\circ\Psi_Q:\widehat Q\xrightarrow{\sim}C^\sharp\) 给出 \(\widehat Q\) 的具体坐标模型。
4. 在上述同构下，\(\eta_Q:Q\to\widehat Q\) 由恒等式
   \[
   \eta_Q=\widehat j\circ p\qquad\text{（等价地，}\Psi_Q\circ\eta_Q=p\text{）}
   \]
   完全确定。特别地，**\(\eta_Q:Q\to\widehat Q\) 恒为 \(S\) 线性满射，且 \(\ker\eta_Q=E\)**，诱导同构 \(Q/E\xrightarrow{\sim}\widehat Q\)；\(\eta_Q\) 为单射（从而为同构）当且仅当 \(\sup_{n\ge1}\nu_n<\infty\)。

**证明.**  
1. 对每个 \(m\ge1\)，\(\bar p_m:Q/t^mQ\to\widehat C/t^m\widehat C\) 与自然约化过渡映射可交换，且由定理 3.1(1) 知每个 \(\bar p_m\) 都是 \(S/t^mS\) 模同构。对逆向极限取 \(\widehat p=\varprojlim_{m\ge1}\bar p_m\)，即得 \(\widehat p:\widehat Q\xrightarrow{\sim}\widehat{\widehat C}\) 是 \(S\) 模同构。
2. 由定理 3.1(1) 的证明，对每个 \(m\ge1\)，\(\bar\pi_{C,m}:\widehat C/t^m\widehat C\xrightarrow{\sim}C/t^mC\) 是 \(S/t^mS\) 模同构，且与 \(m+1\to m\) 的自然约化相容（因 \(\pi_{C,m}(y)\) 恰为记录 \(y\in\widehat C\) 的第 \(m\) 分量）。对 \(m\ge1\) 取逆向极限即得 \(S\) 模同构 \(\Theta_C:=\varprojlim_{m\ge1}\bar\pi_{C,m}:\widehat{\widehat C}\xrightarrow{\sim}\widehat C\)。对任意 \(y\in\widehat C\)，有
   \[
   (\Theta_C\circ\eta_{\widehat C})(y)=\Theta_C\bigl((y+t^m\widehat C)_{m\ge1}\bigr)=\bigl(\pi_{C,m}(y)\bigr)_{m\ge1}=y,
   \]
   故 \(\Theta_C\circ\eta_{\widehat C}=\operatorname{id}_{\widehat C}\)，从而 \(\eta_{\widehat C}=\Theta_C^{-1}\) 是 \(S\) 模同构。
3. 同理，因每个 \(\bar j_m:C/t^mC\to Q/t^mQ\) 为 \(S/t^mS\) 模同构且满足 \(\bar\pi_{C,m}\circ\bar p_m\circ\bar j_m=\operatorname{id}_{C/t^mC}\)，取逆向极限得 \(\widehat j:\widehat C\xrightarrow{\sim}\widehat Q\) 为 \(S\) 模同构，且 \(\Theta_C\circ\widehat p\circ\widehat j=\operatorname{id}_{\widehat C}\)，故 \(\widehat j^{-1}=\Theta_C\circ\widehat p=\Psi_Q\)。
4. 由完成函子的自然性，交换图 \(p:Q\to\widehat C\) 给出 \(\widehat p\circ\eta_Q=\eta_{\widehat C}\circ p\)。左乘 \(\Theta_C=\eta_{\widehat C}^{-1}\) 得 \(\Psi_Q\circ\eta_Q=p\)，再左乘 \(\widehat j=\Psi_Q^{-1}\) 得 \(\eta_Q=\widehat j\circ p\)。因 \(p\) 恒为满射、\(\ker p=E\) 且 \(\widehat j\) 为同构，故 \(\eta_Q\) 恒为满射且 \(\ker\eta_Q=E\)（这与 \(\ker\eta_Q=\bigcap_{m\ge1}t^mQ=E\) 完全一致）；\(\eta_Q\) 为单射当且仅当 \(E=0\iff\sup_{n\ge1}\nu_n<\infty\)。\(\blacksquare\)

---

### 3.3 \(\widehat E\) 与典范映射 \(\eta_E:E\to\widehat E\)

接下来在坐标模型 \(E^\sharp=A^\flat/A^\sharp\) 中计算 \(t^mE\)、\(E/t^mE\) 与 \(\widehat E\)。

**引理 3.3.** 对每个 \(m\ge1\)，在 \(A^\flat\) 中有
\[
t^mA^\flat+A^\sharp=\Bigl\{(a_n)_{n\ge1}\in A^\flat:\#\{n\ge1:v_t(a_n)<m\}<\infty\Bigr\}.
\]
并且有 \(S/t^mS\) 模同构
\[
E^\sharp/t^mE^\sharp\cong\frac{\bigl\{(u_n)_{n\ge1}\in\prod_{n\ge1}S/t^mS:\forall L\ge0,\ \#\{n\ge1:\nu_n\le L\text{ 且 }u_n\neq0\}<\infty\bigr\}}{\bigoplus_{n\ge1}S/t^mS},
\]
由 \((a_n)_{n\ge1}+t^mA^\flat+A^\sharp\mapsto(a_n+t^mS)_{n\ge1}+\bigoplus_{n\ge1}S/t^mS\) 给出。

**证明.**  
若 \(a=t^md+u\)（\(d\in A^\flat\)，\(u\in A^\sharp\)），则因 \(u\in A^\sharp\)，存在 \(N\ge0\) 使得当 \(n>N\) 时 \(v_t(u_n)\ge m\)，从而 \(v_t(a_n)=v_t(t^md_n+u_n)\ge m\)，即 \(\{n\ge1:v_t(a_n)<m\}\) 有限。  
反之，设 \(a=(a_n)_{n\ge1}\in A^\flat\) 且存在 \(N\ge0\) 使得对一切 \(n>N\) 有 \(v_t(a_n)\ge m\)。对 \(n>N\) 写 \(a_n=t^md_n\)（\(d_n\in S\)），则 \(\nu_n+v_t(d_n)=\nu_n+v_t(a_n)-m\to+\infty\)；对 \(1\le n\le N\) 置 \(d_n:=0\)，并置 \(u:=(a_1,\dots,a_N,0,0,\dots)\in\bigoplus_{n\ge1}S\subseteq A^\sharp\)。则 \(d=(d_n)_{n\ge1}\in A^\flat\) 且 \(a=t^md+u\in t^mA^\flat+A^\sharp\)，第一式得证。  
对第二式，映射 \(\rho_m:A^\flat\to\prod_{n\ge1}S/t^mS\)，\((a_n)\mapsto(a_n+t^mS)\) 的原像满足 \(\rho_m(a)\in\bigoplus_{n\ge1}S/t^mS\iff\#\{n:v_t(a_n)<m\}<\infty\iff a\in t^mA^\flat+A^\sharp\)。对任意 \(a\in A^\flat\) 及 \(L\ge0\)，若 \(\nu_n\le L\) 且 \(a_n+t^mS\neq0\)（即 \(v_t(a_n)<m\)），则 \(\nu_n+v_t(a_n)<L+m\)，此类 \(n\) 仅有有限个；反之，若 \((u_n)_{n\ge1}\in\prod_{n\ge1}S/t^mS\) 满足对每个 \(L\ge0\) 仅有有限个 \(n\) 使 \(\nu_n\le L\) 且 \(u_n\neq0\)，取其典范多项式提升 \(\tilde u_n\in k[t]_{<m}\)，则对任意 \(M\ge1\)，\(\nu_n+v_t(\tilde u_n)<M\) 蕴含 \(u_n\neq0\) 且 \(\nu_n<M\)，故仅有有限个此类 \(n\)，即 \((\tilde u_n)_{n\ge1}\in A^\flat\) 且 \(\rho_m((\tilde u_n))=(u_n)\)。由第一同构定理即得第二式。\(\blacksquare\)

**定理 3.4（\(\widehat E\) 与 \(\eta_E\)）.** 对任意非负整数列 \((\nu_n)_{n\ge1}\)：
1. \(\bigcap_{m\ge1}t^mE=0\)。
2. 典范映射 \(\eta_E:E\to\widehat E\) **恒为 \(S\) 模同构**（即 \(E\) 自身关于 \(t\) 进拓扑恒既分离又完备）。通过复合
   \[
   E^\sharp\xrightarrow[\;\sim\;]{\Phi_E}E\xrightarrow[\;\sim\;]{\eta_E}\widehat E,
   \]
   \(\widehat E\) 的具体坐标模型即为 \(E^\sharp=A^\flat/A^\sharp\)，其中 \((a_n)_{n\ge1}+A^\sharp\) 对应于相容商记录 \(\bigl(\Phi_E((a_n)+A^\sharp)+t^mE\bigr)_{m\ge1}\)。

**证明.**  
因 \(\Phi_E:E^\sharp\xrightarrow{\sim}E\) 是 \(S\) 模同构，只需对 \(E^\sharp\) 证明 \(\bigcap_{m\ge1}t^mE^\sharp=0\) 且 \(\eta_{E^\sharp}:E^\sharp\to\widehat{E^\sharp}\) 是满射（由预备节第 2 条，\(\eta_E\) 自动是 \(S\) 线性的）。
1. **单射性（分离性）：** 设 \(a+A^\sharp\in\bigcap_{m\ge1}t^mE^\sharp\)（\(a=(a_n)_{n\ge1}\in A^\flat\)）。由引理 3.3，对每个 \(m\ge1\) 集合 \(\{n\ge1:v_t(a_n)<m\}\) 都是有限集，这意味着 \(\lim_{n\to\infty}v_t(a_n)=+\infty\)，即 \(a\in A^\sharp\)，故 \(a+A^\sharp=0\in E^\sharp\)。因此 \(\bigcap_{m\ge1}t^mE^\sharp=0\)，\(\eta_{E^\sharp}\) 恒为单射。
2. **满射性（完备性）：** 任取相容商记录 \((\bar x^{(m)})_{m\ge1}\in\widehat{E^\sharp}=\varprojlim_{m\ge1}E^\sharp/t^mE^\sharp\)。对每个 \(m\ge1\)，选代表元 \(y^{(m)}\in A^\flat\) 使 \(\bar x^{(m)}=(y^{(m)}+A^\sharp)+t^mE^\sharp\)。由相容性知 \(y^{(m+1)}-y^{(m)}\in t^mA^\flat+A^\sharp\)，故存在 \(d^{(m)}=(d^{(m)}_n)_{n\ge1}\in A^\flat\) 使得
   \[
   y^{(m+1)}-y^{(m)}\equiv t^md^{(m)}\pmod{A^\sharp}\qquad(\forall m\ge1).
   \]
   对每个 \(m\ge1\)，因 \(d^{(m)}\in A^\flat\)，有 \(\lim_{n\to\infty}(\nu_n+v_t(d^{(m)}_n))=+\infty\)，故可选取正整数 \(N_m\ge m\) 使得
   \[
   \forall n>N_m,\qquad \nu_n+v_t\bigl(d^{(m)}_n\bigr)\ge m.
   \]
   定义截断列 \(\tilde d^{(m)}=(\tilde d^{(m)}_n)_{n\ge1}\in A^\flat\) 为：当 \(1\le n\le N_m\) 时 \(\tilde d^{(m)}_n:=0\)，当 \(n>N_m\) 时 \(\tilde d^{(m)}_n:=d^{(m)}_n\)。因 \(d^{(m)}-\tilde d^{(m)}\) 仅有有限个非零坐标，故 \(d^{(m)}-\tilde d^{(m)}\in A^\sharp\)，从而仍有
   \[
   y^{(m+1)}-y^{(m)}\equiv t^m\tilde d^{(m)}\pmod{A^\sharp},\qquad
   y^{(K)}\equiv y^{(1)}+\sum_{m=1}^{K-1}t^m\tilde d^{(m)}\pmod{A^\sharp}\quad(\forall K\ge1).
   \]
   对每个固定的坐标指标 \(n\ge1\)，当 \(m\ge n\) 时必有 \(n\le m\le N_m\)，故 \(\tilde d^{(m)}_n=0\)。因此，对每个 \(K\ge1\) 及每个 \(n\ge1\)，尾和
   \[
   w^{(K)}_n:=\sum_{m=K}^\infty t^{m-K}\tilde d^{(m)}_n\in S
   \]
   实际上只是有限和（仅 \(m<n\) 的项可能非零）。我们来验证对每个 \(K\ge1\) 都有 \(w^{(K)}:=(w^{(K)}_n)_{n\ge1}\in A^\flat\)：  
   任取 \(M\ge1\)，将和式在 \(m=K+M\) 处拆开：
   \[
   w^{(K)}_n=\sum_{m=K}^{K+M-1}t^{m-K}\tilde d^{(m)}_n+\sum_{m\ge K+M}t^{m-K}\tilde d^{(m)}_n.
   \]
   - 对任意 \(m\ge K+M\) 及任意 \(n\ge1\)：若 \(n\le N_m\) 则 \(\tilde d^{(m)}_n=0\)；若 \(n>N_m\)，由 \(N_m\) 的取法有
     \[
     \nu_n+v_t\bigl(t^{m-K}\tilde d^{(m)}_n\bigr)=\nu_n+v_t\bigl(\tilde d^{(m)}_n\bigr)+(m-K)\ge m+M\ge K+2M>M.
     \]
     故对一切 \(n\ge1\)，第二部分满足 \(\nu_n+v_t\bigl(\sum_{m\ge K+M}t^{m-K}\tilde d^{(m)}_n\bigr)>M\)。
   - 第一部分 \(\sum_{m=K}^{K+M-1}t^{m-K}\tilde d^{(m)}\) 是 \(A^\flat\) 中有限个元素之和，故属于 \(A^\flat\)，存在 \(N^*\ge1\) 使得当 \(n>N^*\) 时其第 \(n\) 坐标满足 \(\nu_n+v_t(\cdots)\ge M\)。
   
   合并两部分知当 \(n>N^*\) 时 \(\nu_n+v_t(w^{(K)}_n)\ge M\)。由 \(M\) 的任意性得 \(w^{(K)}\in A^\flat\)（\(\forall K\ge1\)）。  
   现置 \(a:=y^{(1)}+tw^{(1)}\in A^\flat\)（逐坐标即为有限和 \(a_n=y^{(1)}_n+\sum_{m=1}^\infty t^m\tilde d^{(m)}_n\)）。对每个 \(K\ge1\)，有
   \[
   a-y^{(K)}=\Bigl(y^{(1)}+\sum_{m=1}^{K-1}t^m\tilde d^{(m)}-y^{(K)}\Bigr)+t^Kw^{(K)}\in A^\sharp+t^KA^\flat,
   \]
   故在 \(E^\sharp\) 中 \((a+A^\sharp)-(y^{(K)}+A^\sharp)\in t^KE^\sharp\)，即 \(\eta_{E^\sharp}(a+A^\sharp)=(\bar x^{(K)})_{K\ge1}\)。因此 \(\eta_{E^\sharp}\) 恒为同构。\(\blacksquare\)

---

### 3.4 \(E\) 自身的 \(t\) 进拓扑与从 \(Q\) 继承的子空间拓扑的比较

记 \(\mathcal{T}_E\) 为 \(E\) 自身的 \(t\) 进拓扑（以 \(\{t^mE\}_{m\ge1}\) 为零点邻域基），\(\mathcal{T}_{Q|_E}\) 为 \(E\) 从 \(Q\) 的 \(t\) 进拓扑继承的子空间拓扑（以 \(\{E\cap t^mQ\}_{m\ge1}\) 为零点邻域基）。

**定理 3.5.** 对任意非负整数列 \((\nu_n)_{n\ge1}\)：
1. **自身拓扑的分离性：** 由定理 3.4(1) 知 \(\bigcap_{m\ge1}t^mE=0\)，故 \(E\) 自身的 \(t\) 进拓扑 \(\mathcal{T}_E\) **恒为分离拓扑（Hausdorff 拓扑）**（且由定理 3.4(2) 恒完备）。
2. **子空间拓扑的形态与强弱比较：** 由定理 3.1(2) 知 \(E=\bigcap_{m\ge1}t^mQ\)，故对每个 \(m\ge1\) 都有 \(E\cap t^mQ=E\)。因此子空间拓扑 \(\mathcal{T}_{Q|_E}=\{\emptyset,E\}\) **恒为密着拓扑（平凡拓扑）**。特别地，因 \(t^mE\subseteq E=E\cap t^mQ\)（\(\forall m\ge1\)），恒有 \(\mathcal{T}_{Q|_E}\subseteq\mathcal{T}_E\)，即 \(\mathcal{T}_E\) 总比 \(\mathcal{T}_{Q|_E}\) 更细（或相等）。
3. **两种拓扑相同的充要条件：** \(\mathcal{T}_E=\mathcal{T}_{Q|_E}\) 当且仅当指数列 \((\nu_n)_{n\ge1}\) 有界（即 \(\sup_{n\ge1}\nu_n<\infty\)）。
   - 当 \(\sup_{n\ge1}\nu_n<\infty\) 时，\(E=0\)，两种拓扑同为零模上的唯一拓扑；
   - 当 \(\sup_{n\ge1}\nu_n=+\infty\) 时，\(E\neq0\)，\(\mathcal{T}_E\) 是非离散的分离拓扑（因 \(E\) 无挠且 \(E\neq0\)，对一切 \(m\ge1\) 有 \(0\neq t^{m+1}E\subsetneq t^mE\)），严格细于密着拓扑 \(\mathcal{T}_{Q|_E}=\{\emptyset,E\}\)。

**证明.**  
(1) 与 (2) 已由定理 3.4(1) 与定理 3.1(2) 直接给出。对 (3)：在平移不变拓扑群 \(E\) 中，\(\mathcal{T}_E=\mathcal{T}_{Q|_E}=\{\emptyset,E\}\) 当且仅当零点邻域基中每个开子群 \(t^mE\) 包含 \(E\)（即 \(\forall m\ge1,\ t^mE=E\)），这等价于 \(E=\bigcap_{m\ge1}t^mE\)。结合 \(\bigcap_{m\ge1}t^mE=0\) 得 \(\mathcal{T}_E=\mathcal{T}_{Q|_E}\iff E=0\)。再由定理 2.4(2) 知 \(E=0\iff\sup_{n\ge1}\nu_n<\infty\)。（此外当 \(E\neq0\) 时，由定理 2.3(2) 知乘 \(t^m\) 在 \(E\) 上单射，故 \(t^mE\cong E\neq0\)；若存在 \(m\ge1\) 使 \(t^{m+1}E=t^mE\)，消去 \(t^m\) 得 \(tE=E\)，从而 \(E=\bigcap_{k\ge1}t^kE=0\)，矛盾，故 \(0\neq t^{m+1}E\subsetneq t^mE\)。）\(\blacksquare\)
