下面针对任意域 $k$ 及任意非负整数列 $(\nu_n)_{n\ge 1}$，完整构造并证明所要求的全部结论。

---

### 预备记号与 $S$-模结构说明

- 记 $v_t: S \to \mathbb{Z}_{\ge 0}\cup\{+\infty\}$ 为 $t$-进赋值（约定 $v_t(0)=+\infty$，对非零 $u=\sum_{j\ge 0}u_j t^j\in S$ 有 $v_t(u)=\min\{j\ge 0: u_j\neq 0\}$）。对任意 $m\ge 1$，有 $u\in t^m S \iff v_t(u)\ge m$。
- 自然包含 $R=k[t]\hookrightarrow k[[t]]=S$ 对每个 $m\ge 1$ 诱导环同构
  $$R/t^m R \xrightarrow{\;\sim\;} S/t^m S.$$
  由此，对任意 $R$-模 $M$，商模 $M/t^m M$ 具有唯一的相容 $S/(t^m)$-模结构：若 $s=\sum_{j\ge 0} c_j t^j\in S$，记 $s_{<m}=\sum_{j=0}^{m-1}c_j t^j\in R$，则 $s\cdot (x+t^m M)=s_{<m}x+t^m M$。因 $s_{<m+1}-s_{<m}\in t^m R$，自然约化映射 $M/t^{m+1}M\to M/t^m M$ 是 $S$-线性的，从而 $\widehat M=\varprojlim_{m\ge 1}M/t^m M$ 成为 $S$-模。
- 任意 $R$-线性映射 $f:M\to N$ 满足 $f(t^m M)\subseteq t^m N$，故在每层诱导 $S/(t^m)$-线性映射 $f_m:M/t^m M\to N/t^m N$，从而 $\widehat f:\widehat M\to\widehat N$ 是 $S$-线性的；此外若 $N$ 本身已是 $S$-模（例如 $\widehat C,Q,E$），则 $(s-s_{<m})N\subseteq t^m N$，因此典范映射 $\eta_N:N\to\widehat N$ 也是 $S$-线性的。
- 若无歧义，对 $R/t^m R\cong S/t^m S$ 与 $R/(t^{\nu})\cong S/(t^{\nu})$（$\nu\ge 0$）作典范等同（当 $\nu=0$ 时，约定 $t^0=1$，$R/(t^0)=S/(t^0)=0$）。

---

## 目标 1：$\widehat A,\widehat B,\widehat C$ 的坐标模型、诱导映射、正合性、闭包与纤维

### 1.1 坐标模型与相容商记录之间的同构

定义 $S$-子模 $\mathcal A,\mathcal B\subseteq \prod_{n\ge 1} S$（记为同一坐标模型，仅下标基元分别对应 $(f_n)$ 与 $(e_n)$）：
$$\mathcal A=\mathcal B:=c_0(\mathbb N,S)=\left\{(b_n)_{n\ge 1}\in\prod_{n\ge 1}S \;\middle|\; \forall m\ge 1,\; b_n\in t^m S \text{ 对充分大的 } n \text{ 成立}\right\},$$
等价地（写 $b_n=\sum_{j\ge 0}b_{n,j}t^j$），$\lim_{n\to\infty}v_t(b_n)=+\infty$，也即对每个 $j\ge 0$，仅有限个 $n\ge 1$ 满足 $b_{n,j}\neq 0$。

对 $C$，由于 $\iota(f_n)=t^{\nu_n}e_n$，映射 $\sum_{n\ge 1} r_n e_n\mapsto (r_n \bmod t^{\nu_n})_{n\ge 1}$ 诱导 $R$-模同构
$$C=B/\iota(A)\xrightarrow{\;\sim\;}\bigoplus_{n\ge 1} R/(t^{\nu_n})\cong \bigoplus_{n\ge 1} S/(t^{\nu_n}).$$
定义 $S$-子模 $\mathcal C\subseteq \prod_{n\ge 1} S/(t^{\nu_n})$ 为
$$\mathcal C:=\left\{(c_n)_{n\ge 1}\in\prod_{n\ge 1} S/(t^{\nu_n}) \;\middle|\; \forall m\ge 1,\; c_n\in t^m\bigl(S/(t^{\nu_n})\bigr) \text{ 对充分大的 } n \text{ 成立}\right\}.$$
若将每个 $c_n\in S/(t^{\nu_n})$ 唯一写成次数 $<\nu_n$ 的多项式代表 $\sum_{0\le j<\nu_n} c_{n,j}t^j$（$\nu_n=0$ 时为空和 $0$），注意当 $\nu_n\le m$ 时 $t^m(S/(t^{\nu_n}))=0$，而当 $\nu_n>m$ 时 $c_n\in t^m(S/(t^{\nu_n}))\iff c_{n,0}=\cdots=c_{n,m-1}=0$，故
$$c\in\mathcal C \;\Longleftrightarrow\; \forall m\ge 1,\; c_{n,j}=0\text{ 对所有 }0\le j<\min(\nu_n,m)\text{ 在 }n\gg 0\text{ 时成立} \;\Longleftrightarrow\; \forall j\ge 0,\; \{n\ge 1:\nu_n>j\text{ 且 }c_{n,j}\neq 0\}\text{ 有限}.$$

**同构的构造与证明：**

1. **$\Phi_B:\mathcal B\xrightarrow{\;\sim\;}\widehat B$（及 $\Phi_A:\mathcal A\xrightarrow{\;\sim\;}\widehat A$）：**
   对每个 $m\ge 1$，有自然等同 $B/t^m B \cong \bigoplus_{n\ge 1}(R/t^m R)\overline{e_n}\cong \bigoplus_{n\ge 1}S/t^m S$。对 $b=(b_n)_{n\ge 1}\in\mathcal B$，由于 $b_n\bmod t^m S$ 仅对有限个 $n$ 非零，故
   $$\Phi_{B,m}(b):=(b_n\bmod t^m S)_{n\ge 1}\in\bigoplus_{n\ge 1}S/t^m S \cong B/t^m B$$
   良定义，且显然满足 $\pi_{m+1,m}(\Phi_{B,m+1}(b))=\Phi_{B,m}(b)$。于是 $\Phi_B(b):=(\Phi_{B,m}(b))_{m\ge 1}\in\widehat B$。
   - **$S$-线性**：对任意 $s\in S$，在第 $m$ 层有 $(sb_n)\bmod t^m S = (s\bmod t^m S)(b_n\bmod t^m S)$，即 $\Phi_{B,m}(sb)=s\cdot\Phi_{B,m}(b)$。
   - **单性**：若 $\Phi_B(b)=0$，则对一切 $m,n\ge 1$ 有 $b_n\in t^m S$，故 $b_n\in\bigcap_{m\ge 1}t^m S=0$，即 $b=0$。
   - **满性**：任取相容商记录 $x=(x_m)_{m\ge 1}\in\widehat B$，在第 $m$ 层写作 $x_m=(x_{m,n})_{n\ge 1}\in\bigoplus_{n\ge 1}S/t^m S$。对每个固定的 $n\ge 1$，相容性 $x_{m+1,n}\bmod t^m S=x_{m,n}$ 给出 $(x_{m,n})_{m\ge 1}\in\varprojlim_{m\ge 1}S/t^m S=S$，从而存在唯一的 $b_n\in S$ 使 $b_n\bmod t^m S=x_{m,n}$ 对所有 $m\ge 1$ 成立。对任意固定 $m\ge 1$，由 $x_m\in\bigoplus_{n\ge 1}S/t^m S$ 知对充分大的 $n$ 有 $x_{m,n}=0$，即 $b_n\in t^m S$。故 $b=(b_n)_{n\ge 1}\in\mathcal B$ 且 $\Phi_B(b)=x$。

   同理得 $S$-模同构 $\Phi_A:\mathcal A\xrightarrow{\sim}\widehat A$。在此等同下，$\eta_A,\eta_B$ 分别对应有限支撑元 $\bigoplus_{n\ge 1} R\hookrightarrow \mathcal A,\mathcal B$ 的自然包含。

2. **$\Phi_C:\mathcal C\xrightarrow{\;\sim\;}\widehat C$：**
   对每个 $m\ge 1$，
   $$C/t^m C \cong \bigoplus_{n\ge 1} R/(t^{\nu_n},t^m) = \bigoplus_{n\ge 1} R/(t^{\min(\nu_n,m)})\cong \bigoplus_{n\ge 1} S/(t^{\min(\nu_n,m)}).$$
   典范满射 $S/(t^{\nu_n})\to S/(t^{\min(\nu_n,m)})$ 的核恰为 $t^m(S/(t^{\nu_n}))$（当 $m\ge\nu_n$ 时两者均为 $0$；当 $m<\nu_n$ 时两者均为 $t^m S/t^{\nu_n}S$）。于是对 $c=(c_n)_{n\ge 1}\in\mathcal C$，取
   $$\Phi_{C,m}(c):=(c_n\bmod t^{\min(\nu_n,m)})_{n\ge 1}\in \bigoplus_{n\ge 1} S/(t^{\min(\nu_n,m)})\cong C/t^m C,$$
   由于对充分大的 $n$ 有 $c_n\in t^m(S/(t^{\nu_n}))$，该序列仅有有限项非零，且关于 $m$ 相容，从而定义 $S$-线性映射 $\Phi_C:\mathcal C\to\widehat C$。
   - **单性**：若 $\Phi_C(c)=0$，对每个 $n\ge 1$：若 $\nu_n=0$ 则 $c_n\in S/(t^0)=0$；若 $\nu_n\ge 1$ 则取 $m=\nu_n$ 得 $\min(\nu_n,m)=\nu_n$，故 $c_n=\Phi_{C,\nu_n}(c)_n=0$。因此 $c=0$。
   - **满性**：任取相容商记录 $y=(y_m)_{m\ge 1}\in\widehat C$，写作 $y_m=(y_{m,n})_{n\ge 1}\in\bigoplus_{n\ge 1}S/(t^{\min(\nu_n,m)})$。对每个 $n\ge 1$，若 $\nu_n=0$ 令 $c_n=0\in S/(t^0)$；若 $\nu_n\ge 1$ 令 $c_n:=y_{\nu_n,n}\in S/(t^{\nu_n})$。
     - 当 $m\le\nu_n$ 时，由 $y_{\nu_n}$ 到 $y_m$ 的相容性得 $c_n\bmod t^{\min(\nu_n,m)}=y_{\nu_n,n}\bmod t^m=y_{m,n}$；
     - 当 $m>\nu_n$ 时，$\min(\nu_n,m)=\nu_n$，由 $y_m$ 到 $y_{\nu_n}$ 的相容性得 $y_{m,n}=y_{\nu_n,n}=c_n=c_n\bmod t^{\min(\nu_n,m)}$。
     对任意固定 $m\ge 1$，因 $y_{m,n}=0$ 对充分大的 $n$ 成立，故 $c_n\in \ker\bigl(S/(t^{\nu_n})\to S/(t^{\min(\nu_n,m)})\bigr)=t^m(S/(t^{\nu_n}))$ 对充分大的 $n$ 成立。从而 $c=(c_n)_{n\ge 1}\in\mathcal C$ 且 $\Phi_C(c)=y$。

   在此等同下，$\eta_C:C\to\widehat C$ 对应 $\bigoplus_{n\ge 1}R/(t^{\nu_n})\hookrightarrow \mathcal C$ 的自然包含（利用 $R/(t^{\nu_n})\cong S/(t^{\nu_n})$）。

### 1.2 诱导映射 $\widehat\iota$ 与 $\widehat q$

在每层 $m\ge 1$，$\iota$ 与 $q$ 诱导的映射分别为
$$\iota_m\bigl((a_n\bmod t^m)_{n\ge 1}\bigr)=\bigl(t^{\nu_n}a_n\bmod t^m\bigr)_{n\ge 1},\qquad q_m\bigl((b_n\bmod t^m)_{n\ge 1}\bigr)=\bigl(b_n\bmod t^{\min(\nu_n,m)}\bigr)_{n\ge 1}.$$
从而在同构 $\Phi_A,\Phi_B,\Phi_C$ 下，诱导映射 $\widehat\iota:\mathcal A\to\mathcal B$ 与 $\widehat q:\mathcal B\to\mathcal C$ 为
$$\widehat\iota\bigl((a_n)_{n\ge 1}\bigr)=(t^{\nu_n}a_n)_{n\ge 1},\qquad \widehat q\bigl((b_n)_{n\ge 1}\bigr)=(b_n\bmod t^{\nu_n})_{n\ge 1}.$$

### 1.3 完成列在各处的正合性与短正合充要条件

考察完成列
$$0\longrightarrow \widehat A\xrightarrow{\;\widehat\iota\;}\widehat B\xrightarrow{\;\widehat q\;}\widehat C\longrightarrow 0.$$

1. **$\widehat A$ 处的正合性（$\widehat\iota$ 恒为单射）**：
   若 $\widehat\iota((a_n)_{n\ge 1})=(t^{\nu_n}a_n)_{n\ge 1}=0$，由于 $S$ 为整环且 $t^{\nu_n}\neq 0$（包含 $\nu_n=0$ 时 $t^0=1\neq 0$），必有 $a_n=0$ 对一切 $n\ge 1$ 成立。故 $\widehat\iota$ 恒单，完成列在 $\widehat A$ 处**恒正合**。

2. **$\widehat C$ 处的正合性（$\widehat q$ 恒为满射）**：
   任取 $c=(c_n)_{n\ge 1}\in\mathcal C$。对每个 $n\ge 1$，取 $c_n\in S/(t^{\nu_n})$ 的唯一次数 $<\nu_n$ 的多项式代表 $b_n^{(0)}=\sum_{0\le j<\nu_n} c_{n,j}t^j\in R\subseteq S$（当 $\nu_n=0$ 或 $c_n=0$ 时取 $b_n^{(0)}=0$）。对任意 $m\ge 1$，因 $c\in\mathcal C$，对充分大的 $n$ 有 $c_n\in t^m(S/(t^{\nu_n}))$：
   - 若 $\nu_n\le m$，则 $c_n=0$，从而 $b_n^{(0)}=0\in t^m S$；
   - 若 $\nu_n>m$，则 $c_{n,0}=\cdots=c_{n,m-1}=0$，从而 $b_n^{(0)}=\sum_{j=m}^{\nu_n-1}c_{n,j}t^j\in t^m S$。
   故 $b^{(0)}(c):=(b_n^{(0)})_{n\ge 1}\in\mathcal B$，且显然 $\widehat q(b^{(0)}(c))=c$。因此 $\widehat q$ 恒满，完成列在 $\widehat C$ 处**恒正合**。

3. **$\widehat B$ 处的正合性及短正合充要条件**：
   在坐标模型 $\mathcal B$ 中，
   $$\ker\widehat q=\left\{(b_n)_{n\ge 1}\in\mathcal B \;\middle|\; \forall n\ge 1,\; b_n\in t^{\nu_n} S\right\},$$
   而 $\operatorname{im}\widehat\iota=\{(t^{\nu_n}a_n)_{n\ge 1}\mid (a_n)_{n\ge 1}\in\mathcal A\}\subseteq\ker\widehat q$。
   **命题**：$\operatorname{im}\widehat\iota=\ker\widehat q$（从而完成列在 $\widehat B$ 处正合，即完成列短正合）**当且仅当序列 $(\nu_n)_{n\ge 1}$ 有界**（即 $\sup_{n\ge 1}\nu_n<\infty$）。
   **证明**：
   - **充分性**：设存在 $N\in\mathbb Z_{\ge 0}$ 使 $\nu_n\le N$ 对所有 $n\ge 1$ 成立。任取 $b=(b_n)_{n\ge 1}\in\ker\widehat q$，因 $b_n\in t^{\nu_n}S$ 且 $S$ 为整环，存在唯一的 $a_n\in S$ 使 $b_n=t^{\nu_n}a_n$。对任意 $m\ge 1$，因 $b\in\mathcal B$，对充分大的 $n$ 有 $b_n\in t^{N+m}S\subseteq t^{\nu_n+m}S$，从而 $a_n\in t^m S$。于是 $a=(a_n)_{n\ge 1}\in\mathcal A$ 且 $b=\widehat\iota(a)\in\operatorname{im}\widehat\iota$。
   - **必要性**：反设 $(\nu_n)_{n\ge 1}$ 无界。则可归纳选取严格递增指标列 $1\le n_1<n_2<\cdots$ 使 $\nu_{n_k}\ge k$ 对所有 $k\ge 1$ 成立。定义 $b=(b_n)_{n\ge 1}\in\prod_{n\ge 1}S$ 为
     $$b_{n_k}=t^{\nu_{n_k}}\quad(k\ge 1),\qquad b_n=0\quad(n\notin\{n_k\}_{k\ge 1}).$$
     对任意 $m\ge 1$，当 $k\ge m$ 时有 $v_t(b_{n_k})=\nu_{n_k}\ge k\ge m$，故 $b\in\mathcal B$；又显然 $b_n\in t^{\nu_n}S$ 对一切 $n$ 成立，故 $b\in\ker\widehat q$。若 $b=\widehat\iota(a)$ 对某个 $a=(a_n)_{n\ge 1}\in\mathcal A$ 成立，则由 $t^{\nu_{n_k}}a_{n_k}=t^{\nu_{n_k}}$ 得 $a_{n_k}=1\notin tS$ 对无穷多个 $n_k$ 成立，与 $a\in\mathcal A$ 矛盾。故 $\operatorname{im}\widehat\iota\subsetneq\ker\widehat q$。$\square$

### 1.4 $\widehat B$（及 $\widehat C$）的拓扑与 $\operatorname{im}\widehat\iota$ 在 $\widehat B$ 中的闭包

先说明 $\widehat B$ 上的 $t$-进拓扑与逆向极限拓扑完全一致（并对 $\widehat C$ 验证同样性质，供后续使用）：

**引理 1.1**：对每个 $m\ge 1$，典范投影 $\pi_{B,m}:\widehat B\to B/t^m B$ 与 $\pi_{C,m}:\widehat C\to C/t^m C$ 均为满射，且其核分别为
$$\ker\pi_{B,m}=t^m\widehat B,\qquad \ker\pi_{C,m}=t^m\widehat C.$$
特别地，$\widehat B$（以及 $\widehat C$）是 $t$-进分离的：$\bigcap_{m\ge 1}t^m\widehat B=0$ 且 $\bigcap_{m\ge 1}t^m\widehat C=0$。

**证明**：满性由 $\pi_{B,m}\circ\eta_B$ 与 $\pi_{C,m}\circ\eta_C$ 分别为商映射 $B\to B/t^m B$ 与 $C\to C/t^m C$ 即得。显然 $t^m\widehat B\subseteq\ker\pi_{B,m}$ 与 $t^m\widehat C\subseteq\ker\pi_{C,m}$。
- 在 $\mathcal B$ 中，若 $b=(b_n)_{n\ge 1}\in\ker\pi_{B,m}$，则 $b_n\in t^m S$ 对一切 $n\ge 1$ 成立。写 $b_n=t^m b'_n$（$b'_n\in S$），对任意 $r\ge 1$，因 $n\gg 0$ 时 $b_n\in t^{m+r}S$，故 $b'_n\in t^r S$，从而 $b'=(b'_n)_{n\ge 1}\in\mathcal B$ 且 $b=t^m b'\in t^m\mathcal B$。故 $\ker\pi_{B,m}=t^m\widehat B$，进而 $\bigcap_{m\ge 1}t^m\widehat B=\bigcap_{m\ge 1}\ker\pi_{B,m}=0$。
- 在 $\mathcal C$ 中，若 $c=(c_n)_{n\ge 1}\in\ker\pi_{C,m}$，则对一切 $n\ge 1$ 有 $c_n\in t^m(S/(t^{\nu_n}))$。若 $\nu_n\le m$，则 $c_n=0$，置 $c'_n=0$；若 $\nu_n>m$，写 $c_n$ 的唯一次数 $<\nu_n$ 代表为 $\sum_{j=m}^{\nu_n-1}c_{n,j}t^j$，置 $c'_n=\sum_{i=0}^{\nu_n-m-1}c_{n,i+m}t^i\bmod t^{\nu_n}\in S/(t^{\nu_n})$，则 $t^m c'_n=c_n$。对任意 $r\ge 1$，取 $N$ 使 $n>N$ 时 $c_n\in t^{m+r}(S/(t^{\nu_n}))$：对 $n>N$，若 $\nu_n\le m+r$ 则 $c_n=0$ 故 $c'_n=0\in t^r(S/(t^{\nu_n}))$；若 $\nu_n>m+r$ 则 $c_{n,0}=\cdots=c_{n,m+r-1}=0$，故 $c'_n$ 的 $t^0,\dots,t^{r-1}$ 系数全为 $0$，从而 $c'_n\in t^r(S/(t^{\nu_n}))$。于是 $c'=(c'_n)_{n\ge 1}\in\mathcal C$ 且 $c=t^m c'\in t^m\mathcal C$。故 $\ker\pi_{C,m}=t^m\widehat C$，且 $\bigcap_{m\ge 1}t^m\widehat C=\bigcap_{m\ge 1}\ker\pi_{C,m}=0$。$\square$

由此可知 $\widehat B$ 的 $t$-进拓扑与逆向极限拓扑完全相同。下面求 $\operatorname{im}\widehat\iota$ 在 $\widehat B$ 中的闭包 $\overline{\operatorname{im}\widehat\iota}$：

**定理 1.2**：$\operatorname{im}\widehat\iota$ 在 $\widehat B$ 中的闭包为
$$\overline{\operatorname{im}\widehat\iota}=\ker\widehat q=\left\{(b_n)_{n\ge 1}\in\mathcal B \;\middle|\; \forall n\ge 1,\; b_n\in t^{\nu_n}S\right\}.$$

**证明**：
1. 映射 $\widehat q:\widehat B\to\widehat C$ 是 $S$-线性的，故 $\widehat q(t^m\widehat B)\subseteq t^m\widehat C$，即 $\widehat q$ 关于 $t$-进拓扑连续。由引理 1.1，$\widehat C$ 是 $t$-进分离的（从而 Hausdorff），所以 $\{0\}\subseteq\widehat C$ 是闭集，因而 $\ker\widehat q=\widehat q^{-1}(0)$ 在 $\widehat B$ 中闭。因 $\operatorname{im}\widehat\iota\subseteq\ker\widehat q$，得 $\overline{\operatorname{im}\widehat\iota}\subseteq\ker\widehat q$。
2. 反过来，任取 $b=(b_n)_{n\ge 1}\in\ker\widehat q$，写 $b_n=t^{\nu_n}u_n$（$u_n\in S$）。对任意 $m\ge 1$，因 $b\in\mathcal B$，存在 $N\ge 1$ 使对一切 $n>N$ 均有 $b_n\in t^m S$。构造截断序列 $a^{(m)}=(a_n^{(m)})_{n\ge 1}$：
   $$a_n^{(m)}=\begin{cases} u_n, & 1\le n\le N,\\ 0, & n>N.\end{cases}$$
   因 $a^{(m)}$ 仅有限项非零，故 $a^{(m)}\in\mathcal A$。又 $b-\widehat\iota(a^{(m)})$ 的第 $n$ 个分量在 $1\le n\le N$ 时为 $0\in t^m S$，在 $n>N$ 时为 $b_n\in t^m S$，由引理 1.1 得 $b-\widehat\iota(a^{(m)})\in\ker\pi_{B,m}=t^m\widehat B$。因此对每个 $m\ge 1$ 都有 $(b+t^m\widehat B)\cap\operatorname{im}\widehat\iota\neq\varnothing$，即 $b\in\overline{\operatorname{im}\widehat\iota}$。$\square$

### 1.5 $\widehat q$ 的每个纤维

因 $\widehat q:\mathcal B\to\mathcal C$ 恒满，对每个 $c=(c_n)_{n\ge 1}\in\mathcal C$（对应 $\widehat C$ 中元素），纤维 $\widehat q^{-1}(c)$ 非空。以 1.3 中构造的典范多项式提升 $b^{(0)}(c)=(b_n^{(0)})_{n\ge 1}\in\mathcal B$（其中 $b_n^{(0)}\in R$ 为 $c_n$ 的唯一次数 $<\nu_n$ 的代表）为特解，纤维即为陪集
$$\widehat q^{-1}(c)=b^{(0)}(c)+\ker\widehat q=b^{(0)}(c)+\overline{\operatorname{im}\widehat\iota},$$
在坐标模型中显式表为
$$\widehat q^{-1}(c)=\left\{(b_n)_{n\ge 1}\in\mathcal B \;\middle|\; \forall n\ge 1,\; b_n\equiv c_n \pmod{t^{\nu_n}}\right\} = \left\{\bigl(b_n^{(0)}+t^{\nu_n}u_n\bigr)_{n\ge 1} \;\middle|\; (u_n)_{n\ge 1}\in\prod_{n\ge 1}S,\; \forall m\ge 1,\; t^{\nu_n}u_n\in t^m S\;(n\gg 0)\right\}.$$

---

## 目标 2：$E$ 的坐标模型、$j$ 与 $Q$ 的 $t$-幂挠元、$E$ 的挠性及 $p$ 的满射与右逆

### 2.1 $E$ 的明确坐标模型

在 $\Phi_B:\mathcal B\xrightarrow{\sim}\widehat B$ 等同下，定义 $S$-子模 $\mathcal U\subseteq\prod_{n\ge 1}S$：
$$\mathcal U:=\left\{(u_n)_{n\ge 1}\in\prod_{n\ge 1}S \;\middle|\; \forall m\ge 1,\; t^{\nu_n}u_n\in t^m S\text{ 对充分大的 } n \text{ 成立}\right\}$$
（等价地，$\lim_{n\to\infty}\bigl(\nu_n+v_t(u_n)\bigr)=+\infty$）。显然 $\mathcal A=c_0(\mathbb N,S)\subseteq\mathcal U$。

考虑 $S$-线性映射
$$\Theta:\mathcal U\longrightarrow \ker\widehat q,\qquad (u_n)_{n\ge 1}\longmapsto (t^{\nu_n}u_n)_{n\ge 1}.$$
因为 $S$ 是整环且 $t^{\nu_n}\neq 0$，$\Theta$ 为单射；又对任一 $b=(b_n)_{n\ge 1}\in\ker\widehat q\subseteq\mathcal B$，各 $b_n\in t^{\nu_n}S$ 唯一写作 $b_n=t^{\nu_n}u_n$（$u_n\in S$），且 $b\in\mathcal B$ 恰等价于 $u=(u_n)_{n\ge 1}\in\mathcal U$，故 $\Theta:\mathcal U\xrightarrow{\sim}\ker\widehat q$ 是 $S$-模同构。同时，$\Theta(\mathcal A)=\widehat\iota(\mathcal A)=\operatorname{im}\widehat\iota$。因此 $\Theta$ 诱导 $S$-模同构
$$\overline\Theta:\mathcal U/\mathcal A \xrightarrow{\;\sim\;} \ker\widehat q/\operatorname{im}\widehat\iota = \ker p = E, \qquad (u_n)_{n\ge 1}+\mathcal A \longmapsto (t^{\nu_n}u_n)_{n\ge 1}+\operatorname{im}\widehat\iota.$$
这就是 $E$ 的明确坐标模型。（注：当 $\nu_n\to\infty$ 时，$\mathcal U=\prod_{n\ge 1}S$，故 $E\cong (\prod_{n\ge 1}S)/c_0(\mathbb N,S)$；对一般非负整数列 $(\nu_n)_{n\ge 1}$，上述 $\mathcal U/\mathcal A$ 均成立。）

### 2.2 $j$ 的核和像，以及 $Q$ 中被某个 $t^r$（$r\ge 1$）杀死的元素

先验证 $j:C\to Q$ 良定义且与 $p,\eta_C$ 相容：对 $b,b'\in B$，若 $q(b)=q(b')$，则 $b-b'=\iota(a)$（$a\in A$），故 $\eta_B(b)-\eta_B(b')=\eta_B(\iota(a))=\widehat\iota(\eta_A(a))\in\operatorname{im}\widehat\iota$；又对一切 $b\in B$，
$$p(j(q(b)))=\widehat q(\eta_B(b))=\eta_C(q(b)),\qquad \text{即 } p\circ j=\eta_C.$$

1. **$\ker j$**：
   由 1.1 知 $\eta_C:C\to\widehat C$ 等同于包含映射 $\bigoplus_{n\ge 1}R/(t^{\nu_n})\hookrightarrow\mathcal C$，故 $\eta_C$ 是单射（也可直接由 $\bigcap_{m\ge 1}t^m C=\bigoplus_{n\ge 1}\bigcap_{m\ge 1}t^m(R/(t^{\nu_n}))=0$ 看出）。因 $p\circ j=\eta_C$ 为单射，必有
   $$\ker j=0,$$
   即 $j:C\hookrightarrow Q$ 恒为单射。

2. **$Q$ 中被 $t^r$（$r\ge 1$）杀死的元素**：
   对每个 $r\ge 1$，记 $M[t^r]:=\{x\in M: t^r x=0\}$。在 $C\cong \bigoplus_{n\ge 1}R/(t^{\nu_n})$ 中，有
   $$C[t^r]=\bigoplus_{n\ge 1} t^{\max(0,\nu_n-r)}R/(t^{\nu_n}).$$
   **命题 2.1**：对每个 $r\ge 1$，有 $Q[t^r]=j\bigl(C[t^r]\bigr)$；因而 $Q$ 中所有被某个 $t^r$（$r\ge 1$）杀死的元素全体恰好为
   $$\bigcup_{r\ge 1}Q[t^r]=\operatorname{im} j.$$
   **证明**：因 $j$ 为 $R$-线性，显然 $j(C[t^r])\subseteq Q[t^r]$。反之，设 $x=b+\operatorname{im}\widehat\iota\in Q[t^r]$，其中 $b=(b_n)_{n\ge 1}\in\mathcal B$。则 $t^r b=\widehat\iota(a)$ 对某个 $a=(a_n)_{n\ge 1}\in\mathcal A$ 成立，即对一切 $n\ge 1$ 有 $t^r b_n=t^{\nu_n}a_n$。对每个 $n\ge 1$ 分两类讨论：
   - 若 $\nu_n\le r$，将 $b_n\in S$ 唯一写作 $b_n=p_n(t)+t^{\nu_n}u_n$，其中 $p_n(t)\in R$ 满足 $\deg p_n<\nu_n$（$\nu_n=0$ 时 $p_n=0$），$u_n\in S$。因 $b\in\mathcal B$，对充分大的 $n$ 有 $b_n\in t^r S\subseteq t^{\nu_n}S$，从而对充分大的此类 $n$ 必有 $p_n=0$，且 $b_n=t^{\nu_n}u_n$。进而对任意 $m\ge 1$，对充分大的此类 $n$ 有 $t^{\nu_n}u_n\in t^{r+m}S\subseteq t^{\nu_n+m}S$，故 $u_n\in t^m S$。
   - 若 $\nu_n>r$，在整环 $S$ 中约去 $t^r$ 得 $b_n=t^{\nu_n-r}a_n$。将 $a_n\in S$ 唯一写作 $a_n=q_n(t)+t^r v_n$，其中 $q_n(t)\in R$ 满足 $\deg q_n<r$，$v_n\in S$。因 $a\in\mathcal A$，对充分大的 $n$ 有 $a_n\in t^r S$，故 $q_n=0$；进而对任意 $m\ge 1$，对充分大的此类 $n$ 有 $t^r v_n=a_n\in t^{r+m}S$，故 $v_n\in t^m S$。

   令 $\tilde a=(\tilde a_n)_{n\ge 1}$ 与 $d=(d_n)_{n\ge 1}$ 为
   $$\tilde a_n=\begin{cases} u_n, & \nu_n\le r,\\ v_n, & \nu_n>r,\end{cases}\qquad d_n=\begin{cases} p_n(t), & \nu_n\le r,\\ t^{\nu_n-r}q_n(t), & \nu_n>r.\end{cases}$$
   由上述估计，对每个 $m\ge 1$ 在 $n\gg 0$ 时均有 $\tilde a_n\in t^m S$，故 $\tilde a\in\mathcal A$；而 $d_n\in R$ 且对充分大的 $n$ 有 $d_n=0$，故 $d=\sum_{n\ge 1} d_n e_n\in B$。对一切 $n\ge 1$ 均有 $b_n=d_n+t^{\nu_n}\tilde a_n$，且 $t^r d_n\in t^{\nu_n}R$，故 $q(d)\in C[t^r]$ 且
   $$x=b+\operatorname{im}\widehat\iota=\eta_B(d)+\operatorname{im}\widehat\iota=j(q(d))\in j\bigl(C[t^r]\bigr).$$
   因此 $Q[t^r]=j(C[t^r])$。再注意到 $C=\bigoplus_{n\ge 1}R/(t^{\nu_n})$ 的每个元素均为有限和，必被某个 $t^r$（例如取 $r=\max(\{1\}\cup\{\nu_n:n\in\text{支撑}\})$）杀死，即 $C=\bigcup_{r\ge 1}C[t^r]$。于是
   $$\bigcup_{r\ge 1}Q[t^r]=\bigcup_{r\ge 1}j\bigl(C[t^r]\bigr)=j\left(\bigcup_{r\ge 1}C[t^r]\right)=j(C)=\operatorname{im} j.\quad\square$$

3. **$\operatorname{im} j$ 的进一步刻画**：
   - **代数／挠性质刻画**：由命题 2.1，$\operatorname{im} j$ 恰好等于 $Q$ 中全体被某个 $t^r$（$r\ge 1$）杀死的元素集合（亦即 $Q$ 的 $S$-挠子模，因为 $S$ 中任意非零元均可写作 $t^r w$，$r\ge 0$，$w\in S^\times$，被 $t^r w$ 杀死等价于被 $t^r$ 杀死，而 $r=0$ 仅杀死 $0$）。又因 $p\circ j=\eta_C$ 且 $\ker\eta_C=0$，有 $\operatorname{im} j\cap E=0$ 且 $p^{-1}(\operatorname{im}\eta_C)=\operatorname{im} j\oplus E$（实际上对 $x\in Q$，若 $p(x)=\eta_C(c)$，则 $x=j(c)+(x-j(c))$ 且 $x-j(c)\in\ker p=E$）。
   - **坐标模型刻画**：在 $\widehat B/\operatorname{im}\widehat\iota$ 中，$\operatorname{im} j=(\eta_B(B)+\operatorname{im}\widehat\iota)/\operatorname{im}\widehat\iota$ 由有限支撑多项式元组 $(d_n)_{n\ge 1}$（$d_n\in R$，$\deg d_n<\nu_n$）的陪集唯一表示；对任意 $b\in\mathcal B$，$b+\operatorname{im}\widehat\iota\in\operatorname{im} j$ 当且仅当存在 $r\ge 1$ 使 $t^r b\in\operatorname{im}\widehat\iota$（即 $t^r b_n\in t^{\nu_n}S$ 对一切 $n$ 成立且 $(t^{r-\nu_n}b_n)_{n\ge 1}\in\mathcal A$）；同样地，对固定 $r\ge 1$，$Q[t^r]$ 在坐标下显式表为
     $$Q[t^r]=\left\{\bigl(t^{\max(0,\nu_n-r)}g_n\bigr)_{n\ge 1}+\operatorname{im}\widehat\iota \;\middle|\; g_n\in R,\; \deg g_n<\min(\nu_n,r),\; g_n=0\;(n\gg 0)\right\}.$$

### 2.3 $E$ 的 $S$-模挠性

**定理 2.2**：$E$ 恒为**无挠 $S$-模**（即 $S$-挠子模 $T_S(E)=0$）。

**证明**：利用坐标同构 $E\cong \mathcal U/\mathcal A$。设 $s\in S\setminus\{0\}$ 与 $u=(u_n)_{n\ge 1}\in\mathcal U$ 满足 $s u\in\mathcal A$。因 $S=k[[t]]$ 为离散赋值环，可写作 $s=t^r w$，其中 $r=v_t(s)\in\mathbb Z_{\ge 0}$，$w\in S^\times$。因 $w$ 可逆，有 $t^r u\in\mathcal A$。于是对任意 $m\ge 1$，对充分大的 $n$ 有 $t^r u_n\in t^{r+m}S$；由 $S$ 为整环消去 $t^r$ 得 $u_n\in t^m S$ 对充分大的 $n$ 成立。故 $u\in\mathcal A$，即 $u+\mathcal A=0$。$\square$

### 2.4 $p$ 的满射性，以及 $E=0$ 与 $p$ 存在 $S$-线性右逆的充要条件

1. **$p$ 的满射性**：由 $p(b+\operatorname{im}\widehat\iota)=\widehat q(b)$ 知 $\operatorname{im} p=\operatorname{im}\widehat q$。由 1.3 知 $\widehat q:\widehat B\to\widehat C$ 恒满，故 **$p:Q\to\widehat C$ 恒为满射**。

2. **$E=0$ 的充要条件**：因 $E=\ker p=\ker\widehat q/\operatorname{im}\widehat\iota$，故 $E=0\iff \operatorname{im}\widehat\iota=\ker\widehat q$，由 1.3 知这**当且仅当 $(\nu_n)_{n\ge 1}$ 有界**。

3. **$p$ 存在 $S$-线性右逆的充要条件**：
   **定理 2.3**：$p:Q\to\widehat C$ 存在 $S$-线性右逆（即存在 $S$-线性映射 $\sigma:\widehat C\to Q$ 使 $p\circ\sigma=\operatorname{id}_{\widehat C}$）**当且仅当 $(\nu_n)_{n\ge 1}$ 有界**（此时 $E=0$，$p$ 为 $S$-模同构）。

   **证明**：
   - **充分性**：若 $(\nu_n)_{n\ge 1}$ 有界，则 $E=\ker p=0$ 且 $p$ 满，从而 $p:Q\xrightarrow{\sim}\widehat C$ 为 $S$-模同构，其逆映射 $p^{-1}$ 即为 $S$-线性右逆。
   - **必要性**：设 $(\nu_n)_{n\ge 1}$ 无界，反设存在 $S$-线性映射 $\sigma:\widehat C\to Q$ 满足 $p\circ\sigma=\operatorname{id}_{\widehat C}$。取严格递增序列 $1\le n_1<n_2<\cdots$ 使 $\nu_{n_k}\ge k$ 对所有 $k\ge 1$ 成立。在 $\mathcal C\cong\widehat C$ 中构造 $c=(c_n)_{n\ge 1}\in\prod_{n\ge 1}S/(t^{\nu_n})$：
     $$c_{n_k}=t^{\nu_{n_k}-1}\bmod t^{\nu_{n_k}}\quad(k\ge 1),\qquad c_n=0\quad(n\notin\{n_k\}_{k\ge 1}).$$
     因 $\nu_{n_k}\ge k\ge 1$，每个 $c_{n_k}\neq 0$ 在 $S/(t^{\nu_{n_k}})$ 中成立；且对任意 $m\ge 1$，当 $k\ge m+1$ 时 $\nu_{n_k}-1\ge m$，故 $c_{n_k}\in t^m(S/(t^{\nu_{n_k}}))$，从而 $c\in\mathcal C$。显然 $tc=0$ 在 $\mathcal C$ 中成立。记 $\tilde c=\Phi_C(c)\in\widehat C$，则 $t\tilde c=0$。由 $\sigma$ 的 $S$-线性性（实际上只需 $t$-齐次性），
     $$t\,\sigma(\tilde c)=\sigma(t\tilde c)=0\quad\text{在 } Q \text{ 中}.$$
     故 $\sigma(\tilde c)\in Q[t^1]$。由命题 2.1，$Q[t^1]=j(C[t^1])\subseteq\operatorname{im} j$，于是
     $$\tilde c=p(\sigma(\tilde c))\in p(\operatorname{im} j)=\operatorname{im}(p\circ j)=\operatorname{im}\eta_C.$$
     但在坐标模型 $\mathcal C$ 中，$\operatorname{im}\eta_C$ 由仅有限个分量非零的元素构成，而 $c$ 有无穷多个非零分量 $c_{n_k}$（$k\ge 1$），矛盾！$\square$

---

## 目标 3：商映射 $Q/t^mQ\to\widehat C/t^m\widehat C$、$\bigcap_{m\ge 1}t^m Q$、完成 $\widehat Q,\widehat E$、完成映射 $\widehat p$ 及 $E$ 上两种拓扑的比较

### 3.1 诱导映射 $p_m: Q/t^m Q\to\widehat C/t^m\widehat C$

**定理 3.1**：对每个 $m\ge 1$，由 $p$ 诱导的映射
$$p_m: Q/t^m Q \longrightarrow \widehat C/t^m\widehat C,\qquad x+t^m Q\longmapsto p(x)+t^m\widehat C$$
恒为 $S/(t^m)$-模（及 $R$-模）**同构**；且借助引理 1.1 中 $\pi_{C,m}$ 诱导的同构 $\overline\pi_{C,m}:\widehat C/t^m\widehat C\xrightarrow{\sim} C/t^m C$，亦有自然同构
$$Q/t^m Q \xrightarrow[\;\sim\;]{\;p_m\;} \widehat C/t^m\widehat C \xrightarrow[\;\sim\;]{\;\overline\pi_{C,m}\;} C/t^m C \cong \bigoplus_{n\ge 1} S/\bigl(t^{\min(\nu_n,m)}\bigr),$$
同时 $j$ 诱导的 $j_m:C/t^m C\to Q/t^m Q$ 恰为 $\overline\pi_{C,m}\circ p_m$ 的逆同构（因 $p_m\circ j_m=(\eta_C)_m=\overline\pi_{C,m}^{-1}$）。

**证明**：
1. **$E\subseteq t^m Q$ 对一切 $m\ge 1$ 成立**：任取 $e=b+\operatorname{im}\widehat\iota\in E=\ker\widehat q/\operatorname{im}\widehat\iota$（其中 $b\in\ker\widehat q$）。由定理 1.2，$\overline{\operatorname{im}\widehat\iota}=\ker\widehat q$，故对任意 $m\ge 1$ 存在 $a^{(m)}\in\mathcal A$ 使 $b-\widehat\iota(a^{(m)})\in t^m\widehat B$。在商模 $Q=\widehat B/\operatorname{im}\widehat\iota$ 中取像即得
   $$e=\bigl(b-\widehat\iota(a^{(m)})\bigr)+\operatorname{im}\widehat\iota\in \bigl(t^m\widehat B+\operatorname{im}\widehat\iota\bigr)/\operatorname{im}\widehat\iota = t^m Q.$$
2. **满性与单性**：因 $p$ 满，有 $p(t^m Q)=t^m p(Q)=t^m\widehat C$，故 $p_m$ 满。若 $x\in Q$ 满足 $p(x)\in t^m\widehat C=p(t^m Q)$，则存在 $y\in t^m Q$ 使 $p(x-y)=0$，即 $x-y\in\ker p=E\subseteq t^m Q$，从而 $x\in t^m Q$。故 $\ker p_m=0$，$p_m$ 为 $S/(t^m)$-模同构。
3. 最后，因 $\pi_{C,m}:\widehat C\to C/t^m C$ 满且核为 $t^m\widehat C$（引理 1.1），它诱导同构 $\overline\pi_{C,m}:\widehat C/t^m\widehat C\xrightarrow{\sim} C/t^m C$；而 $\pi_{C,m}\circ\eta_C$ 为自然商映射 $C\to C/t^m C$，故 $\overline\pi_{C,m}\circ (\eta_C)_m=\operatorname{id}_{C/t^m C}$，再由 $p\circ j=\eta_C$ 得 $\overline\pi_{C,m}\circ p_m\circ j_m=\operatorname{id}_{C/t^m C}$，从而 $j_m=(\overline\pi_{C,m}\circ p_m)^{-1}$。$\square$

### 3.2 计算 $\bigcap_{m\ge 1}t^m Q$

**定理 3.2**：$\displaystyle\bigcap_{m\ge 1}t^m Q = E$。

**证明**：由 3.1 中第一步已证 $E\subseteq t^m Q$ 对一切 $m\ge 1$ 成立，故 $E\subseteq \bigcap_{m\ge 1}t^m Q$。反之，若 $x\in\bigcap_{m\ge 1}t^m Q$，则对一切 $m\ge 1$ 有 $p(x)\in p(t^m Q)=t^m\widehat C$，故由引理 1.1 得 $p(x)\in\bigcap_{m\ge 1}t^m\widehat C=0$，即 $x\in\ker p=E$。$\square$

（亦可在 $\widehat B$ 中直接看出：$\bigcap_{m\ge 1}(\operatorname{im}\widehat\iota+t^m\widehat B)=\overline{\operatorname{im}\widehat\iota}=\ker\widehat q$，模去 $\operatorname{im}\widehat\iota$ 即得 $\bigcap_{m\ge 1}t^m Q=E$。）

### 3.3 确定 $\widehat Q$、$\eta_Q$ 及 $p$ 诱导的完成映射 $\widehat p$

1. **$\widehat p$ 与 $\eta_{\widehat C}$**：
   因定理 3.1 中同构 $p_m:Q/t^m Q\xrightarrow{\sim}\widehat C/t^m\widehat C$ 与自然约化过渡映射相容，取逆向极限即得 $p$ 诱导的完成映射
   $$\widehat p:\widehat Q\xrightarrow{\;\sim\;}\widehat{\widehat C}$$
   **恒为 $S$-模同构**。
   同时，对每个 $m\ge 1$ 有与约化相容的同构 $\overline\pi_{C,m}:\widehat C/t^m\widehat C\xrightarrow{\sim}C/t^m C$。对任一 $y\in\widehat C$，在 $\widehat{\widehat C}$ 中 $\eta_{\widehat C}(y)=(y+t^m\widehat C)_{m\ge 1}$，经 $\varprojlim_{m\ge 1}\overline\pi_{C,m}$ 映射为 $(\pi_{C,m}(y))_{m\ge 1}=y$。故 $\eta_{\widehat C}:\widehat C\xrightarrow{\sim}\widehat{\widehat C}$ 也是 $S$-模同构（即 $\widehat C$ 自身已 $t$-进分离且完备）。

2. **$\widehat Q$ 与 $\eta_Q$**：
   复合得 $S$-模同构
   $$\Psi_Q:=\eta_{\widehat C}^{-1}\circ \widehat p:\widehat Q\xrightarrow{\;\sim\;}\widehat C \xrightarrow[\;\sim\;]{\;\Phi_C^{-1}\;}\mathcal C.$$
   另外，由 $j_m=(\overline\pi_{C,m}\circ p_m)^{-1}$ 对 $m$ 相容，取逆向极限知 $\widehat j:\widehat C\to\widehat Q$ 满足 $\widehat p\circ\widehat j=\widehat{\eta_C}$；且在第 $m$ 层，由 $\overline\pi_{C,m}(y+t^m\widehat C)=\pi_{C,m}(y)$ 与 $(\eta_C)_m=\overline\pi_{C,m}^{-1}$ 得 $(\eta_C)_m(\pi_{C,m}(y))=y+t^m\widehat C$，从而 $\widehat p(\widehat j(y))=(y+t^m\widehat C)_{m\ge 1}=\eta_{\widehat C}(y)$。因此 $\Psi_Q=\widehat j^{-1}$（即 $\widehat j:\widehat C\xrightarrow{\sim}\widehat Q$ 是 $\Psi_Q$ 的逆同构）。
   由典范映射 $\eta$ 对 $R$-线性映射 $p:Q\to\widehat C$ 的自然性，有交换关系 $\widehat p\circ\eta_Q=\eta_{\widehat C}\circ p$，两边作用 $\eta_{\widehat C}^{-1}$ 得
   $$\Psi_Q\circ\eta_Q=p:Q\longrightarrow\widehat C,\qquad \text{等价地 }\eta_Q=\widehat j\circ p:Q\longrightarrow\widehat Q.$$
   因此：
   - 在同构 $\widehat Q\cong\widehat C\cong\mathcal C$（通过 $\Psi_Q$ 或 $\widehat j$）下，典范映射 $\eta_Q:Q\to\widehat Q$ 正对应于 $p:Q\to\widehat C$；
   - 特别地，$\eta_Q$ 恒为**满射**，其核为 $\ker\eta_Q=\ker p=E=\bigcap_{m\ge 1}t^m Q$（故 $\eta_Q$ 诱导同构 $Q/E\xrightarrow{\sim}\widehat Q$）；
   - $\widehat p=\eta_{\widehat C}\circ \Psi_Q=\eta_{\widehat C}\circ\widehat j^{-1}:\widehat Q\xrightarrow{\sim}\widehat{\widehat C}$ 为 $S$-模同构。

### 3.4 确定 $\widehat E$ 与典范映射 $\eta_E$

在坐标模型 $E\cong \mathcal U/\mathcal A$ 下，先具体刻画 $t^m E$ 与 $E/t^m E$：

**引理 3.3**：对每个 $m\ge 1$ 与 $u=(u_n)_{n\ge 1}\in\mathcal U$，有
$$u\in t^m\mathcal U+\mathcal A \;\Longleftrightarrow\; u_n\in t^m S \text{ 对充分大的 } n \text{ 成立}.$$
**证明**：
- 若 $u=t^m v+a$（$v\in\mathcal U$，$a\in\mathcal A$），由 $a\in\mathcal A$ 知对充分大的 $n$ 有 $a_n\in t^m S$，故 $u_n=t^m v_n+a_n\in t^m S$。
- 反之，若存在 $N\ge 1$ 使对一切 $n>N$ 有 $u_n\in t^m S$，令
  $$a_n=\begin{cases} u_n, & 1\le n\le N,\\ 0, & n>N,\end{cases}\qquad v_n=\begin{cases} 0, & 1\le n\le N,\\ u_n/t^m\in S, & n>N.\end{cases}$$
  则 $a=(a_n)_{n\ge 1}$ 仅有限项非零故 $a\in\mathcal A$；对任意 $r\ge 1$，因 $u\in\mathcal U$，对充分大的 $n>N$ 有 $t^{\nu_n}u_n\in t^{m+r}S$，消去 $t^m$ 得 $t^{\nu_n}v_n\in t^r S$，故 $v=(v_n)_{n\ge 1}\in\mathcal U$。且 $u=t^m v+a\in t^m\mathcal U+\mathcal A$。$\square$

再对每个 $m\ge 1$，定义 $S/(t^m)$-子模
$$\mathcal U_m:=\left\{(\overline u_n)_{n\ge 1}\in\prod_{n\ge 1} S/t^m S \;\middle|\; \forall K\ge 0,\; \{n\ge 1:\nu_n\le K\text{ 且 }\overline u_n\neq 0\}\text{ 有限}\right\}.$$
显然 $\bigoplus_{n\ge 1} S/t^m S\subseteq\mathcal U_m$，且逐坐标约化模 $t^m$ 给出兼容满射？注意当 $\overline u^{(m+1)}\in\mathcal U_{m+1}$ 模 $t^m$ 时，$\{n:\nu_n\le K\text{ 且 }\overline u_n^{(m+1)}\bmod t^m\neq 0\}\subseteq\{n:\nu_n\le K\text{ 且 }\overline u_n^{(m+1)}\neq 0\}$ 有限，故自然约化映射 $\mathcal U_{m+1}\to\mathcal U_m$ 良定义，从而在商 $\mathcal U_m/\bigoplus_{n\ge 1}S/t^m S$ 上有自然约化过渡映射。

**命题 3.4**：对每个 $m\ge 1$，逐坐标约化映射 $\rho_m:\mathcal U\to\prod_{n\ge 1}S/t^m S$ 满足 $\operatorname{im}\rho_m=\mathcal U_m$，且诱导相容的 $S/(t^m)$-模同构
$$E/t^m E \;\cong\; \mathcal U/(t^m\mathcal U+\mathcal A) \;\xrightarrow[\;\sim\;]{\;\overline\rho_m\;}\; \mathcal U_m \Big/ \bigoplus_{n\ge 1} (S/t^m S).$$

**证明**：对任意 $u=(u_n)_{n\ge 1}\in\mathcal U$ 与 $K\ge 0$，取 $r=m+K$，由 $u\in\mathcal U$ 知对充分大的 $n$ 有 $t^{\nu_n}u_n\in t^{m+K}S$；若同时 $\nu_n\le K$，则 $u_n\in t^{m+K-\nu_n}S\subseteq t^m S$，即 $u_n\bmod t^m S=0$。故 $\rho_m(\mathcal U)\subseteq\mathcal U_m$。
反之，任取 $(\overline u_n)_{n\ge 1}\in\mathcal U_m$，取每个 $\overline u_n$ 的唯一次数 $<m$ 的多项式提升 $p_n(t)\in R\subseteq S$（$\overline u_n=0$ 时取 $p_n=0$）。对任意 $r\ge 1$，取 $K=r$：因 $(\overline u_n)\in\mathcal U_m$，对充分大的 $n$ 要么 $\nu_n>r$（此时 $t^{\nu_n}p_n\in t^{\nu_n}S\subseteq t^r S$），要么 $\overline u_n=0$（此时 $p_n=0$ 故 $t^{\nu_n}p_n=0\in t^r S$）。因此 $p=(p_n)_{n\ge 1}\in\mathcal U$ 且 $\rho_m(p)=(\overline u_n)_{n\ge 1}$，即 $\operatorname{im}\rho_m=\mathcal U_m$。
最后，$\rho_m(u)\in\bigoplus_{n\ge 1}(S/t^m S)\iff u_n\in t^m S$ 对充分大的 $n$ 成立 $\iff u\in t^m\mathcal U+\mathcal A$（引理 3.3），故 $\overline\rho_m$ 为同构，且显然与各层自然约化相容。$\square$

**定理 3.5**：对任意非负整数列 $(\nu_n)_{n\ge 1}$，典范映射 $\eta_E: E\to\widehat E$ 恒为 $S$-模**同构**；特别地，
$$\bigcap_{m\ge 1}t^m E = 0,\qquad E \xrightarrow[\;\sim\;]{\;\eta_E\;} \widehat E \cong \varprojlim_{m\ge 1}\left(\mathcal U_m\Big/\bigoplus_{n\ge 1}(S/t^m S)\right)\cong \mathcal U/\mathcal A.$$

**证明**：
1. **单性（分离性）**：若 $u+\mathcal A\in\ker\eta_E=\bigcap_{m\ge 1}t^m E$，则对一切 $m\ge 1$ 有 $u\in t^m\mathcal U+\mathcal A$。由引理 3.3，对每个 $m\ge 1$ 有 $u_n\in t^m S$ 对充分大的 $n$ 成立，即 $u\in\mathcal A$。故 $\bigcap_{m\ge 1}t^m E=0$，$\eta_E$ 恒为单射。
2. **满性（完备性）**：利用命题 3.4 的相容同构 $\overline\rho_m$，任取 $\xi=(\xi_m)_{m\ge 1}\in\varprojlim_{m\ge 1}\bigl(\mathcal U_m/\bigoplus_{n\ge 1}(S/t^m S)\bigr)$。归纳选取一列代表元 $\overline u^{(m)}\in\mathcal U_m$（$m\ge 1$）使 $\overline u^{(m)}\bmod\bigoplus_{n\ge 1}(S/t^m S)=\xi_m$ 且 $\overline u^{(m+1)}\bmod t^m S=\overline u^{(m)}$ 在**所有**坐标 $n\ge 1$ 上成立：
   - 对 $m=1$，任取 $\xi_1$ 的代表 $\overline u^{(1)}\in\mathcal U_1$；
   - 设已取定 $\overline u^{(m)}\in\mathcal U_m$，任取 $\xi_{m+1}$ 的代表 $\tilde u^{(m+1)}\in\mathcal U_{m+1}$。因 $\xi_{m+1}$ 约化为 $\xi_m$，存在 $N_m\ge 1$ 使对一切 $n>N_m$ 有 $\tilde u_n^{(m+1)}\bmod t^m S=\overline u_n^{(m)}$。对 $1\le n\le N_m$，因 $S/t^{m+1}S\to S/t^m S$ 为满射，任取 $\overline u_n^{(m)}\in S/t^m S$ 的一个提升 $\overline u_n^{(m+1)}\in S/t^{m+1}S$，而对 $n>N_m$ 令 $\overline u_n^{(m+1)}:=\tilde u_n^{(m+1)}$。于是 $\overline u^{(m+1)}-\tilde u^{(m+1)}\in\bigoplus_{n\ge 1}(S/t^{m+1}S)\subseteq\mathcal U_{m+1}$，故 $\overline u^{(m+1)}\in\mathcal U_{m+1}$ 仍代表 $\xi_{m+1}$，且 $\overline u_n^{(m+1)}\bmod t^m S=\overline u_n^{(m)}$ 对一切 $n\ge 1$ 成立。

   对每个固定的 $n\ge 1$，$(\overline u_n^{(m)})_{m\ge 1}\in\varprojlim_{m\ge 1}S/t^m S=S$，故存在唯一的 $u_n\in S$ 使 $u_n\bmod t^m S=\overline u_n^{(m)}$ 对一切 $m\ge 1$ 成立。现验证 $u=(u_n)_{n\ge 1}\in\mathcal U$：任取 $r\ge 1$，取 $m=r$ 与 $K=r$。因 $\overline u^{(r)}\in\mathcal U_r$，存在 $M_r\ge 1$ 使对一切 $n>M_r$：
   - 若 $\nu_n\le r$，则必有 $u_n\bmod t^r S=\overline u_n^{(r)}=0$，即 $u_n\in t^r S$，故 $t^{\nu_n}u_n\in t^{\nu_n+r}S\subseteq t^r S$；
   - 若 $\nu_n>r$，则直接有 $t^{\nu_n}u_n\in t^{\nu_n}S\subseteq t^r S$。
   从而对一切 $n>M_r$ 均有 $t^{\nu_n}u_n\in t^r S$。由 $r\ge 1$ 的任意性知 $u\in\mathcal U$。令 $e=\overline\Theta(u+\mathcal A)\in E$，其在第 $m$ 层的像对应 $\rho_m(u)\bmod\bigoplus=\overline u^{(m)}\bmod\bigoplus=\xi_m$，故 $\eta_E$ 满。

   已知 $\eta_E$ 是 $S$-线性的（因 $E$ 本身是 $S$-模），故 $\eta_E:E\xrightarrow{\sim}\widehat E$ 为 $S$-模同构。$\square$

（附注：若将包含映射 $\iota_E:E\hookrightarrow Q$ 完成，因 $E\subseteq t^m Q$ 对所有 $m\ge 1$ 成立，第 $m$ 层映射 $E/t^m E\to Q/t^m Q$ 恒为零，故 $\widehat{\iota_E}=0:\widehat E\to\widehat Q$。）

### 3.5 $E$ 上两种拓扑的比较、分离性及重合充要条件

记 $E$ 自身的 $t$-进拓扑为 $\mathcal T_{\mathrm{int}}$（零点邻域基为 $\{t^m E\}_{m\ge 1}$），从 $Q$ 的 $t$-进拓扑继承的子空间拓扑为 $\mathcal T_{\mathrm{sub}}$（零点邻域基为 $\{E\cap t^m Q\}_{m\ge 1}$）。

1. **子空间拓扑的刻画与拓扑比较**：
   由定理 3.2（或 3.1 第一步），对一切 $m\ge 1$ 均有 $E\subseteq t^m Q$，从而
   $$E\cap t^m Q = E \qquad (\forall m\ge 1).$$
   由此，在 $\mathcal T_{\mathrm{sub}}$ 中唯一的零点邻域就是 $E$ 本身，进而由平移不变性，**$\mathcal T_{\mathrm{sub}}=\{\varnothing, E\}$ 恒为 $E$ 上的密着（平庸）拓扑**。而对任意 $m\ge 1$ 均有 $t^m E\subseteq E=E\cap t^m Q$，故 **$\mathcal T_{\mathrm{int}}$ 恒细于或等于 $\mathcal T_{\mathrm{sub}}$**（$\mathcal T_{\mathrm{sub}}\subseteq\mathcal T_{\mathrm{int}}$）。

2. **自身拓扑的分离性**：
   由定理 3.5，$\bigcap_{m\ge 1}t^m E=0$ 对**任意** $(\nu_n)_{n\ge 1}$ 恒成立，因此 **$E$ 自身的 $t$-进拓扑 $\mathcal T_{\mathrm{int}}$ 恒为分离的（Hausdorff）**。

3. **两种拓扑相同的充要条件**：
   **定理 3.6**：$\mathcal T_{\mathrm{int}}=\mathcal T_{\mathrm{sub}}$ **当且仅当 $(\nu_n)_{n\ge 1}$ 有界**（即 $E=0$）。

   **证明**：
   - **充分性**：若 $(\nu_n)_{n\ge 1}$ 有界，则 $E=0$，单点集上的拓扑唯一，故 $\mathcal T_{\mathrm{int}}=\mathcal T_{\mathrm{sub}}=\{\varnothing,\{0\}\}$。
   - **必要性**：若 $\mathcal T_{\mathrm{int}}=\mathcal T_{\mathrm{sub}}=\{\varnothing,E\}$，因 $tE$ 是 $0$ 在 $\mathcal T_{\mathrm{int}}$ 中的开邻域（包含 $0$），它必在 $\mathcal T_{\mathrm{sub}}$ 中开且非空，故 $tE=E$。由此归纳得 $t^m E=E$ 对一切 $m\ge 1$ 成立，从而由 $E$ 的分离性得
     $$E=\bigcap_{m\ge 1}t^m E=0,$$
     再由 2.4 知这当且仅当 $(\nu_n)_{n\ge 1}$ 有界。$\square$

   （特别地，当 $(\nu_n)_{n\ge 1}$ 无界时，$E\neq 0$，$tE\subsetneq E$，由定理 2.2 知 $t^m$ 在 $E$ 上单射，从而 $t^m E/t^{m+1}E\cong E/tE\neq 0$，即 $E\supsetneq tE\supsetneq t^2E\supsetneq\cdots$ 是严格递降的开子模链，$\mathcal T_{\mathrm{int}}$ 是非平凡的分离拓扑，而 $\mathcal T_{\mathrm{sub}}$ 是密着拓扑，二者严格不同。）

---

### 核心结论总览

| 考察对象 | 任意非负整数列 $(\nu_n)_{n\ge 1}$ 下的结论 | 特殊充要条件（直接用 $(\nu_n)_{n\ge 1}$ 表述） |
| :--- | :--- | :--- |
| $\widehat A,\widehat B,\widehat C$ | $\widehat A\cong\widehat B\cong c_0(\mathbb N,S)$，$\widehat C\cong \mathcal C\subseteq\prod_{n\ge 1}S/(t^{\nu_n})$ | 对一切 $(\nu_n)_{n\ge 1}$ 成立 |
| 完成列正合性 | $\widehat A$ 处恒正合，$\widehat C$ 处恒正合 | 在 $\widehat B$ 处正合（即短正合）$\iff (\nu_n)_{n\ge 1}$ 有界 |
| $\overline{\operatorname{im}\widehat\iota}$ 与纤维 | $\overline{\operatorname{im}\widehat\iota}=\ker\widehat q$；$\widehat q^{-1}(c)=b^{(0)}(c)+\ker\widehat q\neq\varnothing$ | — |
| $E,\;p$ 与挠性 | $E\cong\mathcal U/c_0(\mathbb N,S)$ 恒无 $S$-挠；$p$ 恒满 | $E=0\iff p$ 有 $S$-线性右逆 $\iff (\nu_n)_{n\ge 1}$ 有界 |
| $j$ 与 $Q[t^r]$ | $\ker j=0$，$Q[t^r]=j(C[t^r])$，$\bigcup_{r\ge 1}Q[t^r]=\operatorname{im} j$ | — |
| $p_m,\;\bigcap t^m Q,\;\widehat Q,\;\widehat p$ | $p_m:Q/t^mQ\xrightarrow{\sim}\widehat C/t^m\widehat C$；$\bigcap_{m\ge 1}t^m Q=E$；$\widehat p:\widehat Q\xrightarrow{\sim}\widehat{\widehat C}$；在 $\widehat Q\cong\widehat C$ 下 $\eta_Q$ 对应 $p$ | — |
| $\widehat E,\;\eta_E$ 与 $E$ 的拓扑 | $\bigcap_{m\ge 1}t^m E=0$（恒分离），$\eta_E:E\xrightarrow{\sim}\widehat E$ 恒同构；$\mathcal T_{\mathrm{sub}}=\{\varnothing,E\}\subseteq\mathcal T_{\mathrm{int}}$ | $\mathcal T_{\mathrm{int}}=\mathcal T_{\mathrm{sub}}\iff (\nu_n)_{n\ge 1}$ 有界 |
