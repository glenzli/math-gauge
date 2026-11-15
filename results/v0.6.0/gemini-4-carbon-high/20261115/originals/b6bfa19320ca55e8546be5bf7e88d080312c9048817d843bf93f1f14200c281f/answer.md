下面对任意域 $k$ 及任意给定的非负整数列 $(\nu_n)_{n\ge 1}$ 逐项完成三个整体目标，并给出完整证明。

---

### 预备约定与基本性质

1. **次数与零幂约定**：约定 $t^0=1$，从而当 $\nu_n=0$ 时 $t^0 R=R$，$t^0 S=S$，$R/t^0R=0$，$S/t^0S=0$。对任意整数 $d\ge 0$，记
   $$
   k[t]_{<d}:=\left\{\sum_{i=0}^{d-1}\alpha_i t^i \in R \;\middle|\; \alpha_i\in k\right\}
   $$
   为次数严格小于 $d$ 的多项式空间（特别地 $k[t]_{<0}:=\{0\}$）。对任意 $s=\sum_{i=0}^{\infty}\alpha_i t^i\in S=k[[t]]$ 及 $d\ge 0$，记其截断多项式为 $s_{<d}:=\sum_{i=0}^{d-1}\alpha_i t^i\in k[t]_{<d}$；这是唯一满足 $s-s_{<d}\in t^d S$ 的 $k[t]_{<d}$ 中元素。因此映射 $k[t]_{<d}\to S/t^d S$（$r\mapsto r+t^d S$）是 $k$-线性同构，自然嵌入诱导环同构 $R/t^d R \xrightarrow{\sim} S/t^d S$。
2. **$S$ 是离散赋值整环**：$S=k[[t]]$ 为整环，任意非零元 $s\in S\setminus\{0\}$ 可唯一写为 $s=u t^r$，其中 $r\in\mathbb{Z}_{\ge 0}$，$u\in S^\times$（常数项非零的幂级数在 $S$ 中可逆）。对任意 $d\ge 0$，$t^d\ne 0$ 在 $S$ 中非零因子，且 $t^d S\cap R = t^d R$。
3. **完成上的 $S$ 模结构与典范映射的 $S$ 线性性**：对任意 $R$ 模 $M$，在 $\widehat M=\varprojlim_{m\ge 1} M/t^m M$ 上，$s\in S$ 的作用定义为
   $$
   s\cdot (x_m+t^m M)_{m\ge 1}:=\bigl(s_{<m}x_m+t^m M\bigr)_{m\ge 1}.
   $$
   当 $m'\ge m\ge 1$ 时 $s_{<m'}-s_{<m}\in t^m R$，且 $x_{m'}-x_m\in t^m M$，故 $s_{<m'}x_{m'}-s_{<m}x_m\in t^m M$，上述作用良定并赋予 $\widehat M$ 以延拓 $R$ 作用的 $S$ 模结构；任意 $R$ 线性映射 $\varphi:M\to N$ 诱导的 $\widehat\varphi:\widehat M\to\widehat N$ 均为 $S$ 线性映射。特别地，若 $N$ 本身已是 $S$ 模（其 $R$ 模结构由 $R\hookrightarrow S$ 限制得到），则对任意 $s\in S$、$y\in N$ 及 $m\ge 1$，写 $s=s_{<m}+t^m w$（$w\in S$），有 $sy-s_{<m}y=t^m(wy)\in t^m N$，故典范映射 $\eta_N:N\to\widehat N$（$y\mapsto(y+t^m N)_{m\ge 1}$）是 **$S$ 线性映射**。
4. **$t$ 进拓扑的闭包刻画**：在模 $N$ 的 $t$ 进拓扑中，每个点 $x\in N$ 以 $\{x+t^m N\}_{m\ge 1}$ 为邻域基。对任意子模（或子集）$L\subseteq N$，
   $$
   x\in\overline L \iff \forall m\ge 1,\ (x+t^m N)\cap L\ne\emptyset \iff \forall m\ge 1,\ x\in L+t^m N,
   $$
   故 $\overline L=\bigcap_{m\ge 1}(L+t^m N)$；特别地，$N$ 的 $t$ 进拓扑分离（$\bigcap_{m\ge 1} t^m N=0$）等价于单点集 $\{0\}$ 闭（即 Hausdorff）。

---

## 目标 1：$\widehat A,\widehat B,\widehat C$ 的坐标模型、诱导映射、正合性、闭包与纤维

### 1.1 $\widehat A,\widehat B,\widehat C$ 的具体坐标模型与同构

定义如下三个赋予逐分量 $S$ 运算的 $S$ 模（受限直积）：
$$
M_A := \left\{(a_n)_{n\ge 1}\in\prod_{n\ge 1} S \;\middle|\; \forall m\ge 1,\ \{n\ge 1 : a_n\notin t^m S\}\text{ 为有限集}\right\},
$$
$$
M_B := \left\{(b_n)_{n\ge 1}\in\prod_{n\ge 1} S \;\middle|\; \forall m\ge 1,\ \{n\ge 1 : b_n\notin t^m S\}\text{ 为有限集}\right\},
$$
$$
M_C := \left\{(c_n)_{n\ge 1}\in\prod_{n\ge 1} S/t^{\nu_n}S \;\middle|\; \forall m\ge 1,\ \{n\ge 1 : c_n\notin t^m(S/t^{\nu_n}S)\}\text{ 为有限集}\right\}.
$$
注意在 $S/t^{\nu_n}S$ 中，子模 $t^m(S/t^{\nu_n}S)=(t^m S+t^{\nu_n}S)/t^{\nu_n}S = t^{\min(\nu_n,m)}S/t^{\nu_n}S$（当 $m\ge\nu_n$ 时该子模为 $0$）。容易验证 $M_A,M_B,M_C$ 对逐分量加法与 $S$ 数乘封闭（例如若 $b_n\in t^m S$，则对任意 $s\in S$ 有 $sb_n\in t^m S$，故 $\{n:sb_n\notin t^m S\}\subseteq\{n:b_n\notin t^m S\}$ 有限），因此它们确实是 $S$ 模。

下面给出它们与相容商记录之间的显式 $S$ 模同构：

1. **$\Phi_B:M_B\xrightarrow{\sim}\widehat B$ 与逆映射 $\Psi_B:\widehat B\xrightarrow{\sim} M_B$（以及完全平行的 $\Phi_A:M_A\xrightarrow{\sim}\widehat A$ 与 $\Psi_A$）**：
   - **正向映射 $\Phi_B$**：对 $b=(b_n)_{n\ge 1}\in M_B$ 及每个 $m\ge 1$，集合 $\{n\ge 1:b_n\notin t^m S\}=\{n\ge 1:b_{n,<m}\ne 0\}$ 有限，故有限和 $\sum_{n\ge 1} b_{n,<m}e_n\in B$ 良定。置
     $$
     \Phi_B(b):=\left(\sum_{n\ge 1} b_{n,<m} e_n + t^m B\right)_{m\ge 1}\in \widehat B.
     $$
     当 $m'\ge m\ge 1$ 时，对每个 $n$ 有 $b_{n,<m'}-b_{n,<m}\in t^m S\cap R = t^m R$，故 $\sum_{n\ge 1}b_{n,<m'}e_n - \sum_{n\ge 1}b_{n,<m}e_n\in t^m B$，这说明 $\Phi_B(b)$ 是相容商记录。对任意 $s\in S$，$s_{<m}b_{n,<m}-(sb_n)_{<m}\in t^m R$，故 $\Phi_B$ 是 $S$ 线性的。
   - **逆映射 $\Psi_B$**：设 $u=(x_m+t^m B)_{m\ge 1}\in\widehat B$，其中 $x_m=\sum_{n\ge 1} r_{m,n}e_n\in B$（$r_{m,n}\in R$，对固定的 $m$ 仅有有限个 $n$ 使 $r_{m,n}\ne 0$）。注意 $t^m B=\bigoplus_{n\ge 1} t^m R e_n$，故 $x_m+t^m B$ 唯一决定每个 $r_{m,n}+t^m R\in R/t^m R$，且相容性 $x_{m'}-x_m\in t^m B$（$m'\ge m$）等价于对每个 $n\ge 1$ 有 $r_{m',n}-r_{m,n}\in t^m R$。由标准同构 $\varprojlim_{m\ge 1}R/t^m R\cong S$，对每个 $n\ge 1$ 存在唯一的幂级数 $b_n\in S$ 使得对一切 $m\ge 1$ 有 $b_n-r_{m,n}\in t^m S$（具体而言，$b_n$ 的 $t^i$ 项系数即为 $r_{i+1,n}$ 的 $t^i$ 项系数）。对任意固定的 $m\ge 1$，除有限个 $n$ 外均有 $r_{m,n}=0$，从而 $b_n\in t^m S$，故 $(b_n)_{n\ge 1}\in M_B$。置 $\Psi_B(u):=(b_n)_{n\ge 1}$。
   - **互逆验证**：因 $b_n-r_{m,n}\in t^m S$ 等价于 $b_{n,<m}\equiv r_{m,n}\pmod{t^m R}$，立得 $\Phi_B(\Psi_B(u))=u$ 与 $\Psi_B(\Phi_B(b))=b$。
   - 将 $e_n$ 换为 $f_n$，完全同样地得到 $S$ 模同构 $\Phi_A:M_A\xrightarrow{\sim}\widehat A$（$a=(a_n)_{n\ge 1}\mapsto\bigl(\sum_{n\ge 1}a_{n,<m}f_n+t^m A\bigr)_{m\ge 1}$）及其逆 $\Psi_A:\widehat A\xrightarrow{\sim} M_A$。

2. **$\Phi_C:M_C\xrightarrow{\sim}\widehat C$ 与逆映射 $\Psi_C:\widehat C\xrightarrow{\sim} M_C$**：
   先注意对每个 $m\ge 1$，满射 $B\xrightarrow{q} C\to C/t^m C$ 的核为
   $$
   \iota(A)+t^m B = \bigoplus_{n\ge 1}\bigl(t^{\nu_n}R + t^m R\bigr)e_n = \bigoplus_{n\ge 1} t^{\min(\nu_n,m)}R\,e_n.
   $$
   - **正向映射 $\Phi_C$**：对 $c=(c_n)_{n\ge 1}\in M_C$，对每个 $n\ge 1$ 取唯一代表多项式 $r_n^{(c)}\in k[t]_{<\nu_n}$ 使得 $c_n = r_n^{(c)}+t^{\nu_n}S\in S/t^{\nu_n}S$。对任意 $m\ge 1$，置 $r_{m,n}^{(c)}:=\bigl(r_n^{(c)}\bigr)_{<\min(\nu_n,m)}\in k[t]_{<\min(\nu_n,m)}$。注意
     $$
     r_{m,n}^{(c)}=0 \iff r_n^{(c)}\in t^{\min(\nu_n,m)}S = t^m S+t^{\nu_n}S \iff c_n\in t^m(S/t^{\nu_n}S).
     $$
     由 $c\in M_C$ 知对固定的 $m\ge 1$，仅有有限个 $n$ 使 $r_{m,n}^{(c)}\ne 0$，故可置
     $$
     \Phi_C(c):=\left(q\!\left(\sum_{n\ge 1} r_{m,n}^{(c)} e_n\right)+t^m C\right)_{m\ge 1}\in \widehat C.
     $$
     当 $m'\ge m\ge 1$ 时，$\min(\nu_n,m')\ge\min(\nu_n,m)$，故 $r_{m',n}^{(c)}-r_{m,n}^{(c)}\in t^{\min(\nu_n,m)}R$，其对应项在 $\iota(A)+t^m B$ 中，即在 $C/t^m C$ 中为零，因此 $\Phi_C(c)$ 是相容记录。对 $s\in S$，$s_{<m}r_{m,n}^{(c)}\equiv r_{m,n}^{(sc)}\pmod{t^{\min(\nu_n,m)}R}$，故 $\Phi_C$ 是 $S$ 线性的。
   - **逆映射 $\Psi_C$**：设 $w=(z_m+t^m C)_{m\ge 1}\in\widehat C$。因 $q:B\to C$ 满，对每个 $m\ge 1$ 取提升 $y_m=\sum_{n\ge 1} r_{m,n}e_n\in B$ 使 $q(y_m)=z_m$。不同的提升以及 $t^m C$ 的模去仅改变 $r_{m,n}$ 一个 $t^{\min(\nu_n,m)}R$ 中的项；相容性 $z_{m'}-z_m\in t^m C$（$m'\ge m$）等价于对一切 $n\ge 1$ 有
     $$
     r_{m',n}-r_{m,n}\in t^{\min(\nu_n,m)}R.
     $$
     对每个 $n\ge 1$，取指标 $m_n:=\max(\nu_n,1)\ge 1$，则 $\min(\nu_n,m_n)=\nu_n$，定义
     $$
     c_n := r_{m_n,n} + t^{\nu_n}S \in S/t^{\nu_n}S.
     $$
     由于 $r_{m_n,n}$ 模 $t^{\min(\nu_n,m_n)}R=t^{\nu_n}R\subseteq t^{\nu_n}S$ 唯一，$c_n$ 不依赖于提升的选取。再对任意 $m\ge 1$：若 $m\ge m_n$，则 $\min(\nu_n,m_n)=\nu_n$，相容性给出 $r_{m,n}-r_{m_n,n}\in t^{\nu_n}R\subseteq t^{\min(\nu_n,m)}S$；若 $1\le m<m_n$，则相容性给出 $r_{m_n,n}-r_{m,n}\in t^{\min(\nu_n,m)}R\subseteq t^{\min(\nu_n,m)}S$。因此对一切 $m,n\ge 1$ 恒有
     $$
     r_{m_n,n}-r_{m,n}\in t^{\min(\nu_n,m)}S = t^m S+t^{\nu_n}S.
     $$
     固定 $m\ge 1$，除有限个 $n$ 外均有 $r_{m,n}=0$，从而 $r_{m_n,n}\in t^m S+t^{\nu_n}S$，即 $c_n\in t^m(S/t^{\nu_n}S)$。故 $(c_n)_{n\ge 1}\in M_C$，置 $\Psi_C(w):=(c_n)_{n\ge 1}$。
   - **互逆验证**：对 $c\in M_C$，取 $m=m_n$ 时 $r_{m_n,n}^{(c)}=r_n^{(c)}$，故 $\Psi_C(\Phi_C(c))=c$；反之对 $w\in\widehat C$，由 $r_{m_n,n}-r_{m,n}\in t^{\min(\nu_n,m)}S\cap R=t^{\min(\nu_n,m)}R$ 知 $r_{m,n}^{(\Psi_C(w))}\equiv r_{m,n}\pmod{t^{\min(\nu_n,m)}R}$，故 $\Phi_C(\Psi_C(w))=w$。

---

### 1.2 诱导映射的显式表达

1. **在相容商记录上**：
   - 典范映射 $\eta_M:M\to\widehat M$（$M=A,B,C$）为 $x\mapsto (x+t^m M)_{m\ge 1}$。
   - 诱导映射 $\widehat\iota:\widehat A\to\widehat B$ 与 $\widehat q:\widehat B\to\widehat C$ 分别为
     $$
     \widehat\iota\bigl((x_m+t^m A)_{m\ge 1}\bigr)=\bigl(\iota(x_m)+t^m B\bigr)_{m\ge 1},\qquad
     \widehat q\bigl((y_m+t^m B)_{m\ge 1}\bigr)=\bigl(q(y_m)+t^m C\bigr)_{m\ge 1}.
     $$
2. **在坐标模型 $M_A,M_B,M_C$ 上**：
   - $\Psi_A\circ\eta_A : A\to M_A$ 为 $\sum_{n\ge 1} r_n f_n \mapsto (r_n)_{n\ge 1}$（将 $r_n\in R$ 视为 $S$ 中元素）；
   - $\Psi_B\circ\eta_B : B\to M_B$ 为 $\sum_{n\ge 1} r_n e_n \mapsto (r_n)_{n\ge 1}$；
   - $\Psi_C\circ\eta_C : C\to M_C$ 为 $q\bigl(\sum_{n\ge 1} r_n e_n\bigr) \mapsto (r_n+t^{\nu_n}S)_{n\ge 1}$；
   - $\iota_{\mathrm{coord}}:=\Psi_B\circ\widehat\iota\circ\Phi_A : M_A\to M_B$ 为
     $$
     \iota_{\mathrm{coord}}\bigl((a_n)_{n\ge 1}\bigr)=\bigl(t^{\nu_n}a_n\bigr)_{n\ge 1}.
     $$
     *证明*：对 $a\in M_A$，在第 $m$ 层有 $\iota\bigl(\sum_n a_{n,<m}f_n\bigr)=\sum_n t^{\nu_n}a_{n,<m}e_n$；因 $a_n-a_{n,<m}\in t^m S$ 且 $\nu_n\ge 0$，有 $t^{\nu_n}a_n - t^{\nu_n}a_{n,<m}\in t^{m+\nu_n}S\subseteq t^m S$，由 $\Psi_B$ 的唯一性即得第 $n$ 分量为 $t^{\nu_n}a_n$。
   - $q_{\mathrm{coord}}:=\Psi_C\circ\widehat q\circ\Phi_B : M_B\to M_C$ 为
     $$
     q_{\mathrm{coord}}\bigl((b_n)_{n\ge 1}\bigr)=\bigl(b_n+t^{\nu_n}S\bigr)_{n\ge 1}.
     $$
     *证明*：对 $b\in M_B$，在第 $m_n=\max(\nu_n,1)$ 层，$\widehat q(\Phi_B(b))$ 的第 $n$ 个提升多项式为 $b_{n,<m_n}$；因 $m_n\ge\nu_n$，有 $b_n-b_{n,<m_n}\in t^{m_n}S\subseteq t^{\nu_n}S$，故 $b_{n,<m_n}+t^{\nu_n}S = b_n+t^{\nu_n}S$。

---

### 1.3 完成列各处的正合性及短正合的充要条件

考察完成列
$$
0 \longrightarrow \widehat A \xrightarrow{\;\widehat\iota\;} \widehat B \xrightarrow{\;\widehat q\;} \widehat C \longrightarrow 0.
$$
利用同构 $\Phi_A,\Phi_B,\Phi_C$ 转到坐标列 $0\to M_A \xrightarrow{\iota_{\mathrm{coord}}} M_B \xrightarrow{q_{\mathrm{coord}}} M_C \to 0$ 逐处判定：

1. **在 $\widehat A$ 处恒正合（$\widehat\iota$ 恒为单射）**：
   若 $a=(a_n)_{n\ge 1}\in\ker\iota_{\mathrm{coord}}$，则对一切 $n\ge 1$ 有 $t^{\nu_n}a_n=0\in S$。因 $S$ 是整环且 $t^{\nu_n}\ne 0$，得 $a_n=0$（$\forall n\ge 1$），故 $\ker\widehat\iota=0$。

2. **在 $\widehat C$ 处恒正合（$\widehat q$ 恒为满射）**：
   任取 $c=(c_n)_{n\ge 1}\in M_C$。对每个 $n\ge 1$，取唯一规范多项式代表 $b_n^{(c)}\in k[t]_{<\nu_n}$ 使得 $b_n^{(c)}+t^{\nu_n}S=c_n$。断言对一切 $m\ge 1$ 与 $n\ge 1$ 有
   $$
   b_n^{(c)}\in t^m S \iff c_n\in t^m(S/t^{\nu_n}S).
   $$
   事实上：若 $m<\nu_n$，则 $t^m S+t^{\nu_n}S=t^m S$，故 $c_n\in(t^m S+t^{\nu_n}S)/t^{\nu_n}S \iff b_n^{(c)}\in t^m S$；若 $m\ge\nu_n$，则 $t^m S+t^{\nu_n}S=t^{\nu_n}S$，而 $\deg b_n^{(c)}<\nu_n$，故 $c_n\in t^{\nu_n}S/t^{\nu_n}S=\{0\} \iff b_n^{(c)}=0 \iff b_n^{(c)}\in t^m S$（因 $\deg b_n^{(c)}<\nu_n\le m$ 时 $b_n^{(c)}\in t^m S\implies b_n^{(c)}=0$）。
   由 $c\in M_C$ 知对每个 $m\ge 1$，$\{n\ge 1:b_n^{(c)}\notin t^m S\}=\{n\ge 1:c_n\notin t^m(S/t^{\nu_n}S)\}$ 有限，故 $b^{(c)}:=(b_n^{(c)})_{n\ge 1}\in M_B$，且 $q_{\mathrm{coord}}(b^{(c)})=(b_n^{(c)}+t^{\nu_n}S)_{n\ge 1}=c$。因此 $\widehat q$ 恒为满射。

3. **在 $\widehat B$ 处的正合性**：
   首先，$q_{\mathrm{coord}}\circ\iota_{\mathrm{coord}}\bigl((a_n)\bigr)=(t^{\nu_n}a_n+t^{\nu_n}S)_{n\ge 1}=0$，故总有 $\operatorname{im}\widehat\iota\subseteq\ker\widehat q$。具体地，记
   $$
   I:=\Psi_B(\operatorname{im}\widehat\iota)=\bigl\{(t^{\nu_n}a_n)_{n\ge 1} \;\big|\; (a_n)_{n\ge 1}\in M_A\bigr\},\qquad
   K:=\Psi_B(\ker\widehat q)=\bigl\{(b_n)_{n\ge 1}\in M_B \;\big|\; \forall n\ge 1,\ b_n\in t^{\nu_n}S\bigr\}.
   $$
   **定理**：完成列在 $\widehat B$ 处正合（$\operatorname{im}\widehat\iota=\ker\widehat q$，即 $I=K$）当且仅当指数列 $(\nu_n)_{n\ge 1}$ **有上界**（即 $\sup_{n\ge 1}\nu_n<\infty$）。
   - **充分性**：设存在整数 $N\ge 0$ 使对一切 $n\ge 1$ 有 $\nu_n\le N$。任取 $b=(b_n)_{n\ge 1}\in K$，对每个 $n\ge 1$ 写 $b_n=t^{\nu_n}a_n$（$a_n\in S$）。任给 $m\ge 1$，因 $b\in M_B$，集合 $F=\{n\ge 1:b_n\notin t^{m+N}S\}$ 有限。对任意 $n\notin F$，有 $t^{\nu_n}a_n=b_n\in t^{m+N}S$；在整环 $S$ 中约去 $t^{\nu_n}$（注意 $m+N-\nu_n\ge m$），得 $a_n\in t^{m+N-\nu_n}S\subseteq t^m S$。故 $\{n\ge 1:a_n\notin t^m S\}\subseteq F$ 有限，从而 $(a_n)_{n\ge 1}\in M_A$，即 $b\in I$。
   - **必要性**：设 $(\nu_n)_{n\ge 1}$ 无上界，则可选取严格递增下标子列 $1\le n_1<n_2<n_3<\cdots$ 使对每个 $k\ge 1$ 有 $\nu_{n_k}\ge k$。令
     $$
     a_n:=\begin{cases} 1, & \text{若 } n=n_k\ (k\ge 1),\\ 0, & \text{其他情形,}\end{cases}\qquad b_n:=t^{\nu_n}a_n.
     $$
     一方面，对每个 $m\ge 1$，若 $b_n\notin t^m S$，则必有 $n=n_k$ 且 $\nu_{n_k}<m$，从而 $k\le\nu_{n_k}<m$，这样的下标至多 $m-1$ 个，故 $b=(b_n)_{n\ge 1}\in K$。另一方面，因 $S$ 是整环且 $t^{\nu_n}\ne 0$，满足 $t^{\nu_n}a'_n=b_n$（$\forall n$）的序列唯一为 $(a_n)_{n\ge 1}$；但 $\{n\ge 1:a_n\notin tS\}=\{n_1,n_2,\dots\}$ 为无限集，故 $(a_n)_{n\ge 1}\notin M_A$，即 $b\in K\setminus I$。

4. **完成列短正合的充要条件**：
   由于完成列在 $\widehat A$ 与 $\widehat C$ 处恒正合，整个完成列 $0\to\widehat A\xrightarrow{\widehat\iota}\widehat B\xrightarrow{\widehat q}\widehat C\to 0$ 短正合**当且仅当 $(\nu_n)_{n\ge 1}$ 有上界（$\sup_{n\ge 1}\nu_n<\infty$）**。

---

### 1.4 $\operatorname{im}\widehat\iota$ 在 $\widehat B$ 中的闭包与 $\widehat q$ 的每个纤维

先刻画 $t^m\widehat B$：在 $M_B$ 中断言
$$
t^m M_B = \bigl\{(b_n)_{n\ge 1}\in M_B \;\big|\; \forall n\ge 1,\ b_n\in t^m S\bigr\}.
$$
事实上左含于右显然；反之若 $b=(b_n)_{n\ge 1}\in M_B$ 满足 $\forall n,\,b_n=t^m d_n$（$d_n\in S$），则对任意 $r\ge 1$，$\{n:d_n\notin t^r S\}=\{n:b_n\notin t^{m+r}S\}$ 有限，故 $d=(d_n)_{n\ge 1}\in M_B$ 且 $b=t^m d\in t^m M_B$。

1. **$\operatorname{im}\widehat\iota$ 在 $\widehat B$ 中的闭包**：
   **结论**：对任意指数列 $(\nu_n)_{n\ge 1}$，恒有
   $$
   \overline{\operatorname{im}\widehat\iota} = \ker\widehat q = \Phi_B(K).
   $$
   *证明*：在 $M_B$ 中只需证 $\bigcap_{m\ge 1}(I+t^m M_B)=K$。
   - **$\subseteq$**：设 $b\in\bigcap_{m\ge 1}(I+t^m M_B)$。对每个固定的 $n\ge 1$，取 $m_n=\max(\nu_n,1)\ge 1$，写 $b=u+v$，其中 $u\in I$（故 $u_n\in t^{\nu_n}S$），$v\in t^{m_n}M_B$（故 $v_n\in t^{m_n}S\subseteq t^{\nu_n}S$）。于是 $b_n=u_n+v_n\in t^{\nu_n}S$。这对所有 $n\ge 1$ 成立，故 $b\in K$（这也说明 $\ker\widehat q$ 在 $\widehat B$ 中闭）。
   - **$\supseteq$**：设 $b=(b_n)_{n\ge 1}\in K$，并任给 $m\ge 1$。因 $b\in M_B$，集合 $F_m:=\{n\ge 1:b_n\notin t^m S\}$ 有限。对 $n\in F_m$ 取 $a_n\in S$ 使 $b_n=t^{\nu_n}a_n$；对 $n\notin F_m$ 令 $a_n=0$。因仅有有限个 $a_n\ne 0$，显然 $a=(a_n)_{n\ge 1}\in M_A$，从而 $u:=\iota_{\mathrm{coord}}(a)\in I$。对 $n\in F_m$ 有 $(b-u)_n=0\in t^m S$；对 $n\notin F_m$ 有 $(b-u)_n=b_n\in t^m S$。由前段对 $t^m M_B$ 的刻画知 $b-u\in t^m M_B$，即 $b\in I+t^m M_B$。由 $m\ge 1$ 的任意性得 $b\in\bigcap_{m\ge 1}(I+t^m M_B)$。

2. **$\widehat q$ 的每个纤维**：
   因 $\widehat q:\widehat B\to\widehat C$ 恒为满射，对任意 $y=\Phi_C(c)\in\widehat C$（其中 $c=(c_n)_{n\ge 1}\in M_C$），纤维 $\widehat q^{-1}(y)$ 非空，是由规范提升 $b^{(c)}=(b_n^{(c)})_{n\ge 1}\in M_B$（其中 $b_n^{(c)}\in k[t]_{<\nu_n}$ 是 $c_n$ 的唯一低次多项式代表）平移 $\ker\widehat q$ 所得的闭陪集：
   $$
   \begin{aligned}
   \widehat q^{-1}(y) &= \Phi_B(b^{(c)}) + \ker\widehat q \\
   &= \Phi_B\Bigl(\bigl\{(b_n)_{n\ge 1}\in M_B \;\big|\; \forall n\ge 1,\ b_n+t^{\nu_n}S=c_n\bigr\}\Bigr) \\
   &= \Phi_B\Bigl(\bigl\{(b_n^{(c)}+t^{\nu_n}a_n)_{n\ge 1} \;\big|\; a_n\in S,\ \forall m\ge 1,\ \{n\ge 1:t^{\nu_n}a_n\notin t^m S\}\text{ 有限}\bigr\}\Bigr).
   \end{aligned}
   $$
   （最后一步用了 $b^{(c)}\in M_B$，从而对任意 $m\ge 1$，$b_n^{(c)}+t^{\nu_n}a_n\notin t^m S$ 与 $t^{\nu_n}a_n\notin t^m S$ 至多在有限个下标 $n$ 上有差异。）

---

## 目标 2：$E$ 的模型与挠性、$j$ 的核与像、$Q$ 的 $t^\infty$-挠、$p$ 的满射性与右逆

### 2.1 $E$ 的明确坐标模型

由定义 $Q=\widehat B/\operatorname{im}\widehat\iota$，$p(b+\operatorname{im}\widehat\iota)=\widehat q(b)$，这是良定的 $S$ 线性映射（因 $\operatorname{im}\widehat\iota\subseteq\ker\widehat q$），且
$$
E=\ker p = \frac{\ker\widehat q}{\operatorname{im}\widehat\iota}.
$$
定义 $S$ 模（$\prod_{n\ge 1}S$ 的 $S$ 子模）
$$
\widetilde K := \left\{(a_n)_{n\ge 1}\in\prod_{n\ge 1} S \;\middle|\; \forall m\ge 1,\ \{n\ge 1 : t^{\nu_n}a_n\notin t^m S\}\text{ 为有限集}\right\}.
$$
显然 $M_A\subseteq\widetilde K$（因 $a_n\in t^m S\implies t^{\nu_n}a_n\in t^m S$）。定义商 $S$ 模
$$
M_E := \widetilde K / M_A.
$$
**命题**：映射
$$
\Phi_E : M_E = \widetilde K/M_A \xrightarrow{\;\sim\;} E,\qquad (a_n)_{n\ge 1}+M_A \longmapsto \Phi_B\bigl((t^{\nu_n}a_n)_{n\ge 1}\bigr)+\operatorname{im}\widehat\iota
$$
是 $S$ 模同构。

*证明*：先看 $S$ 线性映射 $\tau:\widetilde K\to K$，$\tau\bigl((a_n)_{n\ge 1}\bigr):=(t^{\nu_n}a_n)_{n\ge 1}$。由 $\widetilde K$ 与 $K$ 的定义，$\tau$ 良定且满；因 $S$ 是整环且 $t^{\nu_n}\ne 0$，$\tau$ 单，故 $\tau:\widetilde K\xrightarrow{\sim} K$ 是 $S$ 模同构。又 $\tau(M_A)=\iota_{\mathrm{coord}}(M_A)=I$，故 $\tau$ 诱导 $S$ 模同构 $\widetilde K/M_A\xrightarrow{\sim} K/I$；再与 $\Phi_B$ 诱导的同构 $K/I\xrightarrow{\sim}\ker\widehat q/\operatorname{im}\widehat\iota = E$ 复合，即得 $S$ 模同构 $\Phi_E:M_E\xrightarrow{\sim} E$。

---

### 2.2 $j:C\to Q$ 的核与像

首先验证 $j(q(b))=\eta_B(b)+\operatorname{im}\widehat\iota$（$b\in B$）良定且满足关键关系 $p\circ j=\eta_C$：
- 若 $q(b)=q(b')$，则 $b-b'=\iota(a)$（$a\in A$），故 $\eta_B(b)-\eta_B(b')=\eta_B(\iota(a))=\widehat\iota(\eta_A(a))\in\operatorname{im}\widehat\iota$，因此 $j:C\to Q$ 是良定的 $R$ 线性映射。
- 对任意 $b\in B$，有
  $$
  (p\circ j)(q(b)) = p\bigl(\eta_B(b)+\operatorname{im}\widehat\iota\bigr) = \widehat q(\eta_B(b)) = \eta_C(q(b)),
  $$
  即 $p\circ j = \eta_C : C\to\widehat C$。

1. **$j$ 的核**：**恒有 $\ker j = 0$（$j$ 恒为单射）**。
   *证明*：设 $x=q\bigl(\sum_{n\ge 1} r_n e_n\bigr)\in\ker j$（$r_n\in R$，除有限个外为 $0$）。则 $\eta_C(x)=p(j(x))=0$。在坐标模型 $M_C$ 中，$\Psi_C(\eta_C(x))=(r_n+t^{\nu_n}S)_{n\ge 1}=0$，即对一切 $n\ge 1$ 有 $r_n\in t^{\nu_n}S\cap R=t^{\nu_n}R$。写 $r_n=t^{\nu_n}u_n$（$u_n\in R$，除有限个外为 $0$），则 $\sum_{n\ge 1}r_n e_n=\iota\bigl(\sum_{n\ge 1}u_n f_n\bigr)\in\iota(A)$，故 $x=0$。

2. **$j$ 的像**：
   在 $Q=\widehat B/\operatorname{im}\widehat\iota$ 中，由定义直接有 $\operatorname{im}j=(\operatorname{im}\eta_B+\operatorname{im}\widehat\iota)/\operatorname{im}\widehat\iota$，且 $\operatorname{im}j\cap E=0$（因 $p|_{\operatorname{im}j}$ 单）。在坐标模型下，$\operatorname{im}j$ 有如下等价的显式刻画：
   $$
   \begin{aligned}
   \operatorname{im}j &= \bigoplus_{n\ge 1} S\cdot\bigl(\eta_B(e_n)+\operatorname{im}\widehat\iota\bigr) \\
   &= \Bigl\{\Phi_B(b)+\operatorname{im}\widehat\iota \;\Big|\; b=(b_n)_{n\ge 1}\in M_B,\ \{n\ge 1:b_n\ne 0\}\text{ 为有限集}\Bigr\} \\
   &= \Bigl\{\Phi_B(b)+\operatorname{im}\widehat\iota \;\Big|\; b=(b_n)_{n\ge 1}\in M_B,\ \{n\ge 1:b_n\notin t^{\nu_n}S\}\text{ 有限，且 }\bigl(\lfloor b_n/t^{\nu_n}\rfloor\bigr)_{n\ge 1}\in M_A\Bigr\},
   \end{aligned}
   $$
   其中对每个 $b_n\in S$，唯一写 $b_n=r_n+t^{\nu_n}a_n$（$r_n\in k[t]_{<\nu_n}$，$a_n\in S$），记 $\lfloor b_n/t^{\nu_n}\rfloor := a_n$。

   *证明*：对任意 $b=(b_n)_{n\ge 1}\in M_B$，作分解 $b_n=r_n+t^{\nu_n}a_n$（$r_n\in k[t]_{<\nu_n}$，$a_n\in S$）。注意 $r_n\ne 0 \iff b_n\notin t^{\nu_n}S$。
   - 若 $\Phi_B(b)+\operatorname{im}\widehat\iota\in\operatorname{im}j$，则存在 $\tilde b=\sum_{n\in F}\tilde r_n e_n\in B$（$F$ 有限，$\tilde r_n\in R$）及 $u=(u_n)_{n\ge 1}\in M_A$ 使 $b_n=\tilde r_n+t^{\nu_n}u_n$（$\forall n$）。对 $n\notin F$ 有 $b_n=t^{\nu_n}u_n\in t^{\nu_n}S$，故 $r_n=0$ 且 $a_n=u_n$；因此 $\{n:b_n\notin t^{\nu_n}S\}\subseteq F$ 有限，且 $(a_n)_{n\ge 1}$ 与 $u\in M_A$ 至多在有限集 $F$ 上不同，故 $(a_n)_{n\ge 1}\in M_A$。这给出了第三个集合的包含。
   - 若 $b\in M_B$ 满足 $F:=\{n:b_n\notin t^{\nu_n}S\}$ 有限且 $a=(a_n)_{n\ge 1}\in M_A$，令 $b'_n:=r_n$（当 $n\in F$ 时）及 $b'_n:=0$（当 $n\notin F$ 时），则 $b'=(b'_n)_{n\ge 1}$ 仅有有限个非零分量，且 $b-b'=\iota_{\mathrm{coord}}(a)\in I$，故 $\Phi_B(b)+\operatorname{im}\widehat\iota=\Phi_B(b')+\operatorname{im}\widehat\iota$ 属于第二个集合。
   - 若 $b=(b_n)_{n\ge 1}\in M_B$ 仅有有限个下标 $n\in F$ 使 $b_n\ne 0$，对 $n\in F$ 写 $b_n=r_n+t^{\nu_n}a_n$（$r_n\in k[t]_{<\nu_n}\subseteq R$，$a_n\in S$），对 $n\notin F$ 令 $r_n=0,a_n=0$，则 $a=(a_n)_{n\ge 1}$ 仅有有限个非零分量，故 $a\in M_A$，从而
     $$
     \Phi_B(b)+\operatorname{im}\widehat\iota = \eta_B\!\left(\sum_{n\in F} r_n e_n\right)+\widehat\iota(\Phi_A(a))+\operatorname{im}\widehat\iota = j\!\left(q\!\left(\sum_{n\in F} r_n e_n\right)\right)\in\operatorname{im}j.
     $$
     特别地，取单一下标的非零 $b_n\in S$ 可知 $\operatorname{im}j$ 是由 $\{\eta_B(e_n)+\operatorname{im}\widehat\iota\}_{n\ge 1}$ 生成的 $S$ 子模（且因分量不交而为直和）。三集合彼此相等得证。

---

### 2.3 $Q$ 中所有被某个 $t^r$（$r\ge 1$）杀死的元素，以及 $E$ 的 $S$ 模挠性

1. **$Q$ 的 $t^\infty$-挠元**：
   **定理**：对任意指数列 $(\nu_n)_{n\ge 1}$，$Q$ 中所有被某个 $t^r$（$r\ge 1$）杀死的元素集合恰为 $\operatorname{im}j$，即
   $$
   \bigl\{x\in Q \;\big|\; \exists r\ge 1,\ t^r x=0\bigr\} = \operatorname{im}j.
   $$
   *证明*：
   - **$\supseteq$**：任取 $x=j(q(b))\in\operatorname{im}j$，其中 $b=\sum_{n\in F} r_n e_n\in B$（$F\subseteq\mathbb{Z}_{\ge 1}$ 有限，$r_n\in R$）。置 $r:=\max\bigl(\{1\}\cup\{\nu_n : n\in F\}\bigr)\ge 1$。对每个 $n\in F$ 有 $r\ge\nu_n$，故 $t^r r_n e_n = \iota(t^{r-\nu_n}r_n f_n)\in\iota(A)$，从而 $t^r b\in\iota(A)$，$q(t^r b)=0$。由 $j$ 的 $R$ 线性性得 $t^r x = j(t^r q(b)) = j(q(t^r b)) = 0$。
   - **$\subseteq$**：设 $x=\Phi_B(b)+\operatorname{im}\widehat\iota\in Q$（$b=(b_n)_{n\ge 1}\in M_B$）满足存在整数 $r\ge 1$ 使 $t^r x=0$。则 $t^r b\in I$，即存在 $a=(a_n)_{n\ge 1}\in M_A$ 使得对一切 $n\ge 1$ 有
     $$
     t^r b_n = t^{\nu_n} a_n \quad (\text{在 } S \text{ 中}).
     $$
     因 $a\in M_A$，在 $M_A$ 的定义中取 $m=r\ge 1$ 知集合 $F:=\{n\ge 1 : a_n\notin t^r S\}$ **有限**。
     对 $n\notin F$，写 $a_n=t^r d_n$（$d_n\in S$）；对 $n\in F$，置 $d_n:=0$。验证 $d:=(d_n)_{n\ge 1}\in M_A$：对任意 $m\ge 1$，若 $d_n\notin t^m S$，则必有 $n\notin F$ 且 $a_n=t^r d_n\notin t^{m+r}S$，故 $\{n\ge 1:d_n\notin t^m S\}\subseteq\{n\ge 1:a_n\notin t^{m+r}S\}$ 有限，即 $d\in M_A$。
     现在对任意 $n\notin F$，有 $t^r b_n = t^{\nu_n}a_n = t^r(t^{\nu_n}d_n)$；在整环 $S$ 中约去 $t^r\ne 0$ 得 $b_n=t^{\nu_n}d_n$。令 $\tilde b := b-\iota_{\mathrm{coord}}(d)\in M_B$，则对一切 $n\notin F$ 有 $\tilde b_n = b_n-t^{\nu_n}d_n=0$，即 $\tilde b$ 仅在有限集 $F$ 上可能非零。由 2.2 节对 $\operatorname{im}j$ 的第二个刻画，立得
     $$
     x = \Phi_B(b)+\operatorname{im}\widehat\iota = \Phi_B(\tilde b)+\operatorname{im}\widehat\iota \in \operatorname{im}j.
     $$

2. **$E$ 的 $S$ 模挠性**：
   **定理**：对任意指数列 $(\nu_n)_{n\ge 1}$，$E$ 作为 $S$ 模**总是无挠的**（torsion-free），即其 $S$ 挠子模
   $$
   \operatorname{Tor}_S(E):=\{e\in E \mid \exists s\in S\setminus\{0\},\ se=0\} = 0.
   $$
   （特别地，当 $\sup_{n\ge 1}\nu_n<\infty$ 时 $E=0$ 为零模；当 $\sup_{n\ge 1}\nu_n=\infty$ 时 $E\ne 0$ 为非零无挠 $S$ 模，从而不是挠 $S$ 模。）

   *证明*：给出两种等价且相互印证的简短证明：
   - **由 2.2 与 2.3 直接推出**：任取 $e\in E$ 及 $s\in S\setminus\{0\}$ 使 $se=0$。写 $s=u t^r$（$u\in S^\times$，$r\ge 0$）。若 $r=0$，乘以 $u^{-1}$ 即得 $e=0$；若 $r\ge 1$，乘以 $u^{-1}$ 得 $t^r e=0$（在 $E\subseteq Q$ 中），由上段定理知 $e\in E\cap\operatorname{im}j=0$。
   - **在坐标模型 $M_E=\widetilde K/M_A$ 中直接验证**：若 $a=(a_n)_{n\ge 1}\in\widetilde K$ 满足 $u t^r a\in M_A$（$u\in S^\times,r\ge 0$），则 $t^r a\in M_A$；对任意 $m\ge 1$，$\{n:a_n\notin t^m S\}=\{n:t^r a_n\notin t^{m+r}S\}$ 有限，故 $a\in M_A$，即 $a+M_A=0\in M_E$。

---

### 2.4 $p$ 的满射性、$E=0$ 及 $p$ 存在 $S$ 线性右逆的充要条件

1. **$p$ 的满射性**：
   因 $p(b+\operatorname{im}\widehat\iota)=\widehat q(b)$，故 $\operatorname{im}p=\operatorname{im}\widehat q$。由 1.3 节知 $\widehat q:\widehat B\to\widehat C$ 恒为满射，因此**对任意指数列 $(\nu_n)_{n\ge 1}$，$p:Q\to\widehat C$ 恒为满射**，即恒有 $S$ 模短正合列
   $$
   0 \longrightarrow E \longrightarrow Q \xrightarrow{\;p\;} \widehat C \longrightarrow 0.
   $$

2. **$E=0$ 的充要条件**：
   因 $E=\ker\widehat q/\operatorname{im}\widehat\iota$，由 1.3 节立知 **$E=0$ 当且仅当 $(\nu_n)_{n\ge 1}$ 有上界（$\sup_{n\ge 1}\nu_n<\infty$）**。

3. **$p$ 存在 $S$ 线性右逆的充要条件**：
   **定理**：$p:Q\to\widehat C$ 存在 $S$ 线性右逆 $\sigma:\widehat C\to Q$（满足 $p\circ\sigma=\operatorname{id}_{\widehat C}$）**当且仅当 $(\nu_n)_{n\ge 1}$ 有上界（$\sup_{n\ge 1}\nu_n<\infty$）**。
   *证明*：
   - **充分性**：若 $\sup_{n\ge 1}\nu_n<\infty$，则 $E=\ker p=0$ 且 $p$ 满，故 $p:Q\xrightarrow{\sim}\widehat C$ 本身是 $S$ 模同构，$\sigma:=p^{-1}$ 即为 $p$ 的 $S$ 线性右逆。
   - **必要性**：反证法。设 $(\nu_n)_{n\ge 1}$ 无上界，而 $\sigma:\widehat C\to Q$ 是 $p$ 的一个 $S$ 线性右逆。选取严格递增下标子列 $1\le n_1<n_2<\cdots$ 使得对一切 $k\ge 1$ 有 $\nu_{n_k}\ge k+1$（从而 $\nu_{n_k}-1\ge k\ge 1$）。在 $\prod_{n\ge 1} S/t^{\nu_n}S$ 中定义元组 $c=(c_n)_{n\ge 1}$：
     $$
     c_n := \begin{cases} t^{\nu_{n_k}-1} + t^{\nu_{n_k}}S, & \text{若 } n=n_k\ (k\ge 1),\\ 0, & \text{其他情形.}\end{cases}
     $$
     验证三点：
     1. **$c\in M_C$**：任给 $m\ge 1$，当 $n=n_k$ 且 $k\ge m$ 时 $\nu_{n_k}-1\ge k\ge m$，故 $c_{n_k}\in t^m(S/t^{\nu_{n_k}}S)$；因此 $\{n\ge 1:c_n\notin t^m(S/t^{\nu_n}S)\}\subseteq\{n_1,\dots,n_{m-1}\}$ 有限，置 $y:=\Phi_C(c)\in\widehat C$。
     2. **$y\notin\operatorname{im}\eta_C$**：对每个 $k\ge 1$，因 $0<\nu_{n_k}-1<\nu_{n_k}$，有 $t^{\nu_{n_k}-1}\notin t^{\nu_{n_k}}S$，即 $c_{n_k}\ne 0$，故 $c$ 有无穷多个非零分量；而 $\Psi_C(\operatorname{im}\eta_C)$ 中每个元素仅有有限个非零分量，因此 $y\notin\operatorname{im}\eta_C$。
     3. **$ty=0$**：对每个 $k\ge 1$，在 $S/t^{\nu_{n_k}}S$ 中 $t\cdot c_{n_k}=t^{\nu_{n_k}}+t^{\nu_{n_k}}S=0$，故 $tc=0\in M_C$，从而 $ty=\Phi_C(tc)=0\in\widehat C$。

     现在由 $\sigma$ 的 $S$ 线性性得 $t\cdot\sigma(y)=\sigma(ty)=\sigma(0)=0\in Q$。根据 2.3 节定理，$\sigma(y)$ 被 $t^1$ 杀死蕴含 $\sigma(y)\in\operatorname{im}j$。两边作用 $p$ 并利用 $p\circ\sigma=\operatorname{id}_{\widehat C}$ 与 $p\circ j=\eta_C$，得
     $$
     y = p(\sigma(y)) \in p(\operatorname{im}j) = \operatorname{im}(p\circ j) = \operatorname{im}\eta_C,
     $$
     与 $y\notin\operatorname{im}\eta_C$ 矛盾！故当 $(\nu_n)_{n\ge 1}$ 无上界时，$p$ 不存在 $S$ 线性右逆。

---

## 目标 3：模 $t^m$ 诱导映射、$\bigcap_{m\ge 1}t^m Q$、完成 $\widehat Q,\widehat E,\widehat p$ 与 $E$ 上的两种拓扑比较

### 3.1 预备引理：$\widehat C$ 的 $t$ 进结构与双重完成

对每个 $m\ge 1$，记逆向极限 $\widehat C=\varprojlim_{r\ge 1} C/t^r C$ 的第 $m$ 个典范投射为 $\operatorname{pr}_m:\widehat C\to C/t^m C$。

**引理**：对任意 $m\ge 1$：
1. $\operatorname{pr}_m$ 是满射，且 $\ker\operatorname{pr}_m = t^m\widehat C$；从而 $\operatorname{pr}_m$ 诱导 $S/(t^m)$ 模同构 $\bar{\operatorname{pr}}_m:\widehat C/t^m\widehat C \xrightarrow{\sim} C/t^m C$。
2. $\bigcap_{m\ge 1} t^m\widehat C = 0$，且典范映射 $\eta_{\widehat C}:\widehat C\xrightarrow{\sim}\widehat{\widehat C}:=\varprojlim_{m\ge 1}\widehat C/t^m\widehat C$ 是 $S$ 模同构，其逆映射为 $\alpha:=\varprojlim_{m\ge 1}\bar{\operatorname{pr}}_m : \widehat{\widehat C}\xrightarrow{\sim}\widehat C$。

*证明*：
1. 因 $\operatorname{pr}_m\circ\eta_C : C\to C/t^m C$ 即为自然商映射（满射），故 $\operatorname{pr}_m$ 满。显然 $t^m\widehat C\subseteq\ker\operatorname{pr}_m$。反之，设 $y=\Phi_C(c)\in\ker\operatorname{pr}_m$（$c=(c_n)_{n\ge 1}\in M_C$）。由 1.1 节 $\Phi_C$ 的构造，$\operatorname{pr}_m(\Phi_C(c))=0$ 意味着对一切 $n\ge 1$ 有 $r_{m,n}^{(c)}=0$，即 $c_n\in t^m(S/t^{\nu_n}S)$。取 1.3 节中的规范多项式提升 $b^{(c)}=(b_n^{(c)})_{n\ge 1}\in M_B$，则对一切 $n\ge 1$ 有 $b_n^{(c)}\in t^m S$。由 1.4 节知存在 $d\in M_B$ 使 $b^{(c)}=t^m d$，于是
   $$
   y = \Phi_C(q_{\mathrm{coord}}(b^{(c)})) = \widehat q(\Phi_B(t^m d)) = t^m \widehat q(\Phi_B(d)) \in t^m\widehat C.
   $$
   故 $\ker\operatorname{pr}_m = t^m\widehat C$，$\bar{\operatorname{pr}}_m:\widehat C/t^m\widehat C\xrightarrow{\sim} C/t^m C$ 为同构。
2. 若 $y\in\bigcap_{m\ge 1} t^m\widehat C = \bigcap_{m\ge 1}\ker\operatorname{pr}_m$，则在 $\widehat C=\varprojlim_{m\ge 1}C/t^m C$ 中 $y$ 的每个分量 $\operatorname{pr}_m(y)=0$，故 $y=0$。进一步，过渡映射与 $(\bar{\operatorname{pr}}_m)_{m\ge 1}$ 交换，故 $\alpha=\varprojlim_{m\ge 1}\bar{\operatorname{pr}}_m:\widehat{\widehat C}\to\widehat C$ 是 $S$ 模同构；对任意 $y=(z_m)_{m\ge 1}\in\widehat C$，有 $\alpha(\eta_{\widehat C}(y))=\bigl(\bar{\operatorname{pr}}_m(y+t^m\widehat C)\bigr)_{m\ge 1}=(\operatorname{pr}_m(y))_{m\ge 1}=y$，故 $\eta_{\widehat C}=\alpha^{-1}$ 是 $S$ 模同构。

---

### 3.2 由 $p$ 诱导的 $p_m : Q/t^m Q \to \widehat C/t^m\widehat C$ 及交 $\bigcap_{m\ge 1} t^m Q$

1. **确定 $p_m : Q/t^m Q \to \widehat C/t^m\widehat C$**：
   **定理**：对任意指数列 $(\nu_n)_{n\ge 1}$ 及每个 $m\ge 1$，由 $p$ 诱导的映射
   $$
   p_m : Q/t^m Q \longrightarrow \widehat C/t^m\widehat C,\qquad x+t^m Q \longmapsto p(x)+t^m\widehat C
   $$
   均为 **$R$ 模（亦即 $S/(t^m)$ 模）同构**。（结合 3.1 节引理，$\bar{\operatorname{pr}}_m\circ p_m : Q/t^m Q\xrightarrow{\sim} C/t^m C$ 亦为同构，将 $\eta_B(b)+\operatorname{im}\widehat\iota+t^m Q$ 映为 $q(b)+t^m C$。）

   *证明*：因 $p:Q\to\widehat C$ 满，诱导映射 $p_m$ 必满。下求 $\ker p_m$：若 $x+t^m Q\in\ker p_m$，则 $p(x)\in t^m\widehat C = t^m p(Q)=p(t^m Q)$，故存在 $y\in Q$ 使 $p(x-t^m y)=0$，即 $x-t^m y\in\ker p=E$，从而 $\ker p_m = (E+t^m Q)/t^m Q$。
   然而由 1.4 节闭包等式 $\ker\widehat q=\overline{\operatorname{im}\widehat\iota}=\bigcap_{r\ge 1}(\operatorname{im}\widehat\iota+t^r\widehat B)$，对每个 $m\ge 1$ 均有 $\ker\widehat q\subseteq\operatorname{im}\widehat\iota+t^m\widehat B$。在商模 $Q=\widehat B/\operatorname{im}\widehat\iota$ 中取像（注意 $t^m Q=(t^m\widehat B+\operatorname{im}\widehat\iota)/\operatorname{im}\widehat\iota$），立得对每个 $m\ge 1$ 恒有
   $$
   E = \frac{\ker\widehat q}{\operatorname{im}\widehat\iota} \subseteq \frac{\operatorname{im}\widehat\iota+t^m\widehat B}{\operatorname{im}\widehat\iota} = t^m Q.
   $$
   因此 $\ker p_m = (E+t^m Q)/t^m Q = t^m Q/t^m Q = 0$，故 $p_m$ 为同构。

2. **计算 $\bigcap_{m\ge 1} t^m Q$**：
   **定理**：对任意指数列 $(\nu_n)_{n\ge 1}$，恒有
   $$
   \bigcap_{m\ge 1} t^m Q = E.
   $$
   *证明*：上段已证对每个 $m\ge 1$ 有 $E\subseteq t^m Q$，故 $E\subseteq\bigcap_{m\ge 1} t^m Q$。反之，若 $x\in\bigcap_{m\ge 1} t^m Q$，则对一切 $m\ge 1$ 有 $p(x)\in p(t^m Q)=t^m\widehat C$，故由 3.1 节引理得 $p(x)\in\bigcap_{m\ge 1} t^m\widehat C=0$，即 $x\in\ker p=E$。（等价地，在 $\widehat B$ 中 $\bigcap_{m\ge 1}(t^m\widehat B+\operatorname{im}\widehat\iota)=\overline{\operatorname{im}\widehat\iota}=\ker\widehat q$，模去 $\operatorname{im}\widehat\iota$ 亦直接给出 $\bigcap_{m\ge 1}t^m Q=E$。）

---

### 3.3 确定 $\widehat Q,\widehat E$、对应典范映射 $\eta_Q,\eta_E$ 及完成映射 $\widehat p$

1. **$p$ 诱导的完成映射 $\widehat p$**：
   因对每个 $m\ge 1$，$p_m:Q/t^m Q\xrightarrow{\sim}\widehat C/t^m\widehat C$ 是同构且与过渡映射相容，取逆向极限知**对任意指数列 $(\nu_n)_{n\ge 1}$，$p$ 诱导的完成映射**
   $$
   \widehat p = \varprojlim_{m\ge 1} p_m : \widehat Q \xrightarrow{\;\sim\;} \widehat{\widehat C}
   $$
   **恒为 $S$ 模同构**。

2. **$\widehat Q$ 及典范映射 $\eta_Q:Q\to\widehat Q$**：
   将同构 $\widehat p:\widehat Q\xrightarrow{\sim}\widehat{\widehat C}$ 与 3.1 节同构 $\alpha=\eta_{\widehat C}^{-1}:\widehat{\widehat C}\xrightarrow{\sim}\widehat C$ 复合，得到显式 $S$ 模同构
   $$
   \beta := \eta_{\widehat C}^{-1}\circ\widehat p : \widehat Q \xrightarrow{\;\sim\;} \widehat C \xleftarrow[\;\sim\;]{\Phi_C} M_C
   $$
   （在相容商记录上，$\beta\bigl((x_m+t^m Q)_{m\ge 1}\bigr)=\bigl(\operatorname{pr}_m(p(x_m))\bigr)_{m\ge 1}\in\widehat C$）。
   由交换图表
   $$
   \widehat p\circ\eta_Q = \eta_{\widehat C}\circ p : Q \longrightarrow \widehat{\widehat C},
   $$
   可得 $\beta\circ\eta_Q = p : Q\to\widehat C$。换言之，在同构 $\beta:\widehat Q\xrightarrow{\sim}\widehat C$ 之下，**典范映射 $\eta_Q:Q\to\widehat Q$ 恰等同于满射 $p:Q\twoheadrightarrow\widehat C$**：
   - $\eta_Q = \widehat p^{-1}\circ\eta_{\widehat C}\circ p : Q\to\widehat Q$ **恒为满的 $S$ 线性映射**；
   - $\ker\eta_Q = \bigcap_{m\ge 1} t^m Q = E = \ker p$，从而 $\eta_Q$ 诱导同构 $Q/E\xrightarrow{\sim}\widehat Q$。

3. **$\widehat E$ 及典范映射 $\eta_E:E\to\widehat E$**：
   **定理**：对任意指数列 $(\nu_n)_{n\ge 1}$，$E$ 关于自身的 $t$ 进拓扑恒既分离又完备；**典范映射 $\eta_E:E\xrightarrow{\sim}\widehat E$ 恒为 $S$ 模同构**（从而复合 $\eta_E\circ\Phi_E : M_E=\widetilde K/M_A \xrightarrow{\sim}\widehat E$ 给出 $\widehat E$ 的具体坐标模型）。

   *证明*：利用 2.1 节的 $S$ 模同构 $\Phi_E:M_E=\widetilde K/M_A\xrightarrow{\sim} E$，只需证 $\bigcap_{m\ge 1} t^m M_E=0$ 且 $\eta_{M_E}:M_E\to\widehat{M_E}=\varprojlim_{m\ge 1} M_E/t^m M_E$ 满（由预备约定 3，$\eta_E$ 已是 $S$ 线性映射）。
   对每个 $m\ge 1$，置 $L_m := t^m\widetilde K + M_A \subseteq\widetilde K$，则 $t^m M_E = L_m/M_A$ 且 $M_E/t^m M_E \cong \widetilde K/L_m$。我们先证关键刻画：
   $$
   L_m = \bigl\{a=(a_n)_{n\ge 1}\in\widetilde K \;\big|\; \{n\ge 1 : a_n\notin t^m S\}\text{ 为有限集}\bigr\}.
   $$
   - **$\subseteq$**：若 $a=t^m d+u$（$d\in\widetilde K,u\in M_A$），则 $\{n:u_n\notin t^m S\}$ 有限，在该有限集之外均有 $a_n=t^m d_n+u_n\in t^m S$，故 $\{n:a_n\notin t^m S\}$ 有限。
   - **$\supseteq$**：设 $a\in\widetilde K$ 使 $F_m:=\{n\ge 1:a_n\notin t^m S\}$ 有限。对 $n\notin F_m$ 写 $a_n=t^m d_n$（$d_n\in S$）并令 $u_n=0$；对 $n\in F_m$ 令 $d_n=0$、$u_n=a_n$。因 $u=(u_n)_{n\ge 1}$ 仅在有限集 $F_m$ 上非零，有 $u\in M_A$。对任意 $r\ge 1$，若 $t^{\nu_n}d_n\notin t^r S$，则必有 $n\notin F_m$ 且 $t^{\nu_n}a_n=t^m(t^{\nu_n}d_n)\notin t^{m+r}S$；因 $a\in\widetilde K$，$\{n:t^{\nu_n}a_n\notin t^{m+r}S\}$ 有限，故 $\{n:t^{\nu_n}d_n\notin t^r S\}$ 有限，即 $d=(d_n)_{n\ge 1}\in\widetilde K$。于是 $a=t^m d+u\in t^m\widetilde K+M_A=L_m$。

   由此立得两件事：
   - **$\eta_{M_E}$ 的单射性（分离性）**：$a\in\bigcap_{m\ge 1} L_m \iff \forall m\ge 1,\ \{n\ge 1:a_n\notin t^m S\}\text{ 有限} \iff a\in M_A$。故 $\bigcap_{m\ge 1} L_m = M_A$，从而
     $$
     \ker\eta_{M_E} = \bigcap_{m\ge 1} t^m M_E = \left(\bigcap_{m\ge 1} L_m\right)/M_A = 0,\qquad\text{即 }\bigcap_{m\ge 1} t^m E = 0.
     $$
   - **$\eta_{M_E}$ 的满射性（完备性）**：任取相容记录 $(x^{(m)}+L_m)_{m\ge 1}\in\varprojlim_{m\ge 1}\widetilde K/L_m$，其中 $x^{(m)}\in\widetilde K$ 且对每个 $m\ge 1$ 有 $x^{(m+1)}-x^{(m)}\in L_m=t^m\widetilde K+M_A$。对每个 $m\ge 1$ 选分解
     $$
     x^{(m+1)}-x^{(m)} = t^m y^{(m)} + u^{(m)},\qquad y^{(m)}\in\widetilde K,\ u^{(m)}\in M_A.
     $$
     令 $\tilde x^{(1)}:=x^{(1)}$，当 $m\ge 2$ 时令 $\tilde x^{(m)}:=x^{(m)}-\sum_{j=1}^{m-1} u^{(j)}\in\widetilde K$。因 $\sum_{j=1}^{m-1} u^{(j)}\in M_A\subseteq L_m$，有 $\tilde x^{(m)}+L_m = x^{(m)}+L_m$（$\forall m\ge 1$），且 $\tilde x^{(m+1)}-\tilde x^{(m)}=t^m y^{(m)}$，归纳即得 $\tilde x^{(m)}=\tilde x^{(1)}+\sum_{j=1}^{m-1} t^j y^{(j)}$。
     对每个下标 $n\ge 1$，级数 $\tilde x^{(1)}_n+\sum_{j=1}^{\infty} t^j y^{(j)}_n$ 在 $S=k[[t]]$ 中收敛于唯一幂级数 $a_n\in S$。置 $a:=(a_n)_{n\ge 1}\in\prod_{n\ge 1} S$。对任意整数 $r\ge 1$ 及一切 $n\ge 1$，可写
     $$
     a_n = \tilde x^{(r)}_n + t^r z^{(r)}_n,\qquad z^{(r)}_n := \sum_{j=r}^{\infty} t^{j-r} y^{(j)}_n \in S.
     $$
     一方面，因 $\tilde x^{(r)}\in\widetilde K$，集合 $\{n\ge 1:t^{\nu_n}\tilde x^{(r)}_n\notin t^r S\}$ 有限，而对一切 $n\ge 1$ 有 $t^{\nu_n}(t^r z^{(r)}_n)=t^r(t^{\nu_n}z^{(r)}_n)\in t^r S$，故 $\{n\ge 1:t^{\nu_n}a_n\notin t^r S\}=\{n\ge 1:t^{\nu_n}\tilde x^{(r)}_n\notin t^r S\}$ 对一切 $r\ge 1$ 有限，即 $a\in\widetilde K$。
     另一方面，对每个 $m\ge 1$，$a-\tilde x^{(m)}\in\widetilde K$ 且对一切 $n\ge 1$ 有 $(a-\tilde x^{(m)})_n=t^m z^{(m)}_n\in t^m S$（例外下标集为空集），由 $L_m$ 的刻画知 $a-\tilde x^{(m)}\in L_m$，从而 $a+L_m=\tilde x^{(m)}+L_m=x^{(m)}+L_m$（$\forall m\ge 1$）。故 $\eta_{M_E}(a+M_A)=(x^{(m)}+L_m)_{m\ge 1}$。因此 $\eta_E:E\xrightarrow{\sim}\widehat E$ 是 $S$ 模同构。
     （附注：包含映射 $i:E\hookrightarrow Q$ 满足 $i(E)=E\subseteq t^m Q$，故其在每层诱导零映射 $E/t^m E\to Q/t^m Q$，完成映射 $\widehat i=0:\widehat E\to\widehat Q$。）

---

### 3.4 $E$ 自身的 $t$ 进拓扑与子空间拓扑的比较

记 $\mathcal{T}_{\mathrm{own}}$ 为 $E$ 自身的 $t$ 进拓扑（以 $\{t^m E\}_{m\ge 1}$ 为零点邻域基），记 $\mathcal{T}_{\mathrm{sub}}$ 为 $E$ 从 $Q$ 的 $t$ 进拓扑继承的子空间拓扑（以 $\{E\cap t^m Q\}_{m\ge 1}$ 为零点邻域基）。

1. **子空间拓扑 $\mathcal{T}_{\mathrm{sub}}$ 与两者的强弱比较**：
   由 3.2 节 $\bigcap_{m\ge 1} t^m Q = E$ 知，对一切 $m\ge 1$ 恒有 $E\cap t^m Q = E$。因此对任意 $e\in E$ 及 $Q$ 中任意包含 $e$ 的开集 $U$，存在 $m\ge 1$ 使 $e+t^m Q\subseteq U$，从而 $E=e+E\subseteq e+t^m Q\subseteq U$，即 $E\cap U=E$。故**对任意指数列 $(\nu_n)_{n\ge 1}$，子空间拓扑 $\mathcal{T}_{\mathrm{sub}}=\{\emptyset,E\}$ 恒为 $E$ 上的最粗拓扑（平凡拓扑 / 非离散拓扑）**。
   相应地，因 $t^m E\subseteq E=E\cap t^m Q$（$\forall m\ge 1$），**$\mathcal{T}_{\mathrm{own}}$ 总是细于或等于 $\mathcal{T}_{\mathrm{sub}}$**（$\mathcal{T}_{\mathrm{sub}}\subseteq\mathcal{T}_{\mathrm{own}}$）。

2. **自身拓扑 $\mathcal{T}_{\mathrm{own}}$ 的分离性**：
   由 3.3 节已证 $\bigcap_{m\ge 1} t^m E = 0$ 对一切 $(\nu_n)_{n\ge 1}$ 成立，故**对任意指数列 $(\nu_n)_{n\ge 1}$，$E$ 自身的 $t$ 进拓扑 $\mathcal{T}_{\mathrm{own}}$ 总是分离的**（Hausdorff）。
   （进一步，当 $\sup_{n\ge 1}\nu_n=\infty$ 时 $E\ne 0$ 且无挠，若某处 $t^m E=t^{m+1}E$，约去单射 $t^m$ 得 $E=tE$，进而 $E=\bigcap_{r\ge 1}t^r E=0$ 矛盾；故此时开子模链严格递降：$E\supsetneq tE\supsetneq t^2 E\supsetneq\cdots$，而子空间拓扑 $\mathcal{T}_{\mathrm{sub}}=\{\emptyset,E\}$ 不分离。）

3. **两种拓扑相同的充要条件**：
   **定理**：$\mathcal{T}_{\mathrm{own}}=\mathcal{T}_{\mathrm{sub}}$ **当且仅当指数列 $(\nu_n)_{n\ge 1}$ 有上界（$\sup_{n\ge 1}\nu_n<\infty$）**。
   *证明*：
   - **充分性**：若 $\sup_{n\ge 1}\nu_n<\infty$，则由 2.4 节知 $E=0$ 为单点模 $\{0\}$，其上拓扑唯一，必有 $\mathcal{T}_{\mathrm{own}}=\mathcal{T}_{\mathrm{sub}}=\{\emptyset,\{0\}\}$。
   - **必要性**：设 $\mathcal{T}_{\mathrm{own}}=\mathcal{T}_{\mathrm{sub}}=\{\emptyset,E\}$。对每个 $m\ge 1$，$t^m E$ 含 $0$ 且在 $\mathcal{T}_{\mathrm{own}}$ 中开，而 $\mathcal{T}_{\mathrm{sub}}$ 中唯一的非空开集为 $E$，故必有 $t^m E=E$（$\forall m\ge 1$）。结合分离性 $\bigcap_{m\ge 1} t^m E=0$ 得
     $$
     E = \bigcap_{m\ge 1} t^m E = 0.
     $$
     再由 2.4 节 $E=0$ 的充要条件，即得 $\sup_{n\ge 1}\nu_n<\infty$。
