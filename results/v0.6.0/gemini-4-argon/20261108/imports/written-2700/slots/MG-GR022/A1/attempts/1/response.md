下面对三个整体目标给出完整结论与严格证明。全文固定域 \(k\)，\(R=k[t]\)，\(S=k[[t]]\)，指数列 \((\nu_n)_{n\ge 1}\subset \mathbb{Z}_{\ge 0}\)。对任意 \(s=\sum_{i=0}^\infty c_i t^i\in S\)，定义其 \(t\)-进赋值（阶）为 \(\operatorname{ord}_t(s)=\inf\{i\ge 0\mid c_i\ne 0\}\)（约定 \(\operatorname{ord}_t(0)=+\infty\)）；对商环 \(S/t^\nu S\)（\(\nu\ge 0\)）中的元素 \(\gamma = s+t^\nu S\)，定义
\[
\operatorname{ord}_t(\gamma)=\begin{cases}
\operatorname{ord}_t(s), & \text{若 }\gamma\ne 0\text{（此时 }0\le \operatorname{ord}_t(s)<\nu\text{ 与代表元选取无关）},\\
+\infty, & \text{若 }\gamma=0.
\end{cases}
\]
特别地，对任意 \(m\ge 1\)，\(\gamma\in t^m(S/t^\nu S)\iff \gamma\equiv 0\pmod{t^{\min(m,\nu)}}\iff \operatorname{ord}_t(\gamma)\ge m\)。

---

## 目标 1：\(\widehat{A},\widehat{B},\widehat{C}\) 的坐标模型、完成列的正合性、闭包与纤维

### 1.1 具体坐标模型与相容商记录同构

对每个 \(m\ge 1\)，各模的第 \(m\) 层商模分别为
\[
A/t^mA = \bigoplus_{n\ge 1}(R/t^mR)\bar f_n,\qquad
B/t^mB = \bigoplus_{n\ge 1}(R/t^mR)\bar e_n,\qquad
C/t^mC = \bigoplus_{n\ge 1}\bigl(R/t^{\min(m,\nu_n)}R\bigr)\bar e_n.
\]
这里约定当 \(\nu_n=0\) 时 \(R/t^0R=0\)。定义如下三个 \(S\)-模（作为积模的子模）：
\[
\begin{aligned}
M_A &= \Bigl\{\alpha=(\alpha_n)_{n\ge 1}\in\prod_{n\ge 1}S \;\Big|\; \lim_{n\to\infty}\operatorname{ord}_t(\alpha_n)=+\infty\Bigr\}
     = \Bigl\{(\alpha_n)_{n\ge 1}\in\prod_{n\ge 1}S \;\Big|\; \forall m\ge 1,\;\alpha_n\in t^mS\text{ 对充分大的 }n\text{ 成立}\Bigr\},\\
M_B &= \Bigl\{\beta=(\beta_n)_{n\ge 1}\in\prod_{n\ge 1}S \;\Big|\; \lim_{n\to\infty}\operatorname{ord}_t(\beta_n)=+\infty\Bigr\}
     = \Bigl\{(\beta_n)_{n\ge 1}\in\prod_{n\ge 1}S \;\Big|\; \forall m\ge 1,\;\beta_n\in t^mS\text{ 对充分大的 }n\text{ 成立}\Bigr\},\\
M_C &= \Bigl\{\gamma=(\gamma_n)_{n\ge 1}\in\prod_{n\ge 1}S/t^{\nu_n}S \;\Big|\; \lim_{n\to\infty}\operatorname{ord}_t(\gamma_n)=+\infty\Bigr\}
     = \Bigl\{(\gamma_n)_{n\ge 1}\in\prod_{n\ge 1}S/t^{\nu_n}S \;\Big|\; \forall m\ge 1,\;\gamma_n\in t^m(S/t^{\nu_n}S)\text{ 对充分大的 }n\text{ 成立}\Bigr\}.
\end{aligned}
\]
其上的 \(S\)-模结构均为逐坐标乘法：对 \(s\in S\)，\(s\cdot(\alpha_n)_{n\ge 1}=(s\alpha_n)_{n\ge 1}\)，\(s\cdot(\beta_n)_{n\ge 1}=(s\beta_n)_{n\ge 1}\)，\(s\cdot(\gamma_n)_{n\ge 1}=(\bar s\gamma_n)_{n\ge 1}\)。

**定理 1.1（坐标模型与相容商记录的同构）**  
以下映射给出 \(S\)-模同构：
1. \(\Phi_A:M_A\stackrel{\sim}{\longrightarrow}\widehat{A}\)，\(\Phi_A\bigl((\alpha_n)_{n\ge 1}\bigr)=\Bigl(\sum_{n\ge 1}(\alpha_n\bmod t^mS)\bar f_n\Bigr)_{m\ge 1}\)；其逆映射 \(\Psi_A:\widehat{A}\stackrel{\sim}{\longrightarrow}M_A\) 将相容商记录 \(\bigl(\sum_{n\ge 1}a_{m,n}\bar f_n\bigr)_{m\ge 1}\)（\(a_{m,n}\in R/t^mR\cong S/t^mS\)）映为 \((\alpha_n)_{n\ge 1}\)，其中 \(\alpha_n=(a_{m,n})_{m\ge 1}\in\varprojlim_{m}R/t^mR = S\)。
2. \(\Phi_B:M_B\stackrel{\sim}{\longrightarrow}\widehat{B}\)，\(\Phi_B\bigl((\beta_n)_{n\ge 1}\bigr)=\Bigl(\sum_{n\ge 1}(\beta_n\bmod t^mS)\bar e_n\Bigr)_{m\ge 1}\)；其逆映射 \(\Psi_B:\widehat{B}\stackrel{\sim}{\longrightarrow}M_B\) 将相容商记录 \(\bigl(\sum_{n\ge 1}b_{m,n}\bar e_n\bigr)_{m\ge 1}\) 映为 \(\beta_n=(b_{m,n})_{m\ge 1}\in S\)。
3. \(\Phi_C:M_C\stackrel{\sim}{\longrightarrow}\widehat{C}\)，\(\Phi_C\bigl((\gamma_n)_{n\ge 1}\bigr)=\Bigl(\sum_{n\ge 1}(\gamma_n\bmod t^{\min(m,\nu_n)})\bar e_n\Bigr)_{m\ge 1}\)；其逆映射 \(\Psi_C:\widehat{C}\stackrel{\sim}{\longrightarrow}M_C\) 将相容商记录 \(\bigl(\sum_{n\ge 1}c_{m,n}\bar e_n\bigr)_{m\ge 1}\)（\(c_{m,n}\in R/t^{\min(m,\nu_n)}R\)）映为 \((\gamma_n)_{n\ge 1}\)，其中 \(\gamma_n = c_{\nu_n,n}\in R/t^{\nu_n}R\cong S/t^{\nu_n}S\)（当 \(\nu_n=0\) 时取 \(\gamma_n=0\)；等价地，取任意 \(m\ge \nu_n\) 时的 \(c_{m,n}\)）。

**证明**  
- 对 \(\widehat{A}\)（\(\widehat{B}\) 完全同理）：若 \(\alpha=(\alpha_n)_{n\ge 1}\in M_A\)，则对每个 \(m\ge 1\)，当 \(n\) 充分大时 \(\alpha_n\in t^mS\)，即 \(\alpha_n\bmod t^mS=0\)，故 \(\sum_{n\ge 1}(\alpha_n\bmod t^mS)\bar f_n\in\bigoplus_{n\ge 1}(R/t^mR)\bar f_n=A/t^mA\) 为有限和，且关于 \(m\) 相容，因此 \(\Phi_A(\alpha)\in\widehat{A}\)。反之，给定相容商记录 \(x=\bigl(\sum_{n\ge 1}a_{m,n}\bar f_n\bigr)_{m\ge 1}\in\widehat{A}\)，固定每个 \(n\ge 1\)，序列 \((a_{m,n})_{m\ge 1}\) 满足 \(a_{m+1,n}\bmod t^m = a_{m,n}\)，故唯一确定幂级数 \(\alpha_n\in\varprojlim_m R/t^mR = S\) 使得 \(\alpha_n\bmod t^mS=a_{m,n}\)。由于对每个固定的 \(m\ge 1\)，\(a_{m,n}=0\) 对充分大的 \(n\) 成立，故 \(\alpha_n\in t^mS\) 对充分大的 \(n\) 成立，即 \((\alpha_n)_{n\ge 1}\in M_A\)。显然 \(\Phi_A\) 与 \(\Psi_A\) 互逆，且保持由 \(S/(t^m)\) 诱导的 \(S\)-模结构。
- 对 \(\widehat{C}\)：若 \(\gamma=(\gamma_n)_{n\ge 1}\in M_C\)，则对每个 \(m\ge 1\)，当 \(n\) 充分大时 \(\gamma_n\in t^m(S/t^{\nu_n}S)\)，其在 \((S/t^{\nu_n}S)/t^m(S/t^{\nu_n}S)\cong R/t^{\min(m,\nu_n)}R\) 中的像 \(\gamma_n\bmod t^{\min(m,\nu_n)}=0\)，从而 \(\Phi_C(\gamma)\in\widehat{C}\) 良定义且关于 \(m\) 相容。反之，给定相容记录 \(z=\bigl(\sum_{n\ge 1}c_{m,n}\bar e_n\bigr)_{m\ge 1}\in\widehat{C}\)，固定 \(n\ge 1\)，当 \(m\ge \nu_n\) 时 \(\min(m,\nu_n)=\nu_n\)，过渡映射在第 \(n\) 个分量上为恒等映射，故存在唯一的 \(\gamma_n\in R/t^{\nu_n}R\cong S/t^{\nu_n}S\) 使得对一切 \(m\ge 1\) 都有 \(c_{m,n}=\gamma_n\bmod t^{\min(m,\nu_n)}\)。对每个 \(m\ge 1\)，因 \(c_{m,n}=0\) 对充分大的 \(n\) 成立，有 \(\gamma_n\in t^m(S/t^{\nu_n}S)\) 对充分大的 \(n\) 成立，故 \((\gamma_n)_{n\ge 1}\in M_C\)。\(\Phi_C\) 与 \(\Psi_C\) 互为逆同构。\(\square\)

**诱导映射的坐标表达式**  
在上述坐标模型 \(M_A,M_B,M_C\) 下：
1. **典范映射**：
   - \(\eta_A:A\to M_A\)，\(\sum_{n\ge 1}a_n f_n\mapsto (a_n)_{n\ge 1}\)（其中 \(a_n\in R\subset S\) 仅有限个非零）；
   - \(\eta_B:B\to M_B\)，\(\sum_{n\ge 1}b_n e_n\mapsto (b_n)_{n\ge 1}\)（其中 \(b_n\in R\subset S\) 仅有限个非零）；
   - \(\eta_C:C\to M_C\)，\(\sum_{n\ge 1}c_n \bar e_n\mapsto (c_n)_{n\ge 1}\)（其中 \(c_n\in R/t^{\nu_n}R\cong S/t^{\nu_n}S\) 仅有限个非零）。
2. **完成映射 \(\widehat{\iota}\) 与 \(\widehat{q}\)**：
   - \(\widehat{\iota}:M_A\to M_B\) 为逐坐标乘以 \(t^{\nu_n}\)：
     \[
     \widehat{\iota}\bigl((\alpha_n)_{n\ge 1}\bigr) = (t^{\nu_n}\alpha_n)_{n\ge 1};
     \]
   - \(\widehat{q}:M_B\to M_C\) 为逐坐标模 \(t^{\nu_n}S\) 约化：
     \[
     \widehat{q}\bigl((\beta_n)_{n\ge 1}\bigr) = (\beta_n\bmod t^{\nu_n}S)_{n\ge 1}.
     \]

---

### 1.2 完成列在各处的正合性及短正合的充要条件

考察完成后的序列
\[
0 \longrightarrow \widehat{A} \stackrel{\widehat{\iota}}{\longrightarrow} \widehat{B} \stackrel{\widehat{q}}{\longrightarrow} \widehat{C} \longrightarrow 0.
\]

**定理 1.2（完成列在各处的正合性）**
1. **在 \(\widehat{A}\) 处**：对任意指数列 \((\nu_n)_{n\ge 1}\)，\(\widehat{\iota}\) 恒为单射（即在 \(\widehat{A}\) 处恒正合）。
2. **在 \(\widehat{C}\) 处**：对任意指数列 \((\nu_n)_{n\ge 1}\)，\(\widehat{q}\) 恒为满射（即在 \(\widehat{C}\) 处恒正合）。
3. **在 \(\widehat{B}\) 处**：恒有 \(\operatorname{im}\widehat{\iota}\subseteq\ker\widehat{q}\)，且 \(\operatorname{im}\widehat{\iota}=\ker\widehat{q}\)（即在 \(\widehat{B}\) 处正合，亦即完成列短正合）当且仅当 **指数列 \((\nu_n)_{n\ge 1}\) 有界**（\(\sup_{n\ge 1}\nu_n<\infty\)）。

**证明**
1. 设 \(\alpha=(\alpha_n)_{n\ge 1}\in M_A\) 满足 \(\widehat{\iota}(\alpha)=(t^{\nu_n}\alpha_n)_{n\ge 1}=0\)。因 \(S=k[[t]]\) 是整环且 \(t^{\nu_n}\ne 0\)，对每个 \(n\ge 1\) 有 \(\alpha_n=0\)，故 \(\ker\widehat{\iota}=0\)。
2. 任取 \(\gamma=(\gamma_n)_{n\ge 1}\in M_C\)。对每个 \(n\ge 1\)，若 \(\gamma_n=0\)，取 \(\beta^{(0)}_n=0\in S\)；若 \(\gamma_n\ne 0\)，取 \(\beta^{(0)}_n\in R\subset S\) 为代表 \(\gamma_n\in R/t^{\nu_n}R\) 的唯一次数 \(<\nu_n\) 的多项式。于是对一切 \(n\ge 1\) 都有 \(\beta^{(0)}_n\bmod t^{\nu_n}S=\gamma_n\) 且 \(\operatorname{ord}_t(\beta^{(0)}_n)=\operatorname{ord}_t(\gamma_n)\)。因 \(\gamma\in M_C\)，有 \(\lim_{n\to\infty}\operatorname{ord}_t(\beta^{(0)}_n)=\lim_{n\to\infty}\operatorname{ord}_t(\gamma_n)=+\infty\)，故 \(\beta^{(0)}=(\beta^{(0)}_n)_{n\ge 1}\in M_B\) 且 \(\widehat{q}(\beta^{(0)})=\gamma\)。这证明 \(\widehat{q}\) 恒为满射。
3. 在 \(M_B\) 中，
   \[
   \ker\widehat{q} = \Bigl\{\beta=(\beta_n)_{n\ge 1}\in M_B \;\Big|\; \forall n\ge 1,\;\beta_n\in t^{\nu_n}S\Bigr\}
   = \Bigl\{(t^{\nu_n}\alpha_n)_{n\ge 1} \;\Big|\; \alpha_n\in S,\;\lim_{n\to\infty}\bigl(\nu_n+\operatorname{ord}_t(\alpha_n)\bigr)=+\infty\Bigr\},
   \]
   而
   \[
   \operatorname{im}\widehat{\iota} = \Bigl\{(t^{\nu_n}\alpha_n)_{n\ge 1} \;\Big|\; \alpha_n\in S,\;\lim_{n\to\infty}\operatorname{ord}_t(\alpha_n)=+\infty\Bigr\}.
   \]
   - **充分性**：若 \((\nu_n)_{n\ge 1}\) 有界，设 \(\nu_n\le M\)（\(\forall n\ge 1\)）。对任意 \(\beta=(t^{\nu_n}\alpha_n)_{n\ge 1}\in\ker\widehat{q}\)，由 \(\nu_n+\operatorname{ord}_t(\alpha_n)\to+\infty\) 及 \(\nu_n\le M\) 得 \(\operatorname{ord}_t(\alpha_n)\ge (\nu_n+\operatorname{ord}_t(\alpha_n))-M\to+\infty\)，故 \((\alpha_n)_{n\ge 1}\in M_A\)，从而 \(\beta\in\operatorname{im}\widehat{\iota}\)。
   - **必要性**：若 \((\nu_n)_{n\ge 1}\) 无界，则存在严格递增下标子列 \(1\le n_1<n_2<\cdots\) 使得 \(\nu_{n_k}\ge k\)（\(\forall k\ge 1\)）。令
     \[
     \alpha_n = \begin{cases} 1, & \text{若 }n=n_k\text{（某 }k\ge 1\text{）},\\ 0, & \text{其他},\end{cases}
     \qquad \beta_n = t^{\nu_n}\alpha_n.
     \]
     则当 \(n=n_k\) 时 \(\operatorname{ord}_t(\beta_{n_k})=\nu_{n_k}\ge k\to+\infty\)，其余坐标为 \(0\)，故 \(\beta=(\beta_n)_{n\ge 1}\in\ker\widehat{q}\)。但因 \(t^{\nu_n}\) 在 \(S\) 中非零因子，\(\beta_n=t^{\nu_n}\alpha_n\) 唯一决定 \(\alpha_{n_k}=1\)，其满足 \(\operatorname{ord}_t(\alpha_{n_k})=0\not\to+\infty\)，故 \(\alpha\notin M_A\)，即 \(\beta\notin\operatorname{im}\widehat{\iota}\)。\(\square\)

---

### 1.3 \(\operatorname{im}\widehat{\iota}\) 在 \(\widehat{B}\) 中的闭包与 \(\widehat{q}\) 的每个纤维

先确定 \(\widehat{B}\cong M_B\) 上的 \(t\)-进邻域基：对每个 \(m\ge 1\)，若 \(\beta=(\beta_n)_{n\ge 1}\in M_B\) 满足 \(\beta_n=t^m\tilde\beta_n\)（\(\tilde\beta_n\in S\)），则 \(\operatorname{ord}_t(\tilde\beta_n)=\operatorname{ord}_t(\beta_n)-m\to+\infty\)，故 \(\tilde\beta=(\tilde\beta_n)_{n\ge 1}\in M_B\)。因此
\[
t^m M_B = \Bigl\{(\beta_n)_{n\ge 1}\in M_B \;\Big|\; \forall n\ge 1,\;\beta_n\in t^m S\Bigr\} = \ker(\widehat{B}\to B/t^mB),
\]
即 \(\widehat{B}\) 的 \(t\)-进拓扑与逆向极限拓扑完全一致。

**定理 1.3（\(\operatorname{im}\widehat{\iota}\) 的闭包与 \(\widehat{q}\) 的纤维）**
1. 对任意指数列 \((\nu_n)_{n\ge 1}\)，\(\operatorname{im}\widehat{\iota}\) 在 \(\widehat{B}\) 的 \(t\)-进拓扑下的闭包恒为 \(\ker\widehat{q}\)：
   \[
   \overline{\operatorname{im}\widehat{\iota}} = \bigcap_{m\ge 1}\bigl(\operatorname{im}\widehat{\iota}+t^m\widehat{B}\bigr) = \ker\widehat{q}
   = \Bigl\{(\beta_n)_{n\ge 1}\in M_B \;\Big|\; \forall n\ge 1,\;\beta_n\in t^{\nu_n}S\Bigr\}.
   \]
2. 对每个 \(\gamma=(\gamma_n)_{n\ge 1}\in M_C\cong\widehat{C}\)，设 \(\beta^{(0)}=(\beta^{(0)}_n)_{n\ge 1}\in M_B\) 为定理 1.2 证明中构造的典范多项式提升（即 \(\beta^{(0)}_n\in R\)，\(\deg\beta^{(0)}_n<\nu_n\) 且 \(\beta^{(0)}_n\bmod t^{\nu_n}S=\gamma_n\)），则 \(\widehat{q}\) 在 \(\gamma\) 处的纤维为
   \[
   \begin{aligned}
   \widehat{q}^{-1}(\gamma) &= \beta^{(0)} + \ker\widehat{q} = \beta^{(0)} + \overline{\operatorname{im}\widehat{\iota}}\\
   &= \Bigl\{(\beta_n)_{n\ge 1}\in M_B \;\Big|\; \forall n\ge 1,\;\beta_n\equiv \gamma_n\pmod{t^{\nu_n}S}\Bigr\}\\
   &= \Bigl\{\bigl(\beta^{(0)}_n+t^{\nu_n}\alpha_n\bigr)_{n\ge 1} \;\Big|\; \alpha_n\in S,\;\lim_{n\to\infty}\bigl(\nu_n+\operatorname{ord}_t(\alpha_n)\bigr)=+\infty\Bigr\}.
   \end{aligned}
   \]

**证明**
1. 一方面，任取 \(\beta=(\beta_n)_{n\ge 1}\in\overline{\operatorname{im}\widehat{\iota}}=\bigcap_{m\ge 1}(\operatorname{im}\widehat{\iota}+t^m M_B)\)。对每个固定的 \(n\ge 1\)，取 \(m=\max(1,\nu_n)\)，则第 \(n\) 个坐标满足 \(\beta_n\in t^{\nu_n}S+t^m S = t^{\nu_n}S\)，故 \(\beta\in\ker\widehat{q}\)。  
   另一方面，任取 \(\beta=(t^{\nu_n}\alpha_n)_{n\ge 1}\in\ker\widehat{q}\) 及任意 \(m\ge 1\)。因 \(\operatorname{ord}_t(\beta_n)\to+\infty\)，存在 \(N_m\ge 1\) 使得当 \(n>N_m\) 时 \(\beta_n\in t^m S\)。令 \(\alpha^{(m)}_n=\alpha_n\)（\(1\le n\le N_m\)），\(\alpha^{(m)}_n=0\)（\(n>N_m\)），则 \(\alpha^{(m)}=(\alpha^{(m)}_n)_{n\ge 1}\in M_A\)，且 \(\beta-\widehat{\iota}(\alpha^{(m)})\) 的前 \(N_m\) 个坐标为 \(0\)、第 \(n>N_m\) 个坐标为 \(\beta_n\in t^m S\)，即 \(\beta-\widehat{\iota}(\alpha^{(m)})\in t^m M_B\)。故 \(\ker\widehat{q}\subseteq\bigcap_{m\ge 1}(\operatorname{im}\widehat{\iota}+t^m M_B)=\overline{\operatorname{im}\widehat{\iota}}\)。
2. 因 \(\widehat{q}(\beta^{(0)})=\gamma\)，作为线性映射的纤维有 \(\widehat{q}^{-1}(\gamma)=\beta^{(0)}+\ker\widehat{q}\)；又因 \(\operatorname{ord}_t(\beta^{(0)}_n)=\operatorname{ord}_t(\gamma_n)\to+\infty\)，条件 \(\operatorname{ord}_t(\beta^{(0)}_n+t^{\nu_n}\alpha_n)\to+\infty\) 与 \(\nu_n+\operatorname{ord}_t(\alpha_n)\to+\infty\) 等价。\(\square\)

---

## 目标 2：\(E\) 的坐标模型、\(j\) 的核与像、挠元、\(p\) 的满射性及右逆存在条件

### 2.1 \(E\) 的明确坐标模型

由定义，\(Q=\widehat{B}/\operatorname{im}\widehat{\iota}\)，\(p:Q\to\widehat{C}\) 由 \(\widehat{q}\) 诱导，故 \(E=\ker p = \ker\widehat{q}/\operatorname{im}\widehat{\iota}\)。记
\[
K_\nu = \Bigl\{\alpha=(\alpha_n)_{n\ge 1}\in\prod_{n\ge 1}S \;\Big|\; \lim_{n\to\infty}\bigl(\nu_n+\operatorname{ord}_t(\alpha_n)\bigr)=+\infty\Bigr\}.
\]
显然 \(M_A\subseteq K_\nu\) 为 \(S\)-子模。

**命题 2.1（\(E\) 的坐标模型）**  
在坐标模型 \(\widehat{B}\cong M_B\) 下，
\[
E \cong \frac{\ker\widehat{q}}{\operatorname{im}\widehat{\iota}}
= \frac{\bigl\{(\beta_n)_{n\ge 1}\in\prod_{n\ge 1}t^{\nu_n}S \;\big|\; \lim_{n\to\infty}\operatorname{ord}_t(\beta_n)=+\infty\bigr\}}{\bigl\{(\beta_n)_{n\ge 1}\in\prod_{n\ge 1}t^{\nu_n}S \;\big|\; \lim_{n\to\infty}(\operatorname{ord}_t(\beta_n)-\nu_n)=+\infty\bigr\}},
\]
且逐坐标乘以 \(t^{\nu_n}\) 诱导如下显式 \(S\)-模同构：
\[
\Theta_E: K_\nu/M_A \stackrel{\sim}{\longrightarrow} E,\qquad
(\alpha_n)_{n\ge 1}+M_A \longmapsto (t^{\nu_n}\alpha_n)_{n\ge 1}+\operatorname{im}\widehat{\iota}.
\]

**证明**  
映射 \(\prod_{n\ge 1}S\to\prod_{n\ge 1}t^{\nu_n}S\)，\((\alpha_n)_{n\ge 1}\mapsto(t^{\nu_n}\alpha_n)_{n\ge 1}\) 是 \(S\)-模同构，且将 \(K_\nu\) 映为 \(\ker\widehat{q}\)、将 \(M_A\) 映为 \(\operatorname{im}\widehat{\iota}\)，取商即得同构 \(\Theta_E\)。\(\square\)

---

### 2.2 典范映射 \(j:C\to Q\) 的核与像

**命题 2.2（\(j\) 的核与像）**  
对任意指数列 \((\nu_n)_{n\ge 1}\)：
1. \(\ker j = 0\)，即 \(j:C\to Q\) 恒为单射。
2. 在 \(Q = M_B/\operatorname{im}\widehat{\iota}\) 中，\(j\) 的像为
   \[
   \begin{aligned}
   \operatorname{im}j &= \frac{\eta_B(B)+\operatorname{im}\widehat{\iota}}{\operatorname{im}\widehat{\iota}}\\
   &= \Bigl\{[(\beta_n)_{n\ge 1}]\in Q \;\Big|\; \beta_n\in t^{\nu_n}S\text{ 对充分大的 }n\text{ 成立，且 }\lim_{n\to\infty}\bigl(\operatorname{ord}_t(\beta_n)-\nu_n\bigr)=+\infty\Bigr\}.
   \end{aligned}
   \]
   等价地，每个 \(x\in\operatorname{im}j\) 在 \(M_B\) 中有唯一的典范代表元 \((r_n)_{n\ge 1}\in\bigoplus_{n\ge 1}R\)，其中 \(\deg r_n<\nu_n\)（\(\forall n\ge 1\)）。

**证明**
1. 注意到对任意 \(b\in B\)，\(p(j(q(b)))=p(\eta_B(b)+\operatorname{im}\widehat{\iota})=\widehat{q}(\eta_B(b))=\eta_C(q(b))\)，即 \(p\circ j = \eta_C\)。因 \(C=\bigoplus_{n\ge 1}(R/t^{\nu_n}R)\bar e_n\)，\(\ker\eta_C=\bigcap_{m\ge 1}t^mC=\bigoplus_{n\ge 1}\bigcap_{m\ge 1}t^m(R/t^{\nu_n}R)=0\)，故 \(\eta_C\) 是单射，从而 \(\ker j\subseteq\ker(p\circ j)=\ker\eta_C=0\)。
2. 设 \(\beta=(\beta_n)_{n\ge 1}\in M_B\)。用带余除法将每个 \(\beta_n\in S\) 唯一写成 \(\beta_n = r_n + t^{\nu_n}\alpha_n\)，其中 \(r_n\in R\) 满足 \(\deg r_n<\nu_n\)，且 \(\alpha_n\in S\)。  
   - 若 \([\beta]\in\operatorname{im}j\)，则存在 \(b=(b_n)_{n\ge 1}\in\bigoplus_{n\ge 1}R\) 及 \(\tilde\alpha=(\tilde\alpha_n)_{n\ge 1}\in M_A\) 使得 \(\beta_n=b_n+t^{\nu_n}\tilde\alpha_n\)。当 \(n\) 充分大时 \(b_n=0\)，故 \(\beta_n=t^{\nu_n}\tilde\alpha_n\in t^{\nu_n}S\) 且 \(\operatorname{ord}_t(\beta_n)-\nu_n=\operatorname{ord}_t(\tilde\alpha_n)\to+\infty\)。  
   - 反之，若 \(\beta_n\in t^{\nu_n}S\) 对充分大的 \(n\) 成立且 \(\operatorname{ord}_t(\beta_n)-\nu_n\to+\infty\)，则当 \(n\) 充分大时 \(r_n=0\) 且 \(\operatorname{ord}_t(\alpha_n)=\operatorname{ord}_t(\beta_n)-\nu_n\to+\infty\)。于是 \(r=(r_n)_{n\ge 1}\in\bigoplus_{n\ge 1}R=\eta_B(B)\)，\(\alpha=(\alpha_n)_{n\ge 1}\in M_A\)，且 \(\beta = r+\widehat{\iota}(\alpha)\in\eta_B(B)+\operatorname{im}\widehat{\iota}\)，即 \([\beta]\in\operatorname{im}j\)。\(\square\)

---

### 2.3 \(Q\) 中被某个 \(t^r\)（\(r\ge 1\)）杀死的元素与 \(E\) 的 \(S\)-模挠性

对每个 \(r\ge 1\)，记 \(Q[t^r]=\{x\in Q\mid t^rx=0\}\)，并记 \(Q[t^\infty]=\bigcup_{r\ge 1}Q[t^r]\)。

**定理 2.3（\(Q\) 的 \(t\)-幂挠子模与 \(E\) 的无挠性）**  
对任意指数列 \((\nu_n)_{n\ge 1}\)：
1. 对每个固定的 \(r\ge 1\)，
   \[
   Q[t^r] = j\bigl(C[t^r]\bigr)
   = \Bigl\{[(\beta_n)_{n\ge 1}]\in Q \;\Big|\; \forall n\ge 1,\;t^r\beta_n\in t^{\nu_n}S,\;\text{且 }\lim_{n\to\infty}\bigl(\operatorname{ord}_t(\beta_n)-\nu_n\bigr)=+\infty\Bigr\}.
   \]
2. \(Q\) 中所有被某个 \(t^r\)（\(r\ge 1\)）杀死的元素全体恰好是 \(\operatorname{im}j\)（亦即 \(Q\) 的 \(S\)-模挠子模 \(Q_{\mathrm{tors}}\)）：
   \[
   Q[t^\infty] = \bigcup_{r\ge 1}Q[t^r] = \operatorname{im}j \cong C.
   \]
3. \(E\) 恒为**无挠 \(S\)-模**（即 \(\operatorname{Tor}_S(E)=0\)）。

**证明**
1. 设 \(x=[\beta]\in Q\)（\(\beta=(\beta_n)_{n\ge 1}\in M_B\)）。则 \(t^rx=0\iff t^r\beta\in\operatorname{im}\widehat{\iota}\iff\) 存在 \(\alpha=(\alpha_n)_{n\ge 1}\in M_A\) 使得对一切 \(n\ge 1\) 有 \(t^r\beta_n = t^{\nu_n}\alpha_n\)。在整环 \(S\) 中，这等价于对一切 \(n\ge 1\) 有 \(t^r\beta_n\in t^{\nu_n}S\)，且 \(\alpha_n=t^{r-\nu_n}\beta_n\) 满足 \(\lim_{n\to\infty}\operatorname{ord}_t(\alpha_n)=\lim_{n\to\infty}(\operatorname{ord}_t(\beta_n)+r-\nu_n)=+\infty\)，即 \(\lim_{n\to\infty}(\operatorname{ord}_t(\beta_n)-\nu_n)=+\infty\)。特别地，当 \(n\) 充分大时 \(\operatorname{ord}_t(\beta_n)-\nu_n\ge 0\)，即 \(\beta_n\in t^{\nu_n}S\)。由命题 2.2(2) 知 \(x\in\operatorname{im}j\)；再由 \(j\) 单射知 \(x=j(c)\) 满足 \(t^rx=0\iff c\in C[t^r]\)。
2. 对任意 \(c=\sum_{n=1}^N c_n\bar e_n\in C\)，取 \(r=\max\bigl(\{1\}\cup\{\nu_1,\dots,\nu_N\}\bigr)\ge 1\)，则 \(t^rc=0\)，故 \(t^rj(c)=j(t^rc)=0\)。结合第 1 条即得 \(\bigcup_{r\ge 1}Q[t^r]=j\bigl(\bigcup_{r\ge 1}C[t^r]\bigr)=j(C)=\operatorname{im}j\)。又因 \(S=k[[t]]\) 中每个非零元均形如 \(s=ut^r\)（\(u\in S^\times\)，\(r\ge 0\)），被 \(s\) 消灭等价于被 \(t^r\) 消灭，故 \(Q_{\mathrm{tors}}=Q[t^\infty]=\operatorname{im}j\)。
3. 若 \(x\in E=\ker p\) 是 \(S\)-挠元，则存在 \(s=ut^r\in S\setminus\{0\}\)（\(u\in S^\times,r\ge 0\)）使得 \(sx=0\)，从而 \(t^{\max(r,1)}x=0\)，故 \(x\in Q[t^\infty]=\operatorname{im}j\)。于是 \(x=j(c)\)（\(c\in C\)），且 \(0=p(x)=p(j(c))=\eta_C(c)\)。由 \(\eta_C\) 单射得 \(c=0\)，从而 \(x=0\)。（也可直接在坐标模型 \(E\cong K_\nu/M_A\) 中验证：若 \(ut^r[\alpha]=0\)，则 \(\operatorname{ord}_t(ut^r\alpha_n)=r+\operatorname{ord}_t(\alpha_n)\to+\infty\implies \operatorname{ord}_t(\alpha_n)\to+\infty\implies \alpha\in M_A\)。）故 \(E\) 恒为无挠 \(S\)-模。\(\square\)

---

### 2.4 \(p\) 的满射性、\(E=0\) 及 \(p\) 存在 \(S\)-线性右逆的充要条件

**定理 2.4**
1. **\(p\) 的满射性**：对任意指数列 \((\nu_n)_{n\ge 1}\)，\(p:Q\to\widehat{C}\) 恒为满射。
2. **\(E=0\) 的充要条件**：\(E=0\) 当且仅当 **\((\nu_n)_{n\ge 1}\) 有界**（\(\sup_{n\ge 1}\nu_n<\infty\)）。
3. **\(p\) 存在 \(S\)-线性右逆的充要条件**：\(p:Q\to\widehat{C}\) 存在 \(S\)-线性右逆（即短正合列 \(0\to E\to Q\xrightarrow{p}\widehat{C}\to 0\) 作为 \(S\)-模分裂）当且仅当 **\((\nu_n)_{n\ge 1}\) 有界**（\(\sup_{n\ge 1}\nu_n<\infty\)）。

**证明**
1. 由定义 \(\operatorname{im}p = \operatorname{im}\widehat{q}\)；由定理 1.2(2) 知 \(\widehat{q}\) 恒为满射，故 \(p\) 恒为满射。
2. \(E=\ker\widehat{q}/\operatorname{im}\widehat{\iota}=0\iff \operatorname{im}\widehat{\iota}=\ker\widehat{q}\)，由定理 1.2(3) 知这当且仅当 \((\nu_n)_{n\ge 1}\) 有界。
3. - **充分性**：若 \((\nu_n)_{n\ge 1}\) 有界，则 \(E=\ker p=0\) 且 \(p\) 满射，故 \(p:Q\stackrel{\sim}{\to}\widehat{C}\) 是 \(S\)-模同构，\(p^{-1}\) 即为 \(S\)-线性右逆。
   - **必要性**：假设 \((\nu_n)_{n\ge 1}\) 无界，则存在严格递增下标子列 \(1\le n_1<n_2<\cdots\) 使得 \(\nu_{n_k}\ge k\ge 1\)（\(\forall k\ge 1\)）。在 \(M_C\cong\widehat{C}\) 中构造元素 \(\gamma=(\gamma_n)_{n\ge 1}\)：
     \[
     \gamma_n = \begin{cases}
     t^{\nu_{n_k}-1}\bmod t^{\nu_{n_k}}S, & \text{若 }n=n_k\text{（某 }k\ge 1\text{）},\\
     0, & \text{其他}.
     \end{cases}
     \]
     因 \(\operatorname{ord}_t(\gamma_{n_k})=\nu_{n_k}-1\ge k-1\to+\infty\)（\(k\to\infty\)），故 \(\gamma\in M_C\)。又因对每个 \(k\ge 1\) 都有 \(t\cdot t^{\nu_{n_k}-1}=t^{\nu_{n_k}}\equiv 0\pmod{t^{\nu_{n_k}}S}\)，故在 \(M_C\) 中有
     \[
     t\gamma = 0.
     \]
     但对一切 \(k\ge 1\) 都有 \(\gamma_{n_k}\ne 0\)，即 \(\gamma\) 有无穷多个非零坐标，故 \(\gamma\notin\operatorname{im}\eta_C\)。  
     若存在 \(S\)-线性右逆 \(\sigma:\widehat{C}\to Q\) 满足 \(p\circ\sigma=\mathrm{id}_{\widehat{C}}\)，则由 \(S\)-线性性得 \(t\sigma(\gamma)=\sigma(t\gamma)=0\)，即 \(\sigma(\gamma)\in Q[t]\)。由定理 2.3 知 \(Q[t]\subseteq\operatorname{im}j\)，故存在 \(c\in C\) 使得 \(\sigma(\gamma)=j(c)\)。两边作用 \(p\) 得
     \[
     \gamma = p(\sigma(\gamma)) = p(j(c)) = \eta_C(c) \in \operatorname{im}\eta_C,
     \]
     矛盾！因此当 \((\nu_n)_{n\ge 1}\) 无界时，\(p\) 不存在 \(S\)-线性右逆。\(\square\)

---

## 目标 3：模 \(t^m\) 诱导映射、\(\bigcap_{m\ge 1}t^mQ\)、\(\widehat{Q}\) 与 \(\widehat{E}\) 及 \(E\) 上的两种拓扑比较

### 3.1 由 \(p\) 诱导的映射 \(p_m:Q/t^mQ\to \widehat{C}/t^m\widehat{C}\) 与 \(\bigcap_{m\ge 1}t^mQ\)

**定理 3.1**  
对任意指数列 \((\nu_n)_{n\ge 1}\)：
1. 对每个 \(m\ge 1\)，恒有 \(E\subseteq t^mQ\)，且由 \(p\) 诱导的映射
   \[
   p_m: Q/t^mQ \stackrel{\sim}{\longrightarrow} \widehat{C}/t^m\widehat{C} \cong C/t^mC = \bigoplus_{n\ge 1}\bigl(R/t^{\min(m,\nu_n)}R\bigr)\bar e_n
   \]
   恒为 \(S/t^mS\)（即 \(R/t^mR\)）模**同构**。
2. 恒有
   \[
   \bigcap_{m\ge 1}t^mQ = E = \ker p.
   \]
   特别地，\(Q\) 的 \(t\)-进拓扑分离当且仅当 \((\nu_n)_{n\ge 1}\) 有界。

**证明**
1. 由定理 1.3(1)，在 \(\widehat{B}\) 中对每个 \(m\ge 1\) 都有 \(\ker\widehat{q}=\overline{\operatorname{im}\widehat{\iota}}\subseteq\operatorname{im}\widehat{\iota}+t^m\widehat{B}\)。在商模 \(Q=\widehat{B}/\operatorname{im}\widehat{\iota}\) 中模去 \(\operatorname{im}\widehat{\iota}\)，即得
   \[
   E = \ker\widehat{q}/\operatorname{im}\widehat{\iota} \subseteq \bigl(\operatorname{im}\widehat{\iota}+t^m\widehat{B}\bigr)/\operatorname{im}\widehat{\iota} = t^mQ.
   \]
   对短正合列 \(0\to E\to Q\xrightarrow{p}\widehat{C}\to 0\) 模 \(t^m\)，可得 \(p_m:Q/t^mQ\to\widehat{C}/t^m\widehat{C}\) 满射，且其核为 \((E+t^mQ)/t^mQ = t^mQ/t^mQ = 0\)（因 \(p^{-1}(t^m\widehat{C})=E+t^mQ=t^mQ\)）。故 \(p_m\) 恒为同构。此外，典范同构 \(\widehat{C}/t^m\widehat{C}\cong C/t^mC\) 将 \([(\gamma_n)_{n\ge 1}]\in M_C/t^mM_C\) 映为有限和 \(\sum_{n\ge 1}(\gamma_n\bmod t^{\min(m,\nu_n)})\bar e_n\)。
2. 由第 1 条知 \(E\subseteq\bigcap_{m\ge 1}t^mQ\)。反之，若 \(x\in\bigcap_{m\ge 1}t^mQ\)，则对每个 \(m\ge 1\) 有 \(p(x)\in p(t^mQ)=t^m\widehat{C}\)，故 \(p(x)\in\bigcap_{m\ge 1}t^m\widehat{C}\)。但在 \(M_C\) 中，若 \(\gamma=(\gamma_n)_{n\ge 1}\in\bigcap_{m\ge 1}t^m M_C\)，则对每个 \(n\ge 1\) 取 \(m=\max(1,\nu_n)\) 即得 \(\gamma_n\in t^{\nu_n}(S/t^{\nu_n}S)=0\)，故 \(\bigcap_{m\ge 1}t^m\widehat{C}=0\)。于是 \(p(x)=0\)，即 \(x\in\ker p=E\)。\(\square\)

---

### 3.2 \(\widehat{Q},\widehat{E}\)、对应典范映射 \(\eta_Q,\eta_E\) 及 \(p\) 诱导的完成映射 \(\widehat{p}\)

我们先刻画 \(E\cong K_\nu/M_A\) 自身的 \(t\)-进滤过 \(\{t^mE\}_{m\ge 1}\)。对每个 \(m\ge 1\)，令
\[
K_{\nu,m} = \Bigl\{\alpha=(\alpha_n)_{n\ge 1}\in K_\nu \;\Big|\; \alpha_n\in t^m S\text{ 对充分大的 }n\text{ 成立}\Bigr\}.
\]

**引理 3.2**  
在同构 \(\Theta_E:K_\nu/M_A\stackrel{\sim}{\longrightarrow}E\) 下，对每个 \(m\ge 1\) 都有
\[
t^m(K_\nu/M_A) = K_{\nu,m}/M_A,\qquad \bigcap_{m\ge 1}K_{\nu,m} = M_A.
\]

**证明**  
- 若 \([\alpha]\in t^m(K_\nu/M_A)\)，则存在 \(\tilde\alpha\in K_\nu\) 及 \(\mu\in M_A\) 使得 \(\alpha=t^m\tilde\alpha+\mu\)。因 \(\mu\in M_A\)，当 \(n\) 充分大时 \(\mu_n\in t^mS\)，故 \(\alpha_n=t^m\tilde\alpha_n+\mu_n\in t^mS\)，即 \(\alpha\in K_{\nu,m}\)。
- 反之，若 \(\alpha=(\alpha_n)_{n\ge 1}\in K_{\nu,m}\)，则存在 \(N\ge 1\) 使得当 \(n>N\) 时 \(\alpha_n=t^m\tilde\alpha_n\)（\(\tilde\alpha_n\in S\)）。对 \(1\le n\le N\) 置 \(\tilde\alpha_n=0,\mu_n=\alpha_n\)；对 \(n>N\) 置 \(\mu_n=0\)。则当 \(n>N\) 时 \(\nu_n+\operatorname{ord}_t(\tilde\alpha_n)=\nu_n+\operatorname{ord}_t(\alpha_n)-m\to+\infty\)，故 \(\tilde\alpha=(\tilde\alpha_n)_{n\ge 1}\in K_\nu\)，\(\mu=(\mu_n)_{n\ge 1}\in M_A\)，且 \(\alpha=t^m\tilde\alpha+\mu\)，即 \([\alpha]\in t^m(K_\nu/M_A)\)。
- 最后，\(\alpha\in\bigcap_{m\ge 1}K_{\nu,m}\iff \forall m\ge 1\)，\(\alpha_n\in t^mS\) 对充分大的 \(n\) 成立 \(\iff \alpha\in M_A\)。\(\square\)

**定理 3.3（\(\widehat{Q},\widehat{E}\)、典范映射与完成映射 \(\widehat{p}\)）**  
对任意指数列 \((\nu_n)_{n\ge 1}\)：
1. **\(p\) 诱导的完成映射 \(\widehat{p}\) 与 \(\widehat{Q},\eta_Q\)**：  
   完成映射 \(\widehat{p}=\varprojlim_{m\ge 1}p_m:\widehat{Q}\stackrel{\sim}{\longrightarrow}\widehat{\widehat{C}}\) 恒为 \(S\)-模**同构**。结合典范同构 \(\eta_{\widehat{C}}:\widehat{C}\stackrel{\sim}{\longrightarrow}\widehat{\widehat{C}}\)，有合成同构
   \[
   \eta_{\widehat{C}}^{-1}\circ\widehat{p}: \widehat{Q} \stackrel{\sim}{\longrightarrow} \widehat{C} \cong M_C.
   \]
   在此同构等同下，典范映射 \(\eta_Q:Q\to\widehat{Q}\cong\widehat{C}\) 恰为商映射 \(p:Q\to\widehat{C}\)；特别地，\(\eta_Q\) 恒为满射，且 \(\ker\eta_Q = \bigcap_{m\ge 1}t^mQ = E\)。
2. **\(\widehat{E}\) 与典范映射 \(\eta_E\)**：  
   对每个 \(m\ge 1\)，\(E/t^mE\cong K_\nu/K_{\nu,m}\)。典范映射
   \[
   \eta_E: E \stackrel{\sim}{\longrightarrow} \widehat{E} = \varprojlim_{m\ge 1} E/t^mE
   \]
   恒为 \(S\)-模**同构**（即 \(E\) 对其自身的 \(t\)-进拓扑总是分离且完备的），故 \(\widehat{E}\cong E\cong K_\nu/M_A\)。  
   （附注：若考虑包含映射 \(i:E\hookrightarrow Q\) 诱导的完成映射 \(\widehat{i}:\widehat{E}\to\widehat{Q}\)，由于 \(i(E)=E\subseteq t^mQ\) 对一切 \(m\ge 1\) 成立，第 \(m\) 层映射 \(i_m:E/t^mE\to Q/t^mQ\) 恒为零，故 \(\widehat{i}=0\)。）

**证明**
1. 由定理 3.1(1)，对每个 \(m\ge 1\)，\(p_m:Q/t^mQ\stackrel{\sim}{\to}\widehat{C}/t^m\widehat{C}\) 是同构，取逆向极限即得 \(\widehat{p}:\widehat{Q}\stackrel{\sim}{\to}\widehat{\widehat{C}}\) 为同构。由交换图 \(\widehat{p}\circ\eta_Q = \eta_{\widehat{C}}\circ p\) 及 \(\eta_{\widehat{C}}:\widehat{C}\stackrel{\sim}{\to}\widehat{\widehat{C}}\) 为同构，即知 \(\eta_{\widehat{C}}^{-1}\circ\widehat{p}\circ\eta_Q = p\)。
2. 先证 \(\eta_E\) 单射：由引理 3.2，\(\ker\eta_E = \bigcap_{m\ge 1}t^mE \cong \bigl(\bigcap_{m\ge 1}K_{\nu,m}\bigr)/M_A = M_A/M_A = 0\)。  
   再证 \(\eta_E\) 满射：任取相容序列 \(\bigl([\alpha^{(m)}]+t^mE\bigr)_{m\ge 1}\in\widehat{E}=\varprojlim_{m\ge 1}E/t^mE\)，其中 \(\alpha^{(m)}=(\alpha^{(m)}_n)_{n\ge 1}\in K_\nu\)。由相容性，对每个 \(m\ge 1\) 有 \(\alpha^{(m+1)}-\alpha^{(m)}\in K_{\nu,m}\)。又因 \(\alpha^{(m+1)}\in K_\nu\)，我们可归纳选取严格递增正整数列 \(1\le N_1<N_2<N_3<\cdots\)，使得对每个 \(m\ge 1\) 及一切 \(n>N_m\) 同时成立：
   \[
   \text{(a)}\;\; \alpha^{(m+1)}_n \equiv \alpha^{(m)}_n \pmod{t^mS},\qquad
   \text{(b)}\;\; \nu_n + \operatorname{ord}_t\bigl(\alpha^{(m+1)}_n\bigr) \ge m.
   \]
   现定义 \(\alpha=(\alpha_n)_{n\ge 1}\in\prod_{n\ge 1}S\) 如下：当 \(1\le n\le N_1\) 时取 \(\alpha_n=0\)；当 \(N_r<n\le N_{r+1}\)（\(r\ge 1\)）时取
   \[
   \alpha_n = \alpha^{(r+1)}_n.
   \]
   - 对 \(N_r<n\le N_{r+1}\)，因 \(n>N_r\)，由 (b)（取 \(m=r\)）得 \(\nu_n+\operatorname{ord}_t(\alpha_n)=\nu_n+\operatorname{ord}_t(\alpha^{(r+1)}_n)\ge r\)。当 \(n\to\infty\) 时 \(r\to\infty\)，故 \(\lim_{n\to\infty}(\nu_n+\operatorname{ord}_t(\alpha_n))=+\infty\)，即 \(\alpha\in K_\nu\)。
   - 固定任意 \(m\ge 1\)。对任意 \(n>N_m\)，设 \(r\ge m\) 为满足 \(N_r<n\le N_{r+1}\) 的唯一整数。对每个 \(j\in\{m,m+1,\dots,r\}\)，因 \(n>N_r\ge N_j\)，由 (a) 知 \(\alpha^{(j+1)}_n\equiv\alpha^{(j)}_n\pmod{t^jS}\)，从而模 \(t^mS\) 同余。逐次传递可得
     \[
     \alpha_n = \alpha^{(r+1)}_n \equiv \alpha^{(r)}_n \equiv \cdots \equiv \alpha^{(m+1)}_n \equiv \alpha^{(m)}_n \pmod{t^mS}\qquad (\forall n>N_m).
     \]
     故 \(\alpha-\alpha^{(m)}\in K_{\nu,m}\)，即 \([\alpha]-[\alpha^{(m)}]\in t^mE\)（\(\forall m\ge 1\)）。因此 \(\eta_E([\alpha])=\bigl([\alpha^{(m)}]+t^mE\bigr)_{m\ge 1}\)，\(\eta_E\) 为满射。\(\square\)

---

### 3.3 \(E\) 自身的 \(t\)-进拓扑与从 \(Q\) 继承的子空间拓扑之比较

记 \(\mathcal{T}_{\mathrm{own}}\) 为 \(E\) 自身的 \(t\)-进拓扑（以 \(\{t^mE\}_{m\ge 1}\) 为零点邻域基），记 \(\mathcal{T}_{\mathrm{sub}}\) 为 \(E\) 从 \(Q\) 的 \(t\)-进拓扑继承的子空间拓扑（以 \(\{E\cap t^mQ\}_{m\ge 1}\) 为零点邻域基）。

**定理 3.4（两种拓扑的比较、分离性及重合充要条件）**
1. **\(E\) 自身 \(t\)-进拓扑 \(\mathcal{T}_{\mathrm{own}}\) 的分离性**：对任意指数列 \((\nu_n)_{n\ge 1}\)，\(\bigcap_{m\ge 1}t^mE=0\)，故 \(\mathcal{T}_{\mathrm{own}}\) **恒为分离的**（且由定理 3.3(2) 知恒为完备的）。
2. **子空间拓扑 \(\mathcal{T}_{\mathrm{sub}}\) 的具体形态与比较**：对任意指数列 \((\nu_n)_{n\ge 1}\) 及任意 \(m\ge 1\)，由定理 3.1(1) 知 \(E\subseteq t^mQ\)，故
   \[
   E\cap t^mQ = E \qquad (\forall m\ge 1).
   \]
   因此，子空间拓扑 \(\mathcal{T}_{\mathrm{sub}}\) 恒为 \(E\) 上的**密着拓扑（平凡拓扑，开集仅有 \(\varnothing\) 和 \(E\)）**，且自身拓扑 \(\mathcal{T}_{\mathrm{own}}\) 恒细于或等于子空间拓扑 \(\mathcal{T}_{\mathrm{sub}}\)（\(\mathcal{T}_{\mathrm{sub}}\subseteq\mathcal{T}_{\mathrm{own}}\)）。
3. **两种拓扑相同的充要条件**：\(\mathcal{T}_{\mathrm{own}}=\mathcal{T}_{\mathrm{sub}}\) 当且仅当 \(E=0\)，即当且仅当 **指数列 \((\nu_n)_{n\ge 1}\) 有界**（\(\sup_{n\ge 1}\nu_n<\infty\)）。当 \((\nu_n)_{n\ge 1}\) 无界时，\(E\ne 0\)，此时 \(\mathcal{T}_{\mathrm{own}}\) 是分离拓扑而 \(\mathcal{T}_{\mathrm{sub}}\) 是非分离的密着拓扑，\(\mathcal{T}_{\mathrm{own}}\) 严格细于 \(\mathcal{T}_{\mathrm{sub}}\)。

**证明**
1. 分离性 \(\bigcap_{m\ge 1}t^mE=0\) 已在引理 3.2 与定理 3.3(2) 中证明。
2. 由 \(t^mE\subseteq E = E\cap t^mQ\) 即知 \(\mathcal{T}_{\mathrm{sub}}\) 为密着拓扑且 \(\mathcal{T}_{\mathrm{sub}}\subseteq\mathcal{T}_{\mathrm{own}}\)。
3. 在 \(\mathcal{T}_{\mathrm{own}}\) 中单点集 \(\{0\}\) 的闭包为 \(\bigcap_{m\ge 1}t^mE=\{0\}\)；而在 \(\mathcal{T}_{\mathrm{sub}}\) 中单点集 \(\{0\}\) 的闭包为 \(\bigcap_{m\ge 1}(E\cap t^mQ)=E\)。故 \(\mathcal{T}_{\mathrm{own}}=\mathcal{T}_{\mathrm{sub}}\iff \{0\}=E\iff (\nu_n)_{n\ge 1}\) 有界（定理 2.4(2)）。\(\square\)
