### 预备约定与基本引理

在 ZFC 公理体系下展开讨论。对参数 $m \in \mathbb{Z}_{>0} \cup \{\infty\}$，指标条件 $0 \le n \le m$ 指非负整数 $n \in \mathbb{Z}_{\ge 0}$ 满足 $n \le m$（即当 $m \in \mathbb{Z}_{>0}$ 时 $n \in \{0,1,\ldots,m\}$，当 $m = \infty$ 时 $n$ 取遍全体非负整数 $\mathbb{Z}_{\ge 0}$）。记集合 $X$ 的幂集为 $\mathcal{P}(X)$，对子集 $A \subseteq X$ 记其特征函数为 $\mathbf{1}_A : X \to [2]$（当 $x \in A$ 时取 $1$，当 $x \notin A$ 时取 $0$）。有限集包含空集 $\varnothing$（$|\varnothing| = 0$）。

**定义（超滤子）** 对任意集合 $X$，$X$ 上的**超滤子**是指子集族 $\mathcal{U} \subseteq \mathcal{P}(X)$，满足：
1. $\varnothing \notin \mathcal{U}$ 且 $X \in \mathcal{U}$；
2. （向上封闭）若 $A \in \mathcal{U}$ 且 $A \subseteq B \subseteq X$，则 $B \in \mathcal{U}$；
3. （有限交封闭）若 $A, B \in \mathcal{U}$，则 $A \cap B \in \mathcal{U}$；
4. （完备二分性）对任意 $A \subseteq X$，$A \in \mathcal{U}$ 与 $X \setminus A \in \mathcal{U}$ 恰有一者成立（其中不兼容性已由 (1)(3) 保证）。

记 $X$ 上全体超滤子构成的集合为 $\operatorname{Ult}(X)$。注意当 $X = \varnothing$ 时，条件 (1) 要求 $\varnothing \notin \mathcal{U}$ 与 $\varnothing \in \mathcal{U}$ 同时成立，故 $\operatorname{Ult}(\varnothing) = \varnothing$；当 $X \neq \varnothing$ 时，对每个 $x \in X$，**主超滤子** $\mathcal{U}_x := \{A \subseteq X : x \in A\} \in \operatorname{Ult}(X)$。

我们先给出全文多处使用的两个基本引理及其证明：

**引理 0.1（有限分划唯一性）** 设 $X \neq \varnothing$，$\mathcal{U} \in \operatorname{Ult}(X)$。对任意正整数 $n \ge 1$ 及 $X$ 的两两不交有限分划 $X = \bigsqcup_{j=0}^{n-1} A_j$，存在唯一的 $j \in [n]$ 使得 $A_j \in \mathcal{U}$。
*证明*：若 $i \neq j$ 而 $A_i, A_j \in \mathcal{U}$，则 $\varnothing = A_i \cap A_j \in \mathcal{U}$，矛盾，故至多一个 $A_j \in \mathcal{U}$。若对所有 $j \in [n]$ 均有 $A_j \notin \mathcal{U}$，则由二分性知 $X \setminus A_j \in \mathcal{U}$（$0 \le j < n$）；由 $X \in \mathcal{U}$ 及有限交封闭性对 $n$ 归纳得 $\bigcap_{j=0}^{n-1}(X \setminus A_j) = X \setminus \bigcup_{j=0}^{n-1} A_j = \varnothing \in \mathcal{U}$，矛盾。$\square$

**引理 0.2（超滤子引理）** 设 $X$ 为集合，$\mathcal{F}_0 \subseteq \mathcal{P}(X)$ 为非空子集族，且满足**有限交性质**（FIP）：对 $\mathcal{F}_0$ 的任意非空有限子族 $\{B_1, \ldots, B_k\}$（$k \ge 1$），均有 $\bigcap_{i=1}^k B_i \neq \varnothing$。则 $X \neq \varnothing$，且存在 $\mathcal{U} \in \operatorname{Ult}(X)$ 使得 $\mathcal{F}_0 \subseteq \mathcal{U}$。
*证明*：取 $B_1 \in \mathcal{F}_0$，由 $k=1$ 时的 FIP 知 $\varnothing \neq B_1 \subseteq X$，故 $X \neq \varnothing$。令 $\mathfrak{F}$ 为 $X$ 上包含 $\mathcal{F}_0$ 的全体真滤子（满足超滤子定义中 (1)–(3) 的子集族）按包含关系构成的偏序集。令
$$\mathcal{F}_{\mathrm{gen}} := \Bigl\{A \subseteq X : \exists k \ge 1,\ \exists B_1, \ldots, B_k \in \mathcal{F}_0 \text{ 使 } \bigcap_{i=1}^k B_i \subseteq A\Bigr\},$$
由 FIP 知 $\varnothing \notin \mathcal{F}_{\mathrm{gen}}$，易验证 $\mathcal{F}_{\mathrm{gen}} \in \mathfrak{F}$，故 $\mathfrak{F}$ 非空。对 $\mathfrak{F}$ 中任意非空链 $\mathfrak{C}$（空链以 $\mathcal{F}_{\mathrm{gen}}$ 为上界），令 $\mathcal{M} = \bigcup_{\mathcal{F} \in \mathfrak{C}} \mathcal{F}$：因每个 $\mathcal{F} \in \mathfrak{C}$ 不含 $\varnothing$ 且含 $\mathcal{F}_0 \cup \{X\}$，故 $\varnothing \notin \mathcal{M}$ 且 $\mathcal{F}_0 \cup \{X\} \subseteq \mathcal{M}$；又若 $A_1, A_2 \in \mathcal{M}$，因 $\mathfrak{C}$ 全序，存在某 $\mathcal{F} \in \mathfrak{C}$ 同时包含 $A_1, A_2$，从而 $A_1 \cap A_2 \in \mathcal{F} \subseteq \mathcal{M}$。故 $\mathcal{M} \in \mathfrak{F}$ 为 $\mathfrak{C}$ 的上界。由 Zorn 引理（在 ZFC 中成立），$\mathfrak{F}$ 有极大元 $\mathcal{U}$。对任意 $A \subseteq X$，若 $A \notin \mathcal{U}$ 且 $X \setminus A \notin \mathcal{U}$，则由 $\mathcal{U}$ 的极大性，集合族 $\mathcal{U} \cup \{A\}$ 与 $\mathcal{U} \cup \{X \setminus A\}$ 均不具有 FIP；故存在 $C_1, C_2 \in \mathcal{U}$ 使得 $C_1 \cap A = \varnothing$ 且 $C_2 \cap (X \setminus A) = \varnothing$，于是 $C_1 \cap C_2 = (C_1 \cap C_2 \cap A) \cup (C_1 \cap C_2 \cap (X \setminus A)) = \varnothing \in \mathcal{U}$，矛盾。故 $\mathcal{U} \in \operatorname{Ult}(X)$ 且 $\mathcal{F}_0 \subseteq \mathcal{U}$。$\square$

---

## 目标 1：截断及其相容关系

### 1.1 $R_m(X)$ 的完全分类

按底集 $X$ 是否为空及参数 $m$ 的取值分类如下：

1. **空底集 $X = \varnothing$（任意 $m \in \mathbb{Z}_{>0} \cup \{\infty\}$）**：
   此时 $[0] = \varnothing$，映射集 $\operatorname{Map}(\varnothing, [0]) = \operatorname{Map}(\varnothing, \varnothing) = \{\operatorname{id}_\varnothing\}$ 是单点集，而陪域 $[0] = \varnothing$。非空集到空集不存在映射，故不存在 $r_0 : \operatorname{Map}(\varnothing, [0]) \to [0]$。因此对一切 $m \in \mathbb{Z}_{>0} \cup \{\infty\}$，
   $$R_m(\varnothing) = \varnothing.$$

2. **非空底集 $X \neq \varnothing$**：
   先考察 $n = 0$ 与 $n = 1$ 分量：
   - 当 $n = 0$ 时，$\operatorname{Map}(X, [0]) = \operatorname{Map}(X, \varnothing) = \varnothing$，故存在唯一的空映射 $r_0 = \varnothing_{\varnothing \to \varnothing} : \varnothing \to \varnothing$。对相容条件 $a(r_n(f)) = r_k(a \circ f)$：若 $n = 0$，不存在 $f : X \to [0]$；若 $n \ge 1, k = 0$，因 $[n] \neq \varnothing$，不存在 $a : [n] \to [0]$。故凡涉及 $0$ 的相容等式均空真成立。
   - 当 $n = 1$ 时，$[1] = \{0\}$，$\operatorname{Map}(X, [1]) = \{\mathbf{0}_X\}$（常值 $0$ 映射），故 $r_1 : \operatorname{Map}(X, [1]) \to [1]$ 唯一确定为 $r_1(\mathbf{0}_X) = 0$。

   现对 $m$ 进一步分类：
   - **情形 $m = 1$**：
     唯一数对 $r^{(1)}_X := (\varnothing_{\varnothing \to \varnothing}, r_1)$ 在 $n=k=1$ 时仅需核对 $a = \operatorname{id}_{[1]}$，显然成立。故 **$R_1(X) = \{r^{(1)}_X\}$ 为单点集**（对任意 $x \in X$ 均有 $r^{(1)}_X = \eta_{1,X}(x)$）。

   - **情形 $m = 2$**：
     定义正规自对偶布尔集函数族：
     $$\mathcal{S}(X) := \bigl\{\mu : \mathcal{P}(X) \to [2] \;\big|\; \mu(\varnothing) = 0,\ \text{且}\ \forall A \subseteq X,\ \mu(X \setminus A) = 1 - \mu(A)\bigr\}.$$
     **断言**：映射 $\Psi_{2,X} : R_2(X) \to \mathcal{S}(X)$，$r \mapsto \mu_r$（其中 $\mu_r(A) := r_2(\mathbf{1}_A)$）是**双射**。
     *证明*：因 $A \mapsto \mathbf{1}_A$ 是 $\mathcal{P}(X) \xrightarrow{\sim} \operatorname{Map}(X, [2])$ 的双射，且 $r_0, r_1$ 唯一确定，$r \in R_2(X)$ 由 $\mu_r : \mathcal{P}(X) \to [2]$ 唯一决定。核对 $1 \le n, k \le 2$ 的全部相容条件：
     - $(n,k)=(1,1)$ 及 $(n,k)=(2,1)$（仅常值 $0$ 映射 $[2] \to [1]$）均自动成立；
     - $(n,k)=(1,2)$：取 $a = c_0, c_1 : [1] \to [2]$（$c_i(0) = i$）作用于 $f = \mathbf{0}_X$，等价于 $r_2(\mathbf{0}_X) = 0$ 与 $r_2(\mathbf{1}_X) = 1$，即 $\mu_r(\varnothing) = 0$ 与 $\mu_r(X) = 1$；
     - $(n,k)=(2,2)$：$\operatorname{Map}([2],[2]) = \{c_0, c_1, \operatorname{id}_{[2]}, \sigma\}$，其中 $\sigma(t) = 1 - t$。$a = c_0, c_1$ 再次给出 $\mu_r(\varnothing) = 0, \mu_r(X) = 1$；$a = \operatorname{id}_{[2]}$ 平凡成立；$a = \sigma$ 给出对一切 $A \subseteq X$ 有 $1 - r_2(\mathbf{1}_A) = r_2(\sigma \circ \mathbf{1}_A) = r_2(\mathbf{1}_{X \setminus A})$，即 $\mu_r(X \setminus A) = 1 - \mu_r(A)$。
     注意由 $\mu(\varnothing) = 0$ 及补集关系自动推出 $\mu(X) = 1 - \mu(\varnothing) = 1$。故全部相容条件与 $\mu_r \in \mathcal{S}(X)$ 完全等价，$\Psi_{2,X}$ 为双射。$\square$

   - **情形 $m \ge 3$（含 $m = \infty$）**：
     **断言**：对每个 $m \ge 3$（含 $m = \infty$）及任意集合 $X$（含 $X = \varnothing$），存在典范双射 $\Phi_{m,X} : \operatorname{Ult}(X) \xrightarrow{\sim} R_m(X)$：当 $X = \varnothing$ 时为空映射；当 $X \neq \varnothing$ 时，对 $\mathcal{U} \in \operatorname{Ult}(X)$，令 $\Phi_{m,X}(\mathcal{U}) = r^{\mathcal{U}} = (r^{\mathcal{U}}_n)_{0 \le n \le m}$，其中 $r^{\mathcal{U}}_0 = \varnothing_{\varnothing \to \varnothing}$，而对 $1 \le n \le m$ 及 $f : X \to [n]$，由引理 0.1 定义 $r^{\mathcal{U}}_n(f)$ 为使 $f^{-1}(j) \in \mathcal{U}$ 的唯一 $j \in [n]$。
     *证明*：$X = \varnothing$ 时两边皆为空集。设 $X \neq \varnothing$：
     1. **良定义性（$r^{\mathcal{U}} \in R_m(X)$）**：对 $1 \le n, k \le m$，$f : X \to [n]$ 及 $a : [n] \to [k]$，设 $j = r^{\mathcal{U}}_n(f)$，则 $f^{-1}(j) \in \mathcal{U}$。因 $f^{-1}(j) \subseteq f^{-1}(a^{-1}(a(j))) = (a \circ f)^{-1}(a(j))$，由向上封闭性知 $(a \circ f)^{-1}(a(j)) \in \mathcal{U}$，由引理 0.1 的唯一性得 $r^{\mathcal{U}}_k(a \circ f) = a(j) = a(r^{\mathcal{U}}_n(f))$。
     2. **构造逆映射并证互逆**：任取 $r \in R_m(X)$，令 $\mu(A) := r_2(\mathbf{1}_A) \in [2]$ 及 $\mathcal{U}_r := \{A \subseteq X : \mu(A) = 1\}$。由 $m=2$ 情形知 $\mu(\varnothing) = 0,\ \mu(X) = 1$ 且 $\mu(X \setminus A) = 1 - \mu(A)$。今设 $A, B \subseteq X$ 满足 $A \cap B = \varnothing$，因 $m \ge 3$，可定义 $f : X \to [3]$ 为
        $$f(x) = \begin{cases} 1, & x \in A, \\ 2, & x \in B, \\ 0, & x \in X \setminus (A \cup B). \end{cases}$$
        取三个映射 $a_1 = \mathbf{1}_{\{1\}},\ a_2 = \mathbf{1}_{\{2\}},\ a_{12} = \mathbf{1}_{\{1,2\}} : [3] \to [2]$。由相容关系 $a(r_3(f)) = r_2(a \circ f)$ 得
        $$\mu(A) = \mathbf{1}_{\{1\}}(r_3(f)),\qquad \mu(B) = \mathbf{1}_{\{2\}}(r_3(f)),\qquad \mu(A \cup B) = \mathbf{1}_{\{1,2\}}(r_3(f)).$$
        因对每个 $t \in [3]$ 在 $\mathbb{Z}$ 中恒有 $\mathbf{1}_{\{1,2\}}(t) = \mathbf{1}_{\{1\}}(t) + \mathbf{1}_{\{2\}}(t)$，故对不交子集 $A, B \subseteq X$ 恒有**有限可加性** $\mu(A \cup B) = \mu(A) + \mu(B)$。由此验证 $\mathcal{U}_r \in \operatorname{Ult}(X)$：
        - $\mu(\varnothing)=0,\ \mu(X)=1 \implies \varnothing \notin \mathcal{U}_r,\ X \in \mathcal{U}_r$；
        - 若 $A \in \mathcal{U}_r$ 且 $A \subseteq C \subseteq X$，则 $1 \ge \mu(C) = \mu(A) + \mu(C \setminus A) = 1 + \mu(C \setminus A) \ge 1$，故 $\mu(C) = 1$，即 $C \in \mathcal{U}_r$；
        - 若 $A, D \in \mathcal{U}_r$，因 $A \setminus D \subseteq X \setminus D$ 且 $\mu(X \setminus D) = 1 - \mu(D) = 0$，由向上封闭性知 $\mu(A \setminus D) = 0$，从而 $1 = \mu(A) = \mu(A \cap D) + \mu(A \setminus D) = \mu(A \cap D)$，故 $A \cap D \in \mathcal{U}_r$；
        - 由 $\mu(X \setminus A) = 1 - \mu(A)$ 知 $X \setminus A \in \mathcal{U}_r \iff A \notin \mathcal{U}_r$。
        最后核对互逆：对任意 $1 \le n \le m$、$f : X \to [n]$，令 $j = r_n(f)$，取 $\delta_j = \mathbf{1}_{\{j\}} : [n] \to [2]$，则 $1 = \delta_j(r_n(f)) = r_2(\delta_j \circ f) = r_2(\mathbf{1}_{f^{-1}(j)}) = \mu(f^{-1}(j))$，即 $f^{-1}(j) \in \mathcal{U}_r$，故 $r_n(f) = r^{\mathcal{U}_r}_n(f)$，即 $\Phi_{m,X}(\mathcal{U}_r) = r$。反之，对 $\mathcal{U} \in \operatorname{Ult}(X)$，$\mathcal{U}_{r^{\mathcal{U}}} = \{A \subseteq X : \mathbf{1}_A^{-1}(1) \in \mathcal{U}\} = \mathcal{U}$。故 $\Phi_{m,X}$ 为双射。特别地，对 $x \in X$，$\eta_{m,X}(x) = \Phi_{m,X}(\mathcal{U}_x)$。$\square$

---

### 1.2 截断映射 $q_{m,k} : R_m(X) \to R_k(X)$（$m \ge k \ge 1$）的像与各纤维

1. **当 $X = \varnothing$ 时**：对一切 $m \ge k \ge 1$，$q_{m,k} : \varnothing \to \varnothing$ 为空双射，像为 $\varnothing$，不存在纤维。
2. **当 $X \neq \varnothing$ 时**：
   - **$m = k$（任意 $m \in \mathbb{Z}_{>0} \cup \{\infty\}$）**：$q_{m,m} = \operatorname{id}_{R_m(X)}$ 为恒等双射，像为 $R_m(X)$，对每个 $s \in R_m(X)$ 纤维为单点集 $\{s\}$。
   - **$m \ge k \ge 3$**：由定义直接有 $q_{m,k} \circ \Phi_{m,X} = \Phi_{k,X}$。因 $\Phi_{m,X}, \Phi_{k,X}$ 皆为双射，**$q_{m,k}$ 是双射**；其像为整个 $R_k(X)$，对每个 $s \in R_k(X)$ 纤维为单点集 $q_{m,k}^{-1}(s) = \{\Phi_{m,X}(\Phi_{k,X}^{-1}(s))\}$。
   - **$m \ge 3$ 且 $k = 2$**：在分类双射下，$\Psi_{2,X}(q_{m,2}(\Phi_{m,X}(\mathcal{U}))) = \mathbf{1}_{\mathcal{U}}$（其中 $\mathbf{1}_{\mathcal{U}}(A) = 1 \iff A \in \mathcal{U}$）。因 $\mathcal{U} = \{A \subseteq X : \mathbf{1}_{\mathcal{U}}(A) = 1\}$，**$q_{m,2}$ 为单射**。
     - **像**：$\operatorname{im}(q_{m,2}) = \bigl\{s \in R_2(X) : \mathcal{U}_s := \{A \subseteq X : s_2(\mathbf{1}_A) = 1\} \in \operatorname{Ult}(X)\bigr\}$，等价于满足不交有限可加性（$\forall A \cap B = \varnothing,\ \mu_s(A \cup B) = \mu_s(A) + \mu_s(B)$）的元素 $s \in R_2(X)$。（注：当 $|X| \in \{1,2\}$ 时 $|\mathcal{S}(X)| = |X| = |\operatorname{Ult}(X)|$，$q_{m,2}$ 为满射；当 $|X| \ge 3$ 时，任取互异三点 $x_1, x_2, x_3 \in X$ 并令 $\mu(A) = 1 \iff |A \cap \{x_1,x_2,x_3\}| \ge 2$，则 $\mu \in \mathcal{S}(X)$ 但 $\mu(\{x_1\}) = \mu(\{x_2\}) = 0 \neq 1 = \mu(\{x_1,x_2\})$，故 $q_{m,2}$ 非满射。）
     - **纤维**：对 $s \in R_2(X)$，若 $\mathcal{U}_s \in \operatorname{Ult}(X)$，则 $q_{m,2}^{-1}(s) = \{\Phi_{m,X}(\mathcal{U}_s)\}$ 为单点集；否则 $q_{m,2}^{-1}(s) = \varnothing$。
   - **$m \ge 2$ 且 $k = 1$**：因 $X \neq \varnothing$（取 $x \in X$ 即有 $\eta_{m,X}(x) \in R_m(X)$），$R_m(X) \neq \varnothing$ 而 $R_1(X) = \{r^{(1)}_X\}$ 为单点集。故 **$q_{m,1}$ 为满射**，像为 $R_1(X) = \{r^{(1)}_X\}$，唯一纤维为 $q_{m,1}^{-1}(r^{(1)}_X) = R_m(X)$（当 $m=2$ 时同构于 $\mathcal{S}(X)$，当 $m \ge 3$ 时同构于 $\operatorname{Ult}(X)$）。

---

### 1.3 与集合映射 $h : X \to Y$ 的相容性

设 $h : X \to Y$ 为任意集合映射：
1. **良定义性与函子性**：若 $X = \varnothing$，则 $R_m(\varnothing) = \varnothing$，$R_m(h) : \varnothing \to R_m(Y)$ 为唯一空映射；若 $X \neq \varnothing$（此时必有 $Y \neq \varnothing$），对任意 $r \in R_m(X)$、$0 \le n, k \le m$、$f : Y \to [n]$ 及 $a : [n] \to [k]$，有
   $$a\bigl((R_m(h)r)_n(f)\bigr) = a\bigl(r_n(f \circ h)\bigr) = r_k\bigl(a \circ (f \circ h)\bigr) = r_k\bigl((a \circ f) \circ h\bigr) = (R_m(h)r)_k(a \circ f),$$
   故 $R_m(h)r \in R_m(Y)$。对任意 $h_1 : X \to Y,\ h_2 : Y \to Z$，有 $(R_m(\operatorname{id}_X)r)_n(f) = r_n(f)$ 及
   $$\bigl(R_m(h_2 \circ h_1)r\bigr)_n(f) = r_n\bigl(f \circ h_2 \circ h_1\bigr) = (R_m(h_1)r)_n(f \circ h_2) = \bigl((R_m(h_2) \circ R_m(h_1))r\bigr)_n(f),$$
   即 $R_m$ 为范畴 $\mathbf{Set}$ 到自身的协变函子。特别地，当群 $G$ 左作用于 $X$ 时，由 $e_X = \operatorname{id}_X$ 及 $(g_1 g_2)_X = g_{1,X} \circ g_{2,X}$ 立即得 $e \cdot r = r$ 且 $(g_1 g_2) \cdot r = R_m(g_{1,X} \circ g_{2,X})r = g_1 \cdot (g_2 \cdot r)$，故 $g \cdot r := R_m(g_X)r$ 确实定义了 $G$ 在 $R_m(X)$ 上的左群作用。
2. **与截断及点值记录的自然性**：直接按分量定义核验得：对一切 $m \ge k \ge 1$，有 $q_{m,k} \circ R_m(h) = R_k(h) \circ q_{m,k}$（特别地，$q_{m,k}$ 为 $G$-等变映射）及 $q_{m,k} \circ \eta_{m,X} = \eta_{k,X}$；对 $x \in X$，$\bigl(R_m(h)\eta_{m,X}(x)\bigr)_n(f) = f(h(x)) = \eta_{m,Y}(h(x))_n(f)$，即 $R_m(h) \circ \eta_{m,X} = \eta_{m,Y} \circ h$（特别地，$\eta_{m,X}$ 为 $G$-等变映射）。
3. **分类双射下的显式相容表达**：当 $X = \varnothing$ 时映射均为空映射；当 $X \neq \varnothing$（从而 $Y \neq \varnothing$）时：
   - **$m = 1$**：$R_1(h)(r^{(1)}_X) = r^{(1)}_Y$。
   - **$m = 2$**：对 $r \in R_2(X)$ 与 $B \subseteq Y$，$\mu_{R_2(h)r}(B) = r_2(\mathbf{1}_B \circ h) = r_2(\mathbf{1}_{h^{-1}(B)}) = \mu_r(h^{-1}(B))$。即若令 $(h_*\mu)(B) := \mu(h^{-1}(B))$，则 $\Psi_{2,Y} \circ R_2(h) = h_* \circ \Psi_{2,X}$。
   - **$m \ge 3$**：对 $\mathcal{U} \in \operatorname{Ult}(X)$，定义推前超滤子 $h_*(\mathcal{U}) := \{B \subseteq Y : h^{-1}(B) \in \mathcal{U}\}$（由逆像保空集、全集、包含、交与补立知 $h_*(\mathcal{U}) \in \operatorname{Ult}(Y)$）。对 $1 \le n \le m$ 及 $f : Y \to [n]$，因 $(f \circ h)^{-1}(j) = h^{-1}(f^{-1}(j)) \in \mathcal{U} \iff f^{-1}(j) \in h_*(\mathcal{U})$，有
     $$R_m(h)\bigl(\Phi_{m,X}(\mathcal{U})\bigr) = \Phi_{m,Y}\bigl(h_*(\mathcal{U})\bigr),$$
     即 $\Phi_m : \operatorname{Ult} \Rightarrow R_m$ 为函子自然同构。特别地，群作用对应 $g \cdot \mathcal{U} := (g_X)_*(\mathcal{U}) = \{A \subseteq X : g^{-1}A \in \mathcal{U}\} = \{gB : B \in \mathcal{U}\}$。

---

### 1.4 有限 $G$ 集合上 $R_m(X)^G$ 的存在判准、精确基数及限制映射

设 $X$ 为有限 $G$ 集合，记 $q_{m,k}$ 在不动集上的限制为 $q_{m,k}^G : R_m(X)^G \to R_k(X)^G$。

1. **当 $X = \varnothing$ 时**：对所有 $m$ 均有 $R_m(\varnothing)^G = \varnothing$（永不存在，基数为 $0$），各 $q_{m,k}^G : \varnothing \to \varnothing$ 皆为空双射。
2. **当 $X \neq \varnothing$（有限，$|X| \ge 1$）时**：
   - **层级 $m = 1$**：$R_1(X) = \{r^{(1)}_X\}$ 为单点集，$G$ 在其上作用平凡。
     - **存在判准**：恒非空（只要 $X \neq \varnothing$）。
     - **精确基数**：$|R_1(X)^G| = 1$。

   - **层级 $m = 2$**：
     在 $\Psi_{2,X} : R_2(X) \xrightarrow{\sim} \mathcal{S}(X)$ 下，$(g \cdot \mu)(A) = \mu(g^{-1}A)$，故 $\mu \in \mathcal{S}(X)^G$ 当且仅当 $\mu$ 在 $G$ 作用于 $\mathcal{P}(X)$（由 $g \cdot A := gA$ 给出）的每个轨道 $[A] \in \mathcal{P}(X)/G$ 上取常值。因 $g(X \setminus A) = X \setminus gA$，取补集映射诱导出轨道集上的对合 $\complement : \mathcal{P}(X)/G \to \mathcal{P}(X)/G$，$[A] \mapsto [X \setminus A]$。
     - **存在判准**：以下三条等价，且任一条成立即为 $R_2(X)^G \neq \varnothing$ 的充要条件：
       1. 对合 $\complement$ 在 $\mathcal{P}(X)/G$ 上无不动点，即对一切 $g \in G$ 与 $A \subseteq X$ 均有 $gA \neq X \setminus A$；
       2. **对每个 $g \in G$，置换 $g_X \in \operatorname{Sym}(X)$ 在 $X$ 上的不相交轮换分解中至少含有一个奇数长度的轮换**（不动点视为长度 $1$ 的奇轮换）。
       *等价性证明*：若某 $g \in G$ 在有限非空集 $X$ 上的所有轮换皆为偶数长度，则在每个偶轮换 $(x_0, x_1, \ldots, x_{2t-1})$（$t \ge 1$，$g x_i = x_{i+1 \bmod 2t}$）上将偶下标点归入 $A$、奇下标点归入 $X \setminus A$，合起来即得 $A \subseteq X$ 使 $gA = X \setminus A$。反之，若存在 $g \in G$ 与 $A \subseteq X$ 使 $gA = X \setminus A$，因 $X$ 有限，任取 $x \in X$ 必落在 $g_X$ 的某最小正周期为 $\ell \ge 1$ 的轮换中（$g^\ell x = x$）；由归纳知 $g^r A$ 在 $r$ 为偶时等于 $A$、在 $r$ 为奇时等于 $X \setminus A$，若 $\ell$ 为奇则 $x \in A \iff g^\ell x \in g^\ell A = X \setminus A$，矛盾，故 $g_X$ 的所有轮换长度皆为偶数。若 (1) 不成立，取 $gA = X \setminus A$，则任何 $\mu \in \mathcal{S}(X)^G$ 必满足 $\mu(A) = \mu(gA) = \mu(X \setminus A) = 1 - \mu(A)$，无解；若 (1) 成立，如下所述必有解。
     - **精确基数**：
       - 若存在 $g \in G$ 在 $X$ 上仅有偶轮换，则 $|R_2(X)^G| = 0$。
       - 若每个 $g \in G$ 在 $X$ 上至少有一个奇轮换，则 $\complement$ 为有限集 $\mathcal{P}(X)/G$ 上无不动点的对合，故 $|\mathcal{P}(X)/G|$ 为偶数，$\mathcal{P}(X)/G$ 分解为 $\frac{1}{2}|\mathcal{P}(X)/G|$ 个二元配对 $\{[A], [X \setminus A]\}$。其中 $\{[\varnothing], [X]\}$（因 $X \neq \varnothing$ 二者不同）上强制 $\mu([\varnothing]) = 0,\ \mu([X]) = 1$；其余 $\frac{1}{2}|\mathcal{P}(X)/G| - 1$ 对上每对恰有 $(\mu([A]), \mu([X \setminus A])) \in \{(0,1),(1,0)\}$ 两种独立选择。
         进一步，令 $\overline{G} := \operatorname{im}(G \to \operatorname{Sym}(X))$ 为诱导的有限置换群（即使 $G$ 无限，因 $X$ 有限，$|\overline{G}| \le |X|! < \infty$），对 $u \in \overline{G}$ 记 $c(u)$ 为 $u$ 在 $X$ 上的轮换个数。子集 $A \subseteq X$ 满足 $u(A) = A$ 当且仅当 $A$ 是 $u$ 的若干轮换之并，故 $|\mathcal{P}(X)^u| = 2^{c(u)}$。由有限群 $\overline{G}$ 作用于有限集 $\mathcal{P}(X)$ 的 **Burnside 引理**（双计数 $\{(u, A) \in \overline{G} \times \mathcal{P}(X) : u(A) = A\}$：按 $u$ 求和为 $\sum_{u \in \overline{G}} |\mathcal{P}(X)^u|$，按轨道 $[A]$ 利用轨道-稳定子定理 $|[A]| \cdot |\operatorname{Stab}_{\overline{G}}(A)| = |\overline{G}|$ 求和为 $|\overline{G}| \cdot |\mathcal{P}(X)/\overline{G}|$）：
         $$|\mathcal{P}(X)/G| = |\mathcal{P}(X)/\overline{G}| = \frac{1}{|\overline{G}|}\sum_{u \in \overline{G}} 2^{c(u)}.$$
         故此时精确基数为
         $$|R_2(X)^G| = 2^{\frac{1}{2}|\mathcal{P}(X)/G| - 1} = 2^{\frac{1}{2|\overline{G}|}\sum_{u \in \overline{G}} 2^{c(u)} - 1}.$$

   - **层级 $m \ge 3$（含 $m = \infty$）**：
     **引理**：有限非空集 $X$ 上的每个超滤子 $\mathcal{U} \in \operatorname{Ult}(X)$ 皆为主超滤子。
     *证明*：对有限分划 $X = \bigsqcup_{x \in X} \{x\}$ 应用引理 0.1，得唯一 $x_0 \in X$ 使 $\{x_0\} \in \mathcal{U}$。对任意 $A \subseteq X$，若 $x_0 \in A$ 则 $\{x_0\} \subseteq A \implies A \in \mathcal{U}$；若 $x_0 \notin A$ 则 $\{x_0\} \subseteq X \setminus A \implies X \setminus A \in \mathcal{U} \implies A \notin \mathcal{U}$。故 $\mathcal{U} = \mathcal{U}_{x_0}$。$\square$
     又对 $x, y \in X$，$\{x\} \in \mathcal{U}_y \iff x = y$，故 $\eta_{m,X} : X \xrightarrow{\sim} R_m(X)$ 是 **$G$-等变双射**，限制到 $G$-不动点集即得双射 $\eta_{m,X}|_{X^G} : X^G \xrightarrow{\sim} R_m(X)^G$。
     - **存在判准**：$R_m(X)^G \neq \varnothing \iff X^G \neq \varnothing$。
     - **精确基数**：$|R_m(X)^G| = |X^G|$。

   - **各不动集合间的限制映射 $q_{m,k}^G : R_m(X)^G \to R_k(X)^G$（$X$ 有限非空）**：
     1. **$m \ge k \ge 3$ 或 $m = k$**：$q_{m,k}^G$ 是**双射**（当 $m \ge k \ge 3$ 时将 $\eta_{m,X}(x)$ 映为 $\eta_{k,X}(x)$，$x \in X^G$）。
     2. **$m \ge 3,\ k = 2$**：$q_{m,2}^G$ 是**单射**，像为 $\eta_{2,X}(X^G) \subseteq R_2(X)^G$（即对应 $G$-不动点主超滤子特征函数的子集）；对 $s \in \eta_{2,X}(X^G)$（设 $s = \eta_{2,X}(x),\ x \in X^G$）纤维为单点集 $\{\eta_{m,X}(x)\}$，对 $s \in R_2(X)^G \setminus \eta_{2,X}(X^G)$ 纤维为 $\varnothing$。（注意当 $X^G \neq \varnothing$ 时每个 $g_X$ 有不动点即长度 $1$ 的奇轮换，自动保证 $R_2(X)^G \neq \varnothing$。）
     3. **$m \ge 3,\ k = 1$**：$q_{m,1}^G : R_m(X)^G \to \{r^{(1)}_X\}$ 在 $X^G \neq \varnothing$ 时为满射（像为 $\{r^{(1)}_X\}$，唯一纤维为 $\eta_{m,X}(X^G)$），在 $X^G = \varnothing$ 时为空映射（像为 $\varnothing$，在 $r^{(1)}_X$ 处纤维为 $\varnothing$）。
     4. **$m = 2,\ k = 1$**：$q_{2,1}^G : R_2(X)^G \to \{r^{(1)}_X\}$ 在 $R_2(X)^G \neq \varnothing$（每个 $g_X$ 含奇轮换）时为满射（像为 $\{r^{(1)}_X\}$，纤维为整个 $R_2(X)^G$），否则为空映射（像与在 $r^{(1)}_X$ 处的纤维皆为 $\varnothing$）。

---

### 1.5 有限层不动记录延拓为完整不动记录的准确范围

同时从**层级参数 $m \in \mathbb{Z}_{>0}$ 的普适范围**与**低层单个记录的可延拓判准**两方面给出完整刻画：

1. **按层级参数 $m \in \mathbb{Z}_{>0}$ 的准确范围：$m \ge 3$**。
   - **当 $m \ge 3$ 时**：对**任意**群 $G$ 及**任意**（不必有限）$G$ 集合 $X$，由 1.2 与 1.3 知 $q_{\infty,m} : R_\infty(X) \xrightarrow{\sim} R_m(X)$ 是 $G$-等变双射（逆映射为 $\Phi_{\infty,X} \circ \Phi_{m,X}^{-1}$）。若 $s \in R_m(X)^G$，令 $r = \Phi_{\infty,X}(\Phi_{m,X}^{-1}(s)) \in R_\infty(X)$，则对任意 $g \in G$ 有 $q_{\infty,m}(g \cdot r) = g \cdot q_{\infty,m}(r) = g \cdot s = s = q_{\infty,m}(r)$，由 $q_{\infty,m}$ 单射得 $g \cdot r = r$，故 $r \in R_\infty(X)^G$。即 **$q_{\infty,m}^G : R_\infty(X)^G \xrightarrow{\sim} R_m(X)^G$ 恒为双射，每个 $m$ 层不动记录均可唯一延拓为完整不动记录**。
   - **当 $m = 1$ 或 $m = 2$ 时**：即便对有限 $G$ 集合也不成立。取 $3$ 阶循环群 $G = C_3$ 正则作用于 $X = [3]$（由轮换 $(0\;1\;2)$ 生成）：每个群元阶为 $1$ 或 $3$（无全偶轮换元），且 $|\mathcal{P}([3])/C_3| = \frac{1}{3}(2^3 + 2^1 + 2^1) = 4$，故 $|R_1([3])^{C_3}| = 1$，$|R_2([3])^{C_3}| = 2^{4/2 - 1} = 2$（即多数表决函数 $\mu_{\mathrm{maj}}(A) = \mathbf{1}_{|A| \ge 2}$ 与少数表决函数 $\mu_{\mathrm{min}}(A) = \mathbf{1}_{|A| \in \{1,3\}}$）；但 $[3]^{C_3} = \varnothing$，故 $R_\infty([3])^{C_3} = \varnothing$，$R_1([3])^{C_3}$ 与 $R_2([3])^{C_3}$ 中没有任何记录能延拓到 $R_\infty([3])^{C_3}$。

2. **$m = 1, 2$ 时具体不动记录可延拓的充要条件**（对任意 $G$ 集合 $X$）：
   - **$m = 2$**：因 $q_{\infty,2} : R_\infty(X) \to R_2(X)$ 为 $G$-等变单射，$s \in R_2(X)^G$ 可延拓到 $R_\infty(X)^G$（此时延拓唯一）当且仅当 $\mathcal{U}_s = \{A \subseteq X : s_2(\mathbf{1}_A) = 1\} \in \operatorname{Ult}(X)$（即 $\mu_s$ 满足不交有限可加性）；特别地，当 $X$ 有限时，充要条件为 $s \in \eta_{2,X}(X^G)$。
   - **$m = 1$**：当 $X \neq \varnothing$ 时，唯一元 $r^{(1)}_X \in R_1(X)^G$ 可延拓到 $R_\infty(X)^G$ 当且仅当 $R_\infty(X)^G \neq \varnothing$（当 $X$ 有限时等价于 $X^G \neq \varnothing$；一般 $X$ 的判准见目标 2.2）。

---

## 目标 2：完整不动记录的空间

### 2.1 置换的三染色引理与 $R_\infty(X)^G$ 的内在拓扑分类

先证明关于双射作用下不变超滤子的关键结构引理：

**引理 2.1（双射的三染色引理与超滤子不动点判准）** 设 $\sigma : X \to X$ 为任意集合 $X$ 上的双射，记 $\operatorname{Fix}(\sigma) := \{x \in X : \sigma(x) = x\}$。则：
1. 存在两两不交的分解 $X = \operatorname{Fix}(\sigma) \sqcup C_1 \sqcup C_2 \sqcup C_3$，使得对每个 $i \in \{1,2,3\}$ 均有 $\sigma(C_i) \cap C_i = \varnothing$；
2. 对任意 $\mathcal{U} \in \operatorname{Ult}(X)$，$\sigma_*(\mathcal{U}) = \mathcal{U}$ 当且仅当 $\operatorname{Fix}(\sigma) \in \mathcal{U}$。

*证明*：
(1) 若 $X = \varnothing$，取 $C_1=C_2=C_3=\varnothing$ 即成。设 $X \neq \varnothing$。因 $\sigma$ 为双射，$X \setminus \operatorname{Fix}(\sigma)$ 在循环置换群 $\langle \sigma \rangle = \{\sigma^k : k \in \mathbb{Z}\}$ 下不变，分解为不相交轨道族 $\{O_\alpha\}_{\alpha \in \Lambda}$（其中 $\Lambda$ 为集合，因 $\{O_\alpha\} \subseteq \mathcal{P}(X)$）。由选择公理，从每个轨道 $O_\alpha$ 中选取代表元 $x_\alpha \in O_\alpha$。固定 $\alpha \in \Lambda$，因 $x_\alpha \notin \operatorname{Fix}(\sigma)$，有 $|O_\alpha| \ge 2$：
- **若 $O_\alpha$ 无限**：映射 $\mathbb{Z} \to O_\alpha,\ k \mapsto \sigma^k(x_\alpha)$ 必为双射（否则若存在 $k < \ell$ 使 $\sigma^k(x_\alpha) = \sigma^\ell(x_\alpha)$，则 $\sigma^{\ell-k}(x_\alpha) = x_\alpha$，带余除法给出 $O_\alpha = \{\sigma^r(x_\alpha) : 0 \le r < \ell - k\}$ 有限，矛盾）。令
  $$C_{1,\alpha} := \{\sigma^{2m}(x_\alpha) : m \in \mathbb{Z}\},\quad C_{2,\alpha} := \{\sigma^{2m+1}(x_\alpha) : m \in \mathbb{Z}\},\quad C_{3,\alpha} := \varnothing,$$
  则 $O_\alpha = C_{1,\alpha} \sqcup C_{2,\alpha}$，且 $\sigma(C_{1,\alpha}) = C_{2,\alpha}$，$\sigma(C_{2,\alpha}) = C_{1,\alpha}$，$\sigma(C_{3,\alpha}) = \varnothing$，均与自身不交。
- **若 $O_\alpha$ 有限**：存在最小正整数 $d \ge 2$ 使 $\sigma^d(x_\alpha) = x_\alpha$，且 $\{0,1,\ldots,d-1\} \to O_\alpha,\ k \mapsto \sigma^k(x_\alpha)$ 为双射。
  - 当 $d = 2t$（$t \ge 1$）为偶数时，令 $C_{1,\alpha} := \{\sigma^{2m}(x_\alpha) : 0 \le m < t\}$，$C_{2,\alpha} := \{\sigma^{2m+1}(x_\alpha) : 0 \le m < t\}$，$C_{3,\alpha} := \varnothing$，则 $\sigma(C_{1,\alpha}) = C_{2,\alpha}$，$\sigma(C_{2,\alpha}) = C_{1,\alpha}$（因 $\sigma(\sigma^{2t-1}(x_\alpha)) = \sigma^{2t}(x_\alpha) = x_\alpha \in C_{1,\alpha}$），均与自身不交。
  - 当 $d = 2t + 1$（$t \ge 1$，因 $d \ge 2$）为奇数时，令
    $$C_{1,\alpha} := \{\sigma^{2m}(x_\alpha) : 0 \le m < t\},\quad C_{2,\alpha} := \{\sigma^{2m+1}(x_\alpha) : 0 \le m < t\},\quad C_{3,\alpha} := \{\sigma^{2t}(x_\alpha)\}.$$
    三者两两不交且并为 $O_\alpha$；同时 $\sigma(C_{1,\alpha}) = C_{2,\alpha}$（与 $C_{1,\alpha}$ 不交），$\sigma(C_{2,\alpha}) = \{\sigma^{2m}(x_\alpha) : 1 \le m \le t\} \subseteq C_{1,\alpha} \cup C_{3,\alpha}$（与 $C_{2,\alpha}$ 不交），$\sigma(C_{3,\alpha}) = \{x_\alpha\} \subseteq C_{1,\alpha}$（因 $t \ge 1$，与 $C_{3,\alpha}$ 不交）。
令 $C_i := \bigsqcup_{\alpha \in \Lambda} C_{i,\alpha}$（$i=1,2,3$）。因各轨道 $O_\alpha$ 在 $\sigma$ 下不变且互不相交，$\sigma(C_i) \cap C_i = \bigsqcup_{\alpha \in \Lambda} (\sigma(C_{i,\alpha}) \cap C_{i,\alpha}) = \varnothing$，且 $X = \operatorname{Fix}(\sigma) \sqcup C_1 \sqcup C_2 \sqcup C_3$。

(2) （$\Rightarrow$）设 $\sigma_*(\mathcal{U}) = \mathcal{U}$（此时必有 $X \neq \varnothing$）。由 (1) 及引理 0.1，$\operatorname{Fix}(\sigma), C_1, C_2, C_3$ 中恰有一者属于 $\mathcal{U}$。若某 $C_i \in \mathcal{U}$，因 $\sigma$ 为双射有 $\sigma^{-1}(\sigma(C_i)) = C_i \in \mathcal{U}$，故 $\sigma(C_i) \in \sigma_*(\mathcal{U}) = \mathcal{U}$，从而 $\varnothing = \sigma(C_i) \cap C_i \in \mathcal{U}$，矛盾！故必有 $\operatorname{Fix}(\sigma) \in \mathcal{U}$。
（$\Leftarrow$）设 $\operatorname{Fix}(\sigma) \in \mathcal{U}$。对任意 $A \subseteq X$，因在 $\operatorname{Fix}(\sigma)$ 上 $\sigma(x) = x$，有 $A \cap \operatorname{Fix}(\sigma) = \sigma^{-1}(A) \cap \operatorname{Fix}(\sigma)$。由 $\operatorname{Fix}(\sigma) \in \mathcal{U}$ 知
$$A \in \mathcal{U} \iff A \cap \operatorname{Fix}(\sigma) \in \mathcal{U} \iff \sigma^{-1}(A) \cap \operatorname{Fix}(\sigma) \in \mathcal{U} \iff \sigma^{-1}(A) \in \mathcal{U} \iff A \in \sigma_*(\mathcal{U}),$$
即 $\sigma_*(\mathcal{U}) = \mathcal{U}$。$\square$

**内在拓扑分类构造**：
对任意群 $G$ 与任意 $G$ 集合 $X$，对 $g \in G$ 记 $X^g := \{x \in X : gx = x\}$，对子群 $H \le G$ 记 $X^H := \{x \in X : \forall h \in H,\ hx = x\}$，并记 $G$ 的全体有限生成子群构成的集合为 $\mathcal{FG}(G)$（它是 $\mathcal{P}(G)$ 的子集，故为集合）。注意对任意有限个元 $g_1, \ldots, g_k \in G$，因点稳定子群 $\operatorname{Stab}_G(x) \le G$ 是子群，恒有 $\bigcap_{i=1}^k X^{g_i} = X^{\langle g_1, \ldots, g_k \rangle}$（对空族约定为 $X^{\{e\}} = X$）。

直接由 $X$ 及其 $G$-作用定义集合
$$\operatorname{Ult}_G(X) := \bigl\{\mathcal{U} \in \operatorname{Ult}(X) : \forall g \in G,\ X^g \in \mathcal{U}\bigr\} = \bigl\{\mathcal{U} \in \operatorname{Ult}(X) : \forall H \in \mathcal{FG}(G),\ X^H \in \mathcal{U}\bigr\},$$
并在 $\operatorname{Ult}_G(X)$ 上赋予由族 $\{\widehat{A} : A \subseteq X\}$（其中 $\widehat{A} := \{\mathcal{U} \in \operatorname{Ult}_G(X) : A \in \mathcal{U}\}$）作为开闭基生成的 Stone 拓扑（因 $\widehat{X} = \operatorname{Ult}_G(X)$，$\widehat{A} \cap \widehat{B} = \widehat{A \cap B}$ 且 $\operatorname{Ult}_G(X) \setminus \widehat{A} = \widehat{X \setminus A}$，该族确为拓扑基；当 $X = \varnothing$ 时 $\operatorname{Ult}_G(\varnothing) = \varnothing$ 取唯一空拓扑）。
（注：从布尔代数角度看，令理想 $\mathcal{I}_G(X) := \{A \subseteq X : \exists H \in \mathcal{FG}(G),\ A \cap X^H = \varnothing\}$，则 $\mathcal{U} \in \operatorname{Ult}(X)$ 属于 $\operatorname{Ult}_G(X)$ 当且仅当 $\mathcal{U} \cap \mathcal{I}_G(X) = \varnothing$，故 $\operatorname{Ult}_G(X)$ 同胚于商布尔代数 $\mathcal{P}(X)/\mathcal{I}_G(X)$ 的 Stone 超滤子空间。）

**定理 2.2（内在同胚分类）** 映射 $\Phi_{\infty,X}$ 诱导拓扑同胚
$$\Phi_{\infty,X}\big|_{\operatorname{Ult}_G(X)} : \operatorname{Ult}_G(X) \xrightarrow{\;\sim\;} R_\infty(X)^G.$$
*证明*：$X = \varnothing$ 时两边皆为空空间，显然同胚。设 $X \neq \varnothing$。
1. **双射性**：由 1.1 与 1.3，$\Phi_{\infty,X} : \operatorname{Ult}(X) \xrightarrow{\sim} R_\infty(X)$ 为 $G$-等变双射。对每个 $\mathcal{U} \in \operatorname{Ult}(X)$，应用引理 2.1(2) 于双射 $\sigma = g_X$（$\forall g \in G$），得
   $$\Phi_{\infty,X}(\mathcal{U}) \in R_\infty(X)^G \iff \forall g \in G,\ (g_X)_*(\mathcal{U}) = \mathcal{U} \iff \forall g \in G,\ X^g \in \mathcal{U} \iff \mathcal{U} \in \operatorname{Ult}_G(X).$$
2. **拓扑相容性（同胚）**：先赋予 $\operatorname{Ult}(X)$ 以 $U_A := \{\mathcal{U} \in \operatorname{Ult}(X) : A \in \mathcal{U}\}$（$A \subseteq X$）为基的 Stone 拓扑，则 $\operatorname{Ult}_G(X)$ 上的 $\{\widehat{A} : A \subseteq X\}$（$\widehat{A} = U_A \cap \operatorname{Ult}_G(X)$）恰为其子空间拓扑。在 $R_\infty(X)$ 上，每个 $[n]$ 取离散拓扑，全体观察 $\mathrm{ev}_{n,f} : r \mapsto r_n(f)$（$n \ge 0,\ f \in \operatorname{Map}(X,[n])$；其中 $n=0$ 时 $\operatorname{Map}(X,[0]) = \varnothing$ 无观察）生成的初始拓扑以单点原像族
   $$V_{n,f,j} := \{r \in R_\infty(X) : r_n(f) = j\} \qquad (n \ge 1,\ f \in \operatorname{Map}(X,[n]),\ j \in [n])$$
   为开子基（因 $[n]$ 中任意子集为单点集之并）。对任意 $n \ge 1,\ f : X \to [n],\ j \in [n]$，有
   $$\Phi_{\infty,X}^{-1}(V_{n,f,j}) = \{\mathcal{U} \in \operatorname{Ult}(X) : r^{\mathcal{U}}_n(f) = j\} = \{\mathcal{U} \in \operatorname{Ult}(X) : f^{-1}(j) \in \mathcal{U}\} = U_{f^{-1}(j)},$$
   故每个子基开集的原像为基开集，$\Phi_{\infty,X}$ 连续；反之，对任意基开集 $U_A$（$A \subseteq X$），有
   $$\Phi_{\infty,X}(U_A) = \{r \in R_\infty(X) : r_2(\mathbf{1}_A) = 1\} = V_{2,\mathbf{1}_A,1},$$
   故 $\Phi_{\infty,X}$ 为开映射。因此 $\Phi_{\infty,X} : \operatorname{Ult}(X) \xrightarrow{\sim} R_\infty(X)$ 是同胚，限制到对应子空间 $\operatorname{Ult}_G(X)$ 与 $R_\infty(X)^G$ 即为同胚。$\square$

---

### 2.2 $R_\infty(X)^G$ 非空的必要充分条件

**定理 2.3** 对任意群 $G$ 与任意 $G$ 集合 $X$，$R_\infty(X)^G \neq \varnothing$ 的必要充分条件是：**对 $G$ 的每个有限生成子群 $H \le G$，均有 $X^H \neq \varnothing$**（等价地说，$X \neq \varnothing$ 且集合族 $\{X^g : g \in G\}$ 具有有限交性质）。

*证明*：由定理 2.2，$R_\infty(X)^G \neq \varnothing \iff \operatorname{Ult}_G(X) \neq \varnothing$。
- **必要性**：若存在 $\mathcal{U} \in \operatorname{Ult}_G(X)$，则对任意有限生成子群 $H = \langle g_1, \ldots, g_k \rangle \le G$（$k \ge 0$；当 $k=0$ 时 $H = \{e\}$，$X^{\{e\}} = X \in \mathcal{U}$），由 $X^{g_i} \in \mathcal{U}$（$1 \le i \le k$）及有限交封闭性得 $X^H = X \cap \bigcap_{i=1}^k X^{g_i} \in \mathcal{U}$。因 $\varnothing \notin \mathcal{U}$，必有 $X^H \neq \varnothing$。
- **充分性**：设对一切 $H \in \mathcal{FG}(G)$ 均有 $X^H \neq \varnothing$。特别地取 $H = \{e\} \in \mathcal{FG}(G)$ 知 $X = X^{\{e\}} \neq \varnothing$。考察非空集族 $\mathcal{F}_0 := \{X^g : g \in G\} \subseteq \mathcal{P}(X)$（至少含 $X^e = X$）：对任意 $g_1, \ldots, g_k \in G$（$k \ge 1$），有 $\bigcap_{i=1}^k X^{g_i} = X^{\langle g_1, \ldots, g_k \rangle} \neq \varnothing$，即 $\mathcal{F}_0$ 满足有限交性质。由引理 0.2（超滤子引理），存在 $\mathcal{U} \in \operatorname{Ult}(X)$ 使得 $\mathcal{F}_0 \subseteq \mathcal{U}$，即 $\mathcal{U} \in \operatorname{Ult}_G(X)$，故 $\Phi_{\infty,X}(\mathcal{U}) \in R_\infty(X)^G \neq \varnothing$。$\square$

---

### 2.3 $\eta_{\infty,X}(X^G)$ 的闭包及其等于 $R_\infty(X)^G$ 的必要充分条件

**命题 2.4（闭包的显式确定）** 对任意 $G$ 集合 $X$，$\eta_{\infty,X}(X^G)$ 在 $R_\infty(X)$ 中的闭包为
$$\overline{\eta_{\infty,X}(X^G)} = \Phi_{\infty,X}\bigl(\{\mathcal{U} \in \operatorname{Ult}(X) : X^G \in \mathcal{U}\}\bigr) = \begin{cases} \varnothing, & X = \varnothing, \\ \{r \in R_\infty(X) : r_2(\mathbf{1}_{X^G}) = 1\}, & X \neq \varnothing. \end{cases}$$
*证明*：$X = \varnothing$ 时两边皆为 $\varnothing$。设 $X \neq \varnothing$。由定理 2.2 的证明，$\Phi_{\infty,X} : \operatorname{Ult}(X) \xrightarrow{\sim} R_\infty(X)$ 是同胚，且将 $\{\mathcal{U}_x : x \in X^G\}$ 映为 $\eta_{\infty,X}(X^G)$，故只需确定 $S := \{\mathcal{U}_x : x \in X^G\}$ 在 $\operatorname{Ult}(X)$ 中的闭包。因 $\{U_A : A \subseteq X\}$ 是 $\operatorname{Ult}(X)$ 的拓扑基，任一 $\mathcal{U} \in \operatorname{Ult}(X)$ 属于 $\overline{S}$ 当且仅当对所有 $A \in \mathcal{U}$ 均有 $U_A \cap S \neq \varnothing$，即存在 $x \in X^G$ 使 $\mathcal{U}_x \in U_A \iff x \in A$，亦即 $A \cap X^G \neq \varnothing$。
- 若 $X^G \in \mathcal{U}$，则对任意 $A \in \mathcal{U}$ 有 $A \cap X^G \in \mathcal{U}$，从而 $A \cap X^G \neq \varnothing$，故 $\mathcal{U} \in \overline{S}$；
- 若 $X^G \notin \mathcal{U}$，则 $X \setminus X^G \in \mathcal{U}$，取 $A = X \setminus X^G \in \mathcal{U}$ 得 $A \cap X^G = \varnothing$，故 $\mathcal{U} \notin \overline{S}$。
因此 $\overline{S} = \{\mathcal{U} \in \operatorname{Ult}(X) : X^G \in \mathcal{U}\}$，经 $\Phi_{\infty,X}$ 即为 $\{r \in R_\infty(X) : r_2(\mathbf{1}_{X^G}) = 1\}$。$\square$

**定理 2.5（闭包等于 $R_\infty(X)^G$ 的充要条件）** 对任意群 $G$ 与任意 $G$ 集合 $X$，
$$\overline{\eta_{\infty,X}(X^G)} = R_\infty(X)^G \iff \text{存在有限生成子群 } H \le G \text{ 使得 } X^H = X^G.$$
*证明*：当 $X = \varnothing$ 时，左边为 $\varnothing = \varnothing$ 成立，右边取 $H = \{e\}$ 有 $\varnothing^{\{e\}} = \varnothing = \varnothing^G$ 亦成立。以下设 $X \neq \varnothing$。注意因对一切 $g \in G$ 有 $X^G \subseteq X^g$，命题 2.4 与定理 2.2 给出包含关系 $\overline{\eta_{\infty,X}(X^G)} \subseteq R_\infty(X)^G$ 恒成立。
- **充分性（$\Leftarrow$）**：设存在有限生成子群 $H = \langle g_1, \ldots, g_k \rangle \le G$（$k \ge 0$）使 $X^H = X^G$。对任意 $\mathcal{U} \in \operatorname{Ult}_G(X)$，有 $X^G = X^H = X \cap \bigcap_{i=1}^k X^{g_i} \in \mathcal{U}$，故由命题 2.4 知 $\Phi_{\infty,X}(\mathcal{U}) \in \overline{\eta_{\infty,X}(X^G)}$。从而 $\overline{\eta_{\infty,X}(X^G)} = R_\infty(X)^G$。
- **必要性（$\Rightarrow$）**：采用逆否证明。假设对一切 $H \in \mathcal{FG}(G)$ 均有 $X^H \neq X^G$；因 $X^G \subseteq X^H$，这意味着对一切 $H \in \mathcal{FG}(G)$ 均有 $X^H \setminus X^G \neq \varnothing$。考察集族
  $$\mathcal{C} := \{X^H \setminus X^G : H \in \mathcal{FG}(G)\} \subseteq \mathcal{P}(X).$$
  因 $\{e\} \in \mathcal{FG}(G)$，$\mathcal{C}$ 非空；对任意有限个 $H_1, \ldots, H_m \in \mathcal{FG}(G)$（$m \ge 1$），子群 $K := \langle H_1 \cup \cdots \cup H_m \rangle$ 仍由这 $m$ 个子群各自的有限生成元之并有限生成，故 $K \in \mathcal{FG}(G)$，且
  $$\bigcap_{j=1}^m (X^{H_j} \setminus X^G) = \Bigl(\bigcap_{j=1}^m X^{H_j}\Bigr) \setminus X^G = X^K \setminus X^G \neq \varnothing.$$
  由引理 0.2，存在 $\mathcal{U} \in \operatorname{Ult}(X)$ 使 $\mathcal{C} \subseteq \mathcal{U}$。对每个 $g \in G$，因 $\langle g \rangle \in \mathcal{FG}(G)$，有 $X^{\langle g \rangle} \setminus X^G \in \mathcal{C} \subseteq \mathcal{U}$，而 $X^{\langle g \rangle} \setminus X^G \subseteq X^g$，故 $X^g \in \mathcal{U}$，即 $\mathcal{U} \in \operatorname{Ult}_G(X)$，$\Phi_{\infty,X}(\mathcal{U}) \in R_\infty(X)^G$。另一方面，$X \setminus X^G = X^{\{e\}} \setminus X^G \in \mathcal{C} \subseteq \mathcal{U}$，故 $X^G \notin \mathcal{U}$，由命题 2.4 知 $\Phi_{\infty,X}(\mathcal{U}) \notin \overline{\eta_{\infty,X}(X^G)}$。因此 $\overline{\eta_{\infty,X}(X^G)} \subsetneq R_\infty(X)^G$。$\square$

---

### 2.4 对所有 $G$ 集合均满足 $\overline{\eta_{\infty,X}(X^G)} = R_\infty(X)^G$ 的群 $G$ 分类

**定理 2.6** 群 $G$ 对其每个 $G$ 集合 $X$ 均满足 $\overline{\eta_{\infty,X}(X^G)} = R_\infty(X)^G$，**当且仅当 $G$ 是有限生成群**。

*证明*：
- **充分性**：若 $G$ 是有限生成群，则 $H = G$ 自身即为 $G$ 的有限生成子群，对任意 $G$ 集合 $X$ 显然有 $X^H = X^G$，由定理 2.5 知 $\overline{\eta_{\infty,X}(X^G)} = R_\infty(X)^G$ 恒成立。
- **必要性**：设 $G$ **不是**有限生成群，故 $G \notin \mathcal{FG}(G)$。在 ZFC 中，因 $\mathcal{FG}(G) \subseteq \mathcal{P}(G)$ 是集合，且对每个 $H \in \mathcal{FG}(G)$ 左陪集空间 $G/H$ 是 $G$ 集合（左乘作用 $g \cdot (aH) := (ga)H$），可构造不交并 $G$ 集合
  $$X := \bigsqcup_{H \in \mathcal{FG}(G)} G/H.$$
  1. **计算 $X^G$**：任取 $H \in \mathcal{FG}(G)$ 及陪集 $aH \in G/H$。若 $aH \in (G/H)^G$，则对任意 $g \in G$ 有 $(aga^{-1})aH = aH \implies g \in H$，故 $H = G$，与 $G \notin \mathcal{FG}(G)$ 矛盾。因此 $X^G = \varnothing$。
  2. **计算 $X^K$（$\forall K \in \mathcal{FG}(G)$）**：对任意有限生成子群 $K \in \mathcal{FG}(G)$，在求和项 $G/K \subseteq X$ 中，单位陪集 $eK$ 对所有 $k \in K$ 满足 $k \cdot (eK) = kK = eK$，故 $eK \in X^K$，从而 $X^K \neq \varnothing = X^G$。
  由定理 2.5，对此 $G$ 集合 $X$ 有 $\overline{\eta_{\infty,X}(X^G)} \neq R_\infty(X)^G$（事实上 $\overline{\eta_{\infty,X}(X^G)} = \varnothing$ 而 $R_\infty(X)^G \neq \varnothing$）。$\square$

---

### 2.5 可数群与可数底集的具体例子及全部不动记录刻画

**构造**：
- 取底集为可数无限集 $X := \mathbb{N} = \{0, 1, 2, \ldots\}$。
- 取群 $G := \bigoplus_{k=0}^\infty (\mathbb{Z}/2\mathbb{Z})$，即支撑有限的二元序列集合
  $$G = \bigl\{g = (g_k)_{k \in \mathbb{N}} \in \{0,1\}^{\mathbb{N}} : \operatorname{supp}(g) := \{k \in \mathbb{N} : g_k = 1\} \text{ 有限}\bigr\},$$
  群运算为逐坐标模 $2$ 加法 $\oplus$。因 $G = \bigcup_{N=0}^\infty \{g \in \{0,1\}^{\mathbb{N}} : \forall k \ge N,\ g_k = 0\}$ 是可数个大小为 $2^N$ 的有限集之并，$G$ 为可数群。
- 将每个 $x \in \mathbb{N}$ 唯一写为 $x = 2k + \varepsilon$（$k \in \mathbb{N},\ \varepsilon \in \{0,1\}$），定义 $G$ 在 $\mathbb{N}$ 上的左作用为
  $$g \cdot (2k + \varepsilon) := 2k + (\varepsilon \oplus g_k).$$
  显然零序列作用为恒等，且 $(g \oplus h) \cdot (2k + \varepsilon) = 2k + (\varepsilon \oplus g_k \oplus h_k) = g \cdot (h \cdot (2k + \varepsilon))$，群作用良定义。

**性质验证与全部不动记录的完整描述**：
1. **$X^G = \varnothing$**：对任意 $x = 2k + \varepsilon \in \mathbb{N}$，取第 $k$ 个标准基元 $e^{(k)} \in G$（$e^{(k)}_k = 1$，其余坐标为 $0$），则 $e^{(k)} \cdot (2k + \varepsilon) = 2k + (1 - \varepsilon) \neq 2k + \varepsilon$，故 $X^G = \varnothing$。
2. **各元素不动点集 $X^g$**：由 $g \cdot (2k + \varepsilon) = 2k + \varepsilon \iff g_k = 0 \iff k \notin \operatorname{supp}(g)$，得
   $$X^g = \mathbb{N} \setminus \bigcup_{k \in \operatorname{supp}(g)} \{2k, 2k+1\}.$$
   因 $\operatorname{supp}(g)$ 有限，对每个 $g \in G$，$X^g$ 皆为 $\mathbb{N}$ 的**余有限子集**；反之，对 $\mathbb{N}$ 的任意有限子集 $F \subseteq \mathbb{N}$，取 $N \in \mathbb{N}$ 使 $F \subseteq [2N]$，令 $g = e^{(0)} \oplus \cdots \oplus e^{(N-1)}$（当 $N=0$ 时取零元），则 $X^g = \mathbb{N} \setminus [2N] \subseteq \mathbb{N} \setminus F$。
3. **全部不动记录的刻画与非空性**：记 $\mathbb{N}$ 上全体**非主（自由）超滤子**为
   $$\operatorname{Ult}_{\mathrm{free}}(\mathbb{N}) := \bigl\{\mathcal{U} \in \operatorname{Ult}(\mathbb{N}) : \forall F \subseteq \mathbb{N}\text{ 有限},\ \mathbb{N} \setminus F \in \mathcal{U}\bigr\} = \operatorname{Ult}(\mathbb{N}) \setminus \{\mathcal{U}_x : x \in \mathbb{N}\}$$
   （注：若超滤子不含单点集 $\{x\}$，则含所有 $\mathbb{N} \setminus \{x\}$，由有限交封闭性含一切余有限集，反之亦然）。
   - 若 $\mathcal{U} \in \operatorname{Ult}_{\mathrm{free}}(\mathbb{N})$，因每个 $X^g$ 余有限，故对一切 $g \in G$ 有 $X^g \in \mathcal{U}$，即 $\mathcal{U} \in \operatorname{Ult}_G(\mathbb{N})$；
   - 若 $\mathcal{U} \in \operatorname{Ult}_G(\mathbb{N})$，对任意有限集 $F \subseteq \mathbb{N}$，取如上 $g \in G$ 使 $X^g \subseteq \mathbb{N} \setminus F$，由 $X^g \in \mathcal{U}$ 及向上封闭性知 $\mathbb{N} \setminus F \in \mathcal{U}$，故 $\mathcal{U} \in \operatorname{Ult}_{\mathrm{free}}(\mathbb{N})$。
   因此 $\operatorname{Ult}_G(\mathbb{N}) = \operatorname{Ult}_{\mathrm{free}}(\mathbb{N})$。因 $\mathbb{N}$ 的余有限子集族 $\mathcal{F}_{\mathrm{cofin}}$ 具有有限交性质（有限个有限集之并仍有限，而 $\mathbb{N}$ 无限），由引理 0.2 知 $\operatorname{Ult}_{\mathrm{free}}(\mathbb{N}) \neq \varnothing$，从而 $R_\infty(\mathbb{N})^G \neq \varnothing$。
   **全部不动记录 $R_\infty(\mathbb{N})^G$** 恰好是双射 $\Phi_{\infty,\mathbb{N}}$ 下 $\operatorname{Ult}_{\mathrm{free}}(\mathbb{N})$ 的像：即全体由某个自由超滤子 $\mathcal{U} \in \operatorname{Ult}_{\mathrm{free}}(\mathbb{N})$ 给出的族 $r^{\mathcal{U}} = (r^{\mathcal{U}}_n)_{n \ge 0}$，其中 $r^{\mathcal{U}}_0 = \varnothing_{\varnothing \to \varnothing}$，而对 $n \ge 1$ 及 $f : \mathbb{N} \to [n]$，$r^{\mathcal{U}}_n(f)$ 是唯一满足 $f^{-1}(j) \in \mathcal{U}$ 的 $j \in [n]$（其拓扑空间同胚于 Stone–Čech 剩余 $\beta\mathbb{N} \setminus \mathbb{N}$）。

---

## 目标 3：乘积比较

设 $(X_i)_{i \in I}$ 为一族 $G$ 集合，记 $X := \prod_{i \in I} X_i$（带对角作用 $(g \cdot x)_i = g \cdot x_i$；当 $I = \varnothing$ 时约定 $X = \{*\}$，带唯一平凡 $G$-作用），当 $i \in I$ 时记第 $i$ 投射为 $p_i : X \to X_i$。乘积空间 $\prod_{i \in I} R_\infty(X_i)^G$ 取乘积拓扑。

### 3.1 $\Pi_{(X_i)}$ 的良定义与连续性

1. **良定义性**：
   - 当 $I = \varnothing$ 时，$X = \{*\}$，$R_\infty(\{*\})^G = \{\eta_{\infty,\{*\}}(*)\}$ 为单点集，陪域 $\prod_{i \in \varnothing} R_\infty(X_i)^G = \{*\}$ 亦为单点集，空族 $(R_\infty(p_i)r)_{i \in \varnothing}$ 恰为陪域唯一元素，良定义（且为双射）。
   - 当 $I \neq \varnothing$ 时，对每个 $i \in I$、$g \in G$ 及 $x = (x_j)_{j \in I} \in X$，有 $p_i(g_X(x)) = g \cdot x_i = g_{X_i}(p_i(x))$，即 $p_i \circ g_X = g_{X_i} \circ p_i$。对任意 $r \in R_\infty(X)^G$，由 1.3 的函子性得
     $$g \cdot \bigl(R_\infty(p_i)r\bigr) = R_\infty(g_{X_i} \circ p_i)r = R_\infty(p_i \circ g_X)r = R_\infty(p_i)(g \cdot r) = R_\infty(p_i)r,$$
     故 $R_\infty(p_i)r \in R_\infty(X_i)^G$，从而 $(R_\infty(p_i)r)_{i \in I} \in \prod_{i \in I} R_\infty(X_i)^G$。（特别地，若某 $X_{i_0} = \varnothing$，则 $X = \varnothing$，定义域 $R_\infty(\varnothing)^G = \varnothing$ 且陪域 $\prod_{i \in I} R_\infty(X_i)^G = \varnothing$，$\Pi_{(X_i)} : \varnothing \to \varnothing$ 为良定义的空映射。）

2. **连续性**：
   先证对任意集合映射 $h : Z \to W$，$R_\infty(h) : R_\infty(Z) \to R_\infty(W)$ 连续：按定义，$R_\infty(W)$ 赋予使全部观察 $\mathrm{ev}_{n,f} : s \mapsto s_n(f)$（$n \ge 0,\ f \in \operatorname{Map}(W,[n])$）连续的最弱拓扑；对每个观察有 $(\mathrm{ev}_{n,f} \circ R_\infty(h))(r) = r_n(f \circ h) = \mathrm{ev}_{n, f \circ h}(r)$，此为 $R_\infty(Z)$ 上的连续观察，由初始拓扑泛性质知 $R_\infty(h)$ 连续。限制定义域与陪域至子空间知，对每个 $i \in I$，分量映射 $\mathrm{pr}_i \circ \Pi_{(X_i)} = R_\infty(p_i)|_{R_\infty(X)^G} : R_\infty(X)^G \to R_\infty(X_i)^G$ 连续（$I = \varnothing$ 时该条件空真成立）。由乘积拓扑泛性质，$\Pi_{(X_i)}$ 连续。

---

### 3.2 $\Pi_{(X_i)}$ 是否总为满射的判定与证明

**结论**：**是**，在 ZFC 中，对**任意**群 $G$ 及**任意**集合指标族 $(X_i)_{i \in I}$，$\Pi_{(X_i)}$ **恒为满射**。

*证明*：
- 若 $I = \varnothing$，由 3.1 知 $\Pi_\varnothing : \{*\} \to \{*\}$ 为双射，特别地为满射。
- 若陪域 $\prod_{i \in I} R_\infty(X_i)^G = \varnothing$（例如存在 $i_0 \in I$ 使 $X_{i_0} = \varnothing$ 或 $R_\infty(X_{i_0})^G = \varnothing$），则其原像必为空（因良定义），空映射 $\varnothing \to \varnothing$ 恒为满射。
- 现设 $I \neq \varnothing$ 且陪域非空，任取一族元素 $(r^{(i)})_{i \in I} \in \prod_{i \in I} R_\infty(X_i)^G$。对每个 $i \in I$，因 $R_\infty(X_i)^G \neq \varnothing$，必有 $X_i \neq \varnothing$；由定理 2.2 令 $\mathcal{U}_i := \Phi_{\infty,X_i}^{-1}(r^{(i)}) \in \operatorname{Ult}_G(X_i)$，故对每个 $i \in I$ 与 $g \in G$ 均有 $X_i^g \in \mathcal{U}_i$。
  在对角作用下，对每个 $g \in G$ 有 $X^g = \prod_{i \in I} X_i^g$。考察 $\mathcal{P}(X)$ 的非空子集族（至少含 $X^e = X$）：
  $$\mathcal{F}_0 := \bigl\{p_i^{-1}(A) : i \in I,\ A \in \mathcal{U}_i\bigr\} \cup \bigl\{X^g : g \in G\bigr\}.$$
  验证 $\mathcal{F}_0$ 的有限交性质：任取其中有限个元素 $p_{i_1}^{-1}(A_1), \ldots, p_{i_m}^{-1}(A_m)$（$m \ge 0,\ i_s \in I,\ A_s \in \mathcal{U}_{i_s}$）与 $X^{g_1}, \ldots, X^{g_k}$（$k \ge 0,\ g_t \in G$，$m+k \ge 1$），设其交集为 $M \subseteq X$。令有限指标子集 $J := \{i_1, \ldots, i_m\} \subseteq I$。
  - 对每个 $j \in J$，令 $B_j := \bigcap_{1 \le s \le m,\, i_s = j} A_s \in \mathcal{U}_j$；
  - 对每个 $i \in I$（无论 $i \in J$ 还是 $i \in I \setminus J$），由 $X_i \in \mathcal{U}_i$ 及 $X_i^{g_t} \in \mathcal{U}_i$（$1 \le t \le k$）得 $F_i := X_i \cap \bigcap_{t=1}^k X_i^{g_t} \in \mathcal{U}_i$。
  按坐标展开得
  $$M = \Bigl\{(x_i)_{i \in I} \in \prod_{i \in I} X_i \;\Big|\; \forall j \in J,\ x_j \in B_j \cap F_j,\ \text{且}\ \forall i \in I \setminus J,\ x_i \in F_i\Bigr\}.$$
  对每个 $j \in J$，因 $B_j, F_j \in \mathcal{U}_j$，有 $B_j \cap F_j \in \mathcal{U}_j$，从而 $B_j \cap F_j \neq \varnothing$；对每个 $i \in I \setminus J$，因 $F_i \in \mathcal{U}_i$，有 $F_i \neq \varnothing$。由**选择公理**（指标集 $I$ 为集合，每个因子皆非空），乘积集 $M \neq \varnothing$！
  于是 $\mathcal{F}_0$ 满足有限交性质。由引理 0.2，存在 $\mathcal{W} \in \operatorname{Ult}(X)$ 使 $\mathcal{F}_0 \subseteq \mathcal{W}$。
  1. 对每个 $g \in G$，$X^g \in \mathcal{F}_0 \subseteq \mathcal{W}$，故 $\mathcal{W} \in \operatorname{Ult}_G(X)$，令 $r := \Phi_{\infty,X}(\mathcal{W}) \in R_\infty(X)^G$；
  2. 对每个 $i \in I$，若 $A \in \mathcal{U}_i$，则 $p_i^{-1}(A) \in \mathcal{F}_0 \subseteq \mathcal{W}$，即 $A \in (p_i)_*(\mathcal{W})$；若 $A \notin \mathcal{U}_i$，则 $X_i \setminus A \in \mathcal{U}_i \subseteq (p_i)_*(\mathcal{W})$，故 $A \notin (p_i)_*(\mathcal{W})$。因此 $(p_i)_*(\mathcal{W}) = \mathcal{U}_i$。
  由 1.3 的自然性，$R_\infty(p_i)r = \Phi_{\infty,X_i}((p_i)_*(\mathcal{W})) = \Phi_{\infty,X_i}(\mathcal{U}_i) = r^{(i)}$（$\forall i \in I$），即 $\Pi_{(X_i)}(r) = (r^{(i)})_{i \in I}$。$\square$

---

### 3.3 平凡群下两因子比较映射为单射的充要条件

先引入超滤子的两种 Fubini 张量乘积并验证其基本性质（该构造在 3.5 中亦将用到）：

**引理 3.1（超滤子的左、右张量积）** 设 $X, Y$ 为非空集合，$\mathcal{U} \in \operatorname{Ult}(X),\ \mathcal{V} \in \operatorname{Ult}(Y)$。对子集 $S \subseteq X \times Y$ 及 $x \in X,\ y \in Y$，记截面 $S_x := \{y' \in Y : (x, y') \in S\}$ 与 $S^y := \{x' \in X : (x', y) \in S\}$，定义
$$\mathcal{U} \otimes \mathcal{V} := \bigl\{S \subseteq X \times Y : \{x \in X : S_x \in \mathcal{V}\} \in \mathcal{U}\bigr\},\qquad \mathcal{U} \tilde{\otimes} \mathcal{V} := \bigl\{S \subseteq X \times Y : \{y \in Y : S^y \in \mathcal{U}\} \in \mathcal{V}\bigr\}.$$
则：
1. $\mathcal{U} \otimes \mathcal{V}$ 与 $\mathcal{U} \tilde{\otimes} \mathcal{V}$ 均属于 $\operatorname{Ult}(X \times Y)$；
2. 二者在两坐标投射 $p_1 : X \times Y \to X,\ p_2 : X \times Y \to Y$ 下的推前皆为 $(\mathcal{U}, \mathcal{V})$；
3. 若群 $G$ 作用于 $X, Y$ 且 $\mathcal{U} \in \operatorname{Ult}_G(X),\ \mathcal{V} \in \operatorname{Ult}_G(Y)$，则 $\mathcal{U} \otimes \mathcal{V}$ 与 $\mathcal{U} \tilde{\otimes} \mathcal{V}$ 均属于 $\operatorname{Ult}_G(X \times Y)$。

*证明*：
(1) 对 $\mathcal{U} \otimes \mathcal{V}$：显然 $\varnothing \notin \mathcal{U} \otimes \mathcal{V}$ 且 $X \times Y \in \mathcal{U} \otimes \mathcal{V}$；由 $S \subseteq T \implies S_x \subseteq T_x$ 得向上封闭性；由 $(S \cap T)_x = S_x \cap T_x$ 及 $\mathcal{V}, \mathcal{U}$ 对有限交封闭得 $\{x : (S \cap T)_x \in \mathcal{V}\} = \{x : S_x \in \mathcal{V}\} \cap \{x : T_x \in \mathcal{V}\}$ 在 $S, T \in \mathcal{U} \otimes \mathcal{V}$ 时属于 $\mathcal{U}$；由 $((X \times Y) \setminus S)_x = Y \setminus S_x$ 及 $\mathcal{V}, \mathcal{U}$ 的二分性得 $\{x : ((X \times Y) \setminus S)_x \in \mathcal{V}\} = X \setminus \{x : S_x \in \mathcal{V}\}$，故完备二分性成立。由对称性 $\mathcal{U} \tilde{\otimes} \mathcal{V} \in \operatorname{Ult}(X \times Y)$。
(2) 对 $A \subseteq X$，$(p_1^{-1}(A))_x = (A \times Y)_x$ 在 $x \in A$ 时为 $Y \in \mathcal{V}$、在 $x \notin A$ 时为 $\varnothing \notin \mathcal{V}$，故 $\{x : (A \times Y)_x \in \mathcal{V}\} = A$，从而 $(p_1)_*(\mathcal{U} \otimes \mathcal{V}) = \mathcal{U}$；又 $(A \times Y)^y = A$（$\forall y \in Y$），故 $\{y \in Y : A \in \mathcal{U}\}$ 在 $A \in \mathcal{U}$ 时为 $Y \in \mathcal{V}$、在 $A \notin \mathcal{U}$ 时为 $\varnothing \notin \mathcal{V}$，从而 $(p_1)_*(\mathcal{U} \tilde{\otimes} \mathcal{V}) = \mathcal{U}$。由对称性，二者在 $(p_2)_*$ 下皆等于 $\mathcal{V}$。
(3) 若 $\mathcal{W} \in \{\mathcal{U} \otimes \mathcal{V},\ \mathcal{U} \tilde{\otimes} \mathcal{V}\}$ 且 $\mathcal{U} \in \operatorname{Ult}_G(X),\ \mathcal{V} \in \operatorname{Ult}_G(Y)$，则对每个 $g \in G$ 有 $X^g \in \mathcal{U} = (p_1)_*(\mathcal{W})$ 且 $Y^g \in \mathcal{V} = (p_2)_*(\mathcal{W})$，即 $p_1^{-1}(X^g), p_2^{-1}(Y^g) \in \mathcal{W}$，从而 $(X \times Y)^g = X^g \times Y^g = p_1^{-1}(X^g) \cap p_2^{-1}(Y^g) \in \mathcal{W}$，故 $\mathcal{W} \in \operatorname{Ult}_G(X \times Y)$。$\square$

**定理 3.2（平凡群单射判准）** 对于平凡群 $G = \{e\}$，比较映射 $\Pi_{(X,Y)} : R_\infty(X \times Y) \to R_\infty(X) \times R_\infty(Y)$ 为单射，**当且仅当 $X$ 与 $Y$ 至少一个为有限集**（其中空集 $\varnothing$ 为有限集；等价地说，$X$ 与 $Y$ 不同时为无限集）。

*证明*：
- **充分性（$X, Y$ 至少一个有限 $\implies$ 单射）**：
  - 若 $X = \varnothing$ 或 $Y = \varnothing$，则 $X \times Y = \varnothing$，$R_\infty(X \times Y) = \varnothing$，空映射 $\varnothing \to \varnothing$ 为单射。
  - 不妨设 $X$ 有限非空（$Y$ 有限非空的情形完全对称），且 $Y \neq \varnothing$。在分类双射 $\Phi_\infty$ 下只需证 $((p_1)_*, (p_2)_*) : \operatorname{Ult}(X \times Y) \to \operatorname{Ult}(X) \times \operatorname{Ult}(Y)$ 为单射。设 $\mathcal{W}_1, \mathcal{W}_2 \in \operatorname{Ult}(X \times Y)$ 满足 $(p_1)_*(\mathcal{W}_k) = \mathcal{U}$ 且 $(p_2)_*(\mathcal{W}_k) = \mathcal{V}$（$k=1,2$）。因 $X$ 有限非空，由 1.4 的引理知存在唯一 $x_0 \in X$ 使 $\mathcal{U} = \mathcal{U}_{x_0}$，故 $\{x_0\} \in (p_1)_*(\mathcal{W}_k)$，即 $\{x_0\} \times Y = p_1^{-1}(\{x_0\}) \in \mathcal{W}_k$（$k=1,2$）。对任意子集 $S \subseteq X \times Y$，令 $B := \{y \in Y : (x_0, y) \in S\} \subseteq Y$，则
    $$S \cap (\{x_0\} \times Y) = \{x_0\} \times B = p_2^{-1}(B) \cap (\{x_0\} \times Y).$$
    由 $\{x_0\} \times Y \in \mathcal{W}_k$ 得
    $$S \in \mathcal{W}_k \iff S \cap (\{x_0\} \times Y) \in \mathcal{W}_k \iff p_2^{-1}(B) \cap (\{x_0\} \times Y) \in \mathcal{W}_k \iff p_2^{-1}(B) \in \mathcal{W}_k \iff B \in \mathcal{V}.$$
    右端与 $k \in \{1,2\}$ 无关，故 $\mathcal{W}_1 = \mathcal{W}_2$。

- **必要性（$X, Y$ 均无限 $\implies$ 非单射）**：
  设 $X, Y$ 均为无限集。由选择公理，固定选择函数 $c_X : \mathcal{P}(X) \setminus \{\varnothing\} \to X$ 并递归定义 $x_n := c_X(X \setminus \{x_0, \ldots, x_{n-1}\})$（因 $X$ 无限，$X \setminus \{x_0, \ldots, x_{n-1}\} \neq \varnothing$ 对所有 $n \in \mathbb{N}$ 成立），即得单射 $\iota_X : \mathbb{N} \hookrightarrow X,\ n \mapsto x_n$；同理得单射 $\iota_Y : \mathbb{N} \hookrightarrow Y,\ n \mapsto y_n$。
  由 2.5 知存在非主超滤子 $\mathcal{F} \in \operatorname{Ult}_{\mathrm{free}}(\mathbb{N})$，令 $\mathcal{U} := (\iota_X)_*(\mathcal{F}) \in \operatorname{Ult}(X)$ 与 $\mathcal{V} := (\iota_Y)_*(\mathcal{F}) \in \operatorname{Ult}(Y)$。由引理 3.1，取 $\mathcal{W}_1 := \mathcal{U} \otimes \mathcal{V}$ 与 $\mathcal{W}_2 := \mathcal{U} \tilde{\otimes} \mathcal{V}$，二者在 $((p_1)_*, (p_2)_*)$ 下同映为 $(\mathcal{U}, \mathcal{V})$。考察“上三角”子集
  $$T := \bigl\{(x_m, y_n) : m, n \in \mathbb{N},\ m < n\bigr\} \subseteq X \times Y.$$
  1. 对每个 $m \in \mathbb{N}$，由 $\iota_X, \iota_Y$ 单射知 $T_{x_m} = \{y_n : n > m\}$，故 $\iota_Y^{-1}(T_{x_m}) = \{n \in \mathbb{N} : n > m\}$ 在 $\mathbb{N}$ 中余有限，属于 $\mathcal{F}$，即 $T_{x_m} \in \mathcal{V}$。因此 $\{x \in X : T_x \in \mathcal{V}\} \supseteq \iota_X(\mathbb{N}) \in \mathcal{U}$，故 $T \in \mathcal{W}_1$。
  2. 对每个 $y \in Y$：若 $y \notin \iota_Y(\mathbb{N})$，则 $T^y = \varnothing \implies \iota_X^{-1}(T^y) = \varnothing \notin \mathcal{F}$；若 $y = y_n$（$n \in \mathbb{N}$），则 $T^{y_n} = \{x_m : 0 \le m < n\}$，故 $\iota_X^{-1}(T^{y_n}) = [n]$ 为有限集，因 $\mathcal{F}$ 非主亦有 $[n] \notin \mathcal{F}$。故对一切 $y \in Y$ 均有 $T^y \notin \mathcal{U}$，即 $\{y \in Y : T^y \in \mathcal{U}\} = \varnothing \notin \mathcal{V}$，从而 $T \notin \mathcal{W}_2$。
  于是 $\mathcal{W}_1 \neq \mathcal{W}_2$，经 $\Phi_{\infty, X \times Y}$ 即知 $\Pi_{(X,Y)}$ 不是单射。$\square$

---

### 3.4 命题一的判定与证明

> **命题一**：对任意群作用，若 $X, Y$ 至少一个有限，则两因子的比较映射 $\Pi_{(X,Y)} : R_\infty(X \times Y)^G \to R_\infty(X)^G \times R_\infty(Y)^G$ 为双射。

**结论**：该全称命题**成立（真命题）**。

*证明*：
- **满射性**：已由 3.2 的一般定理对任意群 $G$ 与任意两因子（无需有限性）直接给出。
- **单射性**：比较映射 $\Pi_{(X,Y)}^G : R_\infty(X \times Y)^G \to R_\infty(X)^G \times R_\infty(Y)^G$ 按定义正是平凡群比较映射 $\Pi_{(X,Y)}^{\{e\}} : R_\infty(X \times Y) \to R_\infty(X) \times R_\infty(Y)$ 在子集 $R_\infty(X \times Y)^G \subseteq R_\infty(X \times Y)$ 上的限制。因 $X, Y$ 至少一个有限，由定理 3.2 知环境映射 $\Pi_{(X,Y)}^{\{e\}}$ 在整个 $R_\infty(X \times Y)$ 上为单射，故其限制 $\Pi_{(X,Y)}^G$ 亦必为单射。

（注：亦可不用选择公理直接构造显式逆映射：若 $X, Y$ 有一为空或有限因子无 $G$-不动点，则定义域与陪域皆为空；若例如 $X$ 有限非空且 $X^G \neq \varnothing$，由 1.4 知 $R_\infty(X)^G = \eta_{\infty,X}(X^G)$，对每个 $x_0 \in X^G$ 嵌入 $j_{x_0} : Y \to X \times Y,\ y \mapsto (x_0, y)$ 是 $G$-等变的，映射 $(\eta_{\infty,X}(x_0), r_2) \mapsto R_\infty(j_{x_0})(r_2)$ 即给出 $\Pi_{(X,Y)}^G$ 的显式逆映射。）
综上，$\Pi_{(X,Y)}$ 既是单射又是满射，故恒为双射。$\square$

---

### 3.5 命题二的判定与证明

> **命题二**：对任意群作用，若 $X^G = Y^G = \varnothing$，则两因子的比较映射 $\Pi_{(X,Y)} : R_\infty(X \times Y)^G \to R_\infty(X)^G \times R_\infty(Y)^G$ 为单射。

**结论**：该全称命题**不成立（假命题）**。

*反例与证明*：
取目标 2.5 所构造的可数群 $G = \bigoplus_{k=0}^\infty (\mathbb{Z}/2\mathbb{Z})$ 及其在 $X = \mathbb{N}$ 上的作用 $g \cdot (2k + \varepsilon) = 2k + (\varepsilon \oplus g_k)$，并令 $Y := \mathbb{N}$ 赋予完全相同的 $G$-作用。
1. 由 2.5 已证，$X^G = Y^G = \varnothing$，满足命题前提。
2. 同样由 2.5，$\operatorname{Ult}_G(\mathbb{N}) = \operatorname{Ult}_{\mathrm{free}}(\mathbb{N}) \neq \varnothing$。任取一个自由超滤子 $\mathcal{U} \in \operatorname{Ult}_{\mathrm{free}}(\mathbb{N})$，令 $r_0 := \Phi_{\infty,\mathbb{N}}(\mathcal{U}) \in R_\infty(\mathbb{N})^G$。
3. 在对角作用的乘积 $G$ 集合 $\mathbb{N} \times \mathbb{N}$ 上，由引理 3.1 构造两个张量积超滤子：
   $$\mathcal{W}_1 := \mathcal{U} \otimes \mathcal{U},\qquad \mathcal{W}_2 := \mathcal{U} \tilde{\otimes} \mathcal{U}.$$
   - 由引理 3.1(3)，因 $\mathcal{U} \in \operatorname{Ult}_G(\mathbb{N})$，有 $\mathcal{W}_1, \mathcal{W}_2 \in \operatorname{Ult}_G(\mathbb{N} \times \mathbb{N})$，故 $w_1 := \Phi_{\infty,\mathbb{N}\times\mathbb{N}}(\mathcal{W}_1)$ 与 $w_2 := \Phi_{\infty,\mathbb{N}\times\mathbb{N}}(\mathcal{W}_2)$ 均属于 $R_\infty(\mathbb{N} \times \mathbb{N})^G$；
   - 由引理 3.1(2) 及 $\Phi_\infty$ 的自然性，$\Pi_{(\mathbb{N},\mathbb{N})}(w_1) = (r_0, r_0) = \Pi_{(\mathbb{N},\mathbb{N})}(w_2)$；
   - 取上三角集 $T := \{(m, n) \in \mathbb{N} \times \mathbb{N} : m < n\}$：对每个 $m \in \mathbb{N}$，截面 $T_m = \{n \in \mathbb{N} : n > m\}$ 在 $\mathbb{N}$ 中余有限，故 $T_m \in \mathcal{U}$，从而 $\{m \in \mathbb{N} : T_m \in \mathcal{U}\} = \mathbb{N} \in \mathcal{U}$，即 $T \in \mathcal{W}_1$（故 $(w_1)_2(\mathbf{1}_T) = 1$）；而对每个 $n \in \mathbb{N}$，截面 $T^n = [n]$ 有限，因 $\mathcal{U}$ 非主有 $T^n \notin \mathcal{U}$，从而 $\{n \in \mathbb{N} : T^n \in \mathcal{U}\} = \varnothing \notin \mathcal{U}$，即 $T \notin \mathcal{W}_2$（故 $(w_2)_2(\mathbf{1}_T) = 0$）。

因此 $w_1 \neq w_2$ 而 $\Pi_{(\mathbb{N},\mathbb{N})}(w_1) = \Pi_{(\mathbb{N},\mathbb{N})}(w_2)$，$\Pi_{(\mathbb{N},\mathbb{N})}$ 不是单射，原全称命题不成立。$\square$
