下面在 ZFC 下对三个目标给出完整分类、构造与证明。约定 $m\in\mathbb{Z}_{\ge1}\cup\{\infty\}$；当 $m=\infty$ 时，$0\le n\le\infty$ 指 $n$ 遍取全体非负整数 $\mathbb{N}=\{0,1,2,\ldots\}$。

---

## 目标一：截断及其相容关系

### 1.1 $R_m(X)$ 的完全分类

对于集合 $X$，考虑 $X=\varnothing$ 与 $X\ne\varnothing$ 两种情形。

1. **空底集 $X=\varnothing$：** 对任意 $m\ge1$（含 $m=\infty$），有 $R_m(\varnothing)=\varnothing$。
   **证明：** 由 $m\ge1$ 知 $n=0$ 为允许指标。因为 $[0]=\varnothing$，映射集合 $\operatorname{Map}(\varnothing,[0])=\{\varnothing\}$ 为单点集，故不存在任何映射 $r_0:\operatorname{Map}(\varnothing,[0])\to[0]$。从而 $R_m(\varnothing)=\varnothing$。

2. **非空底集 $X\ne\varnothing$：** 注意到此时 $\operatorname{Map}(X,[0])=\varnothing$，故 $r_0:\varnothing\to\varnothing$ 唯一存在（即空映射）；对允许的 $n,k$，当 $n=0$ 时 $\operatorname{Map}(X,[0])=\varnothing$，当 $k=0$ 且 $n\ge1$ 时 $\operatorname{Map}([n],[0])=\varnothing$，故所有涉及 $0$ 的相容条件 $a(r_n(f))=r_k(a\circ f)$ 皆空真成立。以下对 $A\subseteq X$，记其示性函数 $\mathbf{1}_A:X\to[2]$ 为 $\mathbf{1}_A(x)=1$（若 $x\in A$）及 $\mathbf{1}_A(x)=0$（若 $x\notin A$）；显然 $\operatorname{Map}(X,[2])=\{\mathbf{1}_A : A\subseteq X\}$。

   - **情形 $m=1$：** $R_1(X)=\{r^{(1)}\}$ 为单点集，其中 $r^{(1)}_0=\varnothing$，而 $r^{(1)}_1:\operatorname{Map}(X,[1])\to[1]$ 将唯一的常值映射 $X\to\{0\}$ 映到 $0$。
     **核验：** $n=k=1$ 时唯一映射 $a=\mathrm{id}_{[1]}$ 显然满足相容性；其余涉及 $0$ 的情形空真。

   - **情形 $m=2$：** 令
     $$\mathcal{C}(X)=\bigl\{\mathcal{F}\subseteq\mathcal{P}(X) : X\in\mathcal{F},\ \forall A\subseteq X,\ (A\in\mathcal{F}\iff X\setminus A\notin\mathcal{F})\bigr\}$$
     （等价地，$\mathcal{F}$ 在每对互补子集 $\{A,X\setminus A\}$ 中恰选取一个，且从 $\{\varnothing,X\}$ 中选取 $X$）。则映射
     $$\Phi_2:R_2(X)\longrightarrow\mathcal{C}(X),\qquad r\longmapsto \mathcal{F}_r:=\{A\subseteq X : r_2(\mathbf{1}_A)=1\}$$
     为双射，其逆映射将 $\mathcal{F}\in\mathcal{C}(X)$ 映到 $r^{(2,\mathcal{F})}=(r_0,r_1,r_2)$，其中 $r_0,r_1$ 为上述唯一映射，$r_2(\mathbf{1}_A)=1$ 当且仅当 $A\in\mathcal{F}$。
     **证明：**
     - *良定义性：* 设 $r\in R_2(X)$。取 $f_0:X\to[1]$ 为常值 $0$，并取 $c_0,c_1:[1]\to[2]$ 为 $c_0(0)=0, c_1(0)=1$。则 $\mathbf{1}_\varnothing=c_0\circ f_0,\ \mathbf{1}_X=c_1\circ f_0$，由相容性得 $r_2(\mathbf{1}_\varnothing)=c_0(r_1(f_0))=0$ 且 $r_2(\mathbf{1}_X)=c_1(r_1(f_0))=1$，故 $\varnothing\notin\mathcal{F}_r$ 且 $X\in\mathcal{F}_r$。再取对换 $\sigma:[2]\to[2],\ t\mapsto 1-t$，有 $\sigma\circ\mathbf{1}_A=\mathbf{1}_{X\setminus A}$，于是 $r_2(\mathbf{1}_{X\setminus A})=\sigma(r_2(\mathbf{1}_A))=1-r_2(\mathbf{1}_A)$，故 $X\setminus A\in\mathcal{F}_r\iff A\notin\mathcal{F}_r$。因此 $\mathcal{F}_r\in\mathcal{C}(X)$。
     - *逆映射良定义且互逆：* 对 $\mathcal{F}\in\mathcal{C}(X)$，逐一核验 $n,k\in\{1,2\}$ 的 $a:[n]\to[k]$ 与 $f:X\to[n]$：
       - $(n,k)=(1,1)$ 与 $(2,1)$：由 $[1]=\{0\}$ 自动成立。
       - $(n,k)=(1,2)$：$a$ 为 $c_0$ 或 $c_1$，分别对应 $\mathbf{1}_\varnothing\notin\mathcal{F}$ 与 $\mathbf{1}_X\in\mathcal{F}$，由 $X\in\mathcal{F}$ 及补集条件（推出 $\varnothing\notin\mathcal{F}$）成立。
       - $(n,k)=(2,2)$：$a:[2]\to[2]$ 仅有四个映射：常值 $0$、常值 $1$、$\mathrm{id}_{[2]}$、对换 $\sigma$。前两者由 $r_2(\mathbf{1}_\varnothing)=0, r_2(\mathbf{1}_X)=1$ 成立；$\mathrm{id}_{[2]}$ 平凡成立；$\sigma$ 由 $A\in\mathcal{F}\iff X\setminus A\notin\mathcal{F}$ 成立。
       互逆性直接由 $r_2$ 的定义及 $r_0,r_1$ 的唯一性得出。

   - **情形 $m\ge3$（含 $m=\infty$）：** 记 $\beta X$ 为 $X$ 上全体超滤子（ultrafilter）构成的集合。则映射
     $$\Phi_m:R_m(X)\longrightarrow\beta X,\qquad r\longmapsto \mathcal{U}_r:=\{A\subseteq X : r_2(\mathbf{1}_A)=1\}$$
     为双射，其逆映射 $\Psi_m$ 将 $\mathcal{U}\in\beta X$ 映到 $r^{(m,\mathcal{U})}=(r_n)_{0\le n\le m}$，其中 $r_0=\varnothing$，且对 $1\le n\le m$ 与 $f:X\to[n]$，$r_n(f)$ 是满足 $f^{-1}(\{i\})\in\mathcal{U}$ 的唯一 $i\in[n]$。
     **证明：**
     - *$\Phi_m(r)\in\beta X$：* 由 $m\ge3$ 知 $r_0,r_1,r_2,r_3$ 均存在。由 $m=2$ 情形已得 $\varnothing\notin\mathcal{U}_r,\ X\in\mathcal{U}_r$ 及对任意 $A\subseteq X$ 恰有 $A,X\setminus A$ 之一在 $\mathcal{U}_r$ 中。对任意 $3$-划分 $X=A_0\sqcup A_1\sqcup A_2$，定义 $f:X\to[3]$ 在 $A_i$ 上取值为 $i$，并定义 $\delta_i:[3]\to[2]$ 为 $\delta_i(i)=1$ 且 $\delta_i(j)=0\ (j\ne i)$。则 $\delta_i\circ f=\mathbf{1}_{A_i}$，故 $r_2(\mathbf{1}_{A_i})=\delta_i(r_3(f))$。由于 $r_3(f)\in[3]$ 取唯一值，故 $A_0,A_1,A_2$ 中**恰有一个**属于 $\mathcal{U}_r$。由此验证滤子公理：
       - *上闭性：* 若 $A\in\mathcal{U}_r$ 且 $A\subseteq B\subseteq X$，对划分 $X=A\sqcup(B\setminus A)\sqcup(X\setminus B)$，因 $A\in\mathcal{U}_r$ 故 $X\setminus B\notin\mathcal{U}_r$，由补集条件得 $B\in\mathcal{U}_r$。
       - *有限交封闭：* 若 $A,B\in\mathcal{U}_r$，对划分 $X=(A\cap B)\sqcup(A\setminus B)\sqcup(X\setminus A)$，因 $X\setminus A\notin\mathcal{U}_r$，故 $A\cap B$ 与 $A\setminus B$ 之一在 $\mathcal{U}_r$ 中；若 $A\setminus B\in\mathcal{U}_r$，则对划分 $X=(A\setminus B)\sqcup B\sqcup(X\setminus(A\cup B))$ 将有 $A\setminus B$ 与 $B$ 同在 $\mathcal{U}_r$ 中，矛盾。故 $A\cap B\in\mathcal{U}_r$。
       从而 $\mathcal{U}_r$ 是 $X$ 上的超滤子。
     - *$\Psi_m$ 的良定义与互逆性：* 对 $\mathcal{U}\in\beta X$ 及 $1\le n\le m$、$f:X\to[n]$，由有限划分 $X=\bigsqcup_{i\in[n]} f^{-1}(\{i\})$ 及 $\mathcal{U}$ 是超滤子，存在唯一 $i\in[n]$ 使 $f^{-1}(\{i\})\in\mathcal{U}$，记 $r_n(f)=i$。对任意 $1\le n,k\le m$ 与 $a:[n]\to[k]$，有 $f^{-1}(\{i\})\subseteq (a\circ f)^{-1}(\{a(i)\})$，由上闭性得 $(a\circ f)^{-1}(\{a(i)\})\in\mathcal{U}$，故 $r_k(a\circ f)=a(i)=a(r_n(f))$。于是 $\Psi_m(\mathcal{U})\in R_m(X)$。
       显然 $\Phi_m(\Psi_m(\mathcal{U}))=\mathcal{U}$。反之，若 $r\in R_m(X)$，$1\le n\le m$，$f:X\to[n]$，取 $\delta_i:[n]\to[2]$（$\delta_i(j)=1\iff j=i$），由 $2\le m$ 得 $r_2(\mathbf{1}_{f^{-1}(\{i\})})=r_2(\delta_i\circ f)=\delta_i(r_n(f))$，故 $r_n(f)=i\iff f^{-1}(\{i\})\in\mathcal{U}_r$，即 $\Psi_m(\Phi_m(r))=r$。

   *(注：在该分类下，对 $x\in X$，点值记录 $\eta_{m,X}(x)$ 在 $m=1$ 时为唯一记录 $r^{(1)}$，在 $m=2$ 时对应主族 $\mathcal{F}_x=\{A\subseteq X : x\in A\}\in\mathcal{C}(X)$，在 $m\ge3$ 时对应主超滤子 $\mathcal{U}_x=\{A\subseteq X : x\in A\}\in\beta X$。)*

---

### 1.2 截断映射 $q_{m,k}$ 的像与纤维

对 $m\ge k\ge1$，$q_{m,k}:R_m(X)\to R_k(X)$ 将 $(r_n)_{0\le n\le m}$ 截断为 $(r_n)_{0\le n\le k}$（显然满足 $0\le n,n'\le k$ 的相容性）。

- **若 $X=\varnothing$：** $R_m(\varnothing)=R_k(\varnothing)=\varnothing$，$q_{m,k}$ 为空映射 $\varnothing\to\varnothing$，像为 $\varnothing$，无纤维（全体纤维集为空族）。
- **若 $X\ne\varnothing$：**
  1. **$m\ge k\ge3$（含 $m=\infty$ 或 $k=\infty$）：** 因 $\Phi_k(q_{m,k}(r))=\{A\subseteq X : r_2(\mathbf{1}_A)=1\}=\Phi_m(r)$，在 $\Phi_m,\Phi_k$ 下 $q_{m,k}$ 对应 $\mathrm{id}_{\beta X}$。因此 $q_{m,k}$ 为**双射**：像为 $R_k(X)$ 全体；任意 $s\in R_k(X)$ 的纤维为单点集 $\{r^{(m,\mathcal{U}_s)}\}$。
  2. **$m\ge3$ 且 $k=2$：** 在 $\Phi_m$ 与 $\Phi_2$ 下，$q_{m,2}$ 对应自然包含 $\beta X\hookrightarrow\mathcal{C}(X)$，故 $q_{m,2}$ 为**单射**。
     - **像：** $\operatorname{im}(q_{m,2})=\{s\in R_2(X) : \mathcal{F}_s\in\beta X\}$。这等价于 $\mathcal{F}_s$ 对二元交封闭，即对所有 $A,B\subseteq X$ 有 $s_2(\mathbf{1}_{A\cap B})=s_2(\mathbf{1}_A)s_2(\mathbf{1}_B)$（若 $\mathcal{F}\in\mathcal{C}(X)$ 对二元交封闭，且 $A\in\mathcal{F},\ A\subseteq B$，若 $B\notin\mathcal{F}$ 则 $X\setminus B\in\mathcal{F}$，推出 $\varnothing=A\cap(X\setminus B)\in\mathcal{F}$，矛盾，故自动上闭从而为超滤子）。
     - **纤维：** 若 $s\in\operatorname{im}(q_{m,2})$，纤维 $q_{m,2}^{-1}(\{s\})$ 为单点集 $\{r^{(m,\mathcal{F}_s)}\}$；若 $s\notin\operatorname{im}(q_{m,2})$，纤维为空集 $\varnothing$。特别地，当 $|X|\in\{1,2\}$ 时，每个 $\mathcal{F}\in\mathcal{C}(X)$ 皆为主超滤子，故 $q_{m,2}$ 为双射；当 $|X|\ge3$ 时（将 $X$ 划为三个非空子集 $A_1\sqcup A_2\sqcup A_3$ 并取三者均在或均不在其中的 $\mathcal{F}\in\mathcal{C}(X)$），存在非超滤子元素，故 $q_{m,2}$ 非满射。
  3. **$m\ge2$ 且 $k=1$：** $R_1(X)=\{r^{(1)}\}$ 为单点集。对 $m=2$，总有 $\mathcal{F}_x\in\mathcal{C}(X)$（由 $X\ne\varnothing$ 取 $x\in X$）；对 $m\ge3$，$\mathcal{U}_x\in\beta X$，故 $R_m(X)\ne\varnothing$。因此 $q_{m,1}$ 为**满射**：像为 $R_1(X)$ 全体，唯一元素 $r^{(1)}$ 的纤维为 $R_m(X)$ 全体。
  4. **$m=k=1$ 或 $m=k=2$：** $q_{m,m}=\mathrm{id}_{R_m(X)}$，像为 $R_m(X)$，每个纤维为单点集 $\{s\}$。

---

### 1.3 与集合映射 $h:X\to Y$ 的相容性

设 $h:X\to Y$ 为任意映射，逐项核验如下：

1. **良定义性：** 对 $r\in R_m(X)$，对所有 $0\le n,k\le m$、$f:Y\to[n]$ 及 $a:[n]\to[k]$，有 $f\circ h:X\to[n]$ 及
   $$a\bigl((R_m(h)r)_n(f)\bigr)=a(r_n(f\circ h))=r_k(a\circ(f\circ h))=r_k((a\circ f)\circ h)=(R_m(h)r)_k(a\circ f),$$
   故 $R_m(h)r\in R_m(Y)$（若 $X=\varnothing$，则 $R_m(\varnothing)=\varnothing$，$R_m(h)$ 为空映射 $\varnothing\to R_m(Y)$）。
2. **函子性：** $(R_m(\mathrm{id}_X)r)_n(f)=r_n(f\circ\mathrm{id}_X)=r_n(f)$，即 $R_m(\mathrm{id}_X)=\mathrm{id}_{R_m(X)}$；对 $h:X\to Y,\ h':Y\to Z$，
   $$\bigl(R_m(h'\circ h)r\bigr)_n(f)=r_n(f\circ h'\circ h)=(R_m(h)r)_n(f\circ h')=\bigl(R_m(h')(R_m(h)r)\bigr)_n(f),$$
   即 $R_m(h'\circ h)=R_m(h')\circ R_m(h)$。
   由此立即得出 $g\cdot r:=R_m(g_X)r$ 确实构成左群作用：$e\cdot r=R_m(\mathrm{id}_X)r=r$，且 $g_1\cdot(g_2\cdot r)=R_m(g_{1,X}\circ g_{2,X})r=R_m((g_1 g_2)_X)r=(g_1 g_2)\cdot r$。
3. **与截断的自然性：** 对任意 $m\ge k\ge1$、$r\in R_m(X)$、$0\le n\le k$ 与 $f:Y\to[n]$，有
   $$\bigl(q_{m,k}^Y(R_m(h)r)\bigr)_n(f)=r_n(f\circ h)=\bigl(R_k(h)(q_{m,k}^X(r))\bigr)_n(f),$$
   即 $q_{m,k}^Y\circ R_m(h)=R_k(h)\circ q_{m,k}^X$。
4. **与点值嵌入的自然性：** 对 $x\in X$，显然 $a(\eta_{m,X}(x)_n(f))=a(f(x))=\eta_{m,X}(x)_k(a\circ f)$，故 $\eta_{m,X}(x)\in R_m(X)$。而且
   $$\bigl(R_m(h)(\eta_{m,X}(x))\bigr)_n(f)=f(h(x))=\eta_{m,Y}(h(x))_n(f),\qquad q_{m,k}^X(\eta_{m,X}(x))=\eta_{k,X}(x),$$
   即 $R_m(h)\circ\eta_{m,X}=\eta_{m,Y}\circ h$ 与 $q_{m,k}^X\circ\eta_{m,X}=\eta_{k,X}$。
5. **分类下的显式表示：** 当 $X\ne\varnothing$ 时（此时由 $h:X\to Y$ 知 $Y\ne\varnothing$）：
   - $m=1$ 时将唯一元映到唯一元；
   - $m=2$ 时，由 $\mathbf{1}_B\circ h=\mathbf{1}_{h^{-1}(B)}$ 得 $(R_2(h)r)_2(\mathbf{1}_B)=r_2(\mathbf{1}_{h^{-1}(B)})$，即 $\Phi_2(R_2(h)r)=h_*\mathcal{F}_r:=\{B\subseteq Y : h^{-1}(B)\in\mathcal{F}_r\}$；
   - $m\ge3$ 时，同理 $\Phi_m(R_m(h)r)=h_*\mathcal{U}_r:=\{B\subseteq Y : h^{-1}(B)\in\mathcal{U}_r\}$（前推超滤子）。

---

### 1.4 有限 $G$ 集合 $X$ 上的 $R_m(X)^G$、基数、限制映射与延拓范围

设 $X$ 为有限 $G$ 集合（群 $G$ 任意，可无限）。首先注意到若 $h:X\to Y$ 为 $G$ 等变映射（$h\circ g_X=g_Y\circ h$），则由自然性有 $R_m(h)(g\cdot r)=g\cdot R_m(h)(r)$。特别地，因为 $q_{m,k}^X\circ g\cdot(-)=q_{m,k}^X\circ R_m(g_X)=R_k(g_X)\circ q_{m,k}^X$ 且 $\eta_{m,X}(gx)=g\cdot\eta_{m,X}(x)$，截断 $q_{m,k}$ 和点值映射 $\eta_{m,X}$ 均 $G$ 等变。对 $X\ne\varnothing$，由 $g_X^{-1}(A)=g^{-1}A$，$G$ 在 $\mathcal{C}(X)$（及 $\beta X$）上的诱导作用为 $g\cdot\mathcal{F}=\{B\subseteq X : g^{-1}B\in\mathcal{F}\}=\{gA : A\in\mathcal{F}\}$。

1. **各 $R_m(X)^G$ 的存在判准与精确基数：**
   - **$m=1$：**
     - *存在判准：* $R_1(X)^G\ne\varnothing\iff X\ne\varnothing$。
     - *精确基数：* 若 $X=\varnothing$，$|R_1(\varnothing)^G|=0$；若 $X\ne\varnothing$，$|R_1(X)|=1$ 且 $G$ 平凡作用在单点集上，故 $|R_1(X)^G|=1$。
   - **$m=2$：**
     - *存在判准：* $R_2(X)^G\ne\varnothing$ 当且仅当**对每个 $g\in G$，置换 $g_X$ 在 $X$ 上至少有一个奇数长度的轮换（即存在 $x\in X$ 使其 $\langle g\rangle$-轨道基数为奇数）**（注意该条件对 $X=\varnothing$ 不成立，故自动蕴含 $X\ne\varnothing$）。等价地表述（当 $X\ne\varnothing$ 时）：不存在 $A\subseteq X$ 与 $g\in G$ 使得 $gA=X\setminus A$（即 $\mathcal{P}(X)$ 中不存在对补集运算 $A\mapsto X\setminus A$ 封闭的 $G$-轨道）。
       **证明：** 若 $X=\varnothing$，两边皆为假。下设 $X\ne\varnothing$。$\mathcal{F}\in\mathcal{C}(X)^G$ 当且仅当 $X\in\mathcal{F}$、每对互补子集 $\{A,X\setminus A\}$ 中恰选其一入 $\mathcal{F}$、且 $\forall g\in G, A\in\mathcal{F}\iff gA\in\mathcal{F}$。
       令 $\mathfrak{P}(X)=\bigl\{\{A,X\setminus A\} : A\subseteq X\bigr\}$（因为 $X\ne\varnothing$，$A\ne X\setminus A$，故每个元素均为二元集，$|\mathfrak{P}(X)|=2^{|X|-1}$）。$G$ 作用在 $\mathcal{P}(X)$ 上且与取补对合 $\tau(A)=X\setminus A$ 交换，从而诱导出 $G$ 在 $\mathfrak{P}(X)$ 上的作用 $g\cdot\{A,X\setminus A\}=\{gA,X\setminus gA\}$。
       若存在 $g\in G$ 与 $A\subseteq X$ 使 $gA=X\setminus A$，则由 $A\in\mathcal{F}\iff gA=X\setminus A\in\mathcal{F}\iff A\notin\mathcal{F}$ 得矛盾，故 $\mathcal{C}(X)^G=\varnothing$。反之，若不存在这样的 $(g,A)$，则对 $\mathfrak{P}(X)$ 中每个 $G$-轨道 $\Omega=G\cdot\{A_0,X\setminus A_0\}$，其在 $\mathcal{P}(X)$ 中的原像分裂为两个互不相交的 $G$-轨道 $G\cdot A_0$ 与 $G\cdot(X\setminus A_0)$（若相交，则 $g_1A_0=X\setminus g_2A_0$，即 $(g_2^{-1}g_1)A_0=X\setminus A_0$，矛盾）。因此可在轨道 $\{\{\varnothing,X\}\}$ 中选 $\{X\}$，并在其余每个轨道 $\Omega\in(\mathfrak{P}(X)/G)\setminus\{\{\{\varnothing,X\}\}\}$ 中任选 $G\cdot A_0$ 或 $G\cdot(X\setminus A_0)$ 并入 $\mathcal{F}$，即得 $\mathcal{C}(X)^G$ 的全部元素。
       再证“$\exists g\in G,\ \exists A\subseteq X,\ gA=X\setminus A$”等价于“$\exists g\in G$ 使得 $g_X$ 的所有轮换长度皆为偶数”：
       - 若 $gA=X\setminus A$，因 $g_X$ 为双射，取补得 $g(X\setminus A)=A$，故对所有 $x\in X$ 有 $gx\in A\iff x\notin A$。沿 $g_X$ 的任一长度为 $L\ge1$ 的轮换 $(x_0,x_1,\dots,x_{L-1})$，成员关系 $g^k x_0\in A$ 随 $k$ 交替变化，由 $g^L x_0=x_0$ 必有 $L$ 为偶数。
       - 反之，若 $g_X$ 的所有轮换长度均为偶数，则在每个轮换 $(x_0,\dots,x_{2s-1})$ 上取偶数步点 $\{x_0,x_2,\dots,x_{2s-2}\}$ 并集为 $A$，即有 $gA=X\setminus A$。
     - *精确基数：* 若判准不成立，$|R_2(X)^G|=0$；若判准成立，则每个 $\Omega\ne\{\{\varnothing,X\}\}$ 有 $2$ 种独立选择，故
       $$|R_2(X)^G| = 2^{|\mathfrak{P}(X)/G|-1} = 2^{\frac{1}{2}|\mathcal{P}(X)/G|-1}.$$
       记 $\overline{G}=\operatorname{im}(G\to\operatorname{Sym}(X))$（有限群），$c(\bar g)$ 为置换 $\bar g$ 在 $X$ 上的轮换个数。因无任何 $\bar g\in\overline{G}$ 满足 $\bar gA=X\setminus A$，对每个 $\bar g\in\overline{G}$ 有 $|\mathfrak{P}(X)^{\bar g}|=\frac{1}{2}|\mathcal{P}(X)^{\bar g}|=2^{c(\bar g)-1}$，对有限群 $\overline{G}$ 作用在有限集 $\mathfrak{P}(X)$ 上应用 Burnside 引理，亦可表为
       $$|R_2(X)^G| = 2^{\left(\frac{1}{|\overline{G}|}\sum_{\bar g\in\overline{G}} 2^{c(\bar g)-1}\right)-1}.$$
       （当 $G$ 本身有限时，$\overline{G}$ 与 $c(\bar g)$ 也可直接换为 $G$ 与 $c(g_X)$。）
   - **$m\ge3$（含 $m=\infty$）：** 因有限集合 $X$ 上的超滤子必为主超滤子（若非主超滤子则包含所有余有限子集，从而包含 $\varnothing$，矛盾；且 $X=\varnothing$ 时 $\beta\varnothing=\varnothing$），故 $\eta_{m,X}:X\to R_m(X)$ 是 $G$ 等变双射。由此 $R_m(X)^G=\eta_{m,X}(X^G)$。
     - *存在判准：* $R_m(X)^G\ne\varnothing\iff X^G\ne\varnothing$。
     - *精确基数：* $|R_m(X)^G|=|X^G|$。

2. **不动集合之间的限制映射 $q_{m,k}^G:R_m(X)^G\to R_k(X)^G$（$m\ge k\ge1$）：**
   - 若 $X=\varnothing$：均为 $\varnothing\to\varnothing$。
   - 若 $X\ne\varnothing$：
     - $m\ge k\ge3$：将 $\eta_{m,X}(x)$ 映到 $\eta_{k,X}(x)\ (x\in X^G)$，为**双射**。
     - $m\ge3, k=2$：将 $\eta_{m,X}(x)$ 映到 $\eta_{2,X}(x)\ (x\in X^G)$（即主超滤子 $\mathcal{U}_x\in\mathcal{C}(X)^G$）。因为 $\eta_{2,X}$ 单射，故 $q_{m,2}^G$ 必为**单射**，像为 $\eta_{2,X}(X^G)=\{\mathcal{F}\in\mathcal{C}(X)^G : \mathcal{F}\text{ 为主超滤子}\}$。当 $|X|\le2$ 或 $R_2(X)^G=\varnothing$ 时它是双射；当 $|X|\ge3$ 且 $R_2(X)^G\ne\varnothing$ 时它**非满射**（事实上记 $f=|X^G|$：若 $f=0$ 则 $|R_2(X)^G|\ge1>0$；若 $f\ge1$，每个 $x\in X^G$ 给出非平凡轨道对 $\{\{x\},\{X\setminus\{x\}\}\}$，共有至少 $f$ 个此类轨道对，而 $f=1$ 且 $|X|\ge3$ 时对任取 $y\in X\setminus X^G$，由 $|X\setminus X^G|\ge2$ 知 $\{y\}\notin\{\varnothing,X,X^G,X\setminus X^G\}$ 又多出一个轨道对，故总有 $|R_2(X)^G|\ge 2^f>f$（$f=1$ 时 $\ge 2^2=4>1$））。
     - $m\ge2, k=1$：将 $R_m(X)^G$ 中所有元映到 $R_1(X)^G$ 的唯一元素 $r^{(1)}$。当且仅当 $R_m(X)^G\ne\varnothing$ 时为满射。
     - $m=k=1$ 或 $m=k=2$：恒等映射。

3. **有限层不动记录延拓为完整不动记录的准确范围：**
   设 $X$ 为有限 $G$ 集合，考虑第 $k$ 层（$k\ge1$ 有限）记录 $s\in R_k(X)^G$ 何时存在 $r\in R_\infty(X)^G$ 使 $q_{\infty,k}(r)=s$：
   - **$k\ge3$：** 全体 $R_k(X)^G$ 中的记录都可延拓为 $R_\infty(X)^G$ 中的不动记录，且延拓唯一（$s=\eta_{k,X}(x)$ 唯一延拓为 $\eta_{\infty,X}(x)$，$x\in X^G$）。
   - **$k=2$：** $s\in R_2(X)^G$ 可延拓为 $R_\infty(X)^G$ 中的记录（且若存在则唯一）当且仅当 $s\in\eta_{2,X}(X^G)$，即等价于 $\mathcal{F}_s$ 为主超滤子（等价地，$\mathcal{F}_s$ 对二元交封闭）。特别地，若 $|X|\le2$ 或 $R_2(X)^G=\varnothing$，范围为全部 $R_2(X)^G$；若 $|X|\ge3$ 且 $R_2(X)^G\ne\varnothing$，延拓范围为真子集 $\eta_{2,X}(X^G)\subsetneq R_2(X)^G$。
   - **$k=1$：** 若 $X=\varnothing$ 则 $R_1(\varnothing)^G=\varnothing$；若 $X\ne\varnothing$，则 $R_1(X)^G$ 的唯一元素 $r^{(1)}$ 可延拓到 $R_\infty(X)^G$ 当且仅当 $X^G\ne\varnothing$（其延拓恰好为 $\eta_{\infty,X}(X^G)$）。

   *(注：若不限制 $X$ 有限而考虑一般 $G$ 集合 $X$，由 $1.2$ 及 $q_{\infty,k}$ 的 $G$ 等变性立即知：$k\ge3$ 时全体 $R_k(X)^G$ 唯一延拓；$k=2$ 时恰为 $\mathcal{F}_s\in\beta X$ 者唯一延拓；$k=1$（$X\ne\varnothing$）时唯一元可延拓当且仅当 $R_\infty(X)^G\ne\varnothing$。)*

---

## 目标二：完整不动记录的空间

### 2.1 $R_\infty(X)$ 的拓扑与 $R_\infty(X)^G$ 的内在分类

当 $X=\varnothing$ 时，$R_\infty(\varnothing)=R_\infty(\varnothing)^G=\varnothing$，$\beta\varnothing=\varnothing$，拓扑为唯一空拓扑，以下所有结论在空集上均显然成立。设 $X\ne\varnothing$。

1. **$R_\infty(X)\cong\beta X$ 为紧致 Hausdorff 零维（Stone）空间：**
   在 $\beta X$ 上赋予由子集族 $\{\widehat{A} : A\subseteq X\}$（其中 $\widehat{A}:=\{\mathcal{U}\in\beta X : A\in\mathcal{U}\}$）生成的 Stone 拓扑。由 $\widehat{A}\cap\widehat{B}=\widehat{A\cap B}$ 与 $\widehat{X}=\beta X$ 知 $\{\widehat{A} : A\subseteq X\}$ 已构成开基，且 $\beta X\setminus\widehat{A}=\widehat{X\setminus A}$ 故每个 $\widehat{A}$ 既开又闭。若 $\mathcal{U}\ne\mathcal{V}\in\beta X$，取 $A\in\mathcal{U}\setminus\mathcal{V}$，则 $\widehat{A}$ 与 $\widehat{X\setminus A}$ 为不交开邻域，故 $\beta X$ 为 Hausdorff 空间。
   在 $R_\infty(X)$ 上，由定义拓扑由子基 $U_{n,f,i}:=\{r\in R_\infty(X) : r_n(f)=i\}\ (n\ge1,\ f:X\to[n],\ i\in[n])$ 生成（因 $X\ne\varnothing$，$\operatorname{Map}(X,[0])=\varnothing$）。在双射 $\Phi_\infty:R_\infty(X)\to\beta X$ 下，
   $$\Phi_\infty(U_{n,f,i})=\widehat{f^{-1}(\{i\})},\qquad \Phi_\infty^{-1}(\widehat{A})=U_{2,\mathbf{1}_A,1},$$
   故 $\Phi_\infty:R_\infty(X)\to\beta X$ 为**同胚**。另一方面，$R_\infty(X)$ 自然嵌入乘积空间 $\prod_{n\in\mathbb{N}}\prod_{f\in\operatorname{Map}(X,[n])}[n]$，而每条相容方程 $a(r_n(f))=r_k(a\circ f)$ 在离散 Hausdorff 空间 $[k]$ 中定义闭集，故 $R_\infty(X)$ 为紧致 Hausdorff 空间（ZFC 下 Tychonoff 定理，因每个 $[n]$ 有限离散从而紧致 Hausdorff）的闭子空间，进而 $R_\infty(X)\cong\beta X$ 紧致 Hausdorff。

2. **关键引理（$G$-不变超滤子的内在刻画）：**
   对任意 $\mathcal{U}\in\beta X$，以下三条等价：
   - (i) $\mathcal{U}\in(\beta X)^G$（即对所有 $g\in G$ 及 $A\subseteq X$，有 $A\in\mathcal{U}\iff gA\in\mathcal{U}$）；
   - (ii) 对所有 $g\in G$，不动点集 $X^g:=\{x\in X : gx=x\}\in\mathcal{U}$；
   - (iii) 对所有有限子集 $F\subseteq G$，公共不动点集 $X^F:=\bigcap_{g\in F} X^g\in\mathcal{U}$（约定 $X^\varnothing=X$）。

   **证明：**
   - (ii)$\iff$(iii) 显然（由滤子对有限交封闭及 $X\in\mathcal{U}$）。
   - (ii)$\implies$(i)：设 $g\in G$ 且 $A\in\mathcal{U}$。因 $X^g\in\mathcal{U}$，故 $A\cap X^g\in\mathcal{U}$。但 $g_X$ 恒等作用在 $X^g$ 上，故 $A\cap X^g=g(A\cap X^g)\subseteq gA$，由上闭性得 $gA\in\mathcal{U}$。将 $g$ 换为 $g^{-1}$ 得反向蕴含，故 $g\cdot\mathcal{U}=\mathcal{U}$。
   - (i)$\implies$(ii)：设 $\mathcal{U}\in(\beta X)^G$ 及 $g\in G$。令 $Y=X\setminus X^g$，则 $g_X$ 限制为 $Y\to Y$ 的无不动点双射 $g_Y$。将 $Y$ 划分为 $\langle g_Y\rangle$-轨道，在 ZFC 下用选择公理在每个轨道 $\mathcal{O}_\alpha$ 中选一代表元 $y_\alpha$，对 $Y$ 进行三染色划分 $Y=A_1\sqcup A_2\sqcup A_3$ 如下：
     - 若 $\mathcal{O}_\alpha=\{g^k y_\alpha : k\in\mathbb{Z}\}$ 无限，按 $k$ 的奇偶分别放入 $A_1,A_2$；
     - 若 $\mathcal{O}_\alpha$ 有限且基数 $L\ge2$ 为偶数，对 $0\le k<L$ 按 $k$ 的奇偶将 $g^k y_\alpha$ 放入 $A_1,A_2$；
     - 若 $\mathcal{O}_\alpha$ 有限且基数 $L\ge3$ 为奇数，将 $y_\alpha=g^0 y_\alpha$ 放入 $A_3$，对 $1\le k\le L-1$ 按 $k$ 的奇偶将 $g^k y_\alpha$ 分别放入 $A_1,A_2$。
     检验各轨道上均有 $g(A_i)\cap A_i=\varnothing\ (i=1,2,3)$（奇数情形：$g(A_3)\subseteq A_1,\ g(A_1)\subseteq A_2,\ g(A_2)\subseteq A_1\cup A_3$），故在全体 $Y$ 上 $g(A_i)\cap A_i=\varnothing$。于是 $X=X^g\sqcup A_1\sqcup A_2\sqcup A_3$ 为四划分。因为 $\mathcal{U}$ 为超滤子，四者之一必在 $\mathcal{U}$ 中。若某 $A_i\in\mathcal{U}$，由 $G$-不变性得 $g(A_i)\in\mathcal{U}$，从而 $\varnothing=A_i\cap g(A_i)\in\mathcal{U}$，矛盾。故必有 $X^g\in\mathcal{U}$。

3. **由 $X$ 及其作用直接构造的内在分类（与拓扑相容）：**
   令 $\mathcal{F}_G:=\{A\subseteq X : \exists\text{ 有限 } F\subseteq G,\ X^F\subseteq A\}$，对偶地令理想 $\mathcal{I}_G:=\{A\subseteq X : \exists\text{ 有限 } F\subseteq G,\ A\cap X^F=\varnothing\}$（因 $(A_1\cup A_2)\cap X^{F_1\cup F_2}\subseteq (A_1\cap X^{F_1})\cup(A_2\cap X^{F_2})$，$\mathcal{I}_G$ 确为布尔代数 $\mathcal{P}(X)$ 的理想）。
   由上述引理，同胚 $\Phi_\infty:R_\infty(X)\xrightarrow{\sim}\beta X$ 限制为 $R_\infty(X)^G$ 到下列空间的**同胚**（各自配备 Stone 拓扑 / 子空间拓扑）：
   $$R_\infty(X)^G \;\cong\; \beta_G(X) := \bigl\{\mathcal{U}\in\beta X : \mathcal{F}_G\subseteq\mathcal{U}\bigr\} = \bigcap_{g\in G}\widehat{X^g} = \bigcap_{\substack{F\subseteq G\\ F\text{ 有限}}}\widehat{X^F} \subseteq \beta X,$$
   其具有闭开基 $\{\widehat{A}\cap\beta_G(X) : A\subseteq X\}$，且为紧致 Hausdorff Stone 空间。
   等价地，直接由作用与布尔商代数构造：
   - 商布尔代数 $\mathcal{P}(X)/\mathcal{I}_G$ 的全体超滤子空间 $\operatorname{Ult}(\mathcal{P}(X)/\mathcal{I}_G)$：设 $q:\mathcal{P}(X)\to\mathcal{P}(X)/\mathcal{I}_G$ 为商同态，则 $\overline{\mathcal{U}}\mapsto q^{-1}(\overline{\mathcal{U}})$ 将 $\operatorname{Ult}(\mathcal{P}(X)/\mathcal{I}_G)$ 双射地映到 $\{\mathcal{U}\in\beta X : \mathcal{U}\cap\mathcal{I}_G=\varnothing\}=\beta_G(X)$，且将基本闭开集 $\widehat{q(A)}$ 映到 $\widehat{A}\cap\beta_G(X)$，故为同胚（若存在有限 $F$ 使 $X^F=\varnothing$，则 $\mathcal{I}_G=\mathcal{P}(X)$，商代数为平凡代数 $\{0=1\}$，其上无超滤子，与 $\beta_G(X)=\varnothing$ 一致）。
   - 或逆极限 $\varprojlim_{F\Subset G}\beta(X^F)$（沿包含 $X^{F'}\hookrightarrow X^F,\ F\subseteq F'$ 所诱导的闭嵌入 $\beta(X^{F'})\hookrightarrow\beta(X^F)$，该嵌入将 $\beta(X^{F'})$ 同胚地等同于 $\widehat{X^{F'}}\cap\beta(X^F)$，故逆极限同胚于 $\bigcap_{F\Subset G}\widehat{X^F}=\beta_G(X)$）。

---

### 2.2 $R_\infty(X)^G\ne\varnothing$ 的充要条件

**定理：** 对任意 $G$ 集合 $X$，
$$R_\infty(X)^G \ne \varnothing \iff \text{对任意有限子集 } F\subseteq G,\quad X^F \ne \varnothing.$$
（注：取 $F=\varnothing$ 给出 $X^\varnothing=X\ne\varnothing$，故本判准同时覆盖 $X=\varnothing$。）

**证明：**
- ($\Rightarrow$) 若存在 $r\in R_\infty(X)^G$，则 $X\ne\varnothing$ 且 $\mathcal{U}_r\in\beta_G(X)$。对任意有限 $F\subseteq G$，由引理有 $X^F\in\mathcal{U}_r$，因为 $\varnothing\notin\mathcal{U}_r$，故 $X^F\ne\varnothing$。
- ($\Leftarrow$) 若对一切有限 $F\subseteq G$ 均有 $X^F\ne\varnothing$，则族 $\mathcal{B}=\{X^F : F\subseteq G\text{ 有限}\}$ 非空（含 $X^\varnothing=X\ne\varnothing$）且对有限交封闭（$X^{F_1}\cap X^{F_2}=X^{F_1\cup F_2}\in\mathcal{B}$），从而具有有限交性质。在 ZFC 下由超滤子引理（Ultrafilter Lemma），$\mathcal{B}$ 可扩充为某个超滤子 $\mathcal{U}\in\beta X$。因 $\mathcal{B}\subseteq\mathcal{U}$，由引理得 $\mathcal{U}\in\beta_G(X)$，即 $\Psi_\infty(\mathcal{U})\in R_\infty(X)^G$。

---

### 2.3 $\eta_{\infty,X}(X^G)$ 的闭包、等于 $R_\infty(X)^G$ 的充要条件及群的分类

1. **闭包 $\overline{\eta_{\infty,X}(X^G)}$：**
   - 若 $X=\varnothing$，则 $X^G=\varnothing$，$\overline{\eta_{\infty,\varnothing}(\varnothing)}=\varnothing$。
   - 若 $X\ne\varnothing$，对任意子集 $S\subseteq X$，证明在 $\beta X$ 中 $\overline{\Phi_\infty(\eta_{\infty,X}(S))}=\widehat{S}=\{\mathcal{U}\in\beta X : S\in\mathcal{U}\}$：
     - 若 $S\in\mathcal{U}$，对 $\mathcal{U}$ 的任意基本开邻域 $\widehat{A}\ (A\in\mathcal{U})$，有 $A\cap S\in\mathcal{U}$，故 $A\cap S\ne\varnothing$；取 $x\in A\cap S$，则 $\mathcal{U}_x\in\widehat{A}\cap\Phi_\infty(\eta_{\infty,X}(S))$。于是 $\mathcal{U}\in\overline{\Phi_\infty(\eta_{\infty,X}(S))}$。
     - 若 $S\notin\mathcal{U}$，则 $X\setminus S\in\mathcal{U}$，于是 $\widehat{X\setminus S}$ 是 $\mathcal{U}$ 的开邻域且与 $\Phi_\infty(\eta_{\infty,X}(S))$ 不交，故 $\mathcal{U}\notin\overline{\Phi_\infty(\eta_{\infty,X}(S))}$。
   从而取 $S=X^G$ 得：在同胚 $\Phi_\infty$ 下，
   $$\overline{\eta_{\infty,X}(X^G)} \cong \widehat{X^G} = \{\mathcal{U}\in\beta X : X^G\in\mathcal{U}\} \cong \beta(X^G)$$
   （若在 $R_\infty(X)$ 中直接写，当 $X\ne\varnothing$ 时即 $\{r\in R_\infty(X) : r_2(\mathbf{1}_{X^G})=1\}$，注意 $X^G=\varnothing$ 时该集合为 $\varnothing$）。

2. **等式 $\overline{\eta_{\infty,X}(X^G)}=R_\infty(X)^G$ 成立的充要条件：**
   **定理：** 对任意 $G$ 集合 $X$，
   $$\overline{\eta_{\infty,X}(X^G)} = R_\infty(X)^G \iff \text{存在有限子集 } F\subseteq G \text{ 使得 } X^F = X^G.$$
   **证明：** 若 $X=\varnothing$，取 $F=\varnothing$ 即有 $X^\varnothing=\varnothing=X^G$，且两端皆为 $\varnothing$。下设 $X\ne\varnothing$。因 $X^G\subseteq X^g\ (\forall g\in G)$，总有 $\widehat{X^G}\subseteq\bigcap_{g\in G}\widehat{X^g}=\beta_G(X)$。
   - ($\Leftarrow$) 若存在有限 $F\subseteq G$ 使 $X^F=X^G$，则对任意 $\mathcal{U}\in\beta_G(X)$，由引理有 $X^G=X^F\in\mathcal{U}$，即 $\mathcal{U}\in\widehat{X^G}$。
   - ($\Rightarrow$) 反证，假设对任意有限 $F\subseteq G$ 均有 $X^F\ne X^G$。因 $X^G\subseteq X^F$，故族 $\mathcal{S}:=\{X^F\setminus X^G : F\subseteq G\text{ 有限}\}$ 中每个集合均非空；又因 $(X^{F_1}\setminus X^G)\cap(X^{F_2}\setminus X^G)=X^{F_1\cup F_2}\setminus X^G\in\mathcal{S}$，故 $\mathcal{S}$ 具有有限交性质。在 ZFC 下由超滤子引理，$\mathcal{S}$ 可扩充为超滤子 $\mathcal{U}\in\beta X$。由 $F=\{g\}$ 得 $X^g\setminus X^G\in\mathcal{U}$，上闭性给出 $X^g\in\mathcal{U}\ (\forall g\in G)$，故 $\mathcal{U}\in\beta_G(X)$；而由 $F=\varnothing$ 得 $X\setminus X^G\in\mathcal{U}$，故 $X^G\notin\mathcal{U}$，即 $\mathcal{U}\notin\widehat{X^G}$。从而 $\overline{\eta_{\infty,X}(X^G)}\subsetneq R_\infty(X)^G$。

3. **满足“对每个 $G$ 集合均有 $\overline{\eta_{\infty,X}(X^G)}=R_\infty(X)^G$”的群 $G$ 的完全分类：**
   **定理：** 群 $G$ 对其每个 $G$ 集合 $X$ 都满足 $\overline{\eta_{\infty,X}(X^G)}=R_\infty(X)^G$，**当且仅当 $G$ 是有限生成群**（包括平凡群 $G=\{e\}$，由 $\varnothing$ 生成）。
   **证明：**
   - ($\Leftarrow$) 设 $G=\langle F\rangle$，$F\subseteq G$ 为有限生成集。对任意 $G$ 集合 $X$ 与 $x\in X^F$，其稳定化子 $\operatorname{Stab}_G(x)=\{g\in G : gx=x\}$ 为 $G$ 的子群且包含 $F$，故包含 $\langle F\rangle=G$，即 $x\in X^G$。从而 $X^F=X^G$，由上条充要条件即得 $\overline{\eta_{\infty,X}(X^G)}=R_\infty(X)^G$。
   - ($\Rightarrow$) 若 $G$ **不是**有限生成群，则对任意有限子集 $F\subseteq G$，子群 $\langle F\rangle$ 皆为 $G$ 的真子群。令 $\mathcal{H}=\{\langle F\rangle : F\subseteq G\text{ 有限}\}$ 为这些真子群构成的集合（非空，含 $\langle\varnothing\rangle=\{e\}$），构造左 $G$ 集合（左陪集空间的不交并）
     $$X = \bigsqcup_{H\in\mathcal{H}} G/H,\qquad g\cdot(H,aH):=(H,gaH).$$
     - 若 $(H,aH)\in X^G$，则 $\forall g\in G$ 有 $gaH=aH$，即 $a^{-1}Ga\subseteq H$，故 $G=H$，与 $H\subsetneq G$ 矛盾。因此 $X^G=\varnothing$，从而 $\overline{\eta_{\infty,X}(X^G)}=\varnothing$。
     - 另一方面，对任意有限子集 $F\subseteq G$，取 $H=\langle F\rangle\in\mathcal{H}$，则对所有 $g\in F\subseteq H$ 均有 $g\cdot(H,eH)=(H,gH)=(H,eH)$，故 $(H,eH)\in X^F$，即 $X^F\ne\varnothing$。由 $2.2$ 知 $R_\infty(X)^G\ne\varnothing$，故 $\overline{\eta_{\infty,X}(X^G)}=\varnothing\ne R_\infty(X)^G$。

---

### 2.4 群与底集均可数的具体例子与全部不动记录的描述

取底集 $X=\mathbb{N}=\{0,1,2,\ldots\}$，取群 $G=\operatorname{Sym}_{\mathrm{fin}}(\mathbb{N})$ 为 $\mathbb{N}$ 上所有有限支集置换构成的群，即
$$G=\bigl\{\sigma\in\operatorname{Sym}(\mathbb{N}) : \operatorname{supp}(\sigma):=\{x\in\mathbb{N} : \sigma(x)\ne x\}\text{ 有限}\bigr\},$$
作用为自然左作用 $\sigma\cdot x=\sigma(x)$。

1. **可数性：** $X=\mathbb{N}$ 可数无穷。因 $\operatorname{supp}(\sigma^{-1})=\operatorname{supp}(\sigma)$ 且 $\operatorname{supp}(\sigma\tau)\subseteq\operatorname{supp}(\sigma)\cup\operatorname{supp}(\tau)$，$G$ 为子群；记 $G_m=\{\sigma\in G : \operatorname{supp}(\sigma)\subseteq[m]\}\cong S_m$ 为有限群，则 $G=\bigcup_{m=1}^\infty G_m$ 为可数个有限集之并，且含所有对换 $(0\ k)\ (k\ge1)$，故 $G$ 可数无穷。
2. **$X^G=\varnothing$：** 对任意 $x\in\mathbb{N}$，对换 $(x\ x+1)\in G$ 移动 $x$，故 $X^G=\varnothing$。
3. **全部不动记录 $R_\infty(\mathbb{N})^G$ 的完整描述：**
   - 对任意 $r\in R_\infty(\mathbb{N})^G$（对应 $\mathcal{U}_r\in\beta_G(\mathbb{N})$）以及任意 $x\in\mathbb{N}$，取 $g=(x\ x+1)\in G$，由关键引理有 $\mathbb{N}^g=\mathbb{N}\setminus\{x,x+1\}\in\mathcal{U}_r$，从而 $\{x\}\notin\mathcal{U}_r$。因此 $\mathcal{U}_r$ 必为**非主超滤子**。
   - 反之，若 $\mathcal{U}\in\beta\mathbb{N}\setminus\mathbb{N}$ 为 $\mathbb{N}$ 上任意非主超滤子，则 $\mathcal{U}$ 包含 $\mathbb{N}$ 的全体余有限子集。对任意 $g\in G$，因 $\operatorname{supp}(g)$ 有限，故 $\mathbb{N}^g=\mathbb{N}\setminus\operatorname{supp}(g)$ 余有限，必属于 $\mathcal{U}$。由关键引理即得 $\mathcal{U}\in\beta_G(\mathbb{N})$。
   - 因此，在 $\Phi_\infty$ 下，**$R_\infty(\mathbb{N})^G$ 恰好对应 $\mathbb{N}$ 上全体非主超滤子空间 $\beta\mathbb{N}\setminus\mathbb{N}$**。由 ZFC 下超滤子引理应用于 $\mathbb{N}$ 上余有限子集滤子（Fréchet 滤子，每元非空且对有限交封闭），知 $\beta\mathbb{N}\setminus\mathbb{N}\ne\varnothing$，故 $R_\infty(\mathbb{N})^G\ne\varnothing$。
   - **作为记录族的显式刻画：** $r=(r_n)_{n\ge0}\in R_\infty(\mathbb{N})^G$ 当且仅当存在（唯一的）非主超滤子 $\mathcal{U}\in\beta\mathbb{N}\setminus\mathbb{N}$ 使 $r=r^{(\infty,\mathcal{U})}$，即 $r_0=\varnothing$，且对一切 $n\ge1$ 和 $f:\mathbb{N}\to[n]$，$r_n(f)$ 为使 $f^{-1}(\{i\})\in\mathcal{U}$ 的唯一 $i\in[n]$（等价地，在记录族中即 $\mathcal{U}_r$ 不含任何单点集/有限集，特别地对任意 $f:\mathbb{N}\to[n]$ 必有 $f^{-1}(\{r_n(f)\})$ 无限，且若 $f$ 最终常值于 $c$ 则 $r_n(f)=c$）。其上的子空间拓扑即为 $\beta\mathbb{N}\setminus\mathbb{N}$ 的 Stone 拓扑，以 $\{\widehat{A}\cap(\beta\mathbb{N}\setminus\mathbb{N}) : A\subseteq\mathbb{N}\}$ 为闭开基。

---

## 目标三：乘积比较

设 $(X_i)_{i\in I}$ 为一族 $G$ 集合，$P:=\prod_{i\in I}X_i$ 取对角作用 $g\cdot(x_i)_{i\in I}=(gx_i)_{i\in I}$，$p_i:P\to X_i$ 为第 $i$ 坐标投影。

### 3.1 $\Pi_{(X_i)}$ 的良定义性与连续性

1. **空指标族 $I=\varnothing$：**
   依约定，$P=\prod_{i\in\varnothing}X_i=\{*\}$ 与 $\prod_{i\in\varnothing}R_\infty(X_i)^G=\{*\}$ 均为单点集。因为 $P=\{*\}$ 上唯一群作用平凡，由目标一与目标二知 $R_\infty(\{*\})^G=R_\infty(\{*\})\cong\beta(\{*\})$ 为单点集。故 $\Pi_\varnothing$ 是单点集到单点集的唯一映射，良定义、连续且为同胚。
2. **非空指标族 $I\ne\varnothing$：**
   - *良定义性：* 对每个 $i\in I$，$p_i$ 为 $G$ 等变映射（$p_i(g\cdot x)=gx_i=g\cdot p_i(x)$）。由 $1.3$ 与 $1.4$ 知 $R_\infty(p_i)$ 将 $R_\infty(P)^G$ 映入 $R_\infty(X_i)^G$，故 $\Pi_{(X_i)}(r)=\bigl(R_\infty(p_i)r\bigr)_{i\in I}\in\prod_{i\in I}R_\infty(X_i)^G$。（若存在 $i_0\in I$ 使 $X_{i_0}=\varnothing$，则 $P=\varnothing$，故 $R_\infty(P)^G=\varnothing$ 且 $\prod_{i\in I}R_\infty(X_i)^G=\varnothing$，$\Pi_{(X_i)}$ 为空映射 $\varnothing\to\varnothing$。）
   - *连续性：* 对任意集合映射 $h:X\to Y$，映射 $R_\infty(h):R_\infty(X)\to R_\infty(Y)$ 连续：因为 $R_\infty(Y)$ 上赋予由所有观察 $\operatorname{ev}_{n,f}:s\mapsto s_n(f)$ 生成的最弱拓扑，而 $\operatorname{ev}_{n,f}\circ R_\infty(h):r\mapsto r_n(f\circ h)=\operatorname{ev}_{n,f\circ h}(r)$ 在 $R_\infty(X)$ 上连续。取 $h=p_i$，限制到子空间 $R_\infty(P)^G\subseteq R_\infty(P)$ 与 $R_\infty(X_i)^G\subseteq R_\infty(X_i)$ 后，每个分量映射 $r\mapsto R_\infty(p_i)r$ 连续。由乘积拓扑的泛性质，映射 $\Pi_{(X_i)}$ 连续。

*(注：在 $\Phi_\infty$ 下，对 $\mathcal{W}\in\beta_G(P)$，有 $\Pi_{(X_i)}(\mathcal{W})=\bigl((p_i)_*\mathcal{W}\bigr)_{i\in I}\in\prod_{i\in I}\beta_G(X_i)$。)*

---

### 3.2 对任意 $G$ 及任意集合指标族是否总为满射

**判定：是，对任意群 $G$ 及任意集合指标族 $(X_i)_{i\in I}$ 总为满射。**

**证明：**
- 若 $I=\varnothing$，已在 $3.1$ 证得其为单点集间双射，从而满射。
- 若 $I\ne\varnothing$ 且 $\prod_{i\in I}R_\infty(X_i)^G=\varnothing$，到达集为空集，任何以空集为到达集的映射皆空真满射（事实上此时存在 $i_0$ 使 $R_\infty(X_{i_0})^G=\varnothing$，从而 $R_\infty(P)^G=\varnothing$，两侧皆空）。
- 下设 $I\ne\varnothing$ 且 $\prod_{i\in I}R_\infty(X_i)^G\ne\varnothing$。任取一族 $G$-不变超滤子 $(\mathcal{U}_i)_{i\in I}\in\prod_{i\in I}\beta_G(X_i)$（特别地对每个 $i\in I$ 有 $X_i\ne\varnothing$）。注意到对角作用的不动点集满足
  $$P^g = \prod_{i\in I} X_i^g,\qquad P^F = \bigcap_{g\in F} P^g = \prod_{i\in I} X_i^F \quad (\forall\text{ 有限 } F\subseteq G).$$
  在 $P$ 的幂集 $\mathcal{P}(P)$ 中考虑如下子集族：
  $$\mathcal{S} := \bigl\{ p_i^{-1}(A) : i\in I,\ A\in\mathcal{U}_i \bigr\} \cup \bigl\{ P^g : g\in G \bigr\}.$$
  验证 $\mathcal{S}$ 具有**有限交性质**：任取 $\mathcal{S}$ 中有限个成员，设为 $p_{i_1}^{-1}(A_1),\dots,p_{i_m}^{-1}(A_m)$（$A_r\in\mathcal{U}_{i_r}$）与 $P^{g_1},\dots,P^{g_k}$（$m,k\ge0$）。令 $J=\{i_1,\dots,i_m\}\subseteq I$（有限）及 $F=\{g_1,\dots,g_k\}\subseteq G$（有限）。对每个 $j\in J$，令 $C_j:=\bigcap\{A_r : 1\le r\le m,\ i_r=j\}\in\mathcal{U}_j$。则上述有限交为
  $$\left(\bigcap_{r=1}^m p_{i_r}^{-1}(A_r)\right)\cap P^F = \prod_{i\in I} B_i,\qquad B_i=\begin{cases} C_i\cap X_i^F, & i\in J,\\ X_i^F, & i\in I\setminus J.\end{cases}$$
  由 $\mathcal{U}_i\in\beta_G(X_i)$ 及目标二关键引理，对一切 $i\in I$ 均有 $X_i^F\in\mathcal{U}_i$（当 $F=\varnothing$ 时 $X_i^\varnothing=X_i\in\mathcal{U}_i$）。故对 $i\in J$ 有 $B_i=C_i\cap X_i^F\in\mathcal{U}_i$，对 $i\in I\setminus J$ 有 $B_i=X_i^F\in\mathcal{U}_i$。从而对所有 $i\in I$ 均有 $B_i\ne\varnothing$。在 ZFC 下由选择公理，非空集合之乘积 $\prod_{i\in I} B_i\ne\varnothing$。
  由超滤子引理（ZFC），$\mathcal{S}$ 扩充为某个超滤子 $\mathcal{W}\in\beta P$。
  - 对一切 $g\in G$，因 $P^g\in\mathcal{S}\subseteq\mathcal{W}$，由目标二关键引理得 $\mathcal{W}\in\beta_G(P)$。
  - 对每个 $i\in I$ 及 $A\in\mathcal{U}_i$，有 $p_i^{-1}(A)\in\mathcal{S}\subseteq\mathcal{W}$，故 $\mathcal{U}_i\subseteq(p_i)_*\mathcal{W}$。因两者皆为 $X_i$ 上的超滤子，由极大性得 $(p_i)_*\mathcal{W}=\mathcal{U}_i$。
  于是在 $\Phi_\infty$ 下 $\Pi_{(X_i)}(\Psi_\infty(\mathcal{W}))$ 等于所取之 $(\mathcal{U}_i)_{i\in I}$，故 $\Pi_{(X_i)}$ 满射。

---

### 3.3 平凡群两集合比较映射 $\Pi_{X,Y}:R_\infty(X\times Y)\to R_\infty(X)\times R_\infty(Y)$ 为单射的充要条件

**结论：** 对平凡群 $G=\{e\}$，$\Pi_{X,Y}$ 为单射（等价地，双射）**当且仅当 $X$ 与 $Y$ 中至少有一个为有限集**（包括空集 $\varnothing$）。

**证明：**
- **充分性：**
  1. 若 $X=\varnothing$ 或 $Y=\varnothing$，则 $X\times Y=\varnothing$，$R_\infty(X\times Y)=\varnothing$，映射空真单射。
  2. 若 $X$ 有限非空（$Y$ 任意非空），设 $\mathcal{W}_1,\mathcal{W}_2\in\beta(X\times Y)$ 满足 $\Pi_{X,Y}(\mathcal{W}_1)=\Pi_{X,Y}(\mathcal{W}_2)=(\mathcal{U},\mathcal{V})$。因 $X$ 有限，超滤子 $\mathcal{U}$ 必为某个 $x_0\in X$ 的主超滤子 $\mathcal{U}_{x_0}$，故 $p_1^{-1}(\{x_0\})=\{x_0\}\times Y\in\mathcal{W}_1\cap\mathcal{W}_2$。于是对任意 $S\subseteq X\times Y$，记 $S_{x_0}:=\{y\in Y : (x_0,y)\in S\}$，有 $S\cap(\{x_0\}\times Y)=p_2^{-1}(S_{x_0})\cap(\{x_0\}\times Y)$，从而对 $t\in\{1,2\}$ 皆有
     $$S\in\mathcal{W}_t \iff S\cap(\{x_0\}\times Y)\in\mathcal{W}_t \iff p_2^{-1}(S_{x_0})\in\mathcal{W}_t \iff S_{x_0}\in\mathcal{V}.$$
     故 $\mathcal{W}_1=\mathcal{W}_2$。
  3. 若 $Y$ 有限非空，由对称性同理可得 $\Pi_{X,Y}$ 单射。

- **必要性：** 设 $X$ 和 $Y$ **均无限**。在 ZFC 下可分别在 $X$ 和 $Y$ 中取可数无穷子集 $X_0=\{x_n : n\in\mathbb{N}\}\subseteq X$ 与 $Y_0=\{y_n : n\in\mathbb{N}\}\subseteq Y$（其中 $n\mapsto x_n$ 和 $n\mapsto y_n$ 单射）。在 $\mathbb{N}$ 上任取非主超滤子 $\mathcal{N}\in\beta\mathbb{N}\setminus\mathbb{N}$，将其前推至 $X$ 和 $Y$，得非主超滤子 $\mathcal{U}:=\{A\subseteq X : \{n\in\mathbb{N} : x_n\in A\}\in\mathcal{N}\}\in\beta X$（含 $X_0$）及 $\mathcal{V}:=\{B\subseteq Y : \{n\in\mathbb{N} : y_n\in B\}\in\mathcal{N}\}\in\beta Y$（含 $Y_0$）。
  在 $X\times Y$ 上定义如下两个子集族（Fubini/张量积）：
  $$\mathcal{W}_1 := \bigl\{S\subseteq X\times Y : \{x\in X : S_x\in\mathcal{V}\}\in\mathcal{U}\bigr\},\qquad \mathcal{W}_2 := \bigl\{S\subseteq X\times Y : \{y\in Y : S^y\in\mathcal{U}\}\in\mathcal{V}\bigr\},$$
  其中 $S_x=\{y\in Y : (x,y)\in S\}$，$S^y=\{x\in X : (x,y)\in S\}$。
  - *验证 $\mathcal{W}_1,\mathcal{W}_2\in\beta(X\times Y)$：* 对 $\mathcal{W}_1$，显然 $\varnothing\notin\mathcal{W}_1$，$X\times Y\in\mathcal{W}_1$，且 $\mathcal{W}_1$ 上闭并对有限交封闭（因为 $(S_1\cap S_2)_x=(S_1)_x\cap (S_2)_x$ 且 $\mathcal{U},\mathcal{V}$ 为滤子）。对任意 $S\subseteq X\times Y$，由 $\mathcal{V}$ 为超滤子得 $((X\times Y)\setminus S)_x=Y\setminus S_x\in\mathcal{V}\iff S_x\notin\mathcal{V}$，再由 $\mathcal{U}$ 为超滤子即知 $S\in\mathcal{W}_1$ 或 $(X\times Y)\setminus S\in\mathcal{W}_1$。同理 $\mathcal{W}_2\in\beta(X\times Y)$。
  - *验证投影相等：* 对 $A\subseteq X$，$(p_1^{-1}(A))_x$ 当 $x\in A$ 时为 $Y\in\mathcal{V}$，否则为 $\varnothing\notin\mathcal{V}$，故 $p_1^{-1}(A)\in\mathcal{W}_1\iff A\in\mathcal{U}$；对 $B\subseteq Y$，$(p_2^{-1}(B))_x=B\ (\forall x\in X)$，故 $p_2^{-1}(B)\in\mathcal{W}_1\iff B\in\mathcal{V}$。同理 $(p_1)_*\mathcal{W}_2=\mathcal{U}$ 且 $(p_2)_*\mathcal{W}_2=\mathcal{V}$。于是 $\Pi_{X,Y}(\mathcal{W}_1)=(\mathcal{U},\mathcal{V})=\Pi_{X,Y}(\mathcal{W}_2)$。
  - *验证 $\mathcal{W}_1\ne\mathcal{W}_2$：* 考虑集合 $S=\{(x_i,y_j) : i,j\in\mathbb{N},\ i<j\}\subseteq X\times Y$。
    - 对每个 $x_i\in X_0$，$S_{x_i}=Y_0\setminus\{y_0,\dots,y_i\}$ 在 $Y_0$ 中余有限；因为 $Y_0\in\mathcal{V}$ 且 $\mathcal{V}$ 非主（不含有限集），故 $S_{x_i}\in\mathcal{V}$。因为 $X_0\in\mathcal{U}$，有 $\{x\in X : S_x\in\mathcal{V}\}=X_0\in\mathcal{U}$，所以 $S\in\mathcal{W}_1$。
    - 对每个 $y_j\in Y_0$，$S^{y_j}=\{x_0,\dots,x_{j-1}\}$ 有限；对 $y\notin Y_0$，$S^y=\varnothing$。因 $\mathcal{U}$ 非主（不含任何有限集），对一切 $y\in Y$ 皆有 $S^y\notin\mathcal{U}$，故 $\{y\in Y : S^y\in\mathcal{U}\}=\varnothing\notin\mathcal{V}$，所以 $S\notin\mathcal{W}_2$。
  故 $\mathcal{W}_1\ne\mathcal{W}_2$，$\Pi_{X,Y}$ 非单射。

---

### 3.4 任意群作用下的两个全称命题判定与证明

1. **命题一：“对任意群 $G$ 及 $G$ 集合 $X,Y$，若 $X,Y$ 至少一个有限，则 $\Pi_{X,Y}:R_\infty(X\times Y)^G\to R_\infty(X)^G\times R_\infty(Y)^G$ 为双射。”**
   **判定：真。**
   **证明：**
   - *满射性：* 由 $3.2$ 已证，对任意群 $G$ 与任意集合指标族，$\Pi$ 恒为满射，特别地对两因子 $\Pi_{X,Y}$ 为满射。
   - *单射性：* 在定义下，$R_\infty(X\times Y)^G\subseteq R_\infty(X\times Y)$ 且 $R_\infty(X)^G\times R_\infty(Y)^G\subseteq R_\infty(X)\times R_\infty(Y)$，而等变比较映射 $\Pi_{X,Y}$ 正是平凡群情形（忘却群作用后）的比较映射 $R_\infty(X\times Y)\to R_\infty(X)\times R_\infty(Y)$ 在子集 $R_\infty(X\times Y)^G$ 上的限制（两者映射规则均为 $r\mapsto(R_\infty(p_1)r, R_\infty(p_2)r)$）。当 $X,Y$ 至少一个有限时，由 $3.3$ 知平凡群情形的比较映射为单射，故其在子集上的限制 $\Pi_{X,Y}$ 亦必单射。
   综上，$\Pi_{X,Y}$ 既是单射又是满射，故为双射（且因是从紧致空间到 Hausdorff 空间的连续双射，实为同胚）。

2. **命题二：“对任意群 $G$ 及 $G$ 集合 $X,Y$，若 $X^G=Y^G=\varnothing$，则 $\Pi_{X,Y}:R_\infty(X\times Y)^G\to R_\infty(X)^G\times R_\infty(Y)^G$ 为单射。”**
   **判定：假。**
   **证明（反例构造）：**
   取 $2.4$ 中的可数群与可数作用：$G=\operatorname{Sym}_{\mathrm{fin}}(\mathbb{N})$，$X=Y=\mathbb{N}$。如 $2.4$ 所证，已有 $X^G=Y^G=\varnothing$。
   任取非主超滤子 $\mathcal{U}\in\beta\mathbb{N}\setminus\mathbb{N}$，如 $3.3$ 构造 $\mathbb{N}\times\mathbb{N}$ 上的两个超滤子
   $$\mathcal{W}_1=\mathcal{U}\otimes\mathcal{U}=\{S\subseteq\mathbb{N}\times\mathbb{N} : \{i\in\mathbb{N} : S_i\in\mathcal{U}\}\in\mathcal{U}\},\quad \mathcal{W}_2=\mathcal{U}\odot\mathcal{U}=\{S\subseteq\mathbb{N}\times\mathbb{N} : \{j\in\mathbb{N} : S^j\in\mathcal{U}\}\in\mathcal{U}\}.$$
   由 $3.3$ 的证明（取 $X_0=Y_0=\mathbb{N},\ x_n=y_n=n,\ \mathcal{N}=\mathcal{U}$），有：
   - $\mathcal{W}_1,\mathcal{W}_2\in\beta(\mathbb{N}\times\mathbb{N})$ 且 $(p_1)_*\mathcal{W}_t=(p_2)_*\mathcal{W}_t=\mathcal{U}\ (t=1,2)$；
   - $\mathcal{W}_1\ne\mathcal{W}_2$（因为 $S=\{(i,j)\in\mathbb{N}\times\mathbb{N} : i<j\}\in\mathcal{W}_1\setminus\mathcal{W}_2$）。

   最后验证 $\mathcal{W}_1,\mathcal{W}_2$ 均属于 $\beta_G(\mathbb{N}\times\mathbb{N})\cong R_\infty(\mathbb{N}\times\mathbb{N})^G$：对任意 $g\in G$，因为 $\operatorname{supp}(g)$ 有限且 $\mathcal{U}$ 非主，故 $\mathbb{N}^g=\mathbb{N}\setminus\operatorname{supp}(g)\in\mathcal{U}$。由于 $(p_1)_*\mathcal{W}_t=(p_2)_*\mathcal{W}_t=\mathcal{U}$，得 $p_1^{-1}(\mathbb{N}^g)\in\mathcal{W}_t$ 且 $p_2^{-1}(\mathbb{N}^g)\in\mathcal{W}_t$。从而对角作用的不动点集
   $$(\mathbb{N}\times\mathbb{N})^g = \mathbb{N}^g\times\mathbb{N}^g = p_1^{-1}(\mathbb{N}^g)\cap p_2^{-1}(\mathbb{N}^g) \in \mathcal{W}_t \quad (t=1,2).$$
   由目标二关键引理，即知 $\mathcal{W}_1,\mathcal{W}_2\in\beta_G(\mathbb{N}\times\mathbb{N})$。因此对应记录 $r^{(1)}=\Psi_\infty(\mathcal{W}_1)\ne r^{(2)}=\Psi_\infty(\mathcal{W}_2)$ 均在 $R_\infty(\mathbb{N}\times\mathbb{N})^G$ 中，且 $\Pi_{\mathbb{N},\mathbb{N}}(r^{(1)})=\Pi_{\mathbb{N},\mathbb{N}}(r^{(2)})$。故 $\Pi_{\mathbb{N},\mathbb{N}}$ 非单射，原全称命题为假。
