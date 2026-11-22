下面在 ZFC 框架下依次完成三个目标，并全程覆盖空底集（及第三项中的空指标族）。

---

### 预备记号与约定

对任意集合 $X$ 与子集 $A\subseteq X$，记 $\mathbf{1}_A:X\to[2]$ 为特征函数（$x\in A$ 时取 $1$，否则取 $0$）；记 $\tau:[2]\to[2]$ 为对换 $\tau(0)=1,\tau(1)=0$。显然 $A\mapsto\mathbf{1}_A$ 给出 $\mathcal{P}(X)$ 与 $\operatorname{Map}(X,[2])$ 之间的双射，且 $\tau\circ\mathbf{1}_A=\mathbf{1}_{X\setminus A}$。

记
$$\mathcal{S}(X):=\bigl\{\mathcal{F}\subseteq\mathcal{P}(X): X\in\mathcal{F},\ \forall A\subseteq X\ (A\in\mathcal{F}\iff X\setminus A\notin\mathcal{F})\bigr\},$$
并记 $\operatorname{Ult}(X)$ 为 $X$ 上全体超滤（ultrafilter）的集合。特别地：
- 当 $X=\varnothing$ 时，若 $\mathcal{F}\in\mathcal{S}(\varnothing)$，则由定义 $\varnothing\in\mathcal{F}$ 且 $\varnothing=\varnothing\setminus\varnothing\notin\mathcal{F}$，矛盾，故 $\mathcal{S}(\varnothing)=\varnothing$；同理超滤要求 $X\in\mathcal{U}$ 且 $\varnothing\notin\mathcal{U}$，故 $\operatorname{Ult}(\varnothing)=\varnothing$。
- 对任意集合 $X$，均有 $\operatorname{Ult}(X)\subseteq\mathcal{S}(X)$。

对任意映射 $h:X\to Y$ 与族 $\mathcal{F}\subseteq\mathcal{P}(X)$，记前推
$$h_*(\mathcal{F}):=\{B\subseteq Y: h^{-1}(B)\in\mathcal{F}\}.$$
对 $G$ 集合 $X$、元素 $g\in G$ 与子集 $F\subseteq G$，记
$$X^g:=\{x\in X: gx=x\},\qquad X^F:=\bigcap_{g\in F}X^g\quad(\text{约定 }X^\varnothing=X).$$

---

## 目标 1：截断及其相容关系

### 1.1 对每个 $m\in\mathbb{Z}_{\ge1}\cup\{\infty\}$ 和每个集合 $X$ 的完全分类

首先注意 $R_m(X)$ 是 $\prod_{0\le n\le m}[n]^{\operatorname{Map}(X,[n])}$ 的子集（$n$ 遍历不超过 $m$ 的非负整数），故为合法集合。

#### 情形 0：$X=\varnothing$
对每个允许的参数 $m$，均有 $0\le m$。而 $\operatorname{Map}(\varnothing,[0])=\operatorname{Map}(\varnothing,\varnothing)=\{\emptyset\}$ 是单点集，$[0]=\varnothing$ 为空集，因此不存在映射 $r_0:\operatorname{Map}(\varnothing,[0])\to[0]$。故对一切 $m\in\mathbb{Z}_{\ge1}\cup\{\infty\}$：
$$R_m(\varnothing)=\varnothing.$$

以下设 $X\ne\varnothing$。此时 $\operatorname{Map}(X,[0])=\varnothing$，故 $r_0:\varnothing\to\varnothing$ 唯一存在（即空映射 $\emptyset$）。同时，对一切允许的 $n,k$：
- 若 $n=0$，不存在 $f:X\to[0]$；
- 若 $k=0$ 且 $n\ge1$，不存在 $a:[n]\to[0]$。

因此，当 $X\ne\varnothing$ 时，$r_0$ 唯一且涉及 $n=0$ 或 $k=0$ 的相容条件全部空真，只需考察 $1\le n,k\le m$。此外，$\operatorname{Map}(X,[1])$ 仅含唯一常值映射 $f_1:X\to[1]$，故 $r_1:\operatorname{Map}(X,[1])\to[1]$ 也唯一确定为 $r_1(f_1)=0$。

#### 情形 1：$m=1$（$X\ne\varnothing$）
允许的 $n,k\ge1$ 只有 $n=k=1$，唯一的 $a:[1]\to[1]$ 是 $\mathrm{id}_{[1]}$，相容条件恒成立。因此 $R_1(X)$ 是**单点集**：
$$|R_1(X)|=1,$$
其唯一元素为 $r=(r_0,r_1)$（即任意 $x\in X$ 的点值记录 $\eta_{1,X}(x)$）。

#### 情形 2：$m=2$（$X\ne\varnothing$）
**命题 1.1.** 映射
$$\Phi_{2,X}:R_2(X)\longrightarrow\mathcal{S}(X),\qquad r\longmapsto\mathcal{F}_r:=\{A\subseteq X: r_2(\mathbf{1}_A)=1\}$$
是双射。

**证明.**
1. *良定义*：设 $r\in R_2(X)$。取 $c_1:[1]\to[2]$ 为 $c_1(0)=1$，则 $c_1\circ f_1=\mathbf{1}_X$，由相容性得
   $$r_2(\mathbf{1}_X)=r_2(c_1\circ f_1)=c_1(r_1(f_1))=c_1(0)=1,$$
   故 $X\in\mathcal{F}_r$。再对任意 $A\subseteq X$ 取 $a=\tau:[2]\to[2]$，有 $\tau\circ\mathbf{1}_A=\mathbf{1}_{X\setminus A}$，故
   $$r_2(\mathbf{1}_{X\setminus A})=r_2(\tau\circ\mathbf{1}_A)=\tau(r_2(\mathbf{1}_A))=1-r_2(\mathbf{1}_A),$$
   于是 $A\in\mathcal{F}_r\iff X\setminus A\notin\mathcal{F}_r$。从而 $\mathcal{F}_r\in\mathcal{S}(X)$（并自动推出 $\varnothing\notin\mathcal{F}_r$）。
2. *逆映射的构造与核验*：对任意 $\mathcal{F}\in\mathcal{S}(X)$，定义 $r^{\mathcal{F}}=(r_0,r_1,r_2)$，其中 $r_0=\emptyset$，$r_1(f_1)=0$，并对 $A\subseteq X$ 令
   $$r_2(\mathbf{1}_A)=\begin{cases}1,&A\in\mathcal{F},\\0,&A\notin\mathcal{F}.\end{cases}$$
   逐一核验所有 $n,k\in\{1,2\}$ 与 $a:[n]\to[k]$ 的相容条件 $a(r_n(f))=r_k(a\circ f)$：
   - $k=1$：等式两端均落入 $[1]=\{0\}$，自动成立。
   - $n=1,k=2$：$f=f_1$，$r_1(f_1)=0$。$a$ 仅有两种可能：$a(0)=0$ 时 $a\circ f_1=\mathbf{1}_\varnothing$，由 $\varnothing\notin\mathcal{F}$ 得 $r_2(\mathbf{1}_\varnothing)=0=a(0)$；$a(0)=1$ 时 $a\circ f_1=\mathbf{1}_X$，由 $X\in\mathcal{F}$ 得 $r_2(\mathbf{1}_X)=1=a(0)$。
   - $n=2,k=2$：$f=\mathbf{1}_A$。$a:[2]\to[2]$ 仅有四个映射：
     - $a=\mathrm{id}_{[2]}$：显然成立；
     - $a\equiv 0$：$a(r_2(\mathbf{1}_A))=0=r_2(\mathbf{1}_\varnothing)=r_2(a\circ\mathbf{1}_A)$；
     - $a\equiv 1$：$a(r_2(\mathbf{1}_A))=1=r_2(\mathbf{1}_X)=r_2(a\circ\mathbf{1}_A)$；
     - $a=\tau$：由 $X\setminus A\in\mathcal{F}\iff A\notin\mathcal{F}$ 得 $r_2(\tau\circ\mathbf{1}_A)=r_2(\mathbf{1}_{X\setminus A})=1-r_2(\mathbf{1}_A)=\tau(r_2(\mathbf{1}_A))$。

   故 $r^{\mathcal{F}}\in R_2(X)$。又显然 $\mathcal{F}_{r^{\mathcal{F}}}=\mathcal{F}$，且由 $r_0,r_1$ 唯一与 $r_2$ 被 $\mathcal{F}_r$ 唯一决定得 $r^{\mathcal{F}_r}=r$。$\square$

（注：当 $X$ 有限且 $|X|=N\ge1$ 时，$\mathcal{P}(X)$ 共分为 $2^{N-1}$ 对互补子集 $\{A,X\setminus A\}$，其中 $\{\varnothing,X\}$ 的取向固定，其余 $2^{N-1}-1$ 对可独立任选其一，故 $|R_2(X)|=2^{2^{N-1}-1}$。）

#### 情形 3：$m\ge3$（含 $m=\infty$，$X\ne\varnothing$）
**命题 1.2.** 对每个 $m\in\mathbb{Z}_{\ge3}\cup\{\infty\}$，映射
$$\Phi_{m,X}:R_m(X)\longrightarrow\operatorname{Ult}(X),\qquad r\longmapsto\mathcal{U}_r:=\{A\subseteq X: r_2(\mathbf{1}_A)=1\}$$
是双射；其逆映射 $\mathcal{U}\mapsto r^{\mathcal{U}}$ 由 $r^{\mathcal{U}}_0=\emptyset$ 以及对每个 $1\le n\le m$ 和 $f:X\to[n]$，令 $(r^{\mathcal{U}})_n(f)$ 为满足 $f^{-1}(j)\in\mathcal{U}$ 的唯一 $j\in[n]$ 给出。

**证明.**
1. *$\mathcal{U}_r$ 是超滤*：设 $r\in R_m(X)$（$m\ge3$）。任取 $X$ 的一个三元无交划分 $X=A_0\sqcup A_1\sqcup A_2$，它对应唯一映射 $f:X\to[3]$（使 $f^{-1}(i)=A_i$）。对每个 $i\in[3]$ 定义 $\delta_i:[3]\to[2]$ 满足 $\delta_i(i)=1$ 且 $\delta_i(j)=0$（$j\ne i$），则 $\delta_i\circ f=\mathbf{1}_{A_i}$。由相容性（$3\le m$）：
   $$r_2(\mathbf{1}_{A_i})=r_2(\delta_i\circ f)=\delta_i(r_3(f)).$$
   记 $j_0=r_3(f)\in[3]$，则 $r_2(\mathbf{1}_{A_i})=1\iff i=j_0$。由此得到**三划分性质**：对 $X$ 的任意三元无交划分 $X=A_0\sqcup A_1\sqcup A_2$，恰有一个 $A_i$ 属于 $\mathcal{U}_r$。
   由此立即推得全部超滤公理：
   - **$\varnothing\notin\mathcal{U}_r$ 且 $X\in\mathcal{U}_r$**：取划分 $(X,\varnothing,\varnothing)$。若 $\varnothing\in\mathcal{U}_r$，则后两块均属于 $\mathcal{U}_r$，与唯一性矛盾，故 $\varnothing\notin\mathcal{U}_r$，进而 $X\in\mathcal{U}_r$。
   - **极大性（互补性）**：对任意 $A\subseteq X$ 取划分 $(A,X\setminus A,\varnothing)$，由 $\varnothing\notin\mathcal{U}_r$ 知 $A$ 与 $X\setminus A$ 恰有一个属于 $\mathcal{U}_r$。
   - **上闭性**：若 $A\in\mathcal{U}_r$ 且 $A\subseteq B\subseteq X$，取划分 $(A,B\setminus A,X\setminus B)$。由唯一性知 $X\setminus B\notin\mathcal{U}_r$，再由互补性得 $B\in\mathcal{U}_r$。
   - **有限交封闭**：若 $A,B\in\mathcal{U}_r$，取划分 $(A\cap B,A\setminus B,X\setminus A)$。由 $A\in\mathcal{U}_r$ 知 $X\setminus A\notin\mathcal{U}_r$；由 $B\in\mathcal{U}_r$ 知 $X\setminus B\notin\mathcal{U}_r$，又 $A\setminus B\subseteq X\setminus B$，由上闭性知 $A\setminus B\notin\mathcal{U}_r$。于是由三划分性质必有 $A\cap B\in\mathcal{U}_r$。

   因此 $\mathcal{U}_r\in\operatorname{Ult}(X)$。

2. *$r$ 由 $\mathcal{U}_r$ 唯一决定*：设 $1\le n\le m$ 且 $f:X\to[n]$，记 $j=r_n(f)\in[n]$。定义 $\delta_{n,j}:[n]\to[2]$ 为 $\delta_{n,j}(j)=1$，其余取 $0$，则 $\delta_{n,j}\circ f=\mathbf{1}_{f^{-1}(j)}$。由相容性（$n,2\le m$）：
   $$r_2(\mathbf{1}_{f^{-1}(j)})=\delta_{n,j}(r_n(f))=\delta_{n,j}(j)=1,$$
   即 $f^{-1}(j)\in\mathcal{U}_r$。因为 $\{f^{-1}(i):i\in[n]\}$ 两两无交，若 $i\ne j$ 且 $f^{-1}(i)\in\mathcal{U}_r$ 则 $\varnothing=f^{-1}(i)\cap f^{-1}(j)\in\mathcal{U}_r$ 矛盾，故 $r_n(f)$ 是满足 $f^{-1}(j)\in\mathcal{U}_r$ 的唯一 $j\in[n]$。

3. *逆映射的良定义与相容性*：任取 $\mathcal{U}\in\operatorname{Ult}(X)$。对任意 $1\le n\le m$ 和 $f:X\to[n]$，有有限无交分解 $X=\bigsqcup_{i=0}^{n-1}f^{-1}(i)$。若所有 $f^{-1}(i)\notin\mathcal{U}$，则由互补性 $X\setminus f^{-1}(i)\in\mathcal{U}$，有限交得 $\varnothing=\bigcap_{i=0}^{n-1}(X\setminus f^{-1}(i))\in\mathcal{U}$ 矛盾；又两两无交故至多一个在 $\mathcal{U}$ 中。因此 $(r^{\mathcal{U}})_n(f)$ 良定义。
   对任意 $1\le n,k\le m$、$f:X\to[n]$ 和 $a:[n]\to[k]$，记 $j=(r^{\mathcal{U}})_n(f)$，则 $f^{-1}(j)\in\mathcal{U}$。由于 $f^{-1}(j)\subseteq (a\circ f)^{-1}(a(j))$，由上闭性得 $(a\circ f)^{-1}(a(j))\in\mathcal{U}$，由唯一性即 $(r^{\mathcal{U}})_k(a\circ f)=a(j)=a((r^{\mathcal{U}})_n(f))$。故 $r^{\mathcal{U}}\in R_m(X)$。
   最后，对任意 $A\subseteq X$，$(r^{\mathcal{U}})_2(\mathbf{1}_A)=1\iff\mathbf{1}_A^{-1}(1)=A\in\mathcal{U}$，故 $\mathcal{U}_{r^{\mathcal{U}}}=\mathcal{U}$；结合第 2 步知 $r^{\mathcal{U}_r}=r$。$\square$

**分类总结（覆盖 $X=\varnothing$）：**
- $m=1$：$R_1(\varnothing)=\varnothing$；$X\ne\varnothing$ 时 $|R_1(X)|=1$。
- $m=2$：$R_2(X)\cong\mathcal{S}(X)$（空集时两侧均为空集）。
- $m\ge3$（含 $m=\infty$）：$R_m(X)\cong\operatorname{Ult}(X)$（空集时两侧均为空集）。

---

### 1.2 遗忘映射 $q_{m,k}$ 的像与各纤维

对 $m\ge k\ge1$，遗忘映射 $q_{m,k}:R_m(X)\to R_k(X)$ 将 $(r_n)_{0\le n\le m}$ 截断为 $(r_n)_{0\le n\le k}$，显然良定义（相容条件自动保持）且满足 $q_{m,m}=\mathrm{id}$、$q_{k,\ell}\circ q_{m,k}=q_{m,\ell}$（$m\ge k\ge\ell\ge1$）。

- **当 $X=\varnothing$**：$q_{m,k}:\varnothing\to\varnothing$ 为空双射，像为 $\varnothing$，无纤维。
- **当 $X\ne\varnothing$**：
  1. **$m=k$**：$q_{m,m}=\mathrm{id}_{R_m(X)}$，像为 $R_m(X)$，对每个 $s\in R_m(X)$ 纤维为 $\{s\}$。
  2. **$m\ge k\ge3$**：因 $\Phi_{m,X}(r)$ 与 $\Phi_{k,X}(q_{m,k}(r))$ 均由 $r_2$ 给出，故 $\Phi_{k,X}\circ q_{m,k}=\Phi_{m,X}$，即 $q_{m,k}$ 在分类双射下对应 $\mathrm{id}_{\operatorname{Ult}(X)}$。从而 $q_{m,k}$ 是**双射**：像为整个 $R_k(X)$，对每个 $s\in R_k(X)$ 纤维为单点集 $\{r^{\mathcal{U}_s}\}$。
  3. **$m\ge3, k=2$**：同理 $\Phi_{2,X}\circ q_{m,2}=\iota\circ\Phi_{m,X}$，其中 $\iota:\operatorname{Ult}(X)\hookrightarrow\mathcal{S}(X)$ 为包含映射。从而 $q_{m,2}$ 是**单射**：
     - **像**：$\operatorname{im}(q_{m,2})=\{s\in R_2(X):\mathcal{F}_s\in\operatorname{Ult}(X)\}$。在 $\mathcal{S}(X)$ 内部，$\mathcal{F}\in\mathcal{S}(X)$ 是超滤当且仅当 $\mathcal{F}$ **对二元交封闭**（因为 $X\in\mathcal{F},\varnothing\notin\mathcal{F}$ 与互补性已成立，而上闭性可由二元交推出：若 $A\in\mathcal{F}, A\subseteq B$ 且 $B\notin\mathcal{F}$，则 $X\setminus B\in\mathcal{F}$，交得 $\varnothing=A\cap(X\setminus B)\in\mathcal{F}$ 矛盾）。
     - **纤维**：对 $s\in R_2(X)$，
       $$q_{m,2}^{-1}(s)=\begin{cases}\{r^{\mathcal{F}_s}\},&\mathcal{F}_s\in\operatorname{Ult}(X),\\\varnothing,&\mathcal{F}_s\notin\operatorname{Ult}(X).\end{cases}$$
     - **满射判准**：$q_{m,2}$ 为满射（从而双射）当且仅当 $|X|\le2$。事实上：$|X|=1$ 时 $|\operatorname{Ult}(X)|=1=|\mathcal{S}(X)|$；$|X|=2$ 时 $|\operatorname{Ult}(X)|=2=|\mathcal{S}(X)|$；而当 $|X|\ge3$ 时，任取三个互异元素 $x_0,x_1,x_2\in X$，定义（无需选择公理）
       $$\mathcal{F}:=\{A\subseteq X: |A\cap\{x_0,x_1,x_2\}|\ge2\}.$$
       因 $|A\cap\{x_0,x_1,x_2\}|+|(X\setminus A)\cap\{x_0,x_1,x_2\}|=3$，恰有一项 $\ge2$，且 $X\in\mathcal{F}$，故 $\mathcal{F}\in\mathcal{S}(X)$；但 $\{x_0,x_1\},\{x_1,x_2\}\in\mathcal{F}$ 而其交 $\{x_1\}\notin\mathcal{F}$，故 $\mathcal{F}\notin\operatorname{Ult}(X)$，所以 $q_{m,2}$ 非满射。
  4. **$m\ge2, k=1$**：因 $X\ne\varnothing$，取 $x\in X$ 即有 $\eta_{m,X}(x)\in R_m(X)$，故 $R_m(X)\ne\varnothing$，而 $R_1(X)=\{*\}$ 为单点集。因此 $q_{m,1}$ 是**满射**，像为 $R_1(X)=\{*\}$，唯一纤维为整个 $R_m(X)$（单射当且仅当 $|R_m(X)|=1\iff|X|=1$，因为 $|X|\ge2$ 时任取 $x\ne y\in X$ 均有 $\eta_{m,X}(x)_2(\mathbf{1}_{\{x\}})=1\ne0=\eta_{m,X}(y)_2(\mathbf{1}_{\{x\}})$）。

---

### 1.3 与集合映射 $h:X\to Y$ 的相容性

设 $h:X\to Y$ 为任意集合映射，$m\in\mathbb{Z}_{\ge1}\cup\{\infty\}$。

1. **良定义与函子性**：对 $r\in R_m(X)$、允许的 $n,k$、$f:Y\to[n]$ 与 $a:[n]\to[k]$，有
   $$a\bigl((R_m(h)r)_n(f)\bigr)=a\bigl(r_n(f\circ h)\bigr)=r_k\bigl(a\circ(f\circ h)\bigr)=r_k\bigl((a\circ f)\circ h\bigr)=(R_m(h)r)_k(a\circ f),$$
   故 $R_m(h)r\in R_m(Y)$。对 $X=\varnothing$，$R_m(h)$ 为唯一空映射 $\varnothing\to R_m(Y)$。进一步，对 $h_1:X\to Y$ 与 $h_2:Y\to Z$：
   $$(R_m(\mathrm{id}_X)r)_n(f)=r_n(f\circ\mathrm{id}_X)=r_n(f),$$
   $$(R_m(h_2\circ h_1)r)_n(f)=r_n(f\circ h_2\circ h_1)=(R_m(h_1)r)_n(f\circ h_2)=\bigl(R_m(h_2)(R_m(h_1)r)\bigr)_n(f),$$
   即 $R_m(\mathrm{id}_X)=\mathrm{id}_{R_m(X)}$ 且 $R_m(h_2\circ h_1)=R_m(h_2)\circ R_m(h_1)$（$R_m$ 为协变函子）。

2. **与上述分类双射的相容性**：
   - 若 $X=\varnothing$，两侧映射均为空映射 $\varnothing\to R_m(Y)$（或 $\varnothing\to\mathcal{S}(Y)$、$\varnothing\to\operatorname{Ult}(Y)$），显然相容。
   - 若 $X\ne\varnothing$，则必有 $Y\ne\varnothing$（因存在映射 $h:X\to Y$）：
     - $m=1$：$R_1(h)$ 是两单点集间的唯一映射。
     - $m=2$：对任意 $\mathcal{F}\in\mathcal{S}(X)$，由 $h^{-1}(Y)=X\in\mathcal{F}$ 及 $h^{-1}(Y\setminus B)=X\setminus h^{-1}(B)$ 知 $h_*(\mathcal{F})\in\mathcal{S}(Y)$。对 $r\in R_2(X)$ 和 $B\subseteq Y$，因 $\mathbf{1}_B\circ h=\mathbf{1}_{h^{-1}(B)}$，有
       $$B\in\Phi_{2,Y}(R_2(h)r)\iff (R_2(h)r)_2(\mathbf{1}_B)=1\iff r_2(\mathbf{1}_{h^{-1}(B)})=1\iff h^{-1}(B)\in\Phi_{2,X}(r)\iff B\in h_*(\Phi_{2,X}(r)),$$
       故 $\Phi_{2,Y}\circ R_2(h)=h_*\circ\Phi_{2,X}$。
     - $m\ge3$（含 $\infty$）：对任意 $\mathcal{U}\in\operatorname{Ult}(X)$，原像保持 $\varnothing,Y$、包含、有限交与补集，故 $h_*(\mathcal{U})\in\operatorname{Ult}(Y)$。由与上完全相同的 $n=2$ 计算即得 $\Phi_{m,Y}\circ R_m(h)=h_*\circ\Phi_{m,X}$。

3. **与 $q_{m,k}$ 及 $\eta_{m,-}$ 的自然性**：
   - 对 $m\ge k\ge1$，由定义立得 $q_{m,k,Y}\circ R_m(h)=R_k(h)\circ q_{m,k,X}$。
   - 对任意 $x\in X$，$\eta_{m,X}(x)\in R_m(X)$（因 $a(f(x))=(a\circ f)(x)$），且
     $$(R_m(h)\eta_{m,X}(x))_n(f)=\eta_{m,X}(x)_n(f\circ h)=f(h(x))=\eta_{m,Y}(h(x))_n(f),$$
     即 $R_m(h)\circ\eta_{m,X}=\eta_{m,Y}\circ h$（$X=\varnothing$ 时两端均为空映射）。在 $m\ge2$ 的分类下，$\eta_{m,X}(x)$ 对应主超滤 $\mathcal{U}_x:=\{A\subseteq X: x\in A\}$。

4. **对群作用的推论**：若 $G$ 左作用于 $X$，因 $(g_1g_2)_X=(g_1)_X\circ(g_2)_X$ 且 $e_X=\mathrm{id}_X$，由函子性立知 $g\cdot r:=R_m(g_X)r$ 定义了 $G$ 在 $R_m(X)$ 上的左作用；在 $\Phi_{m,X}$ 下（$m\ge2$），它对应 $g\cdot\mathcal{F}=(g_X)_*(\mathcal{F})=\{A\subseteq X: g^{-1}A\in\mathcal{F}\}=\{gB: B\in\mathcal{F}\}$。由自然性知 $q_{m,k}$ 和 $\eta_{m,X}$ 都是 $G$-等变映射，从而 $q_{m,k}$ 限制为良定义映射 $q_{m,k}^G:R_m(X)^G\to R_k(X)^G$。

---

### 1.4 任意有限 $G$ 集合 $X$ 的 $R_m(X)^G$ 与限制映射

设 $X$ 为**有限** $G$ 集合（群 $G$ 可任意，不必有限；允许 $X=\varnothing$）。记作用同态 $\rho:G\to\operatorname{Sym}(X),\ g\mapsto g_X$ 的像为 $\overline{G}:=\operatorname{im}(\rho)\le\operatorname{Sym}(X)$，则 $\overline{G}$ 是有限群，且 $G$ 与 $\overline{G}$ 在 $X$、$\mathcal{P}(X)$ 及 $R_m(X)$ 上具有完全相同的轨道与不动点。对每个 $\sigma\in\overline{G}$，记 $c(\sigma)$ 为置换 $\sigma$ 在 $X$ 上的不相交轮换个数（含 $1$-轮换；特别 $X=\varnothing$ 时 $c(\mathrm{id}_\varnothing)=0$）。

#### （1）$m=1$
- **存在判准**：$R_1(X)^G\ne\varnothing\iff X\ne\varnothing$。
- **精确基数**：
  $$|R_1(X)^G|=\begin{cases}0,&X=\varnothing,\\1,&X\ne\varnothing.\end{cases}$$
  （$X\ne\varnothing$ 时 $R_1(X)$ 为单点集，必被 $G$ 固定。）

#### （2）$m=2$
在 $G$-等变双射 $\Phi_{2,X}:R_2(X)\xrightarrow{\sim}\mathcal{S}(X)$ 下，$R_2(X)^G\cong\mathcal{S}(X)^G$，其中
$$\mathcal{S}(X)^G=\{\mathcal{F}\in\mathcal{S}(X): \forall g\in G,\ \forall A\subseteq X,\ (A\in\mathcal{F}\iff gA\in\mathcal{F})\}.$$

**定理 1.3.** 对任意有限 $G$ 集合 $X$：
1. **存在判准**：以下四款等价：
   - (i) $R_2(X)^G\ne\varnothing$；
   - (ii) 取补映射 $c(A)=X\setminus A$ 在轨道集 $\mathcal{P}(X)/G$ 上诱导的对合 $\bar{c}(G\cdot A):=G\cdot(X\setminus A)$ 没有不动点；
   - (iii) 不存在 $A\subseteq X$ 与 $g\in G$ 使得 $gA=X\setminus A$；
   - (iv) 对每个 $g\in G$（等价地，对每个 $\sigma\in\overline{G}$），置换 $g_X$ 在 $X$ 上至少有一个**奇数长度**的轮换。
   （特别地，当 $X=\varnothing$ 时，$e_\varnothing$ 没有任何轮换，故 (iv) 不成立，且 $e\varnothing=\varnothing=\varnothing\setminus\varnothing$，与 $R_2(\varnothing)^G=\varnothing$ 一致。）
2. **精确基数**：
   $$|R_2(X)^G|=\begin{cases}0,&\text{若存在 }g\in G\text{ 使 }g_X\text{ 在 }X\text{ 上的轮换长度全为偶数（含 }X=\varnothing\text{）},\\[4pt]2^{\frac{1}{2}|\mathcal{P}(X)/G|-1},&\text{若每个 }g\in G\text{ 均有至少一个奇数长度的轮换},\end{cases}$$
   其中由有限群 $\overline{G}$ 作用于有限集 $\mathcal{P}(X)$ 的 Cauchy–Frobenius（Burnside）引理，
   $$|\mathcal{P}(X)/G|=|\mathcal{P}(X)/\overline{G}|=\frac{1}{|\overline{G}|}\sum_{\sigma\in\overline{G}}2^{c(\sigma)}$$
   （若 $G$ 自身有限，亦可写作 $\frac{1}{|G|}\sum_{g\in G}2^{c(g_X)}$）。

**证明.**
首先，$c(gA)=X\setminus gA=g(X\setminus A)$，故 $c$ 与 $G$-作用交换，从而在 $\mathcal{P}(X)/G$ 上良定义对合 $\bar{c}$。显然 $\bar{c}(G\cdot A)=G\cdot A\iff X\setminus A\in G\cdot A\iff \exists g\in G,\ gA=X\setminus A$，故 (ii)$\iff$(iii)。

再证 (iii)$\iff$(iv)：固定 $g\in G$。注意 $gA=X\setminus A$ 等价于对所有 $x\in X$ 均有 $x\in A\iff gx\notin A$（若 $gA=X\setminus A$，则 $g(X\setminus A)=X\setminus gA=A$，故 $x\in A\implies gx\notin A$ 且 $x\notin A\implies gx\in A$；反之若 $\forall x\ (x\in A\iff gx\notin A)$，由 $g_X$ 为双射立得 $gA=X\setminus A$）。
- 若 $g_X$ 有长为奇数 $\ell$ 的轮换 $(x,gx,\dots,g^{\ell-1}x)$，则 $gA=X\setminus A$ 推出沿轮换奇偶交替属于 $A$，从而 $x=g^\ell x\in A\iff x\notin A$，矛盾；故不存在这样的 $A$。
- 反之，若 $g_X$ 在 $X$ 上的每个轮换长度 $\ell=2d$ 均为偶数（含 $X=\varnothing$ 时空真），则在每个轮换 $(x_0,gx_0,\dots,g^{2d-1}x_0)$ 上令偶数步 $g^{2j}x_0\in A$、奇数步 $g^{2j+1}x_0\notin A$，即得满足 $gA=X\setminus A$ 的子集 $A\subseteq X$（$X=\varnothing$ 时取 $A=\varnothing$）。

由此得 (iii)$\iff$(iv)。

接着证 (i)$\iff$(ii) 及基数公式：
- (i)$\implies$(ii)：若 $\mathcal{F}\in\mathcal{S}(X)^G$ 且 $gA=X\setminus A$，则由 $G$-不变性得 $A\in\mathcal{F}\iff gA\in\mathcal{F}\iff X\setminus A\in\mathcal{F}$，与 $\mathcal{S}(X)$ 的互补公理矛盾。
- (ii)$\implies$(i) 与计数：设 $\bar{c}$ 无不动点。此时必有 $X\ne\varnothing$（否则 $\{\varnothing\}$ 是 $\bar{c}$ 的不动点），从而 $\mathcal{P}(X)/G$ 划分为若干两两无交的二元 $\bar{c}$-轨道 $\{\mathcal{O},\bar{c}(\mathcal{O})\}$，特别 $|\mathcal{P}(X)/G|$ 为正偶数（至少为 $2$）。因 $g\varnothing=\varnothing$ 且 $gX=X$，$\{\varnothing\}$ 与 $\{X\}$ 构成其中一对互补轨道 $\{\{\varnothing\},\{X\}\}$。
  现在，子族 $\mathcal{F}\subseteq\mathcal{P}(X)$ 属于 $\mathcal{S}(X)^G$ 当且仅当：(a) $\mathcal{F}$ 是若干 $G$-轨道的并（即 $G$-不变）；(b) $\{X\}\subseteq\mathcal{F}$ 且 $\{\varnothing\}\cap\mathcal{F}=\varnothing$；(c) 对其余的每一对互补轨道 $\{\mathcal{O},\bar{c}(\mathcal{O})\}$，$\mathcal{F}$ 恰包含其中之一。因为其余互补轨道共有 $\frac{1}{2}|\mathcal{P}(X)/G|-1$ 对且各对可独立二选一，故精确共有 $2^{\frac{1}{2}|\mathcal{P}(X)/G|-1}\ge1$ 个元素，尤其非空。

最后核验轨道数公式：有限群 $\overline{G}$ 作用于有限集 $\mathcal{P}(X)$，满足 Cauchy–Frobenius 引理的条件。对每个 $\sigma\in\overline{G}$，子集 $A\subseteq X$ 被 $\sigma$ 固定（$\sigma A=A$）当且仅当 $A$ 是 $\sigma$ 的若干轮换的并，故 $|\mathcal{P}(X)^\sigma|=2^{c(\sigma)}$。于是
$$|\mathcal{P}(X)/G|=|\mathcal{P}(X)/\overline{G}|=\frac{1}{|\overline{G}|}\sum_{\sigma\in\overline{G}}|\mathcal{P}(X)^\sigma|=\frac{1}{|\overline{G}|}\sum_{\sigma\in\overline{G}}2^{c(\sigma)}.\qquad\square$$

#### （3）$m\ge3$（含 $m=\infty$）
有限集 $X$ 上每个超滤都是主超滤（若 $\mathcal{U}\in\operatorname{Ult}(X)$ 非主，则对所有 $x\in X$ 有 $X\setminus\{x\}\in\mathcal{U}$，有限交得 $\varnothing=\bigcap_{x\in X}(X\setminus\{x\})\in\mathcal{U}$ 矛盾；$X=\varnothing$ 时两侧均为空集）。因此 $G$-等变映射 $\eta_{m,X}:X\to R_m(X)$ 是**双射**，限制到不动点集得双射
$$\eta_{m,X}|_{X^G}:X^G\xrightarrow{\ \sim\ }R_m(X)^G.$$
- **存在判准**：$R_m(X)^G\ne\varnothing\iff X^G\ne\varnothing$。
- **精确基数**：$|R_m(X)^G|=|X^G|$。

#### （4）有限 $G$ 集合上不动集合之间的限制映射 $q_{m,k}^G:R_m(X)^G\to R_k(X)^G$（$m\ge k\ge1$）
- **$m=k$**：恒等映射。
- **$m\ge k\ge3$**：双射；在双射 $\eta_{m,X}:X^G\xrightarrow{\sim}R_m(X)^G$ 与 $\eta_{k,X}:X^G\xrightarrow{\sim}R_k(X)^G$ 下对应 $\mathrm{id}_{X^G}$。
- **$m\ge3, k=2$**：$q_{m,2}^G$ 为单射；在 $R_m(X)^G\cong X^G$ 与 $R_2(X)^G\cong\mathcal{S}(X)^G$ 下将 $x\in X^G$ 映为主超滤 $\mathcal{U}_x=\{A\subseteq X: x\in A\}$。其像为 $\{\eta_{2,X}(x):x\in X^G\}$（基数 $|X^G|$）；对像中元素纤维为单点，对像外元素纤维为空。
  - 进一步可精确判定满射性：$q_{m,2}^G$ 为满射（双射）当且仅当 $|X|\le2$ **或** $R_2(X)^G=\varnothing$。
    *证明*：若 $R_2(X)^G=\varnothing$，则每个不动点给出 $1$-轮换（奇数长）故必有 $X^G=\varnothing$，为空双射。若 $|X|\le2$，则由 1.2 中 $q_{m,2}$ 为 $G$-等变双射知 $q_{m,2}^G$ 必为双射。反之，设 $|X|\ge3$ 且 $R_2(X)^G\ne\varnothing$，记 $t=|X/G|$ 为 $X$ 的 $G$-轨道数，显然 $|X^G|\le t$：
    - 若 $t=1$，则因 $|X|\ge3$ 有 $|X^G|=0<|R_2(X)^G|$；
    - 若 $t=2$，若 $|X^G|=0$ 则 $0<|R_2(X)^G|$；否则必为一单点轨道 $\{x_0\}$ 与一大小 $\ge2$ 的轨道 $O$，此时 $|X^G|=1$，而 $\mathcal{P}(O)/G$ 至少含 $3$ 个轨道（$\{\varnothing\},\{O\}$ 与单点集所在轨道），每个轨道配以含或不含 $x_0$ 得 $|\mathcal{P}(X)/G|=2|\mathcal{P}(O)/G|\ge6$，故 $|R_2(X)^G|\ge2^{6/2-1}=4>1=|X^G|$；
    - 若 $t\ge3$，由 $G$-不变子集构成 $2^t$ 个单点轨道知 $|\mathcal{P}(X)/G|\ge2^t$，从而 $|R_2(X)^G|\ge2^{2^{t-1}-1}>t\ge|X^G|$（对 $t\ge3$ 归纳显然）。故必非满射。
- **$m\ge2, k=1$**：若 $X=\varnothing$，为空双射 $\varnothing\to\varnothing$；若 $X\ne\varnothing$，$R_1(X)^G=\{*\}$ 为单点集，$q_{m,1}^G:R_m(X)^G\to\{*\}$ 的唯一纤维为整个 $R_m(X)^G$，像为 $\{*\}$（当 $R_m(X)^G\ne\varnothing$）或 $\varnothing$（当 $R_m(X)^G=\varnothing$）。

---

### 1.5 有限层不动记录延拓为完整不动记录的准确范围

对任意有限层 $k\in\mathbb{Z}_{\ge1}$ 与任意 $G$ 集合 $X$，元素 $s\in R_k(X)^G$ 可延拓为完整不动记录 $r\in R_\infty(X)^G$，即 $s\in\operatorname{im}(q_{\infty,k}^G)$。由上述分类立得完整刻画：

1. **$k\ge3$**：对**任意 $G$ 集合 $X$**（有限或无限、空或非空），$q_{\infty,k}:R_\infty(X)\to R_k(X)$ 是 $G$-等变双射，故 $q_{\infty,k}^G:R_\infty(X)^G\to R_k(X)^G$ 是**双射**。因此**全部** $k$ 层不动记录均可延拓为完整不动记录，且延拓**唯一**。
2. **$k=2$**：对**任意 $G$ 集合 $X$**，$q_{\infty,2}:R_\infty(X)\to R_2(X)$ 是 $G$-等变单射。因此，若 $s\in R_2(X)^G$ 存在无群作用的延拓 $r\in R_\infty(X)$（即 $q_{\infty,2}(r)=s$），则对一切 $g\in G$ 有
   $$q_{\infty,2}(g\cdot r)=g\cdot q_{\infty,2}(r)=g\cdot s=s=q_{\infty,2}(r),$$
   由单射性自动推得 $g\cdot r=r$，即 $r\in R_\infty(X)^G$。从而 $s\in R_2(X)^G$ 可延拓为完整不动记录**当且仅当 $\mathcal{F}_s=\{A\subseteq X: s_2(\mathbf{1}_A)=1\}$ 是 $X$ 上的超滤（等价地，$\mathcal{F}_s$ 对二元交封闭）**，且此时延拓**唯一**。
   - **有限 $G$ 集合情形**：可延拓的 $2$ 层不动记录恰好是全体主不动记录 $\{\eta_{2,X}(x):x\in X^G\}$（共 $|X^G|$ 个），每个延拓唯一；其余非超滤型 $2$ 层不动记录（例如 $C_3$ 轮换作用在 $[3]$ 上的“多数决”与“少数决”，此时 $R_2([3])^{C_3}$ 有 $2$ 个元素而 $R_\infty([3])^{C_3}=\varnothing$）均不可延拓。
3. **$k=1$**：若 $X=\varnothing$，$R_1(\varnothing)^G=\varnothing$（空真全延拓）。若 $X\ne\varnothing$，$R_1(X)^G=\{*\}$ 的唯一元素可延拓为完整不动记录**当且仅当 $R_\infty(X)^G\ne\varnothing$**，此时延拓的全体恰好是 $R_\infty(X)^G$（不再一定唯一）。
   - **有限 $G$ 集合情形**：（$X\ne\varnothing$ 时）可延拓当且仅当 $X^G\ne\varnothing$，延拓个数恰好为 $|X^G|$。
   - **一般 $G$ 集合情形**：由下文定理 2.3，可延拓当且仅当对每个有限子集 $F\subseteq G$ 均有 $X^F\ne\varnothing$。

---

## 目标 2：完整不动记录的空间

### 2.1 $R_\infty(X)$ 的拓扑识别与紧 Hausdorff 性

在 $\operatorname{Ult}(X)$ 上取 Stone 拓扑，它以闭开集族
$$U_A:=\{\mathcal{U}\in\operatorname{Ult}(X): A\in\mathcal{U}\}\qquad(A\subseteq X)$$
为拓扑基（因 $U_A\cap U_B=U_{A\cap B}$、$U_X=\operatorname{Ult}(X)$、$\operatorname{Ult}(X)\setminus U_A=U_{X\setminus A}$；当 $X=\varnothing$ 时为空空间）。

**引理 2.1.**
1. 分类双射 $\Phi_{\infty,X}:R_\infty(X)\xrightarrow{\sim}\operatorname{Ult}(X)$ 是**同胚**。
2. $R_\infty(X)$ 与 $R_\infty(X)^G$ 均为紧 Hausdorff 空间；对任意 $h:X\to Y$，$R_\infty(h):R_\infty(X)\to R_\infty(Y)$ 连续。

**证明.**
1. 当 $X=\varnothing$ 时两侧为空空间，平凡成立。设 $X\ne\varnothing$。记观察映射 $\mathrm{ev}_{n,f}:R_\infty(X)\to[n],\ r\mapsto r_n(f)$。
   - 对任意 $n\ge1$、$f:X\to[n]$ 与 $j\in[n]$，由命题 1.2 有
     $$r\in\mathrm{ev}_{n,f}^{-1}(\{j\})\iff r_n(f)=j\iff f^{-1}(j)\in\Phi_{\infty,X}(r)\iff\Phi_{\infty,X}(r)\in U_{f^{-1}(j)}$$
     （而 $n=0$ 时 $[0]=\varnothing$，唯一开集为 $\varnothing$，原像为 $\varnothing$）。因此每个观察映射 $\mathrm{ev}_{n,f}$ 在 $\Phi_{\infty,X}$ 拉回的 Stone 拓扑下连续，即 $R_\infty(X)$ 的定义拓扑弱于（包含于）Stone 拉回拓扑。
   - 反过来，对任意 $A\subseteq X$，有
     $$\Phi_{\infty,X}^{-1}(U_A)=\{r\in R_\infty(X): r_2(\mathbf{1}_A)=1\}=\mathrm{ev}_{2,\mathbf{1}_A}^{-1}(\{1\}),$$
     故每个 Stone 基开集在 $\Phi_{\infty,X}$ 下的原像均是 $R_\infty(X)$ 中的开集。从而两拓扑完全一致，$\Phi_{\infty,X}$ 是同胚。
2. 考察乘积空间 $P:=\prod_{n=0}^\infty\prod_{f\in\operatorname{Map}(X,[n])}[n]$（每个 $[n]$ 取有限离散拓扑，因而紧 Hausdorff；特别 $X=\varnothing$ 时 $n=0$ 因子为空，故 $P=\varnothing$ 仍紧 Hausdorff）。由 ZFC 中的 Tychonoff 定理，$P$ 为紧 Hausdorff 空间。$R_\infty(X)$ 的拓扑正是其作为 $P$ 子空间诱导的子空间拓扑。对每组固定 $(n,k,f,a)$，两个映射 $r\mapsto a(r_n(f))$ 与 $r\mapsto r_k(a\circ f)$ 均从 $P$ 连续映入 Hausdorff 空间 $[k]$，故它们的等化子在 $P$ 中闭。$R_\infty(X)$ 是所有这些闭集的交，从而是 $P$ 的闭子空间，因而紧 Hausdorff。
   对任意 $h:X\to Y$，因 $\mathrm{ev}_{n,f}\circ R_\infty(h)=\mathrm{ev}_{n,f\circ h}$ 均连续，由初拓扑泛性质知 $R_\infty(h)$ 连续。特别对每个 $g\in G$，$r\mapsto g\cdot r=R_\infty(g_X)r$ 连续，从而等化子 $\{r\in R_\infty(X): g\cdot r=r\}$ 在 Hausdorff 空间 $R_\infty(X)$ 中闭，故 $R_\infty(X)^G=\bigcap_{g\in G}\{r:g\cdot r=r\}$ 是闭子空间，亦紧 Hausdorff。$\square$

---

### 2.2 单个双射的不动超滤引理与 $R_\infty(X)^G$ 的内在分类

**引理 2.2（双射不动超滤引理）.** 设 $g:X\to X$ 为双射，$\mathcal{U}\in\operatorname{Ult}(X)$。则
$$g_*(\mathcal{U})=\mathcal{U}\iff X^g\in\mathcal{U}.$$

**证明.**
- （$\Leftarrow$）若 $X^g\in\mathcal{U}$，对任意 $A\in\mathcal{U}$ 有 $A\cap X^g\in\mathcal{U}$。因 $g$ 逐点固定 $X^g$，故 $A\cap X^g=g^{-1}(A\cap X^g)\subseteq g^{-1}(A)$，由上闭性得 $g^{-1}(A)\in\mathcal{U}$，即 $A\in g_*(\mathcal{U})$。由此 $\mathcal{U}\subseteq g_*(\mathcal{U})$；因两者均为超滤（或因 $X^{g^{-1}}=X^g\in\mathcal{U}$ 对 $g^{-1}$ 同理），必有 $g_*(\mathcal{U})=\mathcal{U}$。
- （$\Rightarrow$）设 $g_*(\mathcal{U})=\mathcal{U}$。令 $Y:=X\setminus X^g$，则 $g|_Y$ 是 $Y$ 上无不动点的双射。将 $Y$ 分解为循环群 $\langle g\rangle$ 的轨道。利用选择公理，在每个轨道 $O\subseteq Y$ 中选定一基点 $x_O\in O$，并给 $O$ 中元素赋予 $\{0,1,2\}$ 中的颜色：
  - 若 $O$ 为无限轨道（$k\mapsto g^k(x_O)$ 是 $\mathbb{Z}\xrightarrow{\sim}O$），令 $g^k(x_O)$ 染色为 $k\bmod 2\in\{0,1\}$；
  - 若 $O$ 为偶数长 $\ell\ge2$ 的有限轮换，令 $g^k(x_O)$（$0\le k<\ell$）染色为 $k\bmod 2\in\{0,1\}$；
  - 若 $O$ 为奇数长 $\ell\ge3$ 的有限轮换，令 $g^k(x_O)$（$0\le k\le\ell-2$）染色为 $k\bmod 2\in\{0,1\}$，而令 $g^{\ell-1}(x_O)$ 染色为 $2$。

  记染 $i$ 色的点集为 $A_i$（$i\in\{0,1,2\}$）。核验可知对任意 $y\in Y$，$y$ 与 $gy$ 不同色（特别对奇数轮换，$g^{\ell-2}(x_O)$ 染 $1$ 色，$g^{\ell-1}(x_O)$ 染 $2$ 色，$g^\ell(x_O)=x_O$ 染 $0$ 色，相邻均异色），从而 $g(A_i)\cap A_i=\varnothing$（$i=0,1,2$）。
  于是得到有限无交划分 $X=X^g\sqcup A_0\sqcup A_1\sqcup A_2$。由于 $\mathcal{U}$ 是超滤，其中必有一块属于 $\mathcal{U}$。若某个 $A_i\in\mathcal{U}$，因 $g^{-1}(g(A_i))=A_i\in\mathcal{U}$ 有 $g(A_i)\in g_*(\mathcal{U})=\mathcal{U}$，故 $\varnothing=A_i\cap g(A_i)\in\mathcal{U}$，矛盾。因此必有 $X^g\in\mathcal{U}$。$\square$

结合引理 2.1 与引理 2.2，立刻获得 $R_\infty(X)^G$ 与拓扑相容的内在分类：

**定理 2.3（内在分类与非空判准）.** 设 $X$ 为任意 $G$ 集合（含 $X=\varnothing$）。
1. **内在拓扑分类**：同胚 $\Phi_{\infty,X}$ 限制为同胚
   $$R_\infty(X)^G\xrightarrow{\ \sim\ }\operatorname{Ult}_G(X):=\{\mathcal{U}\in\operatorname{Ult}(X): \forall g\in G,\ X^g\in\mathcal{U}\}=\bigcap_{g\in G}U_{X^g},$$
   其中 $\operatorname{Ult}_G(X)$ 赋予 Stone 子空间拓扑，它以闭开集族 $V_A:=\{\mathcal{U}\in\operatorname{Ult}_G(X):A\in\mathcal{U}\}$（$A\subseteq X$）为拓扑基。
   等价地，记 $X$ 上由固定点集族 $\{X^g:g\in G\}$ 生成的布尔理想为
   $$\mathcal{I}_G(X):=\{A\subseteq X: \exists\text{ 有限 }F\subseteq G,\ A\cap X^F=\varnothing\},$$
   记商布尔代数为 $B_G(X):=\mathcal{P}(X)/\mathcal{I}_G(X)\cong\varinjlim_{F\Subset G}\mathcal{P}(X^F)$（沿限制映射 $A\mapsto A\cap X^{F'}$）。则 $\operatorname{Ult}_G(X)$ 典范同胚于：
   - 商布尔代数 $B_G(X)$ 的 Stone 空间 $\operatorname{Spec}(B_G(X))$（即全体与 $\mathcal{I}_G(X)$ 不交的超滤，亦即布尔同态 $B_G(X)\to[2]$ 的空间配逐点拓扑）；
   - 以及逆向极限 $\varprojlim_{F\Subset G}\operatorname{Ult}(X^F)$（沿有限子集包含 $F\subseteq F'$ 诱导的闭嵌入 $\operatorname{Ult}(X^{F'})\hookrightarrow\operatorname{Ult}(X^F)$）。
   （当 $X=\varnothing$ 时，取 $F=\varnothing$ 有 $X^\varnothing=\varnothing$，故 $\mathcal{I}_G(\varnothing)=\mathcal{P}(\varnothing)$，$B_G(\varnothing)$ 为平凡布尔代数，上述所有空间均为空集。）
2. **非空充要条件**：
   $$R_\infty(X)^G\ne\varnothing\iff \forall\text{ 有限子集 }F\subseteq G,\quad X^F=\bigcap_{g\in F}X^g\ne\varnothing\iff \forall\text{ 有限生成子群 }H\le G,\quad X^H\ne\varnothing.$$
   （注意：取 $F=\varnothing$ 或 $H=\{e\}$ 自动要求 $X\ne\varnothing$。）

**证明.**
1. 由引理 2.2，$\mathcal{U}\in\operatorname{Ult}(X)^G\iff \forall g\in G,\ g_*(\mathcal{U})=\mathcal{U}\iff \forall g\in G,\ X^g\in\mathcal{U}$，故 $\Phi_{\infty,X}(R_\infty(X)^G)=\operatorname{Ult}_G(X)=\bigcap_{g\in G}U_{X^g}$，由引理 2.1 为同胚。
   对 Stone 空间刻画：超滤 $\mathcal{U}\in\operatorname{Ult}(X)$ 对应布尔同态 $\chi_{\mathcal{U}}:\mathcal{P}(X)\to[2]$（$\chi_{\mathcal{U}}(A)=1\iff A\in\mathcal{U}$）。$\chi_{\mathcal{U}}$ 分解过商代数 $B_G(X)=\mathcal{P}(X)/\mathcal{I}_G(X)$ 当且仅当 $\mathcal{I}_G(X)\subseteq\ker\chi_{\mathcal{U}}$，即对所有有限 $F\subseteq G$ 与 $A\subseteq X$，$A\cap X^F=\varnothing\implies A\notin\mathcal{U}$；取 $A=X\setminus X^F$ 即等价于 $\forall F\Subset G,\ X^F\in\mathcal{U}$，即 $\forall g\in G,\ X^g\in\mathcal{U}$。在 $\operatorname{Spec}(B_G(X))$ 上基本闭开集为 $\{\varphi:\varphi([A])=1\}$，正对应 $V_A$，故为同胚。
   对逆向极限刻画：对每个 $S\subseteq X$，包含 $\iota_S:S\hookrightarrow X$ 诱导连续映射 $(\iota_S)_*:\operatorname{Ult}(S)\to\operatorname{Ult}(X),\ \mathcal{V}\mapsto\{B\subseteq X:B\cap S\in\mathcal{V}\}$。它显然是到 $U_S$ 的双射（逆为 $\mathcal{U}\mapsto\{A\cap S:A\in\mathcal{U}\}$），且 $(\iota_S)_*^{-1}(U_B)=U_{B\cap S}$，故是同胚 $\operatorname{Ult}(S)\xrightarrow{\sim}U_S$。于是闭子空间族 $\{U_{X^F}:F\Subset G\}$ 沿包含的逆向极限即交集 $\bigcap_{F\Subset G}U_{X^F}=\operatorname{Ult}_G(X)$（配子空间拓扑）。
2. 先注意对任何有限 $F\subseteq G$，因稳定子是子群，有 $X^F=X^{\langle F\rangle}$，而任意有限生成子群形如 $\langle F\rangle$（含 $\{e\}=\langle\varnothing\rangle$），故后两个条件等价。
   - （$\Rightarrow$）若 $\mathcal{U}\in\operatorname{Ult}_G(X)$，则 $X\in\mathcal{U}$ 且对所有 $g\in G$ 有 $X^g\in\mathcal{U}$。由滤子对有限交封闭，对任意有限 $F\subseteq G$ 均有 $X^F\in\mathcal{U}$；因 $\varnothing\notin\mathcal{U}$，故 $X^F\ne\varnothing$。
   - （$\Leftarrow$）若对一切有限 $F\subseteq G$ 均有 $X^F\ne\varnothing$，则特别 $X=X^\varnothing\ne\varnothing$，且集合族 $\{X^g:g\in G\}$ 在 $\mathcal{P}(X)$ 中具有有限交性质，故它生成的滤子 $\mathcal{F}_G(X)=\{A\subseteq X:\exists F\Subset G,\ X^F\subseteq A\}$ 是 $X$ 上的真滤子（$\varnothing\notin\mathcal{F}_G(X)$）。在 ZFC 下由超滤引理（Zorn 引理应用于包含 $\mathcal{F}_G(X)$ 的全体真滤子按包含序构成的偏序集：非空，且任何链的并仍为真滤子），存在超滤 $\mathcal{U}\in\operatorname{Ult}(X)$ 满足 $\mathcal{F}_G(X)\subseteq\mathcal{U}$。于是 $\mathcal{U}\in\operatorname{Ult}_G(X)$，从而 $R_\infty(X)^G\ne\varnothing$。$\square$

---

### 2.3 $\eta_{\infty,X}(X^G)$ 的闭包、等式判准与群的完全分类

**引理 2.4.** 对任意集合 $X$ 与任意子集 $A\subseteq X$，在同胚 $\Phi_{\infty,X}:R_\infty(X)\xrightarrow{\sim}\operatorname{Ult}(X)$ 下，有
$$\Phi_{\infty,X}\bigl(\overline{\eta_{\infty,X}(A)}\bigr)=U_A=\{\mathcal{U}\in\operatorname{Ult}(X): A\in\mathcal{U}\}.$$

**证明.** 若 $X=\varnothing$，则 $A=\varnothing$，两端均为 $\varnothing$。设 $X\ne\varnothing$。对 $x\in X$，$\Phi_{\infty,X}(\eta_{\infty,X}(x))=\mathcal{U}_x=\{S\subseteq X:x\in S\}$，故 $\mathcal{U}_x\in U_A\iff x\in A$。因 $U_A$ 在 $\operatorname{Ult}(X)$ 中闭（补集为 $U_{X\setminus A}$），故 $\overline{\Phi_{\infty,X}(\eta_{\infty,X}(A))}\subseteq U_A$。反之，任取 $\mathcal{U}\in U_A$ 及 $\mathcal{U}$ 的任意基本开邻域 $U_B$（即 $B\in\mathcal{U}$）。因 $A,B\in\mathcal{U}$，有 $A\cap B\in\mathcal{U}$，从而 $A\cap B\ne\varnothing$。取 $x\in A\cap B$，则 $\mathcal{U}_x\in\Phi_{\infty,X}(\eta_{\infty,X}(A))\cap U_B$，故 $\mathcal{U}\in\overline{\Phi_{\infty,X}(\eta_{\infty,X}(A))}$。$\square$

取 $A=X^G$，立得：
- **闭包确定**：
  $$\overline{\eta_{\infty,X}(X^G)}=\Phi_{\infty,X}^{-1}(U_{X^G})=\begin{cases}\varnothing,&X=\varnothing,\\\{r\in R_\infty(X): r_2(\mathbf{1}_{X^G})=1\},&X\ne\varnothing,\end{cases}$$
  它也恰好等于包含映射 $\iota:X^G\hookrightarrow X$ 诱导的闭嵌入 $R_\infty(\iota):R_\infty(X^G)\hookrightarrow R_\infty(X)$ 的像（同胚于 $\operatorname{Ult}(X^G)$）。

**定理 2.5（闭包等于全不动空间的充要条件）.** 对任意 $G$ 集合 $X$（含 $X=\varnothing$），
$$\overline{\eta_{\infty,X}(X^G)}=R_\infty(X)^G\iff \exists\text{ 有限子集 }F\subseteq G\text{ 使得 }X^F=X^G\iff \exists\text{ 有限生成子群 }H\le G\text{ 使得 }X^H=X^G.$$

**证明.** 后两者的等价性同前（$X^F=X^{\langle F\rangle}$）。在同胚 $\Phi_{\infty,X}$ 下，总有 $U_{X^G}\subseteq\bigcap_{g\in G}U_{X^g}=\operatorname{Ult}_G(X)$，需判定何时 $U_{X^G}=\operatorname{Ult}_G(X)$。
- 若 $X=\varnothing$：两侧均为 $\varnothing$，且取 $F=\varnothing$ 有 $X^\varnothing=\varnothing=X^G$，等价成立。
- 设 $X\ne\varnothing$。等式 $U_{X^G}=\bigcap_{g\in G}U_{X^g}$ 取补后等价于
  $$U_{X\setminus X^G}=\bigcup_{g\in G}U_{X\setminus X^g}.$$
  - （$\Leftarrow$）若存在有限 $F\subseteq G$ 使 $X^F=X^G$，则 $X\setminus X^G=\bigcup_{g\in F}(X\setminus X^g)$。对任意 $\mathcal{U}\in\operatorname{Ult}_G(X)$，有 $\forall g\in F,\ X^g\in\mathcal{U}$，有限交得 $X^G=X^F\in\mathcal{U}$，故 $\mathcal{U}\in U_{X^G}$。从而 $\operatorname{Ult}_G(X)=U_{X^G}$。
  - （$\Rightarrow$）若 $U_{X\setminus X^G}=\bigcup_{g\in G}U_{X\setminus X^g}$，注意 $U_{X\setminus X^G}$ 是紧空间 $\operatorname{Ult}(X)$ 的闭子集，因而紧致；右端是它的一个开覆盖。故存在有限子集 $F\subseteq G$ 使得
    $$U_{X\setminus X^G}=\bigcup_{g\in F}U_{X\setminus X^g}=U_{\bigcup_{g\in F}(X\setminus X^g)}=U_{X\setminus X^F}$$
    （当 $F=\varnothing$ 时右端为 $\varnothing=U_\varnothing=U_{X\setminus X^\varnothing}$）。因为对任意 $A,B\subseteq X$ 有 $U_A=U_B\implies A=B$（考察全体主超滤 $\mathcal{U}_x$），即得 $X\setminus X^G=X\setminus X^F$，从而 $X^F=X^G$。$\square$

**定理 2.6（满足等式的群的完全分类）.** 群 $G$ 对其每个 $G$ 集合 $X$ 均满足 $\overline{\eta_{\infty,X}(X^G)}=R_\infty(X)^G$，**当且仅当 $G$ 是有限生成群**。

**证明.**
- （$\Leftarrow$）若 $G=\langle F\rangle$（$F\subseteq G$ 有限，允许 $G=\{e\}=\langle\varnothing\rangle$），则对任意 $G$ 集合 $X$ 均有 $X^F=X^{\langle F\rangle}=X^G$。由定理 2.5 立得 $\overline{\eta_{\infty,X}(X^G)}=R_\infty(X)^G$。
- （$\Rightarrow$）逆否证明：设 $G$ **不是**有限生成群。令 $\mathcal{H}:=\{H\le G: H\text{ 有限生成}\}\subseteq\mathcal{P}(G)$（是合法集合），并构造 $G$ 集合
  $$X:=\bigsqcup_{H\in\mathcal{H}}G/H=\{(H,aH):H\in\mathcal{H},\ aH\in G/H\},$$
  其上 $G$ 按左平移 $g\cdot(H,aH):=(H,gaH)$ 作用。
  - **计算 $X^G$**：$(H,aH)\in X^G\iff \forall g\in G,\ gaH=aH\iff a^{-1}Ga\subseteq H\iff G=H$。因 $G$ 非有限生成，故 $G\notin\mathcal{H}$，从而 $X^G=\varnothing$。
  - **检验有限子集**：对任意有限子集 $F\subseteq G$，令 $H_0:=\langle F\rangle\in\mathcal{H}$。点 $(H_0,eH_0)\in X$ 被每个 $g\in F\subseteq H_0$ 固定，故 $(H_0,eH_0)\in X^F$，即 $X^F\ne\varnothing=X^G$。

  由定理 2.5 知 $\overline{\eta_{\infty,X}(X^G)}\ne R_\infty(X)^G$（事实上 $\overline{\eta_{\infty,X}(X^G)}=\varnothing$ 而由定理 2.3 有 $R_\infty(X)^G\ne\varnothing$）。$\square$

---

### 2.4 群与底集均可数的具体例子及全部不动记录的完整描述

**构造**：取底集 $X=\mathbb{N}=\{0,1,2,\dots\}$，取群为 $\mathbb{N}$ 上的**有限支集置换群**
$$G:=\operatorname{Sym}_{\mathrm{fin}}(\mathbb{N})=\bigl\{\sigma\in\operatorname{Sym}(\mathbb{N}): \operatorname{supp}(\sigma):=\{n\in\mathbb{N}:\sigma(n)\ne n\}\text{ 有限}\bigr\},$$
作用为自然左作用 $\sigma\cdot n:=\sigma(n)$。

**核验**：
1. **$G$ 与 $X$ 均可数**：$X=\mathbb{N}$ 可数无限。显然有限支集置换对复合与求逆封闭（$\operatorname{supp}(\sigma\tau)\subseteq\operatorname{supp}(\sigma)\cup\operatorname{supp}(\tau)$，$\operatorname{supp}(\sigma^{-1})=\operatorname{supp}(\sigma)$），故 $G$ 是 $\operatorname{Sym}(\mathbb{N})$ 的子群。将 $\operatorname{Sym}([k])$ 视为固定 $\{k,k+1,\dots\}$ 的子群，有 $G=\bigcup_{k=0}^\infty\operatorname{Sym}([k])$，这是有限集的可数并，故 $G$ 可数（无限）。
2. **$X^G=\varnothing$**：对任意 $n\in\mathbb{N}$，对换 $\tau_n:=(n\ n+1)\in G$ 满足 $\tau_n(n)=n+1\ne n$，故没有任何元素被 $G$ 全体固定，即 $X^G=\varnothing$。
3. **全部不动记录的完整描述与非空性**：
   - 对任意 $g\in G$，其不动点集 $\mathbb{N}^g=\mathbb{N}\setminus\operatorname{supp}(g)$ 是 $\mathbb{N}$ 的**余有限子集**。
   - 反过来，对任意有限子集 $S\subseteq\mathbb{N}$，令 $F:=\{\tau_n:n\in S\}$（有限子集），则 $\mathbb{N}^F\subseteq\mathbb{N}\setminus S$（因 $\tau_n(n)\ne n$）。

   因此，由定理 2.3，超滤 $\mathcal{U}\in\operatorname{Ult}(\mathbb{N})$ 属于 $\operatorname{Ult}_G(\mathbb{N})$ 当且仅当 $\mathcal{U}$ 包含 $\mathbb{N}$ 的一切余有限子集，而这等价于 $\mathcal{U}$ 不含任何单点集 $\{k\}$，即 **$\mathcal{U}$ 是 $\mathbb{N}$ 上的非主（自由）超滤**。
   由此给出 $R_\infty(\mathbb{N})^G$ 的完整刻画：
   - **拓扑分类**：$\Phi_{\infty,\mathbb{N}}$ 将 $R_\infty(\mathbb{N})^G$ 同胚地映为全体非主超滤组成的空间
     $$\operatorname{Ult}(\mathbb{N})\setminus\{\mathcal{U}_k:k\in\mathbb{N}\}=\beta\mathbb{N}\setminus\mathbb{N}\cong\operatorname{Spec}\bigl(\mathcal{P}(\mathbb{N})/\mathrm{Fin}\bigr)$$
     （其中 $\mathrm{Fin}$ 为 $\mathbb{N}$ 的有限子集理想）。
   - **显式记录族**：$r=(r_n)_{n\ge0}\in R_\infty(\mathbb{N})^G$ 当且仅当存在（唯一）非主超滤 $\mathcal{U}$ 使得 $r_0=\emptyset$，且对一切 $n\ge1$ 与 $f:\mathbb{N}\to[n]$，$r_n(f)$ 是使 $f^{-1}(j)\in\mathcal{U}$ 的唯一 $j\in[n]$。
   - **等价的内在记录刻画**：$R_\infty(\mathbb{N})^G=R_\infty(\mathbb{N})\setminus\eta_{\infty,\mathbb{N}}(\mathbb{N})=\{r\in R_\infty(\mathbb{N}):\forall k\in\mathbb{N},\ r_2(\mathbf{1}_{\{k\}})=0\}$（也等价于：$r\in R_\infty(\mathbb{N})$ 且每当 $f,f':\mathbb{N}\to[n]$ 仅在有限个点取值不同时均有 $r_n(f)=r_n(f')$）。
   - **非空性**：$\mathbb{N}$ 的余有限子集构成 Fréchet 真滤子（等价地，对一切有限 $F\subseteq G$，$\mathbb{N}^F$ 余有限因而非空），在 ZFC 下由超滤引理存在至少一个非主超滤，故 $R_\infty(\mathbb{N})^G\ne\varnothing$。

---

## 目标 3：乘积比较

设 $(X_i)_{i\in I}$ 为任意集合指标族的 $G$ 集合，记 $X:=\prod_{i\in I}X_i$（取对角作用 $g\cdot(x_i)_{i\in I}=(gx_i)_{i\in I}$；$I=\varnothing$ 时约定 $X=\{*\}$ 取平凡作用），对 $i\in I$ 记投影为 $p_i:X\to X_i$。

### 3.1 $\Pi_{(X_i)}$ 的良定义与连续性

1. **良定义**：
   - 若 $I=\varnothing$：$X=\{*\}$，故 $R_\infty(X)^G=R_\infty(\{*\})$ 为单点集，而空指标族乘积 $\prod_{i\in\varnothing}R_\infty(X_i)^G=\{*\}$ 亦为单点集，$\Pi_\varnothing$ 为单点集间的唯一映射，良定义。
   - 若 $I\ne\varnothing$：对每个 $i\in I$，投影 $p_i:X\to X_i$ 满足 $p_i\circ g_X=g_{X_i}\circ p_i$（$G$-等变）。由 $R_\infty$ 的函子性（目标 1.3），对任意 $r\in R_\infty(X)^G$ 与 $g\in G$ 有
     $$g\cdot R_\infty(p_i)r=R_\infty(g_{X_i}\circ p_i)r=R_\infty(p_i\circ g_X)r=R_\infty(p_i)(g\cdot r)=R_\infty(p_i)r,$$
     即 $R_\infty(p_i)r\in R_\infty(X_i)^G$。故 $\Pi_{(X_i)}(r)=(R_\infty(p_i)r)_{i\in I}\in\prod_{i\in I}R_\infty(X_i)^G$ 良定义。（特别当某个 $X_{i_0}=\varnothing$ 时，$X=\varnothing$，$R_\infty(X)^G=\varnothing$ 且 $R_\infty(X_{i_0})^G=\varnothing$，从而 $\Pi_{(X_i)}$ 是空映射 $\varnothing\to\varnothing$。）

2. **连续性**：
   - 当 $I=\varnothing$ 时，单点空间间的唯一映射显然连续。
   - 当 $I\ne\varnothing$ 时，余域 $\prod_{i\in I}R_\infty(X_i)^G$ 取乘积拓扑，每个因子 $R_\infty(X_i)^G$ 取自 $R_\infty(X_i)$ 的子空间拓扑。由乘积拓扑的泛性质，$\Pi_{(X_i)}$ 连续当且仅当每个分量映射 $r\mapsto R_\infty(p_i)r:R_\infty(X)^G\to R_\infty(X_i)^G$ 连续；由子空间拓扑泛性质，这等价于 $R_\infty(p_i)|_{R_\infty(X)^G}:R_\infty(X)^G\to R_\infty(X_i)$ 连续；又由 $R_\infty(X_i)$ 的初拓扑定义，这等价于对一切 $n\ge0$ 和 $f:X_i\to[n]$，复合映射
     $$r\longmapsto (R_\infty(p_i)r)_n(f)=r_n(f\circ p_i)$$
     在 $R_\infty(X)^G$ 上连续。而它正是 $R_\infty(X)$ 上的连续观察 $\mathrm{ev}_{n,f\circ p_i}$ 在子空间 $R_\infty(X)^G$ 上的限制，故必然连续。因此 $\Pi_{(X_i)}$ 连续。

---

### 3.2 $\Pi_{(X_i)}$ 是否总为满射

**结论：是。对任意群 $G$、任意集合指标族 $I$ 及任意 $G$ 集合族 $(X_i)_{i\in I}$，$\Pi_{(X_i)}$ 总为满射。**

**证明.**
- 若 $I=\varnothing$：$\Pi_\varnothing$ 为单点集间的唯一映射，满射。
- 若 $I\ne\varnothing$ 且 $\prod_{i\in I}R_\infty(X_i)^G=\varnothing$（含存在 $X_{i_0}=\varnothing$ 的情形）：余域为空集，故 $\Pi_{(X_i)}:\varnothing\to\varnothing$ 空真满射。
- 现设 $I\ne\varnothing$ 且 $\prod_{i\in I}R_\infty(X_i)^G\ne\varnothing$。在同胚 $\Phi_{\infty,-}$ 下，任取一族不动超滤 $(\mathcal{U}_i)_{i\in I}\in\prod_{i\in I}\operatorname{Ult}_G(X_i)$。特别地，每个 $X_i\ne\varnothing$，由选择公理知 $X=\prod_{i\in I}X_i\ne\varnothing$。

  先注意到对角作用下每个 $g\in G$ 的不动点集满足
  $$X^g=\left(\prod_{i\in I}X_i\right)^g=\prod_{i\in I}X_i^g.$$
  在 $\mathcal{P}(X)$ 中考虑集合族
  $$\mathcal{C}:=\bigl\{p_i^{-1}(A): i\in I,\ A\in\mathcal{U}_i\bigr\}\ \cup\ \bigl\{X^g: g\in G\bigr\}.$$
  **核验 $\mathcal{C}$ 具有有限交性质**：任取 $\mathcal{C}$ 中有限多个元素 $p_{i_1}^{-1}(A_1),\dots,p_{i_k}^{-1}(A_k)$（其中 $A_s\in\mathcal{U}_{i_s}$）以及 $X^{g_1},\dots,X^{g_m}$（$k,m\ge0$）。记有限集 $F:=\{g_1,\dots,g_m\}\subseteq G$，并对每个 $i\in I$ 令
  $$B_i:=\bigcap_{\substack{1\le s\le k\\ i_s=i}}A_s\quad(\text{无指标满足时取 }B_i=X_i).$$
  则这有限多个集合的交为
  $$\left(\bigcap_{s=1}^k p_{i_s}^{-1}(A_s)\right)\cap\left(\bigcap_{g\in F}X^g\right)=\left(\prod_{i\in I}B_i\right)\cap\left(\prod_{i\in I}X_i^F\right)=\prod_{i\in I}\bigl(B_i\cap X_i^F\bigr).$$
  对**每个** $i\in I$：
  - $B_i$ 是 $\mathcal{U}_i$ 中有限个元素的交（或为 $X_i\in\mathcal{U}_i$），故 $B_i\in\mathcal{U}_i$；
  - 由 $\mathcal{U}_i\in\operatorname{Ult}_G(X_i)$（定理 2.3）知对一切 $g\in F$ 有 $X_i^g\in\mathcal{U}_i$，有限交得 $X_i^F\in\mathcal{U}_i$（$F=\varnothing$ 时 $X_i^\varnothing=X_i\in\mathcal{U}_i$）；
  - 因此 $B_i\cap X_i^F\in\mathcal{U}_i$，从而 $B_i\cap X_i^F\ne\varnothing$。

  由选择公理（ZFC），非空集合族的笛卡尔积 $\prod_{i\in I}(B_i\cap X_i^F)$ 非空。故 $\mathcal{C}$ 具有有限交性质，它生成的滤子是 $X$ 上的真滤子。

  由 ZFC 中的超滤引理（Zorn 引理），存在超滤 $\mathcal{W}\in\operatorname{Ult}(X)$ 满足 $\mathcal{C}\subseteq\mathcal{W}$。核验：
  - 对一切 $g\in G$，$X^g\in\mathcal{C}\subseteq\mathcal{W}$，由定理 2.3 得 $\mathcal{W}\in\operatorname{Ult}_G(X)$；
  - 对一切 $i\in I$ 与 $A\in\mathcal{U}_i$，$p_i^{-1}(A)\in\mathcal{C}\subseteq\mathcal{W}$，故 $A\in(p_i)_*(\mathcal{W})$；因 $\mathcal{U}_i$ 与 $(p_i)_*(\mathcal{W})$ 同为 $X_i$ 上超滤，必有 $(p_i)_*(\mathcal{W})=\mathcal{U}_i$。

  令 $r=\Phi_{\infty,X}^{-1}(\mathcal{W})\in R_\infty(X)^G$，则 $\Pi_{(X_i)}(r)=(\Phi_{\infty,X_i}^{-1}(\mathcal{U}_i))_{i\in I}$。故 $\Pi_{(X_i)}$ 总为满射。$\square$

---

### 3.3 平凡群时两集合 $X,Y$ 的比较映射为单射的充要条件

先引入超滤的 Fubini 张量积供本节及 3.4 共同使用。

**引理 3.1（超滤张量积）.** 设 $\mathcal{U}\in\operatorname{Ult}(X)$、$\mathcal{V}\in\operatorname{Ult}(Y)$。对 $S\subseteq X\times Y$ 与 $x\in X$，记截面 $S_x:=\{y\in Y:(x,y)\in S\}$。定义
$$\mathcal{U}\otimes\mathcal{V}:=\bigl\{S\subseteq X\times Y:\ \{x\in X: S_x\in\mathcal{V}\}\in\mathcal{U}\bigr\}.$$
则 $\mathcal{U}\otimes\mathcal{V}\in\operatorname{Ult}(X\times Y)$，且 $(p_1)_*(\mathcal{U}\otimes\mathcal{V})=\mathcal{U}$、$(p_2)_*(\mathcal{U}\otimes\mathcal{V})=\mathcal{V}$。

**证明.** 依次核验：
- $\varnothing_x=\varnothing\notin\mathcal{V}$，故 $\{x:\varnothing_x\in\mathcal{V}\}=\varnothing\notin\mathcal{U}$，即 $\varnothing\notin\mathcal{U}\otimes\mathcal{V}$；
- $(X\times Y)_x=Y\in\mathcal{V}$，故 $\{x:(X\times Y)_x\in\mathcal{V}\}=X\in\mathcal{U}$，即 $X\times Y\in\mathcal{U}\otimes\mathcal{V}$；
- 若 $S\subseteq T$，则 $S_x\subseteq T_x$，上闭性立得；
- $(S\cap T)_x=S_x\cap T_x\in\mathcal{V}\iff (S_x\in\mathcal{V}\text{ 且 }T_x\in\mathcal{V})$，有限交封闭立得；
- $((X\times Y)\setminus S)_x=Y\setminus S_x\in\mathcal{V}\iff S_x\notin\mathcal{V}$，故 $\{x:((X\times Y)\setminus S)_x\in\mathcal{V}\}=X\setminus\{x:S_x\in\mathcal{V}\}$ 属于 $\mathcal{U}$ 当且仅当 $\{x:S_x\in\mathcal{V}\}\notin\mathcal{U}$，互补性立得。
- 对 $A\subseteq X$，$(p_1^{-1}(A))_x$ 在 $x\in A$ 时为 $Y\in\mathcal{V}$，在 $x\notin A$ 时为 $\varnothing\notin\mathcal{V}$，故 $\{x:(p_1^{-1}(A))_x\in\mathcal{V}\}=A$，从而 $(p_1)_*(\mathcal{U}\otimes\mathcal{V})=\mathcal{U}$；对 $B\subseteq Y$，$(p_2^{-1}(B))_x=B$，故 $\{x:(p_2^{-1}(B))_x\in\mathcal{V}\}$ 在 $B\in\mathcal{V}$ 时为 $X\in\mathcal{U}$、否则为 $\varnothing\notin\mathcal{U}$，从而 $(p_2)_*(\mathcal{U}\otimes\mathcal{V})=\mathcal{V}$。$\square$

**定理 3.2.** 对平凡群 $G=\{e\}$ 与任意两集合 $X,Y$，比较映射
$$\Pi_{X,Y}:R_\infty(X\times Y)\longrightarrow R_\infty(X)\times R_\infty(Y)$$
为单射（等价地，为双射）**当且仅当 $X$ 与 $Y$ 中至少有一个是有限集**（含空集）。

**证明.** 在同胚 $\Phi_{\infty,-}$ 下，只需考察 $\widetilde{\Pi}_{X,Y}:\operatorname{Ult}(X\times Y)\to\operatorname{Ult}(X)\times\operatorname{Ult}(Y),\ \mathcal{W}\mapsto((p_1)_*(\mathcal{W}),(p_2)_*(\mathcal{W}))$。

- **充分性**：若 $X=\varnothing$ 或 $Y=\varnothing$，则两端均为空集，空映射单射。不妨设 $X$ 有限非空（$Y$ 有限非空完全对称），并设 $\mathcal{W}\in\operatorname{Ult}(X\times Y)$ 满足 $(p_1)_*(\mathcal{W})=\mathcal{U}$、$(p_2)_*(\mathcal{W})=\mathcal{V}$。因 $X$ 有限，$\mathcal{U}$ 必为主超滤 $\mathcal{U}_{x_0}$（存在唯一 $x_0\in X$）。于是 $\{x_0\}\in\mathcal{U}=(p_1)_*(\mathcal{W})$，即
  $$\{x_0\}\times Y=p_1^{-1}(\{x_0\})\in\mathcal{W}.$$
  对任意子集 $S\subseteq X\times Y$，记 $S_{x_0}=\{y\in Y:(x_0,y)\in S\}$，恒有
  $$S\cap(\{x_0\}\times Y)=\{x_0\}\times S_{x_0}=(\{x_0\}\times Y)\cap p_2^{-1}(S_{x_0}).$$
  因 $\{x_0\}\times Y\in\mathcal{W}$，由滤子对有限交封闭与上闭性得：
  $$S\in\mathcal{W}\iff S\cap(\{x_0\}\times Y)\in\mathcal{W}\iff p_2^{-1}(S_{x_0})\in\mathcal{W}\iff S_{x_0}\in(p_2)_*(\mathcal{W})=\mathcal{V}.$$
  因此 $\mathcal{W}$ 由 $(\mathcal{U},\mathcal{V})$ 唯一决定，故 $\widetilde{\Pi}_{X,Y}$ 单射。

- **必要性**：设 $X$ 与 $Y$ 均为**无限集**。在 ZFC 下（由选择公理，任何无限集都含可数无限子集），存在单射 $a:\mathbb{N}\hookrightarrow X$ 与 $b:\mathbb{N}\hookrightarrow Y$。由超滤引理取 $\mathbb{N}$ 上一个非主超滤 $\mathcal{U}_0\in\operatorname{Ult}(\mathbb{N})$，令 $\mathcal{U}:=a_*(\mathcal{U}_0)\in\operatorname{Ult}(X)$、$\mathcal{V}:=b_*(\mathcal{U}_0)\in\operatorname{Ult}(Y)$。
  再令 $(a,b):\mathbb{N}\to X\times Y$ 为 $n\mapsto(a(n),b(n))$，构造两个超滤：
  $$\mathcal{W}_1:=(a,b)_*(\mathcal{U}_0),\qquad \mathcal{W}_2:=\mathcal{U}\otimes\mathcal{V}.$$
  1. *投影相同*：由 $p_1\circ(a,b)=a$、$p_2\circ(a,b)=b$ 与前推函子性知 $(p_1)_*(\mathcal{W}_1)=\mathcal{U}$、$(p_2)_*(\mathcal{W}_1)=\mathcal{V}$；由引理 3.1 知 $(p_1)_*(\mathcal{W}_2)=\mathcal{U}$、$(p_2)_*(\mathcal{W}_2)=\mathcal{V}$。
  2. *$\mathcal{W}_1\ne\mathcal{W}_2$*：考察集合 $D:=\{(a(n),b(n)):n\in\mathbb{N}\}\subseteq X\times Y$。
     - 因 $(a,b)^{-1}(D)=\mathbb{N}\in\mathcal{U}_0$，故 $D\in\mathcal{W}_1$。
     - 因 $a$ 单射，对每个 $x\in X$，截面 $D_x=\{y\in Y:(x,y)\in D\}$ 至多含一个元素（若 $x=a(n)$ 则为 $\{b(n)\}$，否则为 $\varnothing$）。又因 $b$ 单射，对任意 $y\in Y$ 原像 $b^{-1}(\{y\})$ 至多含一个元素（有限），而 $\mathcal{U}_0$ 非主，故 $b^{-1}(\{y\})\notin\mathcal{U}_0$，即 $\{y\}\notin\mathcal{V}$；且 $\varnothing\notin\mathcal{V}$。从而对一切 $x\in X$ 均有 $D_x\notin\mathcal{V}$，于是 $\{x\in X:D_x\in\mathcal{V}\}=\varnothing\notin\mathcal{U}$，即 $D\notin\mathcal{W}_2$。

  因此 $\mathcal{W}_1\ne\mathcal{W}_2$ 但 $\widetilde{\Pi}_{X,Y}(\mathcal{W}_1)=(\mathcal{U},\mathcal{V})=\widetilde{\Pi}_{X,Y}(\mathcal{W}_2)$，$\Pi_{X,Y}$ 非单射。$\square$

---

### 3.4 任意群作用下两个全称命题的判定与证明

#### 全称命题一：“若 $X,Y$ 至少一个有限，则两因子的比较映射 $\Pi_{X,Y}:R_\infty(X\times Y)^G\to R_\infty(X)^G\times R_\infty(Y)^G$ 为双射。”

**判定：成立（真）。**

**证明.**
1. **满射性**：由 3.2 的结论，对任意群 $G$ 与任意两 $G$ 集合 $X,Y$，$\Pi_{X,Y}$ 必为满射。
2. **单射性**：考察交换图
   $$\begin{array}{ccc}
   R_\infty(X\times Y)^G & \xrightarrow{\ \Pi_{X,Y}^G\ } & R_\infty(X)^G\times R_\infty(Y)^G\\[4pt]
   \downarrow & & \downarrow\\[4pt]
   R_\infty(X\times Y) & \xrightarrow{\ \Pi_{X,Y}^{\{e\}}\ } & R_\infty(X)\times R_\infty(Y)
   \end{array}$$
   其中两竖直箭头均为子集包含映射（单射），$\Pi_{X,Y}^{\{e\}}$ 是忘掉群作用（即平凡群）时的两因子比较映射。因 $X,Y$ 至少有一个有限，由定理 3.2 知 $\Pi_{X,Y}^{\{e\}}$ 为单射。单射在子集上的限制仍为单射，故 $\Pi_{X,Y}^G$ 单射。

合并 1 与 2 即知 $\Pi_{X,Y}^G$ 为双射（且由 3.1 的连续性及紧 Hausdorff 性，实为同胚）。$\square$

---

#### 全称命题二：“若 $X^G=Y^G=\varnothing$，则两因子的比较映射 $\Pi_{X,Y}:R_\infty(X\times Y)^G\to R_\infty(X)^G\times R_\infty(Y)^G$ 为单射。”

**判定：不成立（假）。**

**反例与证明.**
取目标 2.4 中的群与作用：
$$G=\operatorname{Sym}_{\mathrm{fin}}(\mathbb{N}),\qquad X=Y=\mathbb{N}\quad(\text{自然左作用}).$$
由目标 2.4 已证 $X^G=Y^G=\varnothing$，且对任意非主超滤 $\mathcal{U}_0\in\operatorname{Ult}(\mathbb{N})$（在 ZFC 下由超滤引理应用于 Fréchet 滤子知其存在），均有 $\mathcal{U}_0\in\operatorname{Ult}_G(\mathbb{N})$。

令对角映射 $\Delta:\mathbb{N}\to\mathbb{N}\times\mathbb{N},\ n\mapsto(n,n)$，并构造 $\mathbb{N}\times\mathbb{N}$ 上的两个超滤：
$$\mathcal{W}_1:=\Delta_*(\mathcal{U}_0),\qquad \mathcal{W}_2:=\mathcal{U}_0\otimes\mathcal{U}_0.$$
1. **投影相同**：由 $p_1\circ\Delta=p_2\circ\Delta=\mathrm{id}_{\mathbb{N}}$ 与引理 3.1，对 $k=1,2$ 均有
   $$(p_1)_*(\mathcal{W}_k)=\mathcal{U}_0,\qquad (p_2)_*(\mathcal{W}_k)=\mathcal{U}_0.$$
2. **均属于 $\operatorname{Ult}_G(\mathbb{N}\times\mathbb{N})$**：任取 $g\in G$。因 $\mathcal{U}_0\in\operatorname{Ult}_G(\mathbb{N})$，有 $\mathbb{N}^g\in\mathcal{U}_0$。对 $k=1,2$，由 $(p_1)_*(\mathcal{W}_k)=(p_2)_*(\mathcal{W}_k)=\mathcal{U}_0$ 得 $p_1^{-1}(\mathbb{N}^g)\in\mathcal{W}_k$ 且 $p_2^{-1}(\mathbb{N}^g)\in\mathcal{W}_k$，从而
   $$(\mathbb{N}\times\mathbb{N})^g=\mathbb{N}^g\times\mathbb{N}^g=p_1^{-1}(\mathbb{N}^g)\cap p_2^{-1}(\mathbb{N}^g)\in\mathcal{W}_k.$$
   由定理 2.3 知 $\mathcal{W}_1,\mathcal{W}_2\in\operatorname{Ult}_G(\mathbb{N}\times\mathbb{N})$。
3. **$\mathcal{W}_1\ne\mathcal{W}_2$**：考察对角线 $D:=\{(n,n):n\in\mathbb{N}\}\subseteq\mathbb{N}\times\mathbb{N}$。
   - 因 $\Delta^{-1}(D)=\mathbb{N}\in\mathcal{U}_0$，故 $D\in\mathcal{W}_1$。
   - 对每个 $m\in\mathbb{N}$，截面 $D_m=\{m\}\notin\mathcal{U}_0$（因 $\mathcal{U}_0$ 非主），故 $\{m\in\mathbb{N}: D_m\in\mathcal{U}_0\}=\varnothing\notin\mathcal{U}_0$，即 $D\notin\mathcal{W}_2$。

记 $r^{(1)}:=\Phi_{\infty,\mathbb{N}\times\mathbb{N}}^{-1}(\mathcal{W}_1)$ 与 $r^{(2)}:=\Phi_{\infty,\mathbb{N}\times\mathbb{N}}^{-1}(\mathcal{W}_2)$，则 $r^{(1)},r^{(2)}\in R_\infty(\mathbb{N}\times\mathbb{N})^G$ 满足 $r^{(1)}\ne r^{(2)}$ 而
$$\Pi_{\mathbb{N},\mathbb{N}}(r^{(1)})=\bigl(\Phi_{\infty,\mathbb{N}}^{-1}(\mathcal{U}_0),\Phi_{\infty,\mathbb{N}}^{-1}(\mathcal{U}_0)\bigr)=\Pi_{\mathbb{N},\mathbb{N}}(r^{(2)}).$$
故 $\Pi_{\mathbb{N},\mathbb{N}}$ 不是单射，该全称命题为假。$\square$