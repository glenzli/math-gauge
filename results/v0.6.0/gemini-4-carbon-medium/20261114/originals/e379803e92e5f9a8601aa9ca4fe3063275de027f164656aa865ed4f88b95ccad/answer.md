{}
以下在 **ZFC** 公理体系下对三个目标给出完整分类、构造与严格证明。

---

### 0. 基本记号与预备引理

1. **指标约定与空集映射：**
   记 $\mathbb{N}=\{0,1,2,\dots\}$。对 $m\in\mathbb{Z}_{\ge 1}\cup\{\infty\}$，指标范围“$0\le n\le m$”指满足 $n\le m$ 的所有非负整数 $n\in\mathbb{N}$（当 $m=\infty$ 时 $n$ 取遍全体 $\mathbb{N}$）。
   在 ZFC 中，$[0]=\varnothing$；对任意集合 $A$，$\operatorname{Map}(\varnothing,A)=\{\mathrm{id}_\varnothing\}$ 为单点集（唯一元素为空映射），而当 $A\ne\varnothing$ 时 $\operatorname{Map}(A,\varnothing)=\varnothing$。

2. **超滤子与超滤子引理（ZFC）：**
   对集合 $X$，称子集族 $\mathcal{U}\subseteq\mathcal{P}(X)$ 为 $X$ 上的**超滤子**，若：
   - (U1) $\varnothing\notin\mathcal{U}$ 且 $X\in\mathcal{U}$；
   - (U2) 若 $A\in\mathcal{U}$ 且 $A\subseteq B\subseteq X$，则 $B\in\mathcal{U}$；
   - (U3) 若 $A,B\in\mathcal{U}$，则 $A\cap B\in\mathcal{U}$；
   - (U4) 对每个 $A\subseteq X$，恰有 $A\in\mathcal{U}$ 或 $X\setminus A\in\mathcal{U}$ 之一成立。

   记 $X$ 上全体超滤子的集合为 $\operatorname{Ult}(X)$。注意当 $X=\varnothing$ 时，(U1) 中 $\varnothing\notin\mathcal{U}$ 与 $X\in\mathcal{U}$ 矛盾，故 $\operatorname{Ult}(\varnothing)=\varnothing$。对 $x\in X$，记主超滤子 $\mathcal{U}_x:=\{A\subseteq X:x\in A\}\in\operatorname{Ult}(X)$。对映射 $h:X\to Y$ 及 $\mathcal{U}\in\operatorname{Ult}(X)$，推前 $h_*(\mathcal{U}):=\{B\subseteq Y:h^{-1}(B)\in\mathcal{U}\}\in\operatorname{Ult}(Y)$。

   **引理 0.1（超滤子引理）：** *设 $X\ne\varnothing$，且非空族 $\mathcal{F}_0\subseteq\mathcal{P}(X)$ 具有**有限交性质**（即对任意 $k\ge 1$ 及 $A_1,\dots,A_k\in\mathcal{F}_0$，均有 $A_1\cap\dots\cap A_k\ne\varnothing$）。则存在 $\mathcal{U}\in\operatorname{Ult}(X)$ 使得 $\mathcal{F}_0\subseteq\mathcal{U}$。*
   **证明：** 令 $\mathfrak{P}$ 为包含 $\mathcal{F}_0$ 的全体真滤子（满足 (U1)–(U3) 的子集族）构成的集合，按包含关系 $\subseteq$ 偏序。由有限交性质，$\mathcal{F}:=\{B\subseteq X:\exists A_1,\dots,A_k\in\mathcal{F}_0\;(k\ge 1),\;A_1\cap\dots\cap A_k\subseteq B\}\in\mathfrak{P}$，故 $\mathfrak{P}\ne\varnothing$。若 $\mathfrak{C}\subseteq\mathfrak{P}$ 为非空全序链，则 $\bigcup\mathfrak{C}$ 仍不含 $\varnothing$、含 $X$、向上封闭，且其中任二元必同属链中某成员从而交仍在 $\bigcup\mathfrak{C}$ 中，故 $\bigcup\mathfrak{C}\in\mathfrak{P}$ 为上界。由 ZFC 中的 Zorn 引理，$\mathfrak{P}$ 有极大元 $\mathcal{U}$。对任意 $A\subseteq X$，若 $A\notin\mathcal{U}$，必存在 $B\in\mathcal{U}$ 使 $A\cap B=\varnothing$（否则 $\{C\subseteq X:\exists B\in\mathcal{U},\;A\cap B\subseteq C\}\in\mathfrak{P}$ 真包含 $\mathcal{U}$，矛盾），于是 $B\subseteq X\setminus A$，由 (U2) 得 $X\setminus A\in\mathcal{U}$。故 $\mathcal{U}\in\operatorname{Ult}(X)$。$\square$

---

## 1. 截断及其相容关系

### 1.1 $R_m(X)$ 的完全分类

对子集 $A\subseteq X$，记其特征函数为 $\mathbf{1}_A:X\to[2]$（当 $x\in A$ 时取 $1$，当 $x\in X\setminus A$ 时取 $0$）。定义 $X$ 上的**一致自对偶族**集合为
$$\mathcal{S}(X):=\bigl\{\mathcal{H}\subseteq\mathcal{P}(X):X\in\mathcal{H},\text{ 且 }\forall A\subseteq X,\;(X\setminus A\in\mathcal{H}\iff A\notin\mathcal{H})\bigr\}.$$
注意当 $X=\varnothing$ 时，取 $A=\varnothing$ 得 $\varnothing\in\mathcal{H}\iff\varnothing\notin\mathcal{H}$，矛盾，故 $\mathcal{S}(\varnothing)=\varnothing$。

**定理 1.1（$R_m(X)$ 的完全分类）：** *对任意集合 $X$ 与任意 $m\in\mathbb{Z}_{\ge 1}\cup\{\infty\}$：*
1. **空底集情形（$X=\varnothing$）：** *对一切 $m\in\mathbb{Z}_{\ge 1}\cup\{\infty\}$，均有 $R_m(\varnothing)=\varnothing$。*
2. **层 $m=1$：** *当 $X=\varnothing$ 时 $R_1(\varnothing)=\varnothing$；当 $X\ne\varnothing$ 时，$R_1(X)=\{r_X^{(1)}\}$ 为单点集，其中 $r_{X,0}^{(1)}=\mathrm{id}_\varnothing:\varnothing\to\varnothing$，且对唯一常值映射 $c_0:X\to[1]$ 有 $r_{X,1}^{(1)}(c_0)=0$。*
3. **层 $m=2$：** *映射 $\Psi_X:R_2(X)\to\mathcal{S}(X)$，$r\mapsto\mathcal{H}_r:=\{A\subseteq X:r_2(\mathbf{1}_A)=1\}$ 为双射（涵盖 $X=\varnothing$ 时 $\varnothing\to\varnothing$）。当 $X\ne\varnothing$ 时，其逆映射将 $\mathcal{H}\in\mathcal{S}(X)$ 映为 $(r_0,r_1,r_2^{\mathcal{H}})$，其中 $r_0=\mathrm{id}_\varnothing$，$r_1(c_0)=0$，且对 $f:X\to[2]$ 有 $r_2^{\mathcal{H}}(f)=1\iff f^{-1}(\{1\})\in\mathcal{H}$。*
4. **层 $3\le m\le\infty$：** *映射 $\Phi_{m,X}:\operatorname{Ult}(X)\to R_m(X)$，$\mathcal{U}\mapsto r^{\mathcal{U}}=(r_n^{\mathcal{U}})_{0\le n\le m}$ 为双射（涵盖 $X=\varnothing$ 时 $\varnothing\to\varnothing$），其中当 $X\ne\varnothing$ 时 $r_0^{\mathcal{U}}=\mathrm{id}_\varnothing$，而对每个满足 $1\le n\le m$ 的整数 $n$ 及 $f:X\to[n]$，*
   $$r_n^{\mathcal{U}}(f)=\text{使 }f^{-1}(\{j\})\in\mathcal{U}\text{ 的唯一 }j\in[n];$$
   *其逆映射为 $r\mapsto\mathcal{U}_r:=\{A\subseteq X:r_2(\mathbf{1}_A)=1\}$。*

**证明：**
1. 若 $X=\varnothing$，任何 $r\in R_m(\varnothing)$ 均需给定第 $0$ 层分量 $r_0:\operatorname{Map}(\varnothing,[0])\to[0]$。但 $\operatorname{Map}(\varnothing,\varnothing)=\{\mathrm{id}_\varnothing\}$ 非空而 $[0]=\varnothing$，不存在非空集到空集的映射，故 $R_m(\varnothing)=\varnothing$。

以下设 $X\ne\varnothing$（$X=\varnothing$ 时第 3、4 项双射两侧皆为空集，自动成立）。此时 $\operatorname{Map}(X,[0])=\varnothing$，故 $r_0:\varnothing\to\varnothing$ 唯一确定为 $\mathrm{id}_\varnothing$；凡涉及 $n=0$（无 $f:X\to[0]$）或 $k=0,n\ge 1$（无 $a:[n]\to[0]$）的相容条件 $a(r_n(f))=r_k(a\circ f)$ 均空真成立。又 $\operatorname{Map}(X,[1])=\{c_0\}$，$[1]=\{0\}$，故 $r_1(c_0)=0$ 亦唯一确定，且 $k=1$ 时的相容条件因 $[1]$ 为单点集恒成立。

2. 当 $m=1$ 时，$n,k\in\{0,1\}$，上述唯一的 $(r_0,r_1)$ 满足全部条件，故 $R_1(X)=\{r_X^{(1)}\}$。

3. 当 $m=2$ 时，$r=(r_0,r_1,r_2)$ 中 $r_0,r_1$ 唯一，只需检验涉及 $2$ 的相容条件：
   - $(n,k)=(1,2)$：映射 $a:[1]\to[2]$ 恰有两个：$a_0(0)=0$ 与 $a_1(0)=1$。作用于 $c_0$ 得常值映射 $\mathbf{0}=\mathbf{1}_\varnothing$ 与 $\mathbf{1}=\mathbf{1}_X$，条件等价于 $r_2(\mathbf{1}_\varnothing)=0$ 且 $r_2(\mathbf{1}_X)=1$。
   - $(n,k)=(2,2)$：$\operatorname{Map}([2],[2])$ 共四个映射：恒等映射（条件平凡）、常值 $0$（等价于 $r_2(\mathbf{1}_\varnothing)=0$）、常值 $1$（等价于 $r_2(\mathbf{1}_X)=1$）以及对换 $\sigma(t)=1-t$（等价于对一切 $f:X\to[2]$ 有 $1-r_2(f)=r_2(\sigma\circ f)$）。

   因 $f\mapsto f^{-1}(\{1\})$ 给出 $\operatorname{Map}(X,[2])\cong\mathcal{P}(X)$，且 $\sigma\circ\mathbf{1}_A=\mathbf{1}_{X\setminus A}$，故 $r_2$ 满足上述全部条件当且仅当 $X\in\mathcal{H}_r$、$\varnothing\notin\mathcal{H}_r$ 且 $X\setminus A\in\mathcal{H}_r\iff A\notin\mathcal{H}_r$，即 $\mathcal{H}_r\in\mathcal{S}(X)$。显然 $\Psi_X$ 与 $\mathcal{H}\mapsto(r_0,r_1,r_2^{\mathcal{H}})$ 互逆。

4. 设 $3\le m\le\infty$ 且 $X\ne\varnothing$。
   - **$\Phi_{m,X}$ 良定义：** 对 $\mathcal{U}\in\operatorname{Ult}(X)$、$1\le n\le m$ 及 $f:X\to[n]$，$X=\bigsqcup_{j=0}^{n-1}f^{-1}(\{j\})$。若有两个不同指标 $i\ne j$ 使 $f^{-1}(\{i\}),f^{-1}(\{j\})\in\mathcal{U}$，则 $\varnothing=f^{-1}(\{i\})\cap f^{-1}(\{j\})\in\mathcal{U}$，矛盾；若对一切 $j\in[n]$ 均有 $f^{-1}(\{j\})\notin\mathcal{U}$，则由 (U4) 知一切 $X\setminus f^{-1}(\{j\})\in\mathcal{U}$，有限归纳应用 (U3)（因 $n\ge 1$）得 $\varnothing=\bigcap_{j=0}^{n-1}(X\setminus f^{-1}(\{j\}))\in\mathcal{U}$，矛盾。故 $r_n^{\mathcal{U}}(f)$ 唯一确定。对任意 $1\le n,k\le m$、$f:X\to[n]$ 及 $a:[n]\to[k]$，令 $j=r_n^{\mathcal{U}}(f)$，则 $f^{-1}(\{j\})\in\mathcal{U}$。因 $f^{-1}(\{j\})\subseteq f^{-1}(a^{-1}(\{a(j)\}))=(a\circ f)^{-1}(\{a(j)\})$，由 (U2) 知 $(a\circ f)^{-1}(\{a(j)\})\in\mathcal{U}$，故 $r_k^{\mathcal{U}}(a\circ f)=a(j)=a(r_n^{\mathcal{U}}(f))$，即 $r^{\mathcal{U}}\in R_m(X)$。
   - **逆映射与双射性：** 显然 $\mathcal{U}_{r^{\mathcal{U}}}=\{A\subseteq X:\mathbf{1}_A^{-1}(\{1\})\in\mathcal{U}\}=\mathcal{U}$。反之，任取 $r\in R_m(X)$，令 $\mathcal{U}:=\mathcal{U}_r$。由 $m=2$ 的分析已知 $\mathcal{U}\in\mathcal{S}(X)$，即满足 (U1) 与 (U4)。下用第 $3$ 层（因 $m\ge 3$）证明 (U2) 与 (U3)：
     任取不交子集 $A,B\subseteq X$（$A\cap B=\varnothing$），定义 $f:X\to[3]$ 在 $A$ 上取 $1$、在 $B$ 上取 $2$、在 $X\setminus(A\cup B)$ 上取 $0$。考察三个映射 $a_1,a_2,a_{12}:[3]\to[2]$，分别由 $a_1^{-1}(\{1\})=\{1\}$、$a_2^{-1}(\{1\})=\{2\}$、$a_{12}^{-1}(\{1\})=\{1,2\}$ 定义。注意 $a_1\circ f=\mathbf{1}_A$，$a_2\circ f=\mathbf{1}_B$，$a_{12}\circ f=\mathbf{1}_{A\cup B}$。由相容关系 $a(r_3(f))=r_2(a\circ f)$ 得：
     $$A\in\mathcal{U}\iff r_3(f)=1,\qquad B\in\mathcal{U}\iff r_3(f)=2,\qquad A\cup B\in\mathcal{U}\iff r_3(f)\in\{1,2\}.$$
     由此推得对一切不交的 $A,B\subseteq X$，有 $A\cup B\in\mathcal{U}\iff(A\in\mathcal{U}\text{ 或 }B\in\mathcal{U})$。
     - 若 $A\in\mathcal{U}$ 且 $A\subseteq C\subseteq X$，取 $B=C\setminus A$，因 $A\cap B=\varnothing$ 且 $A\in\mathcal{U}$，得 $C=A\cup B\in\mathcal{U}$，即 (U2) 成立。
     - 若 $C_1,C_2\in\mathcal{U}$，记 $A_1=X\setminus C_1\notin\mathcal{U}$，$A_2=X\setminus C_2\notin\mathcal{U}$。令 $B_2=A_2\setminus A_1\subseteq A_2$，由 (U2) 的逆否命题知 $B_2\notin\mathcal{U}$。因 $A_1\cap B_2=\varnothing$ 且二者均不属于 $\mathcal{U}$，故 $A_1\cup A_2=A_1\cup B_2\notin\mathcal{U}$，再由 (U4) 得 $C_1\cap C_2=X\setminus(A_1\cup A_2)\in\mathcal{U}$，即 (U3) 成立。

     从而 $\mathcal{U}\in\operatorname{Ult}(X)$。最后，对任意 $1\le n\le m$ 及 $f:X\to[n]$，令 $j=r_n(f)\in[n]$，取 $\delta_j:[n]\to[2]$ 使 $\delta_j^{-1}(\{1\})=\{j\}$。则 $\delta_j\circ f=\mathbf{1}_{f^{-1}(\{j\})}$，由相容性得 $r_2(\mathbf{1}_{f^{-1}(\{j\})})=\delta_j(r_n(f))=\delta_j(j)=1$，即 $f^{-1}(\{j\})\in\mathcal{U}$，故 $r_n(f)=r_n^{\mathcal{U}}(f)$，即 $r=\Phi_{m,X}(\mathcal{U})$。$\square$

---

### 1.2 截断映射 $q_{m,k}$ 的像与各纤维

设 $\infty\ge m\ge k\ge 1$。截断 $q_{m,k}:R_m(X)\to R_k(X)$ 定义为 $q_{m,k}((r_n)_{0\le n\le m})=(r_n)_{0\le n\le k}$。

- **当 $X=\varnothing$ 时：** $R_m(\varnothing)=R_k(\varnothing)=\varnothing$，$q_{m,k}:\varnothing\to\varnothing$ 为空双射，$\operatorname{Im}(q_{m,k})=\varnothing$，陪域无元素（无非空纤维）。
- **当 $X\ne\varnothing$ 时：** 分以下四类完整刻画：
  1. **$m=k$（$1\le k\le\infty$）：** $q_{k,k}=\mathrm{id}_{R_k(X)}$ 为恒等双射，$\operatorname{Im}(q_{k,k})=R_k(X)$，对每个 $s\in R_k(X)$，纤维 $q_{k,k}^{-1}(\{s\})=\{s\}$ 为单点集。
  2. **$\infty\ge m>k\ge 3$：** 由定理 1.1(4) 的构造直接有 $q_{m,k}\circ\Phi_{m,X}=\Phi_{k,X}$，故 **$q_{m,k}$ 为双射**；$\operatorname{Im}(q_{m,k})=R_k(X)$，对每个 $s\in R_k(X)$，纤维 $q_{m,k}^{-1}(\{s\})=\{\Phi_{m,X}(\mathcal{U}_s)\}$ 为单点集。
  3. **$\infty\ge m\ge 3$ 且 $k=2$：** 对任意 $\mathcal{U}\in\operatorname{Ult}(X)$，$\Psi_X(q_{m,2}(\Phi_{m,X}(\mathcal{U})))=\mathcal{U}$，故 **$q_{m,2}$ 为单射**。其像为
     $$\operatorname{Im}(q_{m,2})=\Psi_X^{-1}(\operatorname{Ult}(X))=\bigl\{s\in R_2(X):\mathcal{H}_s\in\operatorname{Ult}(X)\bigr\}.$$
     对任意 $s\in R_2(X)$，纤维为
     $$q_{m,2}^{-1}(\{s\})=\begin{cases}\{\Phi_{m,X}(\mathcal{H}_s)\}\text{（单点集）},&\text{若 }\mathcal{H}_s\in\operatorname{Ult}(X),\\\varnothing,&\text{若 }\mathcal{H}_s\in\mathcal{S}(X)\setminus\operatorname{Ult}(X).\end{cases}$$
     （注：当 $1\le|X|\le 2$ 时，互补对至多两组，$\mathcal{S}(X)=\operatorname{Ult}(X)$，故 $q_{m,2}$ 亦为满射；当 $|X|\ge 3$ 时，任取互异三元 $x_1,x_2,x_3\in X$，多数决族 $\mathcal{H}_{\mathrm{maj}}:=\{B\subseteq X:|B\cap\{x_1,x_2,x_3\}|\ge 2\}\in\mathcal{S}(X)\setminus\operatorname{Ult}(X)$，故 $\operatorname{Im}(q_{m,2})\subsetneq R_2(X)$。）
  4. **$\infty\ge m\ge 2$ 且 $k=1$：** 因 $X\ne\varnothing$，任取 $x_0\in X$ 即有 $\eta_{m,X}(x_0)\in R_m(X)\ne\varnothing$，而 $R_1(X)=\{r_X^{(1)}\}$ 为单点集。故 **$q_{m,1}$ 为满射**，$\operatorname{Im}(q_{m,1})=R_1(X)$，在唯一点 $r_X^{(1)}$ 处的纤维为整个 $R_m(X)$（当 $m=2$ 时经 $\Psi_X$ 同构于 $\mathcal{S}(X)$；当 $m\ge 3$ 时经 $\Phi_{m,X}$ 同构于 $\operatorname{Ult}(X)$）。

---

### 1.3 与集合映射 $h:X\to Y$ 的相容性

设 $h:X\to Y$ 为任意集合映射。
1. **良定义与协变函子性：**
   - 若 $X=\varnothing$，则 $R_m(\varnothing)=\varnothing$，$R_m(h):\varnothing\to R_m(Y)$ 为唯一空映射（注意当 $X\ne\varnothing$ 且 $Y=\varnothing$ 时不存在映射 $h:X\to\varnothing$）。
   - 若 $X\ne\varnothing$，对 $r\in R_m(X)$、$0\le n,k\le m$、$f:Y\to[n]$ 及 $a:[n]\to[k]$，
     $$a\bigl((R_m(h)r)_n(f)\bigr)=a\bigl(r_n(f\circ h)\bigr)=r_k\bigl(a\circ(f\circ h)\bigr)=r_k\bigl((a\circ f)\circ h\bigr)=(R_m(h)r)_k(a\circ f),$$
     故 $R_m(h)r\in R_m(Y)$。直接核验知 $R_m(\mathrm{id}_X)=\mathrm{id}_{R_m(X)}$，且对 $h_1:X\to Y,h_2:Y\to Z$ 有
     $$\bigl(R_m(h_2\circ h_1)r\bigr)_n(f)=r_n(f\circ h_2\circ h_1)=(R_m(h_1)r)_n(f\circ h_2)=\bigl((R_m(h_2)\circ R_m(h_1))r\bigr)_n(f),$$
     即 $R_m(h_2\circ h_1)=R_m(h_2)\circ R_m(h_1)$。
2. **与截断及点值记录的自然性：**
   对 $\infty\ge m\ge k\ge 1$，两端在第 $n\le k$ 层作用于 $f:Y\to[n]$ 均为 $r_n(f\circ h)$，故 $q_{m,k}\circ R_m(h)=R_k(h)\circ q_{m,k}$。对 $x\in X$，$\eta_{m,X}(x)\in R_m(X)$（因 $a(f(x))=(a\circ f)(x)$），且 $(R_m(h)\eta_{m,X}(x))_n(f)=f(h(x))=\eta_{m,Y}(h(x))_n(f)$，故 $R_m(h)\circ\eta_{m,X}=\eta_{m,Y}\circ h$，且 $q_{m,k}\circ\eta_{m,X}=\eta_{k,X}$。
3. **与定理 1.1 分类双射的相容性（自然同构）：**
   - $m=1$：当 $X\ne\varnothing$（从而 $Y\ne\varnothing$）时，$R_1(h)(r_X^{(1)})=r_Y^{(1)}$。
   - $m=2$：对 $\mathcal{H}\in\mathcal{S}(X)$，令 $h_*(\mathcal{H}):=\{B\subseteq Y:h^{-1}(B)\in\mathcal{H}\}$。因 $h^{-1}(Y)=X$ 且 $h^{-1}(Y\setminus B)=X\setminus h^{-1}(B)$，故 $h_*(\mathcal{H})\in\mathcal{S}(Y)$。又因 $\mathbf{1}_B\circ h=\mathbf{1}_{h^{-1}(B)}$，对任意 $r\in R_2(X)$ 有
     $$B\in\Psi_Y(R_2(h)r)\iff r_2(\mathbf{1}_B\circ h)=1\iff h^{-1}(B)\in\Psi_X(r)\iff B\in h_*(\Psi_X(r)),$$
     即 $\Psi_Y\circ R_2(h)=h_*\circ\Psi_X$；且 $\Psi_X(\eta_{2,X}(x))=\mathcal{U}_x$。
   - $3\le m\le\infty$：对 $\mathcal{U}\in\operatorname{Ult}(X)$、$1\le n\le m$ 及 $f:Y\to[n]$，有 $(f\circ h)^{-1}(\{j\})=h^{-1}(f^{-1}(\{j\}))\in\mathcal{U}\iff f^{-1}(\{j\})\in h_*(\mathcal{U})$，故
     $$R_m(h)\circ\Phi_{m,X}=\Phi_{m,Y}\circ h_*,\qquad\eta_{m,X}(x)=\Phi_{m,X}(\mathcal{U}_x).$$
4. **群作用的良定义与等变性：**
   若群 $G$ 左作用于 $X$，因 $e_X=\mathrm{id}_X$ 且 $(g_1g_2)_X=g_{1,X}\circ g_{2,X}$，由函子性得 $e\cdot r=r$ 及 $(g_1g_2)\cdot r=R_m(g_{1,X}\circ g_{2,X})r=g_1\cdot(g_2\cdot r)$，故 $R_m(X)$ 成为左 $G$-集合。在 $\Psi_X$ 与 $\Phi_{m,X}$ 下，左作用对应子集族推前 $(g_X)_*(\mathcal{H})=\{B\subseteq X:g^{-1}B\in\mathcal{H}\}=\{gA:A\in\mathcal{H}\}$。由自然性知 $q_{m,k}$ 与 $\eta_{m,X}$ 皆为 $G$-等变映射，且任意 $G$-等变映射 $h:X\to Y$ 诱导的 $R_m(h)$ 亦 $G$-等变。

---

### 1.4 有限 $G$-集合 $X$ 的不动记录存在判准、精确基数及限制映射

设 $X$ 为有限 $G$-集合。记作用像群 $\overline{G}:=\operatorname{Im}(G\to\operatorname{Sym}(X))$（无论 $G$ 本身是否有限，$\overline{G}$ 必为有限群）；对 $\bar{g}\in\overline{G}$，记 $c(\bar{g})$ 为置换 $\bar{g}$ 在 $X$ 上的不相交轮换个数（即 $\langle\bar{g}\rangle$-轨道个数）。

**定理 1.2（有限 $G$-集合的不动记录分类与计数）：** *设 $X$ 为有限 $G$-集合。*
1. **层 $m=1$：**
   - *存在判准：$R_1(X)^G\ne\varnothing\iff X\ne\varnothing$。*
   - *精确基数：当 $X=\varnothing$ 时 $|R_1(X)^G|=0$；当 $X\ne\varnothing$ 时 $|R_1(X)^G|=1$。*
2. **层 $m=2$：**
   - *存在判准：$R_2(X)^G\ne\varnothing$ 当且仅当 **$X\ne\varnothing$，且对每个 $g\in G$，置换 $g_X$ 在 $X$ 上至少有一个奇数长度的轮换（即奇基数 $\langle g\rangle$-轨道）**（等价地：$X\ne\varnothing$ 且不存在 $g\in G$ 与 $A\subseteq X$ 使 $gA=X\setminus A$；亦等价于 $X\ne\varnothing$ 且 $\overline{G}$ 中任何 $2$-幂阶元素在 $X$ 上均有不动点）。*
   - *精确基数：*
     $$|R_2(X)^G|=\begin{cases}0,&\text{若 }X=\varnothing\text{ 或 }\exists g\in G\text{ 使 }g_X\text{ 在 }X\text{ 上的轮换全为偶长},\\[6pt]2^{\frac{1}{2}|\mathcal{P}(X)/G|-1}=2^{\left(\frac{1}{2|\overline{G}|}\sum_{\bar{g}\in\overline{G}}2^{c(\bar{g})}\right)-1},&\text{其余情形}.\end{cases}$$
3. **层 $3\le m\le\infty$：**
   - *点值映射诱导双射 $\eta_{m,X}^G:X^G\xrightarrow{\sim}R_m(X)^G$。*
   - *存在判准：$R_m(X)^G\ne\varnothing\iff X^G\ne\varnothing$。*
   - *精确基数：$|R_m(X)^G|=|X^G|$。*

**证明：**
- $X=\varnothing$ 时一切 $R_m(\varnothing)^G=\varnothing$，基数为 $0$，各公式与判准显然吻合。以下设 $X\ne\varnothing$ 有限。
- $m=1$ 时 $R_1(X)$ 为单点集，$G$ 平凡作用，故 $|R_1(X)^G|=1$。
- $3\le m\le\infty$ 时，设 $X=\{x_1,\dots,x_d\}$（$d\ge 1$）。对任意 $\mathcal{U}\in\operatorname{Ult}(X)$，由 $X=\bigsqcup_{i=1}^d\{x_i\}\in\mathcal{U}$ 知存在唯一 $x_i$ 使 $\{x_i\}\in\mathcal{U}$，由 (U2) 与 (U4) 得 $\mathcal{U}=\mathcal{U}_{x_i}$。故 $\eta_{m,X}:X\to R_m(X)$ 为 $G$-集合同构，取 $G$-不动点即得 $\eta_{m,X}^G:X^G\xrightarrow{\sim}R_m(X)^G$，从而 $|R_m(X)^G|=|X^G|$。
- $m=2$ 时，经 $G$-等变双射 $\Psi_X:R_2(X)\xrightarrow{\sim}\mathcal{S}(X)$，$\mathcal{H}\in\mathcal{S}(X)^G$ 当且仅当 $\mathcal{H}$ 是 $\mathcal{P}(X)$ 中若干 $G$-轨道的并、包含 $\{X\}$、不含 $\{\varnothing\}$，且对每个轨道 $\mathcal{O}\in\mathcal{P}(X)/G$ 恰在 $\mathcal{O}$ 与其补轨道 $\complement(\mathcal{O}):=\{X\setminus A:A\in\mathcal{O}\}$（因 $g(X\setminus A)=X\setminus gA$，取补在 $\mathcal{P}(X)/G$ 上良定义为对合）中择一并入 $\mathcal{H}$。
  - 若存在自互补轨道 $\mathcal{O}=\complement(\mathcal{O})$（即存在 $A\subseteq X,g\in G$ 使 $gA=X\setminus A$），则无法在 $\{\mathcal{O},\complement(\mathcal{O})\}$ 中择一，故 $\mathcal{S}(X)^G=\varnothing$。
  - 若不存在自互补轨道，则对合 $\complement$ 在有限集 $\mathcal{P}(X)/G$ 上无不动点，故 $|\mathcal{P}(X)/G|=2N$ 为正偶数（其中 $\{\varnothing\}$ 与 $\{X\}$ 构成一对，必选 $\{X\}$），其余 $N-1=\frac{1}{2}|\mathcal{P}(X)/G|-1$ 对互补轨道对每对恰有 $2$ 种独立选法，故 $|\mathcal{S}(X)^G|=2^{\frac{1}{2}|\mathcal{P}(X)/G|-1}$。
  - 判别自互补轨道：固定 $g\in G$，将 $X$ 分解为 $g_X$ 的不相交轮换。条件 $gA=X\setminus A$ 等价于对每个轮换 $(y_0,y_1,\dots,y_{\ell-1})$（$gy_i=y_{i+1\bmod\ell}$）有 $y_{i+1}\in A\iff y_i\notin A$。若 $g_X$ 含奇长 $\ell$ 的轮换，沿该轮换交替归属导致 $y_0\in A\iff y_\ell\notin A$，与 $y_\ell=y_0$ 矛盾；反之，若 $g_X$ 的所有轮换长皆为偶数，在每个轮换上令偶数下标点属于 $A$、奇数下标点不属于 $A$，即得 $gA=X\setminus A$。（此外，若令 $\operatorname{ord}(g_X)=2^su$，$u$ 为奇数，则 $g_X$ 轮换全为偶长当且仅当 $2$-幂阶元 $(g_X)^u\in\overline{G}$ 在 $X$ 上无不动点。）
  - 最后，有限群 $\overline{G}$ 作用于 $\mathcal{P}(X)$ 时，元素 $\bar{g}\in\overline{G}$ 固定的子集 $A\subseteq X$ 恰为 $\bar{g}$ 的若干轮换之并，共 $2^{c(\bar{g})}$ 个。由 Burnside 引理得 $|\mathcal{P}(X)/G|=|\mathcal{P}(X)/\overline{G}|=\frac{1}{|\overline{G}|}\sum_{\bar{g}\in\overline{G}}2^{c(\bar{g})}$，代入即得基数公式。$\square$

**有限 $G$-集合不动记录间的限制映射 $q_{m,k}^G:R_m(X)^G\to R_k(X)^G$（$\infty\ge m\ge k\ge 1$）：**
- 当 $X=\varnothing$ 时，所有 $R_m(\varnothing)^G=\varnothing$，$q_{m,k}^G:\varnothing\to\varnothing$ 为空双射。
- 当 $X\ne\varnothing$ 有限时：
  1. $m=k$：$q_{k,k}^G=\mathrm{id}_{R_k(X)^G}$ 为恒等双射。
  2. $\infty\ge m>k\ge 3$：因 $q_{m,k}\circ\eta_{m,X}=\eta_{k,X}$ 且两侧均由点值映射与 $X^G$ 双射等同，**$q_{m,k}^G$ 为双射**。
  3. $\infty\ge m\ge 3$ 且 $k=2$：**$q_{m,2}^G$ 为单射**，其像为 $\operatorname{Im}(q_{m,2}^G)=\eta_{2,X}(X^G)$（对应主超滤子 $\{\mathcal{U}_x:x\in X^G\}$）。对 $s\in R_2(X)^G$，当 $s=\eta_{2,X}(x)$（$x\in X^G$）时纤维为 $\{\eta_{m,X}(x)\}$，否则纤维为 $\varnothing$。（下文 1.5 将证 $q_{m,2}^G$ 为满射当且仅当 $|X|\le 2$ 或 $R_2(X)^G=\varnothing$。）
  4. $m=2,k=1$：陪域为单点集 $\{r_X^{(1)}\}$。若 $R_2(X)^G\ne\varnothing$，则 $q_{2,1}^G$ 为满射，唯一纤维为 $R_2(X)^G$；若 $R_2(X)^G=\varnothing$，则 $q_{2,1}^G:\varnothing\to\{r_X^{(1)}\}$ 像与纤维皆为空。
  5. $\infty\ge m\ge 3,k=1$：陪域为 $\{r_X^{(1)}\}$。若 $X^G\ne\varnothing$，则 $q_{m,1}^G$ 为满射，唯一纤维为 $\eta_{m,X}(X^G)$（基数 $|X^G|$）；若 $X^G=\varnothing$，则 $q_{m,1}^G:\varnothing\to\{r_X^{(1)}\}$ 像与纤维皆为空。

---

### 1.5 有限层不动记录延拓为完整不动记录的准确范围

我们对**任意群 $G$、任意 $G$-集合 $X$（无论有限或无限）及任意有限层 $k\in\mathbb{Z}_{\ge 1}$** 给出有限层不动记录 $s\in R_k(X)^G$ 可延拓为完整不动记录 $r\in R_\infty(X)^G$（即 $s\in\operatorname{Im}(q_{\infty,k}^G)$）的准确范围：

1. **当 $k\ge 3$ 时（无条件唯一延拓）：**
   对**一切**群 $G$ 与**一切** $G$-集合 $X$，**$q_{\infty,k}^G:R_\infty(X)^G\to R_k(X)^G$ 恒为双射**，即每个第 $k$ 层不动记录均可且唯一延拓为完整不动记录。
   *依据：* 由 1.2 节，$q_{\infty,k}:R_\infty(X)\to R_k(X)$ 为 $G$-等变双射。对任意 $s\in R_k(X)^G$，设唯一原像为 $r=q_{\infty,k}^{-1}(s)\in R_\infty(X)$，则对任意 $g\in G$ 有 $q_{\infty,k}(g\cdot r)=g\cdot q_{\infty,k}(r)=g\cdot s=s=q_{\infty,k}(r)$；由 $q_{\infty,k}$ 单射即得 $g\cdot r=r$，故 $r\in R_\infty(X)^G$。

2. **当 $k=2$ 时：**
   - **单个记录的延拓范围：** $s\in R_2(X)^G$ 可延拓至 $R_\infty(X)^G$（且延拓若存在必唯一）**当且仅当 $\mathcal{H}_s\in\operatorname{Ult}(X)$**（若 $X$ 有限，这等价于 $s\in\eta_{2,X}(X^G)$）。
     *依据：* $q_{\infty,2}:R_\infty(X)\to R_2(X)$ 为 $G$-等变单射且像为 $\Psi_X^{-1}(\operatorname{Ult}(X))$；同上由单射性，只要 $s\in R_2(X)^G$ 落在 $\operatorname{Im}(q_{\infty,2})$ 中，其唯一原像 $r\in R_\infty(X)$ 自动满足 $g\cdot r=r$。
   - **整层全可延拓（即 $q_{\infty,2}^G$ 为满射/双射）的准确范围：** 对任意 $G$-集合 $X$，$q_{\infty,2}^G:R_\infty(X)^G\to R_2(X)^G$ 为满射**当且仅当 $|X|\le 2$ 或 $R_2(X)^G=\varnothing$**。
     *证明：* 若 $|X|\le 2$，则 $q_{\infty,2}$ 本身为双射；若 $R_2(X)^G=\varnothing$，则 $R_\infty(X)^G=\varnothing$，映射为空双射。反之，设 $|X|\ge 3$ 且 $R_2(X)^G\ne\varnothing$。若 $R_\infty(X)^G=\varnothing$，则 $\operatorname{Im}(q_{\infty,2}^G)=\varnothing\subsetneq R_2(X)^G$；若 $R_\infty(X)^G\ne\varnothing$，取 $\mathcal{U}\in\operatorname{Ult}(X)^G$。因 $|X|\ge 3$，必存在 $x\in X$ 使 $\{x\}\notin\mathcal{U}$（超滤子至多含一个单点集）。考察单点集轨道 $\mathcal{O}:=G\cdot\{x\}=\{\{gx\}:g\in G\}\in\mathcal{P}(X)/G$。由 $\mathcal{U}$ 的 $G$-不变性知 $\mathcal{O}\cap\mathcal{U}=\varnothing$，故 $\complement(\mathcal{O})\subseteq\mathcal{U}$。因 $|X|\ge 3$，$\mathcal{O}$ 中元素基数为 $1$，而 $\complement(\mathcal{O})$ 中元素余基数为 $1$（当 $X$ 有限时基数为 $|X|-1\ge 2$，无限时基数无限），故 $\mathcal{O}\ne\complement(\mathcal{O})$ 且 $\mathcal{O}\notin\{\{\varnothing\},\{X\}\}$。令 $\mathcal{H}':=(\mathcal{U}\setminus\complement(\mathcal{O}))\cup\mathcal{O}$，则 $\mathcal{H}'\in\mathcal{S}(X)^G$。我们来证 $\mathcal{H}'\notin\operatorname{Ult}(X)$：
     - 若 $|\mathcal{O}|\ge 2$，则 $\mathcal{H}'$ 含有两个不同单点集 $\{x\}$ 与 $\{gx\}$，不能为超滤子；
     - 若 $|\mathcal{O}|=1$，则 $x\in X^G$，$\mathcal{O}=\{\{x\}\}$，$\complement(\mathcal{O})=\{X\setminus\{x\}\}$。因 $|X|\ge 3$，$X\setminus\{x\}$ 至少含两个不同元素，可将其拆为两个非空不交子集 $B_1\sqcup B_2=X\setminus\{x\}\in\mathcal{U}$。因 $\mathcal{U}$ 为超滤子，$B_1,B_2$ 中必有一个不属于 $\mathcal{U}$，记为 $B\notin\mathcal{U}$（$\varnothing\subsetneq B\subsetneq X\setminus\{x\}$）。考察 $C:=\{x\}\cup B$：因 $|C|\ge 2$ 且 $x\in C$，故 $C\ne\{x\}$ 且 $C\ne X\setminus\{x\}$，即 $C\notin\mathcal{O}\cup\complement(\mathcal{O})$；又 $\{x\}\notin\mathcal{U}$ 且 $B\notin\mathcal{U}$，故 $C\notin\mathcal{U}$，从而 $C\notin\mathcal{H}'$。但 $\{x\}\in\mathcal{H}'$ 且 $\{x\}\subseteq C$，违反 (U2)，故 $\mathcal{H}'\notin\operatorname{Ult}(X)$。因此 $\Psi_X^{-1}(\mathcal{H}')\in R_2(X)^G\setminus\operatorname{Im}(q_{\infty,2}^G)$。

3. **当 $k=1$ 时：**
   若 $X=\varnothing$，则 $R_1(\varnothing)^G=\varnothing$，空真全可延拓。若 $X\ne\varnothing$，则 $R_1(X)^G=\{r_X^{(1)}\}$ 为单点集，该唯一元素可延拓为完整不动记录**当且仅当 $R_\infty(X)^G\ne\varnothing$**（一般 $G$-集合的充要条件见定理 2.2，即对每个有限子集 $F\subseteq G$ 有 $X^F\ne\varnothing$；有限 $G$-集合时等价于 $X^G\ne\varnothing$），延拓全体即为 $R_\infty(X)^G$（唯一当且仅当 $|R_\infty(X)^G|=1$）。

---

## 2. 完整不动记录的空间

### 2.1 $R_\infty(X)^G$ 的内在拓扑分类与非空充要条件

对任意集合 $X$，赋予 $\operatorname{Ult}(X)$ **Stone 拓扑**，其开闭基为 $\{V_A:A\subseteq X\}$，其中 $V_A:=\{\mathcal{U}\in\operatorname{Ult}(X):A\in\mathcal{U}\}$（因 $V_\varnothing=\varnothing$，$V_X=\operatorname{Ult}(X)$，$V_A\cap V_B=V_{A\cap B}$ 且 $\operatorname{Ult}(X)\setminus V_A=V_{X\setminus A}$，故 $\{V_A\}_{A\subseteq X}$ 确实构成拓扑的开闭基）。

**命题 2.1：** *对任意 $G$-集合 $X$，$\Phi_{\infty,X}:\operatorname{Ult}(X)\to R_\infty(X)$ 是紧 Hausdorff 零维（Stone）空间之间的 $G$-等变同胚（当 $X=\varnothing$ 时为空空间同胚）。*
**证明：** $X=\varnothing$ 时显然。设 $X\ne\varnothing$。$R_\infty(X)$ 的拓扑由子基 $U_{n,f,j}:=\{r\in R_\infty(X):r_n(f)=j\}$（$n\ge 1,f:X\to[n],j\in[n]$；$n=0$ 时 $\operatorname{Map}(X,[0])=\varnothing$ 无观察）生成。对任意 $\mathcal{U}\in\operatorname{Ult}(X)$，由定理 1.1(4) 知
$$\Phi_{\infty,X}(\mathcal{U})\in U_{n,f,j}\iff r_n^{\mathcal{U}}(f)=j\iff f^{-1}(\{j\})\in\mathcal{U}\iff\mathcal{U}\in V_{f^{-1}(\{j\})};$$
反之对任意 $A\subseteq X$，$\Phi_{\infty,X}(V_A)=U_{2,\mathbf{1}_A,1}$。故双射 $\Phi_{\infty,X}$ 使两边拓扑的基一一对应，从而是同胚（$G$-等变性已由 1.3 节给出）。
验证紧性与 Hausdorff 性：若 $\mathcal{U}\ne\mathcal{V}$，取 $A\in\mathcal{U}\setminus\mathcal{V}$，则 $V_A$ 与 $V_{X\setminus A}$ 为分离二者的不交开闭邻域，故为 Hausdorff 零维空间。将 $R_\infty(X)$ 视为乘积空间 $P:=\prod_{n\ge 0}\prod_{f\in\operatorname{Map}(X,[n])}[n]$ 的子空间，其中每个 $[n]$ 为有限离散紧 Hausdorff 空间；由定义，$R_\infty(X)$ 的拓扑恰为 $P$ 诱导的子空间拓扑。在 ZFC 中由 Tychonoff 定理知 $P$ 紧；对每组 $(n,k,f,a)$，坐标映射 $r\mapsto a(r_n(f))$ 与 $r\mapsto r_k(a\circ f)$ 均为从 $P$ 到离散 Hausdorff 空间 $[k]$ 的连续映射，其等化子在 $P$ 中闭，$R_\infty(X)$ 作为这一族闭集的交是紧空间的闭子集，故紧。$\square$

接下来建立刻画超滤子不动点的核心引理（双射情形的 Katětov 三染色引理）：

**引理 2.1：** *设 $X$ 为任意集合，$\sigma:X\to X$ 为双射，$\operatorname{Fix}(\sigma):=\{x\in X:\sigma(x)=x\}$。则对任意 $\mathcal{U}\in\operatorname{Ult}(X)$，有*
$$\sigma_*(\mathcal{U})=\mathcal{U}\quad\Longleftrightarrow\quad\operatorname{Fix}(\sigma)\in\mathcal{U}.$$
**证明：**
- （$\Leftarrow$）若 $\operatorname{Fix}(\sigma)\in\mathcal{U}$，对任意 $B\subseteq X$，因 $\sigma$ 在 $\operatorname{Fix}(\sigma)$ 上为恒等映射，有 $\sigma^{-1}(B)\cap\operatorname{Fix}(\sigma)=B\cap\operatorname{Fix}(\sigma)$。由 $\operatorname{Fix}(\sigma)\in\mathcal{U}$ 及滤子性质得 $B\in\sigma_*(\mathcal{U})\iff\sigma^{-1}(B)\in\mathcal{U}\iff\sigma^{-1}(B)\cap\operatorname{Fix}(\sigma)\in\mathcal{U}\iff B\cap\operatorname{Fix}(\sigma)\in\mathcal{U}\iff B\in\mathcal{U}$，故 $\sigma_*(\mathcal{U})=\mathcal{U}$。
- （$\Rightarrow$）将 $X\setminus\operatorname{Fix}(\sigma)$ 分解为循环群 $\langle\sigma\rangle$ 作用的轨道族 $\mathfrak{O}$，每个轨道 $O\in\mathfrak{O}$ 的基数均 $\ge 2$。由选择公理（ZFC），在每个轨道 $O\in\mathfrak{O}$ 中选取一个代表元 $x_O\in O$，将 $O$ 划分为两两不交的三个子集 $O_0\sqcup O_1\sqcup O_2=O$：
  - 若 $O$ 无限，则 $\mathbb{Z}\to O,k\mapsto\sigma^k(x_O)$ 为双射，令 $O_0:=\{\sigma^{2k}(x_O):k\in\mathbb{Z}\}$，$O_1:=\{\sigma^{2k+1}(x_O):k\in\mathbb{Z}\}$，$O_2:=\varnothing$；
  - 若 $O$ 有限且 $|O|=2t$（$t\ge 1$），令 $O_0:=\{\sigma^{2j}(x_O):0\le j<t\}$，$O_1:=\{\sigma^{2j+1}(x_O):0\le j<t\}$，$O_2:=\varnothing$；
  - 若 $O$ 有限且 $|O|=2t+1$（$t\ge 1$），令 $O_0:=\{\sigma^{2j}(x_O):0\le j<t\}$，$O_1:=\{\sigma^{2j+1}(x_O):0\le j<t\}$，$O_2:=\{\sigma^{2t}(x_O)\}$。

  对 $i\in\{0,1,2\}$ 令 $A_i:=\bigsqcup_{O\in\mathfrak{O}}O_i$。直接验证知在每个轨道 $O$ 上有 $\sigma(O_0)\subseteq O_1$、$\sigma(O_1)\subseteq O_0\cup O_2$、$\sigma(O_2)\subseteq O_0$，故对每个 $i\in\{0,1,2\}$ 均有 $\sigma(A_i)\cap A_i=\varnothing$，即 $A_i\cap\sigma^{-1}(A_i)=\varnothing$。
  现设 $\sigma_*(\mathcal{U})=\mathcal{U}$。因 $X=\operatorname{Fix}(\sigma)\sqcup A_0\sqcup A_1\sqcup A_2\in\mathcal{U}$，四者必有一属于 $\mathcal{U}$。若某个 $A_i\in\mathcal{U}$，则由 $A_i\in\sigma_*(\mathcal{U})$ 知 $\sigma^{-1}(A_i)\in\mathcal{U}$，从而 $\varnothing=A_i\cap\sigma^{-1}(A_i)\in\mathcal{U}$，矛盾。故必有 $\operatorname{Fix}(\sigma)\in\mathcal{U}$。$\square$

对任意子集 $S\subseteq G$，记公共不动点集 $X^S:=\{x\in X:\forall g\in S,\;gx=x\}$（约定 $X^\varnothing=X$），并记 $X^g:=X^{\{g\}}$；记 $\mathcal{P}_{\mathrm{fin}}(G)$ 为 $G$ 的全体有限子集按包含关系构成的定向偏序集。注意对每个 $F\in\mathcal{P}_{\mathrm{fin}}(G)$，$X^F=X^{\langle F\rangle}$。

**定理 2.2（$R_\infty(X)^G$ 的内在拓扑分类与非空判准）：** *对任意群 $G$ 与任意 $G$-集合 $X$：*
1. **内在分类（与子空间拓扑相容）：** *同胚 $\Phi_{\infty,X}$ 限制为空间同胚*
   $$\Phi_{\infty,X}\big|_{\operatorname{Ult}_G(X)}:\operatorname{Ult}_G(X)\xrightarrow{\;\sim\;}R_\infty(X)^G,\qquad\operatorname{Ult}_G(X):=\bigl\{\mathcal{U}\in\operatorname{Ult}(X):\forall g\in G,\;X^g\in\mathcal{U}\bigr\},$$
   *其中 $\operatorname{Ult}_G(X)$ 取 $\operatorname{Ult}(X)$ 的子空间拓扑（开闭基为 $\{V_A\cap\operatorname{Ult}_G(X):A\subseteq X\}$）。这等价于由 $(X,G)$ 直接构造的以下两种内在拓扑模型：*
   - **布尔商代数 Stone 空间模型：** *在布尔代数 $\mathcal{P}(X)$ 中令理想 $\mathcal{I}_G(X):=\{B\subseteq X:\exists F\in\mathcal{P}_{\mathrm{fin}}(G),\;B\cap X^F=\varnothing\}$，作商布尔代数 $\mathcal{B}_G(X):=\mathcal{P}(X)/\mathcal{I}_G(X)$，则 $R_\infty(X)^G$ 自然同胚于 $\mathcal{B}_G(X)$ 的超滤子 Stone 空间 $\operatorname{Spec}(\mathcal{B}_G(X))$（赋予基本开闭集 $\{u\in\operatorname{Spec}(\mathcal{B}_G(X)):[A]\in u\}$ 生成的拓扑）。*
   - **投射极限模型：** *对 $F_1\subseteq F_2$（$F_1,F_2\in\mathcal{P}_{\mathrm{fin}}(G)$），包含映射 $X^{F_2}\hookrightarrow X^{F_1}\hookrightarrow X$ 诱导闭嵌入 $\operatorname{Ult}(X^{F_2})\hookrightarrow\operatorname{Ult}(X^{F_1})\hookrightarrow\operatorname{Ult}(X)$，且 $R_\infty(X)^G$ 自然同胚于紧 Hausdorff 空间的投射极限 $\varprojlim_{F\in\mathcal{P}_{\mathrm{fin}}(G)}\operatorname{Ult}(X^F)$。*
2. **非空充要条件：** *$R_\infty(X)^G\ne\varnothing$ **当且仅当**对 $G$ 的每个有限子集 $F\subseteq G$（等价地，对 $G$ 的每个有限生成子群 $H\le G$），均有 $X^F\ne\varnothing$。*

**证明：**
1. 对任意 $\mathcal{U}\in\operatorname{Ult}(X)$，$\Phi_{\infty,X}(\mathcal{U})\in R_\infty(X)^G$ 当且仅当对一切 $g\in G$ 有 $(g_X)_*(\mathcal{U})=\mathcal{U}$；由引理 2.1（应用于双射 $\sigma=g_X$），这当且仅当对一切 $g\in G$ 有 $X^g\in\mathcal{U}$，故 $\Phi_{\infty,X}$ 将子空间 $\operatorname{Ult}_G(X)$ 同胚映上 $R_\infty(X)^G$。
   进一步，在滤子中，$\forall g\in G,\;X^g\in\mathcal{U}$ 等价于对一切 $F\in\mathcal{P}_{\mathrm{fin}}(G)$ 有 $X^F\in\mathcal{U}$（$F=\varnothing$ 时 $X^\varnothing=X\in\mathcal{U}$；$F=\{g_1,\dots,g_k\}$ 非空时 $X^F=\bigcap_{i=1}^kX^{g_i}\in\mathcal{U}$），又等价于 $\mathcal{U}\cap\mathcal{I}_G(X)=\varnothing$。商投射 $\pi:\mathcal{P}(X)\to\mathcal{B}_G(X)$ 在与 $\mathcal{I}_G(X)$ 不交的 $\mathcal{P}(X)$-超滤子及 $\mathcal{B}_G(X)$-超滤子之间建立双射 $\mathcal{U}\mapsto\pi(\mathcal{U})$，且将开闭基 $V_A\cap\operatorname{Ult}_G(X)$ 映为 $\{u:[A]\in u\}$，故 $\operatorname{Ult}_G(X)\cong\operatorname{Spec}(\mathcal{B}_G(X))$。同时，在 $\operatorname{Ult}(X)$ 中每个闭嵌入 $\operatorname{Ult}(X^F)\hookrightarrow\operatorname{Ult}(X)$ 的像恰为 $V_{X^F}$，而有非空指标集 $\mathcal{P}_{\mathrm{fin}}(G)$（含 $\varnothing$）的嵌套子空间族 $(V_{X^F})_{F\in\mathcal{P}_{\mathrm{fin}}(G)}$ 的交 $\bigcap_{F}V_{X^F}=\operatorname{Ult}_G(X)$ 经对角映射 $z\mapsto(z)_{F\in\mathcal{P}_{\mathrm{fin}}(G)}$ 与投射极限 $\varprojlim_{F}V_{X^F}\cong\varprojlim_{F}\operatorname{Ult}(X^F)$ 同胚（子空间基本开集 $U\cap\bigcap_FV_{X^F}$ 即 $F=\varnothing$ 分量开集 $U\cap V_X$ 的原像）。当 $X=\varnothing$ 时，所有模型皆为空空间，同样同胚。
2. - （$\Rightarrow$）若 $R_\infty(X)^G\ne\varnothing$，取 $\mathcal{U}\in\operatorname{Ult}_G(X)$，则对每个有限子集 $F\subseteq G$ 有 $X^F\in\mathcal{U}$，由 $\varnothing\notin\mathcal{U}$ 知 $X^F\ne\varnothing$。
   - （$\Leftarrow$）若对一切 $F\in\mathcal{P}_{\mathrm{fin}}(G)$ 均有 $X^F\ne\varnothing$，特别取 $F=\varnothing$ 得 $X=X^\varnothing\ne\varnothing$。族 $\mathcal{F}_0:=\{X^F:F\in\mathcal{P}_{\mathrm{fin}}(G)\}\subseteq\mathcal{P}(X)$ 非空且对有限交封闭（$X^{F_1}\cap X^{F_2}=X^{F_1\cup F_2}\ne\varnothing$），故具有有限交性质。由引理 0.1，存在 $\mathcal{U}\in\operatorname{Ult}(X)$ 使 $\mathcal{F}_0\subseteq\mathcal{U}$，从而对每个 $g\in G$ 有 $X^g=X^{\{g\}}\in\mathcal{U}$，即 $\Phi_{\infty,X}(\mathcal{U})\in R_\infty(X)^G\ne\varnothing$。（因 $X^F=X^{\langle F\rangle}$ 且每个有限生成子群形如 $\langle F\rangle$，两表述等价。）$\square$

---

### 2.2 $\eta_{\infty,X}(X^G)$ 的闭包、等于 $R_\infty(X)^G$ 的判准及群的完全分类

**定理 2.3：** *设 $G$ 为群，$X$ 为 $G$-集合，$\iota:X^G\hookrightarrow X$ 为包含映射。*
1. **闭包的显式刻画：** *在 $R_\infty(X)$ 中，$\eta_{\infty,X}(X^G)$ 的闭包为*
   $$\overline{\eta_{\infty,X}(X^G)}=R_\infty(\iota)\bigl(R_\infty(X^G)\bigr)=\Phi_{\infty,X}\bigl(\bigl\{\mathcal{U}\in\operatorname{Ult}(X):X^G\in\mathcal{U}\bigr\}\bigr)$$
   *（当 $X=\varnothing$ 时为 $\varnothing$；当 $X\ne\varnothing$ 时等于开闭集 $\{r\in R_\infty(X):r_2(\mathbf{1}_{X^G})=1\}$，特别地当 $X^G=\varnothing$ 时为 $\varnothing$）。*
2. **单个作用的等式判准：** *$\overline{\eta_{\infty,X}(X^G)}=R_\infty(X)^G$ **当且仅当**存在有限子集 $F\subseteq G$（等价地，存在有限生成子群 $H\le G$）使得 $X^F=X^G$。*
3. **群的完全分类：** *群 $G$ 对其每个 $G$-集合 $X$ 都满足 $\overline{\eta_{\infty,X}(X^G)}=R_\infty(X)^G$，**当且仅当 $G$ 是有限生成群**。*

**证明：**
1. 当 $X=\varnothing$ 时，两端均为 $\varnothing$。设 $X\ne\varnothing$。在同胚 $\Phi_{\infty,X}$ 下，$\eta_{\infty,X}(X^G)$ 对应 $\{\mathcal{U}_x:x\in X^G\}$，而 $R_\infty(\iota)(R_\infty(X^G))$ 对应开闭集 $V_{X^G}=\{\mathcal{U}\in\operatorname{Ult}(X):X^G\in\mathcal{U}\}$（当 $X^G=\varnothing$ 时两侧均为 $\varnothing$）。因 $V_{X^G}$ 在 $\operatorname{Ult}(X)$ 中闭且包含 $\{\mathcal{U}_x:x\in X^G\}$，故闭包包含于 $V_{X^G}$；反之，对任意 $\mathcal{U}\in V_{X^G}$ 及 $\mathcal{U}$ 的任意基本开邻域 $V_A$（即 $A\in\mathcal{U}$），由 $X^G\in\mathcal{U}$ 得 $A\cap X^G\in\mathcal{U}$，从而 $A\cap X^G\ne\varnothing$；任取 $x\in A\cap X^G$，即有 $\mathcal{U}_x\in V_A\cap\{\mathcal{U}_y:y\in X^G\}$。故 $\overline{\{\mathcal{U}_x:x\in X^G\}}=V_{X^G}$。
2. 因对一切 $g\in G$ 有 $X^G\subseteq X^g$，故 $V_{X^G}\subseteq\operatorname{Ult}_G(X)$（即 $\overline{\eta_{\infty,X}(X^G)}\subseteq R_\infty(X)^G$）恒成立。
   - （$\Leftarrow$）设存在有限子集 $F\subseteq G$ 使 $X^F=X^G$。若 $X=\varnothing$，等式显然成立；若 $X\ne\varnothing$，任取 $\mathcal{U}\in\operatorname{Ult}_G(X)$，由定理 2.2 的证明知 $X^F\in\mathcal{U}$，故 $X^G=X^F\in\mathcal{U}$，即 $\mathcal{U}\in V_{X^G}$。从而 $\overline{\eta_{\infty,X}(X^G)}=R_\infty(X)^G$。
   - （$\Rightarrow$）用反证法，设对每个 $F\in\mathcal{P}_{\mathrm{fin}}(G)$ 均有 $X^F\ne X^G$，即 $X^F\setminus X^G\ne\varnothing$（取 $F=\varnothing$ 知 $X\ne\varnothing$）。考察非空族 $\mathcal{C}:=\{X^F\setminus X^G:F\in\mathcal{P}_{\mathrm{fin}}(G)\}\subseteq\mathcal{P}(X)$。因 $(X^{F_1}\setminus X^G)\cap(X^{F_2}\setminus X^G)=X^{F_1\cup F_2}\setminus X^G\in\mathcal{C}$ 且 $\varnothing\notin\mathcal{C}$，$\mathcal{C}$ 具有有限交性质。由引理 0.1，存在 $\mathcal{U}\in\operatorname{Ult}(X)$ 使 $\mathcal{C}\subseteq\mathcal{U}$。对每个 $g\in G$，$X^g\supseteq X^{\{g\}}\setminus X^G\in\mathcal{U}$，故 $X^g\in\mathcal{U}$，即 $\mathcal{U}\in\operatorname{Ult}_G(X)$；同时 $X\setminus X^G=X^\varnothing\setminus X^G\in\mathcal{U}$，故 $X^G\notin\mathcal{U}$，即 $\mathcal{U}\notin V_{X^G}$。于是 $\overline{\eta_{\infty,X}(X^G)}\subsetneq R_\infty(X)^G$。
3. - （$\Leftarrow$）若 $G$ 有限生成，取有限生成集 $F\subseteq G$ 使 $\langle F\rangle=G$。对任意 $G$-集合 $X$ 及任意 $x\in X^F$，稳定子群 $\operatorname{Stab}_G(x)=\{g\in G:gx=x\}$ 是包含 $F$ 的 $G$ 的子群，故 $\operatorname{Stab}_G(x)\supseteq\langle F\rangle=G$，即 $x\in X^G$。因此 $X^F=X^G$ 对一切 $G$-集合 $X$ 成立，由第 2 项知等式恒成立。
   - （$\Rightarrow$）设 $G$ **不是**有限生成群。令 $\mathcal{FG}(G)\subseteq\mathcal{P}(G)$ 为 $G$ 的全体有限生成子群构成的集合（在 ZFC 中为合法集合），构造左 $G$-集合（陪集空间的不交并，每项赋予左乘作用 $g\cdot(aH)=(ga)H$）：
     $$X:=\bigsqcup_{H\in\mathcal{FG}(G)}G/H.$$
     首先计算 $X^G$：若某项中有 $aH\in(G/H)^G$，则对一切 $g\in G$ 有 $gaH=aH$，即 $a^{-1}ga\in H$，故 $G=aGa^{-1}\subseteq H$，即 $H=G$；但 $G$ 非有限生成，故 $G\notin\mathcal{FG}(G)$，矛盾！因此 $X^G=\varnothing$。
     其次，对任意有限子集 $F\subseteq G$，令 $H_F:=\langle F\rangle\in\mathcal{FG}(G)$，则在求和项 $G/H_F\subseteq X$ 中，单位陪集 $eH_F$ 对一切 $g\in F\subseteq H_F$ 满足 $g\cdot(eH_F)=gH_F=eH_F$，故 $eH_F\in X^F\ne\varnothing=X^G$。由第 2 项（或定理 2.2(2)）知 $\overline{\eta_{\infty,X}(X^G)}=\varnothing\ne R_\infty(X)^G$。$\square$

---

### 2.3 群与底集均可数的具体反例及其全部不动记录

- **具体构造：**
  取底集 $X=\mathbb{N}=\{0,1,2,\dots\}$，取群 $G=S_{\mathrm{fin}}(\mathbb{N})$ 为 $\mathbb{N}$ 上全体**有限支集置换**构成的群，即
  $$G:=\bigl\{g\in\operatorname{Sym}(\mathbb{N}):\operatorname{supp}(g):=\{k\in\mathbb{N}:g(k)\ne k\}\text{ 为有限集}\bigr\},$$
  赋予自然左作用 $g\cdot k=g(k)$。
  - **群结构与可数性：** $\operatorname{supp}(\mathrm{id})=\varnothing$，$\operatorname{supp}(g^{-1})=\operatorname{supp}(g)$，$\operatorname{supp}(gh)\subseteq\operatorname{supp}(g)\cup\operatorname{supp}(h)$，故 $G\le\operatorname{Sym}(\mathbb{N})$ 为子群。对每个 $N\ge 1$，$G_N:=\{g\in G:\operatorname{supp}(g)\subseteq[N]\}\cong\operatorname{Sym}([N])$ 为基数 $N!$ 的有限集，而 $G=\bigcup_{N=1}^\infty G_N$ 为可数个有限集之并，故 $G$ 与 $X=\mathbb{N}$ 均为可数无限集。
  - **$X^G=\varnothing$：** 对任意 $k\in\mathbb{N}$，对换 $\tau_k=(k,\;k+1)\in G$（支集为 $\{k,k+1\}$）满足 $\tau_k(k)=k+1\ne k$，故 $X^G=\varnothing$。
  - **$R_\infty(\mathbb{N})^G\ne\varnothing$：** 对任意有限子集 $F\subseteq G$，$\bigcup_{g\in F}\operatorname{supp}(g)$ 仍为 $\mathbb{N}$ 的有限子集，而 $\mathbb{N}$ 无限，故 $\mathbb{N}^F=\mathbb{N}\setminus\bigcup_{g\in F}\operatorname{supp}(g)\ne\varnothing$。由定理 2.2(2) 知 $R_\infty(\mathbb{N})^G\ne\varnothing$。

- **全部不动记录的完整描述：**
  记 $\operatorname{Ult}_{\mathrm{free}}(\mathbb{N}):=\operatorname{Ult}(\mathbb{N})\setminus\{\mathcal{U}_k:k\in\mathbb{N}\}$ 为 $\mathbb{N}$ 上全体**非主（自由）超滤子**（即包含余有限滤子 $\mathcal{F}_{\mathrm{cof}}:=\{A\subseteq\mathbb{N}:\mathbb{N}\setminus A\text{ 有限}\}$ 的全部超滤子）的集合。我们断言：
  $$R_\infty(\mathbb{N})^G=\Phi_{\infty,\mathbb{N}}\bigl(\operatorname{Ult}_{\mathrm{free}}(\mathbb{N})\bigr)=R_\infty(\mathbb{N})\setminus\eta_{\infty,\mathbb{N}}(\mathbb{N})$$
  （作为拓扑空间同胚于 Stone–Čech 剩余 $\beta\mathbb{N}\setminus\mathbb{N}$）。
  **证明：** 由定理 2.2(1)，$\mathcal{U}\in\operatorname{Ult}_G(\mathbb{N})\iff\forall g\in G,\;\mathbb{N}\setminus\operatorname{supp}(g)\in\mathcal{U}$。
  - 若 $\mathcal{U}\in\operatorname{Ult}_{\mathrm{free}}(\mathbb{N})$，则 $\mathcal{U}$ 不含任何有限集，故对一切 $g\in G$ 均有余有限集 $\mathbb{N}\setminus\operatorname{supp}(g)\in\mathcal{U}$，即 $\mathcal{U}\in\operatorname{Ult}_G(\mathbb{N})$；
  - 反之，若 $\mathcal{U}\in\operatorname{Ult}_G(\mathbb{N})$，对每个 $k\in\mathbb{N}$ 取对换 $\tau_k=(k,\;k+1)\in G$，则 $\mathbb{N}^{\tau_k}=\mathbb{N}\setminus\{k,k+1\}\in\mathcal{U}$，故 $\{k\}\notin\mathcal{U}$，从而 $\mathcal{U}$ 不等于任何主超滤子 $\mathcal{U}_k$，即 $\mathcal{U}\in\operatorname{Ult}_{\mathrm{free}}(\mathbb{N})$。

  写成显式记录族：$R_\infty(\mathbb{N})^G$ 的全体元素恰为形如 $r^{\mathcal{U}}=(r_n^{\mathcal{U}})_{n\ge 0}$（$\mathcal{U}\in\operatorname{Ult}_{\mathrm{free}}(\mathbb{N})$）的族，其中 $r_0^{\mathcal{U}}=\mathrm{id}_\varnothing$，且对 $n\ge 1$ 及 $f:\mathbb{N}\to[n]$，$r_n^{\mathcal{U}}(f)$ 是使 $f^{-1}(\{j\})\in\mathcal{U}$ 的唯一 $j\in[n]$（特别地，凡在余有限集上恒取常值 $j$ 的测试 $f$ 均满足 $r_n^{\mathcal{U}}(f)=j$）。

---

## 3. 乘积比较

设 $(X_i)_{i\in I}$ 为一族左 $G$-集合，记乘积 $P:=\prod_{i\in I}X_i$（赋予对角作用），各坐标投射为 $p_i:P\to X_i$（$i\in I$），右边乘积 $\prod_{i\in I}R_\infty(X_i)^G$ 赋予乘积拓扑。

### 3.1 $\Pi_{(X_i)}$ 的良定义与连续性

1. **空指标族情形（$I=\varnothing$）：**
   依约定，$P=\prod_{i\in\varnothing}X_i=\{\star\}$ 为单点集（带唯一平凡 $G$-作用），陪域 $\prod_{i\in\varnothing}R_\infty(X_i)^G=\{\star'\}$ 亦为单点拓扑空间。由定理 1.2(3)，$R_\infty(\{\star\})^G=\{\eta_{\infty,\{\star\}}(\star)\}$ 也是单点集，$\Pi_\varnothing$ 将该唯一元素映为空族 $\star'$，是单点空间之间的良定义同胚（连续双射）。
2. **一般指标族（$I\ne\varnothing$）：**
   - **良定义：** 对每个 $i\in I$、$g\in G$ 与 $x=(x_j)_{j\in I}\in P$，对角作用满足 $p_i(g\cdot x)=(g\cdot x)_i=g\cdot x_i=g\cdot p_i(x)$，即 $p_i\circ g_P=g_{X_i}\circ p_i$（这在某个 $X_{i_0}=\varnothing$ 从而 $P=\varnothing$ 时作为空映射等式同样成立）。对任意 $r\in R_\infty(P)^G$ 及 $i\in I$，由 $R_\infty$ 的函子性得
     $$g\cdot\bigl(R_\infty(p_i)r\bigr)=R_\infty(g_{X_i}\circ p_i)r=R_\infty(p_i\circ g_P)r=R_\infty(p_i)(g\cdot r)=R_\infty(p_i)r,$$
     故 $R_\infty(p_i)r\in R_\infty(X_i)^G$，从而 $\Pi_{(X_i)}(r)=(R_\infty(p_i)r)_{i\in I}\in\prod_{i\in I}R_\infty(X_i)^G$ 良定义（若存在 $i_0\in I$ 使 $X_{i_0}=\varnothing$，则 $P=\varnothing$，定义域与陪域同为 $\varnothing$，$\Pi_{(X_i)}:\varnothing\to\varnothing$ 为良定义空映射）。
   - **连续性：** 对任意集合映射 $h:Z\to W$，$R_\infty(h):R_\infty(Z)\to R_\infty(W)$ 恒连续：因为 $R_\infty(W)$ 取全部观察 $\operatorname{ev}_{n,f}:s\mapsto s_n(f)$（$n\ge 0,f:W\to[n]$）生成的最弱拓扑，而复合映射 $(\operatorname{ev}_{n,f}\circ R_\infty(h))(r)=r_n(f\circ h)=\operatorname{ev}_{n,f\circ h}(r)$ 恰为 $R_\infty(Z)$ 的一个生成连续观察。对每个 $i\in I$，将连续映射 $R_\infty(p_i):R_\infty(P)\to R_\infty(X_i)$ 限制于子空间 $R_\infty(P)^G$ 并将陪域缩至子空间 $R_\infty(X_i)^G$ 仍连续；由乘积拓扑的泛性质知 $\Pi_{(X_i)}$ 连续。

---

### 3.2 $\Pi_{(X_i)}$ 是否总为满射的判定与证明

**结论：是。** *对任意群 $G$ 及任意集合指标族 $(X_i)_{i\in I}$，$\Pi_{(X_i)}:R_\infty\!\left(\prod_{i\in I}X_i\right)^G\to\prod_{i\in I}R_\infty(X_i)^G$ **恒为满射**。*

**证明：**
- 若 $I=\varnothing$，3.1 已证 $\Pi_\varnothing$ 为单点集间的双射，自然为满射。
- 若陪域 $\prod_{i\in I}R_\infty(X_i)^G=\varnothing$（含某个 $X_{i_0}=\varnothing$ 或某个 $R_\infty(X_{i_0})^G=\varnothing$ 的情形），因 $\Pi_{(X_i)}$ 为到 $\varnothing$ 的良定义映射，定义域 $R_\infty(P)^G$ 必为 $\varnothing$，空映射 $\varnothing\to\varnothing$ 为满射。
- 现设 $I\ne\varnothing$ 且陪域非空，任取一族不动记录 $(r^{(i)})_{i\in I}\in\prod_{i\in I}R_\infty(X_i)^G$。对每个 $i\in I$，必有 $X_i\ne\varnothing$（否则 $R_\infty(X_i)^G=\varnothing$），记 $\mathcal{U}_i:=\Phi_{\infty,X_i}^{-1}(r^{(i)})\in\operatorname{Ult}_G(X_i)$。由选择公理（ZFC），$P=\prod_{i\in I}X_i\ne\varnothing$。
  注意在对角作用下，对任意有限子集 $F\subseteq G$，不动点集满足
  $$P^F=\Bigl(\prod_{i\in I}X_i\Bigr)^F=\prod_{i\in I}(X_i^F).$$
  在 $P$ 上考察非空子集族
  $$\mathcal{E}:=\bigl\{P^F:F\in\mathcal{P}_{\mathrm{fin}}(G)\bigr\}\cup\bigl\{p_i^{-1}(A):i\in I,\;A\in\mathcal{U}_i\bigr\}\subseteq\mathcal{P}(P)$$
  （因 $\varnothing\in\mathcal{P}_{\mathrm{fin}}(G)$，故 $\mathcal{E}\ne\varnothing$）。我们来验证 $\mathcal{E}$ 具有有限交性质：
  任取 $\mathcal{E}$ 的有限非空子族，将其中的第一类集合合并为 $P^{F_1}\cap\dots\cap P^{F_a}=P^F$（其中 $F=F_1\cup\dots\cup F_a\in\mathcal{P}_{\mathrm{fin}}(G)$；若 $a=0$ 则取 $F=\varnothing$），将第二类集合按相同坐标指标 $j\in J$（$J\subseteq I$ 为有限子集）合并：对每个 $j\in J$，有限个属于 $\mathcal{U}_j$ 的集合之交 $B_j$ 仍属于 $\mathcal{U}_j$，且对应的原像之交为 $p_j^{-1}(B_j)$。于是该有限交等于
  $$P^F\cap\bigcap_{j\in J}p_j^{-1}(B_j)=\prod_{j\in J}(X_j^F\cap B_j)\times\prod_{i\in I\setminus J}X_i^F.$$
  因每个 $\mathcal{U}_i\in\operatorname{Ult}_G(X_i)$，由定理 2.2 知对一切 $i\in I$ 有 $X_i^F\in\mathcal{U}_i$（故 $X_i^F\ne\varnothing$），且对每个 $j\in J$ 有 $X_j^F\cap B_j\in\mathcal{U}_j$（故 $X_j^F\cap B_j\ne\varnothing$）。在 ZFC 中由选择公理，一族非空集合的笛卡尔积非空，故上述有限交非空！
  由引理 0.1，存在 $\mathcal{W}\in\operatorname{Ult}(P)$ 使 $\mathcal{E}\subseteq\mathcal{W}$。
  - 对每个 $g\in G$，$P^g=P^{\{g\}}\in\mathcal{E}\subseteq\mathcal{W}$，由定理 2.2(1) 知 $r:=\Phi_{\infty,P}(\mathcal{W})\in R_\infty(P)^G$；
  - 对每个 $i\in I$ 及任意 $A\in\mathcal{U}_i$，有 $p_i^{-1}(A)\in\mathcal{E}\subseteq\mathcal{W}$，即 $A\in(p_i)_*(\mathcal{W})$。于是 $\mathcal{U}_i\subseteq(p_i)_*(\mathcal{W})$；因二者皆为 $X_i$ 上的超滤子，若 $C\notin\mathcal{U}_i$ 则 $X_i\setminus C\in\mathcal{U}_i\subseteq(p_i)_*(\mathcal{W})$ 从而 $C\notin(p_i)_*(\mathcal{W})$，故 $(p_i)_*(\mathcal{W})=\mathcal{U}_i$。

  因此对一切 $i\in I$ 有 $R_\infty(p_i)r=\Phi_{\infty,X_i}((p_i)_*(\mathcal{W}))=\Phi_{\infty,X_i}(\mathcal{U}_i)=r^{(i)}$，即 $\Pi_{(X_i)}(r)=(r^{(i)})_{i\in I}$。$\square$

---

### 3.3 平凡群情形两集合比较映射为单射的充要条件

设 $G=\{e\}$ 为平凡群（此时对任何集合 $Z$ 有 $R_\infty(Z)^G=R_\infty(Z)$）。

**定理 3.1：** *对平凡群及任意集合 $X,Y$，比较映射 $\Pi_{(X,Y)}:R_\infty(X\times Y)\to R_\infty(X)\times R_\infty(Y)$ 为单射**当且仅当 $X$ 与 $Y$ 中至少有一个是有限集**（含空集 $\varnothing$）。*

**证明：**
- **充分性（$\Leftarrow$）：** 不妨设 $X$ 有限（$Y$ 有限的情形由交换两因子对称即得）。
  - 若 $X=\varnothing$ 或 $Y=\varnothing$，则 $X\times Y=\varnothing$，$R_\infty(X\times Y)=\varnothing$，空映射显然为单射。
  - 若 $X\ne\varnothing$ 有限且 $Y\ne\varnothing$，经 $\Phi_{\infty,-}$ 等同于证明 $\operatorname{Ult}(X\times Y)\to\operatorname{Ult}(X)\times\operatorname{Ult}(Y),\;\mathcal{W}\mapsto((p_X)_*\mathcal{W},(p_Y)_*\mathcal{W})$ 为单射。任取 $\mathcal{W}\in\operatorname{Ult}(X\times Y)$，记 $\mathcal{U}=(p_X)_*\mathcal{W}$，$\mathcal{V}=(p_Y)_*\mathcal{W}$。因 $X$ 有限，$X$ 上超滤子必为主超滤子，故存在唯一 $x_0\in X$ 使 $\mathcal{U}=\mathcal{U}_{x_0}$。由 $\{x_0\}\in(p_X)_*\mathcal{W}$ 得 $\{x_0\}\times Y=p_X^{-1}(\{x_0\})\in\mathcal{W}$。现对任意子集 $S\subseteq X\times Y$，记截面 $S_{x_0}:=\{y\in Y:(x_0,y)\in S\}$，则
    $$S\cap(\{x_0\}\times Y)=\{x_0\}\times S_{x_0}=(X\times S_{x_0})\cap(\{x_0\}\times Y)=p_Y^{-1}(S_{x_0})\cap(\{x_0\}\times Y).$$
    因 $\{x_0\}\times Y\in\mathcal{W}$，故
    $$S\in\mathcal{W}\iff S\cap(\{x_0\}\times Y)\in\mathcal{W}\iff p_Y^{-1}(S_{x_0})\cap(\{x_0\}\times Y)\in\mathcal{W}\iff p_Y^{-1}(S_{x_0})\in\mathcal{W}\iff S_{x_0}\in\mathcal{V}.$$
    可见 $\mathcal{W}$ 由 $(\mathcal{U},\mathcal{V})$ 唯一确定，故 $\Pi_{(X,Y)}$ 为单射。

- **必要性（$\Rightarrow$）：** 设 $X$ 与 $Y$ **均为无限集**，我们来构造 $\operatorname{Ult}(X\times Y)$ 中两个不同元素使其在 $X,Y$ 上的边缘推前完全相同。
  在 ZFC 中，无限集必含可数无限子集，故存在单射 $\alpha:\mathbb{N}\hookrightarrow X$ 与 $\beta:\mathbb{N}\hookrightarrow Y$。先在 $\mathbb{N}$ 上取一个自由超滤子 $\mathcal{U}\in\operatorname{Ult}_{\mathrm{free}}(\mathbb{N})$（对余有限滤子应用引理 0.1 即得），在 $\mathbb{N}\times\mathbb{N}$ 上定义迭代超滤子 $\mathcal{W}_1$ 与对换像 $\mathcal{W}_2:=\tau_*(\mathcal{W}_1)$（其中 $\tau(m,n)=(n,m)$）：对 $S\subseteq\mathbb{N}\times\mathbb{N}$，记行截面 $S_m:=\{n\in\mathbb{N}:(m,n)\in S\}$，令
  $$S\in\mathcal{W}_1\iff\bigl\{m\in\mathbb{N}:S_m\in\mathcal{U}\bigr\}\in\mathcal{U}.$$
  1. **$\mathcal{W}_1\in\operatorname{Ult}(\mathbb{N}\times\mathbb{N})$（从而 $\mathcal{W}_2\in\operatorname{Ult}(\mathbb{N}\times\mathbb{N})$）：** $\varnothing_m=\varnothing\notin\mathcal{U}\implies\varnothing\notin\mathcal{W}_1$；$(\mathbb{N}^2)_m=\mathbb{N}\in\mathcal{U}\implies\mathbb{N}^2\in\mathcal{W}_1$；向上封闭显然；由 $(S\cap T)_m=S_m\cap T_m$ 知 $\{m:(S\cap T)_m\in\mathcal{U}\}=\{m:S_m\in\mathcal{U}\}\cap\{m:T_m\in\mathcal{U}\}$；由 $(\mathbb{N}^2\setminus S)_m=\mathbb{N}\setminus S_m$ 知 $\{m:(\mathbb{N}^2\setminus S)_m\in\mathcal{U}\}=\mathbb{N}\setminus\{m:S_m\in\mathcal{U}\}$，故满足 (U1)–(U4)。
  2. **边缘推前相等：** 设 $p_1,p_2:\mathbb{N}\times\mathbb{N}\to\mathbb{N}$ 为两坐标投射。对任意 $A\subseteq\mathbb{N}$，$(p_1^{-1}(A))_m$ 在 $m\in A$ 时为 $\mathbb{N}\in\mathcal{U}$、在 $m\notin A$ 时为 $\varnothing\notin\mathcal{U}$，故 $\{m:(p_1^{-1}(A))_m\in\mathcal{U}\}=A$，从而 $(p_1)_*\mathcal{W}_1=\mathcal{U}$；对任意 $B\subseteq\mathbb{N}$，$(p_2^{-1}(B))_m=B$ 对一切 $m$ 成立，故 $\{m:B\in\mathcal{U}\}$ 在 $B\in\mathcal{U}$ 时为 $\mathbb{N}\in\mathcal{U}$、在 $B\notin\mathcal{U}$ 时为 $\varnothing\notin\mathcal{U}$，从而 $(p_2)_*\mathcal{W}_1=\mathcal{U}$。于是 $(p_1)_*\mathcal{W}_2=(p_2\circ\tau)_*\mathcal{W}_1=\mathcal{U}=(p_1)_*\mathcal{W}_1$，且 $(p_2)_*\mathcal{W}_2=(p_1\circ\tau)_*\mathcal{W}_1=\mathcal{U}=(p_2)_*\mathcal{W}_1$。
  3. **$\mathcal{W}_1\ne\mathcal{W}_2$：** 考察严格上三角集 $T:=\{(m,n)\in\mathbb{N}\times\mathbb{N}:m<n\}$。对每个 $m\in\mathbb{N}$，$T_m=\{n\in\mathbb{N}:n>m\}$ 在 $\mathbb{N}$ 中余有限，因 $\mathcal{U}$ 为自由超滤子，故 $T_m\in\mathcal{U}$ 恒成立，从而 $\{m:T_m\in\mathcal{U}\}=\mathbb{N}\in\mathcal{U}$，得 **$T\in\mathcal{W}_1$**；另一方面，对每个 $n\in\mathbb{N}$，$(\tau^{-1}(T))_n=\{m\in\mathbb{N}:m<n\}=[n]$ 为有限集，故 $[n]\notin\mathcal{U}$ 恒成立，从而 $\{n:(\tau^{-1}(T))_n\in\mathcal{U}\}=\varnothing\notin\mathcal{U}$，得 **$T\notin\mathcal{W}_2$**。因此 $\mathcal{W}_1\ne\mathcal{W}_2$。

  最后令 $\widetilde{\mathcal{W}}_k:=(\alpha\times\beta)_*(\mathcal{W}_k)\in\operatorname{Ult}(X\times Y)$（$k=1,2$）。因 $\alpha\times\beta$ 为单射，$(\alpha\times\beta)^{-1}((\alpha\times\beta)(T))=T$，故 $(\alpha\times\beta)(T)$ 属于 $\widetilde{\mathcal{W}}_1$ 而不属于 $\widetilde{\mathcal{W}}_2$，即 $\widetilde{\mathcal{W}}_1\ne\widetilde{\mathcal{W}}_2$；同时 $(p_X)_*\widetilde{\mathcal{W}}_1=\alpha_*((p_1)_*\mathcal{W}_1)=\alpha_*(\mathcal{U})=(p_X)_*\widetilde{\mathcal{W}}_2$，同理 $(p_Y)_*\widetilde{\mathcal{W}}_1=\beta_*(\mathcal{U})=(p_Y)_*\widetilde{\mathcal{W}}_2$。故 $\Pi_{(X,Y)}$ 不是单射。$\square$

---

### 3.4 任意群作用下两个全称命题的判定与证明

#### 命题一：“对任意群作用，若 $X,Y$ 至少一个有限，则两因子的比较映射 $\Pi_{(X,Y)}:R_\infty(X\times Y)^G\to R_\infty(X)^G\times R_\infty(Y)^G$ 为双射。”

**判定：该全称命题成立（为真）。**

**证明：**
1. **满射性：** 已由 3.2 节对任意群和任意指标族普遍证明，特化到二元指标族即知 $\Pi_{(X,Y)}$ 为满射。
2. **单射性：** 注意有包含映射下的交换图表
   $$\begin{array}{ccc}
   R_\infty(X\times Y)^G & \xrightarrow{\;\Pi_{(X,Y)}\;} & R_\infty(X)^G\times R_\infty(Y)^G \\
   \downarrow & & \downarrow \\
   R_\infty(X\times Y) & \xrightarrow{\;\Pi_{(X,Y)}^{\{e\}}\;} & R_\infty(X)\times R_\infty(Y)
   \end{array}$$
   其中底行即为忘记群作用（视为平凡群作用）时的比较映射 $\Pi_{(X,Y)}^{\{e\}}$，两竖直箭头为子集包含（单射）。当 $X,Y$ 至少一个有限时，由定理 3.1 知底行 $\Pi_{(X,Y)}^{\{e\}}$ 为单射，从而复合映射 $\Pi_{(X,Y)}^{\{e\}}\big|_{R_\infty(X\times Y)^G}$ 为单射，故顶行 $\Pi_{(X,Y)}$ 亦必为单射。

既单且满，故 $\Pi_{(X,Y)}$ 为双射。（注：由紧 Hausdorff 空间到 Hausdorff 空间的连续双射必为同胚，或当 $X$ 有限时直接由显式逆映射 $(\eta_{\infty,X}(x_0),s)\mapsto R_\infty(y\mapsto(x_0,y))(s)$（$x_0\in X^G$），知其实际上还是拓扑同胚。）$\square$

---

#### 命题二：“对任意群作用，若 $X^G=Y^G=\varnothing$，则两因子的比较映射 $\Pi_{(X,Y)}:R_\infty(X\times Y)^G\to R_\infty(X)^G\times R_\infty(Y)^G$ 为单射。”

**判定：该全称命题不成立（为假）。**

**反例与证明：**
取 2.3 节中的群 $G=S_{\mathrm{fin}}(\mathbb{N})$，令 $X=\mathbb{N}$ 与 $Y=\mathbb{N}$ 均赋予 $G$ 的自然置换作用。
1. **核验条件 $X^G=Y^G=\varnothing$：** 已在 2.3 节证得 $\mathbb{N}^{S_{\mathrm{fin}}(\mathbb{N})}=\varnothing$，故 $X^G=Y^G=\varnothing$。
2. **构造不同原像：** 取自由超滤子 $\mathcal{U}\in\operatorname{Ult}_{\mathrm{free}}(\mathbb{N})$，并取定理 3.1 证明中构造的 $\mathcal{W}_1,\mathcal{W}_2\in\operatorname{Ult}(\mathbb{N}\times\mathbb{N})$。我们已知 $\mathcal{W}_1\ne\mathcal{W}_2$，且 $(p_1)_*\mathcal{W}_k=(p_2)_*\mathcal{W}_k=\mathcal{U}$（$k=1,2$）。
   现在核验对每个 $k\in\{1,2\}$ 均有 $\mathcal{W}_k\in\operatorname{Ult}_G(\mathbb{N}\times\mathbb{N})$：任取 $g\in G=S_{\mathrm{fin}}(\mathbb{N})$，其支集 $E:=\operatorname{supp}(g)$ 为 $\mathbb{N}$ 的有限子集。在对角作用 $g\cdot(m,n)=(g(m),g(n))$ 下，不动点集为
   $$(\mathbb{N}\times\mathbb{N})^g=\mathbb{N}^g\times\mathbb{N}^g=(\mathbb{N}\setminus E)\times(\mathbb{N}\setminus E)=p_1^{-1}(\mathbb{N}\setminus E)\cap p_2^{-1}(\mathbb{N}\setminus E).$$
   因 $\mathbb{N}\setminus E$ 在 $\mathbb{N}$ 中余有限且 $\mathcal{U}$ 为自由超滤子，故 $\mathbb{N}\setminus E\in\mathcal{U}=(p_1)_*\mathcal{W}_k=(p_2)_*\mathcal{W}_k$，即 $p_1^{-1}(\mathbb{N}\setminus E)\in\mathcal{W}_k$ 且 $p_2^{-1}(\mathbb{N}\setminus E)\in\mathcal{W}_k$，由滤子交封闭得 $(\mathbb{N}\times\mathbb{N})^g\in\mathcal{W}_k$。因 $g\in G$ 任意，由定理 2.2(1) 得
   $$r^{(1)}:=\Phi_{\infty,\mathbb{N}\times\mathbb{N}}(\mathcal{W}_1)\in R_\infty(\mathbb{N}\times\mathbb{N})^G,\qquad r^{(2)}:=\Phi_{\infty,\mathbb{N}\times\mathbb{N}}(\mathcal{W}_2)\in R_\infty(\mathbb{N}\times\mathbb{N})^G.$$
   由 $\mathcal{W}_1\ne\mathcal{W}_2$ 及 $\Phi_{\infty,\mathbb{N}\times\mathbb{N}}$ 为双射知 $r^{(1)}\ne r^{(2)}$；然而
   $$\Pi_{(\mathbb{N},\mathbb{N})}(r^{(1)})=\bigl(\Phi_{\infty,\mathbb{N}}(\mathcal{U}),\Phi_{\infty,\mathbb{N}}(\mathcal{U})\bigr)=\Pi_{(\mathbb{N},\mathbb{N})}(r^{(2)})$$
   （事实上，沿 $G$-等变对角嵌入 $\Delta:\mathbb{N}\to\mathbb{N}\times\mathbb{N},\;n\mapsto(n,n)$ 推前所得的 $r^{(\Delta)}:=\Phi_{\infty,\mathbb{N}\times\mathbb{N}}(\Delta_*\mathcal{U})\in R_\infty(\mathbb{N}\times\mathbb{N})^G$ 也具有完全相同的像，且三者分别支在对角线 $\{m=n\}$、严格上三角 $\{m<n\}$ 与严格下三角 $\{m>n\}$ 上，两两互异）。故 $\Pi_{(X,Y)}$ 不是单射，该全称命题不成立。$\square$
