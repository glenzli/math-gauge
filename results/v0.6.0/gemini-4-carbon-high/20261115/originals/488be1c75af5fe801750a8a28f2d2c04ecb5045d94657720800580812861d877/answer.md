以下按 S1–S6 逐项给出证明、构造、判定与分类。全文约定：有限抽象单纯复形 $K$ 指由非空有限集合（单形）构成的有限族，且对非空子集封闭；其顶点集记为 $V(K)=\bigcup_{\sigma\in K}\sigma$，标准几何实现 $|K|\subseteq\mathbb{R}^{V(K)}$ 由全体形式凸组合 $\sum_{w\in V(K)}x_w e_w$（满足 $\{w:x_w>0\}\in K$）赋予欧氏子空间拓扑（因 $K$ 有限，这与 CW 弱拓扑一致且紧致 Hausdorff）。对非空空间 $Z$，非约化锥记为 $CZ=(Z\times[0,1])/(Z\times\{1\})$（将 $Z$ 等同于底面 $Z\times\{0\}$），非约化悬挂记为 $\Sigma Z=(Z\times[0,1])/(Z\times\{0\},Z\times\{1\})$（两个极点分别记为南极 $s_-=[Z\times\{0\}]$ 与北极 $s_+=[Z\times\{1\}]$）。

---

## S1 可缩子复形的商

### 1. 有限 CW 复形的紧致 Hausdorff 性质与同伦延拓性质（HEP）

**引理 1.1（紧致 Hausdorff 商空间）**  
设 $X$ 为紧致 Hausdorff 空间，$B\subseteq X$ 为非空闭子集，则商空间 $X/B$ 仍为紧致 Hausdorff 空间。

*证明*：$X/B$ 为紧致空间的连续满射像，故紧致。对 $X/B$ 中任意相异两点 $z_1\neq z_2$，因其原像 $q^{-1}(z_1),q^{-1}(z_2)$ 是紧致 Hausdorff（从而正规）空间 $X$ 中不相交的非空闭集，存在 $X$ 中不相交开集 $U_1\supseteq q^{-1}(z_1)$ 与 $U_2\supseteq q^{-1}(z_2)$。由于 $q^{-1}(z_i)$ 非为单点集即为整个 $B$，把每个不包裹 $B$ 的 $U_i$ 替换为 $U_i\setminus B$ 后仍为包含 $q^{-1}(z_i)$ 的饱和开集，其在 $X/B$ 中的像即为分离 $z_1,z_2$ 的不相交开邻域。$\square$

由于 $Y$ 为**有限** CW 复形，$Y$ 由定义是 Hausdorff 空间，且为有限个紧致闭胞腔特征映射像的并，因此 $Y$ 是紧致 Hausdorff 空间；子复形 $A\subseteq Y$ 在 $Y$ 中闭，故由引理 1.1，$Y/A$ 也是紧致 Hausdorff 空间。

**引理 1.2（有限 CW 偶的强形变收缩与同伦延拓性质）**  
对任意有限 CW 偶 $(M,A)$（$A\subseteq M$ 为子复形），子空间 $N_0=(M\times\{0\})\cup(A\times[0,1])$ 是 $M\times[0,1]$ 的强形变收缩核；特别地，$(M,A)$ 满足同伦延拓性质（HEP）：对任意空间 $Z$、连续映射 $f_0:M\to Z$ 及满足 $h(-,0)=f_0|_A$ 的同伦 $h:A\times[0,1]\to Z$，存在同伦 $H:M\times[0,1]\to Z$ 使 $H(-,0)=f_0$ 且 $H|_{A\times[0,1]}=h$。

*证明*：先对单胞腔偶 $(D^n,S^{n-1})$（$n\ge 0$，$n=0$ 时 $D^0=\{0\},S^{-1}=\varnothing$）构造显式收缩。将 $D^n\times[0,1]\subseteq\mathbb{R}^n\times\mathbb{R}$ 从点 $(0,2)$ 向 $(D^n\times\{0\})\cup(S^{n-1}\times[0,1])$ 作径向投射：令
$$s(x,t)=\min\!\left(\frac{2}{2-t},\,\frac{1}{\|x\|}\right)\in[1,2]\qquad(\text{当 }x=0\text{ 时取 }\tfrac{1}{\|x\|}=+\infty),$$
则 $r(x,t)=\bigl(s(x,t)x,\,2+s(x,t)(t-2)\bigr)$ 连续，把 $D^n\times[0,1]$ 映入 $(D^n\times\{0\})\cup(S^{n-1}\times[0,1])$，且在其上逐点为恒等映射。因 $D^n\times[0,1]$ 在 $\mathbb{R}^{n+1}$ 中凸，线性同伦 $G((x,t),\tau)=(1-\tau)(x,t)+\tau r(x,t)$（$\tau\in[0,1]$）给出 $D^n\times[0,1]$ 到 $(D^n\times\{0\})\cup(S^{n-1}\times[0,1])$ 的强形变收缩。

由于 $(M,A)$ 为有限 CW 偶，$M\setminus A$ 仅含有限个胞腔，可按维数不降序逐个附着得到滤过 $A=M_0\subseteq M_1\subseteq\cdots\subseteq M_m=M$，其中 $M_k=M_{k-1}\cup_{\varphi_k}D^{n_k}$。记粘合商映射为 $p_k:M_{k-1}\sqcup D^{n_k}\to M_k$。因 $(M_{k-1}\sqcup D^{n_k})\times[0,1]\times[0,1]$ 紧致而 $M_k\times[0,1]\times[0,1]$ Hausdorff，连续满射 $p_k\times\operatorname{id}_{[0,1]^2}$ 是闭映射从而是商映射。在 $D^{n_k}\times[0,1]$ 上用 $G$、在 $M_{k-1}\times[0,1]$ 上用常值恒等同伦，两者在 $S^{n_k-1}\times[0,1]$ 上逐点吻合，故下降为 $M_k\times[0,1]$ 到 $(M_k\times\{0\})\cup(M_{k-1}\times[0,1])$ 的强形变收缩。将 $k=m,m-1,\dots,1$ 的这 $m$ 个强形变收缩依次复合，即得 $M\times[0,1]$ 到 $N_0$ 的强形变收缩 $\Phi:(M\times[0,1])\times[0,1]\to M\times[0,1]$（记收缩映射 $\rho(x,t)=\Phi((x,t),1):M\times[0,1]\to N_0$）。给定 $f_0$ 与 $h$，由于 $M\times\{0\}$ 与 $A\times[0,1]$ 均为紧致空间 $N_0$ 的闭子集且 $f_0,h$ 在交集 $A\times\{0\}$ 上一致，由闭集粘合引理得连续映射 $F_0:N_0\to Z$，令 $H=F_0\circ\rho:M\times[0,1]\to Z$ 即满足 HEP。$\square$

### 2. 证明 $q:Y\to Y/A$ 是同伦等价，并说明同伦为何下降到商

1. **构造同伦逆 $g:Y/A\to Y$**：  
   因 $A$ 非空可缩，取定 $a_0\in A$，存在 $A$ 内部的收缩同伦 $h:A\times[0,1]\to A$，满足对任意 $a\in A$ 有 $h(a,0)=a$ 及 $h(a,1)=a_0$。记包含映射 $i:A\hookrightarrow Y$。对有限 CW 偶 $(Y,A)$、恒等映射 $\operatorname{id}_Y:Y\to Y$ 与同伦 $i\circ h:A\times[0,1]\to Y$ 应用引理 1.2（HEP），得连续同伦 $H:Y\times[0,1]\to Y$ 满足：
   $$H(y,0)=y\quad(\forall y\in Y),\qquad H(a,t)=h(a,t)\in A\quad(\forall a\in A,\;\forall t\in[0,1]).$$
   令 $f_1(y)=H(y,1):Y\to Y$。对任意 $a\in A$，有 $f_1(a)=h(a,1)=a_0$，故 $f_1$ 在商映射 $q:Y\to Y/A$ 的每条纤维上取常值。由商拓扑的泛性质，存在唯一连续映射 $g:Y/A\to Y$ 使得 $g\circ q=f_1$。

2. **验证 $g\circ q\simeq\operatorname{id}_Y$**：  
   同伦 $H:Y\times[0,1]\to Y$ 满足 $H(-,0)=\operatorname{id}_Y$ 且 $H(-,1)=f_1=g\circ q$，故 $\operatorname{id}_Y\simeq g\circ q$。

3. **验证 $q\circ g\simeq\operatorname{id}_{Y/A}$ 并说明同伦为何能下降到商**：  
   考虑连续映射 $q\circ H:Y\times[0,1]\to Y/A$。要使它下降为连续同伦 $\overline{H}:(Y/A)\times[0,1]\to Y/A$，必须同时满足**集合论（纤维相容性）**与**点集拓扑（乘积商映射）**两方面的条件：
   - **纤维相容性**：由于 $H$ 由 $A$ 自身内部的收缩同伦 $h:A\times[0,1]\to A$ 经 HEP 延拓而来，在**所有中间时刻** $t\in[0,1]$ 均有 $H(A\times\{t\})\subseteq A$（而不仅是 $t=1$ 时落入 $A$）。因此对任意 $t\in[0,1]$ 与 $a\in A$，$(q\circ H)(a,t)=[A]$，即 $q\circ H$ 在映射 $q\times\operatorname{id}_{[0,1]}:Y\times[0,1]\to(Y/A)\times[0,1]$ 的每条纤维上恒为常值，从而在集合论上唯一诱导映射 $\overline{H}:(Y/A)\times[0,1]\to Y/A$ 满足 $\overline{H}\circ(q\times\operatorname{id}_{[0,1]})=q\circ H$。
   - **拓扑连续性（乘积仍是商映射）**：一般拓扑中商映射与另一空间的乘积未必仍是商映射，但此处 $q\times\operatorname{id}_{[0,1]}$ **确为商映射**，可由以下任一标准定理严格保证：
     1. *紧致到 Hausdorff 准则（利用 $Y$ 的有限性）*：前已证 $Y$ 与 $Y/A$ 均为紧致 Hausdorff 空间，故 $Y\times[0,1]$ 紧致且 $(Y/A)\times[0,1]$ Hausdorff；连续满射 $q\times\operatorname{id}_{[0,1]}$ 必为闭映射，从而是商映射。
     2. *Whitehead 局部紧商引理*：对任意商映射 $q$ 及局部紧 Hausdorff 空间 $I$，$q\times\operatorname{id}_I$ 仍为商映射；此处 $I=[0,1]$ 紧致 Hausdorff，自然局部紧 Hausdorff，满足全部适用条件。

   由商映射 $q\times\operatorname{id}_{[0,1]}$ 的泛性质，$\overline{H}:(Y/A)\times[0,1]\to Y/A$ 连续。对任意 $y\in Y$：
   $$\overline{H}(q(y),0)=q(H(y,0))=q(y),\qquad \overline{H}(q(y),1)=q(H(y,1))=q(g(q(y))).$$
   因 $q$ 满射，故 $\overline{H}(-,0)=\operatorname{id}_{Y/A}$，$\overline{H}(-,1)=q\circ g$，即 $\operatorname{id}_{Y/A}\simeq q\circ g$。综上，$q:Y\to Y/A$ 是同伦等价。$\blacksquare$

---

## S2 非可缩底空间上的锥附着

### 1. 黏着空间的同伦不变性引理

**引理 2.1（沿有限 CW 偶黏着的同伦不变性）**  
设 $(M,A)$ 为有限 CW 偶（$A\neq\varnothing$），$Z$ 为紧致 Hausdorff 空间，$F:A\times[0,1]\to Z$ 为连接 $f_0=F(-,0)$ 与 $f_1=F(-,1)$ 的连续同伦。则黏着空间满足 $Z\cup_{f_0}M\simeq Z\cup_{f_1}M$。

*证明*：构造总黏着空间 $W=Z\cup_F(M\times[0,1])=\bigl(Z\sqcup(M\times[0,1])\bigr)/\!\sim$，其中等价关系由 $(a,t)\sim F(a,t)$（$\forall (a,t)\in A\times[0,1]$）生成，记商映射为 $p:Z\sqcup(M\times[0,1])\to W$。
先证 $W$ 为紧致 Hausdorff 空间：$Z\sqcup(M\times[0,1])$ 紧致，故 $W$ 紧致；设 $w_1\neq w_2\in W$：
- 若两点均在 $W\setminus p(Z)=p((M\setminus A)\times[0,1])$ 中，因 $(M\setminus A)\times[0,1]$ 为饱和开集且 Hausdorff，可直接分离；
- 若 $w_1=p(x_1)\notin p(Z)$ 而 $w_2\in p(Z)$，由紧致 Hausdorff 空间 $M\times[0,1]$ 的正规性，可用不相交开集分离点 $x_1$ 与闭集 $A\times[0,1]$，从而给出 $W$ 中不相交饱和开邻域；
- 若 $w_i=p(z_i)$（$z_1\neq z_2\in Z$），由 $Z$ 的正规性取开集 $V_1,V_2\subseteq Z$ 使 $z_i\in V_i$ 且 $\overline{V_1}\cap\overline{V_2}=\varnothing$，再由 $M\times[0,1]$ 的正规性取不相交开集 $U_1,U_2\subseteq M\times[0,1]$ 分别包含闭集 $F^{-1}(\overline{V_1}),F^{-1}(\overline{V_2})$，令 $U'_i=U_i\setminus\bigl((A\times[0,1])\setminus F^{-1}(V_i)\bigr)$，则 $V_1\sqcup U'_1$ 与 $V_2\sqcup U'_2$ 为不相交饱和开集，其在 $W$ 中的像分离 $w_1,w_2$。

同理 $Z\cup_{f_0}M$ 与 $Z\cup_{f_1}M$ 紧致，且自然映射 $j_0:Z\cup_{f_0}M\to W$（由 $M\cong M\times\{0\}$ 诱导）连续单射；紧致空间到 Hausdorff 空间的连续单射是闭嵌入，故可将 $Z\cup_{f_0}M$ 视为 $W$ 的子空间 $p\bigl(Z\sqcup(M\times\{0\})\bigr)$。

由引理 1.2，$(M,A)$ 为有限 CW 偶，故存在强形变收缩 $\Phi:(M\times[0,1])\times[0,1]\to M\times[0,1]$ 将 $M\times[0,1]$ 强形变收缩到 $(M\times\{0\})\cup(A\times[0,1])$。特别地，对一切 $(a,t)\in A\times[0,1]$ 与一切 $\tau\in[0,1]$，均有 $\Phi((a,t),\tau)=(a,t)$。在 $\bigl(Z\sqcup(M\times[0,1])\bigr)\times[0,1]$ 上定义映射：在 $Z\times[0,1]$ 上取 $(z,\tau)\mapsto p(z)$，在 $(M\times[0,1])\times[0,1]$ 上取 $((m,t),\tau)\mapsto p(\Phi((m,t),\tau))$。两者在黏着纤维上恒取同一值 $p(F(a,t))$；因定义域紧致且 $W\times[0,1]$ Hausdorff，$p\times\operatorname{id}_{[0,1]}$ 是商映射，故下降为 $W$ 到 $j_0(Z\cup_{f_0}M)$ 的强形变收缩。将时间参数作自同胚 $t\mapsto 1-t$ 对称处理，同理得 $j_1(Z\cup_{f_1}M)$ 也是 $W$ 的强形变收缩核。故 $Z\cup_{f_0}M\simeq W\simeq Z\cup_{f_1}M$。$\square$

### 2. 证明 $Y\simeq D\vee\Sigma L$

由于 $L$ 是非空有限 CW 复形，赋予 $CL=(L\times[0,1])/(L\times\{1\})$ 商 CW 结构（底面 $L\times\{0\}$ 保持 $L$ 的胞腔，锥顶点 $c_+=[L\times\{1\}]$ 为一个新增 $0$-胞腔，$L$ 的每个 $k$-胞腔 $e^k$ 产生 $(k+1)$-胞腔 $e^k\times(0,1)$），则 $(CL,L)$ 是有限 CW 偶（$L\neq\varnothing$），且底空间 $D$ 为有限 CW 复形从而紧致 Hausdorff。

因包含映射 $i:L\hookrightarrow D$ 零伦，存在点 $x_0\in D$ 及同伦 $F_0:L\times[0,1]\to D$ 使 $F_0(-,0)=i$ 且 $F_0(-,1)=c_{x_0}$（常值于 $x_0$）。任取定 $D$ 中一点 $d_0\in D$（例如可取 $D$ 的任一 $0$-胞腔；因 $L\neq\varnothing$，$D$ 非空故必有 $0$-胞腔）。由假设 **$D$ 路径连通**，存在连续路径 $\gamma:[0,1]\to D$ 使 $\gamma(0)=x_0,\gamma(1)=d_0$。将 $F_0$ 与路径同伦 $(y,t)\mapsto\gamma(t)$ 拼接，得连接 $i$ 与常值映射 $c_{d_0}:L\to\{d_0\}\subseteq D$ 的连续同伦 $F:L\times[0,1]\to D$。

对有限 CW 偶 $(CL,L)$、紧致 Hausdorff 空间 $D$ 与同伦 $F:i\simeq c_{d_0}$ 应用引理 2.1，立得
$$Y = D\cup_i CL \;\simeq\; D\cup_{c_{d_0}} CL.$$
考察右侧的黏着空间 $D\cup_{c_{d_0}} CL$：常值黏着映射 $c_{d_0}:L\times\{0\}\to D$ 先将 $CL$ 的整个非空底面 $L\times\{0\}$ 坍缩为单点（即 $\Sigma L$ 的南极 $s_-=[L\times\{0\}]$，使 $CL$ 的商成为 $\Sigma L$），同时将该点与 $d_0\in D$ 黏合。形式地，考虑紧致空间 $D\sqcup(L\times[0,1])$ 到 Hausdorff 空间 $(D,d_0)\vee(\Sigma L,s_-)$ 的自然满射（将 $D$ 恒等映入，将 $(y,t)\in L\times[0,1]$ 映为 $[y,t]\in\Sigma L$，其中 $[y,0]=s_-=d_0$）：其等价关系恰由 $(y,1)\sim(y',1)$ 及 $(y,0)\sim d_0$ 生成，与构造 $D\cup_{c_{d_0}}CL$ 的商等价关系完全一致；由紧致到 Hausdorff 满射为商映射，得同胚
$$D\cup_{c_{d_0}} CL \;\cong\; (D,d_0)\vee(\Sigma L,s_-).$$
因此 $Y\simeq D\vee\Sigma L$。

### 3. 楔点的选择及其无关性说明

1. **自然的规范楔点选择**：  
   在上述构造中，在 $D$ 上可取任意 $0$-胞腔 $d_0\in D^{(0)}$（例如直接取子复形 $L$ 的一个 $0$-胞腔），在 $\Sigma L$ 上取南极 $s_-=[L\times\{0\}]$（或对称地取北极 $s_+=[L\times\{1\}]$，由时间翻转自同胚 $[y,t]\mapsto[y,1-t]$ 知 $(\Sigma L,s_-)\cong(\Sigma L,s_+)$）。此时 $d_0$ 与 $s_-$ 均为各自有限 CW 结构的 $0$-胞腔，楔和 $(D,d_0)\vee(\Sigma L,s_-)$ 直接继承有限 CW 复形结构。

2. **楔点在 $D\times\Sigma L$ 中任意选取时的同伦型无关性（以及路径连通条件的作用）**：  
   实际上，对**任意**选取的 $d\in D$ 与 $s\in\Sigma L$，楔和 $(D,d)\vee(\Sigma L,s)$ 的同伦型均与上述相同：
   - **改变 $d\in D$**：因 $D$ **路径连通**，任意 $d\in D$ 均与 $d_0$ 路径相连，上述证明对任意 $d\in D$ 直接给出 $(D,d)\vee(\Sigma L,s_-)\simeq Y$。（注：$D$ 的路径连通性在此必不可少；若 $D$ 不连通，例如 $D=[0,1]\sqcup S^2,L=S^0=\partial[0,1]$，将 $\Sigma L\cong S^1$ 楔在 $[0,1]$ 分支上得 $S^1\sqcup S^2$，楔在 $S^2$ 分支上则得 $*\sqcup(S^2\vee S^1)$，同伦型发生改变。）
   - **改变 $s\in\Sigma L$**：因 $L\neq\varnothing$，$\Sigma L$ 亦为**路径连通**有限 CW 复形（任一点 $[y,t]\in\Sigma L$ 可由路径 $\tau\mapsto[y,\tau t]$ 连至 $s_-$）。对任意 $d\in D$ 与 $s\in\Sigma L$，先将其各自所在的唯一开胞腔 $\Phi(D^k)$（若 $k\ge 1$）以其原像点为锥顶对边界球面作径向锥细分，由于紧致 Hausdorff 空间的拓扑在有限细分下不变，$d$ 与 $s$ 在细分后均成为各自有限 CW 复形的 $0$-胞腔。记 $M=D\cup_{d\sim 0}[0,1]$，则 $(M,\{1\})$ 是有限 CW 偶。取 $\Sigma L$ 中从 $s_-$ 到 $s$ 的路径 $\beta:[0,1]\to\Sigma L$，对偶 $(M,\{1\})$ 与目标空间 $\Sigma L$ 应用引理 2.1 得
     $$\Sigma L\cup_{1\mapsto s_-}M \;\simeq\; \Sigma L\cup_{1\mapsto s}M.$$
     在这两个有限 CW 复形中，连接两端的闭区间 $[0,1]$ 均为非空可缩子复形；对其分别应用 **S1**（两处均满足“环境空间为有限 CW 复形，被坍缩子空间 $[0,1]$ 为非空可缩子复形”的全部适用条件），把 $[0,1]$ 坍缩为单点，左侧商同胚于 $(D,d)\vee(\Sigma L,s_-)$，右侧商同胚于 $(D,d)\vee(\Sigma L,s)$。故任意楔点选择均给出同一同伦型。$\blacksquare$

---

## S3 整数扭结的实例

### 1. 三元组 $(K,v,B)$ 的构造

设 $L$ 是实射影平面 $\mathbb{R}P^2$ 的任一有限抽象单纯三角剖分（故 $|L|\cong\mathbb{R}P^2$，特别地 $V(L)\neq\varnothing$）。
1. 取两个不在 $V(L)$ 中的相异新元素 $u,v\notin V(L)$，令 $V(K)=V(L)\sqcup\{u,v\}$，定义 $K$ 为 $L$ 以 $u,v$ 为两极点的单纯非约化悬挂：
   $$K = (u*L)\cup(v*L) = \bigl\{\{u\},\{v\}\bigr\}\cup L\cup\bigl\{\sigma\cup\{u\}:\sigma\in L\bigr\}\cup\bigl\{\sigma\cup\{v\}:\sigma\in L\bigr\}.$$
   由于 $V(K)$ 有限，且上述任一集合的非空子集仍是 $\{u\}$、$\{v\}$、$\tau$、$\tau\cup\{u\}$ 或 $\tau\cup\{v\}$（其中 $\tau\subseteq\sigma\in L$ 非空故 $\tau\in L$），$K$ 是有限抽象单纯复形，$v$ 是其顶点。
2. 任取 $L$ 的一个顶点 $w\in V(L)$，定义 $1$ 维子复形
   $$B = \bigl\{\{v\},\{w\},\{v,w\}\bigr\}\subseteq K.$$
   因 $\{w\}\in L\subseteq K$ 且 $\{v,w\}=\{w\}\cup\{v\}\in K$，$B$ 是 $K$ 中含顶点 $v$ 的子复形。

### 2. 逐项验证全部几何与代数拓扑性质

1. **$|K|\setminus\{v\}$ 非空可缩**：  
   （在 $|K|\subseteq\mathbb{R}^{V(K)}$ 中将顶点 $z$ 与基向量 $e_z$ 等同。）考察去顶子复形 $K-v=\{\tau\in K:v\notin\tau\}=u*L$。对任意 $x=\sum_{z\in V(K)}x_z e_z\in |K|\setminus\{e_v\}$，其重心坐标满足 $x_v<1$，故 $1-x_v>0$，且 $y(x)=\frac{1}{1-x_v}\sum_{z\neq v}x_z e_z$ 的支撑集为 $\operatorname{supp}(x)\setminus\{v\}\in K-v$，从而 $y(x)\in|K-v|$。定义同伦 $H:(|K|\setminus\{e_v\})\times[0,1]\to|K|\setminus\{e_v\}$ 为
   $$H(x,t)=(1-t)x+t\,y(x)=(1-t)x_v e_v+\frac{1-(1-t)x_v}{1-x_v}\sum_{z\neq v}x_z e_z.$$
   分母 $1-x_v>0$ 处处非零，故 $H$ 连续；$H(x,0)=x$，$H(x,1)=y(x)\in|K-v|$，且当 $x\in|K-v|$（即 $x_v=0$）时 $H(x,t)=x$。因此 $|K-v|=|u*L|$ 是 $|K|\setminus\{e_v\}$ 的强形变收缩核。  
   进一步，$|u*L|$ 含顶点 $e_u$ 故非空；对任意 $y\in|u*L|$ 与 $t\in[0,1]$，因 $\operatorname{supp}(y)\cup\{u\}\in u*L$，线性同伦 $G(y,t)=(1-t)y+t e_u$ 取值于 $|u*L|$ 内部，将 $|u*L|$ 收缩到单点 $\{e_u\}$。故 $|K|\setminus\{v\}\simeq|u*L|\simeq *$ 非空可缩。

2. **包含映射 $(|B|\setminus\{v\})\hookrightarrow|B|$ 为同伦等价**：  
   $|B|=\{(1-s)e_w+s e_v:s\in[0,1]\}\cong[0,1]$，而 $|B|\setminus\{e_v\}=\{(1-s)e_w+s e_v:s\in[0,1)\}\cong[0,1)$。同伦 $\bigl((1-s)e_w+s e_v,t\bigr)\mapsto(1-(1-t)s)e_w+(1-t)s e_v$ 同时将 $|B|$ 与 $|B|\setminus\{e_v\}$ 强形变收缩到公共子空间 $\{e_w\}$，故两者皆可缩，包含映射 $(|B|\setminus\{v\})\hookrightarrow|B|$ 是同伦等价（以常值映射 $x\mapsto e_w$ 为同伦逆）。

3. **同胚 $|K|\cong\Sigma|L|\cong\Sigma\mathbb{R}P^2$ 与悬挂同调同构**：  
   定义连续满射 $\Psi:|L|\times[0,1]\to|K|$ 为：当 $0\le t\le\frac{1}{2}$ 时 $\Psi(y,t)=(1-2t)e_u+2ty$；当 $\frac{1}{2}\le t\le 1$ 时 $\Psi(y,t)=(2-2t)y+(2t-1)e_v$。因 $|L|\times[0,1]$ 紧致而 $|K|$ Hausdorff，$\Psi$ 是商映射，其非单点纤维恰为 $\Psi^{-1}(e_u)=|L|\times\{0\}$ 与 $\Psi^{-1}(e_v)=|L|\times\{1\}$，故诱导同胚 $|K|\cong\Sigma|L|\cong\Sigma\mathbb{R}P^2$。

   **引理 3.1（非空空间的悬挂同调同构）**  
   对任意非空拓扑空间 $Z$ 与任意阿贝尔系数群 $G$，有 $\tilde{H}_0(\Sigma Z;G)=0$，且对一切整数 $n\ge 0$ 有同构 $\tilde{H}_{n+1}(\Sigma Z;G)\cong\tilde{H}_n(Z;G)$。  
   *证明*：因 $Z\neq\varnothing$，$\Sigma Z$ 中任一点 $[z,t]$ 可由路径 $\tau\mapsto[z,\tau t]$ 连至南极 $s_-$，故 $\Sigma Z$ 非空且路径连通，从而 $\tilde{H}_0(\Sigma Z;G)=0$。取开集 $U_+=\Sigma Z\setminus\{s_-\}$ 与 $U_-=\Sigma Z\setminus\{s_+\}$，则：
   - $U_+,U_-$ 均为 $\Sigma Z$ 的开子集且 $U_+\cup U_-=\Sigma Z$（满足奇异同调 Mayer–Vietoris 正合列的切除条件）；
   - $U_+\cap U_-\cong Z\times(0,1)$ 因 $Z\neq\varnothing$ 而非空（满足**约化** Mayer–Vietoris 正合列的适用条件），且投影 $Z\times(0,1)\to Z$（以 $z\mapsto(z,\frac{1}{2})$ 为同伦逆）是同伦等价；
   - $U_+$ 经 $([z,t],\tau)\mapsto[z,(1-\tau)t+\tau]$ 强形变收缩到 $\{s_+\}$，$U_-$ 经 $([z,t],\tau)\mapsto[z,(1-\tau)t]$ 强形变收缩到 $\{s_-\}$，故两者均可缩，对一切 $k$ 有 $\tilde{H}_k(U_\pm;G)=0$。  
   由约化 Mayer–Vietoris 长正合列
   $$0=\tilde{H}_{n+1}(U_+;G)\oplus\tilde{H}_{n+1}(U_-;G)\longrightarrow\tilde{H}_{n+1}(\Sigma Z;G)\xrightarrow{\;\partial\;}\tilde{H}_n(U_+\cap U_-;G)\longrightarrow\tilde{H}_n(U_+;G)\oplus\tilde{H}_n(U_-;G)=0,$$
   得 $\tilde{H}_{n+1}(\Sigma Z;G)\cong\tilde{H}_n(U_+\cap U_-;G)\cong\tilde{H}_n(Z;G)$（$\forall n\ge 0$）。$\square$

4. **$|K|$ 的约化有理同调全零，但 $|K|$ 不可缩**：  
   赋予 $\mathbb{R}P^2$ 标准极小有限 CW 结构 $\mathbb{R}P^2=e^0\cup e^1\cup e^2$（$0,1,2$ 维各含一个胞腔，其中 $e^1$ 两端均黏在 $e^0$ 上故胞腔边缘 $d_1=0$，$e^2$ 沿二度映射 $S^1\to S^1$ 附着故 $d_2=\times 2$）。由 CW 胞腔同调与奇异同调的同构定理（适用于任意 CW 复形）：
   - 取系数群 $G=\mathbb{Q}$，$\mathbb{R}P^2$ 的增广胞腔链复形为
     $$0\longrightarrow\mathbb{Q}\xrightarrow{\;\times 2\;}\mathbb{Q}\xrightarrow{\;0\;}\mathbb{Q}\xrightarrow{\;\operatorname{id}\;}\mathbb{Q}\longrightarrow 0.$$
     因 $\times 2:\mathbb{Q}\to\mathbb{Q}$ 是线性同构，该序列处处正合，故对一切 $n\ge 0$ 有 $\tilde{H}_n(\mathbb{R}P^2;\mathbb{Q})=0$。结合 $|K|\cong\Sigma\mathbb{R}P^2$ 与引理 3.1，对一切整数 $k$ 均有 $\tilde{H}_k(|K|;\mathbb{Q})=0$。
   - 取系数群 $G=\mathbb{Z}$，胞腔链复形 $0\to\mathbb{Z}\xrightarrow{\times 2}\mathbb{Z}\xrightarrow{0}\mathbb{Z}\to 0$ 给出 $\tilde{H}_1(\mathbb{R}P^2;\mathbb{Z})\cong\mathbb{Z}/2\mathbb{Z}$。由引理 3.1，
     $$\tilde{H}_2(|K|;\mathbb{Z})\;\cong\;\tilde{H}_1(\mathbb{R}P^2;\mathbb{Z})\;\cong\;\mathbb{Z}/2\mathbb{Z}\;\neq\;0.$$
     因为单点空间满足 $\tilde{H}_2(*;\mathbb{Z})=0$ 且约化奇异同调具有同伦不变性，$|K|$ **不可缩**。$\blacksquare$

---

## S4 整体对象与全部恢复目标

### 1. 判定结论与三项目标的陈述

**判定结论：所列全部目标在给定条件下均成立。** 具体陈述如下：

1. **同伦类型的完整刻画**：  
   满足全部给定条件的三元组 $(K,v,B)$ 中，$X=|K|$ 的可能同伦类型**恰为所有非空有限抽象单纯复形 $L$ 的几何实现的非约化悬挂 $\Sigma|L|$ 的同伦类型**。
2. **全部类型的实现构造**：  
   对任一非空有限抽象单纯复形 $L$，取相异新顶点 $u,v\notin V(L)$ 及任一顶点 $w\in V(L)$，令
   $$K=(u*L)\cup(v*L),\qquad B=\bigl\{\{v\},\{w\},\{v,w\}\bigr\},$$
   则 $(K,v,B)$ 满足全部原条件，且 $|K|\cong\Sigma|L|$。
3. **仅用局部有限关联数据检验 $X$ 可缩的充要判据**：  
   记 $\mathcal{S}_v=\{\sigma\in K:v\in\sigma\}$ 为 $K$ 中包含 $v$ 的全体单形，$\mathcal{F}_v=\{\tau\in K:\exists\sigma\in\mathcal{S}_v,\,\tau\subseteq\sigma\}$ 为它们的全体面，给定有限关联数据 $(\mathcal{F}_v,\mathcal{S}_v,\subseteq)$。令
   $$L=\mathcal{F}_v\setminus\mathcal{S}_v$$
   赋予诱导面偏序 $\preceq$（即 $\tau_1\preceq\tau_2\iff\tau_1\subseteq\tau_2$；注意即便仅给出二分关联关系 $\{(\tau,\sigma)\in\mathcal{F}_v\times\mathcal{S}_v:\tau\subseteq\sigma\}$，对任意 $\tau_1,\tau_2\in L$，因 $\sigma_2=\tau_2\cup\{v\}$ 是 $\mathcal{S}_v$ 中包含 $\tau_2$ 的唯一极小元且 $v\notin\tau_1$，也有 $\tau_1\preceq\tau_2\iff\tau_1\subseteq\sigma_2$，故偏序 $(L,\preceq)$ 由局部关联数据唯一确定）。  
   按如下纯有限组合步骤构造整矩阵族：
   - 令 $L_q=\{\tau\in L:|\{\eta\in L:\eta\preceq\tau\text{ 为 }(L,\preceq)\text{ 的极小元}\}|=q+1\}$（$0\le q\le d$，$d$ 为最大维数，给定条件下必有 $L_0\neq\varnothing$）。
   - 对有限集 $L_0$ 任取定一个全序 $w_1<\cdots<w_m$。每个 $\tau\in L_q$ 由其关联的极小元集合 $\{w_{i_0}<\cdots<w_{i_q}\}$ 唯一刻画；对 $0\le r\le q$，记 $\partial^{(r)}\tau\in L_{q-1}$ 为满足 $\eta\prec\tau$ 且 $w_{i_r}\not\preceq\eta$ 的唯一元素 $\eta\in L_{q-1}$。
   - 定义 $1\times|L_0|$ 整矩阵 $M_0=\begin{bmatrix}1&1&\cdots&1\end{bmatrix}$；对 $1\le q\le d$，定义 $|L_{q-1}|\times|L_q|$ 整矩阵 $M_q$，其 $(\eta,\tau)$ 元在 $\eta=\partial^{(r)}\tau$ 时取 $(-1)^r$，其余取 $0$（并记 $M_{d+1}=0$，$r_q=\operatorname{rank}(M_q)$，$r_{d+1}=0$）。

   **充要判据**：$X=|K|$ 可缩，当且仅当增广链复形 $(\mathbb{Z}^{L_\bullet},M_\bullet)$ 在 $\mathbb{Z}$ 上处处正合（即对一切 $0\le q\le d$ 有 $\tilde{H}_q(L;\mathbb{Z})=\ker(M_q)/\operatorname{im}(M_{q+1})=0$），亦即有限整矩阵 $M_0,M_1,\dots,M_d$ 的 **Smith 标准型**同时满足以下两条有限算术条件：
   - **（秩正合条件）** $r_0=1$（即 $L_0\neq\varnothing$），且对每个 $q=0,1,\dots,d$ 有 $r_q+r_{q+1}=|L_q|$；
   - **（无整数挠条件）** 对每个 $q=0,1,\dots,d$，$M_q$ 的全部 $r_q$ 个非零不变因子（Smith 标准型对角元）均等于 $1$（等价地，$M_q$ 的全体 $r_q$ 阶子式的最大公因数等于 $1$）。

---

### 2. 刻画与实现构造的证明

#### （1）必要性：任意满足条件的三元组均有 $X\simeq\Sigma|\operatorname{lk}_K(v)|$ 且 $\operatorname{lk}_K(v)\neq\varnothing$

设 $(K,v,B)$ 满足全部给定条件。记去顶子复形 $K-v=\{\tau\in K:v\notin\tau\}$ 与链环（link）$L=\operatorname{lk}_K(v)=\{\tau\in K-v:\tau\cup\{v\}\in K\}$。

- **第一步：证明 $|K-v|$ 非空可缩。**  
  因 $O=|K|\setminus\{v\}$ 非空，必有 $V(K)\setminus\{v\}\neq\varnothing$，故 $K-v\neq\varnothing$。与 S3 第 2 节第 1 条完全相同，显式重心坐标径向同伦
  $$H(x,t)=(1-t)x_v e_v+\frac{1-(1-t)x_v}{1-x_v}\sum_{z\in V(K)\setminus\{v\}}x_z e_z\qquad(x\in O,\;t\in[0,1])$$
  给出 $O=|K|\setminus\{v\}$ 到 $|K-v|$ 的强形变收缩。因 $O$ 非空可缩，故 $D=|K-v|$ 非空可缩。

- **第二步：利用子复形 $B$ 的条件证明 $L=\operatorname{lk}_K(v)$ 非空。**  
  反证法：假设 $\operatorname{lk}_B(v)=\varnothing$（即 $B$ 中没有包含 $v$ 的 $\ge 1$ 维单形）。则在 $C=|B|\subseteq\mathbb{R}^{V(B)}$ 中，每一点 $x\in|B|$ 或者满足 $x_v=0$（即 $x\in O\cap C=|B|\setminus\{e_v\}$），或者满足 $x=e_v$（即 $x_v=1$）。于是 $\{e_v\}=\{x\in|B|:x_v>\frac{1}{2}\}$ 与 $O\cap C=\{x\in|B|:x_v<\frac{1}{2}\}$ 是 $C$ 中互不相交的既开又闭子集。因此 $\{e_v\}$ 构成 $C$ 的一个孤立路径连通分支，且与 $O\cap C$ 不相交，导致包含映射诱导的路径连通分支映射 $\pi_0(O\cap C)\to\pi_0(C)$ 不是满射（$[e_v]$ 不在像中），这与 $O\cap C\hookrightarrow C$ 为同伦等价矛盾！  
  故必有 $\operatorname{lk}_B(v)\neq\varnothing$。因 $B\subseteq K$，$\varnothing\neq\operatorname{lk}_B(v)\subseteq\operatorname{lk}_K(v)=L$，故 $L$ 是**非空**有限抽象单纯复形。

- **第三步：应用 S1 证明 $X=|K|\simeq\Sigma|L|$。**  
  有限单纯复形 $|K|$ 以各开单形为开胞腔具有规范有限 CW 复形结构，子复形 $|K-v|\subseteq|K|$ 是其非空可缩 CW 子复形，完全满足 **S1** 的适用条件。由 **S1**，商映射 $q:|K|\to|K|/|K-v|$ 是同伦等价。  
  下证 $|K|/|K-v|\cong\Sigma|L|$：定义仿射连续映射 $\Phi:|L|\times[0,1]\to|K|$ 为 $\Phi(y,t)=(1-t)y+t e_v$（因 $\operatorname{supp}(y)\in L$，有 $\operatorname{supp}(y)\cup\{v\}\in K$，故取值于 $|K|$ 中），再令 $F=q\circ\Phi:|L|\times[0,1]\to|K|/|K-v|$。
  - *满射性*：$|K|$ 中任一点 $x$ 若 $x_v=0$ 则 $x\in|K-v|$；因 $L\neq\varnothing$，取 $y_0\in|L|\subseteq|K-v|$，有 $F(y_0,0)=q(y_0)=[|K-v|]=q(x)$。若 $x_v=1$ 则 $x=e_v=\Phi(y_0,1)$，故 $q(x)=F(y_0,1)$。若 $0<x_v<1$，则 $y=\frac{1}{1-x_v}\sum_{z\neq v}x_z e_z\in|L|$，且 $x=\Phi(y,x_v)$，故 $q(x)=F(y,x_v)$。因此 $F$ 满射。
  - *纤维结构与商拓扑*：对 $(y,t)\in|L|\times[0,1]$，$\Phi(y,t)$ 的 $e_v$-坐标恰为 $t$。于是 $\Phi(y,t)\in|K-v|\iff t=0$（即 $F^{-1}([|K-v|])=|L|\times\{0\}$）；$\Phi(y,t)=e_v\iff t=1$（即 $F^{-1}(q(e_v))=|L|\times\{1\}$）；当 $0<t<1$ 时，$\Phi(y,t)\in|K|\setminus(|K-v|\cup\{e_v\})$，在此区域 $\Phi$ 与 $q$ 均为单射。因 $|L|\times[0,1]$ 紧致且由引理 1.1 知 $|K|/|K-v|$ Hausdorff，连续满射 $F$ 是商映射，从而诱导同胚 $\Sigma|L|\xrightarrow{\cong}|K|/|K-v|$。  
  综上，$X=|K|\simeq|K|/|K-v|\cong\Sigma|L|$。

#### （2）充分性（实现构造的验证）

对任意非空有限抽象单纯复形 $L$，取 $K=(u*L)\cup(v*L)$ 与 $B=\{\{v\},\{w\},\{v,w\}\}$（$w\in V(L)$ 任取；因 $L\neq\varnothing$，必有 $V(L)\neq\varnothing$）。注意 S3 第 2 节第 1、2、3 条关于 $K$ 为有限单纯复形、$|K|\setminus\{v\}$ 非空可缩、$(|B|\setminus\{v\})\hookrightarrow|B|$ 为同伦等价以及 $|K|\cong\Sigma|L|$ 的证明，在那里仅用到了“$L$ 是非空有限抽象单纯复形”，完全不依赖 $|L|\cong\mathbb{R}P^2$。故同一证明直接验证了此处对一切非空有限抽象单纯复形 $L$ 给出的实现构造 $(K,v,B)$ 满足全部原条件且 $|K|\cong\Sigma|L|$。

---

### 3. 可缩充要判据的证明

#### （1）拓扑部分：$X$ 可缩 $\iff\forall q\ge 0,\;\tilde{H}_q(L;\mathbb{Z})=0$

首先，在偏序同构下 $(L,\preceq)\cong(\operatorname{lk}_K(v),\subseteq)$，按第 1 节构造的整矩阵链复形 $(\mathbb{Z}^{L_\bullet},M_\bullet)$ 正是单纯复形 $L=\operatorname{lk}_K(v)$ 的增广有序单纯链复形 $\tilde{C}_\bullet(L;\mathbb{Z})$。由于有限单纯复形 $|L|$ 的 $\Delta$-复形/CW 胞腔链复形与单纯链复形一致，标准单纯同调与奇异同调同构定理在此适用，给出对一切 $q\ge 0$ 有 $\tilde{H}_q(L;\mathbb{Z})\cong\tilde{H}_q(|L|;\mathbb{Z})$。又因 $L\neq\varnothing$ 且已证 $X\simeq\Sigma|L|$，由同调同伦不变性与 **S3 引理 3.1**（系数取 $G=\mathbb{Z}$，满足 $|L|\neq\varnothing$ 的适用条件），有 $\tilde{H}_0(X;\mathbb{Z})=0$ 且
$$\tilde{H}_{q+1}(X;\mathbb{Z})\;\cong\;\tilde{H}_{q+1}(\Sigma|L|;\mathbb{Z})\;\cong\;\tilde{H}_q(|L|;\mathbb{Z})\;\cong\;\tilde{H}_q(L;\mathbb{Z})\qquad(\forall q\ge 0).$$

- **必要性**：若 $X$ 可缩（$X\simeq *$），由奇异同调同伦不变性，对一切 $k\ge 0$ 有 $\tilde{H}_k(X;\mathbb{Z})=0$，故对一切 $q\ge 0$ 有 $\tilde{H}_q(L;\mathbb{Z})=0$。
- **充分性**：设对一切 $q\ge 0$ 有 $\tilde{H}_q(L;\mathbb{Z})=0$。我们要证 $X$ 可缩；因 $X\simeq\Sigma|L|$，只需证 $Y=\Sigma|L|$ 可缩：
  1. *路径连通性*：由 $\tilde{H}_0(|L|;\mathbb{Z})\cong\tilde{H}_0(L;\mathbb{Z})=0$ 及 $|L|\neq\varnothing$，知 $H_0(|L|;\mathbb{Z})\cong\mathbb{Z}$，故 $|L|$ **非空且路径连通**。
  2. *应用 Seifert–van Kampen 定理证明单连通性*：如 S3 引理 3.1 取开覆盖 $Y=U_+\cup U_-$，并取基点 $x_0=[y_0,\frac{1}{2}]\in U_+\cap U_-$（$y_0\in|L|$）。验证适用条件：$U_+,U_-$ 均为 $Y$ 的开子集；$U_+,U_-$ 可缩从而路径连通且 $\pi_1(U_\pm,x_0)=\{1\}$；交集 $U_+\cap U_-\cong|L|\times(0,1)$ 因 $|L|$ 非空且路径连通故亦**非空且路径连通**。Seifert–van Kampen 定理适用，给出自由积融通
     $$\pi_1(Y,x_0)\;\cong\;\pi_1(U_+,x_0)*_{\pi_1(U_+\cap U_-,x_0)}\pi_1(U_-,x_0)\;=\;\{1\}*_{\pi_1(U_+\cap U_-,x_0)}\{1\}\;=\;\{1\}.$$
     故 $Y$ 路径连通且单连通（即 $1$-连通）。
  3. *应用绝对 Hurewicz 定理证明全部同伦群平凡*：对 $n\ge 2$ 归纳证 $\pi_n(Y,x_0)=0$。归纳假设设 $Y$ 已是 $(n-1)$-连通空间（$n=2$ 时由上一步成立）。绝对 Hurewicz 定理的适用条件为“$n\ge 2$ 且空间 $(n-1)$-连通”，此处完全满足，故 Hurewicz 同态给出同构
     $$\pi_n(Y,x_0)\;\cong\;H_n(Y;\mathbb{Z})\;=\;\tilde{H}_n(Y;\mathbb{Z})\;\cong\;\tilde{H}_{n-1}(L;\mathbb{Z})\;=\;0.$$
     由归纳法，对一切 $n\ge 1$ 均有 $\pi_n(Y,x_0)=0$。结合 $Y$ 路径连通，常值映射 $c:Y\to\{*\}$ 在 $\pi_0$ 上诱导双射，且在所有基点处对所有 $n\ge 1$ 诱导同伦群同构，故 $c$ 是**弱同伦等价**。
  4. *应用 Whitehead 定理得可缩性*：由 S3 第 2 节第 3 条知 $Y=\Sigma|L|\cong|(u*L)\cup(v*L)|$ 是有限单纯复形的几何实现，从而具有 CW 复形结构；单点空间 $\{*\}$ 亦为 CW 复形。Whitehead 定理（“两个 CW 复形之间的弱同伦等价必为同伦等价”）的全部适用条件均满足，故 $c:Y\to\{*\}$ 是同伦等价，即 $Y=\Sigma|L|$ 可缩，从而 $X\simeq\Sigma|L|$ 可缩。

#### （2）代数部分：$\forall q\ge 0,\;\tilde{H}_q(L;\mathbb{Z})=0\iff$ Smith 标准型条件

记 $C_q=\mathbb{Z}^{L_q}$（秩 $n_q=|L_q|$，$0\le q\le d$），$C_{-1}=\mathbb{Z}$，$C_{d+1}=0$。已知对 $0\le q\le d$ 有 $M_q M_{q+1}=0$，记 $K_q=\ker(M_q)\subseteq C_q$，$I_{q+1}=\operatorname{im}(M_{q+1})\subseteq K_q$。
首先，因 $L_0\neq\varnothing$ 且 $M_0=\begin{bmatrix}1&\cdots&1\end{bmatrix}$，自动有 $r_0=\operatorname{rank}(M_0)=1$ 且 $M_0$ 的唯一非零不变因子为 $1$（即 $M_0:C_0\to\mathbb{Z}$ 满射）。
对每个 $q\in\{0,1,\dots,d\}$：
- 自由阿贝尔群 $C_{q-1}$ 的子群 $\operatorname{im}(M_q)\cong C_q/K_q$ 仍是秩为 $r_q$ 的**自由阿贝尔群**，故 $\operatorname{rank}(K_q)=n_q-r_q$，且短正合列
  $$0\longrightarrow K_q/I_{q+1}\longrightarrow C_q/I_{q+1}\longrightarrow C_q/K_q\longrightarrow 0$$
  必可裂，即 $C_q/I_{q+1}\cong(K_q/I_{q+1})\oplus\mathbb{Z}^{r_q}$。
- 另一方面，设 $M_{q+1}:C_{q+1}\to C_q$ 的非零不变因子为 $d_1\mid d_2\mid\cdots\mid d_{r_{q+1}}$（$q=d$ 时 $r_{d+1}=0$，无不变因子），由有限生成自由 $\mathbb{Z}$-模同态的 Smith 标准型定理，有
  $$C_q/I_{q+1}\;\cong\;(\mathbb{Z}/d_1\mathbb{Z})\oplus\cdots\oplus(\mathbb{Z}/d_{r_{q+1}}\mathbb{Z})\oplus\mathbb{Z}^{n_q-r_{q+1}}.$$

比较上述关于有限生成阿贝尔群 $C_q/I_{q+1}$ 的两个同构分解：
- 其自由秩相等给出 $\operatorname{rank}(K_q/I_{q+1})+r_q=n_q-r_{q+1}$，故 $\operatorname{rank}(K_q/I_{q+1})=0\iff r_q+r_{q+1}=n_q$；
- 其挠子群同构给出 $\operatorname{Tors}(K_q/I_{q+1})\cong\operatorname{Tors}(C_q/I_{q+1})\cong\bigoplus_{j=1}^{r_{q+1}}(\mathbb{Z}/d_j\mathbb{Z})$，故 $\operatorname{Tors}(K_q/I_{q+1})=0\iff d_1=\cdots=d_{r_{q+1}}=1$。

有限生成阿贝尔群 $\tilde{H}_q(L;\mathbb{Z})=K_q/I_{q+1}=0$ 当且仅当其自由秩为 $0$ 且挠子群为 $0$。遍历 $q=0,1,\dots,d$（结合 $q=-1$ 处已自动成立的 $r_0=1$ 及 $M_0$ 不变因子为 $1$），即知 $\forall q\ge 0,\;\tilde{H}_q(L;\mathbb{Z})=0$ 与第 1 节所列关于 $M_0,M_1,\dots,M_d$ 的秩条件及不变因子全为 $1$ 的条件完全等价。$\blacksquare$

---

## S5 不提供子复形 B

### 1. 判定结论与新增类型分类

- **判定结论：不必**（$|K|$ 未必同伦等价于非空有限复形的悬挂）。
- **新增可能类型的完整分类**：去掉子复形 $B$ 及其同伦条件后，在同伦等价意义下**唯一新增的同伦类型是离散两点空间 $S^0$**（当且仅当 $\operatorname{lk}_K(v)=\varnothing$，即 $v$ 为 $K$ 的孤立顶点时取得；而当 $\operatorname{lk}_K(v)\neq\varnothing$ 时，$|K|\simeq\Sigma|\operatorname{lk}_K(v)|$ 仍为非空有限单纯复形的非约化悬挂，无其他新增类型）。

### 2. 完整证明

设 $K$ 是有限抽象单纯复形，$v\in V(K)$，且 $O=|K|\setminus\{v\}$ 非空可缩。
首先，S4 第 2 节第（1）部分第一步完全不涉及 $B$，故去顶子复形 $D=|K-v|$ 必**非空可缩**。记链环 $L=\operatorname{lk}_K(v)$，分两种互斥且穷尽的情形讨论：

1. **情形一：$L=\operatorname{lk}_K(v)\neq\varnothing$**。  
   此时 S4 第 2 节第（1）部分第三步的全部条件（$|K|$ 为有限 CW 复形，$|K-v|$ 为非空可缩子复形，且 $L\neq\varnothing$）全部满足（甚至任取 $w\in V(L)$ 并令 $B=\{\{v\},\{w\},\{v,w\}\}$ 即回到 S4 情形），故 $|K|\simeq\Sigma|L|$，同伦等价于非空有限单纯复形（亦即非空有限 CW 复形）$|L|$ 的非约化悬挂，不产生任何新同伦型。

2. **情形二：$L=\operatorname{lk}_K(v)=\varnothing$（即 $v$ 为 $K$ 的孤立顶点）**。  
   - **此时必有 $|K|\simeq S^0$**：  
     因 $K$ 中不含以 $v$ 为端点的更高维单形，$|K|=|K-v|\sqcup\{e_v\}=D\sqcup\{e_v\}$ 为两个不相交既开又闭子集的拓扑不交并。因 $D$ 非空可缩，取 $x_0\in D$ 及收缩同伦 $h:D\times[0,1]\to D$（$h(x,0)=x,h(x,1)=x_0$）。定义 $f:D\sqcup\{e_v\}\to\{x_0\}\sqcup\{e_v\}\cong S^0$ 在 $D$ 上取常值 $x_0$、在 $e_v$ 上取 $e_v$，并以包含映射 $j:\{x_0\}\sqcup\{e_v\}\hookrightarrow D\sqcup\{e_v\}$ 为逆：则 $f\circ j=\operatorname{id}$，而将 $h$ 在 $\{e_v\}\times[0,1]$ 上用常值同伦 $(e_v,t)\mapsto e_v$ 延拓（不交并上连续），即得 $\operatorname{id}_{|K|}\simeq j\circ f$。故 $|K|\simeq S^0$。
   - **存在满足前提的具体实例**：  
     取两个相异顶点 $u,v$，令 $0$ 维有限单纯复形 $K=\bigl\{\{u\},\{v\}\bigr\}$。则 $|K|=\{e_u,e_v\}\cong S^0$，而 $|K|\setminus\{e_v\}=\{e_u\}$ 为单点空间，非空且可缩，满足 S5 的全部前提。
   - **$S^0$ 不同伦等价于任何非空复形（乃至任何非空空间）的悬挂**：  
     对**任意非空**拓扑空间 $Z$，其非约化悬挂 $\Sigma Z$ 路径连通（任取 $z_0\in Z$，任一点 $[z,t]\in\Sigma Z$ 可经路径 $\tau\mapsto[z,\tau t]$ 连至南极 $s_-=[z_0,0]$；即便考虑基点空间 $(Z,z_0)$ 的约化悬挂 $\tilde{\Sigma}Z$，作为 $\Sigma Z$ 的商空间同样路径连通），故 $|\pi_0(\Sigma Z)|=1$。而离散两点空间满足 $|\pi_0(S^0)|=2$。因路径连通分支个数 $|\pi_0|$ 是同伦不变量且 $2\neq 1$，故 $S^0\not\simeq\Sigma Z$。

综上，$|K|$ 不必同伦等价于非空有限复形的悬挂，唯一新增的同伦类型为 $S^0$。$\blacksquare$

---

## S6 悬挂信息的逆向恢复

### 1. 判定结论与反例构造

**判定结论：不必**（$\Sigma|L_1|\simeq\Sigma|L_2|$ 未必推出 $|L_1|\simeq|L_2|$）。

**反例构造**：在 $6$ 个顶点的集合 $\{1,2,3,4,5,6\}$ 上构造如下两个非空有限 $1$ 维抽象单纯复形 $L_1,L_2$：
- 令 $L_1$ 由两个不相交三角形边界构成：其 $0$-单形为 $\{1\},\{2\},\{3\},\{4\},\{5\},\{6\}$，$1$-单形为
  $$\{1,2\},\{2,3\},\{1,3\},\qquad \{4,5\},\{5,6\},\{4,6\}.$$
  其几何实现满足 $|L_1|\cong S^1\sqcup S^1$。
- 令 $L_2$ 由两个在顶点 $1$ 处楔和的三角形边界外加一个孤立顶点 $6$ 构成：其 $0$-单形为 $\{1\},\{2\},\{3\},\{4\},\{5\},\{6\}$，$1$-单形为
  $$\{1,2\},\{2,3\},\{1,3\},\qquad \{1,4\},\{4,5\},\{1,5\}.$$
  其几何实现满足 $|L_2|\cong(S^1\vee S^1)\sqcup\{e_6\}$。

显然 $L_1,L_2$ 均为非空有限抽象单纯复形，满足全部前提。

### 2. 证明 $|L_1|\not\simeq|L_2|$

反证法：假设存在同伦等价 $f:|L_1|\to|L_2|$ 及其同伦逆 $g:|L_2|\to|L_1|$，设同伦 $H:|L_1|\times[0,1]\to|L_1|$ 连接 $g\circ f$ 与 $\operatorname{id}_{|L_1|}$，同伦 $G:|L_2|\times[0,1]\to|L_2|$ 连接 $f\circ g$ 与 $\operatorname{id}_{|L_2|}$。
考察 $|L_2|$ 中的孤立点路径连通分支 $\{e_6\}$。令 $x_0=g(e_6)\in|L_1|$，记 $Y_0$ 为 $|L_1|$ 中包含 $x_0$ 的路径连通分支（则 $Y_0$ 为三角形边界，$Y_0\cong S^1$）。
- 因路径 $t\mapsto G(e_6,t)$ 在 $|L_2|$ 中以 $G(e_6,1)=e_6$ 为终点，而 $\{e_6\}$ 是 $|L_2|$ 的一个路径连通分支，该路径恒常值于 $e_6$，特别地 $f(x_0)=f(g(e_6))=G(e_6,0)=e_6$。又因 $Y_0$ 路径连通，$f(Y_0)$ 是包含 $e_6$ 的路径连通集，故 $f(Y_0)=\{e_6\}$。
- 对任意 $y\in Y_0$，路径 $t\mapsto H(y,t)$ 连接起点 $H(y,0)=g(f(y))=g(e_6)=x_0\in Y_0$ 与终点 $H(y,1)=y\in Y_0$，故整条路径留在路径连通分支 $Y_0$ 中，即 $H(Y_0\times[0,1])\subseteq Y_0$。

于是限制映射 $f|_{Y_0}:Y_0\to\{e_6\}$ 与 $g|_{\{e_6\}}:\{e_6\}\to Y_0$ 互为同伦逆，这意味着 $S^1\cong Y_0$ 可缩！然而对 $S^1$（赋予一个 $0$-胞腔与一个两端黏合的 $1$-胞腔的 CW 结构），其胞腔同调给出 $H_1(S^1;\mathbb{Z})\cong\mathbb{Z}\neq 0=H_1(*;\mathbb{Z})$，与奇异同调同伦不变性矛盾。故 $|L_1|\not\simeq|L_2|$。

### 3. 证明 $\Sigma|L_1|\simeq\Sigma|L_2|$

我们先用 **S1** 证明一个关于不交并的非约化悬挂的一般同伦分解公式。

**引理 6.1**  
设 $X,Y$ 是顶点集不相交的两个非空有限抽象单纯复形，各取定顶点 $x_0\in V(X)$ 与 $y_0\in V(Y)$。对任一含顶点 $z_0$ 的非空有限单纯复形 $Z$，记 $K_\Sigma(Z)=(u_Z*Z)\cup(v_Z*Z)$（故 $|K_\Sigma(Z)|\cong\Sigma|Z|$），并记 $A(Z,z_0)\subseteq K_\Sigma(Z)$ 为由两条边 $\{u_Z,z_0\},\{v_Z,z_0\}$ 生成的 $1$ 维子复形。则有同伦等价
$$\Sigma\bigl(|X|\sqcup|Y|\bigr)\;\simeq\;\bigl(|K_\Sigma(X)|/|A(X,x_0)|\bigr)\;\vee\;\bigl(|K_\Sigma(Y)|/|A(Y,y_0)|\bigr)\;\vee\;S^1,$$
其中右侧三个因子均以各自坍缩所得的基点 $*$ 作楔和。

*证明*：取不在 $V(X)\sqcup V(Y)$ 中的相异元素 $u,v,v_X,v_Y$。
1. 记 $K_\Sigma=K_\Sigma(X\sqcup Y)=(u*(X\sqcup Y))\cup(v*(X\sqcup Y))$，则 $|K_\Sigma|\cong\Sigma(|X|\sqcup|Y|)$；记 $A_1=\bigl\{\{u\},\{v\},\{x_0\},\{u,x_0\},\{v,x_0\}\bigr\}\subseteq K_\Sigma$。因 $|A_1|$ 是依次连接相异三顶点 $u-x_0-v$ 的两段折线弧，$|A_1|\cong[0,1]$ 非空可缩。对有限单纯（CW）复形 $|K_\Sigma|$ 及其非空可缩子复形 $|A_1|$ 应用 **S1**，商映射
   $$q_1:|K_\Sigma|\xrightarrow{\;\simeq\;}|K_\Sigma|/|A_1|$$
   是同伦等价。
2. 在顶点集 $V(X)\sqcup V(Y)\sqcup\{u,v_X,v_Y\}$ 上构造辅助有限抽象单纯复形
   $$K_{\mathrm{aux}}=\bigl((u*X)\cup(v_X*X)\bigr)\;\cup\;\bigl((u*Y)\cup(v_Y*Y)\bigr)\;\cup\;\bigl\{\{v_X\},\{v_Y\},\{v_X,v_Y\}\bigr\}.$$
   （即把 $K_\Sigma(X)$ 与 $K_\Sigma(Y)$ 的北极粘为公共顶点 $u$，保留南极 $v_X\neq v_Y$ 分离，并在 $v_X,v_Y$ 之间添一条边 $\{v_X,v_Y\}$。）考察 $K_{\mathrm{aux}}$ 中的两个简单折线子复形：
   - $T_1$：由三条边 $\{v_Y,v_X\},\{v_X,x_0\},\{x_0,u\}$ 生成的子复形（顶点依次为相异四点 $v_Y-v_X-x_0-u$，故 $|T_1|\cong[0,1]$ 非空可缩）；
   - $T_2$：由四条边 $\{v_X,x_0\},\{x_0,u\},\{u,y_0\},\{y_0,v_Y\}$ 生成的子复形（顶点依次为相异五点 $v_X-x_0-u-y_0-v_Y$，故 $|T_2|\cong[0,1]$ 非空可缩）。

   对有限单纯（CW）复形 $|K_{\mathrm{aux}}|$ 分别就非空可缩子复形 $|T_1|$ 和 $|T_2|$ 应用 **S1**，得两条商映射均为同伦等价：
   $$|K_{\mathrm{aux}}|/|T_1|\xleftarrow[\;\text{S1}\;]{\;\simeq\;}|K_{\mathrm{aux}}|\xrightarrow[\;\text{S1}\;]{\;\simeq\;}|K_{\mathrm{aux}}|/|T_2|.$$
3. 识别两个商空间：
   - 定义满单纯映射 $f:K_{\mathrm{aux}}\to K_\Sigma$：在 $V(X)\sqcup V(Y)\sqcup\{u\}$ 上为恒等，且令 $f(v_X)=f(v_Y)=v$（边 $\{v_X,v_Y\}$ 映为 $0$-单形 $\{v\}\in K_\Sigma$）。复合满射 $q_1\circ|f|:|K_{\mathrm{aux}}|\to|K_\Sigma|/|A_1|$ 从紧致空间映到 Hausdorff 空间（引理 1.1），故为商映射；其像为 $[|A_1|]$ 的原像恰为 $|T_1|$，且将 $|K_{\mathrm{aux}}|\setminus|T_1|$ 双射映上 $|K_\Sigma|\setminus|A_1|$，从而诱导同胚 $|K_{\mathrm{aux}}|/|T_1|\cong|K_\Sigma|/|A_1|$。
   - 在 $|K_{\mathrm{aux}}|$ 中，三个闭子复形 $|(u*X)\cup(v_X*X)|$、$|(u*Y)\cup(v_Y*Y)|$ 与 $|\{v_X,v_Y\}|$ 的两两交集分别为 $\{u\}$、$\{v_X\}$、$\{v_Y\}$，三者全部包含在 $|T_2|$ 中；同时它们各自与 $|T_2|$ 的交集恰分别为 $|A(X,x_0)|$、$|A(Y,y_0)|$ 与边界两点 $\{e_{v_X},e_{v_Y}\}$。因紧致空间到 Hausdorff 空间的满射为商映射，将 $|T_2|$ 坍缩为单点 $*$ 直接给出同胚
     $$|K_{\mathrm{aux}}|/|T_2|\;\cong\;\bigl(|K_\Sigma(X)|/|A(X,x_0)|\bigr)\;\vee\;\bigl(|K_\Sigma(Y)|/|A(Y,y_0)|\bigr)\;\vee\;\bigl(|\{v_X,v_Y\}|/\{e_{v_X},e_{v_Y}\}\bigr),$$
     其中最后一个楔和因子同胚于 $[0,1]/\{0,1\}\cong S^1$。

   串联上述同胚与同伦等价即得引理结论。$\square$

现在将引理 6.1 分别应用于 $L_1$ 与 $L_2$：

1. **计算 $\Sigma|L_1|$**：  
   记 $C_1$ 为顶点 $\{1,2,3\}$ 上的三角形边界，$C_2$ 为顶点 $\{4,5,6\}$ 上的三角形边界，则 $L_1=C_1\sqcup C_2$。取 $x_0=1\in V(C_1),y_0=4\in V(C_2)$。  
   对三角形边界 $C_1$，有带基点同胚 $(|C_1|,e_1)\cong([0,1]/\{0,1\},[0])$。于是 $|K_\Sigma(C_1)|/|A(C_1,1)|$ 同胚于将紧致正方形 $[0,1]\times[0,1]$ 的整个边界 $\partial([0,1]^2)=([0,1]\times\{0,1\})\cup(\{0,1\}\times[0,1])$ 坍缩为单点 $*$ 所得的空间，即带基点同胚于 $(S^2,*)$。同理 $(|K_\Sigma(C_2)|/|A(C_2,4)|,*)\cong(S^2,*)$。由引理 6.1：
   $$\Sigma|L_1|\;\simeq\;S^2\vee S^2\vee S^1.$$

2. **计算 $\Sigma|L_2|$**：  
   记 $X_2=C'_1\cup C'_2$ 为顶点 $\{1,2,3\}$ 上的三角形边界 $C'_1$ 与顶点 $\{1,4,5\}$ 上的三角形边界 $C'_2$ 在公共顶点 $1$ 处的并，$Y_2=\{\{6\}\}$ 为单顶点复形，则 $L_2=X_2\sqcup Y_2$。取 $x_0=1\in V(X_2)$（楔点）与 $y_0=6\in V(Y_2)$。
   - 在 $K_\Sigma(X_2)=K_\Sigma(C'_1)\cup K_\Sigma(C'_2)$ 中，因 $C'_1\cap C'_2=\{\{1\}\}$，两个子复形 $|K_\Sigma(C'_1)|$ 与 $|K_\Sigma(C'_2)|$ 的交集**恰好等于** $|A(X_2,1)|$！因此将 $|A(X_2,1)|$ 坍缩为单点 $*$ 给出带基点同胚
     $$|K_\Sigma(X_2)|/|A(X_2,1)|\;\cong\;\bigl(|K_\Sigma(C'_1)|/|A(C'_1,1)|\bigr)\vee\bigl(|K_\Sigma(C'_2)|/|A(C'_2,1)|\bigr)\;\cong\;S^2\vee S^2.$$
   - 对单顶点复形 $Y_2=\{\{6\}\}$，有 $K_\Sigma(Y_2)=A(Y_2,6)$，故将其坍缩为 $*$ 后得到单点空间 $\{*\}$。
   由引理 6.1：
   $$\Sigma|L_2|\;\simeq\;(S^2\vee S^2)\vee\{*\}\vee S^1\;\cong\;S^2\vee S^2\vee S^1.$$

综上，$\Sigma|L_1|\simeq S^2\vee S^2\vee S^1\simeq\Sigma|L_2|$，但 $|L_1|\not\simeq|L_2|$。$\blacksquare$
