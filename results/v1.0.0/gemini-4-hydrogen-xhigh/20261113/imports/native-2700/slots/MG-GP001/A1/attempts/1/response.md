以下按 **S1–S6** 逐项作答。全文记 $I=[0,1]$；所有几何实现均取通常的拓扑；对抽象单纯复形取通常的非空子集约定（复形 $K$ 的单形是有限顶点集 $V(K)$ 的某些非空子集且对非空子集封闭），并记顶点 $v\in V(K)$ 的闭星、链环与去顶子复形分别为
$$\mathrm{st}_K(v)=\{\sigma\in K:\sigma\text{ 或 }\sigma\cup\{v\}\text{ 在 }K\text{ 中且与 }\mathrm{lk}_K(v)\text{ 相关}\}$$
即更精确地：
$$K\setminus v=\{\sigma\in K:v\notin\sigma\},\qquad \mathrm{lk}_K(v)=\{\tau\in K:v\notin\tau,\ \tau\cup\{v\}\in K\},$$
$$\mathrm{st}_K(v)=\{\sigma\in K:\sigma\cup\{v\}\in K\}=\{v\}\cup\mathrm{lk}_K(v)\cup\{\tau\cup\{v\}:\tau\in\mathrm{lk}_K(v)\}$$
（单点集记为 $\{v\}$；若 $\mathrm{lk}_K(v)=\emptyset$，即无含 $v$ 的高维单形，则 $v$ 为孤立顶点）。对非空空间 $Z$，其**非约化悬挂**定义为
$$\Sigma Z=(Z\times I)/\!\sim,$$
其中将 $Z\times\{0\}$ 捏为南极 $s_0$、将 $Z\times\{1\}$ 捏为北极 $s_1$；其**锥**定义为 $CZ=(Z\times I)/(Z\times\{1\})$，将 $Z$ 与底面 $Z\times\{0\}$ 等同。

---

## S1 可缩子复形的商

**结论**：商映射 $q:Y\to Y/A$ 是同伦等价。

### 证明

1. **有限 CW 对 $(Y,A)$ 具有同伦扩张性质（HEP）**
   设 $Y\setminus A$ 共有有限个胞腔，按维数不减排为 $e_1,\dots,e_m$，令 $Y_0=A$，$Y_k=Y_{k-1}\cup_{\varphi_k} D^{n_k}$（$1\le k\le m$），其中特征映射 $\Phi_k:Y_{k-1}\sqcup D^{n_k}\to Y_k$ 为商映射，$\varphi_k=\Phi_k|_{S^{n_k-1}}:S^{n_k-1}\to Y_{k-1}$。
   对每个 $n\ge 0$，存在收缩映射 $r_n:D^n\times I\to (D^n\times\{0\})\cup (S^{n-1}\times I)$（例如从 $\mathbb{R}^n\times\mathbb{R}$ 中的点 $(0,2)$ 作径向投影；当 $n=0$ 时 $S^{-1}=\emptyset$，取常值收缩到 $D^0\times\{0\}$）。因为 $I$ 是局部紧 Hausdorff 空间（由下文引理 1），$\Phi_k\times\mathrm{id}_I:(Y_{k-1}\sqcup D^{n_k})\times I\to Y_k\times I$ 仍是商映射。于是若已有连续映射 $F_0:Y_k\to Z$ 与同伦 $G_{k-1}:Y_{k-1}\times I\to Z$ 满足 $G_{k-1}(\cdot,0)=F_0|_{Y_{k-1}}$，则将 $F_0\circ\Phi_k|_{D^{n_k}}$ 与 $G_{k-1}\circ(\varphi_k\times\mathrm{id}_I)$ 拼成 $(D^{n_k}\times\{0\})\cup(S^{n_k-1}\times I)\to Z$，再与 $r_{n_k}$ 复合得 $D^{n_k}\times I\to Z$；它在边界 $S^{n_k-1}\times I$ 上与 $G_{k-1}$ 粘合条件相容，由商拓扑泛性质下降为 $G_k:Y_k\times I\to Z$。对 $k=1,\dots,m$ 有限归纳，即得 $(Y,A)$ 满足 HEP。

2. **构造在 $A$ 上保持在 $A$ 内的同伦 $H$**
   因 $A$ 非空且可缩，存在基点 $a_0\in A$ 与同伦 $h:A\times I\to A$，满足 $h(a,0)=a$ 且 $h(a,1)=a_0$（$\forall a\in A$）。记包含映射为 $\iota:A\hookrightarrow Y$。应用 $(Y,A)$ 的 HEP 于 $H_0=\mathrm{id}_Y:Y\to Y$ 及 $\iota\circ h:A\times I\to Y$（在 $t=0$ 处均等于 $\iota$），得连续同伦 $H:Y\times I\to Y$ 满足：
   $$H(y,0)=y\ (\forall y\in Y),\qquad H(a,t)=h(a,t)\in A\ (\forall a\in A,\ \forall t\in I).$$

3. **$H_1$ 分解过商空间 $Y/A$**
   在 $t=1$ 处，对一切 $a\in A$ 有 $H_1(a)=H(a,1)=a_0$。记 $*=q(A)\in Y/A$，则 $q$ 将 $A$ 映为 $*$ 且在 $Y\setminus A$ 上单射，故 $H_1$ 在 $q$ 的每个纤维上取常值。由商空间泛性质，存在唯一连续映射 $g:Y/A\to Y$ 使得 $g\circ q=H_1$（且 $g(*)=a_0$）。此时 $H$ 给出同伦 $\mathrm{id}_Y\simeq g\circ q$。

4. **同伦为何能下降到商（关键拓扑引理）**
   考虑合成映射 $\widetilde{H}:=q\circ H:Y\times I\to Y/A$。对任意 $a\in A$ 与 $t\in I$，有 $H(a,t)=h(a,t)\in A$，故
   $$\widetilde{H}(a,t)=q(H(a,t))=*.$$
   因此 $\widetilde{H}$ 在映射 $q\times\mathrm{id}_I:Y\times I\to (Y/A)\times I$ 的每个纤维（在 $(*,t)$ 处为 $A\times\{t\}$，在 $z\neq *$ 的 $(z,t)$ 处为单点集）上都取常值。
   一般拓扑中，商映射与恒同映射的乘积未必仍是商映射；但此处 **$I=[0,1]$ 是局部紧 Hausdorff 空间**，从而由 Whitehead 引理，$q\times\mathrm{id}_I$ 确实是商映射：

   > **引理 1**：设 $q:Y\to Z$ 为商映射，$K_0$ 为局部紧 Hausdorff 空间（此处取 $K_0=I$），则 $q\times\mathrm{id}_{K_0}:Y\times K_0\to Z\times K_0$ 是商映射。
   > **证明**：$q\times\mathrm{id}_{K_0}$ 满且连续。设 $W\subseteq Z\times K_0$ 满足 $\widetilde{W}:=(q\times\mathrm{id}_{K_0})^{-1}(W)$ 在 $Y\times K_0$ 中开，任取 $(z_0,t_0)\in W$。因 $q$ 满，任取 $y_0\in q^{-1}(z_0)$，则 $(y_0,t_0)\in \widetilde{W}$。因 $K_0$ 局部紧 Hausdorff 且 $\widetilde{W}$ 开，存在 $t_0$ 的开邻域 $V\subseteq K_0$ 与紧邻域 $C_0\subseteq K_0$（$V\subseteq C_0$）及 $y_0$ 的开邻域 $N_0\subseteq Y$ 使得 $N_0\times C_0\subseteq \widetilde{W}$。特别地 $\{y_0\}\times C_0\subseteq\widetilde{W}$，又 $\widetilde{W}$ 是原像集，故 $\{z_0\}\times C_0=(q\times\mathrm{id}_{K_0})(\{y_0\}\times C_0)\subseteq W$。
   > 令 $U:=\{z\in Z:\{z\}\times C_0\subseteq W\}$，则 $z_0\in U$ 且 $U\times V\subseteq U\times C_0\subseteq W$。又 $q^{-1}(U)=\{y\in Y:\{y\}\times C_0\subseteq\widetilde{W}\}$；对任意 $y\in q^{-1}(U)$，由 $C_0$ 紧且 $\widetilde{W}$ 在 $Y\times K_0$ 中开，按管状引理（Tube Lemma）存在 $y$ 的开邻域 $N_y\subseteq Y$ 使 $N_y\times C_0\subseteq\widetilde{W}$，即 $N_y\subseteq q^{-1}(U)$。故 $q^{-1}(U)$ 在 $Y$ 中开，从而由 $q$ 为商映射知 $U$ 在 $Z$ 中开。于是 $U\times V$ 是 $(z_0,t_0)$ 在 $W$ 中的开邻域，证明 $W$ 在 $Z\times K_0$ 中开。$\square$

   由引理 1，$q\times\mathrm{id}_I:Y\times I\to(Y/A)\times I$ 是商映射。由于 $\widetilde{H}=q\circ H$ 连续且在 $q\times\mathrm{id}_I$ 的各纤维上取常值，由商空间泛性质，$\widetilde{H}$ 唯一地下降为连续映射
   $$\overline{H}:(Y/A)\times I\longrightarrow Y/A,\qquad \overline{H}\circ(q\times\mathrm{id}_I)=q\circ H.$$
   对任意 $y\in Y$：
   $$\overline{H}(q(y),0)=q(H(y,0))=q(y),\qquad \overline{H}(q(y),1)=q(H_1(y))=q(g(q(y))).$$
   因 $q$ 满，这给出 $\overline{H}_0=\mathrm{id}_{Y/A}$ 与 $\overline{H}_1=q\circ g$，即 $q\circ g\simeq\mathrm{id}_{Y/A}$。连同 $g\circ q\simeq\mathrm{id}_Y$，证得 $q:Y\to Y/A$ 为同伦等价。$\blacksquare$

---

## S2 非可缩底空间上的锥附着

**结论**：$Y=D\cup_L CL\simeq D\vee\Sigma L$，且对任意楔点选择 $(d,p)\in D\times\Sigma L$ 均有 $(D,d)\vee(\Sigma L,p)\simeq Y$。

### 证明

1. **利用零伦构造中间空间 $W$**
   因包含映射 $i:L\hookrightarrow D$ 零伦，存在某点 $d_0\in D$ 与同伦 $h:L\times I\to D$，满足 $h(x,0)=x$ 且 $h(x,1)=d_0$（$\forall x\in L$）。记常值映射 $c_{d_0}:L\to D$，$c_{d_0}(x)=d_0$。
   令 $CL=(L\times I)/(L\times\{1\})$，其点记为 $[x,s]$（$[x,1]=*$ 为锥顶，$L$ 与 $L\times\{0\}$ 等同）。在 $(D\sqcup(CL\times I))$ 上，将 $((L\times\{0\})\times I)$ 按 $\widetilde{h}([x,0],t)=h(x,t)$ 粘合到 $D$，得到商空间
   $$W:=D\cup_{\widetilde{h}}(CL\times I),\qquad q_W:D\sqcup(CL\times I)\to W.$$

2. **$W$ 为 Hausdorff 空间及两端粘合子空间的同胚识别**
   $D$ 与 $CL\times I$ 皆为有限 CW 复形（从而紧 Hausdorff，进而正规），$A_h:=(L\times\{0\})\times I$ 为 $CL\times I$ 中的闭子集，且 $q_W|_D:D\to W$ 单射。对 $W$ 中任意两点 $p_1\neq p_2$：
   - 若 $p_1,p_2\in q_W(D)$，存在连续函数 $f:D\to I$ 分离之；由 Tietze 扩张定理将 $f\circ\widetilde{h}:A_h\to I$ 连续扩张为 $g:CL\times I\to I$，则 $(f,g)$ 下降为 $W\to I$ 分离 $p_1,p_2$。
   - 若至少一点（设 $p_1$）不在 $q_W(D)$ 中，则 $p_1$ 有唯一原像 $\tilde{p}_1\in (CL\times I)\setminus A_h$；在 $D$ 上取 $f\equiv 0$，利用 $CL\times I$ 的 Urysohn 引理在闭集 $A_h\cup(q_W^{-1}(p_2)\cap(CL\times I))$ 与 $\{\tilde{p}_1\}$ 间构造取值为 $0$ 和 $1$ 的连续函数 $g:CL\times I\to I$，则 $(f,g)$ 下降为 $W\to I$ 分离 $p_1,p_2$。

   故 $W$ 为 Hausdorff 空间。记 $Y_0:=q_W(D\cup(CL\times\{0\}))$ 与 $Y_1:=q_W(D\cup(CL\times\{1\}))$。自然映射 $D\cup_i CL\to Y_0$ 与 $D\cup_{c_{d_0}} CL\to Y_1$ 均为从紧空间到 Hausdorff 空间的连续双射，因而是同胚：
   $$Y_0\cong D\cup_i CL=Y,\qquad Y_1\cong D\cup_{c_{d_0}} CL.$$
   又 $D\cup_{c_{d_0}} CL$ 与 $(D,d_0)\vee(\Sigma L,s_0)$（其中 $s_0=[L\times\{0\}]\in\Sigma L$ 为悬挂南极）都是 $D\sqcup(L\times I)$ 的商空间（因子映射 $\mathrm{id}_D\sqcup\pi_{CL}$ 与 $\mathrm{id}_D\sqcup\pi_\Sigma$ 均在粘合商映射之前为商映射），且诱导完全相同的等价关系（将 $L\times\{1\}$ 捏为一点，并将 $(L\times\{0\})\sqcup\{d_0\}$ 捏为一点），故有自然同胚
   $$D\cup_{c_{d_0}} CL \cong (D,d_0)\vee(\Sigma L,s_0).$$

3. **$W$ 到 $Y_0$ 与 $Y_1$ 的强形变收缩**
   我们需要在不破坏锥顶 $s=1$ 处等价关系的条件下将 $CL\times I$ 强形变收缩到 $J_{CL}:=(CL\times\{0\})\cup((L\times\{0\})\times I)$。为此在正方形 $[0,1]^2$（坐标 $(s,t)$）上取从点 $(1,2)$ 出发向 $J:=([0,1]\times\{0\})\cup(\{0\}\times[0,1])$ 的径向投影 $r:[0,1]^2\to J$：
   $$r(s,t)=\begin{cases}
   \left(0,\dfrac{t-2s}{1-s}\right), & t\ge 2s\ (\text{此时 } s\le \tfrac12<1),\\[6pt]
   \left(\dfrac{2s-t}{2-t},0\right), & t\le 2s.
   \end{cases}$$
   两段在 $t=2s$ 处均等于 $(0,0)$，故 $r$ 连续；在 $J$ 上 $r|_J=\mathrm{id}_J$；且对 $s=1$ 恒有 $r(1,t)=(1,0)$。令直线性同伦
   $$R(s,t,u)=(1-u)(s,t)+u\,r(s,t)\in [0,1]^2\qquad (u\in I).$$
   注意在 $s=1$ 处 $R(1,t,u)=(1,(1-u)t)$，其第一坐标恒为 $1$（不依赖 $x\in L$）。由于 $I\times I$ 局部紧 Hausdorff，由引理 1 知 $\pi_{CL}\times\mathrm{id}_{I\times I}:L\times[0,1]^3\to CL\times I\times I$ 是商映射，从而
   $$\widetilde{R}([x,s],t,u):=([x,R_1(s,t,u)],R_2(s,t,u))$$
   良定义且连续，是 $CL\times I$ 到 $J_{CL}$ 上的强形变收缩（在 $J_{CL}$ 上每一点，含 $s=0$ 的 $(L\times\{0\})\times I$，在所有时刻 $u$ 保持不动）。
   于是在 $(D\sqcup(CL\times I))\times I$ 上定义 $F(d,u)=q_W(d)$，$F(z,t,u)=q_W(\widetilde{R}(z,t,u))$；在粘合处 $((L\times\{0\})\times I)\times I$ 上因 $s=0$ 不动故相容，再由引理 1（$q_W\times\mathrm{id}_I$ 为商映射），$F$ 下降为 $W\to Y_0$ 的强形变收缩。将 $t$ 换为 $1-t$，同理得 $W$ 到 $Y_1$ 的强形变收缩。
   因此包含映射 $j_0:Y_0\hookrightarrow W$ 与 $j_1:Y_1\hookrightarrow W$ 都是同伦等价，从而
   $$Y\cong Y_0\simeq W\simeq Y_1\cong (D,d_0)\vee(\Sigma L,s_0).$$

4. **楔点的选择与无关性说明**
   - 上述构造自然给出 $D$ 中楔点为零伦终点 $d_0=h(L,1)$，$\Sigma L$ 中楔点为悬挂极点 $s_0=[L\times\{0\}]$（对称地，若记 $CL=(L\times I)/(L\times\{0\})$ 或沿 $[x,t]\mapsto[x,1-t]$ 自同胚，也可取北极 $s_1=[L\times\{1\}]$，二者皆为 $\Sigma L$ 的 $0$-胞腔）。
   - **为什么对任意选择都同伦等价**：
     - 首先，因 $D$ **路径连通**，对任意 $d_1\in D$ 存在从 $d_0$ 到 $d_1$ 的路径 $\gamma:I\to D$，使 $c_{d_0}\simeq c_{d_1}:L\to D$；与第 1–3 步完全相同（将 $h$ 换为 $(x,t)\mapsto\gamma(t)$），立即得 $(D,d_0)\vee(\Sigma L,s_0)\simeq (D,d_1)\vee(\Sigma L,s_0)$。（若 $D$ 不路径连通，则必须将楔点选在 $h(L,1)$ 所在的路径连通分支内，否则同伦型会改变。）
     - 其次，因 $L\neq\emptyset$，$\Sigma L$ 自动**路径连通**（任一点 $[x,t]$ 经 $u\mapsto [x,(1-u)t]$ 连到 $s_0$）。此外，对任意有限 CW 复形 $Z$ 及任意点 $p\in Z$，单点对 $(Z,\{p\})$ 都具有 HEP（若 $p\in Z^{(0)}$，$(Z,\{p\})$ 为 CW 对由 S1 已证；若 $p\in e^n\subseteq Z^{(n)}\setminus Z^{(n-1)}$，$n\ge 1$，取特征映射 $\Phi:D^n\to Z^{(n)}$ 下 $p$ 的原像 $z_0\in\mathrm{int}(D^n)$ 及以 $z_0$ 为心的闭球 $B\cong D^n\subseteq\mathrm{int}(D^n)$，将 $[0,1]^2$ 从 $(1/2,2)$ 径向投影到 $([0,1]\times\{0\})\cup(\{0,1\}\times[0,1])$ 得 $B\times I\to (B\times\{0\})\cup(\{0\}\times I)\cup(\partial B\times I)$ 的连续收缩，从而 $(Z^{(n)},\{p\})$ 有 HEP，再与 CW 对 $(Z^{(m)},Z^{(m-1)})$ 的 HEP 有限次复合即得 $(Z,\{p\})$ 有 HEP）。
     - 于是对任意 $d_1\in D$、$p\in\Sigma L$，用一条线段 $I$ 连接它们构造 $Z(d,p):=(D\sqcup\Sigma L)\cup_{\{0\}\mapsto d,\{1\}\mapsto p} I$。由路径连通性，粘合映射 $\{0,1\}\to D\sqcup\Sigma L$ 满足 $(d_0,s_0)\simeq(d_1,p)$，而 $(I,\{0,1\})$ 为 CW 对（同前用 $(I\times I)$ 证明粘合空间的同伦不变性），故 $Z(d_0,s_0)\simeq Z(d_1,p)$。又因 $(D,\{d\})$ 与 $(\Sigma L,\{p\})$ 均有 HEP，将 $I$ 端点处的同伦各自延拓至 $D\times I$ 与 $(\Sigma L)\times I$ 并由引理 1 下降到商，即得 $(Z(d,p),I)$ 具有 HEP；因 $I$ 可缩，完全仿照 S1 将 $I$ 捏为一点给出 $Z(d,p)\simeq Z(d,p)/I\cong (D,d)\vee(\Sigma L,p)$。
     - 综上，对任意 $d_1\in D$ 与 $p\in\Sigma L$，均有 $(D,d_1)\vee(\Sigma L,p)\simeq (D,d_0)\vee(\Sigma L,s_0)\simeq Y$。$\blacksquare$

---

## S3 整数扭结的实例

**构造**：取两个不在 $V(L)$ 中的互异新顶点 $v,w$，作 $L$ 的单纯悬挂
$$K:=(v*L)\cup (w*L)=L\cup\{\tau\cup\{v\}:\tau\in L\}\cup\{\tau\cup\{w\}:\tau\in L\}\cup\{\{v\},\{w\}\}.$$
因 $|L|\cong \mathbb{R}P^2\neq\emptyset$，任取 $L$ 的一个顶点 $u\in V(L)$，取包含 $v$ 的闭 $1$-单形作为子复形：
$$B:=\{\{v\},\{u\},\{v,u\}\}\subseteq K.$$

### 验证全部性质

先证一个将在 S3–S5 中共用的基本引理：

> **引理 2（去顶强形变收缩）**：设 $M$ 为有限抽象单纯复形，$v\in V(M)$，且 $M\setminus v\neq\emptyset$。则 $|M\setminus v|$ 是 $|M|\setminus\{v\}$ 的强形变收缩核；特别地，$|M|\setminus\{v\}$ 非空可缩当且仅当 $|M\setminus v|$ 非空可缩。
> **证明**：在标准重心中坐标嵌入 $|M|\subseteq\mathbb{R}^{V(M)}$ 下，任一点 $x\in|M|\setminus\{v\}$ 的坐标满足 $x_z\ge 0$，$\sum_{z}x_z=1$，支集 $\mathrm{supp}(x)=\{z:x_z>0\}\in M$，且因 $x\neq v$ 有 $x_v<1$（故 $1-x_v>0$，且 $\mathrm{supp}(x)\setminus\{v\}\in M\setminus v$ 非空）。定义连续映射 $r:|M|\setminus\{v\}\to|M\setminus v|$ 为
> $$r(x)_v=0,\qquad r(x)_z=\frac{x_z}{1-x_v}\ (z\neq v),$$
> 并定义直线性同伦 $H:(|M|\setminus\{v\})\times I\to |M|\setminus\{v\}$ 为 $H(x,t)=(1-t)x+t\,r(x)$。当 $t<1$ 时 $\mathrm{supp}(H(x,t))=\mathrm{supp}(x)\in M$ 且 $H(x,t)_v=(1-t)x_v<1$；当 $t=1$ 时 $H(x,1)=r(x)\in|M\setminus v|$；且若 $x\in|M\setminus v|$ 则 $x_v=0$，故 $r(x)=x$、$H(x,t)=x$。故 $|M\setminus v|$ 为 $|M|\setminus\{v\}$ 的强形变收缩核。$\square$

现在逐条核对 $(K,v,B)$：
1. **复形与子复形**：$L$ 有限故 $K$ 为有限单纯复形，$v\in V(K)$，$B\subseteq K$ 为含 $v$ 的子复形。
2. **$|K|\setminus\{v\}$ 非空可缩**：$K\setminus v=w*L$ 非空，其几何实现 $|w*L|\cong C|L|$（经连续双射 $[x,t]\mapsto (1-t)x+t\,w$ 从紧空间到 Hausdorff 空间，即同胚）是锥，故非空可缩（收缩同伦 $[(x,s),u]\mapsto [(x,(1-u)s+u)]$ 缩至顶点 $w$）。由引理 2，$|K|\setminus\{v\}$ 强形变收缩至 $|K\setminus v|$，故非空可缩。
3. **$(|B|\setminus\{v\})\hookrightarrow |B|$ 为同伦等价**：$|B|$ 同胚于闭区间 $[0,1]$（$t\mapsto (1-t)u+t\,v$），$|B|\setminus\{v\}$ 同胚于半开区间 $[0,1)$。连续映射 $f:[0,1]\to[0,1)$，$f(t)=t/2$ 为包含映射 $\iota:[0,1)\hookrightarrow[0,1]$ 的同伦逆（直线性同伦 $(1-s)t+s(t/2)$ 在 $[0,1]$ 与 $[0,1)$ 内分别给出 $\mathrm{id}_{[0,1]}\simeq\iota\circ f$ 与 $\mathrm{id}_{[0,1)}\simeq f\circ\iota$）。
4. **约化有理同调全零但 $|K|$ 不可缩**：
   由 $|K|=|w*L|\cup_{|L|}|v*L|$ 且 $|w*L|\cap|v*L|=|L|$（仿第 2 步可得紧到 Hausdorff 连续双射 $\Sigma|L|\xrightarrow{\cong}|K|$），$|K|\cong \Sigma\mathbb{R}P^2$。
   在 $\Sigma|L|$ 中取开覆盖 $U=\Sigma|L|\setminus\{v\}$ 与 $V=\Sigma|L|\setminus\{w\}$，二者均为开锥，分别强形变收缩至 $w$ 与 $v$ 而可缩，且 $U\cap V\cong |L|\times(0,1)\simeq |L|$。对任意系数群 $G$，由约化奇异同调的 Mayer–Vietoris 长正合列（因为 $U,V$ 的内部覆盖全空间且 $\tilde{H}_*(U;G)=\tilde{H}_*(V;G)=0$），有悬挂同构
   $$\tilde{H}_{n+1}(|K|;G)\cong \tilde{H}_n(|L|;G)\quad(\forall n\ge 0),\qquad \tilde{H}_0(|K|;G)=0.$$
   取 $\mathbb{R}P^2=S^1\cup_{\times 2} D^2$ 的胞腔链复形（在度数 $2,1,0$ 为 $0\to\mathbb{Z}\xrightarrow{\times 2}\mathbb{Z}\xrightarrow{0}\mathbb{Z}\to 0$），得
   $$\tilde{H}_1(\mathbb{R}P^2;\mathbb{Z})\cong\mathbb{Z}/2\mathbb{Z},\qquad \tilde{H}_n(\mathbb{R}P^2;\mathbb{Z})=0\ (n\neq 1),$$
   而与 $\mathbb{Q}$ 系数对应的胞腔链复形 $0\to\mathbb{Q}\xrightarrow{\times 2}\mathbb{Q}\xrightarrow{0}\mathbb{Q}\to 0$（因为 $\times 2$ 在 $\mathbb{Q}$ 上同构）给出 $\tilde{H}_n(\mathbb{R}P^2;\mathbb{Q})=0$（$\forall n\ge 0$）。从而：
   - $\tilde{H}_n(|K|;\mathbb{Q})=0$ 对一切 $n\ge 0$ 成立；
   - $\tilde{H}_2(|K|;\mathbb{Z})\cong\tilde{H}_1(\mathbb{R}P^2;\mathbb{Z})\cong\mathbb{Z}/2\mathbb{Z}\neq 0$，故 $|K|$ 不可缩。$\blacksquare$

---

## S4 整体对象与全部恢复目标

**判定**：所列全部目标（$X$ 同伦类型的完整刻画、全部类型的实现构造、以及仅用含 $v$ 单形及其面之间有限关联数据的 $X$ 可缩充要条件）**均成立**。

### 1. 同伦类型刻画

**定理（刻画）**：在给定条件下，$X=|K|$ 可能的同伦类型**恰好**是所有非空有限抽象单纯复形 $L$ 的几何实现的非约化悬挂 $\Sigma|L|$ 的同伦类型（等价地，所有非空有限 CW 复形的非约化悬挂的同伦类型）。

**证明（必要性）**：
1. 先证 $K\setminus v\neq\emptyset$ 且 $|K\setminus v|$ 可缩。若 $K\setminus v=\emptyset$，则 $K=\{\{v\}\}$，$O=|K|\setminus\{v\}=\emptyset$，与 $O$ 非空矛盾。故 $K\setminus v\neq\emptyset$，由引理 2，$|K\setminus v|$ 是 $O$ 的强形变收缩核，从而非空可缩。
2. 再证 $\mathrm{lk}_K(v)\neq\emptyset$。若不然，$\mathrm{lk}_K(v)=\emptyset$，从而因 $B\subseteq K$ 含 $v$ 亦有 $\mathrm{lk}_B(v)=\emptyset$。于是 $B$ 中除 $\{v\}$ 外不含任何包含 $v$ 的单形。在 $|B|$ 中，重心坐标 $t_v:|B|\to I$ 连续，故开星 $\{x\in|B|:t_v(x)>0\}=\{v\}$ 在 $|B|$ 中既开又闭，即
   $$C=|B|=(|B|\setminus\{v\})\sqcup\{v\}=(O\cap C)\sqcup\{v\}$$
   为拓扑不交并。于是包含映射 $O\cap C\hookrightarrow C$ 的像不交于单点连通分支 $\{v\}$，在 $\pi_0$（及 $H_0$）上非满射，矛盾于 $O\cap C\hookrightarrow C$ 为同伦等价！故必有 $L:=\mathrm{lk}_K(v)\neq\emptyset$。
3. 有限抽象单纯复形 $K$ 的几何实现 $|K|$（因顶点有限，Euclid 子空间拓扑与以各闭单形为闭胞腔的 CW 弱拓扑一致）是有限 CW 复形，其子复形 $K\setminus v$ 与 $\mathrm{st}_K(v)$ 的几何实现都是闭 CW 子复形，满足
   $$|K|=|K\setminus v|\cup |\mathrm{st}_K(v)|,\qquad |K\setminus v|\cap |\mathrm{st}_K(v)|=|L|$$
   （因单形 $\sigma\in(K\setminus v)\cap\mathrm{st}_K(v)\iff v\notin\sigma$ 且 $\sigma\cup\{v\}\in K\iff \sigma\in L$，且对任意两子复形总有 $|M_1|\cap|M_2|=|M_1\cap M_2|$）。又紧空间 $C|L|$ 到 Hausdorff 空间 $|\mathrm{st}_K(v)|$ 的映射 $[x,t]\mapsto (1-t)x+t\,v$ 为连续双射（$t$ 由 $v$-重心坐标唯一恢复，当 $t<1$ 时 $x$ 由其余坐标除以 $1-t$ 唯一恢复），故 $|\mathrm{st}_K(v)|\cong C|L|$，从而
   $$X=|K|\cong |K\setminus v|\cup_{|L|} C|L|.$$
   由第 1 步，$D:=|K\setminus v|$ 非空可缩（从而路径连通，且任意映射 $|L|\to D$ 零伦）。应用 **S2**（其中 $D$ 路径连通有限 CW 复形、$|L|$ 为非空有限子复形且 $|L|\hookrightarrow D$ 零伦），以及 **S1**（将非空可缩子复形 $D\subseteq D\vee\Sigma|L|$ 捏为一点，等价地亦可直接对 $(X,D)$ 应用 S1 得 $X\simeq X/D\cong |\mathrm{st}_K(v)|/|L|\cong \Sigma|L|$），得
   $$X\simeq D\vee\Sigma|L|\simeq (D\vee\Sigma|L|)/D\cong\Sigma|L|.$$
   这里 $L=\mathrm{lk}_K(v)$ 为非空有限抽象单纯复形。（附注：因任何非空有限 CW 复形 $Z$ 都同伦等价于某个非空有限抽象单纯复形 $L$ 的几何实现，且悬挂保持同伦等价，故此集合亦恰好等于全体非空有限 CW 复形的悬挂的同伦类型。）$\square$

### 2. 全部类型的实现构造

**构造**：任取非空有限抽象单纯复形 $L$。与 **S3** 完全相同，取两个不在 $V(L)$ 中的互异新顶点 $v,w$，令
$$K:=(v*L)\cup (w*L),$$
任取顶点 $u\in V(L)$（存在因 $L\neq\emptyset$），令 $B:=\{\{v\},\{u\},\{v,u\}\}\subseteq K$。

**证明（充分性）**：
- $K$ 为有限单纯复形，$v\in V(K)$，$B\subseteq K$ 含 $v$；
- $K\setminus v=w*L$ 非空，$|K\setminus v|\cong C|L|$ 可缩，由引理 2 得 $O=|K|\setminus\{v\}$ 非空可缩；
- $C=|B|\cong [0,1]$，$O\cap C=|B|\setminus\{v\}\cong [0,1)$，包含映射 $[0,1)\hookrightarrow [0,1]$ 为同伦等价（同伦逆 $t\mapsto t/2$）；
- $X=|K|=|w*L|\cup_{|L|}|v*L|\cong C_-|L|\cup_{|L|} C_+|L|\cong\Sigma|L|$（因 $[x,t]\mapsto$ 上下两锥自然给出紧到 Hausdorff 的连续双射）。故刻画中的全部同伦类型均可实现。$\square$

### 3. 仅依赖含 $v$ 单形及其面有限关联数据的可缩充要条件

由题设已保证了 $\mathrm{lk}_K(v)\neq\emptyset$。记 $\mathcal{S}_v:=\{\sigma\in K:v\in\sigma\}$ 为 $K$ 中所有含 $v$ 的单形之集。$\mathcal{S}_v$ 中单形及其面构成的有限子复形正是 $\mathrm{st}_K(v)$，而链环
$$L=\mathrm{lk}_K(v)=\{\sigma\setminus\{v\}:\sigma\in\mathcal{S}_v,\ |\sigma|\ge 2\}$$
（及其各维单形 $L_k=\{\tau\in L:|\tau|=k+1\}$ 与面关联 $\tau'\subset\tau$）完全由 $\mathcal{S}_v$ 及其面之间的有限关联数据唯一决定。固定 $V(L)$ 的任一全序，定义 $L$ 的有限增广单纯链复形 $\widetilde{C}_*(L;\mathbb{Z})$：
$$\cdots\longrightarrow\mathbb{Z}^{L_2}\xrightarrow{\ \partial_2\ }\mathbb{Z}^{L_1}\xrightarrow{\ \partial_1\ }\mathbb{Z}^{L_0}\xrightarrow{\ \varepsilon\ }\mathbb{Z}\longrightarrow 0,$$
其中 $\varepsilon([u])=1$（$\forall u\in L_0$），对有序单形 $\tau=[u_0,\dots,u_k]\in L_k$（$u_0<\dots<u_k$），
$$\partial_k([u_0,\dots,u_k])=\sum_{i=0}^k (-1)^i [u_0,\dots,\widehat{u_i},\dots,u_k]$$
（此链复形也可等价地直接写为 $C_{*+1}(\mathrm{st}_K(v),L;\mathbb{Z})$ 的相对边界矩阵：将 $v$ 放在最前，含 $v$ 的 $(k+1)$-单形 $[v,u_0,\dots,u_k]$ 对应 $L_k$，含 $v$ 的单点 $\{v\}$ 对应 $\mathbb{Z}$，只出现 $\mathcal{S}_v$ 单形间的余维 $1$ 面关联符号）。

**充要判据**：$X=|K|$ 可缩**当且仅当** $L=\mathrm{lk}_K(v)$ 的整系数约化单纯同调全为零：
$$\widetilde{H}_k^{\mathrm{simp}}(L;\mathbb{Z})=0\qquad (\forall\,0\le k\le \dim L)$$
（即上述有限整矩阵链复形 $\widetilde{C}_*(L;\mathbb{Z})$ 正合：$\ker\varepsilon=\operatorname{im}\partial_1$，且对 $1\le k\le \dim L$ 有 $\ker\partial_k=\operatorname{im}\partial_{k+1}$；用有限整数矩阵的标准型也可等价表述为：对所有 $k\ge 0$ 记 $\partial_0:=\varepsilon$，有 $\operatorname{rank}(\partial_k)+\operatorname{rank}(\partial_{k+1})=|L_k|$，且 $\partial_{k+1}$ 的 Smith 标准型中所有非零不变因子均为 $1$）。

**证明**：
因为 $L$ 为有限抽象单纯复形，$|L|$ 具有以各单形为胞腔的正则 CW 结构，其胞腔链复形与有序单纯链复形自然同构，故 $\widetilde{H}_k^{\mathrm{simp}}(L;\mathbb{Z})\cong \tilde{H}_k(|L|;\mathbb{Z})$（$\forall k\ge 0$）。又由第 1 节已证 $X\simeq \Sigma|L|$，故 $X$ 可缩当且仅当 $\Sigma|L|$ 可缩。

- **必要性**：若 $X$ 可缩，则 $\Sigma|L|$ 可缩，故对一切 $n\ge 0$ 有 $\tilde{H}_n(\Sigma|L|;\mathbb{Z})=0$。由 **S3** 已证的悬挂同构（取 $G=\mathbb{Z}$），对一切 $k\ge 0$ 有
  $$\widetilde{H}_k^{\mathrm{simp}}(L;\mathbb{Z})\cong\tilde{H}_k(|L|;\mathbb{Z})\cong\tilde{H}_{k+1}(\Sigma|L|;\mathbb{Z})=0.$$
- **充分性**：设 $\widetilde{H}_k^{\mathrm{simp}}(L;\mathbb{Z})=0$ 对一切 $k\ge 0$ 成立，从而 $\tilde{H}_k(|L|;\mathbb{Z})=0$（$\forall k\ge 0$）。
  1. 因 $L\neq\emptyset$ 且 $\tilde{H}_0(|L|;\mathbb{Z})=0$，$|L|$ **路径连通**。
  2. 在 $\Sigma|L|$ 中取开集 $U=\Sigma|L|\setminus\{s_1\}$ 与 $V=\Sigma|L|\setminus\{s_0\}$。$U$ 与 $V$ 均为开锥从而可缩（$\pi_1(U)=\pi_1(V)=1$），且 $U\cap V\cong |L|\times(0,1)$ 因 $|L|$ 非空路径连通而**路径连通**。满足 Seifert–van Kampen 定理全部前提（$U,V$ 为覆盖全空间的开路径连通子集，且 $U\cap V$ 路径连通），故 $\pi_1(\Sigma|L|)$ 由 $\pi_1(U)$ 与 $\pi_1(V)$ 的像生成，从而 $\pi_1(\Sigma|L|)=1$（单连通）。
  3. 再由悬挂同构，对所有 $n\ge 1$ 有 $\tilde{H}_n(\Sigma|L|;\mathbb{Z})\cong\tilde{H}_{n-1}(|L|;\mathbb{Z})=0$，且因 $\Sigma|L|$ 路径连通有 $\tilde{H}_0(\Sigma|L|;\mathbb{Z})=0$。
  4. $\Sigma|L|$ 是单连通有限 CW 复形（在 $s_0,s_1$ 取 $0$-胞腔，对 $L$ 的每个 $k$-单形 $\tau$ 取 $(k+1)$-胞腔 $\mathring{\tau}\times(0,1)$）。若存在 $n\ge 2$ 使 $\pi_n(\Sigma|L|)\neq 0$，取最小的此类 $n\ge 2$，则 $\Sigma|L|$ 是 $(n-1)$-连通的；由 **Hurewicz 定理**，Hurewicz 同态 $\pi_n(\Sigma|L|)\to H_n(\Sigma|L|;\mathbb{Z})$ 为同构，但 $H_n(\Sigma|L|;\mathbb{Z})=0$，矛盾。故对一切 $n\ge 0$ 有 $\pi_n(\Sigma|L|)=0$，即常值映射 $\Sigma|L|\to\{*\}$ 是弱同伦等价。
  5. 因 $\Sigma|L|$ 与 $\{*\}$ 皆为 CW 复形，由 **Whitehead 定理**，该弱同伦等价是同伦等价，即 $\Sigma|L|$ 可缩，从而 $X\simeq\Sigma|L|$ 可缩。

> **注**：该判据只要求 $L$ **$\mathbb{Z}$-无圈**（$\tilde{H}_*(L;\mathbb{Z})=0$），而不要求 $L$ 本身可缩（例如若 $L$ 取二元二十面体群 $SL(2,5)$ 的平衡展示 $2$-复形或穿孔 Poincaré 同调 $3$-球面的三角剖分，$|L|$ 不可缩但 $\Sigma|L|$ 可缩）；同时由 **S3** 知，仅在 $\mathbb{Q}$ 上检验无圈（只看矩阵秩而不看 $\mathbb{Z}$-不变因子）是**不够**的。$\blacksquare$

---

## S5 不提供子复形 $B$

**判定**：**不必**同伦等价于非空有限复形的悬挂。
**新增可能类型的完整分类**：仅新增**唯一一个**同伦类型，即两点离散空间 $S^0$（亦可视为空复形的悬挂 $\Sigma\emptyset$）。

### 证明

1. **所有可能类型的二分法**：
   由 $|K|\setminus\{v\}$ 非空知 $K\setminus v\neq\emptyset$，故由引理 2 知 $|K\setminus v|$ 非空可缩。设 $L:=\mathrm{lk}_K(v)$。
   - **情形 1（$L\neq\emptyset$）**：虽未给定 $B$，但正如 S4 必要性证明第 3 步所示，$|K|\simeq\Sigma|L|$ 的推导**并未用到 $B$**，仅用到了 $K\setminus v$ 非空可缩与 $L\neq\emptyset$。因此只要 $L\neq\emptyset$，$|K|$ 仍必同伦等价于非空有限单纯复形 $L$ 的悬挂 $\Sigma|L|$。
   - **情形 2（$L=\emptyset$）**：此时 $v$ 为孤立顶点，$K=(K\setminus v)\sqcup\{\{v\}\}$，无任何单形同时包含 $v$ 与 $K\setminus v$ 的顶点。在 $|K|$ 中 $\{v\}=\{x\in|K|:t_v(x)>0\}$ 既开又闭，故拓扑上有不交并分解
     $$|K|=|K\setminus v|\sqcup \{v\}.$$
     因 $|K\setminus v|$ 非空可缩，将其与一点同伦等价并各自映至 $S^0=\{0,1\}$ 的两点，得 $|K|\simeq S^0$。

2. **$S^0$ 确实可实现且不属于原类型**：
   - **实现**：取两个孤立顶点 $K=\{\{v\},\{w\}\}$，则 $|K|\setminus\{v\}=\{w\}$ 非空可缩，而 $|K|=\{v,w\}=S^0$。
   - **非原类型证明**：对**任意非空**空间（特别地任意非空有限复形）$Y$，任取 $y_0\in Y$，则 $\Sigma Y$ 中任一点 $[y,t]$ 经路径 $u\mapsto [y,(1-u)t]$ 连至南极 $s_0$，又 $s_0$ 经 $u\mapsto [y_0,u]$ 连至北极 $s_1$，故 $\Sigma Y$ 必**路径连通**（$|\pi_0(\Sigma Y)|=1$）。而 $|\pi_0(S^0)|=2$。因 $|\pi_0(\cdot)|$ 为同伦不变量，$S^0$ 不可能同伦等价于任何非空有限复形的悬挂。$\blacksquare$

---

## S6 悬挂信息的逆向恢复

**判定**：**不必**推出 $|L_1|\simeq|L_2|$。存在明确的非空有限单纯复形反例。

### 反例构造

取 $|L_1|\cong T^2=S^1\times S^1$ 与 $|L_2|\cong S^1\vee S^1\vee S^2$ 的有限单纯剖分：
- **构造 $L_1$**：取顶点集 $V_1=(\mathbb{Z}/3\mathbb{Z})\times(\mathbb{Z}/3\mathbb{Z})$（共 $9$ 个顶点），以如下 $18$ 个三角形的所有非空面构成 $L_1$：对每个 $(i,j)\in(\mathbb{Z}/3\mathbb{Z})^2$，
  $$\sigma_{i,j}^+=\{(i,j),(i+1,j),(i+1,j+1)\},\qquad \sigma_{i,j}^-=\{(i,j),(i,j+1),(i+1,j+1)\}.$$
  验证这确为有效抽象单纯剖分且 $|L_1|\cong T^2$：$\sigma_{i,j}^+$ 的第二坐标重集为 $\{j,j,j+1\}$，而 $\sigma_{i',j'}^-$ 的第二坐标重集为 $\{j',j'+1,j'+1\}$，在 $\mathbb{Z}/3\mathbb{Z}$ 中若重集相等则必 $j=j'+1$ 且 $j+1=j'$，矛盾于 $2\not\equiv 0\pmod 3$；同型内部比较重集及横坐标对 $\{i,i+1\}=\{i',i'+1\}$ 亦迫使 $(i,j)=(i',j')$；边集 $\{p,p+e\}$（$e\in\{e_1,e_2,e_1+e_2\}$）在 $\mathbb{Z}/3\mathbb{Z}$ 中因 $e\neq -e'$ 也两两互异。故网格 $[0,3]^2/(3\mathbb{Z})^2\cong T^2$ 给出同胚 $|L_1|\cong T^2$。
- **构造 $L_2$**：取 $8$ 个顶点 $V_2=\{x_0,a_1,a_2,b_1,b_2,c_1,c_2,c_3\}$，以两条三边圈 $\{x_0,a_1\},\{a_1,a_2\},\{a_2,x_0\}$ 与 $\{x_0,b_1\},\{b_1,b_2\},\{b_2,x_0\}$ 以及 $3$-单形 $\{x_0,c_1,c_2,c_3\}$ 的全部真非空面构成 $L_2$。三个子复形两两仅交于 $x_0$，故 $|L_2|\cong S^1\vee S^1\vee S^2$。

### 证明 $\Sigma|L_1|\simeq\Sigma|L_2|$ 且 $|L_1|\not\simeq|L_2|$

1. **证明 $\Sigma|L_1|\simeq S^2\vee S^2\vee S^3$**：
   将 $T^2=(\mathbb{R}/3\mathbb{Z})^2$ 看作标准 CW 复形：一个 $0$-胞腔 $x_0=[(0,0)]$，两个 $1$-胞腔 $a,b$ 构成 $1$-骨架 $S^1\vee S^1$，以及一个 $2$-胞腔 $[0,3]^2$ 沿映射 $\varphi:(S^1,1)\to (S^1\vee S^1,x_0)$ 粘合而成，即
   $$T^2\cong (S^1\vee S^1)\cup_\varphi D^2,$$
   其中 $[\varphi]=[a,b]=aba^{-1}b^{-1}\in \pi_1(S^1\vee S^1,x_0)$。

   首先，因为 $I$ 局部紧 Hausdorff，由引理 1 知 $((S^1\vee S^1)\sqcup D^2)\times I\to T^2\times I\to \Sigma T^2$ 与 $((S^1\vee S^1)\sqcup D^2)\times I\to \Sigma(S^1\vee S^1)\sqcup \Sigma D^2\to \Sigma(S^1\vee S^1)\cup_{\Sigma\varphi}\Sigma D^2$ 均为商映射且诱导相同的等价关系（$\partial D^2=S^1\neq\emptyset$ 将两者的上下极点分别粘合在一起），故
   $$\Sigma T^2 \cong \Sigma(S^1\vee S^1)\cup_{\Sigma\varphi}\Sigma D^2.$$
   将 $I$ 参数化为 $[-1,1]$，映射 $(z,t)\in D^2\times[-1,1]\mapsto(\sqrt{1-t^2}\,z,t)\in D^3$ 是紧到 Hausdorff 的连续满射，仅将 $D^2\times\{\pm 1\}$ 捏为 $(0,\pm 1)$，故诱导同胚 $\Sigma D^2\cong D^3$ 并限制为边界同胚 $\Sigma S^1\cong S^2$。从而
   $$\Sigma T^2 \cong \Sigma(S^1\vee S^1)\cup_{\Sigma\varphi} D^3.$$

   其次，记约化悬挂 $\widetilde{\Sigma}(Z,z_0):=(Z\times I)/(Z\times\{0,1\}\cup\{z_0\}\times I)$，并取基点 $x_0\in S^1\vee S^1$ 与 $1\in S^1$。因 $\{x_0\}\times I$ 是有限 CW 复形 $\Sigma(S^1\vee S^1)$ 的非空可缩子复形（在由 $s_0,s_1$ 和 $1$-胞腔 $\{x_0\}\times(0,1)$ 构成的子复形上同胚于 $I$），由 **S1** 知商映射
   $$q_1:\Sigma(S^1\vee S^1)\longrightarrow \Sigma(S^1\vee S^1)/(\{x_0\}\times I)=\widetilde{\Sigma}(S^1\vee S^1)$$
   是同伦等价。又因 $\varphi(1)=x_0$，有 $q_1\circ\Sigma\varphi=(\widetilde{\Sigma}\varphi)\circ q_0$（其中 $q_0:\Sigma S^1\to\widetilde{\Sigma} S^1$）。

   将 $S^1=I/\{0,1\}$，则 $\widetilde{\Sigma} S^1=I^2/\partial I^2\cong S^2$。对任意两圈 $f,g:(I/\{0,1\},0)\to (Z,z_0)$，按定义 $\widetilde{\Sigma}(f\cdot g):I^2/\partial I^2\to\widetilde{\Sigma} Z$ 在 $[0,1/2]\times I$ 上为 $\widetilde{\Sigma} f([2u,t])$，在 $[1/2,1]\times I$ 上为 $\widetilde{\Sigma} g([2u-1,t])$，这恰好是 $\pi_2(\widetilde{\Sigma} Z,*)$ 中的加法 $[\widetilde{\Sigma} f]+[\widetilde{\Sigma} g]$。故悬挂诱导映射 $\Sigma_*:\pi_1(S^1\vee S^1,x_0)\to\pi_2(\widetilde{\Sigma}(S^1\vee S^1),*)$ 是群同态。由于任何空间的第二同伦群 $\pi_2$ 都**交换**，而 $[\varphi]=[a,b]$ 为交换子，必有
   $$[\widetilde{\Sigma}\varphi]=\Sigma_*([a,b])=0\in\pi_2(\widetilde{\Sigma}(S^1\vee S^1),*),$$
   即 $\widetilde{\Sigma}\varphi$ 零伦。从而 $q_1\circ\Sigma\varphi=(\widetilde{\Sigma}\varphi)\circ q_0$ 零伦；再与 $q_1$ 的同伦逆复合（并利用 $\Sigma(S^1\vee S^1)$ 路径连通）知 $\Sigma\varphi:S^2\to\Sigma(S^1\vee S^1)$ 同伦于常值映射 $c_{s_0}$。

   又 $(D^3,S^2)$ 为 CW 对（或视 $D^3=C S^2$，完全同 **S2** 第 3 步用 $W=\Sigma(S^1\vee S^1)\cup_H(D^3\times I)$ 的强形变收缩），将粘合映射 $\Sigma\varphi$ 替换为同伦的常值映射 $c_{s_0}$ 保持同伦型，得
   $$\Sigma T^2\cong \Sigma(S^1\vee S^1)\cup_{\Sigma\varphi} D^3\simeq \Sigma(S^1\vee S^1)\cup_{c_{s_0}} D^3 \cong (\Sigma(S^1\vee S^1),s_0)\vee (D^3/S^2,*)\cong (\Sigma(S^1\vee S^1),s_0)\vee (S^3,*).$$
   在最后这个空间中，$A=\{x_0\}\times I\subseteq \Sigma(S^1\vee S^1)$ 是包含楔点 $s_0=(x_0,0)$ 的非空可缩子复形，再次由 **S1** 捏去 $A$（将 $s_0$ 所在端保持与 $S^3$ 基点重合）得同伦等价
   $$(\Sigma(S^1\vee S^1),s_0)\vee (S^3,*)\xrightarrow{\ \simeq\ } \widetilde{\Sigma}(S^1\vee S^1)\vee S^3 \cong \widetilde{\Sigma} S^1\vee \widetilde{\Sigma} S^1\vee S^3\cong S^2\vee S^2\vee S^3$$
   （其中对 $n\ge 1$，记 $S^n=D^n/\partial D^n$，因 $I$ 局部紧 Hausdorff，$(D^n\to S^n)\times\mathrm{id}_I$ 是商映射，故 $\widetilde{\Sigma} S^n$ 与 $D^{n+1}/\partial D^{n+1}\cong S^{n+1}$ 均作为 $(D^n\times I)/\partial(D^n\times I)$ 而自然同胚）。

2. **证明 $\Sigma|L_2|\simeq S^2\vee S^2\vee S^3$**：
   在 $\Sigma|L_2|=\Sigma(S^1\vee S^1\vee S^2)$ 中，取 $A=\{x_0\}\times I$，它是有限 CW 复形 $\Sigma(S^1\vee S^1\vee S^2)$ 的非空可缩子复形。由 **S1**，捏去 $A$ 给出同伦等价
   $$\Sigma|L_2|\xrightarrow{\ \simeq\ }\widetilde{\Sigma}(S^1\vee S^1\vee S^2)\cong \widetilde{\Sigma} S^1\vee \widetilde{\Sigma} S^1\vee \widetilde{\Sigma} S^2\cong S^2\vee S^2\vee S^3.$$
   综合 1 与 2，即有 $\Sigma|L_1|\simeq S^2\vee S^2\vee S^3\simeq\Sigma|L_2|$。

3. **证明 $|L_1|\not\simeq |L_2|$**：
   - $|L_1|\cong S^1\times S^1$ 的基本群为 $\pi_1(|L_1|)\cong \pi_1(S^1)\times\pi_1(S^1)\cong \mathbb{Z}\times\mathbb{Z}$，是交换群。
   - $|L_2|\cong S^1\vee S^1\vee S^2$ 中，在楔点 $x_0$ 周围取分别包含三个分支及另两分支小可缩开邻域的开集覆盖，各开集交均可缩且路径连通，满足 Seifert–van Kampen 定理前提，故 $\pi_1(|L_2|)\cong \pi_1(S^1)*\pi_1(S^1)*\pi_1(S^2)\cong \mathbb{Z}*\mathbb{Z}$（二元自由群），是非交换群。

   因同伦等价的路径连通空间必有同构的基本群，而 $\mathbb{Z}\times\mathbb{Z}\not\cong \mathbb{Z}*\mathbb{Z}$，故 $|L_1|\not\simeq |L_2|$。$\blacksquare$
