{}
以下按 **S1–S6** 逐项给出完整解答。全文记 $I = [0,1]$。对拓扑空间 $Z$，其**非约化锥**定义为 $CZ = (Z \times [0,1]) / (Z \times \{1\})$（将底面 $Z \times \{0\}$ 与 $Z$ 等同，锥顶记为 $v_+ = [Z \times \{1\}]$）；当 $Z \neq \emptyset$ 时，其**非约化悬挂**定义为
$$\Sigma Z = (Z \times [0,1]) / \big(Z \times \{0\} \sim v_-,\; Z \times \{1\} \sim v_+\big) \cong CZ / (Z \times \{0\}).$$
对有限抽象单纯复形 $K$，统一约定其由有限顶点集 $V(K)$ 上的若干**非空**子集（单形）组成，并对取非空子集封闭；其几何实现 $|K|$ 取通常欧氏（等价于有限 CW）拓扑。

---

## S1 可缩子复形的商

### 结论与证明

商映射 $q: Y \to Y/A$ 是同伦等价。证明分三步。

**第一步：有限 CW 对 $(Y,A)$ 满足同伦延拓性质（HEP）。**
由于 $Y$ 是有限 CW 复形，$A \subset Y$ 是子复形，$Y$ 可由 $A$ 依维数不减地逐个粘附有限多个胞腔得到：
$$A = Y_0 \subset Y_1 \subset \cdots \subset Y_m = Y, \qquad Y_k = Y_{k-1} \cup_{\varphi_k} D^{n_k}.$$
对每个 $n \ge 0$，在 $\mathbb{R}^n \times \mathbb{R}$ 中从点 $(0,2)$ 作径向投影，即得从 $D^n \times I$ 到闭子集 $D^n \times \{0\} \cup \partial D^n \times I$ 的连续收缩映射（当 $n=0$ 时 $D^0 \times \{0\} \cup \emptyset \times I = D^0 \times \{0\}$？注意 $n=0$ 时 $\partial D^0 = \emptyset$，粘附 $0$-胞腔即无交并 $Y_k = Y_{k-1} \sqcup \{e^0\}$，在 $\{e^0\} \times I$ 上直接取常值延拓 $H(e^0,t)=f(e^0)$ 即可；当 $n \ge 1$ 时上述径向投影给出 $D^n \times I \to D^n \times \{0\} \cup \partial D^n \times I$ 的收缩）。因 $I$ 紧 Hausdorff，特征映射与 $\mathrm{id}_I$ 的乘积展示 $Y_k \times I \cong (Y_{k-1} \times I) \cup_{\partial D^{n_k} \times I} (D^{n_k} \times I)$。关于 $k=1,\dots,m$ 归纳延拓，可知 $(Y,A)$ 具有同伦延拓性质：凡连续映射 $f: Y \to Z$ 与同伦 $h: A \times I \to Z$ 满足 $h(-,0) = f|_A$，均存在连续延拓 $H: Y \times I \to Z$ 使得 $H(-,0)=f$ 且 $H|_{A \times I} = h$。

**第二步：构造同伦逆 $g: Y/A \to Y$ 及同伦 $g \circ q \simeq \mathrm{id}_Y$。**
因 $A$ 非空可缩，取定 $a_0 \in A$，存在收缩同伦 $h: A \times I \to A$ 使得对一切 $a \in A$ 有 $h(a,0) = a$ 及 $h(a,1) = a_0$。记包含映射为 $i: A \hookrightarrow Y$。对 $\mathrm{id}_Y : Y \to Y$ 与 $i \circ h : A \times I \to Y$ 应用第一步的 HEP（二者在 $A \times \{0\}$ 上均等于 $i$），得连续同伦 $H: Y \times I \to Y$ 满足：
$$H(y,0) = y \quad (\forall y \in Y), \qquad H(a,t) = h(a,t) \in A \quad (\forall a \in A,\; \forall t \in I).$$
令 $f: Y \to Y$ 为 $f(y) = H(y,1)$。对任意 $a \in A$，有 $f(a) = h(a,1) = a_0$，即 $f$ 在 $A$ 上取常值，从而在 $q: Y \to Y/A$ 的每条纤维上取常值。由商拓扑的泛性质，存在唯一连续映射 $g: Y/A \to Y$ 使得 $g \circ q = f$。于是 $H$ 给出从 $\mathrm{id}_Y = H(-,0)$ 到 $f = g \circ q = H(-,1)$ 的同伦，即 $g \circ q \simeq \mathrm{id}_Y$。

**第三步：说明同伦为何能下降到商，并证 $q \circ g \simeq \mathrm{id}_{Y/A}$。**
考虑复合连续映射 $q \circ H : Y \times I \to Y/A$。要使它沿满射 $q \times \mathrm{id}_I : Y \times I \to (Y/A) \times I$ 下降为连续同伦 $\widetilde{H}: (Y/A) \times I \to Y/A$，需且仅需以下两条机制同时成立：
1. **集合层面的纤维相容性（全时刻保子空间 $A$）**：由于 $H$ 延拓的是 $A$ **内部**的收缩同伦 $h: A \times I \to A$，对**每一个**时刻 $t \in I$ 都有 $H(A \times \{t\}) \subseteq A$（而不仅在 $t=0,1$ 处落入 $A$）。因此对任意 $a \in A$ 与 $t \in I$，$(q \circ H)(a,t) = [A]$（商空间中 $A$ 坍缩成的基点），与 $a$ 的选取无关。这保证 $q \circ H$ 在 $q \times \mathrm{id}_I$ 的每个等价类（形如 $A \times \{t\}$ 或 $\{y\} \times \{t\}$，$y \notin A$）上为常值，从而唯一诱导出良定义的集合映射 $\widetilde{H}: (Y/A) \times I \to Y/A$，满足 $\widetilde{H}(q(y), t) = q(H(y,t))$。
2. **拓扑层面的连续性（商映射与 $I$ 的乘积仍为商映射）**：一般拓扑中商映射与任意空间的乘积未必仍是商映射；但此处有两个充分理由保证 $q \times \mathrm{id}_I : Y \times I \to (Y/A) \times I$ 是商映射：
   - **Whitehead 定理**：区间 $I = [0,1]$ 是局部紧 Hausdorff 空间，任何商映射 $q$ 与局部紧 Hausdorff 空间上的恒等映射 $\mathrm{id}_I$ 的乘积 $q \times \mathrm{id}_I$ 必为商映射；
   - **紧 Hausdorff 判据**（直接利用有限 CW 条件）：有限 CW 复形 $Y$ 是紧 Hausdorff 空间，$Y/A$ 亦为有限 CW 复形（其 $0$-胞腔为 $[A]$ 及 $Y \setminus A$ 的 $0$-胞腔，高维胞腔为 $Y \setminus A$ 的高维胞腔），故 $(Y/A) \times I$ 是 Hausdorff 空间；从紧空间 $Y \times I$ 到 Hausdorff 空间 $(Y/A) \times I$ 的连续满射 $q \times \mathrm{id}_I$ 必为闭映射，从而是商映射。

由商映射 $q \times \mathrm{id}_I$ 的泛性质，$\widetilde{H} \circ (q \times \mathrm{id}_I) = q \circ H$ 的连续性直接推出 $\widetilde{H}: (Y/A) \times I \to Y/A$ 连续。检验端点：对任意 $y \in Y$，
$$\widetilde{H}(q(y), 0) = q(H(y,0)) = q(y) = \mathrm{id}_{Y/A}(q(y)), \qquad \widetilde{H}(q(y), 1) = q(H(y,1)) = q(f(y)) = (q \circ g)(q(y)).$$
因 $q$ 为满射，故 $\widetilde{H}$ 给出 $\mathrm{id}_{Y/A} \simeq q \circ g$。综上，$q: Y \to Y/A$ 是同伦等价。$\blacksquare$

---

## S2 非可缩底空间上的锥附着

### 结论与证明

对任意楔点选取 $(d, z) \in D \times \Sigma L$，均有 $Y = D \cup_L CL \simeq (D, d) \vee (\Sigma L, z)$。以下先证粘附映射同伦不变引理，再导出同伦等价并详细说明楔点选择。

**引理（锥附着关于粘附映射的同伦不变性）**
设 $D$ 为拓扑空间，$L$ 为非空拓扑空间，$f_0, f_1 : L \to D$ 为两个连续映射，$F: L \times I \to D$ 为从 $f_0 = F(-,0)$ 到 $f_1 = F(-,1)$ 的同伦。则贴空间 $Y_0 = D \cup_{f_0} CL$ 与 $Y_1 = D \cup_{f_1} CL$ 同伦等价。

*引理的证明*：将 $Y_0$ 与 $Y_1$ 中来自 $CL$ 的点分别记作 $[x,s]_0$ 与 $[x,s]_1$（$x \in L, s \in [0,1]$），其中 $[x,0]_k = f_k(x) \in D$，锥顶为 $[x,1]_k = v_+^{(k)}$（$k=0,1$）。定义 $\Phi_F : Y_0 \to Y_1$ 为：在 $D$ 上取 $\mathrm{id}_D$，在 $CL$ 上取
$$\Phi_F([x,s]_0) = \begin{cases} F(x, 2s) \in D, & 0 \le s \le \tfrac{1}{2}, \\ [x, 2s-1]_1 \in CL, & \tfrac{1}{2} \le s \le 1. \end{cases}$$
检验粘合条件：当 $s=0$ 时 $F(x,0)=f_0(x)=\Phi_F(f_0(x))$；当 $s=\frac{1}{2}$ 时 $F(x,1)=f_1(x)=[x,0]_1$；当 $s=1$ 时 $[x,1]_1 = v_+^{(1)}$ 与 $x$ 无关。因 $D \sqcup (L \times I) \to Y_0$ 是商映射，由闭集粘合引理与商拓扑泛性质知 $\Phi_F$ 良定义且连续。

令反向同伦为 $\overline{F}(x,t) = F(x, 1-t)$（从 $f_1$ 到 $f_0$），同理得到连续映射 $\Phi_{\overline{F}} : Y_1 \to Y_0$。计算复合 $\Phi_{\overline{F}} \circ \Phi_F : Y_0 \to Y_0$：它在 $D$ 上为 $\mathrm{id}_D$，而在 $[x,s]_0$ 上分三段取值：$s \in [0,\frac{1}{2}]$ 时为 $F(x,2s)$，$s \in [\frac{1}{2}, \frac{3}{4}]$ 时为 $F(x, 3-4s)$，$s \in [\frac{3}{4}, 1]$ 时为 $[x, 4s-3]_0$。定义 $H: Y_0 \times I \to Y_0$ 为：对 $d \in D, \tau \in I$ 取 $H(d,\tau) = d$；对 $[x,s]_0 \in CL, \tau \in I$ 取
$$H([x,s]_0, \tau) = \begin{cases} F(x, 2s) \in D, & 0 \le s \le \dfrac{1-\tau}{2}, \\[6pt] F\big(x, 3(1-\tau)-4s\big) \in D, & \dfrac{1-\tau}{2} \le s \le \dfrac{3(1-\tau)}{4}, \\[8pt] \left[x, \dfrac{4s - 3(1-\tau)}{1+3\tau}\right]_0 \in CL, & \dfrac{3(1-\tau)}{4} \le s \le 1. \end{cases}$$
对一切 $\tau \in [0,1]$：$1+3\tau \ge 1 > 0$；各分界处取值分别为 $F(x, 1-\tau)$（$s=\frac{1-\tau}{2}$）与 $F(x,0) = f_0(x) = [x,0]_0$（$s=\frac{3(1-\tau)}{4}$）；在 $s=0$ 处恒为 $F(x,0)=f_0(x)$，在 $s=1$ 处恒为 $[x,1]_0 = v_+^{(0)}$。由 S1 中所述的 Whitehead 定理（$I$ 局部紧 Hausdorff），$(D \sqcup (L \times I)) \times I \to Y_0 \times I$ 是商映射，故 $H$ 连续。又 $H(-,0) = \Phi_{\overline{F}} \circ \Phi_F$，$H(-,1) = \mathrm{id}_{Y_0}$，故 $\Phi_{\overline{F}} \circ \Phi_F \simeq \mathrm{id}_{Y_0}$。将 $(f_0, f_1, F)$ 与 $(f_1, f_0, \overline{F})$ 互换即得 $\Phi_F \circ \Phi_{\overline{F}} \simeq \mathrm{id}_{Y_1}$。引理证毕。

**主结论 $Y \simeq D \vee \Sigma L$ 的导出**
已知包含映射 $i: L \hookrightarrow D$ 零伦，故存在点 $d_0 \in D$ 及同伦 $F: L \times I \to D$ 使得 $F(-,0) = i$ 且 $F(-,1) = c_{d_0}$（取值于 $d_0$ 的常值映射）。由上述引理，
$$Y = D \cup_i CL \simeq D \cup_{c_{d_0}} CL.$$
由于 $L \neq \emptyset$，$D \cup_{c_{d_0}} CL$ 与楔和 $(D, d_0) \vee (\Sigma L, v_-)$ 都是无交并 $D \sqcup (L \times [0,1])$ 按**完全相同的等价关系**（对所有 $x,x' \in L$ 认同 $(x,1) \sim (x',1)$ 为北极 $v_+$，并认同 $(x,0) \sim d_0$，即在 $\Sigma L$ 中将 $L \times \{0\}$ 坍缩为南极 $v_-$ 再与 $d_0 \in D$ 粘合）取商所得的商空间（两步商映射的复合仍为商映射）。因此有典范同胚
$$D \cup_{c_{d_0}} CL \cong (D, d_0) \vee (\Sigma L, v_-),$$
从而 $Y \simeq (D, d_0) \vee (\Sigma L, v_-)$。

**楔点的选择说明**
1. **构造给出的自然楔点**：上述证明直接给出的楔点，在 $D$ 一侧是零伦 $F$ 的终点 $d_0 \in D$，在 $\Sigma L$ 一侧是非约化悬挂的南极 $v_- = [L \times \{0\}]$（由翻转悬挂参数 $s \mapsto 1-s$ 的同胚，对称地也可取北极 $v_+ = [L \times \{1\}]$）。
2. **$D$ 侧楔点的任意性（依赖 $D$ 路径连通）**：因为 $D$ 是**路径连通**的，对任意点 $d \in D$，存在路径 $\gamma: I \to D$ 连接 $d_0$ 到 $d$。将零伦 $F$ 与同伦 $(x,t) \mapsto \gamma(t)$ 拼接，知包含映射 $i: L \hookrightarrow D$ 同样零伦于常值映射 $c_d$。再次应用上述引理，即得对**任意** $d \in D$ 均有 $Y \simeq (D, d) \vee (\Sigma L, v_-)$。特别地，可取 $d = d_* \in D^0$ 为 $D$ 的一个 $0$-胞腔，使该楔和自然成为有限 CW 复形。（注：若去掉 $D$ 路径连通的假设，将 $\Sigma L$ 楔在不同路径连通分支上会改变整体同伦型。）
3. **$\Sigma L$ 侧楔点的任意性（依赖 $L$ 非空及有限 CW 结构）**：
   - 因 $L \neq \emptyset$，取定 $x_0 \in L$，则 $\Sigma L$ 中任一点 $[x,s]$ 可由路径 $t \mapsto [x, (1-t)s]$ 连至南极 $v_- = [x_0, 0]$，故 $\Sigma L$ **路径连通**。
   - 先固定 $D$ 的一个 $0$-胞腔 $d_* \in D^0$，则 $(D, \{d_*\})$ 是有限 CW 对。对任意点 $z \in \Sigma L$，楔和 $(D, d_*) \vee (\Sigma L, z)$ 就是贴空间 $\Sigma L \cup_{f_z} D$，其中 $f_z: \{d_*\} \to \Sigma L$ 定义为 $f_z(d_*) = z$。取 $\Sigma L$ 中从 $v_-$ 到 $z$ 的路径 $\eta: I \to \Sigma L$，考虑空间 $W = \Sigma L \cup_\eta (D \times I)$。由 S1 第一步对有限 CW 对 $(D, \{d_*\})$ 的证明（分别对端点 $t=0$ 与 $t=1$ 使用），$D \times \{0\} \cup \{d_*\} \times I$ 与 $D \times \{1\} \cup \{d_*\} \times I$ 都是 $D \times I$ 的强形变收缩核；将该形变收缩推推出到贴空间 $W$（同样利用 $I$ 局部紧 Hausdorff 保证商映射乘 $\mathrm{id}_I$ 仍为商映射），即知 $\Sigma L \cup_{f_{v_-}} D$ 与 $\Sigma L \cup_{f_z} D$ 均为 $W$ 的强形变收缩核，从而 $(D, d_*) \vee (\Sigma L, v_-) \simeq (D, d_*) \vee (\Sigma L, z)$。
   - 若进一步允许 $d \in D$ 与 $z \in \Sigma L$ **同时为任意点**（未必是 $0$-胞腔）：对有限 CW 复形 $D$ 中任一点 $d$，设 $e^k$ 是唯一以其内部包含 $d$ 的胞腔（若 $k=0$ 已证；若 $k \ge 1$，将 $D^k$ 视为以原像 $\tilde{d} \in \mathrm{int}(D^k)$ 为锥顶对 $\partial D^k \cong S^{k-1}$ 的锥 $CS^{k-1}$，在径向与时间参数 $(\rho,t) \in [0,1] \times [0,1]$ 构成的矩形上从 $(\frac{1}{2}, 2)$ 投影到三边 $\{0\} \times I \cup [0,1] \times \{0\} \cup \{1\} \times I$，因 $\rho=0$ 落在左边界被固定，故在锥顶处良定义，给出 $D^k \times \{0\} \cup \partial D^k \times I \cup \{\tilde{d}\} \times I$ 作为 $D^k \times I$ 的强形变收缩核）。再沿高于 $k$ 维的有限多个胞腔归纳，可知对**任意** $d \in D$，对子 $(D, \{d\})$ 仍满足上述强形变收缩性质。于是由上一段同理可得 $(D, d) \vee (\Sigma L, z) \simeq (D, d) \vee (\Sigma L, v_-) \simeq Y$。

综上，$D \vee \Sigma L$ 的同伦型完全不依赖于 $D$ 与 $\Sigma L$ 中楔点的选择。$\blacksquare$

---

## S3 整数扭结的实例

### 构造

设 $L$ 是实射影平面 $\mathbb{R}P^2$ 的任一有限单纯三角剖分（故 $|L| \cong \mathbb{R}P^2$，且顶点集 $V(L)$ 有限非空）。取两个互异的新顶点 $u_0, v \notin V(L)$，令 $K$ 为 $L$ 与离散两点复形 $\{\{u_0\}, \{v\}\}$ 的单纯联接（即单纯悬挂）：
$$K := L \;\cup\; \big\{\{u_0\}, \{v\}\big\} \;\cup\; \big\{\tau \cup \{u_0\} : \tau \in L\big\} \;\cup\; \big\{\tau \cup \{v\} : \tau \in L\big\}.$$
任取 $L$ 的一个顶点 $w \in V(L)$，定义含 $v$ 的 $1$ 维子复形
$$B := \big\{\{w\},\; \{v\},\; \{w, v\}\big\} \subseteq K.$$

### 全部性质的证明

1. **$K$ 有限、$v$ 为顶点、$B$ 为含 $v$ 子复形**：
   因 $L$ 有限，$K$ 的单形集有限；直接检验知 $\tau \cup \{u_0\}$（或 $\tau \cup \{v\}$）的任一非空子集必属于 $L$、$\{\{u_0\},\{v\}\}$ 或同形锥单形之一，故 $K$ 是有限抽象单纯复形，且 $\{v\} \in K$。因 $\{w\} \in L$，故 $\{w,v\} \in K$，从而 $B \subseteq K$ 是含顶点 $v$ 的子复形。

2. **$|K| \setminus \{v\}$ 非空可缩**：
   记删去顶点 $v$ 的子复形为 $K \setminus v := \{\sigma \in K : v \notin \sigma\}$，则
   $$K \setminus v = \{\{u_0\}\} \cup L \cup \{\tau \cup \{u_0\} : \tau \in L\} = u_0 * L$$
   是以 $u_0$ 为锥顶、$L$ 为底的单纯锥。利用重心坐标，$|K|$ 中每一点唯一表为 $x = \sum_{u \in V(K)} t_u(x) u$（$t_u(x) \ge 0$，$\sum_u t_u(x) = 1$，支集 $\mathrm{supp}(x) = \{u : t_u(x) > 0\} \in K$）。
   - 对任意 $x \in |K| \setminus \{v\}$，有 $t_v(x) < 1$，故 $1 - t_v(x) = \sum_{u \neq v} t_u(x) > 0$，从而 $\mathrm{supp}(x) \setminus \{v\}$ 非空且是 $\mathrm{supp}(x)$ 不含 $v$ 的面，必属于 $K \setminus v$。定义径向收缩
     $$r: |K| \setminus \{v\} \longrightarrow |K \setminus v|, \qquad r(x) = \sum_{u \neq v} \frac{t_u(x)}{1 - t_v(x)} u,$$
     以及线性同伦 $H(x,s) = (1-s)x + s\,r(x)$（$s \in I$）。因 $x$ 与 $r(x)$ 同属闭单形 $|\mathrm{supp}(x)| \subseteq |K|$，且 $t_v(H(x,s)) = (1-s)t_v(x) \le t_v(x) < 1$，故 $H$ 取值于 $|K| \setminus \{v\}$，且在 $|K \setminus v|$（即 $t_v=0$ 处）逐点固定。因 $K$ 有限，重心坐标连续，故 $|K \setminus v|$ 是 $|K| \setminus \{v\}$ 的强形变收缩核。
   - 又 $|K \setminus v| = |u_0 * L|$ 含点 $u_0$（非空），且可由线性同伦 $G(y, s) = (1-s)y + s u_0$（对任意 $y \in |u_0 * L|$，$\mathrm{supp}(y) \cup \{u_0\} \in u_0 * L$）强形变收缩到单点 $\{u_0\}$，故 $|K \setminus v|$ 非空可缩，从而 $|K| \setminus \{v\}$ **非空可缩**。

3. **包含映射 $(|B| \setminus \{v\}) \hookrightarrow |B|$ 为同伦等价**：
   $|B|$ 同胚于闭线段 $[w, v] \cong [0,1]$，而 $|B| \setminus \{v\}$ 同胚于半开线段 $[w, v) \cong [0,1)$。两者均以单点 $\{w\}$ 为强形变收缩核（同伦均为 $(1-s)x + s w$），因此 $|B| \setminus \{v\}$ 与 $|B|$ 都是可缩空间。两个可缩空间之间的任何连续映射均为同伦等价（以常值映射 $y \mapsto w$ 为同伦逆），故 $(|B| \setminus \{v\}) \hookrightarrow |B|$ 是同伦等价。

4. **$|K|$ 的约化有理同调全零，但 $|K|$ 不可缩**：
   $K$ 是两个单纯锥 $u_0 * L$ 与 $v * L$ 沿公共子复形 $L$ 的并，故 $|K| \cong \Sigma |L| \cong \Sigma \mathbb{R}P^2$。在 $|K|$ 中取开集 $U_+ = |K| \setminus \{u_0\}$ 与 $U_- = |K| \setminus \{v\}$：
   - **适用条件检验（约化奇异同调的 Mayer–Vietoris 正合列）**：$U_+, U_-$ 是 $|K|$ 的开集，满足 $U_+ \cup U_- = |K|$，且交集 $U_+ \cap U_- = |K| \setminus \{u_0, v\}$ 以 $|L| \cong \mathbb{R}P^2$ 为强形变收缩核（先对 $v$ 作径向收缩到 $|u_0 * L| \setminus \{u_0\}$，再对 $u_0$ 作径向收缩到 $|L|$），特别地 $U_+ \cap U_- \neq \emptyset$。
   - 由第 2 条同理知 $U_+ \simeq |v * L| \simeq \{v\}$ 与 $U_- \simeq |u_0 * L| \simeq \{u_0\}$ 均可缩，故对任意系数交换群 $A$，对所有 $q \ge 0$ 有 $\widetilde{H}_q(U_+; A) = \widetilde{H}_q(U_-; A) = 0$。また $U_+, U_-$ 路径连通且交非空，故 $|K|$ 路径连通，$\widetilde{H}_0(|K|; A) = 0$；对所有 $k \ge 0$，Mayer–Vietoris 连接同态给出同构
     $$\widetilde{H}_{k+1}(|K|; A) \xrightarrow{\;\cong\;} \widetilde{H}_k(|L|; A) \cong \widetilde{H}_k(\mathbb{R}P^2; A).$$
   - 标准计算知实射影平面的整同调为 $\widetilde{H}_0(\mathbb{R}P^2; \mathbb{Z}) = 0$，$\widetilde{H}_1(\mathbb{R}P^2; \mathbb{Z}) \cong \mathbb{Z}/2\mathbb{Z}$，且当 $k \ge 2$ 时 $\widetilde{H}_k(\mathbb{R}P^2; \mathbb{Z}) = 0$。
   - **有理系数**：对有限生成自由链复形应用同调泛系数定理（适用条件：$\mathbb{Z}$ 为主理想整环，且 $\mathbb{Q}$ 作为 $\mathbb{Z}$-模无挠/平坦，故 $\mathrm{Tor}_1^{\mathbb{Z}}(\widetilde{H}_{k-1}, \mathbb{Q}) = 0$），得对一切 $k \ge 0$ 有 $\widetilde{H}_k(\mathbb{R}P^2; \mathbb{Q}) \cong \widetilde{H}_k(\mathbb{R}P^2; \mathbb{Z}) \otimes_{\mathbb{Z}} \mathbb{Q} = 0$。代入悬挂同构即得对**所有** $n \ge 0$，$\widetilde{H}_n(|K|; \mathbb{Q}) = 0$。
   - **不可缩性**：取 $A = \mathbb{Z}$ 及 $k = 1$，得
     $$\widetilde{H}_2(|K|; \mathbb{Z}) \cong \widetilde{H}_1(\mathbb{R}P^2; \mathbb{Z}) \cong \mathbb{Z}/2\mathbb{Z} \neq 0.$$
     可缩空间的全部约化整奇异同调群必为零，因此 $|K|$ **不可缩**。$\blacksquare$

---

## S4 整体对象与全部恢复目标

### 判定结论

**所列全部目标在给定条件下均成立。** 具体结论如下：
1. **同伦类型的完整刻画**：在所有满足条件的三元组 $(K, v, B)$ 中，$X = |K|$ 的可能同伦类型**恰好是所有非空有限抽象单纯复形 $L$ 的几何实现的非约化悬挂 $\Sigma |L|$ 的同伦类型**（等价地，所有非空有限 CW 复形的非约化悬挂的同伦类型）。
2. **实现构造**：对任意非空有限抽象单纯复形 $L$，取 S3 中的单纯悬挂 $K = L * \{\{u_0\}, \{v\}\}$ 及单边子复形 $B = \{\{w\}, \{v\}, \{w,v\}\}$（$w \in V(L)$），即满足全部原条件且 $|K| \cong \Sigma |L|$。
3. **局部有限关联数据的可缩性充要判据**：记 $\mathcal{S}_v = \{\sigma \in K : v \in \sigma\}$ 为 $K$ 中含 $v$ 的单形全体，$\mathcal{F}_v = \{\eta \in K : \exists \sigma \in \mathcal{S}_v,\; \eta \subseteq \sigma\}$ 为它们及其全部面构成的有限集（连同面包含关系 $\subseteq$）。令 $L = \mathcal{F}_v \setminus \mathcal{S}_v$（即链环 $\mathrm{Lk}_K(v)$）。则
   $$X \text{ 可缩} \iff L \neq \emptyset \text{ 且对一切 } p \ge 0,\; \widetilde{H}_p^{\mathrm{simp}}(L; \mathbb{Z}) = 0;$$
   等价地，完全以 $\mathcal{S}_v$ 为自由 $\mathbb{Z}$-基构造的有限相对链复形 $(C_*(\mathcal{F}_v, \mathcal{F}_v \setminus \mathcal{S}_v; \mathbb{Z}), \partial^{\mathrm{rel}})$ 在每个维数 $q = 0, 1, \dots, d$（$d = \max_{\sigma \in \mathcal{S}_v} \dim \sigma$）处正合——这等价于其有限整边界矩阵 $M_q$ 满足秩等式 $\mathrm{rank}(M_{q+1}) + \mathrm{rank}(M_q) = |\mathcal{S}_v^{(q)}|$（$0 \le q \le d$，约定 $M_0=0, M_{d+1}=0$）且每个 $M_q$（$1 \le q \le d$）的 Smith 标准形中全部非零不变因子均等于 $1$。

以下逐项给出完整证明。

---

### 一、同伦类型刻画的证明

设 $(K, v, B)$ 满足给定全部条件。在 $K$ 中定义：
- 闭星形 $\mathrm{St}_K(v) := \{\eta \in K : \eta \cup \{v\} \in K\}$；
- 链环 $L := \mathrm{Lk}_K(v) = \{\tau \in \mathrm{St}_K(v) : v \notin \tau\}$；
- 删点复形 $K \setminus v := \{\sigma \in K : v \notin \sigma\}$，并记 $D := |K \setminus v|$。

**第一步：利用 $B$ 的条件证明 $L = \mathrm{Lk}_K(v) \neq \emptyset$。**
对含 $v$ 的子复形 $B \subseteq K$，同样考虑 $\mathrm{Lk}_B(v) = \{\tau \in B : v \notin \tau \text{ 且 } \tau \cup \{v\} \in B\} \subseteq \mathrm{Lk}_K(v)$。反证法：假设 $\mathrm{Lk}_B(v) = \emptyset$。这意味着 $B$ 中除 $0$-单形 $\{v\}$ 外没有其他单形包含 $v$，因此 $\{v\}$ 在 $C = |B|$ 中既是闭集又是开集，从而有拓扑无交并分解
$$C = |B| = |B \setminus v| \sqcup \{v\}, \qquad O \cap C = |B| \setminus \{v\} = |B \setminus v|.$$
- 若 $B \setminus v = \emptyset$，则 $O \cap C = \emptyset$ 而 $C = \{v\} \neq \emptyset$，不存在从非空空间 $C$ 到空集的映射，故包含映射 $O \cap C \hookrightarrow C$ 不可能是同伦等价；
- 若 $B \setminus v \neq \emptyset$，因 $B \setminus v$ 是有限单纯复形，$|B \setminus v|$ 有有限个路径连通分支，设其个数为 $m \ge 1$，则 $H_0(O \cap C; \mathbb{Z}) \cong \mathbb{Z}^m$，而 $H_0(C; \mathbb{Z}) \cong \mathbb{Z}^{m+1}$。因 $\mathbb{Z}^m \not\cong \mathbb{Z}^{m+1}$（有限秩自由交换群的秩是同构不变量），且 $H_0(-;\mathbb{Z})$ 为同伦不变量，$O \cap C \hookrightarrow C$ 亦不可能是同伦等价。

两种情形均与假设矛盾！故必有 $\mathrm{Lk}_B(v) \neq \emptyset$，进而 $L = \mathrm{Lk}_K(v) \supseteq \mathrm{Lk}_B(v)$ 是**非空**有限抽象单纯复形。

**第二步：证明 $X = |K| \simeq \Sigma |L|$。**
1. 完全照搬 S3 第 2 条的重心坐标径向收缩证明（该证明仅用到 $K$ 是有限抽象单纯复形且 $v \in V(K)$），可知 $D = |K \setminus v|$ 是 $O = |K| \setminus \{v\}$ 的强形变收缩核。因为 $O$ 非空可缩，故 $D$ 也是**非空可缩**空间。
2. $K$ 的每个单形要么不含 $v$（属于 $K \setminus v$），要么含 $v$（属于 $\mathrm{St}_K(v)$），故 $K = (K \setminus v) \cup \mathrm{St}_K(v)$，且 $(K \setminus v) \cap \mathrm{St}_K(v) = \mathrm{Lk}_K(v) = L$。由于 $K$ 有限，$|K \setminus v|$ 与 $|\mathrm{St}_K(v)|$ 均为 $X = |K|$ 的闭子复形，满足 $|K \setminus v| \cup |\mathrm{St}_K(v)| = X$ 及 $|K \setminus v| \cap |\mathrm{St}_K(v)| = |L|$。
3. 因 $L \neq \emptyset$，映射 $\varphi: C|L| \to |\mathrm{St}_K(v)|$，$\varphi([y, s]) = (1-s)y + s v$（$y \in |L|, s \in [0,1]$）是从紧空间 $C|L|$ 到 Hausdorff 空间 $|\mathrm{St}_K(v)|$ 的连续双射，故为同胚，且将底面 $|L| \times \{0\}$ 逐点映为 $|L|$、将锥顶映为 $v$。因此 $X \cong D \cup_{|L|} C|L|$。
4. **应用 S1**（适用条件检验：有限单纯复形的几何实现 $X = |K|$ 以各闭单形为胞腔构成有限 CW 复形，$D = |K \setminus v|$ 是其非空可缩 CW 子复形）：由 S1 知商映射 $q: X \to X/D$ 是同伦等价。
5. 复合映射 $C|L| \xrightarrow{\varphi} |\mathrm{St}_K(v)| \hookrightarrow X \xrightarrow{q} X/D$ 是满射（因 $L \neq \emptyset$，$D$ 中各点与 $|L| \subseteq D$ 同调于商点 $[D]$，故在像中），且将 $|L| \times \{0\}$ 坍缩为单点 $[D]$，在 $C|L| \setminus (|L| \times \{0\})$ 上单射。由于 $C|L|$ 紧且有限 CW 复形 $X/D$ 为 Hausdorff 空间，该映射诱导同胚
   $$\Sigma |L| \cong C|L| / (|L| \times \{0\}) \xrightarrow{\;\cong\;} X/D.$$
   结合 $X \simeq X/D$，即得 $X \simeq \Sigma |L|$。

*附注（与有限 CW 复形表述的等价性及悬挂的同伦不变性）*：若 $f: Z_1 \to Z_2$ 是非空空间之间的同伦等价（同伦逆为 $g$，同伦 $H: g \circ f \simeq \mathrm{id}_{Z_1}, G: f \circ g \simeq \mathrm{id}_{Z_2}$），定义 $\Sigma f([z,s]) = [f(z),s]$，则由 S1 中 Whitehead 定理（$I$ 局部紧 Hausdorff），同伦 $([z,s], t) \mapsto [H(z,t), s]$ 连续下降到 $\Sigma Z_1 \times I \to \Sigma Z_1$，证得 $\Sigma g \circ \Sigma f \simeq \mathrm{id}_{\Sigma Z_1}$，同理 $\Sigma f \circ \Sigma g \simeq \mathrm{id}_{\Sigma Z_2}$，即 $\Sigma$ 保持同伦等价。另一方面，对任意非空有限 CW 复形 $W$，由有限 CW 复形的单纯逼近同伦等价定理（Hatcher, *Algebraic Topology*, Theorem 2C.5；适用条件：$W$ 为有限维——此处有限——CW 复形，对其胞腔归纳作重心细分并用单纯映射逼近粘附映射），存在非空有限单纯复形 $L$ 使 $|L| \simeq W$，从而 $\Sigma |L| \simeq \Sigma W$。故两类同伦型完全一致。

---

### 二、实现构造与验证

对任意给定的非空有限抽象单纯复形 $L$（以及任意与 $\Sigma |L|$ 同伦等价的空间类型），取两个互异的新元素 $u_0, v \notin V(L)$，并从非空集 $V(L)$ 中任取一个顶点 $w \in V(L)$，令
$$K := L \;\cup\; \big\{\{u_0\}, \{v\}\big\} \;\cup\; \big\{\tau \cup \{u_0\} : \tau \in L\big\} \;\cup\; \big\{\tau \cup \{v\} : \tau \in L\big\}, \qquad B := \big\{\{w\}, \{v\}, \{w,v\}\big\}.$$
验证（与 S3 第 1–3 条完全一致，该部分证明从未用到 $L$ 是 $\mathbb{R}P^2$，仅用到 $L$ 是非空有限抽象单纯复形）：
1. $K$ 是有限抽象单纯复形，$v \in V(K)$，且因 $\{w\} \in L \implies \{w,v\} \in K$，故 $B \subseteq K$ 是含 $v$ 的子复形；
2. $K \setminus v = u_0 * L$，故 $|K \setminus v| \cong C|L|$ 非空可缩，而 $|K \setminus v|$ 是 $O = |K| \setminus \{v\}$ 的强形变收缩核，从而 $O$ 非空可缩；
3. $C = |B| \cong [0,1]$，$O \cap C = |B| \setminus \{v\} \cong [0,1)$，两者均可缩，故包含映射 $O \cap C \hookrightarrow C$ 是同伦等价；
4. $X = |K| = |u_0 * L| \cup_{|L|} |v * L| \cong \Sigma |L|$，实现了目标同伦类型。

---

### 三、局部有限关联数据的可缩性判据及证明

**1. 从含 $v$ 单形及其面的有限关联数据恢复链复形**
输入数据为有限集 $\mathcal{S}_v = \{\sigma \in K : v \in \sigma\}$、其全部面构成的有限集 $\mathcal{F}_v = \{\eta \in K : \exists \sigma \in \mathcal{S}_v,\; \eta \subseteq \sigma\} = \mathrm{St}_K(v)$ 以及它们之间的面包含关系 $\subseteq$。
- 首先，$L = \mathrm{Lk}_K(v)$ 恰好就是差集 $\mathcal{F}_v \setminus \mathcal{S}_v$（继承面包含关系 $\subseteq$）；甚至仅从偏序集 $(\mathcal{S}_v, \subseteq)$ 本身也可恢复 $L$：$\{v\}$ 是 $(\mathcal{S}_v, \subseteq)$ 的唯一极小元，$\mathcal{S}_v \setminus \{\{v\}\}$ 与 $L$ 通过保序双射 $\sigma \leftrightarrow \sigma \setminus \{v\}$ 一一对应。
- 为直接用 $\mathcal{S}_v$ 写出有限矩阵判据，按维数分级令 $\mathcal{S}_v^{(q)} := \{\sigma \in \mathcal{S}_v : \dim \sigma = q\}$（$q = 0, 1, \dots, d$，其中 $\mathcal{S}_v^{(0)} = \{\{v\}\}$，$d = \max_{\sigma \in \mathcal{S}_v} \dim \sigma$）。将 $1$-单形集 $\mathcal{S}_v^{(1)}$ 任意全序排列为 $e_1 < e_2 < \cdots < e_m$。对任意 $q \ge 1$，每个 $\sigma \in \mathcal{S}_v^{(q)}$ 恰包含 $q$ 个属于 $\mathcal{S}_v^{(1)}$ 的 $1$-维面 $e_{i_1} < e_{i_2} < \cdots < e_{i_q}$，其属于 $\mathcal{S}_v^{(q-1)}$ 的余一维面恰有 $q$ 个：当 $q=1$ 时唯一面为 $\{v\} \in \mathcal{S}_v^{(0)}$；当 $q \ge 2$ 时，记 $\sigma_r \in \mathcal{S}_v^{(q-1)}$（$1 \le r \le q$）为 $\sigma$ 中唯独不包含 $e_{i_r}$ 的那个属于 $\mathcal{S}_v^{(q-1)}$ 的面。
- 定义自由交换群的有限链复形 $(C_*^{\mathrm{rel}}, \partial_*^{\mathrm{rel}})$（即相对单纯链复形 $C_*(\mathrm{St}_K(v), \mathrm{Lk}_K(v); \mathbb{Z})$）：令 $C_q^{\mathrm{rel}} = \mathbb{Z}^{\mathcal{S}_v^{(q)}}$（$0 \le q \le d$，其余维数为 $0$），微分 $\partial_q^{\mathrm{rel}} : C_q^{\mathrm{rel}} \to C_{q-1}^{\mathrm{rel}}$ 定义为：
  $$\partial_1^{\mathrm{rel}}([e_i]) = [\{v\}], \qquad \partial_q^{\mathrm{rel}}([\sigma]) = \sum_{r=1}^q (-1)^{r-1} [\sigma_r] \quad (2 \le q \le d).$$
  在双射 $\sigma \leftrightarrow \tau = \sigma \setminus \{v\}$（将 $[\{v\}]$ 对应于增广链群 $\widetilde{C}_{-1}(L;\mathbb{Z}) = \mathbb{Z}$ 的生成元）下，$(C_*^{\mathrm{rel}}, \partial_*^{\mathrm{rel}})$ 与 $L$ 的增广单纯链复形 $(\widetilde{C}_{*-1}(L; \mathbb{Z}), \tilde{\partial}_{*-1})$ 作为链复形同构，因此对一切 $q \ge 0$ 有
  $$H_q(C_*^{\mathrm{rel}}) \cong \widetilde{H}_{q-1}^{\mathrm{simp}}(L; \mathbb{Z})$$
  （其中约定 $\widetilde{H}_{-1}^{\mathrm{simp}}(\emptyset; \mathbb{Z}) = \mathbb{Z}$，而当 $L \neq \emptyset$ 时增广映射满射，故 $H_0(C_*^{\mathrm{rel}}) = \widetilde{H}_{-1}^{\mathrm{simp}}(L; \mathbb{Z}) = 0$）。

**2. 充要判据的表述与有限可检验性**
**判据**：$X$ 可缩当且仅当链复形 $(C_*^{\mathrm{rel}}, \partial_*^{\mathrm{rel}})$ 在所有维数 $q = 0, 1, \dots, d$ 上正合（即 $H_q(C_*^{\mathrm{rel}}) = 0$，$\forall q \ge 0$；等价地，$L \neq \emptyset$ 且对一切 $p = 0, \dots, d-1$ 有 $\widetilde{H}_p^{\mathrm{simp}}(L; \mathbb{Z}) = 0$）。
用 $\partial_q^{\mathrm{rel}}$ 在标准基下的有限整矩阵 $M_q \in \mathbb{Z}^{|\mathcal{S}_v^{(q-1)}| \times |\mathcal{S}_v^{(q)}|}$（$1 \le q \le d$，并置 $M_0 = 0, M_{d+1} = 0$）表述，正合性充要于以下两条有限整矩阵条件同时成立：
- **秩条件**：对每个 $q = 0, 1, \dots, d$，$\mathrm{rank}(M_{q+1}) + \mathrm{rank}(M_q) = |\mathcal{S}_v^{(q)}|$（注：$q=0$ 时 $|\mathcal{S}_v^{(0)}|=1, M_0=0$，自动蕴涵 $\mathrm{rank}(M_1)=1$，即 $\mathcal{S}_v^{(1)} \neq \emptyset \iff L \neq \emptyset$）；
- **无整扭结条件**：对每个 $q = 1, \dots, d$，整矩阵 $M_q$ 的 Smith 标准形中所有非零对角元（不变因子）均等于 $1$（保证 $\mathbb{Z}^{\mathcal{S}_v^{(q-1)}} / \mathrm{im}(M_q)$ 无挠，结合秩条件即得 $\ker(M_q) = \mathrm{im}(M_{q+1})$）。

有限整矩阵的秩与 Smith 标准形均可由有限步整数行列初等变换（欧几里得算法）精确算出，且输入仅涉及 $(\mathcal{F}_v, \mathcal{S}_v, \subseteq)$ 的有限关联数据。

**3. 判据充要性的证明**
在给定条件下已证 $L \neq \emptyset$ 且 $X \simeq \Sigma |L|$，故 $X$ 可缩当且仅当 $\Sigma |L|$ 可缩。
在 $\Sigma |L| = (|L| \times [0,1])/\sim$ 中取开集 $U_+ = \Sigma |L| \setminus \{v_-\}$ 与 $U_- = \Sigma |L| \setminus \{v_+\}$。
- **同调关系**：$U_+, U_-$ 开且覆盖 $\Sigma |L|$；$U_+$ 与 $U_-$ 分别通过 $[y,s] \mapsto [y, (1-t)s + t]$ 与 $[y,s] \mapsto [y, (1-t)s]$ 强形变收缩到 $v_+$ 与 $v_-$，故均可缩；$U_+ \cap U_- \cong |L| \times (0,1) \simeq |L|$，且因 $L \neq \emptyset$ 知 $U_+ \cap U_- \neq \emptyset$。应用约化奇异同调的 Mayer–Vietoris 正合列，并结合有限单纯复形 $L$ 的单纯同调与奇异同调同构定理（适用条件：$L$ 为单纯复形，$|L|$ 取有限复形的通常拓扑），对所有 $p \ge 0$ 得同构
  $$\widetilde{H}_{p+1}(\Sigma |L|; \mathbb{Z}) \xrightarrow{\;\cong\;} \widetilde{H}_p(|L|; \mathbb{Z}) \xrightarrow{\;\cong\;} \widetilde{H}_p^{\mathrm{simp}}(L; \mathbb{Z}),$$
  且因 $\Sigma |L|$ 路径连通（$L \neq \emptyset$），$\widetilde{H}_0(\Sigma |L|; \mathbb{Z}) = 0$。

由此分证必要性与充分性：
- **必要性（$\Rightarrow$）**：若 $X$ 可缩，则 $\Sigma |L|$ 可缩，故对一切 $q \ge 0$ 有 $\widetilde{H}_q(\Sigma |L|; \mathbb{Z}) = 0$。由上式即得对一切 $p \ge 0$，$\widetilde{H}_p^{\mathrm{simp}}(L; \mathbb{Z}) = 0$（又 $L \neq \emptyset$），从而对一切 $q \ge 0$，$H_q(C_*^{\mathrm{rel}}) = 0$。
- **充分性（$\Leftarrow$）**：设对一切 $q \ge 0$ 有 $H_q(C_*^{\mathrm{rel}}) = 0$，即 $L \neq \emptyset$ 且对一切 $p \ge 0$ 有 $\widetilde{H}_p^{\mathrm{simp}}(L; \mathbb{Z}) = 0$。
  1. **$|L|$ 路径连通**：取 $p = 0$，由 $|L| \neq \emptyset$ 及 $\widetilde{H}_0(|L|; \mathbb{Z}) \cong \widetilde{H}_0^{\mathrm{simp}}(L; \mathbb{Z}) = 0$ 知 $H_0(|L|; \mathbb{Z}) \cong \mathbb{Z}$，故 $|L|$ 恰有一个路径连通分支，即 $|L|$ **非空且路径连通**。
  2. **$\Sigma |L|$ 单连通（应用 Seifert–van Kampen 定理）**：检验适用条件——开集 $U_+, U_-$ 覆盖 $\Sigma |L|$；$U_+, U_-$ 均可缩从而路径连通；交集 $U_+ \cap U_- \cong |L| \times (0,1)$ 作为两个非空路径连通空间的乘积也是**非空且路径连通**的。任取基点 $x_0 \in U_+ \cap U_-$，由 Seifert–van Kampen 定理，$\pi_1(\Sigma |L|, x_0)$ 由 $\pi_1(U_+, x_0)$ 与 $\pi_1(U_-, x_0)$ 在包含映射下的像生成。因 $U_+, U_-$ 可缩，$\pi_1(U_+, x_0) = \pi_1(U_-, x_0) = \{1\}$，故 $\pi_1(\Sigma |L|, x_0) = \{1\}$。
  3. **高阶同伦群全零（应用绝对 Hurewicz 定理）**：由同调同构知对所有 $n \ge 1$，$H_n(\Sigma |L|; \mathbb{Z}) = \widetilde{H}_n(\Sigma |L|; \mathbb{Z}) \cong \widetilde{H}_{n-1}^{\mathrm{simp}}(L; \mathbb{Z}) = 0$。对 $n \ge 2$ 归纳应用绝对 Hurewicz 定理（适用条件：空间路径连通且 $(n-1)$-连通，$n \ge 2$）：当 $n=2$ 时，由第 2 步知 $\Sigma |L|$ 路径连通且 $1$-连通，故 $\pi_2(\Sigma |L|, x_0) \cong H_2(\Sigma |L|; \mathbb{Z}) = 0$；归纳假设 $\Sigma |L|$ 已 $(n-1)$-连通，则 Hurewicz 定理给出 $\pi_n(\Sigma |L|, x_0) \cong H_n(\Sigma |L|; \mathbb{Z}) = 0$。因此对一切 $n \ge 1$，$\pi_n(\Sigma |L|, x_0) = 0$。
  4. **可缩性（应用 Whitehead 定理）**：因为 $L$ 是有限单纯复形，$\Sigma |L| \cong |L * \{\{u_0\}, \{v\}\}|$ 是有限单纯复形的几何实现，从而是 CW 复形；单点空间 $\{x_0\}$ 也是 CW 复形。常值映射 $c: \Sigma |L| \to \{x_0\}$ 在 $\pi_0$ 上诱导双射（两者均路径连通），且在所有 $n \ge 1$ 的同伦群 $\pi_n$ 上诱导零群间的同构，故 $c$ 是两个 CW 复形之间的弱同伦等价。由 Whitehead 定理，$c$ 是同伦等价，即 $\Sigma |L|$ 可缩，进而 $X \simeq \Sigma |L|$ 可缩。$\blacksquare$

---

## S5 不提供子复形 B

### 判定结论

**不必**同伦等价于非空有限复形的悬挂。去掉 $B$ 及其同伦条件后，在同伦等价意义下**新增的可能同伦类型恰有一种，即离散两点空间 $S^0$**。

### 反例与证明

**1. 满足全部前提的反例**
取两个互异顶点 $u_0, v$，定义 $0$ 维有限抽象单纯复形
$$K := \big\{\{u_0\},\; \{v\}\big\}.$$
- $K$ 是有限抽象单纯复形，$v$ 是其顶点；
- $|K| = \{u_0\} \sqcup \{v\} \cong S^0$，故 $|K| \setminus \{v\} = \{u_0\}$ 为单点空间，**非空且可缩**，满足 S5 全部前提；
- 但对**任意**非空空间 $Z$（特别地，任意非空有限 CW 复形或非空有限单纯复形，无论取非约化悬挂 $\Sigma Z$ 还是带基点约化悬挂 $\widetilde{\Sigma} Z$），悬挂空间都是**路径连通**的（在 $\Sigma Z$ 中取定 $z_0 \in Z$，任一点 $[z,s]$ 均可由路径 $t \mapsto [z, (1-t)s + t]$ 连至北极 $v_+ = [z_0, 1]$；约化悬挂作为 $\Sigma Z$ 的商空间亦路径连通），故 $|\pi_0(\Sigma Z)| = 1$。而 $|K| \cong S^0$ 有两个路径连通分支，$|\pi_0(|K|)| = 2 \neq 1$。因路径连通分支数 $|\pi_0(-)|$ 是同伦不变量，$|K|$ 不可能同伦等价于任何非空复形的悬挂。

**2. 新增可能同伦类型的完整分类**
设有限抽象单纯复形 $K$ 及顶点 $v \in V(K)$ 满足 $O = |K| \setminus \{v\}$ 非空可缩。记 $D = |K \setminus v|$，$L = \mathrm{Lk}_K(v)$。由 S3 第 2 条（仅依赖 $K$ 有限与 $v \in V(K)$），$D$ 是 $O$ 的强形变收缩核，故 $D$ 非空可缩。按 $L$ 是否为空分两类讨论：
- **情形一：$L \neq \emptyset$**。
  回顾 S4 第一部分第二步的证明：一旦已知 $L \neq \emptyset$ 且 $D$ 非空可缩，无需再使用 $B$，即可由 S1 直接推得 $|K| \cong D \cup_{|L|} C|L| \simeq \Sigma |L|$，此类型已包含在 S4 的刻画之中（事实上，此时任取 $w \in V(L)$，令 $B = \{\{w\}, \{v\}, \{w,v\}\} \subseteq K$，$(K,v,B)$ 本身就满足 S4 的全部条件）。
- **情形二：$L = \emptyset$**。
  此时 $K$ 中不存在任何维数 $\ge 1$ 的单形包含 $v$，故 $K = (K \setminus v) \sqcup \{\{v\}\}$，几何实现分解为拓扑无交并
  $$|K| = |K \setminus v| \sqcup \{v\} = D \sqcup \{v\}.$$
  因 $D$ 非空可缩，取定 $d_0 \in D$，收缩同伦给出同伦等价 $D \simeq \{d_0\}$；将其与 $\{v\}$ 上的恒等映射作无交并，即得
  $$|K| = D \sqcup \{v\} \simeq \{d_0\} \sqcup \{v\} \cong S^0.$$
  结合上文第 1 点反例可知 $S^0$ 确实可被实现，且不属于 S4 的同伦类型。

综上，唯一新增的同伦类型是离散两点空间 $S^0$ 的同伦型。$\blacksquare$

---

## S6 悬挂信息的逆向恢复

### 判定结论

**不成立**：对非空有限单纯复形 $L_1, L_2$，$\Sigma |L_1| \simeq \Sigma |L_2|$ **不必**推出 $|L_1| \simeq |L_2|$。

### 反例构造与证明

我们的思路是构造一个整同调零调（$\widetilde{H}_*(L_1; \mathbb{Z}) = 0$）但基本群非平凡（$\pi_1(|L_1|) \neq \{1\}$）的非空有限单纯复形 $L_1$，并取 $L_2$ 为单点复形；由 S4 已证判据知 $\Sigma |L_1|$ 与 $\Sigma |L_2|$ 均可缩从而同伦等价，但 $\pi_1$ 区分 $|L_1|$ 与 $|L_2|$。

**第一步：构造 $2$ 维 CW 复形 $X_\Gamma$ 及其显式有限单纯剖分 $L_1$**
考虑有限展示群
$$\Gamma := \big\langle a, b \;\big|\; a^3 b^{-5} = 1,\; a b a b^{-4} = 1 \big\rangle$$
对应的标准 $2$ 维展示 CW 复形 $X_\Gamma$：它有 $1$ 个 $0$-胞腔 $v_0$，$2$ 个有向 $1$-胞腔 $e_a, e_b$（构成 $S^1 \vee S^1$），以及 $2$ 个沿字 $r_1 = a^3 b^{-5}$ 与 $r_2 = a b a b^{-4}$ 粘附的 $2$-胞腔 $f_1, f_2$。下面将 $X_\Gamma$ 显式三角剖分为有限抽象单纯复形 $L_1$：
1. **$1$-骨架 $G$**：取 $5$ 个互异顶点 $v_0, u_1, u_2, w_1, w_2$，令有向圈 $\vec{a}$ 依次经过 $3$ 条有向边 $(v_0, u_1), (u_1, u_2), (u_2, v_0)$，有向圈 $\vec{b}$ 依次经过 $3$ 条有向边 $(v_0, w_1), (w_1, w_2), (w_2, v_0)$。这 $5$ 个顶点与 $6$ 条无向边构成 $1$ 维有限单纯复形 $G$，其几何实现 $|G| \cong S^1 \vee S^1$。
2. **两条边界闭边路**：
   - 将字 $r_1 = a^3 b^{-5}$ 按 $\vec{a}$ 走 $3$ 圈、再按 $\vec{b}$ 反向走 $5$ 圈展开为 $G$ 中长为 $N_1 = 3 \times 3 + 5 \times 3 = 24$ 的闭边路，依次记经过的顶点为 $p_{1,0}, p_{1,1}, \dots, p_{1,24} = p_{1,0}$（下标模 $24$ 理解）；
   - 将字 $r_2 = a b a b^{-4}$ 依次按 $\vec{a}, \vec{b}, \vec{a}$ 及 $4$ 次反向 $\vec{b}$ 展开为 $G$ 中长为 $N_2 = (1+1+1+4) \times 3 = 21$ 的闭边路，依次记经过的顶点为 $p_{2,0}, p_{2,1}, \dots, p_{2,21} = p_{2,0}$（下标模 $21$ 理解）。
   由于每一步均走过 $G$ 的一条边，对每个 $i \in \{1,2\}$ 与 $j \in \mathbb{Z}/N_i\mathbb{Z}$，必有 $p_{i,j} \neq p_{i,j+1}$ 且 $\{p_{i,j}, p_{i,j+1}\} \in G$。
3. **带领圈的圆盘三角剖分**：引入与 $V(G)$ 不交且彼此互异的 $47$ 个新顶点：中心点 $c_1, c_2$，内环顶点 $q_{1,0}, \dots, q_{1,23}$ 及 $q_{2,0}, \dots, q_{2,20}$（总顶点数 $5 + 47 = 52$）。令 $L_1$ 是由对所有 $i \in \{1,2\}$ 和 $j \in \mathbb{Z}/N_i\mathbb{Z}$ 取以下三族 $2$-单形及其全部非空子集生成的有限抽象单纯复形（注：$G$ 的每条边均出现在 $r_1$ 中，故 $G \subseteq L_1$）：
   $$\Delta^{(1)}_{i,j} = \{c_i, q_{i,j}, q_{i,j+1}\}, \quad \Delta^{(2)}_{i,j} = \{p_{i,j+1}, q_{i,j}, q_{i,j+1}\}, \quad \Delta^{(3)}_{i,j} = \{p_{i,j}, p_{i,j+1}, q_{i,j}\}.$$
4. **验证 $|L_1| \cong X_\Gamma$**：
   粘合前，对每个 $i \in \{1,2\}$，先用独立外环顶点 $\tilde{p}_{i,0}, \dots, \tilde{p}_{i, N_i-1}$ 代替 $p_{i,j}$ 构造抽象复形 $D_i$：其中 $\bigcup_j |\Delta^{(1)}_{i,j}|$ 是以 $c_i$ 为心、$q_{i,0}\cdots q_{i,N_i-1}$ 为边界的 $N_i$ 边形闭圆盘，而外层每个四边形 $(\tilde{p}_{i,j}, \tilde{p}_{i,j+1}, q_{i,j+1}, q_{i,j})$ 沿对角线 $\{\tilde{p}_{i,j+1}, q_{i,j}\}$ 剖分为两个三角形 $\Delta^{(3)}_{i,j}$ 与 $\Delta^{(2)}_{i,j}$，相邻扇区沿径向边 $\{\tilde{p}_{i,j}, q_{i,j}\}$ 严丝合缝粘合，故 $|D_i| \cong D^2$，边界为外环 $|\partial P_i|$。
   考察单纯映射 $\pi_i : D_i \to L_1$（将 $\tilde{p}_{i,j} \mapsto p_{i,j}$，固定 $c_i$ 与全体 $q_{i,j}$）：
   - 因 $p_{i,j} \neq p_{i,j+1}$，$\pi_i$ 在 $D_i$ 的**每一个**单形上都是单射（仅外边界边与 $\Delta^{(3)}_{i,j}$ 含两个 $\tilde{p}$ 顶点，即 $\tilde{p}_{i,j}$ 与 $\tilde{p}_{i,j+1}$）；
   - 对 $D_i \setminus \partial P_i$ 中的单形（必含 $c_i$ 或某个 $q_{i,j}$），$\pi_i$ 给出与 $L_1$ 中含 $\{c_i, q_{i,0}, \dots, q_{i, N_i-1}\}$ 顶点的单形之间的**双射**：含 $c_i$ 的单形不含 $\tilde{p}$ 顶点；含相邻对 $\{q_{i,j}, q_{i,j+1}\}$（因 $N_i \ge 4$，相邻对唯一决定 $j$）的 $2$-单形唯一确定 $\Delta^{(2)}_{i,j}$；仅含单个 $q_{i,j}$ 且与外环相交的单形在 $D_i$ 中仅有边 $\{\tilde{p}_{i,j}, q_{i,j}\}$、$\{\tilde{p}_{i,j+1}, q_{i,j}\}$ 与三角形 $\Delta^{(3)}_{i,j}$，因 $p_{i,j} \neq p_{i,j+1}$，它们的像 $\{p_{i,j}, q_{i,j}\}$、$\{p_{i,j+1}, q_{i,j}\}$ 与 $\{p_{i,j}, p_{i,j+1}, q_{i,j}\}$ 互不相同。
   因此 $|\pi_i| : |D_i| \to |L_1|$ 在开圆盘 $|D_i| \setminus |\partial P_i|$ 上单射，在边界 $|\partial P_i|$ 上恰为粘附闭路 $\gamma_i: S^1 \to |G|$。由紧空间 $|G| \sqcup |D_1| \sqcup |D_2|$ 到 Hausdorff 空间 $|L_1|$ 与 $X_\Gamma$ 的商映射具有完全相同的纤维，得同胚 $|L_1| \cong X_\Gamma$。

再取单点有限抽象单纯复形 $L_2 := \{\{w\}\}$（非空，$|L_2| = \{w\}$）。

**第二步：证明 $\Sigma |L_1| \simeq \Sigma |L_2|$**
1. 对 $X_\Gamma$ 计算胞腔同调（适用条件：CW 复形的胞腔同调与奇异同调同构）：$X_\Gamma$ 仅有 $1$ 个 $0$-胞腔、$2$ 个 $1$-胞腔、$2$ 个 $2$-胞腔，无更高维胞腔，故约化胞腔链复形为
   $$0 \longrightarrow C_2^{\mathrm{cell}}(X_\Gamma; \mathbb{Z}) \xrightarrow{\;\partial_2\;} C_1^{\mathrm{cell}}(X_\Gamma; \mathbb{Z}) \xrightarrow{\;\partial_1 = 0\;} \widetilde{C}_0^{\mathrm{cell}}(X_\Gamma; \mathbb{Z}) = 0.$$
   在基 $(f_1, f_2)$ 与 $(e_a, e_b)$ 下，胞腔边界算子 $\partial_2 : \mathbb{Z}^2 \to \mathbb{Z}^2$ 的矩阵由 $r_1 = a^3 b^{-5}$ 与 $r_2 = a b a b^{-4}$ 中 $a, b$ 的指数和给出：
   $$M = \begin{pmatrix} 3 & 2 \\ -5 & -3 \end{pmatrix}, \qquad \det M = 3(-3) - 2(-5) = 1.$$
   因 $\det M = 1 \in \mathbb{Z}^\times$，$\partial_2$ 是 $\mathbb{Z}^2$ 上的同构，故 $\ker(\partial_2) = 0$ 且 $\mathrm{im}(\partial_2) = \mathbb{Z}^2$。因此对**一切** $p \ge 0$，
   $$\widetilde{H}_p^{\mathrm{simp}}(L_1; \mathbb{Z}) \cong \widetilde{H}_p(|L_1|; \mathbb{Z}) \cong \widetilde{H}_p(X_\Gamma; \mathbb{Z}) = 0.$$
2. 在 S4 第三部分第 3 小节中我们已严格证明：对**任意**非空有限抽象单纯复形 $L$，只要对所有 $p \ge 0$ 有 $\widetilde{H}_p^{\mathrm{simp}}(L; \mathbb{Z}) = 0$，其非约化悬挂 $\Sigma |L|$ 必**可缩**（该段证明仅用到 $L$ 是非空有限单纯复形，完全不依赖 $K$ 或 $B$）。将其应用于 $L_1$，即知 $\Sigma |L_1|$ 可缩！
3. 另一方面，$\Sigma |L_2| = \Sigma \{w\} \cong [0,1]$ 显然可缩。任意两个可缩空间同伦等价，故 $\Sigma |L_1| \simeq \Sigma |L_2|$。

**第三步：证明 $|L_1| \not\simeq |L_2|$**
1. 单点空间 $|L_2| = \{w\}$ 的基本群为平凡群 $\pi_1(|L_2|, w) = \{1\}$。
2. 对 $X_\Gamma$ 应用展示复形的 Seifert–van Kampen 定理（在每个 $2$-胞腔 $f_i$ 内取中心点 $c_i$，用开集 $U_0 = X_\Gamma \setminus \{c_1, c_2\} \simeq |G|$ 与两个开圆盘覆盖 $X_\Gamma$，交集路径连通，逐次粘附消去正规闭包），得
   $$\pi_1(|L_1|, v_0) \cong \pi_1(X_\Gamma, v_0) \cong \Gamma = \big\langle a, b \;\big|\; a^3 b^{-5} = 1,\; a b a b^{-4} = 1 \big\rangle.$$
3. 在 $5$ 元对称群 $(S_5, \circ)$（约定 $(\sigma \circ \tau)(k) = \sigma(\tau(k))$）中取两个置换：
   $$\sigma_a = (1\,2\,3), \qquad \sigma_b = (1\,4\,3\,5\,2).$$
   直接逐元计算复合 $\sigma_a \circ \sigma_b$：
   $$1 \xrightarrow{\sigma_b} 4 \xrightarrow{\sigma_a} 4,\quad 4 \xrightarrow{\sigma_b} 3 \xrightarrow{\sigma_a} 1,\quad 3 \xrightarrow{\sigma_b} 5 \xrightarrow{\sigma_a} 5,\quad 5 \xrightarrow{\sigma_b} 2 \xrightarrow{\sigma_a} 3,\quad 2 \xrightarrow{\sigma_b} 1 \xrightarrow{\sigma_a} 2,$$
   故 $\sigma_a \circ \sigma_b = (1\,4)(3\,5)$，是不交对换之积，满足 $(\sigma_a \circ \sigma_b)^2 = \mathrm{id}$。又 $\sigma_a$ 为 $3$-轮换（$\sigma_a^3 = \mathrm{id}$），$\sigma_b$ 为 $5$-轮换（$\sigma_b^5 = \mathrm{id}$），于是关系式得到保持：
   $$\sigma_a^3 \circ \sigma_b^{-5} = \mathrm{id} \circ \mathrm{id} = \mathrm{id}, \qquad \sigma_a \circ \sigma_b \circ \sigma_a \circ \sigma_b^{-4} = (\sigma_a \circ \sigma_b)^2 \circ \sigma_b^{-5} = \mathrm{id} \circ \mathrm{id} = \mathrm{id}.$$
   因此存在良定义的群同态 $\rho: \Gamma \to S_5$ 将生成元 $a \mapsto (1\,2\,3) \neq \mathrm{id}$，$b \mapsto (1\,4\,3\,5\,2)$。这证明 $\pi_1(|L_1|, v_0) \cong \Gamma \neq \{1\}$。

因为路径连通空间的基本群同构类是（无基点）同伦不变量，而 $\pi_1(|L_1|, v_0) \not\cong \{1\} = \pi_1(|L_2|, w)$，故 $|L_1| \not\simeq |L_2|$。$\blacksquare$
