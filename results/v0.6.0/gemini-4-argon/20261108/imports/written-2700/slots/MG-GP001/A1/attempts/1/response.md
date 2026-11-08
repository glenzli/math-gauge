以下按 `S1` 至 `S6` 逐项给出完整证明、构造、分类与反例。

---

## S1 可缩子复形的商

### 命题结论
设 $Y$ 为有限 CW 复形，$A \subset Y$ 是非空可缩子复形，则商映射 $q: Y \to Y/A$ 是同伦等价。

### 完整证明

#### 1. 同伦延拓性质（HEP）的适用条件与收缩同伦的延拓
因为 $Y$ 是有限 CW 复形且 $A \subset Y$ 是子复形，所以 $(Y, A)$ 构成一个 CW 复形对。由 CW 复形对的标准定理，包含映射 $i: A \hookrightarrow Y$ 是上纤维化（cofibration），即 $(Y, A)$ 具有**同伦延拓性质（Homotopy Extension Property, HEP）**：给定任意映射 $f_0: Y \to Z$ 以及在 $A \times I$（其中 $I = [0,1]$）上满足 $\left.h_0\right|_A = \left.f_0\right|_A$ 的同伦 $h_t: A \to Z$，必存在延拓同伦 $H_t: Y \to Z$ 使得 $H_0 = f_0$ 且 $\left.H_t\right|_A = h_t$（$\forall t \in I$）。

由假设，$A$ 非空且可缩，故存在点 $a_0 \in A$ 及同伦 $h: A \times I \to A$，满足：
$$h(a, 0) = a, \qquad h(a, 1) = a_0, \qquad \forall a \in A.$$
取 $Z = Y$，$f_0 = \mathrm{id}_Y: Y \to Y$，并将 $h$ 与包含映射 $i: A \hookrightarrow Y$ 复合得到 $i \circ h: A \times I \to Y$。由于 $(i \circ h)(a, 0) = a = \mathrm{id}_Y(a)$，应用 $(Y, A)$ 的同伦延拓性质，存在连续同伦 $H: Y \times I \to Y$（记 $H_t(y) = H(y, t)$），满足：
1. $H_0 = \mathrm{id}_Y$；
2. 对任意 $t \in I$ 及 $a \in A$，$H_t(a) = h(a, t) \in A$，故 $H_t(A) \subseteq A$；
3. 当 $t = 1$ 时，对任意 $a \in A$，$H_1(a) = h(a, 1) = a_0$，即 $H_1(A) = \{a_0\}$。

#### 2. 同伦逆映射 $g: Y/A \to Y$ 的构造及 $g \circ q \simeq \mathrm{id}_Y$
设 $q: Y \to Y/A$ 为商映射，记 $* = q(A) \in Y/A$ 为将 $A$ 坍缩所得的基点。
考察连续映射 $H_1: Y \to Y$。因为在 $q$ 的唯一非平凡纤维 $A$ 上，$H_1(A) = \{a_0\}$ 为常值映射，由**商拓扑的泛性质**，存在唯一的连续映射 $g: Y/A \to Y$ 使得
$$g \circ q = H_1.$$
由于 $H: Y \times I \to Y$ 是连接 $H_0 = \mathrm{id}_Y$ 与 $H_1 = g \circ q$ 的连续同伦，立即得到
$$g \circ q \simeq \mathrm{id}_Y.$$

#### 3. 同伦为何能下降到商空间以及 $q \circ g \simeq \mathrm{id}_{Y/A}$
要证 $q \circ g \simeq \mathrm{id}_{Y/A}$，考察复合映射 $q \circ H: Y \times I \to Y/A$。我们需要将 $q \circ H$ 沿着乘积映射
$$q \times \mathrm{id}_I: Y \times I \longrightarrow (Y/A) \times I$$
下降为商空间上的同伦 $\widetilde{H}: (Y/A) \times I \to Y/A$。同伦之所以能连续下降到商空间，由以下两条拓扑性质保证：

1. **乘积映射 $q \times \mathrm{id}_I$ 仍是商映射（拓扑前提）：**
   一般拓扑学中，商映射与恒等映射的乘积未必仍是商映射；但此处单位区间 $I = [0,1]$ 是**局部紧 Hausdorff 空间**。由 Whitehead 定理（若 $Z$ 为局部紧 Hausdorff 空间且 $q: X \to W$ 为商映射，则 $q \times \mathrm{id}_Z: X \times Z \to W \times Z$ 也是商映射；或者等价地，因为有限 CW 复形 $Y$ 及 $Y/A$ 均为紧 Hausdorff 空间，$q \times \mathrm{id}_I$ 是从紧空间 $Y \times I$ 到 Hausdorff 空间 $(Y/A) \times I$ 的连续满射，故为闭映射从而是商映射），$q \times \mathrm{id}_I$ 必为商映射。
2. **映射在纤维上保持常值（代数/集合前提）：**
   $q \times \mathrm{id}_I$ 的非单点纤维形如 $A \times \{t\}$（$t \in I$）。由第 1 步性质 2，对任意 $t \in I$ 和 $a \in A$，有 $H(a, t) = h(a, t) \in A$，因此
   $$(q \circ H)(a, t) = q(h(a, t)) = *.$$
   这表明 $q \circ H$ 在 $q \times \mathrm{id}_I$ 的每一个纤维上均为常值。

结合上述两条，由商映射 $q \times \mathrm{id}_I$ 的泛性质，存在唯一的连续映射 $\widetilde{H}: (Y/A) \times I \to Y/A$ 使得
$$\widetilde{H} \circ (q \times \mathrm{id}_I) = q \circ H.$$
检验 $\widetilde{H}$ 在两端点 $t=0,1$ 处的取值（对任意 $y \in Y$）：
- 当 $t=0$ 时：$\widetilde{H}(q(y), 0) = q(H_0(y)) = q(y) = \mathrm{id}_{Y/A}(q(y))$；
- 当 $t=1$ 时：$\widetilde{H}(q(y), 1) = q(H_1(y)) = q(g(q(y))) = (q \circ g)(q(y))$。

因为 $q$ 是满射，故 $\widetilde{H}_0 = \mathrm{id}_{Y/A}$ 且 $\widetilde{H}_1 = q \circ g$，即 $\widetilde{H}$ 给出了同伦 $q \circ g \simeq \mathrm{id}_{Y/A}$。综上，$q: Y \to Y/A$ 是同伦等价。$\blacksquare$

---

## S2 非可缩底空间上的锥附着

### 命题结论
设 $D$ 为路径连通有限 CW 复形，$L \subset D$ 为非空有限子复形，且包含映射 $i: L \hookrightarrow D$ 零伦。令 $Y = D \cup_L CL$，则 $Y \simeq D \vee \Sigma L$。

### 完整证明与楔点选择说明

#### 1. 记号约定与楔点的选择
- **锥与非约化悬挂：**
  锥 $CL = (L \times [0,1]) / (L \times \{1\})$，其中将底面 $L \times \{0\}$ 与 $L$ 等同，记锥顶 $[x, 1]$ 为 $c_+$。在粘合空间 $Y = D \cup_L CL$ 中，对每个 $x \in L$，$D$ 中的 $i(x) = x$ 与 $CL$ 中的 $[x, 0]$ 被等同。
  非约化悬挂 $\Sigma L = (L \times [0,1]) / (L \times \{0\}, L \times \{1\}) \cong CL / L$，其元素记为 $\langle x, s \rangle$（$x \in L, s \in [0,1]$），南极（底面坍缩点）记为 $s_- = \langle x, 0 \rangle$，北极（锥顶坍缩点）记为 $s_+ = \langle x, 1 \rangle$。
- **楔点的选择说明：**
  1. **$D$ 中楔点的选择：** 因为 $i: L \hookrightarrow D$ 零伦，存在某点 $d_0 \in D$ 及零伦 $H: L \times I \to D$ 使得 $H(x, 0) = x$ 且 $H(x, 1) = d_0$（$\forall x \in L$）。若在路径连通空间 $D$ 中另取任意一点 $d_0' \in D$，可取连接 $d_0$ 到 $d_0'$ 的路径 $\gamma: I \to D$，将 $H$ 与 $\gamma$ 拼接即得终止于常值 $d_0'$ 的零伦。因此在 $D$ 中可任取一点 $d_0 \in D$（通常取为零伦终点，或取为 $D$ 的一个 $0$-胞腔）作为楔点。
  2. **$\Sigma L$ 中楔点的选择：** 在构造中，$\Sigma L = CL/L$ 上的自然楔点选为**悬挂极点 $s_- = [L \times \{0\}]$**（即 $CL$ 的底面 $L$ 坍缩所得的南极；由反射同胚 $\langle x, s \rangle \mapsto \langle x, 1-s \rangle$，选北极 $s_+$ 完全对称）。注意 $L$ 虽未必路径连通，但因 $L$ 非空（存在 $x_0 \in L$），$\Sigma L$ 中任意点 $\langle x, s \rangle$ 均可经路径 $\tau \mapsto \langle x, (1-\tau)s \rangle$ 连到 $s_-$，故 $\Sigma L$ **总是路径连通的**。又因 $D$ 与 $\Sigma L$ 均为路径连通 CW 复形，楔和 $D \vee \Sigma L = (D, d_0) \vee (\Sigma L, s_-)$ 的（无基点）同伦型不依赖于楔点在 $D$ 和 $\Sigma L$ 中的具体选取。

以下固定 $d_0 \in D$、南极 $s_- \in \Sigma L$ 为楔点（在 $D \vee \Sigma L$ 中将 $d_0$ 与 $s_-$ 等同，记为 $w_0$），并固定满足 $H(x,0)=x, H(x,1)=d_0$ 的零伦 $H: L \times I \to D$。

#### 2. 显式同伦等价映射的构造
（注：亦可由粘合引理得到——因 $(CL, L)$ 是 CW 复形对，$L \hookrightarrow CL$ 是上纤维化，将粘合映射 $i: L \to D$ 沿零伦 $H$ 替换为常值映射 $c_{d_0}: L \to \{d_0\} \subset D$ 不改变推出空间的同伦型，故 $D \cup_i CL \simeq D \cup_{c_{d_0}} CL \cong (D, d_0) \vee (CL/L, [L]) = D \vee \Sigma L$。下面给出直接且具体的互逆同伦等价映射与同伦。）

- **正向映射 $f: Y = D \cup_L CL \to D \vee \Sigma L$：**
  在 $D$ 上定义 $\left.f\right|_D = \mathrm{id}_D$；在 $CL$ 上对 $[x, t] \in CL$ 定义
  $$f([x, t]) = \begin{cases} H(x, 2t) \in D, & 0 \le t \le \frac{1}{2}, \\ \langle x, 2t - 1 \rangle \in \Sigma L, & \frac{1}{2} \le t \le 1. \end{cases}$$
  **良定义与连续性检验：**
  - 当 $t=0$ 时，$f([x, 0]) = H(x, 0) = x = \left.f\right|_D(x)$，在粘合处 $L = D \cap CL$ 相容；
  - 当 $t=1/2$ 时，$H(x, 1) = d_0 \in D$ 且 $\langle x, 0 \rangle = s_- \in \Sigma L$，在 $D \vee \Sigma L$ 中二者同为楔点 $w_0$；
  - 当 $t=1$ 时，$\langle x, 1 \rangle = s_+ \in \Sigma L$ 与 $x \in L$ 无关，故在商空间 $CL$ 的锥顶 $c_+$ 处良定义。
  由商拓扑与粘合拓扑泛性质，$f$ 连续。

- **反向映射 $g: D \vee \Sigma L \to Y = D \cup_L CL$：**
  在 $D$ 上定义 $\left.g\right|_D = \mathrm{id}_D$；在 $\Sigma L$ 上对 $\langle x, s \rangle \in \Sigma L$ 定义
  $$g(\langle x, s \rangle) = \begin{cases} H(x, 1 - 2s) \in D, & 0 \le s \le \frac{1}{2}, \\ [x, 2s - 1] \in CL, & \frac{1}{2} \le s \le 1. \end{cases}$$
  **良定义与连续性检验：**
  - 当 $s=0$（南极 $s_-$）时，$H(x, 1) = d_0$ 与 $x \in L$ 无关，且与 $\left.g\right|_D(d_0) = d_0$ 在楔点 $w_0$ 处一致；
  - 当 $s=1/2$ 时，$H(x, 0) = x \in L \subset D$ 与 $[x, 0] \in CL$ 在 $Y = D \cup_L CL$ 中被等同；
  - 当 $s=1$（北极 $s_+$）时，$[x, 1] = c_+ \in CL$ 与 $x \in L$ 无关。
  故 $g$ 亦良定义且连续。

#### 3. 验证 $g \circ f \simeq \mathrm{id}_Y$ 与 $f \circ g \simeq \mathrm{id}_{D \vee \Sigma L}$
- **$g \circ f \simeq \mathrm{id}_Y$（相对 $D$）：**
  在 $D$ 上 $(g \circ f)\big|_D = \mathrm{id}_D$；在 $CL$ 上，
  $$(g \circ f)([x, t]) = \begin{cases} H(x, 2t) \in D, & 0 \le t \le \frac{1}{2}, \\ H(x, 2 - 4t) \in D, & \frac{1}{2} \le t \le \frac{3}{4}, \\ [x, 4t - 3] \in CL, & \frac{3}{4} \le t \le 1. \end{cases}$$
  分两步构造从 $g \circ f$ 到 $\mathrm{id}_Y$ 的同伦（在 $D$ 上恒为 $\mathrm{id}_D$）：
  1. 对 $u \in [0, 1]$，将区间 $[0, 3/4]$ 上往返于 $x$ 与 $d_0$ 的同伦路径收缩回起点 $x$：
     $$\Phi_u([x, t]) = \begin{cases} H\bigl(x, (1-u)2t\bigr) \in D, & 0 \le t \le \frac{1}{2}, \\ H\bigl(x, (1-u)(2 - 4t)\bigr) \in D, & \frac{1}{2} \le t \le \frac{3}{4}, \\ [x, 4t - 3] \in CL, & \frac{3}{4} \le t \le 1. \end{cases}$$
     在 $t=0$ 处恒为 $H(x,0)=x$；在 $t=1/2$ 处两侧均为 $H(x, 1-u)$；在 $t=3/4$ 处恒为 $H(x,0)=x=[x,0]$；在 $t=1$ 处恒为 $c_+$。当 $u=1$ 时，$\Phi_1([x,t])$ 在 $t \in [0, 3/4]$ 上恒为 $[x, 0]$，在 $t \in [3/4, 1]$ 上为 $[x, 4t-3]$。
  2. 对 $v \in [0, 1]$，做锥坐标的线性重参数化：
     $$\Psi_v([x, t]) = \left[x, \max\left(0, \frac{4t - 3(1-v)}{1 + 3v}\right)\right],$$
     它在 $v=0$ 时为 $\Phi_1$，在 $v=1$ 时为 $\mathrm{id}_{CL}$，且在 $t=0$ 与 $t=1$ 处固定。因此 $g \circ f \simeq \mathrm{id}_Y$。

- **$f \circ g \simeq \mathrm{id}_{D \vee \Sigma L}$（相对 $D$）：**
  在 $D$ 上 $(f \circ g)\big|_D = \mathrm{id}_D$；在 $\Sigma L$ 上，
  $$(f \circ g)(\langle x, s \rangle) = \begin{cases} H(x, 1 - 2s) \in D, & 0 \le s \le \frac{1}{2}, \\ H(x, 4s - 2) \in D, & \frac{1}{2} \le s \le \frac{3}{4}, \\ \langle x, 4s - 3 \rangle \in \Sigma L, & \frac{3}{4} \le s \le 1. \end{cases}$$
  同理，对 $u \in [0, 1]$，定义（在 $D$ 上恒为 $\mathrm{id}_D$）：
  $$\widetilde{\Phi}_u(\langle x, s \rangle) = \begin{cases} H\bigl(x, 1 - (1-u)2s\bigr) \in D, & 0 \le s \le \frac{1}{2}, \\ H\bigl(x, 1 - (1-u)(2 - 4s)\bigr) \in D, & \frac{1}{2} \le s \le \frac{3}{4}, \\ \langle x, 4s - 3 \rangle \in \Sigma L, & \frac{3}{4} \le s \le 1. \end{cases}$$
  在 $s=0$ 和 $s=3/4$ 处恒为 $H(x,1)=d_0=s_-$（与 $x$ 无关），在 $s=1/2$ 处两侧均为 $H(x, u)$。当 $u=1$ 时，$\widetilde{\Phi}_1$ 将 $[0, 3/4]$ 常值映为 $s_- = \langle x, 0 \rangle$，再经线性重参数化 $\widetilde{\Psi}_v(\langle x, s \rangle) = \left\langle x, \max\left(0, \frac{4s - 3(1-v)}{1 + 3v}\right)\right\rangle$（$v \in [0,1]$）即同伦于 $\mathrm{id}_{D \vee \Sigma L}$。

故 $Y = D \cup_L CL \simeq D \vee \Sigma L$。$\blacksquare$

---

## S3 整数扭结的实例

### 构造
设 $L$ 是实射影平面 $\mathbb{R}P^2$ 的任一有限抽象单纯三角剖分（故 $|L| \cong \mathbb{R}P^2$）。由于 $\mathbb{R}P^2 \neq \emptyset$，顶点集 $V(L)$ 非空，任取一个顶点 $u_0 \in V(L)$。另取两个互异且不在 $V(L)$ 中的新顶点 $v, w \notin V(L)$。

1. **有限单纯复形 $K$ 的构造：**
   令 $K$ 为以 $v, w$ 为两极对 $L$ 作双锥（即抽象非约化悬挂）所得的有限抽象单纯复形：
   $$K = (v * L) \cup (w * L) = \bigl\{\sigma,\; \sigma \cup \{v\},\; \sigma \cup \{w\} \;\big|\; \sigma \in L\bigr\}$$
   （其中把空单形 $\emptyset \in L$ 纳入，使得 $\{v\} = \emptyset \cup \{v\} \in K$，$\{w\} = \emptyset \cup \{w\} \in K$）。因 $L$ 有限，$K$ 是有限抽象单纯复形，且其几何实现为
   $$|K| = |v * L| \cup_{|L|} |w * L| \cong \Sigma |L| \cong \Sigma \mathbb{R}P^2.$$
2. **顶点 $v$：** 取上述新顶点 $v \in V(K)$。
3. **含 $v$ 子复形 $B$ 的构造：**
   因为 $\{u_0\} \in L$，在 $v * L \subset K$ 中有 $1$-单形 $\{v, u_0\} \in K$。取 $B$ 为由边 $\{v, u_0\}$ 生成的闭 $1$-单形子复形：
   $$B = \bigl\{\emptyset, \{v\}, \{u_0\}, \{v, u_0\}\bigr\} \subseteq K.$$

### 全部性质的证明

1. **$|K| \setminus \{v\}$ 非空可缩：**
   在 $|K| = |v * L| \cup_{|L|} |w * L|$ 中，去掉顶点 $v$ 后，开星形 $|v * L| \setminus \{v\}$ 的每个点可唯一表示为重心坐标 $(1-t)v + t y$（其中 $y \in |L|, t \in (0, 1]$）。定义线性形变收缩 $H_s: |K| \setminus \{v\} \to |K| \setminus \{v\}$（$s \in [0,1]$）：在 $|w * L|$ 上恒为恒等映射，在 $|v * L| \setminus \{v\}$ 上定义为
   $$H_s\bigl((1-t)v + ty\bigr) = (1-s)(1-t)v + \bigl(1 - (1-s)(1-t)\bigr)y.$$
   当 $s=1$ 时，$H_1$ 将 $|K| \setminus \{v\}$ 强形变收缩到子复形 $|K \setminus v| = |w * L| = C|L|$。而 $|w * L|$ 是以 $w$ 为锥顶的锥，包含点 $w$（故非空）且可线性收缩到顶点 $\{w\}$。因此 $|K| \setminus \{v\}$ 非空且可缩。
2. **$(|B| \setminus \{v\}) \hookrightarrow |B|$ 为同伦等价：**
   $|B|$ 同胚于闭区间 $[0, 1]$（端点对应 $u_0$ 和 $v$），而 $|B| \setminus \{v\}$ 同胚于半开区间 $[0, 1)$（包含端点 $u_0$）。二者均以 $\{u_0\}$ 为强形变收缩核，皆为可缩空间；两个可缩空间之间的任意连续映射（特别是包含映射 $(|B| \setminus \{v\}) \hookrightarrow |B|$）必为同伦等价。
3. **$|K|$ 的约化有理同调全零（$\widetilde{H}_*(|K|; \mathbb{Q}) = 0$）：**
   将 $|K| \cong \Sigma \mathbb{R}P^2$ 分解为两个可缩闭锥 $C_+ = |v * L|$ 与 $C_- = |w * L|$，其交 $C_+ \cap C_- = |L| \cong \mathbb{R}P^2$。因为 $(C_+, |L|)$ 和 $(C_-, |L|)$ 是 CW 复形对，满足切除定理条件，对任意系数群 $G$ 应用约化同调的 Mayer-Vietoris 正合列：
   $$\cdots \longrightarrow \widetilde{H}_n(C_+; G) \oplus \widetilde{H}_n(C_-; G) \longrightarrow \widetilde{H}_n(|K|; G) \xrightarrow{\;\partial\;} \widetilde{H}_{n-1}(|L|; G) \longrightarrow \widetilde{H}_{n-1}(C_+; G) \oplus \widetilde{H}_{n-1}(C_-; G) \longrightarrow \cdots$$
   因 $C_+, C_-$ 可缩，其约化同调全为零，故得悬挂同构：
   $$\widetilde{H}_0(|K|; G) = 0, \qquad \widetilde{H}_{n}(|K|; G) \cong \widetilde{H}_{n-1}(\mathbb{R}P^2; G) \quad (\forall n \ge 1).$$
   取有理系数 $G = \mathbb{Q}$。已知实射影平面的整系数约化同调为：
   $$\widetilde{H}_k(\mathbb{R}P^2; \mathbb{Z}) \cong \begin{cases} \mathbb{Z}/2\mathbb{Z}, & k = 1, \\ 0, & k \neq 1. \end{cases}$$
   由同调的泛系数定理（因 $\mathbb{Q}$ 是无挠 Abel 群，$\mathrm{Tor}_1^{\mathbb{Z}}(-, \mathbb{Q}) = 0$），对一切 $k \in \mathbb{Z}$ 有
   $$\widetilde{H}_k(\mathbb{R}P^2; \mathbb{Q}) \cong \widetilde{H}_k(\mathbb{R}P^2; \mathbb{Z}) \otimes_{\mathbb{Z}} \mathbb{Q} = 0.$$
   从而对一切 $n \in \mathbb{Z}$，$\widetilde{H}_n(|K|; \mathbb{Q}) = 0$。
4. **$|K|$ 不可缩：**
   在上述悬挂同构中取整系数 $G = \mathbb{Z}$ 及 $n = 2$，得
   $$\widetilde{H}_2(|K|; \mathbb{Z}) \cong \widetilde{H}_1(\mathbb{R}P^2; \mathbb{Z}) \cong \mathbb{Z}/2\mathbb{Z} \neq 0.$$
   因为可缩空间的全部整系数约化同调群必为零，故 $\widetilde{H}_2(|K|; \mathbb{Z}) \neq 0$ 证明 $|K|$ 不可缩。$\blacksquare$

---

## S4 整体对象与全部恢复目标

### 总体判定结论
**所列目标在给定条件下全部成立。** 具体而言：
1. **同伦类型刻画：** 满足给定条件的三元组 $(K, v, B)$ 中，$X = |K|$ 的可能同伦类型**恰好是所有非空有限抽象单纯复形 $L$ 的几何实现的非约化悬挂 $\Sigma |L|$ 的同伦类型**（等价地，非空有限 CW 复形的非约化悬挂的同伦类型）。
2. **实现构造：** 对任意非空有限抽象单纯复形 $L$，均可显式构造满足全部条件的三元组 $(K, v, B)$ 使得 $|K| \cong \Sigma |L|$。
3. **$X$ 可缩的局部有限关联判据：** $X = |K|$ 可缩当且仅当仅由 $K$ 中包含 $v$ 的单形及其含 $v$ 的面之间的关联关系所生成的相对单纯链复形 $(C_\bullet^v(K), \partial_\bullet^v)$ 在整系数 $\mathbb{Z}$ 上处处正合（即 $H_p(C_\bullet^v(K); \mathbb{Z}) = 0, \forall p \ge 0$；等价于各阶整关联矩阵 $\partial_p^v$ 的秩满足 $\mathrm{rank}(\partial_{p+1}^v) + \mathrm{rank}(\partial_p^v) = |S_p(v)|$ 且其 Smith 标准型的全部非零不变因子均为 $1$）。

---

### 1. 同伦类型刻画与实现构造的证明

#### （1）必要性：任意满足条件的三元组 $(K, v, B)$ 均有 $X = |K| \simeq \Sigma |L|$（其中 $L = \mathrm{lk}_K(v)$ 非空）

设 $(K, v, B)$ 满足给定条件。引入 $K$ 中关于顶点 $v$ 的标准局部与外部子复形：
- **去点子复形（deletion）：** $K \setminus v = \{\sigma \in K \mid v \notin \sigma\}$；
- **顶点 $v$ 的链环（link）：** $L := \mathrm{lk}_K(v) = \{\tau \in K \setminus v \mid \tau \cup \{v\} \in K\}$；
- **顶点 $v$ 的闭星形（closed star）：** $\mathrm{st}_K(v) = \{\sigma \in K \mid \sigma \cup \{v\} \in K\} = v * L$。

对子复形 $B \subseteq K$，同样定义 $B \setminus v = \{\sigma \in B \mid v \notin \sigma\}$ 与 $L_B := \mathrm{lk}_B(v) = \{\tau \in B \setminus v \mid \tau \cup \{v\} \in B\}$。显然 $L_B \subseteq L$。

- **第一步：由 $O \cap C \hookrightarrow C$ 是同伦等价证明 $L = \mathrm{lk}_K(v)$ 非空。**
  用反证法。假设 $L_B = \mathrm{lk}_B(v) = \emptyset$。则在 $B$ 中没有任何单形同时包含 $v$ 和其他顶点，即 $\{v\}$ 是 $B$ 的孤立顶点。于是几何实现分解为拓扑不交并：
  $$C = |B| = |B \setminus v| \sqcup \{v\} = (O \cap C) \sqcup \{v\},$$
  其中 $\{v\}$ 是 $C$ 的一个单点连通分支（既是开集又是闭集）。因为 $B$ 是有限单纯复形，$O \cap C = |B \setminus v|$ 的路径连通分支数 $|\pi_0(O \cap C)| = m < \infty$ 是有限非负整数，从而 $|\pi_0(C)| = m + 1$。
  然而，包含映射 $O \cap C \hookrightarrow C$ 是同伦等价，故其在路径连通分支集合上诱导的映射 $\pi_0(O \cap C) \to \pi_0(C)$ 必为双射，这与有限基数 $m \neq m+1$ 矛盾！
  因此必有 $L_B = \mathrm{lk}_B(v) \neq \emptyset$。又因 $L_B \subseteq L = \mathrm{lk}_K(v)$，故 $L = \mathrm{lk}_K(v)$ 是**非空**有限抽象单纯复形。

- **第二步：证明 $D := |K \setminus v|$ 是 $O = X \setminus \{v\}$ 的强形变收缩核，从而 $D$ 非空可缩。**
  在 $X = |K|$ 中，每个点 $x \in |K|$ 具有唯一的重心坐标表示 $x = \sum_{u \in V(K)} \lambda_u(x) u$（$\lambda_u(x) \ge 0, \sum_u \lambda_u(x) = 1$）。于是：
  $$x \in O = |K| \setminus \{v\} \iff \lambda_v(x) < 1, \qquad x \in D = |K \setminus v| \iff \lambda_v(x) = 0.$$
  对任意 $x \in O$ 及 $s \in [0, 1]$，定义映射：
  $$R(x, s) = (1-s)\lambda_v(x)v + \sum_{u \in V(K) \setminus \{v\}} \frac{1 - (1-s)\lambda_v(x)}{1 - \lambda_v(x)} \lambda_u(x) u.$$
  因在 $O$ 上 $1 - \lambda_v(x) > 0$，且对任意 $s \in [0,1]$，$R(x, s)$ 的支撑单形包含于 $x$ 的支撑单形中、在 $v$ 处的系数 $(1-s)\lambda_v(x) < 1$，故 $R: O \times I \to O$ 连续良定义。
  显然 $R(x, 0) = x$，$R(x, 1) \in D$，且当 $x \in D$（即 $\lambda_v(x)=0$）时 $R(x, s) = x$。故 $D = |K \setminus v|$ 是 $O$ 的强形变收缩核。由假设 $O$ 非空可缩，知 $D$ 是非空可缩的有限 CW（单纯）复形。

- **第三步：应用 S1（或 S2）证明 $X \simeq \Sigma |L|$。**
  由 $K = (K \setminus v) \cup (v * L)$ 及 $(K \setminus v) \cap (v * L) = L$，几何实现表示为：
  $$X = |K| = D \cup_{|L|} C|L|,$$
  其中 $C|L| = |v * L|$ 是以 $v$ 为锥顶的锥，且 $|L| \subseteq D$ 是非空有限子复形。
  应用 **S1**（此时 $X$ 为有限 CW 复形，$D \subset X$ 为非空可缩子复形，满足 S1 的全部前提）：商映射 $X \to X/D$ 是同伦等价。又因 $D \cap C|L| = |L|$，商空间为
  $$X/D = (D \cup_{|L|} C|L|)/D \cong C|L| / |L| = \Sigma |L|.$$
  （等价地，因 $D$ 可缩，包含映射 $|L| \hookrightarrow D$ 零伦，满足 **S2** 的全部前提，故 $X \simeq D \vee \Sigma|L| \simeq * \vee \Sigma|L| \simeq \Sigma|L|$。）
  因此 $X = |K| \simeq \Sigma |L|$，其中 $L = \mathrm{lk}_K(v)$ 为非空有限抽象单纯复形。

#### （2）充分性与实现构造：对任意非空有限抽象单纯复形 $L$ 实现 $X \simeq \Sigma |L|$

设 $L$ 是任意给定的非空有限抽象单纯复形。因 $L$ 非空，存在顶点 $u_0 \in V(L)$。取两个互异的新顶点 $v, w \notin V(L)$，仿照 S3 令：
$$K = (v * L) \cup (w * L), \qquad B = \bigl\{\emptyset, \{v\}, \{u_0\}, \{v, u_0\}\bigr\} \subseteq v * L \subseteq K.$$
则：
1. $K$ 是有限抽象单纯复形，$v \in V(K)$，$B \subseteq K$ 是含 $v$ 的子复形；
2. $X = |K| = |v * L| \cup_{|L|} |w * L| \cong \Sigma |L|$；
3. $O = |K| \setminus \{v\}$ 强形变收缩到 $|K \setminus v| = |w * L| = C|L|$，后者是以 $w$ 为顶点的锥，故 $O$ 非空可缩；
4. $C = |B| \cong [0, 1]$ 且 $O \cap C = |B| \setminus \{v\} \cong [0, 1)$，二者均强形变收缩到 $\{u_0\}$，故包含映射 $O \cap C \hookrightarrow C$ 是同伦等价。

这完成了刻画与实现构造的证明。

---

### 2. $X$ 可缩的局部有限关联判据及其证明

#### （1）纯局部有限关联数据的定义与链复形构造
仅使用 $K$ 中**包含顶点 $v$ 的单形及其面之间的有限关联数据**，如下构造一个有限自由 Abel 群链复形 $\bigl(C_\bullet^v(K), \partial_\bullet^v\bigr)$：

1. 对每个整数 $p \ge 0$，记
   $$S_p(v) = \{\sigma \in K \mid v \in \sigma,\; \dim\sigma = p\}$$
   为 $K$ 中包含 $v$ 的 $p$ 维单形集合（注意 $S_0(v) = \{\{v\}\}$ 只含单点单形 $\{v\}$，且因 $K$ 有限，当 $p > \dim K$ 时 $S_p(v) = \emptyset$）。
2. 对每个单形 $\sigma \in S_p(v)$（$p \ge 1$），$\sigma$ 的全体 $(p-1)$ 维面中，恰好有 $p$ 个面包含 $v$（属于 $S_{p-1}(v)$），另有唯一一个面不含 $v$（即 $\tau = \sigma \setminus \{v\} \in \mathrm{lk}_K(v)$）。
   为消除定向任意性，固定将 $S_1(v)$（它们与 $\mathrm{lk}_K(v)$ 的顶点集双射对应：$\{v, u\} \leftrightarrow u$）赋予一个任意全序 $\prec$。对每个 $\sigma \in S_p(v)$（$p \ge 1$），其包含的 $p$ 个属于 $S_1(v)$ 的 $1$ 维面按全序排列为 $e_0 \prec e_1 \prec \cdots \prec e_{p-1}$；删去第 $i$ 个 $1$ 维面所对应的顶点即得 $\sigma$ 的第 $i$ 个含 $v$ 的 $(p-1)$ 维面，记为 $d_i^v(\sigma) \in S_{p-1}(v)$（当 $p=1$ 时，$d_0^v(\{v, u\}) = \{v\} \in S_0(v)$）。
3. 令 $C_p^v(K) = \mathbb{Z}[S_p(v)]$ 为以 $S_p(v)$ 为基的有限秩自由 $\mathbb{Z}$-模，定义边缘同态 $\partial_p^v: C_p^v(K) \to C_{p-1}^v(K)$（$p \ge 1$）：
   $$\partial_p^v(\sigma) = \sum_{i=0}^{p-1} (-1)^i d_i^v(\sigma) \in C_{p-1}^v(K), \qquad \partial_0^v = 0.$$
   （注：此构造仅用到了含 $v$ 单形集合 $\bigcup_{p \ge 0} S_p(v)$ 及其内部的包含关系 $\sigma' \subset \sigma$。）

#### （2）有限可检验的充要判据
**判据：** 在满足 S4 前提的三元组 $(K, v, B)$ 中，$X = |K|$ 可缩**当且仅当**上述局部链复形 $\bigl(C_\bullet^v(K), \partial_\bullet^v\bigr)$ 在 $\mathbb{Z}$ 上处处正合，即：
$$H_p\bigl(C_\bullet^v(K), \partial_\bullet^v\bigr) = \frac{\ker \partial_p^v}{\mathrm{im}\, \partial_{p+1}^v} = 0, \qquad \forall p \ge 0.$$
**有限矩阵检验算法（Smith 标准型）：**
由于每个 $S_p(v)$ 均为有限集，$\partial_p^v$ 是 $|S_{p-1}(v)| \times |S_p(v)|$ 阶整系数矩阵（元素仅取 $0, \pm 1$）。对每个 $1 \le p \le \dim K$ 计算 $\partial_p^v$ 的整矩阵 Smith 标准型，设其秩为 $r_p = \mathrm{rank}(\partial_p^v)$（约定 $r_0 = 0, r_{\dim K + 1} = 0$）。则 $X$ 可缩当且仅当对所有 $0 \le p \le \dim K$ 同时满足：
1. **秩条件（无自由部）：** $r_{p+1} + r_p = |S_p(v)|$；
2. **无挠条件（无整数扭结）：** 每个 $\partial_p^v$（$p \ge 1$）的 Smith 标准型中全部 $r_p$ 个非零对角元（不变因子）均等于 $1$。

#### （3）判据的完整证明
- **第一步：建立链复形同构 $C_\bullet^v(K) \cong \widetilde{C}_{\bullet-1}(L; \mathbb{Z})$。**
  映射 $\Phi_p: S_p(v) \to L_{p-1} = \{\tau \in \mathrm{lk}_K(v) \mid \dim\tau = p-1\}$（对 $p \ge 1$，$\sigma \mapsto \sigma \setminus \{v\}$；对 $p=0$，$\{v\} \mapsto \emptyset$）是双射，且单形之间的面包含关系满足：对 $\sigma' \in S_{p-1}(v), \sigma \in S_p(v)$，
  $$\sigma' \subset \sigma \iff (\sigma' \setminus \{v\}) \subset (\sigma \setminus \{v\}).$$
  在顶点全序下，$d_i^v(\sigma) \setminus \{v\} = d_i(\sigma \setminus \{v\})$（当 $p=1$ 时，$d_0^v(\{v, u\}) = \{v\}$ 对应增广映射 $\epsilon(u) = 1 \in \mathbb{Z} = C_0^v(K)$）。因此，$\Phi_\bullet$ 诱导了链复形的同构：
  $$\bigl(C_\bullet^v(K), \partial_\bullet^v\bigr) \cong \bigl(\widetilde{C}_{\bullet-1}(L; \mathbb{Z}), \widetilde{\partial}_{\bullet-1}\bigr),$$
  其中右侧是 $L = \mathrm{lk}_K(v)$ 的增广单纯链复形（次数平移 $+1$）。同时，$C_\bullet^v(K)$ 也是相对单纯链复形 $C_\bullet(K, K \setminus v; \mathbb{Z})$。
  取同调即得自然同构（并结合 S3 中的悬挂同构）：
  $$H_p\bigl(C_\bullet^v(K), \partial_\bullet^v\bigr) \cong \widetilde{H}_{p-1}(L; \mathbb{Z}) \cong \widetilde{H}_p(\Sigma |L|; \mathbb{Z}) \cong \widetilde{H}_p(X; \mathbb{Z}), \qquad \forall p \ge 0.$$

- **第二步：必要性（$X$ 可缩 $\implies H_p(C_\bullet^v(K), \partial_\bullet^v) = 0, \forall p \ge 0$）。**
  若 $X$ 可缩，则对一切 $p \ge 0$，$\widetilde{H}_p(X; \mathbb{Z}) = 0$，由上述同构立即得到 $H_p(C_\bullet^v(K), \partial_\bullet^v) = 0$（$\forall p \ge 0$）。

- **第三步：充分性（$H_p(C_\bullet^v(K), \partial_\bullet^v) = 0\; (\forall p \ge 0) \implies X$ 可缩）。**
  设对所有 $p \ge 0$ 有 $H_p(C_\bullet^v(K), \partial_\bullet^v) = 0$。则对所有 $q \ge 0$，$\widetilde{H}_q(|L|; \mathbb{Z}) \cong \widetilde{H}_q(L; \mathbb{Z}) \cong H_{q+1}(C_\bullet^v(K), \partial_\bullet^v) = 0$。
  1. **证明 $\Sigma |L|$ 单连通（Seifert-van Kampen 定理）：**
     特别地，当 $q = 0$ 时，$\widetilde{H}_0(|L|; \mathbb{Z}) = 0$，这意味着非空有限多面体 $|L|$ 是**路径连通**的。
     在非约化悬挂 $\Sigma |L| = (|L| \times [0,1]) / (|L| \times \{0\}, |L| \times \{1\})$ 中，取两个开子集：
     $$U_+ = q_{\Sigma}\bigl(|L| \times (1/3, 1]\bigr), \qquad U_- = q_{\Sigma}\bigl(|L| \times [0, 2/3)\bigr).$$
     则 $\Sigma |L| = U_+ \cup U_-$，其中 $U_+$ 和 $U_-$ 均为开锥，故皆可缩（特别地路径连通且单连通：$\pi_1(U_+) = \pi_1(U_-) = \{1\}$）。
     而它们的交集 $U_+ \cap U_- \cong |L| \times (1/3, 2/3) \simeq |L|$ 非空且**路径连通**（因 $\widetilde{H}_0(|L|; \mathbb{Z}) = 0$）。
     这满足 **Seifert-van Kampen 定理**的全部适用条件（两个路径连通开集覆盖全空间，且交集非空路径连通），从而推出 $\pi_1(\Sigma |L|) = \{1\}$，即 $\Sigma |L|$ 是**单连通** CW 复形。
  2. **由 Hurewicz 定理与 Whitehead 定理推出可缩性：**
     因为 $\Sigma |L|$ 是单连通 CW 复形，且对一切 $p \ge 1$，
     $$\widetilde{H}_p(\Sigma |L|; \mathbb{Z}) \cong \widetilde{H}_{p-1}(L; \mathbb{Z}) = 0,$$
     应用**同伦论中的 Hurewicz 定理**（若单连通空间 $W$ 满足对所有 $1 \le i < n$ 有 $\pi_i(W) = 0$，则 $\pi_n(W) \cong H_n(W; \mathbb{Z})$），对 $n \ge 2$ 归纳即得对一切 $n \ge 1$ 有 $\pi_n(\Sigma |L|) = 0$。
     再应用 **Whitehead 定理**（若两个 CW 复形之间的映射诱导所有同伦群的同构，则该映射为同伦等价；应用于常值映射 $\Sigma |L| \to \{*\}$），得知 CW 复形 $\Sigma |L|$ 可缩。
     最后，由第一部分已证的同伦等价 $X \simeq \Sigma |L|$，得出 $X = |K|$ 可缩。$\blacksquare$

---

## S5 不提供子复形 B

### 判定结论与新增类型分类
1. **判定结论：** 若仅假设 $K$ 有限、$v \in K$ 为顶点且 $|K| \setminus \{v\}$ 非空可缩（不再提供子复形 $B$ 及其同伦等价条件），则 $|K|$ **未必**同伦等价于非空有限复形的悬挂。
2. **新增可能同伦类型的完整分类：** 在同伦等价意义下，**唯一新增的同伦类型是离散两点空间 $S^0 = \{0, 1\}$ 的同伦类型**（它对应于 $\mathrm{lk}_K(v) = \emptyset$ 的情形，可视为空复形 $\emptyset$ 的形式非约化悬挂 $S^0 * \emptyset = S^0$）。即此时 $|K|$ 的可能同伦类型恰好分为两类：
   - 当 $\mathrm{lk}_K(v) \neq \emptyset$ 时，$|K| \simeq \Sigma |\mathrm{lk}_K(v)|$（非空有限单纯复形的非约化悬挂）；
   - 当 $\mathrm{lk}_K(v) = \emptyset$ 时，$|K| \simeq S^0$（离散两点空间）。

### 满足全部前提的反例与完整证明

#### 1. 满足全部前提的反例
取有两个顶点 $v, w$（$v \neq w$）且无更高维单形的 $0$ 维有限抽象单纯复形：
$$K = \bigl\{\emptyset, \{v\}, \{w\}\bigr\}.$$
- **检验前提：** $K$ 是有限抽象单纯复形，$v \in K$ 是顶点；$|K| \setminus \{v\} = \{w\}$ 是单点空间，故**非空且可缩**。
- **验证 $|K|$ 不同伦等价于任何非空复形的悬挂：**
  此时 $|K| = \{v, w\} \cong S^0$ 具有 $2$ 个路径连通分支（$|\pi_0(|K|)| = 2$，或 $\widetilde{H}_0(|K|; \mathbb{Z}) \cong \mathbb{Z} \neq 0$）。
  然而，对**任意非空**拓扑空间 $Y$（任取 $y_0 \in Y$），其非约化悬挂 $\Sigma Y$ 中的任意点 $\langle y, t \rangle$ 均可经路径 $s \mapsto \langle y, (1-s)t \rangle$ 连接到南极 $s_- = \langle y_0, 0 \rangle$，故 $\Sigma Y$ 必路径连通（$|\pi_0(\Sigma Y)| = 1$，$\widetilde{H}_0(\Sigma Y; \mathbb{Z}) = 0$）。
  因路径连通分支个数 $|\pi_0(-)|$ 是同伦不变量，故 $|K| \not\simeq \Sigma Y$。

#### 2. 新增类型的分类证明
设 $(K, v)$ 满足 $K$ 有限且 $O = |K| \setminus \{v\}$ 非空可缩。按 $L = \mathrm{lk}_K(v)$ 是否为空分两种互补情形讨论：
- **情形一：$L = \mathrm{lk}_K(v) \neq \emptyset$。**
  注意在 S4 第一部分的证明中，子复形 $B$ 的条件仅在“第一步”中用于推出 $\mathrm{lk}_K(v) \neq \emptyset$；只要 $\mathrm{lk}_K(v) \neq \emptyset$，S4 的“第二步”与“第三步”原封不动成立，故 $|K| \simeq \Sigma |L|$，已属于非空有限复形的非约化悬挂。
- **情形二：$L = \mathrm{lk}_K(v) = \emptyset$。**
  此时 $K$ 中没有包含 $v$ 的正维数单形，即 $\{v\}$ 是 $K$ 的孤立顶点，故 $K = (K \setminus v) \sqcup \{\{v\}\}$，其几何实现为拓扑不交并：
  $$|K| = (|K| \setminus \{v\}) \sqcup \{v\} = O \sqcup \{v\}.$$
  由假设 $O$ 非空可缩，存在同伦等价 $O \simeq \{*\}$。而在拓扑不交并下同伦等价保持不变，故
  $$|K| = O \sqcup \{v\} \simeq \{*\} \sqcup \{v\} \cong S^0.$$
  结合上面已构造的反例 $K = \{\emptyset, \{v\}, \{w\}\}$，可知 $S^0$ 的同伦类型确可实现且为唯一新增的同伦类型。$\blacksquare$

---

## S6 悬挂信息的逆向恢复

### 判定结论
对非空有限单纯复形 $L_1, L_2$，$\Sigma |L_1| \simeq \Sigma |L_2|$ **未必**推出 $|L_1| \simeq |L_2|$。

### 反例构造与完整证明

下面给出两个本质不同且满足全部前提的反例（反例一基于基本群非交换性与上同调环乘法，直接由 S1、S2 严格证明；反例二直接呼应 S4 的可缩性判据）。

---

#### 反例一：$2$ 维环面 $T^2 = S^1 \times S^1$ 与楔和 $S^1 \vee S^1 \vee S^2$

1. **有限单纯复形 $L_1, L_2$ 的选取：**
   - 取 $L_1$ 为 $2$ 维环面 $T^2 = S^1 \times S^1$ 的任一有限单纯三角剖分（例如经典的 $7$ 顶点或 $9$ 顶点三角剖分），则 $|L_1| \cong S^1 \times S^1$；
   - 取 $L_2$ 为楔和空间 $S^1 \vee S^1 \vee S^2$ 的任一有限单纯三角剖分（例如取两个边界为三角形的圆周 $\partial \Delta^2$ 与一个四面体边界 $\partial \Delta^3$，在同一个公共顶点 $x_0$ 处楔和），则 $|L_2| \cong S^1 \vee S^1 \vee S^2$。
   显然 $L_1, L_2$ 均为非空有限抽象单纯复形。

2. **证明 $|L_1| \not\simeq |L_2|$：**
   比较两者的基本群（或整系数上同调环）：
   - $\pi_1(|L_1|) \cong \pi_1(S^1 \times S^1) \cong \mathbb{Z} \times \mathbb{Z}$ 是交换群；
   - 由 Seifert-van Kampen 定理，$\pi_1(|L_2|) \cong \pi_1(S^1 \vee S^1 \vee S^2) \cong \mathbb{Z} * \mathbb{Z}$ 是两个生成元的非交换自由群。
   （或者：在整上同调环 $H^*(-; \mathbb{Z})$ 中，$H^1(T^2; \mathbb{Z}) \times H^1(T^2; \mathbb{Z}) \xrightarrow{\smile} H^2(T^2; \mathbb{Z}) \cong \mathbb{Z}$ 的杯积满射非零，而 $S^1 \vee S^1 \vee S^2$ 上 $H^1$ 的杯积恒为零。）
   因为基本群的同构类（以及上同调环结构）是同伦不变量，故 $|L_1| \not\simeq |L_2|$。

3. **应用 S1 与 S2 证明 $\Sigma |L_1| \simeq \Sigma |L_2|$：**
   - **第一步（由 S1 将非约化悬挂化归为约化悬挂）：**
     对任意带基点 $w_0$（取为 $0$-胞腔）的有限 CW 复形 $W$，在其非约化悬挂 $\Sigma W$ 中，子空间 $A = \{w_0\} \times I$ 是同胚于闭区间 $I$ 的非空可缩子复形。应用 **S1**，商映射 $\Sigma W \to \Sigma W / A = \widetilde{\Sigma} W$（约化悬挂）是同伦等价。
   - **第二步（计算 $\widetilde{\Sigma}|L_2|$）：**
     约化悬挂与楔和可交换，且 $\widetilde{\Sigma} S^n \cong S^{n+1}$，故
     $$\Sigma |L_2| \simeq \widetilde{\Sigma}(S^1 \vee S^1 \vee S^2) \cong \widetilde{\Sigma} S^1 \vee \widetilde{\Sigma} S^1 \vee \widetilde{\Sigma} S^2 \cong S^2 \vee S^2 \vee S^3.$$
   - **第三步（用 S2 计算 $\widetilde{\Sigma}|L_1|$）：**
     环面 $T^2 = S^1 \times S^1$ 具有标准 CW 贴胞分解：
     $$T^2 \cong (S^1 \vee S^1) \cup_\varphi D^2 = (S^1 \vee S^1) \cup_\varphi CS^1,$$
     其中 $D^2 = CS^1$ 沿换位子映射 $\varphi = a b a^{-1} b^{-1}: S^1 \to S^1 \vee S^1$（$a, b$ 为两个圆周生成元）粘合到 $S^1 \vee S^1$ 上。
     因为商空间与紧区间乘积交换（$I$ 局部紧 Hausdorff），对推出贴胞空间取约化悬挂保持推出结构：
     $$\widetilde{\Sigma}(T^2) \cong \widetilde{\Sigma}(S^1 \vee S^1) \cup_{\widetilde{\Sigma}\varphi} C(\widetilde{\Sigma} S^1) \cong (S^2 \vee S^2) \cup_{\widetilde{\Sigma}\varphi} CS^2.$$
     考察粘合映射 $\widetilde{\Sigma}\varphi: S^2 \to S^2 \vee S^2$ 在二阶同伦群 $\pi_2(S^2 \vee S^2, *)$ 中代表的同伦类。由于约化悬挂映射在道路乘积上同伦于余 H-群（co-H-group）乘法，故在 $\pi_2(S^2 \vee S^2, *)$ 中有
     $$[\widetilde{\Sigma}\varphi] = [\widetilde{\Sigma}a] \cdot [\widetilde{\Sigma}b] \cdot [\widetilde{\Sigma}a]^{-1} \cdot [\widetilde{\Sigma}b]^{-1}.$$
     然而，**所有高阶同伦群 $\pi_n$（$n \ge 2$）都是交换群**！因此在交换群 $\pi_2(S^2 \vee S^2, *)$ 中，换位子必为单位元：
     $$[\widetilde{\Sigma}\varphi] = [\widetilde{\Sigma}a] + [\widetilde{\Sigma}b] - [\widetilde{\Sigma}a] - [\widetilde{\Sigma}b] = 0 \in \pi_2(S^2 \vee S^2, *).$$
     这说明映射 $\widetilde{\Sigma}\varphi: S^2 \to S^2 \vee S^2$ **零伦**。
     现在对底空间 $D = S^2 \vee S^2$ 和沿零伦映射 $\widetilde{\Sigma}\varphi$ 附着的锥 $CS^2$ 应用 **S2**（或沿上纤维化 $S^2 \hookrightarrow CS^2$ 将零伦粘合映射 $\widetilde{\Sigma}\varphi$ 同伦替换为常值映射，粘合空间的同伦型不变）：
     $$\Sigma |L_1| \simeq \widetilde{\Sigma}(T^2) \simeq (S^2 \vee S^2) \vee \Sigma S^2 \cong S^2 \vee S^2 \vee S^3 \simeq \Sigma |L_2|.$$

---

#### 反例二（补充：由 S4 可缩判据给出的零调非单连通反例）
- 取 $L_1 = \{\emptyset, \{u_0\}\}$ 为单点复形（$|L_1| = \{u_0\}$ 可缩，$\pi_1(|L_1|) = \{1\}$）；
- 取 $L_2$ 为挖去一个开 $3$ 维单形内部的 Poincaré 同调 $3$ 维球面 $\Sigma^3 \setminus \mathrm{int}(\Delta^3)$ 的有限单纯三角剖分（或具有有限表现完美非平凡基本群的紧致 $\mathbb{Z}$-零调 $2$ 维多面体的三角剖分）。
- 则 $\pi_1(|L_2|) \cong I^*$（$120$ 阶二元二十面体群，非平凡），故 $|L_2|$ 不可缩，从而 $|L_1| \not\simeq |L_2|$。
- 但因 $\widetilde{H}_*(|L_2|; \mathbb{Z}) = 0$，由 **S4 已证的判据**，$\Sigma |L_2|$ 可缩，故 $\Sigma |L_1| \simeq \{*\} \simeq \Sigma |L_2|$。$\blacksquare$
