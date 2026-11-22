# 探针映射空间与连续性层级

---

## S1　局部紧输入

### 1. 通常求值映射的连续性

设 $X$ 为局部紧 Hausdorff 空间，$Y$ 为 Hausdorff 空间。通常求值映射定义为：
$$ev: C_{co}(X, Y) \times X \longrightarrow Y, \quad (f, x) \longmapsto f(x)$$

**证明**：
任取 $(f_0, x_0) \in C_{co}(X, Y) \times X$，设 $W \subset Y$ 为 $ev(f_0, x_0) = f_0(x_0)$ 的任意开邻域。
1. 由 $f_0$ 的连续性，$f_0^{-1}(W)$ 是 $X$ 中包含 $x_0$ 的开集。
2. 因为 $X$ 是局部紧 Hausdorff 空间（因而局部紧正则），存在 $x_0$ 的开邻域 $V \subset X$，使得闭包 $K = \overline{V}$ 是紧集，且 $K \subset f_0^{-1}(W)$。
3. 此时 $f_0(K) \subset W$。由紧开拓扑的定义，子基开集 $[K, W] = \{f \in C(X,Y) : f(K) \subset W\}$ 是 $C_{co}(X, Y)$ 中包含 $f_0$ 的开邻域。
4. 考察积空间中的开邻域 $[K, W] \times V$。对任意 $(f, x) \in [K, W] \times V$，因 $x \in V \subset K$，有：
   $$ev(f, x) = f(x) \in f(K) \subset W$$
   即 $ev([K, W] \times V) \subset W$。
因此 $ev$ 在 $(f_0, x_0)$ 处连续。由 $(f_0, x_0)$ 的任意性，$ev$ 是连续映射。 $\blacksquare$

---

### 2. 柯里化双射及其自然性

定义柯里化映射：
$$\Phi: C(Z, C_{co}(X, Y)) \longrightarrow C(Z \times X, Y), \quad \Phi(g)(z, x) = (g(z))(x) = ev(g(z), x)$$
与逆柯里化映射：
$$\Psi: C(Z \times X, Y) \longrightarrow C(Z, C_{co}(X, Y)), \quad (\Psi(F)(z))(x) = F(z, x)$$

**证明良好定义与双射性**：
1. **$\Phi(g)$ 的连续性**：
   $\Phi(g)$ 可分解为复合：
   $$Z \times X \xrightarrow{g \times \mathrm{id}_X} C_{co}(X, Y) \times X \xrightarrow{ev} Y$$
   $g$ 连续导致 $g \times \mathrm{id}_X$ 连续；又因 $X$ 局部紧 Hausdorff，前文已证 $ev$ 连续。复合连续映射仍连续，故 $\Phi(g) \in C(Z \times X, Y)$。
2. **$\Psi(F)$ 的连续性**：
   - 对固定的 $z \in Z$，$x \mapsto F(z, x)$ 是连续映射 $X \xrightarrow{\iota_z} Z \times X \xrightarrow{F} Y$ 的复合（其中 $\iota_z(x)=(z,x)$ 连续），故 $\Psi(F)(z) \in C_{co}(X, Y)$。
   - 证明 $\Psi(F): Z \to C_{co}(X, Y)$ 连续：只需证明对紧开拓扑的任意子基开集 $[K, W]$（$K \subset X$ 紧，$W \subset Y$ 开），原像 $\Psi(F)^{-1}([K, W])$ 在 $Z$ 中开。
     $$\Psi(F)^{-1}([K, W]) = \{z \in Z : F(\{z\} \times K) \subset W\} = \{z \in Z : \{z\} \times K \subset F^{-1}(W)\}$$
     令 $O = F^{-1}(W)$，由 $F$ 连续知 $O$ 在 $Z \times X$ 中开。若 $z_0 \in \Psi(F)^{-1}([K, W])$，则 $\{z_0\} \times K \subset O$。
     因为 $K$ 是紧集，由管道引理（Tube Lemma），存在 $z_0$ 的开邻域 $V \subset Z$ 使得 $V \times K \subset O$。
     这意味着对所有 $z \in V$，$F(\{z\} \times K) \subset W$，即 $V \subset \Psi(F)^{-1}([K, W])$。因此该原像为开集，$\Psi(F)$ 连续。
3. **互逆双射**：
   直接由底集求值可知 $\Phi(\Psi(F)) = F$ 且 $\Psi(\Phi(g)) = g$。因此 $\Phi$ 是双射。

**自然性验证**：
- **关于 $Z$ 自然**：对任意连续映射 $h: Z' \to Z$，拉回映射满足：
  $$\Phi(g \circ h)(z', x) = (g(h(z')))(x) = \Phi(g)(h(z'), x) = (\Phi(g) \circ (h \times \mathrm{id}_X))(z', x)$$
- **关于 $Y$ 自然**：对任意连续映射 $k: Y \to Y'$，推前映射满足：
  $$\Phi(C(X, k) \circ g)(z, x) = k((g(z))(x)) = (k \circ \Phi(g))(z, x)$$
- **关于 $X$ 自然**：对局部紧 Hausdorff 空间之间的连续映射 $j: X' \to X$，预复合满足：
  $$\Phi(C(j, Y) \circ g)(z, x') = (g(z))(j(x')) = \Phi(g)(z, j(x')) = (\Phi(g) \circ (\mathrm{id}_Z \times j))(z, x')$$
证毕。 $\blacksquare$

---

## S2　探针能检测的映射

### 1. profinite 探针与全部紧 Hausdorff 探针给出相同 $k$ 拓扑

设 $\tau_k$ 为全部紧 Hausdorff 探针给出的拓扑，$\tau_{prof}$ 为 profinite 探针给出的拓扑。

**证明**：
1. **$\tau_k \subset \tau_{prof}$**：
   因为每个 profinite 空间 $S \in \mathrm{Prof}_U$ 均为紧 Hausdorff 空间，每个 profinite 探针 $p: S \to X$ 都是紧 Hausdorff 探针。若 $A \subset X$ 在 $\tau_k$ 中闭，则对任意 profinite 探针 $p: S \to X$，$p^{-1}(A)$ 在 $S$ 中闭，故 $A$ 在 $\tau_{prof}$ 中闭。
2. **$\tau_{prof} \subset \tau_k$**：
   设 $A \subset X$ 在 $\tau_{prof}$ 中闭。任取紧 Hausdorff 空间 $K$ 及连续探针 $f: K \to X$。
   令 $D$ 为 $K$ 的底集赋予离散拓扑。因 $K \in U$，有 $D \in U$。考察其 Stone-Čech 紧化 $\beta D$：
   - 离散空间的 Stone-Čech 紧化 $\beta D$ 是紧 Hausdorff 且零维（具有由闭开集构成的拓扑基），因而是完全不连通的，即 $\beta D \in \mathrm{Prof}_U$。
   - 恒等映射 $D \to K$ 连续，由 Stone-Čech 紧化的泛性质，存在唯一的连续延拓 $\pi: \beta D \to K$。
   - 显然 $D$ 在 $\beta D$ 中稠密且其像覆盖 $K$，故 $\pi$ 是连续满射。
   - 紧空间到 Hausdorff 空间的连续满射必为闭映射，从而 $\pi: \beta D \twoheadrightarrow K$ 是拓扑商映射（quotient map）。
   构造复合映射 $p = f \circ \pi: \beta D \to X$。因 $\beta D \in \mathrm{Prof}_U$，$p$ 是 profinite 探针。
   由 $A$ 在 $\tau_{prof}$ 中闭知，$p^{-1}(A) = \pi^{-1}(f^{-1}(A))$ 在 $\beta D$ 中闭。
   由于 $\pi$ 是商映射，$f^{-1}(A)$ 在 $K$ 中必为闭集。
   由 $K$ 和 $f$ 的任意性，$A$ 在 $\tau_k$ 中闭。
因此 $\tau_{prof} = \tau_k$。 $\blacksquare$

---

### 2. 自然变换与连续映射的同构 $\mathrm{Nat}(h_X, h_Y) \cong C(kX, kY)$

**证明**：
1. **点态表示**：
   单点空间 $* = \{*\} \in \mathrm{Prof}_U$。对于 $x \in X$，记常值映射 $c_x: * \to X$。函子求值 $h_X(*) = C(*, X) \cong X$。
   设 $\alpha: h_X \Rightarrow h_Y$ 为自然变换，定义底集映射 $g: X \to Y$：
   $$g(x) = \alpha_*(c_x)(*)$$
   对任意 $S \in \mathrm{Prof}_U$，$f \in C(S, X)$ 以及 $s \in S$，设点包含映射为 $i_s: * \to S$（$i_s(*) = s$）。因 $f \circ i_s = c_{f(s)}$，由 $\alpha$ 沿 $i_s$ 的自然性：
   $$\alpha_S(f)(s) = (\alpha_S(f) \circ i_s)(*) = \alpha_*(f \circ i_s)(*) = \alpha_*(c_{f(s)})(*) = g(f(s)) = (g \circ f)(s)$$
   即对任意 $S \in \mathrm{Prof}_U$ 与 $f \in C(S, X)$，必有 $\alpha_S(f) = g \circ f$。这表明 $\alpha$ 完全由底集映射 $g$ 决定，且 $g$ 必须满足：对一切 profinite 探针 $f: S \to X$，$g \circ f: S \to Y$ 连续。
2. **连续性等价转化**：
   - 对任意紧 Hausdorff 空间 $S$，连续映射 $h: S \to Y$ 自动连续到 $kY$：对任意 $kY$ 中的开集 $O$，$h^{-1}(O)$ 由 $k$ 拓扑定义即在 $S$ 中开。因此 $C(S, Y) = C(S, kY)$。
   - 由第 1 小节，profinite 探针定义了 $X$ 上的 $k$ 拓扑。根据带最终拓扑（final topology）的空间泛性质，映射 $g: kX \to kY$ 连续，当且仅当对任意测试探针 $f: S \to kX$（即连续映射 $f: S \to X$），复合 $g \circ f: S \to kY$ 连续。
   - 因此，$\{g \circ f \in C(S, Y) \mid \forall S \in \mathrm{Prof}_U, f \in C(S, X)\}$ 充要于 $g \in C(kX, kY)$。
3. 对应关系 $\alpha \mapsto g$ 是双射，其逆映射将 $g \in C(kX, kY)$ 映为后复合自然变换 $\alpha_S(f) = g \circ f$。故：
   $$\mathrm{Nat}(h_X, h_Y) \cong C(kX, kY)$$
$\blacksquare$

---

### 3. 自然变换由原拓扑连续映射诱导的充要条件

**证明**：
连续映射 $f: X \to Y$ 诱导的自然变换对应于集合 $C(X, kY) \subset C(kX, kY)$。欲证：
$$\big(\forall \text{Hausdorff } Y, \, C(X, kY) = C(kX, kY)\big) \iff kX = X$$

- **充分性 ($\Leftarrow$)**：若 $X$ 紧生成，则 $kX = X$。于是对任意 $Y$，$C(kX, kY) = C(X, kY)$，每个自然变换均由原拓扑连续映射诱导。
- **必要性 ($\Rightarrow$)**：假设对所有 Hausdorff 空间 $Y$，均有 $C(kX, kY) = C(X, kY)$。
  由于 $X$ 是 Hausdorff 空间且 $kX$ 拓扑细于 $X$，$kX$ 亦为 Hausdorff 空间，且 $kX \in U$。
  选取 $Y = kX$。由 $k$-化运算的幂等性，$kY = k(kX) = kX$。
  恒等映射 $\mathrm{id}_X: kX \to kX = kY$ 在原定义下连续，故 $\mathrm{id}_X \in C(kX, kY)$。
  根据假设，存在原拓扑连续映射对应此变换，即恒等映射 $\mathrm{id}_X: X \to kX$ 必须连续。
  这表明 $kX$ 上的任意开集在 $X$ 的原拓扑中皆开，即 $\tau_{kX} \subset \tau_X$。
  又恒有 $\tau_X \subset \tau_{kX}$，故 $\tau_X = \tau_{kX}$，即 $kX = X$。$X$ 紧生成。 $\blacksquare$

---

## S3　全部参数化映射记录

### 1. 空间 $M(X,Y)$ 的构造与性质

- **底集**：
  $$M(X,Y) = C(kX, kY)$$
  （此底集自然等同于 $\mathrm{Nat}(h_X, h_Y)$）。
- **拓扑**：
  取紧开拓扑 $C_{co}(kX, kY)$ 的 $k$-化拓扑：
  $$M(X,Y) = k(C_{co}(kX, kY))$$
- **Hausdorff 性验证**：
  因为 $kY$ 为 Hausdorff 空间，$C_{co}(kX, kY)$ 在紧开拓扑下是 Hausdorff 的（若 $f \ne g$，取 $x$ 使 $f(x) \ne g(x)$，利用 $kY$ 的 Hausdorff 性分离两点，其单点紧子集原像开邻域即分离 $f, g$）。
  对 Hausdorff 空间施加 $k$-化得到更细的拓扑，仍保持 Hausdorff 性。从而 $M(X,Y)$ 是紧生成的 Hausdorff 空间。

**验证 $C(S, M(X,Y)) \cong H_{X,Y}(S)$ 自然同构**：
任取 $S \in \mathrm{Prof}_U$。
1. 由定义，$H_{X,Y}(S) = \mathrm{Nat}(h_S \times h_X, h_Y)$。对任意 $T \in \mathrm{Prof}_U$：
   $$(h_S \times h_X)(T) = C(T, S) \times C(T, X) \cong C(T, S \times X) = h_{S \times X}(T)$$
   由 S2 的结论，$\mathrm{Nat}(h_{S \times X}, h_Y) \cong C(k(S \times X), kY)$。
2. 紧 Hausdorff 探针能唯一确定 $k$ 拓扑。因 $S$ 是紧 Hausdorff 空间，对紧探针 $K \to S \times X$，第二坐标因子连续进入 $kX$，故 $k(S \times X) = k(S \times kX)$。
3. 由 Cohen 定理（局部紧 Hausdorff 空间与 $k$ 空间的积空间为 $k$ 空间），紧空间 $S$ 与 $kX$ 的通常积空间 $S \times kX$ 已是 $k$ 空间，从而 $k(S \times kX) = S \times kX$。
4. 由 S1 的指数律（由于 $S$ 局部紧 Hausdorff，置于紧开拓扑第一变量）：
   $$C(S \times kX, kY) \cong C(S, C_{co}(kX, kY))$$
5. 因为 $S$ 紧 Hausdorff，任意连续映射 $S \to C_{co}(kX, kY)$ 自动连续进入其 $k$-化空间 $k C_{co}(kX, kY) = M(X,Y)$，即：
   $$C(S, C_{co}(kX, kY)) = C(S, M(X,Y))$$
综上，在所有 $S \in \mathrm{Prof}_U$ 上自然具备双射：
$$C(S, M(X,Y)) \cong H_{X,Y}(S)$$

---

### 2. 求值自然变换 $ev$ 及伴随同构

- **构造 $ev: h_M \times h_X \to h_Y$**：
  对任意 $T \in \mathrm{Prof}_U$，元组 $(\phi, \psi) \in C(T, M) \times C(T, X)$。定义分量映射：
  $$ev_T(\phi, \psi): T \longrightarrow Y, \quad t \longmapsto (\phi(t))(\psi(t))$$
  - **连续性**：因 $T$ 紧，$T = kT$，$\psi \in C(T, kX)$。这给出了连续映射 $(\phi, \psi): T \to M \times_k kX$。
    在紧生成 Hausdorff 空间范畴 $\mathbf{CGHaus}$ 中，典范求值 $M \times_k kX = k C_{co}(kX, kY) \times_k kX \to kY$ 是连续的；复合连续映射 $kY \to Y$，即得 $t \mapsto (\phi(t))(\psi(t))$ 是连续映射 $T \to Y$。
  - **自然性**：对任意连续映射 $\theta: T' \to T$，
    $$ev_{T'}(\phi \circ \theta, \psi \circ \theta)(t') = \phi(\theta(t'))(\psi(\theta(t'))) = (ev_T(\phi, \psi) \circ \theta)(t')$$
    自然性成立。

- **证明 $\alpha \mapsto ev \circ (\alpha \times \mathrm{id}_{h_X})$ 给出 $\mathrm{Nat}(h_Z, h_M) \cong \mathrm{Nat}(h_Z \times h_X, h_Y)$**：
  设 $Z$ 为任意 Hausdorff 空间。
  1. 根据 S2：
     $$\mathrm{Nat}(h_Z, h_M) \cong C(kZ, kM) = C(kZ, M)$$
     （因 $M$ 紧生成，故 $kM = M$）。
  2. 同样由 S2：
     $$\mathrm{Nat}(h_Z \times h_X, h_Y) \cong \mathrm{Nat}(h_{Z \times X}, h_Y) \cong C(k(Z \times X), kY) \cong C(kZ \times_k kX, kY)$$
  3. 在 Cartesian 闭范畴 $\mathbf{CGHaus}$ 中，具有伴随同构：
     $$C(kZ, k C_{co}(kX, kY)) \cong C(kZ \times_k kX, kY)$$
     该同构由典范求值映射 $E: M \times_k kX \to kY$ 诱导。
  4. 将此伴随转换为预层自然变换，恰由 $\alpha \mapsto ev \circ (\alpha \times \mathrm{id}_{h_X})$ 实现。由于每一步均为双射，该映射构成自然同构：
     $$\mathrm{Nat}(h_Z, h_M) \cong \mathrm{Nat}(h_Z \times h_X, h_Y)$$

- **关于 $X, Y$ 连续映射的自然性**：
  - 对任意连续映射 $u: X' \to X$，$u$ 诱导 $k(u): kX' \to kX$。预复合给出连续映射 $M(u, Y): M(X, Y) \to M(X', Y)$。由复合结合律，$ev_{X'} \circ (M(u, Y) \times \mathrm{id}_{h_{X'}}) = ev_X \circ (\mathrm{id}_{h_M} \times h_u)$，与同构相容。
  - 对任意连续映射 $v: Y \to Y'$，后复合给出连续映射 $M(X, v): M(X, Y) \to M(X, Y')$。同理由结合律 $h_v \circ ev_Y = ev_{Y'} \circ (M(X, v) \times \mathrm{id}_{h_X})$。
  在连续映射下自然性成立。 $\blacksquare$

---

## S4　可数邻域基的输入

### 1. 通常求值映射 $C_{co}(X,Y) \times X \to Y$ 的连续性判断

- **结论**：**否（不必连续）**。
- **反例与核验**：
  取 $X = \mathbb{Q}$（配备欧氏度量诱导的子空间拓扑），$Y = \mathbb{R}$。
  - $X$ 为度量空间，满足第一可数且为 Hausdorff 空间；$Y$ 为 Hausdorff 空间。
  - 考查求值映射 $ev: C_{co}(\mathbb{Q}, \mathbb{R}) \times \mathbb{Q} \to \mathbb{R}$ 在 $(0, 0)$ 处的连续性，其中 $0 \in C_{co}(\mathbb{Q}, \mathbb{R})$ 为恒为零函数。
  - 取 $W = (-1, 1) \subset \mathbb{R}$，其为 $ev(0, 0) = 0$ 的开邻域。
  - 若 $ev$ 连续，则存在 $0$ 在 $C_{co}(\mathbb{Q}, \mathbb{R})$ 中的基开邻域 $U$ 和 $0$ 在 $\mathbb{Q}$ 中的开邻域 $V$，使得：
    $$U \times V \subset ev^{-1}(W)$$
    紧开拓扑的基开邻域形式为：
    $$U = [K, (-\epsilon, \epsilon)] = \left\{f \in C(\mathbb{Q}, \mathbb{R}) : \sup_{k \in K} |f(k)| < \epsilon\right\}$$
    其中 $K \subset \mathbb{Q}$ 为紧子集，$\epsilon > 0$。
  - 易知 $\mathbb{Q}$ 中任意紧子集 $K$ 均为 $\mathbb{R}$ 中的紧集。在 $\mathbb{R}$ 中，$K$ 是无内点的疏朗集，因此 $K$ 在度量空间 $\mathbb{Q}$ 中亦无内点。
  - 开邻域 $V$ 在 $\mathbb{Q}$ 中含有某个区间 $(-r, r) \cap \mathbb{Q}$（$r > 0$）。
  - 因 $K$ 无内点，$V \setminus K \neq \emptyset$。取点 $q \in V \setminus K$。
  - 因为 $K$ 是 $\mathbb{Q}$ 的闭子集且 $q \notin K$，距离 $\delta = \mathrm{dist}(q, K) > 0$。
  - 在 $\mathbb{Q}$ 上构造连续函数：
    $$f(x) = 2 \max\left(0, 1 - \frac{|x - q|}{\delta}\right)$$
    由于 $|k - q| \ge \delta$ 对所有 $k \in K$ 成立，故 $f|_K \equiv 0$。因此 $\sup_{k \in K} |f(k)| = 0 < \epsilon$，即 $f \in U$。
  - 但 $q \in V$，其求值为 $ev(f, q) = f(q) = 2 \notin (-1, 1) = W$。
  - 这与 $U \times V \subset ev^{-1}(W)$ 矛盾。
  因此求值映射在 $(0, 0)$ 处不连续。 $\blacksquare$

---

### 2. 第一可数性是否足以保证 $kX = X$

- **结论**：**是（第一可数性足以保证 $kX = X$）**。
- **论证**：
  恒有 $\tau_X \subset \tau_{kX}$。需证明对第一可数 Hausdorff 空间 $X$，任意 $k$-闭集 $A$ 必为原拓扑闭集。
  1. 设 $A \subset X$ 是 $k$-闭集。反设 $A$ 在原拓扑中不闭，则存在 $x_0 \in \overline{A} \setminus A$。
  2. 因为 $X$ 第一可数，$x_0$ 拥有可数且递降的开邻域基 $V_1 \supset V_2 \supset V_3 \supset \cdots$。
  3. 对每个 $n \ge 1$，因 $x_0 \in \overline{A}$，可选取序列点 $x_n \in A \cap V_n$。
  4. 序列 $(x_n)_{n=1}^\infty$ 在 $X$ 中收敛于 $x_0$。
  5. 集合 $K = \{x_n : n \ge 1\} \cup \{x_0\}$ 是 $X$ 中的紧子集（任意包含 $x_0$ 的开集必包含除有限个项外的所有 $x_n$）。因 $X$ 是 Hausdorff 空间，$K$ 为紧 Hausdorff 子空间。
  6. 根据 $A$ 为 $k$-闭集的定义，原像限制 $A \cap K$ 在子空间 $K$ 中必为闭集。
  7. 然而，点列 $x_n \in A \cap K$ 收敛于 $x_0$。由 $K$ 中闭集的极限封闭性，必有 $x_0 \in A \cap K \subset A$。
  8. 这与 $x_0 \notin A$ 产生直接矛盾。
  故 $A$ 是原拓扑闭集，$\tau_{kX} = \tau_X$，即 $kX = X$。第一可数空间必为紧生成空间。 $\blacksquare$

---

## S5　空间实现的识别

- **结论**：**否（$f$ 不必为原拓扑的同胚）**。

### 1. 普遍反例机制论证

设 $Z$ 是任意非紧生成的 Hausdorff 空间（即 $\tau_Z \subsetneq \tau_{kZ}$）。
令 $X = kZ$，$Y = Z$，且令 $f = \mathrm{id}_Z: kZ \to Z$。
- **连续性**：因 $\tau_Z \subset \tau_{kZ}$，恒等映射 $f: kZ \to Z$ 是连续双射。
- **$h_f$ 是自然同构**：
  对任意 $S \in \mathrm{Prof}_U$，分量映射为：
  $$h_f(S): C(S, kZ) \longrightarrow C(S, Z), \quad \phi \longmapsto f \circ \phi = \phi$$
  对任意连续映射 $\phi \in C(S, Z)$，因 $S$ 是紧 Hausdorff 空间，由 $k$ 拓扑的定义，对 $kZ$ 中的任意开集 $O$，$\phi^{-1}(O)$ 在 $S$ 中开，故 $\phi$ 作为映射 $S \to kZ$ 自动连续。
  因此 $C(S, kZ) = C(S, Z)$ 作为集合完全一致，$h_f(S)$ 对所有 $S$ 均为恒等双射，且与预复合显然自然相容。故 $h_f: h_X \Rightarrow h_Y$ 是自然同构。
- **非原拓扑同胚**：
  $f$ 互逆的原映射为其自身底集恒等映射。由于假设 $\tau_{kZ} \neq \tau_Z$，$f^{-1}: Z \to kZ$ 不是连续映射。故 $f$ 绝非原拓扑意义下的同胚。

### 2. 具体的非紧生成 Hausdorff 空间构造与核验

取自由超滤子 $\mathcal{U}$ 于 $\mathbb{N}$ 上，构造拓扑空间 $Z = \mathbb{N} \cup \{p\}$：
- $\mathbb{N}$ 中的每个单点为开集。
- 点 $p$ 的开邻域形式为 $U \cup \{p\}$，其中 $U \in \mathcal{U}$。
- **Hausdorff 性**：$\mathbb{N}$ 中点彼此分离；对任意 $n \in \mathbb{N}$，$\{n\}$ 与 $(\mathbb{N} \setminus \{n\}) \cup \{p\}$ 均为开集（因非平凡超滤子不含单点集，$\mathbb{N} \setminus \{n\} \in \mathcal{U}$），相互不交。
- **紧子集特征**：$Z$ 中的任意紧子集 $K$ 必为有限集。
  - 若 $p \notin K$，则 $K \subset \mathbb{N}$ 为离散子集，紧必有限。
  - 若 $p \in K$，反设 $K \cap \mathbb{N}$ 为无限集。将无限集 $K \cap \mathbb{N}$ 分拆为两个不交的无限子集 $A_1 \sqcup A_2$。
    由超滤子性质，恰有一个集合不属于 $\mathcal{U}$，不妨设 $A_1 \notin \mathcal{U}$，则 $\mathbb{N} \setminus A_1 \in \mathcal{U}$。
    开集 $W = (\mathbb{N} \setminus A_1) \cup \{p\}$ 是包含 $p$ 的开邻域，但 $W \cap A_1 = \emptyset$。
    开覆盖 $\{W\} \cup \{\{n\} : n \in A_1\}$ 覆盖 $K$。任何有限子族仅能包含 $W$ 和有限个单点，无法覆盖无限集 $A_1$。矛盾。故 $K$ 必为有限集。
- **$k$-化退化为离散拓扑**：
  因 $Z$ 中所有紧集均有限，对任意子集 $A \subset Z$ 及紧集 $K$，$A \cap K$ 为有限集，因而在 $K$ 中必定闭。
  故 $Z$ 的每个子集都是 $k$-闭集，即 $kZ$ 是离散拓扑空间。
- **核验结论**：
  单点集 $\{p\}$ 在 $Z$ 中不是开集（$\emptyset \notin \mathcal{U}$），故 $Z$ 不是离散空间。
  因此 $\tau_Z \subsetneq \tau_{kZ} = \mathcal{P}(Z)$。
  取 $X = kZ$（离散），$Y = Z$（超滤空间），$f = \mathrm{id}$ 满足连续且 $h_f$ 是自然同构，但 $f$ 不是同胚。 $\blacksquare$

---

## S6　复合与可识别范围

### 1. 连续复合与结合律、单位律

在 S3 构造的紧生成实现 $M(X,Y) = k(C_{co}(kX, kY))$ 下：

**构造连续复合映射**：
1. 范畴 $\mathbf{CGHaus}$ 的积对象为 $A \times_k B = k(A \times B)$。
2. 考察 S3 中构造的连续求值映射：
   $$ev_{X,Y}: M(X,Y) \times_k kX \longrightarrow kY, \quad ev_{Y,Z}: M(Y,Z) \times_k kY \longrightarrow kZ$$
3. 在 $\mathbf{CGHaus}$ 中构造复合求值：
   $$(M(Y,Z) \times_k M(X,Y)) \times_k kX \xrightarrow{\cong} M(Y,Z) \times_k (M(X,Y) \times_k kX) \xrightarrow{\mathrm{id} \times_k ev_{X,Y}} M(Y,Z) \times_k kY \xrightarrow{ev_{Y,Z}} kZ$$
   此复合映射连续，且在底集点态上将 $((g, f), x)$ 映射到 $g(f(x))$。
4. 由 $\mathbf{CGHaus}$ 的 Cartesian 闭性伴随：
   $$\mathbf{CGHaus}((M(Y,Z) \times_k M(X,Y)) \times_k kX, kZ) \cong \mathbf{CGHaus}(M(Y,Z) \times_k M(X,Y), M(X,Z))$$
   对应伴随态射即为连续映射：
   $$\circ: M(Y,Z) \times_k M(X,Y) \longrightarrow M(X,Z)$$
   底集求值正是通常的函数映射复合 $\circ(g, f) = g \circ f$。

**结合律与单位律证明**：
- **结合律**：
  对任意 $h \in M(Z, W)$、$g \in M(Y, Z)$、$f \in M(X, Y)$，
  $$((h \circ g) \circ f)(x) = h(g(f(x))) = (h \circ (g \circ f))(x)$$
  两连续映射 $\circ \circ (\circ \times_k \mathrm{id})$ 与 $\circ \circ (\mathrm{id} \times_k \circ)$ 在底集点态求值完全一致。由于 $\mathbf{CGHaus}$ 中态射由底集函数唯一决定，两连续映射严格相等：
  $$\circ \circ (\circ \times_k \mathrm{id}) = \circ \circ (\mathrm{id} \times_k \circ)$$
- **单位律**：
  对每个空间 $X$，恒等映射 $\mathrm{id}_{kX} \in C(kX, kX) = M(X,X)$ 确定整体点态射 $j_X: * \to M(X, X)$。
  由函数复合性质，对任意 $f \in M(X,Y)$ 有 $\mathrm{id}_{kY} \circ f = f$ 以及 $f \circ \mathrm{id}_{kX} = f$。
  从而如下典范图表交换：
  $$M(X,Y) \cong * \times_k M(X,Y) \xrightarrow{j_Y \times_k \mathrm{id}} M(Y,Y) \times_k M(X,Y) \xrightarrow{\circ} M(X,Y)$$
  $$M(X,Y) \cong M(X,Y) \times_k * \xrightarrow{\mathrm{id} \times_k j_X} M(X,Y) \times_k M(X,X) \xrightarrow{\circ} M(X,Y)$$
  两式复合均为 $\mathrm{id}_{M(X,Y)}$。结合律与单位律成立。

---

### 2. 连续映射 $f: X \to Y$ 满足 $h_f$ 同构的充要条件

- **充要条件**：
  $$k(f): kX \longrightarrow kY \quad \text{是拓扑同胚}$$
  （即 $f: X \to Y$ 为双射，且将 $kX$ 上的拓扑同胚映射到 $kY$ 上的拓扑）。

**论证**：
- **充分性 ($\Leftarrow$)**：
  若 $k(f): kX \to kY$ 是同胚，设其连续逆映射为 $g: kY \to kX$。
  由 S2 的结论，连续映射 $g$ 唯一诱导自然变换 $\beta \in \mathrm{Nat}(h_Y, h_X)$，且在同构 $\mathrm{Nat}(h_A, h_B) \cong C(kA, kB)$ 下自然变换的复合对应于连续映射的复合。
  因 $g \circ k(f) = \mathrm{id}_{kX}$ 且 $k(f) \circ g = \mathrm{id}_{kY}$，对应自然变换满足 $\beta \circ h_f = \mathrm{id}_{h_X}$ 和 $h_f \circ \beta = \mathrm{id}_{h_Y}$。故 $h_f$ 是自然同构。
- **必要性 ($\Rightarrow$)**：
  若 $h_f: h_X \to h_Y$ 是自然同构，存在可逆自然变换 $\alpha: h_Y \to h_X$ 使得 $\alpha \circ h_f = \mathrm{id}_{h_X}$ 且 $h_f \circ \alpha = \mathrm{id}_{h_Y}$。
  根据 S2，自然变换范畴与 $k$-空间连续映射等价，$\alpha$ 对应唯一连续映射 $g \in C(kY, kX)$，而 $h_f$ 对应 $k(f) \in C(kX, kY)$。
  两变换互逆等价于 $g \circ k(f) = \mathrm{id}_{kX}$ 且 $k(f) \circ g = \mathrm{id}_{kY}$。
  这表明 $k(f)$ 为连续双射且具有连续逆映射 $g$。故 $k(f): kX \to kY$ 必为同胚。

---

### 3. $X, Y$ 第一可数时的同胚升级判断

- **结论**：**能（必能升级为原拓扑的普通同胚）**。
- **证明**：
  设 $X, Y$ 均为第一可数 Hausdorff 空间，且连续映射 $f: X \to Y$ 满足 $h_f$ 是自然同构。
  1. 由上述充要条件，$k(f): kX \to kY$ 是拓扑同胚。
  2. 根据 S4 第 2 小节证明的核心定理：**第一可数性足以保证空间紧生成**。
     因为 $X$ 和 $Y$ 均为第一可数空间，直接得出：
     $$kX = X \quad \text{且} \quad kY = Y$$
  3. 因此，同胚映射 $k(f): kX \to kY$ 在原拓扑下即为：
     $$f: X \longrightarrow Y$$
  因此，$f$ 自身就是原拓扑意义下的空间同胚。第一可数性保证可升级为普通同胚。 $\blacksquare$
