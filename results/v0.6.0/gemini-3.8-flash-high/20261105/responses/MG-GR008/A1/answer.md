# 塔记录的表示、有限层延拓与自然变换

---

## S1　实际记录与张量

### 1. $F_P$ 的良定义性与函子性

设自由阿贝尔群逆塔为
$$P_0 \xleftarrow{\rho_0} P_1 \xleftarrow{\rho_1} P_2 \xleftarrow{\rho_2} \cdots$$
对 $m \ge n$，过渡态射 $\rho_{n,m} : P_m \to P_n$ 规定为：$\rho_{n,n} = \mathrm{id}_{P_n}$；当 $m > n$ 时，$\rho_{n,m} = \rho_n \circ \rho_{n+1} \circ \cdots \circ \rho_{m-1}$。显然，对任意 $k \ge m \ge n$，满足传递律 $\rho_{n,m} \circ \rho_{m,k} = \rho_{n,k}$。

对任意 $A \in \mathbf{Ab}_{\mathcal{U}}$，阿贝尔群同态集 $\mathrm{Hom}_{\mathbb{Z}}(P_n, A)$ 在逐点加法下构成阿贝尔群。因 $P_n$ 为有限秩自由群，$\mathrm{Hom}_{\mathbb{Z}}(P_n, A) \cong A^{\mathrm{rank}(P_n)} \in \mathcal{U}$。对 $m \ge n$，拉回映射
$$\rho_{n,m}^* : \mathrm{Hom}_{\mathbb{Z}}(P_n, A) \longrightarrow \mathrm{Hom}_{\mathbb{Z}}(P_m, A), \quad u \longmapsto u \circ \rho_{n,m}$$
是群同态，且满足 $\rho_{n,n}^* = \mathrm{id}$ 以及 $\rho_{m,k}^* \circ \rho_{n,m}^* = \rho_{n,k}^*$。故 $\{\mathrm{Hom}_{\mathbb{Z}}(P_n, A), \rho_{n,m}^*\}_{n \in \mathbb{N}}$ 构成由偏序集 $(\mathbb{N}, \le)$ 索引的滤向系统。

#### (1) 等价关系的良定义性
令 $X(A) = \coprod_{n \in \mathbb{N}} \mathrm{Hom}_{\mathbb{Z}}(P_n, A)$。定义其上的二元关系：$(n, u) \sim (m, v)$ 当且仅当存在 $r \ge n, m$ 使得 $u \circ \rho_{n,r} = v \circ \rho_{m,r}$。
- **自反性**：取 $r = n$，显然 $u \circ \rho_{n,n} = u = u \circ \rho_{n,n}$，故 $(n, u) \sim (n, u)$。
- **对称性**：若 $u \circ \rho_{n,r} = v \circ \rho_{m,r}$，则 $v \circ \rho_{m,r} = u \circ \rho_{n,r}$，故 $(m, v) \sim (n, u)$。
- **传递性**：若 $(n, u) \sim (m, v)$（在某 $r_1 \ge n, m$ 处吻合）且 $(m, v) \sim (k, w)$（在某 $r_2 \ge m, k$ 处吻合），取 $r = \max(r_1, r_2)$。由传递律，
  $$u \circ \rho_{n,r} = (u \circ \rho_{n,r_1}) \circ \rho_{r_1, r} = (v \circ \rho_{m,r_1}) \circ \rho_{r_1, r} = v \circ \rho_{m,r},$$
  同理 $w \circ \rho_{k,r} = v \circ \rho_{m,r}$，故 $u \circ \rho_{n,r} = w \circ \rho_{k,r}$，即 $(n, u) \sim (k, w)$。
因此 $\sim$ 为等价关系，商集 $F_P(A) = X(A)/{\sim}$ 良定义。因 $\mathbb{N} \in \mathcal{U}$ 且各 $\mathrm{Hom}(P_n, A) \in \mathcal{U}$，商集 $F_P(A) \in \mathcal{U}$。

#### (2) 群结构的良定义性
对 $[(n, u)], [(m, v)] \in F_P(A)$，取任意 $r \ge n, m$，规定
$$[(n, u)] + [(m, v)] := [(r, u \circ \rho_{n,r} + v \circ \rho_{m,r})].$$
- **不依赖于公共层 $r$ 的选取**：若另选 $r' \ge n, m$，取 $R \ge r, r'$，则
  $$(u \circ \rho_{n,r} + v \circ \rho_{m,r}) \circ \rho_{r, R} = u \circ \rho_{n,R} + v \circ \rho_{m,R} = (u \circ \rho_{n,r'} + v \circ \rho_{m,r'}) \circ \rho_{r', R},$$
  故在 $F_P(A)$ 中属于同一等价类。
- **不依赖于代表元的选取**：若 $(n, u) \sim (n', u')$ 且 $(m, v) \sim (m', v')$，存在充分大的层使两对代表元各自吻合，由同态加法分配律，其和在更深公共层上亦吻合。
- 零元为 $[(0, 0)]$，加法逆元为 $-[(n, u)] = [(n, -u)]$。阿贝尔群公理直接由各 $\mathrm{Hom}(P_r, A)$ 的加法公理导出。

#### (3) 函子性的验证
对 $\mathbf{Ab}_{\mathcal{U}}$ 中的态射 $f : A \to B$，定义
$$F_P(f) : F_P(A) \longrightarrow F_P(B), \quad [(n, u)] \longmapsto [(n, f \circ u)].$$
- 若 $(n, u) \sim (m, v)$，则存在 $r \ge n, m$ 使 $u \circ \rho_{n,r} = v \circ \rho_{m,r}$，两端左复合 $f$ 得 $(f \circ u) \circ \rho_{n,r} = (f \circ v) \circ \rho_{m,r}$，故 $F_P(f)$ 不依赖代表元选取。
- $F_P(f)$ 保持加法：$f \circ (u \circ \rho_{n,r} + v \circ \rho_{m,r}) = f \circ u \circ \rho_{n,r} + f \circ v \circ \rho_{m,r}$。
- 恒等态射与复合：显然 $F_P(\mathrm{id}_A)([(n, u)]) = [(n, \mathrm{id}_A \circ u)] = [(n, u)]$；对 $g : B \to C$，有 $F_P(g \circ f)([(n, u)]) = [(n, g \circ f \circ u)] = F_P(g)(F_P(f)([(n, u)]))$。
综上，$F_P : \mathbf{Ab}_{\mathcal{U}} \to \mathbf{Ab}_{\mathcal{U}}$ 为良定义的加法函子。

---

### 2. 自然同构 $F_P(A) \cong M_P \otimes_{\mathbb{Z}} A$ 的构造

记 $Q_n = \mathrm{Hom}_{\mathbb{Z}}(P_n, \mathbb{Z})$，过渡态射为 $\rho_n^* : Q_n \to Q_{n+1}$，则 $M_P = \mathrm{colim}_n Q_n$。

因 $P_n$ 为有限秩自由阿贝尔群，存在典范同构（评估映射的张量对偶）：
$$\tau_n : Q_n \otimes_{\mathbb{Z}} A \xrightarrow{\ \sim\ } \mathrm{Hom}_{\mathbb{Z}}(P_n, A), \quad \phi \otimes a \longmapsto (x \mapsto \phi(x)a).$$
其逆映射为：选取 $P_n$ 的一组基 $\{e_i\}_{i=1}^{k_n}$ 及其对偶基 $\{e_i^*\}_{i=1}^{k_n} \subset Q_n$，将 $u \in \mathrm{Hom}(P_n, A)$ 映至 $\sum_{i=1}^{k_n} e_i^* \otimes u(e_i)$（与基的选取无关）。

考察如下方块图：
$$\begin{matrix}
Q_n \otimes A & \xrightarrow{\ \ \tau_n\ \ } & \mathrm{Hom}(P_n, A) \\
\rho_n^* \otimes \mathrm{id}_A \Bigg\downarrow & & \Bigg\downarrow \rho_n^* \\
Q_{n+1} \otimes A & \xrightarrow{\ \ \tau_{n+1}\ \ } & \mathrm{Hom}(P_{n+1}, A)
\end{matrix}$$
对任意纯张量 $\phi \otimes a \in Q_n \otimes A$ 与 $y \in P_{n+1}$：
- 沿顶边与右边：$(\rho_n^*(\tau_n(\phi \otimes a)))(y) = (\tau_n(\phi \otimes a))(\rho_n(y)) = \phi(\rho_n(y))a$；
- 沿左边与底边：$\tau_{n+1}((\rho_n^*(\phi)) \otimes a)(y) = (\phi \circ \rho_n)(y)a = \phi(\rho_n(y))a$。
两路径严格相等，故该方块图对所有 $n$ 交换。

因张量函子 $- \otimes_{\mathbb{Z}} A$ 为左伴随，保持所有余极限，特别地保持滤向余极限：
$$\mathrm{colim}_{n \in \mathbb{N}} (Q_n \otimes_{\mathbb{Z}} A) \cong \left(\mathrm{colim}_{n \in \mathbb{N}} Q_n\right) \otimes_{\mathbb{Z}} A = M_P \otimes_{\mathbb{Z}} A.$$
因此，由同构族 $\{\tau_n\}_{n \in \mathbb{N}}$ 在滤向余极限下诱导出群同构：
$$\Theta_A : M_P \otimes_{\mathbb{Z}} A \xrightarrow{\ \sim\ } F_P(A), \quad [(n, \phi)] \otimes a \longmapsto [(n, x \mapsto \phi(x)a)].$$
其逆同构为：
$$\Omega_A : F_P(A) \xrightarrow{\ \sim\ } M_P \otimes_{\mathbb{Z}} A, \quad [(n, u)] \longmapsto \sum_{i=1}^{k_n} [(n, e_i^*)] \otimes u(e_i).$$

对任意态射 $f : A \to B$，显然有
$$\Theta_B \circ (\mathrm{id}_{M_P} \otimes f)([(n, \phi)] \otimes a) = [(n, x \mapsto \phi(x)f(a))] = F_P(f)(\Theta_A([(n, \phi)] \otimes a)),$$
故 $\Theta : M_P \otimes (-) \implies F_P(-)$ 是自然同构。

---

### 3. $M_P$ 的可数性与无挠性证明

#### (1) 可数性
对每个 $n \in \mathbb{N}$，自由阿贝尔群 $P_n$ 秩有限，设其秩为 $k_n \in \mathbb{N}$，则 $Q_n = \mathrm{Hom}(P_n, \mathbb{Z}) \cong \mathbb{Z}^{k_n}$ 为可数集。
记规范投射为 $q_n : Q_n \to M_P$。则 $M_P = \bigcup_{n \in \mathbb{N}} q_n(Q_n)$ 为可数个可数集合的像之并，因此 $M_P$ 至多可数（在 ZFC 下为可数集合）。

#### (2) 无挠性（不预设 $Q_n \to M_P$ 单射）
任取 $x \in M_P$ 及非零整数 $k \in \mathbb{Z} \setminus \{0\}$，设 $k x = 0$。我们需要证明 $x = 0$。
由滤向余极限的定义，存在某个有限层 $n \in \mathbb{N}$ 及 $\phi \in Q_n$，使得 $x = [(n, \phi)] = q_n(\phi)$。
条件 $k x = 0$ 意味着在 $M_P$ 中 $[(n, k\phi)] = 0$。
依据滤向系统的余极限定义，这等价于：存在某个有限下标 $r \ge n$，使得在有限层阿贝尔群 $Q_r$ 中，有
$$\rho_{n,r}^*(k\phi) = 0 \in Q_r.$$
因为 $\rho_{n,r}^* : Q_n \to Q_r$ 是群同态，上式即为
$$k \cdot (\rho_{n,r}^*(\phi)) = 0 \quad (\text{在 } Q_r \text{ 中}).$$
注意到目标群 $Q_r = \mathrm{Hom}_{\mathbb{Z}}(P_r, \mathbb{Z})$。因 $P_r$ 是自由阿贝尔群，$Q_r \cong \mathbb{Z}^{k_r}$ 亦为自由阿贝尔群，特别地，$Q_r$ 是**无挠群**。
在无挠群 $Q_r$ 中，$k \ne 0$ 且 $k \cdot (\rho_{n,r}^*(\phi)) = 0$ 严格蕴涵：
$$\rho_{n,r}^*(\phi) = 0 \in Q_r.$$
因此，根据滤向余极限的同值关系，
$$x = q_n(\phi) = q_r(\rho_{n,r}^*(\phi)) = q_r(0) = 0 \in M_P.$$
此论证仅依赖于各有限阶段群 $Q_r$ 本身的无挠性与等价关系在有限步 $r$ 处的截断，完全未假定过渡态射 $\rho_{n,r}^*$ 或典范映射 $q_n : Q_n \to M_P$ 是单射。故 $M_P$ 必为无挠阿贝尔群。

---

## S2　有限图表和变换

### 1. $F_P$ 保持有限极限的证明

可由以下两途径分别独立确立：

- **途径一（模论平坦性）**：
  由 S1，存在自然同构 $F_P(-) \cong M_P \otimes_{\mathbb{Z}} -$。
  因主理想整环 $\mathbb{Z}$ 上的模是平坦模当且仅当其无挠，由 S1 知 $M_P$ 无挠，故 $M_P$ 为平坦 $\mathbb{Z}$-模。平坦模的张量函子 $M_P \otimes_{\mathbb{Z}} -$ 是阿贝尔范畴 $\mathbf{Ab}_{\mathcal{U}}$ 上的正合函子。在阿贝尔范畴中，加法函子正合当且仅当其保持所有有限极限（与有限余极限）。故 $F_P$ 保持有限极限。

- **途径二（滤向余极限与有限极限的交换性）**：
  对任意 $n \in \mathbb{N}$，可表函子 $\mathrm{Hom}_{\mathbb{Z}}(P_n, -)$ 保持一切极限，特别保持有限极限。
  在阿贝尔范畴 $\mathbf{Ab}_{\mathcal{U}}$（满足 AB5 公理）中，滤向余极限函子 $\mathrm{colim}_n$ 与有限极限（即有限积和核/等化子）可交换。故有限极限与滤向余极限的复合
  $$F_P(\lim_J A_j) = \mathrm{colim}_n \mathrm{Hom}(P_n, \lim_J A_j) \cong \mathrm{colim}_n \lim_J \mathrm{Hom}(P_n, A_j) \cong \lim_J \mathrm{colim}_n \mathrm{Hom}(P_n, A_j) = \lim_J F_P(A_j)$$
  成立。

---

### 2. 自然变换 $\mathrm{Nat}(F_P, F_{P'})$ 的完全描述

设两塔分别为 $P = (P_n, \rho_n)$ 与 $P' = (P'_m, \rho'_m)$。

#### (1) 模同态描述
依 Eilenberg-Watts 定理，张量函子间的自然变换完全由其在 $\mathbb{Z}$ 上的分量决定：
$$\Phi : \mathrm{Nat}(M_P \otimes -, M_{P'} \otimes -) \xrightarrow{\ \sim\ } \mathrm{Hom}_{\mathbb{Z}}(M_P, M_{P'}), \quad \eta \longmapsto \eta_{\mathbb{Z}}.$$
其逆将群同态 $\theta : M_P \to M_{P'}$ 映为自然变换 $\theta \otimes \mathrm{id}_A : M_P \otimes A \to M_{P'} \otimes A$。
结合 S1 的自然同构 $F_P \cong M_P \otimes -$，有典范群同构：
$$\mathrm{Nat}(F_P, F_{P'}) \cong \mathrm{Hom}_{\mathbb{Z}}(M_P, M_{P'}).$$

#### (2) 塔记录 / 逆系统 (pro-morphism) 描述
由余极限与极限的伴随性，以及 $Q_n$ 的有限生成自由性：
$$\begin{aligned}
\mathrm{Hom}_{\mathbb{Z}}(M_P, M_{P'}) &= \mathrm{Hom}_{\mathbb{Z}}\left(\mathrm{colim}_{n} Q_n, M_{P'}\right) \cong \lim_{n \in \mathbb{N}} \mathrm{Hom}_{\mathbb{Z}}(Q_n, M_{P'}) \\
&\cong \lim_{n \in \mathbb{N}} \left(Q_n^* \otimes_{\mathbb{Z}} M_{P'}\right) \cong \lim_{n \in \mathbb{N}} \left(P_n \otimes_{\mathbb{Z}} M_{P'}\right) \\
&\cong \lim_{n \in \mathbb{N}} F_{P'}(P_n) = \lim_{n \in \mathbb{N}} \left(\mathrm{colim}_{m \in \mathbb{N}} \mathrm{Hom}_{\mathbb{Z}}(P'_m, P_n)\right) = \mathrm{Hom}_{\mathbf{pro}\text{-}\mathbf{Ab}}(P', P).
\end{aligned}$$
因此，每个自然变换 $\eta \in \mathrm{Nat}(F_P, F_{P'})$ 等价对应一族记录元 $([f_n])_{n \in \mathbb{N}}$，其中对每个 $n$，$[f_n] \in F_{P'}(P_n)$ 由某有限层态射 $f_n : P'_{m_n} \to P_n$ 代表，且满足相容性条件：
$$F_{P'}(\rho_n)([f_{n+1}]) = [f_n] \in F_{P'}(P_n), \quad \text{即 } \rho_n \circ f_{n+1} \sim f_n.$$
在该描述下，对任意记录 $[(n, u)] \in F_P(A)$（其中 $u \in \mathrm{Hom}(P_n, A)$），自然变换的作用公式为：
$$\eta_A([(n, u)]) = [(m_n, u \circ f_n)] \in F_{P'}(A).$$

---

### 3. 恒等与复合公式

#### (1) 同态视角下的公式
- **恒等**：$\mathrm{id}_{F_P}$ 对应 $\mathrm{id}_{M_P} \in \mathrm{Hom}_{\mathbb{Z}}(M_P, M_P)$。
- **复合**：设 $\eta \in \mathrm{Nat}(F_P, F_{P'})$ 对应 $\theta \in \mathrm{Hom}(M_P, M_{P'})$，$\mu \in \mathrm{Nat}(F_{P'}, F_{P''})$ 对应 $\psi \in \mathrm{Hom}(M_{P'}, M_{P''})$，则复合自然变换 $\mu \circ \eta \in \mathrm{Nat}(F_P, F_{P''})$ 对应群同态的通常复合：
  $$\psi \circ \theta \in \mathrm{Hom}_{\mathbb{Z}}(M_P, M_{P''}).$$

#### (2) 记录 / 态射族视角下的公式
- **恒等公式**：
  $\mathrm{id}_{F_P}$ 对应的相容记录族为对每个 $n$ 取 $[f_n] = [(n, \mathrm{id}_{P_n})] \in F_P(P_n)$。
  代入作用公式即：
  $$(\mathrm{id}_{F_P})_A([(n, u)]) = [(n, u \circ \mathrm{id}_{P_n})] = [(n, u)].$$
- **复合公式**：
  设 $\eta$ 由层映射及态射族 $f_n : P'_{m_n} \to P_n$ 确定，$\mu$ 由 $g_m : P''_{k_m} \to P'_m$ 确定。对任意 $[(n, u)] \in F_P(A)$：
  $$\eta_A([(n, u)]) = [(m_n, u \circ f_n)] \in F_{P'}(A),$$
  $$(\mu \circ \eta)_A([(n, u)]) = \mu_A([(m_n, u \circ f_n)]) = [(k_{m_n}, (u \circ f_n) \circ g_{m_n})] = [(k_{m_n}, u \circ (f_n \circ g_{m_n}))].$$
  即复合自然变换由逐层相继回拉态射 $f_n \circ g_{m_n} : P''_{k_{m_n}} \to P_n$ 代表。

---

## S3　完整表示分类

### 1. 塔确定的非循环充要判据

我们寻找由逆塔自身直接表述（非循环、不依赖“$F_P$ 可表”或“$M_P$ 有限生成”等外部同义反复）的表示性充要条件。

**定理（充要判据）**：
函子 $F_P$ 由某个普通对象 $P \in \mathbf{Ab}_{\mathcal{U}}$ 所表示（即存在自然同构 $F_P(-) \cong \mathrm{Hom}_{\mathbb{Z}}(P, -)$）当且仅当逆塔 $(P_n, \rho_n)_{n \in \mathbb{N}}$ 满足如下条件：
> **判据 $\mathcal{C}$**：
> 存在整数 $n_0 \in \mathbb{N}$，使得：
> 1. （像的最终稳定）对每个 $n \ge n_0$，降链子群序列 $\{\rho_{n,m}(P_m)\}_{m \ge n}$ 在 $P_n$ 中最终稳定：即存在 $m(n) \ge n$，使得对一切 $m \ge m(n)$，恒有
>    $$\rho_{n,m}(P_m) = I_n \le P_n;$$
> 2. （稳定像间同构）对每个 $n \ge n_0$，过渡态射在稳定像上的限制
>    $$\rho_n|_{I_{n+1}} : I_{n+1} \longrightarrow I_n$$
>    是阿贝尔群的同构。

#### 必要性证明
设存在 $P \in \mathbf{Ab}_{\mathcal{U}}$ 使得 $F_P(-) \cong \mathrm{Hom}_{\mathbb{Z}}(P, -)$。
1. **$P$ 必须是有限秩自由阿贝尔群**：
   因 $F_P(-) \cong M_P \otimes -$ 保持任意直和（余积），$\mathrm{Hom}(P, -)$ 保持任意直和，从而 $P$ 必为有限生成阿贝尔群。又因 $M_P$ 无挠使 $F_P$ 正合，$\mathrm{Hom}(P, -)$ 正合，故 $P$ 为有限生成投射 $\mathbb{Z}$-模，即有限秩自由阿贝尔群。
2. **稳定像的存在与同构**：
   由 Yoneda 引理，自然同构 $F_P(-) \cong \mathrm{Hom}(P, -)$ 对应一个通用元 $\xi \in F_P(P)$（对应 $\mathrm{id}_P$），该元素由某有限层态射代表：存在 $n_0 \in \mathbb{N}$ 与 $\pi : P_{n_0} \to P$，使得 $\xi = [(n_0, \pi)]$。
   同时，对偶族由一族态射 $\iota_n : P \to P_n$（对应投射 $\mathrm{Hom}(P_n, -) \to F_P(-) \cong \mathrm{Hom}(P, -)$）组成，满足 $\rho_{n,m} \circ \iota_m = \iota_n$。
   同构性要求 $\pi \circ \iota_{n_0} = \mathrm{id}_P$。故 $\iota_{n_0}$ 为单射且 $\pi$ 为满射。
   进一步，在 $F_P(P_{n_0})$ 中，$\mathrm{id}_{P_{n_0}}$ 与 $\iota_{n_0} \circ \pi$ 给出相同记录元，故存在 $m_0 \ge n_0$，使得
   $$\rho_{n_0, m_0} = \iota_{n_0} \circ \pi \circ \rho_{n_0, m_0} : P_{m_0} \longrightarrow P_{n_0}.$$
   记 $j = \pi \circ \rho_{n_0, m_0} : P_{m_0} \to P$。因 $j \circ \iota_{m_0} = \pi \circ \iota_{n_0} = \mathrm{id}_P$，$j$ 是满射，故 $j(P_{m_0}) = P$。
   由此，对一切 $m \ge m_0$：
   $$\rho_{n_0, m}(P_m) \subseteq \rho_{n_0, m_0}(P_{m_0}) = \iota_{n_0}(j(P_{m_0})) = \iota_{n_0}(P).$$
   反之，$\iota_{n_0}(P) = \rho_{n_0, m}(\iota_m(P)) \subseteq \rho_{n_0, m}(P_m)$。
   因此，对一切 $m \ge m_0$，$\rho_{n_0, m}(P_m) = \iota_{n_0}(P)$ 严格常值！
   同理，对任意 $n \ge n_0$，因 $\iota_n$ 分裂单，存在 $m(n)$ 使得当 $m \ge m(n)$ 时，$\rho_{n,m}(P_m) = \iota_n(P) =: I_n$ 恒成立。条件 1 得证。
   在稳定像上，$\rho_n(I_{n+1}) = \rho_n(\iota_{n+1}(P)) = \iota_n(P) = I_n$。因 $\iota_{n+1} : P \xrightarrow{\sim} I_{n+1}$ 与 $\iota_n : P \xrightarrow{\sim} I_n$ 均为同构，限制映射 $\rho_n|_{I_{n+1}} = \iota_n \circ \iota_{n+1}^{-1} : I_{n+1} \to I_n$ 必为同构。条件 2 得证。

#### 充分性证明
在 S5 中已完全给出构造性论证：在判据 $\mathcal{C}$ 下，通过构造有限层上的回缩态射，严格证明了 $F_P \cong \mathrm{Hom}(I_{n_0}, -)$。

---

### 2. 全部表示对象到同构的构造

由 Yoneda 引理，若函子可表，则表示对象在同构意义下唯一。
由充分性与必要性论证，表示对象完全由塔的稳定层构造确定：
对满足判据 $\mathcal{C}$ 的逆塔，取指标 $n_0$，定义
$$P_{\mathrm{repr}} := I_{n_0} = \bigcap_{m \ge n_0} \rho_{n_0,m}(P_m).$$
因为各 $I_n$ 之间由同构 $\rho_n|_{I_{n+1}}$ 相连，选取任意 $n \ge n_0$ 均有 $I_n \cong I_{n_0}$。
- 若 $I_{n_0} = 0$，则唯一的表示对象为平凡群 $0$；
- 若 $I_{n_0} \ne 0$，因 $I_{n_0}$ 为有限秩自由群 $P_{n_0}$ 的子群，它本身是自由阿贝尔群，设其秩为 $r = \mathrm{rank}(I_{n_0}) \le \mathrm{rank}(P_{n_0})$，则同构意义下的唯一表示对象即为
  $$P \cong \mathbb{Z}^r \cong I_{n_0}.$$

---

### 3. 保持可数小图表极限的塔的分类及其等价性

考虑小范畴 $\mathcal{J}$，其对象集 $\mathrm{Ob}(\mathcal{J})$ 与态射集 $\mathrm{Mor}(\mathcal{J})$ 均为可数集。

**定理（保持可数小图表极限的充要条件）**：
函子 $F_P$ 保持所有对象与箭头均可数的小图表极限，**当且仅当** $F_P$ 可表（即满足判据 $\mathcal{C}$）。

#### 证明
1. **可数极限的归约**：
   在阿贝尔范畴 $\mathbf{Ab}_{\mathcal{U}}$ 中，任意可数图表极限可由可数积 $\prod_{i \in \mathbb{N}} A_i$ 与核（有限极限）构造而成。
   由 S2 知，$F_P$ 恒保持有限极限（从而恒保持核）。因此，$F_P$ 保持所有可数小图表极限，等价于 $F_P$ 保持可数直积，特别地，保持 $\mathbb{Z}^{\mathbb{N}} = \prod_{i \in \mathbb{N}} \mathbb{Z}$ 的极限。
2. **充分性**：若 $F_P$ 可表，则 $F_P(-) \cong \mathrm{Hom}(P, -)$。作为余变可表函子，它保持范畴中的一切极限（包括可数图表极限与任意无限积）。
3. **必要性**：
   假设 $F_P$ 保持可数积 $\mathbb{Z}^{\mathbb{N}}$，即典范比较态射
   $$\kappa : M_P \otimes_{\mathbb{Z}} \mathbb{Z}^{\mathbb{N}} \longrightarrow \left(M_P \otimes_{\mathbb{Z}} \mathbb{Z}\right)^{\mathbb{N}} \cong M_P^{\mathbb{N}}$$
   是满射。
   对任意张量元 $t \in M_P \otimes \mathbb{Z}^{\mathbb{N}}$，由张量积定义，$t$ 必为有限个纯张量之和：
   $$t = \sum_{j=1}^K m_j \otimes v_j, \quad m_j \in M_P, \ v_j = (v_{j,i})_{i \in \mathbb{N}} \in \mathbb{Z}^{\mathbb{N}}.$$
   其在 $M_P^{\mathbb{N}}$ 中的像为序列 $(s_i)_{i \in \mathbb{N}}$，其中每项 $s_i = \sum_{j=1}^K v_{j,i} m_j$。
   由此可见：**对每一项 $i \in \mathbb{N}$，$s_i$ 恒落入由有限个元 $\{m_1, \dots, m_K\}$ 生成的子群 $H \le M_P$ 之中**。换言之，$\mathrm{im}(\kappa)$ 中的序列之所有坐标必被 $M_P$ 的某有限生成子群一致包含。
   由 S1 知 $M_P$ 是可数群，故可将其全体元素排成序列 $(x_i)_{i \in \mathbb{N}}$。
   若 $\kappa$ 为满射，则序列 $(x_i)_{i \in \mathbb{N}} \in M_P^{\mathbb{N}}$ 必落在 $\mathrm{im}(\kappa)$ 中，这意味着存在 $M_P$ 的某个有限生成子群 $H$，包含序列中的每一个 $x_i$。由于该序列遍历了 $M_P$ 的所有元素，必有
   $$M_P = H.$$
   因此，$M_P$ 必为有限生成阿贝尔群！
   结合 S1（$M_P$ 无挠），由有限生成阿贝尔群基本定理，$M_P$ 必为有限秩自由阿贝尔群：$M_P \cong \mathbb{Z}^r$。
   此时 $F_P(A) \cong M_P \otimes A \cong A^r \cong \mathrm{Hom}_{\mathbb{Z}}(\mathbb{Z}^r, A)$，故 $F_P$ 可表。

#### 两判据关系的确定
“函子 $F_P$ 可表”与“函子 $F_P$ 保持所有可数小图表极限”**完全等价**。

#### 与 S2 自然变换分类的一致性
在 S2 中，我们证明了 $\mathrm{Nat}(F_P, F_{P'}) \cong \mathrm{Hom}_{\mathbb{Z}}(M_P, M_{P'})$。
当 $F_P$ 与 $F_{P'}$ 可表时，设其表示对象分别为 $P \cong M_P^*$ 与 $P' \cong M_{P'}^*$（均为有限秩自由群）。
利用有限秩自由群的对偶反等价性，有
$$\mathrm{Hom}_{\mathbb{Z}}(M_P, M_{P'}) \cong \mathrm{Hom}_{\mathbb{Z}}((P')^*, P^*) \cong \mathrm{Hom}_{\mathbb{Z}}(P', P).$$
另一方面，直接由 Yoneda 引理，可表函子间的自然变换集为：
$$\mathrm{Nat}(\mathrm{Hom}(P, -), \mathrm{Hom}(P', -)) \cong \mathrm{Hom}_{\mathbb{Z}}(P', P).$$
两分类结果完全一致，方向严格相符。

---

## S4　秩一塔

设所有 $P_n = \mathbb{Z}$，过渡同态 $\rho_n : P_{n+1} \to P_n$ 为乘以整数 $a_n \in \mathbb{Z}$。

### 1. 秩恒为 1 是否保证 $F_P$ 可表的判断

- **结论：否**（秩恒为 1 不能保证 $F_P$ 可表）。
- **完整反例与验证**：
  取序列 $a_n = 2$（对所有 $n \ge 0$）。各 $P_n = \mathbb{Z}$ 的秩恒为 1。
  此时对偶群 $Q_n = \mathrm{Hom}(\mathbb{Z}, \mathbb{Z}) \cong \mathbb{Z}$，过渡态射 $\rho_n^* : Q_n \to Q_{n+1}$ 亦为乘 2 同态。
  其余极限群为二进有理数群：
  $$M_P = \mathrm{colim}(\mathbb{Z} \xrightarrow{\times 2} \mathbb{Z} \xrightarrow{\times 2} \mathbb{Z} \to \cdots) \cong \mathbb{Z}[1/2].$$
  若 $F_P$ 可表，则由 S3 知 $M_P$ 必须为有限生成自由阿贝尔群。
  但 $\mathbb{Z}[1/2]$ 不是有限生成的：任意有限子集 $\{m_1/2^{k_1}, \dots, m_s/2^{k_s}\}$ 生成的子群恒包含于 $2^{-K}\mathbb{Z}$（其中 $K = \max k_i$），无法包含分母更高的 $2^{-(K+1)}$。
  因此 $F_P$ 不可表。

---

### 2. 整数序列 $(a_n)_{n \in \mathbb{N}}$ 的表示性完整判据

对任意整数序列 $(a_n)_{n \in \mathbb{N}}$，过渡态射为乘积 $\rho_{n,m} = \prod_{k=n}^{m-1} a_k$。

**定理（秩一塔表示性完整判据）**：
由整数序列 $(a_n)_{n \in \mathbb{N}}$ 诱导的函子 $F_P$ 是可表函子，**当且仅当** $(a_n)$ 满足以下两互斥情形之一：
1. **零过渡频繁出现**：存在无穷多个 $n$ 使得 $a_n = 0$（即对任意 $n$，均存在 $m \ge n$ 使得 $\prod_{k=n}^m a_k = 0$）。此时 $M_P = 0$，表示对象为 $P \cong 0$；
2. **最终非零且最终为单模**：只有有限个 $n$ 满足 $a_n = 0$，且除去这些零之后，只有有限个 $n$ 满足 $|a_n| > 1$。换言之，存在截断下标 $N \in \mathbb{N}$，使得对一切 $n \ge N$，恒有
   $$a_n \in \{1, -1\}.$$
   此时 $M_P \cong \mathbb{Z}$，表示对象为 $P \cong \mathbb{Z}$。

#### 证明
- **情形 1 的充分必要性**：
  若存在无穷多个 $n$ 满足 $a_n = 0$，则对任意层 $n$ 的任意元素 $\phi \in Q_n$，选择在其后的某个零态射层 $m \ge n$（$a_m = 0$），拉回至 $m+1$ 层为 $\rho_{n, m+1}^*(\phi) = 0$。因此 $M_P = \mathrm{colim} Q_n = 0$。此时 $F_P(A) \cong 0 \otimes A = 0 \cong \mathrm{Hom}(0, A)$，由平凡群 $P = 0$ 表示。
- **情形 2 的充分必要性**：
  若只有有限个 $a_n = 0$，则存在 $N_0$ 使得当 $n \ge N_0$ 时 $a_n \ne 0$。截去前 $N_0$ 项不改变余极限，故可设所有 $a_n \ne 0$。
  此时各过渡映射单射，$M_P$ 同构于 $\mathbb{Q}$ 中由子群序列 $\frac{1}{\prod_{k=0}^{n-1} a_k}\mathbb{Z}$ 递增张成的子群。
  $\mathbb{Q}$ 的有理子群有限生成当且仅当它是循环群（即分母有公共界）。
  - 若存在 $N$ 使得对所有 $n \ge N$，$|a_n| = 1$，则对所有 $n \ge N$，$\rho_n^* : \mathbb{Z} \to \mathbb{Z}$ 为乘 $\pm 1$ 同构，故 $M_P \cong \mathbb{Z}$ 为秩 1 自由群，$F_P$ 由 $\mathbb{Z}$ 表示；
  - 若有无穷多个 $n$ 满足 $|a_n| \ge 2$，则分母序列的分母绝对值趋向无穷且有无穷多个严格真除数步，所生成的子群不可能包含于任何 $\frac{1}{D}\mathbb{Z}$ 中，从而 $M_P$ 不是有限生成群。由 S3 知 $F_P$ 不可表。
此判据对包含 0、负数在内的一切整数序列均完整适用。

---

## S5　稳定像中的延拓

### 1. 判断每个 $I_n$ 是否必为 $P_n$ 的直和项

- **结论：否**（不必）。
- **反例与验证**：
  令各层自由群均为 $P_n = \mathbb{Z}$（$n \ge 0$）。
  定义过渡态射：
  $$\rho_0 : P_1 \to P_0, \quad x \longmapsto 2x;$$
  对所有 $n \ge 1$，定义 $\rho_n : P_{n+1} \to P_n$ 为恒等态射 $\mathrm{id}_{\mathbb{Z}}$。
  - **核验 S5 前提条件**：
    取 $n_0 = 0$。
    - 对 $n = 0$：对任意 $m \ge 1$，$\rho_{0,m}(P_m) = \rho_0(\rho_{1,m}(P_m)) = \rho_0(\mathbb{Z}) = 2\mathbb{Z}$。故像序列常值稳定为 $I_0 = 2\mathbb{Z}$。
    - 对任意 $n \ge 1$：对任意 $m \ge n$，$\rho_{n,m}(P_m) = \mathbb{Z}$。故像序列常值稳定为 $I_n = \mathbb{Z}$。
    - 稳定像之间的过渡态射：
      当 $n = 0$ 时，$\rho_0|_{I_1} : I_1 = \mathbb{Z} \to I_0 = 2\mathbb{Z}$，映射为 $x \mapsto 2x$，这是自由阿贝尔群间的同构；
      当 $n \ge 1$ 时，$\rho_n|_{I_{n+1}} = \mathrm{id}_{\mathbb{Z}} : \mathbb{Z} \to \mathbb{Z}$ 为同构。
    因此，完全满足 S5 的全部前提假设。
  - **直和项判定**：
    考察 $I_0 = 2\mathbb{Z} \subset \mathbb{Z} = P_0$。
    商群 $P_0/I_0 = \mathbb{Z}/2\mathbb{Z} \cong \mathbb{Z}_2 \ne 0$ 是挠群。
    若 $I_0$ 为 $P_0$ 的直和项，则存在补项 $K$ 使 $P_0 = I_0 \oplus K$，商群 $P_0/I_0 \cong K$ 必为自由群 $P_0$ 的子群，从而必无挠，矛盾！
    因此，$I_0$ **不是** $P_0$ 的直和项。

---

### 2. 构造 $m \ge n_0$ 上的回缩 $r : P_m \to I_m$

依据假设，在层 $n_0$ 处，降链群序列 $\{\rho_{n_0, k}(P_k)\}_{k \ge n_0}$ 最终稳定于 $I_{n_0}$。
因此，存在某个整数 $m \ge n_0$，使得
$$\rho_{n_0, m}(P_m) = I_{n_0}.$$
由于对任意 $k \ge n_0$，$\rho_k|_{I_{k+1}} : I_{k+1} \xrightarrow{\sim} I_k$ 均为同构，其有限次复合
$$\rho_{n_0, m}|_{I_m} : I_m \xrightarrow{\ \sim\ } I_{n_0}$$
亦为阿贝尔群的同构。
记其逆同构为
$$\sigma_{m, n_0} := \left(\rho_{n_0, m}|_{I_m}\right)^{-1} : I_{n_0} \xrightarrow{\ \sim\ } I_m.$$
定义映射 $r : P_m \to I_m$ 为复合：
$$r := \sigma_{m, n_0} \circ \rho_{n_0, m}.$$
因 $\rho_{n_0, m}(P_m) = I_{n_0}$，上式对所有 $x \in P_m$ 良定义且为群同态。
- **回缩性验证**：
  对任意 $x \in I_m \subseteq P_m$，依据限制映射的定义：
  $$r(x) = \sigma_{m, n_0}(\rho_{n_0, m}(x)) = \sigma_{m, n_0}\left(\rho_{n_0, m}|_{I_m}(x)\right) = x.$$
  因此 $r|_{I_m} = \mathrm{id}_{I_m}$，$r : P_m \to I_m$ 确实是回缩态射（且 $P_m = I_m \oplus \ker(r)$）。

---

### 3. 由实际记录证明 $F_P \cong \mathrm{Hom}(I_{n_0}, -)$

我们直接在实际记录元与同态群之间建立映射并验证互逆性与自然性。

对任意 $A \in \mathbf{Ab}_{\mathcal{U}}$：

#### (1) 构造映射 $\Phi_A : F_P(A) \to \mathrm{Hom}_{\mathbb{Z}}(I_{n_0}, A)$
对实际记录 $[(n, u)] \in F_P(A)$（$u \in \mathrm{Hom}(P_n, A)$）：
取任意充分大的 $k \ge \max(n, n_0)$。将该记录提升至第 $k$ 层，得代表元 $u \circ \rho_{n, k} \in \mathrm{Hom}(P_k, A)$。
将其限制在第 $k$ 层的稳定像 $I_k$ 上，再复合逆同构 $\sigma_{k, n_0} = (\rho_{n_0, k}|_{I_k})^{-1} : I_{n_0} \xrightarrow{\sim} I_k$：
$$\Phi_A([(n, u)]) := (u \circ \rho_{n, k})|_{I_k} \circ \sigma_{k, n_0} \in \mathrm{Hom}_{\mathbb{Z}}(I_{n_0}, A).$$
- **良定义性**：
  - 若换选更大的 $k' \ge k$，由传递性 $\rho_{n, k'} = \rho_{n, k} \circ \rho_{k, k'}$ 以及 $\sigma_{k', n_0} = (\rho_{k, k'}|_{I_{k'}})^{-1} \circ \sigma_{k, n_0}$，所得映射恒等；
  - 若 $(n, u) \sim (n', u')$，则在充分深层 $R$ 处 $u \circ \rho_{n, R} = u' \circ \rho_{n', R}$，直接导出在 $I_{n_0}$ 上的映射相同；
  - 显然 $\Phi_A$ 保持群加法。

#### (2) 构造逆映射 $\Psi_A : \mathrm{Hom}_{\mathbb{Z}}(I_{n_0}, A) \to F_P(A)$
利用第 2 步在层 $m$ 上构造的回缩态射 $r = \sigma_{m, n_0} \circ \rho_{n_0, m} : P_m \to I_m$。
对任意 $f \in \mathrm{Hom}_{\mathbb{Z}}(I_{n_0}, A)$，定义延拓态射 $\bar{f} \in \mathrm{Hom}(P_m, A)$ 为：
$$\bar{f} := f \circ (\rho_{n_0, m}|_{I_m}) \circ r = f \circ (\rho_{n_0, m}|_{I_m}) \circ \sigma_{m, n_0} \circ \rho_{n_0, m} = f \circ \rho_{n_0, m}.$$
定义其在 $F_P(A)$ 中的记录：
$$\Psi_A(f) := [(m, \bar{f})] = [(m, f \circ \rho_{n_0, m})] \in F_P(A).$$
$\Psi_A$ 显然为群同态。

#### (3) 验证 $\Phi_A \circ \Psi_A = \mathrm{id}_{\mathrm{Hom}(I_{n_0}, A)}$
对任意 $f \in \mathrm{Hom}(I_{n_0}, A)$，取层 $k = m$ 计算 $\Phi_A$：
$$\Phi_A(\Psi_A(f)) = \Phi_A([(m, f \circ \rho_{n_0, m})]) = (f \circ \rho_{n_0, m})|_{I_m} \circ \sigma_{m, n_0} = f \circ (\rho_{n_0, m}|_{I_m}) \circ (\rho_{n_0, m}|_{I_m})^{-1} = f.$$
故 $\Phi_A \circ \Psi_A = \mathrm{id}$。

#### (4) 验证 $\Psi_A \circ \Phi_A = \mathrm{id}_{F_P(A)}$
对任意 $[(n, u)] \in F_P(A)$，设 $f = \Phi_A([(n, u)])$。
依定义，$\Psi_A(f) = [(m, f \circ \rho_{n_0, m})]$。
我们需证明在 $F_P(A)$ 中 $[(m, f \circ \rho_{n_0, m})] = [(n, u)]$。
由假设，降链 $\rho_{n, k}(P_k)$ 稳定于 $I_n$，$\rho_{n_0, k}(P_k)$ 稳定于 $I_{n_0}$。
选取充分大的 $k \ge \max(n, m)$ 使得
$$\rho_{n, k}(P_k) = I_n \quad \text{且} \quad \rho_{n_0, k}(P_k) = I_{n_0}.$$
将记录 $(m, f \circ \rho_{n_0, m})$ 与 $(n, u)$ 均拉回到第 $k$ 层，分别得到：
$$(f \circ \rho_{n_0, m}) \circ \rho_{m, k} = f \circ \rho_{n_0, k} : P_k \to A,$$
$$u \circ \rho_{n, k} : P_k \to A.$$
任取 $y \in P_k$，我们核验两态射在 $y$ 上的取值：
因 $y \in P_k$，由 $k$ 的选取，$\rho_{n, k}(y) \in I_n$，且 $\rho_{n_0, k}(y) = \rho_{n_0, n}(\rho_{n, k}(y)) \in I_{n_0}$。
代入 $f$ 的定义（在第 $k$ 层计算）：
$$f(\rho_{n_0, k}(y)) = (u \circ \rho_{n, k})|_{I_k} \left(\sigma_{k, n_0}(\rho_{n_0, k}(y))\right).$$
令 $z = \sigma_{k, n_0}(\rho_{n_0, k}(y)) \in I_k$。则依逆映射定义，$\rho_{n_0, k}(z) = \rho_{n_0, k}(y)$。
展开为：
$$\rho_{n_0, n}(\rho_{n, k}(z)) = \rho_{n_0, n}(\rho_{n, k}(y)).$$
注意到 $\rho_{n, k}(z) \in I_n$ 且 $\rho_{n, k}(y) \in I_n$。
因为限制态射 $\rho_{n_0, n}|_{I_n} : I_n \to I_{n_0}$ 是同构（从而为单射），故由上式严格推出：
$$\rho_{n, k}(z) = \rho_{n, k}(y) \in I_n.$$
两端作用 $u$ 即得：
$$u(\rho_{n, k}(z)) = u(\rho_{n, k}(y)).$$
因此，
$$f(\rho_{n_0, k}(y)) = u(\rho_{n, k}(z)) = u(\rho_{n, k}(y)).$$
此式对全体 $y \in P_k$ 均成立，故在 $\mathrm{Hom}(P_k, A)$ 中两同态完全重合：
$$f \circ \rho_{n_0, k} = u \circ \rho_{n, k}.$$
因此在余极限中 $[(m, f \circ \rho_{n_0, m})] = [(n, u)]$。
故 $\Psi_A \circ \Phi_A = \mathrm{id}$。

#### (5) 自然性
对任意态射 $h : A \to B$，显然有
$$\Phi_B(F_P(h)([(n, u)])) = \Phi_B([(n, h \circ u)]) = (h \circ u \circ \rho_{n, k})|_{I_k} \circ \sigma_{k, n_0} = h \circ \Phi_A([(n, u)]).$$
因此 $\Phi : F_P(-) \implies \mathrm{Hom}_{\mathbb{Z}}(I_{n_0}, -)$ 为自然同构。

---

## S6　具体变换与无限积

设 $P_n = \mathbb{Z}$ 且 $a_n = 2$（对所有 $n \ge 0$）。

### 1. 全部 $F_P$ 自同态及自同构的计算

由 S1 与 S4，该塔的余极限模为二进有理数加法群：
$$M_P = \mathrm{colim}(\mathbb{Z} \xrightarrow{\times 2} \mathbb{Z} \xrightarrow{\times 2} \cdots) \cong \mathbb{Z}[1/2].$$

#### (1) 全部自同态 $\mathrm{End}(F_P)$
由 S2，$\mathrm{End}(F_P) = \mathrm{Nat}(F_P, F_P) \cong \mathrm{Hom}_{\mathbb{Z}}(\mathbb{Z}[1/2], \mathbb{Z}[1/2])$。
任取群同态 $\theta : \mathbb{Z}[1/2] \to \mathbb{Z}[1/2]$。
记 $c = \theta(1) \in \mathbb{Z}[1/2]$。
对任意 $x = \frac{m}{2^k} \in \mathbb{Z}[1/2]$（$m \in \mathbb{Z}, k \ge 0$），在 $\mathbb{Z}[1/2]$ 中有
$$2^k \cdot \theta(x) = \theta(2^k x) = \theta(m) = m \cdot \theta(1) = m c.$$
因为 $\mathbb{Z}[1/2]$ 无挠，除以 $2^k$ 的结果在 $\mathbb{Z}[1/2]$ 中唯一确定，故必有
$$\theta(x) = c \cdot \frac{m}{2^k} = c \cdot x.$$
即任何群同态 $\theta$ 必为乘以二进有理数 $c$ 的映射。
反之，对任意 $c \in \mathbb{Z}[1/2]$，乘 $c$ 映射显然是群同态。
因此，作为自同态环，
$$\mathrm{End}(F_P) \cong \mathbb{Z}[1/2].$$
在自然变换的分量上，对应于 $c = \frac{p}{2^k}$（$p \in \mathbb{Z}, k \ge 0$）的自然变换将记录 $[(n, u)]$ 映至 $[(n+k, p \cdot u)]$。

#### (2) 全部自同构 $\mathrm{Aut}(F_P)$
自同构群即为自同态环的乘法单位群：
$$\mathrm{Aut}(F_P) \cong \left(\mathbb{Z}[1/2]\right)^\times.$$
任取 $c \in \mathbb{Z}[1/2]$。设其既约形式为 $c = \frac{p}{2^a}$，其中 $p$ 为奇数，$a \in \mathbb{Z}$。
$c$ 在 $\mathbb{Z}[1/2]$ 中可逆，当且仅当存在 $c' \in \mathbb{Z}[1/2]$ 使得 $c c' = 1$，即 $1/c = \frac{2^a}{p} \in \mathbb{Z}[1/2]$。
这意味着奇数 $p$ 的质因数只能为 2，故必有 $p = \pm 1$。
因此，全部可逆元为
$$c = \pm 2^k \quad (k \in \mathbb{Z}).$$
故自同构群为：
$$\mathrm{Aut}(F_P) \cong \{ \pm 2^k \mid k \in \mathbb{Z} \} \cong \{\pm 1\} \times \mathbb{Z}.$$
每个自同构均为形如 $x \mapsto \pm 2^k x$（$k \in \mathbb{Z}$）的逐分量放缩变换。

---

### 2. 典范比较 $F_P(\mathbb{Z}^{\mathbb{N}}) \to F_P(\mathbb{Z})^{\mathbb{N}}$ 不满射的具体元素

记 $\pi_i : \mathbb{Z}^{\mathbb{N}} \to \mathbb{Z}$ 为第 $i$ 个坐标投射（$i \in \mathbb{N}$）。
典范比较态射为：
$$\Theta : F_P(\mathbb{Z}^{\mathbb{N}}) \longrightarrow \prod_{i \in \mathbb{N}} F_P(\mathbb{Z}) = \left(F_P(\mathbb{Z})\right)^{\mathbb{N}}, \quad \xi \longmapsto (F_P(\pi_i)(\xi))_{i \in \mathbb{N}}.$$
- **典范同构下的像集特征**：
  在同构 $F_P(\mathbb{Z}) \cong M_P = \mathbb{Z}[1/2]$ 之下，目标群为二进有理数序列群 $(\mathbb{Z}[1/2])^{\mathbb{N}}$。
  任取原像中的记录元 $\xi = [(n, u)] \in F_P(\mathbb{Z}^{\mathbb{N}})$，其中 $n \in \mathbb{N}$ 是某个**固定的有限层指标**，$u : \mathbb{Z} \to \mathbb{Z}^{\mathbb{N}}$ 由整数序列 $u(1) = (w_i)_{i \in \mathbb{N}} \in \mathbb{Z}^{\mathbb{N}}$ 完全给出。
  则对每个坐标 $i \in \mathbb{N}$，第 $i$ 个分量为：
  $$F_P(\pi_i)([(n, u)]) = [(n, \pi_i \circ u)] \in F_P(\mathbb{Z}),$$
  在 $\mathbb{Z}[1/2]$ 中对应的二进有理数为 $\frac{w_i}{2^n}$。
  由此可知，**$\Theta$ 的像集中的任意元素 $(y_i)_{i \in \mathbb{N}}$，其所有坐标的分母必有与 $i$ 无关的公共有限上界 $2^n$**，即
  $$\exists n \in \mathbb{N}, \quad \forall i \in \mathbb{N}, \quad 2^n y_i \in \mathbb{Z}.$$

- **具体不满射元素构造与核验**：
  构造元素：
  $$y^* := \left(\frac{1}{2^i}\right)_{i=0}^\infty = \left(1, \ \frac{1}{2}, \ \frac{1}{4}, \ \frac{1}{8}, \ \dots, \ \frac{1}{2^i}, \ \dots\right) \in (\mathbb{Z}[1/2])^{\mathbb{N}} = \left(F_P(\mathbb{Z})\right)^{\mathbb{N}}.$$
  **证明 $y^* \notin \mathrm{im}(\Theta)$**：
  反设存在 $\xi = [(n, u)] \in F_P(\mathbb{Z}^{\mathbb{N}})$ 使得 $\Theta(\xi) = y^*$。
  由前述特征，该代表元具有固定的层数 $n \in \mathbb{N}$，使得对一切 $i \in \mathbb{N}$ 恒有 $2^n y_i^* \in \mathbb{Z}$。
  然而，选取坐标 $i = n+1 \in \mathbb{N}$，则有：
  $$2^n \cdot y^*_{n+1} = 2^n \cdot \frac{1}{2^{n+1}} = \frac{1}{2} \notin \mathbb{Z}.$$
  产生矛盾！
  因此，元素 $y^* = (2^{-i})_{i \in \mathbb{N}}$ 绝不在 $\Theta$ 的像中。故 $\Theta$ 不是满射。

---

### 3. 与有限极限保持的相容性说明

上述不满射现象与 S2 中证明的“$F_P$ 保持有限极限”**完全相容，毫无矛盾**。其机理如下：

1. **有限极限与无限极限的本质区别**：
   无限直积 $\mathbb{Z}^{\mathbb{N}} = \prod_{i=0}^\infty \mathbb{Z}$ 是由无穷离散图表所定义的**无限极限**。
   S2 所保证的是 $F_P$ 保持**有限**极限（即有限图表的极限，或等价地，有限直积与核）。对任意有限项直积 $\prod_{i=1}^K \mathbb{Z}$，比较映射
   $$F_P\left(\prod_{i=1}^K \mathbb{Z}\right) \longrightarrow \prod_{i=1}^K F_P(\mathbb{Z})$$
   恒为同构。因为任意有限个二进有理数 $y_1, \dots, y_K$ 的分母只有有限个，其最大分母 $2^{\max(n_1, \dots, n_K)}$ 必为有限整数，能够在某有限层公共截断上被完全通分代表。
2. **余极限与极限交换的范畴界限**：
   在任何满足 AB5 公理的阿贝尔范畴（如 $\mathbf{Ab}_{\mathcal{U}}$）中，滤向余极限 $\mathrm{colim}_n$ 与一切**有限**极限可交换，但普遍**不与无限积（无限极限）可交换**。
   典范映射 $F_P(\mathbb{Z}^{\mathbb{N}}) \to F_P(\mathbb{Z})^{\mathbb{N}}$ 的本质即为滤向余极限与无限直积的交换比较态射：
   $$\mathrm{colim}_n \prod_{i \in \mathbb{N}} \mathrm{Hom}(P_n, \mathbb{Z}) \longrightarrow \prod_{i \in \mathbb{N}} \mathrm{colim}_n \mathrm{Hom}(P_n, \mathbb{Z}).$$
   该映射在目标对象非有限生成时发生严格退化（非满），正是无限图表下滤向余极限无法突破无限极限这一经典范畴特征的具体体现。因此，无限积保持性的失效与有限极限的保持性完全和谐相容。
