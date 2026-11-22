### 总体判断

**结论：所给 Lean 实现在结论形态与证明方向上准确，但未能完整覆盖数学正文中的推论 `#h-93b9c20ea18b4e59`（路径保证域的全局拟合含义）。**

核心原因有两点：
1. **前提过强（核心缺口）**：源码中锚定到 `#h-93b9c20ea18b4e59` 的全部三个定理（`path_component_guarantee_union_subset_proxy_error`、`path_joint_guarantee_union_subset_proxy_error`、`path_guarantee_union_subset_proxy_error_text`）均无条件要求**每一条可达路径** $q \in \mathcal P$ 都具有合法的受限 Lip 矩阵（`hLq : ∀ q : N.ReachablePath, IsLipMatrix d (N.path_chain q.nodes) (N.path_domain q.nodes) (Lq q)`），即使该路径满足 $j \notin I_{\mathrm{res}}(q)$ 或 $J \not\subseteq I_{\mathrm{res}}(q)$、根本不参与左端并集。在扩展规范空间（允许非分离伪度量）中，该附加前提无法通过取 $\top$ 自动补齐，导致存在满足数学正文全部条件的实例却无法调用任何一条 Lean 定理（见下方反例 1）。
2. **文本封装将分量分支与联合分支强耦合（结构性缺口）**：`path_guarantee_union_subset_proxy_error_text` 将单分量结论与联合分量结论合写为一个合取定理并共享单一顶层 `hLq`（且同时要求给出 `j` 与 `J` 的前提）。即便把 `hLq` 弱化到“在某分量上可评估”或“在 $j$ 或 $J$ 上可评估”，仍存在对联合族 $J$ 合法、但对每个单分量 $j \in I_{\mathrm{res}}$ 都包含无 Lip 矩阵路径的实例（见下方反例 2），从而单条耦合封装定理无法完整覆盖联合分支。

此外，源码在若干辅助等价桥接（如 $U_{q,J}(\boldsymbol\tau) = \bigcap_{j \in J} U_{q,j}(\tau_j)$ 的集合等式、$U \subseteq V^* \Leftrightarrow \forall q, U_q \subseteq V^*$、`N.represents proxy → N.U ⊆ dom proxy`）上未给出显式声明，但这些均属于可直接补证的次要桥接，不影响主逻辑方向。

---

### 一、数学命题与 Lean 源码的对应关系

审阅目标为 `source.md` 中的**推论 `#h-93b9c20ea18b4e59`（路径保证域的全局拟合含义）**（见 [01-user-033.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/AHR02/physical-1/session/work/.visible-input/AHR02/01-user-033.txt#L528-L546)，前置设定见 [01-user-033.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/AHR02/physical-1/session/work/.visible-input/AHR02/01-user-033.txt#L291-L452)），以及 `formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean` 中的实现（见 [01-user-031.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/AHR02/physical-1/session/work/.visible-input/AHR02/01-user-031.txt#L494-L608)、[01-user-032.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/AHR02/physical-1/session/work/.visible-input/AHR02/01-user-032.txt#L402-L521)）：

| 数学正文对象 / 命题要素 | Lean 实现对应声明 | 覆盖评价 |
|---|---|---|
| 扩展规范空间 $(\mathcal X,\mathcal G,\bot)$ 与有限指标集 $I$ | `[Fintype I]`、`hd : ∀ j : I, ExtendedPseudoMetric X bot (d j)` | 准确（`_text` 中由 `j : I` 与 `hJ_nonempty` 隐含 $I$ 非空） |
| 有限算子网络 $\mathcal N$、输入域 $U$、表示 $\phi_{\mathcal N}\equiv_U\phi$ | `N : FiniteOperatorNetwork X bot V`、`N.U`、`hrep : N.represents proxy` | 准确（`N.U ⊆ dom proxy` 可由 `hrep` 与 `N.dom_extensional_operator_eq` 推出） |
| 目标 Lip 包络 $(V^*,\mathbf L^*)$ 与 $U\subseteq V^*$ | `hLstar : TargetLipEnvelopeCertificate d target Vstar Lstar`、`hpathV : ∀ q, N.path_domain q.nodes ⊆ Vstar` | 准确（由 `N.reachable_path_domains_cover` 与 `N.path_domain_subset_source`，`hpathV` 与 `N.U ⊆ Vstar` 逻辑等价） |
| 采样结构 $\mathcal S$、$I_{\mathrm{res}}$、$S_{q,j}$、$I_{\mathrm{res}}(q)$、$\hat\varepsilon_{q,j}$ | `sample : I → Set X`、`evaluable_components`、`path_component_sample`、`path_evaluable_components`、`path_empirical_residual_upper` | 准确且略更一般（未强制 `SamplingStructure` 或 `sample j ⊆ N.U`，因取交 $S_j \cap U_q$ 后自动落入 $U_q \subseteq U \cap \mathrm{dom}(\phi) \cap \mathrm{dom}(\phi^\natural)$） |
| 路径链受限 Lip 证书 $\mathbf L_q \in \mathscr L(c_q)\big|_{U_q}$ | `Lq : N.ReachablePath → I → I → ENNReal`、`hLq : ∀ q : N.ReachablePath, IsLipMatrix d (N.path_chain q.nodes) (N.path_domain q.nodes) (Lq q)` | **前提过强**：要求全体可达路径皆有 Lip 矩阵，超出正文仅对参与保证域的可评估路径取 $\mathbf L_q$ 的设定 |
| 路径分量保证域 $U_{q,j}(\tau_j)$ | `path_component_empirical_guarantee_domain`（展开为 `{x \| x ∈ U_q ∧ weighted_anchor_distance ... + eps ≤ tau}`） | 准确 |
| 路径联合保证域 $U_{q,J}(\boldsymbol\tau)=\bigcap_{j\in J} U_{q,j}(\tau_j)$ | `path_joint_empirical_guarantee_domain`（展开为 `{x \| x ∈ U_q ∧ ∀ j ∈ J, ...}`） | 当 `J.Nonempty` 时与交集定义外延相等（但源码未单列该等式引理；若 $J=\emptyset$ 则二者不等） |
| 分量并集包含 $\bigcup_{q\in\mathcal P,\, j\in I_{\mathrm{res}}(q)} U_{q,j}(\tau_j) \subseteq \{x\in U : d_j(\phi(x),\phi^\natural(x))\le \tau_j\}$ | `path_component_guarantee_union_subset_proxy_error` 及 `_text` 第一支 | 结论准确；受限于过强 `hLq` |
| 联合并集包含 $\bigcup_{q\in\mathcal P,\, J\subseteq I_{\mathrm{res}}(q)} U_{q,J}(\boldsymbol\tau) \subseteq \{x\in U : \forall j\in J,\, d_j(\phi(x),\phi^\natural(x))\le \tau_j\}$ | `path_joint_guarantee_union_subset_proxy_error` 及 `_text` 第二支 | 结论准确；受限于过强 `hLq` 及 `_text` 分支耦合 |

---

### 二、不足之处的可复核论证与反例

#### 不足 1：`hLq` 对全部可达路径全称量化，无法覆盖存在“不可评估且无 Lip 矩阵路径”的合法情形

正文在 `#h-55c4fe8427039cfc` 中并未假定 $\mathcal N$ 的每条可达路径 $q \in \mathcal P$ 都存在 Lip 矩阵；仅在 `#h-0056e459b9376864` 中先固定 $q \in \mathcal P,\ j \in I_{\mathrm{res}}(q)$ 后才取 $\mathbf L_q \in \mathscr L(c_q)\big|_{U_q}$（且前文注“路径采样缺失”明确指出 $S_{q,j}=\emptyset$ 时该路径证书停止）。在推论 `#h-93b9c20ea18b4e59` 的证明中，`@h-4b5219aa3a3bbdad` 也仅应用于并集指标集内的路径（分量形式要求 $j \in I_{\mathrm{res}}(q)$，联合形式要求 $J \subseteq I_{\mathrm{res}}(q)$）。

在源码三个定理（[01-user-032.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/AHR02/physical-1/session/work/.visible-input/AHR02/01-user-032.txt#L418-L419)、[L450-L451](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/AHR02/physical-1/session/work/.visible-input/AHR02/01-user-032.txt#L450-L451)、[L492-L493](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/AHR02/physical-1/session/work/.visible-input/AHR02/01-user-032.txt#L492-L493)）中，证明体仅在已解构出 `hj : j ∈ path_evaluable_components N sample q` 或 `hJ : J ⊆ path_evaluable_components N sample q` 后才调用 `hLq q`，但定理签名却要求对**所有** `q : N.ReachablePath` 成立 `IsLipMatrix`。

需要特别指出：若规范族是分离的，虽然可在未采样路径上人为填入全 $\top$ 矩阵勉强满足 `IsLipMatrix`（因为 $x \neq y \Rightarrow \exists i,\, d_i(x,y)>0 \Rightarrow \top \cdot d_i(x,y)=\top$），但 OET 的扩展规范空间明确允许**非分离伪度量**（见 `gauge_space.lean` 中的 `IsNonSeparating`）。在非分离情形下，由附件已证定理 `all_component_zero_preserved_by_lip_step`（`annihilation_matrix.lean`，[01-user-005.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/AHR02/physical-1/session/work/.visible-input/AHR02/01-user-005.txt#L96-L111)），任何满足 `IsLipMatrix` 的矩阵（即使取 $\top$，因 `ENNReal` 中 $\top \cdot 0 = 0$）都必须保持全分量零距点对。由此构造如下可完全复核的反例：

##### 反例 1（4 点、1 分量、2 节点无环网络；同时阻塞全部三条 Lean 定理）
- **扩展规范空间**：取 $X = \{\bot, a, b, c\}$（4 个互异元素），$I = \{0\}$（即 `Unit`）。在 $X \setminus \{\bot\}$ 上定义 $f(a)=f(b)=0,\ f(c)=1$，并令
  $$d_0(x,y)= \begin{cases} 0, & x=y, \\ \top, & (x=\bot \land y\neq \bot)\ \lor\ (x\neq \bot \land y=\bot), \\ |f(x)-f(y)|, & x,y \in \{a,b,c\}. \end{cases}$$
  逐条核验 `ExtendedPseudoMetric X bot (d 0)`：
  - `nonabsorbing`：$a \neq \bot$；
  - `dist_self`、`symm`、`isolate_bot` 由定义直接成立；
  - `triangle`：若 $x,y,z\in\{a,b,c\}$，则 $d_0$ 为 $\{0,1\}\subset\mathbb R$ 上欧氏距离沿 $f$ 的拉回，满足三角不等式；若三点中涉及 $\bot$，则 $x=z$ 时左端为 $0$，否则若 $x=\bot \neq z$（或 $z=\bot \neq x$），无论 $y=\bot$ 还是 $y\neq\bot$，右端必含一项 $\top$，而若 $x,z\neq\bot$ 且 $y=\bot$，右端为 $\top+\top=\top$。故全部公理成立。
- **有限算子网络 $\mathcal N$**：取 $V=\{v_1,v_2\}$，$U=\{a,b,c\}$（$\bot\notin U$）：
  - $\phi_{v_1}(c)=c$，其余点映到 $\bot$（$\mathrm{dom}(\phi_{v_1})=\{c\}\neq\emptyset$）；
  - $\phi_{v_2}(a)=a,\ \phi_{v_2}(b)=c$，其余点映到 $\bot$（$\mathrm{dom}(\phi_{v_2})=\{a,b\}\neq\emptyset$）；
  - 入口规则 $\mathrm{entry}(c)=v_1,\ \mathrm{entry}(a)=\mathrm{entry}(b)=v_2$（显然满足 `entry_mem`）；
  - 后继选择恒为 `OutputChoice.stop`，`depth_bound := 1`，`path_of x := [entry x]`（无环，所有节点均可达）。
  - 全部可达路径恰为两条：$q_1=[v_1]$（$U_{q_1}=\{c\}$，$c_{q_1}(c)=c$）与 $q_2=[v_2]$（$U_{q_2}=\{a,b\}$，$c_{q_2}(a)=a,\ c_{q_2}(b)=c$）。
- **代理、目标、包络与采样**：
  - 取 $\phi = \phi_{\mathcal N}$（故 `N.represents proxy` 显然成立，$\mathrm{dom}(\phi)=U$）；
  - 取 $\phi^\natural = \mathrm{id}_{\mathcal X}$（或 $\mathrm{id}|_U$），$V^* = U$，$\mathbf L^* = (1)$（对任意 $x,y\in U$ 有 $d_0(x,y)\le 1\cdot d_0(x,y)$，故 `TargetLipEnvelopeCertificate` 与 `hpathV` 均成立）；
  - 取有限环境采样 $S=\{c\}$，分量采样 $S_0=\{c\}\subseteq S\cap U\cap \mathrm{dom}(\phi)\cap\mathrm{dom}(\phi^\natural)$（满足 `SamplingStructure`），$\delta_{o,0}=0$，阈值 $\tau_0=0$（有限），$j=0$，$J=\{0\}$。
- **数学命题完全适用且成立**：
  - $I_{\mathrm{res}}=\{0\}$，$S_{q_1,0}=\{c\}\neq\emptyset \Rightarrow I_{\mathrm{res}}(q_1)=\{0\}$；$S_{q_2,0}=\{c\}\cap\{a,b\}=\emptyset \Rightarrow I_{\mathrm{res}}(q_2)=\emptyset$。
  - 在唯一可评估路径 $q_1$ 上，取 $\mathbf L_{q_1}=(0)$，则 `IsLipMatrix d (N.path_chain q₁.nodes) {c} L_{q_1}` 成立（单点集上距离皆为 $0$）。
  - 此时 $\hat\varepsilon_{q_1,0}=0$，$U_{q_1,0}(0)=\{c\}$；推论 `#h-93b9c20ea18b4e59` 的分量与联合结论均给出
    $$\bigcup_{\substack{q\in\mathcal P\\ 0\in I_{\mathrm{res}}(q)}} U_{q,0}(0) = U_{q_1,0}(0) = \{c\} \subseteq \{x\in U : d_0(\phi(x),\phi^\natural(x))\le 0\} = \{a,c\}.$$
- **全部三条 Lean 定理均不可实例化**：
  对未采样路径 $q_2$，任意 $L : \{0\}\times\{0\}\to \mathrm{ENNReal}$ 均不满足 `IsLipMatrix d (N.path_chain q₂.nodes) {a,b} L`。因为 $a,b\in U_{q_2}$ 满足 $d_0(a,b)=0$，而 $d_0(c_{q_2}(a),c_{q_2}(b))=d_0(a,c)=1$，故
  $$1 = d_0(c_{q_2}(a), c_{q_2}(b)) \not\le L_{0\to 0}\cdot d_0(a,b) = L_{0\to 0}\cdot 0 = 0$$
  （亦可直接由 `all_component_zero_preserved_by_lip_step` 推出 $d_0(a,c)=0$，矛盾）。因此不存在任何 `Lq` 满足 `hLq`。

---

#### 不足 2：联合形式必须按 $J \subseteq I_{\mathrm{res}}(q)$ 守卫 `hLq`，且 `_text` 封装不应将分量支与联合支的 `hLq` 耦合

##### 反例 2（6 点、2 分量、3 节点网络；说明仅弱化到 $I_{\mathrm{res}}(q)\neq\emptyset$ 以及保留 `_text` 单一耦合签名仍不够）
- 取 $X=\{\bot, c, a_0, b_0, a_1, b_1\}$，$I=\{0,1\}$。定义 $f(c)=1$，$f(a_0)=f(b_0)=f(a_1)=f(b_1)=0$，对 $i\in\{0,1\}$ 均取 $d_i$ 为上述拉回伪度量（$\bot$ 以 $\top$ 隔离）。
- 取 3 节点网络 $V=\{v_1,v_2,v_3\}$，$U=X\setminus\{\bot\}$：
  - $\phi_{v_1}(c)=c$；$\phi_{v_2}(a_0)=a_0,\ \phi_{v_2}(b_0)=c$；$\phi_{v_3}(a_1)=a_1,\ \phi_{v_3}(b_1)=c$（各节点在其定义域外映到 $\bot$）；
  - 入口将 $c\mapsto v_1$、$a_0,b_0\mapsto v_2$、$a_1,b_1\mapsto v_3$，后继恒为 `stop`，得到 3 条可达路径 $q_1=[v_1],\, q_2=[v_2],\, q_3=[v_3]$。
- 取 $\phi=\phi_{\mathcal N}$，$\phi^\natural=\mathrm{id}_{\mathcal X}$，$V^*=U$，$\mathbf L^*=\mathbf I_2$（单位矩阵），$\delta_o\equiv 0$；取有限采样 $S=\{c,a_0,a_1\}$，$S_0=\{c,a_0\}$，$S_1=\{c,a_1\}$。
- 于是 $I_{\mathrm{res}}=\{0,1\}$，各路径的可评估分量集为：
  $$I_{\mathrm{res}}(q_1)=\{0,1\},\qquad I_{\mathrm{res}}(q_2)=\{0\},\qquad I_{\mathrm{res}}(q_3)=\{1\}.$$
- 核验 Lip 证书：
  - $q_1$ 上取 $\mathbf L_{q_1}=\mathbf 0$ 合法；
  - $q_2$ 上 $d_0(a_0,b_0)=d_1(a_0,b_0)=0$ 而 $d_0(a_0,c)=1$，故无任何 Lip 矩阵；
  - $q_3$ 上 $d_0(a_1,b_1)=d_1(a_1,b_1)=0$ 而 $d_1(a_1,c)=1$，故无任何 Lip 矩阵。
- **结论**：
  1. 本例中每条路径都满足 $I_{\mathrm{res}}(q)\neq\emptyset$，且对于 $J=\{0,1\}$ 与 $\boldsymbol\tau=\mathbf 0$，唯一满足 $J\subseteq I_{\mathrm{res}}(q)$ 的路径是 $q_1$，其上存在合法 Lip 矩阵 $\mathbf L_{q_1}=\mathbf 0$，因此数学命题的联合结论完全适用并成立（$\{c\}\subseteq\{c,a_0,a_1\}$）。这表明联合分支的 `hLq` 不能仅弱化为 `∀ q, (path_evaluable_components N sample q).Nonempty → ...`，而必须精确守卫为 `∀ q, J ⊆ path_evaluable_components N sample q → ...`。
  2. 同时，对于任意 $j\in I_{\mathrm{res}}=\{0,1\}$，集合 $\{q\in\mathcal P : j\in I_{\mathrm{res}}(q)\}$ 都包含无 Lip 矩阵的路径（$j=0$ 含 $q_2$，$j=1$ 含 $q_3$）。因此，如果 `path_guarantee_union_subset_proxy_error_text` 继续将分量分支与联合分支合并在同一个顶层前提列表中要求同时满足两个分支的 `hLq`，则即便分别守卫，也依然无法对 $J=\{0,1\}$ 调用该 `_text` 定理。

---

### 三、如何补齐（修改方案）

1. **在两个核心定理中将 `hLq` 精确限制到并集实际涉及的路径**：
   - 在 `path_component_guarantee_union_subset_proxy_error` 中，将 `hLq` 改为：
     ```lean
     (hLq : ∀ q : N.ReachablePath,
       j ∈ path_evaluable_components N sample q →
         IsLipMatrix d (N.path_chain q.nodes) (N.path_domain q.nodes) (Lq q))
     ```
     原证明体中只需将 `(hLq q)` 改为 `(hLq q hj)`（`hj` 已由 `rcases hx with ⟨q, hj, hxq⟩` 给出）。
   - 在 `path_joint_guarantee_union_subset_proxy_error` 中，将 `hLq` 改为：
     ```lean
     (hLq : ∀ q : N.ReachablePath,
       J ⊆ path_evaluable_components N sample q →
         IsLipMatrix d (N.path_chain q.nodes) (N.path_domain q.nodes) (Lq q))
     ```
     原证明体中只需将 `(hLq q)` 改为 `(hLq q hJ)`（`hJ` 已由 `rcases hx with ⟨q, hJ, hxq⟩` 给出）。
   - （注：若愿意进一步采用依值族类型，也可写为 `Lq : {q : N.ReachablePath // j ∈ path_evaluable_components N sample q} → I → I → ENNReal`；由于 `I → I → ENNReal` 非空，两者在逻辑上等价，而保留 `Lq : N.ReachablePath → ...` 并守卫 `hLq` 改动最小。）

2. **在 `_text` 封装层解耦分量分支与联合分支**：
   - 将 `path_guarantee_union_subset_proxy_error_text` 拆分为两个独立的正文包装定理（`path_component_guarantee_union_subset_proxy_error_text` 与 `path_joint_guarantee_union_subset_proxy_error_text`），分别携带 `hj_evaluable`、`htau_j_finite` 与守卫后的分量 `hLq`，以及 `hJ_evaluable`、`hJ_nonempty`、`htau_finite` 与守卫后的联合 `hLq`；
   - 或若保留单一合取封装定理，则须将两支各自的 `Lq`、`hLq`（及 `j`/`J` 的前提）移入各自合取支的蕴含前件内部，避免一支的前件阻塞另一支的使用。

3. **补齐次要定义与前提的显式桥接引理（提升与正文表述的字面对应）**：
   - 补证交集等价引理：当 `hJ : J.Nonempty` 时，
     `path_joint_empirical_guarantee_domain d A N sample q J eps tau = ⋂ j ∈ J, path_component_empirical_guarantee_domain d A N sample q j (eps j) (tau j)`；
   - 补证域等价引理：`N.U ⊆ Vstar ↔ ∀ q : N.ReachablePath, N.path_domain q.nodes ⊆ Vstar`，以及 `N.represents proxy → N.U ⊆ dom proxy`；
   - （可选，若希望与第 7、12 章的拟合球语言直接对接）由上述并集包含加上 `htau_finite`、`N.U ⊆ dom proxy`、`N.U ⊆ dom target` 与 `(hd i).symm`，可立即补出一条推论：对任意包含于左端联合并集的子域 $U_0$，成立 `InFittingBall d target proxy U₀ J tau`。

---

### 四、源码已证明内容与需自行补充内容的区分

#### 1. 源码已证明的结论
- **网络路径分解与表示（`operator_network.lean`、`path_sampling.lean`）**：
  - `FiniteOperatorNetwork.path_domain_subset_source`（$U_q \subseteq U$）、`reachable_path_domains_cover`（$\bigcup_{q\in\mathcal P} U_q = U$）、`disjoint_path_domain_of_ne`、`dom_extensional_operator_eq`（$\mathrm{dom}(\phi_{\mathcal N})=U$）、`local_equivalent_extensional_path_chain`；
  - `path_chain_eq_represented_proxy_on_path`（$\phi_{\mathcal N}\equiv_U\phi \Rightarrow c_q = \phi$ 在 $U_q$ 上成立）、`path_component_sample_subset_path_domain`、`path_evaluable_subset_evaluable_components`。
- **路径局部经验上界与路径保证域误差界（`path_guarantee_domains.lean`，对应 `@h-4b5219aa3a3bbdad`）**：
  - `path_local_empirical_upper`、`proxy_path_local_empirical_upper`；
  - `path_component_guarantee_error_bound`、`proxy_path_component_guarantee_error_bound`、`proxy_path_component_guarantee_error_bound_text`；
  - `path_joint_guarantee_error_bound`、`proxy_path_joint_guarantee_error_bound`、`proxy_path_joint_guarantee_error_bound_text`。
- **全路径带 Lip 证书情形下的并集包含（`path_guarantee_domains.lean`，对应 `#h-93b9c20ea18b4e59` 的受限特例）**：
  - `path_component_guarantee_union_subset_proxy_error`（在**全部**可达路径都有 Lip 矩阵的附加前提下，证明了分量并集包含）；
  - `path_joint_guarantee_union_subset_proxy_error`（在**全部**可达路径都有 Lip 矩阵的附加前提下，证明了联合并集包含）；
  - `path_guarantee_union_subset_proxy_error_text`（在同时给定分量与联合两组前提且全部可达路径都有 Lip 矩阵时，打包证明了上述两个包含）。
- **其他被本文论证引用的已证辅助结论**：
  - `all_component_zero_preserved_by_lip_step`（`annihilation_matrix.lean`，用于确认反例中无 Lip 矩阵的严格性）。

#### 2. 需自行补充的内容
- **核心补齐（恢复对 `#h-93b9c20ea18b4e59` 的完整覆盖）**：
  1. 在分量并集定理中将 `hLq` 弱化为仅在 `j ∈ path_evaluable_components N sample q` 时要求 `IsLipMatrix`；
  2. 在联合并集定理中将 `hLq` 弱化为仅在 `J ⊆ path_evaluable_components N sample q` 时要求 `IsLipMatrix`；
  3. 将 `_text` 封装解耦为独立的分量版本与联合版本（或把各自守卫后的 `hLq` 与 `j`/`J` 前提移入对应合取支内部）。
- **形式化桥接补充（源码未显式成文但直接可证）**：
  1. 非空 $J$ 下 `path_joint_empirical_guarantee_domain` 与交集 $\bigcap_{j\in J} U_{q,j}(\tau_j)$ 的集合相等引理；
  2. `N.U ⊆ Vstar ↔ ∀ q : N.ReachablePath, N.path_domain q.nodes ⊆ Vstar` 与 `N.represents proxy → N.U ⊆ dom proxy`（直接衔接正文前提 $U \subseteq \mathrm{dom}(\phi) \cap V^*$）；
  3. 反例 1 与反例 2 的论证（本文已给出完整、可逐条核验的构造与证明）；
  4. （可选）由并集包含向第 7/12 章 `InFittingBall d target proxy U₀ J tau` 结构的直接封装。