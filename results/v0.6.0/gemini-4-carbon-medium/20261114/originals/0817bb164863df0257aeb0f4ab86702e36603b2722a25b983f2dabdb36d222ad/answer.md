{}
{}
以下对 [source.md](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane1-20261114-v5/attempts/AHR04/physical-1/session/work/source.md#L242-L260) 中的**推论 `#h-93b9c20ea18b4e59`（路径保证域的全局拟合含义）**及其在 [path_guarantee_domains.lean](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane1-20261114-v5/attempts/AHR04/physical-1/session/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L514-L638) 中的 Lean 4 实现给出审阅意见（全库 43 个模块均已在本地 Lean 4.29.1 环境下独立编译核验，零 `sorry`、零自定义 `axiom`）。

---

### 一、总体判断与依据

**结论：两个独立的底层核心定理在数学实质上准确且完整地覆盖了原推论的两部分结论（前提比正文更弱）；但对齐正文字面表述的打包定理 `path_guarantee_union_subset_proxy_error_text` 存在前提过度耦合的实质性缺陷，导致其无法完整覆盖正文的联合分量结论，此外集合运算记号与拟合球谓词存在少量编码形态差异。**

具体依据如下：
1. **底层双定理覆盖完整且无退化漏洞**：
   - 单分量全局并集包含关系由 `path_component_guarantee_union_subset_proxy_error`（[path_guarantee_domains.lean](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane1-20261114-v5/attempts/AHR04/physical-1/session/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L520-L545)）证明；
   - 非空分量族全局并集包含关系由 `path_joint_guarantee_union_subset_proxy_error`（[path_guarantee_domains.lean](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane1-20261114-v5/attempts/AHR04/physical-1/session/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L553-L582)）证明。
   - 两者在无需 $j \in I_{\mathrm{res}}$、$J \neq \emptyset$、$J \subseteq I_{\mathrm{res}}$、$\tau_j < +\infty$ 及 `SamplingStructure` 的更弱假设下成立；同时由 `hrep` 与 `hpathV` 可严格排除 $\bot$ 吸收态造成的 `d_j bot bot = 0` 平凡退化，矩阵指标方向 $(i \to j)$ 与上游定义完全一致。
2. **正文对齐定理 `_text` 的前提耦合缺陷（核心不足）**：
   - 正文（[source.md](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane1-20261114-v5/attempts/AHR04/physical-1/session/work/source.md#L244-L258)）中，单分量结论（对任意 $j \in I_{\mathrm{res}}$）与联合结论（对任意非空 $J \subseteq I_{\mathrm{res}}$）是**分别独立全称量化**的：调用联合结论时，仅要求满足 $J \subseteq I_{\mathrm{res}}(q)$ 的路径 $q$ 具备 Lipschitz 证书 $\mathbf L_q \in \mathscr L(c_q)|_{U_q}$。
   - 但 `path_guarantee_union_subset_proxy_error_text`（[path_guarantee_domains.lean](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane1-20261114-v5/attempts/AHR04/physical-1/session/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L590-L637)）将两组参数 `(j, tau_j)` 与 `(J, tau)` 合并进同一个定理签名，并在 `hLq`（第 606–609 行）中要求对所有满足 `j ∈ I_res(q) ∨ J ⊆ I_res(q)` 的路径同时提供 Lipschitz 矩阵。当某条路径仅含单个分量样本（$j \in I_{\mathrm{res}}(q)$ 但 $J \not\subseteq I_{\mathrm{res}}(q)$）且在该路径上不存在有限/扩展实数 Lipschitz 矩阵时，正文的联合结论依然成立，但 `_text` 定理对**任何** $j \in I_{\mathrm{res}}$ 的选取均因 `hLq` 假而无法实例化（详见第三节反例）。
3. **集合表示与接口形态差异**：
   - 路径联合保证域 $U_{q,J}(\boldsymbol\tau)$ 采用性质概括式 `{x | x ∈ U_q ∧ ∀ j ∈ J, ...}` 而非正文的交集记号 $\bigcap_{j \in J} U_{q,j}(\tau_j)$；全局并集采用存在量词 `{x | ∃ q, ...}` 而非 `⋃`；拟合结论直接展开为集合包含 `{x ∈ U | ...}` 而未进一步包装为第 7 章的 `InFittingBall` 谓词。在正文非空有限假设下，这些表示与正文外延等价，但桥接引理未在源码中显式给出。

---

### 二、数学正文与 Lean 实现的逐项对应关系

针对底层定理对（第 520–582 行）及 `_text` 包装定理（第 590–637 行），符号与声明的精确映射如下：

| 数学正文（[source.md](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane1-20261114-v5/attempts/AHR04/physical-1/session/work/source.md#L5-L167), [#L242-L260](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane1-20261114-v5/attempts/AHR04/physical-1/session/work/source.md#L242-L260)） | Lean 实现声明与位置 | 核验说明 |
| :--- | :--- | :--- |
| 扩展规范空间 $(\mathcal X, \mathcal G, \bot)$，有限指标集 $I$ | `{X I V : Type} {bot : X} [Fintype I]`，`d : I → X → X → ENNReal`，`hd : ∀ j, ExtendedPseudoMetric X bot (d j)`（[gauge_space.lean](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane1-20261114-v5/attempts/AHR04/physical-1/session/work/formal_oet/vol_01/ch_01_foundations/gauge_space.lean#L24-L29)） | 允许非分离规范（$x \neq y$ 时可 $d_j(x,y)=0$），仅要求 $d_j(x,\bot)=\top \iff x \neq \bot$。 |
| 目标算子 $\phi^\natural$、代理算子 $\phi \in \mathcal X_{\mathrm{op}}$ | `target proxy : Operator X bot`（[operator_space.lean](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane1-20261114-v5/attempts/AHR04/physical-1/session/work/formal_oet/vol_01/ch_01_foundations/operator_space.lean#L396-L398)） | 满足吸收元保持 `func bot = bot`。 |
| 有限算子网络 $\mathcal N$（输入域 $U$）及外延表示 $\phi_{\mathcal N} \equiv_U \phi$ | `N : FiniteOperatorNetwork X bot V`，`N.U`，`hrep : N.represents proxy`（[operator_network.lean](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane1-20261114-v5/attempts/AHR04/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/operator_network.lean#L174-L197), [#L814-L815](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane1-20261114-v5/attempts/AHR04/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/operator_network.lean#L814-L815)） | `N.source_no_bot` 保证 $\bot \notin U$；`hrep` 蕴含 $U \subseteq \mathrm{dom}(\phi)$ 且在 $U$ 上逐点相等。 |
| 可达路径族 $\mathcal P(\mathcal N)$、路径域 $U_q$、路径算子链 $c_q$ | `N.ReachablePath`、`N.path_domain q.nodes`、`N.path_chain q.nodes`（[operator_network.lean](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane1-20261114-v5/attempts/AHR04/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/operator_network.lean#L497-L498), [#L548-L558](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane1-20261114-v5/attempts/AHR04/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/operator_network.lean#L548-L558)） | $\bigcup_{q \in \mathcal P} U_q = U$ 由 `N.reachable_path_domains_cover`（第 778 行）保证。 |
| 目标算子包络证书 $(V^*, \mathbf L^*)$ 及 $U \subseteq V^*$ | `hLstar : TargetLipEnvelopeCertificate d target Vstar Lstar`（[structural_priors.lean](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane1-20261114-v5/attempts/AHR04/physical-1/session/work/formal_oet/vol_03/ch_12_residuals_and_substitution/structural_priors.lean#L25-L28)），`hpathV : ∀ q : N.ReachablePath, N.path_domain q.nodes ⊆ Vstar` | 由路径域覆盖性，$\forall q, U_q \subseteq V^*$ 与 $U \subseteq V^*$ 逻辑等价。 |
| 全局与路径可评估集 $I_{\mathrm{res}}, I_{\mathrm{res}}(q)$、路径样本 $S_{q,j} = S_j \cap U_q$ | `evaluable_components sample`（[empirical_residuals.lean](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane1-20261114-v5/attempts/AHR04/physical-1/session/work/formal_oet/vol_03/ch_12_residuals_and_substitution/empirical_residuals.lean#L35-L36)），`path_evaluable_components N sample q`、`path_component_sample N sample q j`（[path_sampling.lean](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane1-20261114-v5/attempts/AHR04/physical-1/session/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_sampling.lean#L27-L51)） | 定义逐字一致。 |
| 观测容差 $\delta_{o,j}$ 与路径经验残差上界 $\hat\varepsilon_{q,j}$ | `delta_o : I → ENNReal`，`path_empirical_residual_upper d target N sample delta_o q j`（[path_sampling.lean](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane1-20261114-v5/attempts/AHR04/physical-1/session/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_sampling.lean#L136-L142)） | 精确对应 $\sup_{x \in S_{q,j}} d_j(c_q(x), \phi^\natural(x)) + \delta_{o,j}$。 |
| 路径局部证书 $\mathbf L_q \in \mathscr L(c_q)|_{U_q}$ 与联合矩阵 $\mathbf A_q = \mathbf L_q + \mathbf L^*$ | `IsLipMatrix d (N.path_chain q.nodes) (N.path_domain q.nodes) (Lq q)`（[lip_matrix.lean](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane1-20261114-v5/attempts/AHR04/physical-1/session/work/formal_oet/vol_01/ch_02_operator_bounds/lip_matrix.lean#L21-L24)），`fun i j => Lq q i j + Lstar i j` | `matrix_vector_bound`（[distance_recurrence.lean](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane1-20261114-v5/attempts/AHR04/physical-1/session/work/formal_oet/vol_01/ch_04_operator_chain_calculus/distance_recurrence.lean#L48-L55)）按 `∑ i, A i j * v i` 求和，与正文 $A_{i \to j}$ 顺序一致。 |
| 路径单分量/联合经验保证域 $U_{q,j}(\tau_j), U_{q,J}(\boldsymbol\tau)$ | `path_component_empirical_guarantee_domain`、`path_joint_empirical_guarantee_domain`（[path_guarantee_domains.lean](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane1-20261114-v5/attempts/AHR04/physical-1/session/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L26-L46)） | 复用第 12 章 `guarantee_domains.lean`（[guarantee_domains.lean](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane1-20261114-v5/attempts/AHR04/physical-1/session/work/formal_oet/vol_03/ch_12_residuals_and_substitution/guarantee_domains.lean#L26-L42)）。 |
| 有限阈值 $\tau_j \in [0,+\infty)$、非空 $J \subseteq I_{\mathrm{res}}$ | `finite_ennreal tau_j`（即 `tau_j ≠ ⊤`，[empirical_residuals.lean](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane1-20261114-v5/attempts/AHR04/physical-1/session/work/formal_oet/vol_03/ch_12_residuals_and_substitution/empirical_residuals.lean#L26-L27)），`hJ_nonempty : J.Nonempty`，`hJ_evaluable : J ⊆ evaluable_components sample` | 出现在 `_text` 定理（第 601–605 行）中。 |
| 正文证明依赖 `@h-4b5219aa3a3bbdad` | `proxy_path_component_guarantee_error_bound`（第 152 行）、`path_joint_guarantee_error_bound`（第 210 行）及 `path_chain_eq_represented_proxy_on_path`（[path_sampling.lean](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane1-20261114-v5/attempts/AHR04/physical-1/session/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_sampling.lean#L220-L231)） | 证明结构与正文完全对应。 |

---

### 三、具体不足、可复核反例与补齐方案

#### 不足 1：`path_guarantee_union_subset_proxy_error_text` 的前提耦合导致联合结论丢失合法模型

**1. 问题定位**  
在同一文件的前置定理 `#h-4b5219aa3a3bbdad` 中，作者将正文对齐版拆分为两个独立定理：`proxy_path_component_guarantee_error_bound_text`（[path_guarantee_domains.lean](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane1-20261114-v5/attempts/AHR04/physical-1/session/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L181-L202)）与 `proxy_path_joint_guarantee_error_bound_text`（[#L276-L300](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane1-20261114-v5/attempts/AHR04/physical-1/session/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L276-L300)）。但在推论 `#h-93b9c20ea18b4e59` 中，`path_guarantee_union_subset_proxy_error_text`（[#L590-L637](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane1-20261114-v5/attempts/AHR04/physical-1/session/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L590-L637)）把两个结论合成为合取式 `... ∧ ...`，并将路径局部证书前提写为：
```lean
(hLq : ∀ q : N.ReachablePath,
  (j ∈ path_evaluable_components N sample q ∨
    J ⊆ path_evaluable_components N sample q) →
  IsLipMatrix d (N.path_chain q.nodes) (N.path_domain q.nodes) (Lq q))
```
这迫使用户在仅需**联合结论**（固定非空 $J \subseteq I_{\mathrm{res}}$）时，也必须额外挑出一个 $j \in I_{\mathrm{res}}$，并为所有满足 $j \in I_{\mathrm{res}}(q)$（即便 $J \not\subseteq I_{\mathrm{res}}(q)$）的路径提供 `IsLipMatrix` 证书。

**2. 可复核的 6 点有限反例（已在 Lean 4 中机械化验证）**  
OET 的规范空间（[gauge_space.lean](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane1-20261114-v5/attempts/AHR04/physical-1/session/work/formal_oet/vol_01/ch_01_foundations/gauge_space.lean#L24-L45)）允许非分离伪度量（不同点距离可为 $0$）：
- **空间与规范族**：令 $\mathcal X = \{\bot, a_0, a_1, b_0, b_1, c_0\}$，指标集 $I = \{0, 1\}$，$U := \mathcal X \setminus \{\bot\}$。对每个 $k \in \{0, 1\}$，令 $d_k(x, \bot) = d_k(\bot, x) = \top$（$x \neq \bot$），$d_k(\bot, \bot) = 0$；在 $U$ 上按三簇 $\{a_0, a_1\}, \{b_0, b_1\}, \{c_0\}$ 定义超度量：同簇两点距离为 $0$，异簇两点距离为 $1$。易验 $(d_0, d_1)$ 满足 `ExtendedPseudoMetric` 全部公理。
- **目标算子与包络**：令 $\phi^\natural(\bot) = \bot$，对 $x \in U$ 恒令 $\phi^\natural(x) = a_0$。取 $V^* = U$、零矩阵 $\mathbf L^* = \mathbf 0$，则 $(V^*, \mathbf L^*)$ 是合法的 `TargetLipEnvelopeCertificate`。
- **有限算子网络 $\mathcal N$ 与代理算子 $\phi$**：节点集 $V = \{0, 1, 2\}$，每步立即停机（`is_stop _ _ = true`），路由函数将 $\{a_0,a_1\} \mapsto 0$、$\{b_0,b_1\} \mapsto 1$、$\{c_0\} \mapsto 2$。于是可达路径恰有三条单节点路径 $\mathcal P(\mathcal N) = \{q_0, q_1, q_2\}$：
  - $q_0 = [0]$，$U_{q_0} = \{a_0, a_1\}$：$c_{q_0}(a_0) = a_0$，$c_{q_0}(a_1) = b_0$；
  - $q_1 = [1]$，$U_{q_1} = \{b_0, b_1\}$：$c_{q_1}(b_0) = a_0$，$c_{q_1}(b_1) = b_0$；
  - $q_2 = [2]$，$U_{q_2} = \{c_0\}$：$c_{q_2}(c_0) = a_0$。
  令 $\phi := \phi_{\mathcal N}$，则 $\phi_{\mathcal N} \equiv_U \phi$（满足 `N.represents proxy`）且 $U \subseteq \mathrm{dom}(\phi) \cap V^*$。
- **采样结构与联合指标**：令 $S = U$，$S_0 = \{a_0, c_0\}$，$S_1 = \{b_0, c_0\}$（满足 `SamplingStructure` 及 $S_k \subseteq S \cap U \cap \mathrm{dom}(\phi^\natural)$），故 $I_{\mathrm{res}} = \{0, 1\}$。取观测容差 $\delta_{o,0} = \delta_{o,1} = 0$，非空联合指标集 $J = \{0, 1\} \subseteq I_{\mathrm{res}}$，有限阈值 $\tau_0 = \tau_1 = 0$。
- **正文前提成立且保证域非空**：各路径可评估集分别为 $I_{\mathrm{res}}(q_0) = \{0\}$、$I_{\mathrm{res}}(q_1) = \{1\}$、$I_{\mathrm{res}}(q_2) = \{0, 1\}$。满足 $J \subseteq I_{\mathrm{res}}(q)$ 的路径**仅有 $q_2$**；在单点集 $U_{q_2} = \{c_0\}$ 上，$\mathbf L_{q_2} = \mathbf 0 \in \mathscr L(c_{q_2})|_{U_{q_2}}$，且 $U_{q_2, J}(\boldsymbol\tau) = \{c_0\} \neq \emptyset$，正文联合结论在 $c_0$ 处非空成立。
- **`_text` 定理彻底失效**：在 `ENNReal` 中 $\top \cdot 0 = 0$。
  - 若取 $j = 0 \in I_{\mathrm{res}}$，由于 $0 \in I_{\mathrm{res}}(q_0)$，`hLq` 要求在 $U_{q_0}$ 上存在矩阵 $\mathbf L_{q_0}$ 满足 `IsLipMatrix`。但 $d_0(a_0, a_1) = d_1(a_0, a_1) = 0$，故对**任意**矩阵 $L : I \to I \to \mathrm{ENNReal}$（即使元素取 $\top$），均有 $\sum_{i \in I} L_{i \to 0}\, d_i(a_0, a_1) = 0 < 1 = d_0(a_0, b_0) = d_0(c_{q_0}(a_0), c_{q_0}(a_1))$，即 $\mathscr L(c_{q_0})|_{U_{q_0}} = \emptyset$！
  - 若取 $j = 1 \in I_{\mathrm{res}}$，对称地有 $1 \in I_{\mathrm{res}}(q_1)$，而 $d_i(b_0, b_1) = 0 < 1 = d_0(c_{q_1}(b_0), c_{q_1}(b_1))$，故 $\mathscr L(c_{q_1})|_{U_{q_1}} = \emptyset$！
  因此不存在任何参数选取能调用 `path_guarantee_union_subset_proxy_error_text` 得出上述合法模型的联合保证结论（而未耦合的 `path_joint_guarantee_union_subset_proxy_error` 则可直接适用）。

**3. 补齐方案**  
参照第 181 行与第 276 行的做法，将 `_text` 定理拆分为两个解耦定理（若需向后兼容可保留原定理作为推论）：
- `path_component_guarantee_union_subset_proxy_error_text`：仅量化 `(j : I)` 与 `(tau_j : ENNReal)`，`hLq` 仅要求 `j ∈ path_evaluable_components N sample q → IsLipMatrix ...`，直接调用 `path_component_guarantee_union_subset_proxy_error`；
- `path_joint_guarantee_union_subset_proxy_error_text`：仅量化 `(J : Set I)` 与 `(tau : I → ENNReal)`，`hLq` 仅要求 `J ⊆ path_evaluable_components N sample q → IsLipMatrix ...`，直接调用 `path_joint_guarantee_union_subset_proxy_error`。

---

#### 不足 2：集合记号编码与全局拟合球谓词的表述落差

1. **$U_{q,J}(\boldsymbol\tau)$ 的交集定义 vs. 全称概括定义**：
   - 正文（[source.md](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane1-20261114-v5/attempts/AHR04/physical-1/session/work/source.md#L110-L116)）对非空 $J$ 定义 $U_{q,J}(\boldsymbol\tau) := \bigcap_{j \in J} U_{q,j}(\tau_j)$；Lean（[path_guarantee_domains.lean](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane1-20261114-v5/attempts/AHR04/physical-1/session/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L39-L46)）定义为 `{x | x ∈ N.path_domain q.nodes ∧ ∀ j ∈ J, ... ≤ tau j}`。
   - *原因与差异*：在 Lean 的 `Set X` 中，当 $J = \emptyset$ 时，`⋂ j ∈ ∅, U_{q,j}(τ_j) = Set.univ`，其中包含吸收元 `bot ∉ N.U`，会导致省略 `J.Nonempty` 的第 553 行定理不成立；因此源码采用概括式是有意为之的安全编码。在正文的 `hJ_nonempty : J.Nonempty` 假设下，两者外延恒等。
   - *补齐方式*：补充桥接引理，证明在 `hJ : J.Nonempty` 下 `path_joint_empirical_guarantee_domain ... = ⋂ j ∈ J, path_component_empirical_guarantee_domain ...`。
2. **存在量词并集 vs. 指标并集 `⋃`，以及全函数参数化**：
   - 源码用 `{x | ∃ q : N.ReachablePath, P q ∧ x ∈ ...}` 表示 $\bigcup_{q \in \mathcal P, P(q)} (\cdots)$，可通过 `Set.ext` 与 `Set.mem_iUnion₂` 一步互转；`tau : I → ENNReal` 与 `Lq : N.ReachablePath → I → I → ENNReal` 定义为全函数而非子类型函数，由于 `ENNReal` 非空（含 `0`）且定理从未读取作用域外的指标，不损失任何一般性。
3. **正文标题“全局拟合含义”与第 7 章 `InFittingBall` 的衔接**：
   - 正文结论以显式集合包含给出，同时标题指向代理算子在并集域上的全局拟合保证。第 7 章已在 [fitting_ball.lean](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane1-20261114-v5/attempts/AHR04/physical-1/session/work/formal_oet/vol_02/ch_07_fitting_foundations/fitting_ball.lean#L35-L41) 定义了 `InFittingBall d target proxy U J eps`（要求 `U ⊆ dom target`、`U ⊆ dom proxy`、`∀ j ∈ J, eps j ≠ ⊤` 及 `d j (target.func x) (proxy.func x) ≤ eps j`）。
   - *补齐方式*：结合 `hrep`（蕴含 `N.U ⊆ dom proxy`）、`hpathV` + `hLstar.lip_matrix.1`（蕴含 `N.U ⊆ dom target`）、`(hd j).symm`（对称性转换 `proxy`/`target` 顺序）及 `htau_finite`，即可将联合并集结论直接升级为 `InFittingBall d target proxy union_domain J tau`。

---

### 四、源码已证明的结论与需自行补充的内容区分

#### 1. 源码中已完整证明的结论（零未证假设）
- **局部误差上界基底**（[path_guarantee_domains.lean](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane1-20261114-v5/attempts/AHR04/physical-1/session/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L54-L300)）：在单条可达路径 $q$ 上，由 $x \in U_{q,j}(\tau_j)$（或 $U_{q,J}(\boldsymbol\tau)$）及 $\phi_{\mathcal N} \equiv_U \phi$ 推出 $x \in U_q \subseteq U$ 且 $d_j(\phi(x), \phi^\natural(x)) \le \tau_j$（定理 `proxy_path_component_guarantee_error_bound` 等）。
- **单分量全局并集包含定理** `path_component_guarantee_union_subset_proxy_error`（[#L520-L545](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane1-20261114-v5/attempts/AHR04/physical-1/session/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L520-L545)）：对任意 $j \in I$ 和任意 $\tau_j \in [0, +\infty]$，只要满足 $j \in I_{\mathrm{res}}(q)$ 的路径具有局部证书 $\mathbf L_q$，就有 $\{x \mid \exists q,\ j \in I_{\mathrm{res}}(q) \land x \in U_{q,j}(\tau_j)\} \subseteq \{x \in U \mid d_j(\phi(x), \phi^\natural(x)) \le \tau_j\}$。
- **分量族全局并集包含定理** `path_joint_guarantee_union_subset_proxy_error`（[#L553-L582](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane1-20261114-v5/attempts/AHR04/physical-1/session/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L553-L582)）：对任意 $J \subseteq I$ 和任意 $\boldsymbol\tau : I \to [0, +\infty]$，只要满足 $J \subseteq I_{\mathrm{res}}(q)$ 的路径具有局部证书 $\mathbf L_q$，就有 $\{x \mid \exists q,\ J \subseteq I_{\mathrm{res}}(q) \land x \in U_{q,J}(\boldsymbol\tau)\} \subseteq \{x \in U \mid \forall j \in J,\ d_j(\phi(x), \phi^\natural(x)) \le \tau_j\}$。
- **耦合版正文包装定理** `path_guarantee_union_subset_proxy_error_text`（[#L590-L637](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane1-20261114-v5/attempts/AHR04/physical-1/session/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L590-L637)）：在耦合的 `hLq` 前提下联合导出上述两条包含关系。
- **路径覆盖与代理一致辅助性质**：`reachable_path_domains_cover`（[operator_network.lean](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane1-20261114-v5/attempts/AHR04/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/operator_network.lean#L778-L785)）与 `path_chain_eq_represented_proxy_on_path`（[path_sampling.lean](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane1-20261114-v5/attempts/AHR04/physical-1/session/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_sampling.lean#L220-L231)）。

#### 2. 需调用方或后续形式化自行补充的内容
- **解耦的 `_text` 级单分量/联合包装定理**：若需在保留正文显式有限性/可评估性前提的同时避免不足 1 中的 `hLq` 耦合，需分别对 `path_component_guarantee_union_subset_proxy_error` 与 `path_joint_guarantee_union_subset_proxy_error` 建立独立包装。
- **集合运算记号桥接引理**：
  1. 在 `J.Nonempty` 下将 `path_joint_empirical_guarantee_domain` 改写为双指标交集 `⋂ j ∈ J, path_component_empirical_guarantee_domain ...`；
  2. 将存在量词集合 `{x | ∃ q, ...}` 改写为 `⋃ q, ⋃ (_ : ...), ...`；
  3. 将前提 `N.U ⊆ Vstar` 改写为源码使用的 `∀ q : N.ReachablePath, N.path_domain q.nodes ⊆ Vstar`（利用 `N.path_domain_subset_source`）。
- **有效域非退化与 `InFittingBall` 拟合球判定导出**：若下游定理需要显式的 `x ∈ dom proxy ∩ dom target`（非 $\bot$ 吸收证明）或第 7 章的 `InFittingBall d target proxy ...` 谓词，需结合 `N.dom_extensional_operator_eq`（[operator_network.lean](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane1-20261114-v5/attempts/AHR04/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/operator_network.lean#L344-L353)）、`hLstar.lip_matrix.1` 及 `(hd j).symm` 补充十余行常规推导。
- **具体应用实例的证书与非空性验证**：定理本身是条件性的包含关系（当 $\tau_j < \hat\varepsilon_{q,j}$ 时 $U_{q,j}(\tau_j) = \emptyset$，包含关系平凡成立）；在实际网络拟合任务中，目标包络证书 `(Vstar, Lstar)`、各路径局部 Lipschitz 矩阵 `Lq q`、满足 `SamplingStructure` 的样本集以及使保证域非空的阈值裕度 $\tau_j \ge \hat\varepsilon_{q,j}$，均须由用户针对具体算子网络另行构造与证明。

---

*来源说明：本审阅所涉数学正文与 Lean 4 形式化源码均引自 Zhe Li（Glen Li / glenzli）所著《The Operator Evolution Theory》（https://glenzli.com/books/oet/ ，参见工作区 [ATTRIBUTION.md](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane1-20261114-v5/attempts/AHR04/physical-1/session/work/ATTRIBUTION.md#L1-L4) 与 [LICENSE](file:///private/tmp/math-gauge-carbon-medium-parallel2-lane1-20261114-v5/attempts/AHR04/physical-1/session/work/LICENSE#L1-L7)，遵循 CC BY 4.0 许可协议）；原始附件与源码均未作任何修改。*
