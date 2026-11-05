{}
### 审阅结论

**审阅判断**：附件中的 Lean 实现**准确且完整地覆盖**了数学正文中的“**推论 #h-93b9c20ea18b4e59（路径保证域的全局拟合含义）**”（包括分量形式与联合形式）。

源码实现无未证明公理或 `sorry`，类型检查完全闭合（仅依赖 Lean 4 标准公理 `[propext, Classical.choice, Quot.sound]`），且结构严密。

---

### 一、 数学命题与 Lean 实现的对应关系

数学正文中的推论表述如下：
> **推论 #h-93b9c20ea18b4e59（路径保证域的全局拟合含义）**：
> 1. 对任意 $j \in I_{\mathrm{res}}$ 与有限阈值 $\tau_j$，
>    $$\bigcup_{\substack{q\in\mathcal P\\ j\in I_{\mathrm{res}}(q)}}U_{q,j}(\tau_j) \subseteq \{x\in U : d_j(\phi(x),\phi^\natural(x))\leq\tau_j\}$$
> 2. 对给定非空分量族 $J \subseteq I_{\mathrm{res}}$，
>    $$\bigcup_{\substack{q\in\mathcal P\\ J\subseteq I_{\mathrm{res}}(q)}} U_{q,J}(\boldsymbol\tau) \subseteq \{x\in U : \forall j\in J,\ d_j(\phi(x),\phi^\natural(x))\leq\tau_j\}$$

在文件 [`path_guarantee_domains.lean`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR02-A1/1/input/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean) 中，对应关系如下：

| 数学正文对象 / 符号 | 含义说明 | Lean 源码实现及对应符号 | 所在源文件与位置 |
| :--- | :--- | :--- | :--- |
| $(\mathcal X, \mathcal G, \bot), I$ | 扩展规范空间与有限指标集 | `{X I V : Type} {bot : X} [Fintype I]`, `d`, `hd : ∀ j, ExtendedPseudoMetric X bot (d j)` | [`gauge_space.lean`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR02-A1/1/input/formal_oet/vol_01/ch_01_foundations/gauge_space.lean) |
| $\phi, \phi^\natural$ | 代理算子与目标算子 | `proxy target : Operator X bot` | [`operator_space.lean`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR02-A1/1/input/formal_oet/vol_01/ch_01_foundations/operator_space.lean) |
| $\mathcal N, U, \phi_{\mathcal N} \equiv_U \phi$ | 代理算子的网络表示 | `N : FiniteOperatorNetwork X bot V`, `N.U`, `hrep : N.represents proxy` | [`operator_network.lean`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR02-A1/1/input/formal_oet/vol_01/ch_05_operator_networks/operator_network.lean#L814) |
| $\mathcal P, q, U_q$ | 网络路径族与路径域 | `N.ReachablePath`, `q.nodes`, `N.path_domain q.nodes` | [`operator_network.lean`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR02-A1/1/input/formal_oet/vol_01/ch_05_operator_networks/operator_network.lean#L556) |
| $(V^*, \mathbf L^*), U \subseteq V^*$ | 目标 Lip 包络证书 | `TargetLipEnvelopeCertificate d target Vstar Lstar`, `hpathV : ∀ q, N.path_domain q.nodes ⊆ Vstar` | [`structural_priors.lean`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR02-A1/1/input/formal_oet/vol_03/ch_12_residuals_and_substitution/structural_priors.lean) |
| $c_q, \mathbf L_q \in \mathscr L(c_q)\vert_{U_q}$ | 路径链及其受限 Lip 证书 | `N.path_chain q.nodes`, `hLq : ∀ q, IsLipMatrix d (N.path_chain q.nodes) (N.path_domain q.nodes) (Lq q)` | [`lip_matrix.lean`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR02-A1/1/input/formal_oet/vol_01/ch_02_operator_bounds/lip_matrix.lean#L22) |
| $S_{q,j} = S_j \cap U_q$ | 路径局部采样集 | [`path_component_sample N sample q j`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR02-A1/1/input/formal_oet/vol_03/ch_14_empirical_network_fitting/path_sampling.lean#L25-L30) | [`path_sampling.lean`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR02-A1/1/input/formal_oet/vol_03/ch_14_empirical_network_fitting/path_sampling.lean#L25) |
| $j \in I_{\mathrm{res}}(q)$ | 路径可评估分量 | `j ∈ path_evaluable_components N sample q` | [`path_sampling.lean`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR02-A1/1/input/formal_oet/vol_03/ch_14_empirical_network_fitting/path_sampling.lean#L47) |
| $\hat\varepsilon_{q,j}$ | 路径级经验残差上界 | [`path_empirical_residual_upper d target N sample delta_o q j`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR02-A1/1/input/formal_oet/vol_03/ch_14_empirical_network_fitting/path_sampling.lean#L106-L113) | [`path_sampling.lean`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR02-A1/1/input/formal_oet/vol_03/ch_14_empirical_network_fitting/path_sampling.lean#L106) |
| $\mathbf A_q = \mathbf L_q + \mathbf L^*$ | 路径共同锚点权矩阵 | `fun i j => Lq q i j + Lstar i j` | [`path_guarantee_domains.lean`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR02-A1/1/input/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L26) |
| $U_{q,j}(\tau_j)$ | 路径分量经验保证域 | [`path_component_empirical_guarantee_domain`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR02-A1/1/input/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L26-L34) | [`path_guarantee_domains.lean`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR02-A1/1/input/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L26) |
| $U_{q,J}(\boldsymbol\tau)$ | 路径联合经验保证域 | [`path_joint_empirical_guarantee_domain`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR02-A1/1/input/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L39-L48) | [`path_guarantee_domains.lean`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR02-A1/1/input/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L39) |
| **结论 (1)：分量形式包含** | $\bigcup_{q, j\in I_{\mathrm{res}}(q)} U_{q,j}(\tau_j) \subseteq \{x\in U : d_j(\phi(x),\phi^\natural(x))\leq\tau_j\}$ | [`path_component_guarantee_union_subset_proxy_error`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR02-A1/1/input/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L520-L546) | [`path_guarantee_domains.lean`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR02-A1/1/input/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L520) |
| **结论 (2)：联合形式包含** | $\bigcup_{q, J\subseteq I_{\mathrm{res}}(q)} U_{q,J}(\boldsymbol\tau) \subseteq \{x\in U : \forall j\in J, d_j(\phi(x),\phi^\natural(x))\leq\tau_j\}$ | [`path_joint_guarantee_union_subset_proxy_error`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR02-A1/1/input/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L552-L582) | [`path_guarantee_domains.lean`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR02-A1/1/input/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L552) |
| **正文推论综合打包** | 正文完整同形封装（合取） | [`path_guarantee_union_subset_proxy_error_text`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR02-A1/1/input/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L588-L633) | [`path_guarantee_domains.lean`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR02-A1/1/input/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L588) |

---

### 二、 源码已证明的结论与支撑推导链条

源码中以下定理已完成机器证明，无任何证明缺口：

1. **路径局部经验上界定理**（对应正文命题 @h-4b5219aa3a3bbdad）：
   - [`path_local_empirical_upper`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR02-A1/1/input/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L54-L86)：证明在每条路径 $q$ 的局部域 $U_q$ 上，路径链 $c_q$ 与目标算子偏差受共同锚点距离与路径经验残差控制。
   - [`path_chain_eq_represented_proxy_on_path`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR02-A1/1/input/formal_oet/vol_03/ch_14_empirical_network_fitting/path_sampling.lean#L169-L180)：证明当网络 $\mathcal N$ 表示 $\phi$ 时，在 $U_q$ 上满足 $c_q(x) = \phi(x)$。
   - [`proxy_path_local_empirical_upper`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR02-A1/1/input/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L92-L116)：将上述上界由路径链逐点精确转至代理算子自身：
     $$d_j(\phi(x), \phi^\natural(x)) \le D_{\mathbf A_q, j}(x; S_{q,j}) + \hat\varepsilon_{q,j}$$

2. **单路径保证域误差控制**：
   - [`proxy_path_component_guarantee_error_bound`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR02-A1/1/input/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L152-L175)：证明 $x \in U_{q,j}(\tau_j) \implies d_j(\phi(x), \phi^\natural(x)) \le \tau_j$。
   - [`proxy_path_joint_guarantee_error_bound`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR02-A1/1/input/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L244-L270)：证明 $x \in U_{q,J}(\boldsymbol\tau) \implies \forall j \in J, d_j(\phi(x), \phi^\natural(x)) \le \tau_j$。

3. **全局拟合含义的并集包含关系**：
   - [`path_component_guarantee_union_subset_proxy_error`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR02-A1/1/input/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L520-L546) 与 [`path_joint_guarantee_union_subset_proxy_error`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR02-A1/1/input/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L552-L582)：解构左侧并集后，由局部所属路径 $q$ 的包含关系导出 $x \in N.U$（利用 `N.path_domain_subset_source`），并合成全局容许域包含。
   - [`path_guarantee_union_subset_proxy_error_text`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR02-A1/1/input/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L588-L633)：将分量结论与联合结论合取，保留全部正文假设作为正文同形终态。

---

### 三、 需自行补充与审阅说明的内容

在将数学正文书写习惯与形式化 Lean 代码对比时，存在 4 点概念与记号层面的映射桥梁，需由审阅者自行补充厘清：

1. **并集表示算子（$\bigcup$ 与谓词内包 `{x | ∃ q, ...}`）的等价性**：
   - **正文记号**：使用集合族大并集 $\bigcup_{q\in\mathcal P, j\in I_{\mathrm{res}}(q)} U_{q,j}(\tau_j)$。
   - **Lean 表示**：使用特征谓词内包 `{x | ∃ q : N.ReachablePath, j ∈ path_evaluable_components N sample q ∧ x ∈ ...}`。
   - **补充说明**：在 Mathlib 集合论语义下，二者完全等价。由 `Set.mem_iUnion` 可直接在 `⋃ (q) (_ : j ∈ ...), U_{q,j}` 与谓词内包之间通过 `rfl` 或 `simp only [Set.mem_iUnion]` 双向改写。

2. **路径指标范围（全路径 $\mathcal P$ 与可达路径 `ReachablePath`）的等价性**：
   - **正文记号**：下标写为 $q \in \mathcal P$。
   - **Lean 限制**：量词限制在可达路径 `q : N.ReachablePath`（即满足 $(U_q).\mathrm{Nonempty}$）。
   - **补充论证**：对于不可达路径 $q' \in \mathcal P \setminus \mathcal P_{\mathrm{reach}}$，其路径域 $U_{q'} = \emptyset$。因此其局部采样集 $S_{q',j} = S_j \cap U_{q'} = \emptyset$，从而不可能满足 $j \in I_{\mathrm{res}}(q')$（定义要求 $S_{q',j} \neq \emptyset$）；同时其保证域 $U_{q',j}(\tau_j) \subseteq U_{q'} = \emptyset$ 必为空集。因此不可达路径对并集的贡献严格为 $\emptyset$，全路径并集与可达路径并集完全相同。

3. **目标包络包含条件（全局 $U \subseteq V^*$ 与逐路径 `hpathV`）的等价性**：
   - **正文前提**：正文第 14.1 节全局设定为 $U \subseteq V^*$。
   - **Lean 前提**：定理入参要求 `hpathV : ∀ q : N.ReachablePath, N.path_domain q.nodes ⊆ Vstar`。
   - **补充论证**：在 [`operator_network.lean`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR02-A1/1/input/formal_oet/vol_01/ch_05_operator_networks/operator_network.lean#L778-L789) 中，已证明定理 [`reachable_path_domains_cover`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR02-A1/1/input/formal_oet/vol_01/ch_05_operator_networks/operator_network.lean#L778)：$\bigcup_{q \in \mathcal P_{\mathrm{reach}}} U_q = N.U$。故 $\forall q, U_q \subseteq V^* \iff (\bigcup_q U_q) \subseteq V^* \iff U \subseteq V^*$。若已知全局条件 $hU : N.U \subseteq V^*$，则由 `fun q x hx => hU (N.path_domain_subset_source hx)` 即可瞬间补齐 `hpathV`。

4. **联合保证域的有限交集与逐分量全称命题一致性**：
   - **正文定义**：$U_{q,J}(\boldsymbol\tau) = \bigcap_{j \in J} U_{q,j}(\tau_j)$。
   - **Lean 定义**：[`path_joint_empirical_guarantee_domain`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR02-A1/1/input/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L39) 通过 `empirical_joint_guarantee_domain` 展开为：
     $$\{x \in U_q \mid \forall j \in J, D_{\mathbf A_q, j}(x; S_{q,j}) + \hat\varepsilon_{q,j} \le \tau_j\}$$
   - **补充说明**：这与有限交集定义在外延上完全重合（即 $x \in \bigcap_{j\in J} U_{q,j}(\tau_j) \iff x \in U_q \wedge \forall j \in J, x \in U_{q,j}(\tau_j)$）。

5. **阈值有限性前提在代数层面的弱化**：
   - 正文设定 $\tau_j < +\infty$；而在 `ENNReal` 代数系统中，即使 $\tau_j = \top$，不等式 $d_j \le \top$ 亦恒真。底层模块化定理 [`path_component_guarantee_union_subset_proxy_error`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR02-A1/1/input/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L520) 无需有限性假设即可成立，而同形定理 [`path_guarantee_union_subset_proxy_error_text`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR02-A1/1/input/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L588) 完整保留了正文的有限性前提，兼具代数通用性与正文同形性。
