### 结论判定

所给 Lean 实现**准确且完整**地覆盖了数学正文中的**推论 #h-93b9c20ea18b4e59（路径保证域的全局拟合含义）**。

源码不仅分别给出了单分量分支与联合分量分支的精确形式化证明，还提供了严格保留正文所有前置前提的同形包装定理，代码已通过 Lean 4.29.1 完整类型检查，无任何 `sorry` 或未证明公理。

---

### 一、 数学命题与 Lean 实现的精确对应关系

数学正文推论在 [source.md](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR04-A1/1/input/source.md#L242-L260) 中表述为：
1. **单分量形式**：对任意 $j \in I_{\mathrm{res}}$ 与有限阈值 $\tau_j \in [0, +\infty)$，
   $$\bigcup_{\substack{q\in\mathcal P\\ j\in I_{\mathrm{res}}(q)}} U_{q,j}(\tau_j) \subseteq \{x\in U : d_j(\phi(x),\phi^\natural(x))\leq\tau_j\}$$
2. **联合分量形式**：对给定非空分量族 $J \subseteq I_{\mathrm{res}}$ 与有限阈值族 $\boldsymbol\tau = (\tau_j)_{j\in J}$，
   $$\bigcup_{\substack{q\in\mathcal P\\ J\subseteq I_{\mathrm{res}}(q)}} U_{q,J}(\boldsymbol\tau) \subseteq \{x\in U : \forall j\in J,\ d_j(\phi(x),\phi^\natural(x))\leq\tau_j\}$$

在 [path_guarantee_domains.lean](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR04-A1/1/input/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean) 中，各数学实体与定理的对应映射如下表所示：

| 数学正文实体 / 命题 | Lean 实现 / 源码标识符 | 所在位置与语义对照 |
| :--- | :--- | :--- |
| 扩展规范度量族 $d_i$ 与指标集 $I$ | `(d : I → X → X → ENNReal)`, `(hd : ∀ j, ExtendedPseudoMetric X bot (d j))`, `[Fintype I]` | 规范空间公理与有限指标族 |
| 目标算子 $\phi^\natural$ 与代理算子 $\phi$ | `(target proxy : Operator X bot)` | [`Operator`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR04-A1/1/input/formal_oet/vol_01/ch_01_foundations/operator_space.lean#L16-L19) 算子空间对象 |
| 代理算子网络 $\mathcal N$ 及其输入域 $U$ | `(N : FiniteOperatorNetwork X bot V)` | `N.U` 对应正文全域 $U$ |
| 网络表示条件 $\phi_{\mathcal N} \equiv_U \phi$ | `(hrep : N.represents proxy)` | 即 `LocalEquivalent N.extensional_operator proxy N.U` |
| 代理网络可达路径集 $\mathcal P(\mathcal N)$ | `(q : N.ReachablePath)` | `{p // ∃ x ∈ N.U, N.path_of ⟨x, ...⟩ = p}` |
| 路径域 $U_q$ 与路径链 $c_q$ | `N.path_domain q.nodes`, `N.path_chain q.nodes` | 路径节点序列对应的局域与算子复合链 |
| 目标 Lip 包络 $(V^*, \mathbf L^*)$ 及 $U \subseteq V^*$ | `(Vstar : Set X)`, `(Lstar : I → I → ENNReal)`, `(hLstar : TargetLipEnvelopeCertificate ...)`, `(hpathV : ∀ q, N.path_domain q.nodes ⊆ Vstar)` | 全局包含 $U \subseteq V^*$ 等价表示为逐路径域包含 |
| 采样族 $\mathcal S$ 与可评估集 $I_{\mathrm{res}}$ | `(sample : I → Set X)`, `evaluable_components sample` | $I_{\mathrm{res}} = \{j \in I : S_j \neq \emptyset\}$ |
| 路径采样 $S_{q,j}$ 与可评估集 $I_{\mathrm{res}}(q)$ | [`path_component_sample`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR04-A1/1/input/formal_oet/vol_03/ch_14_empirical_network_fitting/path_sampling.lean#L25-L29), [`path_evaluable_components`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR04-A1/1/input/formal_oet/vol_03/ch_14_empirical_network_fitting/path_sampling.lean#L42-L46) | $S_{q,j} = S_j \cap U_q$，$I_{\mathrm{res}}(q) = \{j : S_{q,j} \neq \emptyset\}$ |
| 路径残差 $\hat\varepsilon_{q,j}$ 与矩阵 $\mathbf A_q = \mathbf L_q + \mathbf L^*$ | [`path_empirical_residual_upper`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR04-A1/1/input/formal_oet/vol_03/ch_14_empirical_network_fitting/path_sampling.lean#L133-L141), `(fun i j => Lq q i j + Lstar i j)` | 采样点偏差上界加上分辨修正 $\delta_{o,j}$ |
| 路径分量保证域 $U_{q,j}(\tau_j)$ | [`path_component_empirical_guarantee_domain`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR04-A1/1/input/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L26-L32) | $D_{\mathbf A_q,j}(x; S_{q,j}) + \hat\varepsilon_{q,j} \le \tau_j$ |
| 路径联合保证域 $U_{q,J}(\boldsymbol\tau)$ | [`path_joint_empirical_guarantee_domain`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR04-A1/1/input/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L39-L46) | $\bigcap_{j\in J} U_{q,j}(\tau_j)$ |
| **单分量包含结论** | [`path_component_guarantee_union_subset_proxy_error`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR04-A1/1/input/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L520-L551) | 严格证明单分量并集包含关系 |
| **联合分量包含结论** | [`path_joint_guarantee_union_subset_proxy_error`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR04-A1/1/input/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L553-L588) | 严格证明联合分量并集包含关系 |
| **正文同形封装定理** | [`path_guarantee_union_subset_proxy_error_text`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR04-A1/1/input/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L590-L637) | 以合取形式 $A \wedge B$ 完整封装正文表述及全部上下文约束 |

---

### 二、 源码已证明的结论

在 [path_guarantee_domains.lean](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR04-A1/1/input/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean) 及依赖文件中，源码已由 Lean 机器核严格验证了以下结论：

1. **单分量并集包含定理** ([`path_component_guarantee_union_subset_proxy_error`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR04-A1/1/input/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L520-L551))：
   对满足前提的代理算子与网络，
   $$\{x \mid \exists q, j \in I_{\mathrm{res}}(q) \wedge x \in U_{q,j}(\tau)\} \subseteq \{x \mid x \in U \wedge d_j(\phi(x), \phi^\natural(x)) \leq \tau\}$$
2. **联合分量并集包含定理** ([`path_joint_guarantee_union_subset_proxy_error`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR04-A1/1/input/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L553-L588))：
   $$\{x \mid \exists q, J \subseteq I_{\mathrm{res}}(q) \wedge x \in U_{q,J}(\boldsymbol\tau)\} \subseteq \{x \mid x \in U \wedge \forall j \in J, d_j(\phi(x), \phi^\natural(x)) \leq \tau_j\}$$
3. **正文完整上下文同形定理** ([`path_guarantee_union_subset_proxy_error_text`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR04-A1/1/input/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L590-L637))：
   将上述两分支作为合取的两个支项组合，并将正文前提（如 $j \in I_{\mathrm{res}}$、$\tau_j < \infty$、$J \neq \emptyset$、$J \subseteq I_{\mathrm{res}}$ 等）以显式假设形式完整对齐。
4. **底层定理与传递链条**：
   - 路径链局部误差控制：[`path_component_guarantee_error_bound`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR04-A1/1/input/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L122-L149) 与 [`path_joint_guarantee_error_bound`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR04-A1/1/input/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L210-L241)。
   - 代理算子等价代换：由 [`path_chain_eq_represented_proxy_on_path`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR04-A1/1/input/formal_oet/vol_03/ch_14_empirical_network_fitting/path_sampling.lean#L220-L232) 证明在 $U_q$ 上 $(c_q)(x) = \phi(x)$，将局部链结论传递至代理算子自身 ([`proxy_path_component_guarantee_error_bound`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR04-A1/1/input/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L152-L179))。
   - 全域包含保全：由 [`FiniteOperatorNetwork.path_domain_subset_source`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR04-A1/1/input/formal_oet/vol_01/ch_05_operator_networks/operator_network.lean#L1637-L1639) 证明 $U_q \subseteq U$。

---

### 三、 审阅需自行补充的说明与论证

虽然源码中已经完成了形式化证明，但在将数学正文语言对照到交互式定理证明代码时，需要审阅者补充以下四个关键论证与理解：

1. **数学族并集与类型论集合推导式（Set Comprehension）的等价性**：
   - 数学文本书写为指标约束并集 $\bigcup_{q\in\mathcal P, j\in I_{\mathrm{res}}(q)} U_{q,j}(\tau_j)$；
   - Lean 中将可达路径定义为子类型 `N.ReachablePath`，并采用谓词构建集合：
     $$\{x \mid \exists q : N.\mathrm{ReachablePath},\ j \in I_{\mathrm{res}}(q) \wedge x \in U_{q,j}(\tau_j)\}$$
   - **补充论证**：由集合论的外延公理与一阶逻辑基本等价律，$x \in \bigcup_{i \in A} B_i \iff \exists i \in A, x \in B_i$；将指标从属于子集条件转化为逻辑合取谓词，二者在外延意义下严格等价，完全覆盖数学正文含义。
2. **包络包含条件 $U \subseteq V^*$ 的局部等价转化**：
   - 正文前置设定 $U \subseteq \mathrm{dom}(\phi) \cap V^*$；Lean 假设为 `hpathV : ∀ q : N.ReachablePath, N.path_domain q.nodes ⊆ Vstar`。
   - **补充论证**：由代理网络的路径划分性质（[`mem_path_domain_reachable_path_at`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR04-A1/1/input/formal_oet/vol_03/ch_14_empirical_network_fitting/path_sampling.lean#L118-L123)），网络全域恰由所有可达路径域覆盖，即 $U = \bigcup_{q\in\mathcal P} U_q$。因此 $U \subseteq V^* \iff \forall q \in \mathcal P, U_q \subseteq V^*$。Lean 采用逐路径假定使引理调用直接解耦，在逻辑上完全等价。
3. **阈值与采样前提的泛化性（弱化前提分析）**：
   - 正文文本中提及“有限阈值 $\tau_j$”和“非空分量族 $J \subseteq I_{\mathrm{res}}$”。
   - **补充分析**：在核心定理 [`path_component_guarantee_union_subset_proxy_error`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR04-A1/1/input/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L520-L551) 中，Lean 源码实际上弱化了这些限制：
     - 当 $\tau_j = \top$ 时，$d_j(\dots) \leq \top$ 恒真；
     - 当 $j \notin I_{\mathrm{res}}$ 时，由 [`path_evaluable_subset_evaluable_components`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR04-A1/1/input/formal_oet/vol_03/ch_14_empirical_network_fitting/path_sampling.lean#L99-L106)，不存在使 $j \in I_{\mathrm{res}}(q)$ 的路径 $q$，左端并集为空集 $\emptyset \subseteq \{x \dots\}$ 显然成立；
     - 包装定理 [`path_guarantee_union_subset_proxy_error_text`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR04-A1/1/input/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L590-L637) 保留了这些显式前提，满足正文的阅读直觉，而核心定理在数学上比正文文本更加普适。
4. **单分量向联合形式的推导闭合性**：
   - 正文证明注记为：“对所有 $j\in J$ 同时应用即可”。
   - **补充分析**：在形式化实现中，联合保证域定义并非机械调用单分量定理，而是通过统一的 [`empirical_joint_guarantee_domain`](file:///private/tmp/math-gauge-v06-native-supplement-20261104-01a1a43a/gemini/sessions/AHR04-A1/1/input/formal_oet/vol_03/ch_12_residuals_and_substitution/guarantee_domains.lean#L39-L46) 将加权锚点距离不等式与全称量化合取（`∀ j : I, j ∈ J → ...`）结合。在进入特定路径后，逐点代入并利用 `path_chain_eq_represented_proxy_on_path`，严格遵循了正文“同时应用单分量局部上界”的思路。

### 总结

该实现不仅准确还原了推论 #h-93b9c20ea18b4e59 的数学内涵与两分支结构，且其证明完全闭环，依赖链条完备无误。
