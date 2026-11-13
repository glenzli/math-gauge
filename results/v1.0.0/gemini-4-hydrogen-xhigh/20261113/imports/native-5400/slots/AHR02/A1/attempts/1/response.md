{}
### 总体结论

Lean 实现（[path_guarantee_domains.lean](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR02/physical-2/session/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L514-L632)）已无 `sorry`/`axiom` 地形式化了 [source.md](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR02/physical-2/session/work/source.md#L242-L259) 中**推论 `#h-93b9c20ea18b4e59`（路径保证域的全局拟合含义）** 的三条定理，但其当前实现**在逻辑覆盖上准确度与完整性存在明确缺口**：

1. **主要缺陷（前提过度加强导致适用性损失）**：三条定理均把路径受限 Lip 矩阵假设 `hLq` 写成对**所有可达路径** `∀ q : N.ReachablePath` 成立，而数学正文仅在并集所涉及的活跃路径（$j \in I_{\mathrm{res}}(q)$ 或 $J \subseteq I_{\mathrm{res}}(q)$）上取 $\mathbf L_q \in \mathscr L(c_q)|_{U_q}$。存在满足正文全部前提（包括非分离伪度量、`SamplingStructure`、$U \subseteq \mathrm{dom}(\phi) \cap V^*$ 与活跃路径 Lip 证书）的有限网络反例，使其在某条未采样路径上不存在任何 `IsLipMatrix`，从而**无法套用源码中的三条 Lean 定理**。
2. **结构耦合与隐式桥接缺失（需自行补充）**：
   - `path_joint_empirical_guarantee_domain` 的 Lean 定义并非正文中的有限非空交 $\bigcap_{j \in J} U_{q,j}(\tau_j)$，源码未证二者在 `J.Nonempty` 下相等的桥接引理（也说明了正文要求 $J$ 非空的必要性：若 $J = \emptyset$，按集合交定义将退化为 `Set.univ ⊈ U`）。
   - `hrep : N.represents proxy` 与 `hpathV` 蕴含正文前提 $U \subseteq \mathrm{dom}(\phi) \cap V^*$，但源码未显式给出这两条等价/蕴含桥接引理。
   - `_text` 包装定理将单分量（`j`）与联合（`J`）两个独立全称结论捆绑在同一签名与同一 `hLq` 下，放松 `hLq` 后二者应拆分为两个独立 `_text` 定理。

---

### 一、数学命题与 Lean 实现的对应关系

| 正文概念 / 命题（[source.md](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR02/physical-2/session/work/source.md#L7-L259)） | Lean 对应对象与位置 | 核验评价 |
| --- | --- | --- |
| 扩展规范空间 $(\mathcal X, \mathcal G, \bot)$、有限 $I$ | `hd : ∀ j : I, ExtendedPseudoMetric X bot (d j)`，[Fintype I](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR02/physical-2/session/work/formal_oet/vol_01/ch_01_foundations/gauge_space.lean#L16-L20) | 准确覆盖 |
| 有限网络 $\mathcal N$、表示 $\phi_{\mathcal N} \equiv_U \phi$ | `N : FiniteOperatorNetwork X bot V`、`hrep : N.represents proxy`（[operator_network.lean](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR02/physical-2/session/work/formal_oet/vol_01/ch_05_operator_networks/operator_network.lean#L174-L196), [L814-L815](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR02/physical-2/session/work/formal_oet/vol_01/ch_05_operator_networks/operator_network.lean#L814-L815)） | 准确覆盖；`U ⊆ dom proxy` 隐含于 `hrep` 与 `dom_extensional_operator_eq` |
| 目标包络 $(V^*, \mathbf L^*)$ 与 $U \subseteq V^*$ | `hLstar : TargetLipEnvelopeCertificate d target Vstar Lstar`（[structural_priors.lean](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR02/physical-2/session/work/formal_oet/vol_03/ch_12_residuals_and_substitution/structural_priors.lean#L25-L28)）、`hpathV` | `hpathV` 与 `N.U ⊆ Vstar` 等价，但缺等价桥接引理 |
| 采样结构 $S_j \subseteq S \cap U \cap \mathrm{dom}(\phi^\natural)$、$\delta_{o,j}$ | `sample : I → Set X`、`delta_o : I → ENNReal` | 定理未强加 `SamplingStructure` 与有限 $\delta_o$（[empirical_residuals.lean](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR02/physical-2/session/work/formal_oet/vol_03/ch_12_residuals_and_substitution/empirical_residuals.lean#L44-L50)），使结论更一般、不损正确性 |
| 路径采样 $S_{q,j} = S_j \cap U_q$ 与 $I_{\mathrm{res}}(q)$ | `path_component_sample`、`path_evaluable_components`（[path_sampling.lean](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR02/physical-2/session/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_sampling.lean#L27-L51)） | 准确覆盖（当 $S_j = \emptyset$ 时 $S_j \cap U_q = \emptyset$） |
| 路径级经验残差 $\hat\varepsilon_{q,j}$ | `path_empirical_residual_upper`（[path_sampling.lean](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR02/physical-2/session/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_sampling.lean#L136-L142), [empirical_residuals.lean](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR02/physical-2/session/work/formal_oet/vol_03/ch_12_residuals_and_substitution/empirical_residuals.lean#L105-L120)） | 准确覆盖（含 $\sup + \delta_o$） |
| 路径保证域 $U_{q,j}(\tau_j)$ 与 $U_{q,J}(\boldsymbol\tau) = \bigcap_{j\in J} U_{q,j}(\tau_j)$ | `path_component_empirical_guarantee_domain` 与 `path_joint_empirical_guarantee_domain`（[path_guarantee_domains.lean](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR02/physical-2/session/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L26-L46)） | 单分量精确；联合版本直接写成 `{x ∈ U_q ∧ ∀ j ∈ J, ...}`，未证明在 `J.Nonempty` 下等于交集 `⋂ j ∈ J, ...` |
| 受限 Lip 证书 $\mathbf L_q \in \mathscr L(c_q)\big|_{U_q}$ | `hLq : ∀ q : N.ReachablePath, IsLipMatrix d (N.path_chain q.nodes) (N.path_domain q.nodes) (Lq q)`（[L530-L531](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR02/physical-2/session/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L530-L531), [L562-L563](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR02/physical-2/session/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L562-L563), [L604-L605](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR02/physical-2/session/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L604-L605)） | **过度加强**：强加到未参与并集的路径上 |
| 推论 `#h-93b9c20ea18b4e59` 分量形式 / 联合形式 / 正文前提包装 | `path_component_guarantee_union_subset_proxy_error`、`path_joint_guarantee_union_subset_proxy_error`、`path_guarantee_union_subset_proxy_error_text`（[L520-L632](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR02/physical-2/session/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L520-L632)） | 仅涵盖 `hLq` 全局成立的子情形；`_text` 版把两支路耦合在同一 `hLq` 下且仅用 `have _ := ...` 保留正文前提 |

---

### 二、关键不足与可复核反例

#### 1. 主要缺陷：`hLq` 对全部可达路径全称量化，无法覆盖正文一般情况

在 [source.md](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR02/physical-2/session/work/source.md#L72-L99) 中：
- `#h-ed8808b4cfd52216` 与注明确说明：若 $j \notin I_{\mathrm{res}}(q)$（即 $S_{q,j} = \emptyset$），路径 $q$ 上**没有**第 $j$ 分量的路径级证书；
- `#h-0056e459b9376864` 仅对满足 $j \in I_{\mathrm{res}}(q)$ 的路径 $q$ 取受限 Lip 证书 $\mathbf L_q \in \mathscr L(c_q)|_{U_q}$；
- `#h-93b9c20ea18b4e59` 两个并集分别只对满足 $j \in I_{\mathrm{res}}(q)$ 与 $J \subseteq I_{\mathrm{res}}(q)$ 的路径取并。

然而，[path_guarantee_domains.lean](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR02/physical-2/session/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L530-L605) 中三条定理均要求 `hLq : ∀ q : N.ReachablePath, IsLipMatrix d (N.path_chain q.nodes) (N.path_domain q.nodes) (Lq q)`——哪怕在 proof body 中（[L542-L544](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR02/physical-2/session/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L542-L544), [L579-L580](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR02/physical-2/session/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L579-L580)）仅在取出 `hj : j ∈ path_evaluable_components N sample q` 或 `hJ : J ⊆ path_evaluable_components N sample q` 后才调用 `hLq q`。

#### 2. 4 点非分离规范空间反例（已用 Lean 4.29.1 机械验证）

取 $X = \{\bot, a, b, c\}$，$I = \{0\}$（即 `Unit`），并在 $X$ 上定义非分离扩展伪度量（满足 [ExtendedPseudoMetric](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR02/physical-2/session/work/formal_oet/vol_01/ch_01_foundations/gauge_space.lean#L16-L20)）：
$$d_0(a,b)=d_0(b,a)=0,\quad d_0(a,c)=d_0(c,a)=d_0(b,c)=d_0(c,b)=1,\quad d_0(x,x)=0,\quad d_0(x,\bot)=d_0(\bot,x)=\top\ (x\neq\bot).$$
构造两节点有限算子网络 `N`（$V = \{\mathrm{true}, \mathrm{false}\}$，输入域 $U = \{a,b,c\}$，转移选择恒为 `OutputChoice.stop`，深度上界 `1`）：
- 节点 `opTrue`：$\bot\mapsto\bot$，其余点全映到 $c$；入口 `entry(c) = true`，对应可达路径 $q_1 = [\mathrm{true}]$，路径域 $U_{q_1} = \{c\}$，路径链 $c_{q_1}(c) = c$。
- 节点 `opFalse`：$\bot\mapsto\bot,\ a\mapsto a,\ b\mapsto c,\ c\mapsto c$；入口 `entry(a) = entry(b) = false`，对应可达路径 $q_2 = [\mathrm{false}]$，路径域 $U_{q_2} = \{a,b\}$，路径链 $c_{q_2}(a)=a,\ c_{q_2}(b)=c$。
- 令代理 $\phi := \phi_{\mathcal N}$、目标 $\phi^\natural := \mathrm{opTrue}$、$V^* := U$、$\mathbf L^* := 0$、$\delta_{o,0} := 0$、样本 $S_0 := \{c\}$（满足 `SamplingStructure`、`hrep`、`hpathV`、`hLstar`、`0 ∈ evaluable_components sample`、$J = \{0\}$ 非空且 $\tau_0 = 0$ 有限）。

核验结果：
1. 在活跃路径 $q_1$ 上：$S_{q_1,0} = \{c\} \neq \emptyset$，即 $0 \in I_{\mathrm{res}}(q_1)$，且 $\mathbf L_{q_1} = 0$ 满足 `IsLipMatrix`（`U_{q_1,0}(0) = {c}`）。
2. 在未采样路径 $q_2$ 上：$S_{q_2,0} = \{c\} \cap \{a,b\} = \emptyset$，即 $0 \notin I_{\mathrm{res}}(q_2)$。对任意矩阵 $L : I \to I \to \mathrm{ENNReal}$（即使允许取 `⊤`）：
   $$d_0(c_{q_2}(a), c_{q_2}(b)) = d_0(a, c) = 1 > 0 = L_{0,0} \cdot 0 = L_{0,0} \cdot d_0(a,b),$$
   故 $\mathscr L(c_{q_2})|_{U_{q_2}} = \emptyset$，`¬ ∃ Lq, ∀ q : N.ReachablePath, IsLipMatrix ... (Lq q)`。
3. **结论**：该实例满足正文 `#h-93b9c20ea18b4e59` 的全部前提并成立对应包含关系，但源码中三条 Lean 定理均**不可实例化/不可使用**。

#### 3. 联合保证域的定义方式与 `_text` 捆绑问题

- **交集定义与 `J.Nonempty`**：正文定义 $U_{q,J}(\boldsymbol\tau) := \bigcap_{j \in J} U_{q,j}(\tau_j)$（要求 $J$ 非空）。Lean 的 [path_joint_empirical_guarantee_domain](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR02/physical-2/session/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L39-L46) 展开为 `{x | x ∈ N.path_domain q.nodes ∧ ∀ j ∈ J, ...}`。当 `J.Nonempty` 时二者集合相等；但当 `J = ∅` 时，Lean 定义给出 $U_q \subseteq U$（从而无需 `hJ_nonempty`），而集合交 $\bigcap_{j \in \emptyset} U_{q,j}(\tau_j) = \mathrm{Set.univ} \ni \bot \notin U$。源码缺少“非空时两者相等”的桥接证明。
- **`_text` 包装的耦合问题**：[path_guarantee_union_subset_proxy_error_text](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR02/physical-2/session/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L588-L632) 将单分量 `j` 与联合族 `J` 合为一个合取结论，共用一个 `hLq`。一旦把 `hLq` 正确弱化到活跃路径，第一支路只需 `j ∈ path_evaluable_components N sample q → IsLipMatrix ...`，第二支路只需 `J ⊆ path_evaluable_components N sample q → IsLipMatrix ...`，二者互不包含（除恰好满足 `j ∈ J` 外）；强行合写会引入跨结论耦合。

---

### 三、区分：源码已证明结论 vs 需自行补充的内容

#### 1. 源码已证明（且已通过 Lean 4.29.1 编译）的结论

1. **路径级单分量与联合局部保证域上界（对应 `#h-4b5219aa3a3bbdad`）**：
   - 路径链局部与联合误差界：[proxy_path_component_guarantee_error_bound](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR02/physical-2/session/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L152-L174)、[path_joint_guarantee_error_bound](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR02/physical-2/session/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L210-L236)、[proxy_path_joint_guarantee_error_bound](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR02/physical-2/session/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L244-L268)。
   - 这些局部命题**本身都只对单个固定 `q` 要求 `IsLipMatrix` 以及 `j ∈ path_evaluable_components` / `J ⊆ path_evaluable_components`**，没有任何多余约束。
2. **网络覆盖、路径链与采样分解基础设施**：
   - [path_chain_eq_represented_proxy_on_path](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR02/physical-2/session/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_sampling.lean#L220-L231)（路径域上 `path_chain = proxy`）。
   - [path_domain_subset_source](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR02/physical-2/session/work/formal_oet/vol_01/ch_05_operator_networks/operator_network.lean#L768-L771)、[reachable_path_domains_cover](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR02/physical-2/session/work/formal_oet/vol_01/ch_05_operator_networks/operator_network.lean#L778-L788)、[dom_extensional_operator_eq](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR02/physical-2/session/work/formal_oet/vol_01/ch_05_operator_networks/operator_network.lean#L344-L355)。
3. **全局 Lip 前提特化下的推论 `#h-93b9c20ea18b4e59`**：
   - [path_component_guarantee_union_subset_proxy_error](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR02/physical-2/session/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L520-L544)、[path_joint_guarantee_union_subset_proxy_error](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR02/physical-2/session/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L552-L580)、[path_guarantee_union_subset_proxy_error_text](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR02/physical-2/session/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L588-L632)（仅在附加“每条可达路径都存在受限 Lip 矩阵”时可用）。

#### 2. 需自行补充与修正的内容

1. **放松三条推论中的 `hLq` 前提（核心补齐）**：
   - 单分量形式应改为：
     ```lean
     (hLq : ∀ q : N.ReachablePath,
       j ∈ path_evaluable_components N sample q →
       IsLipMatrix d (N.path_chain q.nodes) (N.path_domain q.nodes) (Lq q))
     ```
     证明中把 `(hLq q)` 改为 `(hLq q hj)` 即可。
   - 联合形式应改为：
     ```lean
     (hLq : ∀ q : N.ReachablePath,
       J ⊆ path_evaluable_components N sample q →
       IsLipMatrix d (N.path_chain q.nodes) (N.path_domain q.nodes) (Lq q))
     ```
     证明中把 `(hLq q)` 改为 `(hLq q hJ)` 即可。
2. **拆分 `_text` 包装定理（推荐）**：
   - 按同文件第 181 行与第 276 行的风格，拆为 `path_component_guarantee_union_subset_proxy_error_text` 与 `path_joint_guarantee_union_subset_proxy_error_text`，分别携带各自的活跃路径 `hLq` 与 `hj_evaluable`/`htau_j_finite`（或 `hJ_evaluable`/`hJ_nonempty`/`htau_finite`）；若保留合取版，则分别传入按支路限定的 `hLq_comp` 与 `hLq_joint`（或在 `j ∈ I_res(q) ∨ J ⊆ I_res(q)` 上给 `Lq q`）。
3. **补充三个接口桥接引理（使语义对应严格闭环）**：
   - **联合域与有限非空交等价**：在 `hJ : J.Nonempty` 下证明
     `path_joint_empirical_guarantee_domain d A N sample q J eps tau = ⋂ j ∈ J, path_component_empirical_guarantee_domain d A N sample q j (eps j) (tau j)`。
   - **域假设等价**：证明 `(∀ q : N.ReachablePath, N.path_domain q.nodes ⊆ Vstar) ↔ N.U ⊆ Vstar`。
   - **代理定义域蕴含**：由 `hrep : N.represents proxy` 导出 `N.U ⊆ dom proxy`。

---

### 四、验证说明

- 已于 Lean 4.29.1 环境运行编译，包含 [path_guarantee_domains.lean](file:///private/tmp/math-gauge-hydrogen-xhigh-20261113/attempts/AHR02/physical-2/session/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L1-L633) 在内的全部 43 个依赖模块构建成功（退出码 `0`），源码内 `sorry`/`axiom ` 检索无匹配。
- 已通过 `lean --stdin` 在不修改任何工作区附件源码的前提下完成机械验证（退出码 `0`，零报错与零警告）：
  - 验证了上述 3 条桥接引理在 Lean 4.29.1 中可完整证明；
  - 验证了放松 `hLq` 后的单分量与联合全局拟合定理可直接由 `proxy_path_component_guarantee_error_bound` 与 `path_joint_guarantee_error_bound` 证出；
  - 验证了上述 4 点非分离反例满足正文全部假设（含 `SamplingStructure`、`hrep`、`hpathV`、`hLstar`、活跃路径 `IsLipMatrix`），能套用放松 `hLq` 后的定理，而原全局 `hLq` 不可满足；同时验证了 `J = ∅` 时 `⋂ j ∈ ∅, ... ⊈ net.U`。
