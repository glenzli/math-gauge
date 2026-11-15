{}
### 一、总体审阅结论

**结论：所给 Lean 实现的核心局部到全局误差传递机制准确，但未能完整覆盖数学正文的推论 `#h-93b9c20ea18b4e59`（路径保证域的全局拟合含义）。**

数学正文见 [source.md](file:///private/tmp/math-gauge-carbon-high-effort-lane2-20261115-v2/attempts/AHR02/physical-1/session/work/source.md#L242-L260)（前置设定与定义见 [source.md](file:///private/tmp/math-gauge-carbon-high-effort-lane2-20261115-v2/attempts/AHR02/physical-1/session/work/source.md#L5-L166)）；对应的三个目标声明位于 [path_guarantee_domains.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane2-20261115-v2/attempts/AHR02/physical-1/session/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L515-L632)：
- `path_component_guarantee_union_subset_proxy_error`（[path_guarantee_domains.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane2-20261115-v2/attempts/AHR02/physical-1/session/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L520-L544)）
- `path_joint_guarantee_union_subset_proxy_error`（[path_guarantee_domains.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane2-20261115-v2/attempts/AHR02/physical-1/session/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L552-L580)）
- `path_guarantee_union_subset_proxy_error_text`（[path_guarantee_domains.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane2-20261115-v2/attempts/AHR02/physical-1/session/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L588-L631)）

**准确之处与主要不足概述：**
1. **核心算子与集合语义准确**：在假定全路径族均具备 Lip 矩阵的前提下，网络表示 $\phi_{\mathcal N}\equiv_U\phi$、路径采样 $S_{q,j}$、路径可评估集 $I_{\mathrm{res}}(q)$、路径残差上界 $\hat\varepsilon_{q,j}$、组合矩阵 $\mathbf A_q=\mathbf L_q+\mathbf L^*$ 及右侧全局容差集合 $\{x\in U:\dots\}$ 的形式化均与正文一致。
2. **不足 1（核心前提过强——路径链 Lip 证书被全称量化到全部可达路径）**：三个定理均要求 `hLq : ∀ q : N.ReachablePath, IsLipMatrix d (N.path_chain q.nodes) (N.path_domain q.nodes) (Lq q)`。而正文中 $\mathbf L_q\in\mathscr L(c_q)|_{U_q}$ 仅在参与并集的可评估路径（$j\in I_{\mathrm{res}}(q)$ 或 $J\subseteq I_{\mathrm{res}}(q)$）上局部选取（[source.md](file:///private/tmp/math-gauge-carbon-high-effort-lane2-20261115-v2/attempts/AHR02/physical-1/session/work/source.md#L84-L99)）。在 OET 允许的非分离扩展规范空间中，未采样或仅部分采样路径上**甚至可以完全不存在任何 `ENNReal` 值的 Lip 矩阵**（含 `⊤` 亦不存在），导致数学命题成立而三个 Lean 定理的前提恒假、无法适用。
3. **不足 2（正文包装定理将单分量与联合结论强行耦合于同一 `Lq`/`hLq` 作用域）**：`path_guarantee_union_subset_proxy_error_text` 将固定 $(j,\tau_j)$ 与 $(J,\boldsymbol\tau)$ 合取在同一声明中共享单一 `Lq`。当某路径 $q_2$ 满足 $j\in I_{\mathrm{res}}(q_2)$ 但 $J\not\subseteq I_{\mathrm{res}}(q_2)$ 且 $c_{q_2}$ 在 $U_{q_2}$ 上无 Lip 矩阵时，推论第二式对 $J$ 严格成立，却与单分量 $j$ 的路径证书范围冲突。
4. **不足 3（联合保证域的字面交集定义未建立等价桥接，导致 `J.Nonempty` 沦为空置前提）**：正文定义 $U_{q,J}(\boldsymbol\tau)=\bigcap_{j\in J}U_{q,j}(\tau_j)$（[source.md](file:///private/tmp/math-gauge-carbon-high-effort-lane2-20261115-v2/attempts/AHR02/physical-1/session/work/source.md#L110-L116)），该交集仅在 $J\neq\emptyset$ 时等于 `path_joint_empirical_guarantee_domain`；当 $J=\emptyset$ 时字面交集为全空间 `Set.univ`（含吸收元 `bot ∉ N.U`），包含关系不成立。源码未证明二者的等价引理，且在 `path_guarantee_union_subset_proxy_error_text` 中直接丢弃了 `hJ_nonempty`（`have _ := hJ_nonempty`）。
5. **延伸接口区分（字面集合包含 vs 全局拟合闭球 `InFittingBall`）**：推论 `#h-93b9c20ea18b4e59` 的字面公式为集合包含，源码右侧已准确表达；但若需对接第 7/12 章的代理闭球结构 `InFittingBall`（对比第 12 章的 `empirical_fitting_ball_inheritance`，见 [substitution_inheritance.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane2-20261115-v2/attempts/AHR02/physical-1/session/work/formal_oet/vol_03/ch_12_residuals_and_substitution/substitution_inheritance.lean#L28-L50)），源码丢弃了有限阈值前提 `htau_finite` 且未封装 `InFittingBall` 继承定理，需另行补充。

---

### 二、数学正文与 Lean 实现的逐项对应关系

| 数学正文对象 / 条件（[source.md](file:///private/tmp/math-gauge-carbon-high-effort-lane2-20261115-v2/attempts/AHR02/physical-1/session/work/source.md#L7-L260)） | Lean 表达 | 审阅判定 |
| :--- | :--- | :--- |
| 扩展规范空间 $(\mathcal X,\mathcal G,\bot)$，有限 $I$ | `[Fintype I]`, `hd : ∀ j, ExtendedPseudoMetric X bot (d j)`（[gauge_space.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane2-20261115-v2/attempts/AHR02/physical-1/session/work/formal_oet/vol_01/ch_01_foundations/gauge_space.lean#L15-L21)） | 准确 |
| $\phi^\natural,\phi\in\mathcal X_{\mathrm{op}}$，$(V^*,\mathbf L^*)$ | `target proxy : Operator X bot`, `TargetLipEnvelopeCertificate d target Vstar Lstar`（[structural_priors.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane2-20261115-v2/attempts/AHR02/physical-1/session/work/formal_oet/vol_03/ch_12_residuals_and_substitution/structural_priors.lean#L25-L29)） | 准确 |
| $\mathcal N$ 输入域 $U$，$\phi_{\mathcal N}\equiv_U\phi$，$U\subseteq\mathrm{dom}(\phi)\cap V^*$ | `N.U`, `hrep : N.represents proxy`, `hpathV : ∀ q, N.path_domain q.nodes ⊆ Vstar`（[operator_network.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane2-20261115-v2/attempts/AHR02/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/operator_network.lean#L344-L815)） | 等价覆盖：由 `reachable_path_domains_cover` 知 `hpathV ↔ N.U ⊆ Vstar`；由 `dom_extensional_operator_eq` 与 `hrep` 可推 `N.U ⊆ dom proxy`；由 `hLstar` 可推 `Vstar ⊆ dom target` |
| 采样结构 $\mathcal S=\{S_j\}$，$S_{q,j}=S_j\cap U_q$ | `sample : I → Set X`, `path_component_sample N sample q j`（[path_sampling.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane2-20261115-v2/attempts/AHR02/physical-1/session/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_sampling.lean#L27-L30)） | 合理放宽：未要求 `SamplingStructure`，因与 $U_q$ 取交后自动落在 $U_q\subseteq U\cap V^*$ 内 |
| $I_{\mathrm{res}}(q)=\{j\in I_{\mathrm{res}}:S_{q,j}\neq\emptyset\}$ | `path_evaluable_components N sample q`（[path_sampling.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane2-20261115-v2/attempts/AHR02/physical-1/session/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_sampling.lean#L48-L64)） | 集合恒等：$S_{q,j}=S_j\cap U_q\neq\emptyset\Rightarrow S_j\neq\emptyset$（见 `path_evaluable_subset_evaluable_components`，[path_sampling.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane2-20261115-v2/attempts/AHR02/physical-1/session/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_sampling.lean#L103-L109)） |
| $\hat\varepsilon_{q,j}=\sup_{x_s\in S_{q,j}}d_j(c_q(x_s),\phi^\natural(x_s))+\delta_{o,j}$ | `path_empirical_residual_upper d target N sample delta_o q j`（[path_sampling.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane2-20261115-v2/attempts/AHR02/physical-1/session/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_sampling.lean#L136-L142)） | 准确 |
| 对可评估路径取 $\mathbf L_q\in\mathscr L(c_q)|_{U_q}$，$\mathbf A_q=\mathbf L_q+\mathbf L^*$ | `hLq : ∀ q : N.ReachablePath, IsLipMatrix ... (Lq q)`，`fun i j => Lq q i j + Lstar i j` | **不完整（前提过强）**：矩阵索引方向 `i → j` 准确（[lip_matrix.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane2-20261115-v2/attempts/AHR02/physical-1/session/work/formal_oet/vol_01/ch_02_operator_bounds/lip_matrix.lean#L21-L25)），但 `∀ q` 强加到不可评估/未认证路径 |
| $U_{q,j}(\tau_j)$ 与 $U_{q,J}(\boldsymbol\tau)=\bigcap_{j\in J}U_{q,j}(\tau_j)$（$J\neq\emptyset$） | `path_component_empirical_guarantee_domain` 与 `path_joint_empirical_guarantee_domain`（[path_guarantee_domains.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane2-20261115-v2/attempts/AHR02/physical-1/session/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L26-L46)） | **缺失桥接**：联合域直接写成带 `x ∈ U_q` 的描述集，未证明 $J\neq\emptyset$ 时与字面交集 $\bigcap_{j\in J}U_{q,j}(\tau_j)$ 相等 |
| 推论 `#h-93b9c20ea18b4e59` 的两条并集包含式 | 三个定理的 `{x \| ∃ q, ...} ⊆ {x \| x ∈ N.U ∧ ...}`（[path_guarantee_domains.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane2-20261115-v2/attempts/AHR02/physical-1/session/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L520-L631)） | **覆盖不完整**：受限于全局 `hLq`、单分量/联合耦合，且未与标准 `⋃` / `⋂` 记号桥接 |

---

### 三、不足之处的可复核论证与反例

#### 1. 反例 1：全路径 `hLq` 前提严格强于数学命题（未采样路径上可完全不存在 Lip 矩阵）

**依据对比：**
- 正文 `#h-55c4fe8427039cfc`（[source.md](file:///private/tmp/math-gauge-carbon-high-effort-lane2-20261115-v2/attempts/AHR02/physical-1/session/work/source.md#L7-L33)）对代理算子 $\phi$、网络 $\mathcal N$ 及各路径链 $c_q$ **未作全局 Lip 假设**；第 84–85 行明确指出当 $S_{q,j}=\emptyset$ 时“相应路径级证书停止”；`#h-0056e459b9376864`（[source.md](file:///private/tmp/math-gauge-carbon-high-effort-lane2-20261115-v2/attempts/AHR02/physical-1/session/work/source.md#L89-L93)）仅对满足 $j\in I_{\mathrm{res}}(q)$（或 $J\subseteq I_{\mathrm{res}}(q)$）的路径 $q$ 选取 $\mathbf L_q\in\mathscr L(c_q)|_{U_q}$；推论 `#h-93b9c20ea18b4e59` 的证明也仅对并集指标中的路径调用 `#h-4b5219aa3a3bbdad`。
- 反观 [path_guarantee_domains.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane2-20261115-v2/attempts/AHR02/physical-1/session/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L530-L531)（及第 562–563、604–605 行），即使注释写着 *"The union of certified path component guarantee domains"*，形式前提却要求对**所有** `q : N.ReachablePath` 给出 `IsLipMatrix`。

**可复核反例构造（在 Lean `ENNReal` 语义下连 `⊤` 矩阵也不存在）：**
1. **空间与规范族**：取单指标集 $I=\{\star\}$，四点集 $\mathcal X=\{\bot,a,b,c\}$，吸收元为 $\bot$。定义 $d_\star:\mathcal X\times\mathcal X\to[0,+\infty]$ 为：
   - $d_\star(\bot,\bot)=0$，对 $x\neq\bot$ 令 $d_\star(x,\bot)=d_\star(\bot,x)=+\infty$（`⊤`）；
   - $d_\star(a,a)=d_\star(b,b)=d_\star(a,b)=d_\star(b,a)=0$，$d_\star(c,c)=0$；
   - $d_\star(a,c)=d_\star(c,a)=d_\star(b,c)=d_\star(c,b)=1$。
   易核验 $d_\star$ 满足非吸收元存在性（$c\neq\bot$）、自距零、对称性、三角不等式（$\{a,b\}$ 视为零距等价类，到 $c$ 距离为 $1$）及吸收元隔离公理，是合法的 `ExtendedPseudoMetric`（OET 明确包含非分离规范空间，见 [gauge_space.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane2-20261115-v2/attempts/AHR02/physical-1/session/work/formal_oet/vol_01/ch_01_foundations/gauge_space.lean#L15-L37)）。
2. **目标算子与包络证书**：取 $U=V^*=\{a,b,c\}$。令 $\phi^\natural(\bot)=\bot$，且对 $x\in\{a,b,c\}$ 恒有 $\phi^\natural(x)=c$。取零矩阵 $\mathbf L^*=0$，因 $V^*\subseteq\mathrm{dom}(\phi^\natural)$ 且 $d_\star(\phi^\natural(x),\phi^\natural(y))=d_\star(c,c)=0$，`TargetLipEnvelopeCertificate` 成立。
3. **有限算子网络 $\mathcal N$ 与代理算子 $\phi$**：取节点集 $V=\{v_1,v_2\}$（二元有限集）：
   - 节点算子 $\psi_{v_1}=\mathrm{id}_{\mathcal X}$；$\psi_{v_2}(\bot)=\bot,\ \psi_{v_2}(a)=a,\ \psi_{v_2}(b)=c,\ \psi_{v_2}(c)=c$（二者定义域均为 $\{a,b,c\}\neq\emptyset$）；
   - 入口规则：$\mathrm{entry}(c)=v_1$，$\mathrm{entry}(a)=\mathrm{entry}(b)=v_2$；后继选择恒为 `stop`，深度界为 $1$，路径分配 $\mathrm{path\_of}(x)=[\mathrm{entry}(x)]$；
   - 令 $\phi=\phi_{\mathcal N}$（即 `N.extensional_operator`），则 `N.represents proxy` 与 $U\subseteq\mathrm{dom}(\phi)\cap V^*$ 均成立。
   网络恰有两条可达路径：
   - $q_1=[v_1]$：$U_{q_1}=\{c\}$，$c_{q_1}|_{U_{q_1}}$ 为常值 $c$；
   - $q_2=[v_2]$：$U_{q_2}=\{a,b\}$，$c_{q_2}(a)=a,\ c_{q_2}(b)=c$。
4. **采样结构与数学命题的成立性**：取环境样本 $S=\{c\}$，$S_\star=\{c\}$，$\delta_{o,\star}=0$。满足 `SamplingStructure` 且：
   - $I_{\mathrm{res}}=\{\star\}$；
   - $S_{q_1,\star}=\{c\}\neq\emptyset\implies I_{\mathrm{res}}(q_1)=\{\star\}$，$\hat\varepsilon_{q_1,\star}=d_\star(c,c)+0=0$。在 $U_{q_1}=\{c\}$ 上取 $\mathbf L_{q_1}=0\in\mathscr L(c_{q_1})|_{U_{q_1}}$，对有限阈值 $\tau_\star=0$，有 $U_{q_1,\star}(0)=\{c\}\neq\emptyset$；
   - $S_{q_2,\star}=\{c\}\cap\{a,b\}=\emptyset\implies \star\notin I_{\mathrm{res}}(q_2)$（$q_2$ 不参与推论并集）。
   此时数学推论 `#h-93b9c20ea18b4e59` 的全部前提成立，左侧并集为 $\{c\}$，右侧为 $\{x\in U:d_\star(\phi(x),\phi^\natural(x))\le 0\}=\{b,c\}$，包含关系 $\{c\}\subseteq\{b,c\}$ 非空且成立。
5. **Lean 实现前提恒假的证明**：对任意矩阵 $L:I\to I\to\mathrm{ENNReal}$（哪怕令 $L_{\star\to\star}=\top$），在 $a,b\in U_{q_2}$ 处检验 `IsLipMatrix`（[lip_matrix.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane2-20261115-v2/attempts/AHR02/physical-1/session/work/formal_oet/vol_01/ch_02_operator_bounds/lip_matrix.lean#L21-L25)）：
   $$d_\star(c_{q_2}(a),c_{q_2}(b))=d_\star(a,c)=1,\qquad L_{\star\to\star}\cdot d_\star(a,b)=L_{\star\to\star}\cdot 0=0$$
   （在 `ENNReal` 中恒有 `⊤ * 0 = 0`）。因 $1\le 0$ 假，故
   $$\neg\,\exists L,\ \mathrm{IsLipMatrix}\ d\ c_{q_2}\ U_{q_2}\ L,$$
   从而不存在任何族 `Lq` 满足 `∀ q : N.ReachablePath, IsLipMatrix ... (Lq q)`。三个 Lean 定理在此合法实例上一律无法调用。

> **补充说明（分离规范空间情形）**：即便在分离空间（如 $\mathbb R\sqcup\{\bot\}$）中，正文标准下的受限 Lip 矩阵元素取有限实数（若未采样路径上 $c_{q_2}(x)=x^2,\ U_{q_2}=(1,+\infty)$，则无有限 Lip 矩阵）；即便在 Lean 中允许用 `⊤` 填补分离空间上的未采样路径，对于调用方仅在可评估路径上构造的具体矩阵族 `Lq`（例如未采样路径置 `0`），全称前提 `hLq` 同样直接失效。

---

#### 2. 反例 2：部分采样路径下联合命题与单分量命题的证书作用域冲突

考察 `path_guarantee_union_subset_proxy_error_text`（[path_guarantee_domains.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane2-20261115-v2/attempts/AHR02/physical-1/session/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L588-L631)）同时绑定 $(j,\tau_j)$ 与 $(J,\boldsymbol\tau)$ 的结构问题：
- 沿用反例 1 的 $\mathcal X,\phi^\natural,\mathcal N,\phi$，改取双分量指标集 $I=\{0,1\}$，令 $d_0=d_1=d_\star$，联合分量集 $J=\{0,1\}$。
- 取采样集 $S_0=\{c,a\}$，$S_1=\{c\}$。则：
  - 全局可评估集 $I_{\mathrm{res}}=\{0,1\}$，故 $J\subseteq I_{\mathrm{res}}$ 且 $J\neq\emptyset$；
  - 在 $q_1=[v_1]$ 上：$S_{q_1,0}=S_{q_1,1}=\{c\}\neq\emptyset$，故 $I_{\mathrm{res}}(q_1)=\{0,1\}\supseteq J$，且 $\mathbf L_{q_1}=0\in\mathscr L(c_{q_1})|_{U_{q_1}}$；
  - 在 $q_2=[v_2]$ 上：$S_{q_2,0}=\{a\}\neq\emptyset$ 但 $S_{q_2,1}=\emptyset$，故 $I_{\mathrm{res}}(q_2)=\{0\}\not\supseteq J$，而 $\mathscr L(c_{q_2})|_{U_{q_2}}=\emptyset$。

**结论对比**：
- 推论 `#h-93b9c20ea18b4e59` 的**第二式（联合形式）**对 $J=\{0,1\}$ 完全良定义且成立：满足 $J\subseteq I_{\mathrm{res}}(q)$ 的路径仅有 $q_1$，在所有满足 $J\subseteq I_{\mathrm{res}}(q)$ 的路径上均存在合法 Lip 证书 $\mathbf L_q$。
- 然而不仅当前的 `path_joint_guarantee_union_subset_proxy_error` 与 `path_guarantee_union_subset_proxy_error_text` 因要求 $q_2$ 上的 Lip 矩阵而失效；即便尝试修改 `path_guarantee_union_subset_proxy_error_text`，由于第 $0$ 分量在 $q_2$ 上可评估（$0\in I_{\mathrm{res}}(q_2)$）而联合集 $J$ 在 $q_2$ 上不可评估（$J\not\subseteq I_{\mathrm{res}}(q_2)$），单分量结论所需的路径证书域 $\{q:j\in I_{\mathrm{res}}(q)\}$ 与联合结论所需的路径证书域 $\{q:J\subseteq I_{\mathrm{res}}(q)\}$ **本质不同**，不能在单一定理中混用同一个无区分的证书前提。

---

#### 3. 论证与反例 3：字面交集 $\bigcap_{j\in J}U_{q,j}(\tau_j)$ 与 `J.Nonempty` 的缺失桥接

- 正文第 110–116 行将联合路径保证域定义为**非空** $J_q\subseteq I_{\mathrm{res}}(q)$ 上的交集 $U_{q,J_q}(\boldsymbol\tau)=\bigcap_{j\in J_q}U_{q,j}(\tau_j)$。
- Lean 中的 `path_joint_empirical_guarantee_domain`（[path_guarantee_domains.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane2-20261115-v2/attempts/AHR02/physical-1/session/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L39-L46)）展开为（见 [guarantee_domains.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane2-20261115-v2/attempts/AHR02/physical-1/session/work/formal_oet/vol_03/ch_12_residuals_and_substitution/guarantee_domains.lean#L35-L42)）：
  $$\{x \mid x\in U_q \land \forall j\in J,\ D_{\mathbf A_q,j}(x;S_{q,j})+\hat\varepsilon_{q,j}\le\tau_j\}.$$
- **差异可复核验证**：
  1. 当 $J=\emptyset$ 且存在至少一条可达路径 $q\in\mathcal P$ 时，字面交集 `⋂ j ∈ (∅ : Set I), U_{q,j}(τ_j)` 在集合论与 Mathlib 中恒等于全集 `Set.univ : Set X`。因吸收元 `bot ∈ Set.univ`，而有限算子网络公理要求 `bot ∉ N.U`（[operator_network.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane2-20261115-v2/attempts/AHR02/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/operator_network.lean#L176)），故字面交集的并集为 `Set.univ ⊈ N.U`，推论第二式对 $J=\emptyset$ **不成立**——这正是数学正文必须假设“非空分量族 $J\subseteq I_{\mathrm{res}}$”的原因。
  2. 当 `J.Nonempty` 成立时（设 $j_0\in J$），由 $x\in\bigcap_{j\in J}U_{q,j}(\tau_j)\Rightarrow x\in U_{q,j_0}(\tau_{j_0})\Rightarrow x\in U_q$，两种表述才严格相等。但源码中**未提供这一等价引理**，导致 `path_guarantee_union_subset_proxy_error_text` 第 625 行的 `have _ := hJ_nonempty` 未发挥任何实质证明作用。

---

### 四、源码已证明结论与需自行补充内容的区分

#### （一）源码已证明的结论

1. **路径采样与残差基础（[path_sampling.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane2-20261115-v2/attempts/AHR02/physical-1/session/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_sampling.lean#L103-L277)）**：
   - `path_evaluable_subset_evaluable_components`：$I_{\mathrm{res}}(q)\subseteq I_{\mathrm{res}}$；
   - `component_sample_eq_iUnion_path_component_sample` 与 `disjoint_path_component_sample_of_nodes_ne`：$S_j=\bigsqcup_{q\in\mathcal P}S_{q,j}$；
   - `path_chain_eq_represented_proxy_on_path`：在 $U_q$ 上 $c_q(x)=\phi(x)$；
   - `path_empirical_residual_upper_le_global`：$\hat\varepsilon_{q,j}\le\hat\varepsilon_j$。
2. **单条固定路径上的局部经验上界（[path_guarantee_domains.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane2-20261115-v2/attempts/AHR02/physical-1/session/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L54-L300)，对应 `#h-4b5219aa3a3bbdad`）**：
   - `proxy_path_local_empirical_upper`、`proxy_path_component_guarantee_error_bound`、`proxy_path_joint_guarantee_error_bound`：对**单条**给定路径 $q$，仅需**该路径自身**的 `IsLipMatrix d (N.path_chain q.nodes) (N.path_domain q.nodes) Lq` 与 `j ∈ path_evaluable_components N sample q`（或 `J ⊆ ...`），即可推出 $x\in U_{q,j}(\tau_j)\Rightarrow d_j(\phi(x),\phi^\natural(x))\le\tau_j$ 及联合形式（这部分局部定理没有过度量化问题）。
3. **特例化的全局并集包含（[path_guarantee_domains.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane2-20261115-v2/attempts/AHR02/physical-1/session/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L520-L631)）**：
   - 仅在**所有可达路径 $q\in\mathcal P$ 同时具备受限 Lip 矩阵**这一额外强假设下，证明了 `{x | ∃ q, ...}` 形式的路径分量保证域并集与描述集形式的路径联合保证域并集包含于 `{x | x ∈ N.U ∧ ...}`。

#### （二）需自行补充的内容

1. **按路径可评估条件（或已认证路径子集）局部化的并集包含定理**：将 `hLq` 的全称量词收窄至实际参与并集的路径，消除对不可评估/未认证路径的 Lip 依赖。
2. **拆分单分量与联合正文定理**：解除 `path_guarantee_union_subset_proxy_error_text` 中固定 $(j,\tau_j)$ 与 $(J,\boldsymbol\tau)$ 的强耦合，使其各自仅依赖对应路径范围的证书并支持对任意 $j\in I_{\mathrm{res}}$ 或非空 $J\subseteq I_{\mathrm{res}}$ 独立调用。
3. **联合保证域与字面交集 $\bigcap_{j\in J}U_{q,j}(\tau_j)$（及标准并集记号 `⋃`）的等价引理**：在 `J.Nonempty` 前提下证明 `path_joint_empirical_guarantee_domain` 与双索引交集 `⋂ j ∈ J, path_component_empirical_guarantee_domain ...` 相等，以及存在式集合与 `⋃ q, ...` 相等。
4. **全局拟合闭球 `InFittingBall` 继承引理（若需衔接第 7/12 章拟合球算子传递）**：利用有限阈值 `htau_finite`、网络表示隐含的 `N.U ⊆ dom proxy`（由 `dom_extensional_operator_eq` 推出）、`N.U ⊆ Vstar ⊆ dom target` 以及伪度量对称性 `(hd j).symm`，证明认证路径联合保证域并集上的任意子域 $U_0$ 满足 `InFittingBall d target proxy U₀ J tau`。

---

### 五、补齐方案说明

在不改动现有已证明局部引理的前提下，利用 [path_guarantee_domains.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane2-20261115-v2/attempts/AHR02/physical-1/session/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean#L152-L269) 已有的 `proxy_path_component_guarantee_error_bound` 与 `proxy_path_joint_guarantee_error_bound`，可按如下三步完整补齐：

1. **补充字面交集与源域覆盖桥接引理**
   - 对 `hJ_nonempty : J.Nonempty`（取 $j_0\in J$），直接由集合外延性证明：
     ```lean
     path_joint_empirical_guarantee_domain d A N sample q J eps tau =
       ⋂ j ∈ J, path_component_empirical_guarantee_domain d A N sample q j (eps j) (tau j)
     ```
   - 由 `N.reachable_path_domains_cover`（[operator_network.lean](file:///private/tmp/math-gauge-carbon-high-effort-lane2-20261115-v2/attempts/AHR02/physical-1/session/work/formal_oet/vol_01/ch_05_operator_networks/operator_network.lean#L778)）可将前提简化为正文的 `hUVstar : N.U ⊆ Vstar`（再由 `N.path_domain_subset_source.trans hUVstar` 得到每条路径上的 `N.path_domain q.nodes ⊆ Vstar`）。

2. **将两个正文的并集包含定理拆分为各自受可评估性守卫的形式（并兼容部分路径认证）**
   - **分量形式（精确覆盖推论第一式）**：将 `hLq` 减弱为仅对 $j$-可评估路径成立：
     ```lean
     (hj_evaluable : j ∈ evaluable_components sample)
     (htau_j_finite : finite_ennreal tau_j)
     (hrep : N.represents proxy)
     (hUVstar : N.U ⊆ Vstar)
     (hLq : ∀ q : N.ReachablePath,
       j ∈ path_evaluable_components N sample q →
         IsLipMatrix d (N.path_chain q.nodes) (N.path_domain q.nodes) (Lq q))
     (hLstar : TargetLipEnvelopeCertificate d target Vstar Lstar) :
     (⋃ (q : N.ReachablePath) (_ : j ∈ path_evaluable_components N sample q),
       path_component_empirical_guarantee_domain d
         (fun i k => Lq q i k + Lstar i k) N sample q j
         (path_empirical_residual_upper d target N sample delta_o q j) tau_j)
       ⊆ {x | x ∈ N.U ∧ d j (proxy.func x) (target.func x) ≤ tau_j}
     ```
     *证明要点*：对任意属于左侧并集的 $x$，拆出见证路径 $q$ 及 `hjq : j ∈ path_evaluable_components N sample q`，此时 `hLq q hjq` 恰给出该路径上的 `IsLipMatrix`，直接调用已证定理 `proxy_path_component_guarantee_error_bound` 与 `N.path_domain_subset_source` 即得结论。
   - **联合形式（精确覆盖推论第二式）**：保持 `hJ_nonempty : J.Nonempty`，将 `hLq` 减弱为仅对 $J$-可评估路径成立，并在左侧直接使用字面并交 `⋃ (q) (_ : J ⊆ path_evaluable_components N sample q), ⋂ j ∈ J, ...`：
     ```lean
     (hLq : ∀ q : N.ReachablePath,
       J ⊆ path_evaluable_components N sample q →
         IsLipMatrix d (N.path_chain q.nodes) (N.path_domain q.nodes) (Lq q))
     ```
     *证明要点*：先用步骤 1 的交集等价引理（此处真正用到 `hJ_nonempty`！）将 `⋂ j ∈ J, ...` 转为 `path_joint_empirical_guarantee_domain`，再用 `hLq q hJq` 调用已证定理 `proxy_path_joint_guarantee_error_bound`。
   - **更一般的“已认证路径子集”形式**：若仅在部分可评估路径上持有 Lip 证书，可将 `IsLipMatrix d (N.path_chain q.nodes) (N.path_domain q.nodes) (Lq q)` 直接置于并集的存在条件内（`{x | ∃ q, J ⊆ path_evaluable_components N sample q ∧ IsLipMatrix ... (Lq q) ∧ x ∈ ...}`）；当上述守卫版 `hLq` 成立时，它退化为与正文完全一致的并集。

3. **补充全局 `InFittingBall` 继承定理（对齐第 12 章 `empirical_fitting_ball_inheritance`）**
   - 对满足 `U₀ ⊆ ⋃_{q, J ⊆ I_res(q)} U_{q,J}(τ)` 的任意子域 $U_0$：
     - 由步骤 2 得 $U_0\subseteq N.U$ 及 $\forall x\in U_0,\ \forall j\in J,\ d_j(\phi(x),\phi^\natural(x))\le\tau_j$；
     - 由 `hUVstar : N.U ⊆ Vstar` 与 `hLstar.lip_matrix.1 : Vstar ⊆ dom target` 得 `U₀ ⊆ dom target`；
     - 由 `hrep` 与 `N.dom_extensional_operator_eq` 得 `N.U ⊆ dom proxy`，从而 `U₀ ⊆ dom proxy`；
     - 结合 `htau_finite`（证明中真正消费有限阈值假设）与 `(hd j).symm` 即可构造 `InFittingBall d target proxy U₀ J tau`。
