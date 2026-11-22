### 审阅结论

**总体判断：附件中的 Lean 实现准确且完整地覆盖了数学正文中的推论 `#h-93b9c20ea18b4e59（路径保证域的全局拟合含义）`。**

具体而言，`formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean` 在锚点 `h-93b9c20ea18b4e59` 下给出了三条无 `sorry`、无额外公理的定理：
1. `path_component_guarantee_union_subset_proxy_error`（[01-user-032.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/AHR04/physical-1/session/work/.visible-input/AHR04/01-user-032.txt#L408-L433)）：单分量包含式的独立一般形式；
2. `path_joint_guarantee_union_subset_proxy_error`（[01-user-032.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/AHR04/physical-1/session/work/.visible-input/AHR04/01-user-032.txt#L441-L470)）：分量族联合包含式的独立一般形式；
3. `path_guarantee_union_subset_proxy_error_text`（[01-user-032.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/AHR04/physical-1/session/work/.visible-input/AHR04/01-user-032.txt#L478-L522)、[01-user-033.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/AHR04/physical-1/session/work/.visible-input/AHR04/01-user-033.txt#L1-L5)）：保留正文全部显式前提（可评估性、非空分量族、有限阈值）的合取包装。

三者联合起来，在对象定义、前提范围与结论语义上都完整对应正文中的两条包含关系，且无逻辑漏洞或退化空洞。下面给出逐项对应关系，并严格区分**源码已证明的结论**与**需自行补充核验的等价桥接及细微边界说明**。

---

### 一、数学正文与 Lean 实现的逐项对应

正文目标命题见 `source.md` 中的 **推论 `#h-93b9c20ea18b4e59`**（[01-user-033.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/AHR04/physical-1/session/work/.visible-input/AHR04/01-user-033.txt#L537-L554)），其语境与局部定义位于同节前文（[01-user-033.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/AHR04/physical-1/session/work/.visible-input/AHR04/01-user-033.txt#L300-L461)）。

#### 1. 语境与前提对应

| 数学正文（`source.md`） | Lean 实现 | 定位 |
| --- | --- | --- |
| 扩展规范空间 $(\mathcal X,\mathcal G,\bot)$ 与有限指标集 $I$ | `{X I V : Type} {bot : X} [Fintype I]`，`d : I → X → X → ENNReal`，`hd : ∀ j : I, ExtendedPseudoMetric X bot (d j)` | `gauge_space.lean` ([01-user-001.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/AHR04/physical-1/session/work/.visible-input/AHR04/01-user-001.txt#L24-L29))；`path_guarantee_domains.lean` ([01-user-032.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/AHR04/physical-1/session/work/.visible-input/AHR04/01-user-032.txt#L479-L480)) |
| 目标算子 $\phi^\natural$、代理算子 $\phi$ | `target proxy : Operator X bot` | `operator_space.lean` ([01-user-001.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/AHR04/physical-1/session/work/.visible-input/AHR04/01-user-001.txt#L396-L398)) |
| 输入域为 $U$ 的有限算子网络 $\mathcal N$ 及表示 $\phi_{\mathcal N}\equiv_U\phi$ | `N : FiniteOperatorNetwork X bot V`（输入域 `N.U`）及 `hrep : N.represents proxy` | `operator_network.lean` ([01-user-013.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/AHR04/physical-1/session/work/.visible-input/AHR04/01-user-013.txt#L233-L255), [01-user-014.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/AHR04/physical-1/session/work/.visible-input/AHR04/01-user-014.txt#L164-L165)) |
| 目标 Lip 包络证书 $(V^*,\mathbf L^*)$ | `Vstar : Set X`，`Lstar : I → I → ENNReal`，`hLstar : TargetLipEnvelopeCertificate d target Vstar Lstar` | `structural_priors.lean` ([01-user-026.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/AHR04/physical-1/session/work/.visible-input/AHR04/01-user-026.txt#L511-L514)) |
| $U \subseteq \mathrm{dom}(\phi) \cap V^*$ | `hrep : N.represents proxy` 与 `hpathV : ∀ q : N.ReachablePath, N.path_domain q.nodes ⊆ Vstar`（等价性见下文第三节） | `path_guarantee_domains.lean` ([01-user-032.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/AHR04/physical-1/session/work/.visible-input/AHR04/01-user-032.txt#L492-L493)) |
| 可达路径集 $\mathcal P$、路径域 $U_q$、路径链 $c_q$ | `N.ReachablePath`、`N.path_domain q.nodes`、`N.path_chain q.nodes` | `operator_network.lean` ([01-user-013.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/AHR04/physical-1/session/work/.visible-input/AHR04/01-user-013.txt#L556-L617)) |
| 采样族 $\{S_j\}$、$I_{\mathrm{res}}$、$S_{q,j}=S_j\cap U_q$、$I_{\mathrm{res}}(q)$ | `sample : I → Set X`、`evaluable_components sample`、`path_component_sample N sample q j`、`path_evaluable_components N sample q` | `empirical_residuals.lean` ([01-user-025.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/AHR04/physical-1/session/work/.visible-input/AHR04/01-user-025.txt#L192-L193))；`path_sampling.lean` ([01-user-033.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/AHR04/physical-1/session/work/.visible-input/AHR04/01-user-033.txt#L38-L62)) |
| 路径残差上界 $\hat\varepsilon_{q,j}=\sup_{x_s\in S_{q,j}} d_j(c_q(x_s),\phi^\natural(x_s))+\delta_{o,j}$ | `path_empirical_residual_upper d target N sample delta_o q j` | `path_sampling.lean` ([01-user-033.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/AHR04/physical-1/session/work/.visible-input/AHR04/01-user-033.txt#L147-L153))；`empirical_residuals.lean` ([01-user-025.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/AHR04/physical-1/session/work/.visible-input/AHR04/01-user-025.txt#L262-L277)) |
| 路径 Lip 证书 $\mathbf L_q\in\mathscr L(c_q)\big|_{U_q}$ 与 $\mathbf A_q=\mathbf L_q+\mathbf L^*$ | `Lq : N.ReachablePath → I → I → ENNReal`、`hLq`（`IsLipMatrix d (N.path_chain q.nodes) (N.path_domain q.nodes) (Lq q)`）与 `fun i j => Lq q i j + Lstar i j` | `lip_matrix.lean` ([01-user-002.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/AHR04/physical-1/session/work/.visible-input/AHR04/01-user-002.txt#L126-L129))；`path_guarantee_domains.lean` ([01-user-032.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/AHR04/physical-1/session/work/.visible-input/AHR04/01-user-032.txt#L494-L509)) |
| $j\in I_{\mathrm{res}}$、有限 $\tau_j\in[0,+\infty)$；非空 $J\subseteq I_{\mathrm{res}}$、有限族 $\boldsymbol\tau=(\tau_i)_{i\in J}$ | `hj_evaluable`、`htau_j_finite`；`hJ_evaluable`、`hJ_nonempty`、`htau_finite`（在 `*_text` 中显式保留，在独立核心定理中进一步省去非必要前提） | `path_guarantee_domains.lean` ([01-user-032.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/AHR04/physical-1/session/work/.visible-input/AHR04/01-user-032.txt#L485-L491)) |

#### 2. 路径保证域与结论包含式对应

- **单分量路径保证域 $U_{q,j}(\tau_j)$**：
  `path_component_empirical_guarantee_domain`（[01-user-031.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/AHR04/physical-1/session/work/.visible-input/AHR04/01-user-031.txt#L521-L527)）经 `empirical_component_guarantee_domain`（[01-user-025.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/AHR04/physical-1/session/work/.visible-input/AHR04/01-user-025.txt#L542-L546)）与 `anchor_gap_sublevel`（[01-user-025.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/AHR04/physical-1/session/work/.visible-input/AHR04/01-user-025.txt#L383-L387)）逐层展开后，与
  $$\{x\in U_q : D_{\mathbf A_q,j}(x;S_{q,j})+\hat\varepsilon_{q,j}\le\tau_j\}$$
  逐符号一致（其中矩阵索引约定为 `M i j` $= M_{i\to j}$，与 `matrix_vector_bound` [01-user-008.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/AHR04/physical-1/session/work/.visible-input/AHR04/01-user-008.txt#L450-L452) 及 `weighted_anchor_distance` [01-user-025.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/AHR04/physical-1/session/work/.visible-input/AHR04/01-user-025.txt#L363-L366) 一致）。

- **单分量全局包含式**：
  $$\bigcup_{\substack{q\in\mathcal P\\ j\in I_{\mathrm{res}}(q)}} U_{q,j}(\tau_j) \subseteq \{x\in U : d_j(\phi(x),\phi^\natural(x))\le\tau_j\}$$
  对应 `path_component_guarantee_union_subset_proxy_error`（及 `path_guarantee_union_subset_proxy_error_text` 的第一合取支）：
  `{x | ∃ q : N.ReachablePath, j ∈ path_evaluable_components N sample q ∧ x ∈ path_component_empirical_guarantee_domain ...} ⊆ {x | x ∈ N.U ∧ d j (proxy.func x) (target.func x) ≤ tau_j}`。

- **联合路径保证域 $U_{q,J}(\boldsymbol\tau)$ 与联合全局包含式**：
  $$\bigcup_{\substack{q\in\mathcal P\\ J\subseteq I_{\mathrm{res}}(q)}} U_{q,J}(\boldsymbol\tau) \subseteq \{x\in U : \forall j\in J,\ d_j(\phi(x),\phi^\natural(x))\le\tau_j\}$$
  对应 `path_joint_guarantee_union_subset_proxy_error`（及 `path_guarantee_union_subset_proxy_error_text` 的第二合取支）：
  `{x | ∃ q : N.ReachablePath, J ⊆ path_evaluable_components N sample q ∧ x ∈ path_joint_empirical_guarantee_domain ...} ⊆ {x | x ∈ N.U ∧ ∀ i : I, i ∈ J → d i (proxy.func x) (target.func x) ≤ tau i}`。

---

### 二、源码已证明的结论与证明链

以下结论均已在附件 Lean 源码中完整机证（无 `sorry`）：

1. **目标推论本身**：
   - `path_component_guarantee_union_subset_proxy_error`（[01-user-032.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/AHR04/physical-1/session/work/.visible-input/AHR04/01-user-032.txt#L408-L433)）
   - `path_joint_guarantee_union_subset_proxy_error`（[01-user-032.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/AHR04/physical-1/session/work/.visible-input/AHR04/01-user-032.txt#L441-L470)）
   - `path_guarantee_union_subset_proxy_error_text`（[01-user-032.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/AHR04/physical-1/session/work/.visible-input/AHR04/01-user-032.txt#L478-L522)、[01-user-033.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/AHR04/physical-1/session/work/.visible-input/AHR04/01-user-033.txt#L1-L5)）

2. **被上述定理直接调用的已证明支撑链路**：
   - **路径域包含于总域**：`FiniteOperatorNetwork.path_domain_subset_source`（[01-user-014.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/AHR04/physical-1/session/work/.visible-input/AHR04/01-user-014.txt#L118-L121)）给出 $U_q\subseteq U$。
   - **路径链与代理算子在路径域上重合**：`path_chain_eq_represented_proxy_on_path`（[01-user-033.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/AHR04/physical-1/session/work/.visible-input/AHR04/01-user-033.txt#L231-L242)），依赖 `local_equivalent_extensional_path_chain`（[01-user-013.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/AHR04/physical-1/session/work/.visible-input/AHR04/01-user-013.txt#L624-L635)）。
   - **路径局部经验上界（对应正文 `@h-4b5219aa3a3bbdad`）**：
     - `path_local_empirical_upper`（[01-user-031.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/AHR04/physical-1/session/work/.visible-input/AHR04/01-user-031.txt#L549-L579)），由 `path_component_sample_subset_path_domain`、`empirical_residual_upper_certificate`（[01-user-025.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/AHR04/physical-1/session/work/.visible-input/AHR04/01-user-025.txt#L347-L355)）与 `empirical_target_perturbation_upper_point_from_residual_certificate`（[01-user-027.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/AHR04/physical-1/session/work/.visible-input/AHR04/01-user-027.txt#L45-L63)）经 `empirical_target_perturbation_upper_point`（[01-user-026.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/AHR04/physical-1/session/work/.visible-input/AHR04/01-user-026.txt#L546-L603)、[01-user-027.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/AHR04/physical-1/session/work/.visible-input/AHR04/01-user-027.txt#L1-L4)）推出。
     - `path_component_guarantee_error_bound`、`proxy_path_component_guarantee_error_bound`、`path_joint_guarantee_error_bound`（[01-user-032.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/AHR04/physical-1/session/work/.visible-input/AHR04/01-user-032.txt#L10-L124)），依赖 `empirical_component_guarantee_error_bound` 与 `empirical_joint_guarantee_error_bound`（[01-user-026.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/AHR04/physical-1/session/work/.visible-input/AHR04/01-user-026.txt#L36-L70)）。
   - **路径可评估分量蕴含全局可评估分量**：`path_evaluable_subset_evaluable_components`（[01-user-033.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/AHR04/physical-1/session/work/.visible-input/AHR04/01-user-033.txt#L114-L120)）。
   - **网络路径域覆盖与外延定义域**：`FiniteOperatorNetwork.reachable_path_domains_cover`（[01-user-014.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/AHR04/physical-1/session/work/.visible-input/AHR04/01-user-014.txt#L128-L138)）、`FiniteOperatorNetwork.dom_extensional_operator_eq`（[01-user-013.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/AHR04/physical-1/session/work/.visible-input/AHR04/01-user-013.txt#L403-L414)）。

---

### 三、需自行补充核验的桥接论证与细微说明（源码未单独打包为定理）

以下内容属于**正文表述与 Lean 编码形式之间的等价桥接**（源码未作为独立引理列出，但均可在 2–5 步内由源码已有定义和定理直接推出，不构成实质性缺漏）：

1. **联合路径保证域的交集等价性（$J\neq\emptyset$）**
   - 正文将 $U_{q,J}(\boldsymbol\tau)$ 定义为交集 $\bigcap_{i\in J} U_{q,i}(\tau_i)$（[01-user-033.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/AHR04/physical-1/session/work/.visible-input/AHR04/01-user-033.txt#L405-L411)）；
   - Lean 的 `path_joint_empirical_guarantee_domain`（[01-user-031.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/AHR04/physical-1/session/work/.visible-input/AHR04/01-user-031.txt#L534-L541)）经 `empirical_joint_guarantee_domain`（[01-user-025.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/AHR04/physical-1/session/work/.visible-input/AHR04/01-user-025.txt#L553-L560)）直接写为
     $$\{x \in U_q \mid \forall i\in J,\ D_{\mathbf A_q,i}(x;S_{q,i})+\hat\varepsilon_{q,i}\le\tau_i\}.$$
   - **自行补充论证**：当 $J\neq\emptyset$（取 $j_0\in J$）时，对任意 $x\in X$：
     - 若 $x$ 属 Lean 定义集，则 $x\in U_q$ 且对所有 $i\in J$ 不等式成立，故对所有 $i\in J$ 有 $x\in U_{q,i}(\tau_i)$；
     - 反之，若 $x\in\bigcap_{i\in J} U_{q,i}(\tau_i)$，由 $j_0\in J$ 得 $x\in U_{q,j_0}(\tau_{j_0})\subseteq U_q$，且对所有 $i\in J$ 均有对应不等式成立。
     因此二者在正文前提 $J\neq\emptyset$ 下外延相等（且当 $J=\emptyset$ 时 Lean 写法仍保证结果包含于 $U_q$，避免了空交等于全集的病态）。

2. **全局域前提 $U\subseteq\mathrm{dom}(\phi)\cap V^*$ 与 Lean 前提 `(hrep, hpathV)` 的精确等价性**
   - 正文假设 $U\subseteq\mathrm{dom}(\phi)\cap V^*$ 且 $\phi_{\mathcal N}\equiv_U\phi$（[01-user-033.txt](file:///private/tmp/math-gauge-neon-xhigh-20261119-v2/attempts/AHR04/physical-1/session/work/.visible-input/AHR04/01-user-033.txt#L304-L312)），而 Lean 未显式要求 `N.U ⊆ dom proxy` 或 `N.U ⊆ Vstar`，改为 `hrep : N.represents proxy` 与 `hpathV : ∀ q : N.ReachablePath, N.path_domain q.nodes ⊆ Vstar`。
   - **自行补充论证**：
     - 由 `N.path_domain_subset_source`（$U_q\subseteq U$）与 `N.reachable_path_domains_cover`（$\bigcup_{q\in\mathcal P} U_q = U$），有
       $$U \subseteq V^* \iff \forall q\in\mathcal P,\ U_q \subseteq V^*.$$
     - 对任意 $x\in U$，由 `N.dom_extensional_operator_eq` 得 $\phi_{\mathcal N}(x)\neq\bot$，再由 `hrep x hx` 得 $\phi(x)=\phi_{\mathcal N}(x)\neq\bot$，即 $U\subseteq\mathrm{dom}(\phi)$ 自动成立。
     - 结合 `hLstar.lip_matrix.1`（$V^*\subseteq\mathrm{dom}(\phi^\natural)$），同时确保 $U\subseteq\mathrm{dom}(\phi)\cap\mathrm{dom}(\phi^\natural)$，因此右侧集合中的 $d_j(\phi(x),\phi^\natural(x))$ 绝不会落入吸收元 $\bot$。

3. **采样结构限制的放宽与无害性**
   - 正文在 `@h-6f9e054ce01ccfef` 下假设存在有限环境采样集 $S$ 使 $S_j\subseteq S\cap U\cap\mathrm{dom}(\phi^\natural)$，且 $I_{\mathrm{res}}(q)=\{j\in I_{\mathrm{res}}:S_{q,j}\neq\emptyset\}$。
   - Lean 定理对任意 `sample : I → Set X` 与 `delta_o : I → ENNReal` 成立，未要求 `SamplingStructure` 或 `sample j ⊆ N.U`。
   - **自行补充论证**：由已证的 `path_evaluable_subset_evaluable_components`，$S_j\cap U_q\neq\emptyset\implies S_j\neq\emptyset$，故 `path_evaluable_components N sample q` 恒等于 $\{j\in I_{\mathrm{res}}:S_{q,j}\neq\emptyset\}=I_{\mathrm{res}}(q)$；又因 $S_{q,j}=S_j\cap U_q\subseteq U_q\subseteq V^*\subseteq\mathrm{dom}(\phi^\natural)$ 且 $S_{q,j}\subseteq U\subseteq\mathrm{dom}(\phi)$，路径采样自动位于共同定义域内。由于 `ENNReal` 上下确界对任意集与有限集兼容，Lean 结论是正文命题的严格推广，覆盖正文的全部实例。

4. **索引并集记号与集合存在量词记号的一致性**
   - 正文写 $\bigcup_{q\in\mathcal P,\,P(q)} E_q$，Lean 写 `{x | ∃ q : N.ReachablePath, P q ∧ x ∈ E q}`；由 `Set.mem_iUnion` 知二者外延相同。且每条纳入并集的路径均满足 $j\in I_{\mathrm{res}}(q)$（或 $J\subseteq I_{\mathrm{res}}(q)$），因而锚点集 $S_{q,j}$（或各 $S_{q,i}$）均非空，未越出正文“注（路径采样缺失）”规定的定义范围。

5. **合并包装定理 `path_guarantee_union_subset_proxy_error_text` 与两条独立定理的分工**
   - `path_guarantee_union_subset_proxy_error_text` 将单分量 $(j,\tau_j)$ 与分量族 $(J,\boldsymbol\tau)$ 打包为同一条合取定理，其中 `hLq` 要求在满足 $j\in I_{\mathrm{res}}(q)\lor J\subseteq I_{\mathrm{res}}(q)$ 的路径上给出 $\mathbf L_q$。
   - 若使用场景**仅需联合包含式**，且仅在满足 $J\subseteq I_{\mathrm{res}}(q)$ 的路径上拥有 Lip 证书（例如在非分离伪度量空间中，某条仅满足 $j\in I_{\mathrm{res}}(q)$ 但 $J\not\subseteq I_{\mathrm{res}}(q)$ 的路径链 $c_q$ 可能破坏零距等价而不存在任何 `ENNReal` Lip 矩阵），则单靠 `*_text` 包装无法实例化；但此时直接调用同文件同锚点的独立定理 `path_joint_guarantee_union_subset_proxy_error` 即可无额外前提地得到联合包含式（类似地，单分量场景可直接调用 `path_component_guarantee_union_subset_proxy_error`，或在 `*_text` 中取 $J=\{j\}$、$\tau\equiv\tau_j$）。因此整体实现不存在覆盖缺口。

6. **与 `InFittingBall` 记号的衔接（非正文推论要求，仅作补充说明）**
   - 正文推论 `#h-93b9c20ea18b4e59` 本身仅陈述上述两条集合包含式，并未直接写出 `InFittingBall`。若下游需将左端联合并集的任一子集 $U_0$ 转为第 7/12 章的 `InFittingBall d target proxy U₀ J tau`，只需结合 `path_joint_guarantee_union_subset_proxy_error`、前述 $U\subseteq\mathrm{dom}(\phi)\cap\mathrm{dom}(\phi^\natural)$、`htau_finite` 与 `(hd i).symm` 即可直接得到；该推演属于源码之外的可选延伸，不影响本推论覆盖的完整性。

---

*注：本审阅所涉理论定义、命题与 Lean 形式化均源自附件材料：Zhe Li (Glen Li / glenzli), The Operator Evolution Theory (https://glenzli.com/books/oet/, CC BY 4.0)；上述第三节为针对源码覆盖性与前提等价性的补充核验。*