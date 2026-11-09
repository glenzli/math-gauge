# 审阅报告：推论 #h-93b9c20ea18b4e59「路径保证域的全局拟合含义」及其 Lean 实现

## 0. 总判定

**所给实现准确、完整地覆盖该数学命题，且全部内容已在源码中证明；就该推论而言无需自行补充任何证明。** 两个包含关系分别由 `formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean` 中的

- `path_component_guarantee_union_subset_proxy_error`（分量形式），
- `path_joint_guarantee_union_subset_proxy_error`（联合形式），

完整证明；正文级别的前提（$j\in I_{\mathrm{res}}$、阈值有限、$J\subseteq I_{\mathrm{res}}$ 非空）由同文件 `path_guarantee_union_subset_proxy_error_text` 作为两条包含的合取保留。整个工程 `lake build` 编译通过，源码中无任何 `sorry`/`native_decide`/`axiom` 声明，且上述三个定理经 `#print axioms` 检查仅依赖标准公理 `propext, Classical.choice, Quot.sound`。

以下先给出对应关系，再给出可复核的验证记录，最后列出表述差异（均不构成缺口）及“已证明 / 需补充”的明确划分。

## 1. 被审阅的数学命题

对任意 $j\in I_{\mathrm{res}}$ 与有限阈值 $\tau_j$：
$$\bigcup_{\substack{q\in\mathcal P\\ j\in I_{\mathrm{res}}(q)}}U_{q,j}(\tau_j)\subseteq\{x\in U: d_j(\phi(x),\phi^\natural(x))\leq\tau_j\};$$
更一般地，对非空分量族 $J\subseteq I_{\mathrm{res}}$：
$$\bigcup_{\substack{q\in\mathcal P\\ J\subseteq I_{\mathrm{res}}(q)}}U_{q,J}(\boldsymbol\tau)\subseteq\{x\in U:\forall j\in J,\ d_j(\phi(x),\phi^\natural(x))\leq\tau_j\}.$$

正文证明一句话：“若 $x$ 属于左侧某个路径局部保证域，则由 @h-4b5219aa3a3bbdad 得到对应分量的误差上界。对所有 $j\in J$ 同时应用即可。”

## 2. 定义与记号的对应关系（机器核验均为 `rfl` 级定义展开）

| 正文 | Lean | 核验方式 |
|---|---|---|
| $U$（网络输入域） | `N.U` | — |
| $\mathcal P$（路径集） | `N.ReachablePath` | — |
| $U_q$（路径域） | `N.path_domain q.nodes` | — |
| $c_q$（路径链） | `N.path_chain q.nodes` | — |
| $S_j$ | `sample j` | — |
| $S_{q,j}=S_j\cap U_q$ | `path_component_sample N sample q j = sample j ∩ N.path_domain q.nodes` | `rfl` |
| $I_{\mathrm{res}}(q)=\{j\in I_{\mathrm{res}}:S_{q,j}\neq\emptyset\}$ | `path_evaluable_components N sample q = {j \| (sample j ∩ N.path_domain q.nodes).Nonempty}` | `rfl`；与正文集合外延相同：`path_evaluable_subset_evaluable_components` 给出 $\subseteq I_{\mathrm{res}}$，反向由 $S_{q,j}\neq\emptyset\Rightarrow S_j\neq\emptyset$ 平凡 |
| $\hat\varepsilon_{q,j}=\sup_{x_s\in S_{q,j}}d_j(c_q(x_s),\phi^\natural(x_s))+\delta_{o,j}$ | `path_empirical_residual_upper d target N sample delta_o q j` $=(\sup_{x_s\in S_{q,j}} d_j(c_q(x_s),\text{target}.func\,x_s))+\delta_{o,j}$ | `rfl` |
| $D_{\mathbf A,j}(x;E)=\inf_{y\in E}\sum_i[\mathbf A]_{i\to j}d_i(x,y)$ | `weighted_anchor_distance d A j x E` $=\inf_{y\in E}\sum_i A_{ij}\,d_i(x,y)$（`matrix_vector_bound`） | 定义 |
| $\mathbf A_q=\mathbf L_q+\mathbf L^*$ | `fun i j => Lq q i j + Lstar i j` | — |
| $U_{q,j}(\tau_j)=\{x\in U_q: D_{\mathbf A_q,j}(x;S_{q,j})+\hat\varepsilon_{q,j}\leq\tau_j\}$ | `path_component_empirical_guarantee_domain d A N sample q j ε τ`，展开为 $\{x\mid x\in U_q\wedge D_{\mathbf A,j}(x;S_j\cap U_q)+\varepsilon\le\tau\}$ | `rfl`（核查 1） |
| $U_{q,J}(\boldsymbol\tau)=\bigcap_{j\in J}U_{q,j}(\tau_j)$ | `path_joint_empirical_guarantee_domain d A N sample q J ε τ` $=\{x\in U_q\mid\forall j\in J,\ D+\hat\varepsilon_{q,j}\le\tau_j\}$ | `rfl`（核查 3）；$J$ 非空时与逐分量交相等已另行证明（核查 3′） |
| $\phi_{\mathcal N}\equiv_U\phi$ | `hrep : N.represents proxy`（$=$ `LocalEquivalent N.extensional_operator proxy N.U`） | 定义 |
| $\mathbf L_q\in\mathscr L(c_q)\big|_{U_q}$ | `hLq q : IsLipMatrix d (N.path_chain q.nodes) (N.path_domain q.nodes) (Lq q)`，即 $U_q\subseteq\mathrm{dom}(c_q)$ 且 $d_j(c_qx,c_qy)\le\sum_i[\mathbf L_q]_{i\to j}d_i(x,y)$ | 定义 |
| $(V^*,\mathbf L^*)$（@h-9655cbb9401e5c90） | `Vstar`、`Lstar` 与 `hLstar : TargetLipEnvelopeCertificate d target Vstar Lstar`（展开为 `IsLipMatrix d target Vstar Lstar`，含 $V^*\subseteq\mathrm{dom}(\phi^\natural)$） | 定义 |
| $U\subseteq V^*$ | `hpathV : ∀ q, N.path_domain q.nodes ⊆ Vstar`（由 $U_q\subseteq U$，正文假设蕴含它；我已补证该蕴含，见核查 6） | 已证 |
| $\phi^\natural,\ \phi$ | `target`, `proxy`（结论中距离方向 `d j (proxy.func x) (target.func x)` 与正文 $d_j(\phi(x),\phi^\natural(x))$ 一致，代理在前） | — |

## 3. 定理与证明的对应关系

**(1) 分量形式 ↔ `path_component_guarantee_union_subset_proxy_error`。** 左侧集合 `{x | ∃ q : N.ReachablePath, j ∈ path_evaluable_components N sample q ∧ x ∈ path_component_empirical_guarantee_domain d (Lq q + Lstar) N sample q j (path_empirical_residual_upper … q j) tau}` 恰为 $\bigcup_{q:\,j\in I_{\mathrm{res}}(q)}U_{q,j}(\tau_j)$；右侧 `{x | x ∈ N.U ∧ d j (proxy.func x) (target.func x) ≤ tau}` 恰为 $\{x\in U:d_j(\phi(x),\phi^\natural(x))\le\tau_j\}$。证明为：`rcases hx with ⟨q, hj, hxq⟩`（$x$ 属于某条路径局部保证域）后
- `proxy_path_component_guarantee_error_bound`：保证域成员 $\Rightarrow d_j(\phi(x),\phi^\natural(x))\le\tau_j$。其内部正是 h-4b5219aa3a3bbdad 的代入——`path_local_empirical_upper`（Lean 版局部上界，参数逐项对齐：`hpathV`$=U_q\subseteq V^*$、`hLq`$=\mathbf L_q$ 证书、`hLstar`$=\mathbf L^*$ 证书、`hj`$=j\in I_{\mathrm{res}}(q)$）给出 $d_j(c_q(x),\phi^\natural(x))\le D_{\mathbf A_q,j}(x;S_{q,j})+\hat\varepsilon_{q,j}$，`empirical_component_guarantee_error_bound` 把它与子水平条件相加，`path_chain_eq_represented_proxy_on_path`（路径分解 h-56edb9917107efcd + 网络表示）把 $c_q(x)$ 换为 $\phi(x)$；
- `N.path_domain_subset_source hxq.1`：$U_{q,j}(\tau_j)\subseteq U_q\subseteq U$，给出 $x\in U$。

这正是正文“由 h-4b5219aa3a3bbdad 得到对应分量的误差上界”一字不差的展开。

**(2) 联合形式 ↔ `path_joint_guarantee_union_subset_proxy_error`。** 左侧对 $q$ 的限制条件为 `J ⊆ path_evaluable_components N sample q`（$=J\subseteq I_{\mathrm{res}}(q)$）；右侧为 `{x | x ∈ N.U ∧ ∀ j ∈ J, d j (proxy.func x) (target.func x) ≤ tau j}`。证明结构相同：取出见证路径 $q$ 后 `intro j hj` 逐分量调用 `path_joint_guarantee_error_bound`，后者对每个 $j\in J$ 以 `hJ hj` 提供 path-可评估性并应用同一条局部上界——即正文“对所有 $j\in J$ 同时应用即可”。

**(3) 正文前提版本 ↔ `path_guarantee_union_subset_proxy_error_text`。** 以定理参数形式保留正文的全部边条件：`hj_evaluable : j ∈ evaluable_components sample`（$j\in I_{\mathrm{res}}$）、`htau_j_finite`（$\tau_j$ 有限）、`hJ_nonempty`（$J$ 非空）、`hJ_evaluable`（$J\subseteq I_{\mathrm{res}}$）、`htau_finite`（阈值族有限），结论为两条包含关系的合取；证明就是把两个核心定理拼起来（边条件按本仓库惯用的“正文对齐”方式以 `have _ := …` 消耗，并不削弱结论）。

## 4. 机器验证记录（可复核）

1. `grep -rn "sorry\|native_decide\|axiom " formal_oet` → 无任何匹配。
2. `lake build formal_oet.vol_03.ch_14_empirical_network_fitting.path_guarantee_domains` → `Build completed successfully (3341 jobs)`；随后 `lake build`（全库）→ 成功。
3. 另建临时文件（已删除）`import` 该模块后核验，全部通过、无错误：
   - 核查 1–4（上文表格中标注 `rfl` 的四条展开）以 `example … := rfl` 通过，确认定义与正文逐符号一致；
   - 核查 3′：$J$ 非空时 `path_joint_empirical_guarantee_domain … = ⋂ j ∈ J, path_component_empirical_guarantee_domain … (eps j) (tau j)` 已证明，确认 Lean 的联合域就是正文的 $\bigcap_{j\in J}U_{q,j}(\tau_j)$；
   - 核查 5：`N.represents proxy → N.U ⊆ dom proxy` 已证明（$x\in U$ 时 `proxy.func x = extensional.func x ≠ bot`），故正文框架假设 $U\subseteq\mathrm{dom}(\phi)$ 在源码中是**可推出**的，未列为假设并非遗漏；
   - 核查 6：`N.U ⊆ Vstar → ∀ q, N.path_domain q.nodes ⊆ Vstar` 已证明，故 Lean 的逐路径假设恰由正文的 $U\subseteq V^*$ 蕴含；
   - `#print axioms` 对三个定理均输出 `depends on axioms: [propext, Classical.choice, Quot.sound]`——结论确为源码完整证明，不存在 `sorryAx` 或自定义公理。

## 5. 表述差异清单（均不构成覆盖缺口）

1. **核心定理省略了正文的边条件**（$j\in I_{\mathrm{res}}$、$\tau$ 有限、$J$ 非空、$J\subseteq I_{\mathrm{res}}$）。这不削弱而只增强命题：若左侧并集非空，则由 `path_evaluable_subset_evaluable_components` 自动有 $j\in I_{\mathrm{res}}$（联合形式同理得 $J\subseteq I_{\mathrm{res}}$）；并集为空时包含关系平凡；$\tau=\top$ 时结论平凡为真。且 `_text` 版本按正文原样保留了全部条件。
2. **$\mathbf L_q$ 实现为全局赋值 `Lq : N.ReachablePath → I → I → ENNReal`，且 `hLq` 对全部可达路径要求证书**。正文按“每条进入并集的路径取一个证书”读取；由于两个并集遍历所有满足可评估条件的路径，本来就需要对每条这样的路径给出证书，全局赋值是等价而更整洁的表述。差别仅在于：对**不满足**可评估条件、从而不进入并集的路径，Lean 也要求存在证书（路径链不必 Lipschitz 时该假设可能过强）。这不改变被证明的包含关系本身；若确需“仅并集相关路径有证书”的字面版本，用同一论证即可补出：把并集改为 `{x | ∃ q, ∃ L, IsLipMatrix d c_q U_q L ∧ j ∈ path_evaluable_components … ∧ x ∈ path_component_empirical_guarantee_domain d (L + Lstar) …}`，`rcases` 取出 $(q,L,\text{证书})$ 后直接套用已证明的逐路径引理 `proxy_path_component_guarantee_error_bound` / `path_joint_guarantee_error_bound`（现有证明正是这个结构，只需让 `L` 内在于见证）。这是一个约五行的加强表述，不是修补缺口。
3. **部分定义的全面化**。正文只在 $S_{q,j}\neq\emptyset$ 时定义 $\hat\varepsilon_{q,j}$，并把空采样上的 $D$ 排除在定义范围外；Lean 中两者全定义（空集上确界为 $0$、下确界为 $\top$）。两个包含关系的并集条件（$j\in I_{\mathrm{res}}(q)$、$J\subseteq I_{\mathrm{res}}(q)$）恰好排除空采样情形，故该约定差异对结论无影响。
4. **框架性采样结构未形式化**（$S$ 有限、$S_j\subseteq S\cap U\cap\mathrm{dom}(\phi^\natural)$）。它们不进入本推论的证明：$S_{q,j}$ 已通过与 $U_q$ 取交实现“采样点落在 $U$ 内”；采样点若在 $\mathrm{dom}(\phi^\natural)$ 之外，只会使残差为 $\top$、相应保证域在有限阈值下为空，包含关系仍真（在这些路径上空洞成立）。
5. 推论之后的**“注（与全局保证域的比较）”属评注而非本推论的内容**；其引用的单调性方向（同一矩阵下路径共同锚点距离 ≥ 全局共同锚点距离）在源码中由已证明的 `weighted_anchor_distance_mono_of_subset` 与 `path_component_sample_subset_component` 立即给出，无需新定理。

## 6. 源码已证明 vs 需自行补充

**源码已证明（经编译与公理检查确认）：**
- 分量形式包含关系（`path_component_guarantee_union_subset_proxy_error`）；
- 联合形式包含关系（`path_joint_guarantee_union_subset_proxy_error`）；
- 正文前提下的合并版本（`path_guarantee_union_subset_proxy_error_text`）；
- 全部所引用的辅助链：Lean 版 h-4b5219aa3a3bbdad（`path_local_empirical_upper` / `proxy_path_local_empirical_upper`）及其到保证域成员的推论（`path_component/joint_guarantee_error_bound`、`proxy_path_component_guarantee_error_bound`）、路径分解与网络表示的衔接（`path_chain_eq_represented_proxy_on_path`）、路径采样与路径可评估分量的全部定义与引理（`path_sampling.lean`）。

**需自行补充：无。** 就“路径保证域的全局拟合含义”这一推论的数学内容而言，两条包含关系及其正文前提版本都已在源码中完整证明，无需补充。仅当要求上述第 5.2 条的字面边角版本（证书只对进入并集的路径给出）或把第 5.4 条的框架性采样结构作为显式前提重述时，才需按第 5 节给出的方式自行组合——那是表述层面的加强，不改变命题真值，也不是现有实现的缺口。