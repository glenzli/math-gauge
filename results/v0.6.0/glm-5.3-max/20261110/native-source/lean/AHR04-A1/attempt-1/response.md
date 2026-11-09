该文件可无错无警告地独立重新编译。我所有的验证工作已完成。现在让我整理最终审查报告。

---

# 审阅报告：推论 #h-93b9c20ea18b4e59（路径保证域的全局拟合含义）

## 一、总体结论

**所给 Lean 实现准确、完整地覆盖了该数学命题。** 正文推论由两条包含关系组成，它在
`formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean` 中由三条定理实现（行 520 `path_component_guarantee_union_subset_proxy_error`、行 553 `path_joint_guarantee_union_subset_proxy_error`、行 590 `path_guarantee_union_subset_proxy_error_text`）；全库检索锚点 `h-93b9c20ea18b4e59` 仅命中这三处，别无竞争性或残缺实现。我通过完整编译、公理审计与定义展开核验做了独立验证：三条定理及其全部依赖均已完整证明（无 `sorry`），核心定义经 `rfl` 展开后与正文公式逐字一致；正文的两条包含关系分别与两条核心定理逐点相同，正文语境前提（$j\in I_{\mathrm{res}}$、非空 $J\subseteq I_{\mathrm{res}}$、有限阈值）由 `_text` 包装逐条保留。就本推论而言**无需自行补充任何内容**。

## 二、命题—实现逐条对应

正文推论：

**(1) 分量形式**：对任意 $j\in I_{\mathrm{res}}$ 与有限阈值 $\tau_j$，
$$\bigcup_{\substack{q\in\mathcal P\\ j\in I_{\mathrm{res}}(q)}}U_{q,j}(\tau_j)\subseteq\{x\in U:\ d_j(\phi(x),\phi^\natural(x))\leq\tau_j\};$$
**(2) 联合形式**：对给定非空分量族 $J\subseteq I_{\mathrm{res}}$，
$$\bigcup_{\substack{q\in\mathcal P\\ J\subseteq I_{\mathrm{res}}(q)}}U_{q,J}(\boldsymbol\tau)\subseteq\{x\in U:\ \forall j\in J,\ d_j(\phi(x),\phi^\natural(x))\leq\tau_j\}.$$

对应关系：**(1) ↔ `path_component_guarantee_union_subset_proxy_error`；**(2) ↔ `path_joint_guarantee_union_subset_proxy_error`；(1)∧(2) 连同正文语境前提 ↔ `path_guarantee_union_subset_proxy_error_text`（第一合取支即 (1)，第二合取支即 (2)）。

记号与定义的逐项核对（右侧各项均以 `#check`/`rfl` 实际验证，见第四节）：

| 正文记号 | Lean 对应 | 一致性 |
|---|---|---|
| $U$（网络输入域） | `N.U` | 同一对象；正文"$\mathcal N$ 是输入域为 $U$ 的网络"即 `N.U` |
| $U_q$（路径域） | `N.path_domain q.nodes` | 定义相同（h-374f884cd4d69e88） |
| $\mathcal P$ | `N.ReachablePath` | "路径域非空的节点序列"，定义相同 |
| $S_{q,j}=S_j\cap U_q$ | `path_component_sample N sample q j` | `rfl` 验证 = `sample j ∩ N.path_domain q.nodes` |
| $I_{\mathrm{res}}(q)$ | `path_evaluable_components N sample q` | `rfl` 验证 = `{k \| (S_{q,k}).Nonempty}`；因 $S_{q,j}\subseteq S_j$，与正文 $\{j\in I_{\mathrm{res}}:S_{q,j}\neq\emptyset\}$ 相等（库中 `path_evaluable_subset_evaluable_components` 形式化了蕴含方向） |
| $c_q$（路径链） | `N.path_chain q.nodes` | 定义相同 |
| $\phi,\ \phi^\natural$ | `proxy, target` | — |
| $\mathbf L_q,\ \mathbf L^*$ | `Lq q, Lstar` | — |
| $\mathbf A_q=\mathbf L_q+\mathbf L^*$ | `fun i j => Lq q i j + Lstar i j` | 逐项加法 |
| $\hat\varepsilon_{q,j}=\sup_{x_s\in S_{q,j}}d_j(c_q(x_s),\phi^\natural(x_s))+\delta_{o,j}$ | `path_empirical_residual_upper d target N sample delta_o q j` | `rfl` 验证 = `⨆ x ∈ path_component_sample…, d j (path_chain x) (target x) + delta_o j` |
| $D_{\mathbf A,j}(x;E)=\inf_{y\in E}\sum_i[\mathbf A]_{i\to j}d_i(x,y)$ | `weighted_anchor_distance` | `rfl` 验证 = `⨅ y ∈ E, ∑ i, A i j * d i x y` |
| $U_{q,j}(\tau_j)=\{x\in U_q: D+\hat\varepsilon\le\tau_j\}$ | `path_component_empirical_guarantee_domain` | `rfl` 验证集合级展开逐字一致 |
| $U_{q,J}(\boldsymbol\tau)=\bigcap_{j\in J}U_{q,j}(\tau_j)$ | `path_joint_empirical_guarantee_domain` | = `{x ∈ U_q \| ∀ j∈J, D_j+ε̂_{q,j} ≤ τ_j}`，对非空 $J$ 与交形式等价 |

两个陈述的左、右两侧均为逐字对应：
- 左侧并集 ↔ `{x | ∃ q : N.ReachablePath, (j ∈ path_evaluable_components… / J ⊆ path_evaluable_components…) ∧ x ∈ (对应保证域)}`——并集即存在见证，索引条件即 $j\in I_{\mathrm{res}}(q)$ / $J\subseteq I_{\mathrm{res}}(q)$；
- 右侧 ↔ `{x | x ∈ N.U ∧ d j (proxy.func x) (target.func x) ≤ tau}` 及其全 $J$ 分量形式。

## 三、证明路径的对应

正文证明只有一句："若 $x$ 属于左侧某个路径局部保证域，则由 @h-4b5219aa3a3bbdad 得到对应分量的误差上界。对所有 $j\in J$ 同时应用即可。" Lean 逐字实现该结构：

分量形式（`path_component_guarantee_union_subset_proxy_error`）：
```lean
intro x hx
rcases hx with ⟨q, hj, hxq⟩        -- 取出左侧见证路径 q（"x 属于左侧某个…"）
exact ⟨N.path_domain_subset_source hxq.1,        -- x ∈ U_q ⊆ U
  proxy_path_component_guarantee_error_bound … (hLq q hj) … hj hxq⟩
  -- 由 h-4b5219aa3a3bbdad 的保证域形式得 d_j(φ(x),φ*(x)) ≤ τ_j
```
联合形式（`path_joint_guarantee_union_subset_proxy_error`）同法取见证路径后 `intro j hj`，对每个 $j\in J$ 调用 `path_joint_guarantee_error_bound`——即"对所有 $j\in J$ 同时应用"。

所引用的 h-4b5219aa3a3bbdad 在同一文件中具备全部所需形式且均已证明：`path_local_empirical_upper`（路径链逐点形式）、`proxy_path_local_empirical_upper`（代理逐点形式）、`path_component_guarantee_error_bound` / `proxy_path_component_guarantee_error_bound`（分量保证域形式）、`path_joint_guarantee_error_bound` / `proxy_path_joint_guarantee_error_bound`（联合保证域形式），其内核归结到 `empirical_target_perturbation_upper_point`（h-f16da76e4331b725：三角不等式 + 路径链与目标两个 Lip 证书 + 样本残差界，对同一锚点加权和取下确界），与正文 h-4b5219aa3a3bbdad 的证明完全同构。代理与路径链的换桥使用 `path_chain_eq_represented_proxy_on_path`，即正文"由路径分解，$c_q(x)=\phi(x)$"（依赖 `N.represents proxy` 与 `local_equivalent_extensional_path_chain`）。

## 四、验证记录（可独立复核）

1. **编译**：`lake build formal_oet.vol_03.ch_14_empirical_network_fitting.path_guarantee_domains` → `Build completed successfully (3341 jobs)`，无错误；对该文件单独 `lake env lean …` 重新编译，退出码 0、零输出（无错误、无警告）。
2. **无 `sorry`**：对三条推论定理及六条 h-4b5219aa3a3bbdad 依赖形式逐一 `#print axioms`，结果全部仅为 `[propext, Classical.choice, Quot.sound]`，不含 `sorryAx`；全库正则检索 `sorry|admit|native_decide` 仅命中两处英文文档串中的 "admits"一词，无任何证明级 `sorry`/`admit`。
3. **定义展开核验**（均以 `example … := rfl` 编译通过）：$S_{q,j}=S_j\cap U_q$；$I_{\mathrm{res}}(q)=\{k:S_{q,k}\neq\emptyset\}$；$\hat\varepsilon_{q,j}=\sup+\delta_{o,j}$；$D_{\mathbf A,j}=\inf_y\sum_i A_{i\to j}d_i(x,y)$；两个保证域的集合级展开。
4. **辅助事实核验**（`#check` 通过）：`path_evaluable_subset_evaluable_components`（路径可评估⇒全局可评估）、`reachable_path_domains_cover`（$\bigcup_q U_q=N.U$）、`path_domain_subset_source`（$U_q\subseteq U$）、`path_chain_eq_represented_proxy_on_path`（$U_q$ 上 $c_q=\phi$）。

## 五、假设条件的比较：实现不弱于正文，且在多处严格更强

Lean 核心定理只保留证明真正消费的五条假设：`hd`（全分量扩展伪度量）、`hrep`（$\phi_\mathcal N\equiv_U\phi$）、`hpathV`（各 $U_q\subseteq V^*$，与 $U\subseteq V^*$ 等价）、`hLq`（并入左侧的路径上的 $c_q$ Lip 证书）、`hLstar`（$\mathbf L^*\in\mathscr L(\phi^\natural)|_{V^*}$）。正文其余常设条件被省略，逐一说明为何这不构成缺口（反而使定理更强、正文情形成为特例）：

1. **"$j\in I_{\mathrm{res}}$"**：核心定理对任意 `j : I` 成立。若 $S_j=\emptyset$，由 `path_evaluable_subset_evaluable_components`，任何路径上 $j$ 都不可路径评估，左侧并集为空，包含关系平凡成立。
2. **"有限阈值 $\tau_j$"**：推导"误差上界 ≤ $D+\hat\varepsilon$ ≤ $\tau$"对 $\tau=\top$ 同样有效；正文要求有限只是取值约定，非数学必需。`_text` 版本仍保留 `finite_ennreal`。
3. **"非空 $J$"**：正文需要它是因为 $U_{q,J}$ 以交 $\bigcap_{j\in J}$ 定义（空交=全集的约定会破坏命题）；Lean 直接用逐分量刻画定义联合域，对空 $J$ 结论仍真（此时两侧都是 $U$），对非空 $J$ 与正文交形式逐点相同。`_text` 版本仍保留 `J.Nonempty` 与 `J ⊆ evaluable_components sample`。
4. **采样结构条件（$S_j\subseteq S\cap U\cap\mathrm{dom}(\phi^\natural)$、$S$ 有限）**：证明不消费它们——$S_{q,j}=S_j\cap U_q$ 自动含于工作域 $U_q$（`path_component_sample_subset_path_domain`），$\hat\varepsilon_{q,j}$ 是"在 $S_{q,j}$ 上取上确界加 $\delta_{o,j}$"的自足构造（`empirical_residual_upper_certificate`），对任意采样族都给出合法残差证书。
5. **"$U\subseteq\mathrm{dom}(\phi)$"**：对左侧任一点 $x\in U_q$，`IsLipMatrix` 的定义域子句给出 $U_q\subseteq\mathrm{dom}(c_q)$，结合表示得 $\phi(x)=c_q(x)\neq\bot$；$V^*\subseteq\mathrm{dom}(\phi^\natural)$ 由 `hLstar` 同一子句给出。故该正文假设可由 Lean 假设导出，无须单列。
6. **Lip 证书的辖域**：`hLq` 仅在并入左侧的路径（分量形式：$j$ 路径可评估者；联合形式：$J$ 全覆盖者；`_text` 取两者析取）上要求证书——恰为证明实际消费的部分，弱于正文"每条路径都取 $\mathbf L_q$"的常设，故定理更强且正文情形自然满足。
7. **空样本约定**：正文规定 $S_{q,j}=\emptyset$ 时锚点距离"不在定义范围内"；Lean 采完备格约定（空集下确界为 $\top$）。由于两条定理的并集条件均排除空路径样本，该差异不触及任何被审语句。

`_text` 包装把正文语境前提（$j\in I_{\mathrm{res}}$、$J\subseteq I_{\mathrm{res}}$、$J$ 非空、$\tau_j$ 与 $\boldsymbol\tau$ 有限）全部保留为显式假设，故"正文逐字版"与"最小假设版"同时可用。

## 六、源码已证明的结论与需自行补充的内容

**源码已证明（经我的编译与公理审计确认）：**
- 分量形式包含关系 `path_component_guarantee_union_subset_proxy_error`（正文 (1)）；
- 联合形式包含关系 `path_joint_guarantee_union_subset_proxy_error`（正文 (2)）；
- 正文级合取 `path_guarantee_union_subset_proxy_error_text`（(1)∧(2)，含全部正文语境前提）；
- 其全部依赖链：h-4b5219aa3a3bbdad 的六种形式及各自的 `_text` 包装、路径分解引理（`path_chain_eq_represented_proxy_on_path` 等）、h-f16da76e4331b725 `empirical_target_perturbation_upper_point` 及其残差证书形式、全局与路径级保证域误差引理。

**需自行补充的内容：就本推论而言，无。** 两条包含关系及其正文前提版本均已在源码内完成证明，陈述、定义与证明结构均与正文逐项对应。我在本次审阅中补充的仅是审查侧验证（编译、公理审计、`rfl` 展开核对、锚点唯一性检索），命令与输出已尽列于第四节，可独立复核。

两点附注（均非缺口）：其一，推论之后的两段"注"（与全局保证域的比较、路径采样增广的归约）不属于本推论，未形式化；若将来需要，其原料已在库中（`weighted_anchor_distance_mono_of_subset` = h-48bb46f7ef1c3c2e，`empirical_guarantee_domain_subset_of_certificate_bound_le` = h-4c09ebab1364ae8a 的核心）。其二，若坚持"章级常设语境逐字保留"，可在 `_text` 中再并列 `SamplingStructure` 与 $U\subseteq\mathrm{dom}(\phi)$ 两条不使用假设；由第五节的论证，这纯属风格选择，不影响覆盖性判断。