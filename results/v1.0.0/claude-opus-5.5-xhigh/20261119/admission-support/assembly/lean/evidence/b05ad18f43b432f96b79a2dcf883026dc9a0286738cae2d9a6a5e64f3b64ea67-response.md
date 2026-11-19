**结论：实现准确且完整。** `path_guarantee_union_subset_proxy_error_text` 及其调用的分量版、联合版两个定理，覆盖了推论 #h-93b9c20ea18b4e59 的两条包含关系。我没有找到反例，也没有发现需要修补的缺口。Lean 版只在几处无关紧要的地方比正文更一般（见第 4 节）。

**验证情况：**
- `lake build formal_oet.vol_03.ch_14_empirical_network_fitting.path_guarantee_domains` 构建成功。
- 全工程搜索不到 `sorry`、`admit` 或自定义 `axiom`。
- 三个相关定理的 `#print axioms` 只依赖 `propext`、`Classical.choice`、`Quot.sound`。

## 1. 定义层对应

| 正文 | Lean | 说明 |
|---|---|---|
| 有限算子网络 $\mathcal N$，输入域为 $U$ | `N : FiniteOperatorNetwork X bot V`，`N.U` | |
| $\phi_\mathcal N\equiv_U\phi$ | `hrep : N.represents proxy` | 定义为 `LocalEquivalent N.extensional_operator proxy N.U` |
| 路径集 $\mathcal P$、路径域 $U_q$、路径链 $c_q$ | `N.ReachablePath`、`N.path_domain q.nodes`、`N.path_chain q.nodes` | |
| $(V^*,\mathbf L^*)$ | `TargetLipEnvelopeCertificate d target Vstar Lstar` | 含 $V^*\subseteq\mathrm{dom}\,\phi^\natural$ |
| $\mathbf L_q\in\mathscr L(c_q)\vert_{U_q}$ | `IsLipMatrix d (N.path_chain q.nodes) (N.path_domain q.nodes) (Lq q)` | 含 $U_q\subseteq\mathrm{dom}\,c_q$ |
| $\mathbf A_q=\mathbf L_q+\mathbf L^*$ | `fun i j => Lq q i j + Lstar i j` | `L i j` 即 $[\cdot]_{i\to j}$ |
| $S_{q,j}=S_j\cap U_q$ | `path_component_sample` | |
| $I_{\mathrm{res}}(q)$ | `path_evaluable_components` | 见下方注 |
| $\hat\varepsilon_{q,j}=\sup_{S_{q,j}} d_j(c_q,\phi^\natural)+\delta_{o,j}$ | `path_empirical_residual_upper` | 展开为 `empirical_residual_raw_sup + delta_o j` |
| $D_{\mathbf A,j}(x;S)=\inf_{y\in S}\sum_i A_{i\to j}d_i(x,y)$ | `weighted_anchor_distance` | |
| $U_{q,j}(\tau_j)$ | `path_component_empirical_guarantee_domain` | 即 `anchor_gap_sublevel`，定义为 `{x ∈ U_q ∣ D + ε̂ ≤ τ}` |
| $U_{q,J}(\boldsymbol\tau)=\bigcap_{j\in J}U_{q,j}(\tau_j)$ | `path_joint_empirical_guarantee_domain`，写成 `{x ∈ U_q ∣ ∀ j ∈ J, …}` | |
| 并集 $\bigcup_{q:\,j\in I_{\mathrm{res}}(q)}$，右侧集合 $\{x\in U:\dots\}$ | `{x ∣ ∃ q, j ∈ path_evaluable_components … ∧ x ∈ …}`，`{x ∣ x ∈ N.U ∧ …}` | |

注：Lean 里 `path_evaluable_components` 是 `{j ∣ S_{q,j} 非空}`，不先限定 $j\in I_{\mathrm{res}}$。由于 $S_{q,j}\subseteq S_j$（源码引理 `path_evaluable_subset_evaluable_components`），两种写法一致。

## 2. 源码已证明的结论

**分量形式**：`path_component_guarantee_union_subset_proxy_error`。证明链如下：
1. 取出见证路径 `q`。
2. `proxy_path_component_guarantee_error_bound` 给出误差界，它依次依赖：
   - `path_component_guarantee_error_bound` 和 `empirical_component_guarantee_error_bound`；
   - `path_local_empirical_upper`，它即 #h-4b5219aa3a3bbdad；
   - `empirical_target_perturbation_upper_point`：对每个锚点用三角不等式，代理侧 Lip、残差、目标侧 Lip 三项相加，再用 `ENNReal.iInf_add` 取下确界；
   - `empirical_residual_upper_certificate`，提供 $\hat\varepsilon_{q,j}$ 的残差证书。
3. `path_chain_eq_represented_proxy_on_path`（由 `local_equivalent_extensional_path_chain` 加 `hrep` 得到）把 $c_q$ 换成 $\phi$。
4. `path_domain_subset_source` 给出 $x\in U$。

**联合形式**：`path_joint_guarantee_union_subset_proxy_error`。路线相同，换用 `path_joint_guarantee_error_bound`，对每个 $j\in J$ 应用 `path_local_empirical_upper`。

**正文前提版**：`path_guarantee_union_subset_proxy_error_text` 把两者合在一起。假设 `hLq` 写成析取 `j ∈ I_res(q) ∨ J ⊆ I_res(q)`，正好是两部分各自需要的路径集合之并。

## 3. 需要自行补充的桥接（不是缺口）

正文写法和源码写法之间有三处差别，源码里没有专门的引理。我已在临时文件中证明它们并通过编译（未提交，也没有修改附件）：

1. **假设 $U\subseteq V^*$ 等价于 `hpathV : ∀ q, path_domain q ⊆ Vstar`。** 正向用 `path_domain_subset_source`，反向用 `reachable_path_domains_cover`。
2. **$U\subseteq\mathrm{dom}\,\phi$ 不必单独假设。** 它由 `hrep` 和 `dom_extensional_operator_eq` 自动得到。
3. **$J$ 非空时，`∀ j ∈ J` 的写法等于 $\bigcap_{j\in J}U_{q,j}(\tau_j)$。** 取 $j_0\in J$ 即可得到 $x\in U_q$。

借助这三点，我从源码定理推出了与正文逐字对应的 ⋃/⋂ 版本（前提为 `N.U ⊆ Vstar`、对所有 q 给出 `hLq`、`J.Nonempty`），编译通过，公理同上。证明主体如下：

```lean
-- 分量部分
obtain ⟨q, hq, hxq⟩ := hx   -- 来自 ⋃
exact path_component_guarantee_union_subset_proxy_error d hd target proxy N sample
  delta_o Vstar Lq Lstar j tau_j hrep hpathV (fun q _ => hLq q) hLstar ⟨q, hq, hxq⟩
-- 联合部分：先用 J 非空把 ⋂ 还原为 ⟨x ∈ U_q, ∀ k ∈ J, …⟩，再调用
-- path_joint_guarantee_union_subset_proxy_error
```

## 4. Lean 版比正文更一般的地方

以下几处都不会让结论变弱。把正文的数据代入后，得到的正好是正文的陈述。

- **`_text` 版的若干假设没有被使用**（用 `have _ :=` 保留）：$\tau$ 有限、$J$ 非空、$j\in I_{\mathrm{res}}$、$J\subseteq I_{\mathrm{res}}$。因此 Lean 结论更强，例如允许 $\tau=\top$。
- **核心定理不要求 $S_j\subseteq U\cap\mathrm{dom}\,\phi^\natural$，也不要求采样有限。** 原因有两点：
  - $S_{q,j}$ 定义时已经与 $U_q$ 取交；
  - 若采样点不在 $\mathrm{dom}\,\phi^\natural$ 内，则 $d_j(c_q(x_s),\bot)=\top$，残差为 $\top$，在有限阈值下保证域为空。
- **当 $J=\emptyset$ 时**，Lean 的联合域退化为 $U_q$，结论退化为平凡包含。正文本来就排除了这种情形。
- **每条路径只用一个与分量无关的矩阵 $\mathbf L_q$，并不损失一般性。** 即使正文允许按分量选不同的 $\mathbf L_q^{(j)}$，也可以取第 $j$ 列来自 $\mathbf L_q^{(j)}$ 的拼接矩阵。原因是 `IsLipMatrix` 的条件对每个输出分量 $j$ 只约束第 $j$ 列，拼接后仍是合法证书；而 `weighted_anchor_distance … j` 也只用到第 $j$ 列。

总之，正文推论的每个假设都能在 Lean 中找到对应（或在 Lean 中更弱），两条结论在第 3 节的等价改写下逐字一致，证明完整且无未证部分。