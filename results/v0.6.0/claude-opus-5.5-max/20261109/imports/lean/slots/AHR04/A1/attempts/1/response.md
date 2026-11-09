# 审阅结论：推论 h-93b9c20ea18b4e59（路径保证域的全局拟合含义）

## 结论

**实现准确、完整，没有数学缺口。** 推论的两部分（分量形式、联合形式）都有对应定理，且证明完整。两条核心定理不需要正文的附加条件：$j\in I_{\rm res}$、$J\subseteq I_{\rm res}$、$J\neq\emptyset$、阈值有限。所以它们证明的命题比正文更强，蕴含正文。

从 Lean 表述回到正文的逐字表述，只差几条定义层面的桥接（第 4 节）。源码没有把这些桥接单独写成引理，我在临时文件里补写并编译通过了。

## 1. 核验方式

- `lake build` 目标模块成功。附件中全部 43 个 `.lean` 文件逐个用 `lake env lean` 编译，均为 rc=0，没有 error、warning 或 sorry。
- 对下列定理执行 `#print axioms`，结果只有 `propext, Classical.choice, Quot.sound`：`path_component_guarantee_union_subset_proxy_error`、`path_joint_guarantee_union_subset_proxy_error`、`path_guarantee_union_subset_proxy_error_text`、`proxy_path_component_guarantee_error_bound`、`proxy_path_joint_guarantee_error_bound`、`path_local_empirical_upper`。
- 在临时文件中做了三件事（未改动附件）：
  - 按 source.md 的字面重新定义 $I_{\rm res}$、$I_{\rm res}(q)$、$S_{q,j}$、$\hat\varepsilon_{q,j}$、$D_{\mathbf A,j}$、$U_{q,j}$、$U_{q,J}=\bigcap_{j\in J}U_{q,j}$。
  - 在正文全部语境前提下，只调用 `path_guarantee_union_subset_proxy_error_text`，推出了推论的两个包含式，编译通过。前提包括：$U\subseteq\mathrm{dom}\phi\cap V^*$、$\mathcal N$ 的输入域为 $U$、$\phi_{\mathcal N}\equiv_U\phi$、$S_j\subseteq S\cap U\cap\mathrm{dom}\phi^\natural$。
  - 构造了具体模型，检验非空性与锐度（第 6 节）。

## 2. 对象对应关系

| 正文 | Lean | 位置 / 说明 |
|---|---|---|
| 有限 $I$，扩展规范空间 | `[Fintype I]`，`hd : ∀ j, ExtendedPseudoMetric X bot (d j)` | 证明只用对称性和三角不等式 |
| $\phi^\natural,\ \phi$ | `target`, `proxy` | |
| 有限算子网络 $\mathcal N$，输入域 $U$ | `N : FiniteOperatorNetwork X bot V`，`N.U` | $U$ 就是 `N.U` |
| $\phi_\mathcal N\equiv_U\phi$ | `hrep : N.represents proxy` | 即 `LocalEquivalent N.extensional_operator proxy N.U`，`operator_network.lean:814` |
| $\mathcal P,\ U_q,\ c_q$ | `N.ReachablePath`，`N.path_domain q.nodes`，`N.path_chain q.nodes` | `operator_network.lean:556, 548, 497` |
| $(V^*,\mathbf L^*)$ | `Vstar, Lstar, hLstar : TargetLipEnvelopeCertificate …` | 即 `IsLipMatrix d target Vstar Lstar`，`structural_priors.lean:25` |
| $U\subseteq V^*$ | `hpathV : ∀ q, N.path_domain q.nodes ⊆ Vstar` | 二者等价，见 B3 |
| $S_j,\ \delta_{o,j}$ | `sample j`, `delta_o j` | |
| $I_{\rm res}$ | `evaluable_components sample` | `empirical_residuals.lean:35` |
| $S_{q,j}=S_j\cap U_q$ | `path_component_sample N sample q j` | `path_sampling.lean:27` |
| $I_{\rm res}(q)$ | `path_evaluable_components N sample q` | 二者相等，见 B1 |
| $\hat\varepsilon_{q,j}$ | `path_empirical_residual_upper …` | 展开为 `(⨆ x∈S_{q,j}, d j (c_q x) (target x)) + delta_o j`，参数顺序与正文一致；`path_sampling.lean:136`，`empirical_residuals.lean:105,116` |
| $D_{\mathbf A,j}(x;E)=\inf_{x_s\in E}\sum_i A_{i\to j}d_i(x,x_s)$ | `weighted_anchor_distance d A j x E` | 用 `A i j` 表示 $A_{i\to j}$，`empirical_residuals.lean:206` |
| $\mathbf L_q\in\mathscr L(c_q)\vert_{U_q}$，$\mathbf A_q=\mathbf L_q+\mathbf L^*$ | `Lq q` 加 `hLq`，`fun i j => Lq q i j + Lstar i j` | `IsLipMatrix` 自带 $U_q\subseteq\mathrm{dom}\,c_q$ |
| $U_{q,j}(\tau_j)$ | `path_component_empirical_guarantee_domain …` | 展开为 `{x | x ∈ U_q ∧ D + ε̂ ≤ τ}`，与正文定义按 `rfl` 相等 |
| $U_{q,J}(\boldsymbol\tau)=\bigcap_{j\in J}U_{q,j}$ | `path_joint_empirical_guarantee_domain …` | $J\neq\emptyset$ 时相等，见 B2 |
| 并的指标与右侧集合 | `∃ q, j ∈ path_evaluable_components … ∧ …`（联合形式为 `J ⊆ …`）；`{x | x ∈ N.U ∧ d j (proxy.func x) (target.func x) ≤ τ}` | 逐项一致 |

对应的定理：
- 分量形式：`path_guarantee_domains.lean:520`
- 联合形式：`path_guarantee_domains.lean:553`
- 正文形式包装：`path_guarantee_domains.lean:590`

## 3. 证明链（源码已证明）

正文的证明是：$x$ 属于某个 $U_{q,j}(\tau_j)$，于是由 h-4b5219aa3a3bbdad 得到该分量的误差界；联合形式对每个 $j\in J$ 应用同一结论。

Lean 的证明逐步对应：
1. 从左侧取出 $q$、$j\in I_{\rm res}(q)$ 以及 $x$ 的成员关系。
2. 由 `path_domain_subset_source` 得 $x\in U$。
3. 由 `proxy_path_component_guarantee_error_bound`（h-4b5219aa3a3bbdad，`path_guarantee_domains.lean:152`）得误差界。它由以下几步组成：
   - `path_local_empirical_upper`（:54）：在 $U_q$ 上给出 $d_j(c_qx,\phi^\natural x)\le D+\hat\varepsilon_{q,j}$。内部先用 `empirical_residual_upper_certificate` 得到残差证书，再用 `empirical_target_perturbation_upper_point`（h-f16da76e4331b725，`structural_priors.lean:60`）完成"三角不等式 + 两个 Lip 证书 + 同一锚点取下确界"。
   - 代入保证域条件，得到 $\le\tau_j$。
   - `path_chain_eq_represented_proxy_on_path`（`path_sampling.lean:220`）把 $c_q(x)$ 换成 $\phi(x)$。
4. 联合形式经 `path_joint_guarantee_error_bound`（:210）对每个 $j\in J$ 走同一条链。

## 4. 需要自行补充的桥接

以下内容源码没有单独陈述，我已在临时文件中编译验证：

- **B1**：$I_{\rm res}(q)=\{j\in I_{\rm res}:S_{q,j}\neq\emptyset\}$ 等于 `path_evaluable_components`。理由：$S_{q,j}\subseteq S_j$，所以 $S_{q,j}\ne\emptyset\Rightarrow S_j\ne\emptyset$；源码 `path_evaluable_subset_evaluable_components`（`path_sampling.lean:103`）给出了这一方向。
- **B2**：Lean 的联合域定义为 $\{x\in U_q:\forall j\in J,\dots\}$。当 $J\neq\emptyset$ 时，取 $j_0\in J$，有 $x\in U_{q,j_0}\subseteq U_q$，因此它等于 $\bigcap_{j\in J}U_{q,j}(\tau_j)$。$J=\emptyset$ 时 Lean 给出 $U_q$，正文的空交没有意义，但正文已排除这种情形。此时 Lean 的结论退化为 $U\subseteq U$，仍然成立。
- **B3**：`hpathV` 与 $U\subseteq V^*$ 等价。⇐ 方向用 `path_domain_subset_source`，⇒ 方向用 `reachable_path_domains_cover`（$\bigcup_qU_q=U$）。
- **B4**：正文前提 $U\subseteq\mathrm{dom}\phi$ 在 Lean 中不必假设。由 `hrep` 和 `dom_extensional_operator_eq`：$x\in U$ 时 $\phi(x)=\phi_\mathcal N(x)\neq\bot$。推论本身也用不到这一条。
- **B5**：正文为每条满足 $I_{\rm res}(q)\neq\emptyset$ 的路径取定 $\mathbf L_q$，这蕴含核心定理的 `hLq`；在 $J\neq\emptyset$ 时也蕴含包装定理中的析取型 `hLq`。
- **B6**：只想要分量形式时，可以直接用 :520 的核心定理；也可以在包装定理中取 $J=\{j\}$、$\boldsymbol\tau\equiv\tau_j$，此时析取型 `hLq` 退化为单一条件。

## 5. 无害差异（均为泛化或表述问题）

- **核心定理更强。** 去掉的附加条件只覆盖平凡的边界情形：$j\notin I_{\rm res}$ 时左侧为空；$\tau=\top$ 时右侧等于 $U$；$J=\emptyset$ 时两侧都等于 $U$。
- **`_text` 包装中的附加假设只是标注。** 它们以 `have _ := …` 形式出现，不参与证明。这不算错误，但它们在数学上是多余的。
- **采样结构的约束未被使用。** 正文要求 $S$ 有限、$S_j\subseteq S\cap U\cap\mathrm{dom}\phi^\natural$ 并固定 $\delta_o$；Lean 对任意 `sample`、`delta_o` 都成立。推论只用到 $S_{q,j}=S_j\cap U_q$，而 $U\subseteq V^*\subseteq\mathrm{dom}\phi^\natural$ 已由 `IsLipMatrix` 推出。
- **ENNReal 约定。** 阈值与矩阵元允许取 $\top$，约定 $0\cdot\top=0$。由于并的指标保证 $S_{q,j}\neq\emptyset$，空下确界不会出现在左侧。
- **网络类型一致。** 网络用的是 `FiniteOperatorNetwork`，与正文一致；无环网络经 `to_finite` 后保持 `U` 和外延算子，同样被覆盖。
- **证书存在性的预设一致。** `Lq` 是函数，对应正文"每条路径取定 $\mathbf L_q$"的预设。若某条路径的受限 Lip 族为空（伪度量不分离时可能发生），正文的 $U_{q,j}$ 无定义，Lean 也给不出 `hLq`。这时可以改用逐路径定理 `proxy_path_component_guarantee_error_bound`，对有证书的路径取并。

## 6. 非空性与锐度（具体模型，已编译）

模型设定：
- $X=\mathrm{Option\,Bool}$，$\bot=\mathrm{none}$，$I=\mathrm{Unit}$。
- 距离：$d(x,y)=0$（$x=y$）；$\top$（$x\neq y$ 且其中之一为 none）；其余为 $1$。
- $\phi=\mathrm{id}$，$\phi^\natural(\mathrm{some}\,b)=\mathrm{some\,true}$。
- $\mathcal N$ 取附件中的单节点网络，于是 $U=\{\mathrm{some\,true},\mathrm{some\,false}\}$，只有一条路径 $q_0$。
- $S=\{\mathrm{some\,true}\}$，$\delta_o=0$，$V^*=U$，$\mathbf L^*=0$，$\mathbf L_{q_0}=1$。

计算得 $\hat\varepsilon_{q_0}=0$，$D(\mathrm{some\,false};S_{q_0})=1$，所以 $\mathrm{some\,false}\in U_{q_0}(1)$。推论给出误差 $\le1$，而真实误差恰为 $1$。

由此可见：
- 包装定理的全部假设（包括正文附加条件）可以同时满足，左侧非空，结论不是空真；
- 该界在这一点可以取到。

若改用同样合法的 $\mathbf L_{q_0}=2$，该点不再属于 $U_{q_0}(1)$，但真实误差仍 $\le1$。这说明包含关系一般只是单向的，正文也只断言了包含。另外用 $I=\mathrm{Bool}$、两个分量各取不同样本，验证了联合分支。

## 附录：桥接引理（可复核，非必须提交）

以下代码在临时文件中编译通过，只依赖标准公理：

```lean
-- open: ch_01_foundations, ch_05_operator_networks, ch_12_…, ch_14_empirical_network_fitting
theorem path_evaluable_eq (N : FiniteOperatorNetwork X bot V) (sample : I → Set X)
    (q : N.ReachablePath) :
    path_evaluable_components N sample q =
      {j | j ∈ evaluable_components sample ∧ (path_component_sample N sample q j).Nonempty} := by
  ext j
  exact ⟨fun h => ⟨path_evaluable_subset_evaluable_components N sample q h, h⟩, fun h => h.2⟩

theorem joint_eq_iInter (d : I → X → X → ENNReal) (A : I → I → ENNReal)
    (N : FiniteOperatorNetwork X bot V) (sample : I → Set X) (q : N.ReachablePath)
    (J : Set I) (hJ : J.Nonempty) (eps tau : I → ENNReal) :
    path_joint_empirical_guarantee_domain d A N sample q J eps tau =
      ⋂ j ∈ J, path_component_empirical_guarantee_domain d A N sample q j (eps j) (tau j) := by
  ext x; simp only [Set.mem_iInter]
  constructor
  · rintro ⟨hxU, hx⟩ j hj; exact ⟨hxU, hx j hj⟩
  · intro hx; rcases hJ with ⟨j₀, hj₀⟩; exact ⟨(hx j₀ hj₀).1, fun j hj => (hx j hj).2⟩

theorem hpathV_iff (N : FiniteOperatorNetwork X bot V) (Vstar : Set X) :
    (∀ q : N.ReachablePath, N.path_domain q.nodes ⊆ Vstar) ↔ N.U ⊆ Vstar := by
  constructor
  · intro h x hx
    rw [← N.reachable_path_domains_cover] at hx
    rcases Set.mem_iUnion.mp hx with ⟨q, hq⟩; exact h q hq
  · intro h q x hx; exact h (N.path_domain_subset_source hx)

theorem U_sub_dom (N : FiniteOperatorNetwork X bot V) (proxy : Operator X bot)
    (hrep : N.represents proxy) : N.U ⊆ dom proxy := by
  intro x hx
  have h1 : x ∈ dom N.extensional_operator := by rw [N.dom_extensional_operator_eq]; exact hx
  change proxy.func x ≠ bot; rw [← hrep x hx]; exact h1
```

**可选改进。** 若希望 Lean 表述逐字贴合正文，可以把上面四条引理并入源码，并把 `_text` 包装拆成分量、联合两条定理，各自只带所需的 `hLq`。这些只是表述层面的调整，不影响正确性。