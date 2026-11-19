**结论：** Lean 实现的结论部分正确，与正文一致，但不算完全覆盖正文命题。原因在前提：Lean 要求代理网络的**每一条**可达路径都带一个 Lip 证书 `hLq : ∀ q : N.ReachablePath, IsLipMatrix …`。正文只要求出现在并集指标集里的路径（$j\in I_{\rm res}(q)$ 或 $J\subseteq I_{\rm res}(q)$）带证书。当度量族非分离时，可以构造出正文适用、Lean 定理无法调用的例子。补齐只需把这个前提改成条件形式，证明几乎不用改。

## 1. 对应关系

| 正文 | Lean |
|---|---|
| 有限网络 $\mathcal N$，输入域 $U$ | `N : FiniteOperatorNetwork X bot V`，`N.U` |
| $\phi_{\mathcal N}\equiv_U\phi$ | `hrep : N.represents proxy` |
| $\phi^\natural$，$(V^*,\mathbf L^*)$ | `target`、`Vstar`、`Lstar`、`hLstar : TargetLipEnvelopeCertificate …` |
| $U\subseteq V^*$ | `hpathV : ∀ q, N.path_domain q.nodes ⊆ Vstar`（因路径域覆盖 `N.U`，两者等价，我已在 Lean 中验证） |
| $\mathcal P$，$U_q$，$c_q$ | `N.ReachablePath`、`N.path_domain q.nodes`、`N.path_chain q.nodes` |
| $S_{q,j}$，$I_{\rm res}(q)$，$I_{\rm res}$ | `path_component_sample`、`path_evaluable_components`、`evaluable_components sample` |
| $\hat\varepsilon_{q,j}$ | `path_empirical_residual_upper d target N sample delta_o q j`（上确界加 $\delta_{o,j}$，参数顺序一致） |
| $\mathbf L_q$，$\mathbf A_q=\mathbf L_q+\mathbf L^*$ | `Lq q`，`fun i j => Lq q i j + Lstar i j`（约定 `L i j` $=L_{i\to j}$） |
| $D_{\mathbf A,j}(x;E)$ | `weighted_anchor_distance d A j x E` |
| $U_{q,j}(\tau_j)$ | `path_component_empirical_guarantee_domain …` $=\{x\in U_q: D+\hat\varepsilon\le\tau\}$ |
| $U_{q,J}(\boldsymbol\tau)=\bigcap_{j\in J}U_{q,j}$ | `path_joint_empirical_guarantee_domain …`：显式含 $x\in U_q$，$J$ 非空时与交集相同 |
| 两条包含式 | `path_component_guarantee_union_subset_proxy_error`、`path_joint_guarantee_union_subset_proxy_error`；`_text` 版合并两者 |

- **并集指标：** 正文的 $I_{\rm res}(q)$ 要求 $j\in I_{\rm res}$ 且 $S_{q,j}\ne\emptyset$。因 $S_{q,j}\subseteq S_j$，后者已蕴含前者，所以与 Lean 的 `∃ q, j ∈ path_evaluable_components N sample q ∧ …` 一致。
- **右侧集合：** `{x | x ∈ N.U ∧ d j (proxy.func x) (target.func x) ≤ tau}` 与 $\{x\in U: d_j(\phi(x),\phi^\natural(x))\le\tau_j\}$ 一致。

## 2. 源码已证明的内容

- **证明链：** 取并集中的元素，得到 $q$、`hj` 与 `hxq`。由 `path_domain_subset_source` 得 $x\in U$。再用 `proxy_path_component_guarantee_error_bound` 得到分量误差上界；它依次依赖：
  - `path_component_guarantee_error_bound`
  - `empirical_component_guarantee_error_bound` 与 `path_local_empirical_upper`
  - `empirical_target_perturbation_upper_point_from_residual_certificate`
  - 以及 `path_chain_eq_represented_proxy_on_path`（把路径链换成代理）。
  
  联合形式走相同路线，改用 `path_joint_guarantee_error_bound`。
- **编译与公理检查：** 我在本地运行 `lake build`，结果是 `formal_oet.vol_03.ch_14_empirical_network_fitting.path_guarantee_domains` 构建成功。三个推论的 `#print axioms` 只显示 `propext, Classical.choice, Quot.sound`，源码中没有 `sorry`。
- **`_text` 版的附加前提：** $j\in I_{\rm res}$、$J\subseteq I_{\rm res}$、$J$ 非空、阈值有限，这些都写成了前提但在证明中未被使用。这不影响正确性：去掉它们结论仍然成立，Lean 版只是更一般。
- **其它省略的正文条件：** Lean 没有要求 $S_j\subseteq S\cap U\cap\mathrm{dom}\,\phi^\natural$、采样集有限、$U\subseteq\mathrm{dom}\,\phi$。前两条证明用不到；最后一条可由表示关系推出。这些也都是推广，不是缺口。

## 3. 不足：全路径 Lip 证书前提（可复核反例）

**结论：** 正文中 $\mathbf L_q$ 是在"设 $q\in\mathcal P$、$j\in I_{\rm res}(q)$"之后才选取的，推论的并集也只经过这些 $q$。Lean 却要求对所有可达路径给出 `IsLipMatrix`。

**为什么这不是平凡条件：** 即使矩阵允许取 $\top$，在 $U_q$ 上存在 Lip 矩阵也等价于路径链 $c_q$ 保持全分量零距关系：若对所有 $i$ 都有 $d_i(x,y)=0$，则对所有 $j$ 必须有 $d_j(c_qx,c_qy)=0$。我已在本地用 Lean 证明这个等价，充分性方向取全 $\top$ 矩阵即可。
- 在**分离**的度量族下这个条件自动成立。此时可以给不在指标集里的路径填上全 $\top$ 矩阵，Lean 版与正文等价。
- 在**非分离**的度量族下（`gauge_space` 中明确允许这种情形，见 `IsNonSeparating`）就可能失败。

**反例：**
- **空间：** $X=\{\bot,a,b,c\}$，$I=\{*\}$；$d(a,b)=0$，$d(a,c)=d(b,c)=1$，$d(x,\bot)=+\infty$（$x\ne\bot$）。这是一个扩展伪度量。
- **网络：** 两个节点。
  - $\psi_1$：$c\mapsto c$，其余点映到 $\bot$。
  - $\psi_2$：$a\mapsto a$，$b\mapsto c$，其余点映到 $\bot$。
  - 入口：$c\to\beta_1$，$a,b\to\beta_2$；输出一律终止。
  - 于是 $U=\{a,b,c\}$，两条路径为 $q_1=(\beta_1)$，$U_{q_1}=\{c\}$；$q_2=(\beta_2)$，$U_{q_2}=\{a,b\}$。
- **其余数据：** 代理 $\phi=\phi_{\mathcal N}$；目标 $\phi^\natural=\mathrm{id}$；$V^*=U$，$\mathbf L^*=1$；采样 $S_*=\{c\}$；$\delta_o=0$。
- **正文一侧：** $I_{\rm res}(q_1)=\{*\}$，$I_{\rm res}(q_2)=\emptyset$，所以正文只需要 $\mathbf L_{q_1}$，取 $0$ 就合法。推论成立且不空洞：$c\in U_{q_1,*}(0)$，并且 $d(\phi c,c)=0$。
- **Lean 一侧：** `hLq` 还要求 $q_2$ 的 Lip 矩阵，需要 $1=d(\psi_2a,\psi_2b)\le \sum_i L_{i\to *}\,d_i(a,b)=L\cdot 0=0$（在 ENNReal 中 $\top\cdot0=0$），这不可能成立。因此 Lean 推论在这个例子中无法调用。

我在本地 Lean 中验证了这个反例的各个部分（`original_hLq_unsatisfiable`、`text_hLq_satisfiable`、`text_conclusion_nonvacuous`），公理同样只有三条标准公理。这些是我补充的验证，未提交到源码中。

## 4. 补齐方式

把前提改成条件形式，证明只需改成调用 `hLq q hj`。以下版本我已在本地编译通过：

```lean
theorem path_component_guarantee_union_subset_proxy_error_weak
    … (hUV : N.U ⊆ Vstar)
    (hLq : ∀ q : N.ReachablePath, j ∈ path_evaluable_components N sample q →
      IsLipMatrix d (N.path_chain q.nodes) (N.path_domain q.nodes) (Lq q))
    (hLstar : TargetLipEnvelopeCertificate d target Vstar Lstar) :
    {x | ∃ q, j ∈ path_evaluable_components N sample q ∧ x ∈ …} ⊆
      {x | x ∈ N.U ∧ d j (proxy.func x) (target.func x) ≤ tau} := by
  rintro x ⟨q, hj, hxq⟩
  exact ⟨N.path_domain_subset_source hxq.1,
    proxy_path_component_guarantee_error_bound d hd target proxy N sample delta_o q
      Vstar (Lq q) Lstar j tau hrep
      (fun _ hy => hUV (N.path_domain_subset_source hy)) (hLq q hj) hLstar hj hxq⟩
```

联合形式相同，只把条件换成 `J ⊆ path_evaluable_components N sample q → …`，并调用 `proxy_path_joint_guarantee_error_bound`。新的弱前提版本可推出原版本，所以原版本是它的特例。另一种做法是保留原陈述，但说明它只对应"每条路径都已固定 Lip 证书族"这种更强的读法。

**总结：**
- 推论的结论（两条包含式）、所有对象的定义和证明链都已在源码中正确证明。
- 缺口只在 Lip 证书前提的作用范围；只有在度量族非分离、且某条不在指标集中的路径链不保持零距关系时才会出现。
- 按第 4 节改写后即可完整覆盖正文。