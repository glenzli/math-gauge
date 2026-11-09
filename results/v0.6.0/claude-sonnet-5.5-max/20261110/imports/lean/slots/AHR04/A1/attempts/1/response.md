## 审阅结论

**实现准确且完整，我没有发现需要补证的实质缺口。** 推论 #h-93b9c20ea18b4e59（`source.md` 第 242–259 行）的两个包含式及其证明，在 Lean 中都有对应定理，并已在源码中完整证明。

核对环境：Lean 4.29.1 加指定 mathlib。`lake build` 通过。`formal_oet` 内没有 `sorry`、`admit` 或自定义 `axiom`。对三条核心定理和局部上界做 `#print axioms`，只出现 `propext`、`Classical.choice`、`Quot.sound`。

## 1. 对应关系

Lean 文件为 `vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean`（以下简称 PGD），以及同目录的 `path_sampling.lean`（以下简称 PS）。

| 正文 | Lean |
|---|---|
| 第一式（分量式） | `path_component_guarantee_union_subset_proxy_error`（PGD:520） |
| “更一般地”（联合式） | `path_joint_guarantee_union_subset_proxy_error`（PGD:553） |
| 两式合并并保留正文前提 | `path_guarantee_union_subset_proxy_error_text`（PGD:590） |
| 证明所引的局部上界 #h-4b5219aa3a3bbdad | `path_local_empirical_upper`（PGD:54），经 `proxy_path_component_guarantee_error_bound`（:152）和 `proxy_path_joint_guarantee_error_bound`（:244）换到代理 φ 上 |
| 证明中隐含的 $c_q=\phi$（在 $U_q$ 上） | `path_chain_eq_represented_proxy_on_path`（PS:220） |

对象逐项对应：

- **U、网络 𝒩**：`N : FiniteOperatorNetwork X bot V`，`U = N.U`。
- **φ_𝒩 ≡_U φ**：`hrep : N.represents proxy`。
- **U ⊆ dom φ**：由 `hrep` 加 `dom_extensional_operator_eq` 推出。
- **U ⊆ V\***：`hpathV`（逐路径写法）与 `N.U ⊆ Vstar` 等价，依据是 `reachable_path_domains_cover`。
- **(V\*, L\*)**：`TargetLipEnvelopeCertificate d target Vstar Lstar`，即 `IsLipMatrix d target Vstar Lstar` 的包装。
- **𝒫、U_q、c_q**：`N.ReachablePath`、`N.path_domain q.nodes`、`N.path_chain q.nodes`。
- **S_{q,j}**：`sample j ∩ N.path_domain q.nodes`。
- **I_res(q)**：`path_evaluable_components N sample q`。因 S_{q,j}≠∅ 蕴含 S_j≠∅，与正文“j∈I_res 且 S_{q,j}≠∅”一致。
- **ε̂_{q,j}**：`path_empirical_residual_upper ...`，等于对 `d j (c_q x) (target x)` 在 `S_{q,j}` 上取上确界再加 `delta_o j`。
- **L_q ∈ 𝓛(c_q)|_{U_q}，A_q = L_q + L\***：`hLq` 和 `fun i j => Lq q i j + Lstar i j`。
- **D_{A,j}(x;E)**：`weighted_anchor_distance`，即 `⨅ y∈E, ∑ i, A i j * d i x y`。
- **U_{q,j}(τ_j)、U_{q,J}(τ)**：`path_component_empirical_guarantee_domain`、`path_joint_empirical_guarantee_domain`。
- **右端**：`{x | x ∈ N.U ∧ d j (proxy.func x) (target.func x) ≤ tau}`，联合式为 `∀ i ∈ J, …`。

## 2. 核对要点

- **并集下标**：Lean 写作 `{x | ∃ q, j ∈ I_res(q) ∧ x ∈ U_{q,j}}`（联合式为 `J ⊆ I_res(q)`），与正文的 ⋃ 一致。
- **右端针对 φ 本身**：右端是代理 φ 的真实误差，不是路径链 c_q 的误差。从 c_q 换到 φ 靠的是 `hrep` 加 `path_chain_eq_represented_proxy_on_path`。Lean 在 `proxy_path_*` 里完成了这一步，正文证明里只是一句话带过。
- **量词**：证书选择被显式化为全称量化的函数 `Lq`。所以结论是“对任意合法证书选择成立”，与正文“取 L_q”相符。
- **证明结构**：Lean 与正文的“取某路径、套局部上界、对所有 j 同时应用”一致。

## 3. 与正文字面不同的地方（均不构成缺口）

1. **`_text` 版的五个前提未被使用。**
   - 这五个是 `hj_evaluable`、`hJ_evaluable`、`htau_j_finite`、`hJ_nonempty`、`htau_finite`，证明中只作 `have _ :=` 丢弃。
   - 前两个已被并集下标蕴含（`path_evaluable_subset_evaluable_components`）。后三个对包含式无作用。
   - 保留它们是为了与正文前提逐字对齐。真正的内容在不含这些前提的两条核心定理里。
2. **`SamplingStructure` 没有作为前提。**
   - 对路径样本，它的域条件 `x ∈ U ∧ x ∈ dom φ ∧ x ∈ dom φ♮` 可由 `hrep`、`hpathV`、`hLstar` 推出（见下文 S6）。所以 Lean 更一般，没有丢内容。
3. **联合域用 `∀ j∈J` 定义，不是字面上的 ⋂。** 对非空 J 二者相等（见下文 S3）。
4. **`_text` 版的 `hLq` 条件是“`j∈I_res(q)` 或 `J⊆I_res(q)`”。**
   - 分量式与联合式因此共用一族 `Lq`。
   - 若要两族不同的证书，用两条核心定理即可。
   - 若把 L_q 读作可随 j 变化，联合域的 ⋂ 形式也成立（见下文 S5）。
5. **推论只是单向包含，不是等式，也不给出覆盖性。** Lean 与正文一致。例如 target=proxy 时右端恒为 U，而左端受锚点距离限制。这一点我是推理得出，没有逐例在 Lean 里验证。

## 4. 已证明的内容与需自行补充的内容

**源码已证明：**
- 三条推论定理。
- 局部上界及其代理版。
- 路径链等于被表示的代理。
- 网络域的覆盖与包含事实。

**需自行补充的有两类。**

第一类是正文中引用但所附 `source.md` 未给出的定义：#h-9655cbb9401e5c90（目标 Lip 包络）、#h-6f9e054ce01ccfef（采样结构、δ_o、D_{A,j}）、#h-67ea98399b9a982d（保证域）。我按题面约定可使用这些定义，仅凭 Lean 文档串和本章用法核对其含义。若原定义带有额外条件（例如矩阵有限值），只会增加前提，不会破坏该包含关系。

第二类是桥接事实。源码里没有，但都很短，我在临时文件里用 `lake env lean` 验证通过，没有改动附件：

- **S1**：`hpathV ↔ N.U ⊆ Vstar`。
- **S2**：`represents → N.U ⊆ dom proxy`。
- **S3**：非空 J 时，联合域等于分量域的交集。
- **S4**：第一式是联合式取 `J={j}` 的特例。
- **S5**：证书随 j 变化时的 ⋂ 形式，要求 `J.Nonempty`。
- **S6**：路径样本满足 `SamplingStructure` 的域条件。

S1 和 S3 的代码如下（需要 `open formal_oet.vol_01.ch_05_operator_networks formal_oet.vol_02.ch_07_fitting_foundations formal_oet.vol_03.ch_12_residuals_and_substitution formal_oet.vol_03.ch_14_empirical_network_fitting`）：

```lean
theorem pathV_iff (N : FiniteOperatorNetwork X bot V) (Vstar : Set X) :
    (∀ q : N.ReachablePath, N.path_domain q.nodes ⊆ Vstar) ↔ N.U ⊆ Vstar := by
  constructor
  · intro h x hx
    have hx' : x ∈ ⋃ p : N.ReachablePath, N.path_domain p.nodes := by
      rw [N.reachable_path_domains_cover]; exact hx
    rcases Set.mem_iUnion.mp hx' with ⟨q, hq⟩
    exact h q hq
  · intro h q x hx
    exact h (N.path_domain_subset_source hx)

theorem path_joint_eq_iInter (d : I → X → X → ENNReal) (A : I → I → ENNReal)
    (N : FiniteOperatorNetwork X bot V) (sample : I → Set X)
    (q : N.ReachablePath) (J : Set I) (eps tau : I → ENNReal) (hJ : J.Nonempty) :
    path_joint_empirical_guarantee_domain d A N sample q J eps tau =
      ⋂ j ∈ J, path_component_empirical_guarantee_domain d A N sample q j (eps j) (tau j) := by
  ext x
  simp only [path_joint_empirical_guarantee_domain, path_component_empirical_guarantee_domain,
    empirical_joint_guarantee_domain, empirical_component_guarantee_domain, anchor_gap_sublevel,
    Set.mem_iInter, Set.mem_setOf_eq, path_sample_family]
  constructor
  · rintro ⟨hx, h⟩ j hj
    exact ⟨hx, h j hj⟩
  · intro h
    rcases hJ with ⟨j0, hj0⟩
    exact ⟨(h j0 hj0).1, fun j hj => (h j hj).2⟩
```

**非空洞性检查。** 我另做了一个具体实例，`_text` 定理的全部前提可逐一给出，且分量式左端非空：

- 空间与度量：`X = Option Bool`，`bot = none`，`I = Unit`，`d` 为离散扩展度量（对角线为 0，其余为 ⊤）。
- 算子与网络：`φ = restrict_operator id {some true}`，`N = single_node_network φ`，`target = proxy = φ`。
- 证书：`Lq = L* =` 全 1 矩阵，`V* = N.U`。
- 采样与阈值：`sample = {some true}`，`δ_o = 0`，`τ = 0`。

## 5. 可选加固（非必需）

- 补一条 `path_joint_empirical_guarantee_domain = ⋂` 的引理（即 S3），让联合域与正文定义字面一致。
- 补一条“由联合式推分量式”的引理（即 S4），体现“更一般地”。
- 若要处理只有部分路径有证书的情形，可把 `hLq` 改为对路径子集 `Q` 要求，结论改为对 `q∈Q` 的并集。

## 6. 复核方法

- `lake build`。
- 在临时文件中 `import formal_oet.vol_03.ch_14_empirical_network_fitting.path_guarantee_domains`，执行 `#print axioms path_guarantee_union_subset_proxy_error_text`，再用 `lake env lean` 运行。