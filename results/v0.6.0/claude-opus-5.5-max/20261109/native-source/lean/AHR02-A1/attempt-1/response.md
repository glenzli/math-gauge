## 结论

源码中对应推论 #h-93b9c20ea18b4e59 的是 `path_guarantee_domains.lean` 末尾三个声明：

- `path_component_guarantee_union_subset_proxy_error`（分量形式）
- `path_joint_guarantee_union_subset_proxy_error`（联合形式）
- `path_guarantee_union_subset_proxy_error_text`（加上正文前提的包装）

**判断：定义和结论准确，但覆盖不完整，源码定理严格弱于正文推论。**

- **准确的部分。** 所涉对象（$U_q$、$c_q$、$S_{q,j}$、$I_{\mathrm{res}}(q)$、$\hat\varepsilon_{q,j}$、$\mathbf A_q$、$D_{\mathbf A,j}$、$U_{q,j}(\tau_j)$、$U_{q,J}(\boldsymbol\tau)$）逐项与正文一致。两个包含关系的结论与正文逐字对应。证明结构也一致：取见证路径，代入 #h-4b5219aa3a3bbdad。
- **编译核验。** `lake build …path_guarantee_domains` 通过。三个声明的 `#print axioms` 只有 `propext`、`Classical.choice`、`Quot.sound`，没有 `sorry`。
- **缺口只有一处前提。** 三个声明都要求
  `hLq : ∀ q : N.ReachablePath, IsLipMatrix d (N.path_chain q.nodes) (N.path_domain q.nodes) (Lq q)`，
  也就是**所有**可达路径都要有路径链 Lip 证书。正文的 $\mathbf L_q$ 只在“设 $q\in\mathcal P$，$j\in I_{\mathrm{res}}(q)$”下选取，推论的并集也只经过这些路径。
- **这一加强是实质性的。** 本理论允许规范族不分离，且采用 $+\infty\cdot0=0$ 的约定，此时 Lip 证书集合可以是空集。我构造了一个反例：正文推论的全部前提成立、左侧并集非空，而源码三个声明都无法实例化。
- **修补很简单。** 把 `hLq` 改成以并集指标条件为前提的条件式，证明基本不变。补齐版与反例都已在本地编译通过，代码见附录。

---

## 一、对应关系（准确的部分）

| 正文 | Lean | 说明 |
|---|---|---|
| 扩展规范空间，有限 $I$ | `d`，`hd : ∀ j, ExtendedPseudoMetric X bot (d j)`，`[Fintype I]` | 一致 |
| $\phi^\natural,\ \phi$ | `target`，`proxy` | |
| 输入域为 $U$ 的有限网络 $\mathcal N$ | `N : FiniteOperatorNetwork X bot V`，$U$ = `N.U` | |
| $\phi_{\mathcal N}\equiv_U\phi$ | `hrep : N.represents proxy` | 即 `LocalEquivalent N.extensional_operator proxy N.U` |
| $U\subseteq V^*$ | `hpathV : ∀ q, N.path_domain q.nodes ⊆ Vstar` | 与 $U\subseteq V^*$ 等价，因为路径域覆盖 $U$（附录 B 已证） |
| $U\subseteq\mathrm{dom}\,\phi$ | 未单列 | 可由 `hrep` 与 `dom_extensional_operator_eq` 推出（附录 B） |
| $(V^*,\mathbf L^*)$ | `hLstar : TargetLipEnvelopeCertificate d target Vstar Lstar` | 含 `Vstar ⊆ dom target` |
| $\mathcal P,\ U_q,\ c_q$ | `N.ReachablePath`，`N.path_domain q.nodes`，`N.path_chain q.nodes` | |
| $S_{q,j}=S_j\cap U_q$ | `path_component_sample N sample q j` | |
| $I_{\mathrm{res}}(q)$ | `path_evaluable_components N sample q` | 自动包含于 $I_{\mathrm{res}}$（`path_evaluable_subset_evaluable_components`） |
| $\hat\varepsilon_{q,j}$ | `path_empirical_residual_upper d target N sample delta_o q j` | 展开为 $\sup_{x\in S_{q,j}}d_j(c_q(x),\phi^\natural(x))+\delta_{o,j}$ |
| $\mathbf L_q$ | `Lq q` 与 `hLq` | **差异所在**，见第二节 |
| $\mathbf A_q=\mathbf L_q+\mathbf L^*$ | `fun i j => Lq q i j + Lstar i j` | `A i j` $=[\mathbf A]_{i\to j}$，与 `IsLipMatrix` 的下标约定一致 |
| $D_{\mathbf A,j}(x;E)$ | `weighted_anchor_distance d A j x E` | $\inf_{y\in E}\sum_i A_{i\to j}\,d_i(x,y)$ |
| $U_{q,j}(\tau_j)$ | `path_component_empirical_guarantee_domain …` | $\{x\in U_q: D+\hat\varepsilon_{q,j}\le\tau_j\}$ |
| $U_{q,J}(\boldsymbol\tau)$ | `path_joint_empirical_guarantee_domain …` | $\{x\in U_q:\forall j\in J,\dots\}$；$J\neq\emptyset$ 时即 $\bigcap_{j\in J}U_{q,j}(\tau_j)$ |
| 左侧并集 | 满足 `∃ q, j ∈ path_evaluable_components N sample q ∧ x ∈ …` 的 `x` 构成的集合 | 联合形式把条件换成 `J ⊆ …` |
| 右侧 | `x ∈ N.U ∧ d j (proxy.func x) (target.func x) ≤ tau` | 联合形式对 `j ∈ J` 全称，一致 |

其余几点都只是放宽前提，不影响覆盖：

- **省略的正文前提。** 主定理没有 $j\in I_{\mathrm{res}}$、有限阈值、$J$ 非空且 $J\subseteq I_{\mathrm{res}}$ 这些前提，结论更一般；$\tau=\top$ 或 $J=\emptyset$ 时结论平凡成立。`_text` 版重新列出这些前提，但证明中不使用。
- **采样结构约束不需要。** $S_j\subseteq S\cap U\cap\mathrm{dom}\,\phi^\natural$ 与 $S$ 有限都用不到，因为只用到 $S_{q,j}=S_j\cap U_q$，而 $U_q\subseteq V^*\subseteq\mathrm{dom}\,\phi^\natural$。
- **`_text` 版共用前提。** 两个结论共用前提（包括 $J\neq\emptyset$）。若只要分量结论，取 $J=\{j\}$、$\tau\equiv\tau_j$ 即可，没有损失。
- **证明对应。** 先取见证 $q$，用 `path_domain_subset_source` 得 $x\in U$。分量形式再用 `proxy_path_component_guarantee_error_bound`；联合形式用 `path_joint_guarantee_error_bound` 加 `path_chain_eq_represented_proxy_on_path`。这正是正文的“由 @h-4b5219aa3a3bbdad 得到……对所有 $j\in J$ 同时应用”。

---

## 二、不足：路径链 Lip 证书的量词范围

### 2.1 差异

正文需要的前提是：

$$\forall q\in\mathcal P:\quad j\in I_{\mathrm{res}}(q)\ \Longrightarrow\ \mathbf L_q\in\mathscr L(c_q)\big|_{U_q}$$

联合形式中把条件换成 $J\subseteq I_{\mathrm{res}}(q)$。源码则要求对全部可达路径成立。源码证明里其实只对见证路径用到了 `hLq q`，所以这个全称量词只是陈述时写宽了，数学上并不需要。

### 2.2 为什么这是实质性的加强

- **证书集合可能为空。** ENNReal 中 $\top\cdot0=0$。若 $x,y\in U_q$ 对所有 $i$ 都有 $d_i(x,y)=0$，则对任何矩阵都有 $\sum_i L_{i\to j}d_i(x,y)=0$。所以只要 $c_q$ 把这样一对全分量零距的点送到 $d_j$ 距离为正的点对，就有 $\mathscr L(c_q)|_{U_q}=\emptyset$。
- **理论本身采用同一约定。** 例如 h-28ceee0bc7dbdab0“无穷传播系数强制对应局部误差归零”只在 $\top\cdot0=0$ 下才说得通。
- **这种情况确实会出现。** 扩展规范空间只要求伪度量，允许不分离；`gauge_space.lean` 中专门定义了 `IsNonSeparating`。

### 2.3 反例（附录 A 已逐条机器验证）

**空间与度量。** 取 $\mathcal X=\{\bot,a,b,c,e\}$，$I=\{\ast\}$，度量 $d$ 如下：

- $d(x,x)=0$；
- $x\neq y$ 且其中一个是 $\bot$ 时，$d(x,y)=+\infty$；
- $d(a,b)=0$；
- 其余不同的非 $\bot$ 点对，$d=1$。

零距等价类是 $\{a,b\},\{c\},\{e\}$。三角不等式成立，$\bot$ 被隔离，这是扩展伪度量，但不分离。

**网络 $\mathcal N_0$。** 两个节点 $\beta_0,\beta_1$，$U=\{a,b,e\}$：

- $\phi_{\beta_0}$：$a\mapsto a$，$b\mapsto c$，其余 $\mapsto\bot$；
- $\phi_{\beta_1}$：$e\mapsto e$，其余 $\mapsto\bot$；
- 入口：$a,b\mapsto\beta_0$，$e\mapsto\beta_1$；所有输出都终止。

可达路径为 $q_0=(\beta_0)$，$U_{q_0}=\{a,b\}$；以及 $q_1=(\beta_1)$，$U_{q_1}=\{e\}$。

**① 源码前提不可满足。** $d(c_{q_0}(a),c_{q_0}(b))=d(a,c)=1$，而对任意 $L\in[0,+\infty]$ 都有 $L\cdot d(a,b)=0$。所以 $\mathscr L(c_{q_0})|_{U_{q_0}}=\emptyset$。因此对 $\mathcal N_0$，无论目标、代理、采样、$\delta_o$、$\tau$ 怎样取，`hLq` 都不可满足，三个源码声明都无法使用（`uniform_hLq_unsatisfiable`）。

**② 正文推论适用且非平凡。** 取 $\phi=\phi_{\mathcal N_0}$，$\phi^\natural=\mathrm{id}$，$V^*=U$，$\mathbf L^*=(1)$，$S_\ast=\{e\}$，$\delta_o$ 任意。

- 正文全部前提成立：$U\subseteq\mathrm{dom}\,\phi\cap V^*$，且 $\mathbf L^*$ 是目标 Lip 包络。
- $I_{\mathrm{res}}(q_0)=\emptyset$，$I_{\mathrm{res}}(q_1)=\{\ast\}$。
- $\mathbf L_{q_1}=(1)$ 是 $c_{q_1}$ 在 $\{e\}$ 上的 Lip 证书。$q_0$ 不在并集指标中，正文不要求它的证书。
- 左侧并集等于 $U_{q_1,\ast}(\tau)$。由 $D(e;\{e\})=0$ 与 $\hat\varepsilon_{q_1,\ast}=\delta_o$，当 $\delta_o\le\tau$ 时 $e$ 属于左侧（`e_in_union`）。

因此推论在这里断言了一个非空的包含关系。补齐版定理可以在这里实例化（`corollary_instance`），源码版不能。联合形式取 $J=\{\ast\}$，情况相同。

### 2.4 缺口的确切范围

- **何时源码版够用。** 若每条不在并集指标中的路径链都在其路径域上保持全分量零距关系（规范族分离时自动成立），则全 $\top$ 矩阵就是它的 Lip 证书（附录 B `top_matrix_is_lip`）。此时对无关路径填 $\top$：令 `Lq q := if j ∈ I_res(q) then L_q else ⊤`，并集不变，源码定理即可使用。
- **缺口出现的条件。** 规范族不分离，且某条无采样路径的路径链不保持零距关系。

---

## 三、补齐方式

**定理改写。** 只改 `hLq` 的量词范围：

- 分量形式：`hLq : ∀ q, j ∈ path_evaluable_components N sample q → IsLipMatrix d (N.path_chain q.nodes) (N.path_domain q.nodes) (Lq q)`
- 联合形式：`hLq : ∀ q, J ⊆ path_evaluable_components N sample q → …`
- `_text` 版：`hLq : ∀ q, (j ∈ … ∨ J ⊆ …) → …`

证明中把 `hLq q` 换成 `hLq q hj`（或 `hLq q hJ`）即可。原定理是补齐版的特例，传入 `fun q _ => hLq q` 就得到。

**等价性。** `Lq` 仍是全函数；它在指标集外的取值不进入并集，所以补齐版与“只在指标路径上给出的依赖证书族”完全等价。

**备选做法。** 也可以不改原定理，直接由单路径引理推出正文推论，证明只有三行。

---

## 四、源码已证明的结论与需自行补充的内容

**源码已证明**（编译通过，只依赖标准公理）：

1. 分量与联合两个包含关系，但前提是：所有可达路径都有 Lip 证书（`hLq`），外加 `hpathV`（与 $U\subseteq V^*$ 等价）、`hLstar`、`hrep`、`hd`。
2. `_text` 版：同样的结论，加上正文的有限阈值、非空 $J$、可评估条件（不使用），同样带一致证书前提。
3. 推论所依赖的单路径引理，它们只需要单条路径的证书：`proxy_path_component_guarantee_error_bound`、`path_joint_guarantee_error_bound`、`proxy_path_joint_guarantee_error_bound`、`path_chain_eq_represented_proxy_on_path`。

**需自行补充**（不在源码中，我已在本地编译验证，代码见附录）：

1. 只在并集指标路径上要求证书的补齐版：`…_rel` 的分量、联合与 `_text` 三个版本。这才是与正文同强度的形式化。
2. 反例 `ReviewCounter`：
   - 一致证书前提严格强于正文：`uniform_hLq_unsatisfiable`。
   - 正文推论在该网络上可用且非平凡：`corollary_instance`、`e_in_union`。
3. 辅助事实：
   - `hpathV` 与 $U\subseteq V^*$ 等价；
   - `hrep` 推出 $U\subseteq\mathrm{dom}\,\phi$；
   - 零距保持（或规范族分离）时全 $\top$ 矩阵是证书，这刻画了缺口的确切范围。

---

## 附录 A：补齐版定理与反例（`lake env lean` 编译通过，公理仅 `propext / Classical.choice / Quot.sound`）

```lean
import formal_oet.vol_03.ch_14_empirical_network_fitting.path_guarantee_domains

namespace formal_oet.vol_03.ch_14_empirical_network_fitting
open formal_oet.vol_01.ch_01_foundations formal_oet.vol_01.ch_02_operator_bounds
  formal_oet.vol_01.ch_05_operator_networks formal_oet.vol_03.ch_12_residuals_and_substitution

variable {X I V : Type} {bot : X} [Fintype I]

/-- 分量形式（补齐版）：只对并集索引中的路径要求 Lip 证书。 -/
theorem path_component_guarantee_union_subset_proxy_error_rel
    (d : I → X → X → ENNReal) (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot) (N : FiniteOperatorNetwork X bot V)
    (sample : I → Set X) (delta_o : I → ENNReal) (Vstar : Set X)
    (Lq : N.ReachablePath → I → I → ENNReal) (Lstar : I → I → ENNReal)
    (j : I) (tau : ENNReal) (hrep : N.represents proxy)
    (hpathV : ∀ q : N.ReachablePath, N.path_domain q.nodes ⊆ Vstar)
    (hLq : ∀ q : N.ReachablePath, j ∈ path_evaluable_components N sample q →
      IsLipMatrix d (N.path_chain q.nodes) (N.path_domain q.nodes) (Lq q))
    (hLstar : TargetLipEnvelopeCertificate d target Vstar Lstar) :
    {x | ∃ q : N.ReachablePath, j ∈ path_evaluable_components N sample q ∧
      x ∈ path_component_empirical_guarantee_domain d
        (fun i j => Lq q i j + Lstar i j) N sample q j
        (path_empirical_residual_upper d target N sample delta_o q j) tau}
      ⊆ {x | x ∈ N.U ∧ d j (proxy.func x) (target.func x) ≤ tau} := by
  rintro x ⟨q, hj, hxq⟩
  exact ⟨N.path_domain_subset_source hxq.1,
    proxy_path_component_guarantee_error_bound d hd target proxy N sample
      delta_o q Vstar (Lq q) Lstar j tau hrep (hpathV q) (hLq q hj) hLstar hj hxq⟩

/-- 联合形式（补齐版）：只对 `J ⊆ I_res(q)` 的路径要求 Lip 证书。 -/
theorem path_joint_guarantee_union_subset_proxy_error_rel
    (d : I → X → X → ENNReal) (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot) (N : FiniteOperatorNetwork X bot V)
    (sample : I → Set X) (delta_o : I → ENNReal) (Vstar : Set X)
    (Lq : N.ReachablePath → I → I → ENNReal) (Lstar : I → I → ENNReal)
    (J : Set I) (tau : I → ENNReal) (hrep : N.represents proxy)
    (hpathV : ∀ q : N.ReachablePath, N.path_domain q.nodes ⊆ Vstar)
    (hLq : ∀ q : N.ReachablePath, J ⊆ path_evaluable_components N sample q →
      IsLipMatrix d (N.path_chain q.nodes) (N.path_domain q.nodes) (Lq q))
    (hLstar : TargetLipEnvelopeCertificate d target Vstar Lstar) :
    {x | ∃ q : N.ReachablePath, J ⊆ path_evaluable_components N sample q ∧
      x ∈ path_joint_empirical_guarantee_domain d
        (fun i j => Lq q i j + Lstar i j) N sample q J
        (path_empirical_residual_upper d target N sample delta_o q) tau}
      ⊆ {x | x ∈ N.U ∧ ∀ j : I, j ∈ J → d j (proxy.func x) (target.func x) ≤ tau j} := by
  rintro x ⟨q, hJ, hxq⟩
  exact ⟨N.path_domain_subset_source hxq.1, fun j hj =>
    proxy_path_joint_guarantee_error_bound d hd target proxy N sample delta_o q
      Vstar (Lq q) Lstar J tau hrep (hpathV q) (hLq q hJ) hLstar hJ hxq j hj⟩

/-- 原分量定理是补齐版的特例。 -/
example (d : I → X → X → ENNReal) (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot) (N : FiniteOperatorNetwork X bot V)
    (sample : I → Set X) (delta_o : I → ENNReal) (Vstar : Set X)
    (Lq : N.ReachablePath → I → I → ENNReal) (Lstar : I → I → ENNReal)
    (j : I) (tau : ENNReal) (hrep : N.represents proxy)
    (hpathV : ∀ q : N.ReachablePath, N.path_domain q.nodes ⊆ Vstar)
    (hLq : ∀ q : N.ReachablePath,
      IsLipMatrix d (N.path_chain q.nodes) (N.path_domain q.nodes) (Lq q))
    (hLstar : TargetLipEnvelopeCertificate d target Vstar Lstar) :=
  path_component_guarantee_union_subset_proxy_error_rel d hd target proxy N sample
    delta_o Vstar Lq Lstar j tau hrep hpathV (fun q _ => hLq q) hLstar

/-- `_text` 包装的补齐版：证书只在两类并集索引路径上要求。 -/
theorem path_guarantee_union_subset_proxy_error_text_rel
    (d : I → X → X → ENNReal) (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot) (N : FiniteOperatorNetwork X bot V)
    (sample : I → Set X) (delta_o : I → ENNReal) (Vstar : Set X)
    (Lq : N.ReachablePath → I → I → ENNReal) (Lstar : I → I → ENNReal)
    (j : I) (tau_j : ENNReal) (J : Set I) (tau : I → ENNReal)
    (_hj_evaluable : j ∈ evaluable_components sample)
    (_hJ_evaluable : J ⊆ evaluable_components sample)
    (_htau_j_finite : finite_ennreal tau_j) (_hJ_nonempty : J.Nonempty)
    (_htau_finite : ∀ i : I, i ∈ J → finite_ennreal (tau i))
    (hrep : N.represents proxy)
    (hpathV : ∀ q : N.ReachablePath, N.path_domain q.nodes ⊆ Vstar)
    (hLq : ∀ q : N.ReachablePath,
      (j ∈ path_evaluable_components N sample q ∨ J ⊆ path_evaluable_components N sample q) →
      IsLipMatrix d (N.path_chain q.nodes) (N.path_domain q.nodes) (Lq q))
    (hLstar : TargetLipEnvelopeCertificate d target Vstar Lstar) :
    ({x | ∃ q : N.ReachablePath, j ∈ path_evaluable_components N sample q ∧
        x ∈ path_component_empirical_guarantee_domain d
          (fun i j => Lq q i j + Lstar i j) N sample q j
          (path_empirical_residual_upper d target N sample delta_o q j) tau_j}
        ⊆ {x | x ∈ N.U ∧ d j (proxy.func x) (target.func x) ≤ tau_j}) ∧
      ({x | ∃ q : N.ReachablePath, J ⊆ path_evaluable_components N sample q ∧
        x ∈ path_joint_empirical_guarantee_domain d
          (fun i j => Lq q i j + Lstar i j) N sample q J
          (path_empirical_residual_upper d target N sample delta_o q) tau}
        ⊆ {x | x ∈ N.U ∧ ∀ i : I, i ∈ J → d i (proxy.func x) (target.func x) ≤ tau i}) :=
  ⟨path_component_guarantee_union_subset_proxy_error_rel d hd target proxy N sample
      delta_o Vstar Lq Lstar j tau_j hrep hpathV (fun q h => hLq q (Or.inl h)) hLstar,
   path_joint_guarantee_union_subset_proxy_error_rel d hd target proxy N sample
      delta_o Vstar Lq Lstar J tau hrep hpathV (fun q h => hLq q (Or.inr h)) hLstar⟩

end formal_oet.vol_03.ch_14_empirical_network_fitting

namespace ReviewCounter
open formal_oet.vol_01.ch_01_foundations formal_oet.vol_01.ch_02_operator_bounds
  formal_oet.vol_01.ch_05_operator_networks formal_oet.vol_03.ch_12_residuals_and_substitution
  formal_oet.vol_03.ch_14_empirical_network_fitting

inductive Pt | bot | a | b | c | e
  deriving DecidableEq

def cls : Pt → Nat | .bot => 0 | .a => 1 | .b => 1 | .c => 2 | .e => 3

/-- 单分量非分离扩展伪度量：d(a,b)=0，其余不同非 ⊥ 点距离 1，到 ⊥ 为 ⊤。 -/
noncomputable def dd : Unit → Pt → Pt → ENNReal := fun _ x y =>
  if x = y then 0 else if x = Pt.bot ∨ y = Pt.bot then ⊤
  else if cls x = cls y then 0 else 1

instance hdd (i : Unit) : ExtendedPseudoMetric Pt Pt.bot (dd i) where
  nonabsorbing := ⟨Pt.a, by decide⟩
  dist_self := by intro x; simp [dd]
  symm := by intro x y; cases x <;> cases y <;> simp [dd, cls]
  triangle := by intro x y z; cases x <;> cases y <;> cases z <;> simp [dd, cls]
  isolate_bot := by intro x hx; cases x <;> simp_all [dd]

def op0 : Operator Pt Pt.bot := ⟨fun x => match x with | .a => .a | .b => .c | _ => .bot, rfl⟩
def op1 : Operator Pt Pt.bot := ⟨fun x => match x with | .e => .e | _ => .bot, rfl⟩
def Usrc : Set Pt := {x | x = .a ∨ x = .b ∨ x = .e}
def entryF (x : {x : Pt // x ∈ Usrc}) : Bool := decide (x.val = Pt.e)

/-- 两节点、无后继：节点 false 处理 {a,b}，节点 true 处理 {e}。 -/
def N0 : FiniteOperatorNetwork Pt Pt.bot Bool where
  U := Usrc
  bot_not_mem := by simp [Usrc]
  node_fintype := inferInstance
  node_op := fun β => if β then op1 else op0
  node_dom_nonempty := by
    intro β; cases β
    · exact ⟨.a, by simp [dom, op0]⟩
    · exact ⟨.e, by simp [dom, op1]⟩
  entry := entryF
  entry_mem := by rintro ⟨x, hx⟩; rcases hx with rfl | rfl | rfl <;> simp [entryF, dom, op0, op1]
  choice := fun _ _ => OutputChoice.stop
  choice_next_mem := by intro β γ y _ h; cases h
  depth_bound := 1
  path_of := fun x => [entryF x]
  path_terminal := fun _ => TerminalPathFrom.stop rfl
  path_length_le_depth := by intro x; simp
  node_reachable := by
    intro β; cases β
    · exact ⟨⟨.a, by simp [Usrc]⟩, by simp [entryF]⟩
    · exact ⟨⟨.e, by simp [Usrc]⟩, by simp [entryF]⟩

theorem a_mem : Pt.a ∈ N0.path_domain [false] := ⟨Or.inl rfl, by simp [N0, entryF]⟩
theorem b_mem : Pt.b ∈ N0.path_domain [false] := ⟨Or.inr (Or.inl rfl), by simp [N0, entryF]⟩
theorem e_mem : Pt.e ∈ N0.path_domain [true] := ⟨Or.inr (Or.inr rfl), by simp [N0, entryF]⟩
def q0 : N0.ReachablePath := ⟨[false], ⟨Pt.a, a_mem⟩⟩
def q1 : N0.ReachablePath := ⟨[true], ⟨Pt.e, e_mem⟩⟩

/-- 路径 q0 上不存在任何 Lip 矩阵。 -/
theorem no_lip_on_q0 (L : Unit → Unit → ENNReal) :
    ¬ IsLipMatrix dd (N0.path_chain q0.nodes) (N0.path_domain q0.nodes) L := by
  intro hL
  have h := hL.2 Pt.a a_mem Pt.b b_mem ()
  simp [FiniteOperatorNetwork.path_chain, OperatorChain, q0, N0, op0, dd, cls] at h

/-- 源码三个定理共有的一致证书前提对 N0 不可满足。 -/
theorem uniform_hLq_unsatisfiable :
    ¬ ∃ Lq : N0.ReachablePath → Unit → Unit → ENNReal,
      ∀ q, IsLipMatrix dd (N0.path_chain q.nodes) (N0.path_domain q.nodes) (Lq q) :=
  fun ⟨Lq, hLq⟩ => no_lip_on_q0 (Lq q0) (hLq q0)

def sampleE : Unit → Set Pt := fun _ => {Pt.e}
def tgt : Operator Pt Pt.bot := ⟨id, rfl⟩

theorem pd_true (x : Pt) (hx : x ∈ N0.path_domain [true]) : x = Pt.e := by
  rcases hx with ⟨hxU, hpath⟩; simpa [N0, entryF] using hpath

theorem evaluable_nodes (q : N0.ReachablePath)
    (hq : () ∈ path_evaluable_components N0 sampleE q) : q.nodes = [true] := by
  rcases hq with ⟨x, hxS, hxU, hpath⟩
  have hx : x = Pt.e := hxS
  subst hx; rw [← hpath]; simp [N0, entryF]

/-- 正文所需的证书（只在可评估路径上）可以给出。 -/
theorem lip_on_relevant (q : N0.ReachablePath)
    (hq : () ∈ path_evaluable_components N0 sampleE q) :
    IsLipMatrix dd (N0.path_chain q.nodes) (N0.path_domain q.nodes) (fun _ _ => 1) := by
  rw [evaluable_nodes q hq]
  refine ⟨fun x hx => ?_, fun x hx y hy j => ?_⟩
  · obtain rfl := pd_true x hx
    simp [dom, FiniteOperatorNetwork.path_chain, OperatorChain, N0, op1]
  · obtain rfl := pd_true x hx; obtain rfl := pd_true y hy; simp [dd]

theorem tgt_lip : TargetLipEnvelopeCertificate dd tgt Usrc (fun _ _ => 1) := by
  refine ⟨⟨fun x hx => ?_, fun x _ y _ j => by simp [tgt]⟩⟩
  rcases hx with rfl | rfl | rfl <;> simp [dom, tgt]

/-- 补齐版推论在 N0 上可实例化。 -/
theorem corollary_instance (delta tau : ENNReal) :
    {x | ∃ q : N0.ReachablePath, () ∈ path_evaluable_components N0 sampleE q ∧
      x ∈ path_component_empirical_guarantee_domain dd
        (fun i j => (fun (_ : N0.ReachablePath) (_ _ : Unit) => (1 : ENNReal)) q i j +
          (fun (_ _ : Unit) => (1 : ENNReal)) i j) N0 sampleE q ()
        (path_empirical_residual_upper dd tgt N0 sampleE (fun _ => delta) q ()) tau}
      ⊆ {x | x ∈ N0.U ∧ dd () (N0.extensional_operator.func x) (tgt.func x) ≤ tau} :=
  path_component_guarantee_union_subset_proxy_error_rel dd hdd tgt N0.extensional_operator
    N0 sampleE (fun _ => delta) Usrc (fun _ _ _ => 1) (fun _ _ => 1) () tau
    (fun _ _ => rfl) (fun _ _ hx => N0.path_domain_subset_source hx) lip_on_relevant tgt_lip

/-- 左侧并集非空：δ ≤ τ 时 e ∈ U_{q1,*}(τ)。 -/
theorem e_in_union (delta tau : ENNReal) (h : delta ≤ tau) :
    ∃ q : N0.ReachablePath, () ∈ path_evaluable_components N0 sampleE q ∧
      Pt.e ∈ path_component_empirical_guarantee_domain dd
        (fun i j => (fun (_ : N0.ReachablePath) (_ _ : Unit) => (1 : ENNReal)) q i j +
          (fun (_ _ : Unit) => (1 : ENNReal)) i j) N0 sampleE q ()
        (path_empirical_residual_upper dd tgt N0 sampleE (fun _ => delta) q ()) tau := by
  have hS : Pt.e ∈ path_component_sample N0 sampleE q1 () := ⟨rfl, e_mem⟩
  refine ⟨q1, ⟨Pt.e, hS⟩, e_mem, ?_⟩
  rw [weighted_anchor_distance_self_eq_zero dd hdd _ () hS, zero_add]
  have hraw : empirical_residual_raw_sup dd tgt (N0.path_chain q1.nodes)
      (path_component_sample N0 sampleE q1 ()) () = 0 := by
    refine le_antisymm (iSup_le ?_) (zero_le _)
    rintro ⟨x, hxS, hxpd⟩
    have hx : x = Pt.e := hxS
    subst hx
    simp [FiniteOperatorNetwork.path_chain, OperatorChain, q1, N0, op1, tgt, dd]
  simpa [path_empirical_residual_upper, empirical_residual_upper, path_sample_family, hraw]
    using h

end ReviewCounter

#print axioms ReviewCounter.uniform_hLq_unsatisfiable
#print axioms ReviewCounter.e_in_union
#print axioms formal_oet.vol_03.ch_14_empirical_network_fitting.path_guarantee_union_subset_proxy_error_text_rel
```

## 附录 B：辅助核验（编译通过）

```lean
import formal_oet.vol_03.ch_14_empirical_network_fitting.path_guarantee_domains
open formal_oet.vol_01.ch_01_foundations formal_oet.vol_01.ch_02_operator_bounds
  formal_oet.vol_01.ch_05_operator_networks formal_oet.vol_03.ch_14_empirical_network_fitting

variable {X V I : Type} {bot : X} [Fintype I]

/-- `hpathV` 与正文 `U ⊆ V*` 等价。 -/
example (N : FiniteOperatorNetwork X bot V) (Vstar : Set X) :
    (∀ q : N.ReachablePath, N.path_domain q.nodes ⊆ Vstar) ↔ N.U ⊆ Vstar :=
  ⟨fun h _ hx => h (reachable_path_at N hx) (mem_path_domain_reachable_path_at N hx),
   fun h _ _ hx => h (N.path_domain_subset_source hx)⟩

/-- 网络表示推出 `U ⊆ dom φ`。 -/
example (N : FiniteOperatorNetwork X bot V) (proxy : Operator X bot)
    (hrep : N.represents proxy) : N.U ⊆ dom proxy := by
  intro x hx
  have h : x ∈ dom N.extensional_operator := by rw [N.dom_extensional_operator_eq]; exact hx
  simpa [dom, hrep x hx] using h

/-- 路径链保持全分量零距关系时，全 ⊤ 矩阵是 Lip 证书。 -/
theorem top_matrix_is_lip (d : I → X → X → ENNReal) (N : FiniteOperatorNetwork X bot V)
    (q : N.ReachablePath)
    (hzero : ∀ x ∈ N.path_domain q.nodes, ∀ y ∈ N.path_domain q.nodes, (∀ i, d i x y = 0) →
      ∀ j, d j ((N.path_chain q.nodes).func x) ((N.path_chain q.nodes).func y) = 0) :
    IsLipMatrix d (N.path_chain q.nodes) (N.path_domain q.nodes) (fun _ _ => ⊤) := by
  refine ⟨N.path_domain_subset_path_chain_dom q, fun x hx y hy j => ?_⟩
  by_cases h : ∀ i, d i x y = 0
  · rw [hzero x hx y hy h j]; exact zero_le _
  · obtain ⟨i, hi⟩ := not_forall.mp h
    calc _ ≤ (⊤ : ENNReal) := le_top
      _ = ⊤ * d i x y := (ENNReal.top_mul hi).symm
      _ ≤ ∑ k, (fun _ _ => (⊤ : ENNReal)) k j * d k x y :=
          Finset.single_le_sum (f := fun k => (⊤ : ENNReal) * d k x y)
            (fun _ _ => zero_le _) (Finset.mem_univ i)

/-- 分离规范族下该条件自动成立。 -/
example (d : I → X → X → ENNReal) (hd : ∀ j, ExtendedPseudoMetric X bot (d j))
    (hsep : IsSeparating d) (N : FiniteOperatorNetwork X bot V) (q : N.ReachablePath) :
    IsLipMatrix d (N.path_chain q.nodes) (N.path_domain q.nodes) (fun _ _ => ⊤) :=
  top_matrix_is_lip d N q (fun x _ y _ h j => by rw [hsep x y h]; exact (hd j).dist_self _)
```