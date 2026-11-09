## 审阅结论

**对象**：`source.md` 推论 #h-93b9c20ea18b4e59（路径保证域的全局拟合含义）。Lean 实现是 `formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean` 中带该锚点的三条定理，全库只有这三处引用该锚点：

- **T1** `path_component_guarantee_union_subset_proxy_error`（:520）对应第一式（单分量）。
- **T2** `path_joint_guarantee_union_subset_proxy_error`（:552）对应第二式（联合）。
- **T3** `path_guarantee_union_subset_proxy_error_text`（:588）是 T1∧T2，并带上正文的"有限阈值 / J 非空 / J ⊆ I_res"前提。这些前提在证明里未被使用（`have _ := …`）。

**方法**：逐项对读定义、前提和结论，重新编译，`#print axioms`。我另写了审计文件，放在 `$TMPDIR`，未改动附件。环境为 Lean 4.29.1、Mathlib 5e932f97。

### 1. 总评

1. **数学内容准确，两条包含式都被完整覆盖。**
   - `lake build formal_oet.vol_03.ch_14_empirical_network_fitting.path_guarantee_domains` 成功（3341 jobs）。
   - T1–T3 的 `#print axioms` 只有 `propext / Classical.choice / Quot.sound`。
   - 全库没有 `sorry`、`admit`、自定义 `axiom`。
   - 定义、不等号方向、`(proxy, target)` 的参数次序、并集指标、结论集合 `{x ∈ U | …}` 与正文逐项一致。
2. **有一处严格意义上的偏差，也是唯一需要补齐的点。** T1–T3 的 `hLq` 要求**所有**可达路径都有 Lip 证书。正文只对 I_res(q)≠∅ 的路径取证书，证明也只用到并集指标内的路径。因此 Lean 定理在适用范围上比正文窄，数学内容不变。
   - 我给了经 Lean 编译检验的反例模型：`hLq` 不可满足，而正文前提和结论都成立。
   - 我也给了缩窄量词的补齐版本，已编译通过。
   - 该偏差只在规范族**非分离**时实质存在（§4.3）。
3. 其余差异是无害推广或等价改写：不设采样结构前提、阈值不要求有限、J 不要求非空、`hpathV` 逐路径表述（§3.1）。

### 2. 对应关系

| 正文 | Lean |
|---|---|
| 扩展规范空间、有限 I | `d : I → X → X → ENNReal`，`hd : ∀ j, ExtendedPseudoMetric X bot (d j)`，`[Fintype I]` |
| 目标 φ†、代理 φ | `target proxy : Operator X bot` |
| 网络 𝒩（输入域 U），φ_𝒩 ≡_U φ | `N : FiniteOperatorNetwork X bot V`，`N.U`，`hrep : N.represents proxy`（operator_network.lean:814） |
| 𝒫、U_q、c_q | `N.ReachablePath`，`N.path_domain q.nodes`，`N.path_chain q.nodes` |
| (V\*, **L**\*) | `Vstar Lstar`，`hLstar : TargetLipEnvelopeCertificate d target Vstar Lstar`（= `IsLipMatrix d target Vstar Lstar`） |
| U ⊆ dom φ ∩ V\* | `hpathV`（⇔ `N.U ⊆ Vstar`）加上 `hrep`（⇒ `N.U ⊆ dom proxy`） |
| S_j、δ_{o,j} | `sample : I → Set X`，`delta_o`（不设采样结构前提） |
| S_{q,j}=S_j∩U_q，I_res(q) | `path_component_sample`（path_sampling:27），`path_evaluable_components`（:48） |
| ε̂_{q,j} | `path_empirical_residual_upper`（:136）= `⨆_{x∈S_{q,j}} d j (c_q x) (φ† x) + delta_o j` |
| **L**_q，**A**_q=**L**_q+**L**\* | `Lq q`，`fun i j => Lq q i j + Lstar i j` |
| D_{**A**,j}(x;E) | `weighted_anchor_distance`（empirical_residuals:206）= `⨅ y∈E, ∑ i, A i j * d i x y` |
| U_{q,j}(τ_j) | `path_component_empirical_guarantee_domain`（:26） |
| U_{q,J}(**τ**)=⋂_{j∈J}U_{q,j}(τ_j) | `path_joint_empirical_guarantee_domain`（:39） |
| 第一式 / 第二式 / 整条推论 | T1 / T2 / T3 |

### 3. 逐项核对

#### 3.1 前提

- **U ⊆ dom φ ∩ V\***：Lean 用 `N.U` 作 U。逐路径的 `hpathV` 与 `N.U ⊆ Vstar` 等价，依据是路径域覆盖 `reachable_path_domains_cover`（:778）。U ⊆ dom φ 由 `hrep` 加 `dom_extensional_operator_eq`（:344）推出。这两条我都在 Lean 里证了（`hpathV_iff`、`represents_dom`），没有损失。
- **采样结构** S_j ⊆ S∩U∩dom φ† 未设，这是推广。证明只用 S_{q,j}=S_j∩U_q ⊆ U，而它自动成立。若采样点落在 dom φ† 之外，`isolate_bot` 使 ε̂=⊤，对有限阈值保证域为空，不破坏包含式。
- **有限阈值、J 非空**：T1/T2 不需要。τ=⊤ 时结论平凡。J=∅ 时两侧都是 `N.U`。T3 保留这些前提但未使用。
- **hLstar**：包含 `Vstar ⊆ dom target`，与 Lip 矩阵的定义一致。
- **hLq**：见 §4。

#### 3.2 定义

- 共同锚点距离的矩阵朝向与 `IsLipMatrix` 一致：`matrix_vector_bound M v j = ∑ i, M i j * v i`。
- 保证域用 `≤`（不是 `<`），集合为 `{x ∈ U_q | D + ε̂ ≤ τ}`。
- J 非空时，联合域恰等于 ⋂_{j∈J} 分量域，我已证（`path_joint_eq_biInter`）。

#### 3.3 结论与证明

- T1 的结论是 `{x | x ∈ N.U ∧ d j (proxy.func x) (target.func x) ≤ tau}`。T2 是对 `j ∈ J` 的同类集合。两者都与正文一致，参数次序为 (proxy, target)。
- 证明路径与正文一致：
  1. 通过 `path_chain_eq_represented_proxy_on_path`（path_sampling:220）把 c_q(x) 换成 φ(x)。
  2. 调用 `proxy_path_component_guarantee_error_bound`（:152）和 `proxy_path_joint_guarantee_error_bound`（:244）。
  3. 它们的核心是 `path_local_empirical_upper`（:54），即 #h-4b5219aa3a3bbdad 的 Lean 形式。
- 我手工复核了该局部界：三项三角不等式，分别用 c_q 在 U_q 上和 φ† 在 V\* 上的 Lip 界，再用对称性，最后对锚点取下确界。ENNReal 的 `iInf_add` 不需要非空。结论与 Lean 一致。
- 命题只给出包含，没有等号。我另在模型里验证了包含是严格的：τ=0 时点 2 在真实容限区域，却不在任何路径保证域里。

### 4. 不足：Lip 证书的量化范围

#### 4.1 偏差是什么

- T1–T3 的 `hLq`（path_guarantee_domains.lean:530–531、562–563、604–605）是 `∀ q : N.ReachablePath, IsLipMatrix …`。它要求每条可达路径，包括没有采样点（I_res(q)=∅）的路径，都有 Lip 证书。
- 正文说"设 q∈𝒫，j∈I_res(q)，取路径链的受限 Lip 证书 **L**_q"，只对 I_res(q)≠∅ 的路径取证书。
- 支撑引理 `proxy_path_*_guarantee_error_bound` 也只需要单条路径的证书。所以 T1–T3 比证明实际给出的结论弱。

#### 4.2 反例模型（Lean 已检验，代码见附录 B）

- **空间与度量**：`Fin 5`，⊥=0。等价类为 {0}、{1}、{2,3}、{4}。单分量 d 同类为 0，异类为 ⊤。这是非分离的扩展伪度量，d(2,3)=0。
- **网络**：两个节点。`false ↦ op1`（1↦1，其余↦⊥），`true ↦ op2`（2↦2，3↦4，其余↦⊥）。输入域 U={1,2,3}。两条可达路径是 `[false]`（U_q={1}）和 `[true]`（U_q={2,3}）。
- **代理与目标**：代理是网络的外延算子（`hrep` 平凡成立）。目标是 U 上的恒等，V\*=U，**L**\*=1。采样 S={1}。因此 I_res([false])={\*}，I_res([true])=∅。
- **关键事实**：路径 `[true]` 满足 d(2,3)=0，但 d(c(2),c(3))=d(2,4)=⊤。ENNReal 里 ⊤·0=0，所以任何矩阵（含 ⊤ 项）都不是它的 Lip 证书。
- **Lean 结果**（均无 `sorry`，只用标准公理）：
  - `no_lip_second_path` 和 `hLq_all_unsat`：T1–T3 的 `hLq` 在此模型里不可满足，T1–T3 无法实例化。
  - `corollary_in_model`：正文第一式在此模型成立（用缩窄版本得到）。
  - 另已编译、未附代码：
    - 并集非空（点 1，τ=0 时在并集中）。
    - 模型满足 S ⊆ U∩dom φ† 与 U ⊆ dom φ。
    - 包含严格。

#### 4.3 严重程度

- 我归为轻到中等。它不影响数学内容，只影响适用范围。
- 若规范族可分离，则全 ⊤ 矩阵总是任意 U ⊆ dom φ 上的合法 Lip 证书。给非指标路径取全 ⊤ 矩阵，偏差就消失。这是 `top_matrix_lip_of_separating`，已证。
- 只有非分离族（本书有 `IsNonSeparating`）下，才会出现无采样路径恰好没有 Lip 证书的情形。
- 若读者把"证书族对所有 q 给定"理解为正文的标准设定，则 Lean 与正文无偏差。我认为字面上更自然的读法是只对指标内路径取证书。

#### 4.4 补齐

把 `hLq` 缩窄到指标内路径，并把 `hpathV` 换成等价的 `hUV : N.U ⊆ Vstar`：

- 单分量版本：`hLq : ∀ q, j ∈ path_evaluable_components N sample q → IsLipMatrix …`。
- 联合版本：`hLq : ∀ q, J ⊆ path_evaluable_components N sample q → IsLipMatrix …`。
- T3 同理，作用域取 `j ∈ I_res(q) ∨ J ⊆ I_res(q)`。

我的版本是 `component_union_scoped` 和 `joint_union_scoped`，各自的证明体是 `rintro` 加一个 `exact`，直接调用源码已有的逐路径引理。它们蕴含 T1/T2，因此是严格改进。

### 5. 源码已证明 vs. 需自行补充

**源码已证明（无 `sorry`）**
- T1、T2、T3，以及支撑引理 `path_local_empirical_upper`、`proxy_path_component_guarantee_error_bound`、`proxy_path_joint_guarantee_error_bound`、`path_chain_eq_represented_proxy_on_path`。
- 这些结论是在 `hLq`（全路径）等 Lean 假设下的两条包含式。

**需自行补充（我已在本地补充并编译，不属于源码）**
1. 量词缩窄版本（§4.4），这是与正文字面等价所必需的。
2. 等价与蕴含：`hpathV ⇔ N.U ⊆ Vstar`，`hrep ⇒ N.U ⊆ dom proxy`，J 非空时联合域 = ⋂ 分量域。
3. 把"拟合含义"读成拟合球成员时：T2 的并集 W 满足 `InFittingBall d target proxy W J τ`。
   - 这需要 τ 在 J 上有限，T2 本身不要求。
   - `InFittingBall.error` 用 (target, proxy) 次序，与 T1/T2 的 (proxy, target) 次序靠对称性互换。
   - 本地已编译，未附代码。
4. 反例模型及其非空性、严格性（§4.2）。

**不在本推论范围内**
- "注（与全局保证域的比较）"是非形式评注，没有专门的 Lean 定理。我只核对了方向：同一矩阵下 S_{q,j} ⊆ S_j 推出 D_q ≥ D_global，支撑引理是 `weighted_anchor_distance_mono_of_subset`。
- Lip 证书的存在性、并集的非空性，正文都未断言。
- @h-6f9e054ce01ccfef、@h-9655cbb9401e5c90、@h-48bb46f7ef1c3c2e 的正文原文未提供，我以其 Lean 定义为准。

### 6. 复核方式

```
lake build formal_oet.vol_03.ch_14_empirical_network_fitting.path_guarantee_domains   # 成功
lake env lean <附录文件>                                                              # 无报错
```

- 对 T1–T3 和附录各定理执行 `#print axioms`，只出现 `propext / Classical.choice / Quot.sound`。
- 全库 grep `sorry|admit|axiom|native_decide|unsafe|implemented_by`，无命中。

### 附录：审计用 Lean 代码（全文已编译通过）

```lean
import formal_oet.vol_03.ch_14_empirical_network_fitting.path_guarantee_domains

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open formal_oet.vol_01.ch_04_operator_chain_calculus
open formal_oet.vol_01.ch_05_operator_networks
open formal_oet.vol_02.ch_07_fitting_foundations
open formal_oet.vol_03.ch_12_residuals_and_substitution
open formal_oet.vol_03.ch_14_empirical_network_fitting

namespace Audit
section PartA
variable {X I V : Type} {bot : X} [Fintype I]

/-- 第一式；Lip 证书只要求在并集指标内的路径上。 -/
theorem component_union_scoped
    (d : I → X → X → ENNReal) (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot) (N : FiniteOperatorNetwork X bot V)
    (sample : I → Set X) (delta_o : I → ENNReal)
    (Vstar : Set X) (Lq : N.ReachablePath → I → I → ENNReal)
    (Lstar : I → I → ENNReal) (j : I) (tau : ENNReal)
    (hrep : N.represents proxy) (hUV : N.U ⊆ Vstar)
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
    proxy_path_component_guarantee_error_bound d hd target proxy N sample delta_o q
      Vstar (Lq q) Lstar j tau hrep
      (fun y hy => hUV (N.path_domain_subset_source hy)) (hLq q hj) hLstar hj hxq⟩

/-- 第二式；同上。 -/
theorem joint_union_scoped
    (d : I → X → X → ENNReal) (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target proxy : Operator X bot) (N : FiniteOperatorNetwork X bot V)
    (sample : I → Set X) (delta_o : I → ENNReal)
    (Vstar : Set X) (Lq : N.ReachablePath → I → I → ENNReal)
    (Lstar : I → I → ENNReal) (J : Set I) (tau : I → ENNReal)
    (hrep : N.represents proxy) (hUV : N.U ⊆ Vstar)
    (hLq : ∀ q : N.ReachablePath, J ⊆ path_evaluable_components N sample q →
      IsLipMatrix d (N.path_chain q.nodes) (N.path_domain q.nodes) (Lq q))
    (hLstar : TargetLipEnvelopeCertificate d target Vstar Lstar) :
    {x | ∃ q : N.ReachablePath, J ⊆ path_evaluable_components N sample q ∧
      x ∈ path_joint_empirical_guarantee_domain d
        (fun i j => Lq q i j + Lstar i j) N sample q J
        (path_empirical_residual_upper d target N sample delta_o q) tau}
      ⊆ {x | x ∈ N.U ∧ ∀ j : I, j ∈ J → d j (proxy.func x) (target.func x) ≤ tau j} := by
  rintro x ⟨q, hJ, hxq⟩
  exact ⟨N.path_domain_subset_source hxq.1,
    proxy_path_joint_guarantee_error_bound d hd target proxy N sample delta_o q
      Vstar (Lq q) Lstar J tau hrep
      (fun y hy => hUV (N.path_domain_subset_source hy)) (hLq q hJ) hLstar hJ hxq⟩

theorem hpathV_iff (N : FiniteOperatorNetwork X bot V) (Vstar : Set X) :
    (∀ q : N.ReachablePath, N.path_domain q.nodes ⊆ Vstar) ↔ N.U ⊆ Vstar := by
  constructor
  · intro h x hx
    have hx' : x ∈ ⋃ p : N.ReachablePath, N.path_domain p.nodes := by
      rw [N.reachable_path_domains_cover]; exact hx
    rcases Set.mem_iUnion.mp hx' with ⟨q, hq⟩
    exact h q hq
  · intro h q x hx
    exact h (N.path_domain_subset_source hx)

theorem represents_dom (N : FiniteOperatorNetwork X bot V) (proxy : Operator X bot)
    (hrep : N.represents proxy) : N.U ⊆ dom proxy := by
  intro x hx
  have h1 : x ∈ dom N.extensional_operator := by
    rw [N.dom_extensional_operator_eq]; exact hx
  have h2 : N.extensional_operator.func x = proxy.func x := hrep x hx
  have h1' : N.extensional_operator.func x ≠ bot := h1
  intro h3
  exact h1' (h2.trans h3)

theorem path_joint_eq_biInter
    (d : I → X → X → ENNReal) (A : I → I → ENNReal)
    (N : FiniteOperatorNetwork X bot V) (sample : I → Set X)
    (q : N.ReachablePath) (J : Set I) (hJ : J.Nonempty) (eps tau : I → ENNReal) :
    path_joint_empirical_guarantee_domain d A N sample q J eps tau =
      ⋂ j ∈ J, path_component_empirical_guarantee_domain d A N sample q j (eps j) (tau j) := by
  ext x
  simp only [Set.mem_iInter]
  constructor
  · intro hx j hj
    exact ⟨hx.1, hx.2 j hj⟩
  · intro h
    obtain ⟨j₀, hj₀⟩ := hJ
    exact ⟨(h j₀ hj₀).1, fun j hj => (h j hj).2⟩

/-- 可分离规范族下，全 ⊤ 矩阵是任意 U ⊆ dom φ 上的 Lip 证书。 -/
theorem top_matrix_lip_of_separating
    (d : I → X → X → ENNReal) (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (hsep : IsSeparating d) (φ : Operator X bot) (U : Set X) (hU : U ⊆ dom φ) :
    IsLipMatrix d φ U (fun _ _ => ⊤) := by
  refine ⟨hU, ?_⟩
  intro x _ y _ j
  by_cases hxy : x = y
  · subst hxy
    rw [(hd j).dist_self]
    exact zero_le _
  · have hnz : ∃ i, d i x y ≠ 0 := by
      by_contra h
      push Not at h
      exact hxy (hsep x y (fun i => h i))
    obtain ⟨i, hi⟩ := hnz
    have : (⊤ : ENNReal) ≤ ∑ k : I, (⊤ : ENNReal) * d k x y := by
      calc (⊤ : ENNReal) = ⊤ * d i x y := (ENNReal.top_mul hi).symm
        _ ≤ ∑ k : I, (⊤ : ENNReal) * d k x y :=
          Finset.single_le_sum (f := fun k : I => (⊤ : ENNReal) * d k x y)
            (fun _ _ => zero_le _) (Finset.mem_univ i)
    exact le_trans le_top this

end PartA

/-! 附录 B：两条路径的网络，正文前提成立而 `hLq`（全路径）不成立 -/
namespace Model

abbrev Pt := Fin 5

def cls (x : Pt) : Nat := if x = 3 then 2 else x.val          -- 类 {0},{1},{2,3},{4}
noncomputable def dd (x y : Pt) : ENNReal := if cls x = cls y then 0 else ⊤
noncomputable def dI : Unit → Pt → Pt → ENNReal := fun _ => dd

theorem dI_ext : ∀ i : Unit, ExtendedPseudoMetric Pt (0 : Pt) (dI i) := by
  intro i
  refine ⟨⟨1, by decide⟩, ?_, ?_, ?_, ?_⟩
  · intro x; simp [dI, dd]
  · intro x y
    unfold dI dd
    by_cases h : cls x = cls y
    · rw [if_pos h, if_pos h.symm]
    · have h' : cls y ≠ cls x := fun e => h e.symm
      rw [if_neg h, if_neg h']
  · intro x y z
    unfold dI dd
    by_cases hxz : cls x = cls z
    · simp [hxz]
    · by_cases hxy : cls x = cls y
      · have hyz : cls y ≠ cls z := fun h => hxz (hxy.trans h)
        simp [hxy, hyz]
      · simp [hxz, hxy]
  · intro x hx
    unfold dI dd
    fin_cases x <;> simp_all [cls]

def op1 : Operator Pt 0 := ⟨fun x => if x = 1 then 1 else 0, by decide⟩
def op2 : Operator Pt 0 := ⟨fun x => if x = 2 then 2 else if x = 3 then 4 else 0, by decide⟩
def tgt : Operator Pt 0 := ⟨fun x => if x = 1 ∨ x = 2 ∨ x = 3 then x else 0, by decide⟩
def U0 : Set Pt := {x | x = 1 ∨ x = 2 ∨ x = 3}
def entryB (x : Pt) : Bool := decide (x ≠ 1)

noncomputable def Net : FiniteOperatorNetwork Pt 0 Bool where
  U := U0
  bot_not_mem := by simp [U0]
  node_fintype := inferInstance
  node_op := fun b => if b then op2 else op1
  node_dom_nonempty := by
    intro b
    cases b
    · exact ⟨1, by simp [dom, op1]⟩
    · exact ⟨2, by simp [dom, op2]⟩
  entry := fun x => entryB x.1
  entry_mem := by
    rintro ⟨x, hx⟩
    rcases hx with rfl | rfl | rfl <;> simp [dom, entryB, op1, op2]
  choice := fun _ _ => OutputChoice.stop
  choice_next_mem := by intro β γ y _ h; cases h
  depth_bound := 1
  path_of := fun x => [entryB x.1]
  path_terminal := fun x => TerminalPathFrom.stop rfl
  path_length_le_depth := by intro x; simp
  node_reachable := by
    intro β
    cases β
    · exact ⟨⟨1, Or.inl rfl⟩, by simp [entryB]⟩
    · exact ⟨⟨2, Or.inr (Or.inl rfl)⟩, by simp [entryB]⟩

theorem two_mem : (2 : Pt) ∈ Net.path_domain [true] :=
  ⟨Or.inr (Or.inl rfl), by simp [Net, entryB]⟩
theorem three_mem : (3 : Pt) ∈ Net.path_domain [true] :=
  ⟨Or.inr (Or.inr rfl), by simp [Net, entryB]⟩

/-- 路径 `[true]` 的路径链在其路径域上没有任何 Lip 矩阵：d 2 3 = 0，d (op2 2) (op2 3) = d 2 4 = ⊤。 -/
theorem no_lip_second_path :
    ¬ ∃ L : Unit → Unit → ENNReal,
      IsLipMatrix dI (Net.path_chain [true]) (Net.path_domain [true]) L := by
  rintro ⟨L, hL⟩
  have h := hL.2 2 two_mem 3 three_mem ()
  simp [dI, dd, cls, FiniteOperatorNetwork.path_chain, Net, OperatorChain, op2] at h

/-- 故源码 T1–T3 的 `hLq`（对每条可达路径都有证书）在此模型中不可满足。 -/
theorem hLq_all_unsat :
    ¬ ∃ Lq : Net.ReachablePath → Unit → Unit → ENNReal,
      ∀ q : Net.ReachablePath,
        IsLipMatrix dI (Net.path_chain q.nodes) (Net.path_domain q.nodes) (Lq q) := by
  rintro ⟨Lq, hLq⟩
  let q₂ : Net.ReachablePath := ⟨[true], ⟨2, two_mem⟩⟩
  exact no_lip_second_path ⟨Lq q₂, hLq q₂⟩

def sampleC : Unit → Set Pt := fun _ => {1}

/-- 零矩阵是每条带采样点的路径上的合法 Lip 证书。 -/
theorem hLq_index_ok (q : Net.ReachablePath)
    (hq : () ∈ path_evaluable_components Net sampleC q) :
    IsLipMatrix dI (Net.path_chain q.nodes) (Net.path_domain q.nodes)
      (fun _ _ => (0 : ENNReal)) := by
  rcases hq with ⟨x, hx1, hxq⟩
  have hx1' : x = 1 := by simpa [sampleC] using hx1
  subst hx1'
  rcases hxq with ⟨hU, hpath⟩
  refine ⟨Net.path_domain_subset_path_chain_dom q, ?_⟩
  intro a ha b hb j
  have key : ∀ y ∈ Net.path_domain q.nodes, y = 1 := by
    intro y hy
    rcases hy with ⟨hyU, hyp⟩
    have h1 : Net.path_of ⟨y, hyU⟩ = Net.path_of ⟨1, hU⟩ := hyp.trans hpath.symm
    simp [Net, entryB] at h1
    exact h1
  rw [key a ha, key b hb]
  simp [dI, dd]

theorem tgt_cert :
    TargetLipEnvelopeCertificate dI tgt U0 (fun _ _ => (1 : ENNReal)) := by
  refine ⟨⟨?_, ?_⟩⟩
  · intro x hx
    rcases hx with rfl | rfl | rfl <;> simp [dom, tgt]
  · intro x hx y hy j
    have hx' : tgt.func x = x := if_pos (show x = 1 ∨ x = 2 ∨ x = 3 from hx)
    have hy' : tgt.func y = y := if_pos (show y = 1 ∨ y = 2 ∨ y = 3 from hy)
    simp [hx', hy', dI]

/-- 正文第一式在该模型中成立（经缩窄版本）。 -/
theorem corollary_in_model (tau : ENNReal) :
    {x | ∃ q : Net.ReachablePath,
      () ∈ path_evaluable_components Net sampleC q ∧
      x ∈ path_component_empirical_guarantee_domain dI
        (fun i j => (fun (_ _ : Unit) => (0 : ENNReal)) i j
                  + (fun (_ _ : Unit) => (1 : ENNReal)) i j) Net sampleC q ()
        (path_empirical_residual_upper dI tgt Net sampleC (fun _ => 0) q ()) tau}
      ⊆ {x | x ∈ Net.U ∧ dI () (Net.extensional_operator.func x) (tgt.func x) ≤ tau} :=
  component_union_scoped dI dI_ext tgt Net.extensional_operator Net sampleC (fun _ => 0) U0
    (fun _ _ _ => 0) (fun _ _ => 1) () tau (fun _ _ => rfl) (fun _ hx => hx)
    (fun q hq => hLq_index_ok q hq) tgt_cert

end Model
end Audit
```