**结论：部分覆盖。** 对“节点域加细保持外延等价”这一结论，源码的证明是正确的，构造版本完整覆盖了这一情形。但抽象关系 `NodeDomainRefinement` 的定义比正文宽。另外有两类关联缺口：源码没有把这个关系和正文的构造连起来，也没有把构造与正文的入口片、边域公式之间的对应写成定理。对这三点我都在 Lean 里做了检查，代码见附录。

## 一、核对方式

- 用 `lake build` 编译 `network_refinement` 和 `domain_refinement_construction`，编译通过，源码中没有 `sorry`。
- 对 `refinement_preserves_local_equivalence`、`NodePartitionData.network_extensional_eq`、`network_path_projection`、`self_loop_choice_iff`、`local_op_eq_restrict` 执行 `#print axioms`，结果只依赖 `propext`、`Classical.choice`、`Quot.sound`。
- 下文提到的补充定理和反例写在临时文件里，用 `lake env lean` 编译通过，同样只依赖这三条公理，没有 `sorryAx`。

## 二、定义的逐项对应

源码对正文定义给了两种形式化：**构造**（`NodePartitionData` → `presentation` → `prune`）和**关系**（`NodeDomainRefinement N N'`）。

| 正文条款 | 构造 `NodePartitionData` | 关系 `NodeDomainRefinement` |
|---|---|---|
| 有限非空分划 $U_\beta=\bigsqcup_a U_{\beta,a}$，各块非空 | `count_pos`、`nonempty`、`disjoint`、`cover`（等于 `N.node_dom target`） | 同名字段 |
| $\operatorname{dom}f_{\beta,a}=U_{\beta,a}$ 且 $f_{\beta,a}\equiv_{U_{\beta,a}}f_\beta$ | `local_domain`、`local_eq`；已证 `local_op_eq_restrict`，即 $f_{\beta,a}=f_\beta\vert_{U_{\beta,a}}$ | `local_domain`、`local_equiv` |
| 用子节点 $\beta_a$ 替换 $\beta$ | 标签类型 `{v // v ≠ target} ⊕ Fin count` | 字段 `source`（单射）、`old_node_present`、`piece_node_present_iff_reached` |
| 入口片取 $U_\beta^{in}\cap U_{\beta,a}$ | `entry := lift_label (N.entry x) x`；**源码未把公式写成定理** | 由 `entry_projection` 加 `entry_mem` 迫使成立 |
| 入边 $D_{\gamma\to\beta}\cap U_{\beta,a}$、出边 $D_{\beta\to\gamma}\cap f_{\beta,a}(U_{\beta,a})$、自环双交公式 | `choice` 经 `lift_label` 定义；**只有自环一条有定理**（`self_loop_choice_iff`），而且是剪枝前的 | **只在实际产生的输出上约束**（`choice_projection`） |
| 删除未经过的子节点（按 @h-ced8c7236326e104） | `presentation.prune`，即 `prune_choice` 把指向被删节点的转移改为 stop | `piece_node_present_iff_reached` |
| 结论 $\phi_{\mathcal N'}\equiv_U\phi_{\mathcal N}$ | `network_extensional_eq`：外延算子全域相等，强于 $\equiv_U$ | `refinement_preserves_local_equivalence`：在 `N.U` 上局部等价 |

**正文证明中的中间结论：**
- 加细结果是有限网络：构造版本把所有义务都做成了一个完整的 `FiniteOperatorNetwork`，所以这一点已被证明；关系版本则把它当作前提。
- 路径按实际输入重新着色，投影回去恰好是原路径：`network_path_labels` 和 `network_path_projection` 已证，因此路径长度不变。
- 自环在不同次经过时可以选不同子块：`colour_path` 用当前输入选块，这一点被正确实现了。

**关系版本证明的实际结构。** 它是一个投影模拟论证：
1. `node_eval_eq`：新节点在自身定义域上的取值等于原节点。
2. `terminal_projection`：沿实际输入的路由投影回原网络。
3. 由 `terminal_path_unique` 得 `path_projection`。
4. `eval_projected` 给出求值相等。

这个证明完全没有用到 `piece_disjoint`、`piece_cover` 等分划性质，所以结论适用于比正文更大的一类网络。

## 三、不足 1：抽象关系比正文定义宽

`choice_projection` 只约束 `N'.node_actual_input_domain v` 的像上的路由。节点输出像中实际没有产生的点，路由完全不受约束。正文则在整个输出像上规定了边域公式。

**反例（已在 Lean 中验证，`relation_admits_extra_edge`）：**
- 取 $\mathcal X=\{\bot=0,1,2\}$。
- 原网络 $\mathcal N$：单节点 $\beta$，$f_\beta=\mathrm{id}$（定义域 $\{1,2\}$），$U=\{1\}$，没有边。
- 正文对 $\mathcal N$ 的节点域加细只有两种：
  - $q=1$ 时，结果与 $\mathcal N$ 同构，没有边；
  - 分划为 $\{1\},\{2\}$ 时，子节点 $\beta_2$ 不会被经过，删除后剩下的节点算子定义域为 $\{1\}$。
- `loopNet`：与 $\mathcal N$ 相同，只是在从不实际产生的输出 $2$ 上加一条自环，自环边域为 $\{2\}$。它仍是合法的有限网络：输入 $1$ 一步终止。
- 用 $q=1$ 的数据可以构造出 `NodeDomainRefinement baseNet loopNet` 的实例，因此 `NetworkRefinement baseNet loopNet` 成立。
- 但 `loopNet` 不是 $\mathcal N$ 任何一次正文加细的结果：
  - 节点域加细的结果都没有边；
  - 代数加细得到两个都被经过的节点，而 `loopNet` 只有一个节点。
- Lean 中验证的具体差别：
  - 两者的边域分别为 `∅` 与 `{2}`，`presentation_data` 不相等；
  - 终止域分别是 $\{1,2\}$ 与 $\{1\}$。

**数学影响：**
- 作为“定义”，这个关系并没有刻画正文的节点域加细。它只确定节点集、局域算子、入口，以及实际输出上的路由，未产生输出上的边与终止域是任意的。
- 正文的加细保持节点标签图的无环性：新边投影后都是原边，自环只来自原自环。这个关系却会把无环网络“加细”成有环网络，所以凡依赖完整边数据的结论都不能经由它传递，例如属于 $\mathcal X^{dag}_{net}$、对象等同、表示层读出、多步加细可达集。
- 对本题的命题没有危害：前提更宽，定理反而更强，外延等价仍然成立。
- 是否存在加细后继，两种定义等价：关系的分划数据总能生成正文的加细，反方向见下一节的桥接。

**修复方向：**
- 要么把它改名、改文档，说明它是“投影模拟”这一充分条件，不再作为正文的定义；
- 要么增加一个精确字段：对所有 $z\in$ `N'.node_image v` 和所有 `w'`，
  `N'.choice v z = .next w'` ⟺ `N.choice (π v) z = .next (π w')` ∧ ∀ b, `source w' = .inr b → z ∈ piece b`。
  这条字段对 `w'` 只遍历仍然存在的节点，因而已经包含了剪枝。现有证明不需要改，补充的 `network_edge_domain` 正好提供这条字段的满足性。

## 四、不足 2：关系与构造没有桥接

源码在文档里说明两者各自证明，但没有任何定理说明 `P.network` 是 `NodeDomainRefinement` 的实例。后果是：
- 关系版本的定理在源码中没有任何被验证的实例，原则上可能是空真的；
- 正文的构造也从未进入 `NetworkRefinement`。

**补充（已编译通过）：**
- `NodePartitionData.to_refinement : NodeDomainRefinement N P.network`；
- 由它得到推论 `refinement_preserves_local_equivalence (.node_domain P.to_refinement)`。

证明的关键步骤是：在实际输出处，提升后的目标标签一定在终止路径的后继中出现，因此被剪枝保留。这一步用到 `terminal_path_suffix_of_next_at_prefix`。`old_node_present` 这一字段同时证明了正文的断言“只有子节点可能被删”。

## 五、不足 3：构造与正文公式的对应只证了一部分

源码只有剪枝前的自环路由定理。我补充了剪枝后网络的统一公式：

- `network_edge_domain`：对存在的标签 $v,w$，
  $z\in D'_{v\to w}$ ⟺ $z\in\operatorname{img} f'_v$ ∧ `N.choice (π v) z = next (π w)` ∧ （若 $w=\beta_b$，则 $z\in U_{\beta,b}$）。
  它依次给出入边公式、出边公式、自环双交公式，以及无关边不变。终止域即像减去边域之并，因此 $T'_{\beta_a}=f_{\beta,a}(U_{\beta,a})\cap T_\beta$，在剪枝处再扩大。
- `network_entry_domain`：入口片为 $U^{in}_{\pi v}\cap U_{\beta,a}$。

## 六、次要缺口

- 正文给出的长度界是 $\ell(\mathcal N)$，构造里用的是存储的 `N.depth_bound`。由路径投影可以推出 `evaluation_depth` 相等，但源码没有写出来。
- 源码没有把结论封装成 `ExtensionalEquivalent N' N`（即 $U$ 相同且局部等价），也没有给出 `NetworkObject` 编号层面的版本，以及关系沿重编号的传递。这几项都只是简单推论。
- `RefinementRule` 和 `Irreducible` 是抽象的，没有用节点域加细来实例化。

## 七、对正文定义本身的说明

- 正文所说的“选取 $f_{\beta,a}$”其实没有选择余地，它唯一等于 $f_\beta|_{U_{\beta,a}}$。
- $q=1$ 的平凡分划，正文和 Lean 都允许，它产生的是重标号副本。讨论不可约性时，规则族 $R$ 需要排除这种情形。这一点属于定义层面的观察，不是形式化错误。
- 我逐条核对了正文证明的统一边域等式与终止域公式，没有发现问题。

## 八、已证与需补充

- **源码已证：**
  - 构造得到有限网络，且外延算子全域相等；
  - 路径重新着色后投影回去恰好是原路径；
  - $f_{\beta,a}$ 等于限制算子；
  - 自环路由（剪枝前）；
  - 关系版本的外延局部等价。
- **需补充：**
  - 精确化关系，或把它重新定位为充分条件；
  - 桥接 `to_refinement`；
  - 边域与入口片公式；
  - $\ell(\mathcal N)$ 长度界；
  - `ExtensionalEquivalent` 和对象层的封装。

前三项附录里已给出可编译的证明或修复所需的证明，后两项只是简单推论。

## 附录：验证代码（导入原模块，不修改原文件）

**A. 桥接**
```lean
import formal_oet.vol_01.ch_05_operator_networks.network_refinement
import formal_oet.vol_01.ch_05_operator_networks.domain_refinement_construction
namespace formal_oet.vol_01.ch_05_operator_networks
open formal_oet.vol_01.ch_01_foundations formal_oet.vol_01.ch_04_operator_chain_calculus FiniteOperatorNetwork
variable {X V : Type} {bot : X} {N : FiniteOperatorNetwork X bot V} {target : V}
namespace NodePartitionData
variable (P : NodePartitionData N target)

theorem colour_path_getElem : ∀ (p : List V) (y : X) (n : Nat) (hn : n < p.length),
    (P.colour_path p y)[n]'(by simpa using hn) =
      P.lift_label p[n] (chain_eval_nodes_core N.node_op (p.take n) y)
  | [], _, n, hn => by simp at hn
  | v :: rest, y, 0, _ => by simp [colour_path, chain_eval_nodes_core]
  | v :: rest, y, n + 1, hn => by
      simp only [colour_path, List.getElem_cons_succ, List.take_succ_cons, chain_eval_nodes_core]
      exact colour_path_getElem rest _ n (by simpa using hn)

theorem lift_label_eq_inr {w : V} {z : X} {a : Fin P.count}
    (h : P.lift_label w z = .inr a) : w = target ∧ P.piece_at z = a := by
  classical
  unfold lift_label at h
  split_ifs at h with hw
  · exact ⟨hw, Sum.inr.inj h⟩

theorem chain_eval_subtype {Q : P.Label → Prop} (l : List {v // Q v}) (x : X) :
    chain_eval_nodes_core (fun v : {v // Q v} => P.node_op v.val) l x =
      chain_eval_nodes_core P.node_op (l.map Subtype.val) x := by
  induction l generalizing x with
  | nil => rfl
  | cons v rest ih => exact ih _

theorem ndp_eq (v : {v // P.presentation.Reached v}) :
    node_domain_projection target (Subtype.val) v = P.projection v.val := by
  rcases v with ⟨v, hv⟩; cases v <;> rfl

theorem ndp_fun :
    node_domain_projection target (Subtype.val : {v // P.presentation.Reached v} → P.Label) =
      P.projection ∘ Subtype.val := funext P.ndp_eq

noncomputable def to_refinement : NodeDomainRefinement N P.network where
  target := target
  part_count := P.count
  part_count_pos := P.count_pos
  piece := P.piece
  piece_nonempty := P.nonempty
  piece_disjoint := P.disjoint
  piece_cover := P.cover
  local_factor := P.local_op
  local_domain := P.local_domain
  local_equiv := fun a x hx => P.local_eq a x hx
  source := Subtype.val
  source_injective := Subtype.val_injective
  old_node_present := by
    intro β
    obtain ⟨x, hx⟩ := N.node_reachable β.val
    have hm : β.val ∈ (P.colour_path (N.path_of x) x.val).map P.projection := by
      rw [P.colour_path_projection]; exact hx
    obtain ⟨l, hl, hlβ⟩ := List.mem_map.mp hm
    have hl' : l = .inl β := by
      cases l with
      | inl w => exact congrArg Sum.inl (Subtype.ext hlβ)
      | inr a => exact absurd hlβ.symm β.property
    subst hl'
    exact ⟨⟨.inl β, x, hl⟩, rfl⟩
  piece_node_present_iff_reached := by
    intro a
    constructor
    · rintro ⟨⟨v, x, hv⟩, rfl⟩
      obtain ⟨n, hn, hget⟩ := List.getElem_of_mem hv
      have hlen : n < (N.path_of x).length := by simpa [presentation] using hn
      have hlab := P.colour_path_getElem (N.path_of x) x.val n hlen
      have hget' := hlab.symm.trans hget
      obtain ⟨ht, hpiece⟩ := P.lift_label_eq_inr hget'
      have hmem := terminal_path_prefix_input_mem N.choice_next_mem
        (N.entry_mem x) (N.path_terminal x) ⟨n, hlen⟩
      refine ⟨x, ⟨n, hlen⟩, by simpa using ht, ?_⟩
      have hdom : chain_eval_nodes_core N.node_op ((N.path_of x).take n) x.val ∈
          N.node_dom target := by simpa [List.get_eq_getElem, ht] using hmem
      have := P.mem_piece_at _ hdom
      rw [hpiece] at this; exact this
    · rintro ⟨x, n, hlab, hin⟩
      refine ⟨⟨.inr a, x, ?_⟩, rfl⟩
      change Sum.inr a ∈ P.colour_path (N.path_of x) x.val
      have hlab' := P.colour_path_getElem (N.path_of x) x.val n.val n.isLt
      have hpa := P.piece_at_unique _ a hin
      have : (P.colour_path (N.path_of x) x.val)[n.val]'(by simp) = Sum.inr a := by
        rw [hlab']
        have h2 : (N.path_of x)[n.val] = target := by simpa [List.get_eq_getElem] using hlab
        rw [h2]; unfold lift_label; simp only [↓reduceDIte]; exact congrArg Sum.inr hpa
      rw [← this]; exact List.getElem_mem _
  old_node_op_compat := by intro β' β hs; change P.node_op β'.val = _; rw [hs]; rfl
  piece_node_op_compat := by intro β' a hs; change P.node_op β'.val = _; rw [hs]; rfl
  same_input_domain := rfl
  entry_projection := by
    intro x
    change node_domain_projection target Subtype.val (P.network.entry x) = N.entry x
    rw [P.ndp_eq]; exact P.projection_lift _ _
  choice_projection := by
    intro v z hz
    rw [P.ndp_eq, P.ndp_fun]
    obtain ⟨y, ⟨x, pref, suffix, hpath, hy, hydom⟩, rfl⟩ := hz
    change map_output_choice _ (prune_choice P.presentation.Reached P.choice v
      ((P.node_op v.val).func y)) = _
    unfold prune_choice
    cases hc : P.choice v.val ((P.node_op v.val).func y) with
    | stop =>
        simp only [map_output_choice]
        unfold choice at hc
        cases hN : N.choice (P.projection v.val) ((P.node_op v.val).func y) with
        | stop => exact hN.symm
        | next w => rw [hN] at hc; simp [map_output_choice] at hc
    | next w' =>
        have hreach : P.presentation.Reached w' := by
          have hlabels := P.presentation.prune_path_labels x
          have hp' : P.presentation.path_of x =
              pref.map Subtype.val ++ v.val :: suffix.map Subtype.val := by
            rw [← hlabels]; change List.map Subtype.val (P.network.path_of x) = _
            rw [hpath]; simp
          have hyeq : y = chain_eval_nodes_core P.node_op (pref.map Subtype.val) x.val := by
            rw [hy]; exact P.chain_eval_subtype pref x.val
          have hnext : P.choice v.val ((P.node_op v.val).func
                (chain_eval_nodes_core P.node_op (pref.map Subtype.val) x.val)) =
              OutputChoice.next w' := by rw [← hyeq]; exact hc
          obtain ⟨tail, htail⟩ := terminal_path_suffix_of_next_at_prefix
            (P.presentation.path_terminal x) hp' hnext
          refine ⟨x, ?_⟩; rw [hp', htail]; simp
        simp only [hreach, ↓reduceDIte, map_output_choice]
        unfold choice at hc
        cases hN : N.choice (P.projection v.val) ((P.node_op v.val).func y) with
        | stop => rw [hN] at hc; simp [map_output_choice] at hc
        | next w =>
            rw [hN] at hc
            simp only [map_output_choice, OutputChoice.next.injEq] at hc
            subst hc
            simp only [Function.comp_apply, P.projection_lift]
            exact hN.symm
end NodePartitionData

theorem node_domain_construction_preserves_via_relation
    {X V : Type} {bot : X} {N : FiniteOperatorNetwork X bot V} {target : V}
    (P : NodePartitionData N target) :
    LocalEquivalent P.network.extensional_operator N.extensional_operator N.U :=
  refinement_preserves_local_equivalence (.node_domain P.to_refinement)
end formal_oet.vol_01.ch_05_operator_networks
```

**B. 构造的边域与入口片公式**
```lean
import formal_oet.vol_01.ch_05_operator_networks.domain_refinement_construction
namespace formal_oet.vol_01.ch_05_operator_networks
open formal_oet.vol_01.ch_01_foundations formal_oet.vol_01.ch_04_operator_chain_calculus FiniteOperatorNetwork
variable {X V : Type} {bot : X} {N : FiniteOperatorNetwork X bot V} {target : V}
namespace NodePartitionData
variable (P : NodePartitionData N target)

theorem image_subset_original (v : P.Label) :
    (P.node_op v).func '' dom (P.node_op v) ⊆ N.node_image (P.projection v) := by
  rintro z ⟨y, hy, rfl⟩
  exact ⟨y, P.node_domain_subset_original v hy, (P.node_apply_eq_original v y hy).symm⟩

theorem lift_label_eq_iff {u : V} {z : X} (hz : z ∈ N.node_dom u) (w : P.Label) :
    P.lift_label u z = w ↔ P.projection w = u ∧ ∀ b, w = .inr b → z ∈ P.piece b := by
  classical
  by_cases hu : u = target
  · subst hu
    simp only [lift_label, ↓reduceDIte]
    cases w with
    | inl w' => simp [projection, w'.property]
    | inr b =>
      simp only [Sum.inr.injEq, projection, true_and]
      constructor
      · rintro rfl b' rfl; exact P.mem_piece_at z hz
      · intro h; exact P.piece_at_unique z b (h b rfl)
  · simp only [lift_label, hu, ↓reduceDIte]
    cases w with
    | inl w' =>
      simp only [Sum.inl.injEq, projection, reduceCtorEq, false_implies, implies_true, and_true]
      constructor
      · rintro rfl; rfl
      · intro h; exact Subtype.ext h.symm
    | inr b => simp [projection, Ne.symm hu]

theorem network_edge_domain (v w : {v // P.presentation.Reached v}) (z : X) :
    z ∈ P.network.edge_domain v w ↔
      z ∈ (P.node_op v.val).func '' dom (P.node_op v.val) ∧
        N.choice (P.projection v.val) z = .next (P.projection w.val) ∧
        ∀ b, w.val = .inr b → z ∈ P.piece b := by
  classical
  change (z ∈ (P.node_op v.val).func '' dom (P.node_op v.val) ∧
      prune_choice P.presentation.Reached P.choice v z = .next w) ↔ _
  constructor
  · rintro ⟨himg, hc⟩
    refine ⟨himg, ?_⟩
    have hzN := P.image_subset_original v.val himg
    unfold prune_choice at hc
    split at hc
    · cases hc
    · rename_i w' hw'
      split at hc
      · simp only [OutputChoice.next.injEq] at hc
        subst hc
        unfold choice map_output_choice at hw'
        split at hw'
        · cases hw'
        · rename_i u hu
          simp only [OutputChoice.next.injEq] at hw'
          have hzu : z ∈ N.node_dom u := N.edge_domain_subset_node_dom ⟨hzN, hu⟩
          obtain ⟨h1, h2⟩ := (P.lift_label_eq_iff hzu _).mp hw'
          exact ⟨by rw [hu, h1], h2⟩
      · cases hc
  · rintro ⟨himg, hc, hpiece⟩
    refine ⟨himg, ?_⟩
    have hzN := P.image_subset_original v.val himg
    have hzu : z ∈ N.node_dom (P.projection w.val) := N.edge_domain_subset_node_dom ⟨hzN, hc⟩
    have hlift : P.lift_label (P.projection w.val) z = w.val :=
      (P.lift_label_eq_iff hzu _).mpr ⟨rfl, hpiece⟩
    have hP : P.choice v.val z = .next w.val := by simp [choice, hc, map_output_choice, hlift]
    unfold prune_choice; rw [hP]; simp [w.property]

theorem network_entry_domain (v : {v // P.presentation.Reached v}) (x : X) :
    x ∈ P.network.entry_domain v ↔
      x ∈ N.entry_domain (P.projection v.val) ∧ ∀ b, v.val = .inr b → x ∈ P.piece b := by
  constructor
  · rintro ⟨hx, he⟩
    have he' : P.lift_label (N.entry ⟨x, hx⟩) x = v.val := congrArg Subtype.val he
    obtain ⟨h1, h2⟩ := (P.lift_label_eq_iff (N.entry_mem ⟨x, hx⟩) _).mp he'
    exact ⟨⟨hx, h1.symm⟩, h2⟩
  · rintro ⟨⟨hx, he⟩, hp⟩
    refine ⟨hx, Subtype.ext ?_⟩
    change P.lift_label (N.entry ⟨x, hx⟩) x = v.val
    exact (P.lift_label_eq_iff (N.entry_mem ⟨x, hx⟩) _).mpr ⟨he.symm, hp⟩
end NodePartitionData
end formal_oet.vol_01.ch_05_operator_networks
```

**C. 反例（关系比正文定义宽）**
```lean
import formal_oet.vol_01.ch_05_operator_networks.network_refinement
import formal_oet.vol_01.ch_05_operator_networks.network_identity
namespace formal_oet.vol_01.ch_05_operator_networks
open formal_oet.vol_01.ch_01_foundations formal_oet.vol_01.ch_04_operator_chain_calculus FiniteOperatorNetwork

noncomputable def baseNet : FiniteOperatorNetwork (Fin 3) 0 Unit where
  U := {1}
  bot_not_mem := by simp
  node_fintype := inferInstance
  node_op := fun _ => id_operator
  node_dom_nonempty := fun _ => ⟨1, by simp [dom, id_operator]⟩
  entry := fun _ => ()
  entry_mem := by
    rintro ⟨x, hx⟩; simp only [Set.mem_singleton_iff] at hx; subst hx; simp [dom, id_operator]
  choice := fun _ _ => .stop
  choice_next_mem := by intro β γ y _ h; cases h
  depth_bound := 1
  path_of := fun _ => [()]
  path_terminal := fun _ => TerminalPathFrom.stop rfl
  path_length_le_depth := by intro x; simp
  node_reachable := by intro β; exact ⟨⟨1, rfl⟩, by simp⟩

noncomputable def loopNet : FiniteOperatorNetwork (Fin 3) 0 Unit where
  U := {1}
  bot_not_mem := by simp
  node_fintype := inferInstance
  node_op := fun _ => id_operator
  node_dom_nonempty := fun _ => ⟨1, by simp [dom, id_operator]⟩
  entry := fun _ => ()
  entry_mem := by
    rintro ⟨x, hx⟩; simp only [Set.mem_singleton_iff] at hx; subst hx; simp [dom, id_operator]
  choice := fun _ z => if z = 2 then .next () else .stop
  choice_next_mem := by
    intro β γ y hy h
    simp only [id_operator, id] at h ⊢
    split_ifs at h with h2
    · subst h2; simp [dom]
  depth_bound := 1
  path_of := fun _ => [()]
  path_terminal := by
    rintro ⟨x, hx⟩; simp only [Set.mem_singleton_iff] at hx; subst hx
    exact TerminalPathFrom.stop (by simp [id_operator])
  path_length_le_depth := by intro x; simp
  node_reachable := by intro β; exact ⟨⟨1, rfl⟩, by simp⟩

theorem actual_input_eq_one {M : FiniteOperatorNetwork (Fin 3) 0 Unit}
    (hU : M.U = {1}) (hp : ∀ x, M.path_of x = [()]) {y : Fin 3}
    (hy : y ∈ M.node_actual_input_domain ()) : y = 1 := by
  rcases hy with ⟨x, pref, suffix, hpath, rfl, _⟩
  rw [hp x] at hpath
  cases pref with
  | nil =>
      have h : x.val ∈ M.U := x.property
      have h' : x.val ∈ ({1} : Set (Fin 3)) := hU ▸ h
      simpa [FiniteOperatorNetwork.chain_eval_nodes, chain_eval_nodes_core] using h'
  | cons a pref => have := congrArg List.length hpath; simp at this

noncomputable def trivialRefinement (M : FiniteOperatorNetwork (Fin 3) 0 Unit)
    (hU : M.U = {1}) (hop : M.node_op = fun _ => id_operator)
    (hp : ∀ x, M.path_of x = [()]) (hc1 : M.choice () 1 = .stop) :
    NodeDomainRefinement baseNet M where
  target := ()
  part_count := 1
  part_count_pos := by decide
  piece := fun _ => dom (id_operator : Operator (Fin 3) 0)
  piece_nonempty := fun _ => ⟨1, by simp [dom, id_operator]⟩
  piece_disjoint := by intro a b hab; exact absurd (Subsingleton.elim a b) hab
  piece_cover := by
    ext x; simp [FiniteOperatorNetwork.node_dom, baseNet,
      FiniteOperatorNetwork.to_transition_graph, OperatorTransitionGraph.node_dom]
  local_factor := fun _ => id_operator
  local_domain := fun _ => rfl
  local_equiv := fun _ _ _ => rfl
  source := fun _ => .inr 0
  source_injective := fun _ _ _ => rfl
  old_node_present := fun β => absurd rfl β.property
  piece_node_present_iff_reached := by
    intro a
    have ha : a = 0 := Subsingleton.elim _ _
    subst ha
    simp only [exists_const, true_iff]
    refine ⟨⟨1, rfl⟩, ⟨0, by simp [baseNet]⟩, rfl, ?_⟩
    simp [baseNet, FiniteOperatorNetwork.chain_eval_nodes, chain_eval_nodes_core, dom, id_operator]
  old_node_op_compat := by intro β' β h; cases h
  piece_node_op_compat := by intro β' a _; rw [hop]
  same_input_domain := by rw [hU]; rfl
  entry_projection := fun _ => rfl
  choice_projection := by
    rintro ⟨⟩ z ⟨y, hy, rfl⟩
    have h1 := actual_input_eq_one hU hp hy
    subst h1
    rw [show (M.node_op ()).func 1 = 1 by rw [hop]; rfl, hc1]
    rfl

noncomputable def baseRef : NodeDomainRefinement baseNet baseNet :=
  trivialRefinement baseNet rfl rfl (fun _ => rfl) rfl
noncomputable def loopRef : NodeDomainRefinement baseNet loopNet :=
  trivialRefinement loopNet rfl rfl (fun _ => rfl) (by simp [loopNet])

theorem relation_admits_extra_edge :
    baseRef.part_count = loopRef.part_count ∧ (∀ a, baseRef.piece a = loopRef.piece a) ∧
    baseNet.edge_domain () () = ∅ ∧ loopNet.edge_domain () () = {2} ∧
    baseNet.presentation_data ≠ loopNet.presentation_data := by
  have hb : baseNet.edge_domain () () = ∅ := by
    ext z; simp [FiniteOperatorNetwork.edge_domain, FiniteOperatorNetwork.to_transition_graph, baseNet]
  have hl : loopNet.edge_domain () () = {2} := by
    ext z
    simp only [FiniteOperatorNetwork.edge_domain, FiniteOperatorNetwork.to_transition_graph,
      loopNet, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨_, h⟩; by_contra hz; simp [hz] at h
    · rintro rfl; exact ⟨⟨2, by simp [dom, id_operator], rfl⟩, by simp⟩
  refine ⟨rfl, fun _ => rfl, hb, hl, ?_⟩
  intro h
  have := congrFun (congrFun (presentation_data_eq_edge_domain h) ()) ()
  rw [hb, hl] at this
  have h2 : (2 : Fin 3) ∈ (∅ : Set (Fin 3)) := by rw [this]; rfl
  exact h2
end formal_oet.vol_01.ch_05_operator_networks
```