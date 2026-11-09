## 结论

在"节点域加细"这一情形下，所给 Lean 实现准确、完整地覆盖了正文定义和命题 #h-012f4ba72aeb3f20（网络加细保持外延等价）。没有发现会改变数学结论的缺陷。

- **定义**：构造 `NodePartitionData` + `NodePartitionData.network`（已含删冗余）与关系 `NodeDomainRefinement` 都和正文数据逐项对应。我补充验证了两个方向：由关系可以推出正文的全部公式，由正文数据也可以推出关系的全部字段。所以这个关系恰好刻画正文的加细结果。
- **命题**：两处已证明。
  - `refinement_preserves_local_equivalence` 对任意满足关系的 N′ 给出 φ_{N′} ≡_U φ_N。
  - `NodePartitionData.network_extensional_eq` 对规范构造给出外延算子整体相等，连 U 之外也相等。
- **核验**：在本工程中 `lake build` 成功；源码里没有 `sorry`、`admit` 或自定义 `axiom`。上述定理以及 `network_refinement`、`network_edge_domain_eq`、`network_choice_projection`、`piece_label_reached_iff`、`entry_domain_eq`、`path_projection`、`eval_projected` 用 `#print axioms` 检查，只依赖 `propext`、`Classical.choice`、`Quot.sound`。

有一处陈述层面的间接之处：关系里的 `choice_projection` 字段在正文定义中并不存在，它其实是正文证明的核心步骤。另外有几项包装性或外围结论没有在源码中写出来。这些我都在本工程里补写并编译通过（见附录），所以它们属于"建议补充"，不是数学缺口。

## 一、对象层的对应

- **网络的表示方式不同**：正文用图 (V,E)、转移域 D_{β→γ} 和入口片描述网络。Lean 的 `FiniteOperatorNetwork` 用 `entry`、`choice`、`path_of`、`depth_bound`、`node_reachable` 描述，其中入口片 `entry_domain`、边域 `edge_domain β γ = {z ∈ f_β(U_β) | choice β z = next γ}` 和终止域 `terminal_domain` 都是派生出来的。
  - 因此正文要求的三件事在 Lean 里自动成立：出边域互斥，"空入口片、空边域省略"，以及"终止域由出边域的补集确定"。
- **局部等价**：正文的 ≡_U 对应 `LocalEquivalent`，即在 U 上逐点相等。如果正文的 ≡_U 还要求 U⊆dom，也自动满足：两侧外延算子的定义域都等于 U（由 `dom_extensional_operator_eq` 和 `same_input_domain` 得到）。

## 二、定义逐项对照

| 正文要素 | 关系 `NodeDomainRefinement` | 构造 `NodePartitionData` | 判断 |
|---|---|---|---|
| 被加细节点 β，U_β=dom f_β | `target`，`N.node_dom target` | 参数 `target` | 一致 |
| 有限分划 U_β=⊔U_{β,a}，各块非空 | `part_count`、`piece`、`piece_nonempty`、`piece_disjoint`、`piece_cover` | `count`、`piece`、`nonempty`、`disjoint`、`cover` | 一致；`part_count_pos` 是冗余条件 |
| dom f_{β,a}=U_{β,a}，f_{β,a}≡f_β | `local_factor`、`local_domain`、`local_equiv` | `local_op`、`local_domain`、`local_eq` | 一致；正文所说"f_{β,a} 正是 f_β\|_{U_{β,a}}"已由 `local_op_eq_restrict` 证明 |
| 用子节点替换 β | `source`（单射）、`old_node_op_compat`、`piece_node_op_compat` | `Label := {v // v≠target} ⊕ Fin count`、`node_op` | 一致 |
| 子节点入口片 U^in_β∩U_{β,a}，其他入口片不变 | `same_input_domain`、`entry_projection`，由此推出 `entry_domain_eq`：N′.entry_domain v = N.entry_domain(πv) ∩ N′.node_dom v | `entry := lift_label (N.entry x) x` | 一致，已证明 |
| 入边、出边、自环、无关边的四个边域公式 | 统一公式 `edge_domain_eq`：(D_{πv→πw} ∩ f′_v(U′_v)) ∩ U′_w | `network_edge_domain_eq`、`self_loop_choice_iff` | 一致；四个特例都可由统一公式推出 |
| 删除未被任何输入经过的子节点（引理 h-ced8c7236326e104） | `old_node_present`、`piece_node_present_iff_reached`（`NodePieceReached`） | `network := presentation.prune`；`old_label_reached`、`piece_label_reached_iff` | 一致 |

### 为什么 `choice_projection` 只能在实际输出上要求

下面的例子说明，删冗余之后，"路由与原网络一致"在整个输出像上一般不成立。

- **网络 N**：单节点 β，U_β={0,1,2}，f_β(0)=0，f_β(1)=f_β(2)=2；自环转移域 D_{β→β}={2}；入口片 U={0}。输入 0 一步终止，所以这是合法的有限网络。
- **加细**：取 U_{β,1}={0,1}，U_{β,2}={2}。删冗余前有 D′_{β₁→β₂}={2}。
- **删冗余**：β₂ 从未被输入经过，因此被删除。删除后终止域 T′_{β₁}={0,2}，严格大于 f_{β,1}(U_{β,1})∩T_β={0}。
- **结果**：输出点 2 来自非实际输入 1。它在原网络中沿自环继续，在加细结果中却终止。

源码的处理恰好与此相符：`edge_domain_eq` 只约束保留节点之间的边，`choice_projection` 只在实际输出上要求。这也说明正文证明中的等式 T′_{β_a}=f_{β,a}(U_{β,a})∩T_β 只适用于删冗余之前。正文已写明"先考察尚未删除冗余节点的加细数据"，所以这不是错误。

### 关系恰好刻画正文的加细结果

- **由关系推出正文公式**：
  - 入口片公式由源码 `entry_domain_eq` 给出。
  - 自环公式见附录 `self_loop_edge`。
  - 以下公式我在另一个 scratch 文件中用同样的方法推出并编译通过，未收入附录：入边 `= N.edge_domain γ β ∩ U_{β,a}`，出边 `= N.edge_domain β γ ∩ f_{β,a}(U_{β,a})`，无关边不变，旧入口片不变。
  - 节点集由 `source` 单射加两个"存在性"字段确定。因此 N′ 的展示数据 (U, node_op, entry_domain, edge_domain) 在 `source` 重命名下是唯一的，关系不会接纳非教材网络。
- **由正文数据推出关系**：包括正文定义中没有的 `choice_projection` 字段，见附录 `choice_projection_derived` 和 `toNodeDomainRefinement`。所以关系也没有附加多余的约束。

## 三、命题对照

正文命题：若 N′ 由 N 经一次节点域加细得到，则 φ_{N′} ≡_U φ_N。对应的 Lean 结果如下。

- `refinement_preserves_local_equivalence (h : NetworkRefinement N N')`：结论是 `LocalEquivalent N'.extensional_operator N.extensional_operator N.U`。节点域情形取 `h = .node_domain href`。
- `allowed_network_refinement`：说明规范构造确实是一次允许的加细。
- `network_extensional_eq`：外延算子整体相等，比 ≡_U 更强。
- `refinement_preserves_representation`：加细保持网络表示。

证明步骤的对应：

| 正文证明 | Lean |
|---|---|
| 每次经过 β 时按当前输入选子块：(β,y_s)↦(β_{a_s},y_s)，值不变 | 构造：`lift_label`、`colour_path`、`lift_apply`；关系：`node_eval_eq` |
| 入口状态唯一 | 构造：`entry := lift_label …`；关系：`entry_projection` |
| 新边域给出 y_{s+1}∈D′，终止输出落入 T′ | 构造：`coloured_terminal`；关系：`terminal_projection`（经由 `choice_projection`） |
| 删冗余前的数据满足 (i)–(iii)，r′=r≤ℓ(N) | `presentation`（`depth_bound := N.depth_bound`）、`colour_path_length` |
| 删冗余后轨迹与输出不变 | `prune`、`prune_eval`、`prune_path_labels`、`network_path_projection` |
| φ_{N′}(x)=φ_N(x) | 构造：`coloured_eval`、`network_extensional_eq`；关系：`path_projection`、`eval_projected`、`terminal_path_unique` |

关系层的证明实际只用到以下字段：`node_eval_eq` 所需的 `local_domain`、`local_equiv` 和两个 `*_node_op_compat`，以及 `same_input_domain`、`entry_projection`、`choice_projection`。以下字段都没有用到：`piece_disjoint`、`piece_cover`、`source_injective`、两个存在性字段、`edge_domain_eq`。

这意味着保持外延的结论对更宽的一类"运行层"加细也成立。那些精确字段的作用是保证关系就是正文的定义，而不是用来推出结论。

## 四、已证明与需补充

### 源码已证明（无 `sorry`）

- `local_op_eq_restrict`：f_{β,a}=f_β|_{U_{β,a}}。
- `presentation` 和 `network`：构造先满足 (i)–(iii)，删冗余后得到有限网络。
- `old_label_reached`、`piece_label_reached_iff`：哪些节点被保留。
- `network_edge_domain_eq`、`self_loop_choice_iff`：边域公式，包括自环和从未被使用的边。
- `network_choice_projection`：实际输出上的路由与原网络一致。
- `network_refinement`、`allowed_network_refinement`：规范构造满足关系。
- 关系层的 `node_eval_eq`、`terminal_projection`、`path_projection`、`eval_projected`、`entry_domain_eq`、`retained_edge_mem`。
- 主结论 `refinement_preserves_local_equivalence`、`network_extensional_eq`、`refinement_preserves_representation`，以及路径结果 `network_path_labels`、`network_path_projection`。

### 需补充（都不影响命题成立；附录中的代码已编译通过）

(a) **`choice_projection` 是证明内容而不是定义内容。**
- **问题**：源码只对规范构造证明了它。对只按正文公式给出的任意 N′，一般定理在形式上多了一个前提。
- **影响**：没有数学影响，因为它可以推出。
- **论证**：
  1. 沿原网络的终止轨迹归纳。`exists_lift` 说明：原轨迹上每次实际进入节点 γ，相应的子节点必定被保留。
  2. 由 `edge_domain_eq` 可知加细后的网络沿同一节点前进（附录 `follow`），所以加细轨迹投影后就是原轨迹。
  3. 若加细网络在 v 处终止而原网络要继续，则由前缀求值相等（`prefix_eval`）可知原路径会继续，从而加细路径也会继续，矛盾。
- **修复方向**：把附录 A 的引理（`choice_projection_derived`、`toNodeDomainRefinement`、`preserves`）并入源码，或提供"由正文数据构造关系"的构造器。

(b) **结论的包装。**
- **问题**：一般定理只给出 `LocalEquivalent … N.U`。正文"外延等价"要求同一个非空输入域加 ≡_U；对象空间的等价要求外延算子相等。这两种形式都没有单独陈述。
- **修复**：附录 B 的 `refinement_extensional_equivalent` 同时给出两者。U 非空可由 `target` 存在和 `node_reachable` 得到。

(c) **对象空间层。**
- **问题**：正文规定加细结果需先编号编码才是 X_net 的元素。源码的 `RefinementRule (NetworkObject X bot)` 只是一个抽象参数，没有具体的节点域加细规则。
- **修复**：附录 B 的 `NodeDomainRule` 和 `node_domain_rule_preserves`。这一步对后续"不可约代表"有用。

(d) **证明内部的中间结论没有单独陈述。**
- ℓ(N′)=ℓ(N) 未陈述，已补在附录 C 的 `depth_eq`。
- 删冗余前的终止域公式和"旧节点终止域不变"没有形式化。删冗余后只能得到"⊇"（见第二节的例子）。命题本身不需要这些结论。

(e) **加细结果在重命名意义下的唯一性。**
- 第二节已说明展示数据被关系唯一确定，但源码没有"N′ 与 P.network 同构"的显式定理（例如通过 `relabel` 加 `presentation_data` 相等）。
- 若要把"该次加细的结果"当作 X_net 中良定义的对象来用，建议补上。

(f) **细节。**
- `part_count_pos` 是冗余条件。
- `piece_nonempty` 对应"各块非空"这一读法，而且必须如此：空块的局域算子是全未定义算子，违反转移图"定义域非空"的要求。
- `local_op_eq_restrict` 只在构造层给出；关系层同样成立，证明相同。

## 五、对正文定义本身的意见

- 定义是自洽的：新边域满足包含关系与出边互斥，入口片的细分保持输入分划。
- 有一处次序问题：定义中直接调用引理 h-ced8c7236326e104 删冗余，而该引理的前提——删冗余前的数据满足 (i)–(iii)——要到命题 #h-012f4ba72aeb3f20 的证明里才验证。Lean 的构造先用 `presentation` 证明 (i)–(iii)，再执行 `prune`，所以是良基的。建议正文在定义处注明，或把这一验证前移。
- 删冗余后终止域可能严格变大。阅读证明中的终止域等式时，要注意它只适用于删冗余之前。

## 附录：补充验证代码

以下代码为补充验证用，并非修改附件。它在本工程中用 `lake env lean` 编译通过，没有错误，三条 `#print axioms` 只显示三条标准公理。

```lean
import formal_oet.vol_01.ch_05_operator_networks.domain_refinement_construction

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_04_operator_chain_calculus
open formal_oet.vol_01.ch_05_operator_networks
open FiniteOperatorNetwork

namespace ReviewCheck
variable {X V V' : Type} {bot : X}

/-! ### A. 只含教材数据的节点域加细（去掉 `choice_projection`、单射性与非空性） -/
structure TextbookNDR (N : FiniteOperatorNetwork X bot V) (N' : FiniteOperatorNetwork X bot V') where
  target : V
  part_count : Nat
  piece : Fin part_count → Set X
  piece_disjoint : ∀ {a b : Fin part_count}, a ≠ b → Disjoint (piece a) (piece b)
  piece_cover : (⋃ a : Fin part_count, piece a) = N.node_dom target
  local_factor : Fin part_count → Operator X bot
  local_domain : ∀ a, dom (local_factor a) = piece a
  local_equiv : ∀ a, LocalEquivalent (local_factor a) (N.node_op target) (piece a)
  source : V' → ({β : V // β ≠ target} ⊕ Fin part_count)
  old_node_present : ∀ β : {β : V // β ≠ target}, ∃ β' : V', source β' = Sum.inl β
  piece_node_present_iff_reached : ∀ a : Fin part_count,
      (∃ β' : V', source β' = Sum.inr a) ↔ NodePieceReached N target piece a
  old_node_op_compat : ∀ (β' : V') (β : {β : V // β ≠ target}),
      source β' = Sum.inl β → N'.node_op β' = N.node_op β.val
  piece_node_op_compat : ∀ (β' : V') (a : Fin part_count),
      source β' = Sum.inr a → N'.node_op β' = local_factor a
  same_input_domain : N'.U = N.U
  entry_projection : ∀ x : N'.U, node_domain_projection target source (N'.entry x) =
      N.entry (transport_network_input same_input_domain x)
  edge_domain_eq : ∀ v w : V',
    N'.edge_domain v w =
      (N.edge_domain (node_domain_projection target source v)
        (node_domain_projection target source w) ∩ N'.node_image v) ∩ N'.node_dom w

namespace TextbookNDR
variable {N : FiniteOperatorNetwork X bot V} {N' : FiniteOperatorNetwork X bot V'}
variable (T : TextbookNDR N N')

def proj (v : V') : V := node_domain_projection T.target T.source v

theorem node_eval_eq (v : V') (x : X) (hx : x ∈ N'.node_dom v) :
    (N'.node_op v).func x = (N.node_op (T.proj v)).func x := by
  cases hs : T.source v with
  | inl w => simp [proj, node_domain_projection, hs, T.old_node_op_compat v w hs]
  | inr a =>
    have hxpiece : x ∈ T.piece a := by
      rw [← T.local_domain a, ← T.piece_node_op_compat v a hs]; exact hx
    simpa [proj, node_domain_projection, hs, T.piece_node_op_compat v a hs] using
      T.local_equiv a x hxpiece

theorem dom_subset (v : V') : N'.node_dom v ⊆ N.node_dom (T.proj v) := by
  intro x hx
  have h' : (N'.node_op v).func x ≠ bot := hx
  change (N.node_op (T.proj v)).func x ≠ bot
  rw [← T.node_eval_eq v x hx]; exact h'

/-- 原路径上 `γ` 的一次实际发生，其当前输入落在某个保留的 `N'` 节点（投影为 `γ`）中。 -/
theorem exists_lift (x0 : N.U) (pref suffix : List V) (γ : V)
    (hpath : N.path_of x0 = pref ++ γ :: suffix) :
    ∃ w : V', T.proj w = γ ∧ N.chain_eval_nodes pref x0.val ∈ N'.node_dom w := by
  have hlt : pref.length < (N.path_of x0).length := by simp [hpath]
  let n : Fin (N.path_of x0).length := ⟨pref.length, hlt⟩
  have hget : (N.path_of x0).get n = γ := by simp [n, hpath]
  have htake : (N.path_of x0).take n.val = pref := by simp [n, hpath]
  have hmem0 := terminal_path_prefix_input_mem N.choice_next_mem
    (N.entry_mem x0) (N.path_terminal x0) n
  rw [hget, htake] at hmem0
  have hmem : N.chain_eval_nodes pref x0.val ∈ N.node_dom γ := hmem0
  by_cases hγ : γ = T.target
  · subst hγ
    have hcov : N.chain_eval_nodes pref x0.val ∈ ⋃ a, T.piece a := by
      rw [T.piece_cover]; exact hmem
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hcov
    have hreach : NodePieceReached N T.target T.piece a := ⟨x0, n, hget, by rw [htake]; exact ha⟩
    obtain ⟨w, hw⟩ := (T.piece_node_present_iff_reached a).mpr hreach
    refine ⟨w, by simp [proj, node_domain_projection, hw], ?_⟩
    change N.chain_eval_nodes pref x0.val ∈ dom (N'.node_op w)
    rw [T.piece_node_op_compat w a hw, T.local_domain a]; exact ha
  · obtain ⟨w, hw⟩ := T.old_node_present ⟨γ, hγ⟩
    refine ⟨w, by simp [proj, node_domain_projection, hw], ?_⟩
    change N.chain_eval_nodes pref x0.val ∈ dom (N'.node_op w)
    rw [T.old_node_op_compat w ⟨γ, hγ⟩ hw]; exact hmem

/-- 教材证明的核心一步：仅由教材边域公式推出加细轨迹投影为原轨迹。 -/
theorem follow (x0 : N.U) :
    ∀ {v : V} {y : X} {p : List V}, TerminalPathFrom N.node_op N.choice v y p →
    ∀ (pref : List V), N.path_of x0 = pref ++ p → y = N.chain_eval_nodes pref x0.val →
    ∀ {v' : V'} {q : List V'}, T.proj v' = v → y ∈ N'.node_dom v' →
      TerminalPathFrom N'.node_op N'.choice v' y q → q.map T.proj = p := by
  intro v y p ht
  induction ht with
  | @stop v y hs =>
    intro pref hpath hy v' q hpv hyd ht'
    cases ht' with
    | stop _ => simp [hpv]
    | @next _ w _ rest hn _ =>
      exfalso
      have hz : (N'.node_op v').func y ∈ N'.edge_domain v' w := ⟨⟨y, hyd, rfl⟩, hn⟩
      rw [T.edge_domain_eq] at hz
      have h1 := hz.1.1.2
      have hp1 : node_domain_projection T.target T.source v' = v := hpv
      rw [T.node_eval_eq v' y hyd] at h1
      change N.choice (node_domain_projection T.target T.source v')
        ((N.node_op (node_domain_projection T.target T.source v')).func y) = _ at h1
      rw [hp1, hs] at h1
      cases h1
  | @next v γ y rest hs htail ih =>
    intro pref hpath hy v' q hpv hyd ht'
    have heval : (N'.node_op v').func y = (N.node_op v).func y := by
      rw [T.node_eval_eq v' y hyd, hpv]
    obtain ⟨rest', hrest'⟩ : ∃ rest', rest = γ :: rest' := by
      cases htail with
      | stop _ => exact ⟨[], rfl⟩
      | next _ _ => exact ⟨_, rfl⟩
    have hpath' : N.path_of x0 = (pref ++ [v]) ++ γ :: rest' := by rw [hpath, hrest']; simp
    have hy' : (N.node_op v).func y = N.chain_eval_nodes (pref ++ [v]) x0.val := by
      rw [FiniteOperatorNetwork.chain_eval_nodes_append, hy]; rfl
    obtain ⟨w, hpw, hwdom⟩ := T.exists_lift x0 (pref ++ [v]) rest' γ hpath'
    rw [← hy'] at hwdom
    have hydN : y ∈ N.node_dom v := by have := T.dom_subset v' hyd; rwa [hpv] at this
    have hzedge : (N'.node_op v').func y ∈ N'.edge_domain v' w := by
      rw [T.edge_domain_eq]
      refine ⟨⟨?_, ⟨y, hyd, rfl⟩⟩, ?_⟩
      · have hp1 : node_domain_projection T.target T.source v' = v := hpv
        have hp2 : node_domain_projection T.target T.source w = γ := hpw
        rw [hp1, hp2, heval]; exact ⟨⟨y, hydN, rfl⟩, hs⟩
      · rw [heval]; exact hwdom
    have hnext : N'.choice v' ((N'.node_op v').func y) = OutputChoice.next w := hzedge.2
    cases ht' with
    | stop hstop => rw [hnext] at hstop; cases hstop
    | @next _ w' _ restq hn hrestq =>
      have hww : w' = w := OutputChoice.next.inj (hn.symm.trans hnext)
      subst hww
      rw [heval] at hrestq
      have := ih (pref ++ [v]) (by rw [hpath]; simp) hy' hpw hwdom hrestq
      simp [hpv, this]

theorem path_projection (x : N'.U) :
    (N'.path_of x).map T.proj = N.path_of (transport_network_input T.same_input_domain x) :=
  T.follow _ (N.path_terminal _) [] (by simp) rfl
    (T.entry_projection x) (N'.entry_mem x) (N'.path_terminal x)

theorem prefix_eval {v x p} (ht : TerminalPathFrom N'.node_op N'.choice v x p)
    (hx : x ∈ N'.node_dom v) :
    ∀ (pref s : List V'), p = pref ++ s →
      chain_eval_nodes_core N'.node_op pref x =
        chain_eval_nodes_core N.node_op (pref.map T.proj) x := by
  induction ht with
  | @stop v x hs =>
    intro pref s hp
    cases pref with
    | nil => rfl
    | cons a pref' =>
      simp only [List.cons_append, List.cons.injEq] at hp
      obtain ⟨rfl, hrest⟩ := hp
      have hpref : pref' = [] := (List.append_eq_nil_iff.mp hrest.symm).1
      subst hpref
      simp [chain_eval_nodes_core, T.node_eval_eq _ x hx]
  | @next v w x rest hs ht ih =>
    intro pref s hp
    cases pref with
    | nil => rfl
    | cons a pref' =>
      simp only [List.cons_append, List.cons.injEq] at hp
      obtain ⟨rfl, hrest⟩ := hp
      simp only [List.map_cons, chain_eval_nodes_core]
      rw [← T.node_eval_eq _ x hx]
      exact ih (N'.choice_next_mem hx hs) pref' s hrest

/-- 源码关系中的辅助字段 `choice_projection` 可由教材数据推出。 -/
theorem choice_projection_derived (v : V') (z : X)
    (hz : z ∈ (N'.node_op v).func '' N'.node_actual_input_domain v) :
    map_output_choice T.proj (N'.choice v z) = N.choice (T.proj v) z := by
  rcases hz with ⟨y, hy, rfl⟩
  have hyd : y ∈ N'.node_dom v := N'.node_actual_input_domain_subset_node_dom v hy
  cases hc : N'.choice v ((N'.node_op v).func y) with
  | next w =>
    have hzedge : (N'.node_op v).func y ∈ N'.edge_domain v w := ⟨⟨y, hyd, rfl⟩, hc⟩
    rw [T.edge_domain_eq] at hzedge
    exact hzedge.1.1.2.symm
  | stop =>
    cases hN : N.choice (T.proj v) ((N'.node_op v).func y) with
    | stop => rfl
    | next γ =>
      exfalso
      rcases hy with ⟨x, pref, suffix, hpath, hyval, _⟩
      have hproj : N.path_of (transport_network_input T.same_input_domain x) =
          pref.map T.proj ++ T.proj v :: suffix.map T.proj := by
        rw [← T.path_projection x, hpath]; simp
      have hpre := T.prefix_eval (N'.path_terminal x) (N'.entry_mem x) pref (v :: suffix) hpath
      have hnext : N.choice (T.proj v) ((N.node_op (T.proj v)).func
          (chain_eval_nodes_core N.node_op (pref.map T.proj)
            (transport_network_input T.same_input_domain x).val)) = OutputChoice.next γ := by
        have e1 : (N'.node_op v).func y = (N.node_op (T.proj v)).func y := T.node_eval_eq v y hyd
        have e2 : y = chain_eval_nodes_core N.node_op (pref.map T.proj)
            (transport_network_input T.same_input_domain x).val := by rw [hyval]; exact hpre
        rw [← e2, ← e1]; exact hN
      obtain ⟨tail, htail⟩ :=
        terminal_path_suffix_of_next_at_prefix (N.path_terminal _) hproj hnext
      cases suffix with
      | nil => simp at htail
      | cons w rest =>
        have hadj := terminal_path_choice_at_adjacent_prefix (N'.path_terminal x) hpath
        have hw : N'.choice v ((N'.node_op v).func y) = OutputChoice.next w := by
          rw [hyval]; exact hadj
        rw [hw] at hc; cases hc

/-- 教材数据（加上单射与非空分块）即给出源码的 `NodeDomainRefinement`。 -/
def toNodeDomainRefinement (hinj : Function.Injective T.source) (hpos : 0 < T.part_count)
    (hne : ∀ a, (T.piece a).Nonempty) : NodeDomainRefinement N N' where
  target := T.target
  part_count := T.part_count
  part_count_pos := hpos
  piece := T.piece
  piece_nonempty := hne
  piece_disjoint := T.piece_disjoint
  piece_cover := T.piece_cover
  local_factor := T.local_factor
  local_domain := T.local_domain
  local_equiv := T.local_equiv
  source := T.source
  source_injective := hinj
  old_node_present := T.old_node_present
  piece_node_present_iff_reached := T.piece_node_present_iff_reached
  old_node_op_compat := T.old_node_op_compat
  piece_node_op_compat := T.piece_node_op_compat
  same_input_domain := T.same_input_domain
  entry_projection := T.entry_projection
  choice_projection := T.choice_projection_derived
  edge_domain_eq := T.edge_domain_eq

/-- 于是：任何只按教材数据给出的节点域加细都保持外延（直接调用源码主定理）。 -/
theorem preserves (hinj : Function.Injective T.source) (hpos : 0 < T.part_count)
    (hne : ∀ a, (T.piece a).Nonempty) :
    LocalEquivalent N'.extensional_operator N.extensional_operator N.U :=
  refinement_preserves_local_equivalence (.node_domain (T.toNodeDomainRefinement hinj hpos hne))
end TextbookNDR

/-! ### B. 包装：外延等价、整体算子相等、对象空间版本 -/
theorem refinement_extensional_equivalent
    {N : FiniteOperatorNetwork X bot V} {N' : FiniteOperatorNetwork X bot V'}
    (h : NetworkRefinement N N') :
    ExtensionalEquivalent N' N ∧ N'.extensional_operator = N.extensional_operator := by
  classical
  refine ⟨⟨h.same_input_domain, fun x hx =>
    refinement_preserves_local_equivalence h x (h.same_input_domain ▸ hx)⟩, ?_⟩
  apply Operator.ext
  funext x
  by_cases hx : x ∈ N.U
  · exact refinement_preserves_local_equivalence h x hx
  · have hx' : x ∉ N'.U := by rw [h.same_input_domain]; exact hx
    simp [FiniteOperatorNetwork.extensional_operator, hx, hx']

/-- 对象空间 `X_net` 上的节点域加细规则（编号编码后）保持外延读出。 -/
def NodeDomainRule : RefinementRule (NetworkObject X bot) :=
  fun O O' => ∃ (M : NonemptyOperatorNetwork X bot) (V' : Type)
    (N' : FiniteOperatorNetwork X bot V') (_ : NodeDomainRefinement M.network N')
    (hU : N'.U.Nonempty),
      O = NetworkObject.nonempty M ∧ O' = NetworkObject.nonempty (NonemptyOperatorNetwork.encode N' hU)

theorem node_domain_rule_preserves {O O' : NetworkObject X bot}
    (h : NodeDomainRule O O') : NetworkObject.ExtensionalEquivalent O' O := by
  rcases h with ⟨M, V', N', href, hU, rfl, rfl⟩
  show (NetworkObject.nonempty _).extensional_operator = (NetworkObject.nonempty M).extensional_operator
  rw [NetworkObject.extensional_operator_nonempty, NetworkObject.extensional_operator_nonempty,
    NonemptyOperatorNetwork.encode_extensional_operator]
  exact (refinement_extensional_equivalent (.node_domain href)).2

/-! ### C. 关系层推出教材的自环边域公式与求值深度不变 -/
namespace NDR
variable {N : FiniteOperatorNetwork X bot V} {N' : FiniteOperatorNetwork X bot V'}
variable (h : NodeDomainRefinement N N')

theorem self_loop_edge (v w : V') (a b : Fin h.part_count)
    (hv : h.source v = .inr a) (hw : h.source w = .inr b) :
    N'.edge_domain v w =
      N.edge_domain h.target h.target ∩ (h.local_factor a).func '' h.piece a ∩ h.piece b := by
  have pv : node_domain_projection h.target h.source v = h.target := by
    simp [node_domain_projection, hv]
  have pw : node_domain_projection h.target h.source w = h.target := by
    simp [node_domain_projection, hw]
  have iv : N'.node_image v = (h.local_factor a).func '' h.piece a := by
    change (N'.node_op v).func '' dom (N'.node_op v) = _
    rw [h.piece_node_op_compat v a hv, h.local_domain a]
  have dw : N'.node_dom w = h.piece b := by
    change dom (N'.node_op w) = _
    rw [h.piece_node_op_compat w b hw, h.local_domain b]
  rw [h.edge_domain_eq, pv, pw, iv, dw]

include h in
theorem depth_eq : N'.evaluation_depth = N.evaluation_depth := by
  have hlen : ∀ x : {x : X // x ∈ N'.U}, (N'.path_of x).length =
      (N.path_of (transport_network_input h.same_input_domain x)).length := by
    intro x; rw [← h.path_projection x, List.length_map]
  apply le_antisymm
  · apply N'.evaluation_depth_le_of_input_lengths
    intro x; rw [hlen x]; exact N.input_path_length_le_evaluation_depth _
  · apply N.evaluation_depth_le_of_input_lengths
    intro x
    let x' : {x : X // x ∈ N'.U} := ⟨x.val, h.same_input_domain.symm ▸ x.property⟩
    have := hlen x'
    change _ = (N.path_of x).length at this
    rw [← this]; exact N'.input_path_length_le_evaluation_depth x'
end NDR
end ReviewCheck

#print axioms ReviewCheck.TextbookNDR.preserves
#print axioms ReviewCheck.node_domain_rule_preserves
#print axioms ReviewCheck.NDR.depth_eq
```