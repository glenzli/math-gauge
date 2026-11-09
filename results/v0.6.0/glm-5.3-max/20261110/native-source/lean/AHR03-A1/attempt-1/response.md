所有验证均已完成。以下是我的审阅报告。

---

# 审阅报告：节点域加细定义与"网络加细保持外延等价"的 Lean 实现

## 总判断

所给实现**准确且完整地覆盖**了题设数学范围：`source.md` 中"定义（网络加细）(i)（节点域加细）"的全部子条款（含加细后删除未被轨迹经过的子节点），以及"命题 #h-012f4ba72aeb3f20（网络加细保持外延等价）"在节点域情形的陈述与证明。全部结论经机器核查：`lake build` 通过；全仓库无 `sorry/admit/native_decide`；18 条相关定理的 `#print axioms` 仅含 `propext, Classical.choice, Quot.sound`。正文四条边域公式与实现中单一统一交集律的等价性，我另行用 Lean 机器验证通过（证据见第七节）。需要补充的内容仅为若干"可加可不加"的显式化定理（第八节），无任何数学内容缺失。

---

## 一、审阅范围界定

**在范围内**：
- `source.md` §"网络加细与不可约代表"中 **定义（网络加细）(i)（节点域加细）** 的全部条款：有限非空分划、子域上的局域算子及其限制性质、子节点替换、入口输入片细分、入边/出边/自环三类新边域公式、不关联边与入口片不变、空片空边省略、终止域由出边域补集确定、"$f_{\beta,a}$ 正是 $f_\beta|_{U_{\beta,a}}$"、以及末句"加细后若产生不被任何输入轨迹经过的子节点，按 #h-ced8c7236326e104 删除"；
- **命题 #h-012f4ba72aeb3f20** 的节点域情形：$\mathcal{N}'$ 经一次节点域加细得到 $\Rightarrow \phi_{\mathcal{N}'}\equiv_U\phi_{\mathcal{N}}$，含其证明所须验证的全部前提（有限性、入口唯一、后继唯一、统一长度界、边域包含与互斥）。

**不在范围内**（按题意不作审阅，但实现同样给出）：代数加细 `AlgebraicRefinement`（`network_refinement.lean:150`）及其构造 `algebraic_refinement_construction.lean`；其余章节结论。附带说明：`refinement_preserves_local_equivalence`（`network_refinement.lean:453`）对两种加细一并证明，节点域情形走 `.node_domain` 分支，未被弱化。

---

## 二、实现的分层结构

实现分四层，相互衔接：

| 层 | 文件 | 内容 |
|---|---|---|
| 构造数据 | `domain_refinement_construction.lean:12` | `NodePartitionData`：分划 + 子域局域算子（正文定义的原始数据） |
| 关系（定义的抽象化） | `network_refinement.lean:68,118` | `OperationalNodeDomainRefinement`（弱化辅助关系）+ 其扩展 `NodeDomainRefinement`（正文关系，加 `edge_domain_eq`） |
| 具体构造 | `domain_refinement_construction.lean:208,235,449,496` | `presentation`（含全部分片的加细网络表示）→ `network := presentation.prune`（删除未被经过的子节点）→ `network_refinement`（证明构造满足正文关系）→ `allowed_network_refinement` |
| 保持定理 | `network_refinement.lean:428,453,480`；`domain_refinement_construction.lean:258` | `path_eval_eq` / `refinement_preserves_local_equivalence` / `refinement_preserves_representation`；构造层面 `network_extensional_eq` |

删除子节点所依据的 #h-ced8c7236326e104 由 `network_presentation.lean:111` 的 `prune` 实现（`prune_eval`:162、`prune_extensional_operator_eq`:168），`FiniteNetworkPresentation`（`network_presentation.lean:13`）恰好保留正文删除引理所设的 (i)–(iii) 义务、唯独不含无冗余（`network_presentation.lean:7` 的文档注释明确此点），与正文"删除前数据满足 (i)–(iii)"的前提一致。

---

## 三、定义逐项对应与依据

下表逐条核对正文条款。正文记号 $D_{\gamma\to\beta}$、$U_\beta$、$U^{in}_\beta$ 对应 `N.edge_domain γ β`、`N.node_dom β`、`N.entry_domain β`（`operator_network.lean:391,367,359`）。

**1. 有限非空分划 $U_\beta=\bigsqcup_{a=1}^{q}U_{\beta,a}$**
→ `part_count`、`part_count_pos`（$q\ge 1$）、`piece`、`piece_nonempty`（每片非空）、`piece_disjoint`、`piece_cover : (⋃ a, piece a) = N.node_dom target`（`network_refinement.lean` 结构字段；构造侧 `NodePartitionData` 同名字段）。
依据：`N.node_dom target = dom (N.node_op target)`（`operator_network.lean:367`），即正文的 $U_\beta=\mathrm{dom}(f_\beta)$，分划对象是**完整节点定义域**而非有效域。关于"非空"的读法：实现取"每片非空"。若按另一种读法（允许空片、省略其子节点），结果网络相同——空片生成的子节点本就会被删除，其边域公式恒为空集，故该读法不失一般性。

**2. 局域算子 $\mathrm{dom}(f_{\beta,a})=U_{\beta,a}$、$f_{\beta,a}\equiv_{U_{\beta,a}}f_\beta$**
→ `local_factor`、`local_domain`、`local_equiv`（关系中，`network_refinement.lean` 字段）；构造侧 `local_op/local_domain/local_eq`（`domain_refinement_construction.lean` 字段）。`LocalEquivalent ϕ ψ U := ∀ x ∈ U, ϕ.func x = ψ.func x`（`decomposition_core.lean:109`）正是正文 @h-a1caa879309ff2e3 的逐点记号。

**3. "$f_{\beta,a}$ 正是 $f_\beta|_{U_{\beta,a}}$（域外取 ⊥）"**
→ 不是假设而是**推导**：`local_op_eq_restrict`（`domain_refinement_construction.lean:31`）证明 `local_op a = restrict_operator (N.node_op target) (P.piece a)`。证明思路：片内由 `local_eq` 得等值；片外若映射非 ⊥ 则属于 `dom = piece`，矛盾，故必为 ⊥。与正文"由前提被迫等于限制算子"的陈述方式一致。

**4. 用子节点 $\beta_a$ 替换 $\beta$**
→ `source : V' → ({β : V // β ≠ target} ⊕ Fin part_count)`、`source_injective`、`old_node_present`（每个旧节点恰一份：存在性由字段、唯一性由单射）、`piece_node_present_iff_reached`（子节点存在 ⟺ 该片被经过）。构造侧 `Label := {v // v ≠ target} ⊕ Fin count`（`domain_refinement_construction.lean:42`）。

**5. 入口输入片 $U^{in}_β\cap U_{\beta,a}$；其他入口片不变**
→ 存储为标签级前提 `entry_projection`，集合级公式被**推导**为定理 `entry_domain_eq`（`network_refinement.lean:283`）：
$$N'.entry\_domain(v)=N.entry\_domain(\pi v)\cap N'.node\_dom(v),$$
其中 $\pi$ 为投影。对子节点代入 $N'.node\_dom=h.piece\,a$ 即得 $U^{in}_β\cap U_{\beta,a}$；对旧节点因 $U^{in}_γ\subseteq U_γ$（网络结构 `entry_mem`）得"不变"。具体子节点的选取由 `entry_mem`（入口必落在该子节点定义域内）与分划互斥唯一确定；`label_eq_of_projection_eq_of_mem`（`network_refinement.lean:249`）用分划互斥证明标签相等。构造侧：`entry := fun x => lift_label (N.entry x) x.val`，`lift_label target x = .inr (piece_at x)`（含 $x$ 的那个片）。

**6. 三类新边域公式与"不关联边不变"**
→ 实现为单一统一交集律（`NodeDomainRefinement.edge_domain_eq`，`network_refinement.lean:118` 结构的末字段；构造侧 `network_edge_domain_eq`，`domain_refinement_construction.lean:346`）：
$$N'.edge\_domain(v,w)=\bigl(N.edge\_domain(\pi v,\pi w)\cap N'.node\_image(v)\bigr)\cap N'.node\_dom(w).$$
**等价性依据**（我已机器验证，见第七节）：由转移图公理 $D_{\gamma\to\beta}\subseteq f_\gamma(U_\gamma)\cap U_\beta$（`operator_network.lean:407,416` 的 `edge_domain_subset_node_image/edge_domain_subset_node_dom`，即正文定义（算子转移图）(iii)），配合 `old_node_op_compat`（旧节点算子不变，故 $N'.node\_image(\gamma)=f_\gamma(U_\gamma)$）与 `piece_node_op_compat + local_domain`（$N'.node\_dom(\beta_a)=U_{\beta,a}$，$N'.node\_image(\beta_a)=f_{\beta,a}(U_{\beta,a})$），逐一特化得正文四条：
- 入边：$(D_{\gamma\to\beta}\cap f_\gamma(U_\gamma))\cap U_{\beta,a}=D_{\gamma\to\beta}\cap U_{\beta,a}$；
- 出边：$(D_{\beta\to\gamma}\cap f_{\beta,a}(U_{\beta,a}))\cap U_\gamma=D_{\beta\to\gamma}\cap f_{\beta,a}(U_{\beta,a})$；
- 自环（含 $a=b$）：恰为双重交集公式 $D_{\beta\to\beta}\cap f_{\beta,a}(U_{\beta,a})\cap U_{\beta,b}$（无需化简，逐字相同）；
- 旧→旧：返回 $D_{\gamma\to\delta}$ 不变；非边（原 $D=\emptyset$）返回 $\emptyset$。
反向蕴含显然：四种节点对型（旧/片）×（旧/片）穷尽，统一律的每个实例就是其中一条正文公式。故**单一律与正文四款在网络上逐字等价**，无内容增减。自环的语义另行由 `self_loop_choice_iff`（`domain_refinement_construction.lean:119`）确认：源子节点输出像 ∩ 目标子节点输入域，正是正文"同时按源子节点的输出像与目标子节点的输入域细分"。

**7. 空入口片与空边域省略**
→ 表象层自动成立：`entry_domain` 是入口函数的纤维（可为空）；边由非空派生域定义（`Edge β γ := (edge_domain β γ).Nonempty`，`operator_network.lean` 内 `OperatorTransitionGraph.Edge`）；删除后子节点仅在"被经过"时存在，故不会有空定义域子节点。

**8. 终止域由出边域补集确定**
→ 表示层恒真：`terminal_domain β := node_image β \ ⋃ γ, edge_domain β γ`（`operator_network.lean:399`）对任何网络按定义成立，无需另设字段。正文证明中使用的集合等式 $T'_{\beta_a}=f_{\beta,a}(U_{\beta,a})\cap T_\beta$（删余前）与"未被替换节点终止域不变"在构造中成立（choice 由 `map_output_choice lift_label ∘ N.choice` 定义，在全像上一致），其**证明相关内容**（新轨迹终止、输出不变）由 `coloured_terminal`（`domain_refinement_construction.lean:184`）承载。删余后终止域只会扩大（输出本要进入的片被删时变为终止），这与 `transition_graph_import.lean` 的 `terminal_domain_subset_prune_redundant_nodes`（"Removing an outgoing edge may enlarge a terminal domain"）一致，不影响任何轨迹。

**9. 删除未被轨迹经过的子节点（#h-ced8c7236326e104）**
→ `network := presentation.prune`。保留判据 `presentation.Reached v := ∃ x : U, v ∈ path_of x`（`network_presentation.lean:106`）；关键定理 `piece_label_reached_iff`（`domain_refinement_construction.lean:310`）证明
$$Reached(\text{子节点 }a)\iff NodePieceReached(N,\beta,piece,a),$$
后者（`network_refinement.lean:51`）即"某输入的轨迹在 $\beta$ 发生处的当前输入落入片 $a$"——正是正文"每当 $\gamma_s=\beta$，由子域分划唯一选出 $a_s$"的逐次着色（`colour_path`，`domain_refinement_construction.lean:168`；`colour_path_get`:272 给出第 $n$ 位着色用的当前输入）。旧节点不被删除：`old_label_reached`（`:296`）由原网络的无冗余公理（`node_reachable`）推出，对应正文"旧节点保持不变"。删除保持求值：`prune_eval`、`prune_path_labels`、`prune_extensional_operator_eq`（`network_presentation.lean:149,162,168`）。

**10. 前提（网络公理 (i)–(iv) 在新网络上成立）**
→ 构造产出的 `prune : FiniteOperatorNetwork` 以类型承载全部公理；正文证明中逐项核对的对应物：
- 节点集有限：`Fintype` 字段（Label 为有限型与 Fin count 之和）；
- 入口唯一：入口为函数；
- 后继唯一：choice 映射 + `terminal_path_unique`（`network_routing.lean`）；出边互斥：`disjoint_edge_domain_of_ne`（`operator_network.lean:426`，由 choice 表示自动成立）；
- 边域包含 $D'\subseteq f'(U')\cap U'$：presentation 的 `choice_next_mem`（`domain_refinement_construction.lean:154`）；
- 统一长度界：`colour_path_length`（长度不变，$r'=r$）+ `depth_bound := N.depth_bound`（正文取 $\ell(\mathcal N)$，任一统一界即可满足公理 (iii)，取原界成立）。

---

## 四、命题 #h-012f4ba72aeb3f20（节点域情形）的对应

**陈述**：正文"若 $\mathcal{N}'$ 由 $\mathcal{N}$ 经一次节点域加细得到，则 $\phi_{\mathcal{N}'}\equiv_U\phi_{\mathcal{N}}$" →

`refinement_preserves_local_equivalence (h : NetworkRefinement N N') : LocalEquivalent N'.extensional_operator N.extensional_operator N.U`（`network_refinement.lean:453`），节点域情形经归纳类型构造子 `.node_domain` 进入；$U$ 非空的默认约定由结构保证（`node_dom_nonempty + node_reachable` 蕴含 $U\neq\emptyset$；空网络无 `target : V`，无从加细，命题空真）。

**证明路径**（正文证明步骤 ↔ Lean 引理）：

| 正文步骤 | Lean 对应 |
|---|---|
| 轨迹逐步替换 $(\beta,y_s)\mapsto(\beta_{a_s},y_s)$ | `colour_path` + `lift_apply`（局部算子等值）+ `node_eval_eq`（`network_refinement.lean:198`） |
| 新轨迹每步合法（$y_{s+1}\in D'_{\gamma'_s\to\gamma'_{s+1}}$） | `choice_next_mem`（presentation）+ `TerminalPathFrom.next`；轨迹提升 `terminal_projection`（`:209`，stop/next 均由 `choice_projection` 搬运） |
| 新轨迹在原终止处终止，输出不变 | `coloured_terminal`（`:184`）、`coloured_eval`（`:197`） |
| 新旧路径标签对应、长度不变 | `path_projection`（`:228`，经 `terminal_path_unique`）、`colour_path_length` |
| 删余后输出不变 | `prune_eval` + `prune_extensional_operator_eq` |
| 结论 $\equiv_U$ | `refinement_preserves_local_equivalence`；构造层面更强：`network_extensional_eq`（`:258`）证得**算子相等**（两侧 $U$ 相同且域外均 ⊥，故相等是 $\equiv_U$ 的自然强化） |

下游用法亦有覆盖：`refinement_preserves_representation`（`:480`，表示保持）；同节的"允许加细规则/不可约代表"由 `RefinementRule/Irreducible/IrreducibleRepresentative`（`:499–522`）镜像，且与正文同样**不**声明 $\mathcal{N}^{irr}$ 的存在性或唯一性。

---

## 五、关系忠实性：为何既无欠约束也无过约束

这是审阅中最值得核查的一点（一处草率实现可能在此出错）。

**完备方向**（正文构造 ⟹ 关系）：`network_refinement`（`domain_refinement_construction.lean:449`）证明由 `NodePartitionData` 按正文程序构造出的网络满足 `NodeDomainRefinement` 全部字段；`allowed_network_refinement`（`:496`）将其嵌入 `NetworkRefinement`。

**可靠方向**（关系 ⟹ 正文构造数据）：关系的字段把 $N'$ 的**呈现数据**（`network_identity.lean` 的 `presentation_data`：$U$、node_op、entry_domain、edge_domain）完全钉死——$U$ 由 `same_input_domain`；node_op 由 `old_node_op_compat/piece_node_op_compat`（旧节点算子不变、子节点为限制算子）；entry_domain 由推导的 `entry_domain_eq`；edge_domain 由 `edge_domain_eq`（上节已证 ⟺ 正文四款）。由此，凡满足关系者与正文构造结果具有相同呈现数据，而 `presentation_data_eq_extensional_operator`（`network_identity.lean`）保证呈现数据决定外延算子。关系中剩下的自由度（choice 在节点像之外的取值、`path_of/depth_bound` 见证）在正文以边域定义网络的表象里本不存在，属见证数据，不影响任何求值行为——是忠实编码而非弱化。

**一个隐藏的相容性要点**：`choice_projection`（约束实际输出处的路由）与 `edge_domain_eq`（约束全像上的路由）联立时，唯一可能产生矛盾的配置是"某实际输出在 $N$ 中被路由入 $\beta$，而其所属片被删除"。实现正确排除了它：`network_choice_projection`（`domain_refinement_construction.lean:387`）用 `terminal_path_suffix_of_next_at_prefix` 证明——产生该输出的轨迹会继续进入 $\beta$，使该片刻即"被经过"，从而不会出现在删除集中。因此关系恰被正文构造的产出所满足：不空、不矛盾、不宽。

---

## 六、核查方法与结果

1. `lake build`：成功（exit 0）。
2. `grep -rn "sorry|admit|native_decide" formal_oet/`：无匹配（仅英文行文误中关键词）。
3. `#print axioms`（`lake env lean` 于 18 条相关定理）：全部仅 `[propext, Classical.choice, Quot.sound]`，无 `sorryAx`。受检定理含：`local_op_eq_restrict`、`network_extensional_eq`、`network_refinement`、`allowed_network_refinement`、`piece_label_reached_iff`、`network_edge_domain_eq`、`network_choice_projection`、`coloured_terminal/eval`、`old_label_reached`、`entry_domain_eq`、`retained_edge_mem`、`eval_projected`、`path_projection`、`path_eval_eq`、`refinement_preserves_local_equivalence`、`refinement_preserves_representation`、`prune_extensional_operator_eq`。

---

## 七、机器验证证据：统一交集律 ⟹ 正文四条边域公式

以下为我在 `$TMPDIR` 中另行编写并通过 `lake env lean` 检查的验证代码（非附件部分；`#print axioms` 四条均无 `sorryAx`）。它把第三节第 6 条的关键等价性落为机器结论：

```lean
import formal_oet.vol_01.ch_05_operator_networks.domain_refinement_construction

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_05_operator_networks
open formal_oet.vol_01.ch_05_operator_networks.FiniteOperatorNetwork

variable {X V V' : Type} {bot : X}
variable {N : FiniteOperatorNetwork X bot V} {N' : FiniteOperatorNetwork X bot V'}
variable (h : NodeDomainRefinement N N')

private theorem img_unfold {W : Type} (M : FiniteOperatorNetwork X bot W) (w : W) :
    M.node_image w = (M.node_op w).func '' dom (M.node_op w) := rfl
private theorem dom_unfold {W : Type} (M : FiniteOperatorNetwork X bot W) (w : W) :
    M.node_dom w = dom (M.node_op w) := rfl
private theorem proj_inl {v : V'} {γ : {β : V // β ≠ h.target}}
    (hv : h.source v = Sum.inl γ) : h.projection v = γ.val := by
  simp [NodeDomainRefinement.projection, node_domain_projection, hv]
private theorem proj_inr {w : V'} {a : Fin h.part_count}
    (hw : h.source w = Sum.inr a) : h.projection w = h.target := by
  simp [NodeDomainRefinement.projection, node_domain_projection, hw]
private theorem proj_inl_raw {v : V'} {γ : {β : V // β ≠ h.target}}
    (hv : h.source v = Sum.inl γ) :
    node_domain_projection h.target h.source v = γ.val := proj_inl h hv
private theorem proj_inr_raw {w : V'} {a : Fin h.part_count}
    (hw : h.source w = Sum.inr a) :
    node_domain_projection h.target h.source w = h.target := proj_inr h hw

/-- 入边：D'_{γ→β_a} = D_{γ→β} ∩ U_{β,a}（正文分款 1）. -/
theorem in_edge_textbook (v w : V') (γ : {β : V // β ≠ h.target}) (a : Fin h.part_count)
    (hv : h.source v = Sum.inl γ) (hw : h.source w = Sum.inr a) :
    N'.edge_domain v w = N.edge_domain γ.val h.target ∩ h.piece a := by
  rw [h.edge_domain_eq v w, proj_inl_raw h hv, proj_inr_raw h hw]
  have himg : N'.node_image v = N.node_image γ.val := by
    rw [img_unfold, img_unfold, h.old_node_op_compat v γ hv]
  have hdom : N'.node_dom w = h.piece a := by
    rw [dom_unfold, h.piece_node_op_compat w a hw, h.local_domain a]
  rw [himg, hdom,
    Set.inter_eq_self_of_subset_left (edge_domain_subset_node_image N γ.val h.target)]

/-- 出边：D'_{β_a→γ} = D_{β→γ} ∩ f_{β,a}(U_{β,a})（正文分款 2）. -/
theorem out_edge_textbook (v w : V') (a : Fin h.part_count)
    (γ : {β : V // β ≠ h.target})
    (hv : h.source v = Sum.inr a) (hw : h.source w = Sum.inl γ) :
    N'.edge_domain v w =
      N.edge_domain h.target γ.val ∩ (h.local_factor a).func '' h.piece a := by
  rw [h.edge_domain_eq v w, proj_inr_raw h hv, proj_inl_raw h hw]
  have himg : N'.node_image v = (h.local_factor a).func '' h.piece a := by
    rw [img_unfold, h.piece_node_op_compat v a hv, h.local_domain a]
  have hdom : N'.node_dom w = N.node_dom γ.val := by
    rw [dom_unfold, dom_unfold, h.old_node_op_compat w γ hw]
  rw [himg, hdom, Set.inter_eq_self_of_subset_left
    (Set.Subset.trans Set.inter_subset_left
      (edge_domain_subset_node_dom (N := N) (β := h.target) (γ := γ.val)))]

/-- 自环：D'_{β_a→β_b} = D_{β→β} ∩ f_{β,a}(U_{β,a}) ∩ U_{β,b}（正文分款 3）. -/
theorem self_loop_textbook (v w : V') (a b : Fin h.part_count)
    (hv : h.source v = Sum.inr a) (hw : h.source w = Sum.inr b) :
    N'.edge_domain v w = N.edge_domain h.target h.target ∩
      (h.local_factor a).func '' h.piece a ∩ h.piece b := by
  rw [h.edge_domain_eq v w, proj_inr_raw h hv, proj_inr_raw h hw]
  have himg : N'.node_image v = (h.local_factor a).func '' h.piece a := by
    rw [img_unfold, h.piece_node_op_compat v a hv, h.local_domain a]
  have hdom : N'.node_dom w = h.piece b := by
    rw [dom_unfold, h.piece_node_op_compat w b hw, h.local_domain b]
  rw [himg, hdom]

/-- 不关联边保持不变（正文分款 4）. -/
theorem unrelated_edge_textbook (v w : V') (γ δ : {β : V // β ≠ h.target})
    (hv : h.source v = Sum.inl γ) (hw : h.source w = Sum.inl δ) :
    N'.edge_domain v w = N.edge_domain γ.val δ.val := by
  rw [h.edge_domain_eq v w, proj_inl_raw h hv, proj_inl_raw h hw]
  have himg : N'.node_image v = N.node_image γ.val := by
    rw [img_unfold, img_unfold, h.old_node_op_compat v γ hv]
  have hdom : N'.node_dom w = N.node_dom δ.val := by
    rw [dom_unfold, dom_unfold, h.old_node_op_compat w δ hw]
  rw [himg, hdom,
    Set.inter_eq_self_of_subset_left (edge_domain_subset_node_image N γ.val δ.val),
    Set.inter_eq_self_of_subset_left
      (edge_domain_subset_node_dom (N := N) (β := γ.val) (γ := δ.val))]
```

四条全部通过：`'in_edge_textbook'/'out_edge_textbook'/'self_loop_textbook'/'unrelated_edge_textbook' depends on axioms: [propext, Classical.choice, Quot.sound]`。反向蕴含（四款 ⟹ 统一律）按节点对型分类即得，无需单独机检。

---

## 八、源码已证明结论 vs. 需要补充的内容

### 已证明（机器核查通过，见第六节）

定义侧：`local_op_eq_restrict`（限制性）、`piece_at_unique`、`lift_mem_dom/lift_apply`、`node_apply_eq_original`、`self_loop_choice_iff`、`choice_next_mem`（加细后路由合法）、`coloured_terminal/coloured_eval`（轨迹对应与输出不变）、`old_label_reached`、`piece_label_reached_iff`（删除判据）、`network_edge_domain_eq`（统一边域律）、`network_choice_projection`（实际输出路由保持）、`network_path_labels/network_path_projection`、`entry_domain_eq`（关系层入口片公式）、`retained_edge_mem`；删除引理 `prune/prune_eval/prune_extensional_operator_eq`；关系实例 `network_refinement/allowed_network_refinement`；保持定理 `path_eval_eq`、`refinement_preserves_local_equivalence`、`refinement_preserves_representation`、`network_extensional_eq`（算子相等）。

### 需要补充/可选强化（均无数学内容损失）

1. **集合级终止域等式的显式陈述**：正文证明中的 $T'_{\beta_a}=f_{\beta,a}(U_{\beta,a})\cap T_\beta$（删余前）与"未被替换节点终止域不变"未列为命名定理；其内容已由派生定义（`terminal_domain` 恒为像减出边并）与 `coloured_terminal` 承载。修复方向：由 `network_edge_domain_eq` 展开 `terminal_domain` 即得，数行推论。
2. **四条边域公式的分款形式**：源码只给统一律；四条特化是短推论（第七节已验证并给出代码）。若追求与正文逐字同形，可将该四个引理并入附件。
3. **关系层的算子相等**：`refinement_preserves_local_equivalence` 只给 $\equiv_U$；由 `same_input_domain` 与域外 ⊥ 约定可一行提升为算子相等（构造层 `network_extensional_eq` 已是相等）。补充仅为修辞一致性。
4. **"有限非空分划"的读法注记**：实现按"每片非空"执行。若按"允许空片、省略空子节点"读，结果网络相同（空片的子节点在删除步消失、其边域公式恒空），属无损选择；如需覆盖，只需在 `NodePartitionData` 中去掉 `nonempty` 字段并在 `piece_at` 处补全情形分支。

### 无需补充的说明

正文命题的结论、前提、证明步骤在两层（关系层 / 构造层）均有对应且已被 Lean 证明；删除步、长度界、有限性、互斥性、包含性等前提以网络类型字段或已证定理形式自动成立；`choice_projection` 与 `edge_domain_eq` 的相容性由 `network_choice_projection` 排除唯一危险配置。未发现任何需要反例支撑的缺陷。

---

## 九、结论

以"正文条款 → 实现条款 → 机器证据"三列核对，节点域加细的定义（含子节点替换、入口片细分、三类边域公式、空片省略、终止域补集、$f_{\beta,a}=f_\beta|_{U_{\beta,a}}$、删余）与命题 #h-012f4ba72aeb3f20 的节点域情形（$\phi_{\mathcal N'}\equiv_U\phi_{\mathcal N}$，含其全部前提验证）被现有 Lean 源码**准确、完整**地形式化；统一交集律与正文四款边域公式的等价性经我独立机器验证成立。可补充项仅为四条显式化推论（第八节），不影响数学正确性或覆盖度。