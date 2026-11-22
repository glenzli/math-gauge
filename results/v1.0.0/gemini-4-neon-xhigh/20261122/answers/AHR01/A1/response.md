### 一、总体判断

所给 Lean 实现**没有完全准确、完整地覆盖**附件数学正文中的“节点域加细”定义（`#h-eddd1f2d0a9d3528`）及该情形下的“网络加细保持外延等价”（`#h-012f4ba72aeb3f20`）。

附件源码实际上将这一数学范围拆分到了两个**彼此独立、尚未桥接**的模块中，二者在准确性和完整性上表现明显不同：

1. **构造性实现**（`formal_oet/vol_01/ch_05_operator_networks/domain_refinement_construction.lean` 与 `network_presentation.lean`）：
   - `NodePartitionData` $\to$ `P.presentation` $\to$ `P.network := P.presentation.prune` 这一套**对象构造本身在数学上是准确的**，忠实实现了节点域有限非空分划、受限子算子、入口分配、四类边域交集、补集终止域以及按 `#h-ced8c7236326e104` 删去不可达子节点与关联边，并已正确证明路径投影保持与外延算子相等（`network_extensional_eq`）。
   - 但其**显式规格验证与结论封装不完整**：除删冗余前的自环路由引理 `self_loop_choice_iff` 外，未显式证明构造结果 `P.network` 满足正文的入口片公式、四类边域交集公式、终止域公式及保留节点集合刻画，也未将其桥接到 `NodeDomainRefinement` 或封装为 `LocalEquivalent`、`ExtensionalEquivalent`、`represents`、`evaluation_depth` 等结论。

2. **关系型定义与命题实现**（`formal_oet/vol_01/ch_05_operator_networks/network_refinement.lean`）：
   - **存在实质性定义缺陷（欠约束 / 过宽）**：`NodeDomainRefinement` 中的字段 `choice_projection` 仅对有效输出像 `(N'.node_op v).func '' N'.node_actual_input_domain v` 施加路由投影约束，对所有**未被输入域 $U$ 到达的节点输出** `N'.node_image v \ (N'.node_op v).func '' N'.node_actual_input_domain v` 完全不加限制。这导致 `NodeDomainRefinement` 放行大量**不符合正文节点域加细定义的伪加细网络**（可在未到达输出上凭空伪造自环/环路、删除或重定向与被加细节点 $\beta$ 完全无关的边、破坏无环性及固定分划下加细结果在重命名意义下的唯一性）。
   - 虽然在该过宽的关系前提下，`refinement_preserves_local_equivalence` 与 `refinement_preserves_representation` 的证明在逻辑上有效，但**作为正文“节点域加细”定义的形式化规格是不准确的**；且 `network_refinement.lean` 与 `domain_refinement_construction.lean` 没有任何相互导入或等价桥接定理，同时未将节点域加细提升到对象空间 `NetworkObject` 层。

---

### 二、逐项对照审阅（正文要求 vs. Lean 实现）

以下按 `source.md` 中 `#h-eddd1f2d0a9d3528`（节点域加细）与 `#h-012f4ba72aeb3f20`（节点域加细情形下保持外延等价）的逐条要件核对。

#### 1. 底网络对象、目标节点 $\beta$ 与非空输入域约定
- **正文要求**：设 $\mathcal N$ 为（有限）算子网络，选取被加细节点 $\beta \in V$；正文约定凡对网络输入域使用 $\equiv_U$ 均默认 $U \neq \emptyset$，空网络 $\bot_{\mathrm{net}}$ 无节点，不存在节点域加细。
- **Lean 实现与依据**：
  - `NodePartitionData (N : FiniteOperatorNetwork X bot V) (target : V)` 与 `NodeDomainRefinement N N'`（含 `target : V`）均作用在一般有限算子网络 `FiniteOperatorNetwork` 上（允许有向闭路与自环，不限于无环 `OperatorNetwork`），与正文一致。
  - 由 `N.node_reachable target : ∃ x : {x // x ∈ N.U}, target ∈ N.path_of x`，只要存在 `target : V`，就自动蕴含 `N.U.Nonempty`，从而自然排除空网络并满足 $U \neq \emptyset$ 约定。
- **评判**：**准确**。

#### 2. 节点定义域有限非空分划与子局域算子
- **正文要求**：将 $U_\beta = \operatorname{dom}(f_\beta)$ 替换为有限非空分划 $U_\beta = \bigsqcup_{a=1}^q U_{\beta,a}$；对每个 $a$ 选取 $f_{\beta,a} \in \mathcal X_{\mathrm{op}}$ 满足 $\operatorname{dom}(f_{\beta,a}) = U_{\beta,a}$ 且 $f_{\beta,a} \equiv_{U_{\beta,a}} f_\beta$；正文指出 $f_{\beta,a}$ 恰好是 $f_\beta|_{U_{\beta,a}}$。
- **Lean 实现与依据**：
  - `domain_refinement_construction.lean` 中 `NodePartitionData` 包含 `count`、`count_pos : 0 < count`、`piece : Fin count → Set X`、`nonempty`、`disjoint`、`cover : (⋃ a, piece a) = N.node_dom target`、`local_op`、`local_domain`、`local_eq`，并证明 `local_op_eq_restrict : P.local_op a = restrict_operator (N.node_op target) (P.piece a)`。
  - `network_refinement.lean` 中 `NodeDomainRefinement` 具有完全对应的字段（`part_count`、`part_count_pos`、`piece`、`piece_nonempty`、`piece_disjoint`、`piece_cover`、`local_factor`、`local_domain`、`local_equiv`）。
  - 注：`0 < count` 实际上可由 `cover` 与 `N.node_dom_nonempty target` 推出，显式保留作字段无害且与 $q \ge 1$ 一致（二者均允许平凡分划 $q=1$）。
- **评判**：**准确且完整**。

#### 3. 节点替换与删去不可达子节点（`@h-ced8c7236326e104`）
- **正文要求**：用子节点 $\beta_a$ 替换 $\beta$，其余节点 $\gamma \neq \beta$ 及其局域算子不变；加细后若产生不被任何输入轨迹经过的子节点，按 `#h-ced8c7236326e104` 删除这些节点及其关联边，保留其余局域算子、转移域和入口片。
- **Lean 实现与依据**：
  - 在 `domain_refinement_construction.lean` 中：删冗余前以 `P.Label := {v : V // v ≠ target} ⊕ Fin P.count` 为节点集，构造 `P.presentation : FiniteNetworkPresentation X bot P.Label`，再令 `P.network := P.presentation.prune`（调用 `network_presentation.lean` 中基于 `Reached v := ∃ x : N.U, v ∈ N.path_of x` 的裁剪构造）。在 `P.network` 中，所有原非目标节点 `.inl γ` 实际上均可被到达而保留，`.inr a` 被保留当且仅当满足 `NodePieceReached N target P.piece a`。但 `domain_refinement_construction.lean` **未显式证明**这两条可达性刻画引理。
  - 在 `network_refinement.lean` 中：`NodeDomainRefinement` 通过 `source : V' → ({β : V // β ≠ target} ⊕ Fin part_count)`、`source_injective`、`old_node_present`、`piece_node_present_iff_reached`（使用 `NodePieceReached`）、`old_node_op_compat` 与 `piece_node_op_compat`，精确刻画了删去冗余节点后节点集与节点算子的同构（至多差重命名）。
    - 核验：`NodePieceReached N target piece a` 定义为存在 $x \in U$ 与 $n < |p_{\mathcal N}(x)|$ 使 $p_{\mathcal N}(x)_n = \beta$ 且第 $n$ 步当前输入 $N.\mathrm{chain\_eval\_nodes}\ ((p_{\mathcal N}(x)).\mathrm{take}\ n)\ x \in U_{\beta,a}$，准确覆盖了自环及多轮回访 $\beta$ 落入不同分块的情形。
- **评判**：**节点集与算子替换的刻画准确**，但构造侧缺少对 `P.presentation.Reached` 的显式刻画定理。

#### 4. 入口输入片规则与空入口片省略
- **正文要求**：若 $\beta$ 为入口节点，则子节点入口输入片为 $U_\beta^{\mathrm{in}} \cap U_{\beta,a}$；其他节点入口输入片不变；空入口片省略。
- **Lean 实现与依据**：
  - 编码约定：`FiniteOperatorNetwork` 以函数 `entry : U → V` 诱导 `entry_domain β := {x | ∃ hx : x ∈ U, entry ⟨x, hx⟩ = β}`，空 `entry_domain` 表示非入口节点（`transition_graph_import.lean` 与 `network_identity.lean` 已确认这一等价编码），与“空入口片省略”一致。
  - 在 `domain_refinement_construction.lean` 中：`P.presentation.entry x := P.lift_label (N.entry x) x.val`，删冗余后 `P.network.entry` 保持同一映射。在数学上对保留节点确有 `P.network.entry_domain ⟨.inl γ, _⟩ = N.entry_domain γ` 与 `P.network.entry_domain ⟨.inr a, _⟩ = N.entry_domain target ∩ P.piece a`（且被删除分块的该交集必为空），但**源码未将这些入口片等式写成定理证明**。
  - 在 `network_refinement.lean` 中：`NodeDomainRefinement.entry_projection` 要求 `node_domain_projection target source (N'.entry x) = N.entry (transport_network_input same_input_domain x)`。结合 `N'.entry_mem`、`piece_disjoint`、`source_injective` 与 `local_domain`，可以严格推出：
    - 若 `source v = .inl γ`，则 `N'.entry_domain v = N.entry_domain γ.val`；
    - 若 `source v = .inr a`，则 `N'.entry_domain v = N.entry_domain target ∩ piece a`。
    因此 `entry_projection` 作为入口条件在逻辑上是**充分且必要（准确）的**，但源码同样**未显式证出上述入口片公式**。
- **评判**：**逻辑上准确，但显式入口片刻画定理缺失**。

#### 5. 四类边域交集公式、无关边保持、空边域省略与终止域补集规则（**核心缺陷**）
- **正文要求**：
  - 入边（$\gamma \neq \beta$）：$D'_{\gamma\to\beta_a} = D_{\gamma\to\beta} \cap U_{\beta,a}$；
  - 出边（$\gamma \neq \beta$）：$D'_{\beta_a\to\gamma} = D_{\beta\to\gamma} \cap f_{\beta,a}(U_{\beta,a})$；
  - 自环：$D'_{\beta_a\to\beta_b} = D_{\beta\to\beta} \cap f_{\beta,a}(U_{\beta,a}) \cap U_{\beta,b}$；
  - 无关边（$\gamma,\delta \neq \beta$）：$D'_{\gamma\to\delta} = D_{\gamma\to\delta}$；
  - 空边域省略（在 Lean 中由 `Edge β γ := (edge_domain β γ).Nonempty` 准确编码）；
  - 终止域由出边域在节点输出像中的补集确定（删冗余前 $T'_{\beta_a} = f_{\beta,a}(U_{\beta,a}) \cap T_\beta$，$T'_\gamma = T_\gamma$）；
  - 按 `#h-ced8c7236326e104` 删除不可达子节点 $\beta_c$ 及其关联边后：**任意两个保留节点 $v,w \in V'$ 之间的转移域完全不变**，统一满足
    $$D'_{v\to w} = D_{\operatorname{proj}(v)\to\operatorname{proj}(w)} \cap f'_v(U'_v) \cap U'_w,$$
    而被删除入边所对应的输出转入保留源节点的终止域 $T'_v = f'_v(U'_v) \setminus \bigcup_{w\in V'} D'_{v\to w}$。

- **构造侧（`domain_refinement_construction.lean` + `network_presentation.lean`）**：
  - `P.choice v z := map_output_choice (fun w => P.lift_label w z) (N.choice (P.projection v) z)` 与 `prune_choice` 联合之后，对 `P.network` 的任意保留节点 $v,w$，上述统一公式及四类边域公式、终止域补集公式在数学上**全部精确成立**。
  - **不足**：源码只证明了删冗余前自环情形下的 `self_loop_choice_iff`（且仅表述为 `P.choice (.inr a) z = .next (.inr b)` 在 `hz : z ∈ (P.local_op a).func '' P.piece a` 下的充要条件），**未对 `P.network.edge_domain` 证明四类边域等式，也未证明删冗余前后的终止域公式**。

- **关系侧（`network_refinement.lean` 中的 `NodeDomainRefinement`）**：
  - **实质性缺陷**：`NodeDomainRefinement` 的文档注释声称 *"Local entry and successor laws for the domain intersections in the text."*，但其唯一路由字段是：
    ```lean
    -- Pruning may change choices at outputs never reached from the source.
    choice_projection :
      ∀ (v : V') (z : X), z ∈ (N'.node_op v).func '' N'.node_actual_input_domain v →
        map_output_choice (node_domain_projection target source) (N'.choice v z) =
          N.choice (node_domain_projection target source v) z
    ```
  - 这一字段**只约束有效输出像** `(N'.node_op v).func '' N'.node_actual_input_domain v` 上的路由，对集合
    $$N'.\mathrm{node\_image}\ v \setminus (N'.\mathrm{node\_op}\ v).\mathrm{func}\ ''\ N'.\mathrm{node\_actual\_input\_domain}\ v$$
    中的任何点 $z$ 均无约束！
  - 这与正文体系本身相冲突：正文严格区分原始网络 $\mathcal N$ 与有效约化 $\mathcal N^{\mathrm{eff}}$（参见 `#h-adb38f8458662a70`、习题 `#h-171f4e850e8f1c36` 以及 `network_identity.lean` 中的 `PresentationData` 和 `network_extensional_space.lean` 中的 `NetworkObject`，后者均保留未被 $U$ 到达的边域）。节点域加细是在全节点域 $U_\beta$ 与全节点输出像上定义的操作，删去冗余节点也只删去指向被删子节点的边，绝不允许任意改动保留节点之间的未到达边域。
  - （对比可见：同一文件中 `NodeDomainRefinement` 对节点算子要求全定义域相等 `N'.node_op β' = N.node_op β.val` 与 `dom = piece a`，且同文件的 `AlgebraicRefinement` 在全输出像 `z ∈ N'.node_image v` 上约束路由；唯独 `NodeDomainRefinement.choice_projection` 为规避删冗余引起的局部变化而把范围过度缩小到了 `N'.node_actual_input_domain`。）

#### 6. 命题 `#h-012f4ba72aeb3f20`（节点域加细保持外延等价）
- **正文要求**：若 $\mathcal N'$ 由 $\mathcal N$ 经一次节点域加细（含删去冗余节点）得到，则 $\phi_{\mathcal N'} \equiv_U \phi_{\mathcal N}$（因二者在 $U$ 外均取 $\bot$，等价于 $\phi_{\mathcal N'} = \phi_{\mathcal N}$ 或 $\mathcal N' \sim_{\mathrm{op}} \mathcal N$）；证明同时给出了路径重着色对应、轨迹长度不变（$r' = r \le \ell(\mathcal N)$）及新数据经删冗余后确为有限算子网络。
- **Lean 实现与依据**：
  - **构造侧（`domain_refinement_construction.lean`）**：已证 `P.network` 是合法 `FiniteOperatorNetwork`，并已证 `network_path_labels`、`network_path_projection` 与 `network_extensional_eq : P.network.extensional_operator = N.extensional_operator`。由于 `P.network.U = N.U` 按定义成立，外延局部等价 $\phi_{\mathcal N'} \equiv_U \phi_{\mathcal N}$、`ExtensionalEquivalent P.network N`、`represents` 保持及 `evaluation_depth` 不变均为直接推论，但源码未显式封装这些结论。
  - **关系侧（`network_refinement.lean`）**：已证 `NodeDomainRefinement.node_eval_eq`、`terminal_projection`、`path_projection`、`eval_projected`、`NetworkRefinement.path_eval_eq`、`refinement_preserves_local_equivalence`（`LocalEquivalent N'.extensional_operator N.extensional_operator N.U`）和 `refinement_preserves_representation`（`N.represents φ → NetworkRefinement N N' → N'.represents φ`）。
  - **存在的结构性缺口**：
    1. **存在性/构造与关系脱节**：`network_refinement.lean` 预设 `N'` 已经是合法 `FiniteOperatorNetwork`，自身不证明从分划构造出合法有限网络；而 `domain_refinement_construction.lean` 虽完成了构造，却**没有任何定理证明 `NodeDomainRefinement N P.network`**，也没有证明满足 `NodeDomainRefinement N N'` 的网络在重命名意义下等于 `P.network`（实际上在修复前该反方向是假的）。
    2. **结论封装不完全统一**：`network_refinement.lean` 导入了 `effective_equivalence.lean`（其中定义了 `FiniteOperatorNetwork.ExtensionalEquivalent`），但未显式给出 `ExtensionalEquivalent N' N`、`N'.extensional_operator = N.extensional_operator` 与 `N'.evaluation_depth = N.evaluation_depth` 的定理；此外，文件末尾的 `IrreducibleRepresentative` 定义在对象空间 `NetworkObject X bot` 的 `RefinementRule` 上，但节点域加细本身没有经 `NonemptyOperatorNetwork.encode` 提升至 `NetworkObject` 层。

---

### 三、核心缺陷的数学影响与可复核反例

`NodeDomainRefinement.choice_projection` 的欠约束虽然**不影响** `refinement_preserves_local_equivalence` 的真值（因为外延求值只查询有效输出像上的路由），但它使得 `NodeDomainRefinement` **严重偏离正文定义**，产生以下具体数学后果：

1. 违反正文四类边域交集公式与“不与 $\beta$ 关联的边保持不变”的规定；
2. 违反终止域补集公式；
3. **破坏无环性保持**：原网络是无环网络（甚至无边），按 `NodeDomainRefinement` 却可“加细”出含自环或有向闭路的循环网络；
4. **破坏加细结果的唯一性（模节点重命名）**：固定 $\mathcal N$、目标节点 $\beta$ 与分划 $\{U_{\beta,a}\}$ 后，正文唯一决定加细后的网络数据（`PresentationData` / `NetworkObject` 至多差编号），但 `NodeDomainRefinement` 允许无数个彼此非同构的 `N'` 均满足该关系。

下面给出三个完全可逐字段手算复核的有限反例。

#### 反例 1：在未到达输出上伪造自环（无节点删除，破坏自环公式、终止域、无环性与唯一性）

- **底空间与输入域**：取 $X = \mathrm{Fin}\ 4 = \{0,1,2,3\}$，吸收元 $\bot = 0$，输入域 $U = \{1,2\}$（不含 $0$ 且非空）。
- **原网络 $N : \mathrm{FiniteOperatorNetwork}\ (\mathrm{Fin}\ 4)\ 0\ \mathrm{Unit}$**：
  - 节点集 $V = \{\beta\}$（即 `Unit`），局部算子 $f_\beta$ 定义为 $f_\beta(0)=0$，$f_\beta(x)=x$（$x \in \{1,2,3\}$），故 $U_\beta = \operatorname{dom}(f_\beta) = \{1,2,3\}$ 非空。
  - 入口映射：`N.entry ⟨1,_⟩ = β`，`N.entry ⟨2,_⟩ = β`，均满足 `entry_mem`。
  - 路由：`∀ z, N.choice β z = OutputChoice.stop`。故 `choice_next_mem` 平凡成立，$D_{\beta\to\beta} = \emptyset$（**0 条边，无环**），$T_\beta = \{1,2,3\}$。
  - 路径与深度：`depth_bound = 1`，`path_of 1 = path_of 2 = [β]`，均终止于 `stop`，长度 $\le 1$，节点 $\beta$ 被到达。故 $N$ 是合法 `FiniteOperatorNetwork`。
- **非平凡二分划（不触发任何删冗余）**：
  - `part_count = 2`，`piece 0 = {1, 3}`，`piece 1 = {2}`（均非空、互斥、并集为 $\{1,2,3\} = U_\beta$）。
  - `local_factor 0 = restrict_operator f_β {1,3}`，`local_factor 1 = restrict_operator f_β {2}`。
  - 可达性：$1 \in U$ 使 `NodePieceReached N β piece 0` 成立；$2 \in U$ 使 `NodePieceReached N β piece 1` 成立。**两个子节点均保留，无节点被删**。
  - **正文定义的唯一正确加细结果**（亦即 `P.network`）应满足 $D'_{\beta_a\to\beta_b} = \emptyset$（$\forall a,b \in \{0,1\}$）且 $T'_{\beta_0} = \{1,3\}$。
- **反例网络 $N' : \mathrm{FiniteOperatorNetwork}\ (\mathrm{Fin}\ 4)\ 0\ (\mathrm{Fin}\ 2)$**：
  - $U' = \{1,2\}$，`node_op 0 = local_factor 0`（域 $\{1,3\}$），`node_op 1 = local_factor 1`（域 $\{2\}$）。
  - 入口：`N'.entry ⟨1,_⟩ = 0`，`N'.entry ⟨2,_⟩ = 1`。
  - 路由：令 `N'.choice 0 3 = OutputChoice.next 0`，其余一切 `(v, z)` 均取 `OutputChoice.stop`。
  - **核验 $N'$ 是合法 `FiniteOperatorNetwork`**：
    - `choice_next_mem`：唯一取 `.next` 的情形是 `v = 0, γ = 0, (node_op 0).func y = 3`（仅当 `y = 3 ∈ {1,3}`），输出 $3 \in \{1,3\} = \operatorname{dom}(\mathrm{node\_op}\ 0)$，成立；
    - `path_of 1 = [0]`（因 `choice 0 1 = .stop`），`path_of 2 = [1]`（因 `choice 1 2 = .stop`），长度均为 $1 \le 1$，且 `0, 1` 均被到达。
  - **核验 `NodeDomainRefinement N N'` 全部字段成立**：
    - `source := Sum.inr : Fin 2 → ({v : Unit // v ≠ β} ⊕ Fin 2)` 显然单射；`old_node_present` 与 `old_node_op_compat` 空真；`piece_node_present_iff_reached` 两端恒真；`piece_node_op_compat`、`same_input_domain`、`entry_projection` 均直接成立。
    - `choice_projection`：实际输入域 `N'.node_actual_input_domain 0 = {1}`，其输出像为 `{1}`，在 $z=1$ 处 `N'.choice 0 1 = .stop = N.choice β 1`；`N'.node_actual_input_domain 1 = {2}`，输出像为 `{2}`，在 $z=2$ 处 `N'.choice 1 2 = .stop = N.choice β 2`。**未到达输出 $z=3$ 不在有效输出像中，完全逃逸检查！**
- **结论**：`NodeDomainRefinement N N'` 成立，但 $N'$ 凭空多出自环 $D'_{\beta_0\to\beta_0} = \{3\} \neq \emptyset$，终止域缩为 $T'_{\beta_0} = \{1\} \neq \{1,3\}$，且原无环网络 $N$ 被“加细”成了含自环的循环网络，与 `P.network` 绝非节点重命名等价。

#### 反例 2：删除或重定向与 $\beta$ 完全无关的边（违背“不与 $\beta$ 关联的边保持不变”）

- 取 $X = \mathrm{Fin}\ 5 = \{0,1,2,3,4\}$，$\bot = 0$，$U = \{1,2,4\}$，$V = \{\beta, \gamma\}$。
- 在 $N$ 中令 $f_\beta = \mathrm{id}|_{\{1,3,4\}}$、$f_\gamma = \mathrm{id}|_{\{2,3\}}$，$U_\beta^{\mathrm{in}} = \{1,4\}$、$U_\gamma^{\mathrm{in}} = \{2\}$；设 `N.choice γ 3 = OutputChoice.next γ`（存在一条与 $\beta$ 无关的未到达自环 $D_{\gamma\to\gamma} = \{3\}$），其余均为 `.stop`。各路径为 $1,4 \mapsto [\beta]$、$2 \mapsto [\gamma]$，两节点均可达。
- 对 $\beta$ 做非平凡二分划 $U_{\beta,0} = \{1,3\}$、$U_{\beta,1} = \{4\}$（两块均被到达，无删冗余）。按正文，不与 $\beta$ 关联的边必须保持 $D'_{\gamma\to\gamma} = \{3\}$。
- 构造 $N'$ 与正文加细结果完全相同，仅把 `N'.choice γ 3` 改为：
  - **变体 A**：`OutputChoice.stop`（擅自删除无关边 $D_{\gamma\to\gamma}$）；或
  - **变体 B**：`OutputChoice.next β₀`（因 $3 \in U_{\beta,0}$，满足 `choice_next_mem`，擅自将无关边 $\gamma\to\gamma$ 重定向为 $\gamma\to\beta_0$）。
- 因 `N'.node_actual_input_domain γ = {2}`，有效输出像为 `{2}` 不含 $3$，两种变体均满足 `NodeDomainRefinement N N'` 的全部字段。

#### 反例 3：为何不能简单把 `choice_projection` 的域扩大到全 `N'.node_image v`（定位原缺陷成因）

原注释 `-- Pruning may change choices at outputs never reached from the source.` 指向的现象本身是真实的：
- 取 $X = \mathrm{Fin}\ 4$，$\bot = 0$，$U = \{1\}$，$V = \{\beta, \gamma\}$，$f_\gamma = \mathrm{id}|_{\{1,2,3\}}$，$f_\beta = \mathrm{id}|_{\{1,3\}}$，$U_\gamma^{\mathrm{in}} = \{1\}$，`N.choice γ 1 = N.choice γ 3 = .next β`，其余 `.stop`。唯一路径为 $1 \mapsto [\gamma, \beta]$。
- 对 $\beta$ 取分划 $U_{\beta,0} = \{1\}$、$U_{\beta,1} = \{3\}$。由于 $3$ 未被到达，$\beta_1$ 及其入边 $\gamma\to\beta_1$ 按 `#h-ced8c7236326e104` 被删除。
- 在删冗余后的正确网络 `P.network` 中，对保留节点 $\gamma$ 与输出 $z = 3 \in N'.\mathrm{node\_image}\ \gamma$，有 `N'.choice γ 3 = .stop`（因为指向被删节点 $\beta_1$ 的边已被删），而 `N.choice γ 3 = .next β`；故 `map_output_choice proj (N'.choice γ 3) = .stop ≠ .next β = N.choice γ 3`。
- 这说明原代码**为了躲开被删除分块处的 `.next β_c ↦ .stop` 变化，直接把整个 `choice_projection` 退缩到了 `node_actual_input_domain`**，结果连所有保留节点之间的未到达边域也一并放弃了约束。

---

### 四、修复方向与严格等价性论证

#### 修复方向 1：用精确边域交集等式替换 `NodeDomainRefinement.choice_projection`

将 `NodeDomainRefinement` 中的 `choice_projection` 替换为单条精确条件：

```lean
edge_domain_compat :
  ∀ (v w : V'),
    N'.edge_domain v w =
      N.edge_domain (node_domain_projection target source v)
        (node_domain_projection target source w) ∩
      N'.node_image v ∩ N'.node_dom w
```

**可复核论证（充分性、必要性及与正文完全等价）**：

1. **统一覆盖正文四类边域公式及删冗余后的终止域**：
   对任意两个保留节点 $v,w \in V'$，由 `N.edge_domain_subset_node_image` 与 `N.edge_domain_subset_node_dom` 分四种情形展开 `edge_domain_compat`：
   - `source v = .inl γ, source w = .inl δ`：$D'_{v\to w} = D_{\gamma\to\delta} \cap f_\gamma(U_\gamma) \cap U_\delta = D_{\gamma\to\delta}$（无关边不变）；
   - `source v = .inl γ, source w = .inr b`：$D'_{v\to w} = D_{\gamma\to\beta} \cap f_\gamma(U_\gamma) \cap U_{\beta,b} = D_{\gamma\to\beta} \cap U_{\beta,b}$（入边公式）；
   - `source v = .inr a, source w = .inl δ`：$D'_{v\to w} = D_{\beta\to\delta} \cap f_{\beta,a}(U_{\beta,a}) \cap U_\delta = D_{\beta\to\delta} \cap f_{\beta,a}(U_{\beta,a})$（出边公式）；
   - `source v = .inr a, source w = .inr b`：$D'_{v\to w} = D_{\beta\to\beta} \cap f_{\beta,a}(U_{\beta,a}) \cap U_{\beta,b}$（自环公式）。
   - 同时，由 `FiniteOperatorNetwork.terminal_domain` 的补集定义与 `edge_domain` 对全输出像上 `choice` 的唯一决定性（`network_identity.lean` 中的 `presentation_data_eq_choice`），此条件自动等价于全输出像 $z \in N'.\mathrm{node\_image}\ v$ 上的精确路由规则：
     - 若 `N.choice (proj v) z = .stop`，则 `N'.choice v z = .stop`；
     - 若 `N.choice (proj v) z = .next u`（$u \neq \beta$），则 `N'.choice v z = .next w`（对应唯一 `source w = .inl u`）；
     - 若 `N.choice (proj v) z = .next β`，令 $a$ 为满足 $z \in U_{\beta,a}$ 的唯一分块（由 $z \in D_{\operatorname{proj}(v)\to\beta} \subseteq U_\beta = \bigsqcup_a U_{\beta,a}$ 保证存在唯一），若 $a$ 保留（存在 `w` 使 `source w = .inr a`）则 `N'.choice v z = .next w`，若 $a$ 不可达被删则 `N'.choice v z = .stop`（恰好兼容反例 3，同时排除反例 1 与反例 2！）。

2. **与构造性实现 `P.network` 严格双向等价（模节点重命名）**：
   - **构造 $\Rightarrow$ 关系**：对任意 `P : NodePartitionData N target`，令 `source := Subtype.val : {u : P.Label // P.presentation.Reached u} → P.Label`。可证：
     - 每个 `.inl γ` 满足 `P.presentation.Reached (.inl γ)`（由 `N.node_reachable γ` 与 `P.colour_path_projection`）；
     - `.inr a` 满足 `P.presentation.Reached (.inr a) ↔ NodePieceReached N target P.piece a`（由 `colour_path` 与 `piece_at_unique`）；
     - 对任意保留节点 `v, w`，因 `w.property : Reached w.val`，有 `prune_choice Reached P.choice v z = .next w ↔ P.choice v.val z = .next w.val`，进而在 `z ∈ P.network.node_image v` 下恰等价于 `z ∈ N.edge_domain (proj v) (proj w) ∧ z ∈ P.network.node_dom w`。
     从而 `P.network` 满足修复后的 `NodeDomainRefinement N P.network`。
   - **关系 $\Rightarrow$ 唯一性（同构于 `P.network`）**：给定满足修复后 `NodeDomainRefinement N N'` 的任意 `N'`，由 `source_injective`、`old_node_present`、`piece_node_present_iff_reached` 可将 `source` 限制为全局双射 $e : V' \simeq \{u : P.\mathrm{Label} \mid P.\mathrm{presentation.Reached}\ u\}$。逐项核对 `PresentationData` 的四个分量（`U`、`node_op`、`entry_domain`、`edge_domain`），可证：
     $$(N'.\mathrm{relabel}\ e).\mathrm{presentation\_data} = P.\mathrm{network.presentation\_data}.$$
     结合 `network_identity.lean` 中的 `presentation_data_eq_path_of`、`presentation_data_eq_extensional_operator`，立即得到路径投影相等、求值深度相等与外延算子相等，且不再存在任何反例 1、2 那样的伪加细，并且自动保证无环网络在节点域加细下仍为无环网络（以 `N.rank ∘ h.projection` 为拓扑秩）。

3. **保持原有直接证明路径**：若希望不依赖 `P.network` 直接在 `network_refinement.lean` 内证明 `path_projection`，只需沿 `N.path_terminal (transport x)` 做归纳：在每步转移中，若原网络跳向 $u \neq \beta$ 则由 `old_node_present` 取 $w \in V'$；若原网络跳向 $\beta$ 且当前输出 $y' \in U_{\beta,a}$，因该步处于某真实入口轨迹上，`NodePieceReached N target piece a` 成立，故由 `piece_node_present_iff_reached` 取 $w \in V'$；再由 `edge_domain_compat` 得出 `N'.choice v y' = .next w`，最后用 `terminal_path_unique` 得出 `(N'.path_of x).map h.projection = N.path_of (transport x)`。

#### 修复方向 2：补齐构造侧显式规格校验定理与双模块桥接
- 在 `domain_refinement_construction.lean` 中，为 `P.network` 显式证明：
  1. 保留节点刻画：`P.presentation.Reached (.inl γ)` 恒真、`P.presentation.Reached (.inr a) ↔ NodePieceReached N target P.piece a`；
  2. 入口片公式：`P.network.entry_domain` 在非目标节点与保留分块上的精确表达式；
  3. 删冗余后 `P.network.edge_domain` 的统一公式及四类特化公式（无关边、入边、出边、自环）；
  4. 删冗余前（$T'_{\beta_a} = f_{\beta,a}(U_{\beta,a}) \cap T_\beta$，$T'_\gamma = T_\gamma$）与删冗余后的终止域公式；
  5. 构造到关系的桥接定理：`NodeDomainRefinement N P.network`（连同修复后的唯一性定理）。

#### 修复方向 3：补齐外延等价结论包装与 `NetworkObject` 层衔接
- 在 `network_refinement.lean` 中，由 `h.same_input_domain` 与 `refinement_preserves_local_equivalence` 补证：
  - `FiniteOperatorNetwork.ExtensionalEquivalent N' N`（利用已导入的 `effective_equivalence.lean` 定义）；
  - `N'.extensional_operator = N.extensional_operator`；
  - `N'.evaluation_depth = N.evaluation_depth`（由 `path_projection` 推出长度不变）。
- 在 `domain_refinement_construction.lean` 中，由 `P.network_extensional_eq` 补证 `LocalEquivalent`、`FiniteOperatorNetwork.ExtensionalEquivalent`、`represents` 保持及 `P.network.evaluation_depth = N.evaluation_depth`。
- 如需使节点域加细真正接入 `network_refinement.lean` 末尾定义在 `NetworkObject X bot` 上的 `RefinementRule` / `IrreducibleRepresentative`，可借由 `N.node_reachable target` 自动得到的 `N.U.Nonempty` 与 `NonemptyOperatorNetwork.encode`，定义对象空间上的节点域加细关系并证明其保持 `NetworkObject.ExtensionalEquivalent`。

---

### 五、源码已证明结论 vs. 需要修复/补充内容的清晰对照

#### A. 源码已证明的结论（在审阅范围内）

| 所属文件 | 已证明定理 / 构造 | 实际覆盖的数学内容 |
| :--- | :--- | :--- |
| `domain_refinement_construction.lean` | `NodePartitionData.local_op_eq_restrict` | 证明子算子满足 $\operatorname{dom}(f_{\beta,a})=U_{\beta,a}$ 与 $f_{\beta,a}\equiv_{U_{\beta,a}} f_\beta$ 时必有 $f_{\beta,a} = f_\beta|_{U_{\beta,a}}$ |
| `domain_refinement_construction.lean` | `mem_piece_at`, `piece_at_unique`, `projection_lift`, `lift_mem_dom`, `lift_apply`, `node_domain_subset_original`, `node_apply_eq_original` | 分块定位函数与标签提升/投影的基本相容性 |
| `domain_refinement_construction.lean` | `self_loop_choice_iff` | **删冗余前**自环路由满足 `P.choice (.inr a) z = .next (.inr b) ↔ z ∈ N.edge_domain target target ∧ z ∈ P.piece b`（在 $z \in f_{\beta,a}(U_{\beta,a})$ 下） |
| `domain_refinement_construction.lean` | `choice_next_mem`, `colour_path_length`, `colour_path_projection`, `coloured_terminal`, `coloured_eval`, `presentation` | 删冗余前 `FiniteNetworkPresentation` 的合法性、路径重着色终止性、长度不变及求值输出不变 |
| `network_presentation.lean` | `FiniteNetworkPresentation.prune`, `prune_path_labels`, `prune_eval`, `prune_extensional_operator_eq` | 引理 `#h-ced8c7236326e104`：删去不可达节点及关联边后得到合法 `FiniteOperatorNetwork`，且保持路径标签、求值与外延算子 |
| `domain_refinement_construction.lean` | `network`, `network_path_labels`, `network_path_projection`, `network_extensional_eq` | 删去不可达子节点后的实际加细网络 `P.network` 满足路径投影等于原路径，且 `P.network.extensional_operator = N.extensional_operator` |
| `network_refinement.lean` | `NodeDomainRefinement.node_eval_eq`, `terminal_projection`, `path_projection`, `eval_projected` | 在当前 `NodeDomainRefinement N N'` 前提下，证明节点求值一致、终止路径投影到原路径、路径求值一致 |
| `network_refinement.lean` | `NetworkRefinement.path_eval_eq`, `refinement_preserves_local_equivalence`, `refinement_preserves_representation` | 在 `NetworkRefinement.node_domain` 前提下，证明 `LocalEquivalent N'.extensional_operator N.extensional_operator N.U` 及保持 `N.represents φ` |

#### B. 需要修复的实质性缺陷

1. **修正 `NodeDomainRefinement.choice_projection`**（`network_refinement.lean`）：当前仅约束 `N'.node_actual_input_domain v` 的像集，放行未到达输出上的伪造/删改/重定向边（反例 1、2）。需替换为全节点像集上的精确边域公式 `edge_domain_compat`（或与之等价的按分块是否保留分情况的 `N'.choice` 规则），并据此重写 `terminal_projection` / `path_projection` 证明。

#### C. 源码未证明、需要补充的内容

1. **构造侧显式定义校验定理**（`domain_refinement_construction.lean`）：
   - 保留节点刻画（非目标节点全保留；分块节点保留当且仅当 `NodePieceReached`）；
   - `P.network.entry_domain` 的入口片分划公式；
   - `P.network.edge_domain` 在删冗余后的四类边域交集公式（无关边、入边、出边、自环）；
   - 删冗余前后的终止域公式（含 $T'_{\beta_a} = f_{\beta,a}(U_{\beta,a}) \cap T_\beta$）。
2. **构造实现与关系定义的双向桥接**：
   - 证明 `NodeDomainRefinement N P.network`；
   - 在修复 `NodeDomainRefinement` 后，证明任一满足 `NodeDomainRefinement N N'` 的网络经唯一节点双射重命名后与 `P.network` 具有相同的 `PresentationData`（确证关系定义既不欠约束也不过约束）。
3. **结论封装与对象空间层衔接**（属补全性封装）：
   - 在 `network_refinement.lean` 中由现有结论补出 `FiniteOperatorNetwork.ExtensionalEquivalent N' N`、`N'.extensional_operator = N.extensional_operator` 与 `N'.evaluation_depth = N.evaluation_depth`；
   - 在 `domain_refinement_construction.lean` 中由 `network_extensional_eq` 与 `network_path_projection` 补出 `LocalEquivalent`、`ExtensionalEquivalent`、`represents` 保持及 `evaluation_depth` 不变；
   - 如需与 `IrreducibleRepresentative` 所用的 `RefinementRule (NetworkObject X bot)` 对接，补充经 `NonemptyOperatorNetwork.encode` 提升到 `NetworkObject` 层的节点域加细关系及其保持 `NetworkObject.ExtensionalEquivalent` 的定理。