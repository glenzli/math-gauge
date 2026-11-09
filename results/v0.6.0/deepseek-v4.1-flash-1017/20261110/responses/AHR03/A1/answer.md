## 结论

就本题限定的范围——正文中的**节点域加细**及命题  
\[
\mathcal N'\text{ 由 }\mathcal N\text{ 经一次节点域加细得到}
\Longrightarrow
\phi_{\mathcal N'}\equiv_U\phi_{\mathcal N}
\]
的 Lean 实现——我未发现会改变数学结论的错误或反例。核心定义与证明是准确且完整的；`NodePartitionData` 的构造还给出了比“局部等价”更强的结论：
\[
\phi_{\mathcal N'}=\phi_{\mathcal N}.
\]

但需要区分三点：

1. 真正对应正文节点域加细的是 `NodeDomainRefinement`；辅助的 `OperationalNodeDomainRefinement` 有意较弱，只约束实际发生路径，**不应单独当作正文定义的完整形式化**。
2. 源码已证明节点域加细可构造、所得网络保持外延等价，并证明了路径投影、入口片、边域等关键性质。
3. 正文中“允许加细规则族”“不可约代表存在性”、L/K/N 受限数据的比较条件等，不属于本命题证明所需范围；这些没有在本题范围内完整形式化。

---

## 一、定义与 Lean 结构的逐项对应

### 1. 被加细节点与有限非空分划

正文要求将
\[
U_\beta=\operatorname{dom}(f_\beta)
\]
替换为有限非空分划
\[
U_\beta=\bigsqcup_{a=1}^q U_{\beta,a}.
\]

Lean 的 `OperationalNodeDomainRefinement` 中有：

- `target : V`：被加细节点；
- `part_count : Nat`、`part_count_pos : 0 < part_count`；
- `piece : Fin part_count → Set X`；
- `piece_nonempty`；
- `piece_disjoint`；
- `piece_cover : (⋃ a, piece a) = N.node_dom target`。

`N.node_dom target` 正是 `dom (N.node_op target)`，因此这准确对应
\[
\bigsqcup_a U_{\beta,a}=\operatorname{dom}(f_\beta).
\]

### 2. 子节点局域算子

正文要求
\[
\operatorname{dom}(f_{\beta,a})=U_{\beta,a},
\qquad
f_{\beta,a}\equiv_{U_{\beta,a}}f_\beta.
\]

Lean 中有：

- `local_factor : Fin part_count → Operator X bot`；
- `local_domain : dom (local_factor a) = piece a`；
- `local_equiv : LocalEquivalent (local_factor a) (N.node_op target) (piece a)`。

这里 `local_domain + local_equiv` 已经等价于“子节点算子等于原算子在子域上的限制”。原因是 `Operator` 在定义域外取 `bot`，故在 `piece a` 上局部相等且定义域相同，即决定整个算子。构造文件中还直接证明了
`NodePartitionData.local_op_eq_restrict`：
\[
`local_op a = restrict_operator (N.node_op target) (piece a)`.
\]

### 3. 子节点替换与删除不可达子节点

正文要求用子节点 \(\beta_a\) 替换 \(\beta\)，并在最后删除不被任何输入轨迹经过的子节点。

Lean 中：

- `source : V' → ({β : V // β ≠ target} ⊕ Fin part_count)`；
- `source_injective`；
- `old_node_present`：每个原非目标节点都有对应新节点；
- `piece_node_present_iff_reached`：第 \(a\) 个分块对应的子节点存在，当且仅当该分块被实际输入轨迹到达；
- `old_node_op_compat`、`piece_node_op_compat`：节点算子分别保持。

其中
```lean
NodePieceReached N target piece a
```
的定义正是：存在输入 \(x\in N.U\)、存在原路径中节点 `target` 的一次出现，使该次出现之前的当前输入落在 `piece a` 中。这与正文“被某个输入的终止轨迹经过”一致。

因此源码把“先造全部子节点，再按正文删去不可达子节点”的结果编码为后删除证书。

### 4. 入口输入片

正文规定：

- 若原节点 \(\beta\) 是入口节点，则子节点入口片为
  \[
  U_\beta^{\mathrm{in}}\cap U_{\beta,a};
  \]
- 其他入口片保持不变。

Lean 的 `NodeDomainRefinement` 有：

```lean
same_input_domain : N'.U = N.U
entry_projection :
  ∀ x : N'.U,
    node_domain_projection target source (N'.entry x)
      = N.entry (transport_network_input same_input_domain x)
```

由此源码证明了
```lean
NodeDomainRefinement.entry_domain_eq :
  N'.entry_domain v =
    N.entry_domain (h.projection v) ∩ N'.node_dom v
```
其中 `projection` 把旧节点映回自身，把子节点映回原 `target`。

因此：

- 对旧节点 \(v\ne\beta\)：
  \[
  N'.\mathrm{entry\_domain}(v)=N.\mathrm{entry\_domain}(v);
  \]
- 对子节点 \(\beta_a\)：
  \[
  N'.\mathrm{entry\_domain}(\beta_a)
  =N.\mathrm{entry\_domain}(\beta)\cap U_{\beta,a}.
  \]

这正是正文的入口片公式。

### 5. 边域公式

正文给出四类边公式：

\[
\begin{aligned}
D'_{\gamma\to\beta_a}
&=D_{\gamma\to\beta}\cap U_{\beta,a},\\
D'_{\beta_a\to\gamma}
&=D_{\beta\to\gamma}\cap f_{\beta,a}(U_{\beta,a}),\\
D'_{\beta_a\to\beta_b}
&=D_{\beta\to\beta}\cap f_{\beta,a}(U_{\beta,a})\cap U_{\beta,b},
\end{aligned}
\]
其余不涉及 \(\beta\) 的边保持不变。

Lean 没有分别列出四条形如式，而是使用一个统一公式：
```lean
NodeDomainRefinement.edge_domain_eq :
  N'.edge_domain v w =
    (N.edge_domain (projection v) (projection w)
      ∩ N'.node_image v) ∩ N'.node_dom w
```

这个统一公式与正文四式一致。逐项核对：

1. 旧节点 \(\gamma\) 到旧节点 \(\delta\)：
   \[
   D'_{\gamma\delta}
   =D_{\gamma\delta}\cap f_\gamma(U_\gamma)\cap U_\delta
   =D_{\gamma\delta},
   \]
   因为原边域本来就包含于源像与目标定义域。

2. 旧节点 \(\gamma\) 到子节点 \(\beta_a\)：
   \[
   D'_{\gamma\beta_a}
   =D_{\gamma\beta}\cap I_\gamma\cap U_{\beta,a}
   =D_{\gamma\beta}\cap U_{\beta,a}.
   \]

3. 子节点 \(\beta_a\) 到旧节点 \(\gamma\)：
   \[
   D'_{\beta_a\gamma}
   =D_{\beta\gamma}\cap f_{\beta,a}(U_{\beta,a})\cap U_\gamma
   =D_{\beta\gamma}\cap f_{\beta,a}(U_{\beta,a}).
   \]

4. 子节点 \(\beta_a\) 到子节点 \(\beta_b\)：
   \[
   D'_{\beta_a\beta_b}
   =D_{\beta\beta}\cap f_{\beta,a}(U_{\beta,a})\cap U_{\beta,b}.
   \]

所以 `edge_domain_eq` 正是四式的统一写法。

此外，正文说空边域省略。Lean 用 `edge_domain` 集合可以为空来表示；真正的边由
```lean
OperatorTransitionGraph.Edge β γ := (edge_domain β γ).Nonempty
```
判定。因此空边域自然不是一条边，和正文“空边域省略”一致。

### 6. 终止域

正文规定加细后各子节点终止域仍由出边域补集确定。Lean 中 `N'` 本身是 `FiniteOperatorNetwork`，其终止域正是
\[
T'_v=N'.\mathrm{node\_image}(v)
\setminus
\bigcup_w N'.\mathrm{edge\_domain}(v,w).
\]
因此无需再单独存一个终止域字段；在 `edge_domain_eq` 给定后，终止域随网络结构自动确定。

删除不可达子节点后，某个曾指向被删子节点的未使用输出可能成为终止输出；这正是“删去关联边后按补集重新确定终止域”的结果，不影响实际输入轨迹上的外延求值。

---

## 二、源码已经证明的结论

### 1. 构造性节点域加细

在 `domain_refinement_construction.lean` 中，`NodePartitionData` 精确包装了正文所需数据：

- 有限非空分划；
- 每个分块的局域算子；
- 局域定义域与局域等价。

源码构造了包含所有子节点的 `presentation`，再执行 `prune`，得到 `network`，并证明：

```lean
NodePartitionData.network_extensional_eq :
  P.network.extensional_operator = N.extensional_operator
```

这是强于
\[
\phi_{\mathcal N'}\equiv_U\phi_{\mathcal N}
\]
的结论：不仅局部等价，而且完整外延算子相等。

同时源码给出：
```lean
NodePartitionData.network_refinement :
  NodeDomainRefinement N P.network
```
以及
```lean
NodePartitionData.allowed_network_refinement :
  NetworkRefinement N P.network
```
所以该构造确实被登记为一次允许的节点域加细。

### 2. 路径投影与轨迹保持

源码证明了：

- `NodeDomainRefinement.path_projection`：
  \[
  (p_{\mathcal N'}(x))\text{ 经节点投影后}=p_{\mathcal N}(x);
  \]
- `NodeDomainRefinement.eval_projected`：
  \[
  \text{沿 }N'\text{ 路径的复合求值}
  =
  \text{沿投影后 }N\text{ 路径的复合求值}.
  \]

这对应正文节点域加细证明中“原轨迹中的每次出现替换为相应子节点，节点序列和终止输出保持”的论证。由于 `List.map` 不改变长度，路径投影还蕴含节点域加细不改变路径长度，正文所说的长度仍为 \(r\) 也得到覆盖。

### 3. 抽象加细保持外延等价

在 `network_refinement.lean` 中：

```lean
NetworkRefinement.path_eval_eq
```
说明一步加细后的路径求值与原路径求值相同；

```lean
NetworkRefinement.refinement_preserves_local_equivalence :
  LocalEquivalent N'.extensional_operator N.extensional_operator N.U
```
正是节点域加细情形下正文命题的结论；

```lean
NetworkRefinement.refinement_preserves_representation
```
进一步说明若 \(N\) 表示算子 \(\phi\)，则加细后的 \(N'\) 仍表示同一 \(\phi\)。

对节点域分支，证明使用的是：

- `same_input_domain`；
- `entry_projection`；
- `choice_projection`；
- 以及 `NodeDomainRefinement` 的节点算子兼容性。

注意：该外延等价证明并不使用完整的 `edge_domain_eq`。这不是缺陷：正文 h-012f 的实际求值只沿真实发生路径进行；未被使用的边域是否正确，不影响外延等价本身。`edge_domain_eq` 则是完整覆盖正文“节点域加细定义”所必需的，源码已把它放进 `NodeDomainRefinement`。

### 4. 删除冗余节点保持求值

`network_presentation.lean` 中已经证明：

- `FiniteNetworkPresentation.prune_path_labels`；
- `FiniteNetworkPresentation.prune_eval`；
- `FiniteNetworkPresentation.prune_extensional_operator_eq`。

这正是正文引理 h-ced8c7236326e104 在节点域加细最终一步的用途：先构造含全部子节点的网络，再删除不可达子节点，路径与输出保持不变。

---

## 三、需要补充或需要明确的内容

以下都不是本题 h-012f 节点域分支的数学缺口，但属于形式化接口上的补充项。

### 1. 四条边域公式没有各自命名

源码有统一的 `NodeDomainRefinement.edge_domain_eq`，但没有分别为以下四式命名：

- 旧到旧；
- 旧到子节点；
- 子节点到旧；
- 子节点到子节点。

若要逐字对照正文，可补充四个简单推论，例如：

```lean
old_to_old_edge_domain_eq
old_to_piece_edge_domain_eq
piece_to_old_edge_domain_eq
piece_to_piece_edge_domain_eq
```

它们都可以由 `edge_domain_eq` 和节点投影、节点算子兼容性直接推出，不改变数学内容。

### 2. 抽象关系是“后删除证书”

`NodeDomainRefinement` 描述的是删除不可达子节点后的最终网络关系；正文的操作先造全部子节点，再 prune。  
`NodePartitionData.presentation` 实际执行了“先造全部子节点”，`network := presentation.prune` 执行删除，因此构造性部分完整。

如果还想要一个额外定理：

> 任意满足正文四条替换公式的最终网络 \(N'\)，都能选出某个 `source` 映射并构造出 `NodeDomainRefinement N N'`，

则需要额外写“从最终标签集构造 `source`”的引理。这个定理不是 h-012f 证明所必需，但可加强定义与正文的逆向对应。

### 3. `OperationalNodeDomainRefinement` 不能单独代表正文定义

源码注释明确说它有意较弱，只约束实际发生路径，不约束未使用边。  
因此：

- 外延等价证明可以基于这个较弱接口；
- 但“节点域加细定义”的完整性必须看 `NodeDomainRefinement`，它额外加了 `edge_domain_eq`。

这一点在审阅时很重要。

### 4. L/K/N 比较条件与不可约代表不在本题范围

正文“允许加细规则族”中提到，规则族还可以指定节点域加细在 L/K/N 受限数据上的比较条件。Lean 的 `NodeDomainRefinement` 只编码网络结构、局域算子和边域，不编码这类矩阵证书比较条件。

这不会影响 h-012f 的证明，因为该命题只涉及外延算子与求值轨迹。  
如果需要完整形式化“允许加细规则”或“不可约代表”，需要另行补充规则族、L/K/N 比较条件，以及不可约代表的存在性/终止性证明。源码中的 `IrreducibleRepresentative` 也只声明选定代表，不声明存在性或唯一性，这与正文“不声明存在性或唯一性”的说明一致。

### 5. 代数加细分支未在本题审阅

`NetworkRefinement` 同时包含节点域加细和代数加细，但本题只要求节点域分支。上面的结论只针对 `.node_domain` 构造，不评价代数分支。

---

## 四、反例检查与修复方向

未发现针对当前 `NodeDomainRefinement` 的反例。若试图削弱实现，会立即出现问题：

1. **只使用 `OperationalNodeDomainRefinement`，不加入 `edge_domain_eq`**：  
   可以保持所有实际输入路径不变，但删改一条从未被使用的旧边。外延算子仍相等，但所得网络不再满足正文“其余边和转移域保持不变”的节点域加细定义。这说明 `NodeDomainRefinement` 中额外的 `edge_domain_eq` 是必要的；当前源码已经包含它。

2. **删除一个实际被到达的分块**：  
   会违反 `piece_node_present_iff_reached`，并且对应输入的路径投影可能不存在，外延等价一般会破坏。

3. **只要求子节点算子与原子算子在分块上相等，却删去分块外取值信息**：  
   由于 `Operator` 在定义域外取 `bot`，`local_domain + local_equiv` 已足以恢复整个限制算子，故没有缺口。

因此，若要做形式化增强，建议的方向只是：

- 补四条边域公式的命名推论；
- 补 `local_factor = restrict_operator ...` 的抽象版本；
- 补从任意最终标签网络反向构造 `source` 的识别引理；
- 若要研究完整“允许加细规则”，再单独加入 L/K/N 比较条件与不可约性存在性。

这些均为接口增强，不是当前节点域加细与外延等价命题的数学修复。