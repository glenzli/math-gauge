## 总体判断

结论需要分两层看：

1. **就“给定一个 `NetworkRefinement` 见证，证明外延算子保持”这一核心定理而言，源码中的证明是正确的、已完成的。**  
   `refinement_preserves_local_equivalence` 已由源码证明；`domain_refinement_construction` 中还直接证明了规范构造 `NodePartitionData.network` 的外延等式。没有任何 `sorry`/`admit`，且 `lake build` 对相关模块成功。

2. **就“把数学正文的节点域加细精确定义形式化”而言，当前 `NodeDomainRefinement` 不是完整、准确的编码。**  
   它只要求局部算子在分块上一致，以及新网络在**实际到达的输入**上的后继选择与原网络经投影后一致；它没有要求正文中的四类边域公式在全部节点输出上成立。因此它是一个**充分证书/较宽的关系**，不是“`N'` 由正文节点域加细得到”的精确等价定义。

所以更准确的评价是：

> **定理结论层面基本完整；定义和覆盖范围层面不完整。**  
> 当前实现证明的是“若 `N'` 满足一个比正文节点域加细更弱但足以保持实际路径的证书，则外延不变”；它没有证明 `NodeDomainRefinement` 恰好等于正文的节点域加细关系，也没有把 `NodePartitionData` 构造与 `NodeDomainRefinement` 形式连接起来。

---

## 一、逐项对应关系

### 1. 被加细节点与有限非空分拆

正文要求把节点 \(\beta\) 的定义域
\[
U_\beta=\operatorname{dom}(f_\beta)
\]
替换为有限非空分拆
\[
U_\beta=\bigsqcup_{a=1}^{q}U_{\beta,a}.
\]

Lean 中对应为：

- `target : V`：被替换的节点；
- `part_count : Nat`，`part_count_pos : 0 < part_count`；
- `piece : Fin part_count → Set X`；
- `piece_nonempty`；
- `piece_disjoint`；
- `piece_cover : (⋃ a, piece a) = N.node_dom target`。

其中 `N.node_dom target` 就是 `dom (N.node_op target)`。因此这一部分与正文一致。

### 2. 子节点局域算子

正文要求
\[
\operatorname{dom}(f_{\beta,a})=U_{\beta,a},
\qquad
f_{\beta,a}\equiv_{U_{\beta,a}} f_\beta.
\]

Lean 中对应为：

- `local_factor : Fin part_count → Operator X bot`；
- `local_domain : dom (local_factor a) = piece a`；
- `local_equiv : LocalEquivalent (local_factor a) (N.node_op target) (piece a)`。

这已经足够推出
\[
local_factor(a)=\operatorname{restrict}_{U_{\beta,a}}(N.node_op target),
\]
因为 `local_factor a` 的定义域正好是 `piece a`，而在 `piece a` 上取值又与原算子相同；在补集上由 `dom` 的定义只能取 \(\bot\)。

`NodePartitionData.local_op_eq_restrict` 已经把这一事实显式证明了，但仅针对构造路径；通用 `NodeDomainRefinement` 中没有单独列出该引理。这不是数学缺口，只是 API 层面的表述缺失。

### 3. 旧节点与子节点的标签关系

正文说：未经剪枝时，旧节点保留，新增子节点 \(\beta_a\)；若某子节点不可达则删除。

Lean 中对应为：

- `source : V' → ({β : V // β ≠ target} ⊕ Fin part_count)`；
- `source_injective`；
- `old_node_present`；
- `piece_node_present_iff_reached`。

这个组合实际上把最终剪枝后的标签集编码得比较准确：

- 每个旧节点 \(\beta\ne target\) 都有唯一原像；
- 每个被实际到达的分块 `piece a` 恰好有唯一子节点原像；
- 未被到达的分块没有子节点；
- `source_injective` 排除了同一个旧节点或同一个分块对应多个标签。

因此，**在节点标签和剪枝层面**，`NodeDomainRefinement` 与正文的对应是合格的。

### 4. 入口输入片

正文要求：

- 若 \(\beta\) 是入口节点，则子节点入口片为
  \[
  U_\beta^{\mathrm{in}}\cap U_{\beta,a};
  \]
- 其他入口片保持不变；
- 空入口片省略。

Lean 中只有 `entry_projection`：
\[
\forall x\in N'.U,\quad
\operatorname{proj}(N'.\mathrm{entry}(x))
=
N.\mathrm{entry}(x).
\]

这个条件配合 `N'.entry_mem` 和分块互斥，实际上可以推出入口片的正确性：

- 若 \(x\) 原入口为 \(\beta\)，则 `N'.entry x` 必为某个子节点；
- 由 `N'.entry_mem x`，\(x\) 落在该子节点的定义域，即某个 `piece a` 中；
- 分块互斥决定唯一的 \(a\)。

所以入口分块的数学内容可以推出，但源码中没有显式写出
\[
N'.\mathrm{entry\_domain}(\beta_a)=N.\mathrm{entry\_domain}(\beta)\cap U_{\beta,a}
\]
这样的引理。如果要求“正文定义逐项落地”，这是一个需要补充的 API 定理；如果只要求证明外延结论，它不是阻塞点。

### 5. 入边、出边、自环边域：主要缺口

正文明确给出：

\[
D'_{\gamma\to\beta_a}
=
D_{\gamma\to\beta}\cap U_{\beta,a},
\]

\[
D'_{\beta_a\to\gamma}
=
D_{\beta\to\gamma}\cap f_{\beta,a}(U_{\beta,a}),
\]

以及自环
\[
D'_{\beta_a\to\beta_b}
=
D_{\beta\to\beta}
\cap f_{\beta,a}(U_{\beta,a})
\cap U_{\beta,b}.
\]

但 Lean 的 `NodeDomainRefinement` 中没有这些等式。它只有：

```lean
choice_projection :
  ∀ (v : V') (z : X),
    z ∈ (N'.node_op v).func '' N'.node_actual_input_domain v →
      map_output_choice (...) (N'.choice v z)
        = N.choice (...) z
```

注意这里量化的是 \(z\) 属于

\[
(N'.\mathrm{node\_op}\ v)(N'.\mathrm{node\_actual\_input\_domain}\ v),
\]

即**实际到达的输入所产生的输出像**，而不是正文要求的整个
\(N'.\mathrm{node\_image}\ v\)。因此它只约束实际路径上使用的后继，不约束未被源输入使用的输出上的边域。

也就是说，当前字段能够保证：

- 实际路径上的后继正确；
- 实际路径上的终止行为正确；
- 因而外延算子相同。

但它不能保证：

- 未使用输出上的入边；
- 未使用输出上的出边；
- 未使用输出上的自环边；
- 因此也不能保证全局终止域等于正文公式给出的终止域。

这正是主要缺口。

### 6. 终止域

正文说子节点终止域仍由出边域的补集确定。

在 Lean 中，`FiniteOperatorNetwork.terminal_domain` 本身不是独立字段，而是由 `edge_domain` 和节点像定义的。因此：

- 如果边域完全正确，终止域会自动正确；
- 当前实现只在实际路径上保证终止行为；
- 没有一般性地证明正文的
  \[
  T'_{\beta_a}=f_{\beta,a}(U_{\beta,a})\cap T_\beta
  \]
  或其剪枝后的相应公式。

所以“终止域”不是缺少一个存储字段，而是缺少由正确边域推出的全局等式。

### 7. 同一输入域

`same_input_domain : N'.U = N.U` 与正文一致。  
`NetworkRefinement.same_input_domain` 也把该等式从两个分支中提出，方向上足以支持外延比较。

### 8. 结论

正文结论是
\[
\phi_{\mathcal N'}\equiv_U\phi_{\mathcal N}.
\]

Lean 中的
```lean
theorem refinement_preserves_local_equivalence
    (h : NetworkRefinement N N') :
    LocalEquivalent N'.extensional_operator N.extensional_operator N.U
```
在已有 `NetworkRefinement` 见证的前提下，已经给出该结论的证明。配合 `h.same_input_domain`，即可得到两网络在同一输入域上的外延等价；域外二者都由 \(\bot\) 补全，因此也可进一步得到外延算子相等。

源码没有专门包装成
```lean
ExtensionalEquivalent N N'
```
或
```lean
ExtensionalEquivalent N' N
```
但这是容易补上的一层 API，不是数学问题。

---

## 二、源码已经证明的部分

以下结论是源码真实证明的：

1. **规范构造的局部算子确实是被加细节点的限制。**  
   `NodePartitionData.local_op_eq_restrict` 证明了
   \[
   P.\mathrm{local\_op}(a)
   =
   \operatorname{restrict}_{P.\mathrm{piece}(a)}
   (N.\mathrm{node\_op}\ \mathrm{target}).
   \]

2. **规范构造的路径染色与投影正确。**  
   `NodePartitionData.coloured_terminal`、`coloured_eval` 证明了原终止轨迹经子节点染色后仍为终止轨迹，且沿路径求值不变。

3. **规范构造剪枝后仍保持路径。**  
   `NodePartitionData.network_path_labels`、`network_path_projection` 证明了
   \[
   \text{新网络路径}\mapsto\text{原网络路径}
   \]
   的投影关系。

4. **规范构造的外延算子等于原网络。**  
   `NodePartitionData.network_extensional_eq` 给出的是强于正文局部等价的等式：
   \[
   \phi_{P.\mathrm{network}}=\phi_N.
   \]

5. **通用证书下的实际路径投影。**  
   `NodeDomainRefinement.terminal_projection` 证明：若 `N'` 的实际终止路径满足证书条件，则投影到原标签后得到 `N` 的终止路径。

6. **通用证书下的路径唯一性识别。**  
   `NodeDomainRefinement.path_projection` 利用 `terminal_path_unique` 证明投影路径正好等于原网络的唯一路径。

7. **通用证书下的求值相等。**  
   `NodeDomainRefinement.eval_projected` 证明沿投影路径的链式求值与原网络相同。

8. **最终外延保持定理。**  
   `NetworkRefinement.path_eval_eq` 和
   `refinement_preserves_local_equivalence` 已证明：
   若存在 `NetworkRefinement` 见证，则两个外延算子在公共输入域上逐点相等。

9. **表示保持。**  
   `refinement_preserves_representation` 进一步证明：若 `N` 表示算子 \(\varphi\)，则加细后的 `N'` 也表示 \(\varphi\)。

10. **可编译性。**  
    相关模块通过 `lake build`，未发现 `sorry`/`admit` 或新增公理。

---

## 三、关键反例：`NodeDomainRefinement` 比正文定义更宽

下面的例子说明：当前 `NodeDomainRefinement` **不能**被解释为“`N'` 恰好由正文节点域加细得到”。

取
\[
X=\{\bot,a,c,y,z\},
\qquad
U=\{a,c\}.
\]

构造原网络 \(N\)：

- 只有一个节点 \(\beta\)；
- 局域算子
  \[
  f_\beta(a)=a,\quad
  f_\beta(c)=c,\quad
  f_\beta(y)=z,\quad
  f_\beta(z)=z,\quad
  f_\beta(\bot)=\bot;
  \]
- 节点定义域
  \[
  U_\beta=\{a,c,y,z\};
  \]
- 入口节点为 \(\beta\)，入口片为 \(U=\{a,c\}\)；
- 设一个自环边
  \[
  D_{\beta\to\beta}=\{z\},
  \]
  输出 \(z\) 选择进入 \(\beta\)，其余输出终止。

这个网络是合法的有限算子网络：源输入 \(a,c\) 分别一步终止；节点 \(\beta\) 被实际路径经过；边域 \(\{z\}\subseteq f_\beta(U_\beta)\cap U_\beta\)。边 \(\{z\}\) 虽然不被任何源输入轨迹使用，但正文有限网络定义不要求每条边都被使用。

现在把 \(U_\beta\) 分成
\[
A=\{a,y\},
\qquad
B=\{c,z\}.
\]

对子节点 \(A,B\) 取限制算子
\[
f_A=f_\beta|_A,
\qquad
f_B=f_\beta|_B.
\]

构造新网络 \(N'\)：

- 节点为 \(A,B\)；
- 局域算子分别为 \(f_A,f_B\)；
- 入口仍为源输入 \(a\mapsto A,\ c\mapsto B\)；
- \(N'\) 中没有任何边，所有选择均为终止；
- 输入域仍为 \(U=\{a,c\}\)。

先检查正文的边域公式。对子节点 \(A\to B\)，正文要求
\[
D'_{A\to B}
=
D_{\beta\to\beta}
\cap f_A(A)
\cap B.
\]
而
\[
f_A(A)=\{a,z\},
\qquad
B=\{c,z\},
\]
故
\[
D'_{A\to B}
=
\{z\}\cap\{a,z\}\cap\{c,z\}
=
\{z\}.
\]
因此正文定义下的加细网络必须保留一条 \(A\to B\) 的自环边。类似地，\(B\to B\) 也应为 \(\{z\}\)。

但 \(N'\) 中没有任何边。故 \(N'\) **不是**正文节点域加细的结果。

然而 `NodeDomainRefinement` 会接受它：

- 目标为 \(\beta\)；
- 分块 \(A,B\) 非空、互斥、并等于 \(U_\beta\)；
- `local_factor` 为两个限制算子；
- `source` 把两个子标签分别送到 \(A,B\)，且二者都被实际到达；
- `same_input_domain` 成立；
- `entry_projection` 成立；
- 实际输入域中：
  - 子节点 \(A\) 的实际输入只有 \(a\)；
  - 子节点 \(B\) 的实际输入只有 \(c\)；
  - 在 \(a,c\) 上，\(N'\) 与原网络的选择都是终止；
- 因而 `choice_projection` 成立。  
  这里没有删除任何子节点，因为 \(A,B\) 都由源输入实际到达；\(z\) 不是源输入的像，但正文的剪枝规则删除的是不可达节点，而不是未被使用的非空边域。

所以：

\[
\boxed{
N'\text{ 满足当前 }NodeDomainRefinement,\quad
N'\text{ 却不是正文公式给出的节点域加细。}
}
\]

这个反例并不否定外延保持定理；事实上 \(z\notin U\)，两个网络的外延算子仍然相同。它否定的是：当前 `NodeDomainRefinement` 是正文定义的**精确形式化**。

---

## 四、这个缺口的数学影响

### 1. 不影响已经证明的外延结论

`refinement_preserves_local_equivalence` 的证明只使用实际路径：

- 从入口开始；
- 用 `choice_projection` 逐步投影后继；
- 用 `local_equiv` 保持局域求值；
- 用 `terminal_path_unique` 识别原网络路径。

因此，对于当前较宽的证书，定理仍然成立，证明也没有漏洞。它是该关系的**充分条件**。

### 2. 会影响所有依赖“网络数据”而非仅外延算子的下游陈述

如果后续使用：

- `N'.edge_domain`；
- `N'.terminal_domain`；
- `N'.entry_domain` 的精确公式；
- 有效约化；
- 路径分段读出；
- 表示层读出；
- 不可约代表；
- 加细规则的可容许性；

那么不能仅由当前 `NodeDomainRefinement` 推出正文对应的精确网络数据。当前关系允许在实际输入之外改变边和终止域，因此可能把两个在表示层不同、但在外延层相同的网络都识别为“节点域加细”。

### 3. 规范构造 `NodePartitionData` 与通用关系没有桥接

`domain_refinement_construction` 中的 `NodePartitionData` 更接近正文的构造：

- 分块；
- 限制算子；
- 解染路径；
- 剪枝；
- 外延等式。

但它没有证明：

```lean
NodePartitionData -> NodeDomainRefinement
```

也没有证明：

```lean
NodeDomainRefinement -> 与某个 NodePartitionData 的数据相等/同构
```

因此目前是两套平行形式化：

- 一套是较宽的路径证书 `NodeDomainRefinement`；
- 一套是较具体的构造 `NodePartitionData`。

二者没有形式上的互相覆盖。

---

## 五、修复方向

### 如果目标只是“外延保持定理”

当前 `NodeDomainRefinement` 可以保留，但建议：

1. 将名字改为类似
   ```lean
   NodeDomainRefinementCertificate
   ```
   并在文档中明确它只是“保持实际路径的充分证书”，不是正文节点域加细的精确定义。

2. 增加桥接定理：
   ```lean
   NodePartitionData.toNodeDomainRefinement
   ```
   证明 `NodePartitionData.network` 满足该证书。

3. 增加一个简单的包装：
   ```lean
   theorem NetworkRefinement.extensionalEquivalent ...
   ```
   把当前的局部等价和 `same_input_domain` 包装成 `ExtensionalEquivalent`。

### 如果要忠实形式化正文定义

则应新增一个“精确节点域加细”关系，至少包含以下边域条件。以下用 \(s(\beta')\) 表示标签映射，对存在的子节点 \(a,b\)：

1. 旧旧边：
   \[
   N'.\mathrm{edge\_domain}(\beta',\gamma')
   =
   N.\mathrm{edge\_domain}(\beta,\gamma).
   \]

2. 旧入边到子节点：
   \[
   N'.\mathrm{edge\_domain}(\beta',a)
   =
   N.\mathrm{edge\_domain}(\beta,\mathrm{target})
   \cap \mathrm{piece}(a).
   \]

3. 子节点到旧出边：
   \[
   N'.\mathrm{edge\_domain}(a,\gamma')
   =
   N.\mathrm{edge\_domain}(\mathrm{target},\gamma)
   \cap f_a(\mathrm{piece}(a)).
   \]

4. 子节点自环：
   \[
   N'.\mathrm{edge\_domain}(a,b)
   =
   N.\mathrm{edge\_domain}(\mathrm{target},\mathrm{target})
   \cap f_a(\mathrm{piece}(a))
   \cap \mathrm{piece}(b).
   \]

这些条件只需对最终保留的标签陈述；被剪掉的子节点不必陈述，或需要另外规定其源端选择强制为 `stop`。

同时补充：

- 入口域等式：
  \[
  N'.\mathrm{entry\_domain}(a)
  =
  N.\mathrm{entry\_domain}(\mathrm{target})\cap \mathrm{piece}(a);
  \]
- 由边域取补集得到的终止域等式；
- `NodePartitionData.network` 满足上述精确关系的定理；
- 任意正文节点域加细都可嵌入 `NodePartitionData` 的唯一性/同构定理。

---

## 六、最终判定

- **源码已证明的结论：**  
  `NetworkRefinement` 见证下，特别是 `NodeDomainRefinement` 的当前较宽证书下，节点域分支保持外延算子；规范构造 `NodePartitionData.network` 也被直接证明与原网络外延相等。

- **尚未覆盖的内容：**  
  当前 `NodeDomainRefinement` 没有精确编码正文的四类边域公式；它允许未实际使用输出上的边和终止域与正文不同。因此不能把它当作正文“节点域加细”的完整定义。`NodePartitionData` 虽有更接近正文的构造，但缺少与通用关系的形式桥接以及完整的边域/终止域公式。

因此，若验收标准是“证明外延保持”，核心实现是正确的；若验收标准是“完整、准确地形式化正文节点域加细定义及其全部数据约束”，则当前实现**不完整**。