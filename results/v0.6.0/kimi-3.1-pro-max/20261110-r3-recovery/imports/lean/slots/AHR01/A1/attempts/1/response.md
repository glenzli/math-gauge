## 结论

**就“节点域加细保持外延等价”这一命题而言，实现是正确、完整且有实际 Lean 证明的。**关系版证明了同域上的局部等价，构造版进一步证明了删冗后的外延算子全局相等。

但若把 `NodeDomainRefinement` 理解为正文“节点域加细结果”的**精确关系刻画**，则仍有不足：它对未被源输入实际到达的输出上的路由约束过弱，会承认额外删改未使用边域的网络。这不影响外延等价结论，却会改变原始 `edge_domain`、`terminal_domain` 等表示层数据。

---

## 1. 正文定义与实现的逐项对应

### 1.1 有限非空分划与局部算子：对应准确

正文要求
\[
U_\beta=\bigsqcup_{a=1}^qU_{\beta,a},\qquad
\operatorname{dom}f_{\beta,a}=U_{\beta,a},\qquad
f_{\beta,a}\equiv_{U_{\beta,a}}f_\beta .
\]

两套接口都完整表达了这些条件：

- 关系版：`network_refinement.lean:76-102`
  - `part_count_pos`；
  - `piece_nonempty`、`piece_disjoint`、`piece_cover`；
  - `local_domain`、`local_equiv`；
  - 新旧节点算子的兼容条件。
- 构造版：`domain_refinement_construction.lean:12-21` 的 `NodePartitionData` 使用同一组分划和局部算子条件。

正文进一步指出局部算子实际上就是域限制算子。构造版对此有明确证明：

- `local_op_eq_restrict`，`domain_refinement_construction.lean:31-40`。

因此这里不是只假设“域内相等”而遗漏域外取值；`local_domain` 与吸收元保持条件共同保证了域外均为 `bot`。

### 1.2 节点标签与删冗：符合正文的事后删冗规则

关系版的标签类型为
```lean
{v : V // v ≠ target} ⊕ Fin part_count
```
即“未拆分旧节点 + 所有分片子节点”。其中：

- `source_injective` 防止不同新节点共用同一标签；
- `old_node_present` 保证所有旧非目标节点仍保留；
- `piece_node_present_iff_reached` 保证分片节点恰好在其被原网络实际轨迹到达时保留，见 `network_refinement.lean:90-102`。

`NodePieceReached` 检查原网络某条实际路径在目标节点发生处的当前输入是否落入该分片，和“加细后删除不被任何输入轨迹经过的子节点”相符。旧节点原来均满足无冗余性，加细不改变其轨迹发生，因此全部保留也是正确的。

构造版则先建立含所有分片的 `FiniteNetworkPresentation`，再执行
```lean
P.presentation.prune
```
见 `domain_refinement_construction.lean:208-235`，与正文“先加细、再按删冗引理处理”的顺序一致。

### 1.3 输入域与入口片：条件足够，且能推出正文公式

`same_input_domain` 和 `entry_projection` 位于 `network_refinement.lean:103-106`。构造版直接使用
```lean
entry := fun x => P.lift_label (N.entry x) x.val
```
见 `domain_refinement_construction.lean:221`。

虽然关系版只显式约束入口标签的投影，但结合：

- `N'.entry_mem`；
- 子节点定义域等于对应分片；
- 分片互斥；
- `source_injective`；

即可推出：目标子节点的入口输入片正是
\[
U_\beta^{\mathrm{in}}\cap U_{\beta,a},
\]
旧节点的入口片保持不变。因此这里没有削弱实际入口行为。

此外，节点域加细含有 `target`，而 `N.node_reachable target` 给出某个 `x : N.U`，所以该分支自动蕴含 `U` 非空，符合正文使用局部等价记号时的非空约定。

### 1.4 普通边、自环与终止域：构造版忠实，关系版只保留实际部分

构造版统一定义
```lean
map_output_choice (fun w => P.lift_label w z)
  (N.choice (P.projection v) z)
```
见 `domain_refinement_construction.lean:111-112`。其含义是：

- 进入目标节点时，按当前输出所属分片选择目标子节点；
- 离开目标子节点时，沿用原目标节点的后继决策；
- 未涉及目标节点的路由保持不变。

这与正文的普通入边、普通出边公式相符。自环还要求同时细分源输出像和目标输入域，构造版有专门定理：

- `self_loop_choice_iff`，`domain_refinement_construction.lean:119-152`，

正好对应
\[
D'_{\beta_a\to\beta_b}
=D_{\beta\to\beta}\cap f_{\beta,a}(U_{\beta,a})\cap U_{\beta,b}.
\]

终止域没有作为独立任意数据，而仍由节点输出像减去所有出边域得到，符合正文“由出边域补集确定”。

但关系版的 `choice_projection` 只在
```lean
z ∈ (N'.node_op v).func '' N'.node_actual_input_domain v
```
上要求新旧路由一致，见 `network_refinement.lean:107-111`。这足以保证实际求值不变，却不足以保证正文规定的全部原始边域和终止域不变。具体问题见第 3 节。

---

## 2. 源码已经证明的外延保持结论

### 2.1 关系版的证明链完整

节点域分支没有把“完整路径对应”作为未证明的前提，而是实际推导出来：

1. `node_eval_eq`  
   `network_refinement.lean:184-193`  
   新旧节点在实际节点定义域上的局部算子取值相同。

2. `terminal_projection`  
   `network_refinement.lean:195-212`  
   从实际输入域出发，将新网络的终止路径投影为原网络的终止路径。每一步使用 `choice_projection`；进入下一节点时使用已证明的 `next_output_mem_node_actual_input_domain`，因此下一歩仍满足实际输入前提。

3. `path_projection`  
   `network_refinement.lean:214-220`  
   利用入口投影和终止路径唯一性得到
   \[
   \operatorname{map}\ \mathrm{projection}\,(p_{N'}(x))=p_N(x).
   \]
   路径长度不变也随之由 `List.length_map` 得到。

4. `eval_projected`  
   `network_refinement.lean:222-231`  
   证明投影前后的路径求值相等。

5. `NetworkRefinement.path_eval_eq` 与  
   `refinement_preserves_local_equivalence`  
   最终得到
   ```lean
   LocalEquivalent N'.extensional_operator N.extensional_operator N.U
   ```
   这正是正文的
   \[
   \phi_{N'}\equiv_U\phi_N.
   \]

`refinement_preserves_representation` 还正确给出了“若原网络表示某算子，则加细网络仍表示该算子”的推论。

由于两网输入域相同，且外延算子在域外均取 `bot`，该局部等价还可立即提升为两个外延算子的全局相等；关系版没有单独包装这个推论，但不是数学缺口。

### 2.2 构造版独立证明了更强的结论

构造版依次证明：

- `coloured_terminal`：原终止路径按各次实际输入重新着色后仍是终止路径；
- `coloured_eval`：重新着色前后求值相同；
- `network_path_labels`、`network_path_projection`：删冗后的实际路径就是重着色路径，遗忘分片标签即恢复原路径；
- `network_extensional_eq`，`domain_refinement_construction.lean:258-269`：
  ```lean
  P.network.extensional_operator = N.extensional_operator
  ```

这覆盖了正文证明中的“逐次重着色—终止输出不变—删冗不变—外延相等”全过程，并直接包含域外均为 `bot` 的部分。

我对 `network_refinement.lean` 和 `domain_refinement_construction.lean` 运行了 Lean 类型检查，均通过；相关定理的公理报告只有 `propext`、`Classical.choice`、`Quot.sound`，未发现 `sorry` 或额外自定义公理。

---

## 3. 精确定义层面的反例：关系允许额外删除未使用边

取底空间
\[
X=\{\bot,a,b,c\},
\]
其中 \(a,b,c\) 互异且均非吸收元。原网络 \(N\) 只有一个节点 \(\beta\)：

- 源输入域 \(U=\{a\}\)，唯一入口片为 \(\{a\}\)；
- \(U_\beta=\{a,b,c\}\)；
- \(f_\beta\) 在 \(U_\beta\) 上为恒等映射，域外取 \(\bot\)；
- 有一个自环，其边域 \(D_{\beta\to\beta}=\{b\}\)。

唯一源输入 \(a\) 不在自环边域中，因此立即终止。该网络满足统一有限终止和无冗余节点条件；自环从未被源输入实际使用，但仍是合法原始网络数据。

按正文作节点域加细，取
\[
A_0=\{a,b\},\qquad A_1=\{c\}.
\]
分片 \(A_1\) 不可达，删冗后删除；\(A_0\) 对应保留节点 \(\beta_0\)。正文规定保留的自环边域应为
\[
D'_{\beta_0\to\beta_0}
=\{b\}\cap f_{\beta_0}(A_0)\cap A_0
=\{b\},
\]
相应终止域为 \(\{a\}\)。

现在构造另一个网络 \(M\)：它与上述正规加细结果完全相同，唯一区别是把 \(b\) 处的自环也删掉，即在该输出上改为 `stop`。于是：

- \(M\) 的实际输入域仍只有 \(\{a\}\)，实际输出像只有 \(\{a\}\)；
- `choice_projection` 只需在 \(a\) 处检查，两边均为 `stop`，所以成立；
- 分片保留条件、入口投影、局部算子、标签单射及其余字段也均满足；
- 因而按各字段检查，`NodeDomainRefinement N M` 可容纳这个 \(M\)。

但 \(M\) 不是正文规定的加细结果：正文只删除不可达节点及其关联边，**不会额外删除两个保留节点之间原本存在的未使用边**。此处 \(b\) 还属于保留节点的完整局部输出像，因此这不是“选择函数在输出像外的无关紧要的全域化差异”；它实际改变了 Lean 的 `edge_domain`，并把终止域从 \(\{a\}\) 改成 \(\{a,b\}\)。

所以：

- **外延等价定理仍然正确**，因为实际源输入路径完全不变；
- **关系作为正文原始数据加细的精确刻画则过宽**，不能由它反推全部边域、终止域公式或规范加细的表示层身份。

---

## 4. 需要补充的内容与修复方向

### 对主命题

**无需补充证明。**关系版已证明局部等价，构造版已证明全局外延算子相等。二者各自都足以支撑所审阅的节点域加细结论。

### 对“精确定义、完整覆盖”的要求

建议补充以下形式化内容：

1. **给出删冗后的全量原始数据约束。**  
   不能简单把现有 `choice_projection` 无条件扩大到所有完整输出像，因为删冗确实可能使指向已删除分片的后继变为 `stop`。可直接采取以下任一方式：
   - 要求 `N'` 经标签运输后，与 `NodePartitionData.presentation.prune` 的完整 `presentation_data` 相同；该数据包含 `U`、`node_op`、`entry_domain`、`edge_domain`，正好能排除上述额外删边；
   - 或分别陈述保留标签上的普通入边、普通出边、自环及终止域公式，并显式加入目标分片是否被保留的删冗条件。

2. **补关系版与构造版的桥接定理。**  
   附件没有证明
   ```lean
   NodeDomainRefinement N P.network
   ```
   或更一般的“任一正文加细结果恰为规范构造的标签同构”。从定义看，现有弱关系应能容纳规范构造；若采用上述精确化，则可进一步证明双向刻画。当前没有该桥接定理并不削弱主结论，因为构造版已经独立证明了外延相等，但它限制了对“两种接口完全同义”的声明。

3. **可复用的数据公式引理。**  
   构造版目前显式给出了自环判据；普通入边、普通出边、入口片和终止域的全量公式虽可由定义推导，但没有全部封装成独立定理。若后续需要核对表示层数据，宜补上。只为主命题服务时，这些包装不是必需的。

综上，最准确的评价是：**节点域加细的外延保持已被可靠证明；当前关系实现是有意的实际行为层充分证书，但不是正文全部原始网络数据意义上的精确加细关系。**