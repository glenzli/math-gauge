## 结论

**就本题限定的范围——“节点域加细”的定义，以及该情形下“网络加细保持外延等价”的最终命题——所给 Lean 实现在数学上是准确且完整的。** 我没有发现会使定义漏掉正文情形、使定理前提不足，或使结论不成立的反例。

需要区分两种“完整”：

- **定义与最终定理的覆盖**：已经完整。抽象关系证明了正文所要求的局部外延等价；具体构造还证明了更强的全域外延算子相等。
- **正文证明中每个辅助公式都有独立 Lean 定理**：尚未完全做到。主要欠缺的是剪枝前后终止域的专门公式，以及若干很短的封装定理。它们不影响本题最终结论，但若要求逐句覆盖正文证明，应补充。

我执行了相关模块的 `lake build`，编译成功；附件 Lean 源码未检出 `sorry`、`admit` 或自定义 `axiom`。主要定义和定理的 `#print axioms` 仅显示 `propext`、`Classical.choice`、`Quot.sound`。

---

## 一、节点域加细定义的逐项对应

### 1. 有限非空分划与局域算子

正文要求
\[
U_\beta=\bigsqcup_{a=1}^{q}U_{\beta,a},\qquad q>0,
\]
各片非空、互不相交，并且
\[
\operatorname{dom}f_{\beta,a}=U_{\beta,a},\qquad
f_{\beta,a}\equiv_{U_{\beta,a}}f_\beta .
\]

Lean 中对应为：

- `NodePartitionData.count_pos`、`nonempty`、`disjoint`、`cover`：  
  `domain_refinement_construction.lean:12-21`
- 抽象关系中的 `part_count_pos`、`piece_nonempty`、`piece_disjoint`、`piece_cover`、`local_domain`、`local_equiv`：  
  `network_refinement.lean:68-84`

正文随后强调 \(f_{\beta,a}\) 实际上就是 \(f_\beta\) 在该片上的限制。Lean 的 `local_op_eq_restrict` 已证明
\[
f_{\beta,a}=\operatorname{restrict\_operator}(f_\beta,U_{\beta,a}),
\]
见 `domain_refinement_construction.lean:31-40`。理由正是：片内由局部等价相同，片外由定义域条件两边都为 `bot`。因此这里不是只证明了较弱的局部条件。

### 2. 子节点选择、旧节点保留与不可达片删除

`piece_at` 利用覆盖性选取所在片，`piece_at_unique` 利用互斥性证明唯一性，见 `domain_refinement_construction.lean:46-58`。

标签类型
\[
\{\gamma:\gamma\ne\beta\}\;\oplus\;\operatorname{Fin}q
\]
对应旧节点和分裂片。抽象关系中：

- `source_injective` 防止重复标签；
- `old_node_present` 保证所有旧节点保留；
- `piece_node_present_iff_reached` 规定分裂片恰好在其被某次实际发生使用时保留。

见 `network_refinement.lean:85-97`。

具体构造先形成 `presentation`，再以 `presentation.prune` 删除不可达标签，见：

- `domain_refinement_construction.lean:208-235`
- `network_presentation.lean:105-145`

`old_label_reached` 和 `piece_label_reached_iff` 分别证明旧节点必保留、分裂片的保留条件正好是正文所说的实际经过，见 `domain_refinement_construction.lean:295-342`。

这与正文“先加细，再删除不被输入轨迹经过的子节点”的顺序一致。

### 3. 入口输入片

抽象关系已经证明了统一公式
\[
U^{\mathrm{in},\prime}_v
=
U^{\mathrm{in}}_{\pi(v)}\cap U'_v,
\]
即 `NodeDomainRefinement.entry_domain_eq`，见 `network_refinement.lean:283-296`。

其中 \(\pi\) 是把分裂标签投影回原节点的映射。于是：

- 对分裂片 \(\beta_a\)：
  \[
  U^{\mathrm{in},\prime}_{\beta_a}
  =U^{\mathrm{in}}_\beta\cap U_{\beta,a};
  \]
- 对未替换旧节点 \(\gamma\)：因原入口片本已包含于 \(U_\gamma\)，公式化简为
  \[
  U^{\mathrm{in},\prime}_\gamma=U^{\mathrm{in}}_\gamma .
  \]

空入口片在 Lean 中表现为空 `entry_domain`，入口函数自然不会选中该节点；这与正文“空入口片省略”一致，不需要额外的入口节点集合字段。

### 4. 普通边与分裂自环

完整的 `NodeDomainRefinement` 在较弱的 `OperationalNodeDomainRefinement` 之上加入了
\[
D'_{v\to w}
=
\bigl(D_{\pi(v)\to\pi(w)}\cap\operatorname{im}'_v\bigr)\cap U'_w,
\]
见 `network_refinement.lean:118-125`。这里 \(\operatorname{im}'_v\) 是节点局域算子在其整个定义域上的像。

利用原网络的边域包含条件
\[
D_{\gamma\to\delta}\subseteq\operatorname{im}f_\gamma,
\qquad
D_{\gamma\to\delta}\subseteq U_\delta,
\]
该统一公式在四类情形下恰好化简为正文公式：

| 边的情形 | Lean 统一公式化简结果 |
|---|---|
| 旧节点 \(\gamma\to\delta\)，均非 \(\beta\) | \(D_{\gamma\to\delta}\)，即保持不变 |
| 入边 \(\gamma\to\beta_a\) | \(D_{\gamma\to\beta}\cap U_{\beta,a}\) |
| 出边 \(\beta_a\to\gamma\)，\(\gamma\ne\beta\) | \(D_{\beta\to\gamma}\cap f_{\beta,a}(U_{\beta,a})\) |
| 分裂自环 \(\beta_a\to\beta_b\) | \(D_{\beta\to\beta}\cap f_{\beta,a}(U_{\beta,a})\cap U_{\beta,b}\) |

所以统一公式并未误把“双重交集”强加为额外限制；额外交集在原边域包含关系下或是冗余，或正是正文要求。

具体构造并非只满足实际路径上的较弱关系：`network_edge_domain_eq` 在完整局域输出像上证明了同一边域等式，见 `domain_refinement_construction.lean:346-384`；`network_refinement` 将其封装进完整关系，见同文件 `:449-493`。因此，**未被任何入口轨迹使用、但两端节点均保留的边也没有丢失。**

### 5. 终止域和路由条件的作用范围

终止域在 Lean 中由输出像与出边域派生，不是独立数据，见 `operator_network.lean:391-400`。这与正文“终止域由出边域补集确定”一致。

`choice_projection` 只对**实际输入域产生的输出**要求路由投影一致，见 `network_refinement.lean:102-106`；完整保留边则由上述 `edge_domain_eq` 另行约束。这一分层是必要的，而不是定义变弱：删除不可达片后，某些从未实际出现的输出上的 `next` 必须改为 `stop`。

---

## 二、“保持外延等价”已经证明了什么

### 1. 抽象关系情形

令 `h : NodeDomainRefinement N N'`，将其视为 `NetworkRefinement.node_domain h`。

证明链条是：

1. `node_eval_eq`：每个新节点在其定义域上的求值等于其投影原节点的求值，见 `network_refinement.lean:198-207`。
2. `terminal_projection`：把新网络中从实际输入出发的终止轨迹投影为原网络的终止轨迹。归纳中，`next_output_mem_node_actual_input_domain` 保证下一状态仍属于实际输入域，因而可以继续使用 `choice_projection`，见 `network_refinement.lean:209-226`。
3. `path_projection`：
   \[
   (p_{N'}(x)).\operatorname{map}\pi=p_N(x),
   \]
   由入口投影和终止路径唯一性得到，见 `network_refinement.lean:228-234`。
4. `eval_projected`：
   \[
   \operatorname{eval}_{p_{N'}(x)}(x)
   =
   \operatorname{eval}_{(p_{N'}(x)).\operatorname{map}\pi}(x),
   \]
   见 `network_refinement.lean:236-246`。
5. `NetworkRefinement.path_eval_eq` 将上述两步合并，最后由
   `refinement_preserves_local_equivalence` 得出
   \[
   \forall x\in N.U,\quad
   \phi_{N'}(x)=\phi_N(x),
   \]
   即 `LocalEquivalent N'.extensional_operator N.extensional_operator N.U`，见 `network_refinement.lean:428-473`。

这正是正文命题
\[
\phi_{\mathcal N'}\equiv_U\phi_{\mathcal N}
\]
的方向和强度。`same_input_domain` 明确给出 \(N'.U=N.U\)，没有遗漏共同输入域前提。

`refinement_preserves_representation` 还进一步证明：若 \(N\) 表示 \(\varphi\)，则加细后的 \(N'\) 仍表示同一个 \(\varphi\)，见 `network_refinement.lean:480-495`。

值得注意的是，最终外延等价的证明实际只使用实际路由和局部求值；完整边域等式用于保证**定义层面的忠实性**。未使用边不会影响网络从 \(U\) 出发的外延算子，因此这不是证明缺口。

### 2. 具体构造情形

具体实现另外给出了独立、直接的构造证明：

- `colour_path` 按每次发生时的**当前输入**选择分裂片，见 `domain_refinement_construction.lean:167-180`。这正确处理了同一原节点多次发生时可选择不同子节点，以及自环目标片由输出点决定的情形。
- `coloured_terminal` 证明重着色后的路径仍是终止路径；
- `coloured_eval` 证明其输出与原路径相同，见同文件 `:184-205`。
- 剪枝保留这些路径和输出，见 `network_presentation.lean:147-176`。
- `network_path_projection` 证明遗忘分裂标签后恰好恢复原路径，见 `domain_refinement_construction.lean:249-252`。
- `network_extensional_eq` 最终证明
  \[
  \phi_{P.\mathrm{network}}=\phi_N
  \]
  为**整个算子相等**，不只是 \(U\) 上局部等价，见同文件 `:258-269`。

因此，具体构造不但产生满足完整关系的网络，而且直接证明了比正文最终命题更强的结论。

---

## 三、尚需补充的内容及其数学影响

以下不是现有定理的反例，而是若要“逐句覆盖正文证明”或改善 API 时应补充的项目。

### 1. 抽象关系的全域等式与直接外延等价封装

附件对一般 `NodeDomainRefinement` 只命名了局部等价定理；全域算子相等命名定理目前只针对具体构造 `P.network`。

但一般情形下也有
\[
N'.\mathrm{extensional\_operator}
=
N.\mathrm{extensional\_operator}.
\]
理由是：在 \(U\) 内使用已证明的局部等价；在 \(U\) 外，由 `same_input_domain`，两个外延算子都按定义取 `bot`。同理，`same_input_domain` 与局部等价可直接封装为 `ExtensionalEquivalent N' N`。

我在临时检查文件中验证了这两个短封装及下述路径长度等式均可通过 Lean elaboration；它们**不是附件已有定理**。其影响仅是缺少可复用的包装，不需要新增数学前提。

### 2. 路径长度与统一界的显式定理

由 `path_projection` 或构造中的 `network_path_projection`，对列表等式取 `List.length` 即得
\[
|p_{N'}(x)|=|p_N(x)|.
\]
因此节点域加细后的每条实际路径长度不变，并继承正文的
\[
r'=r\le \ell(N).
\]
具体构造的 `colour_path_length` 也已直接证明重着色不增加长度。缺少的只是一个便于下游引用的独立命名结论，不影响外延等价。

### 3. 剪枝前后终止域的专门公式

正文证明在**尚未剪枝**时使用
\[
T'_{\beta_a}
=
f_{\beta,a}(U_{\beta,a})\cap T_\beta,
\]
并未替换旧节点的终止域也不变。附件没有为节点域加细的 `presentation` 单独命名这些公式。

若要求完整覆盖这部分正文，应补充：

1. 剪枝前的上述两条终止域等式；
2. 剪枝后的精确公式，例如由 `edge_domain_eq` 直接得到
   \[
   T^{\mathrm{final}}_v
   =
   \operatorname{im}'_v
   \setminus
   \bigcup_{w\in V'}
   \bigl((D_{\pi(v)\to\pi(w)}\cap\operatorname{im}'_v)\cap U'_w\bigr).
   \]

**不能把剪枝前的简单交集公式直接沿用到剪枝后。** 一个可复核的小例子如下：

- 原网络只有一个节点 \(\beta\)，输入域 \(U=\{a\}\)，而
  \(U_\beta=\{a,a',b\}\)；
- \(f_\beta(a)=a,\ f_\beta(a')=b,\ f_\beta(b)=b\)；
- 输出 \(a\) 上 `stop`，输出 \(b\) 上 `next β`，故自环域为 \(\{b\}\)，原终止域为 \(\{a\}\)；
- 分划取 \(A_0=\{a,a'\}\)、\(A_1=\{b\}\)。

从唯一输入 \(a\) 出发只经过 \(A_0\)，所以 \(A_1\) 被删除。点 \(b\) 虽属于完整像 \(f_{\beta,0}(A_0)\)，却只来自未实际使用的输入 \(a'\)。剪枝前 \(b\) 进入 \(A_1\)，剪枝后只能 `stop`，于是 \(A_0\) 的终止域从 \(\{a\}\) 增大为 \(\{a,b\}\)。

这个例子同时说明：

- `choice_projection` 若改成对完整 `node_image` 量化，会过强；
- 终止域公式必须区分剪枝前后；
- 当前 Lean 的分层处理与正文语义相符。

---

## 总评

- **定义覆盖**：分划、局域限制、入口片、旧边、入边、出边、自环、不可达片删除和空域处理均有对应，统一边域公式在各类情形下可严格化约为正文公式。
- **定理覆盖**：抽象关系已证明正文要求的局部外延等价；具体构造还证明了全域算子相等。
- **没有需要修补的数学前提或反例。**
- **可选补充**：一般关系的全域等式和外延等价封装、显式路径长度定理，以及剪枝前后终止域的专门公式。它们影响的是逐句覆盖和接口复用，不影响本题指定命题的正确性。

审阅对象：Zhe Li（Glen Li / glenzli），ORCID https://orcid.org/0009-0006-6536-3453，*The Operator Evolution Theory*，https://glenzli.com/books/oet/，源仓库 https://gitlab.com/glenzli/oet-public，CC BY 4.0。