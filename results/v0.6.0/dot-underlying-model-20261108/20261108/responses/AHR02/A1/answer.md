# 审阅结论

所给代码正确证明了“**所有可达路径均已给定合法 Lip 矩阵**”这一较强前提下的两个包含关系；分量、联合保证域及误差结论之间的对应也正确。但若按正文的局部设定，只要求参与相应并集的可评估路径具有证书，则现有全局定理的前提过强，不能算完整覆盖。缺口不在集合包含的证明步骤，而在路径证书的量化范围。

这不是正文包含关系的反例，也不是指出 Lean 证明了假命题。完整的局部到全局结论可以用附件已有的局部定理补出，但这一步应与源码已经写出的全局定理区分。

## 1. 已实现部分的对应关系

审阅对象为 `path_guarantee_domains.lean` 中锚点 `h-93b9c20ea18b4e59` 下的三个定理：

- `path_component_guarantee_union_subset_proxy_error`；
- `path_joint_guarantee_union_subset_proxy_error`；
- `path_guarantee_union_subset_proxy_error_text`。

它们的主要对象与正文对应如下：

1. `N.U` 是正文的 (U)，`N.ReachablePath` 是可达路径集合，`N.path_domain q.nodes` 是 (U_q)。`N.represents proxy` 是在 (U) 上逐点相等的网络表示，不要求代理算子在 (U) 外等于网络算子。
2. `path_component_sample N sample q j` 定义为 (S_j\cap U_q)。`path_evaluable_components` 表示该集合非空。虽然定义没有额外写一次 (j\in I_{\mathrm{res}})，但非空的交集已经蕴含 (S_j\ne\varnothing)；附件也有 `path_evaluable_subset_evaluable_components`。
3. `path_empirical_residual_upper` 使用路径链在该采样集上的偏差上确界，再加 `delta_o j`。`path_chain_eq_represented_proxy_on_path` 保证路径链与代理在路径域上相等，因而这确实是正文的路径残差。
4. 分量保证域展开后是
   \[
   \{x\in U_q:D_{L_q+L^*,j}(x;S_{q,j})+\widehat\varepsilon_{q,j}\le\tau_j\}.
   \]
   `weighted_anchor_distance` 对一个共同锚点取下确界，锚点内部才是矩阵加权和；没有误换成逐分量各自选择锚点。
5. 联合保证域展开为
   \[
   \{x\in U_q:\forall j\in J,\ D_{L_q+L^*,j}(x;S_{q,j})+
   \widehat\varepsilon_{q,j}\le\tau_j\}.
   \]
   对正文要求的非空 (J)，这恰好等于各分量保证域的交集。
6. `{x | ∃ q, ... ∧ x ∈ ...}` 正是正文受条件限制的路径并集。联合版本要求同一个路径 (q) 满足 (J\subseteq I_{\mathrm{res}}(q))，没有把“同一路径上的同时保证”混成各分量独立选择路径。

源码的分量证明从左侧取出 (q,h_j,h_{xq})，用 `N.path_domain_subset_source` 得到 (x\in U)，再调用 `proxy_path_component_guarantee_error_bound` 得到误差不超过阈值。联合证明同样先取得 (x\in U)，然后逐个 (j\in J) 调用局部联合结论，并把路径链值改写为代理值。这些步骤正确，也符合正文证明。

底层两个全局定理允许无限阈值和空 (J)，属于更一般的命题。`_text` 包装定理补列了有限阈值、全局可评估性及 (J\ne\varnothing) 的前提；这些前提没有用于证明，并非漏洞。尤其空 (J) 时，Lean 的联合域保留 (x\in U_q)，不等同于不加限制的空交集，但正文排除了空 (J)，所以不影响所审命题。

## 2. 不能忽略的前提强化

三个全局声明均要求：

```lean
hLq : ∀ q : N.ReachablePath,
  IsLipMatrix d (N.path_chain q.nodes) (N.path_domain q.nodes) (Lq q)
```

这要求**每一条可达路径**具有合法 Lip 矩阵，包括没有任何相关采样、根本不进入左侧并集的路径。

而正文先在 (j\in I_{\mathrm{res}}(q)) 的设定下取路径证书、定义保证域，然后仅对这些路径求并。对固定分量，推论只需
\[
\forall q,\quad j\in I_{\mathrm{res}}(q)
\Longrightarrow L_q\in\mathscr L(c_q)|_{U_q}.
\]
联合版本只需
\[
\forall q,\quad J\subseteq I_{\mathrm{res}}(q)
\Longrightarrow L_q\in\mathscr L(c_q)|_{U_q}.
\]
正文明确说无路径采样时相应路径证书停止，并未因此要求该路径另有 Lip 矩阵。

相较之下，代码的 `hpathV : ∀ q, U_q ⊆ Vstar` 不是实质额外限制：正文已经有 (U\subseteq V^*)，而所有 (U_q\subseteq U)。

尤其不能用“未参与并集的路径随便填一个无穷矩阵”消除 `hLq` 的差别。扩展伪度量允许不同点零距，而 `ENNReal` 中 (\infty\cdot0=0)。下面给出满足正文相关设定、却无法满足全路径 `hLq` 的有限例子。

## 3. 可复核的严格性例子

取单分量 (I=\{j\})，以及
\[
X=\{\bot,a,b,c\}.
\]
在非吸收点上，按两个等价类 (\{a,b\})、(\{c\}) 定义距离：同类距离为 (0)，异类距离为 (1)。另外令
\[
d(\bot,\bot)=0,\qquad d(x,\bot)=d(\bot,x)=\infty\quad(x\ne\bot).
\]
这是合法扩展伪度量：非吸收部分是商集上的离散度量的拉回；涉及吸收元的三角不等式也成立。特别有 (d(a,b)=0)、(d(a,c)=1)。

令 (U=V^*=\{a,b,c\})。目标算子把三个非吸收点全映到 (c)，并固定 (\bot)，故有目标证书 (L^*=0)。代理算子定义为
\[
\phi(a)=a,\quad\phi(b)=c,\quad\phi(c)=c,\quad\phi(\bot)=\bot.
\]

用两个立即终止的节点构造有限网络：

- 节点 (g) 的算子仅在 (c) 上非吸收，且 (c\mapsto c)；
- 节点 (b_0) 的算子仅在 (a,b) 上非吸收，且 (a\mapsto a,b\mapsto c)；
- 输入 (c) 选择节点 (g)，输入 (a,b) 选择节点 (b_0)；所有输出选择均为终止，深度界为 (1)。

两个节点定义域非空且均可达，没有后继边需要检查。由此得到两条可达单节点路径 (q_g,q_b)，路径域分别为
\[
U_{q_g}=\{c\},\qquad U_{q_b}=\{a,b\}.
\]
网络在 (U) 上表示上述代理算子。

取 (S_j=\{c\})、(\delta_{o,j}=0\)、(\tau_j=0\)，联合情形取 (J=\{j\})。于是
\[
S_{q_g,j}=\{c\},\qquad S_{q_b,j}=\varnothing.
\]
唯一参与并集的路径是 (q_g)。在其单点域上取 (L_{q_g}=0) 是合法证书，路径残差为零，共同锚点距离为零，因此
\[
U_{q_g,j}(0)=U_{q_g,J}(0)=\{c\}.
\]
而真实零误差域为 (\{b,c\}\)，所以正文两个包含关系均成立且左侧非空。

但 (q_b) 不存在任何合法 Lip 矩阵。单分量矩阵只有一个系数 (\lambda\in[0,\infty])。把 (a,b\in U_{q_b}) 代入 `IsLipMatrix`，必需
\[
1=d(c_{q_b}(a),c_{q_b}(b))
\le\lambda d(a,b)=\lambda\cdot0=0,
\]
矛盾。这对有限或无穷的 (\lambda) 都成立。

因此，全路径 `hLq` 不是正文局部条件的自动后果。即使任意延拓 `Lq` 的函数值，也不能延拓相应合法性证明。这个例子反驳的是“额外前提无损”的说法，而不是源码定理自身。

## 4. 如何补齐，以及哪些内容尚需补充

不必重证局部误差上界。保留现有定义，分别把全局定理的 `hLq` 换成上述带路径可评估条件的前提即可。矩阵族仍可定义在所有可达路径上，但只要求相关路径上的值满足证书条件。

补充证明如下：

- 分量情形：若 (x) 在左侧，则存在 (q)，满足 (j\in I_{\mathrm{res}}(q)) 及 (x\in U_{q,j}(\tau_j))。条件化的前提给出该 (q) 的合法证书。调用附件已有的 `proxy_path_component_guarantee_error_bound` 得到误差界；由路径域包含于 (U) 得到右侧成员资格。
- 联合情形：取同一个见证 (q)，由 (J\subseteq I_{\mathrm{res}}(q)) 取得该路径证书，再调用 `proxy_path_joint_guarantee_error_bound`。其结论对每个 (j\in J) 同时成立，且 (x\in U_q\subseteq U)。

也可用“相关路径”的子类型承载矩阵及其合法性，从类型上避免给无关路径填矩阵。若希望一个矩阵族同时覆盖所有分量的结论，可以只要求具有至少一个可评估分量的路径具备证书，仍不必覆盖完全无采样的路径。

上述条件化全局版本及其证明，是本审阅补充的数学论证；三个现有全局声明并未写出这一较弱前提版本。附件已有局部声明足以支持补齐，但“可由源码中的局部结果再推出”与“现有全局声明已按原前提表达并证明”应当区分。

若作者确实希望额外假设每条可达路径都已配备合法 Lip 矩阵，应在正文明确补列该假设。在这一加强后的解释下，现有实现完整覆盖两个包含关系，无需改变集合或误差结论。

本审阅依据所给源码作语义与证明结构检查，未声称重新编译全部附件；未修改附件，也未提交新增 Lean 源码。

原材料：Zhe Li / Glen Li / glenzli，*The Operator Evolution Theory*，https://glenzli.com/books/oet/ ，CC BY 4.0。本答复是对所给历史附件的审阅，不涉及当前版本的完成状态。
