# 审阅结论

在题目允许采用附件定义、局部上界及辅助声明的范围内，所给实现准确、完整地覆盖了推论 **h-93b9c20ea18b4e59「路径保证域的全局拟合含义」的两个包含关系**。这不是仅由定理名称或注释作出的判断：源码分别证明了分量并集与联合并集的包含关系，且最终给出的误差是代理算子与目标算子的误差，而不只是路径链与目标的误差。

本结论是对所给源码的数学语义及证明结构的审阅；我未另行运行 Lean 编译，也未审阅本章其他结论。

## 一、对象和前提的对应

在 `path_guarantee_domains.lean` 中：

- 正文的 (U) 对应 `N.U`，(q\in\mathcal P) 对应 `q : N.ReachablePath`，(U_q) 对应 `N.path_domain q.nodes`。网络的输入域就是正文的分析域，并没有把正文的 (U) 漏掉。
- `N.represents proxy` 表示网络与代理在 `N.U` 上局部等价。辅助声明 `path_chain_eq_represented_proxy_on_path` 因而在 (x\in U_q) 时给出 (c_q(x)=\phi(x))。不要求两者在整个空间上相等。
- `path_component_sample N sample q j` 定义为 `sample j ∩ N.path_domain q.nodes`，正是 (S_{q,j}=S_j\cap U_q)。
- `path_evaluable_components N sample q` 表示路径采样非空的分量集。正文还显式要求 (j\in I_{\mathrm{res}})，但这不造成差别：(S_j\cap U_q\ne\varnothing) 自动推出 (S_j\ne\varnothing)。源码也已有 `path_evaluable_subset_evaluable_components`。
- `path_empirical_residual_upper` 展开后正是路径采样上 (d_j(c_q(x_s),\phi^\natural(x_s))) 的上确界加同一 `delta_o j`。
- 矩阵 `fun i j => Lq q i j + Lstar i j` 是逐路径的 (\mathbf A_q=\mathbf L_q+\mathbf L^*)，并未强迫所有路径共用一个路径矩阵。
- `hpathV` 由正文的 (U\subseteq V^*) 与 (U_q\subseteq U) 得到；`hLq` 是相关路径上的受限 Lip 证书；`hLstar` 是目标 Lip 包络证书。因此没有偷加一个必须由采样推断的目标正则性结论。

正文的采样域等其他设定没有全部作为并集定理的独立参数重列，这是在所允许的局部上界之上使用较弱前提，并非丢失所需结论。

## 二、保证域确实相同

`path_component_empirical_guarantee_domain` 经由 `empirical_component_guarantee_domain`、`anchor_gap_sublevel` 展开为

\[
\{x\mid x\in U_q\ \land\ D_{\mathbf A_q,j}(x;S_{q,j})+\widehat\varepsilon_{q,j}\le\tau_j\}.
\]

其中 `weighted_anchor_distance` 是先对同一个锚点计算加权和，再取下确界；不是把各分量的下确界分别相加。

联合域的 Lean 定义展开为

\[
\{x\mid x\in U_q\ \land\ \forall j\in J,
D_{\mathbf A_q,j}(x;S_{q,j})+\widehat\varepsilon_{q,j}\le\tau_j\}.
\]

它与正文的 (\bigcap_{j\in J}U_{q,j}(\tau_j)) 在 **(J\ne\varnothing)** 时相同。具体地，左式的成员属于每个分量域；反过来，从交集中取任意 (j_0\in J)，可取得 (x\in U_q)，再从各分量成员关系取得全部不等式。这是本审阅中对两种集合写法的直接展开论证，不声称源码另有一个专门命名的交集等式定理。

非空条件在此对应关系中有实际作用：若 (J=\varnothing)，正文若按通常空交集约定扩展会得到全空间，而 Lean 的上述定义得到 (U_q)。但正文明确排除了空族，故不构成对所审命题的缺口。

## 三、源码已证明的两个结论

### 1. 分量形式

`path_component_guarantee_union_subset_proxy_error` 的左侧是

\[
\{x\mid\exists q,\ j\in I_{\mathrm{res}}(q)\ \land\ x\in U_{q,j}(\tau_j)\},
\]

即正文的受限路径并集。右侧同时包含 (x\in N.U) 和所需误差不等式。

证明从并集成员关系取出 `q, hj, hxq`：

1. `hxq.1` 给出 (x\in U_q)，`N.path_domain_subset_source` 给出 (x\in U)。
2. `proxy_path_component_guarantee_error_bound` 利用该路径的 Lip 证书、目标证书和 `hj` 得出 (d_j(\phi(x),\phi^\natural(x))\le\tau_j)。

后一个辅助定理已在源码中通过路径链等于代理的等式，将 `path_component_guarantee_error_bound` 的路径链误差转换成代理误差。

### 2. 联合形式

`path_joint_guarantee_union_subset_proxy_error` 的左侧是

\[
\{x\mid\exists q,\ J\subseteq I_{\mathrm{res}}(q)\ \land\ x\in U_{q,J}(\boldsymbol\tau)\}.
\]

这里是先取**同一条路径**，再要求它能评估整个 (J)。它没有误写成每个分量各自选择一条路径的量词顺序。

源码同样先由 `hxq.1` 得到 (x\in U)，再固定任意 `j ∈ J`，调用 `path_joint_guarantee_error_bound`，并用 `path_chain_eq_represented_proxy_on_path` 改写为代理值，得到

\[
\forall j\in J,\quad d_j(\phi(x),\phi^\natural(x))\le\tau_j.
\]

因此正文联合形式的全部量词、路径筛选条件及右侧域限制都已被覆盖。

## 四、正文前提包装与范围

最终的 `path_guarantee_union_subset_proxy_error_text` 将这两个包含关系合取，并显式保留：全局分量可评估性、有限阈值、联合分量族非空，以及相关路径的证书。其 `hLq` 用析取条件同时供应两个并集定理所需的证书；分别用 `Or.inl`、`Or.inr` 传入，逻辑正确。两个独立定理也可分别使用，不必为了证明分量形式额外选择一个联合族。

包装中的若干前提只以 `have _ := ...` 保留，并没有参与底层证明。这并非把待证结论假设掉：底层定理实际上证明了更宽参数范围内的包含关系。尤其，有限阈值与 (J\ne\varnothing) 不必用于“从已给出的保证域成员关系推出误差界”这一步；但非空性仍用于上文所述的正文交集写法对应。

综上，无须补写新的数学结论才能覆盖该推论。若希望加强形式化文档的可追溯性，可另列一个“非空联合族时，联合域等于分量域交集”的桥接引理；这只是把上述直接定义展开显式记录，并非修复包含关系的错误。

本推论也没有声称这些路径保证域覆盖整个 (U)，没有给无采样路径自动提供证书，没有给出反向包含，更没有比较路径证书与全局证书所定义保证域的大小；不能把这些更强结论归于所给实现。

---

材料来源：Zhe Li（Glen Li / glenzli），*The Operator Evolution Theory*，https://glenzli.com/books/oet/ ，CC BY 4.0（https://creativecommons.org/licenses/by/4.0/）。本文为基于所提供历史版本附件的审阅与解释，并非对当前版本完成情况的声明。
