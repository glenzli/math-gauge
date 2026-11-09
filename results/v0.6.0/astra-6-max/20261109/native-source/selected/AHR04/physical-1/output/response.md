**结论：所给实现准确、完整地覆盖了正文 `h-93b9c20ea18b4e59` 的两个集合包含式。** 在允许使用附件局部上界与辅助声明的前提下，没有需要补齐的实质证明缺口。

对应关系如下：

| 正文结论 | Lean 中已证明的声明 |
|---|---|
| 分量路径保证域的并包含于真实分量误差区域 | [path_component_guarantee_union_subset_proxy_error](/private/tmp/math-gauge-astra-max-20261109/sessions/AHR04/physical-1/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean:520) |
| 联合路径保证域的并包含于真实联合误差区域 | [path_joint_guarantee_union_subset_proxy_error](/private/tmp/math-gauge-astra-max-20261109/sessions/AHR04/physical-1/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean:553) |
| 保留正文的全局可评估性、有限阈值和非空 \(J\) 条件，同时给出两式 | [path_guarantee_union_subset_proxy_error_text](/private/tmp/math-gauge-astra-max-20261109/sessions/AHR04/physical-1/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean:590) |

具体依据是定义与量词都吻合。`N.U`、`N.ReachablePath`、`N.path_domain q.nodes` 分别对应 \(U,\mathcal P,U_q\)；路径样本是 \(S_j\cap U_q\)，路径可评估性就是该交集非空。矩阵实参为 `Lq q i j + Lstar i j`，残差实参为对应路径的 `path_empirical_residual_upper`。

令
\[
B_{q,j}(x)=D_{\mathbf L_q+\mathbf L^*,j}(x;S_{q,j})
+\widehat\varepsilon_{q,j}.
\]
展开保证域定义，分量成员条件正是
\[
x\in U_q\ \land\ B_{q,j}(x)\le\tau_j,
\]
联合成员条件正是
\[
x\in U_q\ \land\ \forall j\in J,\ B_{q,j}(x)\le\tau_j.
\]
当 \(J\ne\varnothing\) 时，后一条件与正文的 \(\bigcap_{j\in J}U_{q,j}(\tau_j)\) 等价。源码以 `{x | ∃ q, …}` 表示受条件限制的并集，也是准确的集合表达。

证明可直接复核：从并集成员中取出路径 \(q\)，先由 `path_domain_subset_source` 得到 \(x\in U\)，再应用已有局部结论：
\[
d_j(\phi(x),\phi^\natural(x))
\le B_{q,j}(x)\le\tau_j.
\]
其中路径链与代理的对应由 `hrep` 及 `path_chain_eq_represented_proxy_on_path` 保证。联合分支**先固定同一个 \(q\)，再对每个 \(j\in J\) 证明误差界**，与正文的量词顺序一致。它没有将最终误差界作为假设。

有两点实现差异属于合理推广：

- 核心包含定理允许无限阈值，联合核心定理也允许空 \(J\)；正文封装明确加入了有限阈值、非空 \(J\)。这些条件在封装证明中仅以 `have _ := …` 保留，不构成缺证。尤其空 \(J\) 时联合定义与空交的区别，不影响正文的非空情形。
- 源码没有要求采样有限性，因为这一步包含关系不需要它。所需路径样本非空条件仍然保留；相关点的目标定义域由包络证书和 `hpathV` 保证，代理定义域由路径 Lip 证书及表示关系保证。

**源码已证明的范围，就是上述两个包含式。** 如果另要求整个 \(U\) 上都满足误差容限，还须给出保证域并集覆盖 \(U\) 的条件。若希望将结论封装为联合并集上的 `InFittingBall`，则可用已有误差界、共同定义域、有限阈值和距离对称性组装；这是可以补充的接口，不是正文这条推论遗漏的证明。

本次为源码与数学命题的语义审阅，未重新编译附件工程。

被审阅材料：Zhe Li（Glen Li / glenzli），[The Operator Evolution Theory](https://glenzli.com/books/oet/)，[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)。