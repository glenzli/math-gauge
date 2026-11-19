**附件的 Lean 实现准确、完整地证明了“路径保证域的全局拟合含义”。** 正文的单分量包含式和联合包含式各有独立定理，`path_guarantee_union_subset_proxy_error_text` 给出二者的合取。两式右端都是 \(U\) 中满足**真实代理–目标误差**阈值的点集。[正文推论](/private/tmp/math-gauge-astra62-max-20261119/sessions/AHR04/physical-1/work/source.md:242) · [Lean 总定理](/private/tmp/math-gauge-astra62-max-20261119/sessions/AHR04/physical-1/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean:590)

1. **单分量形式。** Lean 用存在一条可达路径 `q` 表达属于路径并集。筛选条件 `j ∈ path_evaluable_components N sample q` 恰好表示 \(S_{q,j}=S_j\cap U_q\ne\varnothing\)。取出这条路径后，保证域成员条件给出 \(x\in U_q\subseteq U\)。路径局部上界与保证域的阈值条件依次给出
   \[
   d_j(c_q(x),\phi^\natural(x))
   \le D_{\mathbf L_q+\mathbf L^*,j}(x;S_{q,j})+\hat\varepsilon_{q,j}
   \le \tau_j .
   \]
   网络表示假设 `hrep` 给出 \(c_q(x)=\phi(x)\)，因此这个界确实适用于代理算子 \(\phi\)。[路径可评估性](/private/tmp/math-gauge-astra62-max-20261119/sessions/AHR04/physical-1/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_sampling.lean:59) · [路径链与代理的等式](/private/tmp/math-gauge-astra62-max-20261119/sessions/AHR04/physical-1/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_sampling.lean:220) · [单分量包含式](/private/tmp/math-gauge-astra62-max-20261119/sessions/AHR04/physical-1/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean:520)

2. **联合形式。** 源码先取出**同一条**满足 \(J\subseteq I_{\rm res}(q)\) 的路径 \(q\)。联合保证域的成员条件展开为 \(x\in U_q\)，且每个 \(i\in J\) 的路径证书上界都不超过 \(\tau_i\)。对非空 \(J\)，这恰好等价于正文的 \(x\in\bigcap_{i\in J}U_{q,i}(\tau_i)\)。证明随后固定任意 \(i\in J\)，在这条路径上应用 `path_joint_guarantee_error_bound`，再用 \(c_q(x)=\phi(x)\) 改写，得到所要求的全部分量界。[联合保证域定义](/private/tmp/math-gauge-astra62-max-20261119/sessions/AHR04/physical-1/work/formal_oet/vol_03/ch_12_residuals_and_substitution/guarantee_domains.lean:35) · [联合包含式](/private/tmp/math-gauge-astra62-max-20261119/sessions/AHR04/physical-1/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean:553)

总定理显式保留了全局可评估性、\(J\) 非空和所选阈值有限等正文条件。证明直接调用前提更弱的两个定理，因此这些条件虽未参与最后一步推导，正文的两条包含式均无需补证。我用 Lean 4.29.1 编译了目标模块，并核对了上述三个定理的公理依赖，均只有 `propext`、`Classical.choice` 和 `Quot.sound`。

原文与形式化出自 Zhe Li（Glen Li / glenzli）的 *The Operator Evolution Theory*，卷 03 第 14 章。[作品主页](https://glenzli.com/books/oet/) · [作者 ORCID](https://orcid.org/0009-0006-6536-3453) · [公共源码](https://gitlab.com/glenzli/oet-public) · [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)