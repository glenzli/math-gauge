**两条并集包含式都已由 Lean 正确证明。** 若所有可达路径都已给出 Lip 证书，现有实现完整覆盖正文结论。若按正文的局部设定，只要求进入相应并集的路径有证书，Lean 的 `hLq` 前提偏强。差异在证书的量词范围，两个误差结论本身一致。[正文推论](source.md:242)

### 源码已证明的结论

- **分量形式。** `path_component_guarantee_union_subset_proxy_error` 用存在量词表示并集。成员见证给出一条可达路径 \(q\)、\(j\in I_{\mathrm{res}}(q)\) 和 \(x\in U_{q,j}(\tau_j)\)。证明由 \(U_q\subseteq U\) 得到 \(x\in U\)，再调用代理路径的局部上界，得到 \(d_j(\phi(x),\phi^\natural(x))\le\tau_j\)。[分量声明](formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean:520)
- **联合形式。** `path_joint_guarantee_union_subset_proxy_error` 先取得**同一条路径** \(q\)，再对每个 \(j\in J\) 应用局部上界。展开联合保证域得到 \(x\in U_q\) 且每个分量的证书上界都不超过对应阈值。对正文的非空 \(J\)，这恰好等价于 \(x\in\bigcap_{j\in J}U_{q,j}(\tau_j)\)。`path_chain_eq_represented_proxy_on_path` 将路径链的值改写为代理算子的值。[联合保证域](formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean:39) · [联合声明](formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean:552)

汇总声明 `path_guarantee_union_subset_proxy_error_text` 保留了正文的全局可评估性、有限阈值和 \(J\ne\varnothing\) 条件。两个核心证明可直接使用路径可评估性和逐点上界，因此无需在证明体中使用这些额外参数。三个声明均已用 Lean 4.29.1 检查通过，`#print axioms` 只列出 `propext`、`Classical.choice` 和 `Quot.sound`。[汇总声明](formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean:588)

### 只给并集所用路径提供证书时

正文在 \(j\in I_{\mathrm{res}}(q)\) 的局部设定下选取 \(\mathbf L_q\)。现有两个并集声明都要求 `hLq` 对**每条**可达路径成立，即使该路径的分量样本为空。这个额外要求一般无法从正文的局部数据推出。[正文的局部证书设定](source.md:87)

取单分量空间 \(X=\{\bot,a,b,c\}\)。非吸收点的距离是两类 \(\{a\}\)、\(\{b,c\}\) 上的离散距离，类内为 \(0\)，类间为 \(1\)，\(\bot\) 到其余点的距离为 \(\infty\)。令 \(U=V^*=\{a,b,c\}\)，目标在 \(U\) 上恒取 \(a\)。代理网络有两个终止节点，第一条路径域为 \(\{a\}\)，映射 \(a\mapsto a\)，第二条路径域为 \(\{b,c\}\)，映射 \(b\mapsto a,\ c\mapsto b\)。各节点在自身定义域外输出 \(\bot\)。

取样本 \(\{a\}\)，观测修正和阈值均为 \(0\)。目标和第一条路径都可取零 Lip 证书，第一条路径保证域为 \(\{a\}\)。第二条路径没有样本，且任何 Lip 系数 \(L\) 都必须对点对 \(b,c\) 满足 \(1\le L\cdot 0=0\)，即使 \(L=\infty\) 也不成立。因此正文所用路径的证书齐备，现有声明的全路径 `hLq` 却无法满足。

**补齐方式**是让分量版的 `hLq` 仅在 \(j\in I_{\mathrm{res}}(q)\) 时要求证书，联合版仅在 \(J\subseteq I_{\mathrm{res}}(q)\) 时要求证书。拆开并集成员见证时已经得到这项条件，随后可直接调用源码中的局部上界。这个较弱前提下的并集版本是可由现有引理推出的补充结论，附件中没有直接声明它。

审阅材料出自 Zhe Li（Glen Li / glenzli）的 *The Operator Evolution Theory*。[作品主页](https://glenzli.com/books/oet/) · [ORCID](https://orcid.org/0009-0006-6536-3453) · [源码仓库](https://gitlab.com/glenzli/oet-public) · [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)