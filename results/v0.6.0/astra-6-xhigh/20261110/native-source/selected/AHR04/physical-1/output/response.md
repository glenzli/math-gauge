**所给实现准确、完整地覆盖了正文推论 `h-93b9c20ea18b4e59` 明写的两条包含关系。** 在允许使用附件局部上界和辅助结论的前提下，没有发现需要补齐的证明缺口。

对应关系如下，三个声明均在 [path_guarantee_domains.lean](/private/tmp/math-gauge-astra-xhigh-20261110/sessions/AHR04/physical-1/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean:520) 中：

| 正文内容 | Lean 声明 |
|---|---|
| 单分量路径保证域之并包含于真实误差容限域 | `path_component_guarantee_union_subset_proxy_error` |
| 联合路径保证域之并包含于真实联合容限域 | `path_joint_guarantee_union_subset_proxy_error` |
| 保留全局可评估性、有限阈值及非空分量族等正文前提 | `path_guarantee_union_subset_proxy_error_text` |

定义和量词也相符：

- `path_component_sample` 是 \(S_j\cap U_q\)，路径可评估条件恰为这个集合非空。因而源码没有把无样本路径当作有效证书。
- 分量保证域展开后正是
  \[
  x\in U_q\ \land\
  D_{\mathbf L_q+\mathbf L^*,j}(x;S_{q,j})
       +\widehat\varepsilon_{q,j}\le\tau_j.
  \]
  矩阵、路径采样集和路径残差均使用同一个 \(q\)。
- 联合保证域写成“\(x\in U_q\)，且所有 \(j\in J\) 都满足上述预算”。在正文 \(J\ne\varnothing\) 的条件下，它与 \(\bigcap_{j\in J}U_{q,j}(\tau_j)\) 完全等价。
- `{x | ∃ q, … ∧ x ∈ …}` 正是正文受限并集的成员表达式。联合定理先选定同一个 \(q\)，再对所有 \(j\in J\) 给出误差界，量词顺序正确。

源码证明可以直接复核为以下论证。若 \(x\) 属于左侧并集，取其路径见证 \(q\)。保证域成员条件给出 \(x\in U_q\)，由 `path_domain_subset_source` 得到 \(x\in U\)。对于相应分量，
\[
d_j(\phi(x),\phi^\natural(x))
\le
D_{\mathbf L_q+\mathbf L^*,j}(x;S_{q,j})
+\widehat\varepsilon_{q,j}
\le\tau_j.
\]
第一步来自附件已有的路径局部上界，第二步来自保证域定义。代理与路径链之间的替换由 `hrep` 和 `path_chain_eq_represented_proxy_on_path` 支持。联合形式对所选路径上的每个 \(j\in J\) 重复此论证。这正是正文证明。

最终包装中的一些前提以 `have _ := …` 保留但未参与证明，**不构成覆盖不足**。例如，集合包含推理本身不需要阈值有限；路径可评估性已经蕴含相应全局可评估性。核心定理允许更弱的前提，包装定理再保留正文语境。目标定义域条件也没有遗漏：`TargetLipEnvelopeCertificate` 内含 \(V^*\subseteq\mathrm{dom}(\phi^\natural)\)，与 `hpathV` 配合即可使用。

需要区分结论范围：

- **源码已经证明**：被这些路径证书覆盖的每一点，满足指定分量的真实误差上界。
- **源码没有在这三个定理中声明**：保证域之并覆盖整个 \(U\)、包含关系是等式，或路径保证域必然大于全局证书保证域。这些也不是正文该推论的断言。
- **可自行补充的推论**：记联合保证域之并为 \(C_J\)，结合两算子的定义域条件、有限阈值和距离对称性，可以进一步封装为 `InFittingBall d target proxy C_J J tau`。若要把拟合域换成整个 \(U\)，还须另有 \(U\subseteq C_J\) 的覆盖条件。此封装不是当前实现完整覆盖正文所必需的。

本次进行了定义、命题及证明的源码语义核对，未重新编译工程。审阅对象为 Zhe Li（Glen Li / glenzli）的 [The Operator Evolution Theory](https://glenzli.com/books/oet/) 附件版本，采用 [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/) 许可。