**结论：以正文给定的路径 Lip 证书族和目标 Lip 包络证书为前提，所给实现准确、完整地覆盖了该推论的两条包含关系。**“全局”指把路径保证域合并；正文和源码都没有断言保证域覆盖整个 \(U\)。

本次核对的是数学含义与源码证明，未另行运行 Lean 编译。

关键实现见 [path_guarantee_domains.lean](/private/tmp/math-gauge-astra-xhigh-20261110/sessions/AHR02/physical-1/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean:520)，对应关系如下：

| 正文结论 | Lean 声明 |
|---|---|
| 分量保证域之并包含于真实分量误差区域 | `path_component_guarantee_union_subset_proxy_error` |
| 联合保证域之并包含于真实联合误差区域 | `path_joint_guarantee_union_subset_proxy_error` |
| 保留全局可评估性、有限阈值及 \(J\neq\varnothing\) 的正文版本 | `path_guarantee_union_subset_proxy_error_text` |

定义的对应也是准确的：

- `path_component_sample` 正是 \(S_j\cap U_q\)。路径可评估性定义为该交集非空，虽然没有再次写出 \(j\in I_{\mathrm{res}}\)，但它自动蕴含全局可评估性；`path_evaluable_subset_evaluable_components` 已证明这一点。
- 路径保证域使用的矩阵是 \(L_q+L^*\)，残差是对应路径采样上的残差上确界加同一个观测修正。`weighted_anchor_distance` 对整个加权和取同一锚点的下确界，没有改成各分量分别选锚点。
- 联合保证域展开为
  \[
  \{x\in U_q:\forall j\in J,\ 
    D_{A_q,j}(x;S_{q,j})+\hat\varepsilon_{q,j}\le\tau_j\}.
  \]
  在正文要求的 \(J\neq\varnothing\) 下，这恰好等于 \(\bigcap_{j\in J}U_{q,j}(\tau_j)\)。

证明可以直接复核。以联合形式为例，左侧成员给出**同一条路径** \(q\)，满足
\[
J\subseteq I_{\mathrm{res}}(q),\qquad x\in U_{q,J}(\boldsymbol\tau).
\]
因此 \(x\in U_q\subseteq U\)，而对每个 \(j\in J\)，局部上界及保证域定义给出
\[
d_j(c_q(x),\phi^\natural(x))
\le D_{A_q,j}(x;S_{q,j})+\hat\varepsilon_{q,j}
\le\tau_j.
\]
`path_chain_eq_represented_proxy_on_path` 再由 `hrep` 得到 \(c_q(x)=\phi(x)\)。这正是联合定理证明中的路径见证拆解、`path_domain_subset_source` 和最后的改写。分量形式则直接调用代理的路径分量误差界。**源码没有把“存在一条路径同时保证所有分量”误换成其他量词顺序。**

正文包装中的若干假设只写成 `have _ := ...`，不构成证明缺口。底层两个包含关系在允许无限阈值等更宽条件下仍成立；正文版本保留有限阈值和非空分量族，是为了符合正文适用范围。合法路径矩阵和目标包络仍由 `hLq`、`hLstar` 实质性提供，并没有被当作采样数据的自动结论。

需要区分源码结论与进一步封装：

- **源码已证明**：正文中的两条集合包含关系。
- **可补充但不是该推论的遗漏**：令联合保证域之并为 \(G_J\)，可以进一步封装成 `InFittingBall d target proxy G_J J tau`。目标定义域由目标包络得到；代理定义域由路径 Lip 证书及路径链等于代理得到；有限阈值已有假设，误差方向可用对称性调整。上述三个最终声明没有直接返回这一结构。
- **不能据此推出**：\(G_J=U\)、保证域等于真实误差区域，或路径保证域与另一套全局证书保证域之间必有某个包含方向。这些也不是正文该推论所声称的内容。

审阅对象为 Zhe Li（Glen Li / glenzli）《[The Operator Evolution Theory](https://glenzli.com/books/oet/)》所附版本，许可为 CC BY 4.0。