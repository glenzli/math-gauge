**结论：所给实现准确、完整地覆盖正文推论 `h-93b9c20ea18b4e59` 的两条集合包含关系，无须补充数学假设或证明。** 我使用附件指定的 Lean 4.29.1，编译了目标文件及其附件依赖，共 43 个模块，全部通过；未修改附件或新增 Lean 源码。

在 [path_guarantee_domains.lean](/private/tmp/math-gauge-sol61-comparison-20261109-01a1b190/xhigh/sessions/AHR04/physical-1/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean:520) 中，对应关系如下：

| 正文结论 | Lean 声明 |
|---|---|
| 分量保证域的并集包含于真实分量容限区域 | `path_component_guarantee_union_subset_proxy_error` |
| 联合保证域的并集包含于真实联合容限区域 | `path_joint_guarantee_union_subset_proxy_error` |
| 保留正文的可评估性、有限阈值、非空分量族前提，同时给出两者 | `path_guarantee_union_subset_proxy_error_text` |

定义和量词也对应准确：

- `N.ReachablePath`、`N.path_domain q.nodes`、`N.path_chain q.nodes` 分别对应 \(\mathcal P,U_q,c_q\)。
- 路径采样、路径可评估分量、路径残差分别采用 `path_component_sample`、`path_evaluable_components`、`path_empirical_residual_upper`；传播矩阵明确取为 \(\mathbf L_q+\mathbf L^*\)。
- `{x | ∃ q, 筛选条件 ∧ x ∈ 保证域}` 正是正文的受条件限制的并集。
- 联合保证域展开为
  \[
  x\in U_q\ \land\
  \forall j\in J,\quad
  D_{\mathbf A_q,j}(x;S_{q,j})+\hat\varepsilon_{q,j}\le\tau_j.
  \]
  在正文的 \(J\ne\varnothing\) 条件下，这恰好等于各分量保证域的交集。路径见证 \(q\) 位于分量全称量词之外，保留了正文“同一路径上同时控制所有分量”的要求。

证明可以直接复核。取左侧成员的路径见证 \(q\)，保证域成员资格给出 \(x\in U_q\) 及证书预算不超过阈值。源码调用已有局部上界得到
\[
d_j(\phi(x),\phi^\natural(x))
\le D_{\mathbf A_q,j}(x;S_{q,j})+\hat\varepsilon_{q,j}
\le\tau_j,
\]
再用 `path_domain_subset_source` 得到 \(x\in U\)。联合分支对每个 \(j\in J\) 应用同一论证。代理值与路径链值的替换由已有的 `path_chain_eq_represented_proxy_on_path` 支持，最终误差确实针对 `proxy`。

前提处理没有隐藏缺口。`hpathV` 对所有路径要求 \(U_q\subseteq V^*\)，结合已有路径域覆盖，等价于正文的 \(U\subseteq V^*\)。`hLq` 要求相关路径具有 Lip 证书，与局部保证域的设定一致。核心定理允许任意扩展阈值、任意分量集合，因此封装中部分正文前提未参与证明；这是有效推广。采样有限性在这一步包含关系中也无需使用。

需要区分的是：**源码已证明的全局范围是这些保证域的并集。** 若要声称整个 \(U\) 上均满足容限，还需另外证明该并集覆盖 \(U\)；若要比较它与使用全局样本构造的经验保证域的大小，还需另给逐点证书上界比较。这些都不是正文两条包含关系所承诺的结论，因而不构成本命题的实现遗漏。

材料来源：Zhe Li（Glen Li / glenzli），[The Operator Evolution Theory](https://glenzli.com/books/oet/)，[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)。