**两条包含关系及其证明逻辑都准确；但证书的量词范围需要区分。** 源码完整证明了“所有可达路径均已给定合法 Lip 矩阵”的版本。按正文只对参与并集的可评估路径取证书的表述，实现的前提偏强，适用范围尚不完全一致。

**源码已经证明的对应关系如下。**

| 正文结论 | Lean 声明 |
|---|---|
| 分量保证域并集包含于真实分量误差域 | `path_component_guarantee_union_subset_proxy_error` |
| 联合保证域并集包含于真实联合误差域 | `path_joint_guarantee_union_subset_proxy_error` |
| 保留有限阈值、全局可评估性及非空 \(J\) 的两式汇总 | `path_guarantee_union_subset_proxy_error_text` |

这三个声明位于 [path_guarantee_domains.lean](/private/tmp/math-gauge-sol61-comparison-20261109-01a1b190/max/sessions/AHR02/physical-1/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean:520)。

具体而言：

- `{x | ∃ q, j ∈ path_evaluable_components … q ∧ …}` 正是正文筛选路径后的并集；联合形式也保留了 \(J\subseteq I_{\rm res}(q)\)。
- 实际代入的矩阵为 `Lq q + Lstar`，残差为相同路径样本上的 `path_empirical_residual_upper`，没有换成全局样本或全局残差。
- 联合域定义为“\(x\in U_q\) 且每个 \(j\in J\) 满足子水平条件”。在正文的 \(J\ne\varnothing\) 前提下，它与 \(\bigcap_{j\in J}U_{q,j}\) 等价。这是展开定义即可复核的对应关系。
- 路径链与代理之间的转换已有 `path_chain_eq_represented_proxy_on_path` 证明，因此结论确实涉及 `proxy`，误差方向也与正文一致。

证明本身就是：从并集成员资格取出路径 \(q\)，再用局部上界得到
\[
d_j(\phi(x),\phi^\natural(x))
\le D_{\mathbf A_q,j}(x;S_{q,j})+\hat\varepsilon_{q,j}
\le\tau_j,
\]
并由 \(U_q\subseteq U\) 得到右侧的域条件。联合形式在同一个 \(q\) 上逐分量应用即可。包装定理中的部分前提没有参与证明，并不构成证明缺口：核心包含关系允许更一般的阈值，而路径可评估性本来就蕴含全局可评估性。

**完整性上的差异是 `hLq` 要求所有路径都有证书。**

三个声明均要求
```lean
∀ q : N.ReachablePath,
  IsLipMatrix d (N.path_chain q.nodes) (N.path_domain q.nodes) (Lq q)
```
正文却只为可评估路径定义相应保证域。未采样、未参与并集的路径，其 Lip 证书并非该包含关系所需。这一额外要求不能由现有定义自动补出。

以下是我补充的数学反例，附件没有相应的 Lean 反例声明。

取单分量空间
\[
X=\{\bot,s,a,b\}.
\]
自距为零，距离对称；非吸收点之间规定
\[
d(a,b)=0,\qquad d(s,a)=d(s,b)=1,
\]
所有非吸收点到 \(\bot\) 的距离均为 \(\infty\)。这满足扩展伪度量公理：非吸收部分是把 \(\{a,b\}\) 看作一个零距类的两点离散距离。

令 \(U=\{s,a,b\}\)，并规定：

| 输入 | \(s\) | \(a\) | \(b\) |
|---|---|---|---|
| 目标 \(\phi^\natural\) | \(s\) | \(s\) | \(s\) |
| 代理 \(\phi\) | \(s\) | \(a\) | \(s\) |

两算子均保持 \(\bot\)。建立两个节点、无转移的有限网络：入口按 \(\{s\}\) 和 \(\{a,b\}\) 分流，各节点取代理在对应块上的限制，块外映到 \(\bot\)。于是两条可达路径域分别为
\[
U_{q_0}=\{s\},\qquad U_{q_1}=\{a,b\},
\]
且网络表示该代理。

取样本 \(\{s\}\)、修正量零、阈值零。目标在 \(V^*=U\) 上有零 Lip 矩阵；唯一可评估路径 \(q_0\) 也有零 Lip 矩阵，其残差和锚点距离均为零。因此正文的并集为 \(\{s\}\)，包含关系成立。

但未采样路径 \(q_1\) **不存在任何 Lip 系数**：其点对 \(a,b\) 要求
\[
1=d(\phi(a),\phi(b))
\le L\,d(a,b)=L\cdot0=0.
\]
即使 \(L=\infty\)，附件使用的 `ENNReal` 仍有 \(\infty\cdot0=0\)。因此当前 Lean 定理无法应用于这个只有参与路径具备所需证书的情形。

**补齐方式是将证书前提限制到参与路径：**

- 分量形式：仅要求 \(j\in I_{\rm res}(q)\) 时具有该路径的 Lip 证书；
- 联合形式：仅要求 \(J\subseteq I_{\rm res}(q)\) 时具有该路径的 Lip 证书。

现有证明取出 `hj` 或 `hJ` 后即可使用这些条件，后续证明无需改变。这个放宽后的推广需要另外补充，源码当前没有证明。另一种处理是明确在正文增加“预先为全部可达路径给定合法 Lip 证书族”；在这一加强语境下，现有实现与两条包含关系完整对应。

本次为语义审阅，未修改或重新编译附件。

所审材料：Zhe Li（Glen Li / glenzli），[The Operator Evolution Theory](https://glenzli.com/books/oet/)，[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)。上述范围分析与反例为本次补充。