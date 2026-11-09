**结论：两条包含关系及其证明正确；但全局定理封装有一处前提过强，严格说尚未覆盖正文的全部适用范围。** 如果额外假定所有可达路径均有 Lip 证书，则实现完整。

在 [path_guarantee_domains.lean](/private/tmp/math-gauge-sol61-comparison-20261109-01a1b190/xhigh/sessions/AHR02/physical-1/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean:520) 中，两个核心定理与正文的对应关系如下：

| 正文内容 | Lean 实现 |
|---|---|
| 分量保证域的受限路径并集 | `path_component_guarantee_union_subset_proxy_error` |
| 联合保证域的受限路径并集 | `path_joint_guarantee_union_subset_proxy_error` |
| 有限阈值、非空 \(J\) 等正文条件 | `path_guarantee_union_subset_proxy_error_text` |
| \(U_q,S_{q,j},\hat\varepsilon_{q,j}\) | `path_domain`、`path_component_sample`、`path_empirical_residual_upper` |
| \(\mathbf A_q=\mathbf L_q+\mathbf L^*\) | `fun i j => Lq q i j + Lstar i j` |

源码已证明的推理是完整的：从左侧成员关系提取一条合格路径 \(q\)，得到 \(x\in U_q\)，调用已有局部上界，
\[
d_j(c_q(x),\phi^\natural(x))
\le D_{\mathbf A_q,j}(x;S_{q,j})+\hat\varepsilon_{q,j}
\le\tau_j,
\]
再由网络表示得到 \(c_q(x)=\phi(x)\)，并由 \(U_q\subseteq U\) 得到右侧成员关系。联合形式使用**同一条路径**，对全部 \(j\in J\) 应用上述论证，没有交换存在量词与全称量词。

联合保证域的定义包含 \(x\in U_q\) 和全部分量不等式；在正文规定的 \(J\ne\varnothing\) 下，这正是各分量保证域的交集。核心定理允许更一般的阈值，最终包装保留有限性条件；这些条件未用于证明并不是漏洞。

不过，第 530、562、604 行的 `hLq` 都要求
\[
\forall q\in\mathcal P,\quad
\mathbf L_q\in\mathscr L(c_q)|_{U_q}.
\]
正文的分量并集只涉及 \(j\in I_{\mathrm{res}}(q)\) 的路径，联合并集只涉及 \(J\subseteq I_{\mathrm{res}}(q)\) 的路径。对不参与并集的路径，正文不需要 Lip 证书。源码因此增加了实际可能无法满足的要求。

以下是本次审阅补充的可复核例子，说明这一差异并非纯粹冗余。

取单分量空间
\[
X=\{\bot,a,b,c,r\}.
\]
非吸收点按 \(\{a\},\{b,c\},\{r\}\) 分成三类：同类距离为零，异类距离为一；非吸收点与 \(\bot\) 距离为无穷。它是离散度量的拉回并加入隔离吸收元，满足附件的全部扩展伪度量公理。

令 \(U=\{a,b,c\}\)，目标在所有非吸收点取值 \(a\)，代理满足
\[
\phi(a)=a,\qquad \phi(b)=a,\qquad \phi(c)=r,
\]
其余点映到 \(\bot\)。用两个均立即停止的节点表示代理：第一节点只处理 \(a\)，第二节点处理 \(b,c\)。两条路径域分别为
\[
U_{q_1}=\{a\},\qquad U_{q_2}=\{b,c\}.
\]

取样本 \(\{a\}\)、修正量零、阈值零。目标在 \(V^*=U\) 上具有零 Lip 证书，路径 \(q_1\) 也具有零 Lip 证书，其保证域就是 \(\{a\}\)。路径 \(q_2\) 无样本，故不参与正文并集。

但 \(q_2\) 不存在任何 Lip 证书，因为
\[
d(b,c)=0,\qquad d(c_{q_2}(b),c_{q_2}(c))=1.
\]
任意 \(L\in\mathrm{ENNReal}\) 都有 \(L\cdot0=0\)，包括 \(L=\top\)，所以要求 \(1\le L\cdot0\) 不可能成立。正文的有效路径保证仍可使用，现有全局封装却无法应用。这是**适用范围的反例**，不是对已证明包含关系的反例。

补齐只需弱化全局封装的证书前提：

- 分量形式：仅要求 \(j\in I_{\mathrm{res}}(q)\) 时该路径的 `IsLipMatrix` 成立。
- 联合形式：仅要求 \(J\subseteq I_{\mathrm{res}}(q)\) 时该路径的 `IsLipMatrix` 成立。

现有证明提取路径见证后已经取得相应可评估性条件，因此直接调用已有局部定理即可；不需要新的数学估计。这个弱化后的全局声明目前尚未在所给源码中出现。

最后，“全局拟合含义”指取并后仍满足真实误差界。源码没有证明并集覆盖整个 \(U\)、等于真实误差域，或与全局经验保证域存在固定包含次序；正文也没有声称这些，不能据此判为缺项。

正文及源码来源：Zhe Li（Glen Li / glenzli），[The Operator Evolution Theory](https://glenzli.com/books/oet/)，[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)。上述五点例与弱化方案为本次审阅补充，未新增 Lean 形式化。