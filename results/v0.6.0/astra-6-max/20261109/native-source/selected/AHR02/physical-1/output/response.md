**已有证明正确，但最终汇总定理加强了前提：它要求所有可达路径都有合法 Lip 矩阵，包括没有进入并集的路径。按正文仅对参与并集的路径使用证书的范围，尚不能认定为完整同形实现。** 若正文另行约定“所有可达路径均已配备合法 Lip 证书”，则现有实现完整覆盖两个包含式。

以下只审阅正文 h-93b9c20ea18b4e59。

[两个汇总定理及最终包装](/private/tmp/math-gauge-astra-max-20261109/sessions/AHR02/physical-1/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean:520) 的结论对应准确：

| 正文结论 | Lean 声明 |
|---|---|
| 分量保证域之并包含于真实分量容差域 | `path_component_guarantee_union_subset_proxy_error` |
| 联合保证域之并包含于真实联合容差域 | `path_joint_guarantee_union_subset_proxy_error` |
| 保留有限阈值、全局可评估性及非空 \(J\) | `path_guarantee_union_subset_proxy_error_text` |

其中，`{x | ∃ q, 条件 q ∧ x ∈ 保证域 q}` 正是受条件筛选的并集。联合分支要求**同一条路径**满足 `J ⊆ path_evaluable_components … q`，与正文一致。Lean 的联合保证域写成
\[
x\in U_q\ \land\ \forall j\in J,\ 
D_{\mathbf A_q,j}(x;S_{q,j})+\hat\varepsilon_{q,j}\le\tau_j,
\]
在正文的 \(J\ne\varnothing\) 条件下，恰好等于各分量保证域的交集。

证明也对应正文：取并集中的路径见证，调用路径局部误差界，利用网络表示把路径链输出替换为代理输出，再由 \(U_q\subseteq U\) 得到右侧成员关系。`_text` 中若干条件未参与证明不构成错误；这两个包含式本身允许更一般的阈值和采样情形。

实质差异在于[全路径 `hLq` 条件](/private/tmp/math-gauge-astra-max-20261109/sessions/AHR02/physical-1/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean:530)：
\[
\forall q\in\mathcal P,\qquad
\mathbf L_q\in\mathscr L(c_q)|_{U_q}.
\]
三个最终声明都采用这个条件。而[正文的局部设定](/private/tmp/math-gauge-astra-max-20261109/sessions/AHR02/physical-1/work/source.md:89)先限定 \(j\in I_{\mathrm{res}}(q)\)，随后才选择该路径的证书；推论的并集也明确排除了不可评估路径。它不需要被排除路径具有 Lip 证书。

这个前提强化不是无害的。下面给出本次审阅补充的可复核模型。

取单分量 \(I=\{j\}\)，
\[
X=\{\bot,a,b,c\},\qquad U=V^*=\{a,b,c\}.
\]
定义对称距离，自距为零，并令
\[
d(a,b)=0,\qquad d(a,c)=d(b,c)=1,\qquad
d(x,\bot)=\infty\quad(x\ne\bot).
\]
非吸收部分是把两类 \(\{a,b\}\)、\(\{c\}\) 赋予离散距离得到的伪度量；加入无限远的吸收元后，仍满足附件的全部扩展伪度量公理。

两个算子都固定 \(\bot\)，其余取值为：

| 输入 | \(a\) | \(b\) | \(c\) |
|---|---:|---:|---:|
| 目标 \(\phi^\natural\) | \(c\) | \(c\) | \(c\) |
| 代理 \(\phi\) | \(a\) | \(c\) | \(c\) |

构造两个节点、执行一步即停止的网络：输入 \(c\) 进入算子为 \(\phi^\natural\) 的节点，输入 \(a,b\) 进入算子为 \(\phi\) 的节点。因此两条路径的域为
\[
U_{q_0}=\{c\},\qquad U_{q_1}=\{a,b\}.
\]
两节点均可达、定义域非空，深度界为 \(1\)，且该网络在 \(U\) 上表示代理 \(\phi\)。

取
\[
S_j=\{c\},\quad \delta_{o,j}=0,\quad \tau_j=0,\quad
\mathbf L^*=0.
\]
目标常值，故目标证书合法。只有 \(q_0\) 可评估，它可取 \(\mathbf L_{q_0}=0\)，其路径残差与锚点距离均为零。因此正文的包含式在此成为
\[
\{c\}\subseteq\{b,c\}.
\]
取 \(J=\{j\}\)，联合式也一样成立。

但是 \(q_1\) **不存在任何合法 Lip 矩阵**。单分量矩阵是标量 \(L\)，其合法性要求
\[
1=d(c_{q_1}(a),c_{q_1}(b))
\le L\,d(a,b)=L\cdot0=0,
\]
矛盾。即使取 \(L=\infty\) 也无济于事，因为 `ENNReal` 中 \(\infty\cdot0=0\)。

因此，这个模型满足参与并集的路径所需的全部条件，却无法满足现有汇总定理的 `hLq`。这里的反例针对**额外前提的可补出性**，并不否定正文的包含式。

补齐可以直接复用现有局部定理，将两个分支的证书假设分别放宽为
\[
\begin{aligned}
&\forall q,\quad j\in I_{\mathrm{res}}(q)
 \Longrightarrow \mathbf L_q\in\mathscr L(c_q)|_{U_q},\\
&\forall q,\quad J\subseteq I_{\mathrm{res}}(q)
 \Longrightarrow \mathbf L_q\in\mathscr L(c_q)|_{U_q}.
\end{aligned}
\]
取出并集见证 \(q\) 时，已经同时取得相应筛选条件；由此取得该路径的证书，再调用源码已有的 `proxy_path_component_guarantee_error_bound` 或 `proxy_path_joint_guarantee_error_bound` 即可。无需新增误差估计。

所以应区分：**源码已经给出了全路径证书假设下的两个包含式，以及补齐所需的局部定理；上述筛选路径版本的汇总论证和四点模型是本次补充。** “全局拟合含义”在这里也只指并集上的误差保证，并未断言这些保证域覆盖整个 \(U\)。

材料来源：Zhe Li（Glen Li / glenzli），[The Operator Evolution Theory](https://glenzli.com/books/oet/)，[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)。本次未修改附件或新增 Lean 源码。