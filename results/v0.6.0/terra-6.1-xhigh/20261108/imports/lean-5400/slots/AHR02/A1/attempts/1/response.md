**结论：两个并集包含式的方向和量词在 Lean 中是正确的，但正文包装定理对路径 Lip 证书的要求偏强。**它要求每一条可达路径都有合法证书，包括没有相应采样、因而不会进入左侧并集的路径。若正文语境本意也要求每条可达路径都有证书，那么现有实现完整覆盖这两个包含式；若按正文证明所需的较弱条件，只要求参与并集的路径有证书，现有最终定理还没有直接覆盖该情形。

源码已经证明的对应关系如下：

- 在 [path_sampling.lean](/private/tmp/math-gauge-v060-terra61-xhigh-20261108/sessions/AHR02/physical-1/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_sampling.lean:27) 中，路径采样集是 `sample j ∩ N.path_domain q.nodes`，路径可评估性就是这个交集非空，对应正文的 \(S_{q,j}\) 与 \(I_{\rm res}(q)\)。
- 在 [path_guarantee_domains.lean](/private/tmp/math-gauge-v060-terra61-xhigh-20261108/sessions/AHR02/physical-1/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean:26) 中，分量保证域和联合保证域分别对应 \(U_{q,j}\) 与 \(U_{q,J}\)。联合定义要求**同一条路径**同时满足所有 \(j\in J\) 的条件，与正文一致。
- 同文件的 `path_component_guarantee_union_subset_proxy_error` 和 `path_joint_guarantee_union_subset_proxy_error` 分别证明两个包含式；最终包装 `path_guarantee_union_subset_proxy_error_text` 同时保留正文的全局可评估性、有限阈值和 \(J\) 非空条件。证明从左侧取出路径见证，使用路径局部误差上界，并由路径域包含于 `N.U` 得到右侧的域条件。网络表示假设用于将路径链值换成代理值。
- 有些正文前提在证明中没有使用，例如有限阈值和 \(J\) 非空；这是因为包含式在更一般的条件下仍成立，不是错误。全局可评估性也可由参与并集的路径可评估性推出。

需要补齐的量词差异可复核地表述为：现有定理的 `hLq` 是

\[
\forall q\in\mathcal P,\qquad
\mathbf L_q\in\mathscr L(c_q)|_{U_q}.
\]

而分量包含式的证明只需要对满足 \(j\in I_{\rm res}(q)\) 的路径有该证书；联合包含式只需要对满足 \(J\subseteq I_{\rm res}(q)\) 的路径有该证书。这并非自动等价：扩展伪度量族允许不同点全分量零距，而算子可以把它们送到正距离的点。

例如，取单指标空间 \(X=\{\bot,a,b,c\}\)，令 \(d(a,b)=0\)，\(c\) 与 \(a,b\) 的距离均为 \(1\)，吸收元与其余点的距离为 \(\infty\)。构造一个两条路径、均立即终止的有限网络：

- 坏路径域为 \(\{a,b\}\)，其节点算子把 \(a\mapsto a\)、\(b\mapsto c\)；
- 好路径域为 \(\{c\}\)，其节点算子把 \(c\mapsto c\)。

两节点在其他输入上可取 \(\bot\)。取网络外延作为代理，恒等算子作为目标，\(U=V^*=\{a,b,c\}\)，采样集为 \(\{c\}\)，修正和阈值均为零。好路径可评估，有合法 Lip 证书，且 \(c\) 属于其零阈值保证域。坏路径没有样本，不参与正文并集；但它不可能有合法 Lip 矩阵，因为其输入距离为 \(0\)，输出距离为 \(1\)。即使矩阵系数取 \(\infty\)，在 `ENNReal` 中仍有 \(\infty\cdot0=0\)。

因此，上述实例满足参与并集的路径所需的局部条件，却无法满足现有最终定理的全路径 `hLq`。这是**前提覆盖不足**，不是现有包含式的反例。

补齐时可分别将两个全局定理的 `hLq` 改为带过滤条件的逐路径前提：分量版要求 `j ∈ path_evaluable_components … q → IsLipMatrix …`；联合版要求 `J ⊆ path_evaluable_components … q → IsLipMatrix …`。从并集成员取出路径和可评估性见证后，直接调用源码已有的对应局部定理即可。也可以给每个参与路径存在性地选择证书。该补充推导在此给出，**附件源码目前的最终包装没有以这个较弱前提声明**。

本次判断依据附件正文和源码声明及证明的静态审阅；没有修改文件，也没有重新运行 Lean 编译。

来源：Zhe Li（Glen Li / glenzli），[The Operator Evolution Theory](https://glenzli.com/books/oet/)，[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)。