**两个包含式都已在 Lean 中证明，结论与正文一致。** 在每条可达路径均给定有效 Lip 矩阵的设定下，覆盖完整。若按正文的局部构造，只要求参与相应并集的路径具备 Lip 证书，现有全局声明的 `hLq` 前提更强。这个较弱前提下的版本可以直接由附件中的局部上界推出。[正文推论](/private/tmp/math-gauge-sol62-max-20261118/sessions/AHR02/physical-1/work/source.md:242)

### 源码已证明的内容

- 分量包含式对应 `path_component_guarantee_union_subset_proxy_error`。左侧的 `∃ q` 同时要求 \(j\in I_{\mathrm{res}}(q)\) 和 \(x\in U_{q,j}(\tau_j)\)。右侧给出 \(x\in U\) 及该点的真实误差界。
- 联合包含式对应 `path_joint_guarantee_union_subset_proxy_error`。左侧用**同一条路径**满足 \(J\subseteq I_{\mathrm{res}}(q)\) 和 \(x\in U_{q,J}(\boldsymbol\tau)\)。展开联合保证域，在 \(J\ne\varnothing\) 时恰是正文中各分量保证域的交集。
- `path_guarantee_union_subset_proxy_error_text` 将两式合并，并显式保留正文的全局可评估性、有限阈值和 \(J\ne\varnothing\) 条件。两条核心证明可分别使用。[Lean 声明](/private/tmp/math-gauge-sol62-max-20261118/sessions/AHR02/physical-1/work/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean:520)

两条证明都从左侧成员取出路径 \(q\)，由 \(x\in U_q\subseteq U\) 得到右侧的域约束，再用路径局部保证界及 \(c_q(x)=\phi(x)\) 得到真实误差界。局部保证域使用的正是 \(S_j\cap U_q\)、矩阵 \(L_q+L^*\) 和该路径的残差上确界加观测修正。三条声明均通过 Lean 4.29.1 检查，`#print axioms` 仅列出 `propext`、`Classical.choice` 和 `Quot.sound`。

### 较弱前提下如何补齐

从并集取出见证 \(q\) 时，已经取得该分支的路径可评估条件。因此，分量式只需在 \(j\in I_{\mathrm{res}}(q)\) 时要求 \(L_q\) 合法，联合式只需在 \(J\subseteq I_{\mathrm{res}}(q)\) 时要求 \(L_q\) 合法。用这个条件取得见证路径的证书，再调用原有局部引理，两条包含式的证明即成立。这是从现有源码可推得的放宽版本，现有全局声明仍使用全路径前提。[正文的局部证书设定](/private/tmp/math-gauge-sol62-max-20261118/sessions/AHR02/physical-1/work/source.md:89)

这个前提差异可以用单分量例子复核。取非吸收点 \(a,b,c\)，令 \(d(a,b)=0\)、\(d(a,c)=d(b,c)=1\)，吸收元与其余点的距离为 \(+\infty\)。目标取恒等算子。代理网络有两条单节点终止路径，一条在 \(\{c\}\) 上固定 \(c\)，另一条在 \(\{a,b\}\) 上把 \(a,b\) 分别送到 \(a,c\)。样本只取 \(\{c\}\)。进入并集的路径有合法 Lip 矩阵，可取零矩阵。未采样的路径把零距点对送成距离为 \(1\) 的点对，任何 Lip 系数都无法满足 \(1\le L\cdot 0\)，包括 \(L=+\infty\)。因此，只给参与并集的路径提供证书，确实不能推出源码当前的全路径 `hLq`。

审阅材料出自 Zhe Li（Glen Li / glenzli）的 *The Operator Evolution Theory*。[ORCID](https://orcid.org/0009-0006-6536-3453) · [作品主页](https://glenzli.com/books/oet/) · [公开源码](https://gitlab.com/glenzli/oet-public) · [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)