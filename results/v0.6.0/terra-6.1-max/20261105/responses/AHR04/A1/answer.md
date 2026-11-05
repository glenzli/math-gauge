## 结论

**就正文推论 #h-93b9c20ea18b4e59 的两条集合包含而言，所给 Lean 实现准确且完整。** 两个分支分别证明了分量保证域之并和联合保证域之并包含于相应的真实误差容许区域；合并包装定理也保留了正文的非空分量族与有限阈值前提。

这里的“全局拟合含义”是指：**路径证书之并内的点**满足误差界。它并不声称证书之并覆盖整个输入域，也不声称集合包含可以反向。

以下判断基于附件中展示的源码及题目允许使用的辅助声明；未另行运行 Lean 编译。

## 正文与 Lean 的对应关系

| 正文对象或条件 | Lean 对应 |
|---|---|
| 目标 \(\phi^\natural\)、代理 \(\phi\)、输入域 \(U\) | `target`、`proxy`、`N.U` |
| 可达路径 \(q\)、路径域 \(U_q\)、路径链 \(c_q\) | `N.ReachablePath`、`N.path_domain q.nodes`、`N.path_chain q.nodes` |
| 网络表示 \(\phi_{\mathcal N}\equiv_U\phi\) | `N.represents proxy` |
| 路径采样 \(S_{q,j}=S_j\cap U_q\) | `path_component_sample N sample q j` |
| 路径可评估集 \(I_{\rm res}(q)\) | `path_evaluable_components N sample q` |
| 路径残差上界 \(\hat\varepsilon_{q,j}\) | `path_empirical_residual_upper ... q j` |
| 路径分量、联合保证域 | `path_component_empirical_guarantee_domain`、`path_joint_empirical_guarantee_domain` |
| \(\mathbf A_q=\mathbf L_q+\mathbf L^*\) | `fun i j => Lq q i j + Lstar i j` |
| 对有相应采样的路径取并 | 集合构造式中的 `∃ q`，并要求 `j ∈ path_evaluable_components ... q` 或 `J ⊆ path_evaluable_components ... q` |

路径可评估意味着全局可评估，这一点源码由 `path_evaluable_subset_evaluable_components` 证明。因此，Lean 对路径可评估性的表达与正文中先要求 \(j\in I_{\rm res}\)、再要求 \(S_{q,j}\ne\varnothing\) 一致。

联合保证域有一个值得说明的**表示差异**：Lean 将其展开为“\(x\in U_q\)，且对每个 \(j\in J\) 满足该分量的不等式”；正文写成各分量保证域的交。由于正文及最终包装定理要求 \(J\ne\varnothing\)，两种写法相等：从交中任选一个分量即可得到 \(x\in U_q\)，其余条件逐项对应。这个等价性是上述定义的直接集合论推论；附件中不必将它作为独立定理使用。

## 源码已证明什么

`path_component_guarantee_union_subset_proxy_error` 正是分量形式的包含。其证明取左侧见证 \(q\)，然后：

1. 由路径保证域成员资格得到 \(x\in U_q\)，再由 `N.path_domain_subset_source` 得到 \(x\in N.U\)；
2. 由 `proxy_path_component_guarantee_error_bound` 得到
   \[
   d_j(\phi(x),\phi^\natural(x))\le \tau_j.
   \]

`path_joint_guarantee_union_subset_proxy_error` 对联合形式做同样的事。它使用的是**同一条见证路径**满足 \(J\subseteq I_{\rm res}(q)\)，随后对每个 \(j\in J\) 应用路径局部上界。

最后，`path_guarantee_union_subset_proxy_error_text` 将两项合并，并保留正文前提。它要求在参与相关并集的路径上有合法路径 Lip 矩阵；这正是定义和使用相应路径证书所需的数据。`hpathV` 要求各路径域包含于 `Vstar`，由正文的 \(U\subseteq V^*\) 和路径域包含于 \(U\) 可得。

包装中的全局可评估性、阈值有限性及 \(J\) 非空性在包含证明体中没有被使用，并不造成缺口：底层集合包含定理在这些方面更一般，而包装保留了正文的使用语境。

Lean 的残差和锚点距离定义在空采样上也有格论意义下的总值；正文则只在路径可评估时使用这些证书。目标定理的左侧明确筛选了路径可评估性，所以这种总值化不会把正文未定义的空采样路径错误地纳入结论。

## 需要区分的后续推论

源码的目标定理直接给出的是**误差区域的集合包含**，不是一个单独打包的 `InFittingBall` 结论。若需要后一种接口，可以补充一个简单包装：以左侧并集为拟合域，使用已证明的包含、`N.represents proxy`、目标 Lip 证书给出的定义域条件、有限阈值，以及测距对称性，构造 `InFittingBall`。这不是正文所列两条包含的缺失分支。

同样，若要推出在整个 \(U\) 上拟合，还必须另有“该路径保证域之并覆盖 \(U\)”的条件；正文和源码均未作此断言。事实上，包含可能严格：例如令一个分量的底层非吸收部分为实数、距离为绝对值，目标与代理都取恒等算子，网络只有一条恒等路径，样本为 \(\{0\}\)，修正为零，并选 \(L_q=L^*=1\)、\(\tau=1\)。此时真实误差在整个 \(U=\mathbb R\) 上为零，而该证书只保证 \(2|x|\le1\) 的点。

---

**材料归属：** Zhe Li（Glen Li / glenzli），[The Operator Evolution Theory](https://glenzli.com/books/oet/)，[ORCID](https://orcid.org/0009-0006-6536-3453)，[公共源码](https://gitlab.com/glenzli/oet-public)，[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)。以上是对附件的审阅与重述，未修改附件。