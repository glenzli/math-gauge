## 结论

**所给全局定理的两个包含式是正确的，但其具名 Lean 包装定理的路径 Lip 假设比正文所需的条件强，因此没有直接覆盖正文在最弱路径局部假设下的全部情形。** 不过，附件中已经证明的路径局部上界足以推出正文的完整结论；缺少的只是按合格路径重新组装全局并集的证明，不需要新增数学假设。

若将正文额外理解为“预先为**每一条**可达路径都给定合法的 Lip 矩阵”，则这个量词差异不存在，`path_guarantee_union_subset_proxy_error_text` 与正文两式相符。

以下是对所给源码和证明的静态审阅；未另行运行 Lean 编译。

## 对应关系与源码已证明的内容

记 Lean 中 `N.U` 为正文的 \(U\)，`q : N.ReachablePath` 为 \(q\in\mathcal P\)。对应关系如下：

| 正文对象 | Lean 对象 |
|---|---|
| 路径域 \(U_q\) | `N.path_domain q.nodes` |
| 路径采样集 \(S_{q,j}\) | `path_component_sample N sample q j` |
| \(j\in I_{\rm res}(q)\) | `j ∈ path_evaluable_components N sample q` |
| 路径链 \(c_q\) | `N.path_chain q.nodes` |
| 路径残差 \(\hat\varepsilon_{q,j}\) | `path_empirical_residual_upper ... q j` |
| \(\mathbf A_q=\mathbf L_q+\mathbf L^*\) | `fun i j => Lq q i j + Lstar i j` |
| 分量保证域、联合保证域 | `path_component_empirical_guarantee_domain`、`path_joint_empirical_guarantee_domain` |

路径可评估性在 Lean 中定义为路径采样集非空；`path_evaluable_subset_evaluable_components` 已证明它蕴含全局可评估性。因此，与正文要求同时属于 \(I_{\rm res}\) 的写法一致。

正文的联合保证域是各分量保证域的交。Lean 将它写成“属于 \(U_q\)，且满足所有 \(j\in J\) 的不等式”。在正文及最终包装要求的 **\(J\ne\varnothing\)** 下，两种写法等价。

源码中的以下结论已经带有证明：

- `proxy_path_component_guarantee_error_bound`：单条路径、单个可评估分量的保证域给出代理与目标的误差上界。
- `proxy_path_joint_guarantee_error_bound`：单条路径上，对 \(J\subseteq I_{\rm res}(q)\) 的所有分量同时给出上界。
- `path_component_guarantee_union_subset_proxy_error` 和 `path_joint_guarantee_union_subset_proxy_error`：在其声明的全路径假设下，分别证明正文两个并集包含式。
- `path_guarantee_union_subset_proxy_error_text` 将两式合并，并保留正文的全局可评估性、有限阈值及 \(J\) 非空条件。这些条件在证明中未被使用，只说明 Lean 在这些方面证明了更一般的结论，并非错误。

此外，`hpathV : ∀ q, U_q ⊆ Vstar` 可由正文的 \(U\subseteq V^*\) 以及路径域覆盖 \(U\) 推出；它不是实质额外限制。有限采样等正文条件未在全局包装中全部重述，也不妨碍结论：路径局部上界只需其中实际用到的条件。

## 需要补充：Lip 证书的量词强度

正文先在 \(j\in I_{\rm res}(q)\) 的路径上取 \(\mathbf L_q\)，并集也只遍历这样的路径。就第一式而言，只需要

\[
\forall q,\quad j\in I_{\rm res}(q)
\Longrightarrow \mathbf L_q\in\mathscr L(c_q)|_{U_q}.
\]

联合式类似，只需要对满足 \(J\subseteq I_{\rm res}(q)\) 的路径有证书。但两个 Lean 全局并集定理都要求：

> `hLq : ∀ q : N.ReachablePath, IsLipMatrix ... (Lq q)`

即使某条路径没有任何相关采样，也必须有 Lip 证书。这个要求不能仅从附件中的网络定义推出。

### 可复核的例子

取唯一分量 \(I=\{j\}\)，令 \(X=\{\bot,a,b,c\}\)。在非吸收点上定义

\[
d(a,b)=0,\qquad d(a,c)=d(b,c)=1,
\]

自距为零，并令 \(\bot\) 与所有非吸收点距离为 \(\infty\)。这满足扩展伪度量公理。

令目标为恒等算子，代理 \(\phi\) 满足

\[
\phi(a)=a,\qquad \phi(b)=c,\qquad \phi(c)=c,\qquad
\phi(\bot)=\bot.
\]

构造一个每条路径均在首节点终止的两节点网络：

- \(a,b\) 走路径 \(q_u\)，节点算子为 \(\phi\)；
- \(c\) 走路径 \(q_s\)，节点算子为恒等算子。

于是 \(U_{q_u}=\{a,b\}\)、\(U_{q_s}=\{c\}\)，网络在 \(U=\{a,b,c\}\) 上表示 \(\phi\)。取 \(S_j=\{c\}\)、目标证书域 \(V^*=U\)、目标 Lip 常数 \(L^*=1\)，并令残差修正及阈值均为零。

此时只有 \(q_s\) 对 \(j\) 可评估；它是单点路径域，可取路径 Lip 常数零。正文包含式成立，左侧是 \(\{c\}\)，右侧是 \(\{a,c\}\)。

然而 \(q_u\) 上不存在任何扩展非负常数 \(L\) 作为 Lip 证书：在点对 \(a,b\) 上必须有

\[
1=d(\phi(a),\phi(b))
\le L\,d(a,b)=L\cdot0=0,
\]

矛盾；这也包括 \(L=\infty\)。因此，不能把正文相关路径上的证书自动扩张成 Lean 包装所要求的全路径证书。

### 如何补齐

无需修改定义。以分量式为例，对左侧成员拆出见证路径 \(q\)，此时已知 \(j\in I_{\rm res}(q)\)，故可使用该路径的局部 Lip 证书，再调用源码已有的 `proxy_path_component_guarantee_error_bound`；最后用 `N.path_domain_subset_source` 得到 \(x\in U\)。

联合式同理：拆出同一条满足 \(J\subseteq I_{\rm res}(q)\) 的路径，调用 `proxy_path_joint_guarantee_error_bound`。因此，**需自行补充的是较弱量词形式的全局组装声明及其证明**；路径级误差估计本身已在源码中证明。

## 范围提醒

正文与 Lean 都只证明“证书保证域的并集包含于真实误差容许域”，并未证明这些保证域覆盖整个 \(U\)，也未证明反向包含。上例中点 \(b\) 就未被保证，且其真实误差为 \(1\)。

正文随后的比较注也与附件辅助声明一致：同一矩阵下，`path_component_sample_subset_component` 和 `weighted_anchor_distance_mono_of_subset` 给出路径锚点距离不小于全局锚点距离；而路径残差上界不大于全局残差上界。两项方向相反，不能仅据此决定保证域包含方向，仍需逐点比较**总证书上界**。

---

材料归属：Zhe Li（Glen Li / glenzli），[The Operator Evolution Theory](https://glenzli.com/books/oet/)，[ORCID](https://orcid.org/0009-0006-6536-3453)，[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)。本答复为对附件的审阅，并补充了上述例子。