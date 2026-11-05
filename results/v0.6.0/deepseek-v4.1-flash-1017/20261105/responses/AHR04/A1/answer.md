## 结论

针对正文锚点 **h-93b9c20ea18b4e59（路径保证域的全局拟合含义）**，所给 Lean 实现 **准确覆盖了分量形式和联合形式**，且本地局部上界 h-4b5219aa3a3bbdad 以及辅助定义也已接入。未发现需要新增数学定理才能补齐的逻辑缺口。

我实际构建了相关模块：

```text
lake build +formal_oet.vol_03.ch_14_empirical_network_fitting.path_guarantee_domains
Build completed successfully (3341 jobs)
```

相关模块中未发现 `sorry`/`admit`。因此以下“源码已证明”的判断是指这些声明在所给 Lean 源码中已有证明项，并且构建通过。

---

## 一、正文命题与 Lean 声明对应

正文中的路径局部对象与 Lean 中的对应关系为：

| 正文对象 | Lean 声明 |
|---|---|
| \(S_{q,j}=S_j\cap U_q\) | `path_component_sample N sample q j` |
| \(I_{\mathrm{res}}(q)\) | `path_evaluable_components N sample q` |
| \(\widehat\varepsilon_{q,j}\) | `path_empirical_residual_upper d target N sample delta_o q j` |
| \(U_{q,j}(\tau_j)\) | `path_component_empirical_guarantee_domain d A N sample q j eps tau` |
| \(U_{q,J}(\boldsymbol\tau)\) | `path_joint_empirical_guarantee_domain d A N sample q J eps tau` |
| h-4b5219 路径局部上界 | `path_local_empirical_upper`、`proxy_path_local_empirical_upper` |
| h-93 分量形式 | `path_component_guarantee_union_subset_proxy_error` |
| h-93 联合形式 | `path_joint_guarantee_union_subset_proxy_error` |
| 正文前提包装 | `path_guarantee_union_subset_proxy_error_text` |

其中核心定义在：

- `path_sampling.lean`：
  - `path_component_sample`
  - `path_evaluable_components`
  - `path_empirical_residual_upper`
  - `path_chain_eq_represented_proxy_on_path`
- `path_guarantee_domains.lean`：
  - `path_component_empirical_guarantee_domain`
  - `path_joint_empirical_guarantee_domain`
  - `path_local_empirical_upper`
  - `path_component_guarantee_error_bound`
  - `path_joint_guarantee_error_bound`
  - 最终两个 union inclusion 定理。

---

## 二、逐层对应关系

### 1. 路径分量保证域

Lean 中：

```lean
def path_component_empirical_guarantee_domain
    ...
    (q : N.ReachablePath) (j : I) (eps tau : ENNReal) : Set X :=
  empirical_component_guarantee_domain d A (N.path_domain q.nodes)
    (path_component_sample N sample q j) j eps tau
```

展开后就是：

\[
\{x\in U_q:
D_{A,j}(x;S_{q,j})+\varepsilon\le \tau\}.
\]

这正是正文的 \(U_{q,j}(\tau_j)\)，其中 \(U_q\) 是 `N.path_domain q.nodes`，\(S_{q,j}\) 是 `path_component_sample`。

### 2. 路径联合保证域

`path_joint_empirical_guarantee_domain` 展开为：

\[
\{x\in U_q:
\forall j\in J,\quad
D_{A,j}(x;S_{q,j})+\varepsilon_j\le \tau_j\}.
\]

这与正文的

\[
U_{q,J}(\boldsymbol\tau)=\bigcap_{j\in J}U_{q,j}(\tau_j)
\]

一致。

### 3. 路径局部上界 h-4b5219

`path_local_empirical_upper` 的结论是：

\[
d_j(c_q(x),\phi^\natural(x))
\le
D_{\mathbf L_q+\mathbf L^*,j}(x;S_{q,j})
+\widehat\varepsilon_{q,j}.
\]

这里：

- `N.path_chain q.nodes` 对应 \(c_q\)；
- `Lq` 对应 \(\mathbf L_q\)；
- `Lstar` 对应 \(\mathbf L^*\)；
- `(fun i j => Lq i j + Lstar i j)` 对应 \(\mathbf A_q=\mathbf L_q+\mathbf L^*\)；
- `path_empirical_residual_upper` 对应 \(\widehat\varepsilon_{q,j}\)。

随后 `proxy_path_local_empirical_upper` 使用

```lean
path_chain_eq_represented_proxy_on_path
```

把 \(c_q(x)=\phi(x)\) 代回，得到正文中的代理形式。

### 4. 最终全局包含关系

分量形式定理：

```lean
theorem path_component_guarantee_union_subset_proxy_error
    ...
    : {x | ∃ q,
        j ∈ path_evaluable_components N sample q ∧
        x ∈ path_component_empirical_guarantee_domain ... τ}
      ⊆
      {x | x ∈ N.U ∧
        d j (proxy.func x) (target.func x) ≤ τ}
```

就是正文的

\[
\bigcup_{\substack{q\in\mathcal P\\ j\in I_{\mathrm{res}}(q)}}
U_{q,j}(\tau_j)
\subseteq
\{x\in U:\ d_j(\phi(x),\phi^\natural(x))\le \tau_j\}.
\]

联合形式定理：

```lean
theorem path_joint_guarantee_union_subset_proxy_error
    ...
    : {x | ∃ q,
        J ⊆ path_evaluable_components N sample q ∧
        x ∈ path_joint_empirical_guarantee_domain ... τ}
      ⊆
      {x | x ∈ N.U ∧
        ∀ j : I, j ∈ J →
          d j (proxy.func x) (target.func x) ≤ τ j}
```

对应正文的

\[
\bigcup_{\substack{q\in\mathcal P\\ J\subseteq I_{\mathrm{res}}(q)}}
U_{q,J}(\boldsymbol\tau)
\subseteq
\{x\in U:\forall j\in J,\ d_j(\phi(x),\phi^\natural(x))\le\tau_j\}.
\]

---

## 三、证明覆盖情况

正文 h-93 的证明逻辑是：

1. 若 \(x\) 属于左侧，则存在路径 \(q\)，使 \(j\in I_{\mathrm{res}}(q)\) 且 \(x\in U_{q,j}(\tau_j)\)；
2. 由 h-4b5219 得到
   \[
   d_j(\phi(x),\phi^\natural(x))
   \le D_{\mathbf A_q,j}(x;S_{q,j})+\widehat\varepsilon_{q,j};
   \]
3. 再由 \(x\in U_{q,j}(\tau_j)\) 得到
   \[
   D_{\mathbf A_q,j}(x;S_{q,j})+\widehat\varepsilon_{q,j}\le\tau_j;
   \]
4. 所以 \(d_j(\phi(x),\phi^\natural(x))\le\tau_j\)，且 \(x\in U_q\subseteq U\)。

Lean 中的证明正是这个链条：

- `proxy_path_component_guarantee_error_bound` 给出分量误差界；
- `path_component_guarantee_union_subset_proxy_error` 对 \(q\) 做出存在性消去；
- 联合形式通过 `path_joint_guarantee_error_bound` 对 \(j\in J\) 同时应用；
- `path_chain_eq_represented_proxy_on_path` 把路径链 \(c_q\) 替换为代理算子 \(\phi\)。

因此最终包含关系与正文完全一致。

---

## 四、源码已证明与需自行补充的部分

### 源码已证明

以下内容在源码中已有定理或定义，且构建通过：

- 路径采样集、可评估分量、路径残差；
- 路径链与代理在路径域上的相等；
- 路径局部上界 h-4b5219；
- 分量保证域到全局误差的局部蕴含；
- 路径保证域并集的全局包含，包括分量形式和联合形式；
- `path_guarantee_union_subset_proxy_error_text` 同时给出两个结论；
- 路径采样分解及路径残差受全局残差控制，属于辅助声明：
  - `component_sample_eq_iUnion_path_component_sample`
  - `disjoint_path_component_sample_of_nodes_ne`
  - `path_empirical_residual_upper_le_global`

所以针对 h-93 的核心数学内容，不需要再补写新的 Lean 定理。

### 需要自行补充或注意的内容

这些不是 h-93 证明的逻辑缺口，而是形式化签名与正文逐字语境之间的差异：

1. **空路径样本的总化处理**

   正文说当 \(S_{q,j}=\varnothing\) 时路径级共同锚点距离/残差不在本章定义范围内。Lean 中 `weighted_anchor_distance` 对空集取 \(\top\)，`path_empirical_residual_upper` 对空样本也仍有总化定义（原始上确界为 \(0\)，再加上 \(\delta_{o,j}\)）。  
   但最终 union 定理显式带有
   ```lean
   j ∈ path_evaluable_components N sample q
   ```
   因此空路径样本不会进入非平凡的路径保证域。若要在 Lean 中逐字表达“未定义”，应额外使用非空性假设；现有包含关系不受影响。

2. **正文的有限阈值与 \(J\neq\varnothing\)**

   核心定理 `path_component_guarantee_union_subset_proxy_error` 和 `path_joint_guarantee_union_subset_proxy_error` 允许任意 `ENNReal` 阈值，也允许空 `J`；正文要求阈值有限、\(J\) 非空。  
   这一点由 `path_guarantee_union_subset_proxy_error_text` 补回：
   - `finite_ennreal tau_j`
   - `finite_ennreal (tau i)`
   - `J.Nonempty`

   核心版本是更强/更一般的陈述，不是缺失。

3. **采样结构、样本落在 \(U\cap\mathrm{dom}(\phi^\natural)\) 等背景条件**

   正文 h-55c4fe8427039cfc 中还有 `SamplingStructure` 和
   \[
   S_j\subseteq S\cap U\cap\mathrm{dom}(\phi^\natural)
   \]
   等采样背景。Lean 的最终定理没有重复这些假设，因为证明只使用
   \[
   S_{q,j}=S_j\cap U_q\subseteq U_q\subseteq V^*.
   \]
   对于路径链残差，目标在样本点上的定义域由 `hLstar` 和 `hpathV` 提供；对于代理定义域，由 `N.represents proxy` 与 `dom N.extensional_operator = N.U` 推出。  
   若希望最终定理的签名逐字复现正文全部背景，可以额外加入：
   ```lean
   hsamplesU : ∀ j, sample j ⊆ N.U
   hsampleTarget : ∀ j, sample j ⊆ dom target
   hUstar : N.U ⊆ Vstar
   ```
   这些条件不会改变现有证明，因为它们在正文语境中成立。

4. **路径采样分解不是 h-93 的最新证明前提**

   正文 h-ed8808b4cfd52216 的
   \[
   S_j=\bigsqcup_{q\in\mathcal P}S_{q,j}
   \]
   在 Lean 中由 `component_sample_eq_iUnion_path_component_sample` 和
   `disjoint_path_component_sample_of_nodes_ne` 分开表达。  
   最终 h-93 的包含关系不需要重新引用该分解；它直接通过“存在某个 \(q\)”处理左侧并集。

5. **路径局部域与全局域的“比较注”**

   正文后面的注说路径局部证书与全局证书不能仅凭名称比较大小；Lean 没有把它单独包装成一条不等式定理。需要时可以用已有的
   - `weighted_anchor_distance_mono_of_subset`
   - `empirical_guarantee_domain_subset_of_certificate_bound_le`

   推出相应比较。  
   但该注不是 h-93 的包含命题本身，不影响 h-93 的覆盖性。

6. **路径链证书的统一性**

   核心定理的单分量版本允许矩阵 `Lq` 作为路径的函数；正文对每条路径固定一个 \(\mathbf L_q\)。`path_guarantee_union_subset_proxy_error_text` 使用统一的 `Lq q` 同时服务分量和联合结论，正好对应正文的“同一路径链证书”语境。这里没有错误。

---

## 五、最终判断

**判断：实现准确且完整覆盖 h-93b9c20ea18b4e59 的分量形式和联合形式。**

可给出如下核心对应：

\[
\boxed{
\begin{aligned}
U_{q,j}(\tau_j)
&\longleftrightarrow
\texttt{path\_component\_empirical\_guarantee\_domain}
\\
U_{q,J}(\boldsymbol\tau)
&\longleftrightarrow
\texttt{path\_joint\_empirical\_guarantee\_domain}
\\
\widehat\varepsilon_{q,j}
&\longleftrightarrow
\texttt{path\_empirical\_residual\_upper}
\\
\text{h-4b5219 局部上界}
&\longleftrightarrow
\texttt{path\_local\_empirical\_upper}
\\
\text{h-93 分量并集包含}
&\longleftrightarrow
\texttt{path\_component\_guarantee\_union\_subset\_proxy\_error}
\\
\text{h-93 联合并集包含}
&\longleftrightarrow
\texttt{path\_joint\_guarantee\_union\_subset\_proxy\_error}
\end{aligned}}
\]

没有发现可以推翻最终包含关系的反例。若把“准确覆盖”理解为**不仅结论相同，而且签名逐字重复正文全部背景假设**，则需要在包装定理中额外显式写出采样结构、\(S_j\subseteq U\cap\mathrm{dom}(\phi^\natural)\) 以及 \(U\subseteq V^*\) 等条件；但这些条件对现有证明不是必需的，而是可以在正文语境下额外加入的强化前提。