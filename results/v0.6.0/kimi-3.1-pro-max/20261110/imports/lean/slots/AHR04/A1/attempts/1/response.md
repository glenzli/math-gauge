## 结论

就正文推论 **`h-93b9c20ea18b4e59`（路径保证域的全局拟合含义）**而言，所给 Lean 实现**准确、完整地覆盖了两个结论：分量形式和联合形式**。没有发现数学缺口或反例，也不需要补充新的证明义务。

实现还包含一个正文语境封装版；其前面的两个核心版本略去若干在逻辑上非必需的正文前提，因而结论稍强，但并不削弱正文命题。

我已实际执行：

```text
lake env lean formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean
```

类型检查通过。对三个相关全局定理执行 `#print axioms`，均只依赖 `propext`、`Classical.choice`、`Quot.sound`，没有 `sorryAx` 或额外数学公理。

## 一、命题对象的对应关系

| 正文对象 | Lean 对应 |
|---|---|
| 公共分析域 \(U\) | `N.U` |
| 可达路径 \(q\in\mathcal P\) | `q : N.ReachablePath` |
| 路径域 \(U_q\) | `N.path_domain q.nodes` |
| 路径采样集 \(S_{q,j}=S_j\cap U_q\) | `path_component_sample N sample q j`，见 `path_sampling.lean:27` |
| 路径可评估分量 \(I_{\mathrm{res}}(q)\) | `path_evaluable_components N sample q`，见 `path_sampling.lean:48` |
| 路径残差 \(\hat\varepsilon_{q,j}\) | `path_empirical_residual_upper d target N sample delta_o q j`，见 `path_sampling.lean:136` |
| \(\mathbf A_q=\mathbf L_q+\mathbf L^*\) | `fun i j => Lq q i j + Lstar i j` |
| 分量保证域 \(U_{q,j}(\tau_j)\) | `path_component_empirical_guarantee_domain`，见 `path_guarantee_domains.lean:26` |
| 联合保证域 \(U_{q,J}(\boldsymbol\tau)\) | `path_joint_empirical_guarantee_domain`，见 `path_guarantee_domains.lean:39` |
| 网络表示 \(\phi_{\mathcal N}\equiv_U\phi\) | `hrep : N.represents proxy` |
| 路径 Lip 证书 | `hLq : IsLipMatrix d (N.path_chain q.nodes) (N.path_domain q.nodes) (Lq q)` |
| 目标 Lip 包络 | `hLstar : TargetLipEnvelopeCertificate d target Vstar Lstar` |

路径可评估性的定义与正文一致：`path_evaluable_subset_evaluable_components`（`path_sampling.lean:103`）证明路径可评估蕴含全局可评估；反过来，正文定义中的交集条件 \(j\in I_{\mathrm{res}}\) 在路径采样非空时是自动成立的。

## 二、两个全局结论均已证明

### 1. 分量形式

正文 `source.md:242-248` 对应：

```lean
path_component_guarantee_union_subset_proxy_error
```

见 `path_guarantee_domains.lean:520-545`。

Lean 用存在量词表达正文的路径并集：

```lean
{x | ∃ q, j ∈ path_evaluable_components N sample q ∧
  x ∈ path_component_empirical_guarantee_domain ...}
```

这正对应于
\[
\bigcup_{q:\;j\in I_{\mathrm{res}}(q)}U_{q,j}(\tau_j).
\]

证明链是完整的：

1. 从成员条件分解出 `q`、路径可评估证明 `hj` 和路径保证域成员证明 `hxq`。
2. `hxq.1` 给出 \(x\in U_q\)，再由 `N.path_domain_subset_source` 得到 \(x\in N.U\)。
3. 调用已证明的 `proxy_path_component_guarantee_error_bound`，代入 `hrep`、`hpathV q`、`hLq q hj`、`hLstar` 和 `hj`，得到
   \[
   d_j(\phi(x),\phi^\natural(x))\le\tau_j.
   \]

其核心不等式正是
\[
d_j(\phi(x),\phi^\natural(x))
\le D_{\mathbf A_q,j}(x;S_{q,j})+\hat\varepsilon_{q,j}
\le\tau_j,
\]
与正文证明完全相同。

### 2. 联合形式

正文 `source.md:250-257` 对应：

```lean
path_joint_guarantee_union_subset_proxy_error
```

见 `path_guarantee_domains.lean:553-582`。

这里并集的指标条件为 `J ⊆ path_evaluable_components N sample q`，与正文的 \(J\subseteq I_{\mathrm{res}}(q)\) 一致。对每个 `j ∈ J`，证明调用 `path_joint_guarantee_error_bound` 得到路径链的误差界，再用：

```lean
path_chain_eq_represented_proxy_on_path N proxy q hrep hxq.1
```

把路径链改写为所表示的代理算子。因此得到所有
\[
d_j(\phi(x),\phi^\natural(x))\le\tau_j,\qquad j\in J,
\]
并且同样有 \(x\in N.U\)。这正是正文的联合包含关系。

## 三、正文语境封装的对应

`path_guarantee_union_subset_proxy_error_text`（`path_guarantee_domains.lean:590-637`）同时给出上述两个结论，并明确保留：

- `hj_evaluable : j ∈ evaluable_components sample`，对应 \(j\in I_{\mathrm{res}}\)；
- `hJ_evaluable : J ⊆ evaluable_components sample`，对应 \(J\subseteq I_{\mathrm{res}}\)；
- `hJ_nonempty : J.Nonempty`，对应正文联合形式的非空分量族；
- `htau_j_finite` 和 `htau_finite`，对应有限阈值。

该封装中的 `hLq` 使用析取前提：

```lean
j ∈ path_evaluable_components ... ∨
  J ⊆ path_evaluable_components ... → IsLipMatrix ...
```

这只是把两个分支所需的证书合并表达。证明分量分支时以 `Or.inl hj` 实例化，联合分支时以 `Or.inr hJ` 实例化，最终分别调用前面的两个核心定理，匹配没有缺失。

## 四、看似不同的前提处理不构成缺口

1. **核心版本未要求有限阈值、全局可评估性或 `J.Nonempty`。**  
   这些条件对包含关系本身不是必需的：
   - 路径并集已经显式要求相应的路径可评估性；而路径可评估又蕴含全局可评估性。
   - 若阈值是 `⊤`，误差不等式自动成立，而源域包含仍由路径域给出。
   - 因此正文封装版通过这些更强核心定理证明正文结论，是合法加强，而不是漏证。封装中这些正文前提未被实际使用，也没有逻辑问题。

2. **`hpathV` 是逐路径书写，而正文写的是 \(U\subseteq V^*\)。**  
   两者在正文语境下直接衔接：已有 `N.path_domain_subset_source`，所以若 `hUV : N.U ⊆ Vstar`，则每条路径域都满足
   ```lean
   N.path_domain_subset_source.trans hUV
   ```
   从而得到所需的 `hpathV`。这只是前提的实例化，不是额外数学证明义务。

3. **没有单独列出 \(U\subseteq\operatorname{dom}\phi\)。**  
   `N.represents proxy` 给出外延算子与代理在 `N.U` 上逐点相等，而已有 `dom N.extensional_operator = N.U`，故代理在 `N.U` 上有定义，不必再作为独立条件重复假设。

4. **空采样上的全量化定义不影响本推论。**  
   Lean 对某些空采样情形仍给出总定义，但两个全局并集都显式排除了不可评估路径，所以这些额外定义不会进入本推论的证明，也不会改变正文所述对象。

## 最终判断

- **源码已经证明：**正文所要求的分量全局包含关系、联合全局包含关系，以及保留正文有限阈值和非空分量族前提的合并版本。
- **无需自行补充：**该推论本身没有缺少的引理或证明步骤；从正文最初设定到 Lean 参数形式只需上述定义展开和直接前提转换。
- **不应误算为缺漏：**实现没有证明反向包含、保证域相等或路径/全局保证域的大小比较；这些都不是 `h-93b9c20ea18b4e59` 的结论。