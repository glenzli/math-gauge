## 结论

所给 Lean 实现**准确、完整地覆盖了正文推论 #h-93b9c20ea18b4e59“路径保证域的全局拟合含义”**，包括分量形式和联合形式两个包含关系。未发现影响该推论的缺失前提、方向错误或未证明的结论。

我对目标文件执行了：

```bash
lake env lean formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean
```

编译成功且无报错；附件源码中也未检出 `sorry`、`admit` 或额外 `axiom` 声明。

## 正文与 Lean 的对应关系

| 正文对象或前提 | Lean 中的对应内容 |
|---|---|
| 路径限制采样 \(S_{q,j}=S_j\cap U_q\) | `path_component_sample`，见 `formal_oet/vol_03/ch_14_empirical_network_fitting/path_sampling.lean:27` |
| \(j\in I_{\mathrm{res}}(q)\)，即路径采样非空 | `j ∈ path_evaluable_components N sample q`；其展开正是路径采样非空，见 `path_sampling.lean:48`、`:59` |
| 路径可评估蕴含全局可评估 | `path_evaluable_subset_evaluable_components`，见 `path_sampling.lean:103` |
| \(U_{q,j}(\tau_j)\) | `path_component_empirical_guarantee_domain`，矩阵取 `Lq q + Lstar`，残差取 `path_empirical_residual_upper` |
| \(U_{q,J}(\boldsymbol\tau)=\bigcap_{j\in J}U_{q,j}(\tau_j)\) | `path_joint_empirical_guarantee_domain`，其定义就是 `x ∈ U_q` 加上所有 `j ∈ J` 的阈值不等式 |
| 网络在 \(U\) 上表示代理 \(\phi\) | `hrep : N.represents proxy`；此处正文的全局域 \(U\) 对应 Lean 的 `N.U` |
| 路径链在路径域上等于代理 | `path_chain_eq_represented_proxy_on_path`，见 `path_sampling.lean:220` |
| 每条路径的 Lip 证书 \(\mathbf L_q\) | `hLq : ∀ q, IsLipMatrix ... (Lq q)` |
| 目标 Lip 包络 \(\mathbf L^*\) | `hLstar : TargetLipEnvelopeCertificate d target Vstar Lstar` |
| \(U_q\subseteq V^*\) | `hpathV : ∀ q, N.path_domain q.nodes ⊆ Vstar`；正文中由 \(U_q\subseteq U\subseteq V^*\) 得到 |
| \(\mathbf A_q=\mathbf L_q+\mathbf L^*\) | `fun i j => Lq q i j + Lstar i j` |

两个核心定理与正文公式逐字对应：

1. **分量形式**  
   `path_component_guarantee_union_subset_proxy_error`，见  
   `formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean:520`

   其左端正是
   ```lean
   {x | ∃ q, j ∈ path_evaluable_components N sample q ∧
     x ∈ path_component_empirical_guarantee_domain ...}
   ```
   右端为
   ```lean
   {x | x ∈ N.U ∧ d j (proxy.func x) (target.func x) ≤ tau}
   ```
   即正文的
   \[
   \bigcup_{q:\,j\in I_{\mathrm{res}}(q)}U_{q,j}(\tau_j)
   \subseteq
   \{x\in U:d_j(\phi(x),\phi^\natural(x))\le\tau_j\}.
   \]

2. **联合形式**  
   `path_joint_guarantee_union_subset_proxy_error`，见同文件 `:552`。  
   左端要求同一个路径 `q` 满足 `J ⊆ path_evaluable_components N sample q`，右端要求所有 `j ∈ J` 同时满足误差界，正是正文的第二个包含式。

3. **正文前提的合并包装**  
   `path_guarantee_union_subset_proxy_error_text`，见同文件 `:588`，将上述两个结论组成合取，并显式保留：
   - `j ∈ evaluable_components sample`；
   - `J ⊆ evaluable_components sample`；
   - `tau_j` 有限；
   - `J.Nonempty`；
   - 所有 `tau i`（`i ∈ J`）有限。

   因而正文中的全局可评估性、有限阈值及联合分量族非空等语境也都保留了。

## 证明链条核对

这些包含关系在源码中确实已经证明，而不是仅作了声明：

- 分量证明从左端取出 `q`、`hj` 和 `hxq`：
  - `N.path_domain_subset_source hxq.1` 给出 `x ∈ N.U`；
  - `proxy_path_component_guarantee_error_bound` 给出代理—目标误差不超过 `tau`。
- 联合证明同样先取得 `x ∈ N.U`，随后：
  - 用 `path_joint_guarantee_error_bound` 得到路径链对所有 `j ∈ J` 的误差界；
  - 用 `path_chain_eq_represented_proxy_on_path` 将路径链改写为所表示的代理。
- 最后的正文包装直接取上述两个定理组成有序对，没有新增未经证明的断言。

## 对几个潜在疑问的说明

1. **核心定理没有显式携带完整的 `SamplingStructure`，并不构成缺失。**  
   正文的全局采样结构主要用于构造路径局部证书。当前全局推论已经把所需的 `hLq`、`hLstar`、`hpathV`、`hrep` 作为前提，因此证明包含关系时不需要重新使用采样结构的全部字段。正文的背景前提可以按上表实例化得到这些 Lean 前提； Lean 核心版本实际上更一般。

2. **路径残差虽然被全定义，空采样路径并未因此获得证书。**  
   `path_empirical_residual_upper` 在 Lean 中是对所有 `q,j` 全定义的；在空采样上，ENNReal 的空上确界按格约定取零，再加 `delta_o`。但本推论左端明确包含 `j ∈ path_evaluable_components N sample q`，联合形式也要求 `J ⊆ path_evaluable_components N sample q`，所以空采样路径不会进入被证明的保证域并集。这与正文“空路径采样不构造路径证书”的限制一致。

3. **正文包装中的若干假设在证明里未被使用，不是逻辑漏洞。**  
   全局可评估性、阈值有限性和 `J.Nonempty` 是正文语境，包含关系本身在更弱条件下也成立。包装保留它们以对应正文，核心定理则给出了更强的泛化版本。

## 已证明内容与无需补充的范围

上述两个包含式及其正文包装均为**附件源码已经证明并编译通过的结论**，不需要我另行补充证明或反例。

实现没有证明、正文也没有声称以下更强结论：保证域并集等于真实误差区域、反向包含成立、或对每个 `x ∈ U` 都无条件有误差不超过阈值。路径/全局保证域之间的大小比较也不属于本推论。因此这些都不能算作本实现的缺口。