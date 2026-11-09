## 结论

我审查的对象是 `source.md` 中编号 `h-93b9c20ea18b4e59` 的推论“路径保证域的全局拟合含义”。在该推论所要求的网络表示、路径 Lip 证书、目标 Lip 包络和采样数据均作为假设给出的前提下，Lean 实现与正文的两个集合包含关系实质一致，未发现数学反例。核心命题和最终包装都已证明，且文件可成功构建，未使用 `sorry`。

需要说明的是，形式化把正文的 `U` 实现为网络的输入域 `N.U`，并且部分正文语境条件是通过额外假设或后置包装补入的；这些属于接口/实例化层面的差异，不是原包含关系的数学缺口。

---

## 1. 正文与 Lean 的对应关系

正文中：

\[
U_q,\quad S_{q,j}=S_j\cap U_q,\quad
I_{\mathrm{res}}(q)=\{j:S_{q,j}\ne\varnothing\},
\]

\[
\hat\varepsilon_{q,j}
=\sup_{x_s\in S_{q,j}}d_j(c_q(x_s),\phi^\natural(x_s))+\delta_{o,j},
\]

\[
U_{q,j}(\tau_j)
=\{x\in U_q:
D_{\mathbf A_q,j}(x;S_{q,j})+\hat\varepsilon_{q,j}\le \tau_j\}.
\]

Lean 中分别对应：

| 正文 | Lean |
|---|---|
| \(U_q\) | `N.path_domain q.nodes` |
| \(S_{q,j}\) | `path_component_sample N sample q j` |
| \(I_{\mathrm{res}}(q)\) | `path_evaluable_components N sample q` |
| \(\hat\varepsilon_{q,j}\) | `path_empirical_residual_upper d target N sample delta_o q j` |
| \(\mathbf L_q\) | `Lq q` |
| \(\mathbf A_q=\mathbf L_q+\mathbf L^*\) | `fun i j => Lq q i j + Lstar i j` |
| \(U_{q,j}(\tau_j)\) | `path_component_empirical_guarantee_domain ...` |
| \(U_{q,J}(\boldsymbol\tau)\) | `path_joint_empirical_guarantee_domain ...` |
| \(D_{\mathbf A,j}(x;S)\) | `weighted_anchor_distance ...` |

局部上界对应：

- `path_local_empirical_upper`：路径链相对目标的局部经验上界；
- `proxy_path_local_empirical_upper`：利用网络表示把路径链替换为代理算子；
- `path_component_guarantee_error_bound`、`proxy_path_component_guarantee_error_bound`：由保证域成员关系得到
  \[
  d_j(\phi(x),\phi^\natural(x))\le \tau_j;
  \]
- `path_joint_guarantee_error_bound`、`proxy_path_joint_guarantee_error_bound`：对 \(J\) 中所有分量同时得到误差界。

最终集合包含由以下定理给出：

1. `path_component_guarantee_union_subset_proxy_error` 对应正文第一式：

   \[
   \bigcup_{\substack{q\in\mathcal P\\ j\in I_{\mathrm{res}}(q)}}
   U_{q,j}(\tau_j)
   \subseteq
   \{x\in U:d_j(\phi(x),\phi^\natural(x))\le\tau_j\}.
   \]

   Lean 中左端写成存在 \(q\) 的集合：
   \[
   \{x:\exists q,\ j\in I_{\mathrm{res}}(q)
   \land x\in U_{q,j}(\tau_j)\}.
   \]

2. `path_joint_guarantee_union_subset_proxy_error` 对应正文的联合分量公式：

   \[
   \bigcup_{\substack{q\in\mathcal P\\ J\subseteq I_{\mathrm{res}}(q)}}
   U_{q,J}(\boldsymbol\tau)
   \subseteq
   \{x\in U:\forall j\in J,\ d_j(\phi(x),\phi^\natural(x))\le\tau_j\}.
   \]

3. `path_guarantee_union_subset_proxy_error_text` 同时包装上述两个结论，并保留了正文中的非空 \(J\)、有限阈值等文本级条件。

---

## 2. 证明逻辑检查

Lean 证明与正文证明的路线一致：

1. 由 `hrep : N.represents proxy` 和
   `path_chain_eq_represented_proxy_on_path`，在路径域 \(U_q\) 上
   \[
   c_q(x)=\phi(x).
   \]

2. 由路径链 Lip 证书 `Lq q`、目标 Lip 包络 `Lstar` 和三角不等式，
   `path_local_empirical_upper` 给出
   \[
   d_j(c_q(x),\phi^\natural(x))
   \le D_{\mathbf A_q,j}(x;S_{q,j})+\hat\varepsilon_{q,j}.
   \]

3. 若 \(x\in U_{q,j}(\tau_j)\)，则
   \[
   D_{\mathbf A_q,j}(x;S_{q,j})+\hat\varepsilon_{q,j}\le\tau_j,
   \]
   从而
   \[
   d_j(\phi(x),\phi^\natural(x))\le\tau_j.
   \]

4. 对 \(x\) 属于路径保证域并集取某个见证路径 \(q\)，即得到第一个包含关系。联合版本对每个 \(j\in J\) 重复上述论证。

因此，正文证明中的三角不等式、路径 Lip 证书、目标 Lip 证书和保证域成员关系在 Lean 中都有对应，并且最终集合包含关系是由这些局部上界直接拼装得到的。

---

## 3. 源码已经证明的内容

在给出所需证书和表示的条件下，源码已证明：

- 路径采样集、路径可评估分量、路径经验残差的定义；
- 路径局部经验上界；
- 路径链与代理算子在路径域上的一致性；
- 由路径保证域成员关系推出分量误差上界；
- 分量形式的全局拟合包含；
- 联合分量形式的全局拟合包含；
- 将两者合并的正文级包装；
- 相关的路径采样分解和残差比较辅助结论。

我还检查了该模块的构建：

```text
lake build formal_oet.vol_03.ch_14_empirical_network_fitting.path_guarantee_domains
```

构建成功；抽查主要定理的 `#print axioms` 只显示 `propext`、`Classical.choice`、`Quot.sound`，没有额外的数学公理或 `sorry`。

---

## 4. 需要自行补充或实例化的内容

以下内容是定理的输入，不是源码已经自动证明的结论：

1. **把正文的 \(U\) 解释为 `N.U`**  
   Lean 的最终结论使用
   \[
   x\in N.U
   \]
   而不是另设一个独立的 `U`。正文中网络 \(N\) 的输入域正是 \(U\)，所以应实例化为 `N.U = U`；若使用一个独立参数 `U`，需要补充 `U = N.U` 或相应的 transport 证明。

2. **网络表示假设**  
   需要提供
   ```lean
   hrep : N.represents proxy
   ```
   即正文中的
   \[
   \phi_N\equiv_U \phi.
   \]

3. **目标 Lip 包络证书**  
   需要提供 `Vstar` 和
   ```lean
   hLstar : TargetLipEnvelopeCertificate d target Vstar Lstar
   ```
   对应正文的 \((\mathbf V^*,\mathbf L^*)\)。

4. **路径域包含于目标证书域**  
   源码把
   ```lean
   hpathV : ∀ q, N.path_domain q.nodes ⊆ Vstar
   ```
   作为假设。正文由
   \[
   U\subseteq V^*
   \]
   和路径域 \(U_q\subseteq U\) 可以推出这一点，但 Lean 定理没有自动从单独一个 `U⊆Vstar` 推导，而是直接要求每条路径的路径域包含于 `Vstar`。

5. **每条相关路径的 Lip 证书**  
   正文中的 \(\mathbf L_q\) 是作为“取路径链的受限 Lip 证书”给出的；Lean 中对应为
   ```lean
   Lq : N.ReachablePath → I → I → ENNReal
   hLq : ∀ q, IsLipMatrix d (N.path_chain q.nodes)
       (N.path_domain q.nodes) (Lq q)
   ```
   若要从节点级 Lip 矩阵自动构造路径链矩阵，应另外使用 `path_chain_lip_matrix` 或 `RightChainLipBounded` 等结果；当前全局拟合定理本身假定已有路径证书。

6. **有限阈值、非空 \(J\) 和采样结构**  
   最终正文包装 `path_guarantee_union_subset_proxy_error_text` 保留了有限阈值和非空 \(J\) 的假设。核心定理实际上允许阈值取 `⊤`、允许 \(J\) 为空，因此核心版本比正文条件更强；精确对应正文时使用 `_text` 版本即可。

   正文的有限采样结构 `SamplingStructure` 未被显式作为参数传入。就本包含命题而言，证明只使用路径采样点和相关 Lip 证书，不需要环境采样集的有限性；若要与正文全部语境逐字对齐，可以额外加入 `SamplingStructure target proxy ambient sample` 等假设，但这不是证明缺口。

---

## 5. 一个接口层面的小问题

`path_component_guarantee_union_subset_proxy_error` 和 `path_guarantee_union_subset_proxy_error_text` 中的

```lean
hLq : ∀ q, IsLipMatrix d (N.path_chain q.nodes)
    (N.path_domain q.nodes) (Lq q)
```

要求对 **所有可达路径** 提供 Lip 证书。正文的并集只涉及满足
\[
j\in I_{\mathrm{res}}(q)
\]
的路径；若只想采用最弱前提，可以弱化为

```lean
∀ q, j ∈ path_evaluable_components N sample q →
  IsLipMatrix d (N.path_chain q.nodes)
    (N.path_domain q.nodes) (Lq q)
```

联合分量版本类似地只需对满足
\[
J\subseteq I_{\mathrm{res}}(q)
\]
的路径提供证书。

这不是原命题的反例，而是当前签名比最字面要求稍强。若实际语境中全局路径 Lip 证书已经存在，则无影响；若没有，则应将 `hLq` 的量词限制到参与并集的路径上。

---

## 6. 关于“是否完整”的判断

按数学内容判断：

- **核心集合包含命题完整**；
- **联合分量版本完整**；
- **路径链到代理算子的替换完整**；
- **给定证书前提下的证明完整**；
- **未发现反例**。

其全局拟合含义只是单向包含，即路径保证域的并集落入真实误差集合；Lean 实现没有额外声称反向包含或与全局保证域相等，这是正确的，因为反向命题一般不能由这些数据推出。

若把正文中紧随其后的“与全局保证域的比较”说明性注记也算作审查对象，则该注记本身不是当前 Lean 定理的直接结论；需要另用
`weighted_anchor_distance_mono_of_subset` 和逐点证书上界比较另行形式化。但这不属于编号 `h-93b9c20ea18b4e59` 的显式集合包含命题。

总体而言：**实现准确覆盖了该推论的数学内容；主要工作是补充正文到 Lean 的实例化桥梁，而不是修正数学结论。**