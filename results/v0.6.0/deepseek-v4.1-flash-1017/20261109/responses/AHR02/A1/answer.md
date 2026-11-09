## 结论

核心数学内容上的判断是：**路径保证域的局部上界、分量并集包含式和联合并集包含式，Lean 实现基本正确，并且这些包含关系在附件源码中已经作为定理证明出来；但它不是对正文的完全逐字形式化，有两处接口/记号层面的不足需要说明。**

具体说：

- 分量形式  
  \[
  \bigcup_{q:\,j\in I_{\rm res}(q)}U_{q,j}(\tau_j)
  \subseteq
  \{x\in U:d_j(\phi(x),\phi^\natural(x))\le \tau_j\}
  \]
  对应 Lean 的  
  `path_component_guarantee_union_subset_proxy_error`。

- 联合形式  
  \[
  \bigcup_{q:\,J\subseteq I_{\rm res}(q)}U_{q,J}(\tau)
  \subseteq
  \{x\in U:\forall j\in J,\ d_j(\phi(x),\phi^\natural(x))\le \tau_j\}
  \]
  对应 Lean 的  
  `path_joint_guarantee_union_subset_proxy_error`。

- 两个形式再由  
  `path_guarantee_union_subset_proxy_error_text`  
  打包，并补入有限阈值、非空分量族等正文前提；不过这些前提在这条打包定理中实际上没有被证明使用，因为核心包含式在更强、更一般的条件下已经成立。

因此：**数学命题的实质内容和证明链条是闭合的，不是只写了陈述而未证明**。没有在相关声明中看到 `sorry`/`admit`。这是一个静态审阅结论；是否能在具体 Mathlib 版本下完整 `lake build` 还需要另行编译确认。

---

## 1. 定义与正文的对应关系

| 正文对象 | Lean 对象 |
|---|---|
| 网络输入域 \(U\) | `N.U` |
| 路径 \(q\) | `q : N.ReachablePath` |
| 路径域 \(U_q\) | `N.path_domain q.nodes` |
| 路径链 \(c_q\) | `N.path_chain q.nodes` |
| 路径采样集 \(S_{q,j}=S_j\cap U_q\) | `path_component_sample N sample q j` |
| 路径可评估分量集 \(I_{\rm res}(q)\) | `path_evaluable_components N sample q` |
| 路径残差 \(\hat\varepsilon_{q,j}\) | `path_empirical_residual_upper d target N sample delta_o q j` |
| 代理网络表示 \(\phi_{\mathcal N}\equiv_U\phi\) | `N.represents proxy` |
| 目标 Lip 包络 \(\mathbf L^*\) | `TargetLipEnvelopeCertificate d target Vstar Lstar` |
| 路径 Lip 证书 \(\mathbf L_q\) | `IsLipMatrix d (N.path_chain q.nodes) (N.path_domain q.nodes) (Lq q)` |
| 矩阵 \(\mathbf A_q=\mathbf L_q+\mathbf L^*\) | `fun i j => Lq q i j + Lstar i j` |
| 共同锚点距离 \(D_{\mathbf A,j}\) | `weighted_anchor_distance` |
| 路径分量保证域 \(U_{q,j}(\tau_j)\) | `path_component_empirical_guarantee_domain` |
| 路径联合保证域 \(U_{q,J}(\tau)\) | `path_joint_empirical_guarantee_domain` |

其中：

- `path_component_empirical_guarantee_domain` 定义为
  \[
  \{x\in U_q:
  D_{\mathbf A_q,j}(x;S_{q,j})+\hat\varepsilon_{q,j}\le \tau_j\},
  \]
  与正文一致。
- `path_joint_empirical_guarantee_domain` 定义为路径域上对所有 \(j\in J\) 同时满足
  \[
  D_{\mathbf A_q,j}(x;S_{q,j})+\hat\varepsilon_{q,j}\le \tau_j,
  \]
  对非空 \(J\) 来说就是正文中各个 \(U_{q,j}(\tau_j)\) 的交集。源码没有单独列出
  \[
  U_{q,J}(\tau)=\bigcap_{j\in J}U_{q,j}(\tau_j)
  \]
  这条集合等式，但这是定义层面立即可以补出的桥接引理；最终包含式的证明并不依赖把它单独命名。

---

## 2. 源码已经证明的证明链

正文的局部上界是：

\[
d_j(\phi(x),\phi^\natural(x))
\le
D_{\mathbf A_q,j}(x;S_{q,j})+\hat\varepsilon_{q,j}.
\]

Lean 中对应的链条是：

1. `path_local_empirical_upper`：证明路径链 \(c_q\) 与目标之间的局部经验上界。
2. `proxy_path_local_empirical_upper`：利用 `N.represents proxy`，把路径链 \(c_q\) 替换为代理 \(\phi\)，得到
   \[
   d_j(\phi(x),\phi^\natural(x))
   \le D_{\mathbf A_q,j}(x;S_{q,j})+\hat\varepsilon_{q,j}.
   \]
3. `path_component_guarantee_error_bound` / `proxy_path_component_guarantee_error_bound`：从
   \[
   x\in U_{q,j}(\tau_j)
   \]
   即
   \[
   D_{\mathbf A_q,j}(x;S_{q,j})+\hat\varepsilon_{q,j}\le\tau_j
   \]
   推出
   \[
   d_j(\phi(x),\phi^\natural(x))\le\tau_j.
   \]
4. `path_joint_guarantee_error_bound` / `proxy_path_joint_guarantee_error_bound`：对 \(J\) 中所有分量同时应用上一步。
5. `path_component_guarantee_union_subset_proxy_error` 和 `path_joint_guarantee_union_subset_proxy_error`：对 \(q\) 取存在量词，得到正文的两个并集包含式。

证明本质上正是正文的三角不等式加两条 Lip 证书：

\[
\begin{aligned}
d_j(\phi(x),\phi^\natural(x))
&\le d_j(c_q(x),c_q(x_s))
  +d_j(c_q(x_s),\phi^\natural(x_s))\\
&\quad +d_j(\phi^\natural(x_s),\phi^\natural(x)),\\
&\le
\sum_i [\mathbf A_q]_{i\to j}d_i(x,x_s)
+\hat\varepsilon_{q,j}.
\end{aligned}
\]

随后对所有锚点 \(x_s\in S_{q,j}\) 取下确界，得到共同锚点距离。Lean 中对应地使用了 `weighted_anchor_distance` 的下确界估计。因此局部上界和最终包含式都有实质证明，不是仅形式上声明。

---

## 3. 正文中的定义域和采样前提是如何被容纳的

正文一开始假设

\[
U\subseteq \operatorname{dom}(\phi)\cap V^*,
\qquad
S_j\subseteq S\cap U\cap\operatorname{dom}(\phi^\natural).
\]

Lean 的最终定理没有逐项显式列出这些假设，但都由已有假设推出或不需要额外使用：

- `N.represents proxy` 表示
  \[
  N.\mathrm{extensionalOperator}\equiv_{N.U}\phi.
  \]
  由于 \(N.U=\operatorname{dom}(N.\mathrm{extensionalOperator})\)，可推出
  \[
  N.U\subseteq \operatorname{dom}\phi.
  \]
- `hpathV : ∀q, N.path_domain q.nodes ⊆ Vstar`，而路径域覆盖网络输入域，故 `N.U ⊆ Vstar`；再由 `hLstar.lip_matrix` 中的定义域条件得到
  \[
  N.U\subseteq \operatorname{dom}\phi^\natural.
  \]
- 路径采样点属于 `N.path_domain q.nodes`，因而也落在目标 Lip 证书的定义域中。
- 正文还要求全局采样只取在目标定义域内；Lean 的 `sample : I → Set X` 可以包含额外点，但这些额外点不会进入 `path_component_sample`，因此不影响包含式。若要与正文完全同形，可以另加 `hsample_subset` 和 `SamplingStructure` 一类接口假设，但数学上不是必要补充。

---

## 4. 需要指出或补齐的地方

### 4.1 正文的 \(J_q\) 记号有歧义，Lean 采用了 \(J_q=J\)

正文一般形式写的是

\[
\bigcup_{q:\,J\subseteq I_{\rm res}(q)}
U_{q,J_q}(\boldsymbol\tau)
\subseteq
\{x\in U:\forall j\in J,\ d_j(\phi(x),\phi^\natural(x))\le\tau_j\}.
\]

但前文定义的 \(U_{q,J_q}\) 只保证 \(j\in J_q\) 的分量。因此，如果严格按照“任取 \(J_q\)”理解，而不同时假设

\[
J\subseteq J_q
\]

则结论并不成立。例如取 \(J=\{1,2\}\)、\(J_q=\{1\}\)，在 \(U_{q,\{1\}}\) 中只验证了第 1 分量，完全可以有一个点在第 2 分量上的真实误差超过 \(\tau_2\)。因此正文要么应写 \(J_q=J\)，要么应补上 \(J\subseteq J_q\)。

Lean 实现直接使用固定的 \(J\)：

```lean
path_joint_empirical_guarantee_domain ... J ... tau
```

这正是正文证明中“对所有 \(j\in J\) 同时应用”的自然含义。因此：

- 若把正文修读为 \(J_q=J\)，Lean 实现是准确的；
- 若坚持字面上任意的 \(J_q\)，则 Lean 没有覆盖这个更强、但当前缺乏额外假设的表述，需要补充 \(J\subseteq J_q\) 或把联合域改成带 \(J_q\) 的依赖族。

这是正文记号层面的缺口，不是 Lean 三角不等式证明的缺口。

---

### 4.2 Lean 最终并集定理要求“所有路径”都有 Lip 证书，正文只需被选中路径有证书

最终 Lean 定理使用：

```lean
(hLq : ∀ q : N.ReachablePath,
  IsLipMatrix d (N.path_chain q.nodes) (N.path_domain q.nodes) (Lq q))
```

也就是要求每个可达路径都预先带有一个路径级 Lip 矩阵。正文局部形式只对固定的 \(q\) 取一个

\[
\mathbf L_q\in\mathscr L(c_q)|_{U_q},
\]

而最终的并集式只对满足路径采样非空条件的 \(q\) 使用这些路径局部保证域。因此，严格按正文的一般性，应该只需要对实际出现在并集中的路径提供证书，例如可改成条件形式：

```text
hLq : ∀ q, j ∈ path_evaluable_components N sample q →
    IsLipMatrix d (N.path_chain q.nodes) (N.path_domain q.nodes) (Lq q)
```

联合形式类似地写成：

```text
hLq : ∀ q, J ⊆ path_evaluable_components N sample q →
    IsLipMatrix d (N.path_chain q.nodes) (N.path_domain q.nodes) (Lq q)
```

或者引入一个“带路径 Lip 证书的路径子类型”，并只对子类型中的路径取并集。

为什么这是实际前提差异？可以构造直观反例：网络有一条带采样、满足所有证书的路径 \(q_0\)，另有若干条没有采样的路径 \(q_1\)。在某个非分离扩展伪度量下，可令 \(q_1\) 的路径链把两个所有分量距离都为 0 的输入点送到一个输出分量距离为正的点对；这样的路径链不存在任何 Lip 矩阵。正文的并集只涉及 \(q_0\)，因此相关结论仍可成立；但 Lean 定理由于要求 `∀ q`，无法实例化。若正文默认“所有可达路径均已给出 Lip 证书”，则这一条不构成数学错误；但附件正文没有明确写出这个全局假设。

因此，这一点应记为：**Lean 证明本身正确，但接口假设比正文所需更强，未完全覆盖“只在被选路径上给出局部证书”的最一般情形。**

---

### 4.3 有限阈值和非空 \(J\) 是保守加强，不是缺口

正文要求阈值有限，且联合分量族非空。Lean 的核心并集定理实际上允许 \(\tau_j=\top\) 以及空 \(J\)；对应的 `_text` 包装又加入了：

- `finite_ennreal tau_j` / `finite_ennreal (tau i)`；
- `J.Nonempty`；
- `j ∈ evaluable_components sample`；
- `J ⊆ evaluable_components sample`。

这些条件在核心证明中没有被使用，但逻辑上不影响正文实例：凡是满足正文假设的情形，都满足 Lean 核心定理的较弱假设。因此这是**加强结论**，不是遗漏。

另外，空采样时 `weighted_anchor_distance` 对空锚点集取下确界得到 `⊤`，在有限 \(\tau\) 下保证域自动为空，和正文“路径级证书停止”的语义相容。但 `path_empirical_residual_upper` 作为 Lean 全函数在空采样上仍有一个值（空上确界为 0 加修正项）；它不应被解释为正文在空采样上定义了路径残差。最终定理通过 `j ∈ path_evaluable_components` 排除了这种非预期使用。

---

### 4.4 没有证明逆包含或等式，这符合正文

正文只断言路径局部保证域的并集包含于真实全局拟合区域，没有断言反向包含，也没有断言它等于某个全局保证域。Lean 实现同样只证明包含：

\[
\text{路径保证域并集}\subseteq \text{真实误差区域}.
\]

这是正确的范围。若把标题“全局拟合含义”理解成“路径保证域等于全局保证域”，那会超出正文；当前实现没有作这个过强的声称。

---

## 5. 最终判断

- **核心数学命题：准确，证明已覆盖。**  
  `path_component_guarantee_union_subset_proxy_error` 和  
  `path_joint_guarantee_union_subset_proxy_error` 实际完成了正文的分量并集和联合并集包含式。

- **局部上界与路径保证域定义：对应良好。**  
  `path_local_empirical_upper`、`proxy_path_local_empirical_upper` 及两个 guarantee-domain 错误界定理构成了完整的证明链。

- **逐字形式化层面：不完全。**  
  主要需要说明两点：
  1. 正文的 \(J_q\) 记号应明确为 \(J_q=J\)，或补充 \(J\subseteq J_q\)；Lean 采用了前者。
  2. Lean 最终定理要求所有可达路径都有 Lip 证书，比正文只在被讨论路径上取局部证书更强；可将 `hLq` 改成按路径局部非空条件给出的条件证书。

- **可选补充，不影响最终包含式：**
  1. 对非空 \(J\) 证明
     \[
     U_{q,J}(\tau)=\bigcap_{j\in J}U_{q,j}(\tau_j)
     \]
     的集合等式。
  2. 把正文的 \(U\subseteq\operatorname{dom}\phi\cap V^*\) 和采样包含条件显式写成接口引理或 wrapper 假设；它们在当前证明中可由 `N.represents`、路径域覆盖和 `hLstar` 的条件推出。
  3. 若需要严格区分“空采样时路径残差未定义”和 Lean 的全函数值，可给路径残差增加 `j ∈ path_evaluable_components` 的依赖参数或使用 `Option`/子类型封装；当前所有面向正文的结论都已经加了非空可评估条件，因此不会产生错误上界。

总体评价：**核心数学内容和证明是正确的；作为正文的正式逐字接口，尚需上述两处澄清或小幅加强条件，尤其是 `hLq` 的全路径假设。**