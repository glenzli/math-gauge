# CH1 给定背景

**定义（扩展规范空间）**：设 $\mathcal{X}$ 为集合，$\bot \in \mathcal{X}$ 为指定的**吸收元**，并要求非吸收部分非空：

$$
\mathcal{X}\setminus\{\bot\}\neq\emptyset.
$$

$\mathcal{X}$ 上的一个**规范结构** $\mathcal{G} = \{d_i\}_{i \in I}$（$I$ 为有限非空指标集）是一族**扩展伪度量**，每个 $d_i: \mathcal{X} \times \mathcal{X} \to \bar{\mathbb{R}}_+ = [0, +\infty]$ 满足：

**(i)** $d_i(x, x) = 0$，

**(ii)** $d_i(x, y) = d_i(y, x)$（对称），

**(iii)** $d_i(x, z) \leq d_i(x, y) + d_i(y, z)$（三角不等式），

**(iv)** $d_i(x, \bot) = +\infty$（$\forall\, x \neq \bot$，吸收元隔离）。

> **约定（$\bar{\mathbb{R}}_+$ 算术）**：全文采用标准扩展非负实数算术：$a + (+\infty) = +\infty$，$0 \cdot (+\infty) = 0$，$a \cdot (+\infty) = +\infty$（$a > 0$）。

称三元组 $(\mathcal{X}, \mathcal{G}, \bot)$ 为**扩展规范空间**（简称**规范空间**）。

> **约定（正文不预设族分离性）**：除非另有说明，本卷不预设族分离性；全分量零距离不必意味着两点相同。

**定义（算子空间）**：

$$\mathcal{X}_{\mathrm{op}} = \{\, \phi : \mathcal{X} \to \mathcal{X} \;\big|\; \phi(\bot) = \bot \,\}$$

$\phi \in \mathcal{X}_{\mathrm{op}}$ 称为 $\mathcal{X}$ 上的一个**算子**。条件 $\phi(\bot) = \bot$ 保证吸收元在所有算子下不变；$\phi(x) = \bot$ 表示 $\phi$ 在 $x$ 处未定义。

定义其**定义域**：

$$\mathrm{dom}(\phi) := \bigl\{\, x \in \mathcal{X} \;\big|\; \phi(x) \neq \bot \,\bigr\}$$

这里 $\mathrm{dom}(\phi)$ 指有效定义域；作为总函数，$\phi:\mathcal{X}\to\mathcal{X}$ 的集合论定义域仍是 $\mathcal{X}$。

# 待严格化的数学想法

那我再增加一题吧，以CH1扩展伪度量空间为基础，通常我们有一些东西来估计一个函数，比如Lip常数，但是对于伪度量比较复杂的场景，一个单一的 Lip 常数是不够的，可能能形成一个矩阵来表示各自分量的关系。同样的，除了 Lip 决定上限，是否还可以考虑下限？同时，也不是所有函数都有 Lip，为了统一的表达，是否考虑扩展一下，比如支持∞。最后，对于算子，我们还有一种性质，就是当一些输入落入到一定范畴，输出就不再可区分，这样是否可以和之前 Lip 定义同样对等的一种矩阵？

请将这一想法整理成自洽、忠于原意的数学定义与基本性质，并给出必要的论证。
