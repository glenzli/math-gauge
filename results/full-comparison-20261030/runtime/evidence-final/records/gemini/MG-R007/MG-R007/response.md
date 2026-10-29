# 对称提升的逐层相容实现

在群表示论、同调代数以及现代对称相分类理论（如对称保护拓扑相中的对称提升与反常分析）中，有限群 $G$ 在塔系统上的表示提升问题是一个基本课题。本文针对所提出的问题给出完整的构造、严密的存在性证明、相容分裂空间的代数几何刻画，以及在整塔同构下的协变变换法则。

---

## 一、 系统结构与问题表述

### 1.1 塔系统的阶梯交换图

设 $G$ 为有限群，$k$ 为任意域，$C$ 为有限维 $k$-线性 $G$-表示。对于每一层 $n \ge 1$，给定有限维 $k$-线性 $G$-表示的短正合列：
$$0 \longrightarrow A_n \xrightarrow{i_n} B_n \xrightarrow{q_n} C \longrightarrow 0$$
其中 $i_n, q_n$ 均为 $G$-等变映射。

层与层之间由 $G$-等变映射 $\alpha_n: A_{n+1} \to A_n$ 与 $\beta_n: B_{n+1} \to B_n$ 相连，且满足相容性条件：
$$\beta_n i_{n+1} = i_n \alpha_n, \qquad q_n \beta_n = q_{n+1}$$
这构成如下交换阶梯图（每行正合，每列向下投影，最右列映射为 $\mathrm{id}_C$）：

$$\begin{CD}
0 @>>> A_{n+1} @>{i_{n+1}}>> B_{n+1} @>{q_{n+1}}>> C @>>> 0 \\
@. @VV{\alpha_n}V @VV{\beta_n}V @VV{\mathrm{id}_C}V @. \\
0 @>>> A_n @>{i_n}>> B_n @>{q_n}>> C @>>> 0
\end{CD}$$

已知每一层都存在（孤立的）$G$-等变线性分裂 $u_n: C \to B_n$，满足 $q_n u_n = I_C$。

### 1.2 逆极限结构

逆极限定义为逐坐标保持层间转移的子空间：
$$A_\infty = \varprojlim A_n = \left\{ (a_n) \in \prod_{n\ge 1} A_n : \alpha_n(a_{n+1}) = a_n \right\}$$
$$B_\infty = \varprojlim B_n = \left\{ (b_n) \in \prod_{n\ge 1} B_n : \beta_n(b_{n+1}) = b_n \right\}$$
定义 $i_\infty((a_n)) = (i_n(a_n))$ 以及 $q_\infty((b_n)) = q_1(b_1)$。

由于对任意 $(b_n) \in B_\infty$ 和任意 $n \ge 1$，有
$$q_n(b_n) = q_{n-1}(\beta_{n-1}(b_n)) = \dots = q_1(b_1) = q_\infty((b_n))$$
故 $q_\infty((b_n))$ 逐层一致。

### 1.3 核心任务
虽然各层独立存在分裂 $u_n$，但一般情况下 $\beta_n u_{n+1} \ne u_n$。我们需要：
1. 构造一族相容的 $G$-等变分裂 $s_n: C \to B_n$，同时满足 $q_n s_n = I_C$ 以及 $\beta_n s_{n+1} = s_n$；
2. 借此建立 $G$-表示同构 $B_\infty \cong A_\infty \oplus C$，并与包含和投影相容；
3. 刻画所有此类相容分裂的自由度空间；
4. 给出整塔交换同构下的变换法则。

---

## 二、 逐层相容分裂族 $(s_n)_{n\ge 1}$ 的构造与证明

### 2.1 代数阻碍分析

任取一族给定的孤立等变分裂 $(u_n)_{n\ge 1}$，定义其相容性偏差（阻碍元）：
$$\Delta_n = u_n - \beta_n u_{n+1} \in \operatorname{Hom}_G(C, B_n)$$
验算其在 $q_n$ 下的像：
$$q_n \Delta_n = q_n u_n - (q_n \beta_n) u_{n+1} = I_C - q_{n+1} u_{n+1} = I_C - I_C = 0$$
因此 $\operatorname{im}(\Delta_n) \subseteq \ker(q_n) = \operatorname{im}(i_n)$。
由于 $i_n: A_n \to B_n$ 是单射且 $G$-等变，故存在唯一的 $G$-等变映射 $d_n \in \operatorname{Hom}_G(C, A_n)$ 使得：
$$i_n \circ d_n = u_n - \beta_n u_{n+1}$$

若我们通过修正项 $f_n \in \operatorname{Hom}_G(C, A_n)$ 寻找相容分裂：
$$s_n = u_n + i_n f_n$$
则 $q_n s_n = q_n u_n + q_n i_n f_n = I_C$ 自动满足。相容性 $\beta_n s_{n+1} = s_n$ 要求：
$$\beta_n(u_{n+1} + i_{n+1} f_{n+1}) = u_n + i_n f_n$$
$$\iff \beta_n u_{n+1} + i_n \alpha_n f_{n+1} = u_n + i_n f_n$$
$$\iff i_n(f_n - \alpha_n f_{n+1}) = \beta_n u_{n+1} - u_n = - i_n d_n$$
由 $i_n$ 的单射性，这等价于在向量空间 $\operatorname{Hom}_G(C, A_n)$ 中求解线性差分方程：
$$f_n - \alpha_n \circ f_{n+1} = -d_n \qquad (\forall n \ge 1)$$

在无穷维同调代数中，该方程是否有解取决于逆系统的第一导出极限 $\varprojlim^1$ 是否为零。下面我们给出两种完整的论证：一种是基于有限维几何的**仿射子空间降链稳定化构造**（高度构造性），另一种是**Mittag-Leffler 条件**的同调代数证明。

---

### 2.2 构造法一：有限维仿射空间的稳定化截面算法

考虑每一层所有 $G$-等变分裂组成的集合：
$$S_n = \{ s \in \operatorname{Hom}_G(C, B_n) : q_n s = I_C \}$$
- **非空性**：根据已知条件，存在 $u_n \in S_n$，故 $S_n \ne \emptyset$。
- **空间结构**：若 $s, s' \in S_n$，则 $q_n(s - s') = 0$，存在唯一的 $f \in \operatorname{Hom}_G(C, A_n)$ 使得 $s - s' = i_n \circ f$。因此，$S_n$ 是一个以有限维 $k$-向量空间 $V_n = \operatorname{Hom}_G(C, A_n)$ 为切空间的**有限维仿射空间**（Affine Space），其维数为 $\dim S_n = \dim_k \operatorname{Hom}_G(C, A_n) \le (\dim_k C)(\dim_k A_n) < \infty$。

定义层间转移映射：
$$\tau_n: S_{n+1} \longrightarrow S_n, \qquad s \longmapsto \beta_n \circ s$$
验证良定义性：$q_n(\tau_n(s)) = q_n \beta_n s = q_{n+1} s = I_C$，且明显保持 $G$-等变性，因此 $\tau_n$ 是非空有限维仿射空间之间的仿射映射。

对任意 $m \ge n$，记复合映射为 $\tau_{n,m}: S_m \to S_n$（规定 $\tau_{n,n} = \mathrm{id}_{S_n}$），定义第 $m$ 层的像集：
$$S_n^{(m)} = \tau_{n,m}(S_m) \subseteq S_n$$
因为仿射映射的像是仿射子空间，所以每个 $S_n^{(m)}$ 都是 $S_n$ 的非空仿射子空间。

随 $m$ 递增，构成仿射子空间的降链：
$$S_n = S_n^{(n)} \supseteq S_n^{(n+1)} \supseteq S_n^{(n+2)} \supseteq \dots \supseteq S_n^{(m)} \supseteq \dots$$
由于 $S_n$ 是有限维仿射空间，子空间的维数是有限非负整数：
$$\dim S_n \ge \dim S_n^{(n+1)} \ge \dots \ge 0$$
整数非增降链必在有限步内稳定。即对每个 $n \ge 1$，存在正整数 $M(n) \ge n$，使得对所有 $m \ge M(n)$：
$$\dim S_n^{(m)} = \dim S_n^{(M(n))}$$
由于包含关系中同维度的仿射子空间必恒等，故当 $m \ge M(n)$ 时：
$$S_n^{(m)} = S_n^{(M(n))}$$
定义稳定像空间：
$$S_n^\infty = \bigcap_{m \ge n} S_n^{(m)} = S_n^{(M(n))}$$
作为有限步达到的仿射子空间，$S_n^\infty$ **必定非空**。

> **关键引理（相容满射性）**：限制映射 $\tau_n|_{S_{n+1}^\infty}: S_{n+1}^\infty \longrightarrow S_n^\infty$ 是**满射**。
>
> **证明**：
> 取充分大的整数 $m$，满足 $m \ge \max\{M(n), M(n+1) + 1\}$。
> 根据定义：
> $$S_{n+1}^\infty = S_{n+1}^{(m-1)} = \tau_{n+1, m}(S_m)$$
> 作用 $\tau_n$ 得：
> $$\tau_n(S_{n+1}^\infty) = \tau_n(\tau_{n+1, m}(S_m)) = \tau_{n, m}(S_m) = S_n^{(m)}$$
> 由于 $m \ge M(n)$，稳定条件给出 $S_n^{(m)} = S_n^\infty$。
> 因此 $\tau_n(S_{n+1}^\infty) = S_n^\infty$。引理获证。

#### 相容族的归纳构造：
基于上述引理，我们可以递归地显式选取 $(s_n)_{n\ge 1}$：
1. **基础步**：由于 $S_1^\infty \ne \emptyset$，任取一个元素 $s_1 \in S_1^\infty$；
2. **归纳步**：假设已选定 $s_n \in S_n^\infty$。由引理可知 $\tau_n|_{S_{n+1}^\infty}$ 是满射，故必存在 $s_{n+1} \in S_{n+1}^\infty$ 满足：
   $$\tau_n(s_{n+1}) = \beta_n \circ s_{n+1} = s_n$$
3. 由此归纳构造出的序列 $(s_n)_{n\ge 1}$ 严格满足：
   $$q_n s_n = I_C, \qquad \beta_n s_{n+1} = s_n \qquad (\forall n \ge 1)$$
   证毕。

---

### 2.3 构造法二：同调代数与 Mittag-Leffler 条件

记有限维向量空间 $V_n = \operatorname{Hom}_G(C, A_n)$，层间诱导的线性映射为 $\alpha_n^*: V_{n+1} \to V_n, f \mapsto \alpha_n \circ f$。
考虑反向系统 $(V_n, \alpha_n^*)_{n\ge 1}$。
对任意 $n \ge 1$，像空间序列 $\alpha_{n,m}^*(V_m)$ 是 $V_n$ 的线性子空间降链。由于 $\dim_k V_n < \infty$，该降链必稳定，即该系统满足 **Mittag-Leffler 条件**。

由同调代数基本定理，对于满足 Mittag-Leffler 条件的群（向量空间）反向系统，其一阶导出极限为零：
$$\varprojlim{}^1 V_n = 0$$
这意味着差分序列算子：
$$\delta: \prod_{n=1}^\infty V_n \longrightarrow \prod_{n=1}^\infty V_n, \qquad (f_n)_{n\ge 1} \longmapsto (f_n - \alpha_n^*(f_{n+1}))_{n\ge 1}$$
是**满射**。

从而，对于阻碍序列 $(-d_n)_{n\ge 1} \in \prod_{n=1}^\infty V_n$，必定存在 $(f_n)_{n\ge 1} \in \prod_{n=1}^\infty V_n$ 使得：
$$\delta((f_n)_{n\ge 1}) = (-d_n)_{n\ge 1} \iff f_n - \alpha_n \circ f_{n+1} = -d_n$$
令 $s_n = u_n + i_n f_n$，代入验证即知 $\beta_n s_{n+1} = s_n$。

---

## 三、 直和分解同构 $B_\infty \cong A_\infty \oplus C$ 的建立

构造好相容族 $(s_n)_{n\ge 1}$ 之后，我们建立逆极限空间的短正合列及其直和分解。

### 3.1 极限分裂映射 $s_\infty$ 的构造

定义线性映射：
$$s_\infty: C \longrightarrow \prod_{n\ge 1} B_n, \qquad c \longmapsto (s_n(c))_{n\ge 1}$$
- **良定义性**：对任意 $n \ge 1$，$\beta_n(s_{n+1}(c)) = (\beta_n s_{n+1})(c) = s_n(c)$，故像落入 $B_\infty$ 中，即 $s_\infty(C) \subseteq B_\infty$；
- **$G$-等变性**：每个 $s_n$ 均是 $G$-等变的，逐坐标定义的 $s_\infty$ 自然是 $G$-等变的；
- **截面性质**：$q_\infty(s_\infty(c)) = q_1(s_1(c)) = I_C(c) = c$，故 $q_\infty \circ s_\infty = I_C$。

### 3.2 逆极限短正合列的正合性

考虑序列：
$$0 \longrightarrow A_\infty \xrightarrow{i_\infty} B_\infty \xrightarrow{q_\infty} C \longrightarrow 0$$

1. **$i_\infty$ 为单射**：
   若 $i_\infty((a_n)) = (i_n(a_n)) = 0$，则对每一层 $n \ge 1$ 均有 $i_n(a_n) = 0$。由每一层 $i_n$ 的单射性，必有 $a_n = 0$，故 $(a_n) = 0$。
2. **$q_\infty$ 为满射**：
   由于已构造出 $s_\infty: C \to B_\infty$ 满足 $q_\infty \circ s_\infty = I_C$，$q_\infty$ 必为满射。
3. **在 $B_\infty$ 处的正合性（$\ker q_\infty = \operatorname{im} i_\infty$）**：
   - 包含关系 $\operatorname{im} i_\infty \subseteq \ker q_\infty$：
     对任意 $a = (a_n) \in A_\infty$，$q_\infty(i_\infty(a)) = q_1(i_1(a_1)) = 0$（因为 $q_1 i_1 = 0$）。
   - 包含关系 $\ker q_\infty \subseteq \operatorname{im} i_\infty$：
     任取 $b = (b_n) \in \ker q_\infty$，则 $q_1(b_1) = 0$。
     因为对所有 $n \ge 1$ 都有 $q_n(b_n) = q_1(b_1) = 0$，所以每一层的分量均属于核：$b_n \in \ker q_n$。
     由原序列的正合性 $\ker q_n = \operatorname{im} i_n$ 以及 $i_n$ 的单射性，对每个 $n$ 存在唯一的 $a_n \in A_n$ 使得：
     $$i_n(a_n) = b_n$$
     我们需要验证序列 $(a_n)$ 属于 $A_\infty$，即 $\alpha_n(a_{n+1}) = a_n$。
     利用转移交换律计算：
     $$i_n(\alpha_n(a_{n+1})) = \beta_n(i_{n+1}(a_{n+1})) = \beta_n(b_{n+1}) = b_n = i_n(a_n)$$
     由 $i_n$ 的单射性，立刻推出 $\alpha_n(a_{n+1}) = a_n$。
     因此 $a = (a_n) \in A_\infty$，且 $i_\infty(a) = b$。从而 $\ker q_\infty = \operatorname{im} i_\infty$。

### 3.3 直和同构的显式构造

由有限群表示范畴的分裂引理（Splitting Lemma）：
存在 $G$-等变线性映射：
$$\Phi: A_\infty \oplus C \longrightarrow B_\infty, \qquad (a, c) \longmapsto i_\infty(a) + s_\infty(c)$$
其逆映射显式为：
$$\Psi: B_\infty \longrightarrow A_\infty \oplus C, \qquad b \longmapsto \Big( i_\infty^{-1}\big(b - s_\infty(q_\infty(b))\big),\, q_\infty(b) \Big)$$
- **逆映射良定义性**：
  $$q_\infty\big(b - s_\infty(q_\infty(b))\big) = q_\infty(b) - (q_\infty s_\infty)(q_\infty(b)) = q_\infty(b) - q_\infty(b) = 0$$
  故 $b - s_\infty(q_\infty(b)) \in \ker q_\infty = \operatorname{im} i_\infty$，$i_\infty^{-1}$ 作用在上面唯一且良定义。
- **与正合列映射的对应关系**：
  设 $\iota_A: A_\infty \hookrightarrow A_\infty \oplus C$ 为第一直和项的自然包含，$\pi_C: A_\infty \oplus C \twoheadrightarrow C$ 为第二直和项的自然投影，则：
  $$\Phi \circ \iota_A(a) = \Phi(a, 0) = i_\infty(a) \implies \Phi \circ \iota_A = i_\infty$$
  $$\pi_C \circ \Psi(b) = q_\infty(b) \implies q_\infty \circ \Phi = \pi_C$$
  这严格建立了同构，并将 $i_\infty$ 对应于第一直和项的包含、将 $q_\infty$ 对应于第二直和项的投影。

---

## 四、 相容分裂自由度的完整刻画

记所有满足条件的相容分裂族集合为：
$$\mathcal{S} = \left\{ (s_n)_{n\ge 1} \in \prod_{n\ge 1} \operatorname{Hom}_G(C, B_n) : \forall n \ge 1,\, q_n s_n = I_C \text{ 且 } \beta_n s_{n+1} = s_n \right\}$$

### 4.1 全局自由度：仿射空间结构

根据前面的论证，$\mathcal{S} \ne \emptyset$。固定一个参考的相容分裂族 $s^{(0)} = (s_n^{(0)})_{n\ge 1} \in \mathcal{S}$。

任取另一个相容分裂族 $s = (s_n)_{n\ge 1} \in \mathcal{S}$，考虑差值族：
$$h_n = s_n - s_n^{(0)} \in \operatorname{Hom}_G(C, B_n)$$
因为 $q_n h_n = q_n s_n - q_n s_n^{(0)} = I_C - I_C = 0$，且 $\ker q_n = \operatorname{im} i_n$，$i_n$ 为单射，故每一层存在唯一的 $g_n \in \operatorname{Hom}_G(C, A_n)$ 使得：
$$h_n = i_n \circ g_n$$

再由层间相容性：
$$s_n = \beta_n s_{n+1} \implies s_n^{(0)} + i_n g_n = \beta_n(s_{n+1}^{(0)} + i_{n+1} g_{n+1}) = s_n^{(0)} + i_n \alpha_n g_{n+1}$$
两边消去 $s_n^{(0)}$，并由 $i_n$ 的单射性可得：
$$g_n = \alpha_n \circ g_{n+1} \qquad (\forall n \ge 1)$$

这说明序列 $(g_n)_{n\ge 1}$ 恰好是反向系统 $(\operatorname{Hom}_G(C, A_n), \alpha_n^*)_{n\ge 1}$ 的相容序列。根据反向极限的泛性质：
$$\varprojlim \operatorname{Hom}_G(C, A_n) \cong \operatorname{Hom}_G\left(C, \varprojlim A_n\right) = \operatorname{Hom}_G(C, A_\infty)$$
对应唯一的 $G$-等变线性映射 $g: C \to A_\infty$，其在第 $n$ 层的分量即为 $g_n$。

反之，对任意 $g \in \operatorname{Hom}_G(C, A_\infty)$，令其分量为 $g_n = \mathrm{pr}_n \circ g$，则定义 $s_n = s_n^{(0)} + i_n \circ g_n$ 必给出 $\mathcal{S}$ 中的相容分裂族。

> **定理（自由度刻画）**：
> 所有相容分裂族构成的集合 $\mathcal{S}$ 是一个以 $k$-向量空间
> $$\mathbb{V} = \operatorname{Hom}_G(C, A_\infty) \cong \varprojlim \operatorname{Hom}_G(C, A_n)$$
> 为切空间的**仿射空间**。即相容分裂的全部自由度精确地由 $\operatorname{Hom}_G(C, A_\infty)$ 参数化。

### 4.2 逐层投影视角的自由度

在有限层截断的视角下，第 $n$ 层的相容分裂 $s_n$ 的取值集合为仿射子空间 $S_n^\infty$（见 2.2 节）。
$S_n^\infty$ 的平行方向（切空间）为：
$$V_n^\infty = \bigcap_{m \ge n} \alpha_{n,m}^*(\operatorname{Hom}_G(C, A_m)) \subseteq \operatorname{Hom}_G(C, A_n)$$
因此，第 $n$ 层分裂能向无穷远延伸的局部自由度维数精确等于有限维向量空间 $V_n^\infty$ 的维度。

---

## 五、 整塔交换图同构下的变换法则

### 5.1 整塔同构的范畴定义

设有两个正合表示塔 $\mathcal{T} = \big( (A_n, B_n, C), (i_n, q_n), (\alpha_n, \beta_n) \big)$ 与 $\mathcal{T}' = \big( (A_n', B_n', C'), (i_n', q_n'), (\alpha_n', \beta_n') \big)$。
整塔之间的同构 $\Theta: \mathcal{T} \xrightarrow{\sim} \mathcal{T}'$ 由一组 $G$-等变同构族给出：
$$\phi_n: A_n \xrightarrow{\sim} A_n', \qquad \psi_n: B_n \xrightarrow{\sim} B_n', \qquad \chi: C \xrightarrow{\sim} C'$$
（注：由于 $q_n \beta_n = q_{n+1}$ 且 $q_n' \beta_n' = q_{n+1}'$，层与层之间底空间的同构 $\chi_n$ 必须与层数 $n$ 无关，统一为同一个同构 $\chi: C \to C'$），使得对所有 $n \ge 1$，所有三维棱柱交换图完全交换：

$$\begin{CD}
0 @>>> A_n @>{i_n}>> B_n @>{q_n}>> C @>>> 0 \\
@. @VV{\phi_n}V @VV{\psi_n}V @VV{\chi}V @. \\
0 @>>> A_n' @>{i_n'}>> B_n' @>{q_n'}>> C' @>>> 0
\end{CD}$$

即：
$$\psi_n \circ i_n = i_n' \circ \phi_n, \qquad q_n' \circ \psi_n = \chi \circ q_n$$
且层间转移映射满足：
$$\phi_n \circ \alpha_n = \alpha_n' \circ \phi_{n+1}, \qquad \psi_n \circ \beta_n = \beta_n' \circ \psi_{n+1}$$

### 5.2 相容分裂族的变换公式

若 $(s_n)_{n\ge 1} \in \mathcal{S}(\mathcal{T})$ 是原塔的一个相容分裂族，在同构 $\Theta$ 下，定义新塔的映射族 $(s_n')_{n\ge 1}$ 为：
$$s_n' = \psi_n \circ s_n \circ \chi^{-1}: C' \longrightarrow B_n'$$

我们验证 $(s_n')_{n\ge 1} \in \mathcal{S}(\mathcal{T}')$：
1. **逐层分裂性**：
   $$q_n' \circ s_n' = q_n' \circ \psi_n \circ s_n \circ \chi^{-1} = (\chi \circ q_n) \circ s_n \circ \chi^{-1} = \chi \circ (q_n s_n) \circ \chi^{-1} = \chi \circ I_C \circ \chi^{-1} = I_{C'}$$
2. **层间相容性**：
   $$\beta_n' \circ s_{n+1}' = \beta_n' \circ \psi_{n+1} \circ s_{n+1} \circ \chi^{-1} = (\psi_n \circ \beta_n) \circ s_{n+1} \circ \chi^{-1} = \psi_n \circ (\beta_n s_{n+1}) \circ \chi^{-1}$$
   利用原相容性 $\beta_n s_{n+1} = s_n$，立即得到：
   $$\beta_n' \circ s_{n+1}' = \psi_n \circ s_n \circ \chi^{-1} = s_n'$$
3. **$G$-等变性**：$\psi_n, s_n, \chi^{-1}$ 均是 $G$-等变的，故其复合 $s_n'$ 也是 $G$-等变的。

因此，$\Theta$ 诱导了相容分裂空间之间的双射：
$$\Theta_*: \mathcal{S}(\mathcal{T}) \xrightarrow{\sim} \mathcal{S}(\mathcal{T}'), \qquad (s_n)_{n\ge 1} \longmapsto (\psi_n \circ s_n \circ \chi^{-1})_{n\ge 1}$$

### 5.3 极限同构与自由度参数的变换

1. **极限截面与直和同构的协变性**：
   在逆极限层面上，$\Theta$ 诱导了同构 $\phi_\infty = \varprojlim \phi_n: A_\infty \xrightarrow{\sim} A_\infty'$ 和 $\psi_\infty = \varprojlim \psi_n: B_\infty \xrightarrow{\sim} B_\infty'$。
   极限分裂映射自然满足：
   $$s_\infty' = \psi_\infty \circ s_\infty \circ \chi^{-1}$$
   对应的直和同构 $\Phi: A_\infty \oplus C \xrightarrow{\sim} B_\infty$ 与 $\Phi': A_\infty' \oplus C' \xrightarrow{\sim} B_\infty'$ 满足完美的共轭交换律：
   $$\Phi' \circ (\phi_\infty \oplus \chi) = \psi_\infty \circ \Phi$$
   即下述方图严格交换：
   $$\begin{CD}
   A_\infty \oplus C @>{\Phi}>{\sim}> B_\infty \\
   @VV{\phi_\infty \oplus \chi}V @VV{\psi_\infty}V \\
   A_\infty' \oplus C' @>{\Phi'}>{\sim}> B_\infty'
   \end{CD}$$

2. **自由度向量的变换**：
   设 $s = s^{(0)} + i_\infty \circ g$，其中 $g \in \operatorname{Hom}_G(C, A_\infty)$。变换后的分裂为：
   $$s' = \psi_\infty \circ (s^{(0)} + i_\infty \circ g) \circ \chi^{-1} = s'^{(0)} + (\psi_\infty \circ i_\infty \circ g \circ \chi^{-1}) = s'^{(0)} + i_\infty' \circ (\phi_\infty \circ g \circ \chi^{-1})$$
   故自由度参数 $g$ 按照下述伴随/共轭法则变换：
   $$g \longmapsto g' = \phi_\infty \circ g \circ \chi^{-1} \in \operatorname{Hom}_G(C', A_\infty')$$
   这证明了映射 $\Theta_*$ 是一个**仿射空间同构**，其底向量空间同构为：
   $$\operatorname{Hom}_G(C, A_\infty) \xrightarrow{\sim} \operatorname{Hom}_G(C', A_\infty'), \qquad g \longmapsto \phi_\infty \circ g \circ \chi^{-1}$$

### 5.4 规范自同构特例（Symmetry Gauge Invariance）

特别地，当考虑原塔到自身的同构（自同构），且保持底表示 $C$ 及核表示 $A_n$ 不动（即 $\chi = I_C$ 且 $\phi_n = I_{A_n}$）时，此类同构对应于系统的**内秉规范变换**（Gauge Transformations）。
此时，必须有 $\psi_n = I_{B_n} + i_n \circ \xi_n \circ q_n$，其中 $\xi_n \in \operatorname{Hom}_G(C, A_n)$ 满足 $\alpha_n \xi_{n+1} = \xi_n$。
在此规范变换下：
$$s_n' = s_n + i_n \circ \xi_n$$
这表明整塔的规范自同构群在相容分裂空间 $\mathcal{S}$ 上的作用是**自由且传递**的，深刻揭示了在物理与代数意义下，所有不同的相容提升在整塔规范等价意义下均属于同一个唯一的轨道。
