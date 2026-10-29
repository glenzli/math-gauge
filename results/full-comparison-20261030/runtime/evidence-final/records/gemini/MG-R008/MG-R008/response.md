# 逐层记录的承载与相容性分类理论

在公理化集合论 $\mathrm{ZFC}$ 框架下，固定 Grothendieck 宇宙 $\mathcal U\in\mathcal V$ 且 $\mathbb N\in\mathcal U$。记 $\mathbf{Ab}_{\mathcal U}$ 为底集属于 $\mathcal U$ 的阿贝尔群及其群同态构成的阿贝尔范畴。

对于有限秩自由阿贝尔群的逆向塔 $\mathbf P = (P_n, \rho_n)_{n\ge0}$：
$$P_0\xleftarrow{\rho_0}P_1\xleftarrow{\rho_1}P_2\xleftarrow{\rho_2}\cdots,$$
其中对 $m\ge n$，$\rho_{n,m}=\rho_n\circ\rho_{n+1}\circ\cdots\circ\rho_{m-1}:P_m\to P_n$（规定 $\rho_{n,n}=\operatorname{id}_{P_n}$）。对任意 $A\in\mathbf{Ab}_{\mathcal U}$，定义其逐层记录函子为：
$$F_{\mathbf P}(A)=\varinjlim_{n\ge0}\operatorname{Hom}_{\mathbb Z}(P_n,A),$$
过渡映射为后复合 $\rho_n^*: u\mapsto u\circ\rho_n$。

---

## 一、 记录函子的代数结构与对偶模表示

为深入刻画 $F_{\mathbf P}$，首先揭示其张量积表示及平坦性。

### 1.1 对偶模与张量表示引理

记 $P_n^* = \operatorname{Hom}_{\mathbb Z}(P_n,\mathbb Z)$ 为 $P_n$ 的对偶自由群。因为 $P_n$ 为有限秩自由阿贝尔群，典范求值映射
$$\Phi_{P_n, A}: P_n^* \otimes_{\mathbb Z} A \xrightarrow{\ \sim\ } \operatorname{Hom}_{\mathbb Z}(P_n, A), \quad \phi \otimes a \mapsto (x \mapsto \phi(x)a)$$
是对 $A$ 自然的群同构。

对于过渡映射 $\rho_n: P_{n+1}\to P_n$，其对偶映射定义为
$$\rho_n^*: P_n^* \to P_{n+1}^*, \quad \phi \mapsto \phi\circ\rho_n.$$
易验证图表对所有 $n\ge0$ 交换：
$$\begin{CD}
P_n^* \otimes_{\mathbb Z} A @>\rho_n^* \otimes \operatorname{id}_A>> P_{n+1}^* \otimes_{\mathbb Z} A \\
@V \Phi_{P_n, A} V{\sim}V @V \Phi_{P_{n+1}, A} V{\sim}V \\
\operatorname{Hom}_{\mathbb Z}(P_n, A) @>>-\circ\rho_n> \operatorname{Hom}_{\mathbb Z}(P_{n+1}, A)
\end{CD}$$

由于正向极限与张量积交换，记有向系统 $(P_n^*, \rho_n^*)_{n\ge0}$ 的正向极限为：
$$M_{\mathbf P} := \varinjlim_{n\ge0} P_n^* \in \mathbf{Ab}_{\mathcal U}.$$

> [!NOTE]
> **引理 1.1（函子的对偶模表示）**
> 对每个 $A\in\mathbf{Ab}_{\mathcal U}$，存在对 $A$ 自然的同构：
> $$F_{\mathbf P}(A) \cong M_{\mathbf P} \otimes_{\mathbb Z} A.$$
> 特别地，$F_{\mathbf P}(\mathbb Z) \cong M_{\mathbf P}$。

### 1.2 对偶模的无挠性与有限极限保持性

> [!IMPORTANT]
> **引理 1.2（$M_{\mathbf P}$ 的平坦性）**
> 模 $M_{\mathbf P}$ 是可数无挠阿贝尔群。从而 $M_{\mathbf P}$ 是平坦 $\mathbb Z$-模，函子 $F_{\mathbf P}$ 保持 $\mathbf{Ab}_{\mathcal U}$ 中的所有有限极限（包括核、拉回及有限乘积）。

**证明**：
设 $x\in M_{\mathbf P}$ 满足 $k x = 0$（其中 $k\in\mathbb Z\setminus\{0\}$）。根据正向极限的定义，存在代表元 $\phi \in P_n^*$ 使得 $x = [\phi]$。
由 $k[\phi]=0$ 知，存在充分大的 $m\ge n$，使得在 $P_m^*$ 中有：
$$\rho_{n,m}^*(k\phi) = k \rho_{n,m}^*(\phi) = 0.$$
因为 $P_m^*$ 是有限秩自由阿贝尔群，其作为 $\mathbb Z$-模是无挠的。因此由 $k\ne0$ 推出 $\rho_{n,m}^*(\phi) = 0$。这表明在极限中 $x = [\phi] = 0$。故 $M_{\mathbf P}$ 无挠。在主理想整环 $\mathbb Z$ 上，无挠模必为平坦模。平坦模的张量积保持所有有限极限，因此 $F_{\mathbf P}$ 自动保持所有有限极限。 $\blacksquare$

---

## 二、 记录函子的可表性分类（承载性判据）

现在回答何时存在 $P\in\mathbf{Ab}_{\mathcal U}$ 使得 $F_{\mathbf P}(A)\cong\operatorname{Hom}_{\mathbb Z}(P,A)$。

### 2.1 塔的最终稳定条件与主定理一

对塔 $\mathbf P$ 及任意 $n\ge0$ 与 $m\ge n$，记过渡映射的像为
$$I_{n,m} = \operatorname{Im}(\rho_{n,m}) = \rho_{n,m}(P_m) \subseteq P_n.$$
固定 $n$ 时，子群族 $\{I_{n,m}\}_{m\ge n}$ 构成 $P_n$ 中的降链：
$$P_n = I_{n,n} \supseteq I_{n,n+1} \supseteq I_{n,n+2} \supseteq \cdots$$
记其极限像为 $I_n^{(\infty)} = \bigcap_{m\ge n} I_{n,m}$。

> [!IMPORTANT]
> **定理 2.1（记录函子的可表性充要判据）**
> 对于有限秩自由阿贝尔群的逆向塔 $\mathbf P$，记录函子 $F_{\mathbf P}$ 在 $\mathbf{Ab}_{\mathcal U}$ 中可表，即存在 $P\in\mathbf{Ab}_{\mathcal U}$ 使得
> $$F_{\mathbf P}(-) \cong \operatorname{Hom}_{\mathbb Z}(P,-),$$
> 当且仅当塔 $\mathbf P$ 满足如下由塔完全确定的**最终稳定准则（Criterion (R)）**：
> 
> 存在整数 $n_0\ge0$，使得对所有 $n\ge n_0$：
> 1. **像降链有限步稳定**：降链 $\{I_{n,m}\}_{m\ge n}$ 在有限步后平稳，即存在 $m_n\ge n$，使得对任意 $m\ge m_n$，
>    $$I_{n,m} = I_{n,m_n} =: I_n.$$
> 2. **稳定核维数保持**：限制映射 $\rho_n|_{I_{n+1}}: I_{n+1} \to I_n$ 是群同构（等价地，稳定秩 $\operatorname{rank}(I_n) = k < \infty$ 为与 $n\ge n_0$ 无关的常数）。

### 2.2 全部表示对象的构造

> [!NOTE]
> **定理 2.2（表示对象的显式构造与同构分类）**
> 设塔 $\mathbf P$ 满足定理 2.1 的判据，设 $n\ge n_0$ 时的稳定秩为 $k = \operatorname{rank}(I_n)$。
> 1. **典范表示对象**：塔的逆向极限
>    $$P_\infty := \varprojlim_{n\ge0} P_n = \left\{(x_n)_{n\ge0}\in\prod_{n=0}^\infty P_n \ \middle|\ \rho_n(x_{n+1})=x_n,\ \forall n\ge0\right\}$$
>    是有限秩自由阿贝尔群，且对于任意 $n\ge n_0$，典范投影
>    $$\pi_n|_{P_\infty}: P_\infty \xrightarrow{\ \sim\ } I_n$$
>    为群同构。故 $P_\infty \cong \mathbb Z^k$。
> 2. **典范自然同构**：典范比较变换
>    $$\Theta: F_{\mathbf P} \xrightarrow{\ \sim\ } \operatorname{Hom}_{\mathbb Z}(P_\infty, -), \quad [n, u] \mapsto u\circ\pi_n$$
>    是对所有 $A\in\mathbf{Ab}_{\mathcal U}$ 的自然同构。
> 3. **全部表示对象分类**：由 Yoneda 引理，$P\in\mathbf{Ab}_{\mathcal U}$ 表示 $F_{\mathbf P}$ 当且仅当
>    $$P \cong P_\infty \cong I_{n_0} \cong \mathbb Z^k.$$
>    所有表示对象在 $\mathbf{Ab}_{\mathcal U}$ 中精确到同构由秩为 $k$ 的自由阿贝尔群全体构成。

### 2.3 判据与构造的完整证明

**第一步：证明必要性**
假设 $F_{\mathbf P}$ 可表，即存在 $P\in\mathbf{Ab}_{\mathcal U}$ 及自然同构 $F_{\mathbf P}(A)\cong\operatorname{Hom}_{\mathbb Z}(P, A)$。
取 $A = \mathbb Z$，由引理 1.1 知：
$$M_{\mathbf P} \cong F_{\mathbf P}(\mathbb Z) \cong \operatorname{Hom}_{\mathbb Z}(P, \mathbb Z) = P^*.$$
作为可表函子，$F_{\mathbf P}$ 必保持 $\mathbf{Ab}_{\mathcal U}$ 中的所有极限，特别地，保持可数个 $\mathbb Z$ 的直积：
$$F_{\mathbf P}(\mathbb Z^{\mathbb N}) \cong \prod_{k=1}^\infty F_{\mathbf P}(\mathbb Z) = M_{\mathbf P}^{\mathbb N}.$$
结合引理 1.1，这意味着典范比较映射
$$\alpha: M_{\mathbf P} \otimes_{\mathbb Z} \mathbb Z^{\mathbb N} \to M_{\mathbf P}^{\mathbb N}, \quad m\otimes (c_k)_{k\ge1} \mapsto (c_k m)_{k\ge1}$$
必须是满射。
任取序列 $(m_k)_{k\ge1} \in M_{\mathbf P}^{\mathbb N}$。若 $\alpha$ 是满射，则必存在有限个元素 $u_1,\dots,u_N\in M_{\mathbf P}$ 及序列 $(c_{j,k})_{k\ge1}\in\mathbb Z^{\mathbb N}$ ($1\le j\le N$) 使得：
$$m_k = \sum_{j=1}^N c_{j,k} u_j, \quad \forall k\ge1.$$
这证明了：**$M_{\mathbf P}$ 的任意可数子集必包含于由有限个元素生成的子群中**。
因为 $M_{\mathbf P} = \varinjlim P_n^*$ 是可数群，取其全体元素构成的序列，立得 $M_{\mathbf P}$ 自身必须是**有限生成的**！
又由引理 1.2，$M_{\mathbf P}$ 无挠，由有限生成阿贝尔群基本定理，$M_{\mathbf P}$ 必为有限秩自由阿贝尔群，即存在 $k\ge0$ 使得 $M_{\mathbf P} \cong \mathbb Z^k$。

现在分析 $M_{\mathbf P} = \varinjlim P_n^*$ 有限生成对塔 $\mathbf P$ 的约束：
记 $\iota_n: P_n^* \to M_{\mathbf P}$ 为正向极限的典范映射。因为 $M_{\mathbf P}$ 由有限个元素生成，必存在 $n_0\ge0$ 使得对所有 $n\ge n_0$，
$$\iota_n: P_n^* \twoheadrightarrow M_{\mathbf P} \quad \text{为满射。}$$
因为 $M_{\mathbf P} \cong \mathbb Z^k$ 自由，正合列 $0\to\operatorname{Ker}(\iota_n)\to P_n^*\to M_{\mathbf P}\to0$ 分裂。
子群 $\operatorname{Ker}(\iota_n) = \bigcup_{m\ge n} \operatorname{Ker}(\rho_{n,m}^*)$ 作为有限秩自由群 $P_n^*$ 的子群是有限生成的，故升链必在有限步平稳：存在 $m_n\ge n$ 使得对任意 $m\ge m_n$，
$$\operatorname{Ker}(\rho_{n,m}^*) = \operatorname{Ker}(\iota_n).$$
注意到对任意同态 $f: P_m\to P_n$，其对偶核为：
$$\operatorname{Ker}(f^*) = \{\phi\in P_n^* \mid \phi\circ f = 0\} = (\operatorname{Im} f)^\perp = (\overline{\operatorname{Im} f})^\perp,$$
其中 $\overline{S}$ 表示子群 $S$ 在 $P_n$ 中的纯闭包（饱和子群）。
因此 $\operatorname{Ker}(\rho_{n,m}^*) = \operatorname{Ker}(\iota_n)$ 意味着：
$$(\overline{I_{n,m}})^\perp = \operatorname{Ker}(\iota_n) \quad (\forall m\ge m_n),$$
由对偶的正规性，$\overline{I_{n,m}} = (\operatorname{Ker}(\iota_n))^\perp$ 是定值子群，记为 $I_n$。
又因 $\operatorname{Im}(\iota_n) \cong P_n^*/\operatorname{Ker}(\iota_n) \cong M_{\mathbf P} \cong \mathbb Z^k$，此商群无挠，故 $I_n$ 是 $P_n$ 的纯子群（直和项），秩为 $k$。
并且对偶映射 $\rho_{n,m}^*$ 将 $P_n^*/\operatorname{Ker}(\iota_n) \cong M_{\mathbf P}$ 同构地映射到其在 $P_m^*$ 中的像，从而对偶地，限制映射 $\rho_{n,m}|_{I_m}: I_m \to I_n$ 必为满射；又因为 $I_m$ 与 $I_n$ 均为秩为 $k$ 的有限自由阿贝尔群，同秩自由群之间的满同态必然是同构！
因此条件 (1) 与 (2) 均成立。必要性证毕。

**第二步：证明充分性与构造**
假设 Criterion (R) 成立。
对 $n\ge n_0$，$I_n$ 为有限秩自由群，且 $\rho_n|_{I_{n+1}}: I_{n+1} \xrightarrow{\ \sim\ } I_n$ 均为群同构。
考察投影映射 $\pi_n: P_\infty = \varprojlim_{m\ge0} P_m \to P_n$。
对于任意 $x=(x_m)_{m\ge0}\in P_\infty$，因 $x_n = \rho_{n,m}(x_m) \in I_{n,m}$ 对所有 $m\ge n$ 成立，故 $x_n \in \bigcap_{m\ge n} I_{n,m} = I_n$。
反之，任给 $y\in I_n$：
- 对 $m \ge n$，由于每个过渡 $\rho_j|_{I_{j+1}}$ 均为同构，存在唯一的 $y_m \in I_m$ 使得 $\rho_{n,m}(y_m) = y$；
- 对 $m < n$，直接定义 $y_m = \rho_{m,n}(y)\in I_m$。
这唯一确定了一个序列 $(y_m)_{m\ge0}\in P_\infty$ 使得 $\pi_n(y) = y$。
因此，限制映射 $\pi_n|_{P_\infty}: P_\infty \to I_n$ 是同构！特别地，$P_\infty$ 是秩为 $k$ 的自由阿贝尔群。

现证 $\Theta_A: F_{\mathbf P}(A) \to \operatorname{Hom}_{\mathbb Z}(P_\infty, A)$ 为同构：
1. **单射性**：设 $[n, u] \in F_{\mathbf P}(A)$ 满足 $\Theta_A([n, u]) = u\circ\pi_n = 0$。
   不失一般性可设 $n\ge n_0$。因 $\pi_n(P_\infty) = I_n$，故 $u|_{I_n} = 0$。
   根据条件 (1)，取 $m\ge m_n$，有 $\operatorname{Im}(\rho_{n,m}) = I_n$。
   从而 $u\circ\rho_{n,m} = u|_{I_n}\circ\rho_{n,m} = 0$。
   在正向极限中，这给出 $[n, u] = [m, u\circ\rho_{n,m}] = [m, 0] = 0$。故 $\Theta_A$ 单。
2. **满射性**：任取 $f \in \operatorname{Hom}_{\mathbb Z}(P_\infty, A)$。
   取固定层 $n\ge n_0$。因为 $\pi_n|_{P_\infty}: P_\infty \to I_n$ 是同构，令 $f' = f \circ (\pi_n|_{P_\infty})^{-1} \in \operatorname{Hom}_{\mathbb Z}(I_n, A)$。
   根据引理，纯子群 $I_n$ 是有限秩自由阿贝尔群 $P_n$ 的直和项，即存在投影回缩 $p_n: P_n \twoheadrightarrow I_n$ 使得 $p_n|_{I_n} = \operatorname{id}_{I_n}$。
   定义 $u := f'\circ p_n \in \operatorname{Hom}_{\mathbb Z}(P_n, A)$。
   则对任意 $x\in P_\infty$，由于 $\pi_n(x) \in I_n$，有：
   $$\Theta_A([n, u])(x) = u(\pi_n(x)) = f'(p_n(\pi_n(x))) = f'(\pi_n(x)) = f(x).$$
   即 $\Theta_A([n, u]) = f$。故 $\Theta_A$ 满。
充分性及表示对象分类证毕。 $\blacksquare$

---

## 三、 可数极限相容性分类

研究对每个对象集与箭头集均可数的范畴 $J$ 及图表 $D: J\to\mathbf{Ab}_{\mathcal U}$，典范比较映射
$$\Psi_D: F_{\mathbf P}\!\left(\varprojlim_{j\in J}D(j)\right) \longrightarrow \varprojlim_{j\in J}F_{\mathbf P}(D(j))$$
何时恒为同构。

### 3.1 极限的还原与主定理二

在阿贝尔范畴 $\mathbf{Ab}_{\mathcal U}$ 中，任意指标范畴为可数范畴 $J$ 的图表极限 $\varprojlim_{j\in J} D(j)$ 均可由**可数积**与**等化子（核）**标准构造：
$$0 \to \varprojlim_{j\in J} D(j) \to \prod_{j\in\operatorname{Ob}(J)} D(j) \xrightarrow{\ \ \prod D(f)\pi_{\operatorname{dom}(f)} - \pi_{\operatorname{cod}(f)}\ \ } \prod_{f\in\operatorname{Mor}(J)} D(\operatorname{cod}(f)).$$

由引理 1.2，$F_{\mathbf P}$ 恒保持等化子（有限极限）。因此：
**$F_{\mathbf P}$ 保持所有可数极限当且仅当 $F_{\mathbf P}$ 保持可数直积。**

> [!IMPORTANT]
> **定理 3.1（可数极限相容性充要判据）**
> 记录函子 $F_{\mathbf P}$ 保持所有对象与箭头均可数的图表的极限，当且仅当塔 $\mathbf P$ 满足**定理 2.1 的最终稳定准则 Criterion (R)**。

**证明**：
**充分性**：若 Criterion (R) 成立，由定理 2.1 与 2.2，$F_{\mathbf P}(-) \cong \operatorname{Hom}_{\mathbb Z}(P_\infty, -)$。
由于反变 $\operatorname{Hom}$ 函子将范畴中的任意余极限转化为极限，而协变代表函子 $\operatorname{Hom}_{\mathbb Z}(P, -)$ 保持**任意形态（有限、可数或任意基数）的极限**。因此典范比较映射 $\Psi_D$ 对任意小范畴 $J$ 的极限恒为同构。

**必要性**：
假设对所有可数范畴 $J$，$\Psi_D$ 恒为同构。特别地，取 $J$ 为离散范畴 $\mathbb N$，图表为常数图表 $D(k) = \mathbb Z$ ($k\ge1$)。此时极限为可数直积：
$$\varprojlim_{k\in\mathbb N} D(k) = \mathbb Z^{\mathbb N} = \prod_{k=1}^\infty \mathbb Z.$$
于是，典范比较映射为群同构：
$$\Psi_{\mathbb Z^{\mathbb N}}: F_{\mathbf P}\!\left(\prod_{k=1}^\infty \mathbb Z\right) \xrightarrow{\ \sim\ } \prod_{k=1}^\infty F_{\mathbf P}(\mathbb Z).$$
结合引理 1.1 的对偶模表示，上式自然同构于：
$$\alpha: M_{\mathbf P} \otimes_{\mathbb Z} \mathbb Z^{\mathbb N} \xrightarrow{\ \sim\ } M_{\mathbf P}^{\mathbb N}.$$
我们直接论证 $\alpha$ 的满射性必然蕴含 $M_{\mathbf P}$ 有限生成：
假设 $M_{\mathbf P}$ 不是有限生成的。
由引理 1.2，$M_{\mathbf P}$ 是可数群，可将其表示为严格递增的有限生成子群链的并：
$$0 = H_0 \subsetneq H_1 \subsetneq H_2 \subsetneq H_3 \subsetneq \cdots \subsetneq \bigcup_{k=1}^\infty H_k = M_{\mathbf P}.$$
对每个 $k\ge1$，选取元素 $y_k \in H_k \setminus H_{k-1}$。
考虑 $M_{\mathbf P}^{\mathbb N}$ 中的序列元素 $\mathbf y = (y_1, y_2, y_3, \dots)$。
若 $\alpha$ 是满射，则存在 $\xi \in M_{\mathbf P}\otimes_{\mathbb Z} \mathbb Z^{\mathbb N}$ 使得 $\alpha(\xi) = \mathbf y$。
由张量积的有限展开，$\xi$ 可写为有限项和：
$$\xi = \sum_{i=1}^m w_i \otimes \mathbf c_i, \quad w_i \in M_{\mathbf P}, \ \mathbf c_i = (c_{i,k})_{k\ge1} \in \mathbb Z^{\mathbb N}.$$
因此对于每一个分量 $k\ge1$，有：
$$y_k = \sum_{i=1}^m c_{i,k} w_i \in \operatorname{span}_{\mathbb Z}\{w_1,\dots,w_m\}.$$
因为有限集 $\{w_1,\dots,w_m\} \subset M_{\mathbf P} = \bigcup_{j=1}^\infty H_j$，必存在充分大的指标 $N$，使得
$$\{w_1, \dots, w_m\} \subseteq H_N.$$
这推出对所有 $k\ge1$，均有 $y_k \in H_N$。
然而取 $k = N+1$，依据选取有 $y_{N+1} \in H_{N+1}\setminus H_N$，与 $y_{N+1}\in H_N$ 发生矛盾！
该矛盾证明 $M_{\mathbf P}$ 必须是有限生成的。
由定理 2.1 证明中的第一步推导可知，$M_{\mathbf P}$ 有限生成充要于塔 $\mathbf P$ 满足 Criterion (R)。必要性证毕。 $\blacksquare$

---

## 四、 两个判据之间的关系

> [!IMPORTANT]
> **定理 4.1（承载与相容的等价性主定理）**
> 对于任意有限秩自由阿贝尔群逆向塔 $\mathbf P$，以下命题彼此**逻辑等价**：
> 1. （**承载性 / 可表性**）记录函子 $F_{\mathbf P}$ 在 $\mathbf{Ab}_{\mathcal U}$ 中可表，即存在 $P\in\mathbf{Ab}_{\mathcal U}$ 使 $F_{\mathbf P}\cong\operatorname{Hom}_{\mathbb Z}(P, -)$；
> 2. （**可数相容性**）$F_{\mathbf P}$ 保持所有对象与箭头均可数的图表的极限；
> 3. （**可数积相容性**）$F_{\mathbf P}$ 保持可数个整数群的直积，即 $F_{\mathbf P}(\mathbb Z^{\mathbb N}) \cong (F_{\mathbf P}(\mathbb Z))^{\mathbb N}$；
> 4. （**完全极限相容性**）$F_{\mathbf P}$ 保持 $\mathbf{Ab}_{\mathcal U}$ 中任意小图表的极限；
> 5. （**塔级几何稳定**）塔 $\mathbf P$ 满足最终稳定准则 Criterion (R)。

### 4.1 本质联系分析与结构谱系

这一等价性揭示了逐层记录函子的如下深层代数拓扑本质：

```
                      塔的最终稳定 Criterion (R)
                                 ▲
                                 │
           ┌─────────────────────┴─────────────────────┐
           ▼                                           ▼
$F_P$ 在 $\mathbf{Ab}_U$ 中可表              $M_P = \varinjlim P_n^*$ 有限生成自由
           ▲                                           ▲
           │                                           │
           ▼                                           ▼
$F_P$ 保持所有小极限 ◄──────等价──────► $F_P$ 保持可数极限 / 可数直积
```

1. **有限极限是“免费”的**：由于过渡自由群的对偶仍自由，对偶正向极限模 $M_{\mathbf P}$ **无条件地恒为无挠模（平坦模）**。这意味着记录函子在任意塔下都自动保持所有有限极限，无需塔满足任何附加稳定条件。
2. **可数极限产生刚性塌缩**：一旦要求函子跨越“有限”迈向“可数”（即保持可数积），张量积的有限线性组合性与笛卡尔积的无穷维数立即产生冲突。要化解这一冲突，对偶模 $M_{\mathbf P}$ 必须是有限生成的（Chase 定理在 $\mathbb Z$ 上的体现）。
3. **可表与极限保持没有缝隙**：在泛函分析或一般代数范畴中，可表性往往严格强于保持可数极限。但在自由记录塔的设定下，可数极限相容性直接强迫塔在几何上发生“最终刚化”，从而使得“可表”与“保持可数极限”的判据完全重合。

---

## 五、 记录函子之间的自然变换、恒等与复合

设有两个有限秩自由阿贝尔群逆向塔：
$$\mathbf P = (P_n, \rho_n)_{n\ge0}, \qquad \mathbf Q = (Q_m, \sigma_m)_{m\ge0},$$
对应的记录函子分别为 $F_{\mathbf P}, F_{\mathbf Q}: \mathbf{Ab}_{\mathcal U} \to \mathbf{Ab}_{\mathcal U}$。

### 5.1 自然变换分类主定理

> [!IMPORTANT]
> **定理 5.1（自然变换的四重同构刻画）**
> 从 $F_{\mathbf P}$ 到 $F_{\mathbf Q}$ 的自然变换群 $\operatorname{Nat}(F_{\mathbf P}, F_{\mathbf Q})$ 存在如下典范群同构：
> $$\operatorname{Nat}(F_{\mathbf P}, F_{\mathbf Q}) 
> \cong \varprojlim_{n\ge0} \varinjlim_{m\ge0} \operatorname{Hom}_{\mathbb Z}(Q_m, P_n)
> \cong \operatorname{Hom}_{\mathbf{pro}\text{-}\mathbf{Ab}}(\mathbf Q, \mathbf P)
> \cong \operatorname{Hom}_{\mathbb Z}(M_{\mathbf P}, M_{\mathbf Q}).$$

**完整论证**：
1. **Yoneda 展开**：由正向极限在反变位置转化为逆向极限，以及 Yoneda 引理：
   $$\begin{aligned}
   \operatorname{Nat}(F_{\mathbf P}, F_{\mathbf Q}) 
   &= \operatorname{Nat}\left(\varinjlim_{n\ge0} \operatorname{Hom}_{\mathbb Z}(P_n, -), F_{\mathbf Q}\right) \\
   &\cong \varprojlim_{n\ge0} \operatorname{Nat}\left(\operatorname{Hom}_{\mathbb Z}(P_n, -), F_{\mathbf Q}\right) \\
   &\cong \varprojlim_{n\ge0} F_{\mathbf Q}(P_n) \\
   &= \varprojlim_{n\ge0} \left(\varinjlim_{m\ge0} \operatorname{Hom}_{\mathbb Z}(Q_m, P_n)\right).
   \end{aligned}$$
2. **pro-范畴反变对偶**：根据 pro-范畴 $\mathbf{pro}\text{-}\mathbf{Ab}$ 的态射定义，
   $$\operatorname{Hom}_{\mathbf{pro}\text{-}\mathbf{Ab}}(\mathbf Q, \mathbf P) = \varprojlim_{n\ge0}\varinjlim_{m\ge0}\operatorname{Hom}_{\mathbb Z}(Q_m, P_n).$$
   这表明态射方向发生反转：从 $\mathbf P$ 的函子到 $\mathbf Q$ 的函子的自然变换，一一对应于从系统 $\mathbf Q$ 到系统 $\mathbf P$ 的 pro-态射。
3. **模同态对应（Watts 定理）**：对于任意 $\tau \in \operatorname{Nat}(F_{\mathbf P}, F_{\mathbf Q})$，取 $A = \mathbb Z$，得群同态
   $$\phi_\tau := \tau_{\mathbb Z}: F_{\mathbf P}(\mathbb Z) \to F_{\mathbf Q}(\mathbb Z), \quad \text{即} \quad \phi_\tau: M_{\mathbf P} \to M_{\mathbf Q}.$$
   反之，任意同态 $\phi\in\operatorname{Hom}_{\mathbb Z}(M_{\mathbf P}, M_{\mathbf Q})$ 诱导自然变换 $\tau_A = \phi\otimes\operatorname{id}_A: M_{\mathbf P}\otimes A \to M_{\mathbf Q}\otimes A$。
   因为有限秩自由群满足 $\operatorname{Hom}(P_n^*, Q_m^*) \cong \operatorname{Hom}(Q_m, P_n)$，有：
   $$\operatorname{Hom}_{\mathbb Z}(M_{\mathbf P}, M_{\mathbf Q}) = \operatorname{Hom}_{\mathbb Z}\left(\varinjlim_n P_n^*, \varinjlim_m Q_m^*\right) \cong \varprojlim_n \varinjlim_m \operatorname{Hom}(P_n^*, Q_m^*) \cong \varprojlim_n \varinjlim_m \operatorname{Hom}(Q_m, P_n).$$
   这四者完全同构。 $\blacksquare$

### 5.2 显式记录表述、恒等变换与复合律

#### 1. 自然变换的显式记录结构
一个自然变换 $\tau \in \operatorname{Nat}(F_{\mathbf P}, F_{\mathbf Q})$ 由满足**层级相容性**的记录序列决定：
对每个 $n\ge0$，存在层级指标 $m_n\ge0$ 及群同态 $\theta_n: Q_{m_n}\to P_n$。
**相容性条件**：对任意 $n' \ge n$，态射 $\rho_{n,n'}\circ\theta_{n'}$ 与 $\theta_n$ 在正向极限 $\varinjlim_m \operatorname{Hom}(Q_m, P_n)$ 中定义同一记录，即存在充分大的 $K \ge m_n, m_{n'}$，使得在 $Q_K$ 上图表交换：
$$\rho_{n,n'} \circ \theta_{n'} \circ \sigma_{m_{n'}, K} = \theta_n \circ \sigma_{m_n, K}.$$

**对记录的作用**：任给 $A\in\mathbf{Ab}_{\mathcal U}$ 及记录元 $[n, u] \in F_{\mathbf P}(A)$（其中 $u\in\operatorname{Hom}_{\mathbb Z}(P_n, A)$），变换后的记录由下式显式给出：
$$\tau_A([n, u]) = [m_n, u \circ \theta_n] \in F_{\mathbf Q}(A).$$

#### 2. 恒等变换（Identity Transformation）
设 $\mathbf P = \mathbf Q$。恒等自然变换 $\operatorname{id}_{F_{\mathbf P}} \in \operatorname{Nat}(F_{\mathbf P}, F_{\mathbf P})$ 对应于：
- 对每个 $n\ge0$，选取 $m_n = n$；
- 选取同态 $\theta_n = \operatorname{id}_{P_n}: P_n \to P_n$。
此时相容性由下式自然满足：
$$\rho_{n,n'} \circ \operatorname{id}_{P_{n'}} = \rho_{n,n'} = \operatorname{id}_{P_n} \circ \rho_{n,n'}.$$
对记录的作用为 $\operatorname{id}_{F_{\mathbf P}, A}([n, u]) = [n, u\circ\operatorname{id}_{P_n}] = [n, u]$。
在对偶模层面上，对应于恒等自同态 $\operatorname{id}_{M_{\mathbf P}}: M_{\mathbf P}\to M_{\mathbf P}$。

#### 3. 复合律（Composition of Natural Transformations）
设三个塔 $\mathbf P, \mathbf Q, \mathbf R$，其中 $\mathbf R = (R_k, \kappa_k)_{k\ge0}$。
设自然变换 $\tau \in \operatorname{Nat}(F_{\mathbf P}, F_{\mathbf Q})$ 由 $\{ (m_n, \theta_n) \}_{n\ge0}$ 给出，其中 $\theta_n: Q_{m_n}\to P_n$；
自然变换 $\eta \in \operatorname{Nat}(F_{\mathbf Q}, F_{\mathbf R})$ 由 $\{ (k_m, \psi_m) \}_{m\ge0}$ 给出，其中 $\psi_m: R_{k_m}\to Q_m$。

> [!NOTE]
> **定理 5.2（复合构造定理）**
> 复合自然变换 $\eta \circ \tau \in \operatorname{Nat}(F_{\mathbf P}, F_{\mathbf R})$ 的作用满足：
> $$(\eta \circ \tau)_A([n, u]) = \eta_A\left([m_n, u\circ\theta_n]\right) = [k_{m_n}, u\circ\theta_n\circ\psi_{m_n}].$$
> 即复合变换在第 $n$ 层的代表元由下述数据给出：
> - 目标层级指标：$l_n := k_{m_n}$；
> - 过渡同态：$\theta_n \circ \psi_{m_n}: R_{k_{m_n}} \xrightarrow{\ \ \psi_{m_n}\ \ } Q_{m_n} \xrightarrow{\ \ \theta_n\ \ } P_n$。
> 
> 在 $\mathbf{pro}\text{-}\mathbf{Ab}$ 范畴中，这恰好对应于态射的反向标准复合：
> $$\mathbf R \xrightarrow{\ \psi\ } \mathbf Q \xrightarrow{\ \theta\ } \mathbf P \quad \Longrightarrow \quad \theta\circ\psi \in \operatorname{Hom}_{\mathbf{pro}\text{-}\mathbf{Ab}}(\mathbf R, \mathbf P);$$
> 在模同态层面，对应于同态的直接复合：
> $$\phi_{\eta\circ\tau} = \phi_\eta \circ \phi_\tau \in \operatorname{Hom}_{\mathbb Z}(M_{\mathbf P}, M_{\mathbf R}).$$

该论证完整确立了记录函子范畴到有限秩自由群 pro-范畴的反变同构，以及到可数平坦模范畴的协变同构，完成了该分类问题的全部构造与论证。
