# 参考论证：有限观察的相容选择

$R(X)$ 自然同构于 $X$ 上超滤子的集合 $U(X)$。在这个同构下，题目规定的单位和乘法就是主超滤子映射与超滤子单子的乘法。所有记录恰好都是唯一的点值求值，当且仅当 $X$ 有限。

## 从相容选择构造超滤子

对 $S\subseteq X$，令 $\chi_S:X\to\{0,1\}$ 为特征函数，定义

$$\mathcal F_r=\{S\subseteq X:r_2(\chi_S)=1\}.$$

先由到单点测试集合的映射及单点到任意有限 $A$ 的映射，得到

$$r_A(x\mapsto a)=a.$$

再对有限测试集合 $A\times B$ 使用两个投影，得到

$$r_{A\times B}(x\mapsto(f(x),g(x)))=(r_A(f),r_B(g)).$$

将这项等式分别与二元布尔交运算及一元补运算复合，得

$$\begin{aligned}
S\cap T\in\mathcal F_r&\iff S\in\mathcal F_r\text{ 且 }T\in\mathcal F_r,\\
S^c\in\mathcal F_r&\iff S\notin\mathcal F_r.
\end{aligned}$$

常值公式给出 $X\in\mathcal F_r$ 与 $\varnothing\notin\mathcal F_r$。若 $S\subseteq T$ 且 $S\in\mathcal F_r$，则 $S\cap T=S$，交公式给出 $T\in\mathcal F_r$。故 $\mathcal F_r$ 是真滤子，补公式又保证它是超滤子。

对任意有限 $A$、$f:X\to A$ 与 $a\in A$，将自然性用于 $A\to\{0,1\}$ 的单点特征函数，得到关键的完整识别

$$f^{-1}(\{a\})\in\mathcal F_r\quad\Longleftrightarrow\quad r_A(f)=a.\tag{1}$$

因此从布尔观察恢复的超滤子决定所有有限观察，并未忽略有三个或更多值的测试集合。

## 从超滤子恢复全部记录

给定超滤子 $\mathcal F$ 和有限映射 $f:X\to A$，$f$ 的各纤维构成有限划分。至少一个纤维属于 $\mathcal F$，否则所有纤维的补集都属于它，有限交为空；至多一个纤维属于它，因为不同纤维不交。定义 $r_A^{\mathcal F}(f)$ 为这个唯一纤维的标号。

若该标号为 $a$，则

$$f^{-1}(\{a\})\subseteq(gf)^{-1}(\{g(a)\}),$$

故 $gf$ 所选择的标号恰为 $g(a)$。这证明相容性。该论证包含空测试集合：若确有 $f:X\to\varnothing$，则 $X=\varnothing$，其上不存在真超滤子，也不存在相容记录；后者会要求从唯一的空映射中选出空集元素。

按特征函数，$\mathcal F_{r^{\mathcal F}}=\mathcal F$；按式 (1)，$r^{\mathcal F_r}=r$。由此得到指定的双向分类。

## 函子、单位与乘法

对 $h:X\to Y$，定义

$$(R(h)r)_A(f)=r_A(fh).$$

原有相容性立即给出新的相容性；逐观察检查可得 $R(I)=I$ 与 $R(kh)=R(k)R(h)$。在超滤子分类下，这正是推前

$$h_*\mathcal F=\{T\subseteq Y:h^{-1}(T)\in\mathcal F\}.$$

题目给出的求值条件唯一确定

$$\eta_X(x)_A(f)=f(x),\qquad
\mu_X(\rho)_A(f)=\rho_A(r\mapsto r_A(f)).\tag{2}$$

单位相容性直接来自复合。对乘法，任意 $g:A\to B$ 满足

$$\begin{aligned}
g(\mu_X(\rho)_A(f))
&=\rho_B(r\mapsto g(r_A(f)))\\
&=\rho_B(r\mapsto r_B(gf))
=\mu_X(\rho)_B(gf).
\end{aligned}$$

故乘法也良定义。所有记录由各项观察取值决定，因此单位自然性、乘法自然性和两条单位律均可逐项代入式 (2) 核对。例如 $R(h)\mu_X=\mu_YR(R(h))$ 两侧在 $A,f:Y\to A$ 上都取值

$$\rho_A(r\mapsto r_A(fh)).$$

对 $\Omega\in R(R(R(X)))$，$\mu_X\mu_{R(X)}$ 与 $\mu_XR(\mu_X)$ 在 $A,f$ 上都取值

$$\Omega_A\bigl(\rho\mapsto\rho_A(r\mapsto r_A(f))\bigr).$$

这证明结合律及全部单子律，没有把它们作为记录的额外公理。

超滤子一侧，$\eta_X(x)=\delta_x$。若 $\mathfrak W\in U(U(X))$，乘法为

$$m_X(\mathfrak W)=\{S\subseteq X:\{\mathcal F:S\in\mathcal F\}\in\mathfrak W\}.$$

将式 (2) 用于 $\chi_S$ 即得到这个成员公式。因此分类同时保持函子、单位与乘法，给出单子同构；这里不额外声称任意自然运算的分类或其他单子的终性质。

## 点值记录的准确范围

$\eta_X$ 总是单射：若 $x\ne y$，以 $\{x\}$ 的特征函数观察，二者取值不同。若 $X$ 有限，有限单点划分说明每个超滤子都恰为一个 $\delta_x$，所以每个记录都是唯一点值记录。

若 $X$ 无限，其余有限滤子是真滤子。在 ZFC 中取扩张它的超滤子 $\mathcal F$。对每个 $x$，$X\setminus\{x\}\in\mathcal F$，故 $\{x\}\notin\mathcal F$；所以它不等于任何主超滤子。相应的 $r^{\mathcal F}$ 不是任何点值记录。这证明“全部记录唯一来自一个点”等价于 $X$ 有限，包括空集情形。

## 大小、评分及来源

有限测试集合及其映射组成的索引集合属于 $\mathcal V$，而 $X\in\mathcal V$，所以记录族构成 $\mathcal V$ 中的集合。任意有限集合都同构于某个有限序数，且记录的自然性强制它沿该同构运输；因此也可用有限集合的骨架定义同一对象。形式化以一个固定较小宇宙中的全部有限测试类型编码记录，并提供向任意有限测试类型的自然运输；它没有把无限 $X$ 排除在外。

完整答案需完成双向分类、题面指定的自然单子结构以及点值记录的充要范围。允许用正确适用的 codensity 定理压缩证明；仅证明存在非点值记录，或仅观察到点值记录可定义，都不完成任务。

公开来源为 [Leinster, Codensity and the ultrafilter monad, 2013](https://arxiv.org/abs/1209.3606)，其中讨论 Kennison–Gildenhuys 的有限集合 codensity 识别。这里独立写出布尔观察、全部有限纤维、求值乘法和有限性判别的论证。未使用未公开 OET 材料。

作者数学自查、Lean 核验、独立 AI 审核和人工审定分开登记；没有候选模型测评。本题与 MG-R019 使用相关的超滤子背景，但它们有不同的输入和主目标；不能将两题表现直接计为两个相互独立的能力维度。
