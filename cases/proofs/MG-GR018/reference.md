# 有限观察、自然运算与非点值记录：逐阶段参考与判准

本组 version 0.1.0；AI 作者自查完成，human pending。未调用候选模型，未为本组生成或编译 Lean。既有母题参考只作为本组完整数学论证的来源，不继承其模型成绩或形式化覆盖。每阶段均 mandatory；分值用于诊断，整组 pass 必须全部阶段实质完成。

## S1 有限底集上的记录

判定：true。

若 X 非空有限，取 U 中有限序数 A 及双射 e:X→A，令 x=e^{-1}(r_A(e))。对任意有限 B 和 f:X→B，写 f=(f e^{-1})e，自然性得 r_B(f)=f(x)。不同 x 用二值特征函数分辨。X 空时 Map(X,∅) 有一个元素，r_∅ 却需把它送到空集，不存在；与无点值一致。不需要用 X 本身作较小宇宙测试。

判准：有限骨架而非大小偷换；空集。

## S2 有限集合上的多元自然选择

判定：classification。

在 [m]={1,…,m} 上令 j=θ_[m](1,…,m)。任意元组定义 h:[m]→X，h(i)=x_i，自然性给 θ_X(x_1,…,x_m)=h(j)=x_j，因此恰为 m 个坐标投影，且它们显然满足自然性。m=0 时 X^0 为单点，X=∅ 不存在到 X 的函数，故无族。与 S1 相同，有限测试能确定函数，但不会额外提供一个自然固定点。

判准：用通用有限元组给必要性；投影充分性；m=0。

## S3 只使用两值测试

判定：false。

否。对非空 A（|A|≤2）令 r_A(f) 为至少被两个 X 元素取到的唯一值；若 A 单点就是其点。空 A 无 X→A，r_A 的定义域也空，故唯一空函数可用。测试间映射若为双射则运输多数值，若非常值且两边均两点仍为双射，其余可能都是常值或单点映射，均保持多数。故自然性全部成立。每个单点特征函数的多数值为 0，所以记录不同于任何点求值。三值以上测试与乘积测试在原条件中有实质作用。

判准：所给反例对全部允许测试映射的自然性核验；排除所有点值。

## S4 整体对象与全部恢复目标

判定：true。

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

判准：Classify all coherent finite-observation records by explicit mutually inverse constructions, with naturality for arbitrary set maps.；Construct the functor action and the unit and multiplication prescribed by the displayed evaluation equations; prove well-definedness, naturality, both unit laws and associativity.；Characterize exactly when every record is uniquely point evaluation; prove both directions, including the finite/empty cases and the infinite obstruction.；Keep the fixed-universe finite tests sufficient for arbitrary allowed X, using finite skeleton transport or an equivalent rigorous size argument.。

## S5 有限观察的连续实现

判定：construction。

在超滤子模型中 e_{A,f}^{−1}({a})=[f^{-1}({a})]，故连续。任意开闭 B⊂U(X) 因紧性是有限个基本开闭 [S_j] 的并，超滤子有限并性质使 B=[∪S_j]。于是 h 的各纤维为 [S_a]。在主点上读取，S_a 两两不交并为 X，定义 f(x)=a 当 x∈S_a；各超滤子恰选择该有限划分的一块，所以 h=e_{A,f}。f(x)=h(ηx) 给唯一性。若 A 空，只有 X 空时存在 f；此时 R(X) 也空，两个函数集均各有一个元素；非空 X 两者皆空。

判准：任意开闭是单个基本开闭；完整有限划分与唯一性。

## S6 乘法的单射性

判定：false。

并非总单射，且恰在 X 有限时单射。有限 X 时 S1 把 R(X)、R(R(X)) 都识别为 X，单位律迫使 μ 为恒等。无限 X 在 ZFC 下取非主超滤子 F（由余有限滤子延拓）。在 U(U(X)) 中比较 δ_F 与 U(η_X)(F)：两者经 m_X 都映到 F，前者由单位律，后者由另一单位律。两者不同，因为全部主超滤子的集合 η_X(X) 属于 U(η_X)(F)，却不属于 δ_F（F 非主）。将这些元素沿 S4 同构运输即为所需两记录。

判准：两个不同原像及乘法相等；有限方向。
