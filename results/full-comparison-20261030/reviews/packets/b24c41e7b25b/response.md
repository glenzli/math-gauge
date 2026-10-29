作者的等式在题目允许“记录保持不变”的前提下**不成立**。附件中的定理使用了更强的前提：在 \(A\) 内，记录每一步都必须按 \(g\) 更新。在这个更强的前提下，代码所声明的数学结论成立。

原前提仍保证
\[
q^{-1}(T_{|B|})\subseteq K,
\]
而且 \(K\) 总是包含于 \(A\) 的最大 \(f\)-前向不变集；但上述包含关系可以是严格的。

**附件的定义与前提。** 在 [RecordLayers.lean](/private/tmp/math-gauge-full-comparison-20261030/sessions/terra/MG-F109/input/RecordLayers.lean:8) 中，`layers B g n` 对应 \(T_n\)，`terminal B g` 对应 \(T_{|B|}\)。`layers_stabilize` 和 `terminal_mem` 的数学内容分别是
\[
T_{|B|+1}=T_{|B|},\qquad
y\in T_{|B|}\iff y\in B\ \text{且}\ g(y)\in T_{|B|}.
\]
这是有限递减链的结论：每次严格下降至少删除一个元素，因此至迟在第 \(|B|\) 层达到固定点。

在 [OrbitModel.lean](/private/tmp/math-gauge-full-comparison-20261030/sessions/terra/MG-F109/input/OrbitModel.lean:7) 中，`orbit` 是 \(f\) 的迭代，`Safe B q f x` 正好表示 \(x\in K\)。但第 14–15 行的 `Realizes` 要求
\[
\forall x,\quad q(x)\in B\Longrightarrow q(f(x))=g(q(x)),
\]
它排除了题目允许的、\(g(q(x))\ne q(x)\) 时的原地保持。这个加强条件确实被使用：`safe_in_layers` 第 30 行用该等式把 \(g(q(x))\) 改写成 \(q(f(x))\)。

在 [Candidate.lean](/private/tmp/math-gauge-full-comparison-20261030/sessions/terra/MG-F109/input/Candidate.lean:7) 中：

- `terminal_implies_safe` 在其声明的 `Realizes` 前提下成立；实际上，题目的较弱前提也足以推出这个方向。
- `exact_realization` 在 `Realizes` 前提下成立，表示 \(K=q^{-1}(T_{|B|})\)。它不能直接用于题目的较弱前提。
- `maximal_invariant` 在 `Realizes` 前提下，证明任意包含于 \(A\) 的前向不变集都包含于 \(q^{-1}(T_{|B|})\)。该定理本身写的是包含关系；结合前面的安全性结论，才能得到所选集合确为最大者。

`Finset Y` 和 `[DecidableEq Y]` 是 Lean 的有限集合表示；在通常的经典数学解释下，它们不额外限制题目中的有限 \(B\)。代码没有要求 \(X\) 有限、\(q\) 单射或满射，也没有约束 \(A\) 外的演化。

**决定性反例。** 取
\[
X=Y=\{0,1\},\quad q=\mathrm{id},\quad f=\mathrm{id},\quad
g(0)=g(1)=1,\quad B=\{0\}.
\]
在唯一需要检查的点 \(0\) 上，\(q(f(0))=q(0)=0\)，所以题目的条件成立。然而
\[
T_0=\{0\},\qquad T_{|B|}=T_1=\varnothing,
\qquad K=\{0\}.
\]
因此 \(q^{-1}(T_{|B|})=\varnothing\ne K\)。这里 \(q\) 甚至是双射，且 \(X\) 有限。此例不满足附件的 `Realizes`，因为 \(q(f(0))=0\ne1=g(q(0))\)。取 \(S=\{0\}\) 也可见，若只把 `maximal_invariant` 的前提换成题目中的较弱条件，其结论会失败。

一般地，`terminal_mem` 表明 \(T_{|B|}\) 同时对保持记录和应用 \(g\) 封闭，因此它的原像在原前提下是 \(A\) 内的前向不变集，故包含于 \(K\)。另一方面，不论记录条件如何，\(K\subseteq A\)，且 \(x\in K\) 蕴含 \(f(x)\in K\)；任何 \(A\) 内的前向不变集都只能包含安全轨道，所以都包含于 \(K\)。

附件末尾的 `#print axioms` 只能报告证明依赖的全局公理，不能检查定理是否符合自然语言目标：`Realizes` 是定理的显式参数，不会因此作为全局公理被报告。

本次执行工具不可用，未能在指定 Lean 和 Mathlib 版本中编译附件，也无法核验 `#print axioms` 的实际输出。上面对定理的判断是对其声明的数学命题及源码证明思路的审查，并非 Lean 内核检验。