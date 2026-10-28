# 可核对的内部基线（非唯一答案）

定义 x≼y 当且仅当存在 n∈ℕ，使 f^n(x)=y。
零次迭代给自反性；若 f^n(x)=y、f^m(y)=z，则 f^(m+n)(x)=z，给传递性。
因此是预序。令 x~y 表示相互可达；由双向传递得到等价关系。
商 Q=X/~ 上定义 [x]≤[y] 当且仅当 x≼y，
利用 x'≼x≼y≼y' 及反向链证明代表元无关性，得到偏序。

若 x≼y，则 f^n(f(x))=f(y)，所以 f 保持可达性和 ~。
诱导 F([x])=[f(x)] 良定且单调；并且 [x]≤F([x])（一步可达）。
这些陈述在空集合下也成立。□

## 信息丢失的具体例子

X={0,1}，f 交换两点。它没有原空间不动点，但两点相互可达，商只有一点，F 为恒等。
因此商上不动不推出原状态不动。
另一边，X=ℕ、f(n)=n+1 时各等价类都是单点，商上的演化仍无不动点。□

## 审核边界

不能把相互可达解释为点相等，也不能把有限次可达扩写为存在无穷迭代极限。
可以给出比上述基线更有用的分类或反例；数学新颖性与正确性另行判断。


## 取材与改编

- [mathlib: Order.Antisymmetrization（数学背景与可核对实现）](https://github.com/leanprover-community/mathlib4/blob/5e932f97dd25535344f80f9dd8da3aab83df0fe6/Mathlib/Order/Antisymmetrization.lean)
- [Lean 4: Theorem Proving in Lean，Quantifiers and Equality](https://lean-lang.org/theorem_proving_in_lean4/quantifiers_and_equality.html)

题面、样本与本参考解由 AI 辅助编写并作首轮数学审校。这里记录的是参考依据；尚待人工审定。
