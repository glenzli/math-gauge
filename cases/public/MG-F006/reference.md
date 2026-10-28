# 参考审核

对应且有效。U 被表示为谓词，invariant 正好表示 f(U)⊆U；
localPreserves 的两个成员证明把适用域限制在 U。
第一次使用得到 R(f(x),f(y))；第二次使用时明确提供 invariant x hx 和 invariant y hy。
因此没有把局部保持偷换成全域保持，也没有遗漏实际中间像域。
不需要 R 自反、对称或传递。空 U 时结论按量词真值成立。□


## 取材与改编

- [算子演化论，公开第一卷，第 4 章：算子链演算](https://github.com/glenzli/oet-public/blob/539b40cec73184d98e06d54fbd10e4b4698bd6e7/the-operator-evolution-theory/vol-01-gauge-spaces-and-operators/04-operator-chain-calculus.md)
- [Lean 4: Theorem Proving in Lean，Quantifiers and Equality](https://lean-lang.org/theorem_proving_in_lean4/quantifiers_and_equality.html)

题面、样本与本参考解由 AI 辅助编写并作首轮数学审校。这里记录的是参考依据；尚待人工审定。
