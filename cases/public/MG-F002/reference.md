# 参考审核

原陈述是 ∃N∈ℕ,∀n∈ℕ,n≤N，为假：给定任何 N，取 n=N+1 即否定它。
candidate.lean 的结论却是 ∀n∈ℕ,∃N∈ℕ,n≤N，
可为每个 n 取 N=n，因而代码在标准库内证明成功。

量词交换改变了见证能否依赖 n；编译通过没有证明统一界。
这不是补一句证明细节即可修复，需撤回原断言或明确改成逐点结论。□


## 取材与改编

- [Lean 4: Theorem Proving in Lean，Quantifiers and Equality](https://lean-lang.org/theorem_proving_in_lean4/quantifiers_and_equality.html)

题面、样本与本参考解由 AI 辅助编写并作首轮数学审校。这里记录的是参考依据；尚待人工审定。
