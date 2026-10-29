# 参考结论

不保证。取 X=ℕ，通常次序，最小元为 0，f(n)=n+1。
若 n≤m，则 n+1≤m+1，所以单调；总有 n≤n+1，所以广延。
然而 n+1≠n 对每个自然数成立，故没有不动点。□

迭代 0,1,2,… 没有在 X 中达到稳定值，且 X 中不存在包含全部迭代项的上界。
不能从“有最小元”或“单调”推出链的上确界存在，也不能把某个更强结构上的不动点定理直接套用。


## 取材与改编

- [mathlib: Order.Antisymmetrization（数学背景与可核对实现）](https://github.com/leanprover-community/mathlib4/blob/5e932f97dd25535344f80f9dd8da3aab83df0fe6/Mathlib/Order/Antisymmetrization.lean)
- [Lean 4: Theorem Proving in Lean，Quantifiers and Equality](https://lean-lang.org/theorem_proving_in_lean4/quantifiers_and_equality.html)

题面、样本与本参考解由 AI 辅助编写并作首轮数学审校。这里记录的是参考依据；尚待人工审定。
