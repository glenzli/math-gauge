# 参考审核

代码证明有效，但它额外接收 Certificate f。该结构已经包含所需的 r、投影等式与回缩等式。
candidate 只把 cert 的三个字段重新包装成存在命题，没有从幂等性构造证书。
因此没有覆盖原题的构造义务；hf 在此实现中没有用于构造。

原题本身可证：令 r(x)=⟨f(x),“x 是其原像”⟩。投影等式由定义成立。
给定 y=⟨y₀,存在 x,f(x)=y₀⟩，幂等性给出 f(y₀)=y₀，
故以子类型外延性得到 r(j(y))=y。空 X 时也无需选择代表元。
reviewer/repair.lean 实现了这一构造，不接受额外 Certificate。□


## 取材与改编

- [Lean 4: Theorem Proving in Lean，Quantifiers and Equality](https://lean-lang.org/theorem_proving_in_lean4/quantifiers_and_equality.html)
- [mathlib: Order.Closure（闭包算子的标准公理）](https://github.com/leanprover-community/mathlib4/blob/5e932f97dd25535344f80f9dd8da3aab83df0fe6/Mathlib/Order/Closure.lean)

题面、样本与本参考解由 AI 辅助编写并作首轮数学审校。这里记录的是参考依据；尚待人工审定。
