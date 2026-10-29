# 参考审核

对应且有效。E 的定义是双向合取。
candidate 的自反性调用 reflR 两次；对称性只交换合取的两个证据，不要求 R 对称；
传递性分别使用 transR x y z 和 transR z y x。
结论 Equivalence 恰好包含自反、对称、传递三项，全部得到证明。
集合为空时也成立，没有引入非空性或反对称性。□


## 取材与改编

- [mathlib: Order.Antisymmetrization（数学背景与可核对实现）](https://github.com/leanprover-community/mathlib4/blob/5e932f97dd25535344f80f9dd8da3aab83df0fe6/Mathlib/Order/Antisymmetrization.lean)

题面、样本与本参考解由 AI 辅助编写并作首轮数学审校。这里记录的是参考依据；尚待人工审定。
