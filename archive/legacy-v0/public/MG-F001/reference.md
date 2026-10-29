# 参考审核

candidate.lean 编译有效，但不完整对应原题。
额外参数 separated 要求 R(x,y)⇒x=y，这不由等价关系推出；
结论又从 R(f(x),f(y)) 改为 f(x)=f(y)。
文件证明的是加强假设下的另一命题。

原题直接由 preserves 得到，不需要 separated。取 X={a,b}，R 恒真、f 为恒等，
便满足原题全部条件而不满足 separated，输出也不必点相等。
修复时删除 separated，把结论恢复为 R；reviewer/repair.lean 给出对应证明。□


## 取材与改编

- [算子演化论，公开第一卷，第 1 章：基础](https://github.com/glenzli/oet-public/blob/539b40cec73184d98e06d54fbd10e4b4698bd6e7/the-operator-evolution-theory/vol-01-gauge-spaces-and-operators/01-foundations.md)
- [Lean 4: Theorem Proving in Lean，Quantifiers and Equality](https://lean-lang.org/theorem_proving_in_lean4/quantifiers_and_equality.html)

题面、样本与本参考解由 AI 辅助编写并作首轮数学审校。这里记录的是参考依据；尚待人工审定。
