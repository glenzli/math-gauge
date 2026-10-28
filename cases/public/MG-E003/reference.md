# 可核对的内部基线（非唯一答案）

称 S⊆X 前向封闭，若 x∈S 且 R(x,y) 蕴含 y∈S。
所有包含 A 的前向封闭集合构成非空族，因为 X 属于其中。
定义 C(A) 为这个族的交。由逐点展开可知交仍前向封闭、包含 A，
并包含于每个这样的 S，故它是最小者。

若 A⊆B，C(B) 是包含 A 的前向封闭集合，故 C(A)⊆C(B)；
由于 C(A) 已前向封闭，有 C(C(A))=C(A)。再加 A⊆C(A)，得到闭包算子。
空集本身前向封闭，故 C(∅)=∅。□

也可令 A_0=A，A_(n+1)=A_n∪{y:存在 x∈A_n,R(x,y)}，并令 D=∪_(n∈ℕ)A_n。
D 包含 A 且前向封闭；归纳证明每个包含 A 的前向封闭 S 都包含每个 A_n，
故 D=C(A)。所有这里的路径均有限长，并不假定传播在某个有限步停止。

取 X=ℕ，A={0}，R(n,m) 当且仅当 m=n+1，则 A_n={0,…,n}，C(A)=ℕ，
没有统一有限步等于 C(A)。□

## 可接受的扩展

任意一族前向封闭集合的并仍前向封闭，故 C 保持任意并：
∪_i C(A_i) 既包含 ∪_i A_i 又前向封闭；结合单调性得到两向包含。
空指标族由 C(∅)=∅ 覆盖。
本构造使用的是集合的幂集及交并，不要求在原 X 上预设完备格或拓扑。
可以提出其他经验证的表示或普遍性质。□


## 取材与改编

- [mathlib: Order.Closure（闭包算子的标准公理）](https://github.com/leanprover-community/mathlib4/blob/5e932f97dd25535344f80f9dd8da3aab83df0fe6/Mathlib/Order/Closure.lean)
- [Lean 4: Theorem Proving in Lean，Quantifiers and Equality](https://lean-lang.org/theorem_proving_in_lean4/quantifiers_and_equality.html)

题面、样本与本参考解由 AI 辅助编写并作首轮数学审校。这里记录的是参考依据；尚待人工审定。
