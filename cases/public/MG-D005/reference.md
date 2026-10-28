# 参考结论

构造成立。~ 自反；其定义在交换 x,y 后不变；若 x~y 且 y~z，
传递性分别给出 x≤z、z≤x，故 ~ 为等价关系。

若 x~x'、y~y'，由 x'≤x≤y≤y' 得 x'≤y'；
反向用 x≤x'≤y'≤y，因此类上的关系与代表元无关。
自反和传递由原关系继承。若 [x]≼[y] 且 [y]≼[x]，
则 x~y，所以 [x]=[y]，这给出商上的反对称性。□

原集合为空时，商也为空，全部公理按量词真值成立。
不需要为每个类选择代表元来定义该关系，也没有给原预序补入反对称性。


## 取材与改编

- [mathlib: Order.Antisymmetrization（数学背景与可核对实现）](https://github.com/leanprover-community/mathlib4/blob/5e932f97dd25535344f80f9dd8da3aab83df0fe6/Mathlib/Order/Antisymmetrization.lean)

题面、样本与本参考解由 AI 辅助编写并作首轮数学审校。这里记录的是参考依据；尚待人工审定。
