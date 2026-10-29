# 加权序列方程的形式化修订

令 $\mathcal S=\mathbb R^{\mathbb N}$，$w_n=n+1$，并定义
$$ (Tu)_n=u_n/w_n,\qquad
\operatorname{Control}(r,C,f)\iff\forall n\in\mathbb N:\ w_n^r|f_n|\le C.$$
称 $f$ 快速衰减，若对每个 $r\in\mathbb N$，存在非负实数 $C$ 使 $\operatorname{Control}(r,C,f)$。

目标是在全部实序列上构造线性逆 $S$，证明 $T(Sf)=f$，任意 $Tu=f$ 的解均等于 $Sf$，且 $S$ 保持快速衰减。还要求对任意 $r\in\mathbb N$、$C\in\mathbb R$、$f\in\mathcal S$ 有
$$\operatorname{Control}(r+1,C,f)\Longrightarrow\operatorname{Control}(r,C,Sf).$$
背景定义以附件 `Core.lean` 为准；允许使用 Mathlib 及经典逻辑。

检查并修订附件 `Core.lean`、`Multiplier.lean`、`Candidate.lean`，使交付完整达到上述目标；保留背景定义的含义。最终回答须在以文件名标注的 Lean 代码块中交付全部新增或改动源码，并说明最终声明及修订理由。不得把修订后的结果说成原文件已经证明。

Lean 4.29.1，Mathlib 5e932f97dd25535344f80f9dd8da3aab83df0fe6。
