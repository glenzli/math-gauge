# MG-R016：实际对象与 Lean 覆盖

Lean 4.29.1；Mathlib revision `5e932f97dd25535344f80f9dd8da3aab83df0fe6`。本题独立编译 `LocalSplitting.lean`，只使用公共 Mathlib。所有自有声明位于 `MathGauge.LocalSplitting`。

| 原文义务或新结论 | 实际定义／声明 |
|---|---|
| 无限乘积环 $\prod_{\mathbb N}\mathbb F_2$ | `R = ℕ → ZMod 2`，Mathlib 逐坐标含幺交换环实例 |
| 实际有限支撑理想 | `finiteSupportIdeal`，以某个自然数之后恒零定义，直接证明加法及任意环标量封闭 |
| 实际商 $R/I$、包含与商映射 | `C`, `inclusion`, `q` |
| 原行短正合 | `inclusion_injective`, `q_surjective`, `row_exact` |
| 中间模是秩一自由模 | `middle_basis : Module.Basis Unit R R` |
| 商模循环、有限生成且非零 | `cyclic`, `quotient_finitely_generated`, `one_not_mem`, `q_one_ne_zero` |
| 坐标幂等元实际属于该理想 | `e`, `e_mem` |
| 不存在任何全局 $R$ 线性右逆 | `no_global_section` |
| 也不存在保持所给商投影的直和分解 | `no_compatible_decomposition` |
| 环中每个元素都幂等 | `boolean_identity`；逐坐标的有限运算由 kernel `decide` 检查 |
| 任意素理想及其通常环局部化 | `Rp p = Localization.AtPrime p`，`p` 任意且仅假设 `p.IsPrime` |
| 理想外／内元素在局部化分别为一／零 | `image_outside_prime`, `image_inside_prime`，使用实际素理想补集与局部化零判据 |
| 每个局部化元素为零或一，局部化为非零域 | `local_dichotomy`, `localField`；非零来自 `IsLocalization.AtPrime.nontrivial` |
| 原商映射在真实分式局部化模上的诱导映射 | `localizedQ = LocalizedModule.map p.primeCompl q` |
| 全部素点在分式模模型上的右逆 | `local_section`，从实际局部化满射及已构造的域结构推出 |
| 题面张量模型上的真实映射 $1\otimes q$ | `tensorQ = AlgebraTensorModule.lTensor (Rp p) (Rp p) q` |
| 分式局部化与张量局部化的模型桥，且保持原映射 | `LocalizedModule.equivTensorProduct` 与本题 `tensorQ_commutes`；在真实分式上证明交换 |
| 张量模型上满射及所需线性右逆 | `tensorQ_surjective`, `local_tensor_section` |
| 全部题设、所有素点的张量局部分裂与全局不存在同时成立 | `counterexample` |

没有把局部分裂、局部域结构或全局失败作为证书输入，也未只检查坐标评价素理想。所有素理想的量词原样保留，不使用素理想分类。关于局部化后的中间正合，题面及反例所需的是原行短正合与商映射局部右逆，代码已直接证明这些完整义务；没有额外宣称一个未经编码的分类定理。

精确源码和导入记录见 `manifest.json`。生成的 `CurrentAudit.lean` 对本题全部 `MathGauge` 声明及递归公理依赖进行核验，只允许 `propext`、`Classical.choice`、`Quot.sound`。数学独立审核与人工审定分开记录；human pending。
