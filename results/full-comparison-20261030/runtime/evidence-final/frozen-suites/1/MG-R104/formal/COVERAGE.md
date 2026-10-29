# MG-R104 形式化覆盖

作者参考 Lean，候选输入不附带。唯一作者模块为 `NilpotentDescent.lean`，命名空间为 `MathGauge.R104.System`（数据结构 `MathGauge.R104.System`）。Lean 4.29.1，Mathlib 固定为 `5e932f97dd25535344f80f9dd8da3aab83df0fe6`。最终编译与全声明公理审计由共用验证器绑定到 manifest；本表仅说明已编码的语义范围。

| 题面义务 | 实际 Lean 构造或定理 | 核对边界 |
| --- | --- | --- |
| 实际逆系数据 | `System` | 任意指标类型和预序，真实依赖环 `R i`、含幺转移、恒等/复合律、满射层增广、相容律和逐元素幂零核。没有转移满射、统一指数或极限核幂零假设。 |
| 实际极限环 | `limit_ring`, `Limit`, `evaluation` | 真正依赖乘积环中的相容元组子环，所有环运算及闭合性均构造。 |
| 指标无关的增广 | `limit_augmentation`, `augmentation_independent` | 用明确的有向性量词及一个任取 `i₀`；非空性只用于选这个指标。有向性没有换成可数或存在最大指标。 |
| 层幂等元唯一提升 | `stage_idempotent_ext`, `stage_lift_exists`, `stage_lift`, `stage_lift_idempotent`, `stage_lift_image` | 背景唯一提升定理只作用在每个真实层环及其核上。存在性的库证明与正文多项式改正是合法不同路线。 |
| 多项式改正恒等式 | `improvement_identity` | 直接 `ring` 验证正文中的恒等式，对任意交换环有效；不是主目标证书。 |
| 逐层提升相容 | `stage_lift_compatible` | 从真实转移同态保持幂等、增广交换和层唯一性推出。 |
| 极限中的幂等提升及唯一性 | `limit_lift`, `limit_lift_idempotent`, `limit_lift_image`, `limit_idempotent_ext`, `unique_limit_lift` | 构造真实相容元组。单射性只限制于幂等元，并未把增广声明为整体单射/满射。 |
| 所有有限完整正交家族的提升 | `lift_family`, `lift_family_complete`, `unique_lift_family` | 分量提升、乘积为零、有限和为一和唯一性分别证明。`J` 仅为 `Fintype`，允许空；任意有限集合可带其有限类型结构。反向映射由真实含幺同态保持这些等式。 |
| 指定商因子的环同构 | `lifted_product_decomposition`, `lifted_product_equiv` | 前者证明实际 `Pi.ringHom` 双射，后者以 `RingEquiv.ofBijective` 给出具名值级环同构，因子确为 `L ⧸ Ideal.span {1 - e_j}`。 |
| 系统态射及自然性 | `Morphism`, `map_limit`, `lift_natural`, `lift_family_natural` | 构造真实极限环同态，逐层使用唯一性证明提升交换；基环态射无需单射或满射。 |

库中的层提升和正交分解背景定理经过 Lean 内核依赖检查；新文件无自设 `axiom`、`sorry`、`admit` 或把所求相容提升放入假设的证书。`System` 的字段均为题面实际数据及公理，主目标不是字段。

参考中的三个错误路径反例（极限核不为幂零元理想、极限增广不满射、幂零元理想无统一指数）具有完整纸面证明，当前未独立形式化。这些是评审材料而非候选主任务。编译通过不等于正文语义审定或人类批准；human pending，尚无新模型运行。
