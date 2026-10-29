# MG-R103 形式化覆盖

作者参考 Lean，候选输入不附带。唯一作者模块为 `BlockFixedPoints.lean`，命名空间为 `MathGauge.R103`。Lean 4.29.1，Mathlib 固定为 `5e932f97dd25535344f80f9dd8da3aab83df0fe6`。最终编译及全声明公理审计由共用验证器绑定到 manifest；本表描述语义对应，不替代该验证，也不代表人工审定。

| 题面义务 | 实际 Lean 构造或定理 | 核对边界 |
| --- | --- | --- |
| 参数化最小解 | `slice`, `solve`, `solve_fixed`, `solve_le_prefixed` | `solve` 本身是 `OrderHom`，其单调性由最小不动点比较证明；参数只需 `Preorder`，并未加完备性。 |
| 实际三块系统 | `triple_update` | 使用真实乘积 `A × (B × C)` 及三张联合单调映射。乘积的括号只表示坐标结合约定。 |
| 内层解与约化映射良定义及单调 | `inner`, `reduced` | 构造的是实际 `OrderHom`，单调性不是证书假设。 |
| 消元结果的方程及最小性 | `assembled_fixed`, `assembled_le_prefixed`, `assembled_eq_lfp` | 对所有联合前不动点给出比较，从而强于仅核对不动点方程。 |
| 三块的两次消元 | `first_update`, `rest_update`, `second_update`, `third_update`, `triple_elimination`, `inner_elimination` | 先消去 `B × C`，内层再拆成 `B,C`，均在实际题面数据上实例化两块定理。 |
| 任意重组与消元顺序 | `coordinate_transport`, `regrouped_elimination` | 对任意序同构到二块乘积证明消元结果；交换及结合三坐标是其特例，再用内层消元覆盖三块的所有顺序。没有把“重组保持答案”当作输入。 |
| 伴随关系下的精确传递 | `lfp_transport`, `parameter_transport` | 假设仅为实际 Galois 连接和一次更新的逐点交换式；结论才是最小解交换式。反向不等式实际使用伴随关系。 |
| 消元与传递一致 | `elimination_transport` | 定理直接以三块消元构造为左端、抽象系统的参数化最小解为右端。 |

基础 `OrderHom.lfp` 来自锁定 Mathlib，并在其真实完备格对象上实例化。新文件没有自设 `axiom`、`sorry`、`admit` 或含主目标的证书字段。

参考中的四个错误路径反例有完整纸面论证，当前不单独声称 Lean 覆盖；候选主任务不要求提交这些反例，也不要求候选提交 Lean。有限格/可数连续性不是形式化前提。所有数学及语义审核为 AI 证据，human 状态仍为 pending；尚无新模型校准。
