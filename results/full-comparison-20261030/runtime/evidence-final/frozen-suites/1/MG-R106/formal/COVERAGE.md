# MG-R106 Lean 覆盖说明

主文件 `DenseRecovery.lean`，命名空间 `MathGauge.R106`。Lean 4.29.1；Mathlib 固定于 `5e932f97dd25535344f80f9dd8da3aab83df0fe6`。作者编译、独立数学审查、统一公理审计和人工批准分别记录；human pending。

| 题面义务 | 实际 Lean 声明 | 覆盖说明 |
|---|---|---|
| 原数据的完整量词 | `cauchy_on_dense`, `complete_domain_recovery` | 任意 `I`, 任意 `Filter I` 加 `NeBot`；任意度量 X,Y，只有 Y 完备；任意稠密 `Set X`；一个非负实常数 K。未改成自然数序列或可数滤子。 |
| 每个完成域延拓 | `extensions`, `extensions_lipschitz`, `extensions_coe` | 使用实际 `UniformSpace.Completion X` 和 `Completion.extension`；证明统一 K-Lipschitz 性与每个原点的延拓等式。 |
| 延拓唯一性 | `extensions_unique` | 证明在所有一致连续延拓中唯一，故包含题目所要求的 K-Lipschitz 类。 |
| 稠密 Cauchy 记录传递到全域 | `cauchy_on_dense` | 显式构造滤子中的共同指标集合并估计三段距离；没有使用全域一致 Cauchy 假设。随后在 `complete_domain_recovery` 内证明 D 像在实际完成域中稠密。 |
| 恢复映射存在并保留 K | `exists_lipschitz_limit`, `complete_domain_recovery` | 完备性给出每个点的真滤子极限；通过距离连续性保持 Lipschitz 界。全域点态趋近蕴含题面的稠密观测趋近，延拓等式由 `extensions_coe` 给出。 |
| 恢复唯一性 | `unique_from_dense_data`, `recovered_unique` | 前者仅使用原稠密观测的极限与连续性，正好覆盖题面更弱的识别条件；后者另外记录全域点态极限唯一性。 |
| 每个完成域紧集上的整族一致趋近 | `compact_uniform_limit`, `complete_domain_recovery` | 对紧集子类型应用等度连续族的点态/一致收敛等价定理。该步骤没有假设整个域紧、局部紧，也不抽取子族。 |
| 同步移动输入 | `moving_input_limit`, `complete_domain_recovery` | 任意 `u:I→Completion X` 沿相同滤子趋于 a；通过固定点误差加 Lipschitz 移动误差直接夹逼，未给 `range u` 附加紧性。 |

主结论覆盖包括空域、K=0 和任意真主滤子等边界。`exists_lipschitz_limit` 的存在性选择属于 ZFC；无额外数学 axiom、`sorry`、`admit` 或待证结论的 certificate 输入。标准 Mathlib 完备化和等度连续定理的适用条件由当前数据验证。

作者参考用有限球覆盖证明紧上一致收敛，Lean 使用同等假设下已证明的等度连续定理；这是有效替代证明，不是语义缩减。四个错误路径见证是评审材料的数学反例，未单独形式化，不构成题面额外义务。未做模型校准或人工审定。
