# MG-P002 — 逐项目标与实际 Lean 覆盖

题目版本保持 **0.1.0**；task.md、rubric.json 与首轮逐字节相同。所有声明位于 `MathGauge.PublicProof.Torus` 及其 `Borrowed` 子命名空间。全部 task 目标均有实际函数声明与证明；编译和公理状态由同目录 `verification-report.json` 给出，人工审核仍为 pending。

| 原题要求 | 最终声明 | 证明与语义边界 |
|---|---|---|
| 实际单位二维环面、归一化 Haar、复值光滑零均值函数 | Functions: `Torus2`, `Smooth`, `MeanZero`, `coeff`; Representation: `smooth_iff_coverOf`, `native_meanZero_iff_cover` | `Torus2 = Fin 2 → UnitAddCircle`，即两个 ℝ/ℤ 的乘积。`Smooth` 使用 Lean 的平滑阶 `∞`，不是解析阶 `⊤`；不包含 Fourier 衰减或可解性字段。Haar 测度与 Mathlib `mFourierCoeff` 同一归一化。 |
| 真正的方向导数 | NativeAnalysis: `transport_native_cover`; NativeTheorems: `nativeTransport_eq`, `nativeTransport_smooth`, `nativeTransport_meanZero` | 原生算子沿环面平移曲线求导；证明它与周期覆盖上的真实 Fréchet 导数作用于 `(α,1)` 相等，并证明算子仍光滑、零均值。 |
| 所有无理 α 的零均值唯一性 | NativeTheorems: `native_solution_unique` | 使用真实 Fourier 系数唯一性、导数系数恒等式及非共振；没有加强 α 的假设。 |
| 对每个光滑右端存在光滑解的精确分类 | NativeTheorems: `native_smoothSurjective_iff` | 等价于存在有限实数 s≥0 与统一正下界。GeneralInverse 构造实际解；Necessity 选注入频率并构造一个固定 Rapid 右端；Classification 将它重构为实际光滑函数，利用解系数有界性排除可解。 |
| 每个实数 r、全部 s≥0 的 Sobolev 估计，含端点 | NativeTheorems: `native_sobolev_iff`; FullTarget: `native_sobolev_summable` | 精确条件是 `HasDivisorBound α s`，即 ∃c>0，∀k≠0，c≤⟨k⟩^s\|αk₁+k₂\|。没有以所有更大 s 的估计替代端点。必要性测试实际光滑零均值 Fourier 单频函数；充分性使用实际导数 Fourier 恒等式逐项比较。 |
| 指定 Euclidean Fourier/Sobolev 范数 | Representation: `nativeHNorm_eq_cover`; Sobolev: `summable_energyTerm` | `weight k = sqrt(1+k₁²+k₂²)`，保留任意实数阶 r；与覆盖表示的范数是严格相等，不只是等价。所有平滑函数的相关无限和均证明收敛。 |
| α*=√2−1 的最小损失恰为 1 且取到 | NativeTheorems: `native_quadratic_sobolev_iff` | Arithmetic 用代数共轭证明 s=1 下界；ArithmeticSharp 用 Dirichlet 逼近排除每个 0≤s<1。这是参考允许的替代路线。 |
| 原题有序混合偏导的 C^m 范数 | NativeAnalysis: `mixedDerivative_cover`, `nativeCNorm_eq_cover`; FullTarget: `native_CMValues_bounded` | 使用 `replicate a false ++ replicate b true` 对应 ∂x^a∂y^b，范围是 a+b≤m；不把 all-word 范数直接改名成题目范数。每个上确界均证明有界；有限指标上的最大值以等价的联合上确界表达。 |
| 全部 m≥0 的 C^(m+4)→C^m 估计、独立于 F 的常数、实际解和唯一性 | FullTarget: `native_fixed_full_solution`, `native_fixed_Cm_bound` | CubicBound 独立证明二维三次衰减可和性，得到真正 m+4 输入估计；CNorm 将所有 a+b≤m 的偏导统一到有限实常数 `fourConstant m`。没有用外部 m+5 结果替代。 |

## 函数与序列的连接确有证明

公开移植的 SmoothFourierData 从真实积分、分部积分和实际导数界推出 Rapid，并利用 Mathlib 实际环面的 Fourier 基完成重构。FourierBridge 反过来证明任意 Rapid 级数的真实 Fourier 积分恢复其系数，并推导所有频率（包括零频率）的坐标导数恒等式。Representation 给出两个实际环面表示以及周期覆盖的双向构造，NativeAnalysis 给出偏导与范数的精确对应。这些不是证书字段或额外假设。

## 参考文中的可选补充不冒充已形式化

本轮覆盖全部 task.md 目标，但没有逐行形式化 reference.md 的所有可选强化：最近整数 Q_s 与 D_s 的等价改写、最佳常数 1/(2πD_s)、无理性指数 μ 的开闭端点表述、显式 Pell 频率公式和各个最佳算术常数尚未分别建立 Lean 声明。任务不要求这些特定路线；形式化采用统一正下界和 Dirichlet 逼近。原题也没有声称四阶是 C^m 尺度的最优损失。

## 可复核证据与来源

`manifest.json` 锁定 task/reference/rubric/COVERAGE、每个模块、模块顺序及共享生成的 CurrentAudit。`verification-report.json` 和 `declarations.json` 保存当前源码的实际编译与全部 MathGauge 声明的动态公理闭包审计。允许的基础公理仅 propext、Classical.choice、Quot.sound；没有额外公理或未证明占位符。

公开移植来源及 API 兼容修订详见 `PORTING.md` 和 `../external/provenance.json`。没有编译或认证整个外部 Navier–Stokes 工程；本轮证据仅针对 manifest 的实际闭包。原作者自查材料保存在 `../history/round1/`，本轮独立 AI 审核在 `../round2-review.json`。没有候选模型试跑，也没有人工批准。
