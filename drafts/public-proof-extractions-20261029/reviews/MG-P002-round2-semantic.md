# MG-P002 独立数学与语义复核

结论：**所审当前源码的数学和题面语义对齐通过，未发现阻断问题。** 这是由未参与 P002 代码编写的 P003 审阅者进行的源码复核；未改动 P002 文件，未重跑其编译。最终编译和完整公理闭包须由父任务按精确冻结源码另行验收。人工批准仍不能由本报告代替。

完整阅读了 task.md、reference.md、rubric.json、source-notes.md，以及 19 个当前 Lean 实现文件（包括三个借用文件，共同依赖闭包中的实际本地源码）。审阅期间新增的 `FullTarget.lean` 和移除重复范数定义后的 `Functions.lean` 已重新阅读。精确输入 SHA256 在配套 JSON 中记录；后续源码变化需要复核相应差异。

## 真实对象与量词

`Torus2 = UnitAddTorus (Fin 2)` 是实际 `(ℝ/ℤ)²`。`Smooth u` 只要求连续函数在实际商映射下的周期拉回为 `ContDiff ℝ ∞`；它没有把 Fourier 衰减、求解性或估计打包成假设。以周期光滑拉回定义环面光滑性与本题的标准环面光滑结构一致。`∞` 保留光滑范围，未改为解析函数要求。

`coordinateDerivative` 是对商环面真实平移曲线作 `deriv`，`transport` 为两坐标导数的指定线性组合。`coordinateDerivative_cover`、`mixedDerivative_cover`、`transport_native_cover` 把它们与真实平面 Fréchet/混合导数连接。`nativeTransport_smooth` 和 `nativeTransport_meanZero` 证明算子确实落在要求的光滑零均值类中。

`NativeSmoothSurjective` 量化每一个实际光滑零均值环面 forcing；`nativeSurjective_iff_cover` 在两个表示间双向转换，故没有只证明预先给定 Fourier 系数序列的特殊情形。`native_smoothSurjective_iff` 给全部无理 α 的精确有限实数损失判据，`native_solution_unique` 补上每个 forcing 的唯一性。显式逆在 `GeneralInverse.lean` 构造，规范环面固定方向逆在 `FullTarget.lean` 构造。

## Fourier 与规范化

借用代码的 `coefficient` 使用真实单位区间积分。`unitCoeff_of_hasDerivAt` 经真实分部积分和周期端值相等得到衰减；`rapid_coefficient` 从实际光滑性及紧单位方形上的导数界证明所有加权绝对矩可和。`contDiff_series` 反向使用可和导数控制和逐项微分，`series_coefficient` 使用 Mathlib 的实际 Fourier 重建。新增 `coefficient_series_eq` 对任意快速衰减序列恢复其真实 Fourier 系数。这些都是定理，不是 `Smooth` 的字段。

单位圆 Haar 测度为概率测度；产品环面与有限函数积环面的测度转换由 `measurePreserving_finTwoArrow` 完成。`native_coeff_eq_cover`、`native_meanZero_iff_cover` 对真实 Fourier 积分和均值给出精确相等，不只是未指定常数的范数等价。Fourier 乘子含 `omega = 2πi`，符号是 `α k₁ + k₂`，与题面一致。

## Sobolev 损失

`nativeHNorm r u` 按题面定义为 Euclidean 频率权重 `sqrt(1+k₁²+k₂²)` 的 `2r` 次幂乘系数模平方之和，再开平方。内部快速衰减和多项式界使用 L1 权重，但 `Weights.lean` 证明它与 Euclidean 权重的量化比较，并只在“存在有限损失”处取自然数上界；逐个实数 s 的端点判据没有被整数化。

`NativeSobolevEstimates` 保留 `∀ r : ℝ, ∃ C : ℝ, ∀ u` 的原量词和对 forcing 独立的有限常数。`native_sobolev_iff` 给出严格正统一小除数界的充要条件。必要方向对实际光滑单频函数测试 r=0，强制 C>0，再得到统一正下界；充分方向逐项比较可和能量。`native_sobolev_summable` 明确证明所有光滑函数的实阶范数和收敛，因此没有利用 Lean 非可和 `tsum` 的默认值。

平方根二方向用非零整数共轭乘积给 loss=1 的统一下界。`dirichlet_frequency` 和极限比较排除每个 `0≤s<1`，`native_quadratic_sobolev_iff` 因而精确得到 `[1,∞)`，包含端点。无需把参考稿可选的 Pell 列、Q_s 表述、最佳常数或无理性指数展开全部加入正式目标；rubric 明确允许等价判据和正确替代证明。

## 必要性的固定坏 forcing

重点完整核对了根任务编写的 `Necessity.lean`。`finite_positive_bound` 利用无理性保证任意有限频率集上的非零除数有正下界；`small_outside_finite` 由不存在任一自然数多项式界，在每个有限排除集之外选择更小除数。良基递归构造的 `q : ℕ → ℤ²` 是注入且不取零。

定义一个固定序列，在 `q n` 处取

`a(q n) = (n+1) · omega · pairDivisor α (q n)`，其余频率为零。

选择条件确保 `weight(q n)^n · ‖a(q n)‖ ≤ 2^(-n)`。对任何固定 p，n≥p 时权重至少为 1，故 p 阶加权项仍受同一几何级数控制；有限个早期项不影响可和性。这里无需额外强制频率模长单调，因为每一阶矩的可和性已直接建立。注入性使序列延拓的系数没有碰撞，且零频率确实为零。

同一 a 的形式逆在 `q n` 处恰等于 n+1，因此无界。`Classification.exists_smooth_unsolvable` 先固定实际函数 `f=series a`，由已证明的重建得到其系数正是 a；假设一个光滑周期解 u 后，由 Fourier 微分公式推出 u 的系数等于这个无界形式逆，与 `rapid_coefficient u` 所给绝对可和系数有界矛盾。这正确完成了“存在一个固定光滑坏 forcing”的量词桥，未将逐个坏频率冒充不可解性。

## 四阶 C 范数估计

`orderedWord a b` 和 `mixedDerivative_cover` 使用与题面完全相同的 `∂₁^a ∂₂^b` 次序。`cmNormCover`/`nativeCNorm` 是所有 a+b≤m 及所有点处实际导数模的上确界；`cmValues_bddAbove` 与 `native_CMValues_bounded` 证明有界，索引非空，故与题面的有限个导数上确界之最大值一致，没有用无界 `sSup` 默认值伪造范数。

新增 `summable_weight_inv_three` 用两个一维 `3/2` 次衰减乘积控制二维三次权重倒数。`coefficient_seminorm_bound_three` 因而只需 p+3 阶输入导数；逆的 l 阶导数需 p=l+1 阶 Fourier 矩，合计正好 l+4。`fourConstant_mono` 把所有 l≤m 统一到同一个只依赖 m 的有限实常数。该证明真正改进了借用代码的五阶输入，不是反转 C 范数的单调性。

`FullTarget.native_fixed_full_solution` 对真实环面 forcing 给规范零均值逆、实际方程、唯一性和所有 m 的 `C^(m+4) → C^m` 界。估计并未宣称四阶在 C 范数尺度最优，且没有把 Sobolev 的最小一阶损失移植为 C 范数的一阶损失。

## 限制与非阻断事项

本报告判断的是当前已读源码的数学语义；不声称独立重新编译上游整个 Navier–Stokes 项目，不声称验证其主定理，也不把本题的成功或历史估计差异当作真实候选模型结果。借用文件已有固定公开 commit/blob 与许可提示；父任务仍需完成版本、移植说明、精确模块清单及全闭包公理验收。本题已读实现未见 `sorry`、`admit`、额外公理或目标证书结构。

题面全部要求的终点在当前源码中有对应。剩余验收是精确源码的编译、公理闭包与证据记录，而非本次审查发现的数学缺口。Human review remains pending.
