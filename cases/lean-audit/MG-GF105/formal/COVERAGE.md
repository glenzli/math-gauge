# MG-GF105 作者 Lean 覆盖

当前题面 0.1.1 的全部 6 阶段均有作者证明、反例或审计对应。机器核验与语义审核是不同证据；人工审核仍待完成，未运行候选模型。

定义和已证辅助声明从母题作者源显式收录；逐文件来源/原哈希/当前哈希见 alignment.json 的 attribution。新增声明不借用母题旧编译记录，全部源在当前 manifest 中重新绑定。

## S1

任意阿贝尔加法群，A/B有限，B非空；不要求群或商群有限。 在A.powerset有限集合里选包含极大的平移两两不交族，同一个F同时满足覆盖及自然数乘积计数界。

声明：`Extensions.MathGauge.F105.ruzsa_maximal_cover`。

## S2

原切片非空、任意实K满足倍增界，无独立K>0条件。 同一陪集差在H，切片含于A控制和集，正cardB除法给原常数。

声明：`Bridge.MathGauge.F105.slice_difference`, `Bridge.MathGauge.F105.lift_cover`, `Candidate.MathGauge.F105.dense_coset_cover`。

## S3

所有有限A与H；任意F⊆A时，覆盖iff商像相等，min card=商像card。 显式有限归纳选单射代表，不引入代表证书；再以S2给最小数上界。

声明：`Extensions.MathGauge.F105.quotient_eq_iff`, `Extensions.MathGauge.F105.covers_iff_image`, `Extensions.MathGauge.F105.select_image_representatives`, `Extensions.MathGauge.F105.cosetCount_le_cover`, `Extensions.MathGauge.F105.exists_minimal_cover`, `Extensions.MathGauge.F105.cosetCount_bound`。

## S4

整数A={0,1},H=0,x=0,K=3/2；有效替代参考答案中的偶数子群。 切片={0}且倍增界成立，任何F⊆切片不能覆盖1；全部反例条件逐一形式证明。

声明：`Extensions.MathGauge.F105.sliceExample`, `Extensions.MathGauge.F105.slice_example_sum`, `Extensions.MathGauge.F105.representatives_not_in_slice`。

## S5

原倍增界保持，但B可空；求乘积界。 非空用除法恢复乘积，空时F=A；另给A={0},H=0,x=1商式除零失败完整反例。

声明：`Extensions.MathGauge.F105.product_cover_allow_empty`, `Extensions.MathGauge.F105.zero_denominator_quotient_fails`。

## S6

审计原S2全过程，辨认非空只在除法所需。 原Candidate对齐；S1最大性、S3最小性与S5边界均为新增证明。经典DecidableEq不意味着G有限。

声明：`Bridge.MathGauge.F105.slice_difference`, `Bridge.MathGauge.F105.lift_cover`, `Candidate.MathGauge.F105.dense_coset_cover`, `Extensions.MathGauge.F105.cosetCount_bound`, `Extensions.MathGauge.F105.product_cover_allow_empty`。

编译入口及逐模块顺序由 manifest.json 明示；CurrentAudit.lean 遍历全部本地声明的传递公理闭包。正式证据为 verification-report.json、declarations.json 和 logs/，只承认与清单完全相同的源哈希。源码检查没有 sorry/admit/新增公理。
