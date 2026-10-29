# MG-GF106 作者 Lean 覆盖

当前题面 0.1.1 的全部 6 阶段均有作者证明、反例或审计对应。机器核验与语义审核是不同证据；人工审核仍待完成，未运行候选模型。

定义和已证辅助声明从母题作者源显式收录；逐文件来源/原哈希/当前哈希见 alignment.json 的 attribution。新增声明不借用母题旧编译记录，全部源在当前 manifest 中重新绑定。

## S1

任意F⊆A且每个H陪集至多一代表；原切片定义。 证明F×B加法注入、平移两两不交、自然数card乘积界；不要求特征2。

声明：`Bridge.MathGauge.F106.slice_difference`, `Answer.MathGauge.F106.representative_sum_injective`, `Answer.MathGauge.F106.representative_translates_disjoint`, `Answer.MathGauge.F106.representative_product_bound`。

## S2

任意阿贝尔群、有限A、非空切片及倍增界。 显式Ruzsa有限覆盖路线，不增加商有限或K正性假设。

声明：`Reference.MathGauge.F106.dense_coset_cover`, `Bridge.MathGauge.F106.lift_cover`。

## S3

F⊆A，商映射像相等iff覆盖；任意覆盖card≥c_H(A)且可取得。 有限归纳真实选择代表，商像可有重复，不默认π在A单射。

声明：`Answer.MathGauge.F106.quotient_eq_iff`, `Answer.MathGauge.F106.covers_iff_image`, `Answer.MathGauge.F106.select_image_representatives`, `Answer.MathGauge.F106.cosetCount_le_cover`, `Answer.MathGauge.F106.exists_minimal_cover`, `Answer.MathGauge.F106.cosetCount_bound`。

## S4

整数A={0,1,2},H=0,K=5/3；全部非空切片为单点。 和集={0,1,2,3,4},c_H(A)=3>K；求和真实只能得c*A≤c*K*A，密度因子不能消去。

声明：`Answer.MathGauge.F106.densityExample`, `Answer.MathGauge.F106.density_example_sum`, `Answer.MathGauge.F106.density_factor_counterexample`, `Answer.MathGauge.F106.singleton_slices_bot`, `Answer.MathGauge.F106.sum_slice_bounds`。

## S5

任意H≤L及任意原H覆盖F⊆A；B_H非空。 B_H⊆B_L，真实从F选L最小代表子集E，cardE=c_L(A)并满足新切片界。

声明：`Answer.MathGauge.F106.slice_mono_subgroup`, `Answer.MathGauge.F106.enlarge_subgroup_reselect`。

## S6

完整Answer覆盖S1–S5，逐阶段分别保留条件。 Core原定义不变；所有有限选择、反例和改变子群的结论均有当前proof term。

声明：`Answer.MathGauge.F106.representative_product_bound`, `Answer.MathGauge.F106.covers_iff_image`, `Answer.MathGauge.F106.exists_minimal_cover`, `Answer.MathGauge.F106.density_factor_counterexample`, `Answer.MathGauge.F106.enlarge_subgroup_reselect`, `Reference.MathGauge.F106.dense_coset_cover`。

编译入口及逐模块顺序由 manifest.json 明示；CurrentAudit.lean 遍历全部本地声明的传递公理闭包。正式证据为 verification-report.json、declarations.json 和 logs/，只承认与清单完全相同的源哈希。源码检查没有 sorry/admit/新增公理。
