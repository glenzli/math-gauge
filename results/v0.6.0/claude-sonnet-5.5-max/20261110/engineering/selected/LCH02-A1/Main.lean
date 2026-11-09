import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space
import formal_oet.vol_01.ch_02_operator_bounds.lch02_matrix
import formal_oet.vol_01.ch_02_operator_bounds.lch02_bounds
import formal_oet.vol_01.ch_02_operator_bounds.lch02_chain

/-!
# LCH02 · 有限复合与路径节群（`source/02-operator-bounds.md` 选段）

**来源与署名**：本形式化是对 Zhe Li（Glen Li / glenzli，ORCID https://orcid.org/0009-0006-6536-3453）
《The Operator Evolution Theory》第一卷第 2 章所选命题的 Lean 4 改编；定理内容、记号与证明思路均出自原作者，
并非形式化者的原创理论。作品主页 https://glenzli.com/books/oet/ ，DOI https://doi.org/10.5281/zenodo.21457931 ，
许可 CC BY 4.0（https://creativecommons.org/licenses/by/4.0/）。改动说明：Lean 形式化、表示约定与辅助引理为新增；
不代表原作者背书。

本文件导入全部目标模块；20 项义务与声明的对应如下
（命名空间均为 `formal_oet.vol_01.ch_02_operator_bounds`）。

| 义务 | 文件 | 主要声明 |
| --- | --- | --- |
| CH02-D01 | `lch02_bounds` | `IsLipMatrix`、`IsLipMatrixOn`、`lipCerts`、`lipCertsOn` |
| CH02-D02 | `lch02_bounds` | `IsCoLipMatrixOn`、`coLipCertsOn`、`coLipCerts` |
| CH02-D03 | `lch02_matrix` | `arrowEntry`、`arrowEntry_mul`、`sum_arrowEntry_mul_mul` |
| CH02-D04 | `lch02_matrix` | `arrowEntry_one`、`orderedProd`、`orderedProd_zero`、`orderedProd_succ` |
| CH02-D05 | `lch02_chain` | `chainComp`、`chainList`、`intermediateImage` 及其对应引理 |
| CH02-D06 | `lch02_matrix` | `IsIndexPath`、`IsPositivePath`、`HasZeroFactor` |
| CH02-P01 | `lch02_bounds` | `mem_lipCerts_iff_scalar` |
| CH02-P02 | `lch02_bounds` | `lipCertsOn_antitone` |
| CH02-P03 | `lch02_bounds` | `lipCerts_subset_lipCertsOn` |
| CH02-P04 | `lch02_chain` | `lip_comp` |
| CH02-P05 | `lch02_bounds` | `coLipCertsOn_antitone` |
| CH02-P06 | `lch02_bounds` | `coLipCerts_subset_coLipCertsOn` |
| CH02-P07 | `lch02_bounds` | `coLipCerts_entry_eq_zero` |
| CH02-P08 | `lch02_chain` | `coLip_comp`、`nonempty_operator_image_of_mem_coLipCertsOn` |
| CH02-P09 | `lch02_chain` | `chain_lip`、`chain_lip_operatorChain` |
| CH02-P10 | `lch02_chain` | `chain_coLip`、`chain_coLip_operatorChain` |
| CH02-P11 | `lch02_chain` | `identity_mem_lipCertsOn`、`chain_lip_zero` |
| CH02-P12 | `lch02_chain` | `identity_mem_coLipCertsOn`、`chain_coLip_zero` |
| CH02-P13 | `lch02_matrix` | `prodEntry_eq_zero_iff_forall_path_hasZeroFactor`、`prodEntry_eq_zero_iff_one` |
| CH02-P14 | `lch02_matrix` | `prodEntry_pos_iff_exists_positivePath`、`prodEntry_pos_iff_one` |
-/
