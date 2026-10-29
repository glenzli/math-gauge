import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space
import formal_oet.vol_01.ch_02_operator_bounds.lip_matrix
import formal_oet.vol_01.ch_02_operator_bounds.decoupling
import formal_oet.vol_01.ch_02_operator_bounds.gauge_choice
import formal_oet.vol_01.ch_02_operator_bounds.matrix_composition
import formal_oet.vol_01.ch_02_operator_bounds.path_algebra
import formal_oet.vol_01.ch_02_operator_bounds.single_channel

/-! Explicit value aliases make every public declaration in the frozen source closure
reachable from the MathGauge axiom audit. No proposition is added as a hypothesis. -/
noncomputable section

namespace MathGauge.C002.Vendored.gauge_space
abbrev ExtendedPseudoMetric := @formal_oet.vol_01.ch_01_foundations.ExtendedPseudoMetric
abbrev ball := @formal_oet.vol_01.ch_01_foundations.ball
abbrev GaugeZeroRelated := @formal_oet.vol_01.ch_01_foundations.GaugeZeroRelated
abbrev IsSeparating := @formal_oet.vol_01.ch_01_foundations.IsSeparating
abbrev IsNonSeparating := @formal_oet.vol_01.ch_01_foundations.IsNonSeparating
abbrev gauge_zero_related_equivalence := @formal_oet.vol_01.ch_01_foundations.gauge_zero_related_equivalence
end MathGauge.C002.Vendored.gauge_space

namespace MathGauge.C002.Vendored.operator_space
abbrev Operator := @formal_oet.vol_01.ch_01_foundations.Operator
abbrev bot_operator := @formal_oet.vol_01.ch_01_foundations.bot_operator
abbrev operator_identity := @formal_oet.vol_01.ch_01_foundations.operator_identity
abbrev operator_compose := @formal_oet.vol_01.ch_01_foundations.operator_compose
abbrev dom := @formal_oet.vol_01.ch_01_foundations.dom
abbrev operator_image := @formal_oet.vol_01.ch_01_foundations.operator_image
abbrev op_dist := @formal_oet.vol_01.ch_01_foundations.op_dist
abbrev operator_space_nonabsorbing := @formal_oet.vol_01.ch_01_foundations.operator_space_nonabsorbing
abbrev op_dist_is_pseudo_metric := @formal_oet.vol_01.ch_01_foundations.op_dist_is_pseudo_metric
abbrev operator_gauge_space_textbook := @formal_oet.vol_01.ch_01_foundations.operator_gauge_space_textbook
abbrev op_dist_eq_top_of_dom_ne := @formal_oet.vol_01.ch_01_foundations.op_dist_eq_top_of_dom_ne
abbrev op_dist_separating_iff := @formal_oet.vol_01.ch_01_foundations.op_dist_separating_iff
abbrev restricted_eval := @formal_oet.vol_01.ch_01_foundations.restricted_eval
abbrev restricted_eval_basic_properties := @formal_oet.vol_01.ch_01_foundations.restricted_eval_basic_properties
abbrev OperatorChain := @formal_oet.vol_01.ch_01_foundations.OperatorChain
abbrev operator_chain_eq_prod := @formal_oet.vol_01.ch_01_foundations.operator_chain_eq_prod
end MathGauge.C002.Vendored.operator_space

namespace MathGauge.C002.Vendored.lip_matrix
abbrev IsLipMatrix := @formal_oet.vol_01.ch_02_operator_bounds.IsLipMatrix
abbrev restricted_lip_matrix_family_antitone := @formal_oet.vol_01.ch_02_operator_bounds.restricted_lip_matrix_family_antitone
abbrev global_lip_matrix_family_subset := @formal_oet.vol_01.ch_02_operator_bounds.global_lip_matrix_family_subset
abbrev IsCoLipMatrix := @formal_oet.vol_01.ch_02_operator_bounds.IsCoLipMatrix
abbrev restricted_colip_matrix_family_antitone := @formal_oet.vol_01.ch_02_operator_bounds.restricted_colip_matrix_family_antitone
abbrev global_colip_matrix_family_subset := @formal_oet.vol_01.ch_02_operator_bounds.global_colip_matrix_family_subset
abbrev single_component_lip_matrix_ineq := @formal_oet.vol_01.ch_02_operator_bounds.single_component_lip_matrix_ineq
abbrev colip_entry_eq_zero_of_output_zero_input_pos := @formal_oet.vol_01.ch_02_operator_bounds.colip_entry_eq_zero_of_output_zero_input_pos
abbrev operator_pair_image_distance_perturbation := @formal_oet.vol_01.ch_02_operator_bounds.operator_pair_image_distance_perturbation
abbrev operator_pair_image_distance_perturbation_rev := @formal_oet.vol_01.ch_02_operator_bounds.operator_pair_image_distance_perturbation_rev
abbrev operator_pair_lip_bound_of_pointwise_perturbation := @formal_oet.vol_01.ch_02_operator_bounds.operator_pair_lip_bound_of_pointwise_perturbation
abbrev operator_pair_colip_bound_of_pointwise_perturbation := @formal_oet.vol_01.ch_02_operator_bounds.operator_pair_colip_bound_of_pointwise_perturbation
end MathGauge.C002.Vendored.lip_matrix

namespace MathGauge.C002.Vendored.decoupling
abbrev lip_bound_of_single_input_row := @formal_oet.vol_01.ch_02_operator_bounds.lip_bound_of_single_input_row
abbrev positive_colip_entry_reflects_zero := @formal_oet.vol_01.ch_02_operator_bounds.positive_colip_entry_reflects_zero
abbrev bi_lip_scalar_bound := @formal_oet.vol_01.ch_02_operator_bounds.bi_lip_scalar_bound
abbrev positive_colip_channels_preserve_distinguishability := @formal_oet.vol_01.ch_02_operator_bounds.positive_colip_channels_preserve_distinguishability
end MathGauge.C002.Vendored.decoupling

namespace MathGauge.C002.Vendored.gauge_choice
abbrev PlanePoint := @formal_oet.vol_01.ch_02_operator_bounds.gauge_choice.PlanePoint
abbrev read_coordinate := @formal_oet.vol_01.ch_02_operator_bounds.gauge_choice.read_coordinate
abbrev coordinate_dist := @formal_oet.vol_01.ch_02_operator_bounds.gauge_choice.coordinate_dist
abbrev overlapping_dist := @formal_oet.vol_01.ch_02_operator_bounds.gauge_choice.overlapping_dist
abbrev shear_operator := @formal_oet.vol_01.ch_02_operator_bounds.gauge_choice.shear_operator
abbrev finite_part := @formal_oet.vol_01.ch_02_operator_bounds.gauge_choice.finite_part
abbrev finite_part_eq_dom := @formal_oet.vol_01.ch_02_operator_bounds.gauge_choice.finite_part_eq_dom
abbrev coordinate_dist_is_extended := @formal_oet.vol_01.ch_02_operator_bounds.gauge_choice.coordinate_dist_is_extended
abbrev gauge_families_are_extended := @formal_oet.vol_01.ch_02_operator_bounds.gauge_choice.gauge_families_are_extended
abbrev diagonal_matrix := @formal_oet.vol_01.ch_02_operator_bounds.gauge_choice.diagonal_matrix
abbrev triangular_matrix := @formal_oet.vol_01.ch_02_operator_bounds.gauge_choice.triangular_matrix
abbrev overlapping_diagonal_lip := @formal_oet.vol_01.ch_02_operator_bounds.gauge_choice.overlapping_diagonal_lip
abbrev coordinate_triangular_lip := @formal_oet.vol_01.ch_02_operator_bounds.gauge_choice.coordinate_triangular_lip
abbrev coordinate_cross_entry_lower_bound := @formal_oet.vol_01.ch_02_operator_bounds.gauge_choice.coordinate_cross_entry_lower_bound
end MathGauge.C002.Vendored.gauge_choice

namespace MathGauge.C002.Vendored.matrix_composition
abbrev matrix_mul := @formal_oet.vol_01.ch_02_operator_bounds.matrix_mul
abbrev matrix_id := @formal_oet.vol_01.ch_02_operator_bounds.matrix_id
abbrev RightChainLipBounded := @formal_oet.vol_01.ch_02_operator_bounds.RightChainLipBounded
abbrev right_chain_lip_matrix := @formal_oet.vol_01.ch_02_operator_bounds.right_chain_lip_matrix
abbrev RightChainCoLipBounded := @formal_oet.vol_01.ch_02_operator_bounds.RightChainCoLipBounded
abbrev right_chain_colip_matrix := @formal_oet.vol_01.ch_02_operator_bounds.right_chain_colip_matrix
abbrev finite_composition_local_matrix_bounds_textbook := @formal_oet.vol_01.ch_02_operator_bounds.finite_composition_local_matrix_bounds_textbook
abbrev lip_matrix_comp := @formal_oet.vol_01.ch_02_operator_bounds.lip_matrix_comp
abbrev colip_matrix_comp := @formal_oet.vol_01.ch_02_operator_bounds.colip_matrix_comp
abbrev lip_matrix_comp_exact := @formal_oet.vol_01.ch_02_operator_bounds.lip_matrix_comp_exact
abbrev colip_matrix_comp_exact := @formal_oet.vol_01.ch_02_operator_bounds.colip_matrix_comp_exact
abbrev zero_step_identity_matrix_lip_colip := @formal_oet.vol_01.ch_02_operator_bounds.zero_step_identity_matrix_lip_colip
end MathGauge.C002.Vendored.matrix_composition

namespace MathGauge.C002.Vendored.path_algebra
abbrev matrix_mul_eq_zero_iff := @formal_oet.vol_01.ch_02_operator_bounds.matrix_mul_eq_zero_iff
abbrev matrix_mul_pos_iff := @formal_oet.vol_01.ch_02_operator_bounds.matrix_mul_pos_iff
abbrev matrix_list_mul := @formal_oet.vol_01.ch_02_operator_bounds.matrix_list_mul
abbrev RightChainLipCertificateList := @formal_oet.vol_01.ch_02_operator_bounds.RightChainLipCertificateList
abbrev RightChainCoLipCertificateList := @formal_oet.vol_01.ch_02_operator_bounds.RightChainCoLipCertificateList
abbrev RightChainLipCertificateList.length_eq := @formal_oet.vol_01.ch_02_operator_bounds.RightChainLipCertificateList.length_eq
abbrev RightChainCoLipCertificateList.length_eq := @formal_oet.vol_01.ch_02_operator_bounds.RightChainCoLipCertificateList.length_eq
abbrev ExistsPositivePath := @formal_oet.vol_01.ch_02_operator_bounds.ExistsPositivePath
abbrev list_matrix_mul_pos_iff := @formal_oet.vol_01.ch_02_operator_bounds.list_matrix_mul_pos_iff
abbrev list_matrix_mul_eq_zero_iff := @formal_oet.vol_01.ch_02_operator_bounds.list_matrix_mul_eq_zero_iff
abbrev finite_matrix_product_entry_zero_positive_textbook := @formal_oet.vol_01.ch_02_operator_bounds.finite_matrix_product_entry_zero_positive_textbook
end MathGauge.C002.Vendored.path_algebra

namespace MathGauge.C002.Vendored.single_channel
abbrev HasScalarLipBound := @formal_oet.vol_01.ch_02_operator_bounds.HasScalarLipBound
end MathGauge.C002.Vendored.single_channel
