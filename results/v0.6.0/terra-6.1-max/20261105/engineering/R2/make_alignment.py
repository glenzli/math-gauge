import json

ledger = json.load(open('../input/obligations.json', encoding='utf-8'))
entries = {}

def add(id, names, rep, deps=()):
    entries['CH03-' + id] = {
        'id': 'CH03-' + id,
        'status': 'complete',
        'declarations': [{'file': 'Main.lean', 'name': 'Chapter3.' + n} for n in names.split()],
        'representation': rep,
        'dependencies': ['CH03-' + dep for dep in deps],
    }

add('D01', 'constComponents identityComponents activeComponents components_partition',
    '集合谓词直接给出常值、非恒常逐点零距、其补集；components_partition 证明常值优先的互斥穷尽。')
add('D02', 'fiber componentFiber fiber_components fiber_intersection',
    '以冻结子族复合伪度量的零距离和 U 成员定义纤维；单分量与有限非空交集对应由定理证明。')
add('D03', 'pointRelation zeroRelation imageZeroSetoid imageQuotient imageClass fiberPreorder zeroRelation_fiber',
    '有序点对限制在 U×U；像点子类型上的零距 setoid 构造实际商及其像类，zeroRelation_fiber 证明与全子族纤维对应。', ['D02'])
add('D04', 'admissibleRadius zeroRadius admissibleRadius_iff_ball admissibleRadius_iff_fiber zeroRadius_empty_admissibles',
    '有限正 ENNReal 半径的合法球取 sSup，空集上确界为 0；所给定理把逐点条件与球及子族纤维包含对应。', ['D02'])
add('D05', 'uniformRadius zeroMatrix',
    'uniformRadius 对 y∈A 在固定评估域 U 取下确界；zeroMatrix 输入 i、输出 j，等于 A=U 的单分量统一半径。', ['D04'])
add('D06', 'ScaleFamily diameter diameterScale diameter_monotone thresholdType threshold_four_spec',
    '尺度只要求非空域上的单调性；直径是两重上确界。Bool 二元组的四个取值与严格尺度判断和非严格半径判断逐一等价。', ['D05'])
add('D07', 'totallyBoundedAtAllScales totallyBounded_iff_finite_nets finite_cover_finite finite_nonempty_cover_bounds',
    '冻结内部网以有限子集为中心；冻结覆盖数的最小值取得和无有限网时为顶均已证明，熵取 log2；这里证明全有界当且仅当每个有限正尺度有内部有限网。')
entries['CH03-D07']['declarations'] += [
    {'file':'formal_oet/vol_01/ch_01_foundations/metric_entropy.lean','name':'formal_oet.vol_01.ch_01_foundations.' + n}
    for n in ['InternalEpsilonNet','covering_number','covering_number_attained','covering_number_eq_top_iff','metric_entropy','subfamily_metric_entropy']]
add('D08', 'entropyDifferenceValid mappingEntropyDifference mappingEntropy_finite_values mappingEntropy_infinite_cases',
    '定义仅接受非空 U、两非空子族、有限正精度及至少一端有限覆盖的证明；有限实差与正负无穷分支分别证明。', ['D07'])
add('P01-01','const_zero_row','常值输出在任意 x,y∈U 为零，零行的有限 ENNReal 和亦为零。',['D01'])
add('P01-02','const_colip_zero','正输入距离和输出零距离代入合法 co-Lip 矩阵，强制对应条目为零。',['D01'])
add('P01-03','identity_preserves_distance dist_eq_of_zero_endpoints','每个端点与其像零距，三角不等式双向得到点对距离相等。',['D01'])
add('P02-01','active_comp','两算子作用顺序为 g*f，第二个限制域是 f.func 的实际像集；证明有效分量包含。',['D01','P01-03','P02-03','P04-01'])
add('P02-02','seqOp seqActive seqOp_eq_reverse_prod active_seq','列表按输入先后递归；每步把限制域替换为实际像，反转乘积对应正文次序，并证明包括空链的包含。',['D01','P02-01'])
add('P02-03','identity_comp','两个恒等分量的逐点零距可传递，保距同时排除复合结果落入常值优先分支。',['D01','P01-03'])
add('P03-01','SwapExample.metric SwapExample.U_nonempty SwapExample.domain_U SwapExample.image_U SwapExample.square SwapExample.component_sets_exact SwapExample.reverse_inclusions_fail',
    'Option Bool 的 none 为吸收元，some false/true 为两点；合法扩展伪度量、换位、实际像域及两条逆包含失败均有证明。',['D01'])
add('P04-01','outer_const','若 g 在 f(U) 的输出恒零距，则 g*f 在 U 恒零距。',['D01'])
add('P05-01','inner_const_of_single_row','单行 Lip 界作用在实际像点；同分量零距乘任意 ENNReal 系数包括无穷仍为零。',['D01'])
add('P06-01','fiber_target_zero','任意两个目标子族零距，由逐分量对称和三角不等式得到纤维相等。',['D02'])
add('P06-02','fiber_image_cover','每个像目标有原像成员，且其纤维族的并集恰为 U，允许 U 为空。',['D02'])
add('P06-03','fiber_equal_or_disjoint fiber_image_cover','任意两纤维相交则目标零距并相等，否则不交；配合非空与覆盖构成去重分划。',['D02','P06-01','P06-02'])
add('P06-04','fiber_intersection fiber_components','对非空 J，复合距离零的纤维严格等于所有单分量纤维的交集。',['D02'])
add('P06-05','fiber_antitone','若 J⊆K，K 的全部零距条件蕴含 J 的条件。',['D02'])
add('P06-06','fiber_singleton fiber_all_subset','单元素子族恢复该分量，全指标纤维包含每一单分量纤维。',['D02','P06-05'])
add('P06-07','identity_component_fiber','对任意目标 y，恒等分量把输出零距纤维等同于 U 内输入零距类。',['D01','D02'])
add('P06-08','constant_component_fiber','任一实际像目标的纤维是 U；与该目标正距离的任意目标具有空纤维。',['D01','D02'])
add('P07-01','image_factor_iff','实际像点子类型上的 T 若按输入给出 B 的值，则 A 的点值相等关系包含于 B 的。',['D03'])
add('P07-02','image_factor_iff','对每个实际像点选择 U 内代表元并利用包含关系证明良定义和赋值公式；无需 U 非空。',['D03'])
add('P07-03','image_factor_both_iff','两个方向的点值因子化等价于两个受限相等关系相等。',['D03','P07-01','P07-02'])
add('P07-04','factor_scalar_lip','在 A 的实际像子类型取代表元，以有限正 KA 的除法及 B 的上界得到 LB/KA 界；允许更一般的 LB。',['D03'])
add('P08-01','quotient_factor_iff','实际像集的零距商上用代表元选择和 Quotient.lift 构造映射，并用 sound/exact 证明双向与赋值公式。',['D03'])
add('P08-02','quotient_factor_both_iff','两个商映射存在等价于零距点对关系相等。',['D03','P08-01'])
add('P08-03','pointRelation_eq_zeroRelation separated_factor_criteria','在 A、B 各自实际像集上分别假设分离性，证明点关系等于零距关系及两类判据一致。',['D03','P07-01','P07-02','P08-01'])
add('P09-01','fiberPreorder_refl fiberPreorder_trans','固定公共 U，零距关系包含的自反性和传递性。',['D03'])
add('P09-02','fiberPreorder_chain','自然数索引链每步包含，归纳证明所有 a≤b 的层间包含。',['D03','P09-01'])
add('P09-03','fiberPreorder_chain_strict','一步真包含的差集点同时见证端点真包含；返回显式差集成员。',['D03','P09-02'])
add('P11-01','constant_subfamily_fiber','若 J 的所有分量在 U 常值，则每个 y∈U 的像目标 J 纤维等于 U。',['D01','D02'])
add('P11-02','constant_subfamily_radius constant_radius_top constant_uniformRadius_top','全部有限正半径均可取，故每个基点及 U 上统一下确界都为顶。',['D01','D04','D05'])
add('P11-03','SwapExample.infiniteMetric SwapExample.twoGauge_extended SwapExample.U_nonempty SwapExample.domain_U SwapExample.infinite_input_uniform SwapExample.infinite_radius_not_constant','两非吸收点和恒等算子，输入距离为顶；分别取同一无穷距离输出和另一有限离散输出，两种通道半径均为顶但输出不常值。',['D01','D04','D05','P03-01'])
add('P12-01','identity_image_fiber','恒等分量在 U 上保距，将像目标纤维化成输入零距类。',['D01','D02','P01-03'])
add('P12-02','identity_radius_lower','有限正 r 的输入球只含零距点时 r 为合法零化半径。',['D01','D04','P01-03'])
add('P13-01','radius_subfamily_inf radius_subfamily_min_attained','先证明点态半径等于子族单分量半径下确界，再以有限非空性证明最小值被某分量取得。',['D02','D04'])
add('P13-02','uniform_subfamily_inf uniform_subfamily_min_attained','交换基点和分量的下确界，有限非空时给出达到最小值的分量及最小性。',['D05','P13-01'])
add('P13-03','uniform_subfamily_mono','J⊆K 时，更多输出零距要求使统一半径不增。',['D02','D04','D05'])
add('P14-01','fiber_zero_output','单分量纤维成员直接给出反向零距，由对称性得到正文方向。',['D02'])
add('P14-02','radius_strict_witness radius_zero_output','严格小于上确界时提取更大的合法有限正半径，借输入对称性证明输出零距。',['D04'])
add('P14-03','fiber_comp_zero_output','明确要求两像点属于 U₂，代入下游纤维成员判据获得复合输出零距。',['P14-01'])
add('P15-01','uniform_comp_propagate','实际像域上零距保持将内侧每个合法半径转成复合的合法半径，再取统一下确界。',['D04','D05'])
add('P15-02','uniform_comp_lip','由单通道 Lip 界和实际像域统一半径获得除以 L 的下界；证明对零和无穷统一有效。',['D04','D05','P18-01'])
add('P16-01','threshold_four threshold_four_spec','Bool² 四种值穷尽；每个值等价于互补不等式的相应组合，因而互斥。',['D06'])
add('P16-02','threshold_scale_mono threshold_four_spec','严格尺度判断在尺度阈值增大时保持，等价于第一位为真。',['D06'])
add('P16-03','threshold_radius_antitone threshold_four_spec','较大零化阈值能满足则较小阈值也满足，等价于第二位为真。',['D06'])
add('P17-01','scale_domain_mono','非空 B⊆A 时一般单调尺度不增，并保持小于阈值。',['D06'])
add('P17-02','radius_domain_antitone','每个 A 上合法的半径在更小评估域 B 仍合法；基点条件可放宽。',['D04'])
add('P17-03','uniformRadius_domain_antitone','同时缩小取下确界的基点集和评估域，统一半径不减。',['D05','P17-02'])
add('P17-04','SwapExample.metric SwapExample.finite_real_isometry SwapExample.diameter_U SwapExample.diameter_singleton SwapExample.scale_reverse_counterexample','两非吸收点的距离为 1，取全二点集和单点集以及阈值 1/2；finite_real_isometry 证明对应带吸收元实线的 {0,1}，尺度反向失败。',['D06','P03-01'])
add('P18-01','uniform_zero_output','输入距离严格低于 U 上半径下确界时，应用基点处单步零化判据。',['D05','P14-02'])
add('P18-02','uniform_output_separation','对前述零化判据取逆否，输出正距离推出输入距离至少统一半径。',['D05','P18-01'])
add('P18-03','insufficient_uniform_radius_witness','每个有限正 α 严格大于统一半径时构造域内两点；取 min(输出距离,1) 得有限正 ε，含无穷输出。',['D04','D05'])
add('P19-01','uniform_threshold_fiber','半径阈值不超过统一半径时，任意基点处该半径开球与 A 的交落入零距纤维。',['D04','D05','P18-01'])
add('P19-02','covering_image_le uniform_threshold_cover','将每个有限输入中心集映射到输出内部；有限像的基数不增，对所有中心集取下确界，自动包括空集和无有限覆盖。',['D07','P18-01'])
add('P19-03','log2_ereal_mono_of_one_le uniform_threshold_entropy','非空 B 的两端覆盖数至少 1，证明含顶情形的 log2 单调性后取对数。',['D07','P19-02'])
add('P21-01','diameter_upper small_diameter_iff_constant','在直径<τσ≤τN 下，统一半径阈值与所有输出点对零距等价。',['D06','P11-02','P18-01'])
add('P21-02','zero_image_cover_one small_diameter_cover_one','非空输出零距类有单点内部覆盖，非空集合覆盖数至少一。',['D07','P21-01'])
add('P22-01','finite_cover_finite finite_nonempty_cover_bounds finite_cover_entropy_real finite_mapping_entropy mappingEntropy_finite_values','有限非空域及其像的内部覆盖数正且有限，两子族熵为实数，映射熵差定义成立。',['D02','D07','D08'])
add('P23-01','constant_mapping_entropy','常值输出的覆盖数为 1、熵为 0，故合法熵差等于输入熵，允许输入熵为顶。',['D01','D07','D08'])
add('P23-02','covering_image_le covering_preimage_le identity_cover_eq','由保距向前推有限中心，向后为每个像中心选择原像，证明覆盖数及熵相等。',['D01','D07','P01-03'])
add('P23-03','identity_mapping_entropy','由良定性与两端覆盖数相等得到有限共同熵，从而熵差为零，不将顶减顶作为合法输入。',['D07','D08','P23-02'])
add('P24-01','covering_image_le scalar_lip_cover','ε/L 输入网的像在有限正 L 下是 ε 输出网，像中心数不超过原中心数。',['D07'])
add('P24-02','scalar_lip_entropy_bound','全有界保证所需输入及输出覆盖数有限；log2 单调和 EReal 减法给出正文下界。',['D07','D08','P24-01'])
add('P25-01','covering_preimage_le colip_cover','从输出中心选择 U 中原像，正有限 co-Lip 条目给 ε/K 输入网；未假定输出有有限网。',['D07'])
add('P25-02','colip_entropy_bound','输入全有界保证合法熵差和有限输入熵，允许输出熵为顶，按反向覆盖数不等式证明上界。',['D07','D08','P25-01'])
add('P26-03','point_constant_self_comp point_constant_self_comp_zero','点值相等经任意算子再次作用仍相等，故所有伪度量零距；同时明确再次输出为吸收元与否的定义域两分支。')
add('P27-01','positive_colip_radius_gap','任意正 co-Lip 条目（可为顶）反射输出零距，故严格小于点态半径的输入距离只能是零。',['D04','P14-02'])
add('P27-02','positive_colip_uniform_gap','任意输入点对的距离为零或至少统一半径；此结论甚至不要求半径严格为正。',['D05','P27-01'])

items = []
for obligation in ledger['obligations']:
    ident = obligation['id']
    if ident in entries:
        items.append(entries[ident])
    else:
        items.append({'id': ident, 'status':'incomplete', 'declarations': [],
            'representation': obligation['source_subpart'] + '：尚未给出所需完整构造和证明。',
            'dependencies': []})
assert len(items) == 92 and len(entries) == sum(x['status'] == 'complete' for x in items)
with open('alignment.json','w',encoding='utf-8') as out:
    out.write('{\n  "case_id": "MG-C003",\n  "version": "0.1.1",\n  "items": [\n')
    for i, entry in enumerate(items):
        out.write('    '+json.dumps(entry,ensure_ascii=False,separators=(',',':')) + (',' if i+1<len(items) else '')+'\n')
    out.write('  ]\n}\n')
print('complete',len(entries),'incomplete',len(items)-len(entries))
