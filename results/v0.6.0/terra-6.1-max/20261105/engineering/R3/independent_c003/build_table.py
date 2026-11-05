import json

counts = [3,3,1,2,1,8,4,3,3,3,3,2,3,3,2,3,4,3,3,1,2,1,3,2,2,3,2,2,5,4]
ids = [f"CH03-D{x:02d}" for x in range(1,9)] + [f"CH03-P{p:02d}-{q:02d}" for p,n in enumerate(counts,1) for q in range(1,n+1)]
assert len(ids) == 92 and len(set(ids)) == 92

entries = {}
def add(id, names, rep, deps=(), status="complete"):
    entries[id] = {"id":id, "status":status,
       "declarations":[{"file":"Main.lean", "name":"Chapter3."+n} for n in names.split()],
       "representation":rep, "dependencies":list(deps)}

add('CH03-D01','constComponents identityComponents activeComponents components_partition','三类指标在 U 上依次为输出零距、非恒常且逐点零距、其余指标；证明常值优先及分划。')
add('CH03-D02','fiber componentFiber subfamily_zero_iff fiber_intersection','纤维用冻结子族伪度量零距定义，证明与逐分量零距及非空子族交集对应。')
add('CH03-D03','pointRelation zeroRelation fiberPreorder imageZeroSetoid ImageQuotient zeroRelation_fiber','点对关系限制在 U×U；像商为实际像上的族零距商；预序是关系包含并证明与全子族纤维对应。',('CH03-D02',))
add('CH03-D04','admissibleRadius radius strict_radius_zero','合法半径要求有限正且受限球的输出零距；radius 是这些半径在 ENNReal 的上确界，允许零及无穷。')
add('CH03-D05','uniformRadius zeroMatrix uniform_le_radius','统一半径是指定基点集上的下确界；zeroMatrix 的 i,j 分别为输入列和输出行。',('CH03-D04',))
add('CH03-D06','InputScale diameterScale thresholdType threshold_four threshold_four_distinct','输入尺度在非空子集间单调，默认直径为点对距离上确界；布尔对使用严格尺度阈值和非严格零化阈值。',('CH03-D05',))
add('CH03-D07','TotallyBoundedIn totallyBoundedIn_iff_nets','全有界用任意有限正精度覆盖数有限定义，证明等价于有限内部网；其余覆盖数及熵复用冻结定义。')
entries['CH03-D07']['declarations'] += [{"file":"formal_oet/vol_01/ch_01_foundations/metric_entropy.lean","name":"formal_oet.vol_01.ch_01_foundations."+n} for n in ('InternalEpsilonNet','covering_number','covering_number_attained','covering_number_eq_top_iff','covering_number_empty','metric_entropy','metric_entropy_nonneg','metric_entropy_empty','subfamily_metric_entropy')]
add('CH03-D08','EntropyDifferenceDomain entropyDifference entropy_real_of_cover_finite entropy_top_of_cover_top entropy_difference_finite entropy_difference_input_infinite entropy_difference_output_infinite','非空域、有限正精度和两个非空子族，要求至少一个覆盖数有限；定义扩展实数熵差并证明有限及两种单侧无穷分支。',('CH03-D07',))
add('CH03-P01-01','const_zero_row','常值分量的输出及零行和均为零。',('CH03-D01',))
add('CH03-P01-02','const_colip_zero','输出零距离与正输入距离迫使任一合法 co-Lip 条目为零，包括无穷。',('CH03-D01',))
add('CH03-P01-03','identity_preserves_distance dist_eq_of_zero_endpoints','两端点各与其像零距，双向三角不等式给出保距。',('CH03-D01',))
add('CH03-P02-01','active_comp','g*f 为先 f 后 g，外侧使用 f(U) 实际像域。',('CH03-D01','CH03-P01-03','CH03-P02-03','CH03-P04-01'))
add('CH03-P02-02','seqOp seqActive seqOp_eq_reverse_prod active_seq','列表顺序为实际输入先后，递推各像域并含空列表恒等基例。',('CH03-D01','CH03-P02-01'))
add('CH03-P02-03','identity_comp','两个恒等分量复合仍逐点零距，并由保距排除常值分支。',('CH03-D01','CH03-P01-03'))
add('CH03-P04-01','outer_const','外侧在内侧实际像域上常值，复合在 U 上常值。',('CH03-D01',))
add('CH03-P05-01','inner_const_of_single_row','输出行只含同分量输入时，单行 Lip 界传递内侧常值；系数允许无穷。',('CH03-D01',))
add('CH03-P06-01','fiber_target_zero','任意两个目标子族零距时，相应纤维相等。',('CH03-D02',))
add('CH03-P06-02','fiber_image_cover','每个像目标纤维非空且并集恰为 U。',('CH03-D02',))
add('CH03-P06-03','fiber_equal_or_disjoint fiber_image_cover','纤维相等或不交；结合非空及覆盖性质即去重分划。',('CH03-D02','CH03-P06-01','CH03-P06-02'))
add('CH03-P06-04','fiber_intersection','非空子族纤维是全部单分量纤维之交。',('CH03-D02',))
add('CH03-P06-05','fiber_antitone','J⊆K 时 K 纤维包含于 J 纤维。',('CH03-D02',))
add('CH03-P06-06','fiber_singleton fiber_all_subset','单元素子族等于单分量纤维，全指标子族包含于每个单分量纤维。',('CH03-D02','CH03-P06-05'))
add('CH03-P06-07','identity_component_fiber','恒等分量的任意目标纤维等于 U 内输入零距类。',('CH03-D01','CH03-D02'))
add('CH03-P06-08','constant_component_fiber','常值分量在像目标的纤维为 U，正距离目标的纤维为空。',('CH03-D01','CH03-D02'))
add('CH03-P07-01','point_factor_iff','像值映射给出点值关系包含。',('CH03-D03',))
add('CH03-P07-02','point_factor_iff','对每个像点选择 U 内原像构造映射；证明代表元无关及赋值，U 空时也成立。',('CH03-D03',))
add('CH03-P07-03','point_factor_both_iff','双向像值因子化等价于点值关系相等。',('CH03-D03','CH03-P07-01','CH03-P07-02'))
add('CH03-P07-04','point_factor_lip','实际像域任意两点选 U 内原像，正有限 K 和有限 L 得到 L/K 标量界。')
add('CH03-P08-01','imageClass imageClass_surjective imageClass_eq_iff factor_surjective_iff quotient_factor_iff','实际像商由族零距 setoid 构造；通过满射核包含构造商映射并证明指定赋值公式及逆向。',('CH03-D03',))
add('CH03-P08-02','quotient_factor_both_iff','应用单向商因子化得到双向关系相等判据。',('CH03-D03','CH03-P08-01'))
add('CH03-P08-03','SeparatesImage point_zero_relation_eq separated_factor_criteria','仅假设各实际像集分别分离，证明点值与零距关系相等及两组判据对应。',('CH03-D03','CH03-P07-01','CH03-P07-02','CH03-P07-03','CH03-P08-01','CH03-P08-02'))
add('CH03-P09-01','fiberPreorder_refl fiberPreorder_trans','固定 U 上的关系包含自反且传递。',('CH03-D03',))
add('CH03-P09-02','fiberPreorder_chain','自然数指标链中任意 a≤b 的关系包含。',('CH03-D03','CH03-P09-01'))
add('CH03-P09-03','fiberPreorder_chain_strict','链中 r→r+1 真包含推出首末真包含，并显式给出末关系中而首关系外的点对。',('CH03-D03','CH03-P09-02'))
add('CH03-P11-01','const_subfamily_fiber','J 内所有分量常值时，任意 U 中基点的像目标纤维为 U。',('CH03-D01','CH03-D02'))
add('CH03-P11-02','const_subfamily_radii','任何输入距离下，常值输出子族每个基点的半径及统一半径均为无穷。',('CH03-D01','CH03-D02','CH03-D04','CH03-D05'))
add('CH03-P12-01','identity_fiber_at_image','恒等分量在像目标上的纤维为基点的 U 内零距类。',('CH03-D01','CH03-D02','CH03-P01-03'))
add('CH03-P12-02','identity_radius_lower','球内仅零距时，有限正半径是合法半径，故点态半径不小于它。',('CH03-D01','CH03-D04','CH03-P01-03'))
add('CH03-P14-01','fiber_zero','单分量纤维成员经距离对称性得到所需次序的输出零距。',('CH03-D02',))
add('CH03-P14-02','strict_radius_zero strict_radius_zero_symm','从严格小于上确界提取有限正合法半径，并用对称性得到输出零距。',('CH03-D04',))
add('CH03-P14-03','fiber_zero_composite','取两个上游像点代入下游纤维判据；所述成员关系已保证第二像点在下游域。',('CH03-D02','CH03-P14-01'))
add('CH03-P15-01','composition_radius_zero_preserving','下游在实际像域反映指定零距时，每个上游合法半径对复合仍合法，再对基点取下确界。',('CH03-D04','CH03-D05'))
add('CH03-P16-01','threshold_four threshold_four_distinct','四种布尔对穷尽，且两两不同。',('CH03-D06',))
add('CH03-P16-02','threshold_first_mono','尺度阈值增加时第一位为真保持。',('CH03-D06',))
add('CH03-P16-03','threshold_second_antitone','零化阈值增加时第二位为真的通道不增。',('CH03-D06',))
add('CH03-P17-01','scale_domain_mono','对任意单调尺度，非空 B⊆A 时尺度及严格阈值判断单调。',('CH03-D06',))
add('CH03-P17-02','radius_mono_domain','评估域缩小时任意原合法半径仍合法；结论对所有基点更强。',('CH03-D04',))
add('CH03-P17-03','uniform_mono_domain','同时缩小基点集合和评估域，统一半径不减。',('CH03-D04','CH03-D05','CH03-P17-02'))
add('CH03-P18-01','strict_uniform_zero','输入距离严格小于统一半径时输出零距。',('CH03-D05','CH03-P14-02'))
add('CH03-P18-02','positive_output_lower_bound','输出距离严格为正时，输入距离不小于统一半径。',('CH03-P18-01',))
add('CH03-P18-03','small_uniform_radius_witness','每个规定的有限正 α 由不合法球产生两点，取 ε=min(1,输出距离)，覆盖输出距离无穷。',('CH03-D04','CH03-D05'))
add('CH03-P19-01','threshold_ball_fiber','统一半径大于等于阈值时，每个阈值开球在 A 内的部分包含于纤维。',('CH03-D02','CH03-D05','CH03-P18-01'))
add('CH03-P19-02','covering_image_le_of_zero threshold_covering','将任意有限内部网的中心取像且基数不增；对空集和无有限覆盖同样由下确界处理。',('CH03-D05','CH03-D07','CH03-P18-01'))
add('CH03-P19-03','log2_ereal_mono_above_one threshold_entropy','非空 B 时输出覆盖数至少一，利用扩展对数在 [1,∞] 单调得到熵界。',('CH03-D07','CH03-P19-02'))
add('CH03-P21-01','small_diameter_zero_iff','输入直径<τσ≤τN 时，统一半径阈值与全部输出点对零距等价。',('CH03-D01','CH03-D05','CH03-D06','CH03-P18-01'))
add('CH03-P21-02','small_diameter_zero_iff const_output_covering_one','由整体零距和非空性，任意正精度下像集内部覆盖数恰为一。',('CH03-D07','CH03-P21-01'))
add('CH03-P23-01','const_output_covering_one const_output_entropy_zero const_entropy_domain const_entropy_difference','常值分量输出覆盖数一、熵零，熵差自动良定且等于输入熵，包括输入熵无穷。',('CH03-D01','CH03-D07','CH03-D08'))
add('CH03-P27-01','colip_point_gap','正 co-Lip 条目不需有限；任何严格小于点态半径的输入距离必须为零。',('CH03-D04','CH03-P14-02'))
add('CH03-P27-02','colip_uniform_gap','任何 U 内点对的输入距离为零或不小于统一半径，结论比正半径前提更强。',('CH03-D05','CH03-P27-01'))

missing = {
'CH03-P03-01':'两点换位反例的合法结构及完整计算尚未形式化。',
'CH03-P04-02':'七点双分量反例及其伪度量合法性尚未形式化。',
'CH03-P10-01':'带吸收元实线和阶跃算子的合法构造尚未形式化。',
'CH03-P10-02':'阶跃反例的全部点态合法半径及边界尚未计算。',
'CH03-P10-03':'固定域阶跃反例的统一半径为零尚未证明。',
'CH03-P11-03':'输入距离无穷时 i=j 及 i≠j 两类反例尚未构造。',
'CH03-P13-01':'有限子族的点态半径最小值公式尚未证明。',
'CH03-P13-02':'统一半径最小值公式和下确界交换尚未证明。',
'CH03-P13-03':'统一半径关于输出子族反单调尚未证明。',
'CH03-P15-02':'有限正 Lip 常数的复合半径除法下界和无穷边界尚未证明。',
'CH03-P17-04':'二点与单点直径反例尚未构造。',
'CH03-P20-01':'阶跃反例上任意输入尺度的二点内部覆盖比较尚未证明。',
'CH03-P22-01':'有限非空集合的两端有限覆盖、有限熵和熵差良定性尚未完整证明。',
'CH03-P23-02':'恒等分量的双向内部覆盖数和熵相等尚未证明。',
'CH03-P23-03':'恒等分量良定熵差为零尚未证明。',
'CH03-P24-01':'单通道 Lip 映射对 ε/L 内部覆盖的推广尚未证明。',
'CH03-P24-02':'全有界下的原文熵差下界尚未证明。',
'CH03-P25-01':'正有限 co-Lip 条目给出的覆盖数下界尚未证明。',
'CH03-P25-02':'允许输出熵无穷的熵差上界尚未证明。',
'CH03-P26-01':'习题 3.1 的伪度量合法性、一次纤维和类型尚未完成。',
'CH03-P26-02':'习题 3.1 的自复合纤维和类型尚未完成。',
'CH03-P26-03':'习题 3.1 的点值常算子及再次像为吸收元分支尚未完成。',
'CH03-P28-01':'习题 3.3 的两个纤维分划及其结构尚未完成。',
'CH03-P28-02':'习题 3.3 的精度 3/2 内部覆盖数与熵差尚未计算。',
'CH03-P29-01':'习题 3.4 的域 [0,1/2] 的直径、统一半径与类型尚未计算。',
'CH03-P29-02':'习题 3.4 的域 [9/10,11/10] 的直径、统一半径与类型尚未计算。',
'CH03-P29-03':'习题 3.4 的域 {0,2} 的直径、统一半径与类型尚未计算。',
'CH03-P29-04':'习题 3.4 的域 [0,2] 的直径、统一半径与类型尚未计算。',
'CH03-P29-05':'习题 3.4 无直径条件时的合法反例尚未完成。',
'CH03-P30-01':'习题 3.5 的所有精度及端点的内部覆盖数尚未计算。',
'CH03-P30-02':'习题 3.5 的两像集、各精度覆盖数和熵差尚未完整计算。',
'CH03-P30-03':'习题 3.5 的最优标量 Lip 常数及必要下界尚未证明。',
'CH03-P30-04':'习题 3.5 的 ε=7/4 覆盖数上界及比较尚未完成。',
}
for id in ids:
    if id not in entries:
        assert id in missing, id
        add(id,'',missing[id],status='incomplete')
assert set(entries) == set(ids)
for e in entries.values():
    assert e['representation'] and all(d in entries and d != e['id'] for d in e['dependencies'])
    assert e['status'] != 'complete' or e['declarations']
with open('independent_c003/alignment.json','w') as f:
    f.write('{\n  "case_id": "MG-C003",\n  "version": "0.1.1",\n  "items": [\n')
    f.write(',\n'.join('    '+json.dumps(entries[id],ensure_ascii=False,separators=(',',':')) for id in ids))
    f.write('\n  ]\n}\n')
print(len(ids), sum(e['status']=='complete' for e in entries.values()), 'complete')
