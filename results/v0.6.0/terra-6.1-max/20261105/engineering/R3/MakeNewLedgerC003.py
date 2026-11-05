import json
from pathlib import Path

counts=[3,3,1,2,1,8,4,3,3,3,3,2,3,3,2,3,4,3,3,1,2,1,3,2,2,3,2,2,5,4]
ids=[f'CH03-D{n:02}' for n in range(1,9)]
ids += [f'CH03-P{p:02}-{n:02}' for p,count in enumerate(counts,1) for n in range(1,count+1)]
assert len(ids)==92

data={}
def done(id,names,rep,deps=()):
    data[id]={'id':id,'status':'complete','declarations':[{'file':'Main.lean','name':'Chapter3Fresh.'+n} for n in names.split()], 'representation':rep,'dependencies':list(deps)}

done('CH03-D01','constComponents identityComponents activeComponents components_partition','按常值优先定义三类指标并证明互斥穷尽。')
done('CH03-D02','fiber componentFiber subfamily_zero_iff fiber_singleton','纤维是 U 中复合子族伪度量为零的点；单分量与各分量零距条件已对应。')
done('CH03-D04','goodRadius pointRadius radius_ball_iff','对有限正合法半径取上确界，合法性等价于受限球包含。')
done('CH03-D05','uniformRadius zeroMatrix','对 A 的基点半径取下确界；矩阵参数 i、j 分别为输入列和输出行。',('CH03-D04',))
done('CH03-D06','ScaleFamily diameter diameter_mono diameterScales channelType threshold_correspondence','非空集上单调尺度、直径和两个比较构成布尔通道类型。',('CH03-D05',))
done('CH03-D07','TotallyBoundedInternal internalNet_text','冻结内覆盖数、熵和子族伪度量；球覆盖等价及所有有限正精度下全有界接口。')
data['CH03-D07']['declarations'] += [{'file':'formal_oet/vol_01/ch_01_foundations/metric_entropy.lean','name':'formal_oet.vol_01.ch_01_foundations.'+n} for n in ['InternalEpsilonNet','covering_number','covering_number_attained','covering_number_eq_top_iff','metric_entropy','subfamily_pseudometric','subfamily_metric_entropy']]
done('CH03-D08','entropyDomain entropyDifference','非空域、子族、有限正精度和至少一端有限覆盖数下的 EReal 输入熵减输出熵。',('CH03-D07',))
for k,n,rep,deps in [
('P01-01','const_zero_row','常值输出与零行有限和均为零。',['D01']),
('P01-02','const_colip_zero','正输入距离与常值输出迫使相应 co-Lip 条目为零。',['D01']),
('P01-03','identity_preserves_distance','恒等分量下像点距离等于输入距离。',['D01']),
('P02-01','active_comp','两步有效分量包含，外步域为实际中间像。',['D01','P01-03','P02-03','P04-01']),
('P02-02','seqOp seqActive seqOp_eq_reverse_prod identity_not_active active_seq','列表顺序为作用顺序，递归实际像域并含零步。',['D01','P02-01']),
('P02-03','identity_comp','两步恒等分量保持且排除常值优先分支。',['D01','P01-03']),
('P04-01','outer_const','外侧在内侧像上常值推出复合常值。',['D01']),
('P05-01','inner_const_of_single_row','单同分量行 Lip 界将内侧常值传给复合，允许无穷系数。',['D01']),
('P06-04','fiber_intersection','非空输出子族纤维是单分量纤维交集。',['D02']),
('P06-05','fiber_antitone','J 包含于 K 时 K 纤维包含于 J 纤维。',['D02']),
('P06-06','fiber_singleton fiber_all_subset','单指标子族等于对应分量，全指标纤维包含于每个分量。',['D02','P06-05']),
('P14-01','fiber_forces_zero','纤维成员给出输出零距及对称方向。',['D02']),
('P14-02','point_radius_witness point_radius_component','严格小于上确界时提取有限正合法半径并得到输出零距。',['D04']),
('P14-03','composite_fiber_forces_zero','代入两个中间像点与下游纤维成员。',['D02','P14-01']),
('P16-01','threshold_cases threshold_correspondence','布尔对四种情况穷尽，并分别对应四组互补不等式。',['D06']),
('P16-02','scale_threshold_mono','增大尺度阈值保留原来小于阈值的通道。',['D06']),
('P16-03','zero_threshold_mono','增大零化阈值后仍达标则原阈值也达标。',['D06']),
('P17-01','scale_domain_mono','非空子域上的单调尺度及尺度阈值结论。',['D06']),
('P17-02','radius_subset','缩小评估域时每个合法半径仍合法。',['D04']),
('P17-03','uniform_subset','同时缩小评估域与基点集合后统一半径不减。',['D04','D05','P17-02']),
('P18-01','zero_of_lt_uniformRadius','小于统一半径的输入点对映到零距输出。',['D04','D05','P14-02']),
('P18-02','positive_output_ge_uniform','输出正距离迫使输入距离不小于统一半径。',['D04','D05','P18-01']),
('P18-03','radius_deficit_witness','任何有限正 α 高于统一半径时产生两点和有限正 ε，含无穷输出距离。',['D04','D05']),
('P19-01','threshold_ball_fiber','低于统一阈值的输入球与域交集包含在纤维中。',['D02','D04','D05','P18-01']),
('P27-01','colip_no_point_gap','正 co-Lip 条目（可为无穷）排除点态半径内正输入距离。',['D04','P14-02']),
('P27-02','colip_gap_uniform','对每个输入点对，距离为零或不小于统一半径。',['D04','D05','P27-01'])]:
    done('CH03-'+k,n,rep,['CH03-'+x for x in deps])

items=[]
for id in ids:
    items.append(data.get(id,{'id':id,'status':'incomplete','declarations':[],'representation':'该项的全部构造或证明尚未交付。','dependencies':[]}))
print('complete',sum(x['status']=='complete' for x in items),'incomplete',sum(x['status']=='incomplete' for x in items))
Path('NewLedgerC003.json').write_text(json.dumps({'case_id':'MG-C003','version':'0.1.1','items':items},ensure_ascii=False,separators=(',',':'))+'\n')
