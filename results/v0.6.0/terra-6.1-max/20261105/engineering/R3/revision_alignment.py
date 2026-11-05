import json

with open('alignment.json') as f:
    data = json.load(f)

def set_item(item_id, names, representation, deps):
    item = next(x for x in data['items'] if x['id'] == item_id)
    item.update(status='complete', declarations=[{'file': 'Main.lean', 'name': n} for n in names],
                representation=representation, dependencies=deps)

set_item('CH03-P09-02', ['Chapter3.finite_fiber_chain'],
         '只假定有限链中 n<m 的逐步包含，归纳得到任意 a≤b≤m 的包含。', ['CH03-D03','CH03-P09-01'])
set_item('CH03-P09-03', ['Chapter3.finite_fiber_chain_strict'],
         '有限链某步严格包含的差集成员同时见证端点严格包含。', ['CH03-D03','CH03-P09-02'])
set_item('CH03-P04-02', ['Chapter3.SevenExample.gauge_metric','Chapter3.SevenExample.first_readout','Chapter3.SevenExample.second_readout','Chapter3.SevenExample.domain_U','Chapter3.SevenExample.image_U','Chapter3.SevenExample.computation'],
         'Option (Fin 6) 为七点空间；首分量恰合并 p,q，第二分量离散；两个算子在其他点取吸收元，计算证明内侧常值而复合非恒常。', ['CH03-D01'])
set_item('CH03-P26-01', ['Chapter3.AbsoluteExample.metric','Chapter3.AbsoluteExample.domain','Chapter3.AbsoluteExample.first_fiber','Chapter3.AbsoluteExample.first_type'],
         'Option ℝ 搭配绝对值读数 edist，等于原文绝对值差；仿射算子保持吸收元，U={0,1}，纤维为 U 且分量常值。', ['CH03-D01','CH03-D02'])
set_item('CH03-P26-02', ['Chapter3.AbsoluteExample.square_zero','Chapter3.AbsoluteExample.square_one','Chapter3.AbsoluteExample.domain','Chapter3.AbsoluteExample.square_fiber','Chapter3.AbsoluteExample.square_active'],
         '同一 U 上平方像为 -3 和 1，0 的像目标纤维是 {0}，唯一分量有效。', ['CH03-D01','CH03-D02','CH03-P26-01'])
set_item('CH03-P28-01', ['Chapter3.AbsoluteExample.metric','Chapter3.AbsoluteExample.four_domain','Chapter3.AbsoluteExample.identity_image','Chapter3.AbsoluteExample.shift_image','Chapter3.AbsoluteExample.four_fibers'],
         '在绝对值读数空间逐个计算四个像目标；恒等纤维为 {-3}、{-2,2}、{0}，平移纤维为 {-3}、{-2,0}、{2}。', ['CH03-D02','CH03-P26-01'])
set_item('CH03-P28-02', ['Chapter3.AbsoluteExample.input_cover','Chapter3.AbsoluteExample.output_cover','Chapter3.AbsoluteExample.four_entropy'],
         '在 3/2 精度通过内部中心与单中心反证得到覆盖数 2、1，熵差等于 1。', ['CH03-D07','CH03-D08','CH03-P28-01'])
set_item('CH03-P29-01', ['Chapter3.FloorExample.metric','Chapter3.FloorExample.Dsmall_domain','Chapter3.FloorExample.Dsmall_nonempty','Chapter3.FloorExample.classification_Dsmall'],
         '[0,1/2] 的直径为 1/2，floor 恒为零，统一半径为无穷，分类为 (1,1)。', ['CH03-D04','CH03-D05','CH03-D06','CH03-P11-02'])
set_item('CH03-P29-02', ['Chapter3.FloorExample.metric','Chapter3.FloorExample.interval_domain','Chapter3.FloorExample.interval_nonempty','Chapter3.FloorExample.wide_classification'],
         '[9/10,11/10] 的直径为 1/5，跨越 1 的输入点可无限接近，统一半径为 0，分类为 (1,0)。', ['CH03-D04','CH03-D05','CH03-D06','CH03-P18-02'])
set_item('CH03-P29-03', ['Chapter3.FloorExample.metric','Chapter3.FloorExample.D_domain','Chapter3.FloorExample.D_nonempty','Chapter3.FloorExample.classification_D'],
         '{0,2} 的直径和统一半径均为 2，分类为 (0,1)。', ['CH03-D04','CH03-D05','CH03-D06'])
set_item('CH03-P29-04', ['Chapter3.FloorExample.metric','Chapter3.FloorExample.interval_domain','Chapter3.FloorExample.interval_nonempty','Chapter3.FloorExample.large_classification'],
         '[0,2] 的直径为 2，跨越 1 的点对迫使统一半径为 0，分类为 (0,0)。', ['CH03-D04','CH03-D05','CH03-D06','CH03-P18-02'])
set_item('CH03-P29-05', ['Chapter3.FloorExample.metric','Chapter3.FloorExample.D_nonempty','Chapter3.FloorExample.D_domain','Chapter3.FloorExample.classification_D','Chapter3.FloorExample.not_global_zero'],
         '{0,2} 上半径为 2≥1，但 floor 像 0、2 有正距离；正半径来自输入点间的距离间隙。', ['CH03-P29-03'])

with open('alignment.json', 'w') as f:
    json.dump(data, f, ensure_ascii=False, indent=2)
    f.write('\n')
