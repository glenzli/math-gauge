# 材料复核记录

这些记录仅供评审侧，不能附入模型请求。均为AI复核，人工状态仍pending，没有候选模型作答或新Lean编译。

- [执行与评分复核](protocol-review-a.md)：检查三次独立、固定A1、两轮历史、传输重试、KEEP/FULL、数学与交付状态、分母和迎合判定；发现均已闭环。[JSON](protocol-review-a.json)绑定最终协议文件。
- [四个书面重点](selection-review-b.md)：完整核对GR002、GR004、GR007、GR014的前提、真值、证明及stage/subclaim边界。[JSON](selection-review-b.json)区分初读0.1.0与最终0.1.1，并核验归档差分。
- [四个Lean相关重点](lean-focus-review.md)：核对GF101、GF107、GF104、GF106的原题、源码要求与精确反例/证明。[JSON](lean-focus-review.json)记录0.1.0源身份，当前版本通过题组目录的编辑等价记录衔接。
- [原消息与槽位复核](packet-review-c.md)：检查八题声明、48条消息、177槽位的分支隔离与未执行状态。[JSON](packet-review-c.json)绑定当时全部试卷为0.1.1的材料包；该报告保留原字节。
- [本轮身份再核验](strict-revalidation-20261030.json)：GR001升级后更新计划的题目与suite身份；八题、重点断言、消息和槽位未改。旧plan/selection仍按原packet-review-c散列保存，不把旧审核当作当前计划的新独立审核。

消息复核中发现立场分支夹带了额外服从与最终性指令，现已删去；三个分支只相差“我确信/仍然确信成立或不成立”的立场句，重点断言、复核要求和交付格式均相同。协议复核不等于多轮执行器已验收；实际运行前仍须按执行门槛验证共享runner。
