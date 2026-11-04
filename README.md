# Math Gauge

**Measure the capability, not just the answer.**

Math Gauge 检查数学推理、Lean 语义对应、完整工程交付与真实答卷审阅，保留假设、量词、定义域、结论强度及可复核的原始证据。

当前为 **本地0.6.0草稿 / human pending**，尚未发布。默认清单、权重和计划分别以 [suite](cases/suite.json)、[profile](protocol/benchmark-profile.json) 和共享计划器为准。既有[0.5配置](protocol/history/v0.5.0/README.md)、[旧机器结果](docs/results/comparison-2026-11-03/index.html)与已发布[v0.4.0](https://github.com/glenzli/math-gauge/releases/tag/v0.4.0)保持各自身份，不能当作0.6完整成绩。

[本轮0.6开发结果](docs/benchmark-comparison-v0.6.0.md)与[离线对比页](docs/results/comparison-v0.6.0/index.html)分开列出标准首答、首份工程封卷、三轮对齐研究和额外补时。标准42槽已闭合；原92项空答保留未决及固定分母区间，补时不覆盖首答。全部结论为AI审核、人审待定。

## 当前默认范围

| 方向 | 默认任务 | 公开能力权重 | 合并3份私有探索后 |
| --- | ---: | ---: | ---: |
| 书面论证 | 14 | 22.5% | 22.5% |
| 历史Lean语义审计 | 4 | 22.5% | 18% |
| 大Lean形式化 | 4 | 45% | 36% |
| 私有研究探索 | 0 | — | 13.5% |
| 真实答卷审阅 | 4 | 10% | 10% |

公开默认26份任务、18个数学家族。形式化梯度为LCH01的8项、LCH02的20项、历史HCH02的40项、原MG-C003的92项；前三份同属CH2家族，先在家族内平均，再平均方向内家族。审计含两对历史失配/正确对照，按35/20/30/15四维审核，不增加候选Lean交付。AR仍按60/30/10及母题家族聚合，重大误判另报。合并探索后29份任务、21家族。

默认数学阶段和形式化义务共226项，另列15项书面判准、16项语义审计维度和12项AR维度。31份reserve含214项原义务；旧题物理路径不动。全库57条任务，保留原43份数学卷、3份相关加强稿、4份AR和7份新增范围。原作者Lean账本仍只覆盖原43卷、372义务、470模块，不能继承给新增任务。[选题与来源边界](docs/selection-v0.6.0.md)列出精确清单。

## 固定计划与实际补考

综合权重保持75%能力、5%重复稳定性、10%中性自查、10%立场自查。能力只取A1。协议0.4只对四份书面题设置重复与三臂：GR002、GR014、GP001、GP002，2真2假、四个家族；各A1/A2，neutral/affirm/deny从各自A1开独立分支，各一次自查。公开42条计划记录，合并探索45条；不按缺测缩小分母。

Lean能力仅取8份新A1（四审计和四形式化）；书面面板缺槽按原消息、合同、分支与逐源条件核验后补齐。两模型各补18个标准槽（8Lean A1及GP001/GP002各完整5槽），旧GR002/GR014整包精确相容后复用；不把复用答卷记录成新调用。新Lean原生、broker及外层墙钟每轮均5400秒；书面后续保留各自原生/工具/外层预算，不从旧outer10800推定模型曾获3小时。

Lean是否100%对齐另设MG-C003的92项专项：承接正式新A1原答和工程，固定三次中性追问，每轮5400秒，不因自称100%早停。专项不入标准42/45条、不加权、不用改好后的答案替代A1。原HCH02的40项operational续作继续独立归档。

新增[到时封卷规则](protocol/deadline-submission.md)：首次终态或截止即停止并收取实际工程，首轮与续作分别审核。本次MG-C003双方首份归档工程以观察后的独立诊断轨报告，原文字答卷和标准42/45结果保留；Gemini另一次90分钟续作到限亦封卷，仍无有效交付记该次失败。

答卷完成时刻与客户端进程退出分开记录。对已在限内产出原生成功结果、却因CLI收尾不退出而被误记失败的答卷，采用[具名执行接纳修订](protocol/native-terminal-evidence.md)；保留全部原失败记录，不重试模型，也不把工具故障当作数学错误。

这是一项观察后的开发组合，尚未完成的新槽为missing/null；专项中断续作不能自动成为正式fresh A1。新题包、AI审核、真实编译、来源核实与人工批准是不同证据。历史中间版本是否公开尚未核实，不能称隐藏留出集或已公开历史发布。

## 准备与核验

Python3.10+，共享runner无第三方运行依赖。以下命令不调用模型：

```sh
python3 -m math_gauge validate
python3 -m math_gauge list
python3 -m math_gauge prepare --case HCH02 --out runs/hch02-packet
python3 -m math_gauge benchmark-plan --out runs/v06-preparation-plan.json
python3 scripts/catalog.py --check
python3 scripts/validate_protocol.py
python3 -m unittest discover -s tests
```

实际新补考先冻结runtime；8份Lean A1可使用独立initial-acquisition profile，选择lean-audit与lean-formalization；书面后续使用最终标准profile与只读原A1依赖绑定；操作步骤见[本地0.6指南](docs/release-consumer-README-v0.6.0.md)。参考、评分、真假、来源、作者Lean和运行元数据留在评审侧；候选仅见完整题面、白名单附件及自己本分支可见历史。准备与导入不会调用候选模型，模型启动需要明确授权。

[评测协议](protocol/evaluation.md) · [评分合同](protocol/benchmark-scoring.md) · [使用指南](docs/usage.md) · [候选Lean核验](protocol/candidate-lean.md) · [运行证据](protocol/execution-evidence.md) · [完整目录](cases/README.md)
