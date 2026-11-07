# 当前验证范围

当前24道公有与9道私有任务均可由共享runner读取，候选投影由case.json明确列出。当前选中的6份原作者证据覆盖122项义务、160个编译模块；这是作者证据的范围，不是33道题的整体Lean覆盖，也不是候选模型通过数。其余任务按自身审核状态报告，不继承父题覆盖。

`verification/author/ledger.json`和当前各题formal目录保留真实编译、公理与独立语义审核身份；路径重组不重新编译未改的Lean，也不改写原编译时间。AI审核、作者编译、候选交付核验与人工批准分别记录，人审仍待完成。

维护检查：

```sh
python3 -m math_gauge validate
python3 scripts/catalog.py --check
python3 scripts/formal/check_evidence.py
python3 scripts/validate_protocol.py
python3 scripts/records.py check
python3 -m unittest discover -s tests
```

正式结果使用保存的原始字节及已具名审核；三模型均按用户授权保留现行结果，本次整理不新增模型调用。DeepSeek七份工程复用既有的逐字节编译与公理审计，四题语义审查和三轮自查另列。旧验证日志交由Git历史，当前验证摘要单独绑定本次实际输入。

当前聚合0.7.0／Strict0.2.0按书面35／Lean35／研究30复算。新默认公开24／完整33个A1，加独立10分的三轮Lean自查；命题拓展10分已建且只用无提示A1，研究稿完善10分待建，主值为已核实贡献／100。当前验证需同时核对六种合并视图的共享重算、原始材料字节不变、公有投影无私有逐题资料，以及结果页和下载文件的题量、分母与分数一致性。来源数学审核0.4.0及原封卷编译回执保持原身份，本次不重编译未改工程。新研究工具组还需核对实际本地计算、候选工作文件读写、参考与历史不可读、外网及本地代理连接被拒绝的源绑定证据；允许使用与实际使用分开记录。

2026-11-07矩形题的[原复核回执](../verification/rectangle-structural-review-20261107.json)记录当时的统一审核；后续独立无工具组按用户要求退出留档。当前工具原答、原审核和新增审核保持原字节，当前成绩不变。本轮[留存与页面验证](../verification/current-archive-validation-20261107.json)单列目录清理、邀请研究上下文、覆盖标记及公私来源核验；原测试回执保持其原观察身份，不新增模型调用或Lean编译。

三评分0.7.0的[源绑定验证回执](../verification/three-score-validation-20261107.json)分别检查MC正向贡献、RMC/Strict数值不变、原答审核散列不变、公私六视图、全量单测及三模式页面与下载。“部分已测”标覆盖不足，不混淆数学题的完整性判定与题包待建权重。
