# 当前验证范围

当前26任务均可由共享runner读取，候选投影由case.json明确列出。当前选中的12份原作者证据覆盖158项义务、253个编译模块；这是作者证据的范围，不是26道题的整体Lean覆盖，也不是候选模型通过数。其余任务按自身审核状态报告，不继承父题覆盖。

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

正式结果使用保存的原始字节及已具名审核；三模型均按用户授权保留现行结果，本次整理不新增模型调用。DeepSeek七份工程复用本次逐字节编译与公理审计，四题语义审查和三轮自查另列。旧验证日志交由Git历史，当前验证摘要单独绑定本次实际输入。

当前聚合0.5.0／Strict0.2.0按书面35／Lean35／研究30复算。新默认公开26／完整29个A1，加独立10分的三轮Lean自查；数学研究30分待建，主值为已获分／100。当前验证需同时核对四种合并视图的共享重算、原始材料字节不变、公有投影无私有逐题资料，以及桌面／手机端切换。来源数学审核0.4.0及原封卷编译回执保持原身份，本次不重编译未改工程。
