# 当前目录

- `cases/`：仅当前22份公开任务；题文、参考、判准、来源和当前作者证据。四档形式化统一位于`lean-formalization/`，公有命题拓展在`theorem-extension/`。
- `protocol/`：当前评测、评分、执行、候选边界与正式结果记录合同；`benchmark-profile.json`是当前标准计划，`scoring-policy.json`是当前有效聚合政策。
- `math_gauge/`：共享实现。`execution`负责真实执行和原答；`catalog`负责题目与候选投影；`review`与`reliability_review`负责判断；`benchmarks`负责冻结计划；`theorem_extension`校验研究首答证据；`scoring`负责聚合；`records`负责正式记录的字节证据和轨迹。
- `results/v0.6.0/`：用户此次选定固定留档的最新模型记录。私有部分仅公开聚合，原始私有记录在配套仓库同版本下。
- `verification/`：当前题目的作者与校准证据、当前迁移及验证摘要；编译收据保留原时间和范围。
- `scripts/`、`tests/`：当前工具与相应合同测试。
- `docs/`：当前使用、结果、选题和来源说明。
- `site/`：由正式结果档案生成的静态展示。
- `runs/`：被Git忽略的临时运行区；不作为正式归档入口。
- `deliveries/`：被Git忽略的当前交付包，供用户取走。

旧版本、旧成绩和备选题使用Git历史恢复，不在当前工作树另设历史库。日常运行不自动成为永久档案；用户明确指定固定留档时，按[正式记录合同](../protocol/result-record.md)收集。
