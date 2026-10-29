# 离线复算

等最终评分、`comparison.json` 和 `runtime/evidence-final/manifest.json` 均写完后运行：

```sh
python3 -B results/full-comparison-20261030/runtime/replay_comparison.py \
  --output results/full-comparison-20261030/runtime/offline-recomputed
```

输出目录必须尚不存在。它将生成重算的 `comparison.json` 和核对记录 `verification.json`；仅当所有核对一致时退出码为 0。该入口不会发送模型请求、重跑 Lean、重新判断数学正确性或修改原始证据。

输入为最终归档内的冻结清单、原始运行及评分记录、执行收据，和仓库 `reviews/lean-report-map.json` 指向的 `answers/<packet>/lean/report.json`。只在内存中重定位文件路径；原始 JSON、答案及报告字节不变。核验归档文件散列、release 对 freeze 的绑定、冻结时共享 runner 指纹和候选 Lean 归档散列后，从归档 `source-code/math_gauge` 加载原来的 `compare_models`。

逐模型 summary、groups、全部 paired 信息与逐题结果必须一致。完整报告比较只忽略顶层 `created_at` 和逐题 `run_dir` 两个明确的路径/时间字段；其他散列、状态和数量均保留。复算期间禁止打开原临时根、启动子进程或访问网络。该核对验证统计可复算，不把 AI 审核提升为人工批准。

仓库换位置后可显式指定 `--results /新位置/results/full-comparison-20261030`、`--archive /新位置/.../runtime/evidence-final` 和新的 `--output`；需要时也可指定 `--reference` 与 `--lean-map`。归档内另保存了一份本入口，使用该副本时须显式给出这些位置。

准备阶段只用清楚标记的合成样本检查，记录见 `offline-replay-checks.json`。真实全量复算须等待最终评分完成。
