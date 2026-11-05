# 当前 C003 预算

Benchmark0.6.0的新MG-C003初答、每次中性跟进和另行登记的操作续作，每轮上限10800秒。原生生成、broker和外层墙钟分别设置并留证，工具调用、编译和等待计入本轮。首次原生终态或固定截止较早者触发停止写入及封卷。

唯一当前profile是[benchmark-profile.json](benchmark-profile.json)，政策为[lean-tool-budget-policy.json](lean-tool-budget-policy.json)：

```sh
python3 -m math_gauge benchmark-plan --target c003-180 --runtime /ABS/c003-runtime.json --out runs/new-c003-plan.json
```

其余七份新Lean采用`lean-90`目标及独立5400秒runtime。普通新书面和AR采用2700秒。不能用一个全局时限覆盖不同预算的组；原生或broker实际更短时明确记录差异，不以外层数字代替内层证据。

已有运行保留实际预算，不按新政策重标。各轮原答与工程独立归档；操作续作不是新的独立A1，后续自查不覆盖初答。
