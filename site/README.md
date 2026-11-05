# 当前静态结果页

页面仅从`results/v0.6.0/`中用户指定的最新正式记录生成。公开与合并视图读取共享评分器生成的机器结果，页面不自行计算成绩。私有部分仅含聚合，不导出私有题文、ID或原答。

```sh
python3 scripts/render_results_site.py
python3 scripts/render_results_site.py --out /private/tmp/math-gauge-current-site
```

`index.html`内嵌展示数据，无外部脚本、字体或图像请求，可直接打开。`data.json`和`downloads/`提供同一当前结果的安全聚合。仓库内的完整记录链接按相对路径指向正式档案；独立部署时可另行配置档案下载位置。

当前展示包括总分、能力方向、四档Lean实际核实数，以及三轮自查后的真实最后状态。旧结果视图不在当前目录另存，使用Git历史恢复。当前仍为开发分析、AI审核、人审待定；本次未部署。
