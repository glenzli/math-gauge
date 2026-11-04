# Math Gauge 静态结果页

`index.html`和`data.json`可独立部署，无脚本、字体或图片联网依赖。包内仅使用相对数据链接与页内导航，可放在任意URL前缀。

```sh
python3 scripts/render_results_site.py
python3 scripts/render_results_site.py --out-dir /tmp/math-gauge-site
```

默认采用工程答卷与自查0.2.0：MG-C003首答两者均74/92，自查按70/30及误报扣20分。生成器从12份结果快照及政策、评审散列读取数值，不调用评分器、模型或Lean。

页面显示总分、能力方向、四道Lean题的正确且完整通过数、家族平均及三轮自查。继承等价测试只用一条注释说明。`data.json`使用 `math-gauge.portable-results/v4`，保留精度和来源；私有题只公开聚合。原答、私有ID、逐义务判据、完整计划和本机路径不导出。

此前视图可以显式生成：

```sh
python3 scripts/render_results_site.py --mixed-source --out-dir /tmp/math-gauge-old-alignment
python3 scripts/render_results_site.py --workspace-only --out-dir /tmp/math-gauge-old-workspace
python3 scripts/render_results_site.py --original-only --out-dir /tmp/math-gauge-original
```

相应程序接口使用 `use_engineering_source=False`、`use_alignment_source=False` 或 `use_workspace_source=False`。它们保留各自历史成绩，当前默认不使用混合来源。

```sh
python3 -m unittest discover -s tests -p 'test_results_site.py'
python3 -m http.server 8000 --directory site
```

生成是确定性的；相同输入产生相同字节。网站分类与上线位置未定，本轮不部署。
