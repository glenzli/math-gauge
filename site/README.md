# Math Gauge 静态结果页

本目录拥有独立结果页的交付与再生成说明。生成器只负责展示冻结的公开分数，不运行模型、Lean 或评分器。

交付文件是 `index.html` 与 `data.json`。HTML 内嵌样式，无脚本、字体、图片或其他联网依赖；关闭 JavaScript 仍可阅读全部内容。页面中的仓库与背景文献链接需要联网，离线时不影响结果阅读。

在仓库根目录重新生成：

```sh
python3 scripts/render_results_site.py
```

也可输出到任意目录，从其他工作目录运行时明确来源仓库：

```sh
python3 /path/to/math-gauge/scripts/render_results_site.py \
  --source-root /path/to/math-gauge --out-dir /tmp/math-gauge-site
```

生成器恰好读取以下四份公开文件，页面与下载数据均使用显式字段白名单。私有题号、题名、题文、答卷、参考、rubric、逐项评审、运行原始输出与完整评测计划均不进入交付目录。

- `docs/results/terra-v0.6.0/result.json`
- `docs/results/terra-v0.6.0/combined-aggregate.json`
- `docs/results/gemini-v0.6.0/result.json`
- `docs/results/gemini-v0.6.0/combined-aggregate.json`

`data.json` 保留冻结数值的完整精度、`null`、上下界、固定分母、权重及来源 SHA-256。本页没有复制或重实现评分逻辑；全题完成度的分数转换仅是将已有比例格式化为百分数。生成过程不含当前日期或绝对本机路径，同一输入会生成相同字节。

当前文案绑定本地 0.6.0 草稿及书面四题面板，明确 AI 审核、人审待定、正式比较资格为 false。若升级题集、改变来源构成、审核资格或面板合同，先更新生成器中的解释与测试，再重新生成，不以旧文案包装新结果。原始结果、旧报告与发布资产保持原样。

本地预览：

```sh
python3 -m http.server 8000 --directory site
```

打开 `http://localhost:8000/`。也可以直接打开 `index.html`。

定向核验：

```sh
python3 -m unittest discover -s tests -p 'test_results_site.py'
```

正式部署时，把 `index.html` 与 `data.json` 原样放入选定静态目录即可。唯一包内链接为相对路径 `data.json`，页内导航使用片段；没有根路径、仓库 Markdown 相对链接或预设站点分类。因此可放在任何 URL 前缀下，包括将来 glenzli.com 选定的位置。本任务未决定分类、改动网站仓库或执行部署。
