# 运行入口

Math Gauge0.6.0已封版。其他Harness按[统一运行与交付指南](harness-guide.md)执行；其中列出精确请求、作答结构、Lean工程、三组预算、独立首答、C003连续三轮、全部尝试记录与导入步骤。

- [公开发布](https://github.com/glenzli/math-gauge/releases/tag/v0.6.0)：25个A1候选题包。
- 受控私版：39个A1完整候选题包，已包含公版25题，不重复执行。
- [三轮合同](../protocol/lean-alignment/study.json)及[固定提示](../protocol/lean-alignment/neutral-prompt.txt)：独立于A1清单，完整评测必须继续三轮。

候选只接收控制器生成的精确消息与附件；README、计划、参考、判准和评审留在运行／评审端。下载GitHub源码归档不能代替候选题包。

## 从固定源码重建公开发行

在v0.6.0精确干净源提交中执行，输出使用仓库外新目录：

```sh
python3 scripts/release.py build --version 0.6.0 --source-commit FULL_PUBLIC_COMMIT --out /absolute/path/to/new-assets
python3 scripts/release.py check --archive /absolute/path/to/new-assets/benchmark-v0.6.0.zip --checksums /absolute/path/to/new-assets/SHA256SUMS --source-commit FULL_PUBLIC_COMMIT
python3 scripts/release.py evaluator-plan --version 0.6.0 --source-commit FULL_PUBLIC_COMMIT --out /absolute/path/to/trusted-evaluator-plan.json
```

完整私版从其锁定的公私两份源码和组合profile使用同一共享发布器构建；具体命令随私版提供。release-lock.json绑定实际公私提交和资产散列。准备、检查、导入与重建不调用模型。

## 记录与评分

[外部交换合同](../protocol/external-harness.md)说明便携交换层及原生记录的边界；[正式结果合同](../protocol/result-record.md)保存全原答、工具／执行证据、模型自评、逐项审核和三轮轨迹。源码中的共享scoring.py负责最终MC／RMC／SMC与两率，固定满分100，未测保持未知。
