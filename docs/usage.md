# 使用与复核

在仓库根目录执行。共享runner需要Python 3.10+，无第三方运行依赖。所有输出目录使用新路径；Lean核验与实际模型调用另需对应环境。

## 当前题集与候选材料

```sh
python3 -m math_gauge validate
python3 -m math_gauge list
python3 -m math_gauge prepare --case MG-GR001 --out runs/gr001
python3 -m math_gauge prepare --case MG-GF101 --out runs/gf101
python3 -m math_gauge prepare --case MG-C002 --out runs/chapter02
```

默认题集为 `cases`，包含全部43份。`validate` 检查合同、来源和身份，`prepare` 只导出材料；二者不调用模型。题目路径、分类和版本见[目录](../cases/README.md)。

导出目录只有prompt.md、request.json及显式附件。适配器应使用共享消息构造器，完整发送白名单文本：

```python
from math_gauge.catalog import candidate_message, read_json

request = read_json("runs/gf101/request.json")
message = candidate_message(request)
```

无附件且instruction为空时消息等于原题面；有附件时追加中性文件名和完整内容。参考、评分、来源、真假、审核和作者源码留在评审侧，不由适配器补入。

## 单份答卷、审核与报告

通用命令适配器从stdin读取JSON请求，向stdout写完整答卷。以下入口会真实调用指定适配器；运行前需另行确定模型、预算、工具与隔离条件：

```sh
python3 -m math_gauge run --case MG-GR001 --out runs/model-gr001 \
  --model 'actual requested model and settings' \
  --command-json '["python3", "/absolute/path/to/adapter.py"]'
python3 -m math_gauge review-template --run runs/model-gr001 \
  --out runs/review-gr001.json
# 完成真实审核后应用该文件：
python3 -m math_gauge review --run runs/model-gr001 --input runs/review-gr001.json
python3 -m math_gauge report --run runs/model-gr001 --out runs/report-gr001
```

审核模板不是完成评分。reviewer、reviewer_kind、decision和各数学轴必须按实际证据填写，并绑定答卷散列。私有题通过同一 `--suite /absolute/path/to/private-suite` 运行，私有位置不复制runner。

[单轮比较工具](../protocol/full-comparison-run.md)是共享runner之上的薄调度层；[隔离流程](../protocol/isolated-cli-runs.md)核验真实文件、进程与工具边界。当前[可靠性计划](../protocol/reliability/README.md)的多轮调度和KEEP/FULL组合尚未实现验收，单轮run不执行该177槽位方案。

## 作者与候选Lean

作者证据的只读身份核验：

```sh
python3 scripts/formal/check_evidence.py
```

该检查复核已保存的编译、源码、公理与语义覆盖绑定，不调用模型、不重编未变源码。需要重编时，按[固定工具链说明](../scripts/formal/README.md)使用受影响题目的manifest和新的输出目录；不混用Lean/Mathlib/TauCeti配置。

候选源码由 `math_gauge.execution.verify_candidate_lean` 从冻结答卷提取，在明确的固定依赖和受限环境中原样核验。它不补import、不改定理、不修proof。候选生成/修复与整章严格通过还需逐义务语义审核；章节清单和冻结背景合同见[候选Lean协议](../protocol/candidate-lean.md)。

## 维护检查

```sh
python3 scripts/catalog.py --check
python3 scripts/validate_protocol.py
python3 -m unittest discover -s tests
python3 -m math_gauge validate
```

分类或源绑定有意更新后，先核对完整材料，再运行 `python3 scripts/catalog.py` 生成目录。协议身份变更后用 `python3 scripts/validate_protocol.py --refresh` 更新当前计划绑定；该操作不能授权执行或填入候选结果。真实编译测试若因缺少指定环境而跳过，应如实报告。
