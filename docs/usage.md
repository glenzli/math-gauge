# 使用与复核

本文从仓库根目录执行命令。共享 runner 需要 Python 3.10+，无需第三方运行依赖；Lean 编译和真实模型调用需要另备对应环境。下文的绝对路径是待替换的占位路径，不要复用已有输出目录。

当前主试卷是41个递进题组和两份整章题，共43份，尚无模型成绩；原41道单题及其结果另行保留。项目定位、规范与实现的区别见[评测方法](evaluation-methods.md)，按能力选题见[重点索引](../exercises/by-focus.md)。

## 当前43份试卷

```sh
python3 -m math_gauge validate --suite drafts/progressive-groups-20261030
python3 -m math_gauge validate --suite drafts/chapter-exams-20261030
python3 -m math_gauge prepare --suite drafts/progressive-groups-20261030 \
  --case MG-GR001 --out runs/group-r001
python3 -m math_gauge prepare --suite drafts/chapter-exams-20261030 \
  --case MG-C002 --out runs/chapter02
```

每次使用新的输出目录。上述命令仅校验或准备材料，不调用模型。确切题目版本以各题`case.json`和修订记录为准；当前仍为draft / human pending，新增目标的完整作者Lean核验未完成。

三次独立初答及八题两轮自查的[材料包](../protocol/reliability-20261030/README.md)已有计划、消息和检查入口，但共享runner的多轮调度、历史绑定与KEEP/FULL组合尚未实现验收。下文单轮`run`命令不是该计划的一键执行器；新实验参数和执行须另行冻结与授权。

## 原41道单题的四套suite

原版目录共 41 题，分属四个 suite。省略 `--suite` 时只使用 `cases/public` 的 20 题，不会自动选择43份新试卷。

```sh
python3 -m math_gauge validate
python3 -m math_gauge validate --suite drafts/true-goal-six-20261029
python3 -m math_gauge validate --suite drafts/public-proof-extractions-20261029
python3 -m math_gauge validate --suite drafts/lean-alignment-20261029
python3 exercises/refresh_catalog.py --check
```

`validate` 检查材料合同与文件身份，不判断数学证明。目录检查核对当前 41 题的来源散列及链接，不重新生成冻结记录。阅读时按[七章目录](../exercises/README.md)或[任务类型](../exercises/task-types.md)选题，原始题号不变。

## 导出候选输入

```sh
python3 -m math_gauge prepare --suite drafts/lean-alignment-20261029 \
  --case MG-F105 --out runs/question-f105
```

参考、评分、来源、审核和作者形式化不会自动进入导出内容。`prompt.md` 保留题面合同；附件题通过 `request.json` 的 `files` 传递显式附件。适配器应使用共享消息构造器：

```python
from math_gauge.catalog import candidate_message, read_json

request = read_json("runs/question-f105/request.json")
message = candidate_message(request)
```

无附件的新题保持题面字节；有附件时加入文件名及完整源码。不向候选追加目录中的母题、预期对齐标签、来源或历史成绩。六个 Lean 母题的相关版本应独立投放，避免前题答案成为后题上下文。

## 接入模型、审核与报告

通用命令适配器从标准输入接收 JSON 请求，向标准输出写完整答卷。以下命令会真正调用指定适配器；使用前先配置并核验模型身份、工具条件和隔离。

```sh
python3 -m math_gauge run --case MG-R001 --out runs/model-a-r001 \
  --model '具体型号与推理设置' \
  --command-json '["python3", "/absolute/path/to/adapter.py"]'
python3 -m math_gauge review-template --run runs/model-a-r001 \
  --out runs/reviews-model-a-r001.json
# 按冻结答卷实际完成审核后，再应用审核文件：
python3 -m math_gauge review --run runs/model-a-r001 \
  --input runs/reviews-model-a-r001.json
python3 -m math_gauge report --run runs/model-a-r001 \
  --out runs/report-model-a-r001
```

审核模板不是完成评分。reviewer、审核种类、结论、条件忠实性与证明有效性必须如实填写；审核绑定原始答卷散列。不能将 AI 审核标成人工审核，也不能用作者参考替代候选答卷。

目录分离不等于闭卷隔离。实际 CLI 流程见[隔离运行说明](../protocol/isolated-cli-runs.md)，本轮配置、冻结与队列规则见[全题集比较协议](../protocol/full-comparison-run.md)。该批操作脚本记录了固定客户端和本机运行位置，不能当作任意机器的一键服务接入；新实验应使用新的目录、预检及授权，并保存身份与所有尝试。

私有题通过同一 `--suite /absolute/path/to/private-suite` 接口运行；私有原题和答卷留在私有位置，发布前另行审查。`examples/demo.py` 是合成流程回放，不产生真实模型成绩。

## 两种 Lean 核验

**作者参考。** [统一验证器](../scripts/formal/README.md)读取逐题 `formal/manifest.json`，绑定题面、参考、评分、覆盖表、源模块、编译器与依赖。默认公开清单现含 20 题；其他题集传自己的 `--suite` 或显式 `--manifest`。

```sh
python3 scripts/formal/verify_suite.py \
  --suite drafts/lean-alignment-20261029/formal-suite.json \
  --dependency-root /absolute/path/to/pinned-dependency-project \
  --lean /absolute/path/to/lean-4.29.1 \
  --out /absolute/path/to/new-author-verification --jobs 2
```

P001 使用单独的 Lean 4.36/TauCeti profile，不能和默认 4.29.1 profile 混在一次调用。既有依赖缓存可复用，改变的题目模块须重新核验。当前 40 题完整作者主任务覆盖、P003 部分覆盖，不由“编译通过”自动扩大范围。

**候选交付。** 使用 `math_gauge.execution.verify_candidate_lean` 从冻结答卷逐字提取文件，在受限环境原样编译并检查全部本地声明及公理依赖。参数和收据状态见[候选源码合同](../protocol/candidate-lean.md)。当前候选隔离实现要求 macOS 的 `sandbox-exec`；不支持的环境返回基础设施错误，不能当作候选数学失败。CLI 的旧 `check-lean` 入口不等同于这个候选答卷核验入口。

## 离线复算已发布结果

离线复算核验档案散列并重新汇总已经保存的评分；不调用模型、不重编 Lean、不重新判断数学，也不要求原机器的临时运行目录仍存在。保留完整结果目录及其相对布局。

首轮 41 题：

```sh
python3 -B results/full-comparison-20261030/runtime/replay_comparison.py \
  --results results/full-comparison-20261030 \
  --archive results/full-comparison-20261030/runtime/evidence-final \
  --reference results/full-comparison-20261030/comparison.json \
  --lean-map results/full-comparison-20261030/reviews/lean-report-map.json \
  --output /absolute/path/to/new-full-replay
```

R005 澄清版补测：

```sh
python3 -B results/r005-clarified-v0.3.1-20261030/evidence-final/tools/supplement_replay.py \
  --archive results/r005-clarified-v0.3.1-20261030/evidence-final \
  --output /absolute/path/to/new-r005-replay
```

两者都要求全新的输出目录，成功时 `verification.json` 中 `matched` 为 true。汇总、分层、配对及逐题结果均比较；完整报告只忽略明确的创建时间与运行目录字段。首轮执行归档依赖同目录下已保存的 `answers/`、`reviews/` 和 `comparison.json`，不能只复制 `runtime/evidence-final/`。

历史快照、冻结题集副本、评审 packet 与原始候选答卷中的路径按产生时的布局保留，部分内部链接或临时绝对路径不会在新克隆中直接可用。不要为了修链接修改证据字节。当前阅读入口使用[习题目录](../exercises/README.md)、各结果 README、`packet-map.json` 和归档 `binding-map.json`；复算程序在内存中重定位路径。

复算一致只证明保存的评分可重现汇总，不证明这些 AI 数学判断已经得到人类确认。当前 runner 后续维护也不替换档案里冻结的原 runner。

## 工程验证

```sh
python3 -m unittest discover -s tests
python3 -m math_gauge validate
python3 exercises/refresh_catalog.py --check
```

真实 Lean 集成测试按对应环境变量启用，详见[作者验证器说明](../scripts/formal/README.md)和 `tests/test_candidate_lean.py`。未配置环境时会跳过，不能把跳过当作真实编译成功。若外层执行环境阻止创建编译隔离进程，应保留失败证据并修正运行权限，不能删除编译隔离层。

发布前可复用与当前源散列、依赖及环境合同一致的已完成检查，无需仅因创建提交而重编所有题。最近验收见[最终工程记录](../results/full-comparison-20261030/validation/finalization/README.md)。

[文档导航](README.md) · [返回首页](../README.md) · [结果与版本](results.md) · [贡献指南](../CONTRIBUTING.md)
