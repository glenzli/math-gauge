# Math Gauge

Measure the capability, not just the answer.

在给定的弱数学结构下，检验模型能否正确证明、识别形式化偏差并推进构造。

## 建立初衷

Math Gauge 源于算子演化论（OET）写作与研究中的实际数学协作需求：
模型需要在明确给定、尽可能弱的结构下推进工作，严格保留假设、量词、定义域和结论强度。
既要识别推导中暗加的条件，也要识别本来能够证明、却被无必要地收紧条件的情形。

项目关注三个方面：在弱条件下完成证明或给出反例；检查形式化是否忠实表达原命题；
在方向确定而结论开放的问题中，提出能够逐项审核的构造与结果。
题目来自已公开的 OET 内容以及其他数学领域的弱结构，并先审核题面、参考论证和判分依据。

目标是在新模型出现时，用明确、可追溯的题目与运行记录，持续判断它们是否适合这种数学工作方式。
有效的不同证明路线和意外结果应当被接受；具体结论的正确性、适用范围与数学贡献分别评价。

## 公开与私有测试集合

项目设置公开测试集合与私有测试集合，两者共享本仓库的 runner 和通用评测协议。

- **公开测试集合**：题面、参考证明或反例、判分依据和可发布的结果放在本仓库，供审阅与复现实验。
- **私有测试集合**：单独维护未公开题目、参考材料、具体判分依据和完整评测记录，不随本仓库披露。
  对外结果只发布经审核的汇总，并说明其复现范围。

目前先建设并校准公开集合；私有集合的题目与执行环境随后补充。
公开集合用于透明审阅，私有集合用于持续评估未公开问题，两部分的运行与审核方法保持一致。

## 建设状态

**正在建设中（Work in progress）。** 当前提供首批公开题目初稿和基础 runner。
题目审核、难度与区分度校准、评分规则以及模型接入仍在推进，尚未形成稳定榜单。
所有题目已经 AI 首轮审校，仍待人工审定；当前示例为流程回放，没有真实模型评测成绩。

## 首版内容

- [15 道公开初稿及参考审核材料](cases/public/README.md)：6 道确定性正反题、6 道形式化一致性题、3 道开放构造题。
- [评测协议](protocol/evaluation.md)：条件忠实、证明有效与范围保持分别审核。
- [来源与 AI 参与说明](SOURCES.md)：仅取材于 OET 已公开第一卷与经典弱结构。
- [初版审核与验证记录](results/initial-validation.md)。

首批题优先验证数学边界和评测流程；这些基础题的通过不代表前沿数学研究能力。
各题的人工审定状态与后续修订均记录在题目元数据中。

## 本地使用

Python 3.10+，runner 无第三方运行依赖。在仓库目录运行：

~~~sh
python3 -m math_gauge validate
python3 -m math_gauge list
python3 -m unittest discover -s tests
~~~

六份形式化审核输入与两份修复示例使用 Lean 4.29.1 标准库，无 mathlib 下载或构建要求：

~~~sh
python3 -m math_gauge check-lean --out runs/lean-check.json
~~~

这里验证固定的题库文件能编译；三份故意失配的输入也应通过。语义对齐仍由审核负责。

## 跑通一个不调用模型的示例

~~~sh
python3 examples/demo.py --out runs/demo
~~~

它回放三个明确标注的示例响应，覆盖三类题，导入 fixture 审核并生成报告。
示例报告的模型比较资格数必须为零。重复执行请使用新的输出目录。

## 接入真实模型

runner 提供供应商无关的命令接口。适配器从标准输入读取一次 JSON 请求，
请求含 task、instruction 与明确列出的 files；把模型完整作答写到标准输出。
runner 为每题建立独立工作目录，保留实际请求、响应、失败与超时。

~~~sh
python3 -m math_gauge run --case MG-D001 --out runs/model-a-001 \
  --model '具体模型与配置标签' \
  --command-json '["python3", "/absolute/path/to/your_adapter.py"]'
python3 -m math_gauge review-template --run runs/model-a-001 --out runs/reviews-001.json
# 人工填入审核依据后：
python3 -m math_gauge review --run runs/model-a-001 --input runs/reviews-001.json
python3 -m math_gauge report --run runs/model-a-001 --out runs/report-001
~~~

适配器路径需绝对路径；默认工作目录只有作答材料，但这不构成操作系统访问隔离。
v0.1 尚无内置供应商适配器，未声称已完成真实模型评测。
不要把任意脚本的输出标签伪装成供应商模型成绩。

同一 runner 可读取另一目录的题集：

~~~sh
python3 -m math_gauge validate --suite /absolute/path/to/math-gauge-private/cases
~~~

## 代码职责

- math_gauge/catalog.py：题目合同、来源、指纹与作答材料投影。
- math_gauge/execution.py：命令或回放执行、原始记录、固定 Lean 文件检查。
- math_gauge/review.py：响应绑定、审核和按类别报告。
- math_gauge/cli.py：命令入口。

安装为命令行工具可使用 python3 -m pip install -e .；直接运行上述模块命令无需安装。
新增题目先补全数学审核依据，通用 runner 只在出现真实协议需要时扩展。
