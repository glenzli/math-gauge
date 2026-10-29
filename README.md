# Math Gauge

Measure the capability, not just the answer.

在给定的弱数学结构下，检验模型能否保持条件、完成证明、识别不可达目标，并推进有效构造。

## 建立初衷

Math Gauge 源于算子演化论（OET）写作与研究中的实际协作需求：模型应在明确给定、尽可能弱的结构下工作，保留假设、量词、定义域和结论强度。既要识别为了得到漂亮结论而暗加条件，也要识别本来能证明、却被无必要收紧条件的结果。

题材覆盖 OET 已公开内容及整个数学领域。本阶段重点放在泛函分析、同调与范畴构造、凝聚集合等抽象结构：熟悉的强定理往往只差一个结构条件就能使用；评测关注模型能否持续记住实际拥有的条件，而不是顺着熟悉结论补齐它们。

有效的短反例、不同证明路线和意外结果都应被接受。结论真假、证明有效性、条件保持和构造贡献分别审核，不按篇幅或预设证明路线评分。

## 公开与私有测试集合

公开测试集合包含题面、参考证明或反例、评审依据和可发布的结果；私有测试集合另行保存未公开题目、参考材料、依据及记录。两者共享本仓库的 runner 和评测协议。私有原题和完整回答不随本仓库披露；对外汇总须说明复现边界。

目前先校准公开集合，私有集合随后建设。新题只使用公开数学概念与独立构造，不抽取 OET 未发布内容。

## 当前状态

**正在建设中（Work in progress）。** 默认公开集合为 [0.3.0 版十道研究式题目](cases/public/README.md)，全部采用相同的 exploration 输入类别。题面只给实际条件和主目标，不附加边界提醒、反例提示、审核清单或 runner 的默认保条件提示。

出题侧保留 MG-R001、MG-R002、MG-R004、MG-R006 四道边界基线，允许完整短反例作为决定性完成。MG-R003、MG-R005、MG-R007、MG-R008、MG-R009、MG-R010 要求成立的构造、分类或映射空间结果；其中 MG-R003、MG-R007、MG-R008、MG-R009、MG-R010 做了实质重设计。真假和诱惑点仅在评审材料中。所有题均为 draft、human pending。本轮已完成十题独立隔离的 Terra 6.1 Max 单次校准，AI 审核为 **10/10 通过**；这批题目前可作条件忠实性的基线，尚未体现对该配置的区分度。

十题均已提供作者参考 Lean，覆盖原任务的成立结论或完整合法反例，以及相应的恢复、分类和自然性构造。逐题覆盖表明确区分实际编码结论、等价证明路线和可选旁支；Lean 核验不等于人工审定，也不等于候选答卷经过了形式化。统一核验入口见 [参考 Lean 复核](scripts/formal/README.md)，本轮答卷、审核和证据见 [完整 Lean 与 Terra 校准](results/full-lean-terra/README.md)。

第一题的题面保持不变：前次 Terra 6.1 Max 通过，本次也通过；此前 Gemini 3.8 Flash High 单次闭卷失败，见 [旧对照与限制](results/recursive-operator-closure/comparison.md)。Gemini 本轮没有运行其余九题，不能据此生成十题模型排名。

优化前的十题 0.2.0 版逐字节保存在 [研究题集归档](archive/research-v0.2/README.md)。更早的基础组、加难组和长链组保存在 [历史归档](archive/legacy-v0/README.md)；已有题面、答卷与审核记录继续绑定原版本。

## 阅读与审核

- [当前十题索引](cases/public/README.md)：题面、参考论证及逐题审核。
- [研究题设计标准](protocol/research-case-design.md)：诱惑、弱记录和范围保持。
- [评测协议](protocol/evaluation.md)：输入边界、证据绑定与评分。
- [来源及作者说明](SOURCES.md)：公开来源和独立改编范围。
- [本轮优化验证记录](results/ten-case-optimization/README.md)：数学审校、全新题面盲审、文件身份与输入投影核对；[首版记录](results/ten-case-validation/README.md) 保留历史范围。
- [隔离 CLI 流程](protocol/isolated-cli-runs.md)：参数化准备、探测、运行与证据核验。

## 本地使用

Python 3.10+，runner 无第三方运行依赖。在仓库目录运行：

~~~sh
python3 -m math_gauge validate
python3 -m math_gauge list
python3 -m unittest discover -s tests
python3 -m math_gauge prepare --case MG-R001 --out /absolute/path/to/new-question-dir
~~~

新题的 prompt.md 与 task.md 字节一致。request.json 仍含题号、版本和共同题型这些传输字段，但不含来源、真假、参考解或 rubric。目录分离本身不构成访问权限隔离；实际模型运行应使用隔离流程并保存探测结果。

当前十题不要求候选提交 Lean，故普通 check-lean 清单仍为空。作者参考形式化由独立的 [逐题验证器](scripts/formal/README.md) 复核：固定 Lean / Mathlib 版本，每题独立编译，并检查全部项目声明的公理依赖。输入投影仍只有 task.md。

原三题型的纯流程回放继续使用历史题集：

~~~sh
python3 examples/demo.py --out runs/demo
~~~

该命令不调用模型，fixture 结果没有正式模型比较资格。它用于验证传输和审核管线，不是当前十题的答题成绩。

## 接入模型与私有集合

通用 runner 接收供应商无关的命令适配器：从标准输入读取 JSON 请求，将完整回答写入标准输出。每题单独建目录，保留请求、响应、失败与超时。适配器负责验证实际模型身份和工具条件；模型标签不能替代证据。

~~~sh
python3 -m math_gauge run --case MG-R001 --out runs/model-a-001 \
  --model '具体型号与推理设置' \
  --command-json '["python3", "/absolute/path/to/adapter.py"]'
python3 -m math_gauge review-template --run runs/model-a-001 --out runs/reviews-001.json
python3 -m math_gauge review --run runs/model-a-001 --input runs/reviews-001.json
python3 -m math_gauge report --run runs/model-a-001 --out runs/report-001
python3 -m math_gauge validate --suite /absolute/path/to/math-gauge-private/cases
~~~

填写审核文件后才执行 review。公开和私有数据均使用这一套 runner；私有仓库不复制实现。

代码职责保持为：catalog.py 管题目合同与可见投影，execution.py 管运行证据，review.py 管响应绑定与报告，cli.py 管命令入口。参数化 CLI 隔离辅助工具位于 scripts/isolated_cli，不承担数学评分。
