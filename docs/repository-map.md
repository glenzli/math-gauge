# 仓库地图

当前仓库维护一套43份完整试卷的公开开发题集、一套共享runner、共同协议及当前作者验证证据。参考与历史继续公开，出题侧材料不因此成为候选输入。

```text
cases/
  suite.json / sources.json        唯一题集合同与来源登记
  proofs/                          29份书面论证
  lean-audit/                      6份Lean语义审计
  lean-construction/               6份Lean生成/修复
  chapters/                        2份整章形式化
  taxonomy.json                    九项考察重点与逐阶段分类依据
  catalog.json / by-focus.md        生成的机器目录与导航
protocol/                          数学、交付、隔离及报告合同
  benchmark-profile.json           评审侧分项、固定权重和题集身份
  benchmark-scoring.md              归一化、综合分、缺测与独立运行标准
  execution-evidence.md             原始运行证据、具名审核与正式比较资格
  external-harness.md               独立题包、控制器、外部提交与导入合同
  reliability/                     未执行的可靠性计划、选择、消息与槽位
math_gauge/                        全部公开与私有题集共享的runner
scripts/
  catalog.py                       当前目录与分类的源绑定及生成
  validate_protocol.py             当前计划、候选边界与固定消息检查
  formal/                          作者Lean验证、证据复查与元数据迁移校验
  isolated_cli/                    CLI隔离准备、探测与收据
  benchmark/                       单轮比较的薄调度层
verification/author/               当前作者编译与语义覆盖证据
verification/runner/               当前评分/多轮软件的离线验收身份
tests/                             合同、数学见证与工具测试
docs/                              定位、方法、使用和验证状态
```

每题 `case.json` 使用 `path_base="case"`，文件路径相对其所在题目目录；suite按分类列出所有case.json。题面是唯一候选任务，完整白名单由solver_files决定。参考、rubric、contract、来源、审核、作者Lean与分类均在评审侧。

| 软件边界 | 职责 |
| --- | --- |
| `math_gauge/catalog.py` | suite/case/阶段合同、路径、附件、散列与候选投影 |
| `math_gauge/execution.py` | 请求与原始响应、冻结合同、源码/清单提取、受限编译、公理审计 |
| `math_gauge/review.py` | 响应绑定审核、逐阶段与交付门槛、报告和配对比较 |
| `math_gauge/benchmarks.py` | 评审侧profile、完整主计划与独立分项投影 |
| `math_gauge/reliability.py` | 独立轮/分支调度、原始历史、重试、KEEP/FULL材料与同计划证据复用 |
| `math_gauge/reliability_review.py` | 多轮材料、当前说明、数学状态与候选Lean的审核绑定 |
| `math_gauge/eligibility.py` | 原始运行证据导入、运行审核快照、逐槽位资格与继承来源 |
| `math_gauge/harness.py` | solver/controller 白名单导出、独立消息构造器和只读题包核验 |
| `math_gauge/harness_import.py` | 外部提交与原始文件导入，绑定共享多轮证据和审核入口 |
| `math_gauge/scoring.py` | 固定分母分项/加权聚合、未知区间、轨迹与配对诊断 |
| `scripts/catalog.py` | 分类证据与当前材料身份，生成出题侧导航 |
| `scripts/validate_protocol.py` | 固定计划、消息、候选白名单与未执行状态 |
| `scripts/formal/check_evidence.py` | 当前作者证据与原始编译记录的身份复核 |

公开与私有材料使用同一runner，不在私有数据内复制执行或评分实现。新分项与多轮入口继续共享案例合同、候选投影和原始源码核验；CLI只做参数分派。外部题包仅携带 solver 内容、控制器与提交模板，完整主计划保存在独立 evaluator 目录；执行端无需本仓库、Codex 或 Math Gauge 安装。`runs/`、`.dev-mesh/`、缓存与凭据只保留本地。

## 历史保留与恢复

旧题、历史实验、设计稿与归档保存在Git历史。清理前的基线提交为 `6a48027baa33e06e913a554fb8bac9394a82b480`；当前仓库无需再维护一份本地历史目录。

```sh
git ls-tree -r --name-only 6a48027baa33e06e913a554fb8bac9394a82b480
# 将PATH_AT_BASE替换为上一步列出的路径：
git show 6a48027baa33e06e913a554fb8bac9394a82b480:PATH_AT_BASE > /absolute/path/to/restored-file
```

历史引用中的Git提交与提交内路径是来源记录，不是当前运行依赖。恢复到题库外的新位置；旧成绩绑定旧材料，不能沿用为当前43份的结果。

[贡献指南](../CONTRIBUTING.md) · [使用指南](usage.md)
