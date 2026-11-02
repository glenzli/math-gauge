# 仓库地图

当前仓库维护默认32卷与显式后备11卷组成的43卷公开开发题库、一套共享runner、共同协议及当前作者验证证据。参考与历史继续公开，出题侧材料不因此成为候选输入。

```text
cases/
  suite.json                      默认32卷清单
  reserve-suite.json                显式后备11卷；两集同根且不重叠
  sources.json                     共同来源登记
  proofs/                          18份默认书面论证
  reserve/proofs/                  11份备选书面论证，数学文件原样迁移
  reserve/README.md                备选按主题索引，须显式选择运行
  reserve/relocations.json         原作者证据路径到现目录的精确迁移表
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
  release-distribution.md           同题集版本的命名任务ZIP与本地构建合同
  reliability/                     新版六题面板、80槽计划与固定消息
math_gauge/                        全部公开与私有题集共享的runner
scripts/
  catalog.py                       当前目录与分类的源绑定及生成
  validate_protocol.py             当前计划、候选边界与固定消息检查
  release.py                       候选发布构建、只读资产核验与评审计划恢复
  formal/                          作者Lean验证、证据复查与元数据迁移校验
  isolated_cli/                    CLI隔离准备、探测与收据
  benchmark/                       单轮比较的薄调度层
verification/author/               当前作者编译与语义覆盖证据
verification/runner/               当前评分/多轮软件的离线验收身份
tests/                             合同、数学见证与工具测试
docs/                              定位、方法、使用和验证状态
  release-consumer-README-v0.3.0.md  默认32题任务ZIP中唯一README的来源
  release-consumer-README-v0.2.0.md  旧43题任务包指南（保留）
  selection-v0.3.0.md               32默认/11后备及80槽的开发取舍
  terra-pilot-2026-11-02.md          旧177槽试跑与32题方案事后分析
  results/                         已审结果的紧凑指标与响应身份，不放原卷
  release-consumer-README.md        v0.1.0历史包内指南来源（保留原样）
  release-notes-v0.1.0.md           v0.1.0正式发布说明来源
releases/v0.1.0/config.json          可从标签恢复的评审计划身份锚点（不入候选ZIP）
releases/v0.3.0/                    新默认包的本地配置与第三方许可
protocol/history/v0.2.0/            原43题/177槽suite、profile与可靠性配置
```

每题 `case.json` 使用 `path_base="case"`，文件路径相对其所在题目目录；默认与后备manifest分别按分类列出case.json，Suite.load可直接接收manifest路径且保留同一个cases根。题面是唯一候选任务，完整白名单由solver_files决定。参考、rubric、contract、来源、审核、作者Lean与分类均在评审侧。

| 软件边界 | 职责 |
| --- | --- |
| `math_gauge/catalog.py` | suite/case/阶段合同、路径、附件、散列与候选投影 |
| `math_gauge/execution.py` | 请求与原始响应、冻结合同、源码/清单提取、受限编译、公理审计 |
| `math_gauge/review.py` | 响应绑定审核、逐阶段与交付门槛、报告和配对比较 |
| `math_gauge/benchmarks.py` | 评审侧profile、完整主计划与独立分项投影 |
| `math_gauge/reliability.py` | 独立轮/分支调度、原始历史、重试、KEEP/FULL材料与同计划证据复用 |
| `math_gauge/reliability_review.py` | 多轮材料、当前说明、数学状态与候选Lean的审核绑定 |
| `math_gauge/eligibility.py` | 原始运行证据导入、运行审核快照、逐槽位资格与继承来源 |
| `math_gauge/release_projection.py` | 版本化候选标识符投影；只改指定命名与非数学署名字段，不重写原始答卷 |
| `math_gauge/harness.py` | 候选白名单导出、单指南任务包、独立标准库控制工具、runtime冻结、完整消息及只读材料核验 |
| `math_gauge/harness_answers.py` | 按顺序保存精确请求和全部原始尝试、自动构造分支历史、显式缺测及单个返回ZIP |
| `math_gauge/harness_import.py` | 安全读取返回ZIP及兼容v1/v2提交，结合可信评审计划导入共享多轮证据和审核入口 |
| `math_gauge/scoring.py` | 固定分母分项/加权聚合、未知区间、轨迹与配对诊断 |
| `scripts/catalog.py` | 分类证据与当前材料身份，生成出题侧导航 |
| `scripts/validate_protocol.py` | 固定计划、消息、候选白名单与未执行状态 |
| `scripts/release.py` | 命名候选ZIP与校验和的可复现构建、安全只读检查及对应标签的评审计划恢复；不调用模型 |
| `scripts/formal/check_evidence.py` | 当前作者证据与原始编译记录的身份复核 |

公开与私有材料使用同一runner，不在私有数据内复制执行或评分实现。新分项与多轮入口继续共享案例合同、候选投影和原始源码核验；CLI只做参数分派。当前默认任务包以中性名称交付32份候选任务、约定附件、一个README、可选控制工具、清单及许可；确定性的标识符投影不改数学内容，原始来源、完整主计划与投影对应记录保存在包外；执行端无需本仓库、Codex 或 Math Gauge 安装，也无需取得评审计划。命名发布ZIP是候选交付物，GitHub自动Source code压缩包仍含公开参考。新Release与题集同版；历史v0.1.0保留旧约定，发布配置和散列不是秘密答案隔离或后端认证。`runs/`、`.dev-mesh/`、缓存与凭据只保留本地。

## 历史保留与恢复

旧题、历史实验、设计稿与归档保存在Git历史。清理前的基线提交为 `6a48027baa33e06e913a554fb8bac9394a82b480`；原43题/177槽机器配置另明确保存在 `protocol/history/v0.2.0/`，旧题文与更早实验仍从Git恢复。

```sh
git ls-tree -r --name-only 6a48027baa33e06e913a554fb8bac9394a82b480
# 将PATH_AT_BASE替换为上一步列出的路径：
git show 6a48027baa33e06e913a554fb8bac9394a82b480:PATH_AT_BASE > /absolute/path/to/restored-file
```

历史引用中的Git提交与提交内路径是来源记录，不是当前运行依赖。恢复到题库外的新位置；旧成绩绑定旧材料；允许明确标注的事后重算，但不能冒充新版32卷/80槽的独立运行。

[贡献指南](../CONTRIBUTING.md) · [使用指南](usage.md)
