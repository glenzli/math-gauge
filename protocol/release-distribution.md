# 任务包分发合同

当前源码及题集为 **本地0.6.0草稿 / human pending，尚未发布**，以[当前suite](../cases/suite.json)、[profile](benchmark-profile.json)及[本地0.6.0指南](../docs/release-consumer-README-v0.6.0.md)为准。当前可从源码准备v1目录包、只读检查和显式bundle导入；这些操作不调用候选模型，也不产生已发布的0.6.0中性ZIP。材料准备者使用受信源码导出；外部执行端只需导出包，不需仓库、完整评审计划、Math Gauge安装或Codex。

已发布的[v0.4.0](https://github.com/glenzli/math-gauge/releases/tag/v0.4.0)采用`benchmark-v0.4.0.zip`命名，交付端只需阅读包根目录的一份README，其源文件为[0.4.0原运行与返回说明](../docs/release-consumer-README-v0.4.0.md)。0.4.0及更早发布资产、原指南和历史合同保持原样，不能用当前题集替换。新任务发布沿用对应suite版本；内部提交格式和工具实现可有各自版本。已发布[v0.1.0](https://github.com/glenzli/math-gauge/releases/tag/v0.1.0)保留其软件/题集分开编号及旧目录约定，见[历史发布说明](../docs/release-notes-v0.1.0.md)与[原包内指南](../docs/release-consumer-README.md)。

## 当前范围与交付边界

本地0.6.0默认26份相关公开任务：14份书面论证、4份历史Lean语义审计、4份大Lean形式化和4份真实答卷审阅，共18个数学家族；另31份reserve须显式选择，全bank保留57条任务。LCH01(8)、LCH02(20)、HCH02(40)同属CH2家族，先在家族内聚合；MG-C003仍为92项。合并3份私有探索后是29份任务、21家族，但私有题、答案、判据和逐题结果均不进入任何公开ZIP。来源及范围见[0.6选题说明](../docs/selection-v0.6.0.md)。

协议0.4的四written面板为GR002、GR014、GP001、GP002，各A1/A2及neutral/affirm/deny各一次，公开标准42条记录、合并探索45条。当前是观察后选题与来源组合；相容旧written/AR记录按原身份复用，不能称全套同步fresh新考。新8份Lean仅用A1，GP001/GP002各整套5槽fresh，两模型各18个标准新槽；MG-C003另有固定3次中性追问的92项对齐专项，不入标准分母或权重，也不替代首次A1。题目与答卷仍待人审，正式比较资格为false。

待审真实答卷属于AR题的合法题目材料，评审参考答案、判准与逐题审核留在包外。AR纳入、8份原答重评及当前选题均是观察后的方法变更；原答、旧审核、旧0.5配置/结果和已发布资产保留原身份。公开参考及Git历史用于透明复核，不使任务包成为隐藏留出集；历史中间版本是否公开尚未核实。

## 已发布中性包的不可变格式

以下为已发布v0.4.0的单根目录结构，属于同版本历史交付合同：

```text
benchmark-v0.4.0/
  README.md
  cases/<case-id>/task.md
  cases/<case-id>/files/<declared-attachment-path>
  tools/benchmark.py
  manifest.json
  LICENSE
  THIRD_PARTY_NOTICES.md
```

任务正文只保留一份，附件保持显式候选白名单。`task-inputs.candidate-projection/v1`只变更指定Lean附件的namespace/end前缀、义务表schema及署名中的特定非数学文字。v0.3.0/0.4.0原指南中的30份Lean附件、两份义务表和两份署名是各自冻结版本的历史计数；当前导出内容、数量与原始/投影字节必须从实际manifest核验，不沿用旧常量。数学正文、定义、公理、证明体、交付义务、原LICENSE及作者/作品/DOI/CC BY归属保留，故意语义失配的Lean仍保留原失配。原始仓库文件不改写；原编译证据不能当作新投影字节的编译记录。

清单及工具属于控制端，不能作为提示交给模型。包内README只给执行流程、作答格式和必要约束，不载入设计论说、成绩、仓库URL或项目品牌。协议schema、工具自有文字及suite显示ID使用中性命名；完整源码provenance与source路径只保存在评审sidecar。许可和第三方作品归属保留。参考、rubric、真假、选择理由、审批、作者证明、完整profile和评审计划均不入ZIP；GitHub自动Source code压缩包含这些公开材料，不是候选交付物。保留题号及公开数学内容仍可能被检索溯源，中性投影不构成匿名或未见题保证。

不可变数据集不预选模型或预算，实际任务范围在新运行中冻结。已发布中性v2包的工具按固定顺序取得完整消息、保存所有原始尝试，再打包一个`answers.zip`；请求历史只来自允许的父节点，未知平台字段保持未知。记录与打包工具生成身份及文件字段，不要求操作者手写散列或完整提交JSON。该返回包由`benchmark-import --input answers.zip --plan ... --out ...`统一核验并接入共享记录。当前0.6.0的v1 partial导入另须显式提供`--bundle`和同一冻结计划，按[本地指南](../docs/release-consumer-README-v0.6.0.md)执行；两种交换不能混用文件布局或入口。来源、数学、候选Lean与人工审核分别完成。

## 执行端能力与可保证的范围

已发布中性包的单一README同时给出人类操作者流程和可复制给独立Codex controller的启动说明，不另发solver提示。controller可读全包和调度，solver只接收单槽位的完整候选消息、冻结参数和所选条件允许的本分支历史/工具反馈。读过指南的controller不能兼任solver，继承全部controller聊天的fork也不满足新上下文。候选可为非GPT模型；必须有真实适配器，不能推定任意Codex后端都可调用任意provider。

工具只提供导出、检查、冻结、消息构造、留证和导入接口，不提供模型派发、并行调度、超时终止、重试等待或进程隔离。单run按冻结顺序串行；实际provider参数映射、角色与历史传输、工具权限、禁止外部搜索、文件访问限制、各分支文件快照及完整执行日志由harness落实。省略execution_track仍为默认无工具；显式本地工具条件不增加使用Lean的提示或义务。候选工具联网限制与controller模型服务传输分开核实。无法满足所选条件时保持prepared/missing和具体限制，不制造答案或来源证明。

| 层次 | 可核对的保证 | 仍需独立证据的部分 |
| --- | --- | --- |
| 下载完整性 | ZIP及清单绑定的字节与文件白名单，显式版本的候选投影及输入散列 | 单独散列不认证发布者；可信下载来源及checksum来源另核实 |
| 运行与回传 | runtime/数据集身份、固定顺序、精确文本历史、第一可读答卷锁定、全部已记录尝试、累计预算与缺测 | 平台实际收发、未披露调用、真实后端/时间、成功终态、超时/上限执行、文件/网络/会话隔离 |
| 评审接入 | 返回包匹配评审端事前保存的精确数据集锚点，安全读取原始材料并接入共享合同 | 数学正确性、候选Lean语义及真实编译、人工批准与正式比较资格 |

执行端可以独立准备和交回材料，不等于仅凭提示词就获得闭卷隔离或可信成绩。候选不能读完整解压目录、控制脚本、清单、其他题、全局记忆、旧结果或公开参考的本地副本；禁止外部检索须覆盖全部实际工具通路。公开参考可访问这一事实不赋予候选本轮访问权限。具体边界及原始证据合同见[外部交换实现合同](external-harness.md)，原生终态取证见[终态证据说明](native-terminal-evidence.md)。

## 当前本地准备与历史构建

当前0.6.0使用[本地指南](../docs/release-consumer-README-v0.6.0.md)中的`benchmark-plan`、`benchmark-export`、`benchmark-export-check`和`benchmark-import`。Lean初答用initial-acquisition profile选择`lean-audit`及`lean-formalization`；四written面板导出使用标准`repeat`、`neutral`、`stance`目标，实际补考另冻结GP001/GP002的10槽白名单。`written-new-panel`可供评审侧`select_slots`使用，当前外部目录导出不接受该目标。

仓库尚无`releases/v0.6.0/config.json`；现有中性v2发行检查器也受固定目标白名单约束，不能直接把含新execution group的当前profile视为已支持的中性发行。已有0.4.0/0.5.0配置各绑定自己的suite版本、任务数与槽数，不能在当前0.6.0题集上构建或恢复成旧发行。新的中性任务包需先完成对应发行配置及兼容验收，再从其精确干净源码提交构建；本地准备或已有指南不表示发布可用性。

以下仅为v0.4.0历史复现命令，必须在对应版本的精确干净源码检出中执行，`FULL_COMMIT_SHA`填该发布的完整源码提交号，输出路径必须是新的；不能填当前0.6.0提交：

```sh
python3 scripts/release.py build --version 0.4.0 --source-commit FULL_COMMIT_SHA \
  --out runs/releases/v0.4.0
```

该历史构建落盘命名ZIP、`SHA256SUMS`和包外`evaluator-plan.json`。包内`release_provenance`只保存不透明源码承诺、投影版本及候选路径/散列；完整仓库/提交身份、源码散列及源文件到投影的映射留在评审sidecar和构建回执。单独检查包不能从不透明承诺恢复或认证原始源码。评审文件同时保存完整基础计划和期望的精确数据集身份；ZIP导入必须与它匹配，不能只接受提交方自洽重算的清单。完整计划由评审端保留，不发给候选或要求外部运行端取得。`releases/v0.4.0/config.json`的v3发行合同指定中性投影；任务版本与Release版本不一致时拒绝构建。更早资产同样保持只读，复现使用各自对应源码。

工具从同一共享实现生成中性wire版本；已安装的检查/导入器只载入自身可信源码生成的中性实现，不执行ZIP中的工具。评审端从原suite重建声明的候选投影，并核对请求/消息散列。原中性请求、完整messages、答卷、平台证据及返回ZIP均保留；共享记录若将传输schema规范化，明确记录转换及原请求散列，不把内部副本当作实际发送内容，也不逆写答卷命名空间。

本地预览记录父提交和实际输入身份，不把未提交源码冒称为发布提交。发布构建仍需其对应源码身份及干净状态合同。构建、只读检查和评审计划恢复都不调用模型；本地打包不等于提交、推送、tag或远端发布，已发布资产保持不可变。

ZIP内的题目字节及清单保持不可变；每次模型或预算选择产生新运行。完整性散列绑定材料，不认证平台、第三方执行时间或隔离真实性。普通外部导入继续标记`external_import`；fixture/replay不能变成模型结果，声明也不自动开放正式比较资格。报告按冻结profile保留固定分母、missing/failed/unresolved及来源，原作者43卷/372义务/470模块不覆盖新增范围。

[外部交换实现合同](external-harness.md) · [仓库评审操作](../docs/usage.md) · [运行证据标准](execution-evidence.md)
