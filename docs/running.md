# 运行与返回

当前benchmark为0.6.0本地草稿，公开26题、42条标准记录；合并私有3题为29题、45条标准记录。题目与正式比较仍待人工批准。

所有准备、导出、检查和导入均不调用模型。实际模型接入由外部harness或已授权适配器完成；请求标签不认证后端。

## 检查当前材料

```sh
python3 -m math_gauge validate
python3 scripts/catalog.py --check
python3 scripts/validate_protocol.py
python3 scripts/records.py check
```

## 冻结运行并导出

先在临时工作区保存实际runtime：模型/适配器、系统提示、支持的参数、工具条件与预算。当前新采集允许本地工具，禁止工具联网与外部检索；完整字段及证据边界见[执行证据](../protocol/execution-evidence.md)和[外部harness](../protocol/external-harness.md)。

同一题的各轮条件必须一致。预算分开配置：书面及新AR每轮2700秒，其余七项新Lean每轮5400秒，C003初答及其后续每轮10800秒。原生、broker与外层分别设置并留证，工具与编译等待计入。

例如使用5400秒runtime准备七项Lean：

```sh
python3 -m math_gauge benchmark-plan --target lean-90 --runtime /ABS/lean90-runtime.json --out runs/new-lean90-plan.json
python3 -m math_gauge benchmark-export --plan runs/new-lean90-plan.json --out runs/new-lean90-bundle
python3 -m math_gauge benchmark-export-check --bundle runs/new-lean90-bundle --plan runs/new-lean90-plan.json
```

C003改用`--target c003-180`与独立10800秒runtime。GP001/GP002新五槽用`written-new-panel`；三道加强书面用`written-refresh`；AR用`answer-review`。完整重复面板可选`repeat`、`neutral`、`stance`。目标选择执行范围，完整分母仍由同一当前profile保存。

候选只接收工具构造的完整messages、显式附件和本分支历史。A1/A2独立，三臂各从同一A1展开；C003三轮专项连续承接自己的上一轮。操作者的说明、全计划、评分、参考、其他答案和全局记忆不交候选。

## 保存与返回

按[正式结果记录合同](../protocol/result-record.md)保存完整原答、自评原话、KEEP/FULL、源码、对齐表、封卷工程及可获得的执行资料。执行成功、可读答复、编译成功、数学通过和人工批准分别记录；无成功父终态的依赖轮按冻结规则阻断。

外部v1目录包使用其共享controller与submission模板返回，评审端按同一冻结plan和bundle导入：

```sh
python3 -m math_gauge benchmark-import --bundle /ABS/bundle --input /ABS/submission.json --plan /ABS/frozen-plan.json --suite cases --out runs/new-import
```

原始交换包与正式结果档案是不同层次。正式档案按用户明确选定后生成，保留原始来源与未知项；不把整理者抽取的自评伪称为候选新增声明。旧DeepSeek答卷的补全指令见[原答恢复说明](deepseek-result-recovery.md)。

## 固定留档

用户选定留档时，保存到`results/v0.6.0/<model>/<record-id>/`；检查命令为`python3 scripts/records.py check`。未选定的运行、试验与调试日志使用临时`runs/`，不自动永久保留。公私共用版本和runner，私有原始材料在私有仓库，公开只保留聚合。
