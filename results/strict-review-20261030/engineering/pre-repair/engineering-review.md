# Math Gauge strict engineering review — 2026-10-30

本轮一次完整离线门槛全部通过；严格源审另有两项 P2 合同缺口，尚未修改源码。所有证据仅写入本目录。候选模型请求 0，Lean 新编译 0，人工审核状态未变。

- Dev Mesh：`owner=sol-engineering-validation`，`run_id=strict-engineering-20261030`，`scope=strict-engineering-readonly-20261030`，intent 为 read。
- 验证前 HEAD：`1ba259df750355a0c5619619d42104219e8b2524`；复核结束父代理归档后的 HEAD：`9e536ad5ebce182ffcb6bcaabdc24c7fbec221c3`。
- 已重新核对 8072 个既有文件，字节变化 0；runner 指纹：`6f8cfa69e334df339fade48e67e50fd5b339f40d66dcc573f3b7528d70677317`。

| 命令 | 退出码 | 结果 |
| --- | ---: | --- |
| `python3 -m unittest discover -s tests` | 0 | 132 项：117 通过，15 可选 Lean 环境测试跳过 |
| `python3 -m math_gauge validate` | 0 | 20 题，human_approved=0；suite 6ad8a8a7c80a7ba769b0677ef250bf9998d9601d190f271ce6b357fa91f5308d |
| `python3 -m math_gauge validate --suite drafts/true-goal-six-20261029` | 0 | 6 题，human_approved=0；suite fb720a5e194c50219c1bbfd44a38d17f484c8e5e387239059e2e6a8a2bbbc7fa |
| `python3 -m math_gauge validate --suite drafts/public-proof-extractions-20261029` | 0 | 3 题，human_approved=0；suite 183ff9585facd68e422609bcb24199878c45da6bb2708a8ddf570c11c0738a8b |
| `python3 -m math_gauge validate --suite drafts/lean-alignment-20261029` | 0 | 12 题，human_approved=0；suite f59c156edaf8684cd62a5505701bc039aaeac7d76dee9f535d20c34f946844b9 |
| `python3 -m math_gauge validate --suite drafts/progressive-groups-20261030` | 0 | 41 题，human_approved=0；suite fb0f0e270c91558320688330913858c7593823ae3a7d31beeb3fdfd787716263 |
| `python3 -m math_gauge validate --suite drafts/chapter-exams-20261030` | 0 | 2 题，human_approved=0；suite b251f76e2e18e94c81b6929f743b17506ff85a76f54c6267db879e49321615ef |
| `python3 exercises/refresh_catalog.py --check` | 0 | 747 来源、340 本地链接、41 原题、7 章 |
| `python3 protocol/reliability-20261030/validate_materials.py` | 0 | 43 候选投影、372 必答义务、48 冻结后续消息、48 独立历史边；模型调用 0 |

完整命令参数、耗时、stdout/stderr 路径和日志散列见 [checks.json](checks.json)。测试环境为 Python 3.14.2，仅设置 `PYTHONDONTWRITEBYTECODE=1`；真实 Lean 环境变量均未启用。15 项跳过的准确名称及理由见 [default-skips.json](default-skips.json)。源码与测试检查确认适配器为回放、本地 Python 合成程序或显式 mock，默认门槛不发候选模型请求。

**P2 · ENG-001：候选 Lean 收据未绑定题组合同。** `execution.py:515-536` 读取并执行冻结合同约束，但 report/manifest 未保存其散列；`review.py:115-124` 只核对 request/response。两次运行的候选输入和答卷相同、评审合同不同时，较弱合同收据可复用于较严合同。合成探针中较严合同要求 Main.lean，旧收据仅含 Other.lean，仍接受 5/5 阶段通过。建议把 group_contract_sha256 写入收据和工件 manifest，并在消费时与运行及审核合同一致核对。探针不构成真实 Lean 编译成绩。

**P2 · ENG-002：基础审核/报告未重验候选输入。** `review.py:10-30` 重验 response 与合同，但不重算 solver/request.json。合成探针改写请求后，既有审核和整组完成报告仍被接受。`compare_models` 在 `review.py:461-471` 另有正确的输入散列检查，因此此发现限基础 inspect/templates/apply/report 路径。建议在 inspect_run 中核对原请求和候选消息散列及身份。

探针原始数据见 [contract-probes.json](contract-probes.json)，可读复现程序见 [contract-probes.py](contract-probes.py)。所有数据标明 fixture_only；不生成模型能力结论。两项缺口均仅报告，未修复。

现有作者 Lean 证据绑定检查：41题的 123 份冻结输入、301 个 manifest 源/覆盖文件、260 个编译源与日志、260 个现有 olean、389 项外部导入缓存，以及 82 项编译器/锁文件散列均匹配。P001 的22条日志按报告原始输出根正确解析。没有重新编译；完整语义范围沿用原目录中的40完整、P003部分，并未升级。具体文件与限制见 [existing-lean-bindings.json](existing-lean-bindings.json)。此前一项真实隔离题组小样例的执行器和测试源码散列亦与当前一致，仅复用其既有证据，不表述为本轮新执行。

其他既有严格合同源审通过：显式候选投影、原始答卷与冻结合同、全义务 alignment、实际审计声明及三公理白名单、数学/编译/环境失败区分、所有必答阶段完整通过、阶段错误传播和当前导航路径。未实现多轮调度或新增功能。后续目录移动或源码修改需按受影响依赖做增量核验。

详细结果与全部核心源码散列见 [engineering-review.json](engineering-review.json) 和 [source-identity-after.json](source-identity-after.json)。
