# 候选 Lean 源码与核验证据

本合同属于公共 runner。作者参考的编译与真实候选源码的核验分别记录；编译成功不代替数学及语义审核，也不改变 human pending 状态。

## 输入消息

`math_gauge.catalog.candidate_message(request) -> str` 是两种模型适配器共同使用的消息构造器。没有附件时，它保留原题面字节；旧题若有非空 instruction，保留原来的 instruction 前缀。有附件时，追加中性的文件名与完整文本围栏，围栏长度大于源码里的连续反引号，避免内容被截断。该消息不追加题号、track、真假标签、family、来源或评审材料等传输元数据。

`Suite.prepare` 的 prompt.md 仍保留原题面合同；适配器应调用本函数，而不是只发送 prompt.md。request 中的 files 是唯一附件来源。runner 为每次运行生成不变的 run_id，在 run.json 的逐题记录冻结 task_kind、family_id 和 candidate_message_sha256，并在 record.json 同时保留 request、message、response 散列。适配器 stdout 以二进制读取，冻结原始字节，不正规化 CRLF。缺失 task_kind 的旧题默认 exploration，缺失 family_id 默认使用题号。

## 原样提取与文件身份

`extract_candidate_lean(response)` 接受题面已有的两类标记：`lean filename=Solution.lean` 信息栏，或 Lean 围栏前的独立文件名行（包括标题、反引号与 File:/文件：前缀）。也接受 `lean Solution.lean`、lean4 与更长围栏。文件体逐字提取，保留 CRLF、Unicode 与空行，记录 UTF-8 起止字节。不能从多个不同版本猜选“最后一份”，不能补 import、改定理名或修 proof。

重复文件名（含大小写别名）、路径逃逸、未结束或无法确定文件名的 Lean 块会得到 format_error，并标记 manual_extraction_needed。仅文字说明、路径链接或空的源码交付集合不算已经交付源码。格式状态与数学判断分开；说明段可能有未命名 Lean 片段，不能因此直接把完整合法文件算成数学失败。提取器不支持的合法等价标记应由独立评审记录为提取限制。支持普通 Unicode 模块文件名；其他合法特殊标识符若仍不支持，同样进入格式审定，不冒充数学错误。

独立评审可用 `extraction_override={reviewer, reviewer_kind, reason, files}` 在新输出目录重新核验；files 只能列出 name/start_byte/end_byte。实现只接受同一冻结答卷中完整围栏体的原始 UTF-8 字节区间，拒绝传入 content、截取半个块、重复区间或文件。人工/AI提取理由与身份持久化并绑定 artifact；它可以区分解释片段与完整交付，不能补代码或删去同一文件内的一行。旧 format_error 收据保留，不覆盖。没有给六道题增加 namespace 或最终声明名要求。

核验从 runner 的冻结 response.md、record.json、solver/request.json 读取，首先重算 request/response 绑定。输入附件取自 request 内的原内容，不信任候选可能修改过的工作目录文件。输出保存 response、request、submitted/、inputs/ 和 manifest.json；输入原件始终保留。

提交的同名文件作为该文件的完整替换。编译集合是全部提交文件，加上这些文件实际 import 的冻结背景模块及其传递依赖。未被引用的旧候选文件不会自动加入新项目；这允许完整重写，同时避免把旧错误工件算进新成果。所有替换和依赖来源都会记录；定义含义是否保持仍由独立数学评审决定。循环依赖、路径冲突或依赖缺失不能通过编辑源码化解。

## 本批六个生成/修复版本

| 题目 | 已有题面允许的交付 | 自动核验配置与语义边界 |
| --- | --- | --- |
| F102 | 新完整文件；自行写最终声明，可用 Core 定义 | 不指定最终文件名或定理名；覆盖精确幂零界、理想像、商映射复合 |
| F104 | 修改或补充原三模块，也允许完整等价实现 | 可替换同名文件；保留正文对象和条件，覆盖最粗性、唯一性及连续性双向性质 |
| F106 | 全部新增文件，明确要求可导入 Solution.lean | 调用方传 required_files=("Solution.lean",)；沿用背景定义，不附加参考中的 helper 名称 |
| F108 | 全部新增或改动文件，可修订 Core/Multiplier/Candidate | 不把输入文件按字节强制不可改；背景数学含义不变，保留同一个 C 和全部逆算子义务 |
| F110 | 完整修订源码；可复用原附件或采用其他正确路线 | 允许反例加原条件下保留结论；恢复条件不限作者的 Realizes，不要求复制参考文件布局 |
| F112 | 自行声明定理与实际反例数据，可等价编码 | 不指定最终文件名或 theorem 类型；完整保留扩展值函数定义域 |

这里没有把生成题的 expected=aligned 当作已发生的模型结果。audit 六题无需新增候选 Lean；其固定输入编译证据已经独立存在。纯文字研究题不因本入口而增加 Lean 义务。

## 编译入口与隔离

```python
from math_gauge.execution import verify_candidate_lean
receipt = verify_candidate_lean(
    case_dir, new_output_directory,
    dependency_root=pinned_complete_dependency_root,
    lean=pinned_lean_binary,
    timeout=120,
    required_files=(),
)
```

case_dir 是单题运行目录，输出目录必须全新且在其外部。调用不执行模型，不改题库或作者参考。依赖身份、导入解析复用 scripts/formal/verify.py 的固定 4.29.1 配置；不改变作者验证器的默认合同。

每次使用新的临时源码、编译产物及 scratch 目录。macOS sandbox-exec 默认拒绝访问：只允许读取明确列出的 Lean 安装、依赖编译库、当前源码和必要系统文件；只允许写临时 build/scratch，拒绝网络与子进程创建。源码不可写，原答卷、题库及参考均不在允许读取范围内。先实际验证正文件可读、原答卷和仓库验证器不可读；探测失败时不执行候选代码。其他平台或不可用隔离均返回 infrastructure_error，不退回无隔离主机编译。编译超时终止进程组。

候选审计器按实际本地模块来源枚举所有声明，包含任意 namespace、私有声明和未被最终定理引用的自定义 axiom；再收集全部依赖。仅允许 propext、Classical.choice、Quot.sound。它没有 MathGauge 命名空间筛选漏洞。编译前后的源码、已有编译产物和验证器身份均核对；原始日志及最终 olean 随收据保存。

依赖环境必须能够实现题面所允诺的 Mathlib。已存在源码却缺缓存、隔离失败或依赖身份错误属于 infrastructure_error；不存在的模块/语法/类型错误属于 compile_error。缺少传递 olean 也归环境故障。不能修改候选源码来规避缓存缺失。实际数学命题与正文是否相同仍需独立审阅，不由签名相似度或编译结果推断。

## 判读和审核绑定

收据状态为 passed、format_error、compile_error、infrastructure_error 或 axiom_rejected。候选源码编译超时为 compile_error 且 reason=timeout；生成的审计器自身失败或超时为 infrastructure_error，实际禁用公理则为 axiom_rejected。收据含 response_sha256、request_sha256、files_sha256、input_files_sha256、artifact_sha256/manifest_sha256、engine_sha256、原始命令、日志及公理清单。passed 只表示原样源码通过当前工程核验。

严格生成/修复通过还需要独立语义审核确认所有题面义务，且审核绑定相同 response、artifact 和编译收据身份。基础设施错误待修环境后原样复验，不计模型数学失败。源码修订属于另一个答卷或明确的后续贡献，不回填原结果。无代码或诚实未完成应如实记录为交付未完成，不能利用空清单产生成功状态。
