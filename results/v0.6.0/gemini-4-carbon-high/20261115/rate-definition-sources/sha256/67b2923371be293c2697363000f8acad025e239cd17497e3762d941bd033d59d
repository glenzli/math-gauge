# 历史章节的完整 Lean 形式化

将附件中的第2章全部数学内容形式化为一个 Lean 项目。原文含证明；前章文字只作背景。obligations.json 明确本题全部40项定义、表示及证明义务，含正文中没有独立编号的事实。以冻结原文和该清单为完整交付范围；不得沿用其他版本的章节内容。

使用 Lean 4.29.1 与 mathlib 提交5e932f97dd25535344f80f9dd8da3aab83df0fe6。给定 formal_oet/ 下两份前置模块可直接使用，不得修改或同名覆盖。只允许这些冻结模块、Lean标准库和固定mathlib；不得读取或导入目标章节或后续章的作者实现及其他外部材料。可使用本地工具，禁止联网检索或下载依赖。

遵循原文的结构、量词、定义域、条件与结论强度。允许等价表示、合并声明和有效的替代证明；使用等价表示时须证明其对应。不得把待证结论作为结构字段、证书、假设或实例直接取回。

提交完整源码，每个文件用独立命名代码块，例如 `lean filename=Main.lean`；Main.lean须导入所交所有目标模块，辅助文件也须全文提交。工作区路径或链接不能代替文件内容。不得使用sorry、admit、新增公理或跳过内核检查的设施；逻辑公理仅允许propext、Classical.choice、Quot.sound。

另用 `json filename=alignment.json` 代码块提交对象，含case_id="HCH02"、version="0.1.0"与items。items必须恰好覆盖40个义务ID；每项为{"id":"…","status":"complete|incomplete","declarations":[{"file":"Main.lean","name":"命名空间.声明名"}],"representation":"与原文的对象、参数、量词及结论的对应说明","dependencies":["实际引用的义务ID"]}。complete表示该项全部目标完成，须列真实存在的声明；incomplete须明确保留。声明可合并或复用，依赖仅记录实际采用的证明。最后说明你是否已经完整完成且严格对齐整章，并列出未完成或未确认的范围。
