# 有限复合与路径节群 · LCH02

将附件中 obligations.json 指定的全部20项义务完整形式化为一个Lean项目。本题是明确的选段任务；完整章节文件只为提供原文和上下文，清单之外的内容不计为交付义务。原文含证明；前置文字只作背景。

使用Lean4.29.1和mathlib5e932f97dd25535344f80f9dd8da3aab83df0fe6。formal_oet/附件是冻结前置模块，可直接导入，不得修改或同名覆盖。只允许这些模块、标准库与固定mathlib，不得读取目标作者实现、评审或下载其他依赖。

保留原文结构、前提、量词、定义域和结论强度。允许等价表示、合并声明、辅助引理和有效替代证明，但须给出表示对应；不得把目标藏入字段、证书或前提。

交付完整源码，每个文件用独立的命名代码块，例如 `lean filename=Main.lean`。Main.lean必须导入所有目标模块，辅助文件也须全文交付。不得使用sorry、admit、新增公理或跳过内核检查设施；逻辑公理仅允许propext、Classical.choice、Quot.sound。

另用 `json filename=alignment.json` 交付对象：case_id="LCH02"、version="0.1.0"、items。items必须恰好覆盖清单全部20项，每项含id、status（complete/incomplete）、declarations（file/name数组）、representation（对象/参数/量词/结论的对应说明）、dependencies（实际使用的义务ID数组）。complete须列真实声明且全部子目标均完成；未完成项不能删除。工作区路径或链接不能代替文件内容。
