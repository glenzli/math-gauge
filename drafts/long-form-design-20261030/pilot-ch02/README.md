# OET 卷1第2章整章 Lean 化：流程校准草案

- `candidate/`：唯一模型可见投影，共8个文件；保留原文证明，属于autoformalization轨。
- `review/`：26项原子义务、参考路线、依赖边、作者实现边界、候选投影哈希、跨章引用审计、前置编译证据。
- `review/background-compilation.json`：两个前置模块与导入烟测实际通过；未编译作者目标章或候选解答。
- `review/build/`：本轮临时编译目录；含外部mathlib缓存链接，不属于可分发/候选投影。
- `review/tracks.md`：说明去证明的discovery轨需另建，尚未生成。

状态：draft / human pending；未新增正式case，未改变现有分数，未跑模型。主设计见同级上层 `oet-chapter-design.md` 与 `.json`。
