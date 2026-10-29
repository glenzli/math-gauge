# 来源与局部抽取

已读取固定 PFR 提交 `f6bdcac2365623d3667d3ff8fd8ddb7f95ce2313` 的 `PFR/Main.lean` 全文件，并核对第 246–270 行与 `blueprint/src/chapter/pfr.tex` 的对应段落。该提交由 RLM25 配置选定。代码 Git blob 身份保存在 sources.fragment.json。

原工程先通过熵论取得 H 与稠密陪集；本题只抽取最后的有限集覆盖桥梁，把已得到的非空切片作为明示输入，并推广到任意阿贝尔群。这个局部步骤确实不需要特征二或环境有限性。没有复制原工程代码，使用已锁定 Mathlib 的已证明 Ruzsa 覆盖引理并独立实现全部桥梁。许可证为 Apache-2.0；数学题与 Lean 实现为独立改编。F105 为正确对照，F106 为同源生成版本，不能跨数据切分。
