# 来源与改编边界

公开来源：[ProofNetVerif 固定版本](https://huggingface.co/datasets/PAug/ProofNetVerif/tree/91183e5b12d64374827bf2782db629b5b0f8f319)，MIT。选中 valid split 第 0 行，id `Munkres|exercise_13_4b1`；原条目的 `correct` 为 false。具体预测及行内容指纹见 source-evidence.json。

将同一集合上的拓扑族推广为一族到不同拓扑空间的映射，加入初始拓扑的入射映射泛性质。历史候选只提供共同下界，漏掉最粗性；本题用可编译的离散拓扑实现这一不足，并另设完整正确实现作正控。具体 Lean 是本项目独立编写，非历史原始输出。

ProofNet-Verified 用于交叉核对同主题的陈述与公开纠错方向；此题的主要原始错误证据来自 ProofNetVerif，不能将二者混成同一数据集或同一次审核。

不复制教材的长段原文或原参考证明；题面、完整参考与 Lean 证明独立编写。Mathlib 定义与库引理按固定修订使用，见 sources.fragment.json。本题不抽取 OET 未公开正文或私有答案。

公开原题及相近错误可能进入训练语料，故适合作校准与条件保持测试；不能声称未见、无污染或已证明有区分度。同源变体须按 family_id 整组划分。
