# 当前 benchmark 验证证据

本目录只保存现行43份题目的有效作者证明、独立审核及材料身份。候选模型尚未运行；这里没有模型答卷或通过率。已淘汰题目与旧实验仅由Git历史保存。

- [作者覆盖与复核方法](author/README.md)：42份完整、GP003部分完成；369/372项义务闭合。
- [当前作者账本](author/ledger.json)：每题源码、编译、公理检查、独立审核及未完成项。
- [目录迁移映射](layout.json)与[题面保全记录](preservation.json)：43份实际候选消息、223份数学输入保持原字节。
- [GP003剩余证明义务](../cases/proofs/MG-GP003/formal/GAPS.md)：编译成功不等于原题全部形式化。

执行`python3 scripts/formal/check_evidence.py`可离线复核当前材料和保存的证明证据，不需要Git历史、Lean缓存或模型服务。重新编译与候选交付核验见[作者工具说明](../scripts/formal/README.md)及[候选Lean合同](../protocol/candidate-lean.md)。

[题目分类](../cases/README.md) · [项目首页](../README.md)
