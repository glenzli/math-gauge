# 本题范围与独立审核参考

次推：路径局部证书被错误提升为全部路径前提

旧提交 `74f2e783c7174b74adf849c500d63e6a43658bf1`，修复 `11b7ec1fc726c561853d0c9e6206da77c6a8ce92`。

- Lean 路径：`the-operator-evolution-theory/formal-oet/formal_oet/vol_03/ch_14_empirical_network_fitting/path_guarantee_domains.lean`。
- 旧 blob：`b4bbb7253d5cb955adab6bc50b1462ddb6b5045f`；SHA-256：`55dfdf12c7889bfc3a06793b3dd8619c8f415ad13ecd69ad26d8e7eb186cc4eb`。
- 同提交正文：`the-operator-evolution-theory/vol-03-empirical-fitting/14-empirical-network-fitting.md`，blob `1a91a04561ecf286d90a4fa9242cf2404f399c05`。这份正文在修复提交中完全未改，排除用后版正文拼旧版 Lean 的文件漂移。

正文 `h-93b9c20ea18b4e59` 只并起目标分量可评估的路径保证域。旧三个全局包装声明却要求 `∀ q, IsLipMatrix ... (Lq q)`；修复按单分量 `j∈I_res(q)`、联合分量 `J⊆I_res(q)` 条件化要求。

**反例不是“任意选坏一个 Lq”**：取五点 `{bot,a,b,c,d}`，一个伪度量分量，其中 b、c 为不同但零距离的点，a、d 及该零距离类彼此距离 1，bot 到其余点距离无穷。输入为 `{a,b,c}`。代理有两条长度 1 路径：q0 的域 `{a}`、输出 a；q1 的域 `{b,c}`，分别输出 a、d。仅采样 a，目标在整个输入域恒为 a，所以目标全域 Lip 系数 0 合法。q0 可评估且有 Lip 系数 0，q1 不可评估。q1 却根本没有任何 ENNReal Lip 系数，因为输入距 0、输出距 1，而包括无穷在内的任何系数都有 `L*0=0`。因此旧全部路径前提无法补齐，而正文的可评估路径保证完全成立。

**评审边界**：旧全局定理在其较强假设下正确；局部上界引理也正确，可以自行组合修复。应报告所给全局接口的范围损失，不能谎称正文数学错误或整份源码毫无覆盖。若接受自行派生为覆盖证据，必须仍明确当前导出包装多出的前提。这一点应在评审合同中提前冻结。

旧 43 模块依赖闭包原样编译全 exit 0，证据和字节位于 `path-guarantee/`。有限伪度量、采样与无系数见同一检查脚本及机器结果。建议题面见 `path-guarantee/candidate-prompt.md`。



许可与来源完整身份另见provenance.json。有限反例为数学模型检查，非Lean记录实例化证明；原样编译不等于语义完整。
