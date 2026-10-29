# 严格工程复核证据

[修复审查](repair/engineering-repair.md)记录两个证据绑定缺口及其修复；[当前源码绑定](current-evidence.json)逐项核对执行器、审核器、对应测试及材料验证器身份。候选模型请求为0，本地synthetic适配器进程不计模型请求。

- [材料链重验](material-validation.md)：归档、editorial清理和唯一strict修订分层核对；7项新回归通过，最终43投影/372义务及300导航链接检查通过。
- [原始审查](pre-repair/engineering-review.md)：修复前一次完整离线检查及两项缺口；当时源码身份保留，不冒充当前实现。
- [最终定向测试](repair/compatibility/focused.stderr.log)：61项，60通过、1可选Lean检查跳过。
- [历史兼容](repair/historical-run-compatibility-after.json)：89个归档新拒绝0；四包28题标为historical/unverifiable，不具当前比较资格。
- [真实隔离合成Lean工程](repair/isolated-group-run/)：仅1个工程、3个模块；原答卷、合同、源码、alignment、收据、日志和olean按原字节保留。原记录中的绝对路径是运行时来源；保存后的相对位置见[工件清单](repair/isolated-group-artifacts.json)。[当前审核器复验](repair/isolated-group-final-review.json)复用未变的真实编译引擎产物，通过5/5阶段。
- [旧runner源码归档](history/runner-source-9e536ad.tar.gz)仅用于核对旧targeted-runner-checks的历史散列，不导入、不执行，也不宣称与当前实现相同。
- [旧packet计划](history/reliability-packet-0.1.0/plan.json)和[旧选择](history/reliability-packet-0.1.0/selection.json)保持packet-review-c原审核输入；当前计划身份变化见[严格重验回执](../../../protocol/reliability-20261030/reviews/strict-revalidation-20261030.json)。

修复过程中的全套失败日志保留在repair/compatibility/，当时focus目录仍在整合，不能称为最终全套通过。最后完整测试由根报告独立绑定；本材料验证器不读取最终测试日志，避免自证循环。作者Lean、数学审核、AI审核和人工批准分别记录；这一次合成编译不提供新增作者题组或整章Lean完整覆盖。
