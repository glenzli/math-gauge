# Math Gauge v0.1.0

首次发布可独立下载、冻结模型配置并交给任意外部 harness 的软件与数据交付物。发布版本 **v0.1.0** 与当前题集版本 **0.2.0** 分别记录；不需要 Codex、clone 仓库或安装 Math Gauge。

下载 **math-gauge-tasks-v0.1.0.zip** 与 **SHA256SUMS**，先验证校验和，再按压缩包内 README 操作。命名 ZIP 只包含候选白名单、脱敏控制材料、独立 Python 控制器及必要分发说明。GitHub 自动附带的 **Source code (zip/tar.gz)** 包含完整源码和公开参考答案，不是候选交付物。

控制器可检查不可变数据集，使用所选模型、预算与执行范围创建新的运行目录，构造完整初答及独立自查分支请求，并生成绑定原始答卷的提交模板。准备、校验、冻结与导入命令本身不调用模型。外部答卷回到同一套来源、数学、Lean、审核和固定分母评分流程；未来私有数据集复用这一实现。

本次保持43份公开开发试卷、177槽/模型的完整计划和现有题目条件。全部试卷仍为 **draft / human pending**。作者 Lean、AI复核、离线工程验收和数学人工批准分别记录；本次发布没有候选模型答卷、通过率或正式能力排名。

参考答案及 Git 历史继续公开以便透明复核，当前数据不是未公开保留集。哈希只绑定材料与配置；runtime、运行UUID、日期或来源声明不认证后端、实际执行时间或隔离。通用外部导入继续标记为 `external_import`，按现有来源合同保留暂定状态，不因导入而取得 `formal_score`。

[下载运行指南](https://github.com/glenzli/math-gauge/blob/v0.1.0/protocol/release-distribution.md) · [评测协议](https://github.com/glenzli/math-gauge/blob/v0.1.0/protocol/evaluation.md) · [验证状态](https://github.com/glenzli/math-gauge/blob/v0.1.0/docs/verification.md)
