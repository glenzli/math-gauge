# 书面重复与三臂自查执行协议 · 本地0.6.0 / 协议0.4.0

本地草稿、human pending，未发布。范围以[机器profile](benchmark-profile.json)及[冻结消息与顺序](reliability/README.md)为准。当前四written面板为GR002/GR014/GP001/GP002，A1/A2独立，neutral/affirm/deny各从同一A1展开一次。Lean、AR和探索只取能力A1；92项Lean对齐专项另列。

独立初答必须使用全新上下文，题面、附件、实际system、参数、track与预算均冻结，不得读其他答卷、参考、评分或旧通过率。三分支只重放本模型同一A1与自己的请求，不得读A2、另一个分支或其他模型。各轮保存完整候选请求、原答、文件、工具轨迹及各项hash；本地编译是允许工具反馈，评审编译与参考反馈不得回送。

新8Lean A1执行local-tools-no-search，C003预算10800秒，其余七项5400秒；各层实际预算分别留证；普通written和AR保留各源真实条件，不能拿outer上限推断native/broker预算。同case及其重复/各臂条件必须一致；跨case的明确来源分层仅供观察后开发组合，formal comparison eligibility为false。不能用未知track或search伪装相容。

每次transport保留实际状态、用量和原始字节。第一份readable raw继续锁定为原答，禁止按数学质量重试；但v5仅在原生和transport成功终态后派生后续。ERROR等待语、partial及中断保留原文和状态，后续阻断，数学审核为unresolved/no-delivery。服务故障重试只能按冻结retry策略新增attempt，不能覆盖旧attempt。原生适配还须独立delivery-gate，不能把非空文本当作已交卷。

GP001/GP002各完整5槽fresh，在新调用前冻结同case的A1/A2和三臂条件；不接旧A1、不引入跨plan父重绑。两模型标准新提交各18（8Lean A1加10written）。旧GR002/GR014整包五槽按精确来源复用，旧GP001/GP002答卷不填当前fresh槽，历史题与旧结果通过Git恢复。

KEEP/FULL按[原格式](reliability/reply-format.md)处理。KEEP继承自身本分支完整主体并保留当前理由独立审核；FULL重新完整交付，不得把A2或别的分支当主体。不因自称通过、认错、语气或答案长短改变调度。

所有导出、检查、导入和计划准备均不调用候选模型。实际调用须另冻模型/runtime/隔离证据并由操作者放行；用共享runner，不在私有数据中复制实现。旧结果与历史预算保持原身份，不把复用说成同步新考。
