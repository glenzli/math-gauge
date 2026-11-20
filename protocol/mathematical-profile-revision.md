# 数学画像：含中性续答

本组件0.1.0用于评分版1.2.0。它在保留[首答画像0.4.0](mathematical-profile.md)的基础上，增加“首答／含续答”两个阶段，不增加第八轴，不改变三项主分、题目、候选调用、两率或费用。方法在观察既有答卷后由用户选定；画像复评为AI审核，人工数学审核仍待完成。

## 阶段与范围

首答阶段读取原0.4.0画像，原政策、逐题裁定、答卷及公私投影保持原字节。含续答阶段只使用[中性续答采用层](neutral-revision.md)已经选定的真实交付，严格绑定同一模型、条件、原父答和当前来源。不能使用未采用尝试、更大工作区或评审者补写的数学。

| 轴 | 含续答阶段 |
|---|---|
| 论证能力、问题忠实度、数学审辨力、数学深度、成果闭合度 | 对每道实际选中的续答按原0.4.0标准分别复评，再以该题首答等级的4/5与续答等级的1/5合成。未入选题、Lean初答及固定三轮自查沿用。 |
| 主动研究性 | 全部沿用首答，收到统一完善或研究邀请后的推进不计作自发研究。 |
| 严格完成度 | 直接读取1.2.0正式SMC及其完整区间，不由画像等级或家族均分重算。 |

五个复评轴继续使用原35个数学家族及原变体权重；C003初答与三轮的嵌套权重不变。先合成逐题等级，再按原家族权重汇总并换算至0–100。退步如实进入1/5，不取最佳、不拼接两份答卷形成新证明。这里的“含续答”表示完整评测流程的折算画像，不表示模型经历了统一的第二次全卷考试。

首答三项主分全满而免测的题，画像也沿用原裁定，不将其原画像等级提升为满档。尚未执行续答或缺少画像审核的题保留未知区间；不继承首答值充作已完成续答评审。不同模型各自的失分集合不同，旁列的续答满分率只说明其自身集合的完善情况。

## 独立数学裁定

每个续答等级为0至4或有明确原因的未知，附具体数学理由与可核对的原文证据。完整读取原题、提供材料、新原答、明确交付附件及已采用的数学审核；旧画像只用来保持标准及首答绑定。不能从MC、RMC、SMC、B/R等级、篇幅或成果组数机械推导画像等级。

论证轴仍检查原题核心：全部必需分支、依赖及表示桥。4档必须核心成立；核心被反驳或存在不可省的新数学缺口时最多2档。TX基线已经严格证明时，单纯未取得额外R3不降低其原题核心论证档。可分离的题外错误与必要核心失败分别判断。

忠实度仍检查原对象、条件、量词、定义域和目标；核心漂移且无实际交付返回桥时最多2档。合法替代路线、反例和诚实未完成按原标准判断，不因与参考组织方式不同而扣档。

审辨力核查新答卷的实际判断与自评，正确改写本身不证明已准确发现旧错误。深度只计已成立的数学机制；闭合度核查实际交出的实质成果的证明、依赖、范围和必要桥梁。统一研究邀请可以产生深度与闭合方面的新证据，但不增加主动研究性。

## 记录与展示

新记录独立绑定原0.4.0画像、精确采用输入、新答及附件、已采用数学审核和五轴逐题复评。公有文件只含合并数值、覆盖、阶段及不透明散列；私有题号、原答、逐题理由、引文和执行源路径留在私库。AI审核、实际形式验证和人工批准继续分开。

网页保留七轴，提供“首答／含续答”切换，阶段选择独立于主榜SMC／RMC／MC。未完成续答画像的配置只能查看已有首答，不伪造第二阶段数值。主动额外成果仍是独立的首答观察。续答题数、满分率及分数变化可在画像旁引用现有来源，不增加新的主分或同等条件排名。

## English

Component0.1.0 adds first-answer and revision-inclusive views for assessment1.2.0 while preserving the complete0.4.0 baseline. Five axes—reasoning, fidelity, discernment, depth and closure—receive independent source-bound reviews of the adopted revisions and use4/5 original plus1/5 revision per task. Original family, variant and Lean-trajectory weights remain fixed; decreases count. Research initiative stays first-answer-only. Strict completion reads the official1.2.0 SMC directly.

Unselected tasks retain their original judgments, without upgrading exempt tasks to full profile grades. Missing revision judgments stay unknown. Reviewers retain the original core and fidelity gates and cite actual delivered mathematics; main scores or B/R levels cannot substitute for axis judgments. Invited research may establish depth and closure but does not establish unsolicited initiative. No new candidate calls or main-score changes occur. The method is post-observation, AI-reviewed and pending human mathematical approval.
