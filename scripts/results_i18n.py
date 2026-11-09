"""Interface translations only; retained mathematical evidence is never translated."""
import json


def language_switch():
    return ('<div class="language-switch" role="group" aria-label="Language / 语言">'
            '<button data-language="zh" aria-pressed="true" lang="zh-CN">中文</button>'
            '<button data-language="en" aria-pressed="false" lang="en">EN</button></div>')


MESSAGES = {
    '主导航': 'Main navigation', '排行榜': 'Leaderboard', '模型排行榜': 'Model leaderboard',
    '分类榜': 'Categories', '能力分项': 'Contributions', '方法与数据': 'Method & data', '题集': 'Tasks',
    '封版': 'Sealed suite', 'AI 审核 · 人审待定': 'AI reviewed · Human review pending',
    '观察后选题与复核，正式比较资格未确立': 'Post-observation selection and review; formal comparison eligibility not established',
    '书面证明、Lean 与数学研究。考察数学论证、形式化交付，以及发现和修复问题的能力。':
        'Written proofs, Lean and mathematical research. Testing mathematical arguments, formal delivery, and the ability to find and repair errors.',
    '当前评测范围': 'Evaluation scope', '公25题 · 私14题': '25 public · 14 private tasks',
    '数学家族': 'Mathematical families', '权重覆盖': 'Scoring capacity', '3轮': '3 rounds',
    'Lean 对齐自查 · 独立计分': 'Lean self-check · separately scored',
    '公开＋私有 · 可靠数学能力 / 100': 'Public + private · Reliable Mathematical Capability / 100',
    '总榜口径': 'Overall score', '计分口径': 'Score mode', '其他图可独立排序': 'Other charts sort independently',
    '仅显示已测完模型': 'Completed models only',
    '筛选只影响显示；已测完不代表全部答对。': 'Display filter only; a completed evaluation does not mean every answer is correct.',
    '当前筛选下没有已测完的模型。': 'No completed evaluations match this filter.',
    '分数为已确认贡献；': 'Scores show confirmed contributions; ', '表示尚无成绩。': ' means no score is available.',
    'MC／RMC／SMC · 规则成绩': 'MC / RMC / SMC · rule-selected results',
    '采用规则允许的最终成绩，满分100。': 'Rule-selected final results, out of 100.',
    '数学能力': 'Mathematical Capability', '可靠数学能力': 'Reliable Mathematical Capability',
    '按有效正向贡献计分，取消显式扣罚。': 'Credits valid positive contributions without explicit deductions.',
    '按有效数学贡献计分，扣除有据的错误承诺；核心错误放行该题最高0分。默认主分。':
        'Credits valid mathematics and deducts evidence-based false claims; critical core false endorsements cap a task at 0. Default primary score.',
    '整题或规定三轮轨迹满足全部实质要求才给分。': 'Credits only tasks or prescribed three-round trajectories that satisfy every substantive requirement.',
    '严格数学交付': 'Strict Mathematical Completion',
    '可靠数学能力按实际完成度计分，并保留错误、回退和误报扣罚。':
        'Reliable capability credits completed work while retaining penalties for errors, regressions and false completion claims.',
    '模型': 'Model', 'RMC · 主分': 'RMC · primary', '评测详情': 'Details', '详细评测 →': 'Full evaluation →',
    '尚未测完': 'Evaluation unfinished', '* 尚未测完': '* Evaluation unfinished',
    '共同条件：允许本地工具及预置公共依赖，禁止联网检索与工具联网。各Harness版本及实际使用情况见模型详情。':
        'Common conditions: local tools and preinstalled public dependencies allowed; external retrieval and tool networking prohibited. See model details for scoped harness versions and actual usage.',
    '重跑与来源备注': 'Retries & provenance',
    '按规则采用首次正常交付；原答、失败及全部尝试记录保留。':
        'The first normal delivery is selected under the retry rule; original answers, failures and all attempts are retained.',
    '查看方法与来源 →': 'Method & provenance →', '分数落差': 'Score gaps',
    '以MC为共同基准 · 规则成绩': 'Common baseline: MC · rule-selected results',
    '可靠差RG与交付差DG共用正负轴，可分别按接近0的程度排序。':
        'Reliability Gap (RG) and Delivery Gap (DG) share a signed axis and can each be sorted by distance from zero.',
    '0表示无落差；结合上方能力分阅读。': 'Zero means no gap; read it alongside the capability scores above.',
    'RG＝RMC−MC · DG＝SMC−MC · 百分点': 'RG = RMC − MC · DG = SMC − MC · percentage points',
    'RG · 可靠差': 'RG · Reliability Gap', 'DG · 交付差': 'DG · Delivery Gap',
    'RG 接近0优先': 'RG closest to 0', 'DG 接近0优先': 'DG closest to 0',
    '排序': 'Sort', '内容可靠率与目标达成率': 'Content reliability & goal attainment',
    '内容核查实际断言；目标按完整独立成果验收。不改变MC、RMC、SMC。AI审核／人审待定。':
        'Assertions are checked for reliability; goals require complete, independently usable results. MC, RMC and SMC are unchanged. AI reviewed; human review pending.',
    '已审内容可靠率': 'Observed content reliability', '已确认目标达成率': 'Confirmed goal attainment',
    '计算方法 →': 'Calculation method →', '可靠': 'Rel.', '达成': 'Goal',
    '分类排行榜': 'Category leaderboards', '三个大类独立排序': 'Each category sorts independently',
    '各分类独立选择排序口径。分数沿用固定题池，完整值与未知区间见模型详情。':
        'Choose a sort mode within each category. Scores use the fixed task pool; model pages retain full values and unresolved intervals.',
    '书面证明': 'Written proofs', 'Lean排行榜': 'Lean leaderboard',
    '书面证明排行榜': 'Written proofs leaderboard', '数学研究排行榜': 'Mathematical research leaderboard',
    '数学研究': 'Mathematical research', 'MC 高→低': 'MC high → low', 'RMC 高→低': 'RMC high → low',
    'SMC 高→低': 'SMC high → low', '类内百分制': 'Within-category / 100',
    '类内满分100 · 总榜权重35%': 'Category / 100 · overall weight 35%',
    '类内满分100 · 总榜权重30%': 'Category / 100 · overall weight 30%',
    '分榜显示类内百分制成绩；总分贡献见下表。未测部分不折算为已测部分的满分。':
        'Category scores are out of 100; their overall contributions appear below. Unrun tasks are never rescaled away.',
    '大类贡献': 'Category contributions',
    '模型按行 · 点击大类表头展开子类 · 每格为贡献分 / 该项满分':
        'One model per row · expand a category header for subcategories · cells show earned / available points',
    '保留大类合计，子类在其右侧展开。公私合并，书面论证12个家族等权；逐题评审与自查轨迹见模型详情。':
        'Category totals stay visible, with subcategories to their right. Public and private results are combined; 12 written-argument families have equal weight. Model details contain task reviews and self-check trajectories.',
    '总分结构 · 书面证明35% · Lean35% · 数学研究30%':
        'Score structure · written proofs 35% · Lean 35% · research 30%',
    '同一份答卷，三个计分口径。分类贡献与下载跟随当前选择；自查、三轮轨迹和扣罚依据在模型详情展开。':
        'Three score modes use the same answers. Contributions and downloads follow the overall mode; model details contain self-check rounds and penalty evidence.',
    '当前成绩下载': 'Download current results',
    '公开＋私有合并，采用规则允许的最终成绩，随计分口径切换。':
        'Combined public and private rule-selected results. Downloads follow the selected score mode.',
    '查看完整方法与数据说明 →': 'Full method & data →',
    'Math Gauge · AI 审核 / 人审待定': 'Math Gauge · AI reviewed / human review pending',
    'Math Gauge · 原答与原评审保留': 'Math Gauge · Original answers and reviews retained',
    '¹ Dot原生独立运行方式': '¹ Dot’s independent native harness',
    '² 使用DeepSeek Harness（DSH）时，多道题因推理过程过长、耗尽最大输出预算而未能交卷，因此改用Codex CLI执行。':
        '² Several tasks exhausted the output budget during lengthy reasoning in DeepSeek Harness (DSH), so execution moved to Codex CLI.',
    '当前留档没有另计的非逻辑重跑。': 'No separately counted nonlogical retries in the retained records.',
    '模型详细评测 · 公开＋私有合并成绩': 'Model evaluation · combined public and private results',
    '当前成绩': 'Current results', '分类贡献': 'Category contributions', '书面论证': 'Written arguments',
    '论证审阅': 'Answer review', '语义审计': 'Semantic audit', '形式化': 'Formalization',
    '对齐自查': 'Alignment self-check', '背景核查': 'Background checks', '命题拓展': 'Theorem extension',
    '数学想法手稿化': 'Manuscript completion', '每格为贡献分 / 该项满分。书面论证12个家族等权；相关变体在家族内聚合。':
        'Cells show earned / available points. The 12 written-argument families have equal weight; related variants aggregate within their family.',
    'Lean · 自查计分': 'Lean · self-check scoring', '比较三种计分口径': 'Compare the three score modes',
    '整章对齐 · 固定三轮': 'Chapter alignment · three fixed rounds',
    '原答事实，不随口径改变。92项义务，采用最后规定轮次；不取最好一轮，不拼接各轮成果。':
        'Original observations stay unchanged across score modes. There are 92 obligations; the last prescribed round is used, with no best-of selection or union of rounds.',
    '展开三轮原答与审核': 'Expand original answers and reviews for all three rounds',
    '形式化初答 · 逐题核实数': 'Initial formalization · verified obligations by task',
    '编译与逐项语义审核同时成立才计完成。初答与后续自查分开计分。':
        'Completion requires both compilation and item-level semantic review. Initial delivery and subsequent self-check are scored separately.',
    '公开题 · 逐题成绩与证据': 'Public tasks · scores & evidence',
    '当前25道公开题。私有14题只进入上方合并贡献，不提供题号、原答或逐题评审。单题比例不可直接相加为总分。':
        'The 25 current public tasks are listed below. The 14 private tasks contribute only to combined totals; their identifiers, answers and task reviews stay private. Task percentages cannot be summed directly into an overall score.',
    '可靠性审核': 'Reliability review', '公开题的错误承诺与扣罚理由': 'False claims & penalty evidence for public tasks',
    '记录数不等于独立样本或扣罚次数；同根因去重。RMC 普通扣罚5%/10%/20%，通常每题最多20%，数学想法手稿化最多50%；已确立的核心错误放行使该题最高0分，SMC 不通过。':
        'Finding counts are not independent samples or penalty counts; shared root causes are deduplicated. Ordinary RMC penalties are 5% / 10% / 20%, capped at 20% per task (50% for manuscript completion). Established critical core false endorsements cap that task at 0 and fail SMC.',
    'Harness与工具': 'Harness & tools', '运行条件、重跑与来源': 'Conditions, retries & provenance',
    '计分方法与证据边界': 'Scoring method & evidence boundaries', '本题成绩': 'Task score',
    'MC/RMC 显示单题计分比例 /100，权重贡献在模型页汇总；SMC 显示整题判定。未测与交付失败分别保留。':
        'MC / RMC show task credit out of 100; weighted contributions appear on the model page. SMC shows the whole-task decision. Unrun tasks and failed deliveries remain distinct.',
    '题目与要求': 'Task & requirements', '判定与主要理由': 'Decision & main reasons', '逐项评审': 'Criterion review',
    '以下为原评审字段的阅读视图；当前口径的额外扣罚与 SMC 判定以本页成绩及上方理由为准。':
        'This is a reading view of the original review fields. Current-mode adjustments and SMC decisions are shown in the task score and reasons above.',
    '完整原答 · 含原自评与不确定性表述': 'Complete original answer · including self-assessment and uncertainty',
    '来源、原评审与运行附件': 'Sources, original reviews & execution attachments',
    '原题文件 ↗': 'Original task ↗', '原答文件 ↗': 'Original answer ↗',
    '补审汇总 JSON ↗': 'Supplemental review JSON ↗', '完整三轮审核与诊断依据 ↗': 'Full three-round review & diagnosis evidence ↗',
    '已获分 /100': 'earned / 100', '完整分区间': 'Full-score interval', '已评任务': 'Adjudicated tasks',
    '大类 / 子类': 'Category / subcategory', '权重': 'Weight', '当前贡献': 'Current contribution',
    '当前口径': 'Current mode', '成绩': 'Score', '整段判定': 'trajectory decision', '自查 /100': 'self-check / 100',
    '计入总分 /10': 'Overall contribution / 10', '未知': 'Unknown', '未通过': 'Fail', '通过': 'Pass',
    '固定三轮平均，只计已核实的正向修复与诊断。': 'Average over three fixed rounds; only verified positive repairs and diagnoses earn credit.',
    '固定三轮平均，保留回退和误报扣罚。': 'Average over three fixed rounds, retaining regression and false-completion penalties.',
    '整段三轮轨迹达标才计10分；未达标为0分，未决保留未知。': 'All three rounds must satisfy the trajectory rule for 10 points; failure earns 0, unresolved evidence remains unknown.',
    '核实全部完成': 'Verified complete', '未完整 · 数量稳定': 'Incomplete · count stable',
    '未完整 · 有进展': 'Incomplete · progress', '未完整 · 有回退': 'Incomplete · regression',
    '轮次未完成': 'Rounds missing', '未运行': 'Not run', '审核未决': 'Review unresolved',
    '轮次 / 状态': 'Round / status', '原答事实': 'Original observations', '完成义务': 'completed obligations',
    '误报全部完成': 'False-complete claims', '最后状态': 'Final state', '任务': 'Task', '核实完成': 'Verified complete',
    '交付失败（交付计0）': 'Delivery failed (0 credit)', '公开题': 'Public task', '题型': 'Type', '判定': 'decision',
    '单题比例': 'task credit', '局部 / 实质 / 重大记录': 'Local / material / critical findings',
    'RMC 整题最高0分': 'Tasks capped at RMC 0', '查看证据': 'View evidence',
    '三个口径，共用同一份答卷': 'Three score modes, the same answers', '固定100分，保留未知': 'Fixed 100-point frame; unknowns retained',
    '工具、运行条件与证据边界': 'Tools, conditions & evidence boundaries', '来源与版本': 'Sources & versions',
    '从想法到数学稿': 'From mathematical ideas to manuscripts', '分数落差：RG与DG': 'Score gaps: RG and DG',
    '三个计分口径、固定分母与公开证据的阅读方式': 'Three score modes, fixed denominators and a guide to public evidence',
    '原题与原答保留原始语言。': 'Original tasks, answers and review evidence remain in their original language.',
    '返回当前口径的排行榜 →': 'Return to the leaderboard in the current mode →',
    '公开题证据': 'public-task evidence',
    '公开＋私有 · 按': 'Public + private · sorted by ', '排序 · 满分100': ' · out of 100',
    '规则允许的最终成绩': 'rule-selected final result', '公开与私有合并，满分保持100；未测项目保持未知。':
        'Public and private results combined, out of 100; unrun tasks remain unknown.',
    '完整贡献区间': 'Full contribution interval', '的子类成绩': ' subcategory scores',
    '展开': 'Expand ', '收起': 'Collapse ',
    '内容可靠率看实际内容是否正确且有论证支持；目标达成率看完整数学成果是否按题意交付。':
        'Content reliability checks actual assertions and their justification; goal attainment checks complete mathematical results against the requested goals.',
    '按独立成果验收；SMC要求整题及规定轨迹全部达标。':
        'Goals are independently usable complete results; SMC requires the whole task and prescribed trajectory.',
    '内容可靠率 高→低': 'Reliability high → low', '目标达成率 高→低': 'Attainment high → low',
    '内容可靠率': 'Content reliability', '目标达成率': 'Goal attainment', '百分比 · 0–100': 'Percentage · 0–100',
    '两率图排序': 'Rate chart sort',
    '各模型MC、RMC、SMC规则成绩，统一0至100分': 'MC, RMC and SMC by model, on a shared 0–100 scale',
    '各模型可靠差与交付差，共用正负轴': 'Reliability and delivery gaps by model, on a shared signed axis',
    '各模型内容可靠率与目标达成率，统一0至100百分比': 'Content reliability and goal attainment by model, on a shared 0–100 percent scale',
    '分类成绩图': ' category scores', '详细评测': 'full evaluation',
    '0.6.1 分发说明': 'Distribution 0.6.1', '其他 Harness 运行指南': 'External harness guide',
}


def javascript_catalog():
    return json.dumps(MESSAGES, ensure_ascii=False).replace('<', '\\u003c').replace('&', '\\u0026')
