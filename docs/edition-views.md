# 评价版本与共用界面

首页默认读取最新评价版。页头以 **1.2.0**、**1.1.0**、**1.0.0** 等版本号提供切换，并在同一套界面中查看该版的总榜、分类、模型详情、公开题评审和成绩下载。分享链接中的 `edition` 会固定所选版本；不带版本的首页始终打开最新一版。网页默认按SMC排序，分数依次为SMC／RMC／MC；链接中明确选择的其他口径仍保留。

例如，本地页面的 `index.html?edition=1.0.0&lang=zh` 显示1.0.0成绩。切换版本会保留当前阅读位置，进入模型、题目或方法页时，版本、语言、计分方式和各图表的选择一并保留。

## 各版本包含什么

1.0.0 提供完整的总榜、分类、模型详情、公开题评审和下载，直接读取该版已采用的成绩及来源更正。原0.6.0／1.0.0的实际答题身份继续随答卷保留。

1.1.0 使用该版的评分结果与评审。总榜、模型分项、TX单题评分、图形几何、成本成绩图和下载读取同一选版数据。评分调整的范围及依据见[1.1.0评分说明](theorem-extension-reassessment.md)。

1.2.0加入一次非Lean失分题中性续答，逐题80%首答＋20%续答。当前本地排行含16个已结算配置，其他配置保留待回交状态及原版成绩入口。续答题数、满分率、分数变化和合并资源读取同一来源绑定记录；内容两率与额外成果观察仍是首答诊断；数学画像独立切换首答／含续答阶段。GLM 5.3、Gemini 3.8 Flash与Gemini 4 Argon不在1.2.0模型集合或待测名单中；其1.1.0及更早的排行／部分测试展示、原答与评审保留。无显式edition的历史详情链接默认打开仍可用的1.1.0，不删除历史模型或题目目录。详见[续答说明](neutral-revision.md)。

切换只改变所查看的版本；模型选择、语言、计分方式和图表排序仍按当前链接保留。发布题包、实际答题版本和评分版本分别记录。

当前1.2.0数学画像为八轴，独立加入[开放研究能力](open-research.md)，“研究主动性”放在最后并保持首答行为含义。1.1.0沿用原七轴，1.0.0不增加画像；首答／含续答的选择独立于总榜计分方式。

## 数据与界面如何分开

- `site/editions.json` 列出可用评价版本及来源。
- `site/data/editions/<版本>/` 保存各页面需要的公开结构化数据；历史整表和成绩下载在 `site/versions/<版本>/`。
- 总榜、模型页和题目页共用显示程序，不为每个版本复制一整套HTML。
- 原题、原答和评审的数学排版内容按内容散列共享，展开时加载。原始文件的链接继续保留。

浏览器使用由同一数据生成的登记文件，因此本机直接打开文件也可切换版本。若所选数据不完整，页面明确显示加载失败，不拿另一版的数字填充。公开数据只含公开题及匿名合并结果；私有题、原答、逐题评审和具体标准继续留在私库。

## English

The homepage defaults to the latest assessment edition, with SMC selected unless the link specifies another score. Controls are ordered SMC / RMC / MC. The selector shows bare version numbers such as1.2.0,1.1.0 and1.0.0. Switching editions preserves the reading position; versioned links retain language, score modes and board choices. The leaderboard, category charts, model details, public task judgments, score–cost plots and downloads all use the selected data.

Edition 1.0.0 provides the complete rankings, categories, model pages, public task reviews and downloads using its adopted scores and source corrections. Edition 1.1.0 uses its own scores and reviews; the [1.1.0 scoring notes](theorem-extension-reassessment.md) explain the changes. Published distributions, execution versions and scoring editions are recorded separately.

Edition1.2.0 blends each selected non-Lean loss task as80% first answer and20% one neutral revision. The local ranking includes16 settled configurations; pending configurations retain links to their earlier scores. Revision counts, full-score rates, deltas and combined resource totals share source-bound evidence. Content rates and surplus observations remain first-answer diagnostics; profiles have separate first-answer and revision-inclusive stages. GLM 5.3, Gemini 3.8 Flash and Gemini 4 Argon are withdrawn from the1.2.0 model cohort and pending list by user selection. Their1.1.0 and earlier rankings or partial-test displays, original answers and reviews are retained. Historical detail links without an explicit edition open the available1.1.0 data; model and case directories are not deleted.

Structured public page data is versioned separately from shared UI code. Mathematical prose is content-addressed and loaded as needed; historical editions do not duplicate full HTML sites. Direct local-file viewing uses safe data registration. Missing or mismatched data produces an explicit error instead of substituting another edition. Private task evidence remains private.

The current 1.2.0 profile has eight axes, separately adding [open research capability](open-research.md) and showing first-answer research initiative last. Edition 1.1.0 retains seven axes; 1.0.0 has no profile. Profile stage is independent of the leaderboard score mode.
