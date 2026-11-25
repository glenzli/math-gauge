# 独立保留评分基底与当前版本

1.3.0 的独立开放研究评审采用时，绑定的是一份含 17 个配置的 1.2.0 原始数据。后来 1.2.0 新增已结算的 Carbon Medium，当前 1.2.0 含 18 个配置。原 17 个模型的完整数据对象均须保持相同；新增配置和顶层版本元数据可以变化。这不自动给新配置建立 1.3.0 研究成绩。

这是两份不同用途的数据：

| 路径 | 用途 |
|---|---|
| `site/data.json` | 原独立研究采用层绑定的 17 配置基底；保留原字节 |
| `site/versions/1.2.0/data.json` | 当前 1.2.0 的完整数据，可包含后来结算的配置 |
| `site/data/editions/1.2.0/` | 当前 1.2.0 总榜、详情与题目页面的数据 |
| `site/versions/1.3.0/` | 从原选定基底及已采用研究评审生成的 1.3.0 数据和下载 |

版本目录为 1.2.0 指向其当前版本路径；首页仍可默认打开 1.3.0。原题、原答、原评审、实际执行版本和历史发行包不因路径分工而改变。

## 显式选择与失败条件

[基底选择组件 0.1.0](../protocol/mathematical-taste/v1.3.0/baseline-selection.json)记录这次展示来源选择。它绑定原基底的路径、字节数和 SHA-256，以及原独立研究采用索引的路径、字节数和 SHA-256。它不补造旧执行收据，不修改数学判断，也不调用候选模型。

存在该组件时，生成器先读取被明确选择的原始文件，再运行既有采用、外部、原生、品味和严格信用校验。原始文件缺失、字节或散列不符、路径越界、符号链接、采用索引被替换，均直接失败。当前 1.2.0 若删除或修改任何原模型的完整对象，也会失败；此组件不允许继续套用失配的旧父答。

没有该组件时，原流程仍要求生成中的 1.2.0 数据与研究评审绑定完全相同。散列失配不会触发搜索旧文件或自动回退。需要变更采用基底时，须另作明确的来源绑定采用，不能仅刷新旧散列。

## 展示、时间与成本

1.3.0 的分数、分类、画像、模型集合和共有计时样本均从同一份选定基底取得。当前 1.2.0 的页面和下载继续使用当前数据。共享图标只沿已核实的相同图标身份转换为网页资源路径，不替换模型成果或评审。

1.3.0 先按其原配置范围生成 1.2.0 时间和成本参考，再全额加入已采用独立研究的有效成本。它不直接筛掉新配置后沿用较大集合已经算出的共有样本，也不再次加入已经合并过的研究成本。对应的时间和成本 JSON 单独放在 `site/versions/1.3.0/downloads/`。时间参考仍不包含独立研究三轮；分数、资源范围和模型交付状态分别说明。

`scripts/results_research_baseline.py` 负责展示来源选择、原模型一致性和选定范围的首页及资源准备；`scripts/results_research_preview.py` 继续组合经既有校验的结果。评分、数学判断及执行仍由原有组件负责。完整生成在全部来源校验成功后才写输出；同样的来源选择也适用于本地增量生成。

## English

The adopted 1.3.0 independent-research reviews bind an exact 17-configuration 1.2.0 baseline. The current 1.2.0 edition later adds settled Carbon Medium results. Every retained model object must remain exactly equal; this compatibility choice admits an additional base-edition configuration without creating its independent-research result.

The original bytes remain at `site/data.json`. Current 1.2.0 full data is published at `site/versions/1.2.0/data.json`, alongside its current page payloads and downloads. The edition catalog points to that current versioned file. The separate 1.3.0 outputs retain their original adopted baseline, grades, policies and source identities.

The explicit selection component binds both the original baseline and settled index by path, byte count and SHA-256. Missing or damaged sources, substituted indexes, unsafe paths, symlinks, removed retained models and any modification to a retained model object fail validation. All existing mathematical and source validators remain strict. Without the component, the original exact-baseline requirement still applies; there is no search or fallback after a mismatch.

Scores, categories, profiles, cohort and timing sample all use the selected baseline. Timing and base costs are rebuilt for that same cohort by their existing owners; adopted independent-research cost is added once in full. The separate 1.3.0 timing reference continues to exclude independent research. Its timing and cost downloads have version-specific paths. This is a publication-source choice, not a new execution receipt, mathematical reassessment or candidate call.

## Carbon medium 的独立新增来源

原17配置的采用层和父数据保持原字节。Carbon medium 另通过 `baseline-additions.json` 绑定当前18配置的完整1.2父快照、独立截止稿采用索引、旧题品味补充及资源投影。生成器逐一核实原17个模型和画像对象仍完全相同，再将新增配置加入展示。新研究三稿及评分独立绑定，不从旧基底继承新题成绩。

The Carbon medium addition binds its own immutable 18-configuration 1.2 parent, admitted-delivery index, legacy-taste supplement and resources. The original 17-model adoption and parent bytes stay unchanged. The generator verifies retained model/profile equality before joining the additional configuration; no research score is inherited from a baseline.
