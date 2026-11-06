# 当前结果页

静态index.html／data.json由scripts/render_results_site.py生成，直接读取固定档案四种合并结果；评分逻辑在共享runner，页面不另计分。离线可打开index.html，亦可用本地静态服务器预览。

三大类书面35／Lean35／研究30，八子类列出公私数量和贡献。研究三项0题建设中，当前主值为已获分／100、可测上限70，完整总分未定。分项／Strict及首次／允许非逻辑重跑可切换，Lean三轮自查独立10分。柱图每家独立主题色与本地图标，实心首次、条纹仅显示重跑实际增量，数值取较高者，只有有差异的模型展示悬停说明。

生成：python3 scripts/render_results_site.py；生成一致性由test_results_site.py核对。downloads仅含三家×两模式×两条件的12个合并投影，不含独立公有总分或私有逐题资料。图标来源与许可见assets/providers。当前benchmark0.6.0／聚合0.5.0／Strict0.2.0，人审待定，尚未发布。
