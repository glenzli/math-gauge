# 全习题集双模型比较

两模型均已完成全部 41 题的单次运行与审核。

这是 AI 数学审核的暂定结果，供人工验收；题目和答卷均未标记为人工批准。纯文字题按完整论证评分，Lean 生成／修复题另须原样编译、公理检查和语义覆盖全部通过。

| 模型 | 严格通过 | 已提交／计划 | 有效运行 | 已定／待定 |
|---|---:|---:|---:|---:|
| Terra 6.1 Max | 40/41（97.6%） | 41/41 | 41 | 41/0 |
| Gemini 3.8 Flash High | 27/41（65.9%） | 41/41 | 41 | 41/0 |

## 分项结果

| 任务 | Terra | Gemini |
|---|---:|---:|
| 数学论证 | 29/29（100.0%） | 20/29（69.0%） |
| Lean 对齐判定 | 6/6（100.0%） | 6/6（100.0%） |
| Lean 生成 | 3/3（100.0%） | 0/3（0.0%） |
| Lean 修复 | 2/3（66.7%） | 1/3（33.3%） |

| 判定题子集 | Terra | Gemini |
|---|---:|---:|
| 原 Lean 对齐（3题） | 3/3（100.0%） | 3/3（100.0%） |
| 原 Lean 失配（3题） | 3/3（100.0%） | 3/3（100.0%） |

| 数学章节 | Terra | Gemini |
|---|---:|---:|
| 算子、轨道与不动点 | 6/6（100.0%） | 4/6（66.7%） |
| 分析、观测与最优恢复 | 10/10（100.0%） | 6/10（60.0%） |
| 代数、商结构与相容提升 | 11/11（100.0%） | 7/11（63.6%） |
| 拓扑、下降与空间重构 | 6/7（85.7%） | 5/7（71.4%） |
| 有限集与定量覆盖 | 2/2（100.0%） | 1/2（50.0%） |
| Fourier 分析与正则性 | 3/3（100.0%） | 3/3（100.0%） |
| 几何拼接与层化比较 | 2/2（100.0%） | 1/2（50.0%） |

| 作者主目标 Lean 覆盖分层 | Terra | Gemini |
|---|---:|---:|
| 完整覆盖（40题） | 39/40（97.5%） | 27/40（67.5%） |
| 部分覆盖（P003，1题） | 1/1（100.0%） | 0/1（0.0%） |

## 同题配对

已具备配对结果 41/41 题。双方都通过 27；仅 Terra 通过 13；仅 Gemini 通过 0；双方都未严格通过 1。

六组 Lean 母题各含两个版本，P002 与 F107/F108 另共享公开来源机制。这些题目并非相互独立的随机样本；本轮不作总体模型排名或显著性推断。完整母题配对、作者 Lean 覆盖子集和各类结果计数见 comparison.json。

## 逐题答卷与审核

| 题目 | Terra | Gemini |
|---|---|---|
| MG-R001 | 通过 · [答卷](reviews/packets/21c8fb89e5a2/response.md) · [初审](reviews/primary/21c8fb89e5a2.json) | 未通过 · [答卷](reviews/packets/f43405e0f988/response.md) · [初审](reviews/primary/f43405e0f988.json) · [复核](reviews/adjudication/f43405e0f988.json) |
| MG-R002 | 通过 · [答卷](reviews/packets/b38222e91241/response.md) · [初审](reviews/primary/b38222e91241.json) | 通过 · [答卷](reviews/packets/99586e529c8d/response.md) · [初审](reviews/primary/99586e529c8d.json) · [复核](reviews/adjudication/99586e529c8d.json) |
| MG-R003 | 通过 · [答卷](reviews/packets/13f5e7e33fbe/response.md) · [初审](reviews/primary/13f5e7e33fbe.json) | 通过 · [答卷](reviews/packets/e383e4095259/response.md) · [初审](reviews/primary/e383e4095259.json) · [复核](reviews/adjudication/e383e4095259.json) |
| MG-R004 | 通过 · [答卷](reviews/packets/0d61dfbe0dfe/response.md) · [初审](reviews/primary/0d61dfbe0dfe.json) | 未通过 · [答卷](reviews/packets/5eba4b3d8afb/response.md) · [初审](reviews/primary/5eba4b3d8afb.json) · [复核](reviews/adjudication/5eba4b3d8afb.json) |
| MG-R005 | 通过 · [答卷](reviews/packets/38bf4bba493c/response.md) · [初审](reviews/primary/38bf4bba493c.json) | 部分完成 · [答卷](reviews/packets/078776bdf876/response.md) · [初审](reviews/primary/078776bdf876.json) · [复核](reviews/adjudication/078776bdf876.json) |
| MG-R006 | 通过 · [答卷](reviews/packets/f0ff92306119/response.md) · [初审](reviews/primary/f0ff92306119.json) | 未通过 · [答卷](reviews/packets/2a18e0b1bfbe/response.md) · [初审](reviews/primary/2a18e0b1bfbe.json) · [复核](reviews/adjudication/2a18e0b1bfbe.json) |
| MG-R007 | 通过 · [答卷](reviews/packets/fdff1afd16ee/response.md) · [初审](reviews/primary/fdff1afd16ee.json) | 通过 · [答卷](reviews/packets/850a839551da/response.md) · [初审](reviews/primary/850a839551da.json) |
| MG-R008 | 通过 · [答卷](reviews/packets/4339d3f9a71a/response.md) · [初审](reviews/primary/4339d3f9a71a.json) | 部分完成 · [答卷](reviews/packets/fee14fd21c58/response.md) · [初审](reviews/primary/fee14fd21c58.json) · [复核](reviews/adjudication/fee14fd21c58.json) |
| MG-R009 | 通过 · [答卷](reviews/packets/de9cdd1b3e3b/response.md) · [初审](reviews/primary/de9cdd1b3e3b.json) | 过滤未作答 · [答卷](reviews/packets/284156682c95/response.md) · [初审](reviews/primary/284156682c95.json) · [复核](reviews/adjudication/284156682c95.json) |
| MG-R010 | 通过 · [答卷](reviews/packets/78b37486e1b0/response.md) · [初审](reviews/primary/78b37486e1b0.json) | 通过 · [答卷](reviews/packets/ce028d37fefb/response.md) · [初审](reviews/primary/ce028d37fefb.json) · [复核](reviews/adjudication/ce028d37fefb.json) |
| MG-R011 | 通过 · [答卷](reviews/packets/b5181acd1d63/response.md) · [初审](reviews/primary/b5181acd1d63.json) | 通过 · [答卷](reviews/packets/208b3d352c9d/response.md) · [初审](reviews/primary/208b3d352c9d.json) · [复核](reviews/adjudication/208b3d352c9d.json) |
| MG-R012 | 通过 · [答卷](reviews/packets/5e6306cd122b/response.md) · [初审](reviews/primary/5e6306cd122b.json) | 通过 · [答卷](reviews/packets/e18625028554/response.md) · [初审](reviews/primary/e18625028554.json) · [复核](reviews/adjudication/e18625028554.json) |
| MG-R013 | 通过 · [答卷](reviews/packets/f273009dba41/response.md) · [初审](reviews/primary/f273009dba41.json) | 未通过 · [答卷](reviews/packets/e91453b9092d/response.md) · [初审](reviews/primary/e91453b9092d.json) · [复核](reviews/adjudication/e91453b9092d.json) |
| MG-R014 | 通过 · [答卷](reviews/packets/17549ef0a7fb/response.md) · [初审](reviews/primary/17549ef0a7fb.json) | 通过 · [答卷](reviews/packets/e1e1f895be4b/response.md) · [初审](reviews/primary/e1e1f895be4b.json) |
| MG-R015 | 通过 · [答卷](reviews/packets/961691a8c0ef/response.md) · [初审](reviews/primary/961691a8c0ef.json) | 过滤未作答 · [答卷](reviews/packets/4fd59098a33e/response.md) · [初审](reviews/primary/4fd59098a33e.json) · [复核](reviews/adjudication/4fd59098a33e.json) |
| MG-R016 | 通过 · [答卷](reviews/packets/76da45badcf7/response.md) · [初审](reviews/primary/76da45badcf7.json) | 通过 · [答卷](reviews/packets/ae72c538e2f7/response.md) · [初审](reviews/primary/ae72c538e2f7.json) |
| MG-R017 | 通过 · [答卷](reviews/packets/8b25121ab790/response.md) · [初审](reviews/primary/8b25121ab790.json) | 通过 · [答卷](reviews/packets/39aaf3d77d87/response.md) · [初审](reviews/primary/39aaf3d77d87.json) · [复核](reviews/adjudication/39aaf3d77d87.json) |
| MG-R018 | 通过 · [答卷](reviews/packets/e58c132e89b7/response.md) · [初审](reviews/primary/e58c132e89b7.json) | 通过 · [答卷](reviews/packets/f766846c4d1b/response.md) · [初审](reviews/primary/f766846c4d1b.json) · [复核](reviews/adjudication/f766846c4d1b.json) |
| MG-R019 | 通过 · [答卷](reviews/packets/034dfe36771b/response.md) · [初审](reviews/primary/034dfe36771b.json) | 通过 · [答卷](reviews/packets/afab628440b3/response.md) · [初审](reviews/primary/afab628440b3.json) |
| MG-R020 | 通过 · [答卷](reviews/packets/386e584d70e1/response.md) · [初审](reviews/primary/386e584d70e1.json) | 通过 · [答卷](reviews/packets/d0ad80327f44/response.md) · [初审](reviews/primary/d0ad80327f44.json) |
| MG-R101 | 通过 · [答卷](reviews/packets/e89d9ca6fc79/response.md) · [初审](reviews/primary/e89d9ca6fc79.json) | 通过 · [答卷](reviews/packets/2a775843904d/response.md) · [初审](reviews/primary/2a775843904d.json) |
| MG-R102 | 通过 · [答卷](reviews/packets/3146f3952200/response.md) · [初审](reviews/primary/3146f3952200.json) | 通过 · [答卷](reviews/packets/7554fc980ee3/response.md) · [初审](reviews/primary/7554fc980ee3.json) |
| MG-R103 | 通过 · [答卷](reviews/packets/b836b0d81d23/response.md) · [初审](reviews/primary/b836b0d81d23.json) | 通过 · [答卷](reviews/packets/2ce01a172fda/response.md) · [初审](reviews/primary/2ce01a172fda.json) |
| MG-R104 | 通过 · [答卷](reviews/packets/87e1ad33fb97/response.md) · [初审](reviews/primary/87e1ad33fb97.json) | 通过 · [答卷](reviews/packets/a8a5db580867/response.md) · [初审](reviews/primary/a8a5db580867.json) |
| MG-R105 | 通过 · [答卷](reviews/packets/4e5591398299/response.md) · [初审](reviews/primary/4e5591398299.json) | 通过 · [答卷](reviews/packets/1616d327a566/response.md) · [初审](reviews/primary/1616d327a566.json) |
| MG-R106 | 通过 · [答卷](reviews/packets/4e8fc2172d98/response.md) · [初审](reviews/primary/4e8fc2172d98.json) | 通过 · [答卷](reviews/packets/ecd6e213c87c/response.md) · [初审](reviews/primary/ecd6e213c87c.json) |
| MG-P001 | 通过 · [答卷](reviews/packets/9eec18790f5f/response.md) · [初审](reviews/primary/9eec18790f5f.json) · [复核](reviews/adjudication/9eec18790f5f.json) | 通过 · [答卷](reviews/packets/a4a22fba44ad/response.md) · [初审](reviews/primary/a4a22fba44ad.json) · [复核](reviews/adjudication/a4a22fba44ad.json) |
| MG-P002 | 通过 · [答卷](reviews/packets/108aba1c6b48/response.md) · [初审](reviews/primary/108aba1c6b48.json) · [复核](reviews/adjudication/108aba1c6b48.json) | 通过 · [答卷](reviews/packets/54c72749a7d9/response.md) · [初审](reviews/primary/54c72749a7d9.json) · [复核](reviews/adjudication/54c72749a7d9.json) |
| MG-P003 | 通过 · [答卷](reviews/packets/8cf5722f7f65/response.md) · [初审](reviews/primary/8cf5722f7f65.json) · [复核](reviews/adjudication/8cf5722f7f65.json) | 未通过 · [答卷](reviews/packets/177e5006f00b/response.md) · [初审](reviews/primary/177e5006f00b.json) · [复核](reviews/adjudication/177e5006f00b.json) |
| MG-F101 | 通过 · [答卷](reviews/packets/29b2026afe1c/response.md) · [初审](reviews/primary/29b2026afe1c.json) | 通过 · [答卷](reviews/packets/20d783f0cca0/response.md) · [初审](reviews/primary/20d783f0cca0.json) · [复核](reviews/adjudication/20d783f0cca0.json) |
| MG-F102 | 通过 · [答卷](reviews/packets/7f71790d484e/response.md) · [初审](reviews/primary/7f71790d484e.json) · [Lean](answers/7f71790d484e/lean/report.json) | 原代码编译失败 · [答卷](reviews/packets/5e5cdc4ce0cd/response.md) · [初审](reviews/primary/5e5cdc4ce0cd.json) · [复核](reviews/adjudication/5e5cdc4ce0cd.json) · [Lean](answers/5e5cdc4ce0cd/lean/report.json) |
| MG-F103 | 通过 · [答卷](reviews/packets/ad027ca46dcf/response.md) · [初审](reviews/primary/ad027ca46dcf.json) | 通过 · [答卷](reviews/packets/e29c883e8c72/response.md) · [初审](reviews/primary/e29c883e8c72.json) · [复核](reviews/adjudication/e29c883e8c72.json) |
| MG-F104 | 原代码编译失败 · [答卷](reviews/packets/d1c7f20dc8f5/response.md) · [初审](reviews/primary/d1c7f20dc8f5.json) · [复核](reviews/adjudication/d1c7f20dc8f5.json) · [Lean](answers/d1c7f20dc8f5/lean/report.json) | 原代码编译失败 · [答卷](reviews/packets/6ec046237f89/response.md) · [初审](reviews/primary/6ec046237f89.json) · [复核](reviews/adjudication/6ec046237f89.json) · [Lean](answers/6ec046237f89/lean/report.json) |
| MG-F105 | 通过 · [答卷](reviews/packets/157278e41029/response.md) · [初审](reviews/primary/157278e41029.json) | 通过 · [答卷](reviews/packets/d06058ad9d9f/response.md) · [初审](reviews/primary/d06058ad9d9f.json) · [复核](reviews/adjudication/d06058ad9d9f.json) |
| MG-F106 | 通过 · [答卷](reviews/packets/1593dd38378a/response.md) · [初审](reviews/primary/1593dd38378a.json) · [Lean](answers/1593dd38378a/lean/report.json) | 原代码编译失败 · [答卷](reviews/packets/67a117318c43/response.md) · [初审](reviews/primary/67a117318c43.json) · [复核](reviews/adjudication/67a117318c43.json) · [Lean](answers/67a117318c43/lean/report.json) |
| MG-F107 | 通过 · [答卷](reviews/packets/7d807e500b52/response.md) · [初审](reviews/primary/7d807e500b52.json) | 通过 · [答卷](reviews/packets/c1721a293868/response.md) · [初审](reviews/primary/c1721a293868.json) · [复核](reviews/adjudication/c1721a293868.json) |
| MG-F108 | 通过 · [答卷](reviews/packets/e52a72990aea/response.md) · [初审](reviews/primary/e52a72990aea.json) · [Lean](answers/e52a72990aea/lean/report.json) | 通过 · [答卷](reviews/packets/3aadf5a9956d/response.md) · [初审](reviews/primary/3aadf5a9956d.json) · [Lean](answers/3aadf5a9956d/lean/report.json) |
| MG-F109 | 通过 · [答卷](reviews/packets/b24c41e7b25b/response.md) · [初审](reviews/primary/b24c41e7b25b.json) | 通过 · [答卷](reviews/packets/6b8d03414c3b/response.md) · [初审](reviews/primary/6b8d03414c3b.json) · [复核](reviews/adjudication/6b8d03414c3b.json) |
| MG-F110 | 通过 · [答卷](reviews/packets/e25809046400/response.md) · [初审](reviews/primary/e25809046400.json) · [Lean](answers/e25809046400/lean/report.json) | 原代码编译失败 · [答卷](reviews/packets/5d4f83d72d3c/response.md) · [初审](reviews/primary/5d4f83d72d3c.json) · [复核](reviews/adjudication/5d4f83d72d3c.json) · [Lean](answers/5d4f83d72d3c/lean/report.json) |
| MG-F111 | 通过 · [答卷](reviews/packets/7e4e06c4cb71/response.md) · [初审](reviews/primary/7e4e06c4cb71.json) | 通过 · [答卷](reviews/packets/34ad21bbc579/response.md) · [初审](reviews/primary/34ad21bbc579.json) · [复核](reviews/adjudication/34ad21bbc579.json) |
| MG-F112 | 通过 · [答卷](reviews/packets/53fe3ad98678/response.md) · [初审](reviews/primary/53fe3ad98678.json) · [复核](reviews/adjudication/53fe3ad98678.json) · [Lean](answers/53fe3ad98678/lean/report.json) | 原代码编译失败 · [答卷](reviews/packets/76a7d10c4e85/response.md) · [初审](reviews/primary/76a7d10c4e85.json) · [复核](reviews/adjudication/76a7d10c4e85.json) · [Lean](answers/76a7d10c4e85/lean/report.json) |

## 未作答与评分边界

严格通过率使用原定每模型 41 题的完整分母，包含服务端过滤未作答。过滤通知不属于错误数学证明，数学审核轴记为 unknown；本轮没有为它重试或改写提示。

| 模型 | 过滤未作答 | 返回数学答卷 | 有数学答卷中的通过数 |
|---|---:|---:|---:|
| Terra 6.1 Max | 0 | 41 | 40/41 |
| Gemini 3.8 Flash High | 2 | 39 | 27/39 |

编译证据表述另记：Gemini 3.8 Flash High MG-F101；Gemini 3.8 Flash High MG-F103；Gemini 3.8 Flash High MG-F105；Gemini 3.8 Flash High MG-F107；Gemini 3.8 Flash High MG-F109；Gemini 3.8 Flash High MG-F111 给出了确定的编译／公理报告文字，但候选没有实际 Lean 执行收据。这些文字不计作候选编译证据；其对齐审计的数学完成情况依题面单独判断。

上表的答卷子集仅作补充，不能替代全题通过率。通过表示所有必需义务已有有效证明；少数通过答卷仍有不影响主证明的附加错误，详见逐题复核。

R005 原题未单独明示竞争函数能否取负无穷值；本轮保留原题及原分数，并在复核中记录该边界。澄清后的新版本将以独立两模型单题补测记录，不替换本轮答卷。

## 运行与证据边界

- 四组题集和评分材料在发送前冻结；两模型逐题消息字节相同，每题独立会话、无答题工具或现场 Lean 反馈，先 Terra 后 Gemini，每模型并发 2 题。
- 请求型号为 `gpt-6.1-terra/max` 和 `gemini-3.8-flash-high/high`。当前 CLI 没有独立回显 Terra 型号／档位和 Gemini 档位；Gemini 回显了型号。请求配置、观测字段和局限分别保留。
- 40 题具有完整作者主任务 Lean 证据；P003 的完整数学参考依赖精确引用的已发表几何结果，作者 Lean 为部分覆盖。作者编译证据不替代候选答案正确性。
- 评审包不另附模型标签，但阶段时序及少数原始答卷中的文件路径可能暴露模型，因此不称完全盲审；原始答卷未为匿名而改写。数学失败、部分完成、争议和格式提取问题保留独立复核；没有改候选代码后回填原分数。
- [事前方案](PLAN.md) · [题集质量门槛](qualification/README.md) · [完整统计](comparison.json) · [习题总目录](../../exercises/README.md)。
