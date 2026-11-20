# Math Gauge

[简体中文](README.md) · [English](README.en.md)

**Measure the capability, not just the answer.**

Math Gauge evaluates models on mathematical work: written proofs, Lean formalization and mathematical research tasks. The current scoring edition is **[1.2.0](docs/neutral-revision.md)**; the latest published task distribution is **[1.0.0](https://github.com/glenzli/math-gauge/releases/tag/v1.0.0)**.

[Live leaderboard](https://glenzli.com/benchmarks/math-gauge/?lang=en) · [Full results](docs/results.md) · [Public tasks](cases/README.md) · [Harness guide](docs/harness-guide.md)

## Why I built Math Gauge

> The first analogy that came to my mind is of immersing the nut in some softening liquid, and why not simply water?
>
> (Alexander Grothendieck, *Récoltes et Semailles*, translated by Colin McLarty in [*The Rising Sea*](https://www.landsburg.com/grothendieck/mclarty1.pdf).)

I really like the phrase "soaking the nut."

Today's frontier models already have very strong mathematical abilities, and benchmarks such as [FrontierMath](https://epoch.ai/frontiermath) and [BrokenArXiv](https://matharena.ai/?comp=overall--brokenarxiv) offer useful points of reference. Yet while writing [OET (Operator Evolution Theory)](https://glenzli.com/books/oet/), I still run into problems: an argument can read smoothly but omit a necessary assumption, or an answer can look correct after quietly changing the question into something more familiar to the model.

In my own mathematical work, I often start with an idea, then gradually clarify the concepts, find a useful representation and work through the derivations and proofs. Some of these ideas do not follow routes familiar to a model. I care about whether it can keep track of the original question, check each step carefully and preserve the assumptions and intent. It can challenge an idea, give a counterexample or suggest another approach, but it needs to explain its reasons and how that approach relates to the original problem.

Over the course of this work, I moved from mainly using Gemini and Claude to GPT models for most tasks. I gradually got a feel for their different strengths, blind spots and styles. But models keep improving, so those impressions need to be revisited. That gave me the idea for a benchmark tailored to my own mathematical work. I could turn the derivations, argument reviews, background checks and Lean formalization I need help with into tasks, compare what the models actually deliver, and use the results to choose my main model and decide how to divide the work. That is how Math Gauge began.

## What the suite tests

| Area | Points | Main tasks |
|---|---:|---|
| Written proof | 35 | Arguments, counterexamples, boundary analysis and review of existing arguments. |
| Lean | 35 | Semantic audits, formalization and three successive self-checks, assessing code, mathematical alignment and error correction. |
| Mathematical research | 30 | Background checks, theorem extensions and developing an idea into a rigorous manuscript. |

The full assessment has **39 initial tasks: 25 public and 14 private, spanning 35 mathematical families**. Three self-check rounds continue the same whole-chapter Lean project, giving 42 prescribed deliveries. Related variants are aggregated within families; public and private tasks share the same runner and scoring rules.

For a first example, read the [matrix-estimate idea-to-manuscript task](cases/manuscript-completion/MG-MCP003/task.md). The [task catalog](cases/README.md) and [selection rationale](docs/selection.md) explain the subcategories, weights and choices. Candidates receive only task text and explicitly supplied materials; references and rubrics stay outside their answer context. Private task text, raw answers and individual reviews remain private.

## Reading the scores

| Score | Meaning |
|---|---|
| **SMC · Strict Mathematical Completion** | Each delivery receives binary whole-task credit; edition1.2.0 weights the first and revision judgments. Lean self-checking still uses the complete three-round trajectory. |
| **RMC · Reliable Mathematical Capability** | Reliable mathematical work after deductions for false claims, misjudgments and related errors. |
| **MC · Mathematical Capability** | Verified positive mathematical contributions, including valid progress on unfinished tasks. |

All three use the same rule-selected answers and fixed weights, reported against **100 points**. Unrun tasks retain unknown ranges; measured coverage is never scaled up to a full score. Each task uses the first normal final allowed by the rules. Without one, verified original work present by the cutoff may earn MC; RMC and SMC are zero. Edition1.2.0 adds one neutral revision for non-Lean loss tasks. All three modes on a selected task use **80% first answer plus20% revision**, including regressions; tasks already full in all three modes are exempt, and Lean results stay unchanged. The two strict judgments remain separate. See the [revision protocol](protocol/neutral-revision.md) and [scoring specification](protocol/benchmark-scoring.md).

Theorem-extension tasks also assess the research increment actually delivered: R1 is useful local progress, R2 is a substantive extension, and R3 is a deep and complete research contribution. Equivalent routes and strong results inside the proof receive the same credit. SMC for this category requires a correct baseline and a complete R3 result. B2/R0 means the original proof is correct without additional research credit. See the [1.1.0 scoring notes](docs/theorem-extension-reassessment.md) for the detailed standards.

## Current results

The leaderboard defaults to SMC, with score controls ordered SMC / RMC / MC. The results page opens **1.2.0**; the local edition now includes 15 settled configurations across GPT, Claude, Kimi and DeepSeek. Other configurations await returns, with **1.1.0/1.0.0** results available. Model pages, task reviews and downloads follow that selection. See [edition switching](docs/edition-views.md). The [interactive page](https://glenzli.com/benchmarks/math-gauge/?lang=en) lets you switch between the three scores, compare categories and open model pages with public answers and task reviews. The [full written report](docs/results.md) retains the score table, source corrections and supplementary tests.

The 15 configurations have 171 adopted revisions, with 100 full in all three modes. The original nine GPT configurations retain their 68 revisions, and 68 external answers from three Claude configurations and Kimi remain adopted. Astra 6.2 xHigh adds nine revisions, eight full in all three modes. All 171 revisions have completed AI mathematical review. Six external configurations, covering 106 tasks, still await returns; GLM is skipped. Costs include the full resource use of effective revisions. Timing still compares 12 shared tasks, with whole-chapter formalization separate, and mathematical profiles offer first-answer and revision-inclusive views. Original answers, historical scores and the published 1.0.0 task package remain intact. These updates are local; each batch below states its first-answer or revision-inclusive scoring edition. [Edition notes](docs/neutral-revision.md)

DeepSeek v4.1 Flash (1017, max) has 26 settled neutral revisions:24 normal finals, one cutoff manuscript reviewed for MC only, and one cutoff with no deliverable content. Edition1.2.0 gives **MC76.93 / RMC64.09 / SMC26.25**, with one of26 revisions full in all modes. Revisions add $8.45 in reference cost, totaling $14.86 with the original answers and three self-checks. Native finals, recovered original delivery files, mathematical judgments and130 independent five-axis judgments remain source-bound; no candidates were called again. [Detailed review](results/edition-reassessments/v1.2.0/deepseek-v4.1-flash-1017/20261110/REPORT.md)

The November 20 [Astra 6.2 (xHigh)](https://glenzli.com/benchmarks/math-gauge/models/astra-6.2-xhigh/?lang=en) run completed 39 initial tasks, three self-checks and nine neutral revisions. Its 1.2.0 scores are SMC **83.90**, RMC **91.66** and MC **92.66**. Original answers and judgments remain unchanged. The run used Codex CLI0.169.1 through the OpenAI API; human mathematical review remains pending. See the [full results](docs/results.md#astra-62-xhigh--2026-11-20) for categories, companion metrics and execution conditions.

The November 19 [Claude Opus 5.5 (xHigh)](https://glenzli.com/benchmarks/math-gauge/models/claude-opus-5.5-xhigh/?lang=en) answers were fully reviewed in parallel by Sol 6.1 Max: MC **91.36**, RMC **88.80**, SMC **54.92**. All 39 initial tasks and three self-checks delivered normally. See the [full results](docs/results.md#claude-opus-55-xhigh--2026-11-19) for evidence and execution conditions.

The November 19 [Astra 6.2 Max](https://glenzli.com/benchmarks/math-gauge/models/astra-6.2-max/?lang=en) run completed all 39 initial tasks and three self-checks. After comparing its original answers with Astra 6, its first assessment under 1.1.0 gives MC **92.25**, RMC **92.25** and SMC **87.17**. See the [full results](docs/results.md#astra-62-max--2026-11-19) for category scores, reliability, attainment, the mathematical profile and execution conditions. The Sol 6.2 Max/xHigh results and comparisons with their predecessors remain there as well.

The profile separates [open research capability and research initiative](docs/open-research.md): what a model delivers when research is explicitly requested, and whether it pursues further work unprompted. Initiative is the last of eight axes. The two are assessed independently; restraint alone does not establish a lack of capability.

The screenshot below illustrates the archived1.1.0 view; the interactive page contains current1.2.0 scores and pending revisions.

[![Math Gauge English leaderboard](docs/screenshots/leaderboard-en.jpg)](https://glenzli.com/benchmarks/math-gauge/?lang=en)

The results combine archived answers from different batches, including reused answers and later supplementary tests. They use **AI review, with partial human spot checks**. Actual conditions, failures and retries remain attached to their sources; see the [review process](docs/review-process.md) and [execution notes](docs/results.md#记录与复算) when comparing models.

<details>
<summary>Cost and timing screenshots</summary>

Both plots below show RMC. Baseline cost counts one selected attempt per task plus the three fixed self-checks; edition1.2.0 adds the full actual cost of adopted revisions. These screenshots precede revisions; consult the interactive page for current values. Cost uses archived API reference tariffs or the confirmed cost on the test date. Time includes tools and waiting and depends on the execution environment. See the [cost method](docs/cost-reference.md) and [timing method](docs/answer-timings.md) for sources and limits.

[![Math Gauge English cost–RMC frontier](docs/screenshots/cost-frontier-en.jpg)](https://glenzli.com/benchmarks/math-gauge/?lang=en&cost-axis=cost&cost-score=partial#cost-frontier)

[![Math Gauge English time–RMC frontier](docs/screenshots/time-frontier-en.jpg)](https://glenzli.com/benchmarks/math-gauge/?lang=en&cost-axis=time&cost-score=partial#cost-frontier)

</details>

## Viewing locally and running the assessment

From the repository root, start a local server and open <http://127.0.0.1:8000/site/>:

```bash
python3 -m http.server 8000 --bind 127.0.0.1
```

To run the assessment, use the [harness and delivery guide](docs/harness-guide.md) to prepare the package and independent candidate environments. All formal tasks **allow local tools and preinstalled public dependencies; external retrieval and tool networking are prohibited**. Model-service and authentication traffic are recorded separately. The guide specifies packages, time limits, sealing, isolation and retries.

## Further reading

| To learn about | Start here |
|---|---|
| Tasks and selection | [Public tasks](cases/README.md) · [Selection rationale](docs/selection.md) |
| Scoring and review | [Evaluation protocol](protocol/evaluation.md) · [Scoring specification](protocol/benchmark-scoring.md) · [Review process](docs/review-process.md) |
| Supplementary metrics | [Mathematical profile: first answers / including revisions](docs/mathematical-profile-revision.md) · [Content reliability and goal attainment](protocol/content-rates.md) · [Additional manuscript results](docs/manuscript-observations.md) |
| Execution and records | [Harness and delivery guide](docs/harness-guide.md) · [Result-record contract](protocol/result-record.md) |
| Time and cost | [Timing method](docs/answer-timings.md) · [Cost method](docs/cost-reference.md) |
| Failures and supplements | [Source corrections](docs/harness-corrections.md) · [Whole-chapter self-check supplements](docs/c003-sealed-continuation.md) · [Attempt and retry statistics](docs/execution-attempts.md) |
| Versions and evidence | [1.1.0 scoring notes](docs/theorem-extension-reassessment.md) · [1.0.0 release](releases/v1.0.0/README.md) · [Evidence retention and recovery](docs/evidence-retention.md) |
