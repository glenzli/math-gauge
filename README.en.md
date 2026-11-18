# Math Gauge

[简体中文](README.md) · [English](README.en.md)

**Measure the capability, not just the answer.**

Math Gauge evaluates models on mathematical work: written proofs, Lean formalization and mathematical research tasks. The current version is **[1.0.0](https://github.com/glenzli/math-gauge/releases/tag/v1.0.0)**.

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
| **MC · Mathematical Capability** | Verified positive mathematical contributions, including valid progress on unfinished tasks. |
| **RMC · Reliable Mathematical Capability** | Valid work after deductions for false claims, misjudgments and related errors; the default primary score. |
| **SMC · Strict Mathematical Completion** | Credit only when all substantive task requirements are met. Self-checking is assessed over the full three-round trajectory, including completion, diagnosis and no regression. |

All three use the same rule-selected answers and fixed weights, reported against **100 points**. Unrun tasks retain unknown ranges; measured coverage is never scaled up to a full score. Each task uses the first normal final allowed by the rules. Without one, verified original work present by the cutoff may earn MC; RMC and SMC are zero. See the [scoring specification](protocol/benchmark-scoring.md) for the detailed criteria.

## Current results

The leaderboard defaults to RMC. The [interactive page](https://glenzli.com/benchmarks/math-gauge/?lang=en) lets you switch between the three scores, compare categories and open model pages with public answers and task reviews. The [full written report](docs/results.md) retains the score table, source corrections and supplementary tests.

The fresh [Sol 6.2 Max](https://glenzli.com/benchmarks/math-gauge/models/sol-6.2-max/?lang=en) run on November 18 is now on the leaderboard: MC **93.21**, RMC **93.21**, SMC **89.17**. See the [full results](docs/results.md#sol-62-max--2026-11-18) for the changes from Sol 6.1 Max.

[![Math Gauge English leaderboard](docs/screenshots/leaderboard-en.jpg)](https://glenzli.com/benchmarks/math-gauge/?lang=en)

The results combine archived answers from different batches, including reused answers and later supplementary tests. They use **AI review, with partial human spot checks**. Actual conditions, failures and retries remain attached to their sources; see the [review process](docs/review-process.md) and [execution notes](docs/results.md#记录与复算) when comparing models.

<details>
<summary>Cost and timing screenshots</summary>

Both plots below show RMC. Cost counts one selected attempt per task plus the three fixed self-checks, using archived API reference tariffs or the confirmed cost on the test date. Time includes tools and waiting and depends on the execution environment. See the [cost method](docs/cost-reference.md) and [timing method](docs/answer-timings.md) for sources and limits.

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
| Supplementary metrics | [Content reliability and goal attainment](protocol/content-rates.md) · [Additional manuscript results](docs/manuscript-observations.md) |
| Execution and records | [Harness and delivery guide](docs/harness-guide.md) · [Result-record contract](protocol/result-record.md) |
| Time and cost | [Timing method](docs/answer-timings.md) · [Cost method](docs/cost-reference.md) |
| Failures and supplements | [Source corrections](docs/harness-corrections.md) · [Whole-chapter self-check supplements](docs/c003-sealed-continuation.md) · [Attempt and retry statistics](docs/execution-attempts.md) |
| Versions and evidence | [1.0.0 release](releases/v1.0.0/README.md) · [Past releases](releases/) · [Evidence retention and recovery](docs/evidence-retention.md) |

Historical answers adopted by 1.0.0 keep their original execution versions, responses and reviews; the release notes explain compatibility. Viewing or recomputing those results does not mean the models were tested again.
