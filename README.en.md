# Math Gauge

[简体中文](README.md) · [English](README.en.md)

**Measure the capability, not just the answer.**

Math Gauge measures whether models can perform mathematical work reliably: prove and refute, review arguments, turn natural-language goals into semantically aligned Lean projects, check research premises, extend propositions, and develop ideas into rigorous manuscripts.

The current formal release is **benchmark 1.0.0**. Public and private tasks form one benchmark, with a shared runner and scoring rules. This release reuses archived 0.6 answers while preserving their original execution identities, responses and reviews; the [release notes](releases/v1.0.0/README.md) record compatibility.

[Leaderboard](site/index.html?lang=en) · [Full results](docs/results.md) · [Task catalog](cases/README.md) · [Harness guide](docs/harness-guide.md)

## Design

Mathematical progress can come from finding spaces, objects and languages that make a problem simpler. In *Récoltes et Semailles*, Grothendieck compares this process to soaking a nut until its shell opens. Math Gauge adopts this emphasis on finding useful mathematical structures. See Colin McLarty's [The Rising Sea](https://www.landsburg.com/grothendieck/mclarty1.pdf), which translates the passage on manuscript pages 552–553.

A short proof, counterexample, quotient construction or alternative representation can complete a task. A change of representation needs a proved correspondence and a bridge back to the original question, preserving assumptions, quantifiers, domains and conclusion strength. Rigorous, faithful alternatives can earn full marks; length and similarity to the reference route carry no credit themselves.

Following the author's [AI, Mathematical Ability, and the Future](https://glenzli.com/notes/ai-mathematical-ability-and-the-future/), **Lv1** covers calculation, execution and implementation with known objects and rules. **Lv2** covers proof and refutation within an existing framework of definitions, axioms, language and questions. These describe kinds of work; very difficult calculations and proofs can belong to either.

This generation samples Lv1/Lv2 abilities needed for OET mathematical writing, review and formalization, asking whether they can be used reliably: do conditions drift through a long argument, does formalization prove the intended statement, does self-checking find and repair gaps, and does research compound a faulty premise? Independently solving frontier open problems is outside the suite's requirements. Productive question formation and the creation of mathematical frameworks need further forms of assessment.

## Suite structure

| Category | Subcategory | Points | Public tasks | Private tasks | Aggregation unit |
|---|---|---:|---:|---:|---|
| Written proof · 35 | Written arguments | 25 | 8 | 4 | 12 mathematical families |
| | Argument review | 10 | 4 | 0 | 4 parent families |
| Lean · 35 | Semantic audit | 10 | 4 | 0 | 2 mathematical families |
| | Formalization | 15 | 4 | 0 | 2 mathematical families |
| | Alignment self-check | 10 | Reuses 1 task | 0 | Three fixed rounds on a 92-obligation chapter |
| Mathematical research · 30 | Background check | 10 | 2 | 2 | 4 mathematical families |
| | Idea-to-manuscript completion | 10 | 1 | 4 | 5 mathematical families |
| | Theorem extension | 10 | 2 | 4 | 6 mathematical families |

There are **39 initial tasks: 25 public and 14 private, spanning 35 mathematical families**. Three successive self-check rounds reuse the same whole-chapter Lean project, giving 42 prescribed deliveries. Related variants are aggregated within families; public and private contributions share a fixed 100-point total.

Written tasks test proofs, boundaries and counterexamples. Lean tasks scale to partial and full chapters, assessing kernel acceptance, semantic alignment and sustained self-checking separately. Research tasks ask models to check premises, attempt extensions, or make an idea rigorous. Public example [MG-MCP003](cases/manuscript-completion/MG-MCP003/task.md) starts from matrix-estimate ideas and requires a complete mathematical manuscript.

Public tasks support replication and inspection; private tasks add undisclosed mathematical problems. Candidates receive only task text and explicitly supplied materials. Private references, rubrics, raw answers and detailed reviews remain private; public reports show their combined contributions. See the [selection rationale](docs/selection.md).

## Reading the scores

| Metric | What it measures |
|---|---|
| **MC · Mathematical Capability** | Positive credit for valid mathematical results, including verified partial progress. |
| **RMC · Reliable Mathematical Capability** | Valid work after deductions for false claims and misjudgments; the default primary score. |
| **SMC · Strict Mathematical Completion** | Acceptance of the complete task goal; Lean self-checking additionally requires the full three-round trajectory to meet completeness, diagnosis and no-regression rules. |

All three use the same rule-selected answers, families and weights. Incorrect work receives no credit merely for being present; compilation also requires a separate check against the mathematical goal. Honest incompleteness and a false claim of completeness have different reliability consequences.

Current aggregation is **0.9.0**, MC **0.3.0**, SMC **0.2.0**, with submission component **0.1.0**. A normal final limits all three scores to the actually delivered work. Without one, verified original work present by the cutoff may earn MC; RMC and SMC are zero. Finals and collected content are mutually exclusive counts. Original 0.8.0 records and reviews remain source-bound.

[Content reliability and complete-goal attainment](protocol/content-rates.md) provide two further views: correctness and support of actual delivered content, and acceptance of complete independent goals required by a task. The research panel's [additional-results observation](docs/manuscript-observations.md) counts verified result groups not requested by the original task. It is separate from the scores and currently covers 80 of 85 manuscript slots across 17 models.

## Current leaderboard

Rows are sorted by RMC. Every score is reported in the fixed 100-point frame. Permitted retries select the first normal delivery under the rules; source records retain the process. Some tests reuse prior answers produced under equivalent conditions.

| Model | Harness | MC | **RMC (main)** | SMC | Finals / collected / tasks |
|---|---|---:|---:|---:|---:|
| [Astra 6 (max)](site/models/astra-6-max/index.html) | Codex CLI | 94.32 | 94.32 | 89.17 | 39 / 0 / 39 |
| [Sol 6.1 (max)](site/models/sol-6.1-max/index.html) | Codex CLI | 94.32 | 94.22 | 89.17 | 39 / 0 / 39 |
| [Claude Opus 5.5 (max)](site/models/claude-opus-5.5-max/index.html) | Claude Code | 93.76 | 91.44 | 59.42 | 39 / 0 / 39 |
| [Astra 6 (xhigh)](site/models/astra-6-xhigh/index.html) | Codex CLI | 91.45 | 90.45 | 79.17 | 39 / 0 / 39 |
| [Dot Underlying (2026-11-08)](site/models/dot-underlying-model-20261108/index.html) | Dot native harness¹ | 91.66 | 90.23 | 78.00 | 39 / 0 / 39 |
| [Claude Sonnet 5.5 (max)](site/models/claude-sonnet-5.5-max/index.html) | Claude Code | 91.95 | 88.20 | 55.42 | 39 / 0 / 39 |
| [Sol 6.1 (xhigh)](site/models/sol-6.1-xhigh/index.html) | Codex CLI | 90.12 | 87.96 | 68.00 | 39 / 0 / 39 |
| [Terra 6.1 (max)](site/models/terra-6.1-max/index.html) | Codex CLI | 82.62 | 80.85 | 65.67 | 39 / 0 / 39 |
| [Gemini 4 Carbon (medium)](site/models/gemini-4-carbon-medium/index.html) | AGY CLI⁴ | 91.78 | 79.74 | 64.50 | 38 / 1 / 39 |
| [Terra 6.1 (xhigh)](site/models/terra-6.1-xhigh/index.html) | Codex CLI | 79.71 | 78.50 | 63.00 | 39 / 0 / 39 |
| [Gemini 4 Hydrogen (xhigh)](site/models/gemini-4-hydrogen-xhigh/index.html) | AGY CLI⁴ | 87.80 | 76.81 | 47.92 | 39 / 0 / 39 |
| [Gemini 4 Carbon (high)](site/models/gemini-4-carbon-high/index.html) | AGY CLI⁴ | 88.51 | 74.78 | 32.83 | 38 / 1 / 39 |
| [Kimi 3.1 Pro (max)](site/models/kimi-3.1-pro-max/index.html) | Claude Code | 75.28 | 70.41 | 43.67 | 38 / 0 / 39 |
| [Gemini 4 Argon (high)](site/models/gemini-4-argon/index.html) | AGY CLI⁴ | 86.33 | 70.24 | 37.92 | 38 / 1 / 39 |
| [DeepSeek v4.1 Flash (max)](site/models/deepseek-v4.1-flash-1017/index.html) | Codex CLI² | 76.71 | 64.23 | 25.83 | 37 / 1 / 39 |
| [Gemini 3.8 Flash (high)](site/models/gemini-3.8-flash-high/index.html) | AGY CLI⁴ | 59.94 | 39.77 | 13.75 | 38 / 1 / 39 |
| [GLM 5.3 (max)](site/models/glm-5.3-max/index.html) | Claude Code³ | 41.48 | 27.34 | 14.08 | 21 / 5 / 39 |

Per-round sources and full score intervals are available in model details. Tested tasks that time out without a submission are scored under the failure rules.

¹ Dot's native independent execution mode.

² Under DeepSeek Harness (DSH), many tasks exhausted the maximum output budget through prolonged reasoning without delivering an answer, so execution uses Codex CLI.

³ GLM 5.3 had frequent timeouts under both Codex CLI and Claude Code; the retained results use Claude Code. Without a normal final, RMC and SMC are zero; verified original work may earn MC. The three self-check rounds were not run.

⁴ Retained AGY CLI runs show serious response-delivery and termination defects that can lose model replies or keep waiting until timeout. Additional reruns are allowed for evidenced harness faults, so physical calls may exceed the usual three attempts. Verified idle tails are removed from displayed times while original clocks are retained. Mathematical errors after a normal submission do not permit a rerun.

The recovered HCH02 reply has been adopted after an AGY delivery fault and reviewed under the existing rules. Original ERROR receipts and scores are retained; benchmark1.0.0 and its scoring methods are unchanged. See the [source correction](docs/harness-corrections.md).

Argon also completed a [sealed-project self-check supplement](docs/c003-sealed-continuation.md). All three projects verify 92/92 obligations; diagnosis earns 30, 25 and 15 out of 30, giving 9.33/10 for self-check. The original A1 failure and HCH02 scores remain unchanged.

Flash also completed three engineering self-checks through the AGY subscription. All delivered normally but stayed at 74/92 with no new repairs; all three falsely claimed full completion, giving RMC −2/10 for self-check. See the [round answers, reviews and score changes](results/v0.6.0/gemini-3.8-flash-high/20261105/supplements/c003-20261114/README.md).

Carbon Medium retains38normal finals and one forced-content A1. The latter uses only the original work from its final effective attempt for MC; task RMC/SMC are0. C003 A1 and three KEEP rounds each verified92/92, passing the whole Strict trajectory. See [model details](site/models/gemini-4-carbon-medium/index.html) and the [source-selection disclosure](results/v0.6.0/gemini-4-carbon-medium/20261115/source-selection-disclosure.json) for actual ordinals, system exclusions and reviews.

The Carbon campaign, including High, Medium and environment troubleshooting, spans more than two days; the earlier Medium batch covered about47hours40minutes, before the additional C003 opportunity. AGY/GCP runs repeatedly suffered stream failures, timeouts and HTTP429. Argon and Carbon also exposed serious reasoning errors and completion problems on complex tasks; unstable calls remain a separate factor when attributing missing submissions. The initial High batch ended without a usable full answer set; the later continuation is documented below.

The 2026-11-15 Carbon High continuation is settled: 38 normal A1 finals, 1 forced-content slot and 0 slots without assessable text out of 39, with MC/RMC/SMC 88.51/74.78/32.83. Non-Lean tasks ran first, followed by Lean tasks, with C003 and its three fixed self-checks last; successful pilots are retained as formal answers. Later native HIGH/MEDIUM requests under AGY1.5.9 preserve their original effort settings. Proven local-controller or authentication TLS faults are preserved separately and consume no effective attempt. Stream failures without proof of a pure system fault retain their original count; deadlines and output exhaustion consume an attempt. See [model details](site/models/gemini-4-carbon-high/index.html) and the [source disclosure](results/v0.6.0/gemini-4-carbon-high/20261115/source-selection-disclosure.json) for mathematical judgments, round states and actual conditions.

The complete retained history contains 62 task-attempt records: seven from the earlier failed batch and 55 from the resumed run and self-checks. These comprise 51 effective attempts and 11 system exclusions. Relative to 39 initial tasks plus three self-check rounds, there are 20 additional attempt records, including nine effective retries. The seven reviewed samples in the older anomaly table are a historical subset, not the campaign retry total; task-attempt records are not API-call counts. See the [complete attempt and retry report](docs/execution-attempts.md).

All 92 formal targets in C003's initial answer were verified. Its three self-checks delivered normally, earning MC/RMC 70→100→100. The first round missed a local numerical error in the original mapping explanation, so the whole trajectory earns SMC0; the later accurate diagnoses do not replace the first round retrospectively.

The user explicitly accepted the retained extra trials after observation. Actual physical and effective attempt numbers and prior failures remain intact, including attempts beyond three; answers were selected by source and first normal delivery, without best-of scoring. This adoption retains AI-review/human-pending status and does not upgrade comparison eligibility.

Results use AI review with partial human spot checks. Existing full-set reviews are attributed to Sol 6.1 Max, with sampled cross-checks by Astra 6 Max and Dot; Carbon retains its source-specific AI review attribution. See the [review process](docs/review-process.md) for source-specific identities, evidence and limitations, and the [results report](docs/results.md) for model-level analysis.

![Math Gauge English leaderboard](docs/screenshots/leaderboard-en.jpg)

![Math Gauge English cost–RMC frontier](docs/screenshots/cost-frontier-en.jpg)

![Math Gauge English time–RMC frontier](docs/screenshots/time-frontier-en.jpg)

Both frontier plots default to RMC: total cost uses a linear dollar scale starting at zero, and typical-task time is measured in minutes. Solid points indicate normal final submissions on all 39 initial tasks; other points are hollow. Colors follow model brands. Model names are shown beside the points; hover highlights the matching point, and clicking pins a label. The frontier uses a solid line. Time includes tool use and waiting, and varies with harness, network and hardware; see the [method and sources](docs/answer-timings.md).

Cost counts only the retained attempt for each task, excluding other retries. Dot used a separate subscription-bundled allowance on its test date, with $0 additional cost. Models with verified tariffs use public API prices with cache discounts. Gemini 4 Hydrogen ran through the AGY subscription; its 42 native usage receipts yield a $51.63 reference cost at official Standard API rates. Argon's reference cost including the three new self-check rounds is $37.74 at introductory 50%-off rates through November 30, 2026; the same usage at December rates would cost about $75.48. Carbon Medium's API reference total is $56.99, excluding auxiliary safety calls. Carbon High's selected-attempt API reference is $73.52, with all 42 selected native usage receipts reconciled; other retries and auxiliary calls are excluded. See the [cost method](docs/cost-reference.md) for full usage, prices and sources. The [interactive plots](site/index.html?lang=en#cost-frontier) provide score and axis controls.

The leaderboard publishes selected snapshots after their test process has ended; future tests are added after settlement. The [interactive page](site/index.html?lang=en) provides category leaderboards, two rates, score gaps, and separate cost and timing rankings, with MC/RMC/SMC controls, bilingual display and shareable URL state. Model pages retain task results, self-check execution states and score intervals.

## Running and reproducing

All formal tasks allow local tools and preinstalled public dependencies. External retrieval and tool networking are prohibited; model-service and authentication connections are recorded separately. Independent initial tasks may run in parallel; C003's three self-check rounds must each continue from the preceding project. Answer formats, time limits, sealing, isolation, failures and retries are specified in the shared [external-harness guide](docs/harness-guide.md).

From the repository root, start a local server and open <http://127.0.0.1:8000/site/>:

```bash
python3 -m http.server 8000 --bind 127.0.0.1
```

The page itself works offline. Horizontal charts use compact rows. Overall and category boards switch independently between chart and table views, with view, visible metrics and sort choices retained in the URL. Downloads and longer run notes expand on demand. See the [results report](docs/results.md) for site regeneration and data recomputation.

Current answers, reviews, mathematical source and timing/cost summaries remain in the working tree. Duplicate copies, original containers, complete event streams and build caches are retained by immutable Git commits and a hash-bound index. Both repositories follow the same [evidence retention and recovery rules](docs/evidence-retention.md); a complete audit requires local Git history.

## Documentation

| Topic | Entry point |
|---|---|
| Tasks and selection | [Task catalog](cases/README.md) · [Selection rationale](docs/selection.md) |
| Execution and external harnesses | [Shared harness guide](docs/harness-guide.md) · [Evaluation protocol](protocol/evaluation.md) |
| Scoring and evidence | [Scoring specification](protocol/benchmark-scoring.md) · [Result-record contract](protocol/result-record.md) |
| Results and supplementary metrics | [Full results](docs/results.md) · [Two rates](protocol/content-rates.md) · [Additional-results observation](docs/manuscript-observations.md) |
| Distributions and reproduction packages | [1.0.0 release](releases/v1.0.0/README.md) · [0.6.1 distribution](releases/v0.6.1/README.md) · [0.6.0 sealed release](releases/v0.6.0/README.md) |

Release 1.0.0 records the current suite and scoring rules; the 0.6.0 task package and published assets remain frozen. Distribution, execution components and scoring methods retain their own version and source identities.
