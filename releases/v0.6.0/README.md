# Benchmark 0.6.0 · public operator package

Version 0.6.0 is sealed. This immutable package contains 25 independent A1 tasks.
The separately controlled complete package contains these 25 plus 14 private
A1 tasks: 39 tasks, 35 mathematical families. Use one package, not both.
A full assessment also continues C003 through three fixed selfcheck rounds;
those rounds are separate from this A1 manifest and make 42 scored deliveries.

Download the companion harness-guide-v0.6.0.md, alignment-study-v0.6.0.json and
neutral-prompt-v0.6.0.txt from the same release. The guide specifies answer
structure, engineering returns, exact continuation prompts, attempts and import.
These are operator materials. Only complete generated messages, explicit
attachments, frozen parameters and permitted own history go to a candidate.
References, rubrics, expected truth, review plans and old answers are excluded.

## Prepare independent A1 contexts

Python 3.10+ and the standard library suffice. The controller never calls models.
Keep runtime declarations and every output outside this downloaded directory.
Freeze actual model and adapter identities, system prompt, supported parameters,
tools, network controls and native/broker/outer budgets before calls. Preserve
unknown settings as unknown. Local tools and preinstalled public dependencies
are allowed for every task; external retrieval and tool networking are forbidden.
Model-service and authentication traffic are recorded separately.

Use c003-180 for the one C003 initial task at10800 seconds, lean-90 for seven
other Lean tasks at5400 seconds, and the union proofs + answer-review +
theorem-extension + background-check + manuscript-completion for the17 other
public tasks at2700 seconds. Each budget group gets a new runtime and run.
The complete package's last union has31 tasks. Do not freeze all tasks at2700.

```sh
python3 tools/benchmark.py check
python3 tools/benchmark.py prepare --runtime ../runtime-10800.json --target c003-180 --out ../run-c003
python3 tools/benchmark.py request --run ../run-c003 --responses ../responses-c003 --slot MG-C003:A1 --out ../request.json
python3 tools/benchmark.py record --run ../run-c003 --responses ../responses-c003 --slot MG-C003:A1 --request ../request.json --response ../raw-answer.md --status ok
python3 tools/benchmark.py pack --run ../run-c003 --responses ../responses-c003 --out ../answers-c003.zip --origin external --declared-external-calls N
```

Replace N with all physical model calls, including failures and retries.
Only use ok for observed successful native/transport delivery. Runtime settings
for this neutral package use execution_track benchmark.local-tools-no-search/v1.
Use only supported output limits; budget.timeout_seconds must match the group.
The companion guide provides full runtime examples and the other target groups.

## Preserve the full original return

Save complete UTF-8 response bytes, beginning and end, self-assessment,
uncertainty, KEEP/FULL markers, named code blocks and explicit attachments.
Hidden reasoning is not required or reconstructed. Save actual request/response
and tool events, original stderr, known usage, every physical request and its
outcome. Original engineering workspaces, entry point, full import closure and
alignment table are sealed separately; record/pack do not collect them for you.
Where the issued task requires full named files, links or patches do not replace
that content. Do not invent missing self-assessment or repair an answer.

Seal at the first native terminal or fixed deadline, whichever occurs first.
Record native generation, stop, collection and CLI cleanup separately. Readable
ERROR is not SUCCESS. Honest incompleteness and mathematical errors are reviewed
from the first normal delivery; neither permits a quality retry.

The benchmark allows at most three effective model attempts under its fixed
acceptance policy. Output exhaustion consumes one; evidenced pure system faults
retain physical numbers and exclusion evidence. Keep this full ledger. The
portable exchange itself supports at most two transport attempts per slot and
does not implement that whole acceptance policy. Never relabel a later request
as the first or hide extra requests; use the companion formal-record guidance.

## Continue and retain C003

After the sealed C003 A1, continue three10800-second rounds with the separately
supplied exact neutral prompt. Use only this model's own visible history and
adjacent parent project. Do not provide references or reviewer feedback. Do not
stop on a self-claimed100percent. KEEP inherits the entire adjacent parent
response and file bytes; FULL resubmits the complete answer and required files.
Save all rounds and use the last prescribed delivery, never the best round or
a union. Later repairs do not replace A1 formalization credit.

Preserve fixed denominators and unknown slots. The full assessment uses
written35 / Lean35 / research30 and shared MC/RMC/SMC rules. This public subset
has no independently normalized benchmark total. AI review, real compilation,
semantic alignment and human approval are distinct; sealing changes none of
those recorded facts. Return all three A1 answer collections, original logs and
sealed engineering, plus the three-round C003 evidence. The evaluator recovers
its trusted external plan from the sealed source version and imports only a
pre-execution-frozen run. Instructions and hashes alone do not certify backend
identity, isolation or mathematical correctness.
