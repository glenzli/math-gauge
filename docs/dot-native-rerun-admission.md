# Dot (261125): native admission and profiles

## Mathematical-profile coverage

The main-score admission and the mathematical profile use separate, source-bound
reviews. The independently reviewed profile for Dot (261125) is added by
[the native profile component](../protocol/dot-native-profiles.md), covering both
the first-answer and revision-inclusive stages in the current 1.2/1.3 editions.
It does not copy Dot (261108), infer subjective grades from aggregate scores, or
change existing main-score judgments. Formalization projects the whole original
Lean SMC, including semantic audits, initial engineering and all three prescribed
self-check rounds; later repairs never fill the initial engineering slot.

主榜与数学画像分别审核。Dot (261125) 的本轮实际答卷已按相同标准独立评审，
由[原生画像组件](../protocol/dot-native-profiles.md)接入当前1.2／1.3的首答及含续答
两个阶段；不沿用Dot (261108)的旧画像，不由总分推算主观评审档，也不改已有主分。
形式化轴使用原始完整Lean SMC，覆盖语义审计、初答工程与固定三轮自查；后续修复
不回填初答工程。全部新增画像审核为观察后的AI评审，人工数学审阅仍待完成。

This gate checks a new Dot source package for one logical run; it does not
publish a result or infer native transport from controller artifacts. Use it on
the **private** evaluator checkout:

```
python3 -m math_gauge.dot_rerun_sources --private-root PRIVATE_RECORD_DIRECTORY \
  --dataset FROZEN_COMPLETE_CANDIDATE_DIRECTORY PRIVATE_MANIFEST.json
```

Manifest schema `math-gauge.dot-native-rerun-sources/v1`; model identity
`dot-20261125`; original task version **1.0.0**. The validator pins the
complete dataset identity, verifies package integrity with the installed
candidate projection reader, and compares every selected call's one-user-message
request to the original task. This verifies byte bindings, not provider
authentication or the assistant's independent observation that the backend
accepted a particular request. Backend and effort stay unknown. No attempt is
converted to a CLI result or marked human-approved.

All artifact references use exact `path`, `bytes`, and `sha256` descriptors
relative to the private root. Put original native terminal text and workspace
answer into distinct artifacts. A normalized observation or review wrapper
must point to its retained source; the wrapper itself is not an original
terminal, authorization, or mathematical judgment. The evidence-level
selections are:

* `native_inline`: separately retained exact captured native final text.
* `observed_inline_bound_authored_file`: full native final was observed and
  compared against exact independently retained, candidate-authored bytes.
  This is not byte-certified native transport.
* `candidate_designated_file`: C003 only, exact file bytes, same-context native
  terminal and candidate designation, and retained user authorization. A short
  or partial inline terminal remains what was actually received.
* `forced_content`: same physical call's original cutoff artifact, with no
  assertion of normal delivery. The score gate must still adjudicate points.
* `nondelivery`: a policy-rejected physical call; no native answer or normal
  continuation parent is attributed to that call. A separately authorized,
  unchanged guarded replay may be selected only on observed normal final.
  Its own second rejection would remain nonfinal.

The manifest maps exactly one slot row per release A1 and C003 R1–R3 in
`slots`. Each is `{physical_calls, selection, review, replay}`; replay is null
for A1. A physical call is `{request, context_id, observation, status,
terminal, archive, designation}`; absent artifacts are explicit nulls.
An observation wrapper binds slot, context, request digest, status and the
three nullable artifact digests to its original event or observation source.
A mathematical review wrapper contains the source, observation digest,
response digest (nullable for nondelivery), `kind: "ai"`, and
`human_review: "pending"`. Designation binds context, exact answer descriptor,
and the retained designation source. Authorization binds explicit scope,
original source reference and `post_observation: true`. Keep all these
contract wrappers private, including their source references.

Each slot retains physical call order and original statuses. The six
first capture-loss calls, two Lean delivery recoveries, three distinct
subsequent capture-damage recaptures and any documented additional recovery
are scoped and separately authorized. Keep every prior failed or damaged
capture without diagnosing the candidate output itself as damaged. Do not
report two mathematical answers or choose by grade. C003 retains the
unselected original trajectory separately; each newly selected round binds
its own dispatch, exact fixed invitation, and immediate selected parent.

## Score and publication requirements

Admission requires a completed and explicitly selected public/private package.
The validator uses the frozen release, historical Dot package and shared
score formulas. The public leaderboard applies the following requirements.

1. Bind 39 original and three fixed round judgments independently per
   condition. The old native input owner hardcodes the historical 0.6.0
   identity, maps both conditions to one review bundle, and insufficiently
   distinguishes selection after capture loss from a normal first attempt.
   Adopt a new source identity with the provenance gate above and invoke
   shared score arithmetic; keep the old reader untouched. The selected
   ordinary submission and C003 engineering/diagnosis status still need
   independently validated judgments. Do not copy provisional totals.
2. In 1.2, bind that exact source to the existing neutral 80/20 policy and
   compute selection from unrounded first-answer losses. Do not run another
   call for the rejected request. A case without a native parent must have a
   settled no-parent disposition and reviewed source-bound scoring treatment,
   not fabricated replay material. Verify combined scoring privately and
   publish only an approved public projection with opaque private bindings.
3. In 1.3, adopt the reviewed independent-research trajectory separately under
   current item-specific contracts. Derived 1.3 score must consume the exact
   newly validated 1.2 baseline, not historical Dot's or a hand-entered total.
   Retain fixed weights and unknown-vs-zero semantics. Compare only after
   explicit selection; do not modify historical displays.
4. Use the actual recorded dispatch clock, not the label-derived date; never
   expose private case inventories, candidate bytes, evaluator notes, genuine
   execution IDs, or unsanitized descriptors in the public row. Add verified
   resource evidence only where independently observed. An absent or invalid
   paired proof is not a pending placeholder to rank.

## Additive 1.2 / 1.3 activation

The old native run is never mutated. The Dot-specific checker uses the
existing 0.9.0 scoring mathematics, neutral 80/20 and item-policy projectors.
The [current selector](../results/edition-admissions/v0.1.0/dot-20261125.json)
binds `native-source.json`, `neutral-public.json`, and
`independent-research-public.json` in the selected evidence replacement.
The 1.3 source binds all three exact selected 1.2 report bytes. The historical
Dot run and archived 1.3 comparison baseline remain available.

Private prerequisites: completed native source ledger and selected physical
observations; independent case/reliability/engineering judgments and submission
review for each of the two distinct conditions; three exact C003 round
snapshots per trajectory; actual neutral replay inputs, observations and
review follows for each selected loss; validated MT001 trajectory, exact
evidence registry, checkpoint reviews and separate E addendum. The 1.2 private
checker replays the shared scorer and 80/20. The 1.3 private checker derives
T/C from exact checkpoint judgments and checks every quoted byte. Unknown
first-condition scores are not silently filled from late technical calls.

For additional damaged captures, keep the original archive and independently
observed status, explicit post-observation authorization scoped to that slot,
and the unchanged replacement request. A normal observed final may be
matched to an exact candidate-authored file, but that is not a byte-certified
transport receipt. The guarded initial policy retry is one exact-request
exception only; prior refusal and later neutral cutoff remain nonfinal.

```sh
python3 -m math_gauge.dot_rerun_scoring --public-root PUBLIC_CHECKOUT \
 --private-root PRIVATE_CHECKOUT --dataset FROZEN_COMPLETE_CANDIDATE_DIRECTORY \
 PRIVATE_BASE_INPUTS_DESCRIPTOR.json PRIVATE_NEUTRAL_MANIFEST_DESCRIPTOR.json \
 PRIVATE_RESEARCH_REGISTRATION_DESCRIPTOR.json
python3 scripts/render_results_site.py --out ISOLATED_OUTPUT
```

The verifier recomputes the opaque paired receipt digest. Its three private
arguments are retained byte descriptors, not paths embedded in the public
source. The first points to `math-gauge.dot-native-rerun-score-inputs/v1`
(`source`, two `conditions` sharing the exact task policy, and six
`private_scores`). The last points to
`math-gauge.dot-native-independent-trajectory/v1` (actual context, original
source root, review, manifest, evidence registry, extension review, and three
independently retained round observations). Do not activate against provisional
totals or before private verification passes. Resources without auditable
evidence stay unknown.
