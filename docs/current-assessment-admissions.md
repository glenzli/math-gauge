# Native current-assessment admissions

`math_gauge/current_assessment_admissions.py` owns new models whose first
mathematical assessment uses benchmark 1.1.0. This is a separate lifecycle from
`theorem_extension_calibration.py`, which reinterprets retained older judgments.
Neither owner executes a candidate or changes scoring arithmetic.

The acquisition record keeps its actual 1.0.0 task and execution identity and its
original shared-scoring component reports. An explicit
`initial_assessment_edition: "1.1.0"` must agree with the retained first-assessment
source freeze and its TX policy digest. A later wrapper cannot convert an old
research judgment into a new initial assessment.

`benchmark.json.current_assessment_admissions` maps new model IDs to exact
public manifest descriptors. It is the only additional field separated from the
sealed source-edition contract. Historical model IDs and native-source identities
cannot be replaced. Source-only selection remains unchanged; current selection
is its disjoint union with validated initial admissions.

The public manifest binds the original record, all six canonical reports, the
public task projection, the current TX policy, initial-review wrappers, and opaque
private input/manifest digests. Wrappers reference unchanged original A1 reviews:
B, R and answer digest must agree exactly. They bind the standard and explicitly
record metadata-only projection with zero new candidate calls. There is no old R,
no base-report reassessment and no score overlay. Private validation checks all
six TX cases and the paired original records/reports using existing validators.
AI review remains distinct from human approval.

The current view can change only version/provenance metadata; all mathematical
values remain equal to the validated shared-scoring reports. Public-only readers
do not manufacture private judgments. `validate_private` is a separate required
paired admission gate.

`current_results.py` composes harness-specific source validation with either the
historical reassessment owner or this initial-assessment owner. Profile sources
likewise use exactly one of `source_calibration` and
`source_initial_assessment`; initial profile evidence binds the original inputs,
content judgments, complete goals and answers without borrowing old R scores.

The historical model list excludes new admissions. A new model's old-edition
URL renders an explicit “not evaluated in this edition” notice and a return link;
score and answer controllers are not started for that absent result. Shared
presentation code does not imply historical participation.

All initial admissions bind the same frozen historical display and cost source.
The historical display must contain exactly the sealed cohort, and its six views
per model must equal the original reports after the existing harness-label display
projection. Current metadata cannot alter historical source hashes. Timing and
cost consumers resolve current models through explicitly selected record paths;
unknown extra cost models remain errors. Existing release files, transition,
calibrations and source edition are not rewritten.
