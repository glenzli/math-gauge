# Sol engineering handoff

Staging only. No repository edits, commits, pushes, tool upgrades, credential copying, or new live model inference occurred.

## Exact integration whitelist

Copy only the nine relative files in `delivery-manifest.json` from `delivery/`, or apply `sol-engineering.patch`. The three edited runner/demo files have recorded original hashes; all matched the current parent repository when packaged. No copied case data, historical results, baseline files, validation outputs or this handoff report enter the patch.

## Changes

- `catalog.py` validates optional string `candidate_instruction`; absence keeps the legacy reminder; empty emits exactly the task UTF-8 bytes with no prefix/separator. Request task strings preserve line endings. Other runner responsibilities stay unchanged.
- Legacy transport tests and synthetic three-track demo use `archive/legacy-v0/public`.
- Active research tests enforce MG-R001..010, empty instruction/attachments, evaluator-independent candidate projection and the original recursive prompt SHA-256 `779bf275a6184fb848a12f3d72089a21d4704513512e10323aa48d4ee462cecd`.
- The CLI helper is preparation/probe/audit tooling, not a mathematical-run launcher. An explicit AGY `models` inventory preflight has closed stdin and checks new files beneath fresh `state/antigravity-cli`; it has only been synthetically tested here. Omitted directory flags in AGY short help are recorded as unadvertised and require that actual preflight. Requested model/effort remain distinct from observed backend metadata.
- CLI identity/help records, explicit paths/deny roots, exact task transport, credential symlink lifecycle, fixed delivery whitelist and immutable prepared-artifact hashes are built into the helper. Run supervision, PID identities/all workers, effective tool canaries, raw model metadata and attempt completeness remain manual gates; audit always reports `isolation_certified: false`.

## Final validation

All commands ran in the staging workspace, using the final engineering source and current parent ten-case data:

- `python3 -m unittest discover -s tests`: PASS, 43 tests in 6.009 s. Includes 21 legacy runner tests, 4 active-suite tests, 14 synthetic helper tests and 4 existing finite witness tests.
- `python3 -m math_gauge validate`: PASS, 10 cases, 0 human approved, suite SHA-256 `92e87ba5f52b06f839e1a440c2983ce976e1bb3bd429eda0c2d16048e061db4b`.
- `python3 -m math_gauge validate --suite archive/legacy-v0/public`: PASS, 15 cases, 0 human approved, suite SHA-256 `b659c39ebe3cca1651b9dd7d33e28f4b11ffeae0b010b691093ef7b5d21f169b`.
- `python3 examples/demo.py --out demo-validation`: PASS; three archived tracks replayed, model-comparison eligible count 0.
- `python3 -m py_compile math_gauge/catalog.py examples/demo.py tests/test_runner.py tests/test_research_suite.py scripts/isolated_cli/prepare.py scripts/isolated_cli/probe.py tests/test_isolated_cli.py`: PASS.

No formatter executable/module was available; source was manually formatted and syntax-checked. No formatter or other tool was installed/upgraded. No Lean fixtures changed in this patch, so no Lean build was run.

## Actual macOS smoke and its limits

`macos-policy-smoke/elevated-probe-report.json` records a real sandbox-exec run with generated outer.sb, an inert fake CLI identity, one synthetic task, and three synthetic negative files. The first restricted attempt returned exit 71 (`sandbox_apply: Operation not permitted`) and is retained in `macos-policy-smoke/report.json`. Normal approved permission escalation then ran the same probe command with the same policy successfully: exit 0, task SHA-256 `2d369b56b57dc959f80ac98f84a7d0a84a897f2a8c24f0e9b567fd3e604b55e5` readable, reference/history/prior_run files all denied with EPERM (errno 1). No bypass or policy weakening occurred.

This proves this generated macOS file policy works on synthetic fixtures. It does not validate actual AGY/Codex startup, model inference, actual parent/worker PID isolation, model availability or live effective tools. No real model CLI, credential files or network inference were involved. `macos-policy-smoke/audit.json` reports artifact checks passed, only open-probe evidence present, missing PID/preflight evidence, no state included, and no isolation certification.

## Documentation sources verified

- https://antigravity.google/docs/subagents/ was opened; it documents workspace `.agents/agents/` discovery, the explicit `tools` allowlist, `mainAgent` selection and empty Markdown-body system prompt boundary. Historical 1.4.9 effective-capability claims separately cite the repository paired canary and raw events.
- https://learn.chatgpt.com/docs/developer-commands#codex-exec was fetched through OpenAI Docs; it supports noninteractive exec and JSON events. The document explicitly makes availability of additional isolation switches depend on the inspected real binary and strict startup, rather than deriving them from a generic web page.

## Parent integration

Apply/copy only the whitelist, then run the repository-required unittest and validate gates once on the integrated tree. Reuse the recorded macOS smoke evidence only while probe.py and the generated policy mechanism remain unchanged. Any actual future client/model run still needs the documented machine-specific gates and separate authorization for live inference.
