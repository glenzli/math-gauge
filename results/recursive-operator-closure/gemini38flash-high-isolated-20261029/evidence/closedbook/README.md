# Gemini 3.8 Flash High: formal closed-book comparison

Antigravity CLI 1.4.9 ran one new conversation in a fresh temporary data directory. Model: `gemini-3.8-flash-high`; effort: `high`. No upgrade was performed by the isolation agent.

The first and only user message was the unchanged task. Input SHA-256: `779bf275a6184fb848a12f3d72089a21d4704513512e10323aa48d4ee462cecd`. No hints, answers, scoring, history, Lean source or follow-up feedback were submitted.

A documented custom primary agent selected with `--agent text-only` configured `tools: [finish]`, a local response-ending tool. The platform also retained its built-in task bookkeeping capability; any manage_task steps are listed in run-metadata.json. No external retrieval tools were used. Its Markdown body was empty. The exact file is `runtime/agent.md`. A separate paired capability test requested web search: the finish-only configuration made search unavailable, while adding search_web produced a completed search. This test did not use the math problem. The CLI init.tools array is the global registry in this version and does not reflect the custom primary-agent allowlist; raw init is retained without alteration.

The operating-system policy in `runtime/outer.sb` denied all user-home data except the exact OAuth/installation files and CLI binaries needed for startup; it also denied other temporary directories, including the prior diagnostic answer and both canary contexts. User-home writes and outbound localhost connections were denied. The language server ran in the newly isolated agy PID, not an existing service. `output/process-evidence.json` captures executable names and sockets without process-argument tokens.

The actual file-open probe read the copied task successfully and returned EPERM for 12 forbidden paths. The actual agy process was separately checked against the same 1 positive and 12 negative paths. See `runtime/probe-result.json` and `output/actual-process-sandbox-check.json`.

Raw stdout is `output/events.ndjson`, also linked as `output/stdout.ndjson`. Raw stderr is `output/stderr.txt`. `output/response.md` is exactly the final result.response UTF-8 text, with no added text or newline. `output/result-event.json` is the exact original result-event line. Raw files are read-only and hashed in `runtime/raw-file-manifest.json`.

The earlier run is preserved separately as a tool-mismatch diagnostic. The decision to fix the search-tool gap and run this comparison was recorded before that diagnostic emitted its final answer. No mathematical output was reviewed by the CLI/isolation agent or used to change the problem, prompts or sample selection. See `runtime/attempt-ledger.json` and the diagnostic `runtime/tool-mismatch-decision.json`.

Do not archive state/; it is private runtime storage. Only credential symlinks were used, and all links were removed after the completed run. The deliverable archive uses a file whitelist and contains no state directory or credential links.

Conversation: `e15847e5-63b2-4653-a53b-c2dd90c139ce`. Reported model duration: 521.090144 seconds. Host wall time: 538.760 seconds. Usage: `{"input_tokens":68372,"output_tokens":74488,"thinking_tokens":68896,"cache_read_tokens":0,"total_tokens":142860}`. Observed external tool steps: 0.
