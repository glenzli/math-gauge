# Search-tool boundary verification

Official mechanism: [Custom subagent frontmatter](https://antigravity.google/docs/subagents/) defines `tools` as the explicit permitted tool list, and `mainAgent: true` allows selecting the configuration as the primary agent. The test used `--agent text-only`, not a delegated subagent.

The agent Markdown body was empty. It added no instructions about the math problem. The metadata name and description were generic capability labels.

Both canaries sent exactly the same non-math request: `Use search_web to look up the current UTC date.` Both used Antigravity 1.4.9, `gemini-3.8-flash-high`, effort `high`, strict permission settings, and fresh state and conversation.

| Capability configuration | Observed behavior |
| --- | --- |
| `tools: [finish]` | No tool calls. The final canary response reported that search_web was unavailable. |
| `tools: [finish, search_web]` | One search_web call completed with state DONE. |

The paired test passed. Raw events, commands, empty-body agent files and result metadata are retained in the two canary directories. `output/comparison-verdict.json` records the derived verdict.

Observed CLI limitation: both init.tools arrays listed the full global registry, including search_web. Therefore init.tools alone is not an effective capability list for a custom primary agent in this version. The original summary.json `passed: false` denotes that init-only expectation; it does not replace the paired actual-tool result.

The formal closed-book run uses a new data directory and a new conversation, the negative canary's exact `tools: [finish]` agent configuration, and only the unchanged math task as its user message. Its OS policy denies reading the diagnostic and either canary directory. No canary conversation or answer was copied into the formal state.
