# Terra selected engineering-source kernel verification

The exact R2/R3 engineering source is Main SHA256 `58f4da3f765069b192b99c3923728b5a1ef0079a2a82e792561f0c1cabb88682` and raw alignment SHA256 `e4cbc1bd81c3abaf8feb57fc8ee616eb054a6b8967d3f4fa7e3f90e41ce1e46e`. R2 and R3 contain identical selected bytes; one fresh kernel verification covers that identity.

- Source/alignment format: passed with original bytes and version0.1.1 unchanged.
- Compilation: all seven modules passed: five reachable original frozen backgrounds, the selected Main, and the generated complete audit. The sixth supplied background is bound input but not imported or counted compiled.
- Axiom audit: all565 declarations by actual module origin passed. Only Classical.choice, Quot.sound and propext occur; no unexpected axioms.
- Mapping inventory: all197 reference occurrences,170 distinct references across92 original alignment items exist in this actual audit inventory.
- Isolation: the new original-Main/original-alignment/reference/engine denial probes and the shared compiler's own positive/negative probes passed. No unisolated fallback, candidate cache, script, network, runtime state or credential use.

No old Terra Main compilation or Gemini report was reused as evidence for this new Main. Original source/JSON, old results and scoring policy remain unchanged. This review made zero model calls and sent no candidate feedback. Mathematical completion and human approval remain separate and are not assigned here.
