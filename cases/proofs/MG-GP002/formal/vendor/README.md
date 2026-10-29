# Reused public Lean source

`external/` preserves the parent MG-P002 public-port originals, license, provenance and exact port diffs. `PARENT-PORTING.md` is the historical parent report: its `../external/` paths resolve in that parent layout and correspond here to `external/`.

The current build imports only the 19 explicit, byte-identical parent modules listed in ../SOURCE-CLOSURE.json plus this group's new MathGauge.GP002 modules. Parent module bytes are frozen here. The previous parent verification is development context only; this group will receive its own fresh compile and full local-declaration axiom audit. No parent score or human approval is inherited.
