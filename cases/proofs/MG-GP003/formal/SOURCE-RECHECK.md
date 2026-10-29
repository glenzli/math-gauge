# MG-GP003 source-hypothesis recheck

AI source review, 2026-10-30. Mathematical source status and Lean completion are distinct.

Primary source: [Mazza–Voevodsky–Weibel, author PDF](https://sites.math.rutgers.edu/~weibel/MVWnotes/prova-hyperlink.pdf). Re-read online: printed pp. 83–84 and 183–187 (PDF pages 95–96 and 195–199). Local frozen PDF hash also rechecked: `bb07651d8cc1b38f2552204e6c777cc7570c19e35d779987907a44efc2669486`. Parent immutable source metadata remains in MG-P003/source-evidence.json; no candidate/source file changed.

- Proposition 11.1 and Theorem 11.3 allow an arbitrary field and finite point sets. “Smooth semilocal” means the neighborhood limit of smooth schemes, not a finite-type claim about the localization itself.
- Lecture 22 explicitly does not require a perfect field. Its running assumption is homotopy invariance with transfers. The convention preceding Lemma 22.10 uses a finite set of points of a smooth quasi-projective variety, without an ambient closed-point restriction.
- Lemma 22.10 handles finite fields separately by transfers after finite extensions, and requires shrinking the first cover member. Corollary 22.11 takes the resulting neighborhood limit.
- Lemma 22.12 states the target semilocal Zariski comparison; its proof uses 11.1, 22.9, 22.11 and induction on the closed points of the localized scheme.

Conclusion: the cited mathematical theorem covers the task's arbitrary-field and nonclosed-point scope. The remaining S5 gap is formal implementation of the actual transfer geometry and its canonical comparison, not an identified defect or unproved claim in the mathematical reference. This source review is not a Lean proof, independent human approval, or candidate-model result.
