# R004 proof-route closure

Date: 2026-10-29. Independent AI review by the R005–R007 author; this reviewer did not author R004. Scope is only the final R004 wording change and its mathematical consequences. Earlier review reports remain unchanged.

**Verdict: closed.** The prescribed Laplacian-led construction route has been removed. No new mathematical defect, assumption or mandatory method was found. Integration is justified for the four files bound below, together with the earlier functional review and closure.

At task.md:19, bounded chain contractions and bounded linear right inverses of the \(L_j\), with norm control, are now explicit outputs. The sentence does not require constructing either output through the other. The reference's formula at lines 69–85 is expressly one possible construction; its distinct construction at lines 41–51 remains available.

The right-inverse wording preserves the actual target. For every degree, including both endpoints, reduced acyclicity gives
\[
\ker d_j=\overline{\operatorname{ran}d_{j-1}}.
\]
If \(L_jx=0\), positivity gives
\[
0=\langle L_jx,x\rangle
=\|d_{j-1}^*x\|^2+\|d_jx\|^2.
\]
Thus \(x\) belongs to that closed range and is orthogonal to it, so \(x=0\). Consequently \(L_jG_j=I\) implies
\[
L_j(G_jL_j-I)=0,\qquad G_jL_j=I.
\]
This also covers zero spaces. No closed-range hypothesis was used to prove injectivity or the equivalence of right and two-sided inverses. The reference correctly uses closed ranges only for the conditional existence theorem and its norm estimates.

The original length-one complex on complex \(\ell^2\), with \(d=\operatorname{diag}(1/n)\), still has both reduced records zero: \(d\) is injective and its range contains every finitely supported sequence. A bounded contraction would satisfy \(s_1e_n=ne_n\). A right inverse of \(L=\operatorname{diag}(1/n^2)\) would satisfy \(G e_n=n^2e_n\). Either contradiction to boundedness refutes the universal conjunction. The reference at line 91, the unchanged rubric's completion policy, and the refreshed design continue to accept any complete legal counterexample; the closed-range classification, the diagonal example and the displayed construction formula are not mandatory.

The adjusted reference passages at lines 23, 33, 69 and 101 agree with this conclusion. The rubric is byte-identical to the previously reviewed version. Author receipt assertions were checked against the actual files and the calculations above, not used as mathematical evidence.

| File in functional/MG-R004 | Reviewed SHA-256 |
| --- | --- |
| task.md | ff03d4b674680281bde97e73b5316f01fc4837fa5c58625eb0dc54706ae2650a |
| reference.md | 6277ce8d8c50683c24d97b37784c237adedd00f97e17dd07d326e446c965e0b3 |
| rubric.json | 4150650a577d363f4d76e3ec681836dd10ce8b38eb7b4c38b77901c59b6fd7b3 |
| design.json | 39fd25ca549ec3f746449e78f3857b42d35d415c591f57f06a9a3d0ba661238f |

All four hashes were stable through report creation and match r004-author-route-repair.json. This is a narrow AI mathematical closure, not a new audit of unchanged cases, a candidate-model trial, a Lean compilation or human approval. The author's frozen pending-review wording is author-stage metadata; this separate report supplies the subsequent independent closure.
