# P002 public Lean port

The three source files below were fetched through the connected GitHub file API from OpenAI's public repository at fixed commit `f9e8bc5b38b6e212696e8a30e3e91517af887bbd`. They are licensed under Apache-2.0; the full license is preserved at `../external/LICENSE`. The upstream root at that commit has no NOTICE file (separately inspected by the root reviewer).

Original bytes are preserved in `../external/upstream/` and their Git blob hashes are verified. The build uses isolated copies under `MathGauge.PublicProof.Torus.Borrowed`; the source modules do not import OET or any unpublished mathematics.

| Upstream module | Git blob | Scope |
|---|---|---|
| NavierStokes/DiophantineGraph.lean | b8372e829aeb2b15ee4b9c98e48fdb16497b7dd6 | Elementary quadratic arithmetic |
| NavierStokes/TorusInverse.lean | 4ab23593f44933403cc852ec7cf5065728ff6ca7 | Rapid series, genuine derivatives, periodic descent, fixed-direction inverse |
| NavierStokes/SmoothFourierData.lean | 1de68214bc1f62781e3fbaac44f294a25d97886d | Actual integral coefficients, decay, Mathlib torus identification and Fourier reconstruction |

The upstream lockfile targets Lean/Mathlib v4.34.0-rc2, Mathlib revision `85e3a25e006c35636f0e53b0e9296caca2685bc0`. This case is ported and freshly checked on the repository's pinned Lean 4.29.1 and Mathlib `5e932f97dd25535344f80f9dd8da3aab83df0fe6`; the default suite toolchain is unchanged. Upstream full-project compilation is not claimed.

All three copies receive provenance headers and module/namespace isolation. DiophantineGraph otherwise preserves its proof text. TorusInverse qualifies ContinuousLinearMap application lemmas, explicitly imports the complex finite-dimensional instance, and expands product/constant integral rewrites into typed calculations for the older elaborator. SmoothFourierData reduces a congrArg lambda before rewriting and expands two constant-integral rewrites into typed calculations. These are proof/API compatibility repairs, with no altered theorem hypotheses or conclusions. Exact original-to-port diffs are stored in `../external/port-diffs/`.

All other MathGauge modules are new case proofs. In particular, CubicBound and CNorm establish the cubic lattice majorant and actual complete m+4 norm estimate; they do not treat the upstream m+5 statement as the requested theorem. The general-alpha classification, exact real-order Sobolev criterion, Dirichlet sharpness, bad smooth forcing, and native torus bridges are new proofs. Root agent supplied the independently compiled Necessity helper; the case owner integrated and checked its actual-function consequence.
