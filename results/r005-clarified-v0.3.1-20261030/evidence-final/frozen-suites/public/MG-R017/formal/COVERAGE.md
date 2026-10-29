# MG-R017 actual-object formal coverage

The version 0.4.0 main target is false. `ProductLifting.lean` supplies a complete counterexample on actual Stone ultrafilter spaces and an actual closed topological subspace. The three frozen case inputs, this coverage document and the exact Lean source are bound by `manifest.json`.

| Task / reference obligation | Encoded declaration or dependency | Exact scope |
|---|---|---|
| The stated lifting property | `Lifts.{u,v,w}` | The parameter has type `Type u`; the profinite surjection source and target independently have types `Type v` and `Type w`. Compactness, Hausdorffness and total disconnectedness are actual instances on every quantified space. |
| Both selected factors are profinite | `P`, `factor_profinite` | `P = Ultrafilter ℕ`, with the library's actual Stone topology. The theorem packages all three actual instances. |
| The factors have the full lifting property | `ultrafilter_lifts.{u,v,w}` | For every set A in universe u and arbitrary independent source/target universes v,w. It constructs a right-inverse choice on principal points, extends it continuously, and proves equality by density. No continuous choice is assumed. |
| Principal points are isolated | `pure_singleton_open` | Identifies `{pure n}` with the basic Stone open of `{n}`. |
| The principal diagonal is open | `diagonalPoints`, `diagonalPoints_open` | Actual range of `n ↦ (pure n,pure n)` in `P × P`, expressed as a union of open singleton rectangles. |
| Its closure is the complete diagonal | `diagonal`, `closure_diagonalPoints` | Both containments, using the closed Hausdorff diagonal and continuity of the diagonal map on the dense principal range. |
| The diagonal is not open | `diagonal_not_open` | An open diagonal would make every singleton open, forcing a compact discrete infinite space to be finite; the injection from ℕ gives the contradiction. |
| An actual profinite covering space | `coverSet`, `Cover`, `coverSet_closed` and the compact/T2/totally-disconnected instances | The union `(Dᶜ × {true}) ∪ (Δ × {false})`, as a subspace of `(P × P) × Bool`. It is proved closed and carries actual inherited topology. |
| The projection is a continuous surjection | `coverMap`, `coverMap_continuous`, `coverMap_surjective` | The witnesses are explicitly provided in the two cases `b ∈ D` and `b ∉ D`. |
| No continuous section exists | `coverMap_no_section` | A proposed section's second coordinate has false-preimage exactly Δ, making Δ open, contradiction. |
| Complete legal refutation | `counterexample`, `product_not_lifts` | `counterexample` retains factors' lifting theorem for arbitrary v,w and the specific small obstructing cover. `product_not_lifts` fails already for the concrete same-universe surjection with `f = id`. |
| Optional extremal-disconnectedness observation | `product_not_extremallyDisconnected` | D is open but its closure is not; this is proved additionally and is not used as an unproved replacement for the explicit cover. |

The Stone background endpoints are imported from pinned Mathlib: `Ultrafilter.topologicalSpace`, `ultrafilter_isOpen_basic`, `ultrafilter_isClosed_basic`, `ultrafilter_compact`, `Ultrafilter.t2Space`, the actual `TotallyDisconnectedSpace (Ultrafilter A)` instance, `denseRange_pure`, `Ultrafilter.pure_injective`, `Ultrafilter.extend`, `continuous_ultrafilter_extend`, and `ultrafilter_extend_pure`. The reference's Boolean-cube paragraph is an alternative explanation of these standard background endpoints; a separate cube embedding and its closed equations are **not** authored in this case. No coverage of that alternative implementation is claimed. The library proves the needed endpoints directly by ultrafilter convergence and topology.

No source or olean from MG-R001–MG-R010 is a dependency. No OET theorem, build output or unpublished manuscript is used. `Mathlib.Topology.ExtremallyDisconnected` is a precise background module; no `import Mathlib` umbrella appears. The proof never uses Gleason's equivalence as an assumed certificate for the required concrete obstruction.

The common verifier compiles this module from copied source in a fresh case-only output, then audits every `MathGauge` declaration including private and generated names. Only `propext`, `Classical.choice` and `Quot.sound` are permitted. Kernel acceptance does not establish human approval or empirical difficulty, and the candidate is not required to submit Lean. Independent mathematical review and human review remain separate metadata.
