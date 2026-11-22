import Ch02.MatrixCore
import Ch02.MatrixBounds
import Ch02.ChainBounds
import Ch02.ChannelDecoupling

/-!
# Chapter 2 (`02-operator-bounds.md`) Complete Lean 4 Formalization Entry Point

Imports all target modules formalizing Chapter 2 of *The Operator Evolution Theory*
(historical snapshot `02-operator-bounds.md`):
- `Ch02.MatrixCore`: Gauge matrices, display convention, ordered products, finite operator
  chains, actual recursive domains, and index paths.
- `Ch02.MatrixBounds`: Global/restricted Lipschitz & co-Lipschitz certificate families,
  single-component degeneration, domain monotonicity, entrywise infimum monotonicity,
  two-step composition laws, co-Lip vanishing criterion, and pairwise perturbation bounds.
- `Ch02.ChainBounds`: Stepwise chain data, finite-composition Lip/co-Lip bounds,
  zero-step identity certificates, and path-based zero/positivity product criteria.
- `Ch02.ChannelDecoupling`: Component channels, row/column/diagonal decoupling,
  single-channel Lipschitz constants and counterexample, two-sided diagonal bounds,
  and positive co-Lip distinguishability preservation & zero-distance reflection.
-/
