# Fixed transfer-profile third-party attribution

The Math Gauge author profile `lean-4.34.1-motivic` binds these external libraries:

| Library | Exact source | License text retained here |
| --- | --- | --- |
| Motivic Cohomology, kangxyz and contributors | [kangxyz/motivic at a6805c4a87cdfd7717dd7a94039246a167f15380](https://github.com/kangxyz/motivic/tree/a6805c4a87cdfd7717dd7a94039246a167f15380) | [LICENSE-Motivic](LICENSE-Motivic), copied unchanged from that commit |
| Aglib, kangxyz and the contributors named in individual source files | [kangxyz/aglib at 2c34f185fa859e862661f939cd216b07bcccfb26](https://github.com/kangxyz/aglib/tree/2c34f185fa859e862661f939cd216b07bcccfb26) | [LICENSE-Aglib](LICENSE-Aglib), copied unchanged from that commit |

Both retained license files have SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`.
The upstream Git blob is `8dada3edaf50dbc082c9a125058f25def75e625a` in both repositories.
The libraries remain external fixed dependencies; their source trees and compiled
caches are not vendored into Math Gauge.

The following eighteen local GP003 source modules are explicitly Apache-2.0.
They contain Math Gauge author proofs, native fixed-library interfaces and
adapted auxiliary arguments. Each source retains its author copyright,
the fixed Motivic revision and a prominent modification/attribution notice.
Any adapted upstream portions retain kangxyz and Motivic Cohomology
contributors copyright; the repository MIT license does not replace it.

| Local source | Scope |
| --- | --- |
| [S5FiniteClosedPointReduction.lean](../../../cases/proofs/MG-GP003/formal/MathGauge/GP003/S5FiniteClosedPointReduction.lean) | finite closed-specialization reduction preserving every original point |
| [S5SimultaneousUniversal.lean](../../../cases/proofs/MG-GP003/formal/MathGauge/GP003/S5SimultaneousUniversal.lean) | simultaneous finite-point projection, frame and retained presentation geometry |
| [S5SimultaneousFinite.lean](../../../cases/proofs/MG-GP003/formal/MathGauge/GP003/S5SimultaneousFinite.lean) | coprime scalar extensions and finite-point geometric assembly |
| [S5SiteBridge.lean](../../../cases/proofs/MG-GP003/formal/MathGauge/GP003/S5SiteBridge.lean) | ordinary big/small Zariski sheafification and literal unit comparison |
| [S5ZariskiKernel.lean](../../../cases/proofs/MG-GP003/formal/MathGauge/GP003/S5ZariskiKernel.lean) | actual unit kernel, Zariski-local zero and the transfer quotient |
| [S5ZariskiComparison.lean](../../../cases/proofs/MG-GP003/formal/MathGauge/GP003/S5ZariskiComparison.lean) | quotient and ordinary Zariski sheafification comparisons |
| [S5TransferSectionLift.lean](../../../cases/proofs/MG-GP003/formal/MathGauge/GP003/S5TransferSectionLift.lean) | the common transfer restriction factor and section lifting |
| [S5GenericRepresentative.lean](../../../cases/proofs/MG-GP003/formal/MathGauge/GP003/S5GenericRepresentative.lean) | actual section representatives and common generic refinements |
| [S5InfiniteAffineMoving.lean](../../../cases/proofs/MG-GP003/formal/MathGauge/GP003/S5InfiniteAffineMoving.lean) | simultaneous original-presheaf moving over infinite fields |
| [S5IntegralComparison.lean](../../../cases/proofs/MG-GP003/formal/MathGauge/GP003/S5IntegralComparison.lean) | integral affine kernel and section comparison |
| [S5FiniteScalarMovingDescent.lean](../../../cases/proofs/MG-GP003/formal/MathGauge/GP003/S5FiniteScalarMovingDescent.lean) | finite scalar restriction, trace and descent |
| [S5FiniteFieldMoving.lean](../../../cases/proofs/MG-GP003/formal/MathGauge/GP003/S5FiniteFieldMoving.lean) | simultaneous moving over finite fields |
| [S5AllFieldMoving.lean](../../../cases/proofs/MG-GP003/formal/MathGauge/GP003/S5AllFieldMoving.lean) | the all-field simultaneous producer |
| [S5DisjointAssembly.lean](../../../cases/proofs/MG-GP003/formal/MathGauge/GP003/S5DisjointAssembly.lean) | finite actual correspondence coproduct assembly |
| [S5DisjointGeometry.lean](../../../cases/proofs/MG-GP003/formal/MathGauge/GP003/S5DisjointGeometry.lean) | clopen integral-component geometry |
| [S5AffineComparison.lean](../../../cases/proofs/MG-GP003/formal/MathGauge/GP003/S5AffineComparison.lean) | affine comparison across integral components |
| [S5AmbientComparison.lean](../../../cases/proofs/MG-GP003/formal/MathGauge/GP003/S5AmbientComparison.lean) | original ambient open-image and neighborhood transport |
| [S5Complete.lean](../../../cases/proofs/MG-GP003/formal/MathGauge/GP003/S5Complete.lean) | the original big/small Zariski-unit endpoints |

The two simultaneous-geometry modules and `S5AmbientComparison` explicitly
identify the adapted upstream geometry/open-image source in their headers.
The remaining modules identify their native-interface and adapted-argument
source in the same fixed snapshot. Imports, exact local source hashes and
the full dependency closure are recorded by the author manifest and compiler
report. Individual upstream Aglib notices, including legacy notices naming
Quillen K-theory contributors where present, are retained by those external
sources, which are not copied into Math Gauge.

Motivic's fixed snapshot also records unrelated source-license exceptions in its
[upstream imported-source notices](https://github.com/kangxyz/motivic/blob/a6805c4a87cdfd7717dd7a94039246a167f15380/docs/provenance/imported-THIRD_PARTY_NOTICES.md).
This attribution does not relicense those exceptions. The inspected transfer,
local-vanishing and sheafification-HI dependency closures contain no Milnor K2
source leaves; the final compiler report separately binds every module actually
used by GP003. No unrelated upstream source archive is redistributed.

Mathlib and the other eight transitive packages keep their own upstream licenses
and notices at the exact revisions in [lake-manifest.json](lake-manifest.json).
This document records source ownership and license provenance; it makes no
mathematical-coverage or human-approval claim.
