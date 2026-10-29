# MG-R002：当前 Lean 覆盖

本页对应冻结的 0.3.0 题面、参考与评分依据；实际数学声明在同目录 Lean 源码中。源码、编译顺序、原始输入及本页散列由 [manifest.json](manifest.json) 绑定。当前逐题构建与全声明审计见 [current-formal.json](current-formal.json)；复核方法见 [共用验证器](../../../../scripts/formal/README.md)。

作者联合交付与旧审计保存于 results/full-lean-terra/formal-history，属于阶段记录。下面保留该题的逐事实数学映射；不把其他题的声明或作者联合编译计数算成本题独立证明。AI 语义审核、Lean 核验与人工审定分别记录，人工仍待定。

所有项目名以下述完整 `MathGauge.` 命名空间为准。

## R002 — original task completely refuted, general boundary theory proved

| Original mathematical fact | Declarations / module | Exact semantic connection |
| --- | --- | --- |
| Real Banach original space | `CompatibleRecords.E`, `original_space_complete` | Actual `C₀(ℕ,ℝ)` on discrete ℕ, with its sup norm and completeness instance. |
| Construct a bounded global functional, not assume one | `convergent`, `seq_limit`, `limit_linear`, `seq_limit_bound`, `exists_extended_limit` | Scalar limit is constructed on the actual subspace of convergent bounded sequences; real Hahn–Banach gives an extension with proved norm ≤ 1. |
| Actual finite test vectors and their bounds | `partial_ones`, `partial_ones_norm`, `test_sequence_linear`, `test_sequence_bound` | Finite initial blocks of ones in c₀; every dual functional gives an actual bounded sequence of these evaluations. |
| Every original finite-dimensional record | `z`, `record` | A bundled real linear map on each actual submodule of the continuous dual. Defined for all submodules, hence includes every finite-dimensional one. |
| Inclusion compatibility | `record_compatible` | The original restriction along actual submodule inclusion. |
| One uniform constant C = 1 | `z_bound`, `record_bound` | Absolute values are bounded in the actual dual operator norm. |
| Nonexistence of an E-valued representative | `coordinate`, `z_coordinate`, `no_original_realization` | Original finite-dimensional singleton spans force every coordinate of x to be 1, contradicting x's actual limit 0. |
| Complete legal counterexample | `CompatibleRecords.counterexample` | Includes completeness, compatibility, bound and nonexistence with all original finite-dimensional quantifiers. |
| Arbitrary legal record data | `RecordBidual.FinitePart`, `Record` | The index type consists of all actual finite-dimensional submodules of the actual continuous dual. The structure contains only original local linear maps, inclusion compatibility and existence of a finite uniform bound. It does not contain a global functional or a realization. |
| Independence of finite observation space | `Record.eval_eq` | Evaluation via the singleton span agrees with the supplied value on every finite-dimensional subspace containing that functional. |
| Global linearity from local compatibility | `pairPart`, `Record.eval_add`, `Record.eval_smul`, `Record.linear` | Addition is proved inside the actual sum of two singleton spans; scalar compatibility inside the singleton span. |
| Actual bounded bidual element | `Record.eval_bound`, `Record.toBidual`, `Record.toBidual_norm`; `bidual_norm_le_given_bound` | Constructs a continuous functional on E′ with norm ≤ the supplied C; no continuity or boundedness certificate is assumed. |
| Bidual restriction and gluing are mutually inverse | `restrict`, `toBidual_restrict`, `restrict_toBidual`, `recordEquiv` | Both operations use all original finite-dimensional restrictions. |
| Exact original record distance | `recordDistance`, `recordDistance_eq_norm` in `RecordRealization.lean` | The supremum is over all ‖φ‖ ≤ 1 of the difference of singleton-span record values, exactly as in the task; proved equal to ‖z_r−z_s‖. |
| Canonical J is an isometric injection | `J`, `J_norm`, `J_injective` | Actual continuous double-dual evaluation map, using Mathlib's proved Hahn–Banach isometry. |
| A specified family is realizable iff its bidual belongs to J(E) | `Represents`, `represents_iff`, `realization_exists_iff` | `Represents` quantifies over every actual finite-dimensional F and φ∈F, with original evaluations φ(x). |
| Unique realization, exact norm and stability | `realization_unique`, `realization_norm`, `realization_given_bound`, `exact_stability` | Includes original supplied-C bound and ‖x_r−x_s‖ = d(r,s). |
| Original operator transform T′F is finite-dimensional | `transpose`, `imagePart`, `imagePoint` in `RecordTransform.lean` | T′ is actual composition φ∘T; imagePart is the actual submodule image and has a proved finite-dimensional instance. |
| Transform obeys original formula and bound C‖T‖ | `transform`, `transform_formula`, `transform_bound` | Formula is r_{T′F}(T′φ); compatibility and linearity follow from constructed restrictions. |
| Bidual transform and canonical naturality | `transform_toBidual`, `canonical_naturality` | Actual T″z and T″Jx = JTx. |
| E-valued recovery on exactly the realizable records | `RealizableRecord`, `recover`, `recover_represents`, `recover_unique`, `recover_exact_stability`, `recover_covariant` | Existence is restricted to the already characterized J(E) boundary. This is not presented as a recovery on every legal record. |
| Every record realizable iff E is reflexive | `all_realizable_iff_surjective` | Exact condition is surjectivity of the canonical map J:E→E″, the reference's definition of reflexivity; no reflexivity hypothesis is added to the counterexample. |
| General theory instantiated on the real counterexample | `RecordInstantiation.c0Record`, `c0Record_no_realization`, `c0Record_bidual_norm`, `c0_bidual_outside_original` | The earlier actual c₀ family inhabits the general original-data record structure. Its constructed bidual has norm ≤ 1 and lies outside J(E). |

**Proof-route substitution, explicitly not claimed as encoded:** the reference constructs the same c₀ obstruction through the isometric identification c₀′ ≃ ℓ¹. This directory instead proves a complete Hahn–Banach/finite-block construction on the actual c₀ dual. The standalone c₀′ ≃ ℓ¹ isomorphism, finite-sign-vector derivation and series representation of each c₀ functional are not encoded here. This does not leave the original task refutation or its general existence/stability/covariance boundary unproved. The parent explicitly accepted this equivalent route during handoff.
