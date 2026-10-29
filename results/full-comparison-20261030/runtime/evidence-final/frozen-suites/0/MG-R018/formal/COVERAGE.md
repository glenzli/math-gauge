# MG-R018 actual-object formal coverage

The version 0.4.0 main target is a true classification and monad-construction theorem. `FiniteObservations.lean` defines the actual families of finite-observation choices, constructs actual ultrafilters from their Boolean choices, and proves inverse constructions and every requested law. No classification or monad conclusion is an input certificate.

| Task / reference obligation | Encoded declaration | Exact scope |
|---|---|---|
| Coherent finite observations | `Record`, `Record.ext` | `choose A f` is a value of every finite test type A; `natural` is exactly the supplied postcomposition equation. Equality is equality of every observation. |
| Constants and pairs | `Record.choose_const`, `Record.choose_pair` | Derived from the supplied naturality, not extra fields. |
| Boolean characteristic functions | private `characteristic`, `characteristic_compl`, `characteristic_inter` | Actual functions into Bool; all private declarations are covered by the dynamic audit. |
| Construct an actual ultrafilter | `accepted`, `accepted_univ`, `accepted_inter`, `accepted_compl`, `toFilter`, `toUltrafilter`, `mem_toUltrafilter` | Filter upward closure and intersection are proved, and complement dichotomy is used to construct an actual `Ultrafilter X`. |
| Recover every finite observation | `choose_fibre` | The fibre over a lies in the constructed ultrafilter iff the record chooses a. |
| Construct a record from an ultrafilter | `selected`, `selected_spec`, `selected_fibre`, `ofUltrafilter` | The pushforward to a finite set is actually proved principal; the resulting unique selected value satisfies naturality. |
| Both inverse laws | `to_of`, `of_to`, `classification` | Actual equivalence `Record X ≃ Ultrafilter X`, valid for arbitrary X including the empty set. |
| Functor action | `Record.map`, `Record.map_id`, `Record.map_comp` | Precomposition of each finite observation; both functor equations are proved. |
| Prescribed unit and multiplication | `Record.point`, `Record.flatten` | Their defining values are exactly the two displayed task equations. `flatten.natural` is proved from the original records' naturality. |
| Unit naturality, both unit laws, associativity, multiplication naturality | `Record.map_point`, `Record.flatten_point`, `Record.flatten_map_point`, `Record.flatten_assoc`, `Record.flatten_natural` | Equalities of actual record values, not assumed laws. This is the complete mathematical monad structure; a separate `CategoryTheory.Monad` wrapper is unnecessary and is not claimed. |
| Natural monad classification | `to_point`, `to_map`, `to_flatten`, `to_flatten_join` | The comparison carries point to `pure`, map to ultrafilter map, and flatten to `joinM` after pushforward by the comparison. The last theorem explicitly identifies the join-and-map notation with the bind formula. |
| Finite tests in arbitrary universes | `Record.evalFinite`, `evalFinite_natural`, `evalFinite_agrees`, `evalFinite_tests`, `evalFinite_unique` | Transport through `Fin (Fintype.card A)` agrees on every original finite test. The transported value has naturality under arbitrary finite maps; its values under maps into skeletal finite tests uniquely determine it. Thus larger finite test universes add no records. |
| Point injectivity | `point_injective` | No two distinct actual points give the same record. |
| An actual infinite obstruction | `free_record_not_point` | Uses the actual cofinite-extending `hyperfilter X`; finite singletons do not belong to it, so its inverse-classified record is not point evaluation. |
| Exact finite criterion | `point_surjective_iff_finite` | Surjectivity iff `Finite X`; combined with `point_injective`, this is the unique point-evaluation condition, including empty X. |

The proof uses standard pinned Mathlib facts about actual ultrafilters: `Ultrafilter.ofComplNotMemIff`, `Ultrafilter.eq_pure_of_finite`, `Ultrafilter.map_map`, `Ultrafilter.map_pure`, `Ultrafilter.pure_injective`, `hyperfilter`, and `Set.Finite.notMem_hyperfilter`. The finite-fibre route in Lean uses the equivalent statement that a pushed-forward ultrafilter on a finite set is principal; the reference proves the finite-partition argument. These are equivalent complete routes, not a change of assumptions.

Universe interpretation: a record uses finite test types in a fixed smaller Lean universe and accepts X in an arbitrary universe. In the task's Grothendieck setting, the testing universe is an element of the ambient universe, so the family and its iterations are ambient-small. The finite transport and uniqueness declarations give the mathematical identification with any equivalent finite skeleton and with every allowed finite testing universe. No universe-code implementation of ZFC or Grothendieck universes is claimed; Lean universes and these explicit transport results encode the relevant size polymorphism.

No source from prior Math Gauge cases is used. No topology or compact-Hausdorff algebra classification is required here or imported from MG-R019. The companion item shares a theme but is not a formal dependency. No generic right Kan extension theorem, terminality among monads, or uniqueness among all possible monad structures is asserted by this reference or its coverage.

`manifest.json` binds the exact task, reference, rubric, this coverage file and source. A fresh case-isolated compilation and all-`MathGauge` axiom audit permits only `propext`, `Classical.choice` and `Quot.sound`; it neither scores candidate answers nor supplies human approval. No candidate model run was performed.
