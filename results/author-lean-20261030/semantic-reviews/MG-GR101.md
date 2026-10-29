# MG-GR101 independent semantic review

Reviewer: author-lean-chapters (independent of this case author). Read-only review; no case files changed. No candidate model run. Human review remains pending.

## Outcome

The mathematical content is correct. S1, S2, S3, and S5 are covered by actual Lean constructions with the stated hypotheses. S4's exact sequence is proved into the image of H in M/L, without inheriting H=L. For a fully explicit representation claim, add the canonical H/L-to-image equivalence and L≤H. S6 correctly handles conditional prefix realizability and the final solution set, but its order example should use a genuine finite permutation and cover the quotient/first-failure distinctions described in the reference.

The current kernel evidence reports passed, 139 audited declarations, only Classical.choice/Quot.sound/propext, and its manifest hash matches the inspected manifest. That compilation result is separate from this semantic review.

## Stage checks

- S1: pairRecords is the actual compatible-pair submodule, pairNoise is coordinate A/B noise inside it, pairMap is the diagonal followed by quotient. pairMap_kernel identifies the actual kernel as A∩B, pairMap_surjective constructs a partial realization from x−y∈A+B. pairEquiv is a linear equivalence of these actual quotients and pairEquiv_on_diagonal checks the requested map. pair_fiber gives exactly t−w∈A∩B. No uniqueness in M is claimed.
- S2: triple_glue accepts the single local H=L equality explicitly and uses it to put w−z into (A∩B)+C. triple_embedding_surjective plus the previously proved injectivity constructs tripleEquiv for the actual j. The ring is not assumed commutative and there is no distributive-lattice instance.
- S3: prefix_exists is an actual induction for all n; n=1 is explicit, n=0 is a harmless stronger boundary case. At induction m it uses exactly prefixKernel A m + A m = ⋂i<m(A i + A m), with 0<m<n. Under zero-based indexing this is exactly the question's m=2,…,n assumption. Pairwise compatibility is only requested within the first n records; unused tails of the ℕ-indexed family are irrelevant. step_zero_iff corrects by u in the entire prefix intersection. prefix_fiber describes all solutions. No three-record-only shortcut or hidden distributivity occurs.
- S4: partial_choice is arbitrary, but raw_obstruction separately proves additivity and left scalar compatibility using choice independence. noise_in_kernel and liftQ provide representative independence. obstruction_onto has the correct restricted target, not all M/L. Injection, exactness, surjection, normalization at (0,0,−h), zero iff realizable, and all solutions are proved. No H=L premise appears. Representation gap: obstruction_image is defined as H.map(mkQ L). The source does not explicitly prove L≤H or produce the canonical linear equivalence from the actual quotient H/(L.comap H.subtype) to that image. These are mathematically true and short; the current proof is not mathematically wrong, but the claimed literal H/L representation should be completed.
- S5: V=Fin 3→ℚ is the actual finite-dimensional rational vector space. All four subspaces are kernels of actual linear maps. omitWitness gives four explicit vectors and every_triple quantifies each omitted j and every retained i. not_all_four derives t0=t1=t2=0 versus t0+t1+t2=1. This is stronger than merely pairwise compatibility and satisfies the exact counterexample requested. FiniteDimensional of this explicit V is standard via the finite Pi instance, not an extra assumed axiom.
- S6: stepClass takes a subtype carrying an actual PrefixGlues witness, so it cannot be evaluated with a fabricated failed-prefix realization. step_independent uses the difference in the full prefix kernel. step_zero_iff is a full iff and constructs the corrected witness. all_steps_iff uses induction from the empty prefix, so universal quantification over potentially empty witness types cannot conceal an earlier failed step. prefix_fiber gives the entire solution set; permutation_invariant gives pointwise equivalence of membership for any true reindexing equivalence, hence the final set and existence are invariant. Current reordered_prefix_differs only compares first-prefix kernels using n↦1−n, which is a swap on the first two indices but not a permutation of ℕ. It should be tied explicitly to Fin 2 or use Equiv.swap. It also does not formalize the possibly different step quotients / first failed position mentioned in the reference.

## Minimal completion recommendations

1. Add `ambiguity_le_obstruction_space`, and a canonical equivalence `(obstruction_space A B C ⧸ (ambiguity A B C).comap (obstruction_space A B C).subtype) ≃ₗ[R] obstruction_image A B C`, with the value on the class of h. Then reuse obstruction_onto as the normalized map into the embedded O and record this bridge in alignment S4.
2. Replace or supplement the reordering example with a true finite permutation. A single three-record example covers the remaining distinctions: M=ℚ; A0=0,x0=0; A1=0,x1=1; A2=⊤,x2=0. Order [0,1,2] first fails at the second record, while [0,2,1] first fails at the third. At the second step the former denominator is 0 and the latter is ⊤, so the actual quotient objects differ. All final solutions are empty in both orders. Use an actual Fin 3 permutation swapping 1 and 2.

These findings are representation/completeness issues, not mathematical counterexamples to the proposed theorems. The original task/reference/rubric should remain unchanged; fixes belong in author Lean, alignment, and fresh verification evidence.

## Inspected identities

- task.md: c52de168321520a52f9304251cf8baae1b5883b4ce83cdccba3b939278b30361
- reference.md: b4f1e7b90874de13265aa4bb09bf7cbd2573a1ad54d0a0fff27f359d26491b62
- formal/FiniteCongruences.lean: 893b502c2a10bad43f53f6f5b2acff9d2a68bc07a93d29792e1749e5c4a373ff
- formal/CongruenceObstruction.lean: 498403a7981ed6f4082c143d3891488ade2abdc8d074e3ce0ae698adbbf2457c
- formal/alignment.json: 7b2607510e77a074f30cefb94dfdff0ef73a470fe7b32cd57fa7c2d40296ef83
- formal/manifest.json: 1792a39ab9208427be6e062fde314c5c75d06830ae7a98692b862985e0b9f417

## Follow-up: both findings resolved

Read QuotientOrderBridges.lean in full and the updated S4/S6 alignment. No author sources were edited by the reviewer.

S4 now explicitly proves L≤H, constructs the actual linear map H→image(H in M/L), proves its kernel is the pulled-back submodule L and proves surjectivity. obstructionQuotientEquiv is the canonical quotient-kernel linear equivalence, and the class-value theorem identifies it with the expected class of h. This closes the literal H/L representation gap without new assumptions.

S6 now uses a genuine Fin 3 permutation on the same three records. The original order succeeds at prefix 1 and fails at prefix 2; the swapped order succeeds at prefix 2 and fails at prefix 3. The second-step quotient is nonzero in the first order and the zero module in the second, with actual quotient assertions. Final solution membership is invariant under that permutation. A separate genuine Equiv.swap 0 1 on natural indices changes the prefix intersection. The former nonpermutation n↦1−n example was removed. Together with the previously reviewed conditional step class and induction, this closes the order boundary gap.

Final semantic result: all six stages aligned; no open mathematical or representation findings. This is independent AI semantic review, not human approval.

Revised identities:
- formal/FiniteCongruences.lean: 247e761b3a711d3b43554acc026bc60be12e848003790823b698fea112216251
- formal/CongruenceObstruction.lean: 498403a7981ed6f4082c143d3891488ade2abdc8d074e3ce0ae698adbbf2457c
- formal/QuotientOrderBridges.lean: 0339113b94fd9fcba299bf79cd4551e48717c6ea66906af4f95d70d6e7e71531
- formal/alignment.json: b688180db821b4fe63209599439f79aab10f6b417586158479c6dc9304e9d34b
- formal/manifest.json: aa31276abd48e642d476c38ef6ae35cb5cf1849d9742b9ffa3701cad9ef756ba

Fresh evidence at review time: passed; report binds current manifest: False. Root is responsible for retaining the final current-identity run.
