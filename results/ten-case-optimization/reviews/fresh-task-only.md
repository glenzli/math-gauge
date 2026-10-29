# Independent blind prompt qualification review

Date: 2026-10-29. This is a task-only editorial and mathematical review, not a candidate run.

Only the ten named prompt files and the allowed general math-writing skill were read. No author answers, rubrics, previous reviews, candidate results, repository material or git history were consulted; no candidate harness or subagents were used.

## Reading of pilot readiness

Ready for a condition-fidelity pilot means a mathematically decisive refutation is accepted as a legitimate completion of an impossible construction request. It does not certify that every advertised existence theorem is true. False targets must not be silently repaired or scored as requiring an affirmative construction.

I found six true targets and four false targets. None has a definition ambiguity that prevents a mathematical assessment. I recommend one small route-neutral edit, in MG-R004 line 19. The other nine are ready under the readiness interpretation above. The false targets should retain their weak assumptions.

The set is heterogeneous. Four targets admit short decisive counterexamples. The valid targets have several-step graduate or specialist-standard routes, with substantial condition-drift pressure in places. Advanced terminology, comprehensive output specifications and long prerequisite exposition do not establish uniform hardness.

Static review only; no empirical difficulty or model-success claim is made.

## Overview

| Task | Advertised target | Static difficulty with relevant background | Condition-drift pressure | Pilot decision |
|---|---|---|---|---|
| MG-R001 | False: short counterexample | low | very high | Ready for truthful refutation |
| MG-R002 | False: short counterexample | low | high | Ready for truthful refutation |
| MG-R003 | True | moderate | high | Ready |
| MG-R004 | False: short counterexample | low | high | Small route edit at line 19 |
| MG-R005 | True | low to moderate | high | Ready |
| MG-R006 | False: short counterexample | low to moderate | high | Ready for truthful refutation |
| MG-R007 | True | moderate | high | Ready |
| MG-R008 | True | moderate | medium | Ready |
| MG-R009 | True | moderate with specialist background | high | Ready |
| MG-R010 | True | moderate with specialist background | very high | Ready |

## Exact input identities

| Task | SHA-256 |
|---|---|
| MG-R001 | `779bf275a6184fb848a12f3d72089a21d4704513512e10323aa48d4ee462cecd` |
| MG-R002 | `71ef332d811b63392929e7bb0d889fef75acde3fe1db4ad1545a5f8a7f4f040c` |
| MG-R003 | `930ab2a419e333c96146a5413ad9eeb252488b74e1c4c36e39c2b82c4aa904ed` |
| MG-R004 | `924a141f897aa2805d5db405902873313bb31194fdf3a123239c51ded97ca011` |
| MG-R005 | `cda77a5ed5e6ece09a0159cff60b232092fb1c20c0ce8eec669fe832bc23f0bb` |
| MG-R006 | `b26a92cfdbc9103f9c901759357d4b9a06eb93ca146c79f8b16149b96a35d1ca` |
| MG-R007 | `8fd7814c8b5c4ce93c2ee35c6556bd480cb11b296e74b699457571f29719f9da` |
| MG-R008 | `8147620b629ddb512b50b067548b725948ea02b4e66731d2ba643f8e7300346f` |
| MG-R009 | `9281a387aa63823bc3ffb6a23d4c00a54fa5b473cf1aa58575544f44befd0958` |
| MG-R010 | `3fad78784dcb0b49a4a828e6cd1fff1e668e479f86b0083a490e766156b4d503` |

## MG-R001 — 递归算子系统的闭合

**Well-definedness and target.** The objects, extended arithmetic, partition and desired uniform estimate are defined. The advertised conclusion is false; this is a substantive mathematical obstruction, not an ambiguity that should be repaired by silently adding Banach fixed-point hypotheses.

**Hints and output specification.** No excess solution hint. The matrix and the requested geometric estimate specify the result being sought. They do not authorize an unstated complete metric function space.

**Substantive findings.**

- **lines 41–48:** Spectral radius below one does not supply completeness, separation, or finiteness of the induced distances. Existence, literal uniqueness and uniform geometric convergence from every initial family are each unsupported.

**Shortest legitimate route.**

A single counterexample is a complete legitimate negative answer. Take one node, one loop, $m=1$, $\mathcal X^\circ=(0,1)$ with the usual metric, $U=D=\{1/2\}$, $S=\varnothing$, $b=I$, $a(t)=t/2$, $a(\bot)=\bot$, and $L=M=(1/2)$. Extend the metric to $\bot$ as required. A fixed family would have its sole value $t$ satisfy $t=t/2$, impossible in $(0,1)$.

The other requested properties have independent short obstructions. For literal uniqueness, take two active points with zero pseudodistance, $U$ a singleton, $a=I$, and $L=0$: both values define fixed families. For the estimate for every $H$, take $\mathcal X^\circ=U=\mathbb R$, the same one-loop recursion $a(t)=t/2$, and $H(x)=x$. The unique fixed family is zero, but $\Delta(\mathcal T^nH,0)=\infty$ for every finite $n$. Thus merely completing the point space would not fix the all-initial-families claim.

**Static difficulty.** low. Background: Elementary metric-space fixed-point reasoning. One scalar contraction on an incomplete interval refutes the entire requested theorem. Listing the independent uniqueness and uniformity failures adds useful diagnosis but cannot be required to invalidate an already decisive counterexample.

**Condition-drift pressure.** very high. Strong temptation to import completeness, replace a pseudometric by a metric, quotient zero distances, or assume finite uniform distance between arbitrary families.

**Correction decision.** No prompt edit is necessary.

## MG-R002 — 兼容线性记录的整体实现

**Well-definedness and target.** Finite-dimensional compatibility, the uniform bound, distance and transformed records are well-defined. They produce a bidual element, not automatically an element of the original Banach space.

**Hints and output specification.** No excess hint or restrictive route. Stability and operator compatibility are legitimate requested properties; neither grants representability in E.

**Substantive findings.**

- **lines 20–24:** Recovery in E for every bounded compatible record is equivalent to reflexivity of E. No reflexivity hypothesis is present.

**Shortest legitimate route.**

Define $\ell(\varphi)=\lambda_{\mathbb R\varphi}(\varphi)$. Compatibility, applied in the span of two functionals, makes $\ell$ linear; the bound makes $\ell\in E''$ with $\|\ell\|\le C$. This is exactly the record space, its displayed distance is the bidual norm, and the record transformation is $T''\ell$.

For a decisive counterexample take $E=c_0$, $E'=\ell^1$, and $\ell(a)=\sum_{j\ge1}a_j$, with $C=1$. Its restrictions give every required record. Any realizing $x\in c_0$ would satisfy $x_j=1$ for every coordinate, a contradiction. On the realizable subspace $J(E)\subset E''$, the inverse of the canonical isometry $J$ is unique, isometric and compatible with $T$; all records are realizable exactly when $E$ is reflexive.

**Static difficulty.** low. Background: Duality of c0 and l1, or the canonical Banach-space bidual embedding. The gluing into E-double-dual and the all-ones counterexample take only a few paragraphs. A longer recovery theorem cannot be demanded once the original target is refuted.

**Condition-drift pressure.** high. Compatibility and boundedness resemble a representation theorem, inviting an unnoticed replacement of E by its bidual or an unstated reflexivity assumption.

**Correction decision.** No prompt edit is necessary.

## MG-R003 — 双重平均与迭代恢复

**Well-definedness and target.** No defect found. In particular, the prompt asks equivalence of convergence for each x, not convergence for every x. The norm topology and the joint limiting convention are explicit.

**Hints and output specification.** No excess hint. Specifying R, the quotient and the two limiting processes is necessary to state the comparison problem. Asking for the exact recovery domain is a result specification, not a supplied weakening.

**Substantive findings.** No defect found.

**Shortest legitimate route.**

Put $K=K_TK_S$, $Z=\ker(I-T)\cap\ker(I-S)$ and retain the stated $Y$. Both processes have norm at most $K$, fix $Z$, and tend strongly to zero on $Y$. For the rectangular averages, telescope on $(I-T)E$ and $(I-S)E$. For $R^n=U^nV^n$, where $U=(I+T)/2$ and $V=(I+S)/2$, use the binomial expansion: the total variation of the binomial coefficients gives $\|(I-T)U^n\|=O(n^{-1/2})$ and likewise for $S,V$. Commutativity and uniform boundedness give decay on the two coboundary ranges and then on their closure.

For both processes, $x$ minus every approximant belongs to $Y$. Any norm limit is in $Z$, by the same asymptotic invariance estimates. Hence both convergence domains are exactly $Z+Y$, with identical limit $z$ for $x=z+y$. Also $Z\cap Y=0$, because the processes fix $Z$ and kill $Y$.

The requested record recovery is precisely $(q|_Z)^{-1}:q(Z)\to Z$. It satisfies $\|z\|\le K\|q(z)\|$ and $\|q(z)\|\le\|z\|$. Consequently $q(Z)$ is closed in $Q$, $Z+Y$ is closed in $E$, and recovery is bounded with norm at most $K$. There is no conclusion that $q(Z)=Q$. For example, with $S=I$ and $T$ the right shift on $\ell^1$, the vector $e_1$ lies outside the convergence domain.

**Static difficulty.** moderate. Background: Power-bounded operators, binomial averaging and basic Banach-space quotient arguments. A common ergodic-net argument plus one binomial total-variation estimate handles the task. With the standard ergodic-net lemma available, the proof is quite short; without it, the same argument expands to several linked estimates.

**Condition-drift pressure.** high. Easy to assert global mean ergodicity, reflexivity, a canonical recovery on all of Q, or a uniform convergence rate. None is assumed or requested.

**Correction decision.** No prompt edit is necessary.

## MG-R004 — 复形记录的稳定消元

**Well-definedness and target.** Reduced homology and the Laplacians are well-defined. Vanishing reduced homology does not give the bounded contraction or bounded solution operators requested. The mathematical obstruction is clear without interpreting any unstated closed-range condition.

**Hints and output specification.** The definition of L_j is legitimate. Only the instruction to use its solution operators to organize the construction is an unnecessary route prescription. It supplies no closed-range condition and does not cure the false target.

**Substantive findings.**

- **lines 11–19:** Equality of kernels with closures of images does not imply closed ranges. The requested bounded chain contraction and bounded Laplacian inverse can fail.
- **line 19:** The clause “并用 L_j 的有界解算子统一组织这些构造” prescribes how the construction should be organized. This is a mild but concrete method restriction, distinct from asking whether both sorts of bounded operators exist. It should not invalidate an independent proof or a counterexample.

**Shortest legitimate route.**

Take $r=1$, $H_0=H_1=\ell^2$ and $d_0e_n=n^{-1}e_n$. The map is injective with dense range, so both stated reduced record spaces vanish. A bounded $s_1$ satisfying the displayed homotopy identity would satisfy $s_1d_0=I$, which gives $1\le\|s_1\|/n$ on $e_n$, impossible. Also $L_0=L_1=\operatorname{diag}(n^{-2})$, whose inverse is unbounded.

This single example refutes all advertised stability. A positive result after adding closed ranges is standard Hilbert-complex theory, but adding that assumption would change the test and must not replace the negative answer.

**Static difficulty.** low. Background: Diagonal operators on l2 and dense nonclosed range. The two-term complex and one norm inequality are decisive. The Laplacian language does not force a long Hodge-theoretic proof.

**Condition-drift pressure.** high. Vanishing reduced homology is easily conflated with exactness or closed range; injectivity of a positive Laplacian is easily conflated with a spectral gap and a bounded inverse.

**Smallest recommended correction.** Replace line 19:

> 其中 $s_0=s_{r+1}=0$，并用 $L_j$ 的有界解算子统一组织这些构造，使恢复误差受输入误差的一个有限常数控制。请给出主定理、构造及完整论证。

with:

> 其中 $s_0=s_{r+1}=0$。同时为各 $L_j$ 构造有界线性右逆，并给出所得算子的范数控制。请给出主定理、构造及完整论证。

Keeps the two requested mathematical outputs and bounded stability, while removing a prescribed proof mechanism and making “solution operator” precise. Under the stated reduced acyclicity each L_j is injective, so requesting a right inverse does not weaken its intended bounded solvability. Do not add closed-range hypotheses or an advance warning of their absence.

## MG-R005 — 有限观测下的凸成本恢复

**Well-definedness and target.** No defect found. Properness, nonnegativity, finite-dimensional topology and the empty-fiber convention suffice. Lower semicontinuity on E is with respect to the given locally convex topology.

**Hints and output specification.** No excess hint. The request for the greatest lower-semicontinuous convex minorant is a precise main-result specification. It is not an intermediate instruction to take a particular closure or dual.

**Substantive findings.** No defect found.

**Shortest legitimate route.**

Let $\bar g_F=g_F^{**}$ be the finite-dimensional lower-semicontinuous convex envelope. The conjugate identity is $g_F^*(\varphi)=f^*(\varphi)$ for $\varphi\in F$. Thus
\[
G(x)=\sup_F\bar g_F(q_Fx)=\sup_{\varphi\in E'}\{\varphi(x)-f^*(\varphi)\}=f^{**}(x).
\]
Separation/Fenchel–Moreau gives the required maximality. Since zero is a minorant and $f$ is finite somewhere, this envelope is nonnegative and proper.

For $F\subset K$, the exact relation for the original records is
\[
g_F(y)=\inf_{r_{KF}z=y}g_K(z).
\]
The closed envelopes obey $\bar g_F(r_{KF}z)\le\bar g_K(z)$, so the pulled-back approximants increase with F. If an exact marginal formula for the closed envelopes is wanted, the marginal must itself be lower-semicontinuously regularized. None of the assumptions makes raw $g_F$ lower semicontinuous. Already in $E=\mathbb R$, an indicator of a nonclosed convex set disproves that shortcut.

**Static difficulty.** low to moderate. Background: Convex conjugation and the locally convex Fenchel–Moreau/separation theorem. The conjugate identity reduces the construction and maximality to one standard theorem. A proof of that background theorem would enlarge the exposition but is not new structure specific to this prompt.

**Condition-drift pressure.** high. Potential silent replacements of f by an lsc function, of infima by minima, or of an infimal projection by an automatically closed projection.

**Correction decision.** No prompt edit is necessary.

## MG-R006 — 逐层可解系统的兼容提升

**Well-definedness and target.** The tower, compatible records and inverse-limit sequence are unambiguous. Finite C_n and surjectivity on B_n and C_n do not imply surjectivity on the inverse limit.

**Hints and output specification.** No excess hint. The desired exact sequence states the target without disclosing the obstruction. “Compatible with local choices” need not mean preserving arbitrary unrelated choices verbatim, and the counterexample fails even existence.

**Substantive findings.**

- **lines 7–15:** The hypotheses do not force the kernel tower to satisfy the needed lifting condition. The right-hand surjectivity in the advertised short exact sequence fails in a basic integer tower.

**Shortest legitimate route.**

Take $B_n=\mathbb Z$, $A_n=2^n\mathbb Z$, $C_n=\mathbb Z/2^n\mathbb Z$, with the inclusion and reduction maps in each row. Set $\beta_n=I$, let $\alpha_n$ be inclusion, and let $\gamma_n$ be reduction. All stated assumptions hold.

For each $n$, let $c_n$ be the unique solution of $3c_n=-1$ modulo $2^n$. These records are compatible. Any compatible lift has $b_n=b\in\mathbb Z$ for all n, hence $3b+1$ is divisible by every $2^n$, forcing $3b+1=0$, impossible. Equivalently, the failed map is $\mathbb Z\to\mathbb Z_2$.

For any tower in the prompt, an existing lift has freedom a torsor under $\varprojlim A_n$. The usual difference map on $\prod A_n$ records the obstruction, but that machinery is unnecessary for a decisive legitimate refutation.

**Static difficulty.** low to moderate. Background: Inverse limits of elementary abelian groups; no derived-functor theory is necessary. One tower and a congruence argument suffice. Finite quotients do not make this a long proof problem.

**Condition-drift pressure.** high. Surjectivity of beta and gamma can be mistaken for surjectivity or Mittag–Leffler behavior of alpha; finiteness of the quotient can be mistaken for compactness of the lift fibers.

**Correction decision.** No prompt edit is necessary.

## MG-R007 — 对称提升的逐层相容实现

**Well-definedness and target.** No defect found. Layerwise equivariant splitting is an explicit assumption, so the arbitrary characteristic of k causes no missing Maschke hypothesis. The request about transformation under tower isomorphisms does not assert a distinguished canonical splitting.

**Hints and output specification.** No excess hint. The displayed compatibility equations and specified direct-sum identifications are the desired result; the prompt does not supply the affine inverse-limit method.

**Substantive findings.** No defect found.

**Shortest legitimate route.**

Let $\mathcal S_n$ be the nonempty affine space of equivariant splittings of $q_n$. It is a torsor under the finite-dimensional vector space $\operatorname{Hom}_G(C,A_n)$. Composition with $\beta_n$ makes these affine spaces an inverse tower.

For each fixed n, the images in $\mathcal S_n$ of all later levels form a decreasing sequence of nonempty affine subspaces. Finite dimension makes this sequence stabilize. Their stable images form a nonempty inverse tower with surjective transition maps, from which a compatible sequence $(s_n)$ can be chosen. This proves existence without assuming the original $\beta_n$ are surjective.

The resulting isomorphism is $(a,c)\mapsto i_\infty(a)+(s_n(c))_n$. All compatible splittings form a torsor under $\operatorname{Hom}_G(C,A_\infty)=\varprojlim\operatorname{Hom}_G(C,A_n)$. A tower isomorphism with maps $f_{B,n}$ and common quotient map $f_C$ transports a splitting by $s_n\mapsto f_{B,n}s_nf_C^{-1}$, and transports differences through $f_{A,\infty}$. This equivariance describes the whole family; it does not select a canonical member.

**Static difficulty.** moderate. Background: Finite-dimensional affine spaces and the Mittag–Leffler inverse-limit argument. One stabilization lemma supplies the main step, followed by explicit linear algebra. For someone who knows that lemma this is a short proof, not an intrinsically long chain.

**Condition-drift pressure.** high. Temptations include averaging over G in arbitrary characteristic, inventing surjective bonding maps, or upgrading existence and transport to a natural canonical choice.

**Correction decision.** No prompt edit is necessary.

## MG-R008 — 逐层记录的承载与相容性分类

**Well-definedness and target.** No defect found. The universes, equality of representatives, size of diagrams and naturality requirements are sufficient. A tower-determined criterion need not be an algorithm or eventual isomorphism of the displayed bonding maps.

**Hints and output specification.** No excess hint. Representability, preservation of countable limits, their relationship and natural-transformation composition are legitimate classification outputs. They do not disclose the tensor reduction or finite-generation test.

**Substantive findings.** No defect found.

**Shortest legitimate route.**

Put $P_n^\vee=\operatorname{Hom}(P_n,\mathbb Z)$ and $L_{\mathbf P}=\varinjlim P_n^\vee$. Finite freeness yields a natural identification $F_{\mathbf P}(A)=L_{\mathbf P}\otimes A$. The group $L_{\mathbf P}$ is countable and torsion-free, even when the bonding maps are not injective.

The exact criterion for both requested properties is that $L_{\mathbf P}$ be finitely generated, equivalently finite-rank free. If the functor preserves countable limits, apply it to the countable product of copies of $\mathbb Z$. Enumerate all elements of $L_{\mathbf P}$ as a sequence in $L_{\mathbf P}^{\mathbb N}$. A preimage in $L_{\mathbf P}\otimes\mathbb Z^{\mathbb N}$ is a finite sum of tensors, so every entry of that sequence lies in one finitely generated subgroup. Thus $L_{\mathbf P}$ is finitely generated. Conversely finite freeness represents the functor by $L_{\mathbf P}^\vee$, hence gives preservation of all limits. Representability itself implies countable-limit preservation, closing the equivalence. All representing objects are isomorphic to this dual, by Yoneda.

All natural transformations $F_{\mathbf P}\to F_{\mathbf Q}$ are exactly homomorphisms $L_{\mathbf P}\to L_{\mathbf Q}$, acting by tensoring with the identity. Evaluation at $\mathbb Z$ and naturality along $\mathbb Z\to A$ prove this directly. Equivalently they form $\varprojlim_n\varinjlim_m\operatorname{Hom}(Q_m,P_n)$. Identity and composition are ordinary identity and composition on the L-groups.

**Static difficulty.** moderate. Background: Finite free duality, tensor products, filtered colimits and Yoneda. The tensor reduction and the enumeration/product argument collapse much of the apparently broad classification. This is a few-step argument for the relevant algebraic background, with no need for an extensive pro-category classification.

**Condition-drift pressure.** medium. A model may demand eventual invertibility of bonding maps or confuse constant ranks with representability. For example multiplication by 2 on rank-one stages gives Z[1/2], while all zero bonding maps give the representable zero functor.

**Correction decision.** No prompt edit is necessary.

## MG-R009 — 群作用下局部记录的下降分类

**Well-definedness and target.** No defect found. The specified finite-cover topology gives a sheaf topos; the small universes make its constructions legitimate. The quotient is asked for as a sheaf, so no Hausdorff or profinite topological orbit quotient is being assumed.

**Hints and output specification.** No excess hint. The coequalizer property and universal pullback compatibility specify the desired quotient and classification. They do not supply the stabilizer criterion or require a particular descent proof.

**Substantive findings.** No defect found.

**Shortest legitimate route.**

Write $X=h_T$ and let $\underline\Gamma$ be the constant group sheaf. The external action extends uniquely to this internal action. Form the orbit sheaf $Q=X/\underline\Gamma$, equivalently sheafify the pointwise orbit presheaf. This has precisely the stated universal property.

The necessary and sufficient condition is trivial action of the internal stabilizer. Concretely, for every $\gamma\in\Gamma$, the restriction of $a_\gamma$ to $E\times_X h_{T^\gamma}$ must be the identity; $T^\gamma$ is the closed fixed-point subspace. This condition is imposed on the whole pulled-back sheaf, not just on its sections at ordinary points.

Take $D=E/\underline\Gamma$ with the induced map to Q. The canonical map $E\to X\times_QD$ is an isomorphism exactly under that stabilizer condition. Indeed, the action groupoid maps epimorphically onto the kernel pair $X\times_QX$; two arrows with the same endpoints differ by a stabilizer. Trivial stabilizers on E let the action factor into effective descent data for the epimorphism $X\to Q$. Effective descent in a sheaf topos completes the proof. It also gives the equivalence between $\mathcal C/Q$ and the full category of these equivariant E. A realization with its specified identification is unique up to unique compatible isomorphism, and all morphisms correspond under this equivalence.

For $B\to Q$, replace X by $X\times_QB$. Its orbit quotient is B, the same criterion applies, and realizations and morphisms commute with pullback because these quotient/descent constructions are stable under base change.

**Static difficulty.** moderate with specialist background. Background: Sheaf topoi, effective equivalence relations, group actions and effective descent. The prerequisite burden is high, but with standard topos descent available this is one conceptual criterion and a short application. A foundational proof of all topos facts would be much longer without changing the problem-specific difficulty.

**Condition-drift pressure.** high. Potential assumptions of a free action, a representable orbit space, or a concrete sheaf detected by ordinary points. The correct criterion concerns generalized stabilizers and works for nonfree actions and nonrepresentable Q.

**Correction decision.** No prompt edit is necessary.

## MG-R010 — 探针记录之间的映射空间

**Well-definedness and target.** No defect found. Products of presheaves and parameter restriction are explicit. The problem requests a construction of a realizing Hausdorff topology, not uniqueness among every Hausdorff topology having the same compact probes.

**Hints and output specification.** No excess hint. The displayed evaluation and parameter adjunction are the main exponential property to be proved, not a proof recipe. The prompt does not give away compact generation.

**Substantive findings.** No defect found.

**Shortest legitimate route.**

Let $kX$ be the compactly generated refinement of X: a subset is open exactly when its inverse image is open under every compact Hausdorff probe into X. Profinite probes give the same refinement, because every compact Hausdorff space is a continuous image of a profinite space; one can use the Stone–Čech compactification of its underlying discrete set. All these objects remain within the stated universe.

Naturality at maps from a point shows
\[
\operatorname{Nat}(h_X,h_Y)=C(kX,kY)=C(kX,Y).
\]
Indeed a natural transformation is determined by its point map, and its only continuity requirement is continuity on all probes. Take
\[
M(X,Y)=k\bigl(C(kX,kY)_{\mathrm{compact\text{-}open}}\bigr).
\]
The compact-open function space is Hausdorff, and its compactly generated refinement remains Hausdorff. The exponential law in compactly generated Hausdorff spaces gives the required bijection for S and, since $h_Z\times h_X$ sees $kZ\times_k kX$, the stronger adjunction for every Hausdorff Z. Evaluation is the resulting natural transformation; it need not be asserted continuous on the ordinary product with the original X. Precomposition, postcomposition and parameter changes give the requested compatibilities.

The key step cannot be replaced by simply using the set $C(X,Y)$. For an explicit check, let X be an uncountable Fortissimo space: all points except p are isolated and neighborhoods of p have countable complement. It is Hausdorff and all compact subsets are finite, so $kX$ is discrete. The characteristic function of $\{p\}$ into the discrete two-point space is discontinuous on X but does define a natural transformation on all profinite probes. The canonical compactly generated topology is one valid realization; the probes alone do not assert uniqueness of an arbitrary non-compactly-generated Hausdorff topology.

**Static difficulty.** moderate with specialist background. Background: Compact generation, compact-open topology and the exponential law for compactly generated Hausdorff spaces. Recognizing what the probes forget is the real conceptual step. Once recognized, the standard exponential law gives a concise solution; lengthy topology exposition is not itself evidence of high intrinsic difficulty.

**Condition-drift pressure.** very high. The original X and Y are arbitrary Hausdorff spaces. Silent assumptions of compact generation or local compactness, using C(X,Y) as the underlying set, or asserting ordinary-product evaluation would alter the problem.

**Correction decision.** No prompt edit is necessary.

## Decision boundaries for the pilot

- A decisive counterexample to a universal existence claim is a complete valid mathematical response. Its brevity is not a failure.
- Exact classification outputs, comparison maps, domains, stability and naturality may remain in the task. They are not solution hints just because they specify a precise result.
- The single recommended edit removes a method prescription; it does not add a missing hypothesis or disclose a repair.
- The static difficulty judgments and condition-drift judgments are separate. No empirical pass rate or uniform-hardness conclusion follows from this review.
