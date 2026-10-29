# Independent mathematical review of the MG-R008 response

Reviewed artifact: `/private/tmp/math-gauge-full-lean-20261029/flow/live-runs/MG-R008/output/response.md`

SHA-256: `bdb0bb99e82f43880301879b997a33e3fae4c11b0bc18d263042b7a119f66288`

Review scope: the complete response, with special attention to its additional Mittag–Leffler plus bounded-stable-rank criterion and the single diagram consisting of the original tower. This is a mathematical review, not a Lean proof of these additional assertions and not human approval.

Finding: no mathematical error found. The main tensor classification agrees with the independently compiled classification in `TowerClassification.lean`. The additional criteria are valid under exactly the given countable finite-free tower hypotheses.

1. The classes c_n=[n,id] are compatible: postcomposition by rho_n agrees with moving id from stage n to n+1. A preimage [k,u] of the compatible family gives, for each n, a later stage r_n with pi_n u rho_(k,r_n)=rho_(n,r_n). Composing with pi_(r_n) gives pi_n u pi_k=pi_n. Equality of every inverse-limit coordinate yields u pi_k=id.
2. The proposed inverse to Theta is h↦[k,h u]. One composite is h u pi_k=h; the other uses the same eventual equality after postcomposition by the representative's map. No strict layerwise compatibility of separately selected later-stage witnesses is needed.
3. Applying the eventual equation at n=k gives im rho_(k,m)=pi_k(L) for all sufficiently large m. For arbitrary n, take m beyond both its own witness and this stabilization stage. The equality of maps gives im rho_(n,m)=pi_n u(im rho_(k,m))=pi_n(L). Because L is a retract of finite-free P_k, all stable-image ranks have a uniform bound. This proves the claimed necessity without requiring the original rho_n to be injective or surjective.
4. Conversely, Mittag–Leffler stabilization makes I_(n+1)→I_n surjective: choose one common sufficiently late stage realizing both stable images. The ranks are therefore nondecreasing, and boundedness makes them eventually equal. A surjection between equal finite-rank free abelian groups is an isomorphism. This yields L≅I_N and pi_n(L)=I_n for every n.
5. Choose k≥N realizing I_N as the image of P_k. The map u:P_k→I_N≅L has the required eventual identities. For n<N they follow by composition through N. For n≥N choose a later stage whose image lies in I_n; equality after the injective isomorphism I_n→I_N forces equality before it. Thus [k,u] lifts c.
6. The dual/inverse-limit isomorphism holds for arbitrary towers, using the actual finite-free bidual identifications. Under finite generation the tensor–Hom representation becomes exactly Theta([n,v])=v pi_n. The displayed basis formula is its inverse, and rank zero is included.
7. The layerwise natural-transformation formula has the correct variance. Evaluating a transformation on [n,id] gives a class in F_Q(P_n), represented by Q_m→P_n. Adjacent compatibility is sufficient for all transitions, and postcomposition gives the stated action on every record. The composition formula Q/R indices agrees with ordinary composition on the invariant groups.
8. Every countable torsion-free group is the union of an increasing sequence of finite generated torsion-free, hence finite-free, subgroups. Dualizing their inclusions gives a tower whose dual direct limit is the original group. Thus the response's final essential-surjectivity statement is also valid.

The response's multiplier-two and coordinate-deletion examples correctly separate the two parts of its stable-image criterion. No assumption of eventual isomorphisms in the original tower is made or needed. The stronger optional results in this review are not silently included in the Lean coverage claim; see `COVERAGE.md` for the exact encoded boundary.
