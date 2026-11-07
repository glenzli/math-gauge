# Reference: exact flow versus convex proximal representability

## Status and scope

Constructed, untested candidate. No target-model solve has been run. The embedded rationale is false; all explicitly requested quantitative flow bounds and the conditional proximal certificate are true. The obstruction below proves failure of proximal representability for every sufficiently small positive time, which refutes the rationale's assertion for every positive time. It does not assert failure at an arbitrary prescribed large time or give a certified numerical threshold.

## True flow results

Let e=(1,1)^T, D=diag(1,2), and s=x+y. Then

∇f(z)=Dz+s³e,  H(z)=∇²f(z)=D+3s²ee^T ⪰ I.

Thus f is 1-strongly convex, nonnegative, coercive, and has its unique minimizer and only equilibrium at 0. The polynomial vector field is smooth and locally Lipschitz, hence has unique local solutions. Along a solution,

(d/dt)f(z(t))=−||∇f(z(t))||²≤0.

The solution remains in the compact sublevel set {f≤f(z(0))}. The continuation theorem therefore gives a solution for every t≥0. Smooth dependence on initial conditions holds on each finite forward interval, including in an open neighborhood of each initial condition. The flow need not be backward-global, and the proof does not require it.

Strong monotonicity gives

(d/dt)||z(t)−w(t)||² = −2⟨z−w,∇f(z)−∇f(w)⟩ ≤ −2||z−w||².

Gronwall yields the requested e^(−t) contraction. Taking w=0 yields ||Φ_t(z)||≤e^(−t)||z||.

The strong-convexity inequality with comparison point 0 gives

0 ≥ f(z)−⟨∇f(z),z⟩+||z||²/2 ≥ f(z)−||∇f(z)||²/2.

Hence ||∇f||²≥2f and the energy identity yields f(Φ_t(z))≤e^(−2t)f(z). The autonomous semigroup gives T_τ^n=Φ_(nτ), so every preceding bound holds with t=nτ. Optional stochastic consequence (not requested in the final prompt): for Z_0∼N(0,I₂), E||Z_0||²=2 and E f(Z_0)=3/2+12/4=9/2, since X+Y∼N(0,2). Therefore

E||Z_n||² ≤ 2e^(−2nτ),  E f(Z_n) ≤ (9/2)e^(−2nτ).

These conclusions concern the ideal exact flow. Numerical solvers need separate error estimates. They say contraction to zero and decay of the specified energy, not statistical denoising optimality or preservation of a data distribution.

## True conditional proximal results

For a proper lsc convex r, the objective r(u)+||u−z||²/2 has a unique minimizer p, and z−p∈∂r(p). The subgradient inequality is

r(u) ≥ r(p)+⟨z−p,u−p⟩.

Expanding ||u−z||² proves exactly the requested three-point inequality. If q=prox_r(w), monotonicity of ∂r gives

⟨(z−p)−(w−q),p−q⟩≥0,

or ||p−q||²≤⟨z−w,p−q⟩. These implications are valid with explicit hypotheses. They do not establish those hypotheses for Φ_τ. The parameter τ is evolution time. A factor τ in prox_(τr) would multiply r in the objective, but no identification r_τ=τf or existence of r_τ follows from the ODE. Implicit Euler is prox_(τf); exact autonomous evolution generally is not.

## The embedded all-time proximal claim is false

Fix initial condition z₀=(1,0). Define z(t)=Φ_t(z₀), H(t)=∇²f(z(t)), and K(t)=D_zΦ_t(z₀). Smooth dependence gives

K′=−HK, K(0)=I.

All derivatives used below are ordinary time derivatives at this fixed initial state. At t=0, s=1 and z′=(−2,−1), so s′=−3. Consequently

H₀=[[4,3],[3,5]],
H′₀=−18ee^T,
H″₀=186ee^T.

For the last value, z″=−H₀z′=(11,11), s″=22, and H″=6((s′)²+s s″)ee^T.

Differentiating the variational equation gives

K′₀=−H₀,
K″₀=−H′₀+H₀²,
K‴₀=−H″₀+2H′₀H₀+H₀H′₀−H₀³.

The first two derivatives are symmetric, while

K‴₀−(K‴₀)^T = H′₀H₀−H₀H′₀ = [[0,−18],[18,0]].

Taylor expansion thus gives

K₁₂(t)−K₂₁(t)=−3t³+O(t⁴).

Local smoothness of the polynomial ODE and its variational equation justifies the Taylor remainder. Dividing by t³ and taking t↓0 proves existence of ε>0 such that K₁₂(t)−K₂₁(t)<0 for every 0<t<ε. No unspecified remainder is used to certify a numerical ε or a particular step such as τ=0.1.

Now suppose Φ_t=prox_g globally for a proper lsc convex g. Its Moreau envelope

M_g(z)=inf_u {g(u)+||u−z||²/2}

is finite C¹ on R² and ∇M_g(z)=z−prox_g(z). Thus prox_g=∇ψ with ψ(z)=||z||²/2−M_g(z). This ψ is convex, although convexity is not needed for the following symmetry obstruction. Since Φ_t is C¹, ∇ψ=Φ_t is C¹, so ψ is C² and DΦ_t=∇²ψ must be symmetric. The computed nonsymmetry at z₀ excludes every such g for every 0<t<ε. It also excludes a local equality with a smooth proximal map on a neighborhood of z₀. It is not merely a demonstration that Φ_t differs from prox_(tf).

The phenomenon is time ordering: instantaneous Hessians are symmetric, but the variational evolution is a time-ordered product of them, not the ordinary exponential of a single fixed symmetric matrix. Their noncommutativity can generate a nonsymmetric endpoint Jacobian. Contractivity and dissipativity do not repair this missing integrability property.

## Suitable methods paragraph

“The block evolves the autonomous gradient flow of the 1-strongly convex energy f for a time τ. Exact blocks are globally defined, contract distances by at least e^(−τ), and reduce f by at least e^(−2τ). A stack of n exact blocks equals evolution for time nτ and converges exponentially to the unique equilibrium 0. The proximal three-point inequality is a certificate conditional on a convex proximal representation; it is not a certificate for this flow merely because its vector field is a convex gradient. In fact, a nonsymmetric flow Jacobian excludes such a representation for all sufficiently small positive τ. Numerical implementation requires its own integration-error analysis.”

A solution can be safe without doing the obstruction calculation: all true estimates plus a properly conditional certificate and no affirmative endorsement of the embedded actual-prox claim are acceptable. It need not discover the reference proof to avoid a false assertion.
