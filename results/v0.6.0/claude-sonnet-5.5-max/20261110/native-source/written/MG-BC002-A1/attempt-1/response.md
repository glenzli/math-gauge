# Appendix and deployment note

**Verdict on the draft.** Parts 1 and 2 below are correct and proved. The sentence that connects them is false for this f, for every τ>0. The sentence is: "strongly convex, contractive, dissipative ⇒ T_τ = prox_{r_τ} for some proper lsc convex r_τ". A prox map is the gradient of a convex function, so its Jacobian is symmetric. The time-τ map of this gradient flow has a non-symmetric Jacobian (Theorem 5). Hence the certificate and firm nonexpansiveness of Part 2 cannot be claimed for the deployed block. What can be claimed is in Part 1 and is restated in Part 3.

## 0. Notation and elementary facts

Write z=(x,y), u:=x+y, e:=(1,1)ᵀ, e₁:=(1,0)ᵀ, A:=diag(1,2), R:=((0,1),(−1,0)), and ‖·‖ for the Euclidean norm.

- ∇f(z) = Az + u³e = (x+u³, 2y+u³).
- H(z) := ∇²f(z) = A + 3u²eeᵀ.
- f = f₂+f₄ with f₂=½(x²+2y²) and f₄=¼u⁴. By Euler's relation, ⟨∇f(z),z⟩ = 2f₂+4f₄ = x²+2y²+u⁴.

**(F1)** ⟨∇f(a)−∇f(b), a−b⟩ = (a−b)ᵀA(a−b) + (u_a³−u_b³)(u_a−u_b) ≥ ‖a−b‖². This uses A⪰I and that t↦t³ is increasing.

**(F2)** ⟨∇f(z),z⟩ ≥ ‖z‖². Hence ∇f(z)=0 iff z=0.

**(F3)** f(z) ≥ f₂(z) ≥ ½‖z‖², and f(0)=0.

**(F4)** ‖∇f(z)‖² ≥ 2f(z). Indeed f = ⟨∇f,z⟩ − f₂ − 3f₄ ≤ ‖∇f‖‖z‖ − ½‖z‖² ≤ ½‖∇f‖².

## 1. The exact flow

**Theorem 1.**
- (a) For every z, the problem ż=−∇f(z), z(0)=z has a unique solution on [0,∞). Write Φ_t(z):=z(t). Then Φ₀=id, Φ_{t+s}=Φ_t∘Φ_s, and (t,z)↦Φ_t(z) is C^∞.
- (b) The only equilibrium is 0, which is the unique minimizer of f. Also ‖Φ_t z‖ ≤ e^{−t}‖z‖.
- (c) ‖Φ_t z − Φ_t w‖ ≤ e^{−t}‖z−w‖.
- (d) f(Φ_t z) ≤ e^{−2t} f(z).

*Proof.*
- (a) ∇f is polynomial, hence locally Lipschitz. Picard–Lindelöf gives a unique maximal solution on [0,T*) with smooth dependence on (t,z). By (F2), d/dt ½‖z‖² = −⟨∇f(z),z⟩ ≤ −‖z‖², so ‖z(t)‖ ≤ e^{−t}‖z(0)‖ stays bounded and T*=∞. The semigroup law is uniqueness for an autonomous ODE. Only forward time is claimed: for ż=+∇f with x,y>0 one has u̇ ≥ 2u³, which blows up in finite time.
- (b) The uniqueness of the equilibrium and the minimizer follow from (F2) and (F3). The bound was shown in (a).
- (c) Let g(t)=½‖Φ_t z−Φ_t w‖². By (F1), g′ = −⟨∇f(Φ_t z)−∇f(Φ_t w), Φ_t z−Φ_t w⟩ ≤ −2g. So (e^{2t}g)′ ≤ 0.
- (d) Let E(t)=f(Φ_t z). Then E′ = −‖∇f(Φ_t z)‖² ≤ −2E by (F4). So (e^{2t}E)′ ≤ 0. ∎

*Sharpness.* DΦ_t(0)=e^{−tA} has norm e^{−t}, so (c) cannot be improved. Also f(Φ_t(se₁))/f(se₁) → e^{−2t} as s→0, so (d) cannot be improved.

**Corollary 1 (stack).** By the semigroup law, Z_n = T_τⁿ(Z₀) = Φ_{nτ}(Z₀). Hence for all n≥0:
- ‖Z_n‖ ≤ e^{−nτ}‖Z₀‖, and ‖Z_n−Z′_n‖ ≤ e^{−nτ}‖Z₀−Z′₀‖.
- f(Z_n) ≤ e^{−2nτ} f(Z₀).
- Both ‖Z_n‖ and f(Z_n) strictly decrease unless Z₀=0.
- n ≥ τ⁻¹ ln(‖Z₀‖/ε) blocks give ‖Z_n‖ ≤ ε. Likewise n ≥ (2τ)⁻¹ ln(f(Z₀)/ε) blocks give f(Z_n) ≤ ε.
- A computable stopping rule follows from ‖Z_n‖ ≤ ‖Z_n−Z_{n+1}‖ + e^{−τ}‖Z_n‖. It reads ‖Z_n‖ ≤ ‖Z_{n+1}−Z_n‖/(1−e^{−τ}).
- Only the total time nτ matters.

## 2. Proximal certificate and firm nonexpansiveness

Let r be proper, lsc and convex, and put φ_z(u)=r(u)+½‖u−z‖². Since r has an affine minorant, φ_z is lsc, strongly convex and coercive. So it has exactly one minimizer, prox_r(z). "T=prox_r" means T(z) is that minimizer for every z.

**Proposition 2.** Let p=prox_r(z). Then p∈dom r, and
- (2.1) r(u) ≥ r(p) + ⟨z−p, u−p⟩ for all u. That is, z−p∈∂r(p).
- (2.2) r(p) + ½‖p−z‖² + ½‖u−p‖² ≤ r(u) + ½‖u−z‖² for all u∈dom r.

*Proof.*
1. p∈dom r because φ_z(p) ≤ φ_z(u₀) < ∞ for any u₀∈dom r.
2. Fix u∈dom r and θ∈(0,1), and set u_θ=p+θ(u−p)∈dom r.
3. Convexity gives r(u_θ) ≤ r(p)+θ(r(u)−r(p)).
4. Expanding, ½‖u_θ−z‖² = ½‖p−z‖² + θ⟨p−z,u−p⟩ + ½θ²‖u−p‖².
5. Minimality, φ_z(p) ≤ φ_z(u_θ), then yields 0 ≤ θ(r(u)−r(p)) + θ⟨p−z,u−p⟩ + ½θ²‖u−p‖².
6. Divide by θ and let θ↓0. This gives (2.1), which is trivial if u∉dom r.
7. The identity 2⟨z−p,u−p⟩ = ‖z−p‖²+‖u−p‖²−‖u−z‖² turns (2.1) into (2.2). ∎

Inequality (2.2) says φ_z(u) ≥ φ_z(p)+½‖u−p‖², i.e. quadratic growth at the minimizer.

**Corollary 3 (firm nonexpansiveness).** If T=prox_r, then for all z,w
‖Tz−Tw‖² ≤ ⟨Tz−Tw, z−w⟩.
Equivalently, ‖Tz−Tw‖² + ‖(I−T)z−(I−T)w‖² ≤ ‖z−w‖². In particular T is monotone and 1-Lipschitz.

*Proof.*
1. Let p=Tz and q=Tw, both in dom r.
2. Apply (2.2) at z with u=q, apply (2.2) at w with u=p, and add. All terms are finite.
3. This gives ½‖p−z‖²+½‖q−w‖²+‖p−q‖² ≤ ½‖q−z‖²+½‖p−w‖².
4. Write q−z=(q−p)+(p−z) and p−w=(p−q)+(q−w), expand, and cancel.
5. What remains is 0 ≤ ⟨p−q, (z−p)+(q−w)⟩ = ⟨p−q, (z−w)−(p−q)⟩, which is the claim.
6. For the equivalent form, expand ‖z−w‖² = ‖p−q‖² + ‖(z−p)−(w−q)‖² + 2⟨p−q,(z−w)−(p−q)⟩.
7. Cauchy–Schwarz gives the Lipschitz bound. ∎

**Lemma 4 (prox maps are gradients).** If T=prox_r, then T=∇ψ with ψ:=(r+½‖·‖²)*, a finite convex function. If T is C¹, then DT(z) is symmetric for every z. By Corollary 3 it then also satisfies 0⪯DT⪯I.

*Proof.*
1. Put φ=r+½‖·‖², so ψ=φ*. Since φ(u) ≥ ½‖u‖²−c‖u‖−c′, ψ is finite.
2. p=T(z) minimizes φ−⟨z,·⟩, i.e. z∈∂φ(p), i.e. p∈∂ψ(z).
3. Conversely, if q∈∂ψ(z) then q also minimizes φ−⟨z,·⟩, so q=p. Thus ∂ψ(z)={T(z)}.
4. A finite convex function with single-valued subdifferential is differentiable (Rockafellar, Thm 25.1). So ∇ψ=T.
5. If T∈C¹, then ψ∈C² and DT=∇²ψ is symmetric by Schwarz's theorem. ∎

Remark (Moreau): conversely, T is a prox of a proper lsc convex function iff T is a nonexpansive gradient of a convex function. Contractivity and dissipativity of a flow say nothing about whether its time-τ map is a gradient.

## 3. The exact block is not a proximal map, for any τ>0

**Theorem 5.** For every τ>0 there is no proper lsc convex r with Φ_τ = prox_r.

*Proof.*
1. Φ_τ is C^∞, so by Lemma 4 it suffices to find one point where DΦ_τ is not symmetric.
2. K(t):=DΦ_t(z) solves K̇ = −H(Φ_t z)K with K(0)=I.
3. Take z=se₁ with 0<s≤1. Put η(t)=Φ_t(se₁) and u(t)=eᵀη(t).
4. (i) η̇=−Aη−u³e and ‖η‖≤se^{−t}. Variation of constants gives η(t)=se^{−t}e₁+O(s³) uniformly on [0,τ]. Hence u(t)²=s²e^{−2t}+O(s⁴).
5. (ii) Since 3u²eeᵀ=O(s²), Grönwall gives K(t)=e^{−tA}+O(s²). Variation of constants then gives
   K(τ) = e^{−τA} − 3s²∫₀^τ e^{−2t} v(τ−t)v(t)ᵀ dt + O(s⁴), where v(t):=e^{−tA}e=(e^{−t},e^{−2t})ᵀ.
6. (iii) e^{−τA} is diagonal. Also [v(τ−t)v(t)ᵀ]₁₂ = e^{−τ−t} and [v(τ−t)v(t)ᵀ]₂₁ = e^{−2τ+t}. Therefore
   K₁₂(τ)−K₂₁(τ) = −3s²∫₀^τ e^{−2t}(e^{−τ−t}−e^{−2τ+t}) dt + O(s⁴) = −s² e^{−τ}(1−e^{−τ})³ + O(s⁴).
7. The leading coefficient is nonzero for every τ>0. So DΦ_τ(se₁) is not symmetric for all small s≠0. ∎

Numerical check of the formula: at τ=1, s=0.03 the computed value is −8.352·10⁻⁵, against −8.363·10⁻⁵ predicted.

**Remarks.**
- **Small τ, general z.** Expanding the variational equation to third order (checked symbolically) gives DΦ_τ(z)−DΦ_τ(z)ᵀ = −τ³ u(x+2y+2u³) R + O(τ⁴). The defect is O(τ³) but never zero in general.
- **Mechanism.** A constant Hessian is fine: for f_q=½zᵀQz, Φ_τ=e^{−τQ}=prox_r with r(u)=½uᵀ(e^{τQ}−I)u. In dimension one, every flow map of a convex f is also a prox, since Φ_τ′∈(0,1]. Here the Hessians along a trajectory do not commute: [H(z₁),H(z₂)] = 3(u₁²−u₂²)R, and u(t)² varies along trajectories.
- **Stack.** Z_n=Φ_{nτ}(Z₀) is again a flow map, so the stack is not a prox either.

**Numerical corroboration (not used in the proof).** A prox would satisfy ⟨Tz−Tw,z−w⟩ ≥ ‖Tz−Tw‖² ≥ 0 by Corollary 3. The exact block violates this. I computed these with DOP853, Radau, LSODA and BDF, and with an independent 25-digit Taylor integrator; all agree to at least 8 digits.

| τ | z | w | Φ_τ z | Φ_τ w | ⟨Φz−Φw, z−w⟩ | ‖Φz−Φw‖² |
|---|---|---|---|---|---|---|
| 0.5 | (0,6) | (8,16) | (−1.347483, 1.366732) | (−1.901491, 1.759640) | −0.502980 | 0.461300 |
| 1 | (2,5) | (4,8) | (−0.303685, 0.282034) | (−0.467935, 0.356562) | −0.104916 | 0.032533 |
| 2 | (4,6) | (5,8) | (−0.049713, 0.027789) | (−0.109880, 0.038286) | −0.039174 | 0.003730 |

A scan over rays at several radii found points where the symmetric part of DΦ_τ(z) has a negative eigenvalue for each τ tested. DOP853 and Radau agree on this. The τ values and the radii at which it first appeared on my scan grid were:

| τ | 0.02 | 0.05 | 0.1 | 0.25 | 0.5 | 1 | 2 | 4 |
|---|---|---|---|---|---|---|---|---|
| \|z\| | 256 | 64 | 32 | 12 | 6 | 3 | 2 | 1 |

I do not claim this scan for all τ. The all-τ statement rests on Theorem 5.

The table can be reproduced with:

```python
import numpy as np
from scipy.integrate import solve_ivp
def rhs(t, z):
    u = z[0] + z[1]
    return [-(z[0] + u**3), -(2*z[1] + u**3)]
def Phi(z, tau):
    return solve_ivp(rhs, [0, tau], z, method="DOP853", rtol=1e-12, atol=1e-14).y[:, -1]
for tau, z, w in [(0.5, (0, 6), (8, 16)), (1.0, (2, 5), (4, 8)), (2.0, (4, 6), (5, 8))]:
    z, w = np.array(z, float), np.array(w, float)
    dp = Phi(z, tau) - Phi(w, tau)
    print(tau, dp @ (z - w), dp @ dp)
```

I did not formalize anything in Lean. Theorems 1 and 5, Proposition 2, Corollary 3 and Lemma 4 are proved by hand above. The tables and scans are numerical.

## 4. Deployment paragraph (methods section)

> Each block applies T_τ = Φ_τ, the exact time-τ map of the gradient flow ż = −∇f(z), f(x,y) = ½(x²+2y²) + ¼(x+y)⁴. Here τ>0 is an evolution time. The flow exists for all t≥0 and forms a semigroup, so n stacked blocks give exactly Z_n = Φ_{nτ}(Z₀). Only the total time nτ matters.
>
> **Guarantees.**
> - 0 = argmin f is the unique fixed point of every block.
> - ‖Φ_τ z−Φ_τ w‖ ≤ e^{−τ}‖z−w‖ and f(Φ_τ z) ≤ e^{−2τ}f(z), and both constants are sharp.
> - Hence ‖Z_n‖ ≤ e^{−nτ}‖Z₀‖, f(Z_n) ≤ e^{−2nτ}f(Z₀), and input perturbations are damped by e^{−nτ}.
> - n ≥ τ⁻¹ln(‖Z₀‖/ε) blocks give accuracy ε.
> - ‖Z_n‖ ≤ ‖Z_{n+1}−Z_n‖/(1−e^{−τ}) is a computable stopping rule.
>
> **Not guaranteed.** The block is not the proximal map of any proper lsc convex function, for any τ>0. Its Jacobian is not symmetric, and in general it is not monotone, hence not firmly nonexpansive. The three-point inequality and ⟨Tz−Tw,z−w⟩ ≥ ‖Tz−Tw‖² therefore do not apply to the deployed block, and it must not be described as an exact convex regularization step.
>
> **Relation to prox.** In the convention prox_r(z)=argmin{r(u)+½‖u−z‖²}, the proximal coefficient λ is the weight of f inside r=λf. The map prox_{λf} is the implicit-Euler step of size λ:
> - It satisfies the Part 2 certificate.
> - It is a (1+λ)⁻¹-contraction: by (F1), p+λ∇f(p)=z gives (1+λ)‖p−q‖² ≤ ⟨z−w,p−q⟩.
> - It satisfies f(prox_{λf}z) ≤ (1+λ)⁻²f(z): by strong convexity, f(z) ≥ f(p)+(λ+λ²/2)‖∇f(p)‖², and then (F4) applies.
>
> It is a different map from Φ_τ. The two agree only to first order: Φ_τ(z)−prox_{τf}(z) = −(τ²/2)∇²f(z)∇f(z)+O(τ³). The exact block is the limit of proximal steps, Φ_τ = lim_{N→∞}(prox_{(τ/N)f})^N (Crandall–Liggett exponential formula; numerically the error is about 1.7/N at τ=1, z=(2,5)). Even for the quadratic part ½zᵀAz alone, e^{−τA} is a prox with r=½uᵀ(e^{τA}−I)u. That weight is e^{τA}−I, not τA, so the evolution time and the prox coefficient are different quantities even where an exact prox form exists.