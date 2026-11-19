I treat this as a review as well as an appendix: the central claim of the design rationale is false, so the methods paragraph cannot use it.

**Summary.**
- Items 1 and 2 are correct as stated. Proofs are in §A1–A3.
- The claim "for every τ>0, T_τ = prox_{r_τ} for some proper lsc convex r_τ" is false for **every** τ>0. In fact Φ_τ is not a prox of *any* function r, convex or not (Theorem A4, proved below).
- So the three-point certificate and firm nonexpansiveness cannot be used for the deployed block. Numerically, the block even fails to be monotone at τ=1.
- The deployment paragraph (§B) states only what actually holds.

---

# Appendix

## A1. Setting, well-posedness, equilibrium

**Derivatives.** Write u = x+y, D = diag(1,2) and J = (1,1)ᵀ(1,1) ⪰ 0. Then

∇f(z) = (x+u³, 2y+u³),  ∇²f(z) = D + 3u²J ⪰ D ⪰ I.

So f is 1-strongly convex and f(z) ≥ ½‖z‖².

**Equilibrium.** ∇f = 0 gives x = −u³ = 2y. Substituting, 2y + 27y³ = 0, so y = 0 and x = 0. The point z* = 0 is the unique critical point and the global minimiser, with f(0) = 0.

**Two inequalities.** For all a, b:
- ∇f(a) − ∇f(b) = A(a−b) with A = ∫₀¹∇²f(b+θ(a−b))dθ ⪰ I. Hence ⟨∇f(a)−∇f(b), a−b⟩ ≥ ‖a−b‖².  (M)
- Strong convexity gives f(w) ≥ f(z) + ⟨∇f(z), w−z⟩ + ½‖w−z‖² ≥ f(z) − ½‖∇f(z)‖². Taking the infimum over w gives the Polyak–Łojasiewicz inequality ‖∇f(z)‖² ≥ 2f(z).  (PL)

**Forward global well-posedness.** ∇f is polynomial, hence C^∞ and locally Lipschitz. Picard–Lindelöf gives a unique maximal solution on [0, t*). Along it, d/dt f(z(t)) = −‖∇f(z(t))‖² ≤ 0. Therefore ‖z(t)‖² ≤ 2f(z(t)) ≤ 2f(z₀), so the solution stays bounded and t* = ∞.

Consequences:
- Φ_t is defined on all of ℝ² for every t ≥ 0.
- (t,z) ↦ Φ_t(z) is C^∞ (smooth dependence on initial data).
- Φ_{t+s} = Φ_t∘Φ_s, by uniqueness.
- Φ_t(0) = 0.
- 0 is the only fixed point of T_τ: if Φ_τ(z) = z, then 0 = f(z) − f(Φ_τ z) = ∫₀^τ‖∇f(Φ_s z)‖²ds, so ∇f(z) = 0.

## A2. Contraction, energy decay, stacks

Let δ(t) = Φ_t(z) − Φ_t(w). By (M),

d/dt ‖δ‖² = −2⟨∇f(Φ_t z) − ∇f(Φ_t w), δ⟩ ≤ −2‖δ‖².

Grönwall's inequality gives **‖Φ_t(z) − Φ_t(w)‖ ≤ e^{−t}‖z−w‖**.

By (PL), d/dt f(Φ_t z) = −‖∇f‖² ≤ −2f(Φ_t z). Hence **f(Φ_t z) ≤ e^{−2t} f(z)**.

Both rates are sharp: DΦ_t(0) = e^{−tD}. Taking z = (ε,0), w = 0 and letting ε→0, the ratios tend to e^{−t} and e^{−2t}.

**Stacks.** By the semigroup property, Z_n = T_τⁿ(Z₀) = Φ_{nτ}(Z₀). Therefore:
- ‖T_τⁿz − T_τⁿw‖ ≤ e^{−nτ}‖z−w‖;
- ‖Z_n‖ ≤ e^{−nτ}‖Z₀‖;
- f(Z_n) ≤ e^{−2nτ}f(Z₀);
- ‖Z_n‖ ≤ e^{−nτ}√(2f(Z₀));
- ‖Z_{n+1} − Z_n‖ ≤ e^{−nτ}‖Z₁ − Z₀‖.

So ‖Z_n‖ ≤ ε once n ≥ τ⁻¹ log(‖Z₀‖/ε). Only the total time nτ matters.

**Averagedness.** T_τ is α-averaged with α = (1+e^{−τ})/2. To see this, write N = (T_τ − (1−α)I)/α. Its Lipschitz constant is at most ((1−α) + e^{−τ})/α = 1.

**Inexact implementation.** If each block is computed with error at most η, then Z̃_{k+1} = T_τ(Z̃_k) + e_k with ‖e_k‖ ≤ η. Since T_τ(0) = 0, this gives ‖Z̃_n‖ ≤ e^{−nτ}‖Z₀‖ + η/(1−e^{−τ}).

## A3. The proximal certificate (valid for genuine prox maps)

**Proposition.** Let r be proper, lsc and convex, and let p = prox_r(z). Then p ∈ dom r, and for every u ∈ dom r:

r(p) + ½‖p−z‖² + ½‖u−p‖² ≤ r(u) + ½‖u−z‖².

*Why the prox is well defined.* F(u) = r(u) + ½‖u−z‖² is lsc and 1-strongly convex. Since r has an affine minorant, F is coercive. So F has a unique minimiser p, and F(p) < ∞, which gives p ∈ dom r.

*Proof of the inequality.* Let u ∈ dom r, θ ∈ (0,1) and u_θ = p + θ(u−p). Use convexity of r and the identity

‖(1−θ)a + θb‖² = (1−θ)‖a‖² + θ‖b‖² − θ(1−θ)‖a−b‖²,

with a = p−z and b = u−z. This gives

F(p) ≤ F(u_θ) ≤ (1−θ)F(p) + θF(u) − ½θ(1−θ)‖u−p‖².

Subtract (1−θ)F(p), divide by θ, and let θ↓0. The result is F(p) + ½‖u−p‖² ≤ F(u). ∎

*Subgradient form.* Expanding ‖u−z‖² = ‖u−p‖² + 2⟨u−p, p−z⟩ + ‖p−z‖² turns the certificate into r(u) ≥ r(p) + ⟨z−p, u−p⟩, that is, z − p ∈ ∂r(p).

**Firm nonexpansiveness.** Let p = T(z) and q = T(w).
1. Apply the certificate at (z, p) with u = q, and at (w, q) with u = p.
2. Add the two inequalities and cancel r(p) + r(q).
3. Use ‖q−z‖² − ‖p−z‖² = ‖q−p‖² + 2⟨q−p, p−z⟩ and ‖p−w‖² − ‖q−w‖² = ‖p−q‖² + 2⟨p−q, q−w⟩.

This leaves 0 ≤ ⟨q−p, (p−q) − (z−w)⟩, i.e.

**‖T z − T w‖² ≤ ⟨T z − T w, z − w⟩.**

In particular T is monotone and nonexpansive.

**Lemma G (gradient structure; convexity of r not needed).** Let r: ℝ² → (−∞, ∞] be any function. Suppose T is continuous and T(z) ∈ argmin_u{r(u) + ½‖u−z‖²} for every z. Then T = ∇φ for a convex C¹ function φ.

*Proof.* Define φ(z) = sup_u{⟨z,u⟩ − r(u) − ½‖u‖²}. It is convex as a supremum of affine functions. It is finite, because the supremum is attained at u = T(z).
- From the definition, φ(w) ≥ ⟨w, T z⟩ − r(T z) − ½‖T z‖² = φ(z) + ⟨w−z, T z⟩.
- Swapping z and w gives φ(z) ≥ φ(w) + ⟨z−w, T w⟩.

Combining the two,

0 ≤ φ(w) − φ(z) − ⟨T z, w−z⟩ ≤ ⟨T w − T z, w−z⟩ = o(‖w−z‖).

So φ is differentiable with ∇φ = T. ∎

*Corollary.* If T is also C¹, then φ ∈ C² and DT(z) = ∇²φ(z). So DT(z) must be symmetric and positive semidefinite for every z.

## A4. The exact block is not a proximal map

**Theorem.** For every τ>0 there is no function r (convex or not, lsc or not) with Φ_τ(z) ∈ prox_r(z) for all z. In particular T_τ ≠ prox_{r_τ} for every proper lsc convex r_τ.

*Proof.* Φ_τ is C^∞, so by Lemma G it would need a symmetric Jacobian everywhere. We show it does not.

1. **Setup.** Fix τ>0. Let z_ε = (ε,0), M_ε(t) = DΦ_t(z_ε) and u_ε(t) = (1,1)·Φ_t(z_ε). The matrix M_ε solves Ṁ = −(D + a_ε(t)J)M with M(0) = I, where a_ε = 3u_ε². By variation of constants,

   M_ε(τ) = e^{−τD} − ∫₀^τ e^{−(τ−s)D} a_ε(s) J M_ε(s) ds.

   All quantities are jointly C^∞ in (s, ε).

2. **Derivatives at ε = 0.** We have Φ_s(0) = 0, so u₀ ≡ 0. Also ∂_εΦ_s(z_ε)|₀ = e^{−sD}e₁, so ∂_εu|₀ = e^{−s}. Hence a₀ ≡ 0, ∂_εa|₀ ≡ 0 and ∂²_εa|₀ = 6e^{−2s}. Since M₀(s) = e^{−sD}, differentiating twice gives ∂_εM_ε(τ)|₀ = 0 and

   ∂²_εM_ε(τ)|₀ = −6∫₀^τ e^{−2s} e^{−(τ−s)D} J e^{−sD} ds.

3. **The antisymmetric entry.** In the matrix e^{−(τ−s)D} J e^{−sD}, entry (2,1) is e^{−2τ+s} and entry (1,2) is e^{−τ−s}. Let ω(ε) = (M_ε(τ))₂₁ − (M_ε(τ))₁₂. Then ω(0) = ω′(0) = 0 and

   ω″(0) = −6∫₀^τ (e^{−2τ−s} − e^{−τ−3s}) ds = 2e^{−4τ}(e^τ − 1)³ > 0.

4. **Conclusion.** By Taylor's theorem, ω(ε) = e^{−4τ}(e^τ−1)³ε² + o(ε²). For small ε ≠ 0 this is nonzero, so DΦ_τ(ε,0) is not symmetric. ∎

**Numerical check.** I integrated the variational equations with DOP853 at rtol 10⁻¹³.
- With ε = 10⁻², ω/ε² matches e^{−4τ}(e^τ−1)³ to about 4 digits for τ = 0.1, 0.5, 1, 2, 5.
- At z = (1,0), τ = 1: DΦ₁ ≈ [[0.2090, −0.1120], [−0.0750, 0.0888]], which is clearly not symmetric.

**Remarks.**

*Monotonicity failure (numerical, not a proof).* Take τ = 1. Three methods (DOP853, Radau/LSODA, and 30-digit mpmath Taylor) agree to at least 10 digits:
- Φ₁(1,2) ≈ (0.0114434, 0.1275112)
- Φ₁(6,10) ≈ (−0.4666463, 0.3563750)

So ⟨Φ₁(6,10) − Φ₁(1,2), (5,8)⟩ ≈ **−0.5595 < 0**. A genuine prox would give at least ‖ΔT‖² ≈ 0.281 (firm nonexpansiveness), and the gradient of any convex function would give at least 0. On integer grids, violations also appear at τ = 2, e.g. z = (1,0), w = (2,2), giving −0.016. I found none at τ = 0.5 on the grid [−6,6]², but the Jacobian test for firm nonexpansiveness fails there too.

*Mechanism.* The Hessians along a trajectory are D + 3u(t)²J, and

[D + aJ, D + bJ] = (b−a)[D,J],  with [D,J] = [[0,−1],[1,0]] ≠ 0.

So they do not commute whenever u² changes along the trajectory. The time-ordered product DΦ_τ = 𝒯exp(−∫H) is then not symmetric.

*When the claim does hold.* If f = ½⟨Az,z⟩ is quadratic, then e^{−τA} = prox_r with r(u) = ½⟨(e^{τA}−I)u,u⟩. Likewise, DΦ_τ(0) = e^{−τD} is the prox of ½[(e^τ−1)x² + (e^{2τ}−1)y²]. The claim also holds if the quadratic part were isotropic, because f would then separate in the coordinates x+y, x−y. Here the anisotropic weights (1,2) together with the coupling (x+y)⁴ break it.

## A5. Evolution time τ versus the prox coefficient

In our convention the quadratic term in prox_r has the fixed weight ½. A step size λ can only enter as prox_{λg}, meaning r = λg; τ appears nowhere in that definition.

- **Implicit Euler is a prox.** The implicit-Euler step with time τ is J_τ = (I+τ∇f)⁻¹ = prox_{τf}. It is a genuine convex prox, with r = τf.
- **The exact flow differs at second order.** Φ_τ(z) = z − τ∇f + (τ²/2)∇²f∇f + O(τ³), whereas prox_{τf}(z) = z − τ∇f + τ²∇²f∇f + O(τ³).
- **The exact flow is a limit of proxes, not a prox.** By the exponential formula (Crandall–Liggett/Brezis), Φ_τ = lim_{n→∞} (prox_{(τ/n)f})ⁿ. Compositions of proxes are generally not proxes, and here the limit is not one.
- **Even the linearisation is not a rescaled energy.** DΦ_τ(0) = e^{−τD} would equal (I+λD)⁻¹ only if e^τ = 1+λ and e^{2τ} = 1+2λ. That forces τ = 0. The "effective coefficient" is e^{kτ}−1 in each eigen-direction (k = 1, 2), not τ.

---

# B. Deployment paragraph (methods section)

Each block is the exact time-τ map T_τ = Φ_τ of the gradient flow ż = −∇f, where f(x,y) = ½(x²+2y²) + ¼(x+y)⁴ is 1-strongly convex with unique minimiser 0. T_τ is a well-defined smooth map on ℝ², and 0 is its only fixed point. It is a strict contraction, ‖T_τz − T_τw‖ ≤ e^{−τ}‖z−w‖, and it decreases the energy, f(T_τz) ≤ e^{−2τ}f(z); both rates are sharp. Because T_τⁿ = Φ_{nτ}, a stack of n blocks satisfies ‖Z_n‖ ≤ e^{−nτ}‖Z₀‖, f(Z_n) ≤ e^{−2nτ}f(Z₀) and ‖Z_n‖ ≤ e^{−nτ}√(2f(Z₀)). These guarantees depend only on the total evolution time nτ, so accuracy ε is reached once n ≥ τ⁻¹log(‖Z₀‖/ε). If each block is computed with error at most η, the bound becomes ‖Z_n‖ ≤ e^{−nτ}‖Z₀‖ + η/(1−e^{−τ}). Each block is (1+e^{−τ})/2-averaged. It is **not** a proximal or convex-regularisation step. Here τ is an evolution time, not a prox coefficient: the proximal step with our unit-weight convention is the implicit-Euler map (I+τ∇f)⁻¹ = prox_{τf}, which agrees with T_τ only to first order in τ. For no τ>0 is T_τ equal to prox_r for any function r, convex or not, because its Jacobian is not symmetric. Proximal certificates and firm nonexpansiveness therefore do not apply to the deployed block, and numerically it is not even monotone at τ = 1.