I have to start with a correction. The sentence "for every τ>0, the exact block has a convex proximal representation T_τ=prox_{r_τ}" is false, and it is false for every τ>0. The rest of the appendix is written around that fact.

## Summary

- **Item 1 holds.** Forward global well-posedness, the unique equilibrium 0, the bound ‖Φ_t z−Φ_t w‖≤e^{−t}‖z−w‖, the bound f(Φ_t z)≤e^{−2t}f(z), and convergence of the stack are all proved in A.
- **The prox claim fails.** If a C¹ map is a proximal map, it is the gradient of a convex function, so its Jacobian is symmetric (B.4). DΦ_τ is not symmetric for any τ>0 (Theorem C.1). So Φ_τ ≠ prox_r for every proper lsc convex r, and in fact for any function r at all.
- **Why the premises don't help.** "Strongly convex energy, contractive, dissipative" are all true, but they do not imply a prox representation. They would in 1D or for quadratic f, but not here.
- **Firm nonexpansiveness also fails.** Numerically, Φ₁ is not even monotone, so the firm nonexpansiveness derived in item 2 does not hold for the deployed block.

**Notation.** z=(x,y), s=x+y=𝟏ᵀz with 𝟏=(1,1)ᵀ, D=diag(1,2), J=𝟏𝟏ᵀ (so ‖J‖=2), d₁=1, d₂=2. Then

$$\nabla f(z)=Dz+s^3\mathbf 1=\begin{pmatrix}x+s^3\\ 2y+s^3\end{pmatrix},\qquad \nabla^2 f(z)=D+3s^2J\succeq D\succeq I .$$

---

## A. Well-posedness, equilibrium, contraction, energy decay (item 1)

**A.1 Strong convexity.**

$$\langle\nabla f(z)-\nabla f(w),z-w\rangle=(x-x')^2+2(y-y')^2+(s^3-s'^3)(s-s')\ \ge\ \|z-w\|^2,$$

because (a³−b³)(a−b)=(a−b)²(a²+ab+b²)≥0.

Since ∇²f⪰I, Taylor's formula gives

$$f(w)\ge f(z)+\langle\nabla f(z),w-z\rangle+\tfrac12\|w-z\|^2. \tag{A.1}$$

Also f(z)≥½‖z‖².

**A.2 Forward global well-posedness.**
- −∇f is a polynomial, so it is C^∞ and locally Lipschitz. Picard–Lindelöf gives a unique maximal solution on [0,T*).
- Along it, d/dt f(z(t))=−‖∇f(z(t))‖²≤0. Hence ½‖z(t)‖²≤f(z(t))≤f(z₀), so the solution stays in a compact set and T*=∞.
- Consequently Φ_t is defined on all of ℝ² for every t≥0. It satisfies Φ₀=id and Φ_{t+s}=Φ_t∘Φ_s. The map (t,z)↦Φ_t(z) is C^∞.
- M(t)=DΦ_t(z) solves the variational equation Ṁ=−∇²f(Φ_t z)M with M(0)=I.
- The flow is only a forward semiflow. For the reversed field the open first quadrant is invariant and ṡ≥2s³ there. So the backward solution from (a,a), a>0, blows up before time 1/(16a²), and (a,a)∉Φ_t(ℝ²) once t≥1/(16a²).

**A.3 Equilibrium.**
- ∇f=0 gives x=−s³ and 2y=−s³. Then x=2y, s=3y, and y(2+27y²)=0, so y=0 and x=0.
- The unique equilibrium is z*=0. It is the unique minimizer of f, with f(0)=0.
- Its linearization is DΦ_t(0)=e^{−tD}=diag(e^{−t},e^{−2t}).

**A.4 Contraction.**
- By A.1, d/dt ½‖Φ_t z−Φ_t w‖² = −⟨∇f(Φ_t z)−∇f(Φ_t w), Φ_t z−Φ_t w⟩ ≤ −‖Φ_t z−Φ_t w‖².
- Grönwall then gives **‖Φ_t(z)−Φ_t(w)‖≤e^{−t}‖z−w‖**.
- Taking w=0 gives ‖Φ_t z‖≤e^{−t}‖z‖.

**A.5 Energy decay.**
- Minimizing the right-hand side of (A.1) over w gives f(w)≥f(z)−½‖∇f(z)‖² for all w. With w=0 this is the Polyak–Łojasiewicz inequality ‖∇f(z)‖²≥2f(z).
- So d/dt f(z(t))≤−2f(z(t)), which gives **f(Φ_t z)≤e^{−2t}f(z)**.
- Similarly, g=∇f(z(t)) satisfies ġ=−∇²f g, so ‖∇f(Φ_t z)‖≤e^{−t}‖∇f(z)‖.
- Both rates are sharp: since DΦ_t(0)=e^{−tD}, along z=εe₁ with ε→0 the ratios tend to e^{−t} and e^{−2t}.

**A.6 Integrated evolution variational inequality (EVI).**
- For any u, A.1 gives d/dt ½‖z(t)−u‖² = ⟨∇f(z),u−z⟩ ≤ f(u)−f(z(t))−½‖z(t)−u‖².
- Multiply by eᵗ, integrate over [0,τ], and use f(z(t))≥f(z(τ)) for t≤τ:

$$\tfrac{e^{\tau}}2\|\Phi_\tau z-u\|^2+(e^\tau-1)f(\Phi_\tau z)\le \tfrac12\|z-u\|^2+(e^\tau-1)f(u)\qquad\forall u. \tag{EVI$_\tau$}$$

**A.7 Stack.** Since T_τⁿ=Φ_{nτ}, we have Z_n=Φ_{nτ}(Z₀). Therefore:
- ‖Z_n−Z_n'‖≤e^{−nτ}‖Z₀−Z₀'‖ (stability under input perturbations).
- ‖Z_n‖≤e^{−nτ}‖Z₀‖, so ‖Z_n‖≤ε as soon as n≥τ^{−1}ln(‖Z₀‖/ε).
- f(Z_n)≤e^{−2nτ}f(Z₀). Also, from EVI_{nτ} with u=0, f(Z_n)≤‖Z₀‖²/(2(e^{nτ}−1)); this bound does not involve the quartic part of f(Z₀).
- ‖∇f(Z_n)‖≤e^{−nτ}‖∇f(Z₀)‖ and ‖Z_{n+1}−Z_n‖≤e^{−nτ}‖Z₁−Z₀‖.
- The only fixed point of T_τ is 0, and the results depend on n and τ only through the total time nτ.

---

## B. The proximal certificate (item 2)

**B.0 Well-definedness.** Let r be proper, lsc and convex. Then r has an affine minorant. So φ_z(u)=r(u)+½‖u−z‖² is lsc, coercive and 1-strongly convex, and prox_r(z) exists and is unique. It lies in dom r.

**B.1 Lemma (certificate).** If p=prox_r(z), then for every u∈dom r:

$$r(p)+\tfrac12\|p-z\|^2+\tfrac12\|u-p\|^2\le r(u)+\tfrac12\|u-z\|^2.$$

*Proof.*
- Let u_θ=(1−θ)p+θu with θ∈(0,1).
- Convexity of r gives r(u_θ)≤(1−θ)r(p)+θr(u).
- The identity ‖(1−θ)a+θb‖²=(1−θ)‖a‖²+θ‖b‖²−θ(1−θ)‖a−b‖², with a=p−z and b=u−z, gives φ_z(u_θ)≤(1−θ)φ_z(p)+θφ_z(u)−½θ(1−θ)‖u−p‖².
- Minimality gives φ_z(p)≤φ_z(u_θ). Subtract (1−θ)φ_z(p), divide by θ, and let θ↓0 to get φ_z(p)+½‖u−p‖²≤φ_z(u). ∎

Conversely, if p satisfies this inequality for all u, then p=prox_r(z).

**B.2 Firm nonexpansiveness.**
- Let p=Tz and p'=Tz'. Apply B.1 at z with u=p', and at z' with u=p.
- Add the two inequalities. The r-terms cancel. Expanding ‖p'−z‖² and ‖p−z'‖² around p and p' leaves

$$\|Tz-Tz'\|^2\le\langle Tz-Tz',\,z-z'\rangle .$$

- Equivalently, ‖Tz−Tz'‖²+‖(I−T)z−(I−T)z'‖²≤‖z−z'‖².
- So T is nonexpansive and monotone, and I−T is firmly nonexpansive as well.

**B.3 Gradient structure (the property that can be tested).**
- Let e(z)=min φ_z=r(Tz)+½‖Tz−z‖² and ψ=½‖·‖²−e.
- Using p=Tz as a competitor at z' gives e(z')≤e(z)+⟨z−p,z'−z⟩+½‖z'−z‖². In terms of ψ this reads ψ(z')≥ψ(z)+⟨Tz,z'−z⟩, so ψ is convex.
- Swapping z and z' gives 0≤ψ(z')−ψ(z)−⟨Tz,z'−z⟩≤⟨Tz'−Tz,z'−z⟩≤‖z'−z‖².
- Hence **T=∇ψ with ψ convex and C^{1,1}**.

**B.4 Corollary.** If T=prox_r and T∈C¹, then DT=∇²ψ is **symmetric**, and by B.2 its eigenvalues lie in [0,1]. In particular ∂ₓT₂=∂_yT₁. (This is the necessity half of Moreau's characterization.)

**B.5 Remark.** B.3 used only that p minimizes φ_z, not that r is convex. So if *any* function r has a continuous single-valued prox map Φ, then Φ=∇ψ with ψ(z)=sup_u{⟨u,z⟩−r(u)−½‖u‖²} convex. Differentiability comes from ⟨Φz,z'−z⟩≤ψ(z')−ψ(z)≤⟨Φz',z'−z⟩ together with continuity of Φ.

---

## C. The exact block is not a proximal map

**Theorem C.1.** For every τ>0, Φ_τ is not a gradient field. Hence there is no function r (convex or not, and in particular no proper lsc convex r_τ) with Φ_τ=prox_r.

The theorem follows from B.4/B.5 and the following lemma.

**Lemma C.2.** For t>0 and 0<ε≤1:

$$\Big|\partial_x\Phi_t^{(2)}(\varepsilon e_1)-\partial_y\Phi_t^{(1)}(\varepsilon e_1)-\varepsilon^2e^{-t}(1-e^{-t})^3\Big|\le 156\,t^2\varepsilon^4 .$$

So the Jacobian is not symmetric at εe₁ whenever ε²<e^{−t}(1−e^{−t})³/(156t²).

*Proof.* Write z(σ)=Φ_σ(εe₁), s(σ)=𝟏ᵀz(σ) and M(σ)=DΦ_σ(εe₁) for σ∈[0,t].

1. By A.4, ‖z(σ)‖≤ε, so |s|≤√2ε, and ‖M(σ)‖≤e^{−σ}≤1.
2. Variation of constants: z(σ)=εe^{−σ}e₁−∫₀^σ e^{−(σ−ρ)D}s³𝟏 dρ, with ‖s³𝟏‖≤4ε³.
   - Hence ‖z(σ)−εe^{−σ}e₁‖≤4σε³.
   - So |s−εe^{−σ}|≤4√2σε³ and |s²−ε²e^{−2σ}|≤14σε⁴.
3. M(σ)=e^{−σD}−3∫₀^σ e^{−(σ−ρ)D}s²JM dρ, so ‖M(σ)−e^{−σD}‖≤12σε².
4. Write s²JM=ε²e^{−2σ}Je^{−σD}+E with ‖E‖≤52σε⁴. Then

$$M(t)=e^{-tD}-3\varepsilon^2\!\int_0^t e^{-2\sigma}e^{-(t-\sigma)D}Je^{-\sigma D}d\sigma+R,\qquad \|R\|\le78t^2\varepsilon^4 .$$

5. The (i,j) entry of e^{−(t−σ)D}Je^{−σD} is e^{−(t−σ)d_i−σd_j}. So, with u=e^{−t}:

$$M_{21}-M_{12}=-3\varepsilon^2\!\int_0^t\!(e^{-2t-\sigma}-e^{-t-3\sigma})\,d\sigma+R_{21}-R_{12}=-\varepsilon^2u(u-1)^3+R_{21}-R_{12},$$

   and −ε²u(u−1)³=ε²e^{−t}(1−e^{−t})³>0, while |R₂₁−R₁₂|≤2‖R‖≤156t²ε⁴. ∎

**C.3 Remarks.**
- **Small τ.** Expanding the variational equation in τ, the first non-symmetric term of DΦ_τ(z) is (τ³/12)[Ḣ,H], with H=∇²f(z), Ḣ=6sṡJ and [J,D]≠0. This gives ∂ₓΦ_τ^{(2)}−∂_yΦ_τ^{(1)}=τ³s(x+2y+2s³)+O(τ⁴), which I confirmed numerically. So the prox picture is accurate to second order in τ and breaks at third order.
- **Where the claim does hold.** For quadratic f=½⟨Az,z⟩, Φ_τ=e^{−τA}=prox_{r_τ} with r_τ=½⟨(e^{τA}−I)·,·⟩. In 1D it also holds. In our case the Hessians along a trajectory do not commute, and that is what breaks the symmetry.
- **Relation to prox steps.** By the Crandall–Liggett formula, Φ_τ=lim_m(prox_{(τ/m)f})^m. That is a limit of *compositions* of prox maps, which is not a prox map in general.

**C.4 Numerical check.** These values are not needed for the proof. I computed them with a 30-digit Taylor-series integrator (mpmath) and cross-checked them with DOP853 and Radau.
- DΦ₁(1,0) ≈ [[0.208957, −0.112005], [−0.075018, 0.088843]], which is not symmetric.
- Φ₁ is not monotone. Take z=(2, 11/2) and w=(3,7):
  - Φ₁z ≈ (−0.3870091, 0.3195062) and Φ₁w ≈ (−0.4690472, 0.3566689).
  - ⟨Φ₁z−Φ₁w, z−w⟩ ≈ −0.02629 < 0, while ‖Φ₁z−Φ₁w‖² ≈ 0.00811. This contradicts B.2.
- In scans, the symmetric part of DΦ_τ was indefinite at some inputs for every τ I tested in [0.05, 8]. The infinitesimal firm-nonexpansiveness test already failed at τ=0.01, at z≈(19.35, 299.38).
- I have not proved that firm nonexpansiveness fails for every τ; the evidence above is numerical.

---

## D. Deployment paragraph (item 3)

> **Denoising block.** Let f(x,y)=½(x²+2y²)+¼(x+y)⁴. It is 1-strongly convex (∇²f⪰diag(1,2)) and has the unique critical point and minimizer z*=0. A block is the exact time-τ map T_τ=Φ_τ of the gradient flow ż=−∇f(z), where **τ>0 is an integration time**. The flow is globally well posed forward in time, Φ_τ is C^∞, and T_τⁿ=Φ_{nτ}: a stack of n blocks is exactly the flow run for total time nτ, with no discretization error. For all inputs z, w and all n:
> - ‖T_τⁿz−T_τⁿw‖≤e^{−nτ}‖z−w‖ and ‖T_τⁿz‖≤e^{−nτ}‖z‖;
> - f(T_τⁿz)≤min{e^{−2nτ}f(z), ‖z‖²/(2(e^{nτ}−1))};
> - ‖∇f(T_τⁿz)‖≤e^{−nτ}‖∇f(z)‖.
>
> These rates are sharp. Each block is therefore an e^{−τ}-contraction, hence (1+e^{−τ})/2-averaged, with unique fixed point 0. Each block also satisfies, for all u, (e^τ−1)f(T_τz)+(e^τ/2)‖T_τz−u‖²≤(e^τ−1)f(u)+½‖z−u‖².
>
> **The block is not a proximal or convex-regularization step.** Under the convention prox_r(z)=argmin_u{r(u)+½‖u−z‖²}, the quadratic term always has weight one, so a step size can enter only through r (backward Euler with step h is prox_{hf}). For no τ>0 is T_τ of this form for any r, because DT_τ is not symmetric. In particular T_τ≠prox_{τf}: the two agree only to O(τ²), and already DT_τ(0)=diag(e^{−τ},e^{−2τ}) differs from diag(1/(1+τ),1/(1+2τ)). The weight that naturally multiplies f is e^τ−1, not τ. We do not claim firm nonexpansiveness. Because the attractor 0 does not depend on the input, the total time nτ sets the trade-off between smoothing and keeping information about the input.

**Suggested replacement for the rationale sentence:** "Since the vector field is the negative gradient of a 1-strongly convex energy, the exact block is an e^{−τ}-contraction toward the unique minimizer and reduces the energy by at least the factor e^{−2τ}; it is not a proximal (convex-regularization) step." If an exact prox interpretation is essential, the block would have to become prox_{τf}. That is a different map, and its contraction factor is 1/(1+τ) rather than e^{−τ}.