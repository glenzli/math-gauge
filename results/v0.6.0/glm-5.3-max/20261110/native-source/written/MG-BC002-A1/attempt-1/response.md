All computations are complete and cross-validated (three independent integrators agree to ~1e-13; margins are 6 orders of magnitude above numerical noise). I now have everything needed. Let me compose the final deliverable.

---

# Mathematical Appendix — Exact Gradient-Flow Denoising Block

**Setting and notation.** The state is $z=(x,y)\in\mathbb R^2$ with

$$f(x,y)=\frac{x^{2}+2y^{2}}{2}+\frac{(x+y)^{4}}{4},\qquad \nabla f(x,y)=\bigl(x+s^{3},\,2y+s^{3}\bigr),\quad s:=x+y .$$

$\Phi_t(z)$ denotes the solution at time $t\ge 0$ of $\dot z=-\nabla f(z)$, $z(0)=z$. The deployed block is $T_\tau=\Phi_\tau$ ($\tau>0$), and a stack of $n$ identical blocks is $Z_n=T_\tau^{\,n}(Z_0)$. We write $\|\cdot\|$ and $\langle\cdot,\cdot\rangle$ for the Euclidean norm and inner product. For Appendix A.3 it is convenient to use the **orthogonal** coordinates

$$u=\frac{x+y}{\sqrt2},\qquad v=\frac{x-y}{\sqrt2}\quad\Longleftrightarrow\quad f(u,v)=\frac{3u^{2}-2uv+3v^{2}}{4}+u^{4},\qquad \dot u=\tfrac12(v-3u)-4u^{3},\ \ \dot v=\tfrac12(u-3v).$$

A closed-form solution of the ODE is not needed (and none is used): every statement below follows from structural properties of $f$.

---

## A.1 Well-posedness, equilibrium, contraction, dissipativity, stack convergence

**Lemma A.1 (derivatives, strong convexity, coercivity).** For all $z=(x,y)$ and all $w=(w_1,w_2)\in\mathbb R^2$, with $s=x+y$,

$$\nabla^2 f(x,y)=\begin{pmatrix}1+3s^2&3s^2\\3s^2&2+3s^2\end{pmatrix},\qquad 
w^{\top}\!\nabla^2 f(z)\,w \;=\; \|w\|^{2}+3s^{2}(w_1+w_2)^{2}+w_2^{2}\;\ge\;\|w\|^{2},$$

so $\nabla^2f\succeq I$ on $\mathbb R^2$ ($f$ is $1$-strongly convex, and the constant $1$ is sharp: $\nabla^2 f(0)$ has smallest eigenvalue $1$ with eigenvector $(1,0)$). Moreover

$$f(z)-\tfrac12\|z\|^{2}=\frac{s^{4}+2y^{2}}{4}\;\ge\;0,\qquad\text{i.e.}\qquad f(z)\ \ge\ \tfrac12\|z\|^{2}\quad\text{(coercivity)},\qquad f\ \text{is } C^\infty .\qquad\square$$

**Proposition A.2 (forward global well-posedness).** For every $z_0\in\mathbb R^2$ the ODE $\dot z=-\nabla f(z)$, $z(0)=z_0$, has a unique solution on $[0,\infty)$. Consequently $\Phi_0=\mathrm{Id}$, $\Phi_{t+s}=\Phi_t\circ\Phi_s$ for all $t,s\ge0$ (semigroup property), $\Phi_t(0)=0$, $\Phi_t$ is injective, and $(t,z)\mapsto\Phi_t(z)$ is $C^\infty$.

*Proof.* $F:=-\nabla f$ is a polynomial ($C^\infty$, hence locally Lipschitz) vector field, so Picard–Lindelöf gives a unique maximal solution on $[0,T_{\max})$. Along any solution,
$\frac{d}{dt}f(z(t))=\langle\nabla f,\dot z\rangle=-\|\nabla f(z(t))\|^{2}\le 0$, hence $f(z(t))\le f(z_0)$ and, by Lemma A.1, $\|z(t)\|^{2}\le 2f(z(t))\le 2f(z_0)$: the trajectory remains in the compact set $K=\{f\le f(z_0)\}$. If $T_{\max}<\infty$, then $\|z(t)-z(t')\|\le\int_{t}^{t'}\!\|F\|\le M_K|t-t'|$ with $M_K=\max_K\|F\|<\infty$, so $z(t)$ converges to some $\bar z\in K$ as $t\uparrow T_{\max}$; restarting Picard–Lindelöf from $(T_{\max},\bar z)$ extends the solution — a contradiction. Hence $T_{\max}=\infty$. The semigroup property is uniqueness; smooth dependence on data is standard for $C^\infty$ vector fields. ∎

*(Remark: only **forward** time is global. The backward (ascent) flow can blow up in finite time — e.g. in $(u,v)$-coordinates $\dot u=+4u^3$ starting from $u_0\ne0$ explodes at $t=1/(8u_0^2)$ — so $\Phi_\tau$ is injective but not surjective.)*

**Proposition A.3 (equilibrium).** $\nabla f(z)=0$ holds **only** at $z^\star=(0,0)$; $z^\star$ is the unique global minimizer of $f$ and $\min f=f(0)=0$. In particular $z^\star$ is the unique equilibrium of the flow and the unique fixed point of every $T_\tau$.

*Proof.* $x+s^3=0=2y+s^3$ gives $x=2y$, then $s=3y$ and $0=x+s^3=2y+27y^3=y(2+27y^2)$, so $y=0$, $x=0$; conversely $\nabla f(0)=0$. Strict convexity ($\nabla^2f\succeq I\succ0$) makes the critical point the unique minimizer; $f\ge\frac12\|\cdot\|^2$ with $f(0)=0$ gives $\min f=0$. Finally, $\mathrm{Fix}(T_\tau)=\{0\}$ because $\|\Phi_\tau(z)\|\le e^{-\tau}\|z\|<\|z\|$ for $z\ne0$ (Theorem A.4 below). ∎

**Lemma A.4 (strong monotonicity).** For all $z,w\in\mathbb R^2$,
$$\bigl\langle \nabla f(z)-\nabla f(w),\,z-w\bigr\rangle=\int_0^1 (z-w)^{\top}\nabla^2 f\bigl(w+\theta(z-w)\bigr)(z-w)\,d\theta\ \ge\ \|z-w\|^{2}.$$

*Proof.* Segment integral of Lemma A.1. ∎

**Theorem A.5 (contraction).** For all $z,w\in\mathbb R^2$ and all $t\ge0$,
$$\boxed{\ \|\Phi_t(z)-\Phi_t(w)\|\ \le\ e^{-t}\,\|z-w\|\ }\qquad\text{in particular}\qquad \|\Phi_t(z)-z^\star\|\le e^{-t}\|z-z^\star\| .$$
The rate is sharp (smallest eigenvalue of $\nabla^2f(0)$ equals $1$).

*Proof.* For two solutions $z(t)=\Phi_t(z)$, $w(t)=\Phi_t(w)$,
$$\frac{d}{dt}\frac12\|z(t)-w(t)\|^{2}=\bigl\langle -\nabla f(z)+\nabla f(w),\,z-w\bigr\rangle\le-\|z-w\|^{2}$$
by Lemma A.4; Grönwall. Take $w=z^\star=0$ (an equilibrium) for the second bound. ∎

**Lemma A.6 (Polyak–Łojasiewicz inequality with constant $1$).** For all $z=(x,y)$, $s=x+y$,
$$\|\nabla f(x,y)\|^{2}-2f(x,y)\;=\;2\Bigl(y+\frac{s^{3}}{2}\Bigr)^{2}+\frac32\,s^{4}+\frac32\,s^{6}\;\ge\;0 ,$$
with equality iff $z=0$. The constant $1$ is sharp: $\|\nabla f\|^{2}/(2f)\to1$ as $z\to0$ along $y=0$.

*Proof.* Direct expansion: $\|\nabla f\|^{2}=(x+s^3)^2+(2y+s^3)^2$, $2f=x^{2}+2y^{2}+\tfrac12 s^{4}$; subtracting and using $x=s-y$ gives $2y^{2}+2s^{3}y+\tfrac32 s^{4}+2s^{6}=2\bigl(y+\tfrac{s^{3}}{2}\bigr)^{2}+\tfrac32 s^{4}+\tfrac32 s^{6}$. ∎

**Theorem A.7 (energy dissipation).** For all $z$ and all $t\ge0$,
$$\boxed{\ f(\Phi_t(z))\ \le\ e^{-2t}\,f(z)\ }\qquad(\text{strict unless } z=0).$$

*Proof.* $\frac{d}{dt}f(\Phi_t(z))=-\|\nabla f(\Phi_t(z))\|^{2}\le-2f(\Phi_t(z))$ by Lemma A.6, and $f\ge0$; multiplicative Grönwall. Strictness: equality in Lemma A.6 occurs only at the origin. ∎

**Corollary A.8 (quantitative convergence of a stack).** Let $Z_n=T_\tau^{\,n}(Z_0)=\Phi_\tau^{\,n}(Z_0)$. By the semigroup property,
$$Z_n=\Phi_{n\tau}(Z_0),$$
i.e. **stacking $n$ blocks is exactly the flow run for total time $n\tau$**, and all guarantees depend only on the product $n\tau$:

1. $\|Z_n-z^\star\|\le e^{-n\tau}\|Z_0-z^\star\|$ and $\|Z_n\|\le e^{-n\tau}\sqrt{2f(Z_0)}$;
2. $f(Z_n)\le e^{-2n\tau}f(Z_0)$, with $f$ strictly decreasing at each block unless $Z_0=0$;
3. (input robustness) for any two inputs, $\|Z_n-\widetilde Z_n\|\le e^{-n\tau}\|Z_0-\widetilde Z_0\|\|$; the whole stack is globally $e^{-n\tau}$-Lipschitz;
4. $Z_n\to z^\star=0$ geometrically; to reach $\|Z_n\|\le\varepsilon\|Z_0\|$ it suffices that $n\tau\ge\ln(1/\varepsilon)$, and to reach $f(Z_n)\le\varepsilon$ it suffices that $n\tau\ge\tfrac12\ln\!\bigl(f(Z_0)/\varepsilon\bigr)$ — independent of how the dwell time is split across blocks.

*Proof.* Iterate Theorems A.5/A.7 along $Z_{k+1}=\Phi_\tau(Z_k)$, or apply them once at time $n\tau$ using the semigroup property; $\tfrac12\|Z_n\|^2\le f(Z_n)$ for the second bound in 1. ∎

*Numerical cross-check (random samples, tolerances $10^{-12}$–$10^{-13}$):* worst observed ratios $\|\Phi_tz-\Phi_tw\|/\|z-w\|$ were $0.6495\le e^{-0.3}$, $0.2645\le e^{-1}$, $0.0447\le e^{-2.7}$; worst energy ratios $0.468\le e^{-0.6}$, $0.0719\le e^{-2}$, $0.00276\le e^{-5.4}$. ✔

---

## A.2 The proximal certificate and firm nonexpansiveness

Throughout, $r:\mathbb R^{d}\to(-\infty,+\infty]$ is **proper, lower semicontinuous (lsc) and convex**, and
$$\operatorname{prox}_r(z)=\arg\min_{u\in\mathbb R^{d}}\Bigl\{\,r(u)+\tfrac12\|u-z\|^{2}\Bigr\}.$$

**Lemma B.1 (prox is well defined).** For every $z$, the minimization problem has exactly one solution, and it lies in $\operatorname{dom}r$.

*Proof.* $r$ majorizes an affine function, so the objective is coercive; it is lsc and strictly convex (the squared term is strictly convex); existence by the direct method, uniqueness by strict convexity. A minimizer cannot lie outside $\operatorname{dom}r$, where the objective is $+\infty$. ∎

**Theorem B.2 (proximal certificate).** *Let $T=\operatorname{prox}_r$ with $r$ proper, lsc, convex. Then for every $z$, with $p=T(z)$, and every $u\in\operatorname{dom}r$:*

$$\boxed{\ r(p)+\frac{\|p-z\|^{2}}{2}+\frac{\|u-p\|^{2}}{2}\ \le\ r(u)+\frac{\|u-z\|^{2}}{2}\ }$$

*Proof.* Let $\varphi(w)=r(w)+\tfrac12\|w-z\|^{2}$; $p$ minimizes $\varphi$. Fix $u\in\operatorname{dom}r$ and $\theta\in(0,1)$; by convexity of $\operatorname{dom}r$, $p_\theta:=p+\theta(u-p)\in\operatorname{dom}r$. Minimality gives $\varphi(p)\le\varphi(p_\theta)$. By convexity of $r$ and expansion of the quadratic term,
$$r(p_\theta)\le(1-\theta)r(p)+\theta r(u),\qquad 
\frac{\|p_\theta-z\|^{2}}{2}=\frac{\|p-z\|^{2}}{2}+\theta\langle p-z,\,u-p\rangle+\frac{\theta^{2}}{2}\|u-p\|^{2}.$$
Hence $0\le\varphi(p_\theta)-\varphi(p)\le\theta\bigl[r(u)-r(p)+\langle p-z,u-p\rangle\bigr]+\frac{\theta^{2}}{2}\|u-p\|^{2}$. Divide by $\theta$ and let $\theta\downarrow0$:
$$r(u)\ \ge\ r(p)+\langle z-p,\,u-p\rangle . \tag{∗}$$
Now add $\tfrac12\|u-z\|^{2}=\tfrac12\|p-z\|^{2}+\langle p-z,u-p\rangle+\tfrac12\|u-p\|^{2}$ to $(∗)$; the cross terms cancel and yield the claim. ∎

*Remark (subdifferential form).* $(∗)$ is exactly the subgradient inequality for $z-p\in\partial r(p)$, which follows from Fermat's rule and the sum rule $0\in\partial(r+\tfrac12\|\cdot-z\|^2)(p)=\partial r(p)+p-z$. The proof above derives it from scratch.

**Corollary B.3 (firm nonexpansiveness).** *Under the hypotheses of Theorem B.2, for all $z,z'$, with $p=\operatorname{prox}_r(z)$, $p'=\operatorname{prox}_r(z')$:*
$$\|p-p'\|^{2}\ \le\ \langle p-p',\,z-z'\rangle\qquad(\text{firm nonexpansiveness}),$$
*and consequently $\|p-p'\|\le\|z-z'\|$ (nonexpansiveness) and $\langle p-p',z-z'\rangle\ge0$ (monotonicity).*

*Proof.* Apply B.2 twice — certificate $(z,\,u=p')$ and certificate $(z',\,u=p)$, legitimate because $p,p'\in\operatorname{dom}r$ (Lemma B.1) — and add:
$$\|p-p'\|^{2}\ \le\ \frac{\|p'-z\|^{2}+\|p-z'\|^{2}-\|p-z\|^{2}-\|p'-z'\|^{2}}{2} .$$
Writing $A=p-z$, $B=p'-z'$, $\Delta=p-p'$, $d=z-z'$ (so $\Delta-d=A-B$), the right-hand side equals $\tfrac12\bigl[\|A-\Delta\|^{2}+\|\Delta+B\|^{2}-\|A\|^{2}-\|B\|^{2}\bigr]=\|\Delta\|^{2}-\langle A-B,\Delta\rangle=\langle\Delta,d\rangle$. Finally $\langle p-p',z-z'\rangle\le\|p-p'\|\,\|z-z'\|$ gives nonexpansiveness. ∎

**Remark B.4 (three consequences used in A.3).**
**(a) Descent.** Taking $u=z\in\operatorname{dom}r$ in B.2: $r(p)+\|p-z\|^{2}\le r(z)$. For $r=\tau f$ (our $f$ is convex and everywhere finite): $f(\operatorname{prox}_{\tau f}z)+\frac1{\tau}\|\operatorname{prox}_{\tau f}z-z\|^{2}\le f(z)$.
**(b) Prox maps are gradient maps (symmetry test).** Let $M_r(z)=\min_u\{r(u)+\tfrac12\|u-z\|^{2}\}$ be the Moreau envelope. Classically (Moreau), $M_r$ is convex and $C^{1}$ with $\nabla M_r(z)=z-\operatorname{prox}_r(z)$ (envelope theorem for the jointly convex function $(u,z)\mapsto r(u)+\tfrac12\|u-z\|^2$, smooth in $z$ with unique minimizer). Hence, **if a $C^{1}$ map $T$ satisfies $T=\operatorname{prox}_r$, then $T=I-\nabla M_r$ is a gradient field and $DT$ is symmetric everywhere.**
**(c) Firm nonexpansiveness alone is not sufficient.** $T=\tfrac12(I+R)$, with $R$ a $90^\circ$ rotation, is firmly nonexpansive (indeed $\|T\delta\|^{2}=\tfrac12\|\delta\|^{2}=\langle T\delta,\delta\rangle$) but is not a prox of any lsc convex function, because $DT=\tfrac12(I+R)$ is not symmetric — contradicting (b). So (B.3) and (b) are *necessary* conditions only; this is all we need.

---

## A.3 What the continuous-flow block actually is — and is not

### C.1 Description suitable for the methods section

The block $T_\tau=\Phi_\tau$ is the **exact time-$\tau$ solution map** of the gradient flow $\dot z=-\nabla f(z)$ of the $1$-strongly convex, coercive, nonnegative energy $f$; it is a $C^\infty$ self-map of $\mathbb R^2$ with unique fixed point $z^\star=0$, and (A.1)

- per block: $\;\|T_\tau z-T_\tau w\|\le e^{-\tau}\|z-w\|$ (global $e^{-\tau}$-Lipschitz) and $f(T_\tau z)\le e^{-2\tau}f(z)$;
- per stack ($n$ blocks): $Z_n=\Phi_{n\tau}(Z_0)$ (semigroup), $\|Z_n\|\le e^{-n\tau}\|Z_0\|$, $f(Z_n)\le e^{-2n\tau}f(Z_0)$, $Z_n\to0$ geometrically, and the stack is $e^{-n\tau}$-Lipschitz in its input; accuracy $\varepsilon$ costs total dwell time $n\tau\ge\ln(1/\varepsilon)$ in distance, $n\tau\ge\tfrac12\ln(f(Z_0)/\varepsilon)$ in energy.

No closed form of $\Phi_\tau$ is required. Example (verified): from $Z_0=(7,7)$, $f=9677.5$: after one block with $\tau=1$, $Z_1=(0.18578,\,0.04392)$, $\|Z_1\|=0.1909\le e^{-1}\cdot9.899$, $f(Z_1)=1.99\cdot10^{-2}\le e^{-2}\cdot 9677.5$.

### C.2 The proximal claim in the rationale is false

The rationale argues: gradient of a strongly convex energy, contractive and dissipative $\Rightarrow$ "$T_\tau=\operatorname{prox}_{r_\tau}$ for some proper lsc convex $r_\tau$, for every $\tau>0$". The premise is true and quantified in A.1 ($e^{-t}$-contraction, $e^{-2t}$-dissipation), but the conclusion **does not follow and is false**: "contractive" yields *nonexpansivity* (1-Lipschitz), whereas a proximal operator must be **firmly nonexpansive** (Corollary B.3) **and** a gradient map with symmetric differential (Remark B.4(b)) — strictly stronger properties, both of which fail here.

**Theorem C.1 (no convex proximal representation; numerical certificate at $\tau=1$).** *Let $\tau=1$, $z=(7,7)$, $w=(6.5,\,6.2)$. Numerically (see verification note below),*
$$\Phi_1(z)=(0.18577532,\ 0.04391981),\qquad \Phi_1(w)=(0.23186922,\ 0.01884727),$$
$$\|\Phi_1 z-\Phi_1 w\|^{2}=2.75328\cdot10^{-3}\ >\ -2.98892\cdot10^{-3}=\langle \Phi_1z-\Phi_1w,\ z-w\rangle .$$
*Hence $\Phi_1$ violates firm nonexpansiveness — and even monotonicity ($\langle \Phi_1z-\Phi_1w,z-w\rangle<0$), which is impossible for any prox by Corollary B.3. Therefore*
$$\Phi_1\ \neq\ \operatorname{prox}_{r}\quad\text{for every proper lsc convex } r .$$

*Verification note.* The ODE was integrated in the $(u,v)$ chart ($\dot u=\tfrac12(v-3u)-4u^3$, $\dot v=\tfrac12(u-3v)$; here $z\leftrightarrow(u,v)=(9.89949494,\,0)$, $w\leftrightarrow(8.98025612,\,0.21213203)$, $\|z-w\|=0.94339811$) with adaptive Runge–Kutta DOP853 (rtol $10^{-13}$) and independently Radau and LSODA (rtol $10^{-12}$); all three agree to $<10^{-10}$ on every quantity above. The margin $5.74\cdot10^{-3}$ exceeds the integration error by more than six orders of magnitude.

**Theorem C.2 (structural obstruction; rigorous for all small $\tau$, numerical for all tested $\tau$).** *If $\Phi_\tau=\operatorname{prox}_{r_\tau}$ for a proper lsc convex $r_\tau$, then by Remark B.4(b) the differential $D\Phi_\tau(z)$ must be **symmetric** for every $z$. This fails:*

*(i) Rigorous, small $\tau$.* The flow has the $C^{1}$-uniform Taylor expansion
$$\Phi_\tau(z)=z-\tau\nabla f(z)+\frac{\tau^{2}}{2}\nabla^{2}\!f(z)\nabla f(z)-\frac{\tau^{3}}{6}\,D\bigl(\nabla^{2}\!f\,\nabla f\bigr)(z)\,\nabla f(z)+O(\tau^{4}).$$
The first two vector fields are gradients ($\nabla f$ and $\nabla^{2}\!f\,\nabla f=\nabla\bigl(\tfrac12\|\nabla f\|^{2}\bigr)$), hence curl-free; a direct computation in the $(u,v)$ chart gives
$$\operatorname{curl}\Bigl(D\bigl(\nabla^{2}\!f\,\nabla f\bigr)\,\nabla f\Bigr)(u,v)=6u\,(8u^{3}+3u-v),$$
which equals $66\ne0$ at $(u,v)=(1,0)$ (i.e. $z_0=(1/\sqrt2,\,1/\sqrt2)$). Hence
$$\operatorname{curl}\bigl(D\Phi_\tau\bigr)(z_0)=-\tfrac{\tau^{3}}{6}\cdot 66+O(\tau^{4})=-11\,\tau^{3}\,(1+o(1))\ \ne\ 0\quad\text{for all }0<\tau<\tau_0,$$
so $D\Phi_\tau(z_0)$ is not symmetric and $\Phi_\tau\ne\operatorname{prox}_{r}$ for every proper lsc convex $r$ and every sufficiently small $\tau>0$. (Numerically: $-8.51\cdot10^{-8}$ at $\tau=0.002$, ratio $0.967$ to $-11\tau^{3}$.)

*(ii) Numerical scan, $\tau\in[0.01,\,10]$.* With $J=D\Phi_\tau$ at the stated base point on the ray $x=y$ (chart $v_0=0$), let $\lambda_+=\lambda_{\max}\bigl(J^{\top}J-\tfrac{J+J^{\top}}{2}\bigr)$ (infinitesimal firm-nonexpansiveness defect) and $\omega=J_{21}-J_{12}$ (asymmetry):

| $\tau$ | base point $(x,y)$ | $\lambda_+$ | $\omega=J_{21}-J_{12}$ |
|---|---|---|---|
| 0.01 | (70.71, 70.71) | $2.19\cdot10^{-5}$ | $-1.97\cdot10^{-3}$ |
| 0.05 | (35.36, 35.36) | $3.06\cdot10^{-4}$ | $-9.54\cdot10^{-3}$ |
| 0.1 | (35.36, 35.36) | $6.85\cdot10^{-4}$ | $-1.83\cdot10^{-2}$ |
| 0.5 | (35.36, 35.36) | $3.86\cdot10^{-3}$ | $-6.21\cdot10^{-2}$ |
| 1 | (7.07, 7.07) | $6.91\cdot10^{-3}$ | $-7.15\cdot10^{-2}$ |
| 2 | (7.07, 7.07) | $6.72\cdot10^{-3}$ | $-4.28\cdot10^{-2}$ |
| 5 | (7.07, 7.07) | $5.50\cdot10^{-4}$ | $-2.70\cdot10^{-3}$ |
| 10 | (7.07, 7.07) | $3.80\cdot10^{-6}$ | $-1.84\cdot10^{-5}$ |

$\lambda_+>0$ means firm nonexpansiveness already fails infinitesimally (directions realizing it are given by the top eigenvector of $J^{\top}J-\mathrm{sym}\,J$); $\omega\ne0$ means the gradient-map/symmetry condition fails. Both defects are positive for **every** $\tau$ tested, with margins $\ge10^{4}$ above the verified integration error. Jacobians were obtained from the variational equation $\dot J=-\nabla^{2}\!f\,J$, $J_0=I$, and cross-checked against central finite differences (agreement $10^{-11}$).

*(iii) Mechanism (why the defects must occur).* In the $(u,v)$ chart the Hessian is $H(u)=\begin{pmatrix}3/2+12u^{2}&-1/2\\-1/2&3/2\end{pmatrix}$: where $|u|$ is large the $u$-direction is stiff (rate $\approx12u^{2}$) while the $v$-direction contracts at rate $3/2$, and $H(u_1)$, $H(u_2)$ do **not** commute ($[H(1),H(2)]=\begin{pmatrix}0&18\\-18&0\end{pmatrix}\ne0$), so the contraction directions rotate along trajectories. A difference aligned with the stiff direction is crushed, while differences in the soft direction are transported into the stiff one. Numerically, at $\tau=1$,
$$D\Phi_1(u_0,0)\ \xrightarrow[\ u_0\to\infty\ ]{}\ \begin{pmatrix}0&0.0716\\ 0&0.2389\end{pmatrix}$$
(values at $u_0=10,50,200,800$: $\begin{psmallmatrix}1.4\cdot10^{-4}&0.07183\\3.1\cdot10^{-4}&0.23893\end{psmallmatrix}\to\begin{psmallmatrix}1.4\cdot10^{-8}&0.07158\\4.7\cdot10^{-8}&0.23887\end{psmallmatrix}$) — a non-normal, asymmetric limit: the $u$-column is annihilated, the $v$-column is rotated into $u$. For any map with such a differential $J=\begin{psmallmatrix}0&j\\0&c\end{psmallmatrix}$, $j>0$, the matrix $J^{\top}J-\mathrm{sym}\,J=\begin{psmallmatrix}0&-j/2\\-j/2&j^{2}+c^{2}-c\end{psmallmatrix}$ has determinant $-j^{2}/4<0$, hence a positive eigenvalue: firm nonexpansiveness fails. This rotation is exactly what a proximal operator cannot do, since it is a gradient map (B.4(b)) and firmly nonexpansive (B.3).

**Where the intuition goes wrong.** The exact flow *is* a limit of proximal maps — the classical exponential formula
$$\Phi_\tau=\lim_{k\to\infty}\ \operatorname{prox}_{(\tau/k)f}^{\;k}$$
(numerically: error $4.2\cdot10^{-3}$ at $k=100$, $4.3\cdot10^{-5}$ at $k=10^{4}$ from $z=(1,1)$, $\tau=1$). But compositions and limits of prox maps preserve only *nonexpansivity*, not the prox property itself. "Contractive and dissipative" is exactly enough for A.1 — and not enough for a convex proximal representation.

### C.3 The evolution time $\tau$ vs. the coefficient in the prox definition

In our convention $\operatorname{prox}_r(z)=\arg\min_u\{r(u)+\|u-z\|^{2}/2\}$, the coefficient of the squared distance is the **fixed number $1/2$**: $\operatorname{prox}_r=(I+\partial r)^{-1}$ is a *unit* resolvent. The only way a step/time parameter enters a proximal map is through the penalty:
$$\operatorname{prox}_{\tau r}(z)=\arg\min_{u}\Bigl\{r(u)+\frac{\|u-z\|^{2}}{2\tau}\Bigr\}=(I+\tau\,\partial r)^{-1}.$$
The natural proximal object with parameter $\tau$ associated to our flow is therefore the **implicit-Euler step** $z\mapsto z-\tau\nabla f(z_{\text{new}})$, which is exactly $\operatorname{prox}_{\tau f}$ — a *genuine* convex prox: since $f$ is $1$-strongly convex, $\operatorname{prox}_{\tau f}$ is firmly nonexpansive, $(1+\tau)^{-1}$-contractive, and obeys the descent $f(p)+\frac{1}{\tau}\|p-z\|^{2}\le f(z)$ (Remark B.4(a)). But it is a **different map** from the exact flow block: $\|\Phi_1(z)-\operatorname{prox}_{f}(z)\|\approx0.30$ at $z=(1,1)$ (also $0.37$ at $(2,-1)$, $0.15$ at $(0.5,0.5)$); they agree only to order $O(\tau^{2})$ per step. Thus the draft conflates three distinct roles: (i) the **evolution time** $\tau$ of the exact flow (what our block has), (ii) the **implicit-step parameter** $\tau$ of $\operatorname{prox}_{\tau f}$ (what the block is *not*), and (iii) the **unit prox coefficient** $1/2$ fixed by the definition. Even if a representation $T_\tau=\operatorname{prox}_{r_\tau}$ existed, $\tau$ would be a structural parameter of $r_\tau$, not the prox coefficient; in fact, by C.1–C.2, no such convex $r_\tau$ exists at all.

### C.4 Deployment paragraph (for the paper)

> Each denoising block is the exact time-$\tau$ solution operator $T_\tau=\Phi_\tau$ of the gradient flow $\dot z=-\nabla f(z)$, where $f(x,y)=\frac{x^{2}+2y^{2}}{2}+\frac{(x+y)^{4}}{4}$ is $1$-strongly convex with unique equilibrium at the origin; $\tau$ is the block's evolution (dwell) time, not a proximal step size. Stacking $n$ blocks runs the flow for total time $n\tau$: $Z_n=\Phi_{n\tau}(Z_0)$. Each block is globally $e^{-\tau}$-Lipschitz and reduces the energy by at least the factor $e^{-2\tau}$; a stack is $e^{-n\tau}$-Lipschitz in its input, contracts distance to the equilibrium as $\|Z_n\|\le e^{-n\tau}\|Z_0\|$, and decreases the energy as $f(Z_n)\le e^{-2n\tau}f(Z_0)$, so relative accuracy $\varepsilon$ is reached once the total dwell time satisfies $n\tau\ge\ln(1/\varepsilon)$ (distance) or $n\tau\ge\frac12\ln(f(Z_0)/\varepsilon)$ (energy), independently of the split across blocks. The block is not an implicit-Euler step (that would be the firmly nonexpansive map $\operatorname{prox}_{\tau f}=(I+\tau\nabla f)^{-1}$, which differs from $\Phi_\tau$ by $O(\tau^{2})$ per step), and it is **not** a proximal operator of any convex function: at $\tau=1$ the pair $z=(7,7)$, $w=(6.5,6.2)$ violates firm nonexpansiveness ($\|\Phi_1z-\Phi_1w\|^{2}=2.75\cdot10^{-3}>-2.99\cdot10^{-3}=\langle\Phi_1z-\Phi_1w,z-w\rangle$), which is impossible for any prox; the same obstruction occurs for every $\tau$ tested ($10^{-2}$–$10$) and provably for all sufficiently small $\tau$ (Appendix A.3). We therefore describe the deployed block as an exact dissipative-flow step with the quantitative contraction and energy guarantees above, and we withdraw the "exact convex regularization step" interpretation from the design rationale.

---

**Summary of what was established.** (1) The flow is globally well-posed forward in time with unique equilibrium $z^\star=0$; $\nabla^2f\succeq I$ gives the sharp contraction $\|\Phi_tz-\Phi_tw\|\le e^{-t}\|z-w\|$, and the sharp PL inequality $\|\nabla f\|^2\ge2f$ gives $f(\Phi_tz)\le e^{-2t}f(z)$; stacks satisfy $\|Z_n\|\le e^{-n\tau}\|Z_0\|$, $f(Z_n)\le e^{-2n\tau}f(Z_0)$, with all guarantees depending only on the total dwell time $n\tau$. (2) The proximal certificate and firm nonexpansiveness were proved from first principles, with the auxiliary facts that a prox is monotone and a gradient map with symmetric differential. (3) The rationale's proximal claim is false — $\Phi_\tau$ fails firm nonexpansiveness (even monotonicity) and fails the symmetry test, at $\tau=1$ by explicit numerical certificate and for all small $\tau$ rigorously — so the block must be described as an exact contractive, dissipative flow step, with $\tau$ an evolution time rather than the (unit) prox coefficient; the correct proximal object with parameter $\tau$ is the different map $\operatorname{prox}_{\tau f}$.