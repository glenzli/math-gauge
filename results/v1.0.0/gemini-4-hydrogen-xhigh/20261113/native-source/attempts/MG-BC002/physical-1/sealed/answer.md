Waiting for the numerical check on firm nonexpansiveness to complete.
Waiting for the Jacobian asymptotic check to finish.
## Mathematical Appendix

### 1. Well-Posedness, Equilibrium, Contraction, Energy Decay, and Stack Convergence

Let $z = (x,y) \in \mathbb{R}^2$ with the Euclidean inner product $\langle z, w \rangle = x_1 x_2 + y_1 y_2$ and norm $\|z\| = \sqrt{x^2 + y^2}$, and consider the autonomous gradient flow
$$\dot{z}(t) = -\nabla f(z(t)), \qquad z(0) = z_0 \in \mathbb{R}^2,$$
for the energy
$$f(x,y) = \frac{x^2 + 2y^2}{2} + \frac{(x+y)^4}{4}.$$

#### 1.1 Smoothness, $1$-Strong Convexity, and Unique Equilibrium
Since $f$ is a polynomial, $f \in C^\infty(\mathbb{R}^2, \mathbb{R})$. Its gradient and Hessian are
$$\nabla f(x,y) = \begin{pmatrix} x + (x+y)^3 \\ 2y + (x+y)^3 \end{pmatrix}, \qquad \nabla^2 f(x,y) = \begin{pmatrix} 1 + 3(x+y)^2 & 3(x+y)^2 \\ 3(x+y)^2 & 2 + 3(x+y)^2 \end{pmatrix} = B + 3(x+y)^2 C,$$
where $B := \operatorname{diag}(1,2)$ and $C := \begin{pmatrix} 1 & 1 \\ 1 & 1 \end{pmatrix} = \mathbf{1}\mathbf{1}^T$. For every $z=(x,y) \in \mathbb{R}^2$ and $v = (v_1, v_2)^T \in \mathbb{R}^2$,
$$v^T \nabla^2 f(z) v = v_1^2 + 2v_2^2 + 3(x+y)^2 (v_1 + v_2)^2 \ge v_1^2 + v_2^2 = \|v\|^2,$$
so $\nabla^2 f(z) \succeq I_2$ globally on $\mathbb{R}^2$. Thus $f$ is **$1$-strongly convex**, and by the fundamental theorem of calculus along the segment $\xi(\theta) = w + \theta(z - w)$, $\nabla f$ is **$1$-strongly monotone**:
$$\langle \nabla f(z) - \nabla f(w), z - w \rangle = \int_0^1 (z-w)^T \nabla^2 f(\xi(\theta))(z-w)\,d\theta \ge \|z - w\|^2 \qquad \forall z, w \in \mathbb{R}^2.$$
Likewise, Taylor's formula gives for all $u, v \in \mathbb{R}^2$:
$$f(u) \ge f(v) + \langle \nabla f(v), u - v \rangle + \frac{1}{2}\|u - v\|^2.$$

To identify the equilibrium, note that $f(x,y) \ge \frac{x^2+2y^2}{2} \ge \frac{1}{2}\|z\|^2 \ge 0$ with $f(0,0) = 0$. Moreover, $\nabla f(x,y) = 0$ gives:
- Subtracting components: $0 = \partial_x f(x,y) - \partial_y f(x,y) = x - 2y \implies x = 2y$;
- Substituting into the second component: $0 = 2y + (3y)^3 = y(2 + 27y^2) \implies y = 0 \implies x = 0$.

Hence $z^* = (0,0)$ is the **unique equilibrium** of $\dot{z} = -\nabla f(z)$ and the unique global minimizer of $f$, with $\min_{\mathbb{R}^2} f = f(0,0) = 0$. (In particular, $\Phi_t(0) = 0$ for all $t \ge 0$.)

#### 1.2 Forward Global Well-Posedness and Semigroup Property
Because $-\nabla f \in C^\infty(\mathbb{R}^2, \mathbb{R}^2)$ is locally Lipschitz (though not globally Lipschitz, due to the cubic term), the Picard–Lindelöf theorem yields for each $z_0 \in \mathbb{R}^2$ a unique maximal solution $z: (T_{\min}(z_0), T_{\max}(z_0)) \to \mathbb{R}^2$ with $z(0)=z_0$ and $T_{\max}(z_0) > 0$. By smooth dependence of ODE solutions on initial conditions, $(t, z_0) \mapsto \Phi_t(z_0)$ is $C^\infty$ on its domain.

To show $T_{\max}(z_0) = +\infty$, differentiate $\frac{1}{2}\|z(t)\|^2$ along the solution on $[0, T_{\max}(z_0))$: using $\nabla f(0)=0$ and $1$-strong monotonicity,
$$\frac{d}{dt}\left(\frac{1}{2}\|z(t)\|^2\right) = -\langle z(t), \nabla f(z(t)) \rangle \le -\|z(t)\|^2 \le 0.$$
Hence $z(t)$ remains inside the compact ball $K := \overline{B}(0, \|z_0\|)$ for all $t \in [0, T_{\max}(z_0))$. (Equivalently, $\frac{d}{dt}f(z(t)) = -\|\nabla f(z(t))\|^2 \le 0$, so $z(t)$ stays in the compact sublevel set $\{z : f(z) \le f(z_0)\}$.) If $T_{\max}(z_0) < \infty$, then $\|\dot{z}(t)\| = \|\nabla f(z(t))\| \le M := \sup_{z \in K}\|\nabla f(z)\| < \infty$ on $[0, T_{\max}(z_0))$, so $z(t)$ is uniformly Lipschitz on $[0, T_{\max}(z_0))$ and the limit $z_\infty := \lim_{t \uparrow T_{\max}(z_0)} z(t) \in K$ exists; applying local existence at $z_\infty$ extends the solution beyond $T_{\max}(z_0)$, contradicting maximality. Thus $T_{\max}(z_0) = +\infty$ for every $z_0 \in \mathbb{R}^2$, and $\Phi_t : \mathbb{R}^2 \to \mathbb{R}^2$ is globally well-defined and $C^\infty$ for all $t \ge 0$.

By uniqueness of forward solutions to the autonomous ODE, $\Phi$ satisfies the semigroup property:
$$\Phi_0 = \mathrm{id}_{\mathbb{R}^2}, \qquad \Phi_{t+s}(z) = \Phi_t(\Phi_s(z)) \quad \forall t, s \ge 0,\; \forall z \in \mathbb{R}^2.$$

#### 1.3 Contraction Bound $\|\Phi_t(z) - \Phi_t(w)\| \le e^{-t}\|z - w\|$
Let $z, w \in \mathbb{R}^2$ and set $z(t) = \Phi_t(z)$, $w(t) = \Phi_t(w)$ for $t \ge 0$. Using $1$-strong monotonicity of $\nabla f$:
$$\frac{d}{dt}\left(\frac{1}{2}\|z(t) - w(t)\|^2\right) = -\langle z(t) - w(t), \nabla f(z(t)) - \nabla f(w(t)) \rangle \le -\|z(t) - w(t)\|^2.$$
Multiplying by $2e^{2t}$ gives $\frac{d}{dt}\big(e^{2t}\|z(t) - w(t)\|^2\big) \le 0$. Integrating from $0$ to $t \ge 0$ yields
$$e^{2t}\|\Phi_t(z) - \Phi_t(w)\|^2 \le \|z - w\|^2 \implies \|\Phi_t(z) - \Phi_t(w)\| \le e^{-t}\|z - w\| \qquad \forall t \ge 0,\; \forall z,w \in \mathbb{R}^2.$$

#### 1.4 Energy Decay Bound $f(\Phi_t(z)) \le e^{-2t} f(z)$
From the $1$-strong convexity lower bound $f(u) \ge f(v) + \langle \nabla f(v), u - v \rangle + \frac{1}{2}\|u - v\|^2$, taking the minimum over $u \in \mathbb{R}^2$ on both sides (attained on the left at $0$ with $f(0) = 0$, and on the right at $u = v - \nabla f(v)$) gives the $1$-Polyak–Łojasiewicz inequality:
$$0 \ge f(v) - \frac{1}{2}\|\nabla f(v)\|^2 \implies \|\nabla f(v)\|^2 \ge 2f(v) \qquad \forall v \in \mathbb{R}^2.$$
Along $z(t) = \Phi_t(z)$,
$$\frac{d}{dt} f(z(t)) = -\langle \nabla f(z(t)), \nabla f(z(t)) \rangle = -\|\nabla f(z(t))\|^2 \le -2f(z(t)).$$
Therefore $\frac{d}{dt}\big(e^{2t} f(z(t))\big) \le 0$, and integrating from $0$ to $t \ge 0$ gives
$$f(\Phi_t(z)) \le e^{-2t} f(z) \qquad \forall t \ge 0,\; \forall z \in \mathbb{R}^2.$$

#### 1.5 Quantitative Convergence for a Stack $Z_n = T_\tau^n(Z_0)$
For $T_\tau = \Phi_\tau$ ($\tau > 0$), induction using the semigroup property $\Phi_{a+b} = \Phi_a \circ \Phi_b$ gives
$$Z_n = T_\tau^n(Z_0) = \Phi_{n\tau}(Z_0) \qquad \forall n \in \mathbb{N}_0.$$
Evaluating the continuous-time bounds at $t = n\tau$ (or iterating the one-block bounds $n$ times) yields, for all $Z_0, W_0 \in \mathbb{R}^2$ and all $n \ge 0$:
1. **Contraction of the $n$-block stack:** $\|T_\tau^n(Z_0) - T_\tau^n(W_0)\| \le e^{-n\tau}\|Z_0 - W_0\|$.
2. **Convergence to the equilibrium $0$:** Taking $W_0 = 0$ gives
   $$\|Z_n\| \le e^{-n\tau}\|Z_0\|,$$
   and using $\frac{1}{2}\|z\|^2 \le f(z)$ also gives $\|Z_n\| \le \sqrt{2 f(Z_n)} \le e^{-n\tau}\sqrt{2 f(Z_0)}$.
3. **Exponential energy dissipation:**
   $$f(Z_n) \le e^{-2n\tau} f(Z_0), \qquad f(Z_{n+1}) \le e^{-2\tau} f(Z_n).$$
4. **Step-increment and complexity bounds:** Successive blocks satisfy $\|Z_{n+1} - Z_n\| \le e^{-n\tau}\|T_\tau(Z_0) - Z_0\|$, and achieving $\|Z_n\| \le \varepsilon$ (respectively $f(Z_n) \le \varepsilon$) for $\varepsilon > 0$ requires at most $n \ge \frac{1}{\tau}\ln(\|Z_0\|/\varepsilon)$ (respectively $n \ge \frac{1}{2\tau}\ln(f(Z_0)/\varepsilon)$) blocks, depending only on the total horizon $n\tau$.

---

### 2. The Standard Proximal Certificate, Firm Nonexpansiveness, and Refutation of the Draft's Proximal Claim

Let $r : \mathbb{R}^2 \to (-\infty, +\infty]$ be proper ($\operatorname{dom} r := \{u \in \mathbb{R}^2 : r(u) < +\infty\} \neq \emptyset$ and $r > -\infty$), lower-semicontinuous (lsc), and convex, and define
$$\operatorname{prox}_r(z) := \arg\min_{u \in \mathbb{R}^2} \phi_z(u), \qquad \phi_z(u) := r(u) + \frac{\|u - z\|^2}{2}.$$

**Well-definedness of $\operatorname{prox}_r(z)$.** Fix $u_0 \in \operatorname{dom} r$. Because $\operatorname{epi} r \subset \mathbb{R}^2 \times \mathbb{R}$ is nonempty, closed, and convex and does not contain $(u_0, r(u_0) - 1)$, strict hyperplane separation gives $(a, \beta) \in \mathbb{R}^2 \times \mathbb{R}$ and $\gamma \in \mathbb{R}$ such that $\langle a, u_0 \rangle + \beta(r(u_0)-1) < \gamma < \langle a, u \rangle + \beta \alpha$ for all $(u, \alpha) \in \operatorname{epi} r$. Testing $(u_0, r(u_0)) \in \operatorname{epi} r$ forces $\beta > 0$, so $r(u) \ge \langle g, u \rangle + c$ for all $u \in \mathbb{R}^2$ (with $g = -a/\beta$, $c = \gamma/\beta$). Thus $\phi_z$ is lsc, proper, and coercive ($\phi_z(u) \ge \frac{1}{2}\|u - (z - g)\|^2 + c + \langle g, z \rangle - \frac{1}{2}\|g\|^2 \to +\infty$ as $\|u\| \to \infty$), so its nonempty closed sublevel set $\{u : \phi_z(u) \le \phi_z(u_0)\}$ is compact and $\phi_z$ attains a minimum $p \in \operatorname{dom} r$. Moreover, $p$ is unique because $\phi_z$ is $1$-strongly convex on $\operatorname{dom} r$.

#### 2.1 Proximal Certificate
**Theorem (Three-point proximal inequality).** *Suppose $T = \operatorname{prox}_r$ with $r : \mathbb{R}^2 \to (-\infty, +\infty]$ proper, lsc, and convex. Then for every $z \in \mathbb{R}^2$, setting $p = T(z) \in \operatorname{dom} r$, we have for all $u \in \operatorname{dom} r$:*
$$r(p) + \frac{\|p - z\|^2}{2} + \frac{\|u - p\|^2}{2} \le r(u) + \frac{\|u - z\|^2}{2}.$$

*Proof.* Fix $z \in \mathbb{R}^2$, let $p = T(z) \in \operatorname{dom} r$, and let $u \in \operatorname{dom} r$. For any $\theta \in (0, 1]$, define $u_\theta := (1 - \theta)p + \theta u$. By convexity of $r$,
$$r(u_\theta) \le (1-\theta)r(p) + \theta r(u).$$
Expanding the squared norms yields the identity
$$\|u_\theta - z\|^2 = \|(1-\theta)(p - z) + \theta(u - z)\|^2 = (1-\theta)\|p - z\|^2 + \theta\|u - z\|^2 - \theta(1-\theta)\|u - p\|^2.$$
Adding $r(u_\theta)$ and $\frac{1}{2}\|u_\theta - z\|^2$ and using optimality of $p$ for $\phi_z$,
$$\phi_z(p) \le \phi_z(u_\theta) \le (1-\theta)\phi_z(p) + \theta\phi_z(u) - \frac{\theta(1-\theta)}{2}\|u - p\|^2.$$
Since $\phi_z(p) \in \mathbb{R}$ is finite, subtracting $(1-\theta)\phi_z(p)$ and dividing by $\theta > 0$ yields
$$\phi_z(p) + \frac{1-\theta}{2}\|u - p\|^2 \le \phi_z(u) \qquad \forall \theta \in (0,1].$$
Letting $\theta \downarrow 0$ gives $\phi_z(p) + \frac{1}{2}\|u - p\|^2 \le \phi_z(u)$, which is the stated inequality. *(Equivalently, optimality $0 \in \partial r(p) + (p - z)$ means $z - p \in \partial r(p)$, so $r(u) \ge r(p) + \langle z - p, u - p \rangle$, and rearranging $\frac{1}{2}\|u-z\|^2 = \frac{1}{2}\|u-p\|^2 + \frac{1}{2}\|p-z\|^2 + \langle p - z, u - p \rangle$ gives the same bound.)* $\square$

#### 2.2 Firm Nonexpansiveness
**Corollary.** *Under $T = \operatorname{prox}_r$ as above, $T$ is firmly nonexpansive:*
$$\|T(z) - T(w)\|^2 \le \langle T(z) - T(w), z - w \rangle \qquad \forall z, w \in \mathbb{R}^2,$$
*and in particular nonexpansive ($\|T(z) - T(w)\| \le \|z - w\|$) and satisfies $\|T(z) - T(w)\|^2 + \|(\mathrm{id} - T)(z) - (\mathrm{id} - T)(w)\|^2 \le \|z - w\|^2$.*

*Proof.* Let $z, w \in \mathbb{R}^2$ and write $p = T(z) \in \operatorname{dom} r$, $q = T(w) \in \operatorname{dom} r$. Applying the proximal certificate at $(z, u=q)$ and at $(w, u=p)$ gives
$$r(p) + \frac{\|p - z\|^2}{2} + \frac{\|q - p\|^2}{2} \le r(q) + \frac{\|q - z\|^2}{2},$$
$$r(q) + \frac{\|q - w\|^2}{2} + \frac{\|p - q\|^2}{2} \le r(p) + \frac{\|p - w\|^2}{2}.$$
Summing both inequalities and canceling the finite quantity $r(p) + r(q)$ yields
$$\|p - q\|^2 \le \frac{1}{2}\big(\|q - z\|^2 - \|p - z\|^2\big) + \frac{1}{2}\big(\|p - w\|^2 - \|q - w\|^2\big).$$
Using $\|a\|^2 - \|b\|^2 = \langle a - b, a + b \rangle$,
$$\|q - z\|^2 - \|p - z\|^2 = \langle q - p, p + q - 2z \rangle, \qquad \|p - w\|^2 - \|q - w\|^2 = \langle q - p, 2w - p - q \rangle.$$
Summing these two terms gives $\langle q - p, 2w - 2z \rangle = 2\langle p - q, z - w \rangle$. Dividing by $2$ establishes
$$\|p - q\|^2 \le \langle p - q, z - w \rangle.$$
Cauchy–Schwarz gives $\|p - q\| \le \|z - w\|$, and expanding $\|(z - w) - (p - q)\|^2 = \|z - w\|^2 - 2\langle p - q, z - w \rangle + \|p - q\|^2 \le \|z - w\|^2 - \|p - q\|^2$ yields the equivalent identity. $\square$

---

#### 2.3 Why the Draft's Rationale Fails: $T_\tau = \Phi_\tau$ Has No Proximal Representation for Any $\tau > 0$

The draft asserts that because $\Phi_t$ is the gradient flow of a strongly convex energy and is contractive and dissipative, $T_\tau = \Phi_\tau = \operatorname{prox}_{r_\tau}$ for some proper lsc convex $r_\tau$. **This inference is false for every $\tau > 0$**; in fact, $T_\tau = \Phi_\tau$ violates both Jacobian symmetry (a necessary condition for any $C^1$ proximal map) and firm nonexpansiveness for every $\tau > 0$.

**Proposition (Refutation of $T_\tau = \operatorname{prox}_{r_\tau}$ and firm nonexpansiveness).** *For the flow map $T_\tau = \Phi_\tau$ of $\dot{z} = -\nabla f(z)$ and every $\tau > 0$:*
1. *There exists no proper, lsc, convex function $r_\tau : \mathbb{R}^2 \to (-\infty, +\infty]$ such that $T_\tau = \operatorname{prox}_{r_\tau}$.*
2. *$T_\tau$ is not firmly nonexpansive.*

*Proof of (1) (Conservative-field obstruction).* First suppose $T = \operatorname{prox}_r$ for a proper, lsc, convex $r$. Define the Moreau envelope $M_r(z) := \min_{u} \{ r(u) + \frac{1}{2}\|u - z\|^2 \} = r(T(z)) + \frac{1}{2}\|T(z) - z\|^2 \in \mathbb{R}$ and $\psi(z) := \frac{1}{2}\|z\|^2 - M_r(z)$. For any $z, w \in \mathbb{R}^2$, using $u = T(z)$ as a competitor in $M_r(w)$ gives
$$M_r(w) \le r(T(z)) + \frac{1}{2}\|T(z) - w\|^2 = M_r(z) + \frac{1}{2}\|w\|^2 - \frac{1}{2}\|z\|^2 - \langle T(z), w - z \rangle,$$
so $\psi(w) - \psi(z) \ge \langle T(z), w - z \rangle$. Swapping $z$ and $w$ gives $\psi(w) - \psi(z) \le \langle T(w), w - z \rangle$. Combining with nonexpansiveness of $T$ (Section 2.2),
$$0 \le \psi(w) - \psi(z) - \langle T(z), w - z \rangle \le \langle T(w) - T(z), w - z \rangle \le \|w - z\|^2.$$
Dividing by $\|w - z\|$ and letting $w \to z$ shows $\psi$ is everywhere differentiable with $\nabla \psi = T$. Hence if $T \in C^1(\mathbb{R}^2, \mathbb{R}^2)$, then $\psi \in C^2(\mathbb{R}^2, \mathbb{R})$ and by Schwarz's theorem its Jacobian $DT(z) = \nabla^2 \psi(z)$ must be symmetric for every $z \in \mathbb{R}^2$.

Now test $T_\tau = \Phi_\tau \in C^\infty(\mathbb{R}^2, \mathbb{R}^2)$ along $z_0 = \varepsilon e_1 = (\varepsilon, 0)^T$. Write $J(t; \varepsilon) := D_{z_0}\Phi_t(\varepsilon e_1)$ and $s(t; \varepsilon) := x(t; \varepsilon) + y(t; \varepsilon)$ where $(x(t;\varepsilon), y(t;\varepsilon))^T = \Phi_t(\varepsilon e_1)$. Differentiating the flow yields the variational equation
$$\partial_t J(t; \varepsilon) = -\nabla^2 f(\Phi_t(\varepsilon e_1))\,J(t; \varepsilon) = -\big(B + 3s(t;\varepsilon)^2 C\big) J(t; \varepsilon), \qquad J(0; \varepsilon) = I_2.$$
At $\varepsilon = 0$: $\Phi_t(0) \equiv 0$, $s(t;0) \equiv 0$, and $J(t;0) = e^{-t B} = \operatorname{diag}(e^{-t}, e^{-2t})$. Differentiating $\Phi_t(\varepsilon e_1)$ once in $\varepsilon$ at $\varepsilon = 0$ gives $\left.\partial_\varepsilon\right|_{\varepsilon=0} \Phi_t(\varepsilon e_1) = J(t;0)e_1 = (e^{-t}, 0)^T$, so $\left.\partial_\varepsilon s(t;\varepsilon)\right|_{\varepsilon=0} = e^{-t}$, $\left.\partial_\varepsilon(s^2)\right|_{\varepsilon=0} = 0$, and $\left.\partial_\varepsilon^2(s^2)\right|_{\varepsilon=0} = 2e^{-2t}$. Differentiating $\partial_t J(t;\varepsilon)$ in $\varepsilon$ at $\varepsilon=0$:
- $J^{(1)}(t) := \left.\partial_\varepsilon J(t;\varepsilon)\right|_{\varepsilon=0}$ satisfies $\dot{J}^{(1)} = -B J^{(1)}$ with $J^{(1)}(0)=0$, so $J^{(1)}(t) \equiv 0$;
- $J^{(2)}(t) := \left.\partial_\varepsilon^2 J(t;\varepsilon)\right|_{\varepsilon=0}$ satisfies
  $$\dot{J}^{(2)}(t) = -B J^{(2)}(t) - 6e^{-2t} C J(t;0), \qquad J^{(2)}(0) = 0.$$
Since $C J(t;0) = \begin{pmatrix} e^{-t} & e^{-2t} \\ e^{-t} & e^{-2t} \end{pmatrix}$, the $(1,2)$ and $(2,1)$ entries satisfy $\dot{J}^{(2)}_{12} = -J^{(2)}_{12} - 6e^{-4t}$ and $\dot{J}^{(2)}_{21} = -2J^{(2)}_{21} - 6e^{-3t}$ with zero initial values, giving at $t = \tau > 0$:
$$J^{(2)}_{12}(\tau) = -6\int_0^\tau e^{-(\tau - t)}e^{-4t}\,dt = 2(e^{-4\tau} - e^{-\tau}), \qquad J^{(2)}_{21}(\tau) = -6\int_0^\tau e^{-2(\tau - t)}e^{-3t}\,dt = 6(e^{-3\tau} - e^{-2\tau}).$$
Subtracting gives
$$\left.\frac{\partial^2}{\partial \varepsilon^2}\right|_{\varepsilon=0}\Big(J_{12}(\tau;\varepsilon) - J_{21}(\tau;\varepsilon)\Big) = 2\big(e^{-4\tau} - 3e^{-3\tau} + 3e^{-2\tau} - e^{-\tau}\big) = 2e^{-\tau}(e^{-\tau} - 1)^3 < 0 \qquad \forall \tau > 0.$$
Since $J_{12}(\tau; 0) - J_{21}(\tau; 0) = 0$ and $\left.\partial_\varepsilon\right|_{\varepsilon=0}(J_{12}-J_{21}) = 0$, for every $\tau > 0$ we have $J_{12}(\tau;\varepsilon) \neq J_{21}(\tau;\varepsilon)$ for all sufficiently small $\varepsilon \neq 0$. Thus $D\Phi_\tau$ is not symmetric, so $T_\tau \neq \operatorname{prox}_{r_\tau}$ for any proper, lsc, convex $r_\tau$.

*Proof of (2) (Failure of firm nonexpansiveness for every $\tau > 0$).* Change to orthonormal-rescaled coordinates $s = x + y$, $d = x - y$, i.e., $\binom{s}{d} = \sqrt{2} Q \binom{x}{y}$ where $Q = \frac{1}{\sqrt{2}}\begin{pmatrix} 1 & 1 \\ 1 & -1 \end{pmatrix}$ is orthogonal. Then the ODE becomes
$$\dot{s} = -2s^3 - \frac{3}{2}s + \frac{1}{2}d, \qquad \dot{d} = \frac{1}{2}s - \frac{3}{2}d,$$
and $J_{sd}(t) := \frac{\partial(s(t), d(t))}{\partial(s_0, d_0)} = Q\,D\Phi_t(z_0)\,Q^T$, so $M_{sd} := \frac{1}{2}(J_{sd}(\tau) + J_{sd}(\tau)^T) - J_{sd}(\tau)^T J_{sd}(\tau)$ has the exact same eigenvalues as $M := \frac{1}{2}(D\Phi_\tau(z_0) + D\Phi_\tau(z_0)^T) - D\Phi_\tau(z_0)^T D\Phi_\tau(z_0)$.

Consider $z_0 = (R, R)$ ($R \ge 10$), so $s(0) = 2R > 0$ and $d(0) = 0$.
- *Positivity:* Since $s(0) > 0$ and $\dot{d}(0) = R > 0$, we have $s(t) > 0$ and $d(t) > 0$ on small $(0, \eta)$; if either vanished first at $T > 0$, integrating $\frac{d}{dt}(e^{\frac{3}{2}t}d) = \frac{1}{2}e^{\frac{3}{2}t}s$ and $\frac{d}{dt}(e^{\int_0^t(2s^2+3/2)dr}s) = \frac{1}{2}e^{\int_0^t(2s^2+3/2)dr}d$ on $[0, T]$ gives a contradiction, so $s(t), d(t) > 0$ for all $t > 0$.
- *Uniform upper bound on $[0,\tau]$:* Let $\bar{d} := \max_{0 \le t \le \tau} d(t)$ and $a := (\bar{d}/2)^{1/3} + 1$. Whenever $s(t) \ge a$, $\dot{s}(t) \le -2s(t)^3 + \frac{1}{2}\bar{d} \le -s(t)^3 < 0$, so $s$ cannot cross $a$ from below; hence if $s(t_1) \ge a$ then $s(t) \ge a$ on $[0, t_1]$ and $(s^{-2})' \ge 2$ on $[0, t_1]$, giving $s(t_1) < (2t_1)^{-1/2}$. Thus $s(t) \le (2t)^{-1/2} + a$ for all $t \in (0, \tau]$. From $\dot{d} \le \frac{1}{2}s$ and $d(0)=0$,
  $$\bar{d} \le \frac{1}{2}\int_0^\tau \Big((2t)^{-1/2} + (\bar{d}/2)^{1/3} + 1\Big)\,dt = \sqrt{\frac{\tau}{2}} + \frac{\tau}{2}\big((\bar{d}/2)^{1/3} + 1\big),$$
  which implies $\bar{d} \le C_0(\tau) < \infty$ independent of $R$, and hence $s(t) \le (2t)^{-1/2} + (C_0(\tau)/2)^{1/3} + 1$ for all $t \in (0, \tau]$.
- *Variational system:* Writing the columns of $J_{sd}(t)$ as $(u_i(t), v_i(t))^T$ ($i=1,2$) with $(u_1(0),v_1(0))=(1,0)$ and $(u_2(0),v_2(0))=(0,1)$,
  $$\dot{u}_i = -(6s^2 + \tfrac{3}{2})u_i + \tfrac{1}{2}v_i, \qquad \dot{v}_i = \tfrac{1}{2}u_i - \tfrac{3}{2}v_i.$$
  By the same integrating-factor positivity argument, $u_i(t), v_i(t) > 0$ for all $t > 0$, and $\frac{1}{2}\frac{d}{dt}(u_i^2 + v_i^2) \le -(u_i^2 + v_i^2)$ yields $0 \le u_i(t), v_i(t) \le 1$ for all $t \ge 0$.
- *Decay of column 1:* While $s(t) \ge 1$, $\dot{s} \ge -2s^3 - \frac{3}{2}s \ge -\frac{7}{2}s^3$, so $(s^{-2})' \le 7$, ensuring $s(t) \ge 1$ and $s(t)^2 \ge ((2R)^{-2} + 7t)^{-1}$ on $[0, \min(\tau, \frac{3}{28}))$. Taking $\delta_R := \min(\tau, \frac{1}{10}, R^{-1})$, we have $\int_0^{\delta_R} 6s(t)^2\,dt \ge \frac{6}{7}\ln(1 + 28R^2\delta_R) \to +\infty$ as $R \to \infty$. On $[0, \delta_R]$, $v_1(\delta_R) \le \frac{1}{2}\delta_R$ and
  $$u_1(\delta_R) \le e^{-\int_0^{\delta_R} 6s^2\,dt} + \frac{1}{2}\int_0^{\delta_R} e^{-\int_t^{\delta_R}(6s^2 + 3/2)\,dr}\,dt \le e^{-\int_0^{\delta_R} 6s^2\,dt} + \frac{\delta_R}{2} \xrightarrow{R \to \infty} 0.$$
  By norm monotonicity on $[\delta_R, \tau]$, $u_1(\tau) \to 0$ and $v_1(\tau) \to 0$ as $R \to \infty$.
- *Uniform lower bound on $u_2(\tau)$:* Since $u_2 \ge 0$, $\dot{v}_2 \ge -\frac{3}{2}v_2$ gives $v_2(t) \ge e^{-\frac{3}{2}\tau}$ on $[0,\tau]$. On $[\tau/2, \tau]$, $s(t) \le K(\tau) := \tau^{-1/2} + (C_0(\tau)/2)^{1/3} + 1$, so $\dot{u}_2 \ge -(6K(\tau)^2 + \frac{3}{2})u_2 + \frac{1}{2}e^{-\frac{3}{2}\tau}$. Since $u_2(\tau/2) > 0$,
  $$u_2(\tau) \ge \frac{1}{2}e^{-\frac{3}{2}\tau}\int_{\tau/2}^\tau e^{-(6K(\tau)^2 + 3/2)(\tau - t)}\,dt =: c(\tau) > 0 \quad (\text{independent of } R).$$
- *Negative eigenvalue of $M$:* In $M_{sd}$, $M_{11} = u_1(\tau) - u_1(\tau)^2 - v_1(\tau)^2 \to 0$, $|M_{22}| = |v_2(\tau) - u_2(\tau)^2 - v_2(\tau)^2| \le 1$, and $M_{12} = \frac{1}{2}(u_2(\tau) + v_1(\tau)) - u_1(\tau)u_2(\tau) - v_1(\tau)v_2(\tau) \ge \frac{1}{2}c(\tau) - o(1)$ as $R \to \infty$. Hence $\limsup_{R \to \infty}\det M_{sd} \le -\frac{1}{4}c(\tau)^2 < 0$. Choosing $R$ large enough that $M$ has an eigenvalue $\lambda < 0$ with unit eigenvector $\eta \in \mathbb{R}^2$, setting $w_\varepsilon = z_0 + \varepsilon\eta$ gives
  $$\lim_{\varepsilon \to 0}\frac{\|\Phi_\tau(w_\varepsilon) - \Phi_\tau(z_0)\|^2 - \langle \Phi_\tau(w_\varepsilon) - \Phi_\tau(z_0), w_\varepsilon - z_0 \rangle}{\varepsilon^2} = \|D\Phi_\tau(z_0)\eta\|^2 - \langle D\Phi_\tau(z_0)\eta, \eta \rangle = -\lambda > 0,$$
  so firm nonexpansiveness fails for small $\varepsilon > 0$. *(Note that contraction with factor $e^{-\tau} < 1/2$ for $\tau > \ln 2$ still does not force firm nonexpansiveness when $D\Phi_\tau$ is non-symmetric.)* $\square$

---

### 3. Deployment Description (Suitable for the Methods Section)

Each denoising block $T_\tau = \Phi_\tau : \mathbb{R}^2 \to \mathbb{R}^2$ ($\tau > 0$) implements the exact time-$\tau$ flow map of the autonomous continuous-time gradient system $\dot{z} = -\nabla f(z)$ for the smooth, $1$-strongly convex energy $f(x,y) = (x^2 + 2y^2)/2 + (x+y)^4/4$, which is globally forward well-posed and has unique equilibrium $z^* = (0,0)$ ($\min f = f(0,0) = 0$). A single block guarantees strict Euclidean contraction with factor $e^{-\tau}$ ($\|T_\tau(z) - T_\tau(w)\| \le e^{-\tau}\|z - w\|$) and exponential energy dissipation ($f(T_\tau(z)) \le e^{-2\tau}f(z)$). By the flow semigroup property, stacking $n$ identical blocks is mathematically equivalent to integrating the exact flow over cumulative horizon $n\tau$, $Z_n = T_\tau^n(Z_0) = \Phi_{n\tau}(Z_0)$, yielding uniform global exponential convergence to the zero equilibrium—$\|Z_n - W_n\| \le e^{-n\tau}\|Z_0 - W_0\|$, $\|Z_n\| \le e^{-n\tau}\|Z_0\|$, and $f(Z_n) \le e^{-2n\tau}f(Z_0)$—with no discretization step-size instability. Unlike an implicit-Euler step $(I + \tau \nabla f)^{-1} = \operatorname{prox}_{\tau f}$, which scales $f$ by $\tau$ inside the unit-coefficient proximal operator $\operatorname{prox}_r(z) = \arg\min_u \{ r(u) + \frac{1}{2}\|u-z\|^2 \}$ (equivalently placing $1/\tau$ in front of $\frac{1}{2}\|u-z\|^2$, yielding Lipschitz constant $(1+\tau)^{-1}$ and firm nonexpansiveness), the parameter $\tau > 0$ here is strictly the continuous ODE evolution time, not a proximal penalty coefficient; moreover, for every $\tau > 0$, the exact flow map $T_\tau = \Phi_\tau$ has a non-symmetric Jacobian and fails firm nonexpansiveness, so it does not admit a representation $T_\tau = \operatorname{prox}_{r_\tau}$ for any proper, lower-semicontinuous, convex $r_\tau$ and should be characterized strictly as a continuous-time strongly convex gradient-flow contraction rather than a convex proximal regularization step.
