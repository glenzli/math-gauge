Below are **(I) the Mathematical Appendix** (covering Items 1 and 2, together with a rigorous proof that the draft rationale’s claim $T_\tau = \operatorname{prox}_{r_\tau}$ fails for every $\tau > 0$, and the exact relation between the flow horizon $\tau$ and the proximal convention) and **(II) the Methods-Section Deployment Description** (Item 3, ready to replace the flawed draft rationale).

---

## I. Mathematical Appendix

throughout, $\mathbb{R}^2$ is equipped with the standard Euclidean inner product $\langle z, w \rangle = x_1 x_2 + y_1 y_2$ and norm $\|z\| = \sqrt{\langle z, z \rangle}$ for $z = (x_1, y_1)$, $w = (x_2, y_2)$.

### A.1. Global Well-Posedness, Equilibrium, Contraction, Dissipation, and Stack Convergence

Consider the smooth potential $f \in C^\infty(\mathbb{R}^2; \mathbb{R})$ defined for $z = (x, y) \in \mathbb{R}^2$ by
$$f(x, y) = \frac{x^2 + 2y^2}{2} + \frac{(x + y)^4}{4},$$
and the autonomous gradient system
$$\dot{z}(t) = -\nabla f(z(t)), \qquad z(0) = z \in \mathbb{R}^2.$$

#### 1. Strong convexity and unique equilibrium
Direct differentiation gives, for $z = (x, y) \in \mathbb{R}^2$,
$$\nabla f(x, y) = \begin{pmatrix} x + (x + y)^3 \\ 2y + (x + y)^3 \end{pmatrix}, \qquad \nabla^2 f(x, y) = \begin{pmatrix} 1 & 0 \\ 0 & 2 \end{pmatrix} + 3(x + y)^2 \begin{pmatrix} 1 & 1 \\ 1 & 1 \end{pmatrix}.$$
For every $z \in \mathbb{R}^2$ and $v = (v_1, v_2) \in \mathbb{R}^2$,
$$\langle v, \nabla^2 f(z) v \rangle = v_1^2 + 2v_2^2 + 3(x + y)^2(v_1 + v_2)^2 \ge v_1^2 + v_2^2 = \|v\|^2,$$
so $\nabla^2 f(z) \succeq I_2$ everywhere on $\mathbb{R}^2$ (and the modulus $\mu = 1$ is sharp, attained at $z = (0, 0)$ along $v = (1, 0)$). Consequently, $f$ is $1$-strongly convex on $\mathbb{R}^2$: for all $z, w \in \mathbb{R}^2$, integrating along $w + s(z - w)$ for $s \in [0, 1]$ yields
$$\langle \nabla f(z) - \nabla f(w), z - w \rangle = \int_0^1 \langle z - w, \nabla^2 f(w + s(z - w))(z - w) \rangle \, ds \ge \|z - w\|^2, \tag{1}$$
and Taylor's theorem with integral remainder gives
$$f(w) \ge f(z) + \langle \nabla f(z), w - z \rangle + \frac{1}{2}\|w - z\|^2. \tag{2}$$

Equilibria of $\dot{z} = -\nabla f(z)$ satisfy $\nabla f(z^*) = 0$. Clearly $\nabla f(0, 0) = (0, 0)$ and $f(0, 0) = 0$. If $\nabla f(z^*) = 0$, then setting $(z, w) = (z^*, 0)$ in $(1)$ gives $0 \ge \|z^*\|^2$, hence $z^* = (0, 0)$ is the **unique equilibrium** of the flow and the unique global minimizer of $f$ on $\mathbb{R}^2$ (indeed, $(2)$ at $z = 0$ gives the coercivity bound $f(w) \ge \frac{1}{2}\|w\|^2 \ge 0$).

#### 2. Forward global well-posedness
Because $-\nabla f$ is polynomial ($C^\infty$), it is locally Lipschitz on $\mathbb{R}^2$. By the Picard–Lindelöf theorem, for each $z \in \mathbb{R}^2$ there exists a unique maximal forward solution $t \mapsto \Phi_t(z)$ defined on $[0, T_{\max}(z))$ for some $T_{\max}(z) \in (0, \infty]$. Along this trajectory,
$$\frac{d}{dt} f(\Phi_t(z)) = \langle \nabla f(\Phi_t(z)), -\nabla f(\Phi_t(z)) \rangle = -\|\nabla f(\Phi_t(z))\|^2 \le 0, \tag{3}$$
so $t \mapsto f(\Phi_t(z))$ is nonincreasing on $[0, T_{\max}(z))$. Using $\frac{1}{2}\|u\|^2 \le f(u)$, we obtain for all $t \in [0, T_{\max}(z))$ that
$$\|\Phi_t(z)\| \le \sqrt{2 f(\Phi_t(z))} \le \sqrt{2 f(z)},$$
so the trajectory stays inside the compact ball $\overline{B(0, \sqrt{2f(z)})}$. By the standard continuation / blow-up alternative for locally Lipschitz ODEs, $T_{\max}(z) = +\infty$. By classical smooth dependence on initial data (and the contraction bound proved next), $(t, z) \mapsto \Phi_t(z)$ is globally defined and $C^\infty$ on $[0, \infty) \times \mathbb{R}^2$, is Lipschitz-continuous in $z$, and satisfies the autonomous semigroup property $\Phi_0 = \mathrm{id}_{\mathbb{R}^2}$ and $\Phi_{t + s} = \Phi_t \circ \Phi_s$ for all $t, s \ge 0$, with $\Phi_t(0) = 0$.

#### 3. Pairwise state contraction and exponential energy dissipation
- **State contraction**: Let $z, w \in \mathbb{R}^2$ and set $\Delta(t) := \Phi_t(z) - \Phi_t(w)$ for $t \ge 0$. Differentiating $\frac{1}{2}\|\Delta(t)\|^2$ and applying $(1)$ gives
  $$\frac{d}{dt}\left(\frac{1}{2}\|\Delta(t)\|^2\right) = -\langle \nabla f(\Phi_t(z)) - \nabla f(\Phi_t(w)), \Delta(t) \rangle \le -\|\Delta(t)\|^2.$$
  Therefore $\frac{d}{dt}\big(e^{2t}\|\Delta(t)\|^2\big) = 2e^{2t}\big(\frac{d}{dt}\frac{1}{2}\|\Delta(t)\|^2 + \|\Delta(t)\|^2\big) \le 0$. Integrating over $[0, t]$ and taking square roots yields
  $$\|\Phi_t(z) - \Phi_t(w)\| \le e^{-t}\|z - w\| \qquad \forall t \ge 0,\; \forall z, w \in \mathbb{R}^2. \tag{4}$$

- **Energy dissipation**: Taking the infimum over $w \in \mathbb{R}^2$ on both sides of $(2)$ at any $u \in \mathbb{R}^2$ (the right-hand side is minimized at $w = u - \nabla f(u)$) gives the Polyak–Łojasiewicz inequality
  $$0 = \inf_{w \in \mathbb{R}^2} f(w) \ge f(u) - \frac{1}{2}\|\nabla f(u)\|^2 \implies \|\nabla f(u)\|^2 \ge 2 f(u) \qquad \forall u \in \mathbb{R}^2.$$
  Combining this with $(3)$ along $u = \Phi_t(z)$ gives $\frac{d}{dt} f(\Phi_t(z)) \le -2 f(\Phi_t(z))$, so $\frac{d}{dt}\big(e^{2t} f(\Phi_t(z))\big) \le 0$. Integrating from $0$ to $t$ yields
  $$f(\Phi_t(z)) \le e^{-2t} f(z) \qquad \forall t \ge 0,\; \forall z \in \mathbb{R}^2. \tag{5}$$

*(Remark: Both rates $e^{-t}$ and $e^{-2t}$ are sharp, as seen from the linearization $\dot{x} = -x$, $\dot{y} = -2y$ at the origin along the $x$-axis.)*

#### 4. Quantitative convergence for an $n$-block stack
For fixed $\tau > 0$, let $T_\tau := \Phi_\tau$ and $Z_n := T_\tau^n(Z_0)$ for $n \in \mathbb{N}_0$. By the semigroup property, $T_\tau^n = \Phi_{n\tau}$ and $T_\tau(0) = 0$. Setting $q_\tau := e^{-\tau} \in (0, 1)$, $(4)$ and $(5)$ yield, for all $Z_0, W_0 \in \mathbb{R}^2$ and $n \ge 0$:
1. **Stack Lipschitz stability**: $\|T_\tau^n(Z_0) - T_\tau^n(W_0)\| \le e^{-n\tau}\|Z_0 - W_0\| = q_\tau^n \|Z_0 - W_0\|$.
2. **State convergence to equilibrium** ($W_0 = 0$): $\|Z_n\| \le e^{-n\tau}\|Z_0\| = q_\tau^n \|Z_0\| \to 0$ as $n \to \infty$.
3. **Energy decay**: $0 \le f(Z_n) \le e^{-2n\tau} f(Z_0) = q_\tau^{2n} f(Z_0) \to 0$ as $n \to \infty$ (with per-block decrease $f(Z_{k+1}) \le e^{-2\tau} f(Z_k)$).
4. **Step-displacement and *a posteriori* bounds**: $\|Z_{n+1} - Z_n\| = \|T_\tau^n(Z_1) - T_\tau^n(Z_0)\| \le e^{-n\tau}\|Z_1 - Z_0\|$, and by the triangle inequality $\|Z_n\| \le \|Z_n - Z_{n+1}\| + \|T_\tau(Z_n) - T_\tau(0)\| \le \|Z_{n+1} - Z_n\| + e^{-\tau}\|Z_n\|$, giving the observable error certificate $\|Z_n\| \le (1 - e^{-\tau})^{-1}\|Z_{n+1} - Z_n\|$.
5. **Depth complexity**: For any tolerance $\varepsilon > 0$, $\|Z_n\| \le \varepsilon$ holds for all $n \ge \max\!\big\{0, \lceil \tau^{-1} \ln(\|Z_0\|/\varepsilon) \rceil\big\}$, and $f(Z_n) \le \varepsilon$ holds for all $n \ge \max\!\big\{0, \lceil (2\tau)^{-1} \ln(f(Z_0)/\varepsilon) \rceil\big\}$.

---

### A.2. Proximal Certificate and Firm Nonexpansiveness

Recall the unit-weight convention
$$\operatorname{prox}_r(z) := \operatorname{argmin}_{u \in \mathbb{R}^2} \left\{ r(u) + \frac{1}{2}\|u - z\|^2 \right\}.$$

**Proposition A.1 (Proximal three-point certificate and firm nonexpansiveness).** *Let $r : \mathbb{R}^2 \to (-\infty, +\infty]$ be proper, lower-semicontinuous (lsc), and convex, and suppose $T : \mathbb{R}^2 \to \mathbb{R}^2$ satisfies $T = \operatorname{prox}_r$. Then $T$ is uniquely well-defined with $T(\mathbb{R}^2) \subset \operatorname{dom} r$. Moreover:*
1. *(Proximal certificate)* *For every $z \in \mathbb{R}^2$, setting $p = T(z)$, and every $u \in \operatorname{dom} r$,*
   $$r(p) + \frac{1}{2}\|p - z\|^2 + \frac{1}{2}\|u - p\|^2 \le r(u) + \frac{1}{2}\|u - z\|^2. \tag{6}$$
2. *(Firm nonexpansiveness)* *For all $z, w \in \mathbb{R}^2$,*
   $$\|T(z) - T(w)\|^2 \le \langle T(z) - T(w), z - w \rangle, \tag{7}$$
   *or equivalently,*
   $$\|T(z) - T(w)\|^2 + \|(I - T)(z) - (I - T)(w)\|^2 \le \|z - w\|^2. \tag{8}$$

*Proof.* Fix $z \in \mathbb{R}^2$ and define $\phi_z(u) := r(u) + \frac{1}{2}\|u - z\|^2$.
- **Well-definedness**: Since $r$ is proper, choose $u_0 \in \operatorname{dom} r$, so $m := \inf_{u \in \mathbb{R}^2} \phi_z(u) \le \phi_z(u_0) < +\infty$. Suppose toward a contradiction that there exists a sequence $(u_k)$ with $\phi_z(u_k) \le \phi_z(u_0)$ and either $\|u_k\| \to \infty$ or $\phi_z(u_k) \to -\infty$. If $(u_k)$ is bounded, compactness in $\mathbb{R}^2$ and lower semicontinuity of $r$ give a cluster point $\bar{u}$ with $r(\bar{u}) > -\infty$, preventing $\phi_z(u_k) \to -\infty$. If $\|u_k - u_0\| \to \infty$, let $t_k := \|u_k - u_0\|^{-1} \in (0, 1)$ for large $k$ and $w_k := (1 - t_k)u_0 + t_k u_k \in \partial B(u_0, 1)$. Convexity of $r$ gives
  $$r(w_k) \le (1 - t_k)r(u_0) + t_k\left(\phi_z(u_k) - \frac{1}{2}\|u_k - z\|^2\right) \to -\infty,$$
  contradicting lower semicontinuity of $r$ and $r > -\infty$ at any cluster point of $(w_k)$ on the compact sphere $\partial B(u_0, 1)$. Thus $m \in \mathbb{R}$ and every minimizing sequence $\phi_z(u_k) \to m$ is bounded; by convexity of $r$ and the parallelogram identity, for any $u, v \in \operatorname{dom} r$,
  $$\frac{1}{8}\|u - v\|^2 \le \frac{1}{2}\phi_z(u) + \frac{1}{2}\phi_z(v) - \phi_z\!\left(\frac{u + v}{2}\right) \le \frac{1}{2}\phi_z(u) + \frac{1}{2}\phi_z(v) - m.$$
  Applying this to a minimizing sequence shows $(u_k)$ is Cauchy, hence $u_k \to p$ for some $p \in \mathbb{R}^2$, and lsc gives $m \le \phi_z(p) \le \liminf_{k\to\infty} \phi_z(u_k) = m < +\infty$, so $p \in \operatorname{dom} r$ minimizes $\phi_z$. Applying the same inequality to two minimizers $p, \tilde{p}$ yields $\|p - \tilde{p}\|^2 \le 0$, proving uniqueness.

- **Proof of $(6)$**: Let $p = T(z) \in \operatorname{dom} r$, $u \in \operatorname{dom} r$, and $\theta \in (0, 1)$. Put $u_\theta := (1 - \theta)p + \theta u = p + \theta(u - p)$. By optimality $\phi_z(p) \le \phi_z(u_\theta)$ and convexity of $r$,
  $$r(p) + \frac{1}{2}\|p - z\|^2 \le (1 - \theta)r(p) + \theta r(u) + \frac{1}{2}\|(p - z) + \theta(u - p)\|^2.$$
  Expanding $\frac{1}{2}\|(p - z) + \theta(u - p)\|^2 = \frac{1}{2}\|p - z\|^2 + \theta\langle p - z, u - p \rangle + \frac{\theta^2}{2}\|u - p\|^2$, canceling $\frac{1}{2}\|p - z\|^2$, rearranging, and dividing by $\theta > 0$ gives
  $$r(p) + \langle z - p, u - p \rangle \le r(u) + \frac{\theta}{2}\|u - p\|^2.$$
  Letting $\theta \downarrow 0$ yields $r(p) + \langle z - p, u - p \rangle \le r(u)$. Substituting the three-point Euclidean identity
  $$\langle z - p, u - p \rangle = \frac{1}{2}\|p - z\|^2 + \frac{1}{2}\|u - p\|^2 - \frac{1}{2}\|u - z\|^2$$
  and adding $\frac{1}{2}\|u - z\|^2$ to both sides yields $(6)$.

- **Proof of $(7)$ and $(8)$**: For $z, w \in \mathbb{R}^2$, set $p = T(z) \in \operatorname{dom} r$ and $q = T(w) \in \operatorname{dom} r$. Apply $(6)$ at $z$ with $u = q$, and at $w$ with $u = p$:
  $$r(p) + \frac{1}{2}\|p - z\|^2 + \frac{1}{2}\|q - p\|^2 \le r(q) + \frac{1}{2}\|q - z\|^2,$$
  $$r(q) + \frac{1}{2}\|q - w\|^2 + \frac{1}{2}\|p - q\|^2 \le r(p) + \frac{1}{2}\|p - w\|^2.$$
  Adding the two inequalities cancels the finite quantities $r(p), r(q)$ and gives
  $$\|p - q\|^2 \le \frac{1}{2}\Big(\|q - z\|^2 - \|p - z\|^2 + \|p - w\|^2 - \|q - w\|^2\Big).$$
  Since $\|q - z\|^2 - \|p - z\|^2 = \|q\|^2 - \|p\|^2 + 2\langle p - q, z \rangle$ and $\|p - w\|^2 - \|q - w\|^2 = \|p\|^2 - \|q\|^2 - 2\langle p - q, w \rangle$, the right-hand side equals $\langle p - q, z - w \rangle$, establishing $(7)$ (and Cauchy–Schwarz immediately gives nonexpansiveness $\|T(z) - T(w)\| \le \|z - w\|$). Finally, expanding
  $$\|(I - T)(z) - (I - T)(w)\|^2 = \|(z - w) - (p - q)\|^2 = \|z - w\|^2 - 2\langle p - q, z - w \rangle + \|p - q\|^2$$
  and applying $2\|p - q\|^2 \le 2\langle p - q, z - w \rangle$ yields $(8)$. $\blacksquare$

---

### A.3. Why the Exact Flow Block Has No Convex Proximal Representation (and Role of $\tau$)

The current draft infers from strong convexity, contractivity, and dissipativity that $T_\tau = \operatorname{prox}_{r_\tau}$ for some proper, lsc, convex $r_\tau$. **That inference is invalid: for every $\tau > 0$, no such $r_\tau$ exists.**

**Proposition A.2 (Non-existence of convex proximal representation for $T_\tau = \Phi_\tau$).** *For every $\tau > 0$, there is no proper, lower-semicontinuous, convex function $r_\tau : \mathbb{R}^2 \to (-\infty, +\infty]$ such that $\Phi_\tau = \operatorname{prox}_{r_\tau}$.*

*Proof.* Suppose first that a $C^1$ map $T = (T_1, T_2) : \mathbb{R}^2 \to \mathbb{R}^2$ admits $T = \operatorname{prox}_r$ with $r$ proper, lsc, and convex. Define $\psi(z) := \langle z, T(z) \rangle - r(T(z)) - \frac{1}{2}\|T(z)\|^2 \in \mathbb{R}$. For any $z, w \in \mathbb{R}^2$, setting $p = T(z)$ and $q = T(w)$, expanding the squared distances in $(6)$ with $u = q$ gives $\psi(z) \ge \psi(w) + \langle z - w, q \rangle + \frac{1}{2}\|q - p\|^2$. Combining this with the symmetric inequality upon swapping $z \leftrightarrow w$ and using $\|q - p\| \le \|w - z\|$ from $(7)$ yields
$$0 \le \frac{1}{2}\|q - p\|^2 \le \psi(w) - \psi(z) - \langle T(z), w - z \rangle \le \langle q - p, w - z \rangle \le \|w - z\|^2.$$
Dividing by $\|w - z\|$ as $w \to z$ shows $\psi$ is differentiable everywhere with $\nabla \psi(z) = T(z)$. Since $T \in C^1$, $\psi \in C^2(\mathbb{R}^2)$, so Schwarz's theorem forces the Jacobian $DT(z) = \nabla^2 \psi(z)$ to be symmetric everywhere:
$$\frac{\partial T_2}{\partial x}(x, y) - \frac{\partial T_1}{\partial y}(x, y) = 0 \qquad \forall (x, y) \in \mathbb{R}^2. \tag{9}$$

Now write $\Phi_t(x, y) = (X(t, x, y), Y(t, x, y)) \in C^\infty([0, \infty) \times \mathbb{R}^2; \mathbb{R}^2)$ and $S := X + Y$, so
$$\dot{X} = -X - S^3, \quad X(0, x, y) = x; \qquad \dot{Y} = -2Y - S^3, \quad Y(0, x, y) = y.$$
Evaluate partial derivatives with respect to $(x, y)$ at $(x, y) = (0, 0)$, where $X(t, 0, 0) = Y(t, 0, 0) = S(t, 0, 0) = 0$:
1. *First partials*: Since $S^3$ vanishes to third order at $(0,0)$, $\dot{X}_x = -X_x$ ($X_x(0)=1$), $\dot{Y}_x = -2Y_x$ ($Y_x(0)=0$), $\dot{X}_y = -X_y$ ($X_y(0)=0$), $\dot{Y}_y = -2Y_y$ ($Y_y(0)=1$). Hence at $(0,0)$, $X_x(t) = e^{-t}$, $Y_x(t) = 0$, $X_y(t) = 0$, $Y_y(t) = e^{-2t}$, so $S_x(t) = e^{-t}$ and $S_y(t) = e^{-2t}$.
2. *Second partials*: Every second partial of $S^3$ carries a factor of $S = 0$ at $(0,0)$, so all second partials of $X, Y, S$ vanish identically at $(0,0)$.
3. *Third partials*: Because $S$ and all second partials of $S$ vanish at $(0,0)$, $\partial_{uvw}^3(S^3)\big|_{(0,0)} = 6 S_u S_v S_w$ for any $u, v, w \in \{x, y\}$. Differentiating the ODEs at $(0,0)$ therefore gives the linear scalar initial-value problems
   $$\dot{Y}_{xxx}(t, 0, 0) + 2 Y_{xxx}(t, 0, 0) = -6 S_x(t)^3 = -6 e^{-3t}, \qquad Y_{xxx}(0, 0, 0) = 0,$$
   $$\dot{X}_{xxy}(t, 0, 0) + X_{xxy}(t, 0, 0) = -6 S_x(t)^2 S_y(t) = -6 e^{-4t}, \qquad X_{xxy}(0, 0, 0) = 0.$$
   Integrating via integrating factors $e^{2t}$ and $e^t$ over $[0, \tau]$ yields
   $$Y_{xxx}(\tau, 0, 0) = -6 e^{-2\tau}(1 - e^{-\tau}), \qquad X_{xxy}(\tau, 0, 0) = -2 e^{-\tau}(1 - e^{-3\tau}).$$
   Hence, for every $\tau > 0$,
   $$\left.\frac{\partial^2}{\partial x^2}\left(\frac{\partial \Phi_{\tau, 2}}{\partial x} - \frac{\partial \Phi_{\tau, 1}}{\partial y}\right)\right|_{(0,0)} = Y_{xxx}(\tau, 0, 0) - X_{xxy}(\tau, 0, 0) = 2 e^{-\tau}(1 - e^{-\tau})^3 > 0.$$
Thus $D\Phi_\tau$ is non-symmetric near $(0, 0)$, violating $(9)$ for every $\tau > 0$. $\blacksquare$

**Geometric reason and distinction between flow time $\tau$ and the proximal convention.**
Along curved trajectories where $x + y \ne 0$, the quadratic Hessian $\operatorname{diag}(1, 2)$ and the quartic rank-$1$ Hessian $3(x + y)^2 \mathbf{1}\mathbf{1}^\top$ do not commute; consequently, the variational flow $\dot{J} = -\nabla^2 f(\Phi_t(z)) J$, $J(0) = I_2$, generates a non-symmetric Jacobian $D\Phi_\tau(z)$ (and away from the origin, $\Phi_\tau$ can even violate firm nonexpansiveness $(7)$). Moreover:
- In our definition $\operatorname{prox}_r(z) = \operatorname{argmin}_u \{r(u) + \frac{1}{2}\|u - z\|^2\}$, the quadratic anchor carries a **fixed unit weight** (coefficient $\frac{1}{2}$, i.e., resolvent $(I + \partial r)^{-1}$). An implicit-Euler step of step size $\tau > 0$ on $f$ enters by scaling the regularizer to $r = \tau f$, namely $\operatorname{prox}_{\tau f}(z) = (I + \tau \nabla f)^{-1}(z) = \operatorname{argmin}_u \{f(u) + \frac{1}{2\tau}\|u - z\|^2\}$, which contracts distances by $(1 + \tau)^{-1}$ and satisfies $(\operatorname{prox}_{\tau f})^n \ne \operatorname{prox}_{n\tau f}$.
- In the deployed block $T_\tau = \Phi_\tau$, $\tau > 0$ is instead the **continuous ODE integration horizon** in $T_\tau(z) = z - \int_0^\tau \nabla f(\Phi_s(z))\,ds$. It composes additively as an exact semigroup ($T_\tau^n = \Phi_{n\tau}$), contracts distances at the strictly faster exponential rate $e^{-\tau} < (1 + \tau)^{-1}$, agrees with $\operatorname{prox}_{\tau f}(z)$ only to first order as $\tau \downarrow 0$ ($\Phi_\tau(z) = \operatorname{prox}_{\tau f}(z) + O(\tau^2)$), and cannot be written as $\operatorname{prox}_{r_\tau}$ for any convex $r_\tau$ when $\tau > 0$.

---

## II. Methods-Section Deployment Description (Item 3)

> **Continuous-Flow Denoising Block and Stack Guarantees.** Each denoising block implements the exact time-$\tau$ flow map $T_\tau := \Phi_\tau : \mathbb{R}^2 \to \mathbb{R}^2$ ($\tau > 0$) of the autonomous gradient ODE $\dot{z} = -\nabla f(z)$ for the $1$-strongly convex potential $f(x,y) = \frac{1}{2}(x^2 + 2y^2) + \frac{1}{4}(x+y)^4$. Because $-\nabla f$ is smooth and $f$ is coercive with $\nabla^2 f(z) \succeq I_2$ everywhere, $\Phi_t$ is globally well-posed forward in time on $[0, \infty) \times \mathbb{R}^2$ and admits the origin $z^* = (0,0)$ as its unique equilibrium and global energy minimizer ($f(0) = 0$). A single block $T_\tau$ guarantees strict Euclidean contraction $\|T_\tau(z) - T_\tau(w)\| \le e^{-\tau}\|z - w\|$ for all $z, w \in \mathbb{R}^2$ and exponential energy dissipation $f(T_\tau(z)) \le e^{-2\tau} f(z)$. By autonomous time-invariance, stacking $n$ identical blocks satisfies the exact semigroup identity $Z_n = T_\tau^n(Z_0) = \Phi_{n\tau}(Z_0)$, yielding uniform $e^{-n\tau}$-Lipschitz input-perturbation stability, global geometric convergence $\|Z_n\| \le e^{-n\tau}\|Z_0\|$ to $z^* = 0$, and geometric energy decay $f(Z_n) \le e^{-2n\tau} f(Z_0)$. Here the hyperparameter $\tau > 0$ is the continuous ODE evolution duration, which must be distinguished from the fixed unit coefficient ($\frac{1}{2}$) multiplying $\|u - z\|^2$ in our proximal convention $\operatorname{prox}_r(z) = \operatorname{argmin}_u \{r(u) + \frac{1}{2}\|u - z\|^2\}$ (where a step size $\tau$ in an implicit-Euler discretization $(I + \tau \nabla f)^{-1} = \operatorname{prox}_{\tau f}$ instead scales the penalty functional relative to the unit quadratic tether, achieves contraction $(1+\tau)^{-1}$, and does not satisfy $(\operatorname{prox}_{\tau f})^n = \operatorname{prox}_{n\tau f}$). Furthermore, although $T_\tau(z) = \operatorname{prox}_{\tau f}(z) + O(\tau^2)$ as $\tau \downarrow 0$, non-commutativity of the quadratic and quartic Hessian terms of $f$ makes the Jacobian $D\Phi_\tau$ non-symmetric for every $\tau > 0$; thus $T_\tau$ does not admit an exact convex proximal representation $T_\tau = \operatorname{prox}_{r_\tau}$ for any proper lower-semicontinuous convex $r_\tau$, and its deployment guarantees rest directly on continuous-time gradient-flow contraction and Lyapunov dissipation rather than proximal firm nonexpansiveness.
