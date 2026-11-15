{}
> **Key revision note on the draft rationale.** The first claim in the draft (*strong convexity, strict contractivity, and energy dissipation of the continuous gradient flow*) is **true** and proved in Section A.1. However, the second claim (*"Thus, for every $\tau > 0$, the exact block has a convex proximal representation $T_\tau = \operatorname{prox}_{r_\tau}$ for some proper lower-semicontinuous convex $r_\tau$"*) is **false for every $\tau > 0$**. Using the proximal certificate and firm nonexpansiveness proved in Section A.2, Section A.3 proves analytically that for every $\tau > 0$, $T_\tau = \Phi_\tau$ violates **both** necessary conditions for a proximal representation: its Jacobian $D\Phi_\tau(z)$ is non-symmetric at bounded states (so $\Phi_\tau$ is not conservative even locally), and $\Phi_\tau$ fails global firm nonexpansiveness on $\mathbb{R}^2$. Section 3 below provides the corrected deployment/methods text.

---

## Mathematical Appendix

Throughout, $\mathbb{R}^2$ carries the standard Euclidean inner product $\langle z, w \rangle = x_1 x_2 + y_1 y_2$ and norm $\|z\| = \sqrt{x^2 + y^2}$ for $z = (x, y) \in \mathbb{R}^2$.

### 1. Well-Posedness, Equilibrium, Contractivity, Energy Decay, and Stack Convergence

Consider the smooth polynomial energy $f \in C^\infty(\mathbb{R}^2)$ given by
$$f(x, y) = \frac{x^2 + 2y^2}{2} + \frac{(x + y)^4}{4}.$$

#### Strong convexity and unique equilibrium
Direct differentiation gives the gradient and Hessian:
$$\nabla f(x, y) = \begin{pmatrix} x + (x + y)^3 \\ 2y + (x + y)^3 \end{pmatrix}, \qquad \nabla^2 f(x, y) = \begin{pmatrix} 1 & 0 \\ 0 & 2 \end{pmatrix} + 3(x + y)^2 \begin{pmatrix} 1 & 1 \\ 1 & 1 \end{pmatrix}.$$
For every $z = (x, y) \in \mathbb{R}^2$ and $\xi = (\xi_1, \xi_2) \in \mathbb{R}^2$,
$$\langle \nabla^2 f(z)\xi, \xi \rangle = \xi_1^2 + 2\xi_2^2 + 3(x + y)^2(\xi_1 + \xi_2)^2 \ge \xi_1^2 + \xi_2^2 = \|\xi\|^2,$$
so $\nabla^2 f(z) \succeq I_2$ everywhere on $\mathbb{R}^2$ (with equality when $x + y = 0$ and $\xi = (1, 0)$, so $\mu = 1$ is sharp). Integrating along line segments yields $1$-strong convexity of $f$ and $1$-strong monotonicity of $\nabla f$: for all $z, w \in \mathbb{R}^2$,
$$f(w) \ge f(z) + \langle \nabla f(z),\, w - z \rangle + \frac{1}{2}\|w - z\|^2, \qquad \langle \nabla f(z) - \nabla f(w),\, z - w \rangle \ge \|z - w\|^2.$$

Equilibria of $\dot{z} = -\nabla f(z)$ satisfy $\nabla f(z) = 0$. Clearly $\nabla f(0, 0) = (0, 0)$ and $f(0, 0) = 0$. Since
$$\langle \nabla f(z), z \rangle = x^2 + 2y^2 + (x + y)^4 \ge \|z\|^2,$$
$\nabla f(z) = 0$ forces $z = z^* := (0, 0)$ (equivalently, $x + (x+y)^3 = 0 = 2y + (x+y)^3$ implies $x = 2y$ and $y(2 + 27y^2) = 0$). Thus $z^* = (0, 0)$ is the unique equilibrium of the ODE and the unique global minimizer of $f$, with $\min_{\mathbb{R}^2} f = f(0, 0) = 0$.

#### Forward global well-posedness
Because $-\nabla f \in C^\infty(\mathbb{R}^2; \mathbb{R}^2)$ is locally Lipschitz (though superlinear, so backward-in-time trajectories can blow up in finite negative time), the Picard–Lindelöf theorem provides for each initial state $z \in \mathbb{R}^2$ a unique maximal solution $t \mapsto \Phi_t(z)$ of $\dot{z}(t) = -\nabla f(z(t))$, $z(0) = z$, on an open interval $(t_-(z), T_+(z))$ with $0 < T_+(z) \le +\infty$.

For $t \in [0, T_+(z))$, let $z(t) = \Phi_t(z)$. Differentiating $f(z(t))$ gives
$$\frac{d}{dt} f(z(t)) = \langle \nabla f(z(t)), \dot{z}(t) \rangle = -\|\nabla f(z(t))\|^2 \le 0,$$
so $f(z(t)) \le f(z)$ for all $t \in [0, T_+(z))$. Since $f(x, y) \ge \frac{1}{2}(x^2 + 2y^2) \ge \frac{1}{2}\|z\|^2$, the forward trajectory remains inside the compact sublevel set $\{ u \in \mathbb{R}^2 : f(u) \le f(z) \} \subset \overline{B}_{\sqrt{2f(z)}}(0)$. By the standard continuation criterion for autonomous ODEs (finite-time blow-up requires escaping every compact set), $T_+(z) = +\infty$ for every $z \in \mathbb{R}^2$. Smooth dependence on initial data ensures $(t, z) \mapsto \Phi_t(z)$ is $C^\infty$ on $[0, \infty) \times \mathbb{R}^2$, continuous (in fact globally Lipschitz, shown next) in $z$, and satisfies the autonomous semigroup law $\Phi_0 = \operatorname{Id}$ and $\Phi_{t+s} = \Phi_t \circ \Phi_s$ for all $t, s \ge 0$.

#### Exponential contractivity
Fix $z, w \in \mathbb{R}^2$ and set $\Delta(t) := \Phi_t(z) - \Phi_t(w)$ for $t \ge 0$. Using $1$-strong monotonicity of $\nabla f$,
$$\frac{d}{dt}\left(\frac{1}{2}\|\Delta(t)\|^2\right) = -\big\langle \nabla f(\Phi_t(z)) - \nabla f(\Phi_t(w)),\, \Delta(t) \big\rangle \le -\|\Delta(t)\|^2.$$
Hence $\frac{d}{dt}\big(e^{2t}\|\Delta(t)\|^2\big) = e^{2t}\big(2\|\Delta(t)\|^2 + \frac{d}{dt}\|\Delta(t)\|^2\big) \le 0$. Integrating over $[0, t]$ and taking square roots yields
$$\|\Phi_t(z) - \Phi_t(w)\| \le e^{-t}\|z - w\| \qquad \forall t \ge 0,\; \forall z, w \in \mathbb{R}^2.$$

#### Exponential energy dissipation
Evaluating the $1$-strong convexity inequality between $z$ and $w = 0$ gives
$$0 = f(0) \ge f(z) - \langle \nabla f(z), z \rangle + \frac{1}{2}\|z\|^2 = f(z) - \frac{1}{2}\|\nabla f(z)\|^2 + \frac{1}{2}\|z - \nabla f(z)\|^2 \ge f(z) - \frac{1}{2}\|\nabla f(z)\|^2,$$
which is the global Polyak–Łojasiewicz inequality $\|\nabla f(z)\|^2 \ge 2f(z)$ for all $z \in \mathbb{R}^2$. Along $z(t) = \Phi_t(z)$,
$$\frac{d}{dt} f(z(t)) = -\|\nabla f(z(t))\|^2 \le -2 f(z(t)) \implies \frac{d}{dt}\big(e^{2t} f(z(t))\big) \le 0 \qquad \forall t \ge 0.$$
Integrating from $0$ to $t$ establishes
$$f(\Phi_t(z)) \le e^{-2t} f(z) \qquad \forall t \ge 0,\; \forall z \in \mathbb{R}^2.$$

#### Quantitative convergence for an $n$-block stack
For configurable $\tau > 0$ and $T_\tau = \Phi_\tau$, the semigroup property implies that an $n$-layer stack realizes the exact time-$n\tau$ state $Z_n = T_\tau^n(Z_0) = \Phi_{n\tau}(Z_0)$ for every $n \in \mathbb{N}$ and $Z_0 \in \mathbb{R}^2$. Since $T_\tau(0) = \Phi_\tau(0) = 0$, the single-flow bounds immediately imply, for all $Z_0, W_0 \in \mathbb{R}^2$ and $n \ge 0$:
1. **Uniform input-to-state stability:** $\|T_\tau^n(Z_0) - T_\tau^n(W_0)\| \le e^{-n\tau}\|Z_0 - W_0\|$.
2. **Geometric convergence to equilibrium:** $\|Z_n\| = \|Z_n - z^*\| \le e^{-n\tau}\|Z_0\|$, with step residuals $\|Z_{n+1} - Z_n\| \le e^{-n\tau}\|T_\tau(Z_0) - Z_0\|$.
3. **Geometric energy dissipation:** $0 \le f(Z_n) \le e^{-2n\tau} f(Z_0)$ (and $\|Z_n\| \le \sqrt{2f(Z_n)} \le e^{-n\tau}\sqrt{2f(Z_0)}$).
4. **Explicit depth complexity:** Achieving $\|Z_n\| \le \varepsilon$ (for $Z_0 \neq 0$) or $f(Z_n) \le \varepsilon$ (for $f(Z_0) > 0$) for any target tolerance $\varepsilon > 0$ requires at most
   $$n = \left\lceil \frac{1}{\tau}\ln\frac{\|Z_0\|}{\varepsilon} \right\rceil \qquad \text{or} \qquad n = \left\lceil \frac{1}{2\tau}\ln\frac{f(Z_0)}{\varepsilon} \right\rceil$$
   blocks, respectively.

---

### 2. Standard Proximal Certificate and Firm Nonexpansiveness

**Proposition (Proximal Three-Point Certificate, Firm Nonexpansiveness, and Conservative Potential).** *Let $r : \mathbb{R}^2 \to (-\infty, +\infty]$ be proper, lower-semicontinuous (lsc), and convex, and suppose $T : \mathbb{R}^2 \to \mathbb{R}^2$ admits the representation*
$$T(z) = \operatorname{prox}_r(z) := \operatorname{argmin}_u \left\{ r(u) + \frac{1}{2}\|u - z\|^2 \right\}.$$
*Then $T(z) \in \operatorname{dom} r$ is uniquely defined for every $z \in \mathbb{R}^2$, and:*
1. *(Three-point proximal certificate) For every $z \in \mathbb{R}^2$, setting $p = T(z)$, and every $u \in \operatorname{dom} r$,*
   $$r(p) + \frac{1}{2}\|p - z\|^2 + \frac{1}{2}\|u - p\|^2 \le r(u) + \frac{1}{2}\|u - z\|^2.$$
2. *(Firm nonexpansiveness) For all $z, w \in \mathbb{R}^2$,*
   $$\|T(z) - T(w)\|^2 \le \langle T(z) - T(w),\, z - w \rangle,$$
   *equivalently $\|T(z) - T(w)\|^2 + \|(I - T)(z) - (I - T)(w)\|^2 \le \|z - w\|^2$; in particular, $\|T(z) - T(w)\| \le \|z - w\|$.*
3. *(Conservative gradient structure) The function $\psi(z) := \frac{1}{2}\|z\|^2 - r(T(z)) - \frac{1}{2}\|T(z) - z\|^2$ is finite, convex, and differentiable everywhere on $\mathbb{R}^2$ with $\nabla \psi = T$. Consequently, if $T \in C^1(\mathbb{R}^2; \mathbb{R}^2)$, its Jacobian $DT(z) = \nabla^2 \psi(z)$ is symmetric everywhere on $\mathbb{R}^2$.*

*Proof.* Fix $u_0 \in \operatorname{dom} r \neq \emptyset$. Because $r > -\infty$ is lsc and $\overline{B}_1(u_0) \subset \mathbb{R}^2$ is compact, $m := \min_{\|w - u_0\| \le 1} r(w) > -\infty$ is finite. For any $u$ with $\|u - u_0\| > 1$, putting $\lambda = \|u - u_0\|^{-1} \in (0, 1)$ places $(1 - \lambda)u_0 + \lambda u \in \overline{B}_1(u_0)$, so convexity gives $m \le (1 - \lambda)r(u_0) + \lambda r(u)$, i.e., $r(u) \ge r(u_0) - (r(u_0) - m)\|u - u_0\|$. Hence $\phi_z(u) := r(u) + \frac{1}{2}\|u - z\|^2$ is lsc, proper ($\phi_z(u_0) < +\infty$), and coercive ($\phi_z(u) \to +\infty$ as $\|u\| \to \infty$), so $\phi_z$ attains its global minimum at some $p \in \operatorname{dom} r$.

**(1)** Let $p \in \operatorname{dom} r$ minimize $\phi_z$, let $u \in \operatorname{dom} r$, and take $\theta \in (0, 1)$. Set $u_\theta := (1 - \theta)p + \theta u$. By convexity of $r$, $r(u_\theta) \le (1 - \theta)r(p) + \theta r(u)$. Using the exact Euclidean identity
$$\|u_\theta - z\|^2 = \|(1 - \theta)(p - z) + \theta(u - z)\|^2 = (1 - \theta)\|p - z\|^2 + \theta\|u - z\|^2 - \theta(1 - \theta)\|u - p\|^2,$$
optimality $\phi_z(p) \le \phi_z(u_\theta)$ yields
$$r(p) + \frac{1}{2}\|p - z\|^2 \le (1 - \theta)\!\left(r(p) + \frac{1}{2}\|p - z\|^2\right) + \theta\!\left(r(u) + \frac{1}{2}\|u - z\|^2\right) - \frac{\theta(1 - \theta)}{2}\|u - p\|^2.$$
Since $r(p), r(u) \in \mathbb{R}$, subtracting $(1 - \theta)\phi_z(p)$, dividing by $\theta \in (0, 1)$, and letting $\theta \downarrow 0$ gives
$$r(p) + \frac{1}{2}\|p - z\|^2 + \frac{1}{2}\|u - p\|^2 \le r(u) + \frac{1}{2}\|u - z\|^2.$$
(If $\tilde{p}$ is also a minimizer of $\phi_z$, testing with $u = \tilde{p}$ gives $\frac{1}{2}\|\tilde{p} - p\|^2 \le \phi_z(\tilde{p}) - \phi_z(p) = 0$, proving uniqueness of $p = T(z)$.)

**(2)** Given $z, w \in \mathbb{R}^2$, set $p = T(z) \in \operatorname{dom} r$ and $q = T(w) \in \operatorname{dom} r$. Applying (1) at $z$ with $u = q$ and at $w$ with $u = p$ gives
$$r(p) + \frac{1}{2}\|p - z\|^2 + \frac{1}{2}\|q - p\|^2 \le r(q) + \frac{1}{2}\|q - z\|^2,$$
$$r(q) + \frac{1}{2}\|q - w\|^2 + \frac{1}{2}\|p - q\|^2 \le r(p) + \frac{1}{2}\|p - w\|^2.$$
Adding these two inequalities and canceling the finite quantity $r(p) + r(q)$ yields
$$\|p - q\|^2 \le \frac{1}{2}\big(\|q - z\|^2 - \|q - w\|^2\big) + \frac{1}{2}\big(\|p - w\|^2 - \|p - z\|^2\big).$$
Since $\frac{1}{2}(\|q - z\|^2 - \|q - w\|^2) = \frac{1}{2}(\|z\|^2 - \|w\|^2) - \langle q, z - w \rangle$ and $\frac{1}{2}(\|p - w\|^2 - \|p - z\|^2) = \frac{1}{2}(\|w\|^2 - \|z\|^2) + \langle p, z - w \rangle$, the right-hand side simplifies to $\langle p - q, z - w \rangle$, proving $\|T(z) - T(w)\|^2 \le \langle T(z) - T(w), z - w \rangle$. Equivalently,
$$\|(z - w) - (p - q)\|^2 = \|z - w\|^2 - 2\langle p - q, z - w \rangle + \|p - q\|^2 \le \|z - w\|^2 - \|p - q\|^2,$$
and Cauchy–Schwarz gives $\|T(z) - T(w)\| \le \|z - w\|$.

**(3)** Let $M_r(z) := r(T(z)) + \frac{1}{2}\|T(z) - z\|^2 \in \mathbb{R}$ and $\psi(z) := \frac{1}{2}\|z\|^2 - M_r(z)$. Before adding the two inequalities in (2), substituting $r(q) = M_r(w) - \frac{1}{2}\|q - w\|^2$ into the first inequality and expressing $M_r$ via $\psi$ gives
$$\psi(w) - \psi(z) \le \left(\frac{1}{2}\|w\|^2 - \frac{1}{2}\|q - w\|^2\right) - \left(\frac{1}{2}\|z\|^2 - \frac{1}{2}\|q - z\|^2\right) - \frac{1}{2}\|q - p\|^2 = \langle q,\, w - z \rangle - \frac{1}{2}\|q - p\|^2.$$
Swapping $z$ and $w$ gives $\psi(w) - \psi(z) \ge \langle p,\, w - z \rangle + \frac{1}{2}\|q - p\|^2$. Because $\|q - p\| \le \|w - z\|$ by (2),
$$0 \le \frac{1}{2}\|T(w) - T(z)\|^2 \le \psi(w) - \psi(z) - \langle T(z),\, w - z \rangle \le \langle T(w) - T(z),\, w - z \rangle \le \|w - z\|^2 = o(\|w - z\|)$$
as $w \to z$. Hence $\psi$ is convex and Fréchet differentiable everywhere with $\nabla \psi = T$. When $T \in C^1$, $\psi \in C^2$ and equality of mixed partials yields $DT(z) = \nabla^2 \psi(z) = DT(z)^\top$. $\blacksquare$

---

### 3. Non-Existence of a Convex Proximal Representation for Every $\tau > 0$

**Theorem (Failure of Proximal Representability and Firm Nonexpansiveness of $T_\tau = \Phi_\tau$).** *For every $\tau > 0$, the exact continuous-flow map $T_\tau = \Phi_\tau$ satisfies:*
1. *$D\Phi_\tau(z_0)^\top \neq D\Phi_\tau(z_0)$ at the fixed bounded point $z_0 = \frac{1}{\sqrt{2}}(1, 1)$ (so $\Phi_\tau$ is not conservative even locally);*
2. *$\Phi_\tau$ is not globally firmly nonexpansive on $\mathbb{R}^2$.*

*By either (1) or (2) together with the Proposition in Section A.2, for every $\tau > 0$ there exists **no** proper lower-semicontinuous convex function $r_\tau : \mathbb{R}^2 \to (-\infty, +\infty]$ such that $T_\tau = \operatorname{prox}_{r_\tau}$.*

*Proof.* Introduce the orthogonal involution $Q = \frac{1}{\sqrt{2}}\begin{pmatrix} 1 & 1 \\ 1 & -1 \end{pmatrix}$ ($Q^\top = Q = Q^{-1}$), and write $(u, v)^\top = Qz$. In $(u, v)$ coordinates, $\tilde{f}(u, v) = f(Q^\top(u, v)^\top) = \frac{3}{4}u^2 - \frac{1}{2}uv + \frac{3}{4}v^2 + u^4$, and $\tilde{\Phi}_t := Q\Phi_t Q^\top$ is the exact flow of
$$\dot{u} = -\frac{3}{2}u + \frac{1}{2}v - 4u^3, \qquad \dot{v} = \frac{1}{2}u - \frac{3}{2}v.$$
Because $Q$ is orthogonal, symmetry of $D\Phi_\tau(z)$ and firm nonexpansiveness of $\Phi_\tau$ are equivalent to symmetry of $J(\tau) := D\tilde{\Phi}_\tau(u_0, v_0) = Q D\Phi_\tau(z) Q^\top$ and firm nonexpansiveness of $\tilde{\Phi}_\tau$. Along any trajectory $(u(t), v(t))$, $J(t) = (j_{kl}(t))_{1 \le k, l \le 2}$ solves the variational equation $\dot{J}(t) = -H(t)J(t)$, $J(0) = I_2$, with
$$H(t) = \nabla^2 \tilde{f}(u(t), v(t)) = \begin{pmatrix} a(t) & -\frac{1}{2} \\ -\frac{1}{2} & \frac{3}{2} \end{pmatrix}, \qquad a(t) := \frac{3}{2} + 12u(t)^2.$$

**Step 1 (Trajectory cone and two-sided decay for $(u(0), v(0)) = (R, 0)$, $R > 0$).** Fix any $R > 0$ and take $(u(0), v(0)) = (R, 0)$ (corresponding to $z_R = \frac{R}{\sqrt{2}}(1, 1)$). Since $u(0) = R > 0$, $v(0) = 0$, and $\dot{v}(0) = \frac{1}{2}R > 0$, we have $0 < v(t) < 3u(t)$ for small $t > 0$. Because $(0, 0)$ is an equilibrium, $(u(t), v(t)) \neq (0, 0)$ for all $t \ge 0$; at any hypothetical first positive zero of $u$ or $v$, either $u = 0, v > 0 \implies \dot{u} = \frac{1}{2}v > 0$ or $v = 0, u > 0 \implies \dot{v} = \frac{1}{2}u > 0$, both impossible. Thus $u(t) > 0$ and $v(t) > 0$ for all $t > 0$.

Consequently, $\dot{u} > -\frac{3}{2}u - 4u^3$, so $\frac{d}{dt}(e^{-3t}u(t)^{-2}) = -2e^{-3t}u^{-3}(\dot{u} + \frac{3}{2}u) < 8e^{-3t} \le 8$, giving $u(t)^2 \ge \frac{e^{-3t}}{R^{-2} + 8t}$ for all $t \ge 0$. Next, suppose $t_1 := \inf\{ t > 0 : v(t) \ge 3u(t) \} < \infty$. Then $t_1 > 0$, $v(t_1) = 3u(t_1)$, $\frac{d}{dt}(3u - v)\big|_{t=t_1} \le 0$, and $v(s) \le 3u(s)$ on $[0, t_1]$. On $[0, t_1]$, $\dot{u}(s) = -\frac{3}{2}u(s) + \frac{1}{2}v(s) - 4u(s)^3 \le -4u(s)^3$, whence $\frac{d}{ds}(u(s)^{-2}) \ge 8$ and $u(s) \le (R^{-2} + 8s)^{-1/2} < (8s)^{-1/2}$ for $s \in (0, t_1]$. If $t_1 \ge \frac{1}{2}$, then $u(t_1) < (4)^{-1/2} = \frac{1}{2}$; if $0 < t_1 < \frac{1}{2}$, integrating $\dot{v}(s) < \frac{1}{2}(8s)^{-1/2}$ from $0$ to $t_1$ gives $3u(t_1) = v(t_1) < \frac{\sqrt{t_1}}{2\sqrt{2}} < \frac{1}{4}$, so again $u(t_1) < \frac{1}{2}$. Yet at $v(t_1) = 3u(t_1)$ with $0 < u(t_1) < \frac{1}{2}$,
$$\frac{d}{dt}(3u - v)\Big|_{t=t_1} = 3(-4u(t_1)^3) - (-4u(t_1)) = 4u(t_1)\big(1 - 3u(t_1)^2\big) > u(t_1) > 0,$$
a contradiction. Therefore $t_1 = +\infty$, and for all $R > 0$ and all $t > 0$:
$$0 < v(t) < 3u(t), \qquad \dot{u}(t) < -4u(t)^3 < 0, \qquad \frac{e^{-3t}}{R^{-2} + 8t} \le u(t)^2 \le \frac{1}{R^{-2} + 8t}.$$

**Step 2 (Strict positivity of $J(t)$).** Each column $X(t) = (x_1(t), x_2(t))^\top$ of $J(t)$ solves $\dot{x}_1 = -a(t)x_1 + \frac{1}{2}x_2$, $\dot{x}_2 = \frac{1}{2}x_1 - \frac{3}{2}x_2$. For $(x_1(0), x_2(0)) = (1, 0)$ we have $\dot{x}_2(0) = \frac{1}{2} > 0$, and for $(0, 1)$ we have $\dot{x}_1(0) = \frac{1}{2} > 0$; since $(0,0)$ cannot be reached by uniqueness and $\dot{x}_1 = \frac{1}{2}x_2 > 0$ when $x_1 = 0, x_2 > 0$ (likewise for $x_2 = 0$), all four entries $j_{11}(t), j_{12}(t), j_{21}(t), j_{22}(t)$ are strictly positive for all $t > 0$.

**Step 3 (Proof of (1): Non-symmetry at $R = 1$ for all $\tau > 0$).** Set $R = 1$ ($z_0 = \frac{1}{\sqrt{2}}(1, 1)$), $y_1(t) := j_{21}(t)$, and $y_2(t) := j_{12}(t)$. Eliminating $j_{11} = 2\dot{y}_1 + 3y_1$ from $\dot{j}_{11} = -a(t)j_{11} + \frac{1}{2}y_1$ and $j_{22} = 2\dot{y}_2 + 2a(t)y_2$ from $\dot{j}_{22} = \frac{1}{2}y_2 - \frac{3}{2}j_{22}$ yields
$$\ddot{y}_1 + \left(\frac{3}{2} + a(t)\right)\dot{y}_1 + \left(\frac{3}{2}a(t) - \frac{1}{4}\right)y_1 = 0, \qquad y_1(0) = 0,\; \dot{y}_1(0) = \frac{1}{2},$$
$$\ddot{y}_2 + \left(\frac{3}{2} + a(t)\right)\dot{y}_2 + \left(\frac{3}{2}a(t) - \frac{1}{4} + \dot{a}(t)\right)y_2 = 0, \qquad y_2(0) = 0,\; \dot{y}_2(0) = \frac{1}{2}.$$
With $P(t) := \exp\!\big(\int_0^t (\frac{3}{2} + a(s))\,ds\big) > 0$, the Wronskian $W = y_1\dot{y}_2 - \dot{y}_1 y_2$ satisfies $\frac{d}{dt}(P(t)W(t)) = -\dot{a}(t)P(t)y_1(t)y_2(t)$ and $W(0) = 0$. By Steps 1–2, $\dot{a}(s) = 24u(s)\dot{u}(s) < 0$ and $y_1(s), y_2(s) > 0$ for all $s > 0$, so
$$P(t)\big(y_1(t)\dot{y}_2(t) - \dot{y}_1(t)y_2(t)\big) = -\int_0^t \dot{a}(s)P(s)y_1(s)y_2(s)\,ds > 0 \implies \frac{d}{dt}\left(\frac{y_2(t)}{y_1(t)}\right) > 0 \qquad \forall t > 0.$$
Since $\lim_{t \downarrow 0} \frac{y_2(t)}{y_1(t)} = \frac{\dot{y}_2(0)}{\dot{y}_1(0)} = 1$, we obtain $j_{12}(\tau) > j_{21}(\tau) > 0$, hence $D\Phi_\tau(z_0)^\top \neq D\Phi_\tau(z_0)$, for every $\tau > 0$.

**Step 4 (Proof of (2): Failure of firm nonexpansiveness for all $\tau > 0$).** Fix any $\tau > 0$ and let $R \to \infty$ in Step 1. Because $j_{12} > 0$, $\dot{j}_{22} = \frac{1}{2}j_{12} - \frac{3}{2}j_{22} \ge -\frac{3}{2}j_{22}$ with $j_{22}(0) = 1$ gives $j_{22}(t) \ge e^{-3t/2}$. On $[\tau/2, \tau]$, Step 1 gives $u(t)^2 < (4\tau)^{-1}$, so $a(t) < \frac{3}{2} + \frac{3}{\tau} =: \kappa_\tau$ and $\dot{j}_{12}(t) + \kappa_\tau j_{12}(t) \ge \frac{1}{2}e^{-3\tau/2}$. Since $j_{12}(\tau/2) > 0$, integrating over $[\tau/2, \tau]$ yields the $R$-independent positive lower bound
$$j_{12}(\tau) \ge \frac{e^{-3\tau/2}}{2\kappa_\tau}\big(1 - e^{-\kappa_\tau\tau/2}\big) =: c(\tau) > 0 \qquad \forall R > 0.$$
Conversely, for column 1, contractivity from Section A.1 implies $\|D\tilde{\Phi}_s\| \le e^{-s} \le 1$. Given any $\varepsilon > 0$, choose $\eta \in (0, \tau)$ with $\frac{\eta}{2} + \frac{\eta^2}{4} < \frac{\varepsilon}{2}$. On $[0, \eta]$, $0 < j_{11}(s) \le 1$ implies $\dot{j}_{21}(s) \le \frac{1}{2}j_{11}(s) \le \frac{1}{2}$, so $0 \le j_{21}(s) \le \frac{\eta}{2}$. Then $\dot{j}_{11}(s) + 12u(s)^2 j_{11}(s) \le \frac{1}{2}j_{21}(s) \le \frac{\eta}{4}$, and integrating with $A(s) := \int_0^s 12u(r)^2\,dr$ (increasing in $s$) gives $j_{11}(\eta) \le e^{-A(\eta)} + \frac{\eta^2}{4}$. By Step 1, $A(\eta) \ge \int_0^\eta \frac{12e^{-3\eta}}{R^{-2} + 8r}\,dr = \frac{3}{2}e^{-3\eta}\ln(1 + 8R^2\eta) \to +\infty$ as $R \to \infty$; hence for large $R$, $e^{-A(\eta)} < \frac{\varepsilon}{2}$, and the chain rule for $\tilde{\Phi}_\tau = \tilde{\Phi}_{\tau - \eta} \circ \tilde{\Phi}_\eta$ gives
$$\sqrt{j_{11}(\tau)^2 + j_{21}(\tau)^2} = \|J(\tau)e_1\| \le \|D\tilde{\Phi}_{\tau - \eta}\| \|J(\eta)e_1\| \le j_{11}(\eta) + j_{21}(\eta) < \varepsilon.$$
Thus $\lim_{R \to \infty} j_{11}(\tau) = \lim_{R \to \infty} j_{21}(\tau) = 0$ while $\|J(\tau)\| \le 1$ and $j_{12}(\tau) \ge c(\tau) > 0$. Forming $\widetilde{M}_\tau(R) := \frac{J(\tau) + J(\tau)^\top}{2} - J(\tau)^\top J(\tau)$, we have $(\widetilde{M}_\tau)_{11} \to 0$, $|(\widetilde{M}_\tau)_{22}| \le 2$, and $\liminf_{R \to \infty} (\widetilde{M}_\tau)_{12} \ge \frac{1}{2}c(\tau) > 0$, so
$$\limsup_{R \to \infty} \det \widetilde{M}_\tau(R) \le -\frac{c(\tau)^2}{4} < 0.$$
For sufficiently large $R$, choosing an eigenvector $\xi \in \mathbb{R}^2 \setminus \{0\}$ of $Q^\top \widetilde{M}_\tau(R) Q$ with negative eigenvalue gives $\langle D\Phi_\tau(z_R)\xi, \xi \rangle < \|D\Phi_\tau(z_R)\xi\|^2$. By Taylor's theorem, for small $\delta > 0$, $w_R := z_R + \delta\xi$ satisfies $\langle \Phi_\tau(w_R) - \Phi_\tau(z_R),\, w_R - z_R \rangle < \|\Phi_\tau(w_R) - \Phi_\tau(z_R)\|^2$, violating firm nonexpansiveness. $\blacksquare$

*Remark (Origin of the misconception).* A single **implicit-Euler** step $(I + \tau\nabla f)^{-1}(z) = \operatorname{argmin}_u \{ \tau f(u) + \frac{1}{2}\|u - z\|^2 \} = \operatorname{prox}_{\tau f}(z)$ *is* an exact convex proximal map, and by the exponential formula $\Phi_\tau(z) = \lim_{m \to \infty} (\operatorname{prox}_{(\tau/m)f})^m(z)$. While contractivity and Lyapunov decay survive composition and the continuous-time limit, proximal representability and firm nonexpansiveness are not preserved under composing nonlinear maps in $\mathbb{R}^2$ whose Hessians $\nabla^2 f(\Phi_t(z))$ fail to commute along trajectories.

---

## 3. Methods-Section Deployment Description

> **Autonomous Continuous-Flow Denoising Block.** Each denoising layer implements the exact time-$\tau$ flow map $T_\tau = \Phi_\tau : \mathbb{R}^2 \to \mathbb{R}^2$ of the autonomous gradient system $\dot{z} = -\nabla f(z)$ for the $1$-strongly convex energy $f(x, y) = \frac{1}{2}(x^2 + 2y^2) + \frac{1}{4}(x + y)^4$, evaluated by numerical ODE integration over $[0, \tau]$ without requiring a closed-form trajectory. Because $f$ is smooth, coercive, and $1$-strongly convex with unique global minimizer $z^* = (0, 0)$ ($f(0, 0) = 0$), the forward flow is globally well-posed on $[0, \infty)$, and each block $T_\tau$ ($\tau > 0$) is a smooth global strict contraction satisfying $\|T_\tau(z) - T_\tau(w)\| \le e^{-\tau}\|z - w\|$ and the strict Lyapunov dissipation bound $f(T_\tau(z)) \le e^{-2\tau}f(z)$. By the autonomous semigroup property ($\Phi_t \circ \Phi_s = \Phi_{t+s}$), stacking $n$ identical blocks yields the exact time-$n\tau$ state $Z_n = T_\tau^n(Z_0) = \Phi_{n\tau}(Z_0)$ free of time-discretization drift, guaranteeing uniform input-to-state stability $\|T_\tau^n(Z_0) - T_\tau^n(W_0)\| \le e^{-n\tau}\|Z_0 - W_0\|$, geometric state convergence $\|Z_n\| \le e^{-n\tau}\|Z_0\|$ to $z^* = (0, 0)$, and exponential energy decay $f(Z_n) \le e^{-2n\tau}f(Z_0)$. Crucially, unlike an implicit-Euler discretization step $(I + \tau\nabla f)^{-1}(z) = \operatorname{prox}_{\tau f}(z)$, the exact continuous-flow block $T_\tau = \Phi_\tau$ is **not** a convex proximal operator: under our convention $\operatorname{prox}_r(z) = \operatorname{argmin}_u \{ r(u) + \frac{1}{2}\|u - z\|^2 \}$, the quadratic proximity term carries a fixed coefficient $\frac{1}{2}$ (so a step size $\tau$ enters an implicit-Euler step algebraically by scaling the regularizer $r = \tau f$), whereas in $T_\tau = \Phi_\tau$ the parameter $\tau > 0$ is the continuous integration horizon in $T_\tau(z) = z - \int_0^\tau \nabla f(\Phi_t(z))\,dt$. Because the state-dependent Hessians $\nabla^2 f(\Phi_t(z))$ do not commute along generic trajectories, $T_\tau$ has a non-symmetric Jacobian and is not globally firmly nonexpansive for any $\tau > 0$, so $T_\tau \neq \operatorname{prox}_{r_\tau}$ for every proper lower-semicontinuous convex $r_\tau$ (agreeing with $\operatorname{prox}_{\tau f}$ only to first order as $\tau \downarrow 0$).
