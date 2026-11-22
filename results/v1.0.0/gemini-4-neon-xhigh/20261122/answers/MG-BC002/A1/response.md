### Important Correction to the Draft Design Rationale

Before giving the appendix and deployment text, note that the central claim in the current draft rationale is **mathematically false for every $\tau > 0$**:

> *Draft claim:* “The vector field is the gradient of a strongly convex energy, and its evolution is contractive and dissipative. Thus, for every $\tau>0$, the exact block has a convex proximal representation $T_\tau = \mathrm{prox}_{r_\tau}$ for some proper lower-semicontinuous convex $r_\tau$.”

For $f(x,y) = \frac{1}{2}(x^2 + 2y^2) + \frac{1}{4}(x+y)^4$, the exact continuous-flow map $T_\tau = \Phi_\tau$ **does not admit** a proximal representation $T_\tau = \mathrm{prox}_{r_\tau}$ for **any** $\tau > 0$ and **any** proper lower-semicontinuous convex $r_\tau$—indeed, not even for any proper nonconvex $r_\tau$, nor even locally on any neighborhood of the origin. Specifically, in Section 2.3 below we prove two independent obstructions for **every** $\tau > 0$:

1. **Failure of Jacobian symmetry (non-gradient / non-proximal structure, even locally near $0$):** Every continuous single-valued proximal operator $T = \mathrm{prox}_r$ (for any proper $r$) is the gradient of a convex potential $\psi$, so if $T$ is $C^1$ then $DT(z)$ must be symmetric everywhere. For $T_\tau = \Phi_\tau$, however,
   $$\left.\frac{\partial^2}{\partial x^2}\!\left(\frac{\partial (\Phi_\tau)_1}{\partial y} - \frac{\partial (\Phi_\tau)_2}{\partial x}\right)\right|_{(0,0)} = -2e^{-\tau}(1 - e^{-\tau})^3 < 0 \qquad \forall\,\tau > 0.$$
2. **Failure of global monotonicity and firm nonexpansiveness:** Every convex proximal operator $\mathrm{prox}_r$ is firmly nonexpansive and hence monotone ($\langle T(w)-T(z), w-z\rangle \ge 0$). For every $\tau > 0$, $T_\tau = \Phi_\tau$ violates monotonicity—and therefore violates firm nonexpansiveness—at sufficiently large states in the $(1,1)$ direction.

By contrast, all of the gradient-flow, contraction, energy-dissipation, and semigroup guarantees in Section 1 hold exactly. The appendix and deployment paragraph below reflect this rigorously.

---

## Mathematical Appendix

### 1. Forward Global Well-Posedness, Equilibrium, Contraction, Energy Decay, and Stack Convergence

#### 1.1. Strong convexity of $f$ and unique equilibrium

For $z = (x,y) \in \mathbb{R}^2$,
$$f(x,y) = \frac{1}{2}(x^2 + 2y^2) + \frac{1}{4}(x+y)^4$$
is a polynomial and hence $f \in C^\infty(\mathbb{R}^2)$. Its gradient and Hessian are
$$\nabla f(x,y) = \begin{pmatrix} x + (x+y)^3 \\ 2y + (x+y)^3 \end{pmatrix}, \qquad \nabla^2 f(x,y) = \begin{pmatrix} 1 & 0 \\ 0 & 2 \end{pmatrix} + 3(x+y)^2 \begin{pmatrix} 1 & 1 \\ 1 & 1 \end{pmatrix}.$$

For every $z = (x,y) \in \mathbb{R}^2$ and every $v = (v_1, v_2) \in \mathbb{R}^2$,
$$\langle v, \nabla^2 f(z) v\rangle = v_1^2 + 2v_2^2 + 3(x+y)^2(v_1 + v_2)^2 \ge v_1^2 + v_2^2 = \|v\|^2,$$
with equality at $z = (0,0)$ along $v = (1,0)$. Hence $\nabla^2 f(z) \succeq I$ everywhere, so $f$ is **$1$-strongly convex** (sharply, with modulus $\mu = 1$). By Taylor's theorem with integral remainder, for all $u, v \in \mathbb{R}^2$,
$$f(v) \ge f(u) + \langle \nabla f(u), v - u\rangle + \frac{1}{2}\|v - u\|^2, \tag{1.1}$$
and by the fundamental theorem of calculus applied to $s \mapsto \nabla f(w + s(z-w))$, $\nabla f$ is **$1$-strongly monotone**:
$$\langle \nabla f(z) - \nabla f(w), z - w\rangle = \int_0^1 \langle z-w, \nabla^2 f(w + s(z-w))(z-w)\rangle\, ds \ge \|z-w\|^2 \qquad \forall\,z,w\in\mathbb{R}^2. \tag{1.2}$$

**Unique equilibrium.** Clearly $\nabla f(0,0) = (0,0)$ and $f(0,0) = 0$. If $\nabla f(z) = 0$, then setting $w = 0$ in (1.2) yields $0 = \langle \nabla f(z) - \nabla f(0), z\rangle \ge \|z\|^2$, so $z = (0,0)$. (Directly: $x + (x+y)^3 = 2y + (x+y)^3 = 0 \implies x = 2y \implies 2y + 27y^3 = y(2 + 27y^2) = 0 \implies y = x = 0$.) Moreover,
$$f(z) = \frac{1}{2}x^2 + y^2 + \frac{1}{4}(x+y)^4 \ge \frac{1}{2}\|z\|^2 \ge 0, \tag{1.3}$$
so $z^* = (0,0)$ is the **unique equilibrium** of $\dot{z} = -\nabla f(z)$ and the **unique global minimizer** of $f$.

---

#### 1.2. Forward global well-posedness and semigroup property

Consider the autonomous initial-value problem
$$\dot{z}(t) = -\nabla f(z(t)), \qquad z(0) = z_0 \in \mathbb{R}^2. \tag{1.4}$$

1. **Local existence and uniqueness:** Since $-\nabla f \in C^\infty(\mathbb{R}^2)$ is locally Lipschitz on $\mathbb{R}^2$, the Picard–Lindelöf theorem guarantees, for every $z_0 \in \mathbb{R}^2$, a unique maximal $C^\infty$ solution $z : (T_{\min}(z_0), T_{\max}(z_0)) \to \mathbb{R}^2$ with $T_{\min}(z_0) < 0 < T_{\max}(z_0) \le +\infty$.
2. **Forward completeness ($T_{\max}(z_0) = +\infty$):** For all $t \in [0, T_{\max}(z_0))$, using (1.2) with $w = 0$ and $\nabla f(0) = 0$,
   $$\frac{d}{dt}\!\left(\frac{1}{2}\|z(t)\|^2\right) = -\langle z(t), \nabla f(z(t))\rangle \le -\|z(t)\|^2 \le 0.$$
   Hence $\|z(t)\| \le \|z_0\|$ for all $t \in [0, T_{\max}(z_0))$, so the forward trajectory remains inside the compact closed ball $\overline{B}(0, \|z_0\|)$. By the standard escape-from-compact-sets (continuation) theorem for ODEs, $T_{\max}(z_0) = +\infty$. (Global existence is specifically *forward* in time: in backward time $s = -t$, the cubic term in $+\nabla f$ causes finite-time blow-up, e.g., along initial states with $x_0 = y_0 > 0$.)
3. **Smoothness and semigroup property:** Therefore the forward flow $\Phi : [0,\infty) \times \mathbb{R}^2 \to \mathbb{R}^2$, $(t, z_0) \mapsto \Phi_t(z_0)$, is globally defined. By smooth dependence of ODE solutions on initial data, $\Phi \in C^\infty([0,\infty) \times \mathbb{R}^2)$ (in particular, $\Phi_t \in C^\infty(\mathbb{R}^2)$ for every $t \ge 0$). Because (1.4) is autonomous and solutions are unique,
   $$\Phi_0 = \mathrm{Id}, \qquad \Phi_{t+s} = \Phi_t \circ \Phi_s \qquad \forall\,t, s \ge 0.$$
   Continuous dependence on initial data is quantified globally by the contraction estimate below.

---

#### 1.3. Global contraction bound

Fix $z, w \in \mathbb{R}^2$ and write $z(t) = \Phi_t(z)$, $w(t) = \Phi_t(w)$. Define $D(t) := \frac{1}{2}\|z(t) - w(t)\|^2$. By (1.2), for all $t \ge 0$,
$$\dot{D}(t) = \langle z(t) - w(t), \dot{z}(t) - \dot{w}(t)\rangle = -\langle z(t) - w(t), \nabla f(z(t)) - \nabla f(w(t))\rangle \le -\|z(t) - w(t)\|^2 = -2D(t).$$
Multiplying by $e^{2t}$ gives $\frac{d}{dt}(e^{2t} D(t)) = e^{2t}(\dot{D}(t) + 2D(t)) \le 0$. Integrating over $[0, t]$ yields $e^{2t} D(t) \le D(0)$, i.e., $\|z(t) - w(t)\|^2 \le e^{-2t}\|z - w\|^2$, and taking square roots gives
$$\|\Phi_t(z) - \Phi_t(w)\| \le e^{-t}\|z - w\| \qquad \forall\,t \ge 0,\; \forall\,z, w \in \mathbb{R}^2. \tag{1.5}$$
Setting $w = 0$ (since $\Phi_t(0) = 0$) gives $\|\Phi_t(z)\| \le e^{-t}\|z\|$. Moreover, because $D\Phi_t(0) = \mathrm{diag}(e^{-t}, e^{-2t})$, the contraction factor $e^{-t}$ is sharp.

---

#### 1.4. Exponential energy decay

First establish the Polyak–Łojasiewicz (PL) inequality for $f$. Setting $v = 0$ in (1.1) and completing the square gives, for every $u \in \mathbb{R}^2$,
$$0 = f(0) \ge f(u) - \langle \nabla f(u), u\rangle + \frac{1}{2}\|u\|^2 = f(u) + \frac{1}{2}\|u - \nabla f(u)\|^2 - \frac{1}{2}\|\nabla f(u)\|^2 \ge f(u) - \frac{1}{2}\|\nabla f(u)\|^2,$$
and therefore
$$\|\nabla f(u)\|^2 \ge 2 f(u) \qquad \forall\,u \in \mathbb{R}^2. \tag{1.6}$$
Now set $E(t) := f(\Phi_t(z))$. Differentiating along the flow and applying (1.6) yields
$$\dot{E}(t) = \langle \nabla f(\Phi_t(z)), -\nabla f(\Phi_t(z))\rangle = -\|\nabla f(\Phi_t(z))\|^2 \le -2 f(\Phi_t(z)) = -2E(t).$$
Hence $\frac{d}{dt}(e^{2t} E(t)) \le 0$ for all $t \ge 0$. Integrating from $0$ to $t$ yields
$$f(\Phi_t(z)) \le e^{-2t} f(z) \qquad \forall\,t \ge 0,\; \forall\,z \in \mathbb{R}^2. \tag{1.7}$$
In addition, integrating $\dot{E}(s) = -\|\nabla f(\Phi_s(z))\|^2$ gives the exact dissipation identity
$$f(\Phi_t(z)) + \int_0^t \|\nabla f(\Phi_s(z))\|^2\, ds = f(z). \tag{1.8}$$

---

#### 1.5. Quantitative convergence for a stack $Z_n = T_\tau^n(Z_0)$

Fix $\tau > 0$ and let $T_\tau = \Phi_\tau$. By induction using the semigroup law $\Phi_{t+s} = \Phi_t \circ \Phi_s$,
$$Z_n = T_\tau^n(Z_0) = \Phi_\tau^n(Z_0) = \Phi_{n\tau}(Z_0) \qquad \forall\,n \in \mathbb{N}_0.$$
Applying (1.5) and (1.7) at $t = n\tau$ yields the following quantitative guarantees for all $Z_0, W_0 \in \mathbb{R}^2$ and all $n \ge 0$:

- **Strict pairwise contraction / input-perturbation stability:**
  $$\|T_\tau^n(Z_0) - T_\tau^n(W_0)\| \le e^{-n\tau}\|Z_0 - W_0\|.$$
  In particular, $T_\tau$ is a Banach contraction with constant $q_\tau = e^{-\tau} < 1$ and unique fixed point $0$.
- **Geometric convergence to the equilibrium $0$:**
  $$\|Z_n\| \le e^{-n\tau}\|Z_0\|, \qquad \|Z_{n+1} - Z_n\| \le e^{-n\tau}\|Z_1 - Z_0\|, \qquad \|Z_n\| \le \frac{e^{-n\tau}}{1 - e^{-\tau}}\|Z_1 - Z_0\|.$$
  (The last inequality follows by summing $\|Z_n\| \le \sum_{k=n}^\infty \|Z_{k+1} - Z_k\| \le \sum_{k=n}^\infty e^{-k\tau}\|Z_1 - Z_0\|$.)
- **Geometric energy decay:**
  $$f(Z_n) \le e^{-2n\tau} f(Z_0), \qquad \text{with } \frac{1}{2}\|Z_n\|^2 \le f(Z_n).$$
- **Depth / horizon complexity:** To guarantee $\|Z_n\| \le \varepsilon$ (for $\varepsilon > 0$ and $\|Z_0\| > \varepsilon$), it suffices that
  $$n \ge \frac{1}{\tau}\ln\!\left(\frac{\|Z_0\|}{\varepsilon}\right) \quad \Longleftrightarrow \quad n\tau \ge \ln\!\left(\frac{\|Z_0\|}{\varepsilon}\right).$$
  To guarantee $f(Z_n) \le \varepsilon$ (for $f(Z_0) > \varepsilon$), it suffices that
  $$n \ge \frac{1}{2\tau}\ln\!\left(\frac{f(Z_0)}{\varepsilon}\right) \quad \Longleftrightarrow \quad n\tau \ge \frac{1}{2}\ln\!\left(\frac{f(Z_0)}{\varepsilon}\right).$$
  Because $T_\tau^n = \Phi_{n\tau}$, the output and all convergence bounds depend only on the cumulative evolution time $T = n\tau$.

---

### 2. Standard Proximal Certificate, Firm Nonexpansiveness, and Refutation of the Draft Rationale

#### 2.1. Statement and proof of the proximal certificate

Let $r : \mathbb{R}^d \to (-\infty, +\infty]$ (here $d = 2$) be proper ($\mathrm{dom}\,r := \{u \in \mathbb{R}^d : r(u) < +\infty\} \neq \emptyset$ and $r > -\infty$), lower-semicontinuous (l.s.c.), and convex. Recall that for each $z \in \mathbb{R}^d$,
$$\mathrm{prox}_r(z) := \arg\min_{u \in \mathbb{R}^d}\left\{ r(u) + \frac{1}{2}\|u - z\|^2 \right\}.$$
Because $r$ is proper, l.s.c., and convex, it admits a continuous affine minorant $r(u) \ge \langle a, u\rangle + b$, so $g_z(u) := r(u) + \frac{1}{2}\|u - z\|^2$ is proper, l.s.c., coercive ($g_z(u) \to +\infty$ as $\|u\|\to\infty$), and strictly convex; hence $g_z$ attains a unique global minimum at a point $p = \mathrm{prox}_r(z) \in \mathrm{dom}\,r$.

**Proposition 2.1 (Proximal three-point certificate).** *Suppose $T = \mathrm{prox}_r$ with $r : \mathbb{R}^d \to (-\infty,+\infty]$ proper, l.s.c., and convex. Then for every $z \in \mathbb{R}^d$, writing $p = T(z) \in \mathrm{dom}\,r$, we have*
$$r(p) + \frac{1}{2}\|p - z\|^2 + \frac{1}{2}\|u - p\|^2 \le r(u) + \frac{1}{2}\|u - z\|^2 \qquad \forall\,u \in \mathrm{dom}\,r. \tag{2.1}$$

*Proof.* Fix $z \in \mathbb{R}^d$, $p = T(z) \in \mathrm{dom}\,r$, $u \in \mathrm{dom}\,r$, and $\theta \in (0, 1)$. Set $u_\theta := (1-\theta)p + \theta u$. Since $p$ minimizes $g_z$,
$$r(p) + \frac{1}{2}\|p - z\|^2 \le r(u_\theta) + \frac{1}{2}\|u_\theta - z\|^2.$$
By convexity of $r$, $r(u_\theta) \le (1-\theta)r(p) + \theta r(u)$. For the quadratic term, writing $u_\theta - z = (1-\theta)(p-z) + \theta(u-z)$, direct expansion verifies the Euclidean identity
$$\|(1-\theta)(p-z) + \theta(u-z)\|^2 = (1-\theta)\|p-z\|^2 + \theta\|u-z\|^2 - \theta(1-\theta)\|u - p\|^2.$$
Substituting both relations into $g_z(p) \le g_z(u_\theta)$ gives
$$r(p) + \frac{1}{2}\|p-z\|^2 \le (1-\theta)r(p) + \theta r(u) + \frac{1-\theta}{2}\|p-z\|^2 + \frac{\theta}{2}\|u-z\|^2 - \frac{\theta(1-\theta)}{2}\|u-p\|^2.$$
Since $r(p)$ and $r(u)$ are finite, subtracting $(1-\theta)\bigl(r(p) + \frac{1}{2}\|p-z\|^2\bigr)$ from both sides and dividing by $\theta > 0$ yields
$$r(p) + \frac{1}{2}\|p-z\|^2 + \frac{1-\theta}{2}\|u-p\|^2 \le r(u) + \frac{1}{2}\|u-z\|^2.$$
Letting $\theta \downarrow 0$ establishes (2.1). $\square$

*(Remark: Using $\|u-z\|^2 - \|p-z\|^2 - \|u-p\|^2 = 2\langle u-p, p-z\rangle$, (2.1) is algebraically equivalent to the subdifferential optimality condition $r(u) \ge r(p) + \langle z - p, u - p\rangle$ for all $u \in \mathrm{dom}\,r$, i.e., $z - p \in \partial r(p)$.)*

---

#### 2.2. Derivation of firm nonexpansiveness under $T = \mathrm{prox}_r$

**Corollary 2.2 (Firm nonexpansiveness).** *Under the hypotheses of Proposition 2.1, $T = \mathrm{prox}_r$ is firmly nonexpansive:*
$$\|T(z) - T(w)\|^2 \le \langle T(z) - T(w), z - w\rangle \qquad \forall\,z, w \in \mathbb{R}^d. \tag{2.2}$$
*In particular, $T$ is monotone ($\langle T(z) - T(w), z - w\rangle \ge 0$) and nonexpansive ($\|T(z) - T(w)\| \le \|z - w\|$), and equivalently $\|T(z) - T(w)\|^2 + \|(I-T)(z) - (I-T)(w)\|^2 \le \|z - w\|^2$.*

*Proof.* Let $z, w \in \mathbb{R}^d$ and set $p = T(z) \in \mathrm{dom}\,r$ and $q = T(w) \in \mathrm{dom}\,r$. Applying (2.1) at $(z, p)$ with $u = q$ and at $(w, q)$ with $u = p$ gives
$$r(p) + \frac{1}{2}\|p-z\|^2 + \frac{1}{2}\|q-p\|^2 \le r(q) + \frac{1}{2}\|q-z\|^2,$$
$$r(q) + \frac{1}{2}\|q-w\|^2 + \frac{1}{2}\|p-q\|^2 \le r(p) + \frac{1}{2}\|p-w\|^2.$$
Adding these two inequalities and canceling the finite quantity $r(p) + r(q)$ yields
$$\|p-q\|^2 + \frac{1}{2}\bigl(\|p-z\|^2 - \|q-z\|^2 + \|q-w\|^2 - \|p-w\|^2\bigr) \le 0.$$
Expanding the four squared norms,
$$\|p-z\|^2 - \|q-z\|^2 = \|p\|^2 - \|q\|^2 - 2\langle p-q, z\rangle, \qquad \|q-w\|^2 - \|p-w\|^2 = \|q\|^2 - \|p\|^2 + 2\langle p-q, w\rangle,$$
so the parenthesized sum equals $-2\langle p-q, z-w\rangle$. Substituting this back gives
$$\|p - q\|^2 - \langle p - q, z - w\rangle \le 0,$$
which is (2.2). Monotonicity follows from $\|T(z)-T(w)\|^2 \ge 0$, nonexpansiveness follows from Cauchy–Schwarz, and the equivalent form follows by expanding $\|(z-w) - (p-q)\|^2 = \|z-w\|^2 - 2\langle p-q, z-w\rangle + \|p-q\|^2$. $\square$

---

#### 2.3. Why the draft rationale fails: $T_\tau = \Phi_\tau$ is neither a proximal map nor firmly nonexpansive for any $\tau > 0$

We now prove that the actual continuous-flow block $T_\tau = \Phi_\tau$ fails **both** the gradient/symmetry condition required of any proximal operator (even locally near $0$ and even for nonconvex $r_\tau$) **and** the global monotonicity / firm-nonexpansiveness property of Corollary 2.2, for **every** $\tau > 0$.

##### Obstruction 1: Non-symmetric Jacobian (rules out $T_\tau = \mathrm{prox}_{r_\tau}$ for all $\tau > 0$, even locally near $0$ and for arbitrary proper $r_\tau$)

**Lemma 2.3 (Every $C^1$ proximal map has a symmetric Jacobian).** *Let $U \subseteq \mathbb{R}^2$ be open and $r : \mathbb{R}^2 \to (-\infty, +\infty]$ be any proper function (not necessarily convex or l.s.c.). Suppose $T \in C^1(U; \mathbb{R}^2)$ satisfies $T(z) \in \arg\min_{u \in \mathbb{R}^2}\{r(u) + \frac{1}{2}\|u-z\|^2\}$ for every $z \in U$. Then $T = \nabla\psi$ on $U$ for a $C^2$ convex function $\psi$, and hence $DT(z) = DT(z)^\top$ for all $z \in U$.*

*Proof.* Since $r(u) + \frac{1}{2}\|u-z\|^2 = \frac{1}{2}\|z\|^2 - \bigl(\langle z, u\rangle - r(u) - \frac{1}{2}\|u\|^2\bigr)$, the minimizer $T(z)$ maximizes $u \mapsto \langle z, u\rangle - r(u) - \frac{1}{2}\|u\|^2$, and $r(T(z)) \in \mathbb{R}$ is finite for all $z \in U$. Define
$$\psi(z) := \sup_{u \in \mathbb{R}^2}\left\{\langle z, u\rangle - r(u) - \frac{1}{2}\|u\|^2\right\} = \langle z, T(z)\rangle - r(T(z)) - \frac{1}{2}\|T(z)\|^2, \qquad z \in U.$$
For any $z, w \in U$, taking $u = T(z)$ in the supremum defining $\psi(w)$ gives
$$\psi(w) \ge \langle w, T(z)\rangle - r(T(z)) - \frac{1}{2}\|T(z)\|^2 = \psi(z) + \langle T(z), w - z\rangle.$$
Swapping $z$ and $w$ gives $\psi(w) - \psi(z) \le \langle T(w), w - z\rangle$. Combining the two inequalities,
$$0 \le \psi(w) - \psi(z) - \langle T(z), w - z\rangle \le \langle T(w) - T(z), w - z\rangle \le \|T(w) - T(z)\|\,\|w - z\|.$$
Because $T$ is continuous on the open set $U$, dividing by $\|w-z\|$ and letting $w \to z$ proves that $\psi$ is Fréchet differentiable on $U$ with $\nabla \psi = T$. Since $T \in C^1(U)$, $\psi \in C^2(U)$ (and is convex as a pointwise supremum of affine functions), so Clairaut's theorem gives $DT(z) = \nabla^2\psi(z) = DT(z)^\top$ for all $z \in U$. $\square$

*(Equivalently, under convexity of $r$, summing the Proposition 2.1 certificate $r(p_k) + \langle z_k - p_k, p_{k+1} - p_k\rangle \le r(p_{k+1})$ around closed polygons gives cyclical monotonicity and hence $\oint_\gamma \langle T(z), dz\rangle = 0$ on every closed $C^1$ loop, which again forces $\partial_y T_1 = \partial_x T_2$.)*

**Theorem 2.4 (Asymmetry of $D\Phi_\tau$ for every $\tau > 0$).** *Write $\Phi_t(x,y) = (X(t,x,y), Y(t,x,y))$. For every $\tau > 0$,*
$$\left.\frac{\partial^2}{\partial x^2}\!\left(\frac{\partial X}{\partial y} - \frac{\partial Y}{\partial x}\right)\right|_{(\tau,0,0)} = X_{xxy}(\tau,0,0) - Y_{xxx}(\tau,0,0) = -2e^{-\tau}(1 - e^{-\tau})^3 < 0. \tag{2.3}$$
*Consequently, for every $\tau > 0$ and every open neighborhood $U$ of $(0,0)$, $D\Phi_\tau(z)$ fails to be symmetric on $U$; in particular, $T_\tau = \Phi_\tau$ (and likewise every stack $T_\tau^n = \Phi_{n\tau}$, $n \ge 1$) cannot be represented as $\mathrm{prox}_{r_\tau}$ for any proper function $r_\tau$ (convex or nonconvex), globally or even locally on $U$.*

*Proof.* Set $S(t,x,y) := X(t,x,y) + Y(t,x,y)$. The flow solves
$$\partial_t X = -X - S^3, \qquad \partial_t Y = -2Y - S^3, \qquad X(0,x,y) = x,\quad Y(0,x,y) = y.$$
Since $\Phi \in C^\infty([0,\infty)\times\mathbb{R}^2)$, mixed partials in $t, x, y$ commute. Along $(x,y) = (0,0)$, we have $X(t,0,0) = Y(t,0,0) = S(t,0,0) = 0$ for all $t \ge 0$.

1. *First spatial derivatives at $(0,0)$:* Differentiating in $x$ and $y$ and evaluating at $(0,0)$ (where $3S^2 = 0$) gives
   $$\partial_t X_x = -X_x,\; X_x(0)=1 \implies X_x(t,0,0)=e^{-t}; \qquad \partial_t Y_x = -2Y_x,\; Y_x(0)=0 \implies Y_x(t,0,0)=0;$$
   $$\partial_t X_y = -X_y,\; X_y(0)=0 \implies X_y(t,0,0)=0; \qquad \partial_t Y_y = -2Y_y,\; Y_y(0)=1 \implies Y_y(t,0,0)=e^{-2t}.$$
   Hence $S_x(t,0,0) = e^{-t}$ and $S_y(t,0,0) = e^{-2t}$.
2. *Third spatial derivatives at $(0,0)$:* Differentiating $S^3$ three times, every term containing a factor of $S$ vanishes at $(0,0)$:
   $$\left.\partial_x^2\partial_y(S^3)\right|_{(t,0,0)} = 6 S_x^2 S_y = 6 e^{-4t}, \qquad \left.\partial_x^3(S^3)\right|_{(t,0,0)} = 6 S_x^3 = 6 e^{-3t}.$$
   Applying $\partial_x^2\partial_y$ to $\partial_t X = -X - S^3$ and $\partial_x^3$ to $\partial_t Y = -2Y - S^3$ at $(0,0)$ (with zero initial conditions because $X(0,x,y)=x$ and $Y(0,x,y)=y$ are linear) yields:
   - $\partial_t X_{xxy} + X_{xxy} = -6 e^{-4t}$, $X_{xxy}(0,0,0) = 0$, so
     $$e^\tau X_{xxy}(\tau,0,0) = -6\int_0^\tau e^{-3t}\,dt = -2(1 - e^{-3\tau}) \implies X_{xxy}(\tau,0,0) = -2e^{-\tau}(1 - e^{-3\tau});$$
   - $\partial_t Y_{xxx} + 2 Y_{xxx} = -6 e^{-3t}$, $Y_{xxx}(0,0,0) = 0$, so
     $$e^{2\tau} Y_{xxx}(\tau,0,0) = -6\int_0^\tau e^{-t}\,dt = -6(1 - e^{-\tau}) \implies Y_{xxx}(\tau,0,0) = -6e^{-2\tau}(1 - e^{-\tau}).$$
3. *Comparison:* Subtracting gives
   $$\begin{aligned}
   X_{xxy}(\tau,0,0) - Y_{xxx}(\tau,0,0)
   &= -2e^{-\tau}(1 - e^{-3\tau}) + 6e^{-2\tau}(1 - e^{-\tau}) \\
   &= -2e^{-\tau}(1 - e^{-\tau})\bigl[(1 + e^{-\tau} + e^{-2\tau}) - 3e^{-\tau}\bigr] \\
   &= -2e^{-\tau}(1 - e^{-\tau})^3 < 0
   \end{aligned}$$
   for every $\tau > 0$ (since $0 < e^{-\tau} < 1$). If $\partial_y X(\tau,\cdot) = \partial_x Y(\tau,\cdot)$ held on an open neighborhood $U$ of $(0,0)$, differentiating twice in $x$ at $(0,0)$ would force $X_{xxy}(\tau,0,0) = Y_{xxx}(\tau,0,0)$, a contradiction. Applying Lemma 2.3 completes the proof. $\square$

*Geometric mechanism:* Along trajectories, the Hessian $\nabla^2 f(z) = \mathrm{diag}(1,2) + 3(x+y)^2\mathbf{1}\mathbf{1}^\top$ is a time-varying sum of two non-commuting symmetric matrices ($[\mathrm{diag}(1,2), \mathbf{1}\mathbf{1}^\top] \neq 0$). Consequently, the time-ordered exponential solving $\dot{J}(t) = -\nabla^2 f(\Phi_t(z)) J(t)$ develops a nonzero skew-symmetric part (at order $O(\tau^3)$ as $\tau \downarrow 0$ and remaining nonzero for all $\tau > 0$). Note that this also rules out any rescaled proximal representation $\arg\min_u \{\tilde{r}_\tau(u) + \frac{1}{2\gamma}\|u-z\|^2\}$, since that equals $\mathrm{prox}_{\gamma\tilde{r}_\tau}$.

---

##### Obstruction 2: Failure of global monotonicity and firm nonexpansiveness for every $\tau > 0$

Even more directly against Corollary 2.2, $T_\tau = \Phi_\tau$ is not even globally monotone (hence not firmly nonexpansive) on $\mathbb{R}^2$ for any $\tau > 0$.

**Theorem 2.5 (Failure of monotonicity and firm nonexpansiveness for every $\tau > 0$).** *For every $\tau > 0$, there exist $z, w \in \mathbb{R}^2$ such that*
$$\langle \Phi_\tau(w) - \Phi_\tau(z), w - z\rangle < 0 < \|\Phi_\tau(w) - \Phi_\tau(z)\|^2.$$
*In particular, $T_\tau = \Phi_\tau$ is neither monotone nor firmly nonexpansive on $\mathbb{R}^2$ (giving a second, direct contradiction to $T_\tau = \mathrm{prox}_{r_\tau}$ via Corollary 2.2).*

*Proof.* Introduce the orthogonal rotation $Q = \frac{1}{\sqrt{2}}\begin{pmatrix}1 & 1 \\ 1 & -1\end{pmatrix}$ ($Q^\top = Q = Q^{-1}$) and coordinates $(u, v)^\top = Q(x,y)^\top = \bigl(\frac{x+y}{\sqrt{2}}, \frac{x-y}{\sqrt{2}}\bigr)^\top$. Because $Q$ is orthogonal, inner products, norms, and the eigenvalues of $\mathrm{sym}(D\Phi_\tau(z)) := \frac{1}{2}(D\Phi_\tau(z) + D\Phi_\tau(z)^\top)$ are preserved under $\tilde{\Phi}_t := Q\circ\Phi_t\circ Q^\top$. In $(u, v)$ coordinates, $f$ becomes $\tilde{f}(u,v) = \frac{3}{4}u^2 - \frac{1}{2}uv + \frac{3}{4}v^2 + u^4$, so the flow $\dot{z} = -\nabla f(z)$ reads
$$\dot{u} = -4u^3 - \frac{3}{2}u + \frac{1}{2}v, \qquad \dot{v} = \frac{1}{2}u - \frac{3}{2}v.$$

Fix $\tau > 0$ and take initial condition $(u(0), v(0)) = (M, 0)$ with $M > 0$. Write the Jacobian $J(t) := D\tilde{\Phi}_t(M, 0) = \begin{pmatrix} p(t) & \xi(t) \\ q(t) & \eta(t)\end{pmatrix}$, whose columns solve the linear variational system
$$\begin{aligned}
\dot{p} &= -\bigl(12u^2 + \tfrac{3}{2}\bigr)p + \tfrac{1}{2}q, & \dot{q} &= \tfrac{1}{2}p - \tfrac{3}{2}q, & (p(0), q(0)) &= (1, 0), \\
\dot{\xi} &= -\bigl(12u^2 + \tfrac{3}{2}\bigr)\xi + \tfrac{1}{2}\eta, & \dot{\eta} &= \tfrac{1}{2}\xi - \tfrac{3}{2}\eta, & (\xi(0), \eta(0)) &= (0, 1).
\end{aligned}$$

**Step 1 (Positivity).** We claim $u(t), p(t), \eta(t) > 0$ for all $t \ge 0$ and $v(t), q(t), \xi(t) > 0$ for all $t > 0$. For $(u,v)$: since $u(0) = M > 0$, $v(0) = 0$, and $\dot{v}(0) = \frac{1}{2}M > 0$, we have $u(t), v(t) > 0$ for small $t > 0$. If $t_0 := \inf\{t > 0 : u(t) \le 0 \text{ or } v(t) < 0\} < \infty$, then $t_0 > 0$ and $u, v \ge 0$ on $[0, t_0]$ with $u > 0$ on $[0, t_0)$. Setting $A(t) = \int_0^t (4u(s)^2 + \frac{3}{2})\,ds$,
$$e^{3t_0/2}v(t_0) = \frac{1}{2}\int_0^{t_0} e^{3s/2}u(s)\,ds > 0, \qquad e^{A(t_0)}u(t_0) = M + \frac{1}{2}\int_0^{t_0} e^{A(s)}v(s)\,ds \ge M > 0,$$
contradicting the minimality of $t_0$ by continuity. The exact same integrating-factor argument applied to $(p,q)$ and $(\xi,\eta)$ establishes $p(t), \eta(t) > 0$ for all $t \ge 0$, $q(t), \xi(t) > 0$ for all $t > 0$, and additionally
$$\dot{\eta} \ge -\frac{3}{2}\eta \implies \eta(t) \ge e^{-3t/2} \qquad \forall\,t \ge 0. \tag{2.4}$$

**Step 2 ($M$-independent upper bound on $u$ on $[\tau/2, \tau]$ and positive lower bound on $\xi(\tau)$).** Let $V_* := \max_{t \in [0,\tau]} v(t) > 0$ and $C_0 := (V_*/4)^{1/3} > 0$. Whenever $t \in [0,\tau]$ satisfies $u(t) = C_0$,
$$\dot{u}(t) = -4C_0^3 - \frac{3}{2}C_0 + \frac{1}{2}v(t) \le -V_* - \frac{3}{2}C_0 + \frac{1}{2}V_* = -\frac{1}{2}V_* - \frac{3}{2}C_0 < 0.$$
Hence once $u(t_1) \le C_0$ for some $t_1 \in [0,\tau]$, necessarily $u(t) \le C_0$ for all $t \in [t_1, \tau]$. In particular, if $M \le C_0$ then $u(t) \le C_0$ on $[0,\tau]$. If $M > C_0$, let $t_1 := \inf(\{t \in [0,\tau] : u(t) \le C_0\}\cup\{\tau\})$. On $(0, t_1)$, $u(t) > C_0$ implies $2u(t)^3 > 2C_0^3 = \frac{1}{2}V_* \ge \frac{1}{2}v(t)$, so $\dot{u}(t) < -2u(t)^3$ and hence $\frac{d}{dt}(u(t)^{-2}) = -2u(t)^{-3}\dot{u}(t) > 4$. Integrating from $0$ to $t \in (0, t_1]$ gives $u(t)^{-2} > M^{-2} + 4t > 4t$, so $u(t) < \frac{1}{2\sqrt{t}}$, while $u(t) \le C_0$ on $[t_1, \tau]$. In both cases,
$$u(t) \le \frac{1}{2\sqrt{t}} + C_0 \qquad \forall\,t \in (0, \tau].$$
Inserting this into $v(t) = \frac{1}{2}\int_0^t e^{-\frac{3}{2}(t-s)} u(s)\,ds$ yields, for every $t \in [0,\tau]$,
$$v(t) \le \frac{1}{2}\int_0^t \frac{ds}{2\sqrt{s}} + \frac{C_0}{2}\int_0^t e^{-\frac{3}{2}(t-s)}\,ds \le \frac{\sqrt{\tau}}{2} + \frac{C_0}{3} = \frac{\sqrt{\tau}}{2} + \frac{1}{3}\!\left(\frac{V_*}{4}\right)^{\!1/3}.$$
Taking the maximum over $t \in [0,\tau]$ and using $x^{1/3} \le x + 1$ for all $x \ge 0$ gives
$$V_* \le \frac{\sqrt{\tau}}{2} + \frac{1}{3}\!\left(\frac{V_*}{4} + 1\right) \implies \frac{11}{12}V_* \le \frac{\sqrt{\tau}}{2} + \frac{1}{3} \implies V_* \le \frac{6\sqrt{\tau} + 4}{11}.$$
Consequently $C_0 \le \frac{V_*}{4} + 1 < \sqrt{\tau} + 2$, so for every $t \in [\tau/2, \tau]$,
$$u(t) \le \frac{1}{\sqrt{2\tau}} + \sqrt{\tau} + 2 =: U_\tau,$$
independent of $M$. Setting $K_\tau := 12 U_\tau^2 + \frac{3}{2}$, we obtain on $[\tau/2, \tau]$ using (2.4):
$$\dot{\xi}(t) + K_\tau \xi(t) \ge \dot{\xi}(t) + \bigl(12u(t)^2 + \tfrac{3}{2}\bigr)\xi(t) = \frac{1}{2}\eta(t) \ge \frac{1}{2}e^{-3\tau/2}.$$
Multiplying by $e^{K_\tau t}$, integrating over $[\tau/2, \tau]$, and dropping $e^{K_\tau \tau/2}\xi(\tau/2) > 0$ yields the $M$-independent lower bound
$$\xi(\tau) > \frac{e^{-3\tau/2}}{2K_\tau}\bigl(1 - e^{-K_\tau \tau/2}\bigr) =: \alpha_\tau > 0. \tag{2.5}$$

**Step 3 (Decay of $p(\tau) \to 0$ as $M \to \infty$).** Since $v(t) \ge 0$, $\dot{u} \ge -4u^3 - \frac{3}{2}u$, so $w(t) := u(t)^{-2}$ satisfies $\dot{w} = -2u^{-3}\dot{u} \le 8 + 3w$ with $w(0) = M^{-2}$. Thus
$$e^{-3t}w(t) \le M^{-2} + 8\int_0^t e^{-3s}\,ds = M^{-2} + \frac{8}{3}(1 - e^{-3t}) \le M^{-2} + 8t \implies u(t)^2 \ge \frac{e^{-3t}}{M^{-2} + 8t}.$$
Set $\delta := \min\bigl(\tau, \frac{1}{3}\ln\frac{4}{3}\bigr) \in (0, 1)$, so $e^{-3t} \ge \frac{3}{4}$ on $[0, \delta]$. For $0 \le s \le t \le \delta$, let $E(t,s) := \exp\bigl(-\int_s^t (12u(r)^2 + \frac{3}{2})\,dr\bigr) \in (0, 1]$. Then for all $t \in [0, \delta]$,
$$\int_0^t 12u(r)^2\,dr \ge 9\int_0^t \frac{dr}{M^{-2} + 8r} = \frac{9}{8}\ln(1 + 8M^2 t) \implies E(t,0) \le (1 + 8M^2 t)^{-9/8},$$
and hence
$$\int_0^\delta E(t,0)\,dt \le \int_0^\infty (1 + 8M^2 t)^{-9/8}\,dt = \frac{1}{M^2}.$$
Define $S(t) := \int_0^t p(s)\,ds$ on $[0,\delta]$. Since $p, q > 0$ on $(0,\delta]$, $e^{-\frac{3}{2}(t-s)} \le 1$, and $E(t,s) \le 1$,
$$q(t) = \frac{1}{2}\int_0^t e^{-\frac{3}{2}(t-s)} p(s)\,ds \le \frac{1}{2}S(t),$$
$$p(t) = E(t,0) + \frac{1}{2}\int_0^t E(t,s)q(s)\,ds \le E(t,0) + \frac{1}{4}\int_0^t S(s)\,ds \le E(t,0) + \frac{\delta}{4}S(\delta).$$
Integrating $p(t)$ over $[0,\delta]$ and using $\delta^2 < 1$ gives $S(\delta) \le M^{-2} + \frac{1}{4}S(\delta)$, hence $S(\delta) \le \frac{4}{3M^2}$. Therefore
$$q(\delta) \le \frac{2}{3M^2}, \qquad p(\delta) \le (1 + 8M^2\delta)^{-9/8} + \frac{\delta}{3M^2}.$$
By (1.5), $\|D\tilde{\Phi}_s(w)\|_2 = \|D\Phi_s(Q^\top w)\|_2 \le e^{-s} \le 1$ for all $s \ge 0$ and $w \in \mathbb{R}^2$. Using the chain rule on $\tilde{\Phi}_\tau = \tilde{\Phi}_{\tau-\delta}\circ\tilde{\Phi}_\delta$ gives $\binom{p(\tau)}{q(\tau)} = D\tilde{\Phi}_{\tau-\delta}(\tilde{\Phi}_\delta(M,0))\binom{p(\delta)}{q(\delta)}$, so
$$0 < p(\tau) \le \sqrt{p(\tau)^2 + q(\tau)^2} \le e^{-(\tau-\delta)}\sqrt{p(\delta)^2 + q(\delta)^2} \le p(\delta) + q(\delta) \le (1 + 8M^2\delta)^{-9/8} + \frac{\delta + 2}{3M^2} \xrightarrow{M\to\infty} 0. \tag{2.6}$$
By the same operator-norm bound, $0 < \eta(\tau) \le \|D\tilde{\Phi}_\tau(M,0)\|_2 \le e^{-\tau}$.

**Step 4 (Negative eigenvalue of $\mathrm{sym}(D\Phi_\tau(z_0))$).** For $z_0 = Q^\top(M, 0) = \bigl(\frac{M}{\sqrt{2}}, \frac{M}{\sqrt{2}}\bigr)$, combining (2.5) and (2.6) with $q(\tau) > 0$ gives
$$\det\bigl(\mathrm{sym}(D\Phi_\tau(z_0))\bigr) = \det\bigl(\mathrm{sym}(J(\tau))\bigr) = p(\tau)\eta(\tau) - \frac{1}{4}\bigl(\xi(\tau) + q(\tau)\bigr)^2 < e^{-\tau} p(\tau) - \frac{1}{4}\alpha_\tau^2 < 0$$
for $M$ sufficiently large. Thus the real symmetric $2\times 2$ matrix $\mathrm{sym}(D\Phi_\tau(z_0))$ has a strictly negative eigenvalue $\lambda_- < 0$ with unit eigenvector $h \in \mathbb{R}^2$. Setting $w_\varepsilon := z_0 + \varepsilon h$, differentiability of $\Phi_\tau$ at $z_0$ gives
$$\langle \Phi_\tau(w_\varepsilon) - \Phi_\tau(z_0), w_\varepsilon - z_0\rangle = \varepsilon^2 \langle D\Phi_\tau(z_0) h, h\rangle + o(\varepsilon^2) = \varepsilon^2 \lambda_- + o(\varepsilon^2) < 0$$
for all sufficiently small $\varepsilon > 0$ (and $\Phi_\tau(w_\varepsilon) \neq \Phi_\tau(z_0)$ because $\langle \Phi_\tau(w_\varepsilon)-\Phi_\tau(z_0), w_\varepsilon - z_0\rangle \neq 0$). Hence $\Phi_\tau$ is neither monotone nor firmly nonexpansive. $\square$

---

### 3. What the Actual Continuous-Flow Block Guarantees, and Distinguishing $\tau$ from the Proximal Coefficient

#### 3.1. Guarantees of the continuous-flow block $T_\tau = \Phi_\tau$ and its stack $Z_n = T_\tau^n(Z_0)$

- **What is guaranteed:**
  1. *Global forward well-posedness and smoothness:* For every $\tau > 0$, $T_\tau = \Phi_\tau : \mathbb{R}^2 \to \mathbb{R}^2$ is globally defined and $C^\infty$.
  2. *Exact semigroup additivity (depth–time equivalence):* $T_\tau^n = \Phi_\tau^n = \Phi_{n\tau}$, so stacking $n$ blocks of duration $\tau$ is identical to a single continuous evolution of total horizon $T = n\tau$.
  3. *Unique equilibrium and strict exponential contraction:* $z^* = (0,0)$ is the unique fixed point of $T_\tau$ and global minimizer of $f$, and every block strictly contracts Euclidean distances by at least $e^{-\tau}$, giving $\|T_\tau^n(Z_0) - T_\tau^n(W_0)\| \le e^{-n\tau}\|Z_0 - W_0\|$ and $\|Z_n\| \le e^{-n\tau}\|Z_0\|$.
  4. *Continuous energy dissipation and exponential Lyapunov decay:* Along each block $f(T_\tau(z)) + \int_0^\tau \|\nabla f(\Phi_t(z))\|^2\,dt = f(z)$ and $f(T_\tau(z)) \le e^{-2\tau} f(z)$, so $f(Z_n) \le e^{-2n\tau} f(Z_0)$ and every energy sublevel set and origin-centered Euclidean ball is forward invariant.
- **What is NOT guaranteed (and must not be claimed):**
  - $T_\tau$ is **not** a single convex proximal step $\mathrm{prox}_{r_\tau}$ for any proper l.s.c. convex (or even nonconvex) $r_\tau$, so it does **not** carry the single-step proximal three-point certificate (2.1).
  - $T_\tau$ is **not** a conservative gradient map ($D\Phi_\tau$ is asymmetric even arbitrarily close to $0$), and is **not** globally monotone or firmly nonexpansive on $\mathbb{R}^2$ for any $\tau > 0$. (Being globally contractive and dissipative is strictly weaker than being a convex proximal operator.)

#### 3.2. Distinguishing the evolution time $\tau$ from the coefficient in $\mathrm{prox}$

1. **Fixed quadratic coefficient in $\mathrm{prox}_r$:** In the convention
   $$\mathrm{prox}_r(z) = \arg\min_u \left\{ r(u) + \frac{1}{2}\|u - z\|^2 \right\},$$
   the coefficient multiplying $\frac{1}{2}\|u - z\|^2$ is fixed to $1$ (not $1/\tau$). Introducing a positive proximal scaling coefficient $\gamma > 0$ via $\arg\min_u \{ \tilde{r}(u) + \frac{1}{2\gamma}\|u - z\|^2 \} = \arg\min_u \{ \gamma\tilde{r}(u) + \frac{1}{2}\|u - z\|^2 \} = \mathrm{prox}_{\gamma\tilde{r}}(z)$ merely rescales the regularizer inside a single optimization problem; it does not enlarge the class of proximal maps.
2. **Evolution time $\tau$ in $T_\tau = \Phi_\tau$ vs. implicit-Euler step size:** In our deployed block $T_\tau = \Phi_\tau$, $\tau > 0$ is the **continuous integration horizon** of the ODE $\dot{z} = -\nabla f(z)$, **not** a proximal penalty coefficient. By contrast, an implicit-Euler (proximal-point) discretization of $\dot{z} = -\nabla f(z)$ with step size $\tau > 0$ takes the form
   $$J_\tau(z) := \mathrm{prox}_{\tau f}(z) = \arg\min_u \left\{ f(u) + \frac{1}{2\tau}\|u - z\|^2 \right\},$$
   where $\tau$ scales $f$ (equivalently $1/\tau$ weights $\frac{1}{2}\|u-z\|^2$). The two maps differ fundamentally:
   - $J_\tau = \mathrm{prox}_{\tau f}$ *is* an exact convex proximal step satisfying (2.1) and firm nonexpansiveness (2.2), with slower worst-case contraction $(1+\tau)^{-1} > e^{-\tau}$, and it does *not* satisfy semigroup additivity ($J_\tau^n \neq J_{n\tau}$ in general).
   - $\Phi_\tau$ is the **continuous-time limit of infinitely many infinitesimal proximal steps** ($\Phi_\tau(z) = \lim_{m\to\infty}(\mathrm{prox}_{(\tau/m) f})^m(z)$ by the Crandall–Liggett exponential formula), already differs from $\mathrm{prox}_{\tau f}$ at $O(\tau^2)$ ($\Phi_\tau(z) - \mathrm{prox}_{\tau f}(z) = -\frac{\tau^2}{2}\nabla^2 f(z)\nabla f(z) + O(\tau^3)$), satisfies exact semigroup additivity $T_\tau^n = \Phi_{n\tau}$ and faster contraction $e^{-\tau}$, and is not representable as $\mathrm{prox}_{r_\tau}$ for any $\tau > 0$ under any choice of regularizer $r_\tau$ or quadratic coefficient.

---

## Short Deployment Paragraph (Methods Section)

Each denoising block applies the exact continuous-time gradient-flow map $T_\tau = \Phi_\tau : \mathbb{R}^2 \to \mathbb{R}^2$ associated with $\dot{z} = -\nabla f(z)$ for $f(x,y) = \frac{1}{2}(x^2 + 2y^2) + \frac{1}{4}(x+y)^4$ over a configurable evolution horizon $\tau > 0$. Because $f$ is smooth and $1$-strongly convex with unique global minimizer $z^* = (0,0)$, the flow is forward globally well-posed and $C^\infty$ for all $t \ge 0$. Consequently, each block is a strict global contraction ($\|T_\tau(z) - T_\tau(w)\| \le e^{-\tau}\|z - w\|$) and exponentially dissipates the energy ($f(T_\tau(z)) \le e^{-2\tau} f(z)$ with exact dissipation balance $f(T_\tau(z)) + \int_0^\tau \|\nabla f(\Phi_t(z))\|^2\,dt = f(z)$). By the autonomous semigroup property, stacking $n$ identical blocks yields $Z_n = T_\tau^n(Z_0) = \Phi_{n\tau}(Z_0)$, which depends only on the cumulative integration time $n\tau$ and guarantees exponential perturbation stability $\|T_\tau^n(Z_0) - T_\tau^n(W_0)\| \le e^{-n\tau}\|Z_0 - W_0\|$, state convergence $\|Z_n\| \le e^{-n\tau}\|Z_0\|$, and energy decay $f(Z_n) \le e^{-2n\tau} f(Z_0)$ (requiring $n\tau \ge \ln(\|Z_0\|/\varepsilon)$ to reach $\|Z_n\| \le \varepsilon$). Here $\tau$ is strictly the continuous-flow evolution time rather than a quadratic penalty coefficient in a proximal operator $\mathrm{prox}_r(z) = \arg\min_u\{r(u) + \frac{1}{2}\|u-z\|^2\}$ (or an implicit-Euler step $\mathrm{prox}_{\tau f}$): although $\Phi_\tau$ is the continuous-time limit of infinitesimal implicit-Euler steps $(\mathrm{prox}_{(\tau/m) f})^m$, for every $\tau > 0$ the exact flow map $T_\tau$ has a non-symmetric Jacobian and fails global monotonicity and firm nonexpansiveness, and therefore should be characterized as a contractive, energy-dissipative continuous gradient-flow semigroup rather than a single convex proximal regularization step.