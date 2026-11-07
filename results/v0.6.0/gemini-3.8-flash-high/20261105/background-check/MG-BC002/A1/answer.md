## Part 1: Mathematical Appendix — Flow Analysis and Stack Convergence

### 1. Energy Potential and Vector Field
The system state is $z = (x, y)^\top \in \mathbb{R}^2$, and the energy function is
$$f(x, y) = \frac{1}{2}\left(x^2 + 2y^2\right) + \frac{1}{4}(x + y)^4.$$

The gradient vector field $\nabla f(z)$ is given by:
$$\nabla f(z) = \begin{pmatrix} \partial_x f(x, y) \\ \partial_y f(x, y) \end{pmatrix} = \begin{pmatrix} x + (x + y)^3 \\ 2y + (x + y)^3 \end{pmatrix}.$$

The Hessian matrix $\nabla^2 f(z)$ is:
$$\nabla^2 f(z) = \begin{pmatrix} 1 + 3(x + y)^2 & 3(x + y)^2 \\ 3(x + y)^2 & 2 + 3(x + y)^2 \end{pmatrix} = \begin{pmatrix} 1 & 0 \\ 0 & 2 \end{pmatrix} + 3(x + y)^2 \begin{pmatrix} 1 & 1 \\ 1 & 1 \end{pmatrix}.$$
For any non-zero vector $v = (v_1, v_2)^\top \in \mathbb{R}^2$:
$$v^\top \nabla^2 f(z) v = v_1^2 + 2v_2^2 + 3(x + y)^2(v_1 + v_2)^2 \ge v_1^2 + 2v_2^2 \ge \|v\|^2.$$
Hence, $\nabla^2 f(z) \succeq I$ uniformly for all $z \in \mathbb{R}^2$. This establishes that $f$ is **1-strongly convex** on $\mathbb{R}^2$ with respect to the standard Euclidean norm.

---

### 2. Forward Global Well-Posedness
Consider the Cauchy problem for the autonomous gradient flow:
$$\dot{z}(t) = -\nabla f(z(t)), \quad z(0) = z_0.$$

1. **Local Well-Posedness:** The components of $\nabla f(z)$ are polynomials, hence $C^\infty$ and locally Lipschitz continuous on $\mathbb{R}^2$. By the Picard–Lindelöf theorem, there exists a unique maximal solution $z(t) = \Phi_t(z_0)$ defined on an interval $[0, T_{\max})$.
2. **Global Existence ($T_{\max} = +\infty$):** Along any trajectory, the energy evolves according to:
   $$\frac{d}{dt} f(z(t)) = \langle \nabla f(z(t)), \dot{z}(t) \rangle = -\|\nabla f(z(t))\|^2 \le 0.$$
   Thus, $f(z(t)) \le f(z_0)$ for all $t \in [0, T_{\max})$. Moreover, $f$ is coercive:
   $$f(x, y) \ge \frac{1}{2}(x^2 + 2y^2) \ge \frac{1}{2}\|z\|^2 \implies \|z(t)\| \le \sqrt{2 f(z_0)}.$$
   Consequently, every trajectory remains inside the compact sublevel set $\mathcal{K} = \{z \in \mathbb{R}^2 : \|z\| \le \sqrt{2f(z_0)}\}$. By the escape of compact sets theorem, no finite-time blowup can occur, meaning $T_{\max} = +\infty$. The continuous flow map $\Phi_t: \mathbb{R}^2 \to \mathbb{R}^2$ is globally well-defined for all $t \ge 0$ and satisfies the continuous semigroup property $\Phi_{t+s} = \Phi_t \circ \Phi_s$ with $\Phi_0 = I$.

---

### 3. Identification of the Unique Equilibrium
An equilibrium $z^* = (x^*, y^*)^\top$ satisfies $\dot{z} = -\nabla f(z^*) = 0$:
$$\begin{cases} x + (x + y)^3 = 0, & (1) \\ 2y + (x + y)^3 = 0. & (2) \end{cases}$$
Subtracting (2) from (1) yields:
$$x - 2y = 0 \implies x = 2y.$$
Substituting $x = 2y$ back into (2):
$$2y + (3y)^3 = y(2 + 27y^2) = 0.$$
Since $2 + 27y^2 \ge 2 > 0$ for all $y \in \mathbb{R}$, the unique real root is $y = 0$, which immediately gives $x = 0$. 

Thus, the unique equilibrium is the origin:
$$z^* = (0, 0)^\top.$$
At this point, $f(z^*) = f(0, 0) = 0$.

---

### 4. Derivation of the Contractivity Bound: $\|\Phi_t(z) - \Phi_t(w)\| \le e^{-t}\|z - w\|$
Let $z(t) = \Phi_t(z)$ and $w(t) = \Phi_t(w)$ be two trajectories initialized at $z, w \in \mathbb{R}^2$. Define the squared Euclidean distance:
$$D(t) = \frac{1}{2}\|z(t) - w(t)\|^2.$$
Differentiating with respect to $t$:
$$\frac{d}{dt} D(t) = \langle z(t) - w(t), \dot{z}(t) - \dot{w}(t) \rangle = -\langle \nabla f(z(t)) - \nabla f(w(t)), z(t) - w(t) \rangle.$$
By the mean-value theorem for vector-valued functions and the uniform lower bound $\nabla^2 f \succeq I$:
$$\langle \nabla f(z) - \nabla f(w), z - w \rangle = \int_0^1 (z - w)^\top \nabla^2 f(w + s(z - w)) (z - w) \, ds \ge \|z - w\|^2.$$
Applying this 1-strong monotonicity property yields:
$$\frac{d}{dt} D(t) \le -\|z(t) - w(t)\|^2 = -2 D(t).$$
Multiplying by the integrating factor $e^{2t}$:
$$\frac{d}{dt}\left( e^{2t} D(t) \right) \le 0 \implies D(t) \le e^{-2t} D(0).$$
Substituting $D(t) = \frac{1}{2}\|z(t) - w(t)\|^2$ and taking the square root gives:
$$\|\Phi_t(z) - \Phi_t(w)\| \le e^{-t}\|z - w\|, \quad \forall t \ge 0.$$

---

### 5. Derivation of the Dissipation Bound: $f(\Phi_t(z)) \le e^{-2t}f(z)$
Along any trajectory $z(t) = \Phi_t(z)$, the energy dissipation rate is:
$$\frac{d}{dt} f(z(t)) = -\|\nabla f(z(t))\|^2.$$
Since $f$ is 1-strongly convex, for any $u, v \in \mathbb{R}^2$:
$$f(v) \ge f(u) + \langle \nabla f(u), v - u \rangle + \frac{1}{2}\|v - u\|^2.$$
Minimizing the right-hand side over $v \in \mathbb{R}^2$ gives the minimum at $v = u - \nabla f(u)$:
$$f(v) \ge f(u) - \frac{1}{2}\|\nabla f(u)\|^2, \quad \forall v \in \mathbb{R}^2.$$
Evaluating this inequality at the global minimizer $v = z^* = (0, 0)$ where $f(z^*) = 0$:
$$0 \ge f(u) - \frac{1}{2}\|\nabla f(u)\|^2 \implies \|\nabla f(u)\|^2 \ge 2 f(u),$$
which is the Polyak–Łojasiewicz (PL) inequality with modulus $\mu = 1$.
Applying this to $u = z(t)$:
$$\frac{d}{dt} f(z(t)) = -\|\nabla f(z(t))\|^2 \le -2 f(z(t)).$$
Integrating with the factor $e^{2t}$:
$$\frac{d}{dt}\left( e^{2t} f(z(t)) \right) \le 0 \implies f(\Phi_t(z)) \le e^{-2t} f(z), \quad \forall t \ge 0.$$

---

### 6. Quantitative Convergence for a Stacked Architecture
Each denoising block is $T_\tau = \Phi_\tau$ for a fixed $\tau > 0$. Stacking $n$ identical blocks produces:
$$Z_n = T_\tau^n(Z_0) = \underbrace{(\Phi_\tau \circ \cdots \circ \Phi_\tau)}_{n \text{ times}}(Z_0).$$
By the continuous dynamical semigroup property ($\Phi_t \circ \Phi_s = \Phi_{t+s}$):
$$Z_n = \Phi_{n\tau}(Z_0).$$
Because the equilibrium $z^* = 0$ is stationary ($\Phi_t(0) = 0$ and $f(0) = 0$):
1. **State-Space Metric Convergence:** Setting $w = 0$ in the contractivity bound:
   $$\|Z_n\| = \|\Phi_{n\tau}(Z_0) - \Phi_{n\tau}(0)\| \le e^{-n\tau}\|Z_0\|.$$
2. **Energy Dissipation Convergence:**
   $$f(Z_n) \le e^{-2n\tau} f(Z_0).$$
3. **Perturbation Robustness:** For any two initial representations $Z_0, W_0$ (e.g., perturbed vs. unperturbed inputs):
   $$\|Z_n - W_n\| \le e^{-n\tau}\|Z_0 - W_0\|.$$

Both the Euclidean norm and the energy decay geometrically with depth $n$ at linear rates $\rho = e^{-\tau} < 1$ and $\rho^2 = e^{-2\tau} < 1$ per layer, respectively.

---

## Part 2: Proximal Certificate and Firm Nonexpansiveness

### 1. Statement of the Proximal Certificate
Let $r: \mathbb{R}^d \to (-\infty, +\infty]$ be a proper, lower-semicontinuous (l.s.c.), convex function. Under the convention:
$$\text{prox}_r(z) = \arg\min_{v \in \mathbb{R}^d} \left\{ r(v) + \frac{1}{2}\|v - z\|^2 \right\},$$
let $p = T(z) = \text{prox}_r(z)$. Then for every $u \in \text{dom } r$:
$$r(p) + \frac{1}{2}\|p - z\|^2 + \frac{1}{2}\|u - p\|^2 \le r(u) + \frac{1}{2}\|u - z\|^2.$$

### 2. Proof of the Certificate
The objective function $\psi(v) = r(v) + \frac{1}{2}\|v - z\|^2$ is 1-strongly convex and proper l.s.c., ensuring that the minimizer $p$ is unique. 

By Fermat's rule for convex optimization, $0 \in \partial \psi(p)$. Because the quadratic term $\frac{1}{2}\|\cdot - z\|^2$ is continuously differentiable with gradient $p - z$, the subdifferential sum rule applies:
$$0 \in \partial r(p) + (p - z) \iff z - p \in \partial r(p).$$
By definition of the Fenchel subdifferential of $r$ at $p$, for all $u \in \text{dom } r$:
$$r(u) \ge r(p) + \langle z - p, u - p \rangle. \qquad (3)$$
We now rewrite the inner product $\langle z - p, u - p \rangle$ using the Euclidean polarization identity:
$$\|u - z\|^2 = \|(u - p) + (p - z)\|^2 = \|u - p\|^2 + \|p - z\|^2 + 2\langle u - p, p - z \rangle.$$
Rearranging gives:
$$\langle z - p, u - p \rangle = -\langle p - z, u - p \rangle = \frac{1}{2}\|u - z\|^2 - \frac{1}{2}\|p - z\|^2 - \frac{1}{2}\|u - p\|^2.$$
Substituting this identity into (3):
$$r(u) \ge r(p) + \frac{1}{2}\|u - z\|^2 - \frac{1}{2}\|p - z\|^2 - \frac{1}{2}\|u - p\|^2.$$
Rearranging terms yields the desired certificate:
$$r(p) + \frac{1}{2}\|p - z\|^2 + \frac{1}{2}\|u - p\|^2 \le r(u) + \frac{1}{2}\|u - z\|^2. \qquad \blacksquare$$

---

### 3. Derivation of Firm Nonexpansiveness
Let $z_1, z_2 \in \mathbb{R}^d$, and define $p_1 = T(z_1) = \text{prox}_r(z_1)$ and $p_2 = T(z_2) = \text{prox}_r(z_2)$. Since $p_1, p_2 \in \text{dom } r$:

1. Apply the certificate for $(z_1, p_1)$ with test point $u = p_2$:
   $$r(p_1) + \frac{1}{2}\|p_1 - z_1\|^2 + \frac{1}{2}\|p_2 - p_1\|^2 \le r(p_2) + \frac{1}{2}\|p_2 - z_1\|^2. \qquad (4)$$
2. Apply the certificate for $(z_2, p_2)$ with test point $u = p_1$:
   $$r(p_2) + \frac{1}{2}\|p_2 - z_2\|^2 + \frac{1}{2}\|p_1 - p_2\|^2 \le r(p_1) + \frac{1}{2}\|p_1 - z_2\|^2. \qquad (5)$$

Adding inequalities (4) and (5), the potential values $r(p_1)$ and $r(p_2)$ cancel:
$$\|p_1 - p_2\|^2 + \frac{1}{2}\|p_1 - z_1\|^2 + \frac{1}{2}\|p_2 - z_2\|^2 \le \frac{1}{2}\|p_2 - z_1\|^2 + \frac{1}{2}\|p_1 - z_2\|^2. \qquad (6)$$
Expanding the cross-terms on the right-hand side:
$$\|p_2 - z_1\|^2 = \|(p_2 - p_1) + (p_1 - z_1)\|^2 = \|p_1 - p_2\|^2 + \|p_1 - z_1\|^2 + 2\langle p_2 - p_1, p_1 - z_1 \rangle,$$
$$\|p_1 - z_2\|^2 = \|(p_1 - p_2) + (p_2 - z_2)\|^2 = \|p_1 - p_2\|^2 + \|p_2 - z_2\|^2 + 2\langle p_1 - p_2, p_2 - z_2 \rangle.$$
Summing these two expansions and dividing by 2:
$$\frac{1}{2}\|p_2 - z_1\|^2 + \frac{1}{2}\|p_1 - z_2\|^2 = \|p_1 - p_2\|^2 + \frac{1}{2}\|p_1 - z_1\|^2 + \frac{1}{2}\|p_2 - z_2\|^2 + \langle p_1 - p_2, (p_2 - z_2) - (p_1 - z_1) \rangle.$$
Substituting this expression into the right-hand side of (6) and canceling identical terms on both sides gives:
$$0 \le \langle p_1 - p_2, (p_2 - z_2) - (p_1 - z_1) \rangle = \langle p_1 - p_2, (z_1 - p_1) - (z_2 - p_2) \rangle.$$
Rewriting the inner product:
$$\langle p_1 - p_2, (z_1 - z_2) - (p_1 - p_2) \rangle \ge 0 \iff \|p_1 - p_2\|^2 \le \langle p_1 - p_2, z_1 - z_2 \rangle.$$
This is the characterization of **firm nonexpansiveness**. 

Equivalently, it can be written as:
$$\|T(z_1) - T(z_2)\|^2 + \|(I - T)(z_1) - (I - T)(z_2)\|^2 \le \|z_1 - z_2\|^2,$$
which immediately implies nonexpansiveness (Lipschitz continuity with constant 1):
$$\|T(z_1) - T(z_2)\| \le \|z_1 - z_2\|. \qquad \blacksquare$$

---

## Part 3: Deployment Description (Methods Section Paragraph)

**Continuous Denoising Dynamics and Multi-Block Stacking.** Each autonomous denoising block implements the exact continuous-time flow operator $T_\tau = \Phi_\tau$ of the gradient system $\dot{z} = -\nabla f(z)$ over a transit duration $\tau > 0$, where the potential $f(z) = \frac{1}{2}(x^2+2y^2) + \frac{1}{4}(x+y)^4$ is uniformly 1-strongly convex. Consequently, each block provides a certified contractive denoising guarantee: for any states $z, w \in \mathbb{R}^2$, $\|T_\tau(z) - T_\tau(w)\| \le e^{-\tau}\|z - w\|$, while strictly dissipating the energy via $f(T_\tau(z)) \le e^{-2\tau}f(z)$. Deploying a depth-$n$ cascade $Z_n = T_\tau^n(Z_0)$ exploits the continuous semigroup property $\Phi_\tau^n = \Phi_{n\tau}$, meaning an $n$-block stack corresponds exactly to a continuous evolution of total transit time $t = n\tau$. This guarantees exponential convergence toward the unique ground-state equilibrium $z^* = (0, 0)$ with $\|Z_n\| \le e^{-n\tau}\|Z_0\|$ and $f(Z_n) \le e^{-2n\tau}f(Z_0)$, completely bypassing discretization errors or numerical instabilities. 

**Distinction from Proximal Discretization.** It is mathematically essential to distinguish the flow transit time $\tau$ from the weighting parameter in proximal regularization. In standard proximal formulations $\text{prox}_{\gamma f}(z) = \arg\min_u \{\gamma f(u) + \frac{1}{2}\|u - z\|^2\}$ (which corresponds to an implicit Euler step), $\gamma$ acts as a static trade-off coefficient balancing energy minimization against Euclidean displacement, yielding only firm nonexpansiveness ($\text{Lip} \le 1$). In our architecture, the coefficient $\frac{1}{2}$ is fixed by definition, and the block is not an implicit Euler step ($T_\tau \ne \text{prox}_{\tau f}$). Instead, $\tau$ represents the continuous physical transit time along the trajectory curve $\dot{z} = -\nabla f(z)$, translating directly into an exponential contractivity modulus $e^{-\tau} < 1$ that compounds strictly multiplicatively across layers.
