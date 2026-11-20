## Mathematical appendix

Write \(z=(x,y)\), \(s=x+y\), and \(g=\nabla f\). Throughout, \(\langle\cdot,\cdot\rangle\) and \(\|\cdot\|\) are the Euclidean inner product and norm.

\[
 g(x,y)=\binom{x+s^3}{2y+s^3},\qquad
 \nabla^2 f(x,y)=
 \begin{pmatrix}1+3s^2&3s^2\\3s^2&2+3s^2\end{pmatrix}.
 \tag{A1}
\]

For \(v=(a,b)\),

\[
 v^{\mathsf T}\nabla^2f(x,y)v
 =a^2+2b^2+3s^2(a+b)^2\ge a^2+2b^2.
 \tag{A2}
\]

Thus \(f\) is \(C^\infty\), coercive (since it is nonnegative and equal to zero only at the origin), and \(1\)-strongly convex; indeed it is \(\nabla^2f\ge I\). These facts are used below. In particular, \(f(0)=0\) and \(f(z)>0\) for \(z\ne0\).

### 1. The exact flow, its equilibrium, and decay estimates

#### Global well-posedness

Because \(g\) is locally Lipschitz, the initial-value problem

\[
\dot z=-g(z),\qquad z(0)=z_0
 \tag{A3}
\]

has a unique local \(C^\infty\) solution. Along this solution,

\[
\frac d{dt}f(z(t))=\langle g(z(t)),\dot z(t)\rangle=-\|g(z(t))\|^2\le0.
 \tag{A4}
\]

Consequently \(z(t)\) remains in the compact sublevel set \(\{z:f(z)\le f(z_0)\}\). Choose a closed ball containing that sublevel set. Because \(Dg=\nabla^2f\) is continuous, it is bounded on this ball; the mean-value inequality therefore gives a Lipschitz bound for \(g\) on the sublevel set. In particular, \(\|g(z(t))\|\) has a uniform bound on the maximal forward interval. A solution whose state remains in a compact set and whose velocity is bounded cannot reach a finite blow-up time, so it extends uniquely for all forward time. Denote it by \(\Phi_t(z_0)\). It satisfies

\[
\Phi_0=\operatorname{id},\qquad \Phi_{t+s}=\Phi_t\circ\Phi_s
 \qquad(t,s\ge0).
 \tag{A5}
\]

The origin is an equilibrium because \(g(0)=0\). Conversely, if \(g(z)=0\), strong convexity, equivalently strong monotonicity of \(g=\nabla f\), gives

\[
0=\langle g(z)-g(0),z\rangle
 =\langle g(z),z\rangle\ge\|z\|^2.
 \tag{A6}
\]

Thus \(z=0\). Since \(f\ge0=f(0)\), the origin is the unique global minimizer and the unique equilibrium.

#### Contraction in space

Set \(z_1(t)=\Phi_t(z_1)\) and \(z_2(t)=\Phi_t(z_2)\). Then

\[
\begin{aligned}
\frac12\frac d{dt}\|z_1(t)-z_2(t)\|^2
&=\langle z_1-z_2,\dot z_1-\dot z_2\rangle\\
&=-\langle z_1-z_2,g(z_1)-g(z_2)\rangle
\le-\|z_1-z_2\|^2. \tag{A7}
\end{aligned}
\]

Gronwall's inequality (or direct integration) gives, for all \(z_1,z_2\in\mathbb R^2\),

\[
\boxed{\|\Phi_t(z_1)-\Phi_t(z_2)\|
 \le e^{-t}\|z_1-z_2\|\qquad(t\ge0).}
 \tag{A8}
\]

Because \(\Phi_t(0)=0\), choosing \(z_2=0\) yields \(\|\Phi_t(z)\|\le e^{-t}\|z\|\).

#### Energy dissipation

We first record the quadratic estimate

\[
\|g(z)\|^2\ge 2f(z)\qquad(z\in\mathbb R^2).
 \tag{A9}
\]

It can be checked directly without a local-optimality assumption. Put \(s=x+y\). Expanding the difference gives

\[
\begin{aligned}
\|g(x,y)\|^2-2f(x,y)
&=2y^2+2s^3y+\frac32s^4+2s^6\\
&=2\left(y+\frac{s^3}{2}\right)^2+\frac32s^4+2s^6-\frac12s^6\\
&=2\left(y+\frac{s^3}{2}\right)^2+\frac32s^4+\frac32s^6\ge0. \tag{A10}
\end{aligned}
\]

Combining (A4) and (A9) along a trajectory yields

\[
\frac d{dt}f(\Phi_t(z))=-\|g(\Phi_t(z))\|^2
 \le -2f(\Phi_t(z)).
\]

Thus, by Gronwall's inequality,

\[
\boxed{f(\Phi_t(z))\le e^{-2t}f(z)\qquad(t\ge0).}
 \tag{A11}
\]

The inequality also handles \(z=0\). No differentiability or uniqueness of the minimizer in a proximal problem is being assumed here.

#### Stacked exact blocks

Let \(T_\tau=\Phi_\tau\) and \(Z_n=T_\tau^n(Z_0)\). The semigroup property gives the exact identity

\[
Z_n=\Phi_{n\tau}(Z_0).
 \tag{A12}
\]

Hence

\[
\boxed{\|Z_n\|\le e^{-n\tau}\|Z_0\|,\qquad
 f(Z_n)\le e^{-2n\tau}f(Z_0)}
 \qquad(n=0,1,2,\ldots).
 \tag{A13}
\]

In particular, \(Z_n\to0\). If \(\varepsilon>0\) and \(Z_0\ne0\), the norm criterion \(\|Z_n\|\le\varepsilon\) is ensured by

\[
n\ge \frac1\tau\log\left(\frac{\|Z_0\|}{\varepsilon}\right),
 \qquad
 \tau>0.
 \tag{A14}
\]

Likewise, if \(Z_0\ne0\) and \(\delta>0\), then \(f(Z_n)\le\delta\) is ensured by

\[
n\ge \frac1{2\tau}\log\left(\frac{f(Z_0)}{\delta}\right).
 \tag{A15}
\]

The right-hand sides are understood as zero when they are negative. Equations (A13)--(A15) contain no time-discretization error because each \(T_\tau\) is the exact flow map.

### 2. Proximal maps: the conditional certificate and firm nonexpansiveness

Let \(r:\mathbb R^2\to(-\infty,+\infty]\) be proper, lower semicontinuous, and convex, and suppose \(T(z)=\operatorname{prox}_r(z)\) in the convention

\[
T(z)=\arg\min_u\left\{r(u)+\frac12\|u-z\|^2\right\}.
 \tag{A16}
\]

Let \(p=T(z)\). Properness, coercivity of the quadratic, and lower semicontinuity ensure that the minimizer exists; strict convexity of the quadratic ensures that it is unique. The first-order condition is

\[
0\in\partial r(p)+p-z,
\qquad\text{equivalently}\qquad z-p\in\partial r(p).
 \tag{A17}
\]

Convexity of \(r\) gives the subgradient inequality, for every \(u\in\operatorname{dom}r\),

\[
r(u)\ge r(p)+\langle z-p,u-p\rangle.
 \tag{A18}
\]

Therefore

\[
\begin{aligned}
r(u)+\frac12\|u-z\|^2
&\ge r(p)+\langle z-p,u-p\rangle+\frac12\|u-z\|^2\\
&=r(p)+\frac12\|p-z\|^2+\frac12\|u-p\|^2. \tag{A19}
\end{aligned}
\]

This is the requested certificate:

\[
\boxed{r(p)+\frac12\|p-z\|^2+\frac12\|u-p\|^2
 \le r(u)+\frac12\|u-z\|^2}
 \qquad(u\in\operatorname{dom}r).
 \tag{A20}
\]

It has the following interpretation: if \(p\) is selected by the proximal minimization at observation \(z\), then moving from \(p\) toward any admissible \(u\) cannot decrease the full objective by more than the right-hand side of (A20). The term \(\|p-z\|^2/2\) is retained in the certificate.

For firm nonexpansiveness, let \(p=T(z)\) and \(q=T(w)\). Apply (A20) to the pair \((z,p)\) with \(u=q\), and to the pair \((w,q)\) with \(u=p\). Adding gives

\[
\|p-q\|^2
\le\frac12\left(
\|q-z\|^2+\|p-w\|^2-\|p-z\|^2-\|q-w\|^2
\right).
 \tag{A21}
\]

The right-hand side equals \(\langle q-p,w-z\rangle\) (expand the four squares). Hence

\[
\boxed{\|T(z)-T(w)\|^2\le\langle T(z)-T(w),z-w\rangle.}
 \tag{A22}
\]

Equivalently,

\[
\boxed{\langle T(z)-T(w),z-w\rangle\ge\|T(z)-T(w)\|^2.}
 \tag{A23}
\]

This is firm nonexpansiveness. By Cauchy--Schwarz,

\[
\|T(z)-T(w)\|\le\|z-w\|.
 \tag{A24}
\]

Finally, \((I-T)(z)-(I-T)(w)=(z-w)-(T(z)-T(w))\), so (A22) and the expansion of the norm give

\[
\|T(z)-T(w)\|^2+\|(I-T)(z)-(I-T)(w)\|^2
\le\|z-w\|^2.
 \tag{A25}
\]

The implication (A16)\(\Rightarrow\)(A20) and (A22)--(A25) is valid. It does not establish its converse, and strong convexity of \(f\) alone does not produce an \(r\) in (A16).

### 3. The limitation of the draft's unconditional proximal claim

One cannot justify the draft's statement

\[
T_\tau=\Phi_\tau=\operatorname{prox}_{r_\tau}
 \qquad\text{for every }\tau>0
 \tag{A26}
\]

by strong convexity of \(f\). The requested certificate is a necessary consequence of a proximal representation, not a sufficient construction of one from the gradient flow.

Here is a local obstruction. If \(T=\operatorname{prox}_r\) for proper lower-semicontinuous convex \(r\), then, for every \(z\),

\[
T(z)=\nabla e_r(z),\qquad
 e_r(z)=\inf_u\left\{r(u)+\frac12\|u-z\|^2\right},
 \tag{A27}
\]

where \(e_r\) is the Moreau envelope. The envelope \(e_r\) is a finite convex function and is \(C^{1,1}\). Thus, wherever its Hessian exists in the classical sense, \(DT(z)\) is symmetric positive semidefinite. Since \(e_r\) is convex, its Hessian is symmetric almost everywhere as well.

Now take any \(z_0\) at which the exact flow map \(\Phi_\tau\) is a \(C^1\) diffeomorphism; this holds here because \(\nabla^2f\) is globally positive definite. Write \(J_\tau=D\Phi_\tau(z_0)\). Differentiating the variational equation gives

\[
\dot J_t=-\nabla^2f(\Phi_t(z_0))J_t,\qquad J_0=I.
 \tag{A28}
\]

At \(z_0=(0,1)\) the state expansion is

\[
x(t)=-t+\frac{13}{2}t^2-\frac{101}{3}t^3+O(t^4),\qquad
y(t)=1-3t+9t^2-\frac{75}{2}t^3+O(t^4),
\tag{A28a}
\]

and hence

\[
s(t)=1-4t+\frac{35}{2}t^2-\frac{427}{6}t^3+O(t^4).
\tag{A28b}
\]

Since \(\nabla^2f=\operatorname{diag}(1,2)+3s^2\mathbf 1\mathbf 1^{\mathsf T}\), this gives

\[
\nabla^2f(z(t))
=\begin{pmatrix}4&3\\3&5\end{pmatrix}
-24t\begin{pmatrix}1&1\\1&1\end{pmatrix}
+141t^2\begin{pmatrix}1&1\\1&1\end{pmatrix}
+O(t^3).
\tag{A28c}
\]

Substitution into the variational equation and matching powers of \(t\) yields (in the ordering \((x,y)\))

\[
J_\tau=I-\tau\begin{pmatrix}4&3\\3&5\end{pmatrix}
+\tau^2\begin{pmatrix}49/2&51/2\\51/2&29\end{pmatrix}
+\tau^3\begin{pmatrix}-967/6&-174\\-170&-1109/6\end{pmatrix}
+O(\tau^4).
 \tag{A29}
\]

The cubic term already has unequal off-diagonal entries \(-174\ne-170\), so the skew term is \(-4\tau^3+O(\tau^4)\). Hence, for every sufficiently small \(\tau>0\), \(D\Phi_\tau(z_0)\) is not symmetric in a neighborhood of \(z_0\). A proximal map's derivative is symmetric almost everywhere. This contradiction rules out (A26) for those \(\tau\) and, in particular, rules out a universal “exact convex proximal block” interpretation. The exact flow remains valid as a contraction and a dissipative map; it is the unconditional proximal interpretation that fails.

If the intended deployment only needs exact contraction and energy decay, no proximal representation is needed. The draft sentence asserting it for every \(	au>0\) should therefore be removed or qualified.

### Deployment paragraph

Each deployed block is the exact autonomous continuous-flow map

\[
T_\tau=\Phi_\tau,\qquad
\dot z=-\nabla f(z),
\qquad
f(x,y)=\frac{x^2+2y^2}{2}+\frac{(x+y)^4}{4},
 \tag{A31}
\]

with physical evolution time \(\tau>0\). For all \(z,w\in\mathbb R^2\),

\[
\|T_\tau(z)-T_\tau(w)\|
\le e^{-\tau}\|z-w\|,\qquad
 f(T_\tau(z))\le e^{-2\tau}f(z).
 \tag{A32}
\]

Stacking \(n\) identical blocks produces \(Z_n=T_\tau^n(Z_0)=\Phi_{n\tau}(Z_0)\), so

\[
\|Z_n\|\le e^{-n\tau}\|Z_0\|,\qquad
 f(Z_n)\le e^{-2n\tau}f(Z_0).
 \tag{A33}
\]

Thus the stack converges exponentially to the unique equilibrium \((0,0)\), with the displayed deterministic sensitivity and dissipation guarantees. These statements concern the exact flow; they are not a claim that the numerical implementation has no discretization error.

The coefficient in

\[
\operatorname{prox}_r(z)
=\arg\min_u\left\{r(u)+\frac12\|u-z\|^2\right\}
 \tag{A34}
\]

is a fixed factor \(1/2\) inside the squared norm; it is not the evolution time \(\tau\). In generalized notation \(\operatorname{prox}_{\eta r}(z)=\arg\min_u\{\eta r(u)+\|u-z\|^2/2\}\), the scalar \(\eta\) is a proximal-step coefficient and is a different parameter from \(\tau\). In particular, \(\operatorname{prox}_{\eta f}\) is the implicit-Euler / backward-Euler map with step \(\eta\), rather than the exact flow map \(\Phi_\eta\).

## Self-audit and delivery status

- **Retained:** the gradient and Hessian calculation, forward global well-posedness, the unique equilibrium, spatial contraction, energy dissipation, stacked-flow identities and convergence thresholds, the conditional proximal certificate, and firm nonexpansiveness.
- **Corrected or added:** I removed reliance on an invalid converse from strong convexity to proximal representability; I supplied an explicit polynomial identity and completed-square estimate for the energy inequality; and I added a local Taylor obstruction showing that the draft's universal exact-proximal interpretation is false. The deployment discussion now keeps \(\tau\), the proximal coefficient, and the prox-map notation distinct.
- **Still unresolved or uncertain:** No closed form for \(\Phi_t\) is supplied, which the problem explicitly says is unnecessary. The obstruction rules out a universal proximal representation, not every conceivable block-specific representation at each individual \(\tau\); it is sufficient to invalidate the draft's unrestricted design rationale. The displayed estimates are deterministic forward-flow guarantees and do not describe numerical discretization or stochastic perturbations.

This is a standard proof task whose requested arguments are completed; there is no separate new research problem to solve. In the supplied B/R terminology, the baseline result is complete, so I claim **B2**; I do not claim a research increment, so the research level is **R0**. The resulting research score is **R=0**. The baseline contribution is correct, so I claim no baseline-error deduction; the reliable research level is therefore the same **R=0**. I do not claim SMC: under the present rubric it additionally requires **R3**, which this standard proof task does not contain.
