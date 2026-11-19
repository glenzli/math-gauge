## Mathematical appendix

### 1. Global flow and convergence

Let \(A=\operatorname{diag}(1,2)\) and \(v=(1,1)^\top\). Then
\[
\nabla f(z)=Az+(v^\top z)^3v,
\qquad
\nabla^2 f(z)=A+3(v^\top z)^2vv^\top\succeq I.
\]
Thus \(f\) is \(1\)-strongly convex. Since \(\nabla f(0)=0\), the origin is its unique minimizer and the flow’s unique equilibrium.

The smooth vector field gives a unique local solution. Along that solution,
\[
\frac{d}{dt}f(\Phi_t(z))=-\|\nabla f(\Phi_t(z))\|^2.
\]
Since \(f(a)\ge \tfrac12\|a\|^2\), the solution stays in a bounded sublevel set. The ODE continuation theorem therefore gives existence for all \(t\ge0\).

For \(a=\Phi_t(z)\) and \(b=\Phi_t(w)\), strong convexity gives
\[
\frac{d}{dt}\frac12\|a-b\|^2
=-\langle a-b,\nabla f(a)-\nabla f(b)\rangle
\le-\|a-b\|^2.
\]
Integrating yields \(\|\Phi_t(z)-\Phi_t(w)\|\le e^{-t}\|z-w\|\). The strong convexity inequality at \(a\), evaluated at \(0\), also gives
\[
f(a)\le \langle \nabla f(a),a\rangle-\tfrac12\|a\|^2
\le \tfrac12\|\nabla f(a)\|^2.
\]
It follows that \(\frac{d}{dt}f(\Phi_t(z))\le -2f(\Phi_t(z))\) and hence \(f(\Phi_t(z))\le e^{-2t}f(z)\).

By autonomy and uniqueness, \(T_\tau^n=\Phi_{n\tau}\). In particular,
\[
\|Z_n\|\le e^{-n\tau}\|Z_0\|,
\qquad
f(Z_n)\le e^{-2n\tau}f(Z_0).
\]
Two stacks with different initial states also satisfy the pairwise contraction bound with factor \(e^{-n\tau}\).

### 2. Proximal certificate and firm nonexpansiveness

Suppose \(T=\operatorname{prox}_r\) for a proper lower-semicontinuous convex function \(r\). Define \(G_z(a)=r(a)+\tfrac12\|a-z\|^2\), and let \(p=T(z)\). For \(u\in\operatorname{dom}r\) and \(0<\lambda<1\), minimality and \(1\)-strong convexity of \(G_z\) give
\[
G_z(p)\le G_z((1-\lambda)p+\lambda u)
\le (1-\lambda)G_z(p)+\lambda G_z(u)
-\tfrac12\lambda(1-\lambda)\|u-p\|^2.
\]
Canceling, dividing by \(\lambda\), and letting \(\lambda\downarrow0\) proves
\[
r(p)+\tfrac12\|p-z\|^2+\tfrac12\|u-p\|^2
\le r(u)+\tfrac12\|u-z\|^2.
\]
With \(q=T(w)\), apply the certificate at \(z\) using \(u=q\) and at \(w\) using \(u=p\). Adding and expanding the squares yields firm nonexpansiveness,
\[
\|T(z)-T(w)\|^2\le \langle T(z)-T(w),z-w\rangle.
\]

### 3. The exact flow has no convex proximal representation

A \(C^1\) convex proximal map must have a symmetric Jacobian. To see this, define
\[
H(z)=\sup_{u\in\operatorname{dom}r}
\bigl\{\langle z,u\rangle-r(u)-\tfrac12\|u\|^2\bigr\}.
\]
The maximizer is \(T(z)\), by expanding the squared distance in the proximal objective. Comparing the maximizers at \(z\) and \(z+h\) gives
\[
0\le H(z+h)-H(z)-\langle T(z),h\rangle
\le \langle T(z+h)-T(z),h\rangle\le \|h\|^2,
\]
where the last bound follows from firm nonexpansiveness and Cauchy–Schwarz. Thus \(\nabla H=T\). If \(T\) is \(C^1\), its Jacobian is the Hessian of \(H\) and is symmetric.

Fix any \(t>0\), set \(e_1=(1,0)^\top\) and \(E_s=e^{-sA}\), and write \(z_s=\Phi_s(\varepsilon e_1)\) and \(J_s=D\Phi_s(\varepsilon e_1)\). Smooth dependence on initial conditions gives
\[
\dot J_s=-\bigl(A+3(v^\top z_s)^2vv^\top\bigr)J_s,\qquad J_0=I.
\]
The contraction bound gives \(\|z_s\|\le|\varepsilon|\) and \(\|J_s\|\le e^{-s}\). Variation of constants in the state and Jacobian equations then gives \(z_s=\varepsilon E_s e_1+O(\varepsilon^3)\) and \(J_s=E_s+O(\varepsilon^2)\), uniformly on \([0,t]\). Substituting these estimates back into the Jacobian equation in integral form yields
\[
J_t=E_t-3\varepsilon^2\int_0^t e^{-2s}E_{t-s}vv^\top E_s\,ds+O(\varepsilon^4).
\]
In particular,
\[
\begin{aligned}
(J_t)_{12}-(J_t)_{21}
&=-3\varepsilon^2\left[e^{-t}\int_0^t e^{-3s}\,ds
-e^{-2t}\int_0^t e^{-s}\,ds\right]+O(\varepsilon^4)\\
&=-\varepsilon^2e^{-t}(1-e^{-t})^3+O(\varepsilon^4).
\end{aligned}
\]
For each \(t>0\), the leading coefficient is nonzero, so the Jacobian is asymmetric for sufficiently small nonzero \(\varepsilon\). This rules out \(T_\tau=\operatorname{prox}_{r_\tau}\) for every \(\tau>0\).

## Deployment paragraph

Each block advances the exact gradient flow by elapsed time \(\tau\). A stack of \(n\) blocks advances it to time \(n\tau\), contracts pairwise state distances by a factor at most \(e^{-n\tau}\), and bounds the remaining energy by \(e^{-2n\tau}f(Z_0)\). Every initial state converges to the origin. At every positive block duration, the flow violates the Jacobian symmetry required for a convex proximal representation. The proximal convention fixes the squared-distance coefficient at \(1/2\). In that convention, an implicit Euler step of size \(\tau\) would be \(\operatorname{prox}_{\tau f}\), equivalently the minimizer of \(f(u)+\|u-z\|^2/(2\tau)\).