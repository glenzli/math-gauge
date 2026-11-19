## Mathematical appendix

The exact block satisfies the stated contraction and energy bounds. For every \(\tau>0\), however, its Jacobian is nonsymmetric at some inputs arbitrarily close to the origin. This rules out the draft’s convex proximal representation.

### 1. Forward flow and convergence

Let \(A=\operatorname{diag}(1,2)\) and \(v=(1,1)^\top\). Then
\[
\nabla f(z)=Az+(v^\top z)^3v,\qquad
\nabla^2 f(z)=A+3(v^\top z)^2vv^\top\succeq I.
\]
Thus \(f\) is \(1\)-strongly convex, and \(\nabla f(0)=0\) makes the origin its unique minimizer and the unique equilibrium.

The smooth vector field gives a unique local solution \(X_t=\Phi_t(z)\). Along that solution,
\[
\frac{d}{dt}f(X_t)=-\|\nabla f(X_t)\|^2.
\]
Since \(f(X_t)\le f(z)\) and \(f(X_t)\ge \|X_t\|^2/2\), the trajectory stays in a bounded set. The ODE continuation theorem therefore gives existence for all \(t\ge0\).

For a second trajectory \(Y_t=\Phi_t(w)\), strong convexity gives
\[
\frac12\frac{d}{dt}\|X_t-Y_t\|^2
=-\langle X_t-Y_t,\nabla f(X_t)-\nabla f(Y_t)\rangle
\le-\|X_t-Y_t\|^2.
\]
Integration yields \(\|\Phi_t(z)-\Phi_t(w)\|\le e^{-t}\|z-w\|\). For the energy estimate, applying strong convexity at \(z\) with comparison point \(0\) gives
\[
f(z)\le \langle\nabla f(z),z\rangle-\tfrac12\|z\|^2
\le \tfrac12\|\nabla f(z)\|^2.
\]
Consequently \(\frac{d}{dt}f(X_t)\le-2f(X_t)\), so \(f(\Phi_t(z))\le e^{-2t}f(z)\).

Autonomy and uniqueness give \(T_\tau^n=\Phi_{n\tau}\). In particular,
\[
\boxed{\quad \|Z_n\|\le e^{-n\tau}\|Z_0\|,\qquad
f(Z_n)\le e^{-2n\tau}f(Z_0).\quad}
\]

### 2. Proximal certificate and firm nonexpansiveness

Suppose \(T=\operatorname{prox}_r\) for a proper lower-semicontinuous convex \(r\). The optimality condition for \(p=T(z)\) is \(z-p\in\partial r(p)\). Hence every \(u\in\operatorname{dom}r\) satisfies
\[
r(u)\ge r(p)+\langle z-p,u-p\rangle.
\]
Adding \(\tfrac12\|u-z\|^2\) and expanding the square gives the certificate
\[
\boxed{\quad
r(p)+\tfrac12\|p-z\|^2+\tfrac12\|u-p\|^2
\le r(u)+\tfrac12\|u-z\|^2.\quad}
\]
For \(q=T(w)\), monotonicity of \(\partial r\) gives
\(\langle (z-p)-(w-q),p-q\rangle\ge0\). Rearranging yields firm nonexpansiveness,
\[
\|T(z)-T(w)\|^2\le\langle T(z)-T(w),z-w\rangle.
\]

### 3. Testing the proximal claim for the exact block

A continuously differentiable convex proximal map must have a symmetric Jacobian. To see this, define
\[
\Psi(z)=\sup_u\{\langle z,u\rangle-r(u)-\tfrac12\|u\|^2\}.
\]
The unique maximizer is \(T(z)\). Using the maximizers at \(z\) and \(z+h\) gives
\[
\langle T(z),h\rangle
\le\Psi(z+h)-\Psi(z)
\le\langle T(z+h),h\rangle.
\]
Firm nonexpansiveness makes \(T\) \(1\)-Lipschitz, so the two bounds differ by at most \(\|h\|^2\). Thus \(\nabla\Psi=T\), and for \(T\in C^1\) its Jacobian is the symmetric Hessian of \(\Psi\).

To test this condition, fix \(t>0\). Write \(e_1=(1,0)^\top\), \(X_s(a)=\Phi_s(ae_1)\), \(J_s(a)=D\Phi_s(ae_1)\), and \(E_s=e^{-sA}\). The variational equation \(J'_s=-\nabla^2 f(X_s(a))J_s\), with \(J_0=I\), gives
\[
J_t(a)=E_t-3\int_0^t (v^\top X_s(a))^2
                  E_{t-s}vv^\top J_s(a)\,ds.
\]
At the equilibrium \(J_s(0)=E_s\). Smooth dependence on the initial state therefore gives \(J_s(a)\to E_s\) and \(X_s(a)/a\to E_se_1=e^{-s}e_1\), uniformly on \([0,t]\). Taking the difference of the off-diagonal entries in the integral yields
\[
\begin{aligned}
\lim_{a\to0}\frac{(J_t(a))_{12}-(J_t(a))_{21}}{a^2}
&=-3\int_0^t\bigl(e^{-t-3s}-e^{-2t-s}\bigr)\,ds\\
&=-e^{-t}(1-e^{-t})^3<0 .
\end{aligned}
\]
Thus \(D\Phi_t(ae_1)\) fails the symmetry condition for all sufficiently small nonzero \(a\). Since \(t>0\) was arbitrary, the obstruction applies to every positive deployment time.

## Deployment paragraph

Each block advances the gradient flow of \(f\) for a duration \(\tau\). A stack of \(n\) blocks realizes the exact time-\(n\tau\) map, contracts input differences by a factor at most \(e^{-n\tau}\), and drives the state to zero with energy at most \(e^{-2n\tau}f(Z_0)\). Here \(\tau\) specifies elapsed evolution time. With the quadratic coefficient fixed at \(1/2\) in the proximal convention, \(\operatorname{prox}_{\tau f}\) describes the implicit-Euler update \(p+\tau\nabla f(p)=z\).