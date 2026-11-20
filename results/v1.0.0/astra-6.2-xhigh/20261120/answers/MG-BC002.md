## Mathematical appendix

### 1. Global flow, contraction, and energy decay

Let \(A=\operatorname{diag}(1,2)\) and \(b=(1,1)^\top\). Then
\[
\nabla f(z)=Az+(b^\top z)^3b,\qquad
\nabla^2 f(z)=A+3(b^\top z)^2bb^\top\succeq I.
\]
Thus \(f\) is \(1\)-strongly convex. Since \(\nabla f(0)=0\), the origin is its unique minimizer and the unique equilibrium.

The smooth vector field gives a unique local solution. Along that solution,
\[
\frac{d}{dt}f(\Phi_t(z))=-\|\nabla f(\Phi_t(z))\|^2.
\]
Since \(f(v)\ge \|v\|^2/2\), the trajectory stays in a compact sublevel set. The ODE continuation theorem therefore gives existence for every \(t\ge0\).

For \(v=\Phi_t(z)\) and \(w=\Phi_t(w_0)\), strong convexity gives
\[
\frac12\frac{d}{dt}\|v-w\|^2
=-\langle v-w,\nabla f(v)-\nabla f(w)\rangle
\le -\|v-w\|^2.
\]
Also, the strong convexity inequality evaluated at the minimizer gives
\[
f(v)\le \langle\nabla f(v),v\rangle-\tfrac12\|v\|^2
\le \tfrac12\|\nabla f(v)\|^2.
\]
Integrating the two differential inequalities yields
\[
\boxed{\ \|\Phi_t(z)-\Phi_t(w_0)\|\le e^{-t}\|z-w_0\|,\qquad
f(\Phi_t(z))\le e^{-2t}f(z).\ }
\]
By autonomy and uniqueness, \(T_\tau^n=\Phi_{n\tau}\). In particular,
\(\|Z_n\|\le e^{-n\tau}\|Z_0\|\) and \(f(Z_n)\le e^{-2n\tau}f(Z_0)\).

### 2. Proximal certificate and its applicability

Suppose \(T=\operatorname{prox}_r\) for a proper lower-semicontinuous convex \(r\). The optimality condition at \(p=T(z)\) is \(z-p\in\partial r(p)\). Hence \(r(u)\ge r(p)+\langle z-p,u-p\rangle\) for every \(u\in\operatorname{dom}r\). Expanding \(\|u-z\|^2\) about \(p\) gives
\[
\boxed{\ r(p)+\tfrac12\|p-z\|^2+\tfrac12\|u-p\|^2
\le r(u)+\tfrac12\|u-z\|^2.\ }
\]
For \(q=T(w)\), monotonicity of \(\partial r\) gives
\(\langle (z-p)-(w-q),p-q\rangle\ge0\). Rearranging proves firm nonexpansiveness,
\[
\|T(z)-T(w)\|^2\le \langle T(z)-T(w),z-w\rangle .
\]

**The claimed proximal representation fails for every \(\tau>0\).** To see the obstruction, any differentiable convex proximal map must have a symmetric Jacobian. Indeed, define
\[
H(z)=\sup_u\{\langle z,u\rangle-r(u)-\tfrac12\|u\|^2\}.
\]
The unique maximizer is \(T(z)\). Using the maximizers at \(z\) and \(z+d\) to bound the increment gives
\[
0\le H(z+d)-H(z)-\langle T(z),d\rangle
\le \langle T(z+d)-T(z),d\rangle\le\|d\|^2.
\]
Thus \(T=\nabla H\), so a \(C^1\) proximal map has symmetric Jacobian.

For the given flow, fix \(t>0\), set \(e_1=(1,0)^\top\), and write \(v_a(s)=\Phi_s(ae_1)\), \(J_a(s)=D\Phi_s(ae_1)\), and \(E(s)=e^{-sA}\). The variational equation is
\[
\dot J_a=-AJ_a-3(b^\top v_a)^2bb^\top J_a,\qquad J_a(0)=I.
\]
At the equilibrium, \(J_0(s)=E(s)\). Smooth dependence on initial data gives \(v_a(s)/a\to e^{-s}e_1\) and \(J_a(s)\to E(s)\) uniformly on \([0,t]\) as \(a\to0\). Variation of constants therefore yields
\[
J_a(t)=E(t)-3a^2\int_0^t e^{-2s}E(t-s)bb^\top E(s)\,ds+o(a^2).
\]
With \(\rho=e^{-t}\), the two off-diagonal entries are
\[
(J_a(t))_{12}=-a^2\rho(1-\rho^3)+o(a^2),\qquad
(J_a(t))_{21}=-3a^2\rho^2(1-\rho)+o(a^2).
\]
Their difference is \(-a^2\rho(1-\rho)^3+o(a^2)\). Since \(0<\rho<1\), the Jacobian is asymmetric for sufficiently small nonzero \(a\). Taking \(t=\tau\) rules out \(T_\tau=\operatorname{prox}_{r_\tau}\) for any proper lower-semicontinuous convex \(r_\tau\).

## Deployment description

Each block advances the gradient flow of \(f\) by time \(\tau\). A stack of \(n\) blocks implements the exact flow at time \(n\tau\), contracts distances between inputs by a factor of at most \(e^{-n\tau}\), and reduces the energy to at most \(e^{-2n\tau}f(Z_0)\). Every stack trajectory converges to the origin. The parameter \(\tau\) specifies elapsed flow time. In the stated proximal convention, the squared-distance coefficient is fixed at \(1/2\). A proximal update of \(f\) with step size \(\tau\) would be \(\operatorname{prox}_{\tau f}\), which solves the implicit-Euler equation \(u+\tau\nabla f(u)=z\).