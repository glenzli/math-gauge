**Appendix**

**1. Flow and convergence.** Let \(A=\operatorname{diag}(1,2)\) and \(b=(1,1)^\top\). Then
\[
\nabla f(z)=Az+(b^\top z)^3b,\qquad
\nabla^2 f(z)=A+3(b^\top z)^2bb^\top\succeq I.
\]
Thus \(f\) is \(1\)-strongly convex, and \(0\), where \(\nabla f(0)=0\), is its unique minimizer and the unique equilibrium. The smooth vector field gives a unique local solution. Along this solution,
\[
\frac{d}{dt}f(z_t)=-\|\nabla f(z_t)\|^2.
\]
Since \(f(z)\ge \|z\|^2/2\), each trajectory stays in a compact sublevel set. The ODE continuation theorem therefore gives global existence forward in time.

For \(z_t=\Phi_t(z)\) and \(w_t=\Phi_t(w)\), strong monotonicity of \(\nabla f\) gives
\[
\frac12\frac{d}{dt}\|z_t-w_t\|^2
=-\langle z_t-w_t,\nabla f(z_t)-\nabla f(w_t)\rangle
\le -\|z_t-w_t\|^2.
\]
Integration yields \(\|\Phi_t(z)-\Phi_t(w)\|\le e^{-t}\|z-w\|\). Strong convexity also gives
\[
f(z)\le \langle\nabla f(z),z\rangle-\tfrac12\|z\|^2
\le \tfrac12\|\nabla f(z)\|^2,
\]
where the first inequality uses \(f(0)=0\) and the second follows by completing the square. Hence \(\frac{d}{dt}f(z_t)\le -2f(z_t)\), so \(f(\Phi_t(z))\le e^{-2t}f(z)\). By the semigroup property, \(Z_n=\Phi_{n\tau}(Z_0)\), and therefore
\[
\|Z_n\|\le e^{-n\tau}\|Z_0\|,\qquad f(Z_n)\le e^{-2n\tau}f(Z_0).
\]

**2. Proximal certificate.** Suppose \(T=\operatorname{prox}_r\) for a proper lower-semicontinuous convex \(r\). Write \(F_z(u)=r(u)+\|u-z\|^2/2\) and \(p=T(z)\). Since \(p\) minimizes the \(1\)-strongly convex function \(F_z\), for \(u\in\operatorname{dom}r\) and \(0<\lambda<1\),
\[
F_z(p)\le F_z((1-\lambda)p+\lambda u)
\le (1-\lambda)F_z(p)+\lambda F_z(u)
-\tfrac12\lambda(1-\lambda)\|u-p\|^2.
\]
Subtract \(F_z(p)\), divide by \(\lambda\), and let \(\lambda\downarrow0\). This gives the claimed certificate:
\[
r(p)+\tfrac12\|p-z\|^2+\tfrac12\|u-p\|^2
\le r(u)+\tfrac12\|u-z\|^2.
\]
For \(q=T(w)\), apply the certificate with input \(z\) and competitor \(q\), then with input \(w\) and competitor \(p\). Adding and expanding gives firm nonexpansiveness:
\[
\|T(z)-T(w)\|^2\le \langle T(z)-T(w),z-w\rangle.
\]

**3. Why the exact flow is not proximal.** A \(C^1\) convex proximal map must have a symmetric Jacobian. Indeed, for such a representation define
\[
G(z)=\sup_u\{\langle z,u\rangle-r(u)-\tfrac12\|u\|^2\}.
\]
The maximizer is \(T(z)\). Comparing the maximizers at \(z\) and \(z+h\) gives
\[
\langle T(z),h\rangle\le G(z+h)-G(z)\le\langle T(z+h),h\rangle.
\]
Firm nonexpansiveness implies that \(T\) is \(1\)-Lipschitz, so these bounds give \(\nabla G=T\). If \(T\) is \(C^1\), its Jacobian is therefore the symmetric Hessian of \(G\).

Now fix any \(\tau>0\), put \(E_t=e^{-tA}\), and write \(z_\varepsilon(t)=\Phi_t((\varepsilon,0))\) and \(J_\varepsilon(t)=D\Phi_t((\varepsilon,0))\). Smooth dependence on initial data gives the variational equation
\[
\dot J_\varepsilon
=-\bigl(A+3(b^\top z_\varepsilon)^2bb^\top\bigr)J_\varepsilon,\qquad J_\varepsilon(0)=I.
\]
Contractivity bounds \(\|z_\varepsilon(t)\|\le |\varepsilon|e^{-t}\) and \(\|J_\varepsilon(t)\|\le e^{-t}\). Variation of constants in the state and variational equations then gives \(z_\varepsilon(t)=(\varepsilon e^{-t},0)^\top+O_\tau(\varepsilon^3)\) and \(J_\varepsilon(t)=E_t+O_\tau(\varepsilon^2)\), uniformly on \([0,\tau]\). Substituting these estimates back into the variational integral gives
\[
J_\varepsilon(\tau)=E_\tau
-3\varepsilon^2\int_0^\tau e^{-2s}E_{\tau-s}bb^\top E_s\,ds
+O_\tau(\varepsilon^4).
\]
The difference of its off-diagonal entries is
\[
(J_\varepsilon(\tau))_{12}-(J_\varepsilon(\tau))_{21}
=-3\varepsilon^2\int_0^\tau
\bigl(e^{-\tau-3s}-e^{-2\tau-s}\bigr)\,ds+O_\tau(\varepsilon^4)
=-\varepsilon^2 e^{-\tau}(1-e^{-\tau})^3+O_\tau(\varepsilon^4).
\]
For each fixed \(\tau>0\), this is nonzero for sufficiently small nonzero \(\varepsilon\). Thus **no positive-time block \(\Phi_\tau\) is a convex proximal map**, despite its contraction and energy dissipation.

**Deployment**

Each block advances the exact gradient flow by time \(\tau\). A stack of \(n\) blocks advances it by time \(n\tau\), contracts pairwise distances by at most \(e^{-n\tau}\), and reduces the energy to at most \(e^{-2n\tau}f(Z_0)\), yielding exponential convergence to \(0\). Here \(\tau\) is elapsed evolution time, not the coefficient of the squared distance in the proximal definition, which is fixed at \(1/2\). An implicit-Euler step of size \(\tau\) would instead be \(\operatorname{prox}_{\tau f}\), equivalently minimizing \(f(u)+\|u-z\|^2/(2\tau)\). The deployed block is the exact flow, not that regularization step.