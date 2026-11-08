# Mathematical appendix

The contraction and dissipation claims are correct. The proximal conclusion in the draft is not: for this energy, **for every fixed \(\tau>0\), the exact flow map \(\Phi_\tau\) is not the proximal map of any proper lower-semicontinuous convex function.** We establish the evolution guarantees, prove the conditional proximal certificate, and explain the obstruction.

## 1. Global flow and quantitative convergence

Write \(s=x+y\). Then
\[
\nabla f(x,y)=\begin{pmatrix}x+s^3\\2y+s^3\end{pmatrix},
\qquad
\nabla^2f(x,y)=
\begin{pmatrix}1&0\\0&2\end{pmatrix}
+3s^2\begin{pmatrix}1&1\\1&1\end{pmatrix}
\succeq I.
\]
Thus \(f\) is \(1\)-strongly convex, with \(f(z)\geq\|z\|^2/2\). Since \(\nabla f(0)=0\), its unique minimizer and the ODE's unique equilibrium are \(0\), and \(f(0)=0\).

The vector field \(-\nabla f\) is smooth and locally Lipschitz, so each initial state has a unique maximal local solution. Along any such solution,
\[
\frac{d}{dt}f(z(t))=-\|\nabla f(z(t))\|^2\leq0.
\]
The trajectory therefore stays in its initial compact energy sublevel set. A solution of a locally Lipschitz vector field that stays in a compact set cannot have a finite forward maximal time. Consequently \(\Phi_t(z)\) exists uniquely for every \(z\in\mathbb R^2\) and \(t\geq0\). The flow is smooth in the initial state and has the semigroup property.

Strong convexity gives strong monotonicity:
\[
\langle\nabla f(a)-\nabla f(b),a-b\rangle\geq\|a-b\|^2.
\]
For \(a(t)=\Phi_t(z)\) and \(b(t)=\Phi_t(w)\), it follows that
\[
\frac{d}{dt}\|a(t)-b(t)\|^2
=-2\langle\nabla f(a(t))-\nabla f(b(t)),a(t)-b(t)\rangle
\leq-2\|a(t)-b(t)\|^2.
\]
Hence
\[
\boxed{\|\Phi_t(z)-\Phi_t(w)\|\leq e^{-t}\|z-w\|.}
\]

The strong-convexity inequality also implies
\[
0=f(0)\geq f(z)-\langle\nabla f(z),z\rangle+\tfrac12\|z\|^2,
\]
and therefore
\[
f(z)\leq\langle\nabla f(z),z\rangle-\tfrac12\|z\|^2
\leq\tfrac12\|\nabla f(z)\|^2.
\]
Combining this with the energy identity yields
\[
\boxed{f(\Phi_t(z))\leq e^{-2t}f(z).}
\]
In addition, the exact dissipation identity is
\[
f(\Phi_t(z))+\int_0^t\|\nabla f(\Phi_s(z))\|^2\,ds=f(z).
\]

For a stack of identical blocks, uniqueness and autonomy give
\[
T_\tau^n=\Phi_{n\tau}.
\]
In particular, with \(Z_n=T_\tau^n(Z_0)\),
\[
\boxed{\|Z_n\|\leq e^{-n\tau}\|Z_0\|,\qquad
f(Z_n)\leq e^{-2n\tau}f(Z_0).}
\]
Two stacks started at \(Z_0,W_0\) satisfy
\[
\|Z_n-W_n\|\leq e^{-n\tau}\|Z_0-W_0\|.
\]
For example, if \(\|Z_0\|>\varepsilon>0\), then
\(n\geq\lceil\tau^{-1}\log(\|Z_0\|/\varepsilon)\rceil\)
suffices for \(\|Z_n\|\leq\varepsilon\). These are deterministic, pointwise guarantees, so they also apply to each realization of a random initial state.

## 2. The conditional proximal certificate

Let \(r:\mathbb R^2\to(-\infty,+\infty]\) be proper, lower-semicontinuous and convex. For each \(z\), the function
\[
u\longmapsto r(u)+\tfrac12\|u-z\|^2
\]
is proper, lower-semicontinuous and strongly convex, and is coercive because a proper closed convex function has an affine minorant. It therefore has a unique minimizer \(p=\operatorname{prox}_r(z)\).

Its optimality condition is
\[
z-p\in\partial r(p).
\]
Thus, for every \(u\in\operatorname{dom}r\),
\[
r(u)\geq r(p)+\langle z-p,u-p\rangle.
\]
Using
\[
\tfrac12\|u-z\|^2
=\tfrac12\|u-p\|^2+\tfrac12\|p-z\|^2
+\langle u-p,p-z\rangle,
\]
we obtain the claimed certificate:
\[
\boxed{
r(p)+\tfrac12\|p-z\|^2+\tfrac12\|u-p\|^2
\leq r(u)+\tfrac12\|u-z\|^2.
}
\]

For firm nonexpansiveness, put \(p=\operatorname{prox}_r(z)\) and \(q=\operatorname{prox}_r(w)\). Monotonicity of \(\partial r\) gives
\[
0\leq\langle(z-p)-(w-q),p-q\rangle,
\]
so
\[
\boxed{\|p-q\|^2\leq\langle p-q,z-w\rangle.}
\]
Equivalently,
\[
\|p-q\|^2+\|(z-p)-(w-q)\|^2\leq\|z-w\|^2.
\]
These statements hold under the proximal representation; they do not establish that such a representation exists for a given flow.

## 3. Why the exact flow is not a convex proximal map

A necessary property of any convex proximal map is that it is a gradient field. Indeed, define
\[
h(u)=r(u)+\tfrac12\|u\|^2,
\qquad
\psi(z)=h^*(z)=\sup_u\{\langle z,u\rangle-h(u)\}.
\]
The supremum is attained uniquely at \(\operatorname{prox}_r(z)\). To see differentiability directly, write \(p(z)=\operatorname{prox}_r(z)\). The maximizing inequalities imply
\[
\langle p(z),v\rangle
\leq\psi(z+v)-\psi(z)
\leq\langle p(z+v),v\rangle.
\]
Firm nonexpansiveness implies that \(p\) is \(1\)-Lipschitz, so the difference between either bound and \(\langle p(z),v\rangle\) is at most \(\|v\|^2\). Therefore \(\nabla\psi=p\). In particular, if a proximal map is \(C^1\), its Jacobian is symmetric everywhere.

We now show that \(D\Phi_t\) is not symmetric for any fixed \(t>0\). Let
\[
A=\operatorname{diag}(1,2),\qquad
B=\begin{pmatrix}1&1\\1&1\end{pmatrix},\qquad
E(s)=e^{-As}.
\]
Consider the trajectory \(z_a(s)=\Phi_s(a,0)\). Smooth dependence on initial conditions, the cubic nonlinearity, and oddness of the vector field give, uniformly on \([0,t]\),
\[
z_a(s)=a(e^{-s},0)+O(a^3).
\]
Consequently \((x_a(s)+y_a(s))^2=a^2e^{-2s}+O(a^4)\).

The initial-state Jacobian \(J_a(s)=D\Phi_s(a,0)\) solves
\[
\dot J_a(s)=-\bigl[A+3(x_a(s)+y_a(s))^2B\bigr]J_a(s),
\qquad J_a(0)=I.
\]
Variation of constants, or its Taylor expansion at \(a=0\), gives
\[
J_a(t)=E(t)-3a^2\int_0^tE(t-s)e^{-2s}BE(s)\,ds+O(a^4).
\]
Here the remainders are for fixed \(t\), and the expansion is justified by the smooth variational equation. Its off-diagonal entries are
\[
(J_a(t))_{12}=-a^2e^{-t}(1-e^{-3t})+O(a^4),
\]
\[
(J_a(t))_{21}=-3a^2e^{-2t}(1-e^{-t})+O(a^4).
\]
Subtracting,
\[
\boxed{
(J_a(t))_{12}-(J_a(t))_{21}
=-a^2e^{-t}(1-e^{-t})^3+O(a^4).
}
\]
For every fixed \(t>0\), the coefficient of \(a^2\) is strictly negative. Thus the Jacobian is nonsymmetric at \((a,0)\) for all sufficiently small nonzero \(a\). This rules out a convex proximal representation of \(\Phi_t\).

Although the instantaneous vector field is a negative gradient, its finite-time flow map need not itself be a gradient map. Strong convexity, contraction and energy dissipation do not bridge that gap.

# Deployment paragraph

Each block implements the exact time-\(\tau\) evolution of \(\dot z=-\nabla f(z)\). It is globally defined, contracts differences between inputs by at least the factor \(e^{-\tau}\), and reduces the energy by at least the factor \(e^{-2\tau}\). A depth-\(n\) stack is exactly the time-\(n\tau\) flow, with the corresponding exponential stability and convergence bounds toward the unique equilibrium \(0\). These are stability and energy-reduction guarantees, not a guarantee of recovery of an unknown clean signal; indefinitely stacking these autonomous blocks drives every input to zero. The parameter \(\tau\) is elapsed evolution time, whereas the proximal convention here fixes the quadratic fidelity coefficient at \(1/2\). For comparison, an implicit-Euler step of size \(\tau\) would be \(\operatorname{prox}_{\tau f}\), equivalently minimizing \(f(u)+\|u-z\|^2/(2\tau)\). The deployed exact-flow block is different and, for this energy, admits no convex proximal representation for any \(\tau>0\).
