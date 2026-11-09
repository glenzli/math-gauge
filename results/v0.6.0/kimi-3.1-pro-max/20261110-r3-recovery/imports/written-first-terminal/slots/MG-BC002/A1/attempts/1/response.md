## Mathematical appendix

### 1. The exact gradient-flow block

Writing \(s=x+y\), we have
\[
\nabla f(x,y)=
\begin{pmatrix}
x+s^3\\
2y+s^3
\end{pmatrix},
\qquad
\nabla^2 f(x,y)=
\begin{pmatrix}1&0\\0&2\end{pmatrix}
+3s^2\begin{pmatrix}1&1\\1&1\end{pmatrix}.
\]
The second matrix is positive semidefinite, so
\[
\nabla^2 f(z)\succeq I\qquad(z\in\mathbb R^2).
\]
Thus \(f\) is \(1\)-strongly convex. It is also coercive, since
\[
f(x,y)\ge \frac{x^2+2y^2}{2}\ge \frac12\|(x,y)\|^2,
\qquad f(0)=0.
\]

**Forward global well-posedness.** Because \(\nabla f\) is smooth, it is locally Lipschitz, giving local existence and uniqueness. Along any forward solution \(z(t)\),
\[
\frac{d}{dt}f(z(t))
=\langle \nabla f(z(t)),\dot z(t)\rangle
=-\|\nabla f(z(t))\|^2\le0.
\]
Consequently,
\[
\|z(t)\|^2\le 2f(z(t))\le 2f(z(0)),
\]
so the solution remains in a compact sublevel set and cannot blow up in finite forward time. Hence there is a unique solution on \([0,\infty)\) for every initial state. Its flow satisfies
\[
\Phi_0=\mathrm{id},\qquad \Phi_{t+s}=\Phi_t\circ\Phi_s
\quad(t,s\ge0).
\]

The only equilibrium is \(z^*=0\). Indeed, setting \(s=x+y\), the equations \(\nabla f=0\) give \(x=-s^3\) and \(y=-s^3/2\), hence
\[
s=x+y=-\frac32s^3,
\]
which forces \(s=0\), and therefore \(x=y=0\).

**Contraction.** Fix \(z,w\), and put
\[
a(t)=\Phi_t(z),\qquad b(t)=\Phi_t(w),\qquad d(t)=a(t)-b(t).
\]
By the fundamental theorem of calculus,
\[
\dot d(t)
=-\left(\int_0^1\nabla^2f\bigl(b(t)+\theta d(t)\bigr)\,d\theta\right)d(t).
\]
Using \(\nabla^2f\succeq I\),
\[
\frac12\frac{d}{dt}\|d(t)\|^2
=-\int_0^1 d(t)^{\mathsf T}\nabla^2f(b+\theta d)d(t)\,d\theta
\le-\|d(t)\|^2.
\]
Grönwall’s inequality therefore yields
\[
\boxed{\ \|\Phi_t(z)-\Phi_t(w)\|\le e^{-t}\|z-w\|\ }.
\]
In particular, taking \(w=0\) gives \(\|\Phi_t(z)\|\le e^{-t}\|z\|\). This also proves continuous dependence on the initial state.

**Energy decay.** Strong convexity with modulus \(1\), together with \(\nabla f(0)=0\), implies
\[
0=f(0)\ge f(\zeta)-\langle\nabla f(\zeta),\zeta\rangle
+\frac12\|\zeta\|^2.
\]
Thus
\[
f(\zeta)
\le \langle\nabla f(\zeta),\zeta\rangle-\frac12\|\zeta\|^2
\le\frac12\|\nabla f(\zeta)\|^2,
\]
where the last step follows from
\(\frac12\|\nabla f(\zeta)-\zeta\|^2\ge0\). Hence
\(2f\le\|\nabla f\|^2\), and along \(z(t)=\Phi_t(z)\),
\[
\frac{d}{dt}f(z(t))=-\|\nabla f(z(t))\|^2\le-2f(z(t)).
\]
Therefore
\[
\boxed{\ f(\Phi_t(z))\le e^{-2t}f(z)\ }.
\]

For \(T_\tau=\Phi_\tau\), the semigroup property gives
\(T_\tau^n=\Phi_{n\tau}\). Consequently, for \(Z_n=T_\tau^n(Z_0)\),
\[
\boxed{
\|Z_n\|\le e^{-n\tau}\|Z_0\|,\qquad
f(Z_n)\le e^{-2n\tau}f(Z_0)
}
\]
and, for two initial states,
\[
\|T_\tau^n(Z_0)-T_\tau^n(W_0)\|
\le e^{-n\tau}\|Z_0-W_0\|.
\]
Thus every stack converges exponentially to the unique equilibrium \(0\), with energy decaying at rate \(e^{-2n\tau}\).

### 2. Conditional proximal certificate and firm nonexpansiveness

This subsection concerns any map \(T\) for which a representation \(T=\operatorname{prox}_r\) is **assumed**, with \(r\) proper, lower-semicontinuous, and convex. It does not by itself establish such a representation for \(\Phi_\tau\).

For fixed \(z\), define
\[
F_z(u)=r(u)+\frac12\|u-z\|^2.
\]
This objective is strongly convex and has a unique minimizer \(p=T(z)\). First-order optimality gives
\[
z-p\in\partial r(p).
\]
Therefore, for every \(u\in\operatorname{dom}r\),
\[
r(u)\ge r(p)+\langle z-p,u-p\rangle.
\]
Also,
\[
\frac12\|u-z\|^2
=\frac12\|p-z\|^2+\frac12\|u-p\|^2
+\langle p-z,u-p\rangle.
\]
Combining these identities and inequalities cancels the inner-product terms and yields the requested certificate:
\[
\boxed{
r(p)+\frac12\|p-z\|^2+\frac12\|u-p\|^2
\le r(u)+\frac12\|u-z\|^2.
}
\]

For firm nonexpansiveness, let \(p=T(z)\) and \(q=T(w)\). Since
\[
z-p\in\partial r(p),\qquad w-q\in\partial r(q),
\]
monotonicity of the subdifferential gives
\[
\left\langle (z-p)-(w-q),p-q\right\rangle\ge0.
\]
Equivalently,
\[
\boxed{
\langle T(z)-T(w),z-w\rangle
\ge \|T(z)-T(w)\|^2.
}
\]
This is firm nonexpansiveness. Cauchy–Schwarz then implies
\[
\|T(z)-T(w)\|\le\|z-w\|.
\]
An equivalent residual form is
\[
\|T(z)-T(w)\|^2
+\|(z-T(z))-(w-T(w))\|^2
\le\|z-w\|^2.
\]

## Deployment description

Each deployed block evolves the state exactly under \(\dot z=-\nabla f(z)\) for time \(\tau\); it is not the implicit-Euler map \((I+\tau\nabla f)^{-1}\). A block contracts pairwise distances by at most \(e^{-\tau}\), reduces \(f\) by at most \(e^{-2\tau}\), and \(n\) identical blocks equal \(\Phi_{n\tau}\), giving \(\|Z_n\|\le e^{-n\tau}\|Z_0\|\) and \(f(Z_n)\le e^{-2n\tau}f(Z_0)\). Here \(\tau\) is the continuous evolution time, not the quadratic coefficient in the proximal convention: even if a representation \(T_\tau=\operatorname{prox}_{r_\tau}\) were independently established, its objective would still be \(r_\tau(u)+\frac12\|u-z\|^2\). Strong convexity and dissipativity alone do not imply that such a representation exists, so the unconditional deployment guarantee is exact gradient-flow contraction and energy decay, while the proximal certificate and firm nonexpansiveness apply only conditionally on a separately proven proximal representation.