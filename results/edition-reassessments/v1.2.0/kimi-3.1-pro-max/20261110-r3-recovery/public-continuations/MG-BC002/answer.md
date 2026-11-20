## Mathematical appendix

### 1. The exact gradient-flow block

Let \(s=x+y\). Then
\[
\nabla f(x,y)=
\begin{pmatrix}
x+s^3\\
2y+s^3
\end{pmatrix},
\qquad
\nabla^2f(x,y)=
\begin{pmatrix}1&0\\0&2\end{pmatrix}
+3s^2\begin{pmatrix}1&1\\1&1\end{pmatrix}.
\]
The second matrix is positive semidefinite, so
\[
\nabla^2f(z)\succeq I\qquad(z\in\mathbb R^2).
\]
Thus \(f\) is \(1\)-strongly convex. It is also coercive, since
\[
f(x,y)\ge \frac{x^2+2y^2}{2}\ge \frac12\|(x,y)\|^2,
\qquad f(0)=0.
\]

#### Forward global well-posedness and equilibrium

Because \(\nabla f\) is smooth, it is locally Lipschitz, which gives local existence and uniqueness. Along any forward solution \(z(t)\),
\[
\frac{d}{dt}f(z(t))
=\langle\nabla f(z(t)),\dot z(t)\rangle
=-\|\nabla f(z(t))\|^2\le0.
\]
Consequently,
\[
\|z(t)\|^2\le 2f(z(t))\le 2f(z(0)).
\]
The solution therefore remains in a compact sublevel set and cannot blow up in finite forward time. Hence there is a unique solution on \([0,\infty)\) for every initial state. Its flow satisfies
\[
\Phi_0=\mathrm{id},\qquad
\Phi_{t+s}=\Phi_t\circ\Phi_s\qquad(t,s\ge0).
\]

The only equilibrium is \(z^*=0\). Indeed, \(\nabla f(x,y)=0\) gives
\[
x=-s^3,\qquad y=-\frac12s^3,
\]
and hence
\[
s=x+y=-\frac32s^3.
\]
Thus \(s(1+\frac32s^2)=0\), forcing \(s=0\), and therefore \(x=y=0\).

#### Contraction

Fix \(z,w\), and put
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
=-\int_0^1d(t)^{\mathsf T}\nabla^2f(b+\theta d)d(t)\,d\theta
\le-\|d(t)\|^2.
\]
Grönwall’s inequality therefore yields
\[
\boxed{\|\Phi_t(z)-\Phi_t(w)\|\le e^{-t}\|z-w\|\qquad(t\ge0).}
\]
Taking \(w=0\) also gives
\[
\|\Phi_t(z)\|\le e^{-t}\|z\|.
\]

#### Energy decay

Strong convexity with modulus \(1\), together with \(\nabla f(0)=0\), implies
\[
0=f(0)\ge f(\zeta)-\langle\nabla f(\zeta),\zeta\rangle
+\frac12\|\zeta\|^2.
\]
Therefore
\[
f(\zeta)
\le\langle\nabla f(\zeta),\zeta\rangle-\frac12\|\zeta\|^2
\le\frac12\|\nabla f(\zeta)\|^2,
\]
where the last inequality follows from
\(\frac12\|\nabla f(\zeta)-\zeta\|^2\ge0\). Hence
\[
2f(\zeta)\le\|\nabla f(\zeta)\|^2.
\]
Along \(z(t)=\Phi_t(z)\), this gives
\[
\frac{d}{dt}f(z(t))
=-\|\nabla f(z(t))\|^2
\le-2f(z(t)),
\]
and consequently
\[
\boxed{f(\Phi_t(z))\le e^{-2t}f(z)\qquad(t\ge0).}
\]

For \(T_\tau=\Phi_\tau\), the semigroup property gives \(T_\tau^n=\Phi_{n\tau}\). Thus, for \(Z_n=T_\tau^n(Z_0)\),
\[
\boxed{
\|Z_n\|\le e^{-n\tau}\|Z_0\|,\qquad
f(Z_n)\le e^{-2n\tau}f(Z_0).
}
\]
For two initial states,
\[
\boxed{
\|T_\tau^n(Z_0)-T_\tau^n(W_0)\|
\le e^{-n\tau}\|Z_0-W_0\|.
}
\]
In particular, every stack converges exponentially to the unique equilibrium \(0\).

### 2. Proximal certificate and firm nonexpansiveness

This subsection first concerns any map \(T\) for which a representation
\[
T=\operatorname{prox}_r
\]
is **assumed**, with \(r\) proper, lower-semicontinuous, and convex.

For fixed \(z\), define
\[
F_z(u)=r(u)+\frac12\|u-z\|^2.
\]
This objective is proper, lower-semicontinuous, and strongly convex, so it has a unique minimizer \(p=T(z)\). Since the quadratic term is continuous and convex, first-order optimality gives
\[
0\in\partial F_z(p)=\partial r(p)+p-z,
\]
or equivalently
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
Combining these relations cancels the inner-product terms and yields the requested certificate:
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
\left\langle(z-p)-(w-q),p-q\right\rangle\ge0.
\]
Equivalently,
\[
\boxed{
\langle T(z)-T(w),z-w\rangle
\ge\|T(z)-T(w)\|^2.
}
\]
This is firm nonexpansiveness. Cauchy–Schwarz then implies
\[
\|T(z)-T(w)\|\le\|z-w\|.
\]
An equivalent residual form is
\[
\boxed{
\|T(z)-T(w)\|^2
+\|(z-T(z))-(w-T(w))\|^2
\le\|z-w\|^2.
}
\]

#### Additional check: the present flow has no such proximal representation

For this particular \(f\), the draft’s proximal assertion is not merely unjustified: it is false for every \(\tau>0\).

To see this, first recall the Moreau-envelope identity. If \(T=\operatorname{prox}_r\), define
\[
M_r(z)=\inf_u\left\{r(u)+\frac12\|u-z\|^2\right\}.
\]
Under the stated proper-lsc-convex assumptions, \(M_r\) is differentiable and
\[
\nabla M_r(z)=z-T(z).
\]
Moreover,
\[
h(z):=\frac12\|z\|^2-M_r(z)
=\sup_u\left\{\langle z,u\rangle-r(u)-\frac12\|u\|^2\right\}
\]
is convex, and \(\nabla h=T\). Thus every proximal map is the gradient of a convex function. If such a map is smooth, its Jacobian must therefore be symmetric.

We now show that \(D\Phi_t\) fails this necessary condition for every \(t>0\). Write
\[
\Phi_t(x,y)=(X_t(x,y),Y_t(x,y)).
\]
The ODE has the form
\[
\dot z=-Az-(x+y)^3
\begin{pmatrix}1\\1\end{pmatrix},
\qquad A=\begin{pmatrix}1&0\\0&2\end{pmatrix}.
\]
Duhamel’s formula, using
\[
s(u)=e^{-u}x+e^{-2u}y+O(\|(x,y)\|^3),
\]
gives the fixed-\(t\) expansions
\[
X_t=e^{-t}x-\int_0^t e^{-(t-u)}
(e^{-u}x+e^{-2u}y)^3\,du+O(\|(x,y)\|^5),
\]
\[
Y_t=e^{-2t}y-\int_0^t e^{-2(t-u)}
(e^{-u}x+e^{-2u}y)^3\,du+O(\|(x,y)\|^5).
\]
Consequently, with
\[
a_t=\int_0^t e^{-3u}\,du=\frac{1-e^{-3t}}3,
\qquad
b_t=\int_0^t e^{-u}\,du=1-e^{-t},
\]
the relevant third derivatives at the origin are
\[
X_{t,xxy}(0)=-6e^{-t}a_t,\qquad
Y_{t,xxx}(0)=-6e^{-2t}b_t.
\]
If \(D\Phi_t\) were symmetric near the origin, then
\[
X_{t,y}=Y_{t,x},
\]
and differentiating twice in \(x\) would imply
\[
e^{-t}a_t=e^{-2t}b_t.
\]
But, putting \(q=e^{-t}\),
\[
a_t-qb_t
=\frac{1-q^3}{3}-q(1-q)
=\frac{(1-q)^3}{3}>0
\qquad(0<q<1).
\]
This is impossible for every \(t>0\). Hence
\[
\boxed{\Phi_\tau\neq\operatorname{prox}_r
\quad\text{for every }\tau>0
\text{ and every proper lsc convex }r.}
\]

## Short deployment description

Each deployed block evolves the state exactly under \(\dot z=-\nabla f(z)\) for elapsed time \(\tau\); it is not the implicit-Euler map \((I+\tau\nabla f)^{-1}\). A block contracts pairwise distances by a factor at most \(e^{-\tau}\) and reduces \(f\) by a factor at most \(e^{-2\tau}\). Because \(n\) identical blocks equal \(\Phi_{n\tau}\), they guarantee \(\|Z_n\|\le e^{-n\tau}\|Z_0\|\) and \(f(Z_n)\le e^{-2n\tau}f(Z_0)\). Here \(\tau\) is the continuous evolution time, not the coefficient in the proximal convention, whose quadratic term remains \(\frac12\|u-z\|^2\). For this particular flow, no convex proximal representation exists for any \(\tau>0\), so the deployment should not be described as an exact convex regularization step.

### Revision status and self-assessment

- **Retained:** the complete well-posedness, equilibrium, contraction, energy-decay, stack-convergence, proximal-certificate, and firm-nonexpansiveness proofs.
- **Added/corrected:** a Jacobian/Moreau-envelope argument definitively rules out the claimed proximal representation for every \(\tau>0\); the deployment wording is updated accordingly.
- **Outstanding or uncertain:** none of the requested items remains unfinished; no closed-form ODE solution is needed.
- **Self-assessment:** B2 for the original requirements. The additional all-\(\tau>0\) non-representability theorem is a complete supplementary determination, consistent with R2 under the supplied scale.