## Mathematical appendix

Let \(g(z)=\nabla f(z)\) and \(s=x+y\). Then

\[
g(x,y)=\nabla f(x,y)
=\begin{pmatrix}x+s^3\\[2mm]2y+s^3\end{pmatrix},
\]

and

\[
\nabla^2 f(x,y)
=
\begin{pmatrix}
1+3s^2 & 3s^2\\
3s^2 & 2+3s^2
\end{pmatrix}.
\]

For every \(v=(a,b)\in\mathbb R^2\),

\[
v^T\nabla^2 f(x,y)v
=a^2+2b^2+3s^2(a+b)^2
\ge a^2+b^2.
\]

Therefore \(f\) is \(C^\infty\), coercive, and \(1\)-strongly convex.

### 1. Continuous flow: well-posedness, contraction, and dissipation

#### 1.1 Global well-posedness and equilibrium

Because \(g\) is \(C^\infty\), local solutions of

\[
\dot z=-g(z)
\]

exist and are unique. Along a trajectory,

\[
\frac{d}{dt}f(z(t))
=
-g(z(t))\cdot \dot z(t)
=
-\|g(z(t))\|^2\le 0.
\]

Thus \(z(t)\) remains in the sublevel set \(\{z:f(z)\le f(z(0))\}\), which is compact because \(f\) is coercive. Since \(g\) is locally Lipschitz and bounded on that compact set, the local solution cannot blow up in finite time. Hence \(\Phi_t(z)\) exists uniquely for every \(z\in\mathbb R^2\) and every \(t\ge0\), and

\[
\Phi_{t+s}=\Phi_t\circ\Phi_s.
\]

The equilibrium is unique. Indeed, \(g(0)=0\), and \(f\ge0\) with \(f(0)=0\), so \(0\) is the global minimizer. Alternatively, if \(g(z)=0\), strong monotonicity gives

\[
0=\langle g(z)-g(0),z-0\rangle\ge \|z\|^2,
\]

so \(z=0\). Thus

\[
\boxed{\text{the unique equilibrium is }(x,y)=(0,0).}
\]

#### 1.2 Contraction

Let \(z(t)=\Phi_t(z)\) and \(w(t)=\Phi_t(w)\). Then

\[
\frac12\frac{d}{dt}\|z(t)-w(t)\|^2
=
-\langle z-w,g(z)-g(w)\rangle
\le -\|z-w\|^2,
\]

where the inequality is strong monotonicity. Hence

\[
\|z(t)-w(t)\|^2\le e^{-2t}\|z-w\|^2,
\]

or

\[
\boxed{
\|\Phi_t(z)-\Phi_t(w)\|
\le e^{-t}\|z-w\|,
\qquad t\ge0.
}
\]

In particular, taking \(w=0\),

\[
\|\Phi_t(z)\|\le e^{-t}\|z\|.
\]

#### 1.3 Energy decay

Strong convexity gives, for all \(z,w\),

\[
f(w)\ge f(z)+\langle g(z),w-z\rangle+\frac12\|w-z\|^2.
\]

Take \(w=z-g(z)\). Since \(f\ge0\),

\[
0\le f(z-g(z))
\ge f(z)-\frac12\|g(z)\|^2,
\]

so

\[
\|g(z)\|^2\ge 2f(z).
\]

Therefore

\[
\frac{d}{dt}f(\Phi_t(z))
=
-\|g(\Phi_t(z))\|^2
\le -2f(\Phi_t(z)),
\]

and Gronwall's inequality yields

\[
\boxed{
f(\Phi_t(z))\le e^{-2t}f(z).
}
\]

#### 1.4 Stacked blocks

Since \(T_\tau=\Phi_\tau\),

\[
Z_n=T_\tau^n(Z_0)=\Phi_{n\tau}(Z_0).
\]

Using \(\Phi_t(0)=0\),

\[
\boxed{
\|Z_n\|\le e^{-n\tau}\|Z_0\|,
}
\]

and

\[
\boxed{
f(Z_n)\le e^{-2n\tau}f(Z_0).
}
\]

Thus the stack converges exponentially to the unique equilibrium \(0\). If one wants \(\|Z_n\|\le\varepsilon\), it suffices that

\[
n\ge \frac1\tau\log\frac{\|Z_0\|}{\varepsilon}.
\]

If one wants \(f(Z_n)\le\varepsilon_f\), it suffices that

\[
n\ge \frac{1}{2\tau}\log\frac{f(Z_0)}{\varepsilon_f}.
\]

These estimates are exact for the exact flow map; they contain no time-discretization error.

---

### 2. Conditional proximal certificate

Let \(r:\mathbb R^2\to(-\infty,+\infty]\) be proper, lower-semicontinuous, and convex, and suppose

\[
T(z)=\operatorname{prox}_r(z)
=
\arg\min_u\left\{r(u)+\frac12\|u-z\|^2\right\}.
\]

Set \(p=T(z)\). The first-order optimality condition for the prox minimization is

\[
0\in \partial r(p)+p-z,
\]

equivalently,

\[
z-p\in\partial r(p).
\]

By convexity of \(r\), for every \(u\in\operatorname{dom}r\),

\[
r(u)\ge r(p)+\langle z-p,u-p\rangle.
\]

Therefore

\[
\begin{aligned}
r(u)+\frac12\|u-z\|^2
&\ge
r(p)+\langle z-p,u-p\rangle+\frac12\|u-z\|^2\\
&=
r(p)+\frac12\|p-z\|^2+\frac12\|u-p\|^2.
\end{aligned}
\]

Hence the standard proximal certificate holds:

\[
\boxed{
r(p)+\frac12\|p-z\|^2+\frac12\|u-p\|^2
\le
r(u)+\frac12\|u-z\|^2
}
\]

for all \(u\in\operatorname{dom}r\).

Now put \(p=T(z)\), \(q=T(w)\), and apply the certificate twice: once to \((z,p)\) with \(u=q\), and once to \((w,q)\) with \(u=p\). Adding the resulting inequalities gives

\[
\|p-q\|^2
\le
\frac12\left(
\|q-z\|^2+\|p-w\|^2-\|p-z\|^2-\|q-w\|^2
\right).
\]

The right-hand side equals \(\langle q-p,w-z\rangle\), so

\[
\|p-q\|^2\le \langle q-p,w-z\rangle
=
\langle p-q,z-w\rangle.
\]

Equivalently,

\[
\boxed{
\langle T(z)-T(w),z-w\rangle
\ge
\|T(z)-T(w)\|^2.
}
\]

Thus \(T\) is firmly nonexpansive. By Cauchy–Schwarz,

\[
\boxed{
\|T(z)-T(w)\|\le \|z-w\|.
}
\]

Equivalently,

\[
\|T(z)-T(w)\|^2
+
\|(I-T)(z)-(I-T)(w)\|^2
\le
\|z-w\|^2.
\]

#### Important caveat: this certificate is conditional

The above argument proves only:

\[
T=\operatorname{prox}_r\text{ for convex }r
\quad\Longrightarrow\quad
T\text{ satisfies the certificate and is firmly nonexpansive.}
\]

It does **not** prove that a strongly convex gradient flow map is a proximal map. In fact, the statement in the draft that \(T_\tau=\Phi_\tau\) admits a convex proximal representation for every \(\tau>0\) is false for the present \(f\).

For example, take \(z_0=(0,1)\), and let \(J_\tau=D\Phi_\tau(z_0)\). The Jacobian solves the variational equation

\[
\dot J_\tau=-H(\Phi_\tau(z_0))J_\tau,
\qquad J_0=I.
\]

At \(z_0=(0,1)\),

\[
H(z_0)=
\begin{pmatrix}4&3\\3&5\end{pmatrix},
\qquad
\dot H(0)
=
-24
\begin{pmatrix}1&1\\1&1\end{pmatrix}
+O(t^2).
\]

A direct Taylor expansion of the variational equation gives

\[
(J_\tau)_{12}-(J_\tau)_{21}
=
-4\tau^3+O(\tau^4).
\]

Thus, for every sufficiently small \(\tau>0\), \(D\Phi_\tau(z_0)\) is not symmetric.

If \(\Phi_\tau=\operatorname{prox}_r\) for a convex \(r\), then \(\Phi_\tau\) is a \(C^\infty\) diffeomorphism onto its open range, and

\[
p\mapsto \Phi_\tau^{-1}(p)-p
\]

is a continuous selection of \(\partial r(p)\). Convexity then forces this selection to equal \(\nabla r(p)\) on the open range, so its Jacobian \(J_\tau^{-1}-I\) must be symmetric. This would force \(J_\tau\) itself to be symmetric, a contradiction.

Therefore the exact flow block is not, in general, an exact convex proximal step. The correct conclusion from strong convexity is contraction and energy dissipation, not proximal representability.

---

### 3. Deployment description

Each deployed block is the exact autonomous continuous-flow map

\[
T_\tau=\Phi_\tau,
\qquad
\dot z=-\nabla f(z),
\qquad
f(x,y)=\frac{x^2+2y^2}{2}+\frac{(x+y)^4}{4},
\]

where \(\tau>0\) is the physical evolution time. For all \(z,w\in\mathbb R^2\),

\[
\|T_\tau(z)-T_\tau(w)\|\le e^{-\tau}\|z-w\|,
\]

and

\[
f(T_\tau(z))\le e^{-2\tau}f(z).
\]

Stacking \(n\) identical blocks gives the exact flow at horizon \(n\tau\):

\[
Z_n=T_\tau^n(Z_0)=\Phi_{n\tau}(Z_0),
\]

so

\[
\|Z_n\|\le e^{-n\tau}\|Z_0\|,
\qquad
f(Z_n)\le e^{-2n\tau}f(Z_0).
\]

Hence the stack converges exponentially to the unique equilibrium \((0,0)\), with bounded sensitivity to perturbations and monotone energy dissipation.

The coefficient in

\[
\operatorname{prox}_r(z)
=
\arg\min_u\left\{r(u)+\frac12\|u-z\|^2\right\}
\]

is fixed at \(1/2\); it is not the evolution time \(\tau\). If one uses the common notation \(\operatorname{prox}_{\eta r}(z)=\arg\min_u\{\eta r(u)+\frac12\|u-z\|^2\}\), then \(\eta\) is a separate proximal-step coefficient. In particular, \(\operatorname{prox}_{\eta f}\) is the backward-Euler map with step \(\eta\), not the exact flow map \(\Phi_\eta\). Therefore the deployed block should be described as an exact continuous-flow contraction/dissipation step, not as an exact convex regularization step, unless a proximal representation is separately proved. For the present \(f\), the draft’s universal proximal-representation claim is false.