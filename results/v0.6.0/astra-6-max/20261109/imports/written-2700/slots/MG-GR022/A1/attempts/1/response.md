记 \(v=v_t\)，约定 \(v(0)=+\infty\)、\(S/(t^0)=0\)。对 \(c\in S/(t^\ell)\)，记 \(\widetilde c\) 为次数小于 \(\ell\) 的唯一多项式代表，并令 \(v(c)=v(\widetilde c)\)。特别地，零元的赋值为 \(+\infty\)。

定义
\[
\mathcal D=\left\{(a_n)\in\prod_{n\ge1}S:
\forall m\ge1,\ \#\{n:v(a_n)<m\}<\infty\right\},
\]
以及
\[
\mathcal T=\left\{(c_n)\in\prod_{n\ge1}S/(t^{\nu_n}):
\forall m\ge1,\ \#\{n:v(c_n)<m\}<\infty\right\}.
\]
这里的条件就是坐标在 \(t\) 进意义下趋于零。

先给出完成的坐标模型。自然地，
\[
\boxed{\widehat A\simeq\mathcal D,\qquad
\widehat B\simeq\mathcal D,\qquad
\widehat C\simeq\mathcal T.}
\]
事实上，各层商分别为
\[
A/t^mA\simeq B/t^mB\simeq\bigoplus_nS/(t^m),\qquad
C/t^mC\simeq\bigoplus_nS/(t^{\min(m,\nu_n)}).
\]
上述同构把坐标序列送到相容记录
\[
(a_n)\longmapsto\bigl((a_n\bmod t^m)_n\bigr)_{m\ge1},
\]
\[
(c_n)\longmapsto
\bigl((c_n\bmod t^{\min(m,\nu_n)})_n\bigr)_{m\ge1}.
\]
反过来，相容记录在每个坐标上分别确定一个 \(S\) 中的元素或一个 \(S/(t^{\nu_n})\) 中的元素；每层记录具有有限支撑，恰好给出定义 \(\mathcal D,\mathcal T\) 的条件。这证明了同构及其双向构造。所有 \(S\) 作用均为逐坐标作用。

典范映射 \(\eta_A,\eta_B,\eta_C\) 都是把原来的有限支撑坐标放入这些模型，因而均为单射。诱导映射为
\[
\widehat\iota(a_n)=(t^{\nu_n}a_n),\qquad
\widehat q(b_n)=(b_n\bmod t^{\nu_n}).
\]

为描述像与核，再定义
\[
\mathcal H=
\left\{(a_n)\in\prod_nS:
\forall m\ge1,\ \#\{n:\nu_n+v(a_n)<m\}<\infty\right\}.
\]
于是 \(\mathcal D\subseteq\mathcal H\)，并且
\[
I:=\operatorname{im}\widehat\iota
 =\{(t^{\nu_n}a_n):a\in\mathcal D\},
\]
\[
K:=\ker\widehat q
 =\{b\in\mathcal D:b_n\in t^{\nu_n}S\ \forall n\}
 =\{(t^{\nu_n}a_n):a\in\mathcal H\}.
\]

对任意 \(c=(c_n)\in\mathcal T\)，逐坐标取上述多项式代表，得到
\[
\sigma(c)=(\widetilde c_n)\in\mathcal D.
\]
因此 \(\widehat q\) 总是满射，而且它的每个纤维为
\[
\boxed{\widehat q^{-1}(c)
=\sigma(c)+K
=\left\{(\widetilde c_n+t^{\nu_n}a_n)_n:a\in\mathcal H\right\}.}
\]
这里 \(\sigma\) 只是选定的坐标提升，不声称它是 \(S\) 线性的。

由于 \(S\) 是整环，\(\widehat\iota\) 总是单射。另有
\[
\boxed{\overline{\operatorname{im}\widehat\iota}=K.}
\]
证明如下：
\[
t^m\mathcal D=\{b\in\mathcal D:b_n\in t^mS\ \forall n\},
\]
所以逐坐标条件 \(b_n\in t^{\nu_n}S\) 定义的 \(K\) 是闭的。而每个 \(b\in K\) 的有限坐标截断都属于 \(I\)，这些截断在 \(\mathcal D\) 的 \(t\) 进拓扑下收敛到 \(b\)。

像与核相等的条件恰好是指数列有界：
\[
\boxed{I=K\iff \mathcal H=\mathcal D
\iff \sup_n\nu_n<\infty.}
\]
若 \(\nu_n\le N\)，则
\[
\{n:v(a_n)<m\}\subseteq
\{n:\nu_n+v(a_n)<N+m\},
\]
故 \(\mathcal H\subseteq\mathcal D\)。若指数列无界，可取递增的指标 \(n_j\)，使 \(\nu_{n_j}\ge j\)，并令
\[
a_{n_j}=1,\qquad a_n=0\quad(n\notin\{n_j\}).
\]
此时 \(a\in\mathcal H\setminus\mathcal D\)。

因此，完成列总在左端和右端正合，而
\[
\boxed{
0\longrightarrow\widehat A
\xrightarrow{\widehat\iota}\widehat B
\xrightarrow{\widehat q}\widehat C
\longrightarrow0
\text{ 短正合}
\iff \sup_n\nu_n<\infty.}
\]

接下来考虑 \(Q,E,j\)。坐标模型给出
\[
Q=\mathcal D/I,\qquad
\boxed{E=K/I\simeq\mathcal H/\mathcal D,}
\]
其中最后的同构为
\[
a+\mathcal D\longmapsto (t^{\nu_n}a_n)_n+I.
\]
映射 \(p\) 是逐坐标约化，始终满射；其纤维是
\[
p^{-1}(c)=(\sigma(c)+I)+E.
\]
特别地，
\[
\boxed{E=0\iff\sup_n\nu_n<\infty.}
\]

\(E\) 始终是无挠 \(S\)-模。事实上，若 \(0\ne s=t^ru\in S\)，其中 \(u\) 为单位，则
\[
sa\in\mathcal D\Longrightarrow a\in\mathcal D
\]
直接由 \(v(sa_n)=r+v(a_n)\) 得到。因此
\[
\operatorname{Tor}_S(E)=0.
\]
所以 \(E\) 是挠模也恰好发生在 \(E=0\)，即指数列有界时。

通过 \(R/(t^\ell)\simeq S/(t^\ell)\)，把 \(C\) 视为自然的 \(S\)-模。此时
\[
j((c_n))=(\widetilde c_n)+I
\]
是 \(S\) 线性的。若 \(j(q(b))=0\)，其中 \(b\in B\)，则每个多项式坐标 \(b_n\) 在 \(S\) 中被 \(t^{\nu_n}\) 整除，也就在 \(R\) 中被它整除；有限支撑又保证 \(b\in\iota(A)\)。故
\[
\boxed{\ker j=0.}
\]
其像正是 \(Q\) 中具有有限支撑代表的类。

更精确地，对每个 \(r\ge1\)，
\[
\boxed{
Q[t^r]=j(C[t^r])
=j\!\left(\bigoplus_n
\frac{t^{\max(\nu_n-r,0)}S}{t^{\nu_n}S}\right).}
\]
为证明没有其他元素，设 \(x=b+I\) 且 \(t^rx=0\)。于是存在 \(a\in\mathcal D\)，满足
\[
t^rb_n=t^{\nu_n}a_n.
\]
若 \(c_n:=b_n\bmod t^{\nu_n}\ne0\)，则
\[
v(a_n)=r+v(b_n)-\nu_n<r.
\]
这样的坐标只有有限个，故 \(c=\widehat q(b)\) 属于 \(C[t^r]\)。现在
\[
x-j(c)\in E,\qquad t^r(x-j(c))=0,
\]
由 \(E\) 无挠可得 \(x=j(c)\)。反向包含显然。因此
\[
\boxed{\operatorname{Tor}_S(Q)=j(C).}
\]

虽然 \(p\) 总是满射，它存在 \(S\) 线性右逆的条件仍然是指数列有界：
\[
\boxed{p\text{ 存在 }S\text{ 线性右逆}
\iff\sup_n\nu_n<\infty.}
\]
有界时 \(E=0\)，故 \(p\) 本身就是同构。无界时，取前面的 \(n_j\)，令
\[
c^*_{n_j}=t^{\nu_{n_j}-1}\bmod t^{\nu_{n_j}},\qquad
c^*_n=0\quad(n\notin\{n_j\}).
\]
则 \(c^*\in\mathcal T\)、\(tc^*=0\)，但 \(c^*\) 具有无限支撑。若 \(s\) 是右逆，则 \(s(c^*)\in Q[t]=j(C[t])\)，从而
\[
c^*=p(s(c^*))\in\eta_C(C),
\]
与无限支撑矛盾。

最后计算有限层商及拓扑。置
\[
L_m=\bigoplus_nS/(t^{\min(m,\nu_n)}).
\]
由 \(\mathcal D/t^m\mathcal D\simeq\bigoplus_nS/(t^m)\)，再对 \(I\) 的像取商，得到
\[
Q/t^mQ\simeq L_m,\qquad
(b+I)+t^mQ\longmapsto
(b_n\bmod t^{\min(m,\nu_n)})_n.
\]
另一方面，
\[
t^m\mathcal T
=\{c\in\mathcal T:c_n\in t^m(S/(t^{\nu_n}))\ \forall n\}.
\]
这里反向包含可通过将 \(\widetilde c_n\) 除以 \(t^m\) 得到；除法只把非零坐标的赋值降低 \(m\)，仍满足趋零条件。因此
\[
\mathcal T/t^m\mathcal T\simeq L_m.
\]
在这两个同构下，由 \(p\) 诱导的映射就是
\[
\boxed{\overline p_m:L_m\xrightarrow{\mathrm{id}}L_m.}
\]

这些同构与过渡约化相容，故
\[
\boxed{\widehat Q\simeq\mathcal T=\widehat C,\qquad
\eta_Q=p.}
\]
同时，\(\mathcal T/t^m\mathcal T\simeq L_m\) 也证明
\(\widehat{\mathcal T}\simeq\mathcal T\)，其典范映射为恒等映射。因此
\[
\boxed{
\widehat p:\widehat Q\longrightarrow\widehat{\widehat C}
\quad\text{在上述模型中为 }\mathrm{id}_{\mathcal T}.}
\]
由典范映射的核即得
\[
\boxed{\bigcap_{m\ge1}t^mQ=E.}
\]
特别地，\(Q\) 分离当且仅当指数列有界。

为了明确计算 \(\widehat E\)，定义
\[
V_m=\left\{x\in\prod_nS/(t^m):
\forall L\ge0,\ 
\#\{n:\nu_n\le L,\ x_n\ne0\}<\infty\right\},
\qquad
F_m=\bigoplus_nS/(t^m).
\]
逐坐标约化给出满射 \(\mathcal H\to V_m\)：可用次数小于 \(m\) 的代表提升。其核为 \(t^m\mathcal H\)，因为
\[
\mathcal H\cap(t^mS)^{\mathbb N}=t^m\mathcal H.
\]
而 \(\mathcal D\) 的像为 \(F_m\)。所以
\[
E/t^mE\simeq V_m/F_m,
\]
并且典范映射具体为
\[
\eta_E:\mathcal H/\mathcal D
\longrightarrow\varprojlim_m V_m/F_m,\qquad
[a]\longmapsto\bigl([a\bmod t^m]\bigr)_m.
\]

这个映射是同构。单射性来自：若每个 \(a\bmod t^m\) 都具有有限支撑，则 \(a\in\mathcal D\)。

对于满射性，给定相容的类族，可递归选取代表 \(x^{(m)}\in V_m\)，使
\[
x^{(m+1)}\bmod t^m=x^{(m)}
\]
严格成立：相容性保证原先的差属于 \(F_m\)，提升该有限支撑差并扣除即可。严格相容的坐标记录确定 \(a_n\in S\)。对每个 \(L\ge1\)，
\[
\{n:\nu_n+v(a_n)<L\}
\subseteq
\{n:\nu_n<L,\ x_n^{(L)}\ne0\},
\]
右侧有限，故 \(a\in\mathcal H\)，并提升给定的类族。于是
\[
\boxed{\widehat E\simeq E=\mathcal H/\mathcal D,\qquad
\eta_E=\mathrm{id}_E}
\]
（在上述自然同构下）。特别地，\(E\) 自身的 \(t\) 进拓扑始终分离且完备：
\[
\boxed{\bigcap_{m\ge1}t^mE=0.}
\]
包含映射 \(E\hookrightarrow Q\) 诱导的完成映射则为零，因为其复合到 \(\widehat Q\simeq\mathcal T\) 就是 \(p|_E=0\)。

由于 \(E\subseteq t^mQ\) 对所有 \(m\) 成立，继承拓扑在零点的邻域基为
\[
E\cap t^mQ=E.
\]
因此，\(E\) 从 \(Q\) 继承的子空间拓扑始终是不可分拓扑，即只有 \(\varnothing,E\) 两个开集。它与始终分离的自身 \(t\) 进拓扑相同，当且仅当 \(E=0\)。也就是
\[
\boxed{
E\text{ 的自身 }t\text{ 进拓扑与继承拓扑相同}
\iff\sup_n\nu_n<\infty.}
\]