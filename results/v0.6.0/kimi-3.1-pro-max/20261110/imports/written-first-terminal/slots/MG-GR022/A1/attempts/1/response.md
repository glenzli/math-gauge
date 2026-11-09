以下所有结论的分界条件都是：

\[
\boxed{\text{指数列 }(\nu_n)\text{ 有界，即 }\sup_n\nu_n<\infty.}
\]

记 \(I=\operatorname{im}\widehat\iota\)。对 \(s\in S\)，令 \(v(s)\) 为其 \(t\) 进赋值，并约定 \(v(0)=\infty\)。所谓 \(v(x_n)\to\infty\)，是指对每个 \(M\)，除有限个 \(n\) 外均有 \(v(x_n)\ge M\)。

## 一、三个完成的坐标模型及完成列

### 1. 坐标模型与相容商记录

定义

\[
\mathcal L=\left\{x=(x_n)\in\prod_{n\ge1}S:\ v(x_n)\to\infty\right\}.
\]

因为

\[
A/t^mA\cong B/t^mB\cong\bigoplus_{n\ge1}R/(t^m),
\]

坐标逐项取逆极限即得自然同构

\[
\widehat A\cong\mathcal L,\qquad \widehat B\cong\mathcal L.
\]

具体地，\(x\in\mathcal L\) 对应相容记录

\[
x\longmapsto\left((x_n\pmod{t^m})_{n\ge1}\right)_{m\ge1}.
\]

每个记录确实只有有限个非零坐标，因为 \(\{n:v(x_n)<m\}\) 有限。反之，相容记录逐坐标给出 \(x_n\in S\)，而各层记录的有限支撑性恰好等价于 \(v(x_n)\to\infty\)。

再令

\[
D_n=S/t^{\nu_n}S\cong R/t^{\nu_n}R,
\]

其中 \(\nu_n=0\) 时 \(D_n=0\)。定义

\[
\mathcal C=
\left\{c=(c_n)\in\prod_{n\ge1}D_n:\
\forall m,\ \{n:c_n\notin t^mD_n\}\text{ 有限}\right\}.
\]

由于

\[
C/t^mC\cong
\bigoplus_{n\ge1}R/(t^{\nu_n},t^m)
=
\bigoplus_{n\ge1}R/t^{\min(m,\nu_n)}R,
\]

同样有自然同构

\[
\widehat C\cong\mathcal C,
\]

对应关系仍是

\[
c\longmapsto
\left((c_n\pmod{t^m})_{n\ge1}\right)_{m\ge1}.
\]

也可以这样描述 \(\mathcal C\)：对每个 \(c_n\) 取次数小于 \(\nu_n\) 的典范代表元 \(\widetilde c_n\)（若 \(c_n=0\)，取 \(\widetilde c_n=0\)），则

\[
c\in\mathcal C\quad\Longleftrightarrow\quad v(\widetilde c_n)\to\infty.
\]

在这些模型下，\(S\) 的作用均为逐坐标作用，且

\[
\boxed{\widehat\iota(a)=(t^{\nu_n}a_n)_n},\qquad
\boxed{\widehat q(b)=(b_n\bmod t^{\nu_n})_n}.
\]

典范映射 \(\eta_A,\eta_B,\eta_C\) 就是把原来的有限支撑序列放入上述坐标模型。

### 2. 正合性、核、闭包与纤维

映射 \(\widehat\iota\) 总是单射，因为每个坐标上的乘以 \(t^{\nu_n}\) 都是 \(S\) 上的单射。

映射 \(\widehat q\) 总是满射。事实上，给定 \(c\in\mathcal C\)，令

\[
b^c=(\widetilde c_n)_n.
\]

由 \(v(\widetilde c_n)\to\infty\)，有 \(b^c\in\widehat B\)，并且 \(\widehat q(b^c)=c\)。

其核为

\[
U:=\ker\widehat q
=\left\{u\in\mathcal L:\ u_n\in t^{\nu_n}S\ \text{对所有 }n\right\}.
\]

因此

\[
\boxed{\widehat q^{-1}(c)=b^c+U\qquad(c\in\widehat C).}
\]

当然，\(b^c\) 也可换成 \(c\) 的任意一个提升。

下面证明

\[
\boxed{\overline I=U=\ker\widehat q,}
\]

其中闭包取在 \(\widehat B\) 的 \(t\) 进拓扑中。

一方面，若 \(u\in U\)，固定 \(m\)，令

\[
F=\{n:v(u_n)<m\},
\]

这是有限集。把 \(u\) 在 \(F\) 上的部分记为 \(u_F\)。因为 \(u_n\in t^{\nu_n}S\)，所以 \(u_F\in I\)；而 \(u-u_F\in t^m\widehat B\)。故

\[
u\in I+t^m\widehat B
\]

对所有 \(m\) 成立，即 \(u\in\overline I\)。

另一方面，若 \(b\notin U\)，则存在 \(n\) 使

\[
r:=v(b_n)<\nu_n.
\]

取 \(m>r\)。任意 \(I+t^m\widehat B\) 中元素的第 \(n\) 个坐标，其赋值至少为 \(\min(\nu_n,m)>r\)，故不可能等于 \(b\)。因此 \(b\notin\overline I\)。这证明了 \(\overline I=U\)。

综上，完成列

\[
0\longrightarrow\widehat A
\xrightarrow{\widehat\iota}\widehat B
\xrightarrow{\widehat q}\widehat C
\longrightarrow0
\]

在 \(\widehat A\) 处和 \(\widehat C\) 处总正合，在 \(\widehat B\) 处正合当且仅当 \(I=U\)。

若 \(\nu_n\le N\) 对所有 \(n\) 成立，则对 \(u\in U\)，令 \(a_n=u_n/t^{\nu_n}\)，有

\[
v(a_n)=v(u_n)-\nu_n\ge v(u_n)-N\to\infty,
\]

故 \(a\in\mathcal L\)，从而 \(u=\widehat\iota(a)\)。于是 \(I=U\)。

若 \((\nu_n)\) 无界，取子列 \(n_i\) 使 \(\nu_{n_i}\to\infty\)。定义

\[
u_n=
\begin{cases}
t^{\nu_{n_i}},&n=n_i\text{ 对某个 }i,\\
0,&\text{其余 }n.
\end{cases}
\]

则 \(u\in U\)。若 \(u=\widehat\iota(a)\)，就必须有 \(a_{n_i}=1\) 对所有 \(i\) 成立，这与 \(v(a_n)\to\infty\) 矛盾。因此 \(u\notin I\)。

所以

\[
\boxed{
0\to\widehat A\to\widehat B\to\widehat C\to0
\text{ 短正合}
\iff I=U
\iff \sup_n\nu_n<\infty.
}
\]

## 二、\(E\)、\(j\)、挠性及分裂性

### 1. \(E\) 的坐标模型

定义

\[
\mathcal D=
\left\{a=(a_n)\in\prod_{n\ge1}S:\
\nu_n+v(a_n)\to\infty\right\}.
\]

这是 \(\prod S\) 的 \(S\) 子模，并且 \(\mathcal L\subseteq\mathcal D\)。映射

\[
\mathcal D\longrightarrow U,\qquad
a\longmapsto(t^{\nu_n}a_n)_n
\]

是 \(S\) 线性同构；在该同构下，\(\mathcal L\) 恰好对应 \(I\)。因此

\[
\boxed{
E=U/I\cong\mathcal D/\mathcal L,
}
\]

其中同构为

\[
a+\mathcal L\longmapsto
(t^{\nu_n}a_n)_n+I.
\]

特别地，上一节的讨论给出

\[
\boxed{E=0\iff(\nu_n)\text{ 有界}.}
\]

由于 \(\widehat q\) 总满射，故

\[
\boxed{p:Q\twoheadrightarrow\widehat C\text{ 总为满射}.}
\]

### 2. \(j\) 的核和像

由定义直接有

\[
p\circ j=\eta_C.
\]

而 \(C\) 是有限支撑的坐标序列，\(\eta_C\) 在每个坐标上都是自然同构 \(R/t^{\nu_n}\cong D_n\)，所以 \(\eta_C\) 单射。于是

\[
\boxed{\ker j=0.}
\]

下面确定 \(Q\) 的 \(t\) 幂挠子模。结论是

\[
\boxed{
\{x\in Q:\exists r\ge1,\ t^rx=0\}=\operatorname{im}j=j(C).
}
\]

先证明任意挠元素都在 \(j(C)\) 中。设 \(x=b+I\)，且 \(t^rx=0\)。则存在 \(a\in\mathcal L\)，使得

\[
t^rb_n=t^{\nu_n}a_n
\]

对所有 \(n\) 成立。因此

\[
v(a_n)=r+v(b_n)-\nu_n\to\infty.
\]

除有限个 \(n\) 外，有 \(v(a_n)\ge r\)，从而 \(v(b_n)\ge\nu_n\)。把这个有限集记为 \(F\)。在 \(F\) 外令 \(a'_n=b_n/t^{\nu_n}\)，在 \(F\) 上令 \(a'_n=0\)，则

\[
v(a'_n)=v(a_n)-r\to\infty
\quad(n\notin F),
\]

故 \(a'\in\mathcal L\)。这说明 \(b\) 与一个在 \(F\) 外为零的序列相差 \(I\) 中元素，所以 \(x\) 有有限支撑代表元。

再把每个有限支撑坐标按模 \(t^{\nu_n}\) 截断成多项式，所差部分仍属于 \(I\)。因此 \(x\) 实际上有 \(B\) 中的有限支撑代表元，即 \(x\in j(C)\)。

反过来，若 \(x=j(c)\)，取 \(B\) 中有限支撑代表元 \(b\)。只要 \(r\) 大于其支撑上所有 \(\nu_n\)，就有 \(t^rb\in I\)，故 \(t^rx=0\)。

此外，\(j(C)\) 也正好等于 \(Q\) 中所有“具有有限支撑代表元的类”。

### 3. \(E\) 无挠

若 \(x\in E\) 且 \(t^rx=0\)，则由上述结论 \(x=j(c)\)。于是

\[
0=p(x)=p(j(c))=\eta_C(c).
\]

由 \(\eta_C\) 单射得 \(c=0\)，故 \(x=0\)。由于 \(S\) 是离散赋值环，任意非零元素都是单位乘以某个 \(t^r\)，所以

\[
\boxed{E\text{ 是无挠 }S\text{ 模；特别地，乘以 }t\text{ 在 }E\text{ 上是单射}.}
\]

### 4. \(p\) 何时有 \(S\) 线性右逆

若 \((\nu_n)\) 有界，则 \(E=0\)，\(p\) 是同构，当然有右逆。

反过来，设 \((\nu_n)\) 无界。取 \(n_i\) 使 \(\nu_{n_i}\to\infty\)，并不妨设所有 \(\nu_{n_i}\ge1\)。在 \(\widehat C\) 中定义 \(c\)：

\[
c_n=
\begin{cases}
t^{\nu_{n_i}-1}\pmod{t^{\nu_{n_i}}},&n=n_i,\\
0,&\text{其余 }n.
\end{cases}
\]

由于 \(\nu_{n_i}-1\to\infty\)，确有 \(c\in\widehat C\)。同时

\[
tc=0,
\]

而 \(c\) 有无限多个非零坐标，故 \(c\notin\eta_C(C)\)。

若存在右逆 \(s:\widehat C\to Q\)，则

\[
t\,s(c)=s(tc)=0.
\]

由 \(Q\) 的挠子模等于 \(j(C)\)，有 \(s(c)=j(d)\)。于是

\[
c=p(s(c))=p(j(d))=\eta_C(d),
\]

矛盾。因此

\[
\boxed{
p\text{ 存在 }S\text{ 线性右逆}
\iff(\nu_n)\text{ 有界}
\iff E=0.
}
\]

## 三、模 \(t^m\)、再次完成及两种拓扑

### 1. \(E\subseteq t^mQ\) 及 \(p\) 诱导的商映射

固定 \(m\)，取 \(E\) 中元素 \(x=u+I\)，其中 \(u\in U\)。令

\[
F=\{n:v(u_n)<m\},
\]

仍为有限集。与证明闭包时相同，\(u\) 在 \(F\) 上的部分属于 \(I\)，而其余部分属于 \(t^m\widehat B\)。故

\[
x\in t^mQ.
\]

因此对每个 \(m\)，

\[
\boxed{E\subseteq t^mQ.}
\]

由此可得

\[
\boxed{
p_m:Q/t^mQ\longrightarrow\widehat C/t^m\widehat C
\text{ 对每个 }m\ge1\text{ 都是同构}.
}
\]

满射性由 \(p\) 满射立即得到。若 \(p(x)\in t^m\widehat C\)，取 \(y\in Q\) 使 \(p(x)=t^mp(y)\)，则

\[
x-t^my\in E\subseteq t^mQ,
\]

故 \(x\in t^mQ\)，证明了单射性。

坐标模型还给出自然同构

\[
C/t^mC\cong\widehat C/t^m\widehat C
\cong\bigoplus_{n\ge1}R/t^{\min(m,\nu_n)}R.
\]

在这个识别下，\(p_m\) 就是相应商记录上的恒等映射。更明确地说，其逆映射为

\[
c+t^mC\longmapsto j(c)+t^mQ.
\]

### 2. \(Q\) 中所有 \(t^mQ\) 的交

由于 \(\widehat C\) 是分离的，即

\[
\bigcap_m t^m\widehat C=0,
\]

若 \(x\in\bigcap_m t^mQ\)，则 \(p(x)\in\bigcap_m t^m\widehat C=0\)，所以 \(x\in E\)。反向包含刚刚已经证明。因此

\[
\boxed{\bigcap_{m\ge1}t^mQ=E.}
\]

特别地，

\[
Q\text{ 分离}\iff E=0\iff(\nu_n)\text{ 有界}.
\]

### 3. \(\widehat Q\) 与 \(p\) 的完成映射

各 \(p_m\) 与过渡映射相容，故给出逆向极限同构

\[
\widehat Q
=\varprojlim_m Q/t^mQ
\cong
\varprojlim_m\widehat C/t^m\widehat C
\cong\widehat C.
\]

在此同构下，典范映射恰好就是 \(p\)：

\[
\boxed{\widehat Q\cong\widehat C,\qquad \eta_Q=p.}
\]

也就是说，\(p\) 正是 \(Q\) 的 \(t\) 进完备化映射；它以 \(E\) 为核并且满射。

同理，\(\widehat{\widehat C}\) 自然等同于 \(\widehat C\)，所以

\[
\boxed{
\widehat p:\widehat Q\to\widehat{\widehat C}
\text{ 在上述识别下就是 }\operatorname{id}_{\widehat C}.
}
\]

### 4. \(\widehat E\)：\(E\) 自身已经完备

使用 \(E\cong\mathcal D/\mathcal L\)。首先有

\[
t^m\mathcal D
=\{a\in\mathcal D:\ v(a_n)\ge m\text{ 对所有 }n\}.
\]

事实上，若 \(a=t^md\)，则 \(\nu_n+v(a_n)=\nu_n+m+v(d_n)\)，所以 \(a\in\mathcal D\) 当且仅当 \(d\in\mathcal D\)。

由坐标模型可知 \(\mathcal D\) 对这个 \(t\) 进拓扑完备。再计算

\[
\boxed{\bigcap_{m\ge1}(t^m\mathcal D+\mathcal L)=\mathcal L.}
\]

若 \(a\notin\mathcal L\)，则存在 \(K\) 及无限集 \(I_0\)，使得 \(v(a_n)\le K\) 对所有 \(n\in I_0\) 成立。取 \(m>K\)。若

\[
a=t^md+\ell,\qquad d\in\mathcal D,\ \ell\in\mathcal L,
\]

则在 \(I_0\) 上，\(v(t^md_n)\ge m>v(a_n)\)，故

\[
v(\ell_n)=v(a_n)\le K.
\]

这与 \(v(\ell_n)\to\infty\) 矛盾。

因为

\[
E/t^mE\cong\mathcal D/(t^m\mathcal D+\mathcal L),
\]

上述交公式首先说明

\[
\bigcap_m t^mE=0,
\]

即 \(E\) 自身的 \(t\) 进拓扑总是分离的。

进一步，自然映射

\[
\mathcal D/\mathcal L\longrightarrow
\varprojlim_m\mathcal D/(t^m\mathcal D+\mathcal L)
\]

是同构：满射性可通过逐级选取代表元、并用 \(\mathcal L\) 中元素调整，使相邻代表元之差落入 \(t^m\mathcal D\)，再利用 \(\mathcal D\) 的完备性取极限得到；其核由上述交公式为零。因此

\[
\boxed{\widehat E\cong E,\qquad \eta_E\text{ 是同构}.}
\]

也就是说，尽管 \(E\) 可以非零，它自身始终是 \(t\) 进完备分离的。

### 5. 两种拓扑的比较

由 \(E\subseteq t^mQ\)，有

\[
E\cap t^mQ=E
\qquad(m\ge1).
\]

所以 \(E\) 从 \(Q\) 继承的子空间拓扑以 \(E\) 本身为零点的唯一基本邻域，即

\[
\boxed{\text{继承拓扑是平凡拓扑（indiscrete topology）：开集只有 }\varnothing,E.}
\]

而 \(E\) 自身的 \(t\) 进拓扑以 \(t^mE\) 为零点邻域基，且总是分离、完备。因此自身拓扑总细于继承拓扑；若 \(E\ne0\)，二者不可能相同，否则非零的 \(E\) 会同时具有分离且平凡的拓扑。

最终得到

\[
\boxed{
E\text{ 的自身 }t\text{ 进拓扑与从 }Q\text{ 继承的拓扑相同}
\iff E=0
\iff(\nu_n)\text{ 有界}.
}
\]

在无界情形，\(E\ne0\)，自身拓扑严格细于继承的平凡拓扑。