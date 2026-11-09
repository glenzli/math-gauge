记 \(v=v_t\)，并约定 \(v(0)=+\infty\)、\(S/(t^0)=0\)。对于 \(S/(t^d)\) 中的非零元素，用其唯一次数小于 \(d\) 的多项式代表定义 \(v\)。

置
\[
T=\left\{(a_n)\in\prod_nS:
\forall m\ge1,\ \#\{n:v(a_n)<m\}<\infty\right\},
\]
\[
D=\left\{(c_n)\in\prod_nS/(t^{\nu_n}):
\forall m\ge1,\ \#\{n:v(c_n)<m\}<\infty\right\}.
\]
也就是说，\(T,D\) 都要求坐标在 \(t\) 进意义下趋于零。

逐层有
\[
A/t^mA\cong B/t^mB\cong\bigoplus_nS/(t^m),\qquad
C/t^mC\cong\bigoplus_nS/(t^{\min(m,\nu_n)}).
\]
因此存在 \(S\) 线性同构
\[
\widehat A\cong T,\qquad \widehat B\cong T,\qquad \widehat C\cong D.
\]
具体地，坐标与相容商记录的对应为
\[
(a_n)\longmapsto\bigl((a_n\bmod t^m)_n\bigr)_{m\ge1},
\]
\[
(c_n)\longmapsto
\bigl((c_n\bmod t^{\min(m,\nu_n)})_n\bigr)_{m\ge1}.
\]
上述有限性条件保证每层记录具有有限支撑。反之，相容记录逐坐标确定 \(S\) 或 \(S/(t^{\nu_n})\) 中的元素，每层的有限支撑又保证所得坐标满足上述条件。这也证明了这些对应互为逆映射。各典范映射就是有限支撑坐标的自然嵌入。

在这些模型中，诱导映射为
\[
d:=\widehat\iota:T\longrightarrow T,\qquad
d(a)_n=t^{\nu_n}a_n,
\]
\[
\rho:=\widehat q:T\longrightarrow D,\qquad
\rho(b)_n=b_n\bmod t^{\nu_n}.
\]

再定义
\[
U=\left\{(a_n)\in\prod_nS:
\forall m\ge1,\ \#\{n:\nu_n+v(a_n)<m\}<\infty\right\}.
\]
显然 \(T\subseteq U\)，且对角公式将 \(d\) 延伸为单射 \(U\to T\)。记
\[
H=d(T),\qquad
K=d(U)=\{b\in T:b_n\in t^{\nu_n}S\text{ 对所有 }n\}.
\]
于是
\[
\operatorname{im}\widehat\iota=H,\qquad
\ker\widehat q=K.
\]

坐标整除条件定义闭子模，所以 \(K\) 在 \(T\) 中闭。另一方面，任意 \(b\in K\) 的有限支撑截断都属于 \(H\)，且这些截断在 \(T\) 中收敛到 \(b\)。故
\[
\boxed{\ \overline{\operatorname{im}\widehat\iota}=K=\ker\widehat q.\ }
\]

给定 \(c\in D\)，令 \(\widetilde c_n\) 是 \(c_n\) 的次数小于 \(\nu_n\) 的代表，零坐标取零。则 \(\widetilde c\in T\)，且
\[
\rho(\widetilde c)=c,\qquad
\boxed{\ \widehat q^{-1}(c)=\widetilde c+K
=\widetilde c+d(U).\ }
\]
特别地，\(\widehat q\) 总满射；每个纤维都是闭集，而 \(\widetilde c+H\) 在该纤维中稠密。

因此完成列
\[
0\longrightarrow\widehat A
\xrightarrow{\widehat\iota}\widehat B
\xrightarrow{\widehat q}\widehat C\longrightarrow0
\]
在左端总是单射、右端总是满射，中间是否正合由 \(U=T\) 决定。事实上，
\[
\boxed{\ U=T\iff \sup_n\nu_n<\infty.\ }
\]
若 \(\nu_n\le N\)，则
\[
\{n:v(a_n)<m\}\subseteq
\{n:\nu_n+v(a_n)<N+m\},
\]
所以 \(a\in U\) 蕴含 \(a\in T\)。若指数无界，选取不同的 \(n_j\)，使 \(\nu_{n_j}\ge j+1\)，并令 \(a_{n_j}=1\)、其余坐标为零，则 \(a\in U\setminus T\)。故完成列短正合当且仅当指数列有界。

现在有具体模型
\[
Q=T/H,\qquad
\boxed{\ E=K/H\cong U/T,\quad
a+T\longmapsto d(a)+H.\ }
\]
由 \(\rho\) 的满射性，\(p\) 总满射；并且
\[
\boxed{\ E=0\iff\sup_n\nu_n<\infty.\ }
\]

通过
\[
C=\bigoplus_nS/(t^{\nu_n})
\]
赋予 \(C\) 自然的 \(S\) 模结构。由于
\[
p\circ j=\eta_C
\]
且 \(\eta_C\) 在上述模型中是单射，故
\[
\boxed{\ker j=0.}
\]

\(E\) 总是无挠的。事实上，对任意 \(r\ge1\)，
\[
t^ra\in T\quad\Longrightarrow\quad a\in T.
\]
所以 \(E[t^r]=0\)。又因为 \(S\) 的任意非零元素都是单位乘以 \(t^r\)，这证明
\[
\operatorname{Tor}_S(E)=0.
\]

对于 \(Q\)，结论恰为
\[
\boxed{\ Q[t^r]
=j\left(\bigoplus_n
\frac{t^{\max(\nu_n-r,0)}S}{t^{\nu_n}S}\right),\qquad
\operatorname{Tor}_S(Q)=\operatorname{im}j.\ }
\]
证明如下。\(j(C)\) 中的每个元素具有有限支撑，因而被某个 \(t^r\) 杀死。反之，设 \([b]\in Q\) 满足 \(t^r[b]=0\)，则存在 \(a\in T\) 使
\[
t^rb=d(a).
\]
集合 \(F=\{n:a_n\notin t^rS\}\) 有限。令
\[
h_n=
\begin{cases}
a_n/t^r,&n\notin F,\\
0,&n\in F.
\end{cases}
\]
则 \(h\in T\)，且 \(b-d(h)\) 支撑于 \(F\)。将其有限个坐标分别模 \(t^{\nu_n}\) 约化，就得到 \(j(C)\) 中的同一元素。结合 \(j\) 的单射性即得固定 \(r\) 的公式。

\(p\) 的分裂条件也是指数有界：
\[
\boxed{\ p\text{ 存在 }S\text{ 线性右逆}
\iff\sup_n\nu_n<\infty.\ }
\]
有界时 \(E=0\)，所以 \(p\) 本身是同构。无界时，取上述 \(n_j\)，令
\[
c_{n_j}=t^{\nu_{n_j}-1}\bmod t^{\nu_{n_j}},
\qquad c_n=0\quad(n\notin\{n_j\}).
\]
则 \(c\in D[t]\)，但具有无限支撑，故不属于 \(\eta_C(C)\)。若存在右逆 \(s\)，则 \(s(c)\in Q[t]\)，从而
\[
c=p(s(c))\in p(j(C))=\eta_C(C),
\]
矛盾。

接下来确定所有有限层商。逐坐标除以 \(t^m\) 可见
\[
t^mD=
\{c\in D:c_n\in t^m(S/(t^{\nu_n}))\text{ 对所有 }n\};
\]
所选商坐标仍趋于零。因此
\[
D/t^mD\cong\bigoplus_nS/(t^{\min(m,\nu_n)}).
\]
另一方面，
\[
\ker\left(T\longrightarrow
\bigoplus_nS/(t^{\min(m,\nu_n)})\right)
=H+t^mT.
\]
这里的等式可直接验证：\(b\in T\) 模 \(t^m\) 只有有限个非零坐标；若它属于左边的核，这些坐标都可由有限支撑的对角像消去，余项属于 \(t^mT\)。

所以 \(p\) 对每个 \(m\ge1\) 诱导同构
\[
\boxed{\ 
Q/t^mQ\xrightarrow[\sim]{\,p_m\,}
\widehat C/t^m\widehat C
\cong\bigoplus_nS/(t^{\min(m,\nu_n)}),
\ }
\]
其公式为
\[
[b]\bmod t^mQ\longmapsto
(b_n\bmod t^{\min(m,\nu_n)})_n.
\]
特别地，
\[
p^{-1}(t^mD)=t^mQ.
\]
于是
\[
\boxed{\ \bigcap_{m\ge1}t^mQ=E.\ }
\]
这也表明 \(Q\) 分离当且仅当指数列有界。

取上述有限层同构的逆极限，得到
\[
\boxed{\ \widehat Q\cong D=\widehat C,\qquad
\eta_Q=p\ }
\]
（这里通过该同构识别目标）。上述 \(D/t^mD\) 的计算同时说明 \(D\) 自身完备且分离。因此，识别
\(\widehat Q\cong D\) 和 \(\widehat D\cong D\) 后，
\[
\boxed{\ \widehat p:\widehat Q\longrightarrow\widehat{\widehat C}
\text{ 就是 }\operatorname{id}_D.\ }
\]

最后计算 \(E\) 自身的完成。由定义，
\[
t^mU=U\cap\prod_n t^mS,\qquad
t^mE=(T+t^mU)/T.
\]
若 \(a+T\in\bigcap_m t^mE\)，则对每个 \(m\)，\(a\) 模 \(t^m\) 都具有有限支撑；这正是 \(a\in T\) 的条件。因此
\[
\bigcap_m t^mE=0,
\]
即 \(E\) 自身的 \(t\) 进拓扑总是分离的。

此外，\(U\) 自身完备：一个 \(t\) 进柯西序列逐坐标有极限 \(a\in\prod_nS\)。对每个 \(L\)，取与 \(a\) 逐坐标模 \(t^L\) 相同的某个序列项 \(u\in U\)，则
\[
\{n:\nu_n+v(a_n)<L\}
=\{n:\nu_n+v(u_n)<L\}
\]
是有限集，故 \(a\in U\)。

任取相容记录 \((e_m)\in\varprojlim_mE/t^mE\)。逐次选取代表 \(u_m\in U\)，利用相容性从 \(u_{m+1}\) 中减去适当的 \(T\) 元素，可使
\[
u_{m+1}-u_m\in t^mU.
\]
其极限 \(u\in U\) 表示整个记录。这证明 \(\eta_E\) 满射；结合分离性得到
\[
\boxed{\ \widehat E\cong E\cong U/T,\qquad
\eta_E\text{ 是同构}.\ }
\]
在此识别下，包含映射 \(E\hookrightarrow Q\) 诱导的完成映射
\(\widehat E\to\widehat Q\) 为零。

由于 \(E\subseteq t^mQ\) 对每个 \(m\) 都成立，
\[
E\cap t^mQ=E.
\]
所以 \(E\) 从 \(Q\) 继承的子空间拓扑是平凡拓扑，即只有空集和全集。其自身的 \(t\) 进拓扑则总是完备且分离。两者相同当且仅当 \(E=0\)，也就是
\[
\boxed{\ \text{两种拓扑相同}\iff\sup_n\nu_n<\infty.\ }
\]