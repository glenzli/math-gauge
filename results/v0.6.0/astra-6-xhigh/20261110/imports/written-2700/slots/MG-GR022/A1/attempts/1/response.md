所有涉及的充要条件都是指数列有界，即
\[
\exists N\ge0\quad\forall n,\qquad \nu_n\le N.
\]
具体而言，完成列短正合、\(E=0\)、\(p\) 存在 \(S\) 线性右逆，以及 \(E\) 上的两种拓扑相同，均等价于此条件。另一方面，\(E\) 自身始终是无挠、分离且完备的 \(S\) 模。下面给出坐标模型及证明。

约定 \(S/(t^0)=0\)，并令 \(v\) 表示 \(t\) 阶，\(v(0)=+\infty\)。在 \(S/(t^\nu)\) 上，非零元素的阶由其次数小于 \(\nu\) 的唯一多项式代表确定。

先定义
\[
\begin{aligned}
D&=\left\{(x_n)\in\prod_{n\ge1}S:
  \forall m\ge1,\ \#\{n:v(x_n)<m\}<\infty\right\},\\
H&=\left\{(c_n)\in\prod_{n\ge1}S/(t^{\nu_n}):
  \forall m\ge1,\ \#\{n:v(c_n)<m\}<\infty\right\},\\
P&=\left\{(a_n)\in\prod_{n\ge1}S:
  \forall m\ge1,\ \#\{n:\nu_n+v(a_n)<m\}<\infty\right\}.
\end{aligned}
\]
这些都是按坐标运算的 \(S\) 模，且 \(D\subseteq P\)。记
\[
d(a)=(t^{\nu_n}a_n)_n,\qquad
\rho(b)=(b_n\bmod t^{\nu_n})_n.
\]

**完成的坐标描述。** 有典范 \(S\) 模同构
\[
\widehat A\simeq D,\qquad \widehat B\simeq D,\qquad
\widehat C\simeq H,
\]
在这些同构下，
\[
\widehat\iota=d|_D,\qquad \widehat q=\rho.
\]

具体地，
\[
A/t^mA\simeq B/t^mB\simeq\bigoplus_n S/(t^m).
\]
一个相容商记录 \((x^{(m)})_m\) 在第 \(n\) 个坐标上给出相容的模 \(t^m\) 记录，因而唯一确定 \(x_n\in S\)。每层记录具有有限支撑，恰好等价于 \((x_n)\in D\)。反向映射是
\[
(x_n)\longmapsto\bigl((x_n\bmod t^m)_n\bigr)_m.
\]

同样，
\[
C\simeq\bigoplus_n S/(t^{\nu_n}),\qquad
C/t^mC\simeq\bigoplus_n S/(t^{\min(m,\nu_n)}).
\]
相容记录的第 \(n\) 个坐标在 \(m\ge\nu_n\) 后稳定，确定
\(c_n\in S/(t^{\nu_n})\)。各层有限支撑恰好给出 \(H\) 的定义；反向映射为
\[
(c_n)\longmapsto
\bigl((c_n\bmod t^{\min(m,\nu_n)})_n\bigr)_m.
\]
这些对应显然保持各层给定的 \(S\) 作用。典范映射 \(\eta_A,\eta_B\) 是把有限支撑的多项式坐标放入 \(D\)，而 \(\eta_C\) 是把有限支撑坐标放入 \(H\)；三者均单射。

对 \(c\in H\)，令 \(\sigma(c)_n\) 是 \(c_n\) 的次数小于 \(\nu_n\) 的多项式代表；当 \(\nu_n=0\) 时取零。由于代表保持 \(t\) 阶，
\[
\sigma(c)\in D,\qquad \rho(\sigma(c))=c.
\]
因此 \(\widehat q\) 总是满射。这里 \(\sigma\) 是 \(k\) 线性的坐标提升，一般不是 \(S\) 线性的。

令 \(I=\operatorname{im}\widehat\iota\)、\(K=\ker\widehat q\)，则
\[
I=dD,\qquad
K=\{b\in D:b_n\in t^{\nu_n}S\ \forall n\}=dP.
\]
特别地，每个纤维都有明确描述：
\[
\boxed{\ \widehat q^{-1}(c)=\sigma(c)+dP\quad(c\in H).\ }
\]

因为 \(S\) 是整环，\(d|_D\) 单射。故完成列
\[
0\longrightarrow\widehat A
 \xrightarrow{\widehat\iota}\widehat B
 \xrightarrow{\widehat q}\widehat C
 \longrightarrow0
\]
总在两端正合，唯一可能不正合之处是 \(\widehat B\)，其障碍为 \(dP/dD\)。

此外，
\[
\boxed{\ \overline{\operatorname{im}\widehat\iota}
       =\ker\widehat q=dP.\ }
\]
事实上，
\[
t^mD=\{b\in D:b_n\in t^mS\ \forall n\}.
\]
坐标条件 \(b_n\in t^{\nu_n}S\) 是闭条件，所以 \(K\) 闭。另一方面，给定 \(b=d(a)\in K\)，保留 \(b\) 的有限多个坐标即可使被删去的部分属于 \(t^mD\)；所保留的部分是 \(d(a)\) 的有限坐标截断，属于 \(dD\)。故 \(dD\) 在 \(K\) 中稠密。

若 \(\nu_n\le N\)，则 \(d(a)\in D\) 蕴含 \(a\in D\)，因而 \(P=D\)。若指数列无界，可选互异指标 \(n_j\)，使 \(\nu_{n_j}\ge j\)，并取
\[
a_{n_j}=1,\qquad a_n=0\quad(n\notin\{n_j\}).
\]
此时 \(a\in P\setminus D\)。所以
\[
\boxed{\ 
\text{完成列短正合}
\iff \operatorname{im}\widehat\iota\text{ 闭}
\iff (\nu_n)\text{ 有界}.
\ }
\]

接下来分析 \(Q\)、\(E\) 和挠元。由上述坐标描述，
\[
Q=D/dD,\qquad
p([b])=\rho(b),
\]
且总有短正合列
\[
0\longrightarrow E\longrightarrow Q\xrightarrow{p}H\longrightarrow0.
\]
其中
\[
\boxed{\ E\simeq P/D,\qquad
a+D\longmapsto d(a)+dD.\ }
\]

为了同时看清 \(E\) 的模结构和自身拓扑，定义
\[
F=k^{(\mathbb N)},\qquad
L=\left\{(\lambda_n)\in k^{\mathbb N}:
 \forall h\ge1,\ 
 \#\{n:\nu_n<h,\ \lambda_n\ne0\}<\infty\right\},
\qquad W=L/F.
\]
这里 \(F\) 是有限支撑序列空间。等价地，若
\(J_h=\{n:\nu_n=h\}\)，则
\[
L\simeq\prod_{h\ge0}k^{(J_h)},\qquad
F\simeq\bigoplus_{h\ge0}k^{(J_h)}.
\]

将 \(a_n\) 展开为
\[
a_n=\sum_{\ell\ge0}a_{n,\ell}t^\ell,\qquad
a^{(\ell)}=(a_{n,\ell})_n.
\]
直接由有限性条件可得
\[
a\in P\iff a^{(\ell)}\in L\quad\forall\ell,
\qquad
a\in D\iff a^{(\ell)}\in F\quad\forall\ell.
\]
于是存在典范 \(S\) 模同构
\[
\boxed{\ 
E\simeq W[[t]],\qquad
a+D\longmapsto\sum_{\ell\ge0}(a^{(\ell)}+F)t^\ell.
\ }
\]
这里 \(W[[t]]=\prod_{\ell\ge0}Wt^\ell\)，\(S\) 按通常的卷积公式作用。此映射的核正是 \(D\)，而逐系数选取 \(L\) 中的代表证明其满射性。

由此立即得到
\[
\operatorname{Tor}_S(E)=0.
\]
也可直接验证：若 \(t^ra\in D\)，则 \(a\in D\)；而 \(S\) 的每个非零元素都是单位乘以某个 \(t^r\)。

对于 \(j\)，有
\[
p\circ j=\eta_C.
\]
因为 \(\eta_C\) 单射，
\[
\boxed{\ \ker j=0.\ }
\]
其像正是 \(Q\) 中可由有限支撑的 \(b\in D\) 代表的类：有限多个形式幂级数坐标都可以模 \(t^{\nu_n}\) 化为多项式，差属于 \(dD\)。

更精确地，对每个 \(r\ge1\)，
\[
\boxed{\ 
Q[t^r]=j(C[t^r])
=j\left(\bigoplus_n
 \frac{t^{\max(\nu_n-r,0)}S}{t^{\nu_n}S}\right).
\ }
\]
证明反向包含即可。设 \(t^r[b]=0\)，即
\[
t^rb=d(a),\qquad a\in D.
\]
集合
\[
T=\{n:a_n\notin t^rS\}
\]
有限。令 \(u_n=0\) 当 \(n\in T\)，并令 \(u_n=a_n/t^r\) 当 \(n\notin T\)。则 \(u\in D\)，且 \(b-d(u)\) 支撑在 \(T\) 上。因此 \([b]\in j(C)\)。再由 \(j\) 单射，得到上述公式。

每个 \(C\) 中的元素都被某个 \(t^r\) 杀死，故
\[
\boxed{\ 
\bigcup_{r\ge1}Q[t^r]=\operatorname{Tor}_S(Q)=j(C).
\ }
\]

已经证明 \(p\) 总是满射，且
\[
\boxed{\ E=0\iff(\nu_n)\text{ 有界}.\ }
\]
其分裂条件也是
\[
\boxed{\ p\text{ 存在 }S\text{ 线性右逆}
       \iff(\nu_n)\text{ 有界}.\ }
\]
有界时 \(p\) 本身就是同构。无界时，仍选取
\(\nu_{n_j}\ge j\)，并定义
\[
c_{n_j}=t^{\nu_{n_j}-1}\bmod t^{\nu_{n_j}},
\qquad c_n=0\quad(n\notin\{n_j\}).
\]
则 \(c\in H\)、\(tc=0\)，但 \(c\) 有无限支撑，因此
\(c\notin\eta_C(C)\)。若存在 \(S\) 线性右逆 \(s\)，则
\[
ts(c)=s(tc)=0,
\]
从而 \(s(c)\in Q[t]=j(C[t])\)，这与
\(p(s(c))=c\notin\eta_C(C)\) 矛盾。

最后计算有限层商、完成及拓扑。对每个 \(m\ge1\)，记
\[
G_m=\bigoplus_n S/(t^{\min(m,\nu_n)}).
\]
首先，
\[
Q/t^mQ
\simeq D/(dD+t^mD)
\simeq G_m.
\]
第二个同构将 \([b]\) 送到
\((b_n\bmod t^{\min(m,\nu_n)})_n\)：因为
\(D/t^mD=\bigoplus_nS/(t^m)\)，而 \(dD\) 的像正是各坐标中
\(t^{\nu_n}S/(t^m)\) 的直和。

另一方面，坐标约化给出满射 \(H\to G_m\)，其核恰为 \(t^mH\)。事实上，若 \(c\) 在 \(G_m\) 中为零，则其多项式提升 \(\sigma(c)\) 的每个坐标均被 \(t^m\) 整除，并且
\(\sigma(c)/t^m\in D\)。因此
\[
c=t^m\rho\bigl(\sigma(c)/t^m\bigr).
\]
于是
\[
H/t^mH\simeq G_m.
\]

所以题目中的诱导映射为
\[
\boxed{\ 
\overline p_m:Q/t^mQ\xrightarrow{\sim}
\widehat C/t^m\widehat C,
\quad
\text{在两侧的 }G_m\text{ 坐标下是恒等映射}.
\ }
\]
所有这些同构都与自然约化相容。

由 \(H\simeq\varprojlim_mG_m\)，可知 \(H\) 对自身的 \(t\) 进拓扑分离且完备。有限层同构还给出
\[
t^mQ=p^{-1}(t^mH),
\]
因而
\[
\boxed{\ \bigcap_{m\ge1}t^mQ=\ker p=E.\ }
\]
特别地，\(Q\) 分离当且仅当指数列有界。

取逆极限得到
\[
\boxed{\ \widehat Q\simeq H=\widehat C.\ }
\]
在此同构下，典范映射就是
\[
\boxed{\ 
\eta_Q=p,\qquad
[b]\longmapsto(b_n\bmod t^{\nu_n})_n.
\ }
\]
由于 \(\widehat H\simeq H\)，\(p\) 诱导的完成映射为
\[
\boxed{\ 
\widehat p:\widehat Q\xrightarrow{\sim}\widehat{\widehat C},
\qquad \widehat p=\operatorname{id}_H
\ }
\]
其中两侧均采用上述典范同构。

对于 \(E\simeq W[[t]]\)，有
\[
E/t^mE\simeq\bigoplus_{\ell=0}^{m-1}Wt^\ell,
\]
故
\[
\boxed{\ \widehat E\simeq W[[t]]\simeq E.\ }
\]
典范映射 \(\eta_E\) 将一个形式级数送到其所有有限截断；在上述同构下它是恒等映射。因此 \(E\) 自身的 \(t\) 进拓扑始终分离且完备。顺带可见，包含映射 \(E\hookrightarrow Q\) 所诱导的完成映射
\(\widehat E\to\widehat Q\) 为零。

但 \(E\) 从 \(Q\) 继承的子空间拓扑完全不同：由
\(E\subseteq t^mQ\)，对所有 \(m\ge1\) 都有
\[
E\cap t^mQ=E.
\]
所以该子空间拓扑只有 \(\varnothing\) 和 \(E\) 两个开集。它与 \(E\) 自身分离的 \(t\) 进拓扑相同，当且仅当 \(E=0\)，即
\[
\boxed{\ 
E\text{ 的自身 }t\text{ 进拓扑等于继承的子空间拓扑}
\iff(\nu_n)\text{ 有界}.
\ }