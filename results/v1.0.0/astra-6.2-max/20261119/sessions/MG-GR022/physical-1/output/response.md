## 1. 完成的坐标、纤维与正合性

记 \(S_n=S/(t^{\nu_n})\)，其中 \(S/(t^0)=0\)。以下“几乎所有 \(n\)”指除有限个以外的所有 \(n\)。定义
\[
\begin{aligned}
D&=\left\{b\in\prod_{n\ge1}S\ \middle|\ 
  \forall m\ge1,\ b_n\in t^mS\text{ 对几乎所有 }n\text{ 成立}\right\},\\
T&=\left\{c\in\prod_{n\ge1}S_n\ \middle|\ 
  \forall m\ge1,\ c_n\in t^mS_n\text{ 对几乎所有 }n\text{ 成立}\right\}.
\end{aligned}
\]
则有 \(S\) 线性同构
\[
\widehat A\simeq D,\qquad \widehat B\simeq D,\qquad \widehat C\simeq T,
\]
其中 \(S\) 逐坐标作用。

事实上，利用 \(R/(t^m)\simeq S/(t^m)\) 及 \(C\simeq\bigoplus_n S_n\)，各层的商为
\[
A/t^mA\simeq B/t^mB\simeq\bigoplus_n S/(t^m),\qquad
C/t^mC\simeq\bigoplus_n S/(t^{\min(m,\nu_n)}).
\]
从坐标族到相容商记录的映射，是在第 \(m\) 层逐坐标作上述约化。反过来，给定相容记录，对 \(A,B\)，第 \(n\) 个坐标的所有约化唯一确定一个幂级数。对 \(C\)，第 \(n\) 个坐标在 \(m\ge\max(1,\nu_n)\) 时已经稳定，给出 \(S_n\) 中的元素。每层记录支撑有限，恰好给出 \(D,T\) 定义中的条件。这两个构造互逆。在这些同构下，\(\eta_A,\eta_B\) 是有限支撑多项式族的嵌入，\(\eta_C\) 是 \(\bigoplus_n S_n\hookrightarrow T\) 的嵌入。

记 \(\delta(a)=(t^{\nu_n}a_n)_n\)。诱导映射为
\[
\widehat\iota(a)=\delta(a),\qquad
\widehat q(b)=(b_n\bmod t^{\nu_n})_n.
\]
因 \(t^{\nu_n}\) 在 \(S\) 中非零，\(\widehat\iota\) 单射。对 \(c\in T\)，令 \(\ell(c)_n\) 为 \(c_n\) 的次数小于 \(\nu_n\) 的多项式代表，零坐标取 \(0\)。由于
\[
c_n\in t^mS_n\quad\Longleftrightarrow\quad \ell(c)_n\in t^mS,
\]
有 \(\ell(c)\in D\) 且 \(\widehat q(\ell(c))=c\)，故 \(\widehat q\) 满射。置
\[
H=\{a\in\textstyle\prod_n S\mid \delta(a)\in D\}.
\]
逐坐标求原像便得到像、核以及每个纤维
\[
\operatorname{im}\widehat\iota=\delta D,\qquad
\ker\widehat q=\delta H,\qquad
\widehat q^{-1}(c)=\ell(c)+\delta H\quad(c\in T).
\]

为了计算闭包，注意对每个 \(m\ge1\) 都有
\[
t^mD=D\cap\prod_n t^mS,\qquad
t^mT=T\cap\prod_n t^mS_n. \tag{1}
\]
第一式成立是因为把右边的族逐坐标除以 \(t^m\) 后仍属于 \(D\)。第二式可对 \(\ell(c)\) 作同样的除法，再逐坐标约化到 \(S_n\)。因此 \(T\) 分离，连续映射 \(\widehat q\) 的核是闭的。若 \(b\in\delta H\)，对给定的 \(m\) 仅保留 \(b_n\notin t^mS\) 的有限个坐标。所得族支撑有限，且各坐标均可被 \(t^{\nu_n}\) 整除，故属于 \(\delta D\)。它与 \(b\) 的差属于 \(t^mD\)。这就证明
\[
\boxed{\ \overline{\operatorname{im}\widehat\iota}=\delta H=\ker\widehat q.\ }
\]

若所有 \(\nu_n\le d\)，则对 \(a\in H\)，几乎所有 \(n\) 都满足 \(t^{\nu_n}a_n\in t^{m+d}S\)，从而 \(a_n\in t^mS\)。故 \(H=D\)。若指数列无界，取互异的 \(n_i\) 使 \(\nu_{n_i}\ge i\)。在这些位置取 \(1\)、其余位置取 \(0\) 的族属于 \(H\setminus D\)。由于 \(\delta\) 单射，完成列在 \(\widehat A,\widehat C\) 处总是正合，在 \(\widehat B\) 处正合的充要条件，也就是整列短正合的充要条件，为
\[
\boxed{\ \sup_{n\ge1}\nu_n<\infty.\ }
\]

## 2. \(E\) 的坐标、\(Q\) 的挠元与 \(p\) 的右逆

在 \(Q=D/\delta D\) 中用 \([b]\) 表示 \(b\) 的类。由第一部分，\(p\) 满射，且有 \(S\) 线性同构
\[
H/D\xrightarrow{\ \sim\ }E,\qquad a+D\longmapsto[\delta a].
\]
特别地，\(E=0\) 当且仅当指数列有界。

把 \(E\) 进一步写成幂级数模，可以同时看出它的挠性和完成。对 \(d\ge0\)，令
\[
I_d=\{n\mid \nu_n=d\},\qquad V_d=k^{(I_d)},\qquad
V=\bigoplus_{d\ge0}V_d,\qquad W=\prod_{d\ge0}V_d,\qquad U=W/V,
\]
其中 \(k^{(I_d)}\) 表示 \(I_d\) 上有限支撑的标量族。将 \(a_n\) 展开为 \(\sum_{i\ge0}a_{i,n}t^i\)，记 \(a_i=(a_{i,n})_n\)。则
\[
a\in D\ \Longleftrightarrow\ \forall i,\ a_i\in V,\qquad
a\in H\ \Longleftrightarrow\ \forall i,\ a_i\in W.
\]
第一式来自每阶约化的有限支撑条件。对于第二式，在 \(I_d\) 上，\(\delta a\) 的 \(t^{i+d}\) 系数就是 \(a_{i,n}\)，所以 \(\delta a\in D\) 蕴含每个 \(a_i\) 在每个 \(I_d\) 上支撑有限。反过来，\(\delta a\) 的 \(t^h\) 系数只涉及 \(0\le d\le h\) 的有限个层，因此其支撑也有限。

于是逐系数取商给出
\[
\boxed{\ E\xrightarrow{\ \sim\ }U[[t]],\qquad
[\delta a]\longmapsto\sum_{i\ge0}(a_i+V)t^i.\ } \tag{2}
\]
这里 \(U[[t]]\) 带通常的形式幂级数 \(S\) 作用。上式的零类恰对应 \(a\in D\)，任意系数串都可逐项选取 \(W\) 中的代表，故确为同构。乘 \(t\) 在 \(U[[t]]\) 上是单射，而 \(S\) 中每个非零元都是单位乘以 \(t\) 的某次幂，所以 **\(E\) 是无挠 \(S\) 模**。

对 \(c\in C=\bigoplus_n S_n\)，有 \(j(c)=[\ell(c)]\)。由 \(pj=\eta_C\) 得 \(\ker j=0\)。任意有限支撑的 \(b\in D\) 与 \(\ell(\widehat q(b))\) 之差都属于 \(\delta D\)，因为该差逐坐标除以 \(t^{\nu_n}\) 后仍支撑有限。因此 **\(j(C)\) 恰由 \(Q\) 中有有限支撑代表的类组成**，且此识别与 \(S\) 作用相容。

固定 \(r\ge1\)。若 \(t^r[b]=0\)，则 \(t^rb=\delta a\) 对某个 \(a\in D\) 成立。令
\[
F=\{n\mid a_n\notin t^rS\}.
\]
此集有限。在 \(F\) 外取 \(a'_n=a_n/t^r\)，在 \(F\) 上取 \(a'_n=0\)，得到 \(a'\in D\)。于是 \(b-\delta a'\) 的支撑包含于 \(F\)，故 \([b]\in j(C)\)。再由 \(j\) 单射，逐坐标计算得
\[
Q[t^r]=j\!\left(\bigoplus_n t^{\max(\nu_n-r,0)}S_n\right),\qquad
\bigcup_{r\ge1}Q[t^r]=j(C).
\]
最后一个等式用到了 \(C\) 中每个元素都支撑有限。

若指数列有界，\(p\) 是同构，其逆即为 \(S\) 线性右逆。若指数列无界，仍取 \(\nu_{n_i}\ge i\)，定义
\[
c_{n_i}=t^{\nu_{n_i}-1}\bmod t^{\nu_{n_i}},\qquad
c_n=0\quad(n\notin\{n_i\mid i\ge1\}).
\]
因 \(\nu_{n_i}-1\to\infty\)，有 \(c\in T\)。此元素满足 \(tc=0\)，且支撑无限。若存在 \(S\) 线性右逆 \(\sigma\)，则 \(\sigma(c)\in Q[t]\)，而 \(p(Q[t])\subseteq\eta_C(C)\) 中的元素都支撑有限，与 \(p\sigma(c)=c\) 矛盾。故
\[
\boxed{\ p\text{ 存在 }S\text{ 线性右逆}\quad\Longleftrightarrow\quad
\sup_n\nu_n<\infty.\ }
\]

## 3. 有限层、完成与两种拓扑

由闭包公式，对每个 \(m\ge1\) 都有 \(\delta H\subseteq\delta D+t^mD\)，故 \(E\subseteq t^mQ\)。若 \(p(x)=t^mc\)，由满射性可取 \(y\in Q\) 使 \(p(y)=c\)。于是 \(x-t^my\in E\subseteq t^mQ\)。这证明
\[
p^{-1}(t^mT)=t^mQ.
\]
因此 \(p\) 在每个有限层诱导同构。利用 (1)，其坐标公式为
\[
Q/t^mQ\xrightarrow[\sim]{\,p_m\,}T/t^mT
 \simeq\bigoplus_n S/(t^{\min(m,\nu_n)}),\qquad
[b]\bmod t^mQ\longmapsto
 (b_n\bmod t^{\min(m,\nu_n)})_n .
\]
由于 \(T\) 分离，随即得到
\[
\boxed{\ \bigcap_{m\ge1}t^mQ=p^{-1}(0)=E.\ }
\]

这些有限层同构与自然约化相容。按第一部分的相容记录还原坐标，得到
\[
\widehat Q\simeq T,\qquad \widehat{\widehat C}\simeq T.
\]
在这些识别下，典范映射 \(\eta_Q\) 就是 \(p:Q\to T\)，\(\eta_{\widehat C}\) 是 \(T\) 的恒等映射，而完成映射 \(\widehat p:\widehat Q\to\widehat{\widehat C}\) 也是 \(T\) 的恒等映射。

最后，在 (2) 的坐标下，\(t^mE\) 恰由前 \(m\) 个系数为零的级数组成。因此
\[
E/t^mE\simeq\bigoplus_{i=0}^{m-1}Ut^i,\qquad
\widehat E\simeq U[[t]]\simeq E.
\]
典范映射 \(\eta_E\) 把级数送到它的所有相容截断，逐项恢复系数就是其逆。故 **\(E\) 自身的 \(t\) 进拓扑总是分离且完备**。

从 \(Q\) 继承的子空间拓扑满足 \(E\cap t^mQ=E\) 对所有 \(m\) 成立，因而其开集只有 \(\varnothing\) 和 \(E\)。由自身拓扑的分离性，两种拓扑相同当且仅当 \(E=0\)，亦即当且仅当 \(\sup_n\nu_n<\infty\)。