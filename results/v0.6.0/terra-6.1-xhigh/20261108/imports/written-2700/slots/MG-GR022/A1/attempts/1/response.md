记 \(v(0)=\infty\)，并约定 \(S/(t^0)=0\)。下面所有“有限支撑”都指只有有限多个坐标非零。

设
\[
D=\left\{x=(x_n)\in S^{\mathbb N}:
\text{对每个 }m\ge1,\ \#\{n:v(x_n)<m\}<\infty\right\}.
\]
这是通常的受限直积，也可表述为 \(v(x_n)\to\infty\)。再置
\[
H=\{(t^{\nu_n}a_n)_n:a\in D\},\qquad
K=D\cap\prod_{n\ge1}t^{\nu_n}S.
\]

以下的主要判据都是同一个条件：
\[
\boxed{\quad \sup_{n\ge1}\nu_n<\infty.\quad} \tag{*}
\]

### 1. 完成的坐标模型、正合性与纤维

有自然的 \(S\) 模同构
\[
\widehat A\cong D,\qquad \widehat B\cong D,
\]
分别使用基 \((f_n)\) 和 \((e_n)\)。此外，
\[
\widehat C\cong
T:=\left\{(y_n)\in\prod_{n\ge1}S/(t^{\nu_n}):
\begin{array}{l}
\text{对每个 }m\ge1,\ \text{只有有限多个 }n\\
\text{满足 }y_n\notin t^m(S/(t^{\nu_n}))
\end{array}\right\}.
\]
在这些坐标下，
\[
\widehat\iota(a)_n=t^{\nu_n}a_n,\qquad
\widehat q(x)_n=x_n\bmod t^{\nu_n}.
\]

这些模型与相容商记录的对应如下。一个 \(x\in D\) 在第 \(m\) 层给出有限支撑记录
\[
(x_n\bmod t^m)_n\in\bigoplus_n R/(t^m).
\]
反过来，一组相容记录逐坐标确定 \(S\) 中的元素，而每层有限支撑正是 \(x\in D\) 的条件。对 \(C\)，第 \(m\) 层是
\[
C/t^mC\cong\bigoplus_n R/(t^{\min(m,\nu_n)}),
\]
相同的逐坐标过程给出上面的 \(T\)。

完成列
\[
0\longrightarrow\widehat A\xrightarrow{\widehat\iota}
\widehat B\xrightarrow{\widehat q}\widehat C\longrightarrow0
\]
中，\(\widehat\iota\) 总是单射，\(\widehat q\) 总是满射，并且
\[
\operatorname{im}\widehat\iota=H,\qquad
\ker\widehat q=K.
\]
满射性可直接看到：每个 \(y_n\in S/(t^{\nu_n})\) 取次数小于 \(\nu_n\) 的多项式代表 \(x_n\)，得到的 \(x\) 属于 \(D\)。

因此，若 \(y\in\widehat C\) 且 \(x\in D\) 是它的任意一个提升，则
\[
\widehat q^{-1}(y)=x+K.
\]
而且
\[
\boxed{\ \overline{\operatorname{im}\widehat\iota}=K\ },
\]
这里的闭包取自 \(\widehat B\) 的 \(t\) 进拓扑。确实，\(K\) 是 \(\widehat q\) 的核，因而闭；另一方面，\(K\) 中任一元素的有限截断均属于 \(H\)，并 \(t\) 进收敛到该元素。

完成列在 \(\widehat B\) 处正合，当且仅当 \(H=K\)，也当且仅当条件 \((*)\) 成立。因此，**完成列短正合当且仅当指数列有界**。

证明最后一个判据：若所有 \(\nu_n\le N\)，且 \(x_n=t^{\nu_n}a_n\) 构成 \(D\) 中的元素，则
\[
v(a_n)\ge v(x_n)-N\longrightarrow\infty,
\]
故 \(a\in D\)，即 \(K=H\)。若指数列无界，可选互异的 \(n_i\) 使 \(\nu_{n_i}\ge i\)。令 \(a_{n_i}=1\)，其余坐标为零，则 \((t^{\nu_n}a_n)\in K\)，但 \(a\notin D\)，故该元素不属于 \(H\)。

### 2. 核、挠元与右逆

令
\[
L=\{a=(a_n)\in S^{\mathbb N}:(t^{\nu_n}a_n)_n\in D\}.
\]
逐坐标乘以 \(t^{\nu_n}\) 给出 \(L\cong K\)，并把 \(D\) 对应到 \(H\)。因此
\[
\boxed{\quad E=K/H\cong L/D.\quad}
\]

映射 \(j:C\to Q\) 是单射。它的像由 \(D/H\) 中具有有限支撑代表的类组成，也就是
\[
\ker j=0,\qquad
\operatorname{im}j
=\{x+H:x\in D\text{ 有限支撑}\}.
\]
事实上，有限支撑的 \(S\) 坐标可逐坐标模 \(t^{\nu_n}\) 换成多项式代表；而有限支撑的 \(b\in B\) 若属于 \(H\)，则它已经属于 \(\iota(A)\)。

对每个 \(r\ge1\)，置
\[
D_r=\left\{\bigl(t^{\max(\nu_n-r,0)}a_n\bigr)_n:a\in D\right\}.
\]
则 \(H\subseteq D_r\subseteq D\)，并且 \(Q\) 中被 \(t^r\) 杀死的元素恰为
\[
\boxed{\quad Q[t^r]=D_r/H.\quad}
\]
确实，\(t^r x\in H\) 等价于：当 \(\nu_n>r\) 时，\(x_n/t^{\nu_n-r}\) 存在，且这些商与 \(\nu_n\le r\) 时的 \(x_n\) 一起构成 \(D\) 中的序列。故 \(Q\) 的全部 \(S\) 挠元为
\[
\bigcup_{r\ge1}D_r/H,
\]
因为 \(S\) 的每个非零元素都是某个 \(t^r\) 乘以单位。

相反，\(E\) 是**无挠 \(S\) 模**：在 \(L/D\) 中，若 \(t^r a\in D\)，则 \(a\in D\)，因为把所有赋值加上同一个固定整数不会改变其是否趋于无穷。

由 \(\widehat q\) 的满射性，\(p:Q\to\widehat C\) 总是满射。并且
\[
\boxed{\quad
E=0
\ \Longleftrightarrow\
p\text{ 是同构}
\ \Longleftrightarrow\
p\text{ 有 }S\text{ 线性右逆}
\ \Longleftrightarrow\ (*) .
\quad}
\]

这里只需证明无界时不存在右逆。仍取互异的 \(n_i\)，使 \(\nu_{n_i}\ge i\)，并定义
\[
y_{n_i}=t^{\nu_{n_i}-1}\bmod t^{\nu_{n_i}},\qquad
y_n=0\quad(n\notin\{n_i\}).
\]
则 \(y\in\widehat C\) 且 \(ty=0\)。若它有被 \(t\) 杀死的提升 \(x+H\in Q\)，就有 \(tx\in H\)。但
\[
\frac{t x_{n_i}}{t^{\nu_{n_i}}}\equiv1\pmod t
\]
对每个 \(i\) 成立，所以这些商不构成 \(D\) 中的序列，矛盾。\(S\) 线性右逆必须把 \(y\) 送到一个被 \(t\) 杀死的提升，因此不存在。

### 3. 商拓扑、完成与两种核拓扑

对每个 \(m\ge1\)，两侧都有自然坐标同构
\[
Q/t^mQ\cong
\bigoplus_n R/(t^{\min(m,\nu_n)})
\cong\widehat C/t^m\widehat C,
\]
在这些同构下，\(p\) 诱导的映射就是恒等映射。因此它对每个 \(m\) 都是同构。

例如，对 \(Q\)，利用 \(D/t^mD\cong\bigoplus_n R/(t^m)\)，再除以 \(H\) 的像，即得左边。对 \(\widehat C\)，坐标模 \(t^m\) 的核正是 \(t^m\widehat C\)：将每个坐标中可除的 \(t^m\) 除去后，受限支撑条件仍成立。

由于 \(\widehat C\) 是分离的，上述各层同构给出
\[
\boxed{\quad \bigcap_{m\ge1}t^mQ=E.\quad}
\]
并且，取逆极限得到自然同构
\[
\boxed{\quad \widehat Q\xrightarrow[\sim]{\widehat p}\widehat C.\quad}
\]
在此同构下，典范映射 \(\eta_Q:Q\to\widehat Q\) 就是 \(p\)。因此 \(\ker\eta_Q=E\)，而 \(\eta_Q\) 总是满射。

对 \(E\) 自身，结论不同：**\(E\) 是 \(t\) 进分离且完备的**。更明确地，令
\[
U_m=\left\{z=(z_n)\in\prod_n S/(t^m):
\text{对每个 }N,\ 
\#\{n:\nu_n\le N,\ z_n\ne0\}<\infty\right\}.
\]
则逐坐标模 \(t^m\) 给出
\[
\boxed{\quad
E/t^mE\cong U_m\big/\bigoplus_n S/(t^m),\qquad
\widehat E\cong E\cong L/D.
\quad}
\]
最后一个同构把 \(a+D\) 送到其各层模 \(t^m\) 的相容记录。

证明这一描述：\(L\) 模 \(t^m\) 的像恰为 \(U_m\)。其核在商 \(L/D\) 中正是 \(t^m(L/D)\)：若 \(a\bmod t^m\) 有限支撑，可先减去一个有限支撑序列 \(h\)，再写 \(a-h=t^m a'\)；由 \((t^{\nu_n}(a_n-h_n))\in D\) 可知 \(a'\in L\)。

这些商的逆极限没有增加新元素。具体地，对一组相容的 \(U_m/\bigoplus S/(t^m)\) 记录，可在每一层只修改有限多个坐标，递归选出逐坐标相容的代表 \(z^{(m)}\in U_m\)。它们逐坐标确定 \(a\in S^{\mathbb N}\)，而所有 \(z^{(m)}\in U_m\) 共同保证 \(a\in L\)。若该逆极限记录为零，则 \(a\bmod t^m\) 对每个 \(m\) 都有限支撑，所以 \(a\in D\)。这同时证明完备性和分离性。

最后，由 \(E=\bigcap_m t^mQ\)，从 \(Q\) 继承到 \(E\) 的子空间拓扑是**平凡拓扑**：每个零点邻域都包含整个 \(E\)。而 \(E\) 自身的 \(t\) 进拓扑分离。因此
\[
\boxed{\quad
E\text{ 自身的拓扑与继承的拓扑相同}
\ \Longleftrightarrow\ E=0
\ \Longleftrightarrow\ \sup_n\nu_n<\infty.
\quad}
\]
在完成映射方面，包含 \(E\hookrightarrow Q\) 诱导的
\[
\widehat E\longrightarrow\widehat Q
\]
是零映射；与此相对，\(\eta_E:E\to\widehat E\) 是同构。