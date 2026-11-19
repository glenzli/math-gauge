## 1. 完成的坐标模型与正合性

令 \(T_n=S/t^{\nu_n}S\)，用自然同构 \(R/(t^{\nu_n})\cong T_n\) 将 \(C\) 写成 \(\bigoplus_n T_n\)。当 \(\nu_n=0\) 时，\(T_n=0\)。定义
\[
\begin{aligned}
D&=\left\{(b_n)\in\prod_n S:
   \text{对每个 }m\ge1,\ b_n\bmod t^mS\text{ 只有有限个非零坐标}\right\},\\
T&=\left\{(c_n)\in\prod_n T_n:
   \text{对每个 }m\ge1,\ c_n\bmod t^mT_n\text{ 只有有限个非零坐标}\right\}.
\end{aligned}
\]
则有 \(S\) 线性同构
\[
\widehat A\cong D,\qquad \widehat B\cong D,\qquad \widehat C\cong T.
\]
对于 \(A,B\)，坐标序列逐项模 \(t^m\) 约化，给出第 \(m\) 层的有限支撑记录。反过来，相容记录在每个坐标上给出一个 \(S\) 元素，每层的有限支撑性恰好给出 \(D\) 的条件。对于 \(C\)，第 \(m\) 层为
\[
C/t^mC\cong\bigoplus_n T_n/t^mT_n
\cong\bigoplus_n S/t^{\min(m,\nu_n)}S.
\]
固定 \(n\) 后，该坐标从 \(m\ge\nu_n\) 起稳定为 \(T_n\)，所以相容记录恰好来自 \(T\) 中的序列。典范映射 \(\eta_A,\eta_B\) 把有限支撑的多项式序列视为幂级数序列，\(\eta_C\) 则是有限支撑序列到 \(T\) 的包含。

在这些模型中，
\[
\widehat\iota((a_n))=(t^{\nu_n}a_n)_n,\qquad
\widehat q((b_n))=(b_n\bmod t^{\nu_n}S)_n .
\]
由于 \(S\) 是整环，\(\widehat\iota\) 单射。对 \(c\in T\)，令 \(\rho_n(c_n)\) 为 \(c_n\) 的次数小于 \(\nu_n\) 的多项式代表元，\(T_n=0\) 时取零。对每个 \(m\)，有
\[
\rho_n(c_n)\in t^mS\quad\Longleftrightarrow\quad c_n\in t^mT_n.
\]
因此 \(\rho(c)=(\rho_n(c_n))_n\in D\)，且 \(\widehat q(\rho(c))=c\)，故 \(\widehat q\) 满射。

记 \(J=\operatorname{im}\widehat\iota\)，并用 \(v\) 表示 \(t\) 进阶数，约定 \(v(0)=+\infty\)。置
\[
X=\left\{(a_n)\in\prod_n S:
   \text{对每个 }m\ge1,\ \{n:\nu_n+v(a_n)<m\}\text{ 有限}\right\}.
\]
于是
\[
K:=\ker\widehat q
 =D\cap\prod_n t^{\nu_n}S
 =\{(t^{\nu_n}a_n)_n:a\in X\},\qquad
\widehat q^{-1}(c)=\rho(c)+K .
\]

在 \(D\) 中，\(t^mD=D\cap\prod_n t^mS\)，因为将右边的序列逐项除以 \(t^m\) 后仍属于 \(D\)。若 \(b\notin K\)，取一个满足 \(b_n\notin t^{\nu_n}S\) 的坐标，则 \(b+t^{\nu_n}D\) 与 \(K\) 不交，所以 \(K\) 闭。反过来，给定 \(b\in K\) 和 \(m\ge1\)，只保留 \(b_n\notin t^mS\) 的有限个坐标，得到的序列属于 \(J\)，且与 \(b\) 相差一个 \(t^mD\) 中的元素。因此
\[
\overline J=K,\qquad K\subseteq J+t^mD\quad(m\ge1).
\]

完成列在 \(\widehat A\) 和 \(\widehat C\) 处总是正合。在 \(\widehat B\) 处正合当且仅当 \(X=D\)。若所有 \(\nu_n\le L\)，则 \(v(a_n)<m\) 蕴含 \(\nu_n+v(a_n)<m+L\)，故 \(X=D\)。若指数列无界，选取 \(\nu_{n_j}\) 严格递增的子列，并令 \(a_{n_j}=1\)，其余坐标为零，则 \(a\in X\setminus D\)。所以**完成列短正合当且仅当指数列有界**。

## 2. 核 \(E\)、挠元与右逆

由逐项乘以 \(t^{\nu_n}\) 得到坐标同构
\[
X/D\xrightarrow{\ \sim\ }E=K/J,\qquad
[a]\longmapsto [(t^{\nu_n}a_n)_n].
\]
还可以按幂级数系数描述这个商。令
\[
V=\left\{(u_n)\in\prod_n k:
  \text{对每个 }L\ge0,\ \{n:\nu_n\le L,\ u_n\ne0\}\text{ 有限}\right\},
\qquad
W=V/k^{(\mathbb N)}.
\]
其中 \(k^{(\mathbb N)}\) 是有限支撑序列空间。写 \(a_n=\sum_{\ell\ge0}a_{n,\ell}t^\ell\)。若 \(a\in X\)，则在 \(\nu_n\le L\) 的坐标中，\(a_{n,\ell}\ne0\) 蕴含 \(\nu_n+v(a_n)<L+\ell+1\)，故每一阶的系数序列属于 \(V\)。反过来，若每一阶的系数序列都属于 \(V\)，则对固定的 \(m\)，条件 \(\nu_n+v(a_n)<m\) 只涉及有限个阶数及其对应的有界指数范围，因而只在有限个坐标成立。类似地，\(a\in D\) 恰好要求每一阶的系数序列具有有限支撑。

逐阶取商便给出 \(S\) 线性同构
\[
E\cong W[[t]],\qquad
[a]\longmapsto \sum_{\ell\ge0}[(a_{n,\ell})_n]t^\ell .
\]
这里 \(W[[t]]\) 是系数取值于 \(W\) 的形式幂级数模，\(S\) 按幂级数乘法作用。任取每一阶系数类的代表元即可得到原像。乘以 \(t\) 是单射，而 \(S\) 的任意非零元都是 \(t\) 的幂乘以单位，故 \(E\) 是**无挠 \(S\) 模**。由 \(E\cong X/D\) 可知，**\(E=0\) 当且仅当指数列有界**。

由于 \(p\circ j=\eta_C\) 是有限支撑序列的包含，\(\ker j=0\)。\(j(C)\) 恰好是 \(Q\) 中可由有限支撑序列代表的类，因为有限支撑的幂级数序列可以逐项换成模 \(t^{\nu_n}\) 的多项式代表元，差值属于 \(J\)。更精确地，对每个 \(r\ge1\)，
\[
Q[t^r]:=\ker(t^r:Q\to Q)
 =j(C[t^r])
 =j\!\left(\bigoplus_n t^{\max(\nu_n-r,0)}T_n\right).
\]
事实上，若 \(t^r[b]=0\)，则存在 \(a\in D\) 使 \(t^rb_n=t^{\nu_n}a_n\)。取有限集 \(F=\{n:a_n\notin t^rS\}\)。在 \(F\) 外，将 \(a_n\) 除以 \(t^r\)，在 \(F\) 内填零，所得序列仍属于 \(D\)。它经 \(\widehat\iota\) 的像恰好是 \(b\) 在 \(F\) 外的部分。因此 \([b]\) 由 \(F\) 上的有限支撑序列代表，属于 \(j(C)\)。再由 \(j\) 的单射性及各 \(T_n\) 中的计算得到上式。每个 \(C\) 元素都由某个 \(t^r\) 杀死，故 \(j(C)=\bigcup_{r\ge1}Q[t^r]\)。

\(p\) 总是满射，因为 \(\widehat q\) 满射。若指数列有界，则 \(E=0\)，所以 \(p\) 的逆就是 \(S\) 线性右逆。反过来，若 \(s\) 是 \(S\) 线性右逆，则 \(1-sp\) 给出从 \(Q\) 到 \(E\) 且在 \(E\) 上为恒等的映射。由 \(K\subseteq J+t^mD\) 可知 \(E\subseteq t^mQ\) 对每个 \(m\) 成立。应用 \(1-sp\) 得 \(E\subseteq t^mE\)。而 \(W[[t]]\) 中属于所有 \(t^mW[[t]]\) 的幂级数的各阶系数全为零，所以 \(E=0\)。因此 **\(p\) 存在 \(S\) 线性右逆当且仅当指数列有界**。

## 3. 商层、再完成与两种拓扑

对每个 \(m\ge1\)，满射性及 \(E\subseteq t^mQ\) 给出
\[
p^{-1}(t^mT)=t^mQ.
\]
确实，若 \(p(x)\in t^mT\)，可选 \(y\in Q\) 使 \(p(x)=t^mp(y)\)，于是 \(x-t^my\in E\subseteq t^mQ\)。

逐坐标约化 \(T\to\bigoplus_nT_n/t^mT_n\) 是满射，因为有限支撑的记录可以用有限支撑的序列提升。其核是 \(t^mT\)。若每个 \(c_n\in t^mT_n\)，则 \(\rho(c)\in D\cap\prod_n t^mS=t^mD\)，将 \(\rho(c)\) 除以 \(t^m\) 后再逐项约化到 \(T_n\)，就得到 \(c\) 在 \(T\) 中的一个 \(t^m\) 原像。因此 \(p\) 诱导同构
\[
Q/t^mQ\xrightarrow{\ \sim\ }\widehat C/t^m\widehat C
\cong\bigoplus_n S/t^{\min(m,\nu_n)}S.
\]
在右端的坐标下，由 \(b\in D\) 代表的类被送到 \((b_n\bmod t^{\min(m,\nu_n)}S)_n\)。这些同构与自然约化相容。

每个坐标 \(T_n\) 都被 \(t^{\nu_n}\) 杀死，所以 \(\bigcap_{m\ge1}t^mT=0\)。取上面的原像可得
\[
\bigcap_{m\ge1}t^mQ=E.
\]
取各层同构的逆极限得到 \(\widehat Q\cong T=\widehat C\)，在此识别下 \(\eta_Q=p\)。同一组坐标记录也给出 \(\widehat{\widehat C}\cong T\)，且 \(\eta_{\widehat C}\) 对应于恒等映射。因此 \(p\) 诱导的完成映射 \(\widehat p:\widehat Q\to\widehat{\widehat C}\) 在两端识别为 \(T\) 后就是恒等映射。

对 \(E\) 自身的 \(t\) 进拓扑，\(E/t^mE\) 在 \(W[[t]]\) 模型中保留前 \(m\) 个系数。相容的截断记录唯一确定全部系数，故
\[
\widehat E\cong W[[t]],\qquad
\eta_E\left(\sum_{\ell\ge0}w_\ell t^\ell\right)
=\left(\sum_{\ell=0}^{m-1}w_\ell t^\ell\bmod t^mE\right)_{m\ge1}.
\]
所以 \(\eta_E\) 是同构，且 \(E\) 自身的 \(t\) 进拓扑总是分离。另一方面，从 \(Q\) 继承的零点邻域基由 \(E\cap t^mQ=E\) 给出，所以子空间拓扑是平凡拓扑。**这两种拓扑相同当且仅当指数列有界**，此时 \(E=0\)。