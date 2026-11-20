记 \(S_d=S/(t^d)\)，其中 \(S_0=0\)，并令 \(L_n=S_{\nu_n}\)。由 \(R/(t^d)\simeq S_d\)，可将 \(C\) 识别为 \(\bigoplus_n L_n\)。

## 1. 完成列、闭包与纤维

令 \(P=\prod_{n\ge1}S\)，并定义
\[
\begin{aligned}
F&=\{x\in P:\ \forall m\ge1,\ \{n:x_n\notin t^mS\}\text{ 有限}\},\\
T&=\{y\in\textstyle\prod_n L_n:\ \forall m\ge1,\ 
                  \{n:y_n\notin t^mL_n\}\text{ 有限}\}.
\end{aligned}
\]
则有典范的 \(S\) 模同构
\[
\widehat A\simeq F,\qquad \widehat B\simeq F,\qquad \widehat C\simeq T.
\]

具体地，\(x\in F\) 的第 \(m\) 层记录是 \((x_n\bmod t^m)_n\in\bigoplus_n S_m\)。反过来，一族相容记录在每个坐标 \(n\) 上确定唯一的 \(x_n\in k[[t]]\)，而第 \(m\) 层的有限支撑恰好给出 \(F\) 的定义条件。对 \(C\)，第 \(m\) 层记录属于
\[
C/t^mC=\bigoplus_n L_n/t^mL_n
       \simeq\bigoplus_n S_{\min(m,\nu_n)}.
\]
固定 \(n\) 后，该坐标从 \(m\ge\max(1,\nu_n)\) 起稳定，给出唯一的 \(y_n\in L_n\)。各层记录的有限支撑同样恰好给出 \(y\in T\)。这些对应都与逐层的标量作用相容。\(\eta_A,\eta_B\) 将有限支撑的多项式族嵌入 \(F\)，\(\eta_C\) 是 \(\bigoplus_n L_n\hookrightarrow T\)。

在这些模型下，诱导映射为
\[
\widehat\iota(x)=Dx=(t^{\nu_n}x_n)_n,\qquad
\widehat q(x)=\rho(x)=(x_n\bmod t^{\nu_n})_n.
\]
\(D\) 在 \(P\) 上单射，故 \(\widehat\iota\) 单射。对 \(y\in T\)，令 \(\ell_n(y_n)\) 为 \(y_n\) 的次数小于 \(\nu_n\) 的多项式代表元，零元取代表元 \(0\)。对每个 \(m\)，有
\[
\ell_n(y_n)\in t^mS\quad\Longleftrightarrow\quad y_n\in t^mL_n.
\]
因此 \(\ell(y)\in F\) 且 \(\rho(\ell(y))=y\)，故 \(\widehat q\) 满射。

令
\[
U=\{a\in P:Da\in F\},\qquad
K=F\cap\prod_n t^{\nu_n}S=DU.
\]
于是 \(\ker\widehat q=K\)，\(\operatorname{im}\widehat\iota=DF\)，而每个纤维为
\[
\boxed{\ \widehat q^{-1}(y)=\ell(y)+K
       =\{\ell(y)+Da:a\in U\}.\ }
\]

为计算闭包，注意 \(F\cap\prod_n t^mS=t^mF\)，因为逐坐标除以 \(t^m\) 后，所得坐标仍趋于零。若 \(x\in K\)，只保留满足 \(x_n\notin t^mS\) 的有限多个坐标，就得到一个属于 \(DF\) 的元素，与 \(x\) 之差属于 \(t^mF\)。反过来，若 \(x\in\bigcap_m(DF+t^mF)\)，则对每个 \(n\) 取 \(m\ge\max(1,\nu_n)\)，可得 \(x_n\in t^{\nu_n}S\)。故
\[
\boxed{\ \overline{\operatorname{im}\widehat\iota}
       =\bigcap_{m\ge1}(DF+t^mF)=K=\ker\widehat q.\ }
\]

完成列总在 \(\widehat A,\widehat C\) 处正合，在 \(\widehat B\) 处正合的充要条件是 \(U=F\)。若所有 \(\nu_n\le d\)，则 \(Da\in F\) 意味着对每个 \(m\)，除有限多个 \(n\) 外都有 \(t^{\nu_n}a_n\in t^{m+d}S\)，从而 \(a_n\in t^mS\)。故 \(U=F\)。若指数无界，取互异的 \(n_i\) 使 \(\nu_{n_i}\ge i\)，令 \(a_{n_i}=1\)，其余坐标为零，则 \(Da\in F\) 而 \(a\notin F\)。因此
\[
\boxed{\ \text{完成列短正合}\quad\Longleftrightarrow\quad
                 \sup_n\nu_n<\infty.\ }
\]

## 2. \(E\) 的坐标、\(Q\) 的挠元与 \(p\) 的分裂

在 \(Q=F/DF\) 中，\(p([x])=\rho(x)\)，所以 \(p\) 总是满射。由 \(D\) 的单射性，
\[
U/F\xrightarrow{\ \sim\ }E=K/DF,\qquad a+F\longmapsto Da+DF.
\]
特别地，**\(E=0\) 当且仅当指数列有界**。

把这个模型按 \(t\) 的次数展开，还能看出 \(E\) 的挠性和完成。令
\[
V_0=k^{(\mathbb N_{\ge1})},\qquad
V=\{v\in k^{\mathbb N_{\ge1}}:\ \forall d\ge0,\
        \{n:\nu_n\le d,\ v_n\ne0\}\text{ 有限}\},\qquad W=V/V_0.
\]
写 \(a_n=\sum_{i\ge0}a_{i,n}t^i\)，令 \(v_i=(a_{i,n})_n\)。则 \(a\in F\) 当且仅当每个 \(v_i\in V_0\)，而 \(a\in U\) 当且仅当每个 \(v_i\in V\)。为证后一断言，若 \(a_{i,n}\ne0\) 且 \(\nu_n\le d\)，则 \((Da)_n\notin t^{i+d+1}S\)。反过来，若 \((Da)_n\notin t^mS\)，则 \(\nu_n<m\)，且至少一个 \(i<m\) 满足 \(a_{i,n}\ne0\)。对这有限多个 \(i\) 应用 \(V\) 的定义即可。

因此，逐系数取商给出
\[
\boxed{\ E\simeq W[[t]],\qquad
       Da+DF\longmapsto\sum_{i\ge0}(v_i+V_0)t^i.\ }
\]
这里 \(W[[t]]\) 是系数在 \(W\) 中的形式幂级数模。每个系数都可在 \(V\) 中选取提升，故该映射满射，且幂级数乘法的系数公式给出 \(S\) 线性。乘以 \(t\) 在此模型中单射，而 \(S\) 的每个非零元都是单位乘以 \(t\) 的幂，故 **\(E\) 是无挠 \(S\) 模**。

由于 \(pj=\eta_C\) 单射，\(\ker j=0\)。\(j(C)\) 正是 \(Q\) 中具有有限支撑代表元的类，因为任一有限支撑的 \(S\) 坐标族与其逐坐标多项式代表元之差属于 \(DF\)。更精确地，对每个 \(r\ge1\)，
\[
\boxed{\ Q[t^r]=j\!\left(\bigoplus_n t^{\max(\nu_n-r,0)}L_n\right)
                =j(C[t^r]).\ }
\]
事实上，若 \(t^r[x]=0\)，则 \(t^rx=Da\) 对某个 \(a\in F\) 成立。凡 \(a_n\in t^rS\)，约去 \(t^r\) 即得 \(x_n\in t^{\nu_n}S\)。所以 \(\rho(x)\) 只有有限多个非零坐标，确定了一个 \(c\in C[t^r]\)。于是 \([x]-j(c)\in E\) 且被 \(t^r\) 杀死，由 \(E\) 无挠即得 \([x]=j(c)\)。反向包含由 \(j\) 的线性得到。每个 \(c\in C\) 都有有限支撑，故
\[
\bigcup_{r\ge1}Q[t^r]=j(C).
\]

最后，由闭包公式，\(E\subseteq t^mQ\) 对每个 \(m\) 成立，而幂级数模型给出 \(\bigcap_m t^mE=0\)。若 \(s\) 是 \(p\) 的 \(S\) 线性右逆，则 \(h=\operatorname{id}_Q-sp:Q\to E\) 在 \(E\) 上为恒等，因而
\[
E=h(E)\subseteq\bigcap_m h(t^mQ)\subseteq\bigcap_m t^mE=0.
\]
反之，若 \(E=0\)，满射 \(p\) 本身就是同构。故 **\(p\) 存在 \(S\) 线性右逆当且仅当 \(\sup_n\nu_n<\infty\)**。

## 3. 逐层商、再次完成与两种拓扑

将 \(F\) 模 \(t^m\) 约化得到 \(\bigoplus_n S_m\)，其中 \(DF\) 的像为 \(\bigoplus_n t^{\nu_n}S_m\)。于是
\[
Q/t^mQ=F/(DF+t^mF)\simeq\bigoplus_n S_{\min(m,\nu_n)}.
\]
在 \(T\) 一侧，第 \(m\) 层投影也满射到这个直和，因为有限支撑记录可以逐坐标提升。其核恰为 \(t^mT\)。事实上，若记录为零，则 \(\ell(y)\) 的所有坐标都被 \(t^m\) 整除，故 \(\ell(y)/t^m\in F\)，从而 \(y=t^m\rho(\ell(y)/t^m)\)。因此在上述坐标下，\(p\) 诱导的映射是
\[
\boxed{\quad
Q/t^mQ\ \simeq\ \bigoplus_n S_{\min(m,\nu_n)}
\ \xrightarrow{\ \operatorname{id}\ }\ 
\bigoplus_n S_{\min(m,\nu_n)}\ \simeq\ \widehat C/t^m\widehat C .
\quad}
\]

这些恒等映射与自然约化相容。取逆极限并使用第一部分的相容记录模型，得到
\[
\widehat Q\simeq T,\qquad
\widehat{\widehat C}\simeq T,\qquad
\eta_Q=p,\qquad \eta_{\widehat C}=\operatorname{id}_T,\qquad
\widehat p=\operatorname{id}_T
\]
（均在所示识别下）。特别地，
\[
\boxed{\ \bigcap_{m\ge1}t^mQ=\ker\eta_Q=E.\ }
\]

对于 \(E\simeq W[[t]]\)，模 \(t^mE\) 就是保留次数小于 \(m\) 的系数。因此相容的截断族唯一恢复整个幂级数，给出 \(\widehat E\simeq W[[t]]\simeq E\)，典范映射 \(\eta_E\) 在此识别下为恒等。故 \(E\) 自身的 \(t\) 进拓扑总是完备且分离。

从 \(Q\) 继承的子空间拓扑则以 \(E\cap t^mQ=E\) 为零点邻域基，因而其开集只有 \(\varnothing\) 和 \(E\)。由于自身拓扑分离，**两种拓扑相同当且仅当 \(E=0\)，亦即当且仅当指数列有界**。