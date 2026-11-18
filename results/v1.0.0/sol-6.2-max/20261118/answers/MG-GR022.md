记 \(S_n=S/t^{\nu_n}S\)。在 \(S\) 上用 \(v\) 表示 \(t\) 阶，令 \(v(0)=\infty\)。在 \(S_n\) 上，用次数小于 \(\nu_n\) 的多项式代表定义非零元素的 \(t\) 阶，也令 \(v(0)=\infty\)。下文说一列阶数趋于无穷，是指对每个 \(m\ge1\)，阶数小于 \(m\) 的指标只有有限个。

## 一、完成的坐标、正合性与纤维

三个完成的坐标模型是
\[
\widehat A\simeq L,\qquad \widehat B\simeq L,\qquad
\widehat C\simeq L_C,
\]
其中
\[
L=\{a\in\textstyle\prod_{n\ge1}S:v(a_n)\to\infty\},
\qquad
L_C=\{c\in\textstyle\prod_{n\ge1}S_n:v(c_n)\to\infty\}.
\]
对 \(A,B\)，第 \(m\) 层商都是 \(\bigoplus_n S/t^mS\)，坐标列 \(a\) 对应的相容记录是 \(\bigl((a_n\bmod t^m)_n\bigr)_m\)。反过来，每个坐标的相容约化记录唯一确定一个幂级数。每层记录的有限支撑条件恰好给出 \(v(a_n)\to\infty\)。

对 \(C=\bigoplus_n S_n\)，第 \(m\) 层是 \(\bigoplus_n S/t^{\min(m,\nu_n)}S\)。坐标列 \(c\) 对应的记录是
\[
\bigl((c_n\bmod t^{\min(m,\nu_n)})_n\bigr)_m.
\]
反过来，第 \(n\) 个坐标由 \(m\ge \nu_n\) 时的稳定值给出。每层记录有限支撑恰好等价于 \(v(c_n)\to\infty\)。这些同构与各层的标量作用相容。典范映射 \(\eta_A,\eta_B\) 将有限支撑的多项式列视为幂级数列，\(\eta_C\) 将有限支撑列包含到 \(L_C\) 中。

诱导映射为
\[
\widehat\iota(a)=(t^{\nu_n}a_n)_n,\qquad
\widehat q(b)=(b_n\bmod t^{\nu_n})_n .
\]
前者逐坐标单射。对每个 \(c\in L_C\)，取各 \(c_n\) 的截断多项式代表 \(b^0_n(c)\)，零坐标取零。因为 \(v(b^0_n(c))=v(c_n)\)，所以 \(b^0(c)\in L\)，这给出 \(\widehat q\) 的满射性。

设
\[
D=\{a\in\textstyle\prod_{n\ge1}S:\nu_n+v(a_n)\to\infty\},
\qquad T(a)=(t^{\nu_n}a_n)_n .
\]
则 \(T:D\to L\) 单射，并且
\[
I:=\operatorname{im}\widehat\iota=T(L),\qquad
K:=\ker\widehat q=T(D).
\]
这里 \(K=T(D)\) 是因为逐坐标除以 \(t^{\nu_n}\) 后，所得序列属于 \(D\) 恰好等价于原序列属于 \(L\)。因此每个纤维都有明确描述
\[
\widehat q^{-1}(c)=b^0(c)+T(D).
\]

为计算闭包，注意对 \(M=L\) 或 \(L_C\) 都有
\[
t^mM=\{x\in M:v(x_n)\ge m\ \text{对所有 }n\}.
\]
乘 \(t^m\) 给出一个包含方向。反向对非零坐标的幂级数或截断多项式代表除以 \(t^m\)，零坐标仍取零。所得非零坐标的阶数只减少 \(m\)，所以所得列仍属于 \(M\)。特别地，\(L_C\) 分离。由于 \(\widehat q\) 是 \(S\) 线性的，它连续，故 \(K\) 闭。每个 \(b\in K\) 的有限支撑截断都属于 \(I\)，且这些截断在 \(L\) 中收敛到 \(b\)。于是
\[
\overline{\operatorname{im}\widehat\iota}=K.
\]

若所有 \(\nu_n\) 有统一上界，则 \(\nu_n+v(a_n)\to\infty\) 蕴含 \(v(a_n)\to\infty\)，所以 \(D=L\)。若 \((\nu_n)\) 无界，可选严格递增的指标 \(n_\ell\)，使 \(\nu_{n_\ell}\ge\ell\)。在这些指标上取值 \(1\)、其余取值 \(0\) 的序列属于 \(D\setminus L\)。因此完成列始终在 \(\widehat A\) 和 \(\widehat C\) 处正合。在 \(\widehat B\) 处正合，也即完成列短正合的充要条件是 **\((\nu_n)\) 有界**。

## 二、\(E\)、\(j\) 与 \(p\) 的右逆

由 \(\widehat q\) 满射可知 \(p\) 始终满射。映射
\[
D/L\xrightarrow{\ \sim\ } E,\qquad a+L\longmapsto T(a)+I
\]
给出 \(E\) 的坐标模型。两个代表列等价，恰好当其差的坐标阶数趋于无穷。由上面对 \(D=L\) 的判定，
\[
E=0\quad\Longleftrightarrow\quad(\nu_n)\text{ 有界}.
\]
此外，对任意 \(r\ge0\)，\(t^ra\in L\) 当且仅当 \(a\in L\)，因为乘 \(t^r\) 只给阶数加上固定的 \(r\)。\(S\) 的每个非零元素都是单位乘以某个 \(t^r\)，因此 \(E\) 是无挠 \(S\) 模。

等式 \(pj=\eta_C\) 给出 \(\ker j=0\)。在 \(C=\bigoplus_n S_n\) 的自然 \(S\) 作用下，\(j(c)\) 可由 \(c\) 的任意有限支撑幂级数提升来表示，因为两个这样的提升之差是 \(K\) 中的有限支撑列，因而属于 \(I\)。这也说明 \(j\) 是 \(S\) 线性的，且 \(\operatorname{im}j\) 恰好由具有有限支撑代表的类组成。

对每个 \(r\ge1\)，写 \(Q[t^r]=\{x\in Q:t^rx=0\}\)。则
\[
Q[t^r]=j\bigl(C[t^r]\bigr)
=j\left(\bigoplus_{n\ge1}t^{\max(\nu_n-r,0)}S_n\right).
\]
事实上，若 \(x=b+I\) 被 \(t^r\) 杀死，则 \(t^rb=T(a)\) 对某个 \(a\in L\) 成立。在 \(p(x)\) 的非零坐标上，\(v(b_n)<\nu_n\)，从而
\[
v(a_n)=r+v(b_n)-\nu_n<r.
\]
这样的指标只有有限个，所以 \(p(x)=\eta_C(c)\) 对某个 \(c\in C\) 成立。由 \(\eta_C\) 单射可知 \(t^rc=0\)。于是 \(x-j(c)\in E\) 且被 \(t^r\) 杀死，由 \(E\) 无挠得到 \(x=j(c)\)。反向包含由 \(j\) 的线性性给出。每个 \(c\in C\) 都是有限支撑列，因而被某个 \(t^r\) 杀死。所以 **\(Q\) 中所有被某个 \(t^r\) 杀死的元素恰好组成 \(j(C)\)**。

若 \((\nu_n)\) 有界，则 \(p\) 是同构，因而存在 \(S\) 线性右逆。若 \((\nu_n)\) 无界，沿用上面的 \(n_\ell\)，取 \(c^*\) 在 \(n_\ell\) 处为 \(t^{\nu_{n_\ell}-1}\bmod t^{\nu_{n_\ell}}\)，其余坐标为零。它属于 \(L_C\)，被 \(t\) 杀死，且有无限支撑。若 \(p\) 有 \(S\) 线性右逆，则该右逆会把 \(c^*\) 送入 \(Q[t]\)，从而 \(c^*\in p(Q[t])\)。然而 \(p(Q[t])\subseteq\eta_C(C)\) 中的元素均为有限支撑，矛盾。因此 **\(p\) 有 \(S\) 线性右逆的充要条件是 \((\nu_n)\) 有界**。

## 三、逐层商、再次完成与拓扑

对每个 \(m\ge1\)，有
\[
t^mQ=(I+t^mL)/I .
\]
这也表明 \(Q\) 的 \(t\) 进拓扑就是从 \(L\) 得到的商拓扑。由 \(\overline I=K\) 得 \(K\subseteq I+t^mL\)，于是 \(I+t^mL=K+t^mL\)。又因为 \(\widehat q(t^mL)=t^m\widehat C\)，所以 \(p\) 诱导同构
\[
Q/t^mQ\xrightarrow{\ \sim\ }\widehat C/t^m\widehat C
\simeq \bigoplus_{n\ge1}S/t^{\min(m,\nu_n)}S .
\]
合成后的坐标映射将 \(b+I\) 模 \(t^mQ\) 的类送到 \((b_n\bmod t^{\min(m,\nu_n)})_n\)。右侧的坐标同构来自逐坐标约化，其核由第一部分对 \(t^mL_C\) 的描述给出，满射性可用有限支撑提升验证。

特别地，\(t^mQ=p^{-1}(t^m\widehat C)\)。由于 \(\widehat C\) 分离，
\[
\bigcap_{m\ge1}t^mQ=E.
\]
逐层同构与约化相容，取逆极限得到 \(\widehat Q\simeq L_C=\widehat C\)。在这个识别下，\(\eta_Q\) 就是 \(p\)。同一坐标模型也给出 \(\eta_{\widehat C}:\widehat C\xrightarrow{\sim}\widehat{\widehat C}\)。将 \(\widehat Q\) 和 \(\widehat{\widehat C}\) 都识别为 \(L_C\) 后，\(p\) 诱导的完成映射 \(\widehat p\) 是恒等映射。

为计算 \(E\) 自身的完成，对每个 \(m\ge1\) 定义
\[
\begin{aligned}
P_m&=\left\{u\in\prod_{n\ge1}S/t^mS:
\text{对每个整数 }d\ge0,\ 
\{n:\nu_n\le d,\ u_n\ne0\}\text{ 有限}\right\},\\
F_m&=\bigoplus_{n\ge1}S/t^mS .
\end{aligned}
\]
逐坐标模 \(t^m\) 将 \(D\) 映到 \(P_m\)，因为若 \(\nu_n\le d\) 且 \(a_n\bmod t^m\ne0\)，则 \(\nu_n+v(a_n)<d+m\)。反过来，取 \(u\in P_m\) 的各坐标截断多项式代表。对于任意 \(h\ge1\)，满足 \(\nu_n+v(a_n)<h\) 的指标都满足 \(\nu_n\le h-1\) 且 \(u_n\ne0\)，故只有有限个。这给出从 \(D\) 出发的满射。其核是 \(t^mD\)，因为逐坐标除以固定的 \(t^m\) 保持 \(D\) 的增长条件。\(L\) 在约化下的像恰好是 \(F_m\)。因此
\[
E/t^mE\simeq D/(L+t^mD)\simeq P_m/F_m,
\]
过渡映射由坐标约化给出。典范映射 \(\eta_E\) 将 \(a+L\) 送到各层 \((a_n\bmod t^m)_n\) 在 \(P_m/F_m\) 中的类。若该记录为零，则 \(a\) 的每层约化都有限支撑，故 \(a\in L\)。这证明了 \(\eta_E\) 单射，也证明了 \(E\) 自身的 \(t\) 进拓扑分离。

给定任意相容记录 \((\xi_m)_m\in\varprojlim_m P_m/F_m\)，先取 \(\xi_1\) 的代表 \(u^{(1)}\in P_1\)。选好 \(u^{(m)}\) 后，\(\xi_{m+1}\) 的任意代表约化到第 \(m\) 层，与 \(u^{(m)}\) 只差一个 \(F_m\) 中的元素。将这个差提升到 \(F_{m+1}\) 并修正代表，就能选得 \(u^{(m+1)}\) 精确约化为 \(u^{(m)}\)。这些相容代表逐坐标确定一个幂级数列 \(a\)。若 \(\nu_n+v(a_n)<h\)，则 \(\nu_n\le h-1\) 且 \(u^{(h)}_n\ne0\)。因为 \(u^{(h)}\in P_h\)，这样的指标只有有限个，所以 \(a\in D\)。于是 \(a+L\) 映到原记录，证明 \(\eta_E\) 满射。因此 **\(\widehat E\simeq D/L=E\)，且在此识别下 \(\eta_E\) 是恒等映射**。

最后，每个 \(t^mQ\) 都包含 \(E\)，故 \(E\) 从 \(Q\) 继承的子空间拓扑只有 \(\varnothing\) 和 \(E\) 两个可能的开集。\(E\) 自身的 \(t\) 进拓扑总是分离。两种拓扑相同当且仅当 \(E=0\)，即当且仅当 **\((\nu_n)\) 有界**。