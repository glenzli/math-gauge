# 对角呈示的完成与商拓扑

约定 (v=v_t)，且 (v(0)=+infty)。对一列数写 (u_n\to+\infty)，意思是对每个整数 (h)，只有有限多个 (n) 满足 (u_n<h)。以下所有有界性条件均指整个给定指数列 ((\nu_n))。

定义两个 (S) 模
\[
D=\{(x_n)\in\prod_{n\ge1}S:v(x_n)\to+\infty\},
\qquad
H=\{(a_n)\in\prod_{n\ge1}S:\nu_n+v(a_n)\to+\infty\}.
\]
显然 (D\subset H)。令 (T_n=S/(t^{\nu_n}))，其中 (T_n=0) 当 (\nu_n=0)。对 (c_n\in T_n)，用其唯一的次数小于 (\nu_n) 的多项式代表元定义 (v(c_n))，零元的赋值仍为 (+\infty)。置
\[
T=\{(c_n)\in\prod_{n\ge1}T_n:v(c_n)\to+\infty\}.
\]

## 1. 完成、正合性与纤维

有自然的 (S) 线性同构
\[
\widehat A\simeq D,\qquad \widehat B\simeq D,\qquad \widehat C\simeq T.
\]
前两个同构分别使用基 (f_n,e_n)。具体地，坐标列 (x\in D) 对应相容记录
\[
\left((x_n\bmod t^m)_n\right)_{m\ge1}
\in\varprojlim_m\bigoplus_n S/(t^m).
\]
每层记录具有有限支撑，恰好等价于 (x\in D)。反过来，对每个固定坐标取相容记录的逆极限，得到唯一的 (x_n\in S)；各层的有限支撑保证 (x\in D)。

同样，利用
\[
C/t^mC\simeq\bigoplus_n S/(t^{\min(m,\nu_n)}),
\]
(c\in T) 对应记录
\[
\left((c_n\bmod t^{\min(m,\nu_n)})_n\right)_{m\ge1}.
\]
逐坐标取逆极限给出逆映射，而每层有限支撑正好给出 (T) 的衰减条件。这也证明这些同构与题设的 (S) 作用相容。典范映射 (\eta_A,\eta_B) 是将有限支撑的多项式坐标列嵌入 (D)；(\eta_C) 是将有限支撑的 (T_n) 坐标列嵌入 (T)。三者均为单射。

在这些模型中，诱导映射为
\[
\widehat\iota:D\longrightarrow D,quad
(a_n)\longmapsto(t^{\nu_n}a_n),
\qquad
\widehat q:D\longrightarrow T,quad
(b_n)\longmapsto(b_n\bmod t^{\nu_n}).
\]
令
\[
I=\{(t^{\nu_n}a_n):a\in D\},\qquad
K=\{b\in D:b_n\in t^{\nu_n}S\text{ 对所有 }n\}
  =\{(t^{\nu_n}a_n):a\in H\}.
\]
于是 (I=\operatorname{im}\widehat\iota)，(K=\ker\widehat q)。

对 (c\in T)，记 (\ell(c)_n\) 为 (c_n) 的上述多项式代表元。其赋值与 (c_n) 相同，故 (\ell(c)\in D)，且 (\widehat q(\ell(c))=c)。因此 (\widehat q) 总是满射，并且它的每个纤维恰为
\[
\widehat q^{-1}(c)=\ell(c)+K.
\]
这里 (\ell) 只是用于描述纤维，不断言其为 (S) 线性映射。

(\widehat\iota) 总是单射。因此完成列在左端和右端总是正合，在中间的同调为 (K/I)。又有
\[
\overline I=K\quad\text{（在 }D=\widehat B\text{ 的 }t\text{ 进拓扑中）}.
\]
事实上，(K) 是逐坐标的闭条件之交，因而闭；任意 (b\in K) 的有限坐标截断属于 (I)，并在 (D) 中收敛到 (b)。这里使用
\[
t^mD=\{x\in D:x_n\in t^mS\text{ 对所有 }n\},
\]
它也表明该拓扑就是相容记录的逆极限拓扑。

最后，
\[
\boxed{\quad 0\longrightarrow\widehat A\longrightarrow\widehat B
\longrightarrow\widehat C\longrightarrow0\text{ 短正合}
\iff \sup_n\nu_n<\infty.\quad}
\]
若 (\nu_n\le N)，则 (a\in H) 蕴含 (v(a_n)\to\infty)，故 (H=D)，从而 (K=I)。若指数列无界，选互异的 (n_j) 使 (\nu_{n_j}\ge j)，令 (a_{n_j}=1)、其余坐标为零。则 (a\in H\setminus D)，故 (K\ne I)。这同时给出了 (I) 闭的充要条件。

## 2. (E)、典范嵌入与挠元

乘以对角列 (t^{\nu_n}) 给出自然同构
\[
\boxed{E=K/I\simeq H/D.}
\]
换言之，(E) 的元素是满足 (\nu_n+v(a_n)\to\infty) 的坐标列，模掉满足 (v(a_n)\to\infty) 的坐标列。此后用此同构识别二者。

### 典范映射 (j)

有 (C\simeq\bigoplus_nT_n)，且 (j) 将有限支撑的 (c\) 送到 (\ell(c)+I\in Q=D/I)。若此类为零，则每个坐标的模 (t^{\nu_n}) 余数为零，因此 (c=0)。所以
\[
\ker j=0,\qquad
\operatorname{im}j=\{\ell(c)+I:c\in\bigoplus_nT_n\}.
\]
并且 (p\circ j=\eta_C)。

### (E) 的挠性及 (Q) 的全部挠元

(E) 是无挠的 (S) 模。事实上，若 (t^r a\in D)，则 (a\in D)，因为赋值统一减去固定整数 (r) 不改变趋于无穷的性质。所以 (H/D) 没有非零的 (t) 幂挠元。(S=k[[t]]) 的任意非零元都是单位乘以一个 (t) 幂，故这就是 (S) 模无挠性。

对每个 (r\ge1)，有精确公式
\[
\boxed{Q[t^r]=j(C[t^r])
=j\left(\bigoplus_n
\frac{t^{\max(\nu_n-r,0)}S}{t^{\nu_n}S}\right).}
\]
证明如下。设 (x=b+I\in Q[t^r])，则有 (a\in D) 使
\[
t^r b_n=t^{\nu_n}a_n\quad\text{对所有 }n.
\]
若 (c_n=b_n\bmod t^{\nu_n}\ne0)，则
\[
v(a_n)=r+v(b_n)-\nu_n<r.
\]
因 (a\in D)，这样的坐标只有有限多个。因此 (p(x)=c\in C[t^r])。于是 (x-j(c)\in E) 且被 (t^r) 杀死，由 (E) 无挠知 (x=j(c))。反向包含由 (j) 的线性性立即得到。

每个有限支撑的 (c\in C) 都被某个 (t) 幂杀死，故
\[
\boxed{\operatorname{Tor}_S(Q)=\bigcup_{r\ge1}Q[t^r]=j(C).}
\]
特别地，(E\cap j(C)=0)；(E) 仅在它为零时才是挠模。

### 满射、消失与分裂条件

由第一部分，(p) 总是满射，且
\[
\boxed{E=0\iff\sup_n\nu_n<\infty.}
\]
此外，
\[
\boxed{p\text{ 存在 }S\text{ 线性右逆}
\iff\sup_n\nu_n<\infty.}
\]
有界时 (p) 本身是同构。无界时选互异的 (n_j) 使 (\nu_{n_j}\ge j)，定义
\[
c_{n_j}=t^{\nu_{n_j}-1}\bmod t^{\nu_{n_j}},\qquad
c_n=0\quad(n\notin\{n_j\}).
\]
则 (c\in T[t])，但 (c) 有无限支撑，所以 (c\notin\eta_C(C))。若有 (S) 线性右逆 (s)，则 (s(c)\in Q[t]=j(C[t]))，从而 (c=p(s(c))\in\eta_C(C))，矛盾。

## 3. 商模、完成与两种拓扑

### 有限层商与 (Q) 的完成

先注意
\[
t^mT=\{c\in T:c_n\in t^mT_n\text{ 对所有 }n\}.
\]
非平凡的包含可用多项式代表元证明：若每个 (c_n\) 属于 (t^mT_n)，其代表元可除以 (t^m)，所得坐标列的赋值至多统一下降 (m)，仍满足衰减条件。因此
\[
T/t^mT\simeq\bigoplus_nS/(t^{\min(m,\nu_n)}).
\]
这些同构与约化映射相容；结合第一部分的记录模型，可知 (T) 的自身 (t) 进拓扑分离且完备。

另一方面，
\[
Q/t^mQ\simeq D/(I+t^mD).
\]
在 (D/t^mD=\bigoplus_n S/(t^m)) 中，(I) 的像就是逐坐标理想 (t^{\nu_n}(S/(t^m))) 的直和。因此
\[
\boxed{\quad
Q/t^mQ\xrightarrow[\ p_m\ ]{\ \sim\ }T/t^mT
\simeq\bigoplus_nS/(t^{\min(m,\nu_n)})\quad}
\]
对每个 (m\ge1) 都成立；(p_m) 在共同坐标模型中就是恒等映射，具体为逐坐标取模 (t^{\min(m,\nu_n)})。

特别地，(E\subset t^mQ) 对所有 (m) 成立。反之，若 (x\in\bigcap_m t^mQ)，则 (p(x)\in\bigcap_m t^mT=0)。所以
\[
\boxed{\bigcap_{m\ge1}t^mQ=E.}
\]
由相容的 (p_m) 取逆极限，得到自然同构
\[
\boxed{\widehat Q\simeq T=\widehat C.}
\]
在此识别下，典范映射 (\eta_Q:Q\to\widehat Q) 正是 (p)；特别地，它总是满射，核为 (E)。又因 (\widehat T\simeq T)，(p) 诱导的完成映射
\[
\widehat p:\widehat Q\longrightarrow\widehat{\widehat C}
\]
在两端与 (T) 的自然识别下是恒等同构。

### (E) 自身的完成

为完整计算 (\widehat E)，定义
\[
L_m=\left\{(u_n)\in\prod_n S/(t^m):
\text{对每个整数 }h,\ 
\{n:\nu_n<h,\ u_n\ne0\}\text{ 有限}\right\},
\qquad F_m=\bigoplus_n S/(t^m).
\]
逐坐标取模给出
\[
H/t^mH\simeq L_m,\qquad D/t^mD\simeq F_m,
\qquad E/t^mE\simeq L_m/F_m.
\]
证明第一式时，若 (a\in H)，在 (\nu_n<h) 且 (a_n\bmod t^m\ne0) 的坐标上有
(\nu_n+v(a_n)<h+m)，故这些坐标有限。反过来，给 (L_m) 中的坐标取次数小于 (m) 的代表元，便得到 (H) 中的提升。核恰为 (t^mH)，因为统一除以 (t^m) 保持定义 (H) 的衰减条件。另外 (D\cap t^mH=t^mD)，这也证明了第三式。

逐坐标的相容记录给出
\[
\varprojlim_m L_m=H,\qquad \varprojlim_m F_m=D.
\]
这里第一式的逆向衰减条件可这样检查：对固定 (h\ge1)，若 (\nu_n+v(a_n)<h)，则 (\nu_n<h) 且 (a_n\bmod t^h\ne0)，只有有限多个这样的 (n)。

由于约化 (F_{m+1}\to F_m) 满射，取逆极限保留短正合列
\[
0\longrightarrow F_m\longrightarrow L_m\longrightarrow L_m/F_m\longrightarrow0
\]
的右端满射性。具体地，对于相容的商类，可逐层选提升；相邻提升之差属于 (F_m)，再从 (F_{m+1}) 提升该差来修正下一层，便得到真正相容的 (L_m) 记录。因此
\[
\boxed{\widehat E
=\varprojlim_m(L_m/F_m)\simeq H/D=E.}
\]
这一同构的逆向正是典范映射 (\eta_E)：它将 (a+D) 送到
\[
\left((a_n\bmod t^m)_n+F_m\right)_{m\ge1}.
\]
所以 (E) 在自身 (t) 进拓扑下总是分离且完备。也可直接检查分离性：若 (a+D\in t^mE)，则 (a\bmod t^m) 具有有限支撑；若这对所有 (m) 成立，则 (a\in D)。

作为相关的自然性结论，包含映射 (E\hookrightarrow Q) 诱导的完成映射
(\widehat E\to\widehat Q) 为零，因为它在每个有限层商上已经为零。

### 两种拓扑的比较

(E) 从 (Q) 继承的零点邻域基为
\[
E\cap t^mQ=E\qquad(m\ge1).
\]
故此子空间拓扑总是不分辨点的平凡拓扑，即仅有开集 (\varnothing,E)。与之相对，(E) 自身的 (t) 进拓扑总是分离且完备。因此
\[
\boxed{\quad
E\text{ 的自身 }t\text{ 进拓扑与从 }Q\text{ 继承的拓扑相同}
\iff E=0\iff\sup_n\nu_n<\infty.\quad}
\]
综上，指数列有界恰好同时刻画完成列短正合、(\operatorname{im}\widehat\iota) 闭、(E=0)、(p) 有 (S) 线性右逆、(Q) 分离，以及 (E) 的上述两种拓扑相同；而 (p) 的满射性、各有限层商的同构及 (E) 自身的分离完备性对所有指数列均成立。
