下面记
\[
v_t(0)=\infty,\qquad 
v_t\Big(\sum_{j\ge0}a_jt^j\Big)=\min\{j:a_j\ne0\}.
\]
对 \(x\in R/(t^{\nu_n})\)，取唯一代表元 \(\tilde x\in k[t]\)，\(\deg\tilde x<\nu_n\)，仍记
\[
v_t(x)=v_t(\tilde x)
\]
（若 \(x=0\)，约定为 \(\infty\)）。又记
\[
t^{\nu_n}(R/(t^{\nu_n}))=0
\]
当 \(\nu_n=0\) 时。

本文将反复使用：\(\nu=(\nu_n)\) 有界，当且仅当
\[
\sup_{n\ge1}\nu_n<\infty.
\]

主要结论先列出：
\[
\boxed{
\begin{aligned}
&\widehat A\to\widehat B\to\widehat C
\text{ 中，左右两端总是正合的；中间正合}\\
&\iff \operatorname{im}\widehat\iota\text{ 在 }\widehat B\text{ 中闭}
\iff E=0
\iff \sup_n\nu_n<\infty.
\end{aligned}}
\]
并且 \(p:Q\to\widehat C\) 总是满射；它有 \(S\)-线性右逆当且仅当 \(\sup_n\nu_n<\infty\)。此外 \(E\) 总是无挠的，且
\[
\widehat Q\simeq\widehat C,\qquad \widehat E\simeq E.
\]

---

# 一、三个完成的坐标模型与完成列

## 1.1 坐标模型

定义
\[
\mathcal A=\left\{(a_n)\in S^{\mathbb N}:
\forall m,\ a_n\in t^mS\text{ 对除有限个之外的 }n
\right\},
\]
等价地
\[
\mathcal A=\left\{(a_n)\in S^{\mathbb N}:v_t(a_n)\to\infty\right\}.
\]
同理定义
\[
\mathcal B=\left\{(b_n)\in S^{\mathbb N}:v_t(b_n)\to\infty\right\}.
\]
因为
\[
A/t^mA\simeq\bigoplus_{n\ge1}R/(t^m)f_n,\qquad
B/t^mB\simeq\bigoplus_{n\ge1}R/(t^m)e_n,
\]
取逆极限得到自然同构
\[
\boxed{
\widehat A\simeq\mathcal A,\qquad
\widehat B\simeq\mathcal B.
}
\]
同构由
\[
(a_n)\longmapsto (a_n\bmod t^m)_{m\ge1}
\]
的逆极限记录给出。特别地，\(\eta_A,\eta_B\) 就是把有限支撑列映到同一列。

对 \(C\)，有
\[
C/t^mC
\simeq B/(t^mB+\iota(A))
\simeq\bigoplus_{n\ge1}R/(t^{\min(m,\nu_n)}).
\]
因此
\[
\boxed{
\widehat C\simeq
\mathcal C:=
\left\{
(c_n)_{n\ge1}:\ 
c_n\in R/(t^{\nu_n}),\quad
v_t(c_n)\to\infty
\right\}.
}
\]
等价地，对每个 \(m\)，除有限个 \(n\) 外都有
\[
c_n\in t^m(R/(t^{\nu_n})).
\]
坐标与逆极限记录的对应为
\[
(c_n)_{n\ge1}
\longmapsto
\bigl(c_n\bmod t^{\min(m,\nu_n)}\bigr)_{m,n}.
\]
注意当 \(\nu_n=0\) 时 \(R/(t^{\nu_n})=0\)，该坐标自动为零。

完成映射为
\[
\eta_C(c)=c\text{（有限支撑列）}.
\]

## 1.2 诱导映射

在这些坐标下，
\[
\boxed{
\widehat\iota:\mathcal A\to\mathcal B,\qquad
\widehat\iota(a)_n=t^{\nu_n}a_n,
}
\]
以及
\[
\boxed{
\widehat q:\mathcal B\to\mathcal C,\qquad
\widehat q(b)_n=b_n\bmod t^{\nu_n}.
}
\]
后者确实是良定义的：若 \(b_n\in t^mS\)，则
\[
b_n\bmod t^{\nu_n}\in t^{\min(m,\nu_n)}(R/(t^{\nu_n})),
\]
故 \(v_t(\widehat q(b)_n)\to\infty\)。

## 1.3 核、闭包与纤维

令
\[
\boxed{
D:=\{b\in\mathcal B:t^{\nu_n}\mid b_n\text{ 对一切 }n\}.
}
\]
显然
\[
\ker\widehat q=D.
\]

再记
\[
I:=\operatorname{im}\widehat\iota
=\{t^{\nu_n}a_n:(a_n)\in\mathcal A\}.
\]

### 命题 1.1
在 \(\mathcal B=\widehat B\) 中，
\[
\boxed{
\overline{I}=D.
}
\]
更精确地，\(I\subseteq D\)，且 \(I\) 在 \(D\) 中稠密。

**证明。**

先证 \(D\) 闭。设 \(b^{(r)}\in D\)，且在 \(\widehat B\) 中 \(b^{(r)}\to b\)。任取 \(n\)。取 \(N\ge\nu_n\)。当 \(r\gg0\) 时
\[
b^{(r)}_n\equiv b_n\pmod{t^N}.
\]
但 \(t^{\nu_n}\mid b^{(r)}_n\)，故 \(b^{(r)}_n\) 的前 \(\nu_n\) 个系数为零；因 \(N\ge\nu_n\)，得到 \(t^{\nu_n}\mid b_n\)。故 \(b\in D\)。

再证 \(I\) 在 \(D\) 中稠密。取 \(b\in D\) 及 \(m\ge1\)。因为 \(b\in\mathcal B\)，除有限个 \(n\) 外有 \(b_n\in t^mS\)。对这样的 \(n\)，若 \(\nu_n<m\)，也令 \(a_n=0\)，则
\[
b_n-t^{\nu_n}a_n=b_n\in t^mS\subseteq t^mS.
\]
若 \(\nu_n\ge m\)，则 \(b_n\in t^{\nu_n}S\subseteq t^mS\)，同样可取 \(a_n=0\)。只有有限个 \(n\) 可能使 \(b_n\notin t^mS\)，对这些 \(n\) 选取 \(a_n\in S\) 使得
\[
t^{\nu_n}a_n\equiv b_n\pmod{t^m}.
\]
其余 \(a_n=0\)。于是 \(a=(a_n)\) 为有限支撑列，特别地 \(a\in\mathcal A\)，且
\[
b-\widehat\iota(a)\in t^m\widehat B.
\]
故 \(I\) 在 \(D\) 中稠密。于是 \(\overline I=D\)。\(\square\)

### 命题 1.2（\(\widehat q\) 的纤维）
映射 \(\widehat q:\widehat B\to\widehat C\) 总是满射。事实上，对
\[
c=(c_n)\in\widehat C,
\]
取 \(b^c_n\in R\) 为 \(c_n\) 的唯一次数 \(<\nu_n\) 的代表元（若 \(\nu_n=0\) 取 \(0\)）。则
\[
b^c=(b^c_n)\in\widehat B,\qquad
\widehat q(b^c)=c.
\]
因此
\[
\boxed{
\widehat q^{-1}(c)=b^c+D.
}
\]
这就是说，\(\widehat q\) 的每个纤维都是 \(D\) 的一个平移。

**证明。** 因为 \(v_t(c_n)\to\infty\)，故 \(v_t(b^c_n)\to\infty\)，所以 \(b^c\in\widehat B\)。其余由 \(\ker\widehat q=D\) 立即得到。\(\square\)

## 1.4 完成列正合性的充要条件

考虑完成列
\[
0\longrightarrow\widehat A
\xrightarrow{\ \widehat\iota\ }
\widehat B
\xrightarrow{\ \widehat q\ }
\widehat C
\longrightarrow0.
\]

- \(\widehat\iota\) 总是单射：若 \(t^{\nu_n}a_n=0\) 对一切 \(n\)，因 \(S\) 是整区，得 \(a_n=0\)。
- \(\widehat q\) 总是满射，见命题 1.2。
- 中间的正合性等价于
\[
\operatorname{im}\widehat\iota=\ker\widehat q=D.
\]

### 定理 1.3
\[
\boxed{
\operatorname{im}\widehat\iota=D
\iff \sup_{n\ge1}\nu_n<\infty.
}
\]
因此完成列
\[
0\to\widehat A\to\widehat B\to\widehat C\to0
\]
短正合，当且仅当指数列 \((\nu_n)\) 有界。

**证明。**

若 \(\nu_n\le N\) 对一切 \(n\)。取 \(b\in D\)。写
\[
b_n=t^{\nu_n}a_n,\qquad a_n\in S.
\]
则
\[
v_t(a_n)=v_t(b_n)-\nu_n\ge v_t(b_n)-N\to\infty.
\]
故 \(a=(a_n)\in\mathcal A\)，从而 \(b=\widehat\iota(a)\)。于是 \(D=I\)。

反之，若 \(\nu_n\) 无界，取子列 \(n_j\) 使得 \(\nu_{n_j}\to\infty\)。定义
\[
b_{n_j}=t^{\nu_{n_j}},\qquad
b_n=0\quad(n\notin\{n_j\}).
\]
则 \(v_t(b_{n_j})=\nu_{n_j}\to\infty\)，故 \(b\in\widehat B\)。又 \(t^{\nu_n}\mid b_n\) 对一切 \(n\)，故 \(b\in D\)。若 \(b=\widehat\iota(a)\)，则必有
\[
a_{n_j}=1\qquad\text{对一切 }j,
\]
于是 \(v_t(a_{n_j})=0\) 不趋于 \(\infty\)，矛盾。故 \(b\notin I\)。因此 \(D\ne I\)，完成列中间不正合。\(\square\)

于是：

- 当 \(\nu_n\) 有界时，\(\operatorname{im}\widehat\iota=D\) 为闭子模，完成列短正合；
- 当 \(\nu_n\) 无界时，\(\operatorname{im}\widehat\iota\) 在 \(D\) 中稠密但严格小于 \(D\)，故不闭；完成列在 \(\widehat B\) 处不正合。

这完成第一部分。

---

# 二、\(E\)、\(Q\) 的挠性、\(p\) 与右逆

## 2.1 \(E\) 的坐标模型

由
\[
E=\ker p=D/I
\]
及 \(D=\{b\in\mathcal B:t^{\nu_n}\mid b_n\ \forall n\}\)，每个 \(b\in D\) 可唯一写成
\[
b_n=t^{\nu_n}c_n,\qquad c_n\in S.
\]
定义
\[
\boxed{
W:=\left\{(c_n)\in S^{\mathbb N}:
\nu_n+v_t(c_n)\to\infty
\right\},
}
\]
以及
\[
V:=\mathcal A=\{(c_n)\in S^{\mathbb N}:v_t(c_n)\to\infty\}.
\]
注意
\[
(c_n)\in W
\iff
(t^{\nu_n}c_n)\in\widehat B.
\]
于是有自然同构
\[
\boxed{
E\simeq W/V,\qquad
t^{\nu_n}c_n+I\longmapsto c+V.
}
\]
等价地，
\[
\boxed{
E\simeq
\frac{
\{(c_n)\in S^{\mathbb N}:\nu_n+v_t(c_n)\to\infty\}
}{
\{(c_n)\in S^{\mathbb N}:v_t(c_n)\to\infty\}
}.
}
\]
这是 \(E\) 的一个明确坐标模型。\(S\) 作用按坐标逐项给出。

## 2.2 \(j:C\to Q\) 的核与像

在模型
\[
C\simeq\bigoplus_{n\ge1}R/(t^{\nu_n})
\]
下，取 \(c=(c_n)\) 为有限支撑列，并取 \(\tilde c_n\in R\) 为 \(c_n\) 的次数 \(<\nu_n\) 的代表元。则
\[
j(c)=[(\tilde c_n)]\in Q=\widehat B/I.
\]
这个定义不依赖代表元的选取，因为相差 \(t^{\nu_n}\) 的倍数的有限支撑列属于 \(I\)。

### 命题 2.1
\[
\boxed{
\ker j=0.
}
\]

**证明。** 若 \(j(c)=0\)，则有限支撑列 \((\tilde c_n)\in I\)。于是对每个 \(n\)，\(\tilde c_n\in t^{\nu_n}S\)。但 \(\deg\tilde c_n<\nu_n\)，故 \(\tilde c_n=0\)，从而 \(c_n=0\)。故 \(c=0\)。\(\square\)

接下来确定 \(Q\) 的全部 \(t\)-幂挠元。

### 定理 2.2
\[
\boxed{
Q_{\mathrm{tor}}
:=\bigcup_{r\ge1}Q[t^r]
=j(C).
}
\]
等价地，若 \(b\in\widehat B\)，则类 \([b]\in Q\) 被某个 \(t^r\) 杀死，当且仅当
\[
\boxed{
v_t(b_n)-\nu_n\to\infty.
}
\]
因此
\[
Q_{\mathrm{tor}}
\simeq
C
\simeq
\bigoplus_{n\ge1}R/(t^{\nu_n}).
\]

**证明。**

设 \(b\in\widehat B\)，且 \(t^r[b]=0\)，即
\[
t^rb\in I.
\]
存在 \(a=(a_n)\in\mathcal A\) 使得
\[
t^rb_n=t^{\nu_n}a_n\qquad\forall n.
\]
若 \(\nu_n\ge r\)，则
\[
v_t(b_n)-\nu_n=v_t(a_n)-r\to\infty;
\]
若 \(\nu_n<r\)，则
\[
a_n=t^{r-\nu_n}b_n,
\qquad
v_t(b_n)-\nu_n=v_t(a_n)-r\to\infty.
\]
故必要性成立。

反之，若
\[
v_t(b_n)-\nu_n\to\infty,
\]
则只有有限个 \(n\) 可能使
\[
v_t(b_n)<\nu_n-r
\]
对给定的 \(r\) 成立。取 \(r\ge1\) 足够大，使得
\[
v_t(b_n)\ge\nu_n-r\qquad\forall n.
\]
定义
\[
a_n=t^{r-\nu_n}b_n\in S
\]
（若指数为负，则该不等式保证 \(b_n\) 可被相应的 \(t\) 幂整除）。则
\[
v_t(a_n)=r+v_t(b_n)-\nu_n\to\infty,
\]
故 \(a\in\mathcal A\)，且
\[
t^rb_n=t^{\nu_n}a_n.
\]
于是 \(t^r[b]=0\)。

最后证明 \(j(C)=Q_{\mathrm{tor}}\)。上面已经说明 \(j(C)\subseteq Q_{\mathrm{tor}}\)，因为 \(C\) 中元素有限支撑，故存在统一的 \(t^r\) 杀死它。

反过来，若 \([b]\in Q_{\mathrm{tor}}\)，则 \(v_t(b_n)-\nu_n\to\infty\)。于是除有限个 \(n\) 外有
\[
v_t(b_n)\ge\nu_n,
\]
即 \(b_n\equiv0\pmod{t^{\nu_n}}\)。令
\[
c_n=b_n\bmod t^{\nu_n},
\]
则只有有限个 \(c_n\) 可能非零，故得到 \(c=(c_n)\in C\)。取有限支撑多项式代表元 \(\tilde c_n\)，则
\[
b-(\tilde c_n)\in I,
\]
因为对除有限个之外的 \(n\)，\((b_n-\tilde c_n)/t^{\nu_n}=b_n/t^{\nu_n}\) 的赋值
\[
v_t(b_n)-\nu_n\to\infty,
\]
而有限个例外可任意。因此 \([b]=j(c)\)。故
\[
Q_{\mathrm{tor}}=j(C)\simeq C.
\]
\(\square\)

## 2.3 \(E\) 是 \(S\)-无挠的

### 命题 2.3
\[
\boxed{
E\text{ 是 }S\text{-无挠模}.
}
\]
更精确地，
\[
\boxed{
E\cap Q_{\mathrm{tor}}=0.
}
\]

**证明。** 取 \(e=[d]\in E\)，其中 \(d\in D\)，写成
\[
d_n=t^{\nu_n}c_n.
\]
若 \(t^re=0\)，则 \(t^rd\in I\)。但
\[
t^rd=t^{\nu_n}(t^rc_n),
\]
故 \((t^rc_n)\in\mathcal A\)，即
\[
v_t(t^rc_n)=r+v_t(c_n)\to\infty.
\]
于是 \(v_t(c_n)\to\infty\)，即 \(c=(c_n)\in\mathcal A\)，从而 \(d=\widehat\iota(c)\in I\)。故 \(e=0\)。因此 \(E\) 没有非零 \(t\)-挠元；因为 \(S\) 是整区，任何非零纯量都是 \(t^r\) 乘一个单位，故 \(E\) 是 \(S\)-无挠的。\(\square\)

## 2.4 \(p\) 的满射性

由
\[
p([b])=\widehat q(b),
\]
而 \(\widehat q\) 总是满射，故
\[
\boxed{
p:Q\to\widehat C\text{ 总是满射}.
}
\]

## 2.5 \(E=0\) 与右逆的充要条件

由第一部分，
\[
\boxed{
E=0
\iff D=I
\iff \sup_n\nu_n<\infty.
}
\]

### 定理 2.4
\(p:Q\to\widehat C\) 存在 \(S\)-线性右逆，当且仅当
\[
\boxed{
\sup_{n\ge1}\nu_n<\infty.
}
\]

**证明。**

若 \(\sup\nu_n<\infty\)，则 \(E=0\)，即 \(p\) 是 \(S\)-模同构，故 \(p^{-1}\) 就是 \(S\)-线性右逆。

反之，设 \(\nu_n\) 无界。取子列 \(n_j\) 使得
\[
\nu_{n_j}\to\infty,\qquad \nu_{n_j}\ge1.
\]
在 \(\widehat C\) 中定义
\[
c_{n_j}=t^{\nu_{n_j}-1}\bmod t^{\nu_{n_j}},
\qquad
c_n=0\quad(n\notin\{n_j\}).
\]
因为
\[
v_t(c_{n_j})=\nu_{n_j}-1\to\infty,
\]
故 \(c\in\widehat C\)。并且
\[
tc=0
\]
逐坐标成立，因为 \(t\cdot t^{\nu_{n_j}-1}=t^{\nu_{n_j}}=0\) 在 \(R/(t^{\nu_{n_j}})\) 中。

假设存在 \(S\)-线性右逆 \(s:\widehat C\to Q\)。则
\[
s(tc)=t\,s(c).
\]
但 \(tc=0\)，故
\[
t\,s(c)=0.
\]
取 \(b\in\widehat B\) 代表 \(s(c)\)。因 \(p(s(c))=c\)，有
\[
b_{n_j}\equiv t^{\nu_{n_j}-1}\pmod{t^{\nu_{n_j}}},
\]
故
\[
b_{n_j}=t^{\nu_{n_j}-1}u_j
\]
其中 \(u_j\in S^\times\)。于是
\[
tb_{n_j}=t^{\nu_{n_j}}u_j.
\]
若 \(t[b]=0\)，则 \(tb\in I\)。于是存在 \(a=(a_n)\in\mathcal A\) 使得
\[
tb_n=t^{\nu_n}a_n.
\]
对 \(n=n_j\)，得到 \(a_{n_j}=u_j\)，其赋值为 \(0\)，与 \(v_t(a_n)\to\infty\) 矛盾。因此
\[
t[b]\ne0.
\]
这与 \(t\,s(c)=0\) 矛盾。故不存在 \(S\)-线性右逆。\(\square\)

---

# 三、模 \(t^m\) 的映射、完成与拓扑

## 3.1 \(Q/t^mQ\to\widehat C/t^m\widehat C\)

由
\[
t^mQ=\frac{t^m\widehat B+I}{I},
\]
得到
\[
Q/t^mQ
\simeq
\widehat B/(t^m\widehat B+I)
\simeq
B/(t^mB+\iota(A))
\simeq
C/t^mC.
\]
另一方面，
\[
\widehat C/t^m\widehat C\simeq C/t^mC.
\]
于是
\[
\boxed{
Q/t^mQ\simeq
\widehat C/t^m\widehat C\simeq
C/t^mC\simeq
\bigoplus_{n\ge1}R/(t^{\min(m,\nu_n)}).
}
\]
由 \(p\) 诱导的映射
\[
\overline p_m:Q/t^mQ\longrightarrow\widehat C/t^m\widehat C
\]
在这两个自然同构下就是恒等映射。逐坐标地，
\[
[b]\bmod t^m
\longmapsto
\bigl(b_n\bmod t^{\min(m,\nu_n)}\bigr)_{n\ge1}.
\]

## 3.2 \(\bigcap_{m\ge1}t^mQ\)

### 定理 3.1
\[
\boxed{
\bigcap_{m\ge1}t^mQ=E=\ker p.
}
\]

**证明。**

先证 \(E\subseteq t^mQ\) 对每个 \(m\) 成立。取 \(e=[d]\in E=D/I\)，其中 \(d\in D\)。固定 \(m\)。对满足 \(\nu_n<m\) 的 \(n\)，令
\[
i_n=d_n;
\]
对满足 \(\nu_n\ge m\) 的 \(n\)，令 \(i_n=0\)。因为 \(d\in\mathcal B\)，故在集合 \(\{n:\nu_n<m\}\) 上
\[
v_t(d_n/t^{\nu_n})=v_t(d_n)-\nu_n\to\infty,
\]
所以 \(i=(i_n)\in I\)。于是
\[
d-i
\]
在 \(\nu_n<m\) 的坐标上为零，在 \(\nu_n\ge m\) 的坐标上属于 \(t^mS\)。定义
\[
b_n=\begin{cases}
(d_n-i_n)/t^m,&\nu_n\ge m,\\
0,&\nu_n<m.
\end{cases}
\]
则 \(b\in\widehat B\)，且
\[
d=t^mb+i\in t^m\widehat B+I.
\]
故
\[
e=[d]\in t^mQ.
\]
于是 \(E\subseteq\bigcap_m t^mQ\)。

反过来，若 \(q\in\bigcap_m t^mQ\)，则
\[
p(q)\in\bigcap_m t^m\widehat C.
\]
但由坐标模型，
\[
\bigcap_{m\ge1}t^m\widehat C=0
\]
（对每个固定的 \(n\)，取 \(m>\nu_n\)，则 \(t^m\) 在 \(R/(t^{\nu_n})\) 上作用为零）。故 \(p(q)=0\)，即 \(q\in\ker p=E\)。因此
\[
\bigcap_m t^mQ=E.
\]
\(\square\)

因此 \(Q\) 的 \(t\)-进拓扑分离，当且仅当 \(E=0\)，即当且仅当 \(\sup\nu_n<\infty\)。

## 3.3 \(\widehat Q\) 及典范映射

由 3.1，
\[
\widehat Q
=\varprojlim_m Q/t^mQ
\simeq
\varprojlim_m C/t^mC
=\widehat C.
\]
并且
\[
\boxed{
\widehat Q\simeq Q/E\simeq\widehat B/D\simeq\widehat C,
}
\]
其中典范映射
\[
\eta_Q:Q\to\widehat Q\simeq\widehat C
\]
正是 \(p\)。换言之，在自然同构下
\[
\boxed{
\eta_Q=p.
}
\]
其核为
\[
\ker\eta_Q=\bigcap_m t^mQ=E.
\]

## 3.4 \(\widehat E\) 及典范映射

我们需要计算 \(E/t^mE\)。令
\[
W_m:=t^mW
=\{(c_n)\in W:t^m\mid c_n\text{ 对一切 }n\}.
\]
则
\[
t^mE=\frac{W_m+V}{V}.
\]
对每个 \(m\ge1\)，定义
\[
P_m:=\{c\in W:c_n\in k[t],\ \deg c_n<m\ \forall n\},
\]
以及
\[
F_m:=\{c\in P_m:c_n=0\text{ 对除有限个之外的 }n\}.
\]
于是 \(F_m=P_m\cap V\)。

任意 \(c\in W\) 可唯一分解为
\[
c=c_{<m}+c_{\ge m},
\]
其中 \(c_{<m}\in P_m\)，而 \(c_{\ge m}\in W_m\)（逐坐标截去次数 \(<m\) 的部分）。并且
\[
P_m\cap W_m=0.
\]
进一步，
\[
P_m\cap(W_m+V)=F_m.
\]
事实上，若 \(x\in P_m\cap(W_m+V)\)，写成 \(x=d+v\)，\(d\in W_m\)，\(v\in V\)。对除有限个之外的 \(n\)，\(d_n\in t^mS\)，且 \(v_n\in t^mS\)，故 \(x_n\in t^mS\)。但 \(\deg x_n<m\)，所以 \(x_n=0\)。故 \(x\) 为有限支撑，即 \(x\in F_m\)。反向包含显然。

因此
\[
\boxed{
E/t^mE
\simeq
\frac{W}{W_m+V}
\simeq
P_m/F_m.
}
\]
这些同构与 \(m\) 相容；从 \(m+1\) 到 \(m\) 的过渡映射就是多项式截断
\[
P_{m+1}/F_{m+1}\longrightarrow P_m/F_m.
\]
取逆极限。过渡映射
\[
F_{m+1}\to F_m
\]
是满射（有限支撑多项式直接看作次数 \(<m+1\) 的多项式即可），故 \(\varprojlim{}^1F_m=0\)。于是逆极限序列正合：
\[
0\to\varprojlim_mF_m\to
\varprojlim_mP_m\to
\varprojlim_m(P_m/F_m)\to0.
\]
显然
\[
\varprojlim_mP_m\simeq W,\qquad
\varprojlim_mF_m\simeq V.
\]
因此
\[
\boxed{
\widehat E
=\varprojlim_m E/t^mE
\simeq
\varprojlim_m(P_m/F_m)
\simeq
W/V
\simeq
E.
}
\]
更精确地，典范映射
\[
\boxed{
\eta_E:E\to\widehat E
}
\]
是同构。直观地，逆映射由截断
\[
[c]\longmapsto
\bigl([c_{<m}]\bigr)_{m\ge1}
\]
给出。

## 3.5 \(p\) 诱导的完成映射

因为
\[
\widehat Q\simeq\widehat C,\qquad
\widehat{\widehat C}\simeq\widehat C,
\]
故 \(p\) 诱导的完成映射
\[
\widehat p:\widehat Q\longrightarrow\widehat{\widehat C}
\]
在同构
\[
\widehat Q\simeq\widehat C,\qquad
\widehat{\widehat C}\simeq\widehat C
\]
下就是恒等映射：
\[
\boxed{
\widehat p:\widehat C\longrightarrow\widehat C
\text{ 是恒等同构}.
}
\]
特别地，\(\widehat p\) 是满射且是单射。

另一方面，因为
\[
E=\bigcap_m t^mQ,
\]
包含映射 \(E\hookrightarrow Q\) 的完成映射
\[
\widehat E\to\widehat Q
\]
在同构 \(\widehat E\simeq E\)、\(\widehat Q\simeq\widehat C\) 下是零映射：
\[
\boxed{
\widehat E\longrightarrow\widehat Q
\text{ 为零映射}.
}
\]
这正是完成函子在非有限生成模上不保持左正合的体现。

## 3.6 \(E\) 的两种拓扑比较

### 1. 从 \(Q\) 继承的子空间拓扑

由定理 3.1，
\[
E=\bigcap_{m\ge1}t^mQ.
\]
因此对每个 \(m\)，
\[
E\cap t^mQ=E.
\]
所以 \(E\) 从 \(Q\) 继承的子空间拓扑是**平凡拓扑（不可分拓扑）**：其零点邻域基只有 \(E\) 本身。

### 2. \(E\) 自身的 \(t\)-进拓扑

自身的零点邻域基为
\[
t^mE=\frac{W_m+V}{V}.
\]
断言：
\[
\boxed{
\bigcap_{m\ge1}t^mE=0.
}
\]
证明如下。设 \(e=[c]\in\bigcap_m t^mE\)，\(c\in W\)。对每个 \(m\)，存在 \(d^{(m)}\in W_m\) 及 \(v^{(m)}\in V\)，使得
\[
c=d^{(m)}+v^{(m)}.
\]
固定 \(M\)。取 \(m\ge M\)。因为 \(d^{(m)}\in W_m\)，故
\[
d^{(m)}_n\in t^mS\subseteq t^MS\qquad\forall n.
\]
又 \(v^{(m)}\in V\)，故对除有限个之外的 \(n\)，
\[
v^{(m)}_n\in t^mS\subseteq t^MS.
\]
于是对除有限个之外的 \(n\)，
\[
c_n\in t^MS.
\]
由于 \(M\) 任意，得到
\[
v_t(c_n)\to\infty,
\]
即 \(c\in V\)，从而 \(e=0\)。因此
\[
\bigcap_m t^mE=0.
\]
所以 \(E\) 自身的 \(t\)-进拓扑总是分离的。

### 3. 两种拓扑何时相同

- 若 \(E=0\)，两种拓扑当然相同。
- 若 \(E\ne0\)，自身拓扑是分离的，而继承拓扑是平凡拓扑，故两者不同；更精确地，自身的 \(t\)-进拓扑严格细于继承拓扑。

因此
\[
\boxed{
E\text{ 的自身 }t\text{-进拓扑等于从 }Q\text{ 继承的子空间拓扑}
\iff E=0
\iff \sup_{n\ge1}\nu_n<\infty.
}
\]

---

# 总结

对所有非负整数列 \((\nu_n)\)：

1. 完成列
   \[
   0\to\widehat A\to\widehat B\to\widehat C\to0
   \]
   左端、右端总是正合；中间正合当且仅当
   \[
   \boxed{\sup_n\nu_n<\infty.}
   \]
   一般地，
   \[
   \ker\widehat q
   =\overline{\operatorname{im}\widehat\iota}
   =\{b\in\widehat B:t^{\nu_n}\mid b_n\ \forall n\}.
   \]

2. 有坐标模型
   \[
   E\simeq
   \frac{\{(c_n)\in S^{\mathbb N}:\nu_n+v_t(c_n)\to\infty\}}
   {\{(c_n)\in S^{\mathbb N}:v_t(c_n)\to\infty\}}.
   \]
   并且
   \[
   \ker j=0,\qquad
   j(C)=Q_{\mathrm{tor}}
   =\{[b]:v_t(b_n)-\nu_n\to\infty\}
   \simeq C
   \simeq\bigoplus_nR/(t^{\nu_n}).
   \]
   模 \(E\) 是 \(S\)-无挠的，且
   \[
   E\cap Q_{\mathrm{tor}}=0.
   \]
   映射 \(p:Q\to\widehat C\) 总是满射；\(E=0\) 以及 \(p\) 有 \(S\)-线性右逆都等价于
   \[
   \boxed{\sup_n\nu_n<\infty.}
   \]

3. 对每个 \(m\)，
   \[
   Q/t^mQ\simeq\widehat C/t^m\widehat C
   \simeq\bigoplus_nR/(t^{\min(m,\nu_n)}),
   \]
   且 \(\overline p_m\) 是恒等映射。进一步
   \[
   \bigcap_m t^mQ=E,\qquad
   \widehat Q\simeq\widehat C,\qquad
   \widehat E\simeq E.
   \]
   典范映射 \(\eta_Q\) 在同构 \(\widehat Q\simeq\widehat C\) 下就是 \(p\)；\(\eta_E\) 是同构；完成后的 \(\widehat p\) 是恒等同构。\(E\) 自身的 \(t\)-进拓扑总是分离的，而它从 \(Q\) 继承的子空间拓扑是平凡拓扑；两者相同当且仅当
   \[
   \boxed{\sup_n\nu_n<\infty.}
   \]