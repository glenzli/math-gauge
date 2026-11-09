以下始终记
\[
\rho_{n,m}=\rho_{m-1}\cdots \rho_n:P_m\to P_n\quad(n\le m),
\]
并记 \(Q_n=\operatorname{Hom}(P_n,\mathbb Z)\)，其过渡映射为
\[
q_{n,m}=\rho_{n,m}^*:Q_n\to Q_m,\qquad q\mapsto q\circ \rho_{n,m}.
\]
所有余极限均取 \(\mathbb N=\{0,1,2,\dots\}\) 上的滤过余极限。

---

# S1　实际记录与张量

## 1. \(F_P\) 良定义

令
\[
(n,u)\sim(m,v)\quad\Longleftrightarrow\quad
\exists r\ge n,m:\quad u\rho_{n,r}=v\rho_{m,r},
\]
其中 \(u\in\operatorname{Hom}(P_n,A)\)，\(v\in\operatorname{Hom}(P_m,A)\)。

这是构造滤过余极限的标准等价关系：

- 自反、对称显然。
- 若 \((n,u)\sim(m,v)\)，\((m,v)\sim(k,w)\)，分别有见证 \(r,s\)。取 \(t\ge r,s\)，则
  \[
  u\rho_{n,t}=v\rho_{m,t}=w\rho_{k,t},
  \]
  故传递。
- 加法：取 \(r\ge n,m\)，定义
  \[
  [n,u]+[m,v]=[r,u\rho_{n,r}+v\rho_{m,r}].
  \]
  若换代表 \((n,u)\sim(n',u')\)，\((m,v)\sim(m',v')\)，取足够大的 \(t\) 同时见证两者及上述两个水平，则两个和在 \(P_t\) 上的像相同，故加法不依赖代表和所选水平。
- 零元为 \([n,0]\)，负元为 \([n,-u]\)。群公理在公共层上逐点验证。

于是 \(F_P(A)\) 是阿贝尔群。对群同态 \(h:A\to B\)，定义
\[
F_P(h)([n,u])=[n,h\circ u].
\]
若 \(u\rho_{n,r}=v\rho_{m,r}\)，则 \(hu\rho_{n,r}=hv\rho_{m,r}\)，故良定义；加法逐层保持。恒等与复合显然。因此
\[
F_P:\mathrm{Ab}_U\to\mathrm{Ab}_U
\]
是函子。

## 2. 自然同构 \(F_P(A)\cong M_P\otimes A\)

因为 \(P_n\) 是有限秩自由群，求值映射
\[
\beta_{n,A}:Q_n\otimes A\longrightarrow \operatorname{Hom}(P_n,A),
\qquad
\beta_{n,A}(q\otimes a)(p)=q(p)a
\]
是同构。事实上取 \(P_n\) 的一组基 \(e_1,\dots,e_{r_n}\) 及对偶基 \(e^1,\dots,e^{r_n}\in Q_n\)，逆映射为
\[
u\longmapsto \sum_{i=1}^{r_n} e^i\otimes u(e_i).
\]
它与塔的过渡映射相容：
\[
\begin{array}{ccc}
Q_n\otimes A & \xrightarrow{\ \beta_{n,A}\ } & \operatorname{Hom}(P_n,A)\\
\downarrow q_{n,m}\otimes\mathrm{id} & & \downarrow u\mapsto u\rho_{n,m}\\
Q_m\otimes A & \xrightarrow{\ \beta_{m,A}\ } & \operatorname{Hom}(P_m,A).
\end{array}
\]
故取余极限得
\[
F_P(A)=\varinjlim_n \operatorname{Hom}(P_n,A)
\cong \varinjlim_n (Q_n\otimes A)
\cong \Bigl(\varinjlim_n Q_n\Bigr)\otimes A
=M_P\otimes A.
\]
最后一式用了滤过余极限与张量积交换。这个同构自然于 \(A\)。在记录上，它把
\[
[n,q]\otimes a
\]
送到记录
\[
[n,\ p\mapsto q(p)a].
\]

## 3. \(M_P\) 可数、无挠

每个 \(Q_n\cong\mathbb Z^{r_n}\) 可数，而 \(M_P\) 是可数个可数集的商，故 \(M_P\) 可数。

证明无挠时不假设 \(Q_n\to M_P\) 单射。设 \(0\ne k\in\mathbb Z\)，\([q]\in M_P\)，其中 \(q\in Q_n\)，且
\[
k[q]=[kq]=0.
\]
按余极限中的相等关系，存在 \(r\ge n\) 使
\[
(kq)\rho_{n,r}=0\quad\text{于 }Q_r.
\]
即 \(k(q\rho_{n,r})=0\)。由于 \(Q_r\cong\mathbb Z^{r}\) 无挠，得 \(q\rho_{n,r}=0\)，故 \([q]=0\)。因此 \(M_P\) 无挠。注意这里只用了 \(Q_r\) 无挠；即使某个 \(Q_n\to M_P\) 有非零核，也不影响结论。

---

# S2　有限图表和变换

## 1. \(F_P\) 保持有限极限

由 S1，\(F_P\cong M_P\otimes(-)\)。每个 \(Q_n\) 是自由阿贝尔群，故平坦；滤过余极限保持正合列，因此 \(M_P=\varinjlim Q_n\) 平坦。等价地，已经证明 \(M_P\) 无挠，而阿贝尔群无挠当且仅当平坦。

于是 \(M_P\otimes(-)\) 正合，且张量积与有限直和交换：
\[
M_P\otimes(A\oplus B)\cong (M_P\otimes A)\oplus(M_P\otimes B).
\]
正合性给出核的保持，有限直和给出有限乘积的保持；有限极限由有限乘积与等化子生成。因此 \(F_P\) 保持一切有限极限。

## 2. 全部自然变换

设 \(P,P'\) 为两塔，记
\[
M=M_P,\qquad M'=M_{P'}.
\]
由 S1，有自然同构
\[
F_P(A)\cong M\otimes A,\qquad F_{P'}(A)\cong M'\otimes A.
\]

**命题：**
\[
\operatorname{Nat}(F_P,F_{P'})\cong \operatorname{Hom}_{\mathbb Z}(M,M')
\]
为阿贝尔群同构。与 \(f:M\to M'\) 对应的自然变换 \(\eta^f\) 的分量为
\[
\eta^f_A:M\otimes A\to M'\otimes A,\qquad
\eta^f_A(m\otimes a)=f(m)\otimes a.
\]
反之，若 \(\eta:F_P\to F_{P'}\) 是自然变换，则在 \(A=\mathbb Z\) 上，
\[
f=\eta_{\mathbb Z}:M\otimes\mathbb Z\to M'\otimes\mathbb Z
\]
给出 \(f\in\operatorname{Hom}(M,M')\)。

事实上，对任意 \(m\in M\)，\(a\in A\)，令 \(i_a:\mathbb Z\to A\) 为 \(i_a(1)=a\)。由自然性，
\[
\begin{aligned}
\eta_A(m\otimes a)
&=\eta_A\bigl((\mathrm{id}_M\otimes i_a)(m\otimes 1)\bigr)\\
&=(\mathrm{id}_{M'}\otimes i_a)\bigl(\eta_{\mathbb Z}(m\otimes 1)\bigr)
=f(m)\otimes a.
\end{aligned}
\]
因此 \(\eta=\eta^f\)。

恒等变换对应 \(\mathrm{id}_M\)。复合为
\[
\eta^g\circ\eta^f=\eta^{g\circ f},
\]
因为 \((g\otimes\mathrm{id}_A)\circ(f\otimes\mathrm{id}_A)=(g\circ f)\otimes\mathrm{id}_A\)。

---

# S3　完整表示分类

## 1. 表示性的充要判据

对每个 \(n\)，记
\[
E_n=\operatorname{Im}(Q_n\to M_P)\subseteq M_P.
\]
由于 \(Q_n\to Q_{n+1}\) 的像在余极限中给出同一元素，故
\[
E_0\subseteq E_1\subseteq E_2\subseteq\cdots,\qquad
M_P=\bigcup_{n\ge0}E_n.
\]

**定理：**
\[
F_P\text{ 可由普通 }P\in\mathrm{Ab}_U\text{ 表示}
\iff M_P\text{ 有限生成}.
\]
等价地，
\[
\boxed{\ \exists n\ge0\quad E_n=M_P\ }.
\]
把最后一句展开，就得到完全由塔的过渡映射给出的、非循环的判据：
\[
\boxed{
\begin{aligned}
&\exists n\ \forall m\ge n\ \forall \varphi\in Q_m\ \exists \psi\in Q_n\ \exists r\ge m:\\
&\qquad\qquad \varphi\circ\rho_{m,r}=\psi\circ\rho_{n,r}.
\end{aligned}}
\tag{\(\star\)}
\]
也就是说：存在某一层 \(n\)，使以后每一层上的任何一个泛函在某个更晚层都能由第 \(n\) 层的某个泛函表示。

## 2. 证明

### 2.1 一个乘积非满射引理

**引理：** 若 \(M_P\) 不有限生成，则典范映射
\[
c:M_P\otimes\mathbb Z^{\mathbb N}\longrightarrow (M_P)^{\mathbb N}
\tag{1}
\]
不满射。

证明：因为 \(E_n\) 是有限生成群 \(Q_n\) 的像，若 \(E_n=M_P\)，则 \(M_P\) 有限生成。故 \(M_P\) 不有限生成时，每个 \(E_n\ne M_P\)。取
\[
x_n\in M_P\setminus E_n\qquad(n\ge0),
\]
并令 \(x=(x_n)_{n\ge0}\in M_P^{\mathbb N}\)。

若 \(x=c(t)\)，则
\[
t=\sum_{k=1}^s m_k\otimes v^{(k)},\qquad
m_k\in M_P,\quad v^{(k)}\in\mathbb Z^{\mathbb N}.
\]
因为 \(M_P=\bigcup E_n\)，可取 \(N\) 足够大，使
\[
m_1,\dots,m_s\in E_N.
\]
于是
\[
c(t)_N=\sum_{k=1}^s m_k v^{(k)}_N\in E_N,
\]
但 \(x_N\notin E_N\)。矛盾。因此 \(c\) 不满射。引理得证。

### 2.2 必要性

若 \(F_P\cong\operatorname{Hom}(P,-)\)，则它保持所有极限，特别保持可数乘积：
\[
F_P(\mathbb Z^{\mathbb N})\cong F_P(\mathbb Z)^{\mathbb N}.
\]
由 S1，这正是映射 \((1)\) 为同构。由引理，\(M_P\) 必须有限生成。

### 2.3 充分性

若 \(M_P\) 有限生成，则由 S1 它无挠，故由有限生成无挠阿贝尔群的结构定理，
\[
M_P\cong\mathbb Z^d
\]
对某个 \(d\ge0\) 成立。令
\[
P_{\mathrm{rep}}=M_P^*=\operatorname{Hom}(M_P,\mathbb Z)\cong\mathbb Z^d.
\]
对任意 \(A\)，求值映射
\[
M_P\otimes A\longrightarrow \operatorname{Hom}(M_P^*,A),
\qquad
m\otimes a\longmapsto\bigl(\varphi\mapsto \varphi(m)a\bigr)
\]
是自然同构，因为 \(M_P\) 是有限秩自由群。于是由 S1，
\[
F_P(A)\cong M_P\otimes A
\cong\operatorname{Hom}(M_P^*,A)
=\operatorname{Hom}(P_{\mathrm{rep}},A).
\]
因此 \(F_P\) 可表示。

最后，
\[
E_n=M_P
\iff
\text{每个 }m\ge n\text{ 的 }E_m\text{ 已经包含在 }E_n\text{ 中},
\]
这正是 \((\star)\)。

## 3. 全部表示对象

在可表示情形，令
\[
P_\infty=\varprojlim_n P_n
=\left\{(p_n)\in\prod_n P_n:\rho_n(p_{n+1})=p_n\right\}.
\]
自然有
\[
P_\infty\cong \varprojlim_n \operatorname{Hom}(Q_n,\mathbb Z)
\cong \operatorname{Hom}\Bigl(\varinjlim_n Q_n,\mathbb Z\Bigr)
=M_P^*.
\]
当 \(M_P\) 有限生成时，\(P_\infty\cong M_P^*\cong\mathbb Z^d\) 是有限秩自由群，并且
\[
F_P\cong\operatorname{Hom}(P_\infty,-).
\]
若 \(P\in\mathrm{Ab}_U\) 也是表示对象，即
\[
\operatorname{Hom}(P,-)\cong F_P\cong\operatorname{Hom}(P_\infty,-),
\]
则由 Yoneda 引理 \(P\cong P_\infty\)。反过来，任何同构于 \(P_\infty\) 的群显然也表示 \(F_P\)。

因此全部表示对象在同构意义下恰为
\[
\boxed{\ P_\infty\cong M_P^*\cong\mathbb Z^d\ }.
\]
特别地，它们全都同构于某个有限秩自由阿贝尔群。

## 4. 保持可数小图表极限的塔

这里“对象及箭头均可数的小图表”按指标范畴 \(\mathcal I\) 满足
\[
|\operatorname{Ob}\mathcal I|\le\aleph_0,\qquad
|\operatorname{Mor}\mathcal I|\le\aleph_0
\]
理解。

**命题：** 以下三条等价：

1. \(F_P\) 保持所有对象、箭头均可数的小图表的极限；
2. \(M_P\) 有限生成；
3. \(F_P\) 可表示。

证明：

- 若 \(F_P\) 保持所有这种极限，则特别取离散指标范畴 \(\mathbb N\) 及常函子 \(i\mapsto\mathbb Z\)。其极限为 \(\prod_{i\in\mathbb N}\mathbb Z=\mathbb Z^{\mathbb N}\)，故映射 \((1)\) 为同构。由引理，\(M_P\) 有限生成。
- 反之，若 \(M_P\) 有限生成，则由上段 \(F_P\cong\operatorname{Hom}(P_\infty,-)\)。可表示函子保持一切小极限，当然保持上述极限。

于是两个判据完全重合：
\[
\boxed{
F_P\text{ 可表示}
\iff
F_P\text{ 保持所有可数小图表极限}
\iff
M_P\text{ 有限生成}.
}
\]
注意 S2 只断言 \(F_P\) 保持有限极限；可数乘积是可数小图表极限，但一般不是有限极限，所以二者并无冲突。

## 5. 与 S2 的自然变换分类一致

若 \(P,P'\) 都是可表示的塔，则
\[
M_P\cong P_\infty^*,\qquad M_{P'}\cong (P'_\infty)^*.
\]
由 S2，
\[
\operatorname{Nat}(F_P,F_{P'})\cong\operatorname{Hom}(M_P,M_{P'}).
\]
有限秩自由群的对偶给出自然同构
\[
\operatorname{Hom}(M_P,M_{P'})
\cong\operatorname{Hom}\bigl((P'_\infty)^*,P_\infty^*\bigr)
\cong\operatorname{Hom}(P'_\infty,P_\infty).
\]
而由 Yoneda，
\[
\operatorname{Nat}\bigl(\operatorname{Hom}(P_\infty,-),
\operatorname{Hom}(P'_\infty,-)\bigr)
\cong\operatorname{Hom}(P'_\infty,P_\infty).
\]
在 S2 中 \(f:M_P\to M_{P'}\) 对应 \(f^*:(P'_\infty)^*\to P_\infty^*\)；在 Yoneda 中对应 \(u\mapsto u\circ f^*\)。恒等与复合也一致。

---

# S4　秩一塔

设所有 \(P_n=\mathbb Z\)，且
\[
\rho_n=\cdot a_n,\qquad a_n\in\mathbb Z.
\]
则
\[
Q_n=\mathbb Z,\qquad q_{n,n+1}:Q_n\to Q_{n+1}
\]
也是乘以 \(a_n\)。因此
\[
M_P=\varinjlim\bigl(
\mathbb Z\xrightarrow{a_0}\mathbb Z\xrightarrow{a_1}\mathbb Z
\xrightarrow{a_2}\cdots\bigr).
\]

## 1. 秩恒为 \(1\) 不保证可表示

取 \(a_n=2\) 对所有 \(n\)。则
\[
M_P=\varinjlim(\mathbb Z\xrightarrow{2}\mathbb Z\xrightarrow{2}\cdots)
\cong\mathbb Z[1/2].
\]
\(\mathbb Z[1/2]\) 不是有限生成阿贝尔群，故由 S3，\(F_P\) 不可表示。

因此“每个 \(P_n\) 的秩都等于 \(1\)”不足以保证 \(F_P\) 可表示。

## 2. 全部整数序列的完整判据

**定理：** \(F_P\) 可表示当且仅当下列两条件至少一个成立：

\[
\text{(I) }a_n=0\text{ 对无穷多个 }n\text{ 成立};
\]
或
\[
\text{(II) }a_n\in\{-1,1\}\text{ 对所有充分大的 }n\text{ 成立}.
\]

具体地：

- 若 (I) 成立，则 \(M_P=0\)，故
  \[
  F_P(A)=0=\operatorname{Hom}(0,A),
  \]
  表示对象为 \(0\)。
- 若 (II) 成立，则 \(M_P\cong\mathbb Z\)，故
  \[
  F_P(A)\cong A=\operatorname{Hom}(\mathbb Z,A),
  \]
  表示对象为 \(\mathbb Z\)。

没有其它可表示情形。

### 证明

**情形 (I)：零点无限。**  
任取代表 \([q]\)，\(q\in Q_n=\mathbb Z\)。取 \(m\ge n\) 使 \(a_m=0\)。则从 \(Q_n\) 到 \(Q_{m+1}\) 的复合映射含因子 \(a_m=0\)，故 \(q\) 在 \(Q_{m+1}\) 中的像为 \(0\)。于是 \([q]=0\)。所以 \(M_P=0\)。

**情形：零点只有有限多个。**  
令 \(n_0\) 大于最后一个零点（若没有零点，取 \(n_0=0\)）。则对所有 \(n\ge n_0\)，\(a_n\ne0\)，过渡映射均为单射，故 \(M_P\) 是无挠秩 \(1\) 群。

- 若 (II) 成立，取 \(N\ge n_0\)，使得 \(a_n=\pm1\) 对所有 \(n\ge N\) 成立。则从 \(Q_N\) 以后所有过渡映射都是同构，故
  \[
  Q_N\to M_P
  \]
  是同构，\(M_P\cong\mathbb Z\)。

- 若 (II) 不成立，则在 \(n\ge n_0\) 中有无穷多个 \(n\) 满足 \(|a_n|\ge2\)。用反证法，设 \(M_P\) 有限生成。由于 \(M_P\) 无挠秩 \(1\)，必有 \(M_P\cong\mathbb Z\)。由 S3，存在 \(n\ge n_0\) 使 \(Q_n\to M_P\) 满射。记 \(e_k\in Q_k\) 为生成元，并令
  \[
  A_{n,m}=a_n a_{n+1}\cdots a_{m-1}\qquad(m>n).
  \]
  在余极限中
  \[
  [e_n]=A_{n,m}[e_m].
  \]
  因为 \(Q_n\to M_P\) 满射且 \(Q_n=\mathbb Z\)，\([e_n]\) 是 \(M_P\cong\mathbb Z\) 的生成元。又因 \(E_n=M_P\subseteq E_m\)，也有 \(E_m=M_P\)，故 \([e_m]\) 也是生成元。于是 \(A_{n,m}[e_m]\) 是生成元，迫使 \(A_{n,m}=\pm1\)。这对所有 \(m>n\) 都必须成立，于是
  \[
  a_m=\pm1\qquad(m\ge n),
  \]
  与 (II) 不成立矛盾。因此 \(M_P\) 不有限生成，由 S3 \(F_P\) 不可表示。

综上，判据成立。

---

# S5　稳定像中的延拓

设存在 \(n_0\)，使得对每个 \(n\ge n_0\)，\(\operatorname{Im}\rho_{n,m}\) 随 \(m\) 最终稳定为 \(I_n\)，并且
\[
\rho_n|_{I_{n+1}}:I_{n+1}\longrightarrow I_n
\]
是同构。

## 1. \(I_n\) 未必是 \(P_n\) 的直和项

**结论：否。**

例如取 \(n_0=0\)，令
\[
P_n=\mathbb Z\qquad(n\ge0),
\]
并令
\[
\rho_0=\cdot 2:P_1\to P_0,\qquad
\rho_n=\mathrm{id}_{\mathbb Z}:P_{n+1}\to P_n\quad(n\ge1).
\]
则：

- 对 \(n=0\)，
  \[
  \operatorname{Im}\rho_{0,m}=2\mathbb Z\qquad(m\ge1),
  \]
  故 \(I_0=2\mathbb Z\)。
- 对 \(n\ge1\)，
  \[
  \operatorname{Im}\rho_{n,m}=\mathbb Z,
  \]
  故 \(I_n=\mathbb Z\)。

并且
\[
\rho_0|_{I_1}:I_1=\mathbb Z\xrightarrow{\cdot2}2\mathbb Z=I_0
\]
是同构，而对 \(n\ge1\)，
\[
\rho_n|_{I_{n+1}}:\mathbb Z\xrightarrow{\mathrm{id}}\mathbb Z
\]
也是同构。因此条件全部满足。

但
\[
I_0=2\mathbb Z\subsetneq \mathbb Z=P_0
\]
不是 \(P_0\) 的直和项（若它是，则 \(\mathbb Z/(2\mathbb Z)\) 应无挠，实际为 \(\mathbb Z/2\mathbb Z\)）。所以并非每个 \(I_n\) 都必须是 \(P_n\) 的直和项。

若给定的 \(n_0>0\)，只需把上述例子整体平移指标：从 \(P_{n_0}=\mathbb Z\) 开始，令 \(\rho_{n_0}=\cdot2\)，以后取恒等即可。

## 2. 构造某个 \(P_m\to I_m\) 的回缩

取 \(m_0\ge n_0\) 足够大，使得
\[
\operatorname{Im}\rho_{n_0,m}=I_{n_0}\qquad(m\ge m_0).
\]
再取 \(m\ge m_0\)。因为每个 \(\rho_n|_{I_{n+1}}\) 都是同构，复合映射
\[
\rho_{n_0,m}|_{I_m}:I_m\longrightarrow I_{n_0}
\]
也是同构。令
\[
\sigma_m=(\rho_{n_0,m}|_{I_m})^{-1}:I_{n_0}\longrightarrow I_m.
\]
由于 \(\operatorname{Im}\rho_{n_0,m}=I_{n_0}\)，可以定义
\[
r_m=\sigma_m\circ\rho_{n_0,m}:P_m\longrightarrow I_m.
\]
对 \(x\in I_m\)，有
\[
r_m(x)=\sigma_m(\rho_{n_0,m}(x))=x.
\]
因此 \(r_m\) 是回缩，即
\[
r_m|_{I_m}=\mathrm{id}_{I_m}.
\]
于是对每个 \(m\ge m_0\)，\(I_m\) 实际上是 \(P_m\) 的直和项：
\[
P_m=\ker r_m\oplus I_m.
\]
特别地，存在某个 \(m\ge n_0\)（例如 \(m=m_0\)）具有所需回缩。

## 3. 用实际记录证明 \(F_P\cong\operatorname{Hom}(I_{n_0},-)\)

由于尾系统 \(\{n\ge n_0\}\) 在 \(\mathbb N\) 中共尾，
\[
F_P(A)=\varinjlim_{n\ge n_0}\operatorname{Hom}(P_n,A).
\]
对每个 \(n\ge n_0\)，仍记
\[
\sigma_n=(\rho_{n_0,n}|_{I_n})^{-1}:I_{n_0}\to I_n.
\]
于是当 \(n\le m\) 时，
\[
\rho_{n,m}\circ\sigma_m=\sigma_n.
\tag{2}
\]
这是因为 \(\rho_{n_0,m}=\rho_{n_0,n}\circ\rho_{n,m}\)，再在稳定像上取逆。

定义
\[
\Phi_A:F_P(A)\longrightarrow \operatorname{Hom}(I_{n_0},A),
\]
在记录上为
\[
\Phi_A([n,u])=u\circ\sigma_n:I_{n_0}\to A.
\]
若 \([n,u]=[m,u\rho_{n,m}]\)，则由 (2)
\[
(u\circ\rho_{n,m})\circ\sigma_m
=u\circ(\rho_{n,m}\circ\sigma_m)
=u\circ\sigma_n,
\]
故 \(\Phi_A\) 与代表选取无关。它显然自然于 \(A\)。

**满射性：**  
任取 \(f\in\operatorname{Hom}(I_{n_0},A)\)。取 \(m\ge m_0\)。因为 \(I_m\) 是 \(P_m\) 的直和项且有回缩 \(r_m:P_m\to I_m\)，同态
\[
f\circ\sigma_m^{-1}:I_m\to A
\]
可以延拓为
\[
u=(f\circ\sigma_m^{-1})\circ r_m:P_m\to A.
\]
于是
\[
\Phi_A([m,u])=u\circ\sigma_m
=f\circ\sigma_m^{-1}\circ r_m\circ\sigma_m
=f,
\]
因为 \(r_m|_{I_m}=\mathrm{id}\) 且 \(\sigma_m(I_{n_0})=I_m\)。故 \(\Phi_A\) 满射。

**单射性：**  
设 \(\Phi_A([n,u])=0\)。则
\[
u\circ\sigma_n=0.
\]
由于 \(\sigma_n(I_{n_0})=I_n\)，这等价于
\[
u|_{I_n}=0.
\]
由稳定像的假设，存在 \(m\ge n\) 使
\[
\operatorname{Im}\rho_{n,m}=I_n.
\]
于是对任意 \(p\in P_m\)，\(\rho_{n,m}(p)\in I_n\)，从而
\[
(u\circ\rho_{n,m})(p)=0.
\]
故
\[
u\rho_{n,m}=0,
\]
按余极限关系 \([n,u]=0\)。因此 \(\Phi_A\) 单射。

所以每个 \(\Phi_A\) 都是同构，并且自然于 \(A\)。最终得到
\[
\boxed{
F_P\cong\operatorname{Hom}(I_{n_0},-)
}
\]
为自然同构。特别地，这里无需 \(I_{n_0}\) 是 \(P_{n_0}\) 的直和项；它本身作为有限秩自由群仍给出普通表示对象。

---

# S6　具体变换与无限积

取 \(P_n=\mathbb Z\) 且 \(a_n=2\) 对所有 \(n\)。则
\[
M_P=\varinjlim(\mathbb Z\xrightarrow{2}\mathbb Z\xrightarrow{2}\cdots)
\cong\mathbb Z[1/2].
\]
这里把第 \(n\) 层的 \(1\) 送到 \(2^{-n}\in\mathbb Z[1/2]\)。

## 1. 全部自同态

设 \(T\in\operatorname{End}_{\mathrm{Ab}}(\mathbb Z[1/2])\)。令
\[
q=T(1)\in\mathbb Z[1/2].
\]
对任意 \(k\ge0\)，由
\[
1=2^k\cdot 2^{-k}
\]
得
\[
q=T(1)=2^kT(2^{-k}).
\]
由于 \(\mathbb Z[1/2]\) 无挠，
\[
T(2^{-k})=q/2^k.
\]
于是对任意 \(m/2^k\in\mathbb Z[1/2]\)，
\[
T(m/2^k)=mT(2^{-k})=m q/2^k=q\cdot (m/2^k).
\]
因此 \(T\) 就是乘以 \(q\)：
\[
T=\mu_q.
\]
反过来，任意 \(q\in\mathbb Z[1/2]\) 都给出自同态 \(\mu_q\)。

所以由 S2，
\[
\boxed{
\operatorname{End}(F_P)\cong\mathbb Z[1/2]
}
\]
作为环同构；其中自同态 \(\eta^q\) 由
\[
\eta^q_A(m\otimes a)=qm\otimes a
\]
给出。在记录上，若 \(q=m/2^s\)，则
\[
\eta^q_A([n,a])=[n+s,\,m a].
\]
恒等对应 \(q=1\)，复合对应 \(q\) 的乘法。

## 2. 全部自同构

\(\mu_q\) 可逆当且仅当 \(q\) 是环 \(\mathbb Z[1/2]\) 的单位。\(\mathbb Z[1/2]\) 的单位恰为
\[
\{\pm 2^k:k\in\mathbb Z\}.
\]
因此
\[
\boxed{
\operatorname{Aut}(F_P)\cong\{\pm2^k:k\in\mathbb Z\}
\cong C_2\times\mathbb Z.
}
\]

## 3. 无限积比较映射不满射的具体元素

由 S1，
\[
F_P(\mathbb Z^{\mathbb N})
\cong M_P\otimes\mathbb Z^{\mathbb N}
\cong\varinjlim_n\mathbb Z^{\mathbb N},
\]
其中过渡映射为 \(v\mapsto 2v\)。典范比较映射
\[
c:F_P(\mathbb Z^{\mathbb N})\longrightarrow F_P(\mathbb Z)^{\mathbb N}
\]
在记录上为
\[
c([n,v])=\left(\frac{v_j}{2^n}\right)_{j\ge0},
\qquad
v=(v_j)_{j\ge0}\in\mathbb Z^{\mathbb N}.
\]
也就是 \(c\) 的像由“具有某个公共分母 \(2^n\)”的序列组成。

取
\[
\xi=\left(1,\frac12,\frac14,\frac18,\dots\right)
=\left(2^{-j}\right)_{j\ge0}
\in F_P(\mathbb Z)^{\mathbb N}
=\mathbb Z[1/2]^{\mathbb N}.
\]
若 \(\xi=c([n,v])\)，则对所有 \(j\ge0\)，
\[
\frac{v_j}{2^n}=2^{-j},
\]
即
\[
v_j=2^{\,n-j}.
\]
当 \(j>n\) 时，\(2^{n-j}\) 不是整数，与 \(v_j\in\mathbb Z\) 矛盾。因此
\[
\boxed{
\xi=(2^{-j})_{j\ge0}
\text{ 不在 }F_P(\mathbb Z^{\mathbb N})\to F_P(\mathbb Z)^{\mathbb N}
\text{ 的像中。}
}
\]
故典范比较映射不满射。

## 4. 与有限极限保持的关系

这并不与 S2 矛盾。S2 断言 \(F_P\) 保持**有限**极限；有限乘积是有限直和，而张量积与有限直和交换：
\[
F_P(\mathbb Z^r)\cong M_P\otimes\mathbb Z^r
\cong (M_P)^r
\cong F_P(\mathbb Z)^r
\qquad(r<\infty).
\]
也就是说，对有限多个坐标，总可以选一个公共分母 \(2^n\)，所以比较映射是同构。

而 \(\mathbb Z^{\mathbb N}=\prod_{j\in\mathbb N}\mathbb Z\) 是一个**可数无限乘积**，不是有限极限。上面的元素 \(\xi\) 的各坐标分母无界，且没有单一的公共分母，正好说明
\[
F_P\Bigl(\prod_{j\in\mathbb N}\mathbb Z\Bigr)
\not\cong
\prod_{j\in\mathbb N}F_P(\mathbb Z).
\]
这与 S3 的判据一致：对 \(a_n=2\) 的塔，\(M_P=\mathbb Z[1/2]\) 不有限生成，故 \(F_P\) 既不可表示，也不保持可数小图表极限；但它仍保持一切有限极限。