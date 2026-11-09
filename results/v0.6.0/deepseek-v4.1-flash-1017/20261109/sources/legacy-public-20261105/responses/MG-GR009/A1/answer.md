以下固定题设记号：\(\mathbf C=\mathrm{Sh}(\mathrm{Prof}_U)\)，覆盖为有限联合满射覆盖；\(H=h_T\)，\(\Gamma\) 在 \(T\) 上的作用记为 \(h_\gamma\)，等变层的作用记为 \(a_\gamma\)。等变层的态射均指在切片 \(\mathbf C/H\) 中且与 \(\Gamma\)-作用相容的态射。

---

## S1　有限群的自由作用

### 1.1 轨道空间

设 \(\Gamma\) 有限且在 \(T\) 上自由。令
\[
q:T\longrightarrow T/\Gamma
\]
为轨道投影。

- \(T/\Gamma\) 是紧 Hausdorff 的：有限群作用的商映射是 proper、finite-to-one 的。
- \(T/\Gamma\) 全不连通：若 \(O\subset T\) 是一条轨道，\(F\subset T\) 是不含 \(O\) 的闭不变子集，则可取包含 \(O\)、与 \(F\) 不交的 clopen 集 \(C\)，再令
  \[
  U=\bigcap_{\gamma\in\Gamma}\gamma C.
  \]
  则 \(U\) 是 clopen、\(\Gamma\)-不变、包含 \(O\)、与 \(F\) 不交。其像给出 \(T/\Gamma\) 中的 clopen 集分离 \([O]\) 与 \([F]\)。故 \(T/\Gamma\) 有 clopen 基。

于是 \(T/\Gamma\in \mathrm{Prof}_U\)。

因为作用自由，
\[
T\times_{T/\Gamma}T\cong \Gamma\times T,
\]
其中同构可取为
\[
(\gamma,t)\longmapsto (t,\gamma t),
\]
两个投影分别是
\[
p_1(\gamma,t)=t,\qquad p_2(\gamma,t)=\gamma t.
\]

### 1.2 \(h_{T/\Gamma}\) 是层商

对任意 \(Y\in\mathbf C\)，由 \(\{q:T\to T/\Gamma\}\) 是覆盖，层公理给出
\[
Y(T/\Gamma)\cong \operatorname{Eq}\Bigl(
Y(T)\rightrightarrows Y(T\times_{T/\Gamma}T)
\Bigr).
\]
利用 \(T\times_{T/\Gamma}T\cong\Gamma\times T\)，右端正是使
\[
s(t)=s(\gamma t)\qquad(\forall \gamma\in\Gamma,\ t\in T)
\]
的截面 \(s\in Y(T)\)，即 \(Y(T)^\Gamma\)。另一方面，商 \(Q\) 的泛性质为
\[
\operatorname{Hom}_{\mathbf C}(Q,Y)
\cong \operatorname{Hom}_{\mathbf C}(H,Y)^\Gamma
=Y(T)^\Gamma.
\]
因此
\[
Q\cong h_{T/\Gamma}.
\]
即 \(h_{T/\Gamma}\) 是 \(h_T\) 在 \(\Gamma\)-作用下的层商。

### 1.3 所有等变层均可实现

令 \(Q=h_{T/\Gamma}\)，\(q:H=h_T\to Q\) 为商映射。映射 \(q\) 是一个覆盖，其 Čech 群胚为
\[
H\times_QH\cong h_{T\times_{T/\Gamma}T}\cong h_{\Gamma\times T}.
\]
一个等变层 \(E\to H\) 及其作用 \(a_\gamma\) 恰好给出沿该 Čech 群胚的下降数据：在 \((\gamma,t)\) 上，
\[
a_\gamma:E_t\longrightarrow E_{\gamma t}.
\]
作用律 \(a_{\gamma\delta}=a_\gamma a_\delta\) 给出余圈条件。

由于 \(\mathbf C\) 是 Grothendieck topos，而 \(q\) 是覆盖、从而是有效满射，沿 \(q\) 的下降是有效的。因此存在 \(D\to Q\) 及同构
\[
E\cong H\times_QD.
\]
在这个同构下，\(\Gamma\)-作用正是
\[
(h,d)\longmapsto (h_\gamma h,d),
\]
即只改变 \(H\)-坐标。故每个等变层 \(E\to H\) 都在 \(Q\) 上实现。

事实上，上述下降给出
\[
(\mathbf C/H)^\Gamma\simeq \mathbf C/Q,
\]
其中正向函子为 \(D\mapsto q^*D=H\times_QD\)。

---

## S2　有限集合上的纤维分类

设 \(\Gamma,T\) 有限，\(X\) 为有限 \(\Gamma\)-集合，\(f:X\to T\) 等变。令
\[
S=T/\Gamma.
\]
因为 \(T\) 有限离散，\(S\) 也是有限离散。与 S1 相同的层条件（此处不需要自由）给出
\[
Q=h_{T/\Gamma}=h_S.
\]

取每个 \(T\)-轨道的一个代表 \(t_i\)，设
\[
G_i=\Gamma_{t_i}.
\]
记
\[
X_i=f^{-1}(t_i).
\]
则 \(X_i\) 是有限 \(G_i\)-集合。

### 2.1 \(X\to T\) 的分类

\(X\to T\) 在同构意义下由各 \(X_i\) 决定：
\[
X\cong \coprod_i \Gamma\times_{G_i}X_i
\longrightarrow
\coprod_i \Gamma/G_i\cong T,
\]
其中
\[
[\gamma,x]\longmapsto \gamma t_i,\qquad x\in X_i.
\]
反之，任意有限 \(G_i\)-集合 \(X_i\) 都通过该诱导构造给出一个等变映射 \(X\to T\)。

等变映射也逐轨道分解：
\[
\operatorname{Hom}^{\Gamma}_T(X,X')
\cong \prod_i \operatorname{Hom}^{G_i}(X_i,X_i').
\]
因此 \(X\cong X'\) 当且仅当对每个 \(i\)，有 \(G_i\)-等变双射 \(X_i\cong X_i'\)。

### 2.2 \(h_X\) 可实现的充要条件

考虑典范映射
\[
\Phi:X\longrightarrow T\times_S(X/\Gamma),
\qquad
x\longmapsto (f(x),[x]).
\]
这是 \(T\) 上的 \(\Gamma\)-等变映射。另一方面，由 Yoneda 与有限离散性，
\[
h_T\times_{h_S}h_{X/\Gamma}\cong h_{T\times_S(X/\Gamma)}.
\]
故
\[
h_X\text{ 在 }Q=h_S\text{ 上可实现}
\iff
\Phi\text{ 是同构}.
\]
而在轨道 \(i\) 上，\(\Phi\) 的纤维映射正是商映射
\[
X_i\longrightarrow X_i/G_i.
\]
因此得到充要条件：
\[
\boxed{\ h_X\text{ 在 }Q\text{ 上可实现}
\iff
\text{对每个 }i,\ G_i=\Gamma_{t_i}\text{ 在 }X_i\text{ 上作用平凡。}\ }
\]
等价地，对每个 \(t\in T\)，稳定子 \(\Gamma_t\) 在纤维 \(X_t=f^{-1}(t)\) 上作用平凡。

若条件成立，则
\[
X\cong T\times_S Y,\qquad Y=X/\Gamma=\coprod_i X_i,
\]
且实现对象为
\[
D=h_Y=h_{X/\Gamma}\in\mathbf C/Q.
\]
必要性也可直接看出：若 \(h_X\cong H\times_QD\)，则 \(t_i\) 固定时，作用只改变 \(H\)-坐标，故在纤维 \(X_i\) 上 \(G_i\) 必须作用平凡。

### 2.3 可实现对象的自同构群

在等变切片 \(\mathbf C/H\) 中，
\[
\operatorname{Aut}^{\Gamma}_{\mathbf C/H}(h_X)
\cong
\operatorname{Aut}_{\Gamma/T}(X).
\]
若 \(X\cong T\times_SY\) 且 \(Y=\coprod_i X_i\)，则在 \(T\) 上的等变自同构由 \(Y\) 在 \(S\) 上的自同构决定。由于 \(Y\) 是有限 \(S\)-集合，
\[
\operatorname{Aut}_{\mathbf C/S}(h_Y)
\cong
\operatorname{Aut}_S(Y)
\cong
\prod_i \operatorname{Sym}(X_i).
\]
因此
\[
\boxed{
\operatorname{Aut}^{\Gamma}_{\mathbf C/H}(h_X)
\cong
\prod_i \operatorname{Sym}(X_i)
}
\]
在可实现情形下成立。这里 \(\operatorname{Sym}(\varnothing)=1\)。由于拉回 \(q^*:\mathbf C/Q\to(\mathbf C/H)^\Gamma\) 全忠实，这也是实现对象 \(D=h_{X/\Gamma}\) 在 \(\mathbf C/Q\) 中的自同构群。

---

## S3　一般层的完整下降

### 3.1 构造 \(Q\) 与 \(q\)

在 \(\mathbf C\) 中取余等化子
\[
\coprod_{\gamma\in\Gamma}H
\rightrightarrows
H
\longrightarrow
Q,
\]
其中一个映射在第 \(\gamma\) 个余积分量上为 \(h_\gamma:H\to H\)，另一个为恒等映射。等价地，可取
\[
Q=\operatorname{coeq}\bigl(H\times\Gamma\rightrightarrows H\bigr).
\]
因为这对映射在 \(\gamma=e\) 处有公共截面，\(q:H\to Q\) 是正则满射，特别地局部满射。

由余等化子的泛性质，对任意 \(Y\in\mathbf C\)，
\[
\operatorname{Hom}_{\mathbf C}(Q,Y)
\cong
\{f\in\operatorname{Hom}_{\mathbf C}(H,Y)\mid
f\circ h_\gamma=f\ \ \forall\gamma\in\Gamma\}.
\]
即
\[
\operatorname{Hom}_{\mathbf C}(Q,Y)
\cong
\operatorname{Hom}_{\mathbf C}(H,Y)^\Gamma
\]
自然成立。并且
\[
q\circ h_\gamma=q\qquad(\forall\gamma\in\Gamma).
\]

若 \(\Gamma\) 有限且作用自由，则 \(Q=h_{T/\Gamma}\)，回到 S1。

### 3.2 不预选 \(D\) 的可实现性判据

设 \(E\to H\) 是等变层。定义
\[
D_E:=E/\Gamma
:=\operatorname{coeq}\bigl(\Gamma\times E\rightrightarrows E\bigr),
\]
其中两个映射为
\[
(\gamma,e)\longmapsto e,
\qquad
(\gamma,e)\longmapsto a_\gamma(e).
\]
由于 \(q\pi:E\to Q\) 在两映射下相等，得到
\[
d_E:D_E\longrightarrow Q.
\]
于是有典范映射
\[
c_E:E\longrightarrow H\times_QD_E,
\qquad
e\longmapsto(\pi(e),[e]).
\]
这里 \([e]\) 表示 \(e\) 在 \(E/\Gamma\) 中的像。

**判据：**
\[
\boxed{
E\text{ 在 }Q\text{ 上可实现}
\iff
c_E:E\to H\times_QD_E\text{ 是同构。}
}
\]

证明如下。

- 若 \(E\cong H\times_QD\)，则 \(q^*D=H\times_QD\)。基变换保持余等化子，故
  \[
  (H\times_QD)/\Gamma\cong D.
  \]
  因而 \(D_E\cong D\)，且 \(c_E\) 就是原来的同构。
- 反之，若 \(c_E\) 是同构，则取 \(D=D_E\)，便有
  \[
  E\cong H\times_QD_E,
  \]
  而 \(H\times_QD_E\) 上的 \(\Gamma\)-作用只改变 \(H\)-坐标。因此 \(E\) 可实现。

注意 \(c_E\) 本身是 \(\Gamma\)-等变的：\(D_E\) 不带 \(\Gamma\)-作用，右端的 \(\Gamma\)-作用仅来自 \(H\)。

### 3.3 所有实现及态射的分类

拉回函子
\[
q^*:\mathbf C/Q\longrightarrow(\mathbf C/H)^\Gamma,
\qquad
D\longmapsto H\times_QD
\]
是全忠实的。实际上，若
\[
\varphi:q^*D\to q^*D'
\]
在 \(H\) 上且等变，则写成
\[
\varphi(h,d)=(h,\overline\varphi(h,d)).
\]
等变性给出
\[
\overline\varphi(\gamma h,d)=\overline\varphi(h,d).
\]
故 \(\overline\varphi\) 经
\[
(H\times_QD)/\Gamma\cong D
\]
分解，给出唯一映射 \(D\to D'\)。反向拉回显然。因此 \(q^*\) 全忠实。

由此得到：

1. \(q^*\) 的本质像正是可实现对象。
2. 对固定的 \(E\)，若其可实现，则
   \[
   D_E=E/\Gamma
   \]
   是唯一实现对象（在唯一同构意义下）：任意实现 \(D\) 都有唯一的同构
   \[
   D\cong E/\Gamma
   \]
   与实现同构相容。
3. 若 \(E\cong q^*D\)，\(E'\cong q^*D'\)，则
   \[
   \operatorname{Hom}^{\Gamma}_{\mathbf C/H}(E,E')
   \cong
   \operatorname{Hom}_{\mathbf C/Q}(D,D').
   \]
   因而可实现对象组成的全子范畴通过 \(q^*\) 等价于 \(\mathbf C/Q\)。
4. 固定实现对象 \(E\) 的实现群胚等价于 \(B\operatorname{Aut}_{\mathbf C/Q}(D_E)\)，并且
   \[
   \operatorname{Aut}_{\mathbf C/Q}(D_E)
   \cong
   \operatorname{Aut}^{\Gamma}_{\mathbf C/H}(E).
   \]

### 3.4 任意基底 \(B\to Q\) 的版本

设
\[
b:B\to Q
\]
是任意层。置
\[
H_B:=H\times_QB,
\qquad
q_B:H_B\to B.
\]
基变换保持余等化子，因此 \(q_B\) 仍是 \(\Gamma\)-作用
\[
\Gamma\times H_B\rightrightarrows H_B
\]
的余等化子，并且
\[
H_B/\Gamma\cong B.
\]
于是 S3.2、S3.3 的结论逐字适用于基底 \(B\)：

- 一个等变层 \(F\to H_B\) 在 \(B\) 上可实现，当且仅当
  \[
  c_F^B:F\longrightarrow H_B\times_B(F/\Gamma)
  \]
  是同构。
- 其实现对象在唯一同构意义下为 \(F/\Gamma\)。
- 函子
  \[
  q_B^*:\mathbf C/B\to(\mathbf C/H_B)^\Gamma
  \]
  全忠实，本质像为实现对象。

与基底拉回相容性如下。若 \(E\to H\) 在 \(Q\) 上由 \(D\to Q\) 实现，则
\[
b^*E=E\times_QB
\]
作为 \(H_B\)-上的等变对象由 \(b^*D=D\times_QB\) 实现，并且
\[
b^*(q^*D)\cong q_B^*(b^*D),
\qquad
(b^*E)/\Gamma\cong b^*(E/\Gamma),
\]
以及
\[
b^*c_E\cong c_{b^*E}^B.
\]
这些同构对 \(b\)、\(D\)、\(E\) 以及态射均自然。因此实现与基底拉回严格相容。

---

## S4　单点上的检验

**判断：否。** 仅在 \(E(*)\) 上逐点检查固定性，不足以保证 \(E\) 在 \(Q\) 上可实现。

构造反例如下。

取
\[
T=*,
\qquad
\Gamma=\mathbb Z/2=\{1,\sigma\}.
\]
则
\[
H=h_*=1,
\qquad
Q=1,
\qquad
q=\mathrm{id}_1.
\]

令
\[
R=\{0,1\}^{\mathbb N}
\]
为 Cantor 空间，并令 \(\sigma\) 作用为翻转第一个坐标：
\[
\sigma(x_0,x_1,x_2,\ldots)
=(1-x_0,x_1,x_2,\ldots).
\]
该作用没有不动点。

令 \(\mathcal F\subset h_R\) 为“有限像映射”构成的子层：
\[
\mathcal F(U)
=
\{f\in\operatorname{Hom}_{\mathrm{Prof}_U}(U,R)
\mid f(U)\text{ 是有限集}\}.
\]
这是子层：有限像性质在限制下保持；若 \(\{U_i\to U\}\) 是有限覆盖且每个 \(f|_{U_i}\) 有有限像，则
\[
f(U)=\bigcup_i f(U_i)
\]
也是有限集。

令
\[
E:=h_R/\mathcal F
\]
为把子层 \(\mathcal F\) 坍缩成一点的商层，即
\[
E=\operatorname{coeq}\bigl(\mathcal F\times h_R
\rightrightarrows h_R\bigr)
\]
的等价描述（更具体地，是 \(h_R\leftarrow\mathcal F\to 1\) 的推挤）。记商映射为
\[
q:h_R\longrightarrow E.
\]
\(E\) 是终对象 \(1\) 上的层。

在 Grothendieck topos 中，商去子层 \(\mathcal F\) 后的相等关系可按有限覆盖逐片计算：
\[
q(f)=q(g)
\]
当且仅当存在有限联合满射覆盖 \(\{U_i\to U\}\)，使得对每个 \(i\)，或者
\[
f|_{U_i}=g|_{U_i},
\]
或者
\[
f|_{U_i},\,g|_{U_i}\in\mathcal F(U_i).
\]
这是由商层的余等化子与层公理得到的标准描述。

下面验证 \(E(*)\) 只有一个元素。

任取 \(e\in E(*)\)。因为 \(q:h_R\to E\) 是满射，存在 \(*\) 的有限覆盖 \(\{U_i\to *\}\) 以及提升
\[
f_i\in h_R(U_i)=\operatorname{Hom}(U_i,R)
\]
使得
\[
q(f_i)=e|_{U_i}.
\]
令
\[
W=\coprod_i U_i,
\]
并把 \(f_i\) 拼成
\[
f:W\longrightarrow R.
\]
则 \(q(f)=e|_W\)。

现在 \(\{W\to *\}\) 是单点覆盖，故层公理给出
\[
q(f\circ p_1)=q(f\circ p_2)
\quad\text{in }E(W\times W),
\]
其中 \(p_1,p_2:W\times W\to W\) 是投影。

断言：若 \(f\) 的像无限，则不可能有
\[
q(f\circ p_1)=q(f\circ p_2).
\]
事实上，若等号成立，则有有限覆盖
\[
\{V_j\to W\times W\}
\]
使得在每个 \(V_j\) 上或者
\[
f\circ p_1=f\circ p_2
\]
或者 \(f\circ p_1,f\circ p_2\) 都有有限像。

由于 \(f(W)\) 无限，对每个 \(x\in W\)，存在 \(y\in W\) 使得
\[
f(x)\ne f(y).
\]
点 \((x,y)\in W\times W\) 被某个 \(V_j\) 覆盖。在该 \(V_j\) 上不可能有 \(f\circ p_1=f\circ p_2\)，因为在覆盖 \((x,y)\) 的点处两端值不同。所以在该 \(V_j\) 上 \(f\circ p_1\) 有有限像，从而
\[
f(x)\in f(p_1(V_j))
\]
是有限集。对所有 \(x\in W\)，这样的有限个 \(j\) 覆盖了 \(W\)：
\[
W=\bigcup_j p_1(V_j).
\]
于是
\[
f(W)=\bigcup_j f(p_1(V_j))
\]
是有限集，矛盾。故 \(f\) 必须有有限像。

于是 \(f\in\mathcal F(W)\)，从而
\[
q(f)=*
\]
（坍缩点）。因此 \(e|_W=*|_W\)。由于 \(\{W\to *\}\) 是覆盖，得到 \(e=*\)。所以
\[
\boxed{E(*)=\{*\}}
\]
只有一个元素。

再证明 \(\sigma\)-作用非平凡。若
\[
q(\mathrm{id}_R)=q(\sigma),
\]
则由上述逐片判据，存在 \(R\) 的有限覆盖 \(\{V_j\to R\}\)，使得在每个 \(V_j\) 上或者
\[
\mathrm{id}_R|_{V_j}=\sigma|_{V_j},
\]
或者两者都有有限像。

第一种情形不可能：若 \(V_j\ne\varnothing\)，写覆盖映射为 \(u_j:V_j\to R\)，则
\[
u_j(z)=\sigma(u_j(z))
\]
对某个 \(z\) 成立，而 \(\sigma\) 没有不动点，矛盾。因此每个非空 \(V_j\) 都必须属于第二种情形，即 \(u_j\) 有有限像。于是 \(R\) 被有限个有限集
\[
u_j(V_j)
\]
覆盖，矛盾，因为 \(R\) 是无限集。故
\[
q(\mathrm{id}_R)\ne q(\sigma).
\]

\(\sigma\) 置换 \(R\) 保持有限像性质，因此诱导 \(E\) 上的作用 \(a_\sigma\)，且坍缩点 \(*\) 固定。于是
\[
a_\sigma(q(\mathrm{id}_R))
=q(\sigma\circ\mathrm{id}_R)
=q(\sigma)
\ne q(\mathrm{id}_R).
\]
所以 \(a_\sigma\) 在 \(E\) 上不是恒等作用。

现在 \(E(*)=\{*\}\)，因此对唯一的 \(e\in E(*)\) 和任意 \(\gamma\in\Gamma\)，都有
\[
\gamma\pi(e)=\pi(e)
\]
（因 \(T=*\)），并且
\[
a_\gamma(e)=e.
\]
故 S4 的逐点条件成立。

但 \(Q=1\)，\(H=1\)。若 \(E\) 在 \(Q=1\) 上可实现，则
\[
E\cong H\times_QD\cong 1\times_1D\cong D,
\]
而 \(H=1\) 上的 \(\Gamma\)-作用是平凡的，故右端的 \(\Gamma\)-作用只能是恒等作用。于是 \(E\) 上的作用也必须平凡，与 \(a_\sigma\ne\mathrm{id}_E\) 矛盾。

因此 \(E\) 不在 \(Q\) 上可实现。S4 的答案是否定的。

---

## S5　局部满射的基底检验

**判断：是。** 若 \(B\to Q\) 局部满射，则在 \(B\) 上拉回可实现确实反映原对象在 \(Q\) 上可实现。

设
\[
b:B\to Q
\]
局部满射。按题设定义，这等价于 \(b\) 是层 topos \(\mathbf C\) 中的满射：对每个测试对象 \(U\) 及 \(s\in Q(U)\)，存在有限覆盖 \(\{U_i\to U\}\) 和 \(b_i\in B(U_i)\) 使
\[
b(b_i)=s|_{U_i}.
\]

置
\[
H_B=H\times_QB,
\qquad
E_B=E\times_QB=b^*E.
\]
由 S3.4，
\[
E_B/\Gamma\cong b^*(E/\Gamma),
\]
且
\[
b^*c_E\cong c_{E_B}^B.
\]
题设说 \(E_B\) 在 \(B\) 上可实现。由 S3 的判据，
\[
c_{E_B}^B
\]
是同构。

现在使用标准下降事实：

> 在 Grothendieck topos 中，沿满射的拉回反映同构。  
> 换言之，若 \(f:X\to Y\) 在 \(\mathbf C/Q\) 中且 \(b^*f\) 是同构，则 \(f\) 本身是同构。

其证明可用有效下降：\(b\) 是有效满射，\(b^*f\) 的逆沿核对 \(B\times_QB\rightrightarrows B\) 的两个拉回相等，因此给出下降数据，下降为 \(Y\to X\)；再由拉回的忠实性，它就是 \(f\) 的逆。这里 \(\mathbf C\) 是 Grothendieck topos、\(b\) 是满射，条件适用。

于是
\[
b^*c_E\cong c_{E_B}^B
\]
是同构，故 \(c_E\) 是同构。由 S3 判据，\(E\) 在 \(Q\) 上可实现。

因此 S5 的答案是肯定的。

---

## S6　非空基底与全局结论

**判断：否。** “\(B\) 非空且可表示”本身不足以推出拉回可实现反映原对象可实现；还必须要求 \(B\to Q\) 在某种意义下覆盖 \(Q\)。

### 6.1 完整反例

取
\[
\Gamma=\mathbb Z/2=\{1,\sigma\},
\qquad
T=\{a,b\}
\]
为两点离散空间，\(\Gamma\) 在 \(T\) 上作用平凡。于是
\[
H=h_T=h_{\{a\}}\sqcup h_{\{b\}}
=\mathbf 1_a\sqcup\mathbf 1_b,
\]
且
\[
Q=H,
\qquad
q=\mathrm{id}_H.
\]

再取
\[
R=\{0,1\},
\]
令 \(\sigma\) 交换 \(0,1\)。令
\[
E=\mathbf 1_a\sqcup h_R.
\]
定义投影
\[
\pi:E\longrightarrow H
\]
为：在第一个余积分量 \(\mathbf 1_a\) 上取到 \(\mathbf 1_a\) 的恒等映射；在第二个余积分量 \(h_R\) 上取唯一映射
\[
h_R\longrightarrow \mathbf 1_b.
\]
定义 \(\Gamma\)-作用：在 \(\mathbf 1_a\) 上平凡；在 \(h_R\) 上由 \(\sigma:R\to R\) 后复合给出。由于 \(\Gamma\) 在 \(H\) 上作用平凡，该作用覆盖
\[
h_\gamma=\mathrm{id}_H.
\]
因此 \(E\to H\) 是等变层。

取
\[
B=\mathbf 1_a=h_*\hookrightarrow Q=H.
\]
这是非空可表示层，且 \(B\to Q\) 是包含一个连通分量的单射。

计算拉回：
\[
H_B=H\times_QB\cong B,
\qquad
E_B=E\times_QB\cong \mathbf 1_a.
\]
\(E_B\) 上的 \(\Gamma\)-作用是平凡的。它在 \(B\) 上可实现：取
\[
D=\mathbf 1_a\in\mathbf C/B,
\]
则
\[
H_B\times_BD\cong B\times_BD\cong D\cong E_B,
\]
并且作用只改变 \(H_B=B\) 的坐标，而 \(B\) 上 \(\Gamma\)-作用平凡，故诱导作用正是 \(E_B\) 的平凡作用。

但是 \(E\) 不在 \(Q\) 上可实现。若
\[
E\cong H\times_QD,
\]
由于 \(Q=H\) 且 \(q=\mathrm{id}_H\)，
\[
H\times_QD\cong H\times_HD\cong D.
\]
而 \(H=Q\) 上 \(\Gamma\)-作用平凡，所以 \(H\times_QD\) 上的 \(\Gamma\)-作用只能是恒等作用。于是 \(E\) 上的作用也必须平凡。可是在第二个余积分量 \(h_R\) 上，\(\sigma\) 交换 \(0\) 与 \(1\)：例如
\[
a_\sigma(0)=1\ne 0
\]
在 \(h_R(*)=R\) 上。矛盾。

故
\[
E_B\text{ 在 }B\text{ 上可实现}
\quad\not\Longrightarrow\quad
E\text{ 在 }Q\text{ 上可实现}.
\]
S6 的答案是否定的。这里 \(B=\mathbf 1_a\) 非空可表示，但 \(B\hookrightarrow Q\) 只覆盖了 \(Q\) 的一个分量，并不是局部满射。

### 6.2 可用的检验原则

由以上各阶段可整理如下。

1. **通用判据（S3）。**  
   先算
   \[
   D_E=E/\Gamma,
   \]
   再检查典范映射
   \[
   c_E:E\to H\times_Q(E/\Gamma)
   \]
   是否为同构。这是不预选实现对象 \(D\) 的完整判据。

2. **有限自由作用自动实现（S1）。**  
   若 \(\Gamma\) 有限且在 \(T\) 上自由，则每个等变层都在 \(Q=h_{T/\Gamma}\) 上可实现。

3. **有限集合情形逐稳定子检查（S2）。**  
   在 S2 的有限情形，只需检查每个代表纤维 \(X_i\) 上 \(G_i=\Gamma_{t_i}\) 作用是否平凡；等价地，
   \[
   X\cong T\times_{T/\Gamma}(X/\Gamma).
   \]

4. **单点检查不够（S4）。**  
   即使对每个 \(e\in E(*)\) 及固定 \(\pi(e)\) 的 \(\gamma\) 都有 \(a_\gamma(e)=e\)，也不能推出可实现。必须检查整个层 \(E\)，而不只是全局点。

5. **局部满射基底可以检验（S5）。**  
   若 \(B\to Q\) 局部满射，则
   \[
   E\times_QB\text{ 在 }B\text{ 上可实现}
   \Longrightarrow
   E\text{ 在 }Q\text{ 上可实现}.
   \]
   更一般地，若一族 \(\{B_i\to Q\}\) 使
   \[
   \coprod_iB_i\longrightarrow Q
   \]
   局部满射，并且每个 \(E\times_QB_i\) 在 \(B_i\) 上可实现，则 \(E\) 在 \(Q\) 上可实现。即“在一族覆盖 \(Q\) 的基底上分别检验”是足够的。

6. **非空可表示本身不够（S6）。**  
   若 \(B=h_S\) 非空但 \(B\to Q\) 不覆盖 \(Q\)，例如只落在 \(Q\) 的一个连通分量上，则拉回可实现只说明 \(E\) 在该分量上可实现；其他分量可能仍有障碍。S6 的反例正是如此。  
   因此应先检查 \(B\to Q\) 是否为局部满射（或若干 \(B_i\) 是否共同局部覆盖 \(Q\)）；若不是，就不能仅由拉回可实现推出全局可实现。

---

### 结论汇总

- **S1：** 有限自由作用时，\(T/\Gamma\) 为 profinite，\(h_{T/\Gamma}\) 是层商；所有等变层均实现。
- **S2：** 有限情形按 \(X_i\) 的 \(G_i\)-作用分类；可实现当且仅当各稳定子作用平凡；自同构群为 \(\prod_i\operatorname{Sym}(X_i)\)。
- **S3：** 一般商 \(Q=H/\Gamma\) 存在；可实现当且仅当 \(E\to H\times_Q(E/\Gamma)\) 为同构；可实现对象范畴等价于 \(\mathbf C/Q\)；任意基底拉回版本及相容性成立。
- **S4：** 否；单点固定条件不足。
- **S5：** 是；局部满射基底拉回可实现反映全局可实现。
- **S6：** 否；非空可表示但不覆盖 \(Q\) 的基底不能反映全局可实现。