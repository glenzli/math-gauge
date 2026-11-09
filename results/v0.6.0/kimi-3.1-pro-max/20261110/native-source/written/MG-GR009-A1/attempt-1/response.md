以下记 \(*\) 为单点空间，并把 \(\gamma\in\Gamma\) 在 \(H=h_T\) 上的作用仍记为 \(\gamma\)。所用层余等化子均指在 \(\mathcal C\) 中取余等化子；等价地，可先取预层商再层化。

## S1　有限群的自由作用

### 1. Profinite 轨道空间

令 \(S=T/\Gamma\) 取商拓扑，\(q:T\to S\) 为商映射。轨道关系
\[
R=\bigcup_{\gamma\in\Gamma}\{(t,\gamma t):t\in T\}\subseteq T\times T
\]
是有限个闭集的并，故为闭集；因此 \(S\) 是紧 Hausdorff 空间。

还需证明 \(S\) 全不连通。设两个不同轨道为 \(O_1,O_2\)。取 clopen 集 \(C\subseteq T\)，使 \(O_1\subseteq C\) 且 \(C\cap O_2=\varnothing\)，再令
\[
C_0=\bigcap_{\gamma\in\Gamma}\gamma C .
\]
则 \(C_0\) 是 \(\Gamma\)-不变 clopen 集，\(O_1\subseteq C_0\)，而 \(C_0\cap O_2=\varnothing\)。其饱和像 \(q(C_0)\) 是 \(S\) 中分离 \(q(O_1)\)、\(q(O_2)\) 的 clopen 集。因此 \(S\) 紧 Hausdorff 且全不连通，从而是 profinite；其 \(U\)-小性由 \(T\) 的 \(U\)-小性得到。

自由性还给出同构
\[
\Gamma\times T\xrightarrow{\;\sim\;}T\times_S T,\qquad
(\gamma,t)\longmapsto(t,\gamma t).
\]
它连续、满射，并由自由性单射；两边分别为紧空间和 Hausdorff 空间，故为同胚。

### 2. \(h_S\) 是层商

对任意 \(Y\in\mathcal C\)，单射满射 \(q:T\to S\) 本身构成覆盖，故层条件给出
\[
Y(S)=\operatorname{Eq}\!\left(Y(T)\rightrightarrows Y(T\times_S T)\right).
\]
利用上述 \(\Gamma\times T\simeq T\times_S T\)，右边正是
\[
Y(T)^\Gamma
=\{y\in Y(T):Y(\gamma)(y)=y\ \text{对所有 }\gamma\}.
\]
由层范畴中的 Yoneda 引理，这自然等同于
\[
\operatorname{Hom}(h_S,Y)
\cong \operatorname{Hom}(H,Y)^\Gamma .
\]
所以
\[
h_S\cong H/\Gamma,
\]
且 \(h_q:H\to h_S\) 是层余等化子投影。

### 3. 所有等变层均可实现

设 \(\pi:E\to H\) 等变，作用为 \(a_\gamma\)。令
\[
D=E/\Gamma
\]
为层商。因为 \(q\pi:E\to h_S\) 是 \(\Gamma\)-不变的，它诱导 \(D\to h_S\)。记 \(r:E\to D\) 为商映射，并有典范态射
\[
\theta:E\longrightarrow H\times_{h_S}D,\qquad
\theta=(\pi,r).
\]
右侧的 \(\Gamma\) 作用只改变 \(H\) 坐标，而 \(\theta\) 显然等变。

层化给出的局部描述是：

- \(r\) 局部满射；
- 若 \(r(e)=r(e')\)，则经有限覆盖细化后，有某个 \(\gamma\) 使 \(e'=a_\gamma(e)\)；
- 对 \(H\to h_S\) 也有同样描述。

由此 \(\theta\) 局部满射：局部把 \(D\)-坐标写成 \(r(e)\)，再把等式 \(q\pi(e)=q(t)\) 细化为 \(\pi(e)=\gamma t\)，用 \(a_{\gamma^{-1}}(e)\) 即可得到所需提升。

若 \(\theta(e)=\theta(e')\)，经细化有 \(e'=a_\gamma(e)\)，且它们的 \(H\)-坐标相同，故
\[
\gamma\pi(e)=\pi(e).
\]
在非空测试空间上取一点，由 \(T\) 上作用自由得 \(\gamma=1\)；空测试空间上的层截面唯一。因此 \(e=e'\)。故 \(\theta\) 也是单态射，从而是同构。

所以每个等变 \(E\to H\) 均在 \(h_S\) 上实现，典范下降对象为 \(E/\Gamma\)。

---

## S2　有限集合上的纤维分类

从每个 \(T\)-轨道中选代表 \(t\)，记代表集为 \(\mathcal R\)，稳定子为 \(S_t=\Gamma_t\)。

### 1. 对象与态射的分类

给定 \(p:X\to T\)，令
\[
Y_t=p^{-1}(t).
\]
等变性使 \(Y_t\) 成为有限 \(S_t\)-集合。反过来，给定一族有限 \(S_t\)-集合 \(Y_t\)，构造
\[
X=\coprod_{t\in\mathcal R}\Gamma\times_{S_t}Y_t,
\]
其中
\[
\Gamma\times_{S_t}Y_t=(\Gamma\times Y_t)/(\gamma s,y)\sim(\gamma,sy),
\]
并定义
\[
[\gamma,y]\longmapsto\gamma t,\qquad
g\cdot[\gamma,y]=[g\gamma,y].
\]
有自然等变同构
\[
X\cong\coprod_{t\in\mathcal R}\Gamma\times_{S_t}p^{-1}(t),\qquad
[\gamma,y]\mapsto\gamma y.
\]

因此，\(T\) 上的有限等变集合范畴等价于
\[
\prod_{t\in\mathcal R}\{\text{有限 }S_t\text{-集合}\}.
\]
在此坐标下，等变态射恰为任意一族 \(S_t\)-等变映射
\[
f_t:Y_t\to Y'_t,
\]
并通过 \([\gamma,y]\mapsto[\gamma,f_t(y)]\) 唯一延拓。

若进一步把有限 \(S_t\)-集合分解为传递轨道，则对象由重数
\[
n_{t,K}\in\mathbb N,\qquad
t\in\mathcal R,\ [K]\ \text{遍历 }S_t\text{ 中子群共轭类}
\]
分类：
\[
Y_t\cong\coprod_{[K]}n_{t,K}\,(S_t/K).
\]
一般对象的等变自同构群为
\[
\operatorname{Aut}(X\to T)
\cong
\prod_{t\in\mathcal R}\ \prod_{[K]}
\left((N_{S_t}(K)/K)\wr\mathfrak S_{n_{t,K}}\right).
\]

### 2. 可实现的充要条件

**充要条件是：每个 \(S_t\) 在 \(Y_t=p^{-1}(t)\) 上作用平凡。**

必要性：若 \(h_X\cong H\times_QD\)，且作用只改变 \(H\) 坐标，则任意 \(\gamma\in S_t\) 固定 \(t\)，故也固定纤维中每个点。

充分性：若所有 \(S_t\)-作用平凡，令
\[
D=\coprod_{t\in\mathcal R}Y_t,
\]
并把 \(Y_t\) 送到轨道点 \([t]\in T/\Gamma\)。则
\[
X\cong T\times_{T/\Gamma}D
\]
为 \(\Gamma\)-等变同构，作用只改变 \(T\) 坐标。

等价地，由于等变性本来就有 \(\Gamma_x\subseteq S_{\pi(x)}\)，可实现性也可写成
\[
\Gamma_x=\Gamma_{\pi(x)}\qquad(x\in X).
\]
在重数坐标中，这意味着只允许 \(K=S_t\) 的轨道类型，即
\[
X\cong\coprod_{t\in\mathcal R}n_t\,(\Gamma/S_t).
\]

若 \(n_t=|Y_t|\)，则可实现对象的等变自同构群为
\[
\boxed{\operatorname{Aut}(h_X)\cong\prod_{t\in\mathcal R}\mathfrak S_{n_t}.}
\]
这也正是其下降对象 \(D\to Q\) 在 \(Q\) 上的自同构群。

---

## S3　一般层的完整下降

### 1. 商基底

定义
\[
Q=H/\Gamma
=\operatorname{Coeq}\!\left(\coprod_{\gamma\in\Gamma}H\rightrightarrows H\right),
\]
两个映射分别为恒等和 \(h_\gamma\)，并令 \(q:H\to Q\) 为投影。余等化子的普遍性质直接给出自然双射
\[
\operatorname{Hom}(Q,Y)
\cong
\{f\in\operatorname{Hom}(H,Y):fh_\gamma=f\ \forall\gamma\}.
\]
这就是所要求的不变映射普遍性质。一般情形下 \(Q\) 不必可表示。

### 2. 不预选 \(D\) 的判据

给定等变 \(\pi:E\to H\)，令
\[
D_E=E/\Gamma,\qquad r_E:E\to D_E.
\]
因为 \(q\pi\) 不变，诱导 \(p_E:D_E\to Q\)。定义
\[
\theta_E=(\pi,r_E):E\longrightarrow H\times_QD_E.
\]

考虑如下**局部迷向条件**：
\[
\tag{Iso}
\begin{array}{l}
\text{对每个 profinite }U\text{、每个 }e\in E(U)\text{ 和每个 }\gamma\in\Gamma,\\
\gamma\,\pi(e)=\pi(e)\ \Longrightarrow\ a_\gamma(e)=e.
\end{array}
\]
这里等式都是测试对象 \(U\) 上的截面的等式，不只是全局点。

**定理：以下三条等价：**

1. \(E\) 在 \(Q\) 上可实现；
2. \(\theta_E\) 是同构；
3. \(E\) 满足 (Iso)。

证明如下。

先注意 \(\theta_E\) 总局部满射。给定局部截面 \((t,d)\)，经覆盖可取 \(e\) 使 \(r_E(e)=d\)。于是
\[
q\pi(e)=p_Er_E(e)=q(t).
\]
由层商 \(Q=H/\Gamma\) 的局部描述，再细化后有 \(\gamma\) 使 \(\gamma\pi(e)=t\)。此时
\[
\theta_E(a_\gamma(e))=(t,d),
\]
故得局部满射性。

接着，\(\theta_E\) 为单态射当且仅当 (Iso) 成立。事实上，若 \(\theta_E(e)=\theta_E(e')\)，则两者 \(H\)-坐标相同，且经细化有 \(e'=a_\gamma(e)\)。于是 \(\gamma\) 固定共同的 \(H\)-坐标；(Iso) 给出 \(a_\gamma(e)=e\)，故 \(e=e'\)。反之，若 \(\theta_E\) 单且 \(\gamma\pi(e)=\pi(e)\)，则
\[
\theta_E(a_\gamma(e))=\theta_E(e),
\]
所以 \(a_\gamma(e)=e\)。

层范畴中局部满射且单即为同构，故 \(2\iff3\)。若 \(\theta_E\) 为同构，它本身就是实现，故 \(2\Rightarrow1\)。最后，若
\[
E\cong H\times_QD
\]
且作用只改变 \(H\) 坐标，则任何固定 \(H\)-坐标的 \(\gamma\) 必固定整个截面，故 (Iso) 成立，即 \(1\Rightarrow3\)。

### 3. 所有实现及态射

对任意 \(D\to Q\)，对象 \(q^*D=H\times_QD\) 自然可实现。由于层 top os 中拉回保持余等化子，
\[
(q^*D)/\Gamma
\cong (H/\Gamma)\times_QD
\cong D.
\]
因此上述结果给出范畴等价
\[
\mathcal C/Q\;\simeq\;
\{\text{可实现的 }H\text{ 上等变层}\},
\]
正向函子为 \(D\mapsto q^*D\)，反向函子为 \(E\mapsto E/\Gamma\)。

特别地：

- 任意实现 \(\alpha:E\cong q^*D\) 都诱导唯一同构
  \[
  D\cong E/\Gamma,
  \]
  并使 \(\alpha\) 与典范实现 \(\theta_E\) 相容；
- 对可实现的 \(E,E'\)，有自然双射
  \[
  \operatorname{Hom}_{H,\Gamma}(E,E')
  \cong
  \operatorname{Hom}_{\mathcal C/Q}(E/\Gamma,E'/\Gamma).
  \]
  向下取 \(\Gamma\)-商，向上用 \(q^*\)。

所以下降对象没有额外选择：在唯一同构意义下，它必须是 \(E/\Gamma\)。

### 4. 任意基底 \(B\to Q\)

令
\[
H_B=H\times_QB,\qquad q_B:H_B\to B.
\]
拉回保持层商，故
\[
H_B/\Gamma\cong B.
\]
对任意 \(D\to B\)，定义
\[
q_B^*D=H_B\times_BD,
\]
作用只改变 \(H_B\) 的 \(H\) 坐标。

对任意等变 \(F\to H_B\)，同样有
\[
D_F=F/\Gamma\to B,\qquad
\theta_F:F\to H_B\times_B(F/\Gamma).
\]
完全相同证明给出：
\[
F\text{ 可在 }B\text{ 上实现}
\iff \theta_F\text{ 为同构}
\iff F\text{ 满足对所有测试截面的 (Iso)}.
\]
并有等价
\[
\mathcal C/B\simeq
\{\text{可实现的 }H_B\text{ 上等变层}\},
\]
以及相应的态射分类
\[
\operatorname{Hom}_{H_B,\Gamma}(q_B^*D,q_B^*D')
\cong\operatorname{Hom}_{\mathcal C/B}(D,D').
\]

### 5. 与基底拉回相容

设 \(u:B'\to B\) 是 \(Q\) 上的态射，记 \(\widetilde u:H_{B'}\to H_B\)。则存在自然同构
\[
q_{B'}^*(u^*D)\cong \widetilde u^{\,*}q_B^*D,
\]
并且拉回保持层商：
\[
(\widetilde u^{\,*}F)/\Gamma
\cong u^*(F/\Gamma).
\]
在这些典范同构下，
\[
\theta_{\widetilde u^{\,*}F}
=\widetilde u^{\,*}\theta_F.
\]
因此可实现对象、其下降对象以及下降态射都与任意基底拉回相容。

---

## S4　单点上的检验

**结论：不必然可实现。**

题设条件只是 \(U=*\) 时的 (Iso)；一般它不能推出所有测试对象上的 (Iso)。下面给出完整反例。

取
\[
T=*,\qquad \Gamma=C_2=\{1,s\},
\]
并令 \(\Gamma\) 在 \(T\) 上作用平凡。于是 \(H=Q=1\)，而可实现性恰要求 \(\Gamma\) 在 \(E\) 上作用平凡。

令 \(A=\mathbb Z_2\) 为二元进展整数所成的 profinite 阿贝尔群。定义预层
\[
P(U)=C(U,A)/\operatorname{Const}(U,A),
\]
其中分母是全体常值连续映射，限制由预合成诱导。令 \(D\) 为 \(P\) 的关联层。\(A\) 上的取负 \(a\mapsto-a\) 保持常值函数子群，故诱导 \(D\) 的自同构，仍记为 \(s\)。

取 \(E=D\)，\(\pi:E\to H=1\) 为唯一态射，\(s\) 按上述自同构作用。等变性显然成立。

### 全局截面条件成立

\(P(*)\) 只有一个元素。关联层的任意截面都可局部由预层截面表示。若 \(x\in D(*)\)，取 \(*\) 的有限覆盖 \(\{V_i\to*\}\)，使 \(x|_{V_i}\) 来自 \(P(V_i)\)。某个 \(V_i\) 非空，取一点 \(u:*\to V_i\)。由于 \(V_i\to*\) 与 \(u\) 的复合为恒等，沿 \(u\) 限制可知 \(x\) 来自 \(P(*)\)。因此
\[
E(*)=D(*)
\]
只有一个元素。故题设中的全局点条件自动成立。

### 但作用非平凡

考虑 \(\operatorname{id}_A\in C(A,A)\) 在 \(D(A)\) 中的像 \(\xi\)。若 \(s(\xi)=\xi\)，则 \([2\operatorname{id}_A]\) 在 \(D(A)\) 中为零。

关联层的局部等号性质意味着：此时存在有限共同满射覆盖 \(\{r_i:V_i\to A\}\)，使每个
\[
2\operatorname{id}_A\circ r_i=2r_i
\]
在 \(P(V_i)\) 中为零，即 \(2r_i\) 为常值映射。由于这些 \(r_i\) 共同满射，这将推出 \(2A\) 是有限集，矛盾；事实上 \(2\mathbb Z_2\) 无限。

所以 \(s\) 在 \(D(A)\) 上非平凡。若 \(E\) 可在 \(Q=1\) 上实现，则作用只改变 \(H=1\) 坐标，必为平凡作用，矛盾。

因此该 \(E\) 满足单点检验，却不可实现。

---

## S5　局部满射的基底检验

**结论：是，\(E\) 必在 \(Q\) 上可实现。**

我们验证 \(E\) 的完整局部迷向条件 (Iso)。设 \(e\in E(U)\)，且
\[
\gamma\pi(e)=\pi(e).
\]
因为 \(B\to Q\) 局部满射，对截面 \(q\pi(e)\in Q(U)\)，存在有限覆盖 \(\{r_i:V_i\to U\}\) 及 \(b_i\in B(V_i)\)，使
\[
p(b_i)=q\pi(e)|_{V_i}.
\]
于是
\[
e_i=(e|_{V_i},b_i)
\]
是 \(E\times_QB\) 在 \(V_i\) 上的截面。

其在 \(H\times_QB\) 中的坐标为 \((\pi(e)|_{V_i},b_i)\)。由于 \(\gamma\) 固定第一个坐标且不改变第二个坐标，\(\gamma\) 固定 \(e_i\) 的整个基坐标。题设说拉回后的对象可在 \(B\) 上实现，故由 S3 的必要条件，
\[
a_\gamma(e_i)=e_i.
\]
投影到 \(E\) 得
\[
a_\gamma(e)|_{V_i}=e|_{V_i}.
\]
这些 \(V_i\) 覆盖 \(U\)，而 \(E\) 是层，故 \(a_\gamma(e)=e\)。

所以 \(E\) 满足 (Iso)，由 S3 即可实现。等价地，也可说拉回后的 \(\theta_E\) 为同构，而局部满射基底的拉回函子反映同构。

---

## S6　非空基底与全局结论

**结论：不必然反映可实现性。**“非空可表示”本身不能保证 \(B\to Q\) 局部满射。

取
\[
\Gamma=C_2,\qquad T=\{0,1\},
\]
并令 \(\Gamma\) 在 \(T\) 上作用平凡。于是 \(Q=H=h_T\)。

令
\[
X=T\times\{0,1\}\to T
\]
为投影。非平凡元素 \(s\) 在纤维 \(t=1\) 上作用平凡，而在 \(t=0\) 上交换两点：
\[
s(0,\varepsilon)=(0,1-\varepsilon),\qquad
s(1,\varepsilon)=(1,\varepsilon).
\]
取 \(E=h_X\)。这是 \(H\) 上的等变对象。

因为 \(Q=H\)，若 \(E\) 可实现，则作用只改变 \(H\) 坐标；但 \(H\) 上作用平凡，所以 \(E\) 上作用也必须平凡。这与纤维 \(t=0\) 上的交换矛盾，故 \(E\) 不可实现。

现在取非空可表示层
\[
B=h_{\{1\}},
\]
并由包含 \(\{1\}\hookrightarrow T\) 给出 \(B\to Q\)。拉回后
\[
E\times_QB\cong h_{\{1\}\times\{0,1\}},
\]
其上的 \(\Gamma\)-作用平凡；同时 \(H\times_QB\cong B\)。取
\[
D=h_{\{0,1\}}\to B,
\]
即得
\[
E\times_QB\cong(H\times_QB)\times_BD,
\]
作用只改变 \(H\)-坐标。因此拉回后可实现，而原对象不可实现。

此处的 \(B\to Q\) 确实不是局部满射：全局截面 \(0\in Q(*)\) 不可能提升到 \(B\)；若能经某个覆盖局部提升，取覆盖空间的一点并限制到 \(*\)，就会得到全局提升，矛盾。

### 可用的检验原则汇总

1. **典范检验**：\(E\) 可实现当且仅当
   \[
   \theta_E:E\to H\times_Q(E/\Gamma)
   \]
   为同构；下降对象在必存在时必为 \(E/\Gamma\)。
2. **局部迷向检验**：等价地，必须对所有测试对象 \(U\)、所有 \(e\in E(U)\) 检验
   \[
   \gamma\pi(e)=\pi(e)\Rightarrow a_\gamma(e)=e.
   \]
   只检验 \(U=*\) 不够。
3. **覆盖基底检验**：若 \(B\to Q\) 局部满射，则
   \[
   E\text{ 可实现}\iff E\times_QB\text{ 可在 }B\text{ 上实现}.
   \]
   对共同局部满射的基底族也可逐一检验。
4. **任意拉回只保留正向结论**：可实现对象的任意拉回仍可应用，且下降对象随之拉回；但非空、可表示的基底若无局部满射性，不能反向推出原对象可实现。