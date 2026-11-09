以下把可实现同构都理解为“在 \(H\) 上且等变”的同构。

先说明两项通用事实。有限联合满射族在拉回和复合下稳定，且该拓扑次典范：若 \(S_i\to S\) 是覆盖，则 \(\coprod_iS_i\to S\) 是紧空间到 Hausdorff 空间的满射，因而是商映射，连续映射可沿它唯一粘合。故各 \(h_T\) 确为层。又因 \(U\in V\)，此站点可取 \(V\)-小骨架，\(\mathcal C\) 是相应的 Grothendieck 拓扑斯；其中满态射恰为题定的局部满射，且满态射对对象的下降有效。

## S1　有限群的自由作用

令 \(P=T/\Gamma\) 为集合轨道空间，赋予商拓扑，记商映射为 \(p:T\to P\)。

轨道等价关系是有限个同胚之图的并，因而在 \(T\times T\) 中闭。紧 Hausdorff 空间的闭等价关系商仍为紧 Hausdorff 空间，所以 \(P\) 紧且 Hausdorff。它还有开闭邻域基：若 \([t]\in O\subset P\)，其中 \(O\) 开，取
\[
t\in C\subset p^{-1}(O)
\]
且 \(C\) 开闭，则
\[
W=\bigcup_{\gamma\in\Gamma}\gamma C
\]
是饱和开闭集，而 \(p(W)\) 是包含 \([t]\)、包含于 \(O\) 的开闭集。故 \(P\) 全不连通，并且所有构造均在 \(U\) 内，所以 \(P\in\mathrm{Prof}_U\)。

由于作用自由，
\[
\Gamma\times T\xrightarrow{\sim}T\times_P T,
\qquad
(\gamma,t)\longmapsto(\gamma t,t)
\]
是连续双射；其源紧、靶 Hausdorff，故为同胚。

映射 \(h_p:h_T\to h_P\) 局部满射：对任意 \(x:S\to P\)，拉回
\[
S\times_P T\longrightarrow S
\]
是 profinite 空间的满射，构成一个覆盖，并给出 \(x\) 的提升。其核对就是上述作用关系。因此，不变映射 \(h_T\to Y\) 恰好在核对上相等，由满态射的有效性唯一经过 \(h_P\)。这证明 \(h_P\) 是层商。

最后，等变结构 \(a_\gamma\) 给出此核对上的下降同构：沿 \((\gamma t,t)\)，把 \(t\) 上的截面 \(e\) 送至 \(a_\gamma(e)\)。群作用律保证余循环条件。由于 \(h_p\) 是层拓扑斯中的满态射，有效下降给出 \(D\to h_P\)，以及
\[
E\cong h_T\times_{h_P}D,
\]
其作用只改变 \(h_T\) 坐标。故每个等变层均可实现。

## S2　有限集合上的纤维分类

取 \(T\) 的轨道代表集 \(R\)，写
\[
K_t=\Gamma_t,\qquad F_t=X_t\quad(t\in R).
\]
稳定子 \(K_t\) 自然作用于纤维 \(F_t\)。得到范畴等价
\[
\mathrm{Fin}_\Gamma/T
\simeq
\prod_{t\in R}\mathrm{Fin}_{K_t}.
\]

其逆构造为
\[
X=\coprod_{t\in R}\Gamma\times_{K_t}F_t,
\qquad
[\gamma,f]\longmapsto\gamma t,
\]
其中 \((\gamma k,f)\sim(\gamma,kf)\)，\(\Gamma\) 从左作用。它是有限集合，映射等变，且代表点 \(t\) 上的纤维恢复为 \(F_t\)。对原来的 \(X\)，映射 \([\gamma,f]\mapsto\gamma f\) 给出所需同构。

因此，等变态射恰由各纤维上的 \(K_t\)-等变映射组成：
\[
\operatorname{Hom}_{\Gamma/T}(X,X')
\cong
\prod_{t\in R}\operatorname{Hom}_{K_t}(F_t,F'_t).
\]

**可实现的充要条件是每个 \(K_t\) 在 \(F_t\) 上作用平凡。**

必要性来自实现的定义：固定 \(t\) 的元素只能改变第一坐标，而在 \(t\) 上第一坐标也不变，故必须固定整个纤维。

反之，若这些稳定子作用均平凡，则
\[
X\longrightarrow T\times_{T/\Gamma}(X/\Gamma),
\qquad x\longmapsto(\pi(x),[x])
\]
是双射。满射性由移动轨道代表得到；若两点有相同像，则它们位于同一纤维且相差一个稳定子元素，因而相等。这是有限离散空间的等变同构，所以可取
\[
D=h_{X/\Gamma}.
\]
等价地，条件是
\[
\Gamma_x=\Gamma_{\pi(x)}\qquad(x\in X).
\]

一般对象的自同构群为
\[
\operatorname{Aut}_{\Gamma/T}(X)
\cong\prod_{t\in R}\operatorname{Aut}_{K_t}(F_t).
\]
对可实现对象，这简化为
\[
\boxed{\operatorname{Aut}_{\Gamma/T}(X)
\cong\prod_{t\in R}\operatorname{Sym}(F_t).}
\]
由 Yoneda 引理，这也是相应等变层的自同构群，并等于下降对象在 \(Q\) 上的自同构群。

## S3　一般层的完整下降

### 商层及局部轨道描述

对任意带 \(\Gamma\)-作用的层 \(F\)，定义
\[
\overline F
=
a\bigl(S\longmapsto F(S)/\Gamma\bigr),
\]
其中 \(a\) 是层化，商预层使用给定的常元素 \(\gamma\) 的作用。

层化有以下局部描述：

- 每个 \(\overline F(S)\) 中的截面，都在某有限覆盖上来自 \(F\)；
- 对 \(u,v\in F(S)\)，
  \[
  [u]=[v]
  \iff
  \text{存在有限覆盖 }S_i\to S
  \text{ 及 }\gamma_i\in\Gamma,\quad
  v|_{S_i}=a_{\gamma_i}(u|_{S_i}).
  \tag{1}
  \]

这是商预层的层化性质；层化所需的逐层局部表示可通过复合覆盖合并为有限覆盖。

取
\[
Q=\overline H,\qquad q:H\to Q.
\]
由层化的泛性质，
\[
\operatorname{Hom}_{\mathcal C}(Q,Y)
\cong
\{f:H\to Y:\ f\circ h_\gamma=f\ \forall\gamma\in\Gamma\},
\]
自然于 \(Y\)。所以 \(q\) 不变，并满足要求的商泛性质；它还是局部满射。这里不要求 \(Q\) 可表示。

### 不预选 \(D\) 的判据

定义
\[
D_E=\overline E.
\]
映射 \(q\pi\) 不变，因而诱导 \(r_E:D_E\to Q\)。有典范等变映射
\[
\kappa_E:E\longrightarrow H\times_QD_E,
\qquad
e\longmapsto(\pi(e),[e]).
\tag{2}
\]

它总是局部满射。事实上，给定 \((x,d)\)，先局部把 \(d\) 提升为 \(e\)。等式 \(qx=q\pi(e)\) 与 (1) 又保证：进一步有限覆盖后，
\[
x=\gamma\pi(e).
\]
此时 \(a_\gamma(e)\) 就是 \((x,d)\) 的提升。

以下条件等价：

1. \(E\) 在 \(Q\) 上可实现；
2. \(\kappa_E\) 是同构；
3. \(\kappa_E\) 是单态射；
4. 对每个测试对象 \(S\)、每个 \(e\in E(S)\) 及每个 \(\gamma\in\Gamma\)，
   \[
   \gamma\pi(e)=\pi(e)\quad\Longrightarrow\quad a_\gamma(e)=e.
   \tag{3}
   \]

证明如下。实现立即蕴含 (3)，因为作用只改变第一坐标。若 (3) 成立，且 \(\kappa_E(e)=\kappa_E(f)\)，则由 (1)，有限覆盖后可写
\[
f=a_\gamma(e),\qquad \pi(f)=\pi(e).
\]
于是 \(\gamma\pi(e)=\pi(e)\)，由 (3) 得 \(f=e\)。层的分离性给出原来的 \(f=e\)，所以 \(\kappa_E\) 单。结合它总是局部满射，局部唯一提升可粘合，故它是同构。最后 (2) 为同构本身便给出实现。

也可把 (3) 写成固定点层上的条件。每个
\[
T^\gamma=\{t\in T:\gamma t=t\}
\]
是闭 profinite 子空间；判据等价于
\[
a_\gamma\big|_{\,E\times_Hh_{T^\gamma}}=\mathrm{id}
\qquad(\gamma\in\Gamma).
\tag{4}
\]
这检验的是整个层上的作用。

### 所有实现及态射的分类

令 \(\mathrm{Eq}^0_\Gamma(H)\) 是满足 (3) 的等变对象组成的满子范畴。则
\[
\boxed{\mathcal C/Q\xrightarrow{\sim}\mathrm{Eq}^0_\Gamma(H),
\qquad D\longmapsto H\times_QD,}
\tag{5}
\]
逆函子为 \(E\mapsto D_E\)。

为核验全忠实性，先看 \(F=H\times_QD\)。投影 \(F\to D\) 是 \(q\) 的拉回，因而局部满射；它的同纤维截面由 (1) 局部相差一个 \(\Gamma\)-元素。因此
\[
\overline{H\times_QD}\cong D.
\tag{6}
\]
此外，对任意等变 \(E\to H\)，都有自然双射
\[
\operatorname{Hom}_{\mathrm{Eq}_\Gamma(H)}
   (E,H\times_QD)
\cong
\operatorname{Hom}_{\mathcal C/Q}(D_E,D):
\]
左边的映射由 \(\pi\) 和一个不变的第二坐标组成，后者恰好唯一经过 \(D_E\)。结合 (6) 即得 (5)。

具体而言，可实现的 \(E,F\) 满足
\[
\operatorname{Hom}_{\mathrm{Eq}_\Gamma(H)}(E,F)
\cong
\operatorname{Hom}_{\mathcal C/Q}(D_E,D_F).
\]
对固定 \(E\)，若记录实现连同同构
\(\phi:E\overset{\sim}{\to}H\times_QD\)，则实现范畴在不可实现时为空；在可实现时，任意两个实现之间存在唯一与这些同构相容的同构。典范实现就是 \((D_E,\kappa_E)\)。

### 任意基底及拉回相容性

给定任意 \(B\to Q\)，令
\[
H_B=H\times_QB.
\]
群作用仅改变 \(H\) 坐标。投影 \(H_B\to B\) 局部满射，且同纤维截面由 (1) 局部属于同一轨道，故
\[
\overline{H_B}\cong B.
\]

对任意等变对象 \(F\to H_B\)，构造
\[
D_{B,F}=\overline F\longrightarrow B.
\]
完全相同的论证给出
\[
\mathcal C/B\simeq\mathrm{Eq}^0_\Gamma(H_B),
\qquad
D\longmapsto H_B\times_BD,
\tag{7}
\]
其中右边仍由所有测试对象上的稳定子平凡条件定义。

若 \(u:B'\to B\)，有自然同构
\[
\boxed{
\overline{F\times_BB'}
\cong
\overline F\times_BB'.}
\tag{8}
\]
右边的截面可局部把 \(\overline F\) 坐标提升到 \(F\)，故典范映射局部满射；两组这样的提升给出同一截面，当且仅当它们局部相差一个 \(\Gamma\)-元素，故该映射也单，从而为同构。

在 (8) 下，典范映射 \(\kappa\) 正是原典范映射的拉回。因此 (7) 的对象分类、态射分类以及实现同构均与基底拉回相容。特别地，
\[
D_{E\times_QB}\cong D_E\times_QB.
\tag{9}
\]

## S4　单点上的检验

**不必可实现，甚至 \(\Gamma=C_2\)、\(T=*\) 时也不成立。**

令
\[
K=(\mathbf Z/3)^{\mathbb N}.
\]
由于 \(\mathbb N\in U\)，这是一个无限的 \(U\)-小 profinite 交换群。定义群层
\[
K_{\mathrm{lc}}(S)
=
\{\text{局部常值映射 }S\to K\},
\]
这里目标 \(K\) 赋离散拓扑。这些映射在紧空间上均有有限像；沿有限联合满射的下降也保持连续，故 \(K_{\mathrm{lc}}\) 是层，并是 \(h_K\) 的子群层。

取交换群层商
\[
M=h_K/K_{\mathrm{lc}},
\]
即商预层的层化。它满足 \(3M=0\)。

首先，\(M(*)=0\)。映射 \(h_K\to M\) 局部满射，而任意 \(*\) 的覆盖都有一个非空成员；选择其中一点便得到该成员到 \(*\) 的结构映射的截面。因此 \(h_K(*)\to M(*)\) 满射。但
\[
h_K(*)=K_{\mathrm{lc}}(*)=K,
\]
所以其像只有零。

其次，\(M\ne0\)。考虑
\[
m=[\mathrm{id}_K]\in M(K).
\]
若 \(m=0\)，则存在有限覆盖 \(f_i:S_i\to K\)，使每个
\(\mathrm{id}_K\circ f_i=f_i\) 局部常值，因而有有限像。有限个有限像不可能联合覆盖无限集合 \(K\)，矛盾。

现在令 \(T=*\)、\(H=Q=*\)、\(\Gamma=C_2=\{1,\sigma\}\)，取 \(E\) 为 \(M\) 的底层集合层，令
\[
a_\sigma(z)=-z.
\]
这是群作用。因为 \(E(*)=\{0\}\)，题设单点条件成立。但 \(-m\ne m\)：否则 \(2m=0\)，结合 \(3m=0\) 将推出 \(m=0\)。

所以作用并不平凡。在 \(H=Q=*\) 时，任何实现的作用都必须平凡，故这个 \(E\) 不可实现。

## S5　局部满射的基底检验

**必可实现。**

记 \(E_B=E\times_QB\)。用 S3 的判据证明即可。

给定任意 \(S,e\in E(S),\gamma\in\Gamma\)，满足
\[
\gamma\pi(e)=\pi(e).
\]
由于 \(B\to Q\) 局部满射，存在有限覆盖 \(S_i\to S\) 和
\(b_i\in B(S_i)\)，提升 \(q\pi(e)|_{S_i}\)。

于是 \((e|_{S_i},b_i)\in E_B(S_i)\) 的基点被 \(\gamma\) 固定。拉回对象可实现，故
\[
a_\gamma(e)|_{S_i}=e|_{S_i}.
\]
由层的分离性，\(a_\gamma(e)=e\)。这对所有测试对象成立，所以 S3 的判据给出原 \(E\) 可实现。

其典范下降对象为 \(D_E\)，并由 (9) 满足
\[
D_{E_B}\cong D_E\times_QB.
\]

## S6　非空基底与全局结论

**仅假设基底非空且可表示，不足以反映可实现性。**

取
\[
\Gamma=C_2=\{1,\sigma\},\qquad T=\{0,1\},
\]
让 \(\Gamma\) 在 \(T\) 上平凡作用。因此 \(Q=h_T\)，且 \(q=\mathrm{id}\)。

令
\[
X=\{a,b,c\},\qquad
\pi(a)=0,\quad\pi(b)=\pi(c)=1,
\]
并令 \(\sigma\) 固定 \(a\)、交换 \(b,c\)。取 \(E=h_X\)，以及非空可表示基底
\[
B=h_{\{0\}}\longrightarrow h_T.
\]
则
\[
H_B\cong *,\qquad E_B\cong h_{\{a\}}\cong *,
\]
作用平凡，所以拉回后可在 \(B\) 上实现，可取 \(D=B\)。

原对象却不可实现：\(\sigma\) 固定基点 \(1\)，但交换其纤维中的 \(b,c\)，违反 S2 或 S3 的必要条件。这里 \(B\to Q\) 并不局部满射，因为 \(1\in Q(*)\) 在任何覆盖上都无法提升到 \(B\)。

由此前结果，可使用以下检验原则：

- 一般情形的充要条件，是在**所有 profinite 测试对象**上检验稳定子作用平凡，即 S3 的 (3) 或 (4)。
- 单点条件一般只有必要性，S4 给出反例；S2 的有限可表示情形则可直接检查集合纤维。
- 可实现性在任意基底拉回下保持，并被局部满射的基底拉回反映；联合局部满射的基底族也能联合检测。
- 非空可表示基底本身不足够。若 \(Q=*\)，则非空可表示 \(B\to *\) 确实是覆盖，此时可应用 S5。
- S1 的有限自由作用使稳定子障碍自动消失，故所有等变层都能下降。