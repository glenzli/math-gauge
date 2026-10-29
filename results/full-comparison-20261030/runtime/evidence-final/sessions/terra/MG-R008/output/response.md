令
\[
X_n=P_n^\vee:=\operatorname{Hom}_{\mathbb Z}(P_n,\mathbb Z),
\qquad
d_{n,m}=\rho_{n,m}^\vee:X_n\longrightarrow X_m,
\]
并记
\[
G_{\mathbf P}:=\varinjlim_n X_n,\qquad \iota_n:X_n\longrightarrow G_{\mathbf P}.
\]
这是一个可数无挠阿贝尔群。有限秩自由群的对偶配对给出自然同构
\[
F_{\mathbf P}(A)\cong G_{\mathbf P}\otimes_{\mathbb Z}A. \tag{1}
\]

**主定理。** 对给定的塔，下列条件等价：

1. 存在 \(P\in\mathbf{Ab}_{\mathcal U}\)，使 \(F_{\mathbf P}\) 自然同构于 \(\operatorname{Hom}_{\mathbb Z}(P,-)\)。
2. 题目中的比较映射对每个对象集与箭头集均可数的 \(\mathcal U\)-小图表都是同构。
3. 对可数个整数群的乘积，比较映射
   \[
   F_{\mathbf P}(\mathbb Z^{\mathbb N})
   \longrightarrow F_{\mathbf P}(\mathbb Z)^{\mathbb N}
   \]
   是满射。
4. \(G_{\mathbf P}\) 是有限生成群。
5. 塔满足以下只涉及其各层和过渡映射的条件：
   \[
   \boxed{\;
   \exists n\ \forall m\ge n\ \exists r\ge m\
   \exists h:P_n\to P_m,\qquad
   \rho_{m,r}=h\circ\rho_{n,r}.
   \;} \tag{2}
   \]

这些条件成立时，\(G_{\mathbf P}\) 是有限秩自由群，唯一的表示对象的同构类型为
\[
P_{\mathrm{rep}}=G_{\mathbf P}^\vee.
\]
此时 \(F_{\mathbf P}\) 实际上保持所有 \(\mathcal U\)-小极限。因此，可表示性与题目要求的可数极限相容性完全等价。

可以从有限多层构造表示对象。取满足 (2) 的 \(n\)，令
\[
K_n=\ker\iota_n=\bigcup_{m\ge n}\ker d_{n,m}.
\]
由于 \(X_n\) 有限生成，存在 \(M\ge n\) 使 \(K_n=\ker d_{n,M}\)。于是
\[
L:=\operatorname{im}(d_{n,M})\subseteq X_M
\]
经 \(\iota_M\) 同构于 \(G_{\mathbf P}\)，所以可取 \(P_{\mathrm{rep}}=L^\vee\)。若 \(r=\operatorname{rank}\rho_{n,M}\)，则每个表示对象都同构于 \(\mathbb Z^r\)。

更精确地，固定一个群 \(P\) 后，所有自然同构
\[
F_{\mathbf P}(-)\xrightarrow{\sim}\operatorname{Hom}(P,-)
\]
对应于所有群同构 \(s:P\xrightarrow{\sim}G_{\mathbf P}^\vee\)；对应的自然同构在纯张量上为
\[
g\otimes a\longmapsto\bigl(p\longmapsto s(p)(g)\,a\bigr).
\]

下面证明这些结论。

对每个有限秩自由群 \(P_n\)，映射
\[
X_n\otimes A\longrightarrow\operatorname{Hom}(P_n,A),
\qquad
\lambda\otimes a\longmapsto\bigl(p\mapsto\lambda(p)a\bigr)
\]
是自然同构，且与塔的过渡映射相容。张量积与滤过余极限交换，故得到 (1)。

每个 \(X_n\) 可数，故其顺序余极限 \(G_{\mathbf P}\) 可数。它也无挠：若 \(k\ne0\) 且 \(k\iota_n(x)=0\)，则在某个 \(m\ge n\) 有 \(k\,d_{n,m}(x)=0\)；\(X_m\) 无挠，故 \(d_{n,m}(x)=0\)，从而 \(\iota_n(x)=0\)。所用余极限、张量积和可数乘积均属于 \(\mathcal U\)。

先将条件 (4) 转换为塔条件。因为每个 \(X_n\) 有限生成，
\[
G_{\mathbf P}\text{ 有限生成}
\quad\Longleftrightarrow\quad
\exists n,\ \iota_n(X_n)=G_{\mathbf P}. \tag{3}
\]
事实上，若 \(G_{\mathbf P}\) 有有限个生成元，可在同一足够高的层代表它们。

设 \(\iota_n(X_n)=G_{\mathbf P}\)，并固定 \(m\ge n\)。取 \(X_m\) 的一组有限基。每个基向量在 \(G_{\mathbf P}\) 中的像都等于某个 \(X_n\) 元素的像；由有限性，可取共同的 \(r\ge m\)，并得到同态 \(b:X_m\to X_n\)，使
\[
d_{m,r}=d_{n,r}\circ b.
\]
对偶化并用有限秩自由群与其双对偶的典范同构，得到
\(\rho_{m,r}=b^\vee\circ\rho_{n,r}\)，即 (2)。

反过来，若 (2) 成立，则对每个 \(m\ge n\)，对偶化该式表明
\[
\iota_m(X_m)\subseteq\iota_n(X_n).
\]
较低层的像也包含在 \(\iota_n(X_n)\) 中，因此 \(\iota_n(X_n)=G_{\mathbf P}\)。这证明了条件 (4) 与 (5) 等价。

再看乘积比较映射。通过 (1)，它是
\[
\gamma:G_{\mathbf P}\otimes\mathbb Z^{\mathbb N}
\longrightarrow G_{\mathbf P}^{\mathbb N},
\qquad
g\otimes(a_i)_i\longmapsto(a_i g)_i.
\]
更具体地，
\[
\operatorname{im}\gamma
=
\bigcup_{\substack{H\le G_{\mathbf P}\\ H\text{ 有限生成}}}
H^{\mathbb N}. \tag{4}
\]
一方面，张量积中的元素是有限个纯张量之和，所以其各坐标都位于同一个有限生成子群中。另一方面，每个这样的 \(H\) 都是有限秩自由群，因而
\(H\otimes\mathbb Z^{\mathbb N}\cong H^{\mathbb N}\)。

同一论证还表明 \(\gamma\) 总是单射：任一张量来自某个有限生成子群 \(H\)；若它在 \(G_{\mathbf P}^{\mathbb N}\) 中为零，则它在 \(H^{\mathbb N}\) 中也为零，而 \(H\otimes\mathbb Z^{\mathbb N}\to H^{\mathbb N}\) 是同构。

由于 \(G_{\mathbf P}\) 可数，可取一个列出其全部元素的序列。若 \(\gamma\) 满射，(4) 表明这个序列的所有项都位于某个有限生成子群中，故 \(G_{\mathbf P}\) 本身有限生成。这证明条件 (3) 蕴含条件 (4)。

若条件 (4) 成立，有限生成无挠阿贝尔群 \(G_{\mathbf P}\) 是有限秩自由群。于是典范映射
\[
G_{\mathbf P}\otimes A
\longrightarrow\operatorname{Hom}(G_{\mathbf P}^\vee,A),
\qquad
g\otimes a\longmapsto(\lambda\mapsto\lambda(g)a)
\]
是自然同构，故条件 (1) 成立。表示函子按极限的泛性质保持所有 \(\mathcal U\)-小极限，所以条件 (1) 蕴含条件 (2)；对以 \(\mathbb N\) 为对象集的离散范畴应用条件 (2)，就得到条件 (3)。主定理的等价性得证。

上面的有限层构造也随之成立：由 (3)，\(\iota_n\) 满射；而 \(K_n\) 是有限秩自由群 \(X_n\) 的子群，故有限生成。其有限个生成元都在某个共同的后续层变为零，得到所需的 \(M\)。因而 \(\iota_M|_L:L\to G_{\mathbf P}\) 是同构。任意两个表示对象同构，以及表示同构由 \(s:P\to G_{\mathbf P}^\vee\) 参数化，都由协变 Yoneda 引理得到。

对任意两座塔 \(\mathbf P,\mathbf Q\)，全部自然变换还有两个等价的描述。首先，在 (1) 下，
\[
\operatorname{Nat}(F_{\mathbf P},F_{\mathbf Q})
\cong
\operatorname{Hom}_{\mathbb Z}(G_{\mathbf P},G_{\mathbf Q}). \tag{5}
\]
对应于 \(\alpha:G_{\mathbf P}\to G_{\mathbf Q}\) 的自然变换在 \(A\) 上为
\[
\alpha\otimes I_A:G_{\mathbf P}\otimes A\to G_{\mathbf Q}\otimes A.
\]
反之，任意自然变换在 \(\mathbb Z\) 上的分量给出 \(\alpha\)。对 \(a\in A\) 使用同态 \(\mathbb Z\to A,\ 1\mapsto a\)，自然性迫使该变换把每个 \(g\otimes a\) 送到 \(\alpha(g)\otimes a\)，从而确定其全部分量。在 (5) 下，恒等变换对应恒等同态，复合对应同态的通常复合；自然变换可逆当且仅当 \(\alpha\) 是同构。

其次，可以直接用塔的逐层记录描述。存在自然双射
\[
\operatorname{Nat}(F_{\mathbf P},F_{\mathbf Q})
\cong
\varprojlim_n\ \varinjlim_m
\operatorname{Hom}_{\mathbb Z}(Q_m,P_n), \tag{6}
\]
其中内层余极限通过与 \(\mathbf Q\) 的过渡映射前复合形成；外层从 \(n+1\) 到 \(n\) 的映射则是与 \(\rho_n\) 后复合。

具体地，(6) 右侧的元素是一族相容的
\[
t_n=[m,f:Q_m\to P_n]\in F_{\mathbf Q}(P_n).
\]
它作用在记录上的公式为
\[
[n,u:P_n\to A]\longmapsto[m,u\circ f:Q_m\to A]. \tag{7}
\]
相容性保证该公式与各个代表元的选择无关。反过来，对于自然变换 \(\tau\)，取
\[
t_n=\tau_{P_n}\bigl([n,I_{P_n}]\bigr)
\]
便恢复这族相容记录；自然性随即给出 (7)。这证明了 (6)。

恒等变换对应
\[
t_n=[n,I_{P_n}]\qquad(n\ge0).
\]
若 \(t:F_{\mathbf P}\to F_{\mathbf Q}\)、\(s:F_{\mathbf Q}\to F_{\mathbf R}\)，并选取
\[
t_n=[m,f:Q_m\to P_n],\qquad
s_m=[k,g:R_k\to Q_m],
\]
则复合的第 \(n\) 项为
\[
(s\circ t)_n=[k,f\circ g:R_k\to P_n]. \tag{8}
\]
在 (5) 下，\([m,f]\) 在第 \(n\) 层给出的群同态是
\[
X_n\longrightarrow G_{\mathbf Q},\qquad
\lambda\longmapsto\iota_m^{\mathbf Q}(f^\vee\lambda).
\]
这些同态相容，故诱导 \(G_{\mathbf P}\to G_{\mathbf Q}\)；公式 (8) 正对应这些群同态的复合。

最后，(5) 也给出这类函子的整体分类：它们按自然同构分类，等价于可数无挠阿贝尔群按群同构分类。确实，任给可数无挠群 \(G\)，将其写成递增的有限生成子群之并
\[
G_0\subseteq G_1\subseteq\cdots,\qquad \bigcup_nG_n=G.
\]
每个 \(G_n\) 都是有限秩自由群。取 \(P_n=G_n^\vee\)，过渡映射为包含 \(G_n\hookrightarrow G_{n+1}\) 的对偶，则所得塔满足 \(G_{\mathbf P}\cong G\)。

例如，若所有 \(P_n=\mathbb Z\) 且过渡映射均为乘 \(2\)，则 \(G_{\mathbf P}\cong\mathbb Z[1/2]\)。它秩为 \(1\) 但不是有限生成群；序列 \((2^{-n})_{n\ge0}\) 不在上述乘积比较映射的像中。因此，这座塔既不可表示，也不满足可数极限相容性。