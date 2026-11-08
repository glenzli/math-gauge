以下写 \(\mathbf 1=h_*\)，并将 \(\Gamma\) 的常值层记为 \(\underline\Gamma\)。在 profinite 测试空间上，\(\underline\Gamma(U)\) 可看作连续映射 \(U\to\Gamma\)，其中 \(\Gamma\) 取离散拓扑；这些映射有有限像。

## S1　有限群的自由作用

令 \(P=T/\Gamma\) 带商拓扑。轨道等价关系是有限个闭图像
\[
\bigcup_{\gamma\in\Gamma}\{(t,\gamma t):t\in T\}\subseteq T\times T
\]
的并，因此 \(P\) 是紧 Hausdorff 空间。若两个轨道不同，利用 \(T\) 的零维性和轨道的有限性，可找一个包含第一轨道、避开第二轨道的 \(\Gamma\)-不变开闭集。它在商中的像仍是开闭集，故 \(P\) 全不连通。因此 \(P\) 是 profinite 空间。

可表示预层是层：有限联合满射族可合并为一个从有限不交并出发的满射，而紧空间到 Hausdorff 空间的连续满射是商映射，故连续映射可按覆盖下降。自然映射
\[
h_T\longrightarrow h_P
\]
是局部满射：对任意 \(U\to P\)，拉回
\[
U\times_P T\longrightarrow U
\]
是 profinite 空间间的满射，因而本身是一个覆盖，其上有到 \(T\) 的提升。又因 \(T\to P\) 的同纤维点恰为同一轨道，该映射的核对关系由 \(\Gamma\) 的作用生成。所以 \(h_P\) 是层范畴中的商 \(h_T/\Gamma\)。

自由性还给出同胚
\[
\Gamma\times T\xrightarrow{\sim}T\times_P T,\qquad
(\gamma,t)\longmapsto(t,\gamma t).
\]
它连续且双射；左边紧、右边 Hausdorff。于是对任意等变层 \(E\to h_T\)，群作用恰给出沿 \(h_T\to h_P\) 的下降数据。层范畴中满射是有效下降态射，因此存在 \(D\to h_P\) 及等变同构
\[
E\cong h_T\times_{h_P}D,
\]
其中作用只改变 \(h_T\) 坐标。也可将 \(D\) 取为 \(E\) 的层商 \(E/\Gamma\)。

## S2　有限集合上的纤维分类

对每个 \(T\) 的轨道选代表 \(t\)，令 \(G_t=\Gamma_t\)。把有限等变集合 \(X\to T\) 送到纤维
\[
F_t=X_t,
\]
便得到一个有限 \(G_t\)-集合。反过来，给定各 \(F_t\)，在轨道 \(\Gamma t\cong\Gamma/G_t\) 上构造
\[
X|_{\Gamma t}=\Gamma\times_{G_t}F_t
\longrightarrow \Gamma/G_t,\qquad [\gamma,x]\longmapsto\gamma G_t.
\]
这些构造互逆，故所求范畴等价于各有限 \(G_t\)-集合范畴的乘积。态射对应各纤维上的 \(G_t\)-等变映射。

令 \(Q=h_{T/\Gamma}\)。**可实现的充要条件**是每个稳定子 \(G_t\) 在 \(F_t\) 上平凡作用。

必要性来自实现
\[
h_X\cong h_T\times_Q D
\]
中作用只改变 \(h_T\) 坐标：固定 \(t\) 的元素必须固定其上所有点。反之，若稳定子均平凡作用，则以 \(Y=X/\Gamma\) 有有限集合间的等变双射
\[
X\xrightarrow{\sim}T\times_{T/\Gamma}Y,
\]
所以取 \(D=h_Y\) 即得实现。

可实现对象在 \(h_T\) 上的等变自同构群为
\[
\operatorname{Aut}_{\Gamma/T}(X)
\cong\prod_{[t]\in T/\Gamma}\operatorname{Sym}(F_t),
\]
其中空纤维的对称群为平凡群。

## S3　一般层的完整下降

在层范畴 \(\mathcal C\) 中取余等化子
\[
\underline\Gamma\times H
\;\substack{\longrightarrow\\[-4pt]\longrightarrow}\;
H\xrightarrow{q}Q,
\]
两箭头分别为作用和投影。具体可先取相应预层余等化子，再层化。由余等化子的泛性质，
\[
\operatorname{Hom}(Q,Y)\cong
\operatorname{Hom}(H,Y)^\Gamma
\]
对每个层 \(Y\) 自然成立。这里常值群层的等变性可逐个 \(\gamma\in\Gamma\) 检查，因为常值元素局部生成该层。

\(q\) 是层范畴中的满射，也即题目意义下的局部满射。令
\[
R=H\times_Q H.
\]
自然箭头
\[
\underline\Gamma\times H\longrightarrow R,\qquad
(\gamma,h)\longmapsto(h,\gamma h)
\]
为满射。理由是其在 \(H\times H\) 中的像是等价关系：单位、逆元和乘法分别给出自反、对称、传递性；Grothendieck 拓扑斯中的等价关系均有效，所以此像正是商映射 \(q\) 的核对关系。

对于等变对象 \(\pi:E\to H\)，以下条件等价：

1. \(E\) 可在 \(Q\) 上实现。
2. 作用箭头 \((\gamma,e)\mapsto a_\gamma(e)\) 通过满射
   \[
   \underline\Gamma\times E\longrightarrow R\times_{H,\mathrm{pr}_1}E,\qquad
   (\gamma,e)\longmapsto(\pi(e),\gamma\pi(e),e)
   \]
   分解。
3. 对每个 profinite 测试空间 \(U\)、每个 \(e\in E(U)\) 和每个 \(\gamma\in\Gamma\)，
   \[
   \gamma\pi(e)=\pi(e)\quad\Longrightarrow\quad a_\gamma(e)=e.
   \tag{*}
   \]

第三项是一个**不预选 \(D\)** 的判据。要看它等价于第二项，比较两个在同一 \(e\) 上作用、且将 \(\pi(e)\) 送到同一截面的群元素；在测试空间的有限开闭分割上，它们均可取为常值，此时用 \(\delta^{-1}\gamma\) 应用 \((*)\)。层的分离性将局部等式拼成等式。

若第二项成立，分解出的 \(R\)-作用满足单位和组合律：可在上述满射上拉回检验，那里它们就是群作用律。它因此是沿 \(q\) 的下降数据。Grothendieck 拓扑斯中满射是有效下降态射，故存在 \(D\to Q\) 和所需等变同构。反向蕴涵直接成立，因为实现中的作用只改变 \(H\) 坐标。

更精确地，拉回函子
\[
q^*:\mathcal C/Q\longrightarrow
\{\Gamma\text{-等变对象 }E\to H\}
\]
全忠实，其本质像恰是满足 \((*)\) 的对象。因而两个可实现对象之间的每个等变态射唯一地从 \(Q\) 上的态射下降。对固定的可实现 \(E\)，考虑所有带指定同构
\[
\phi:E\xrightarrow{\sim}H\times_Q D
\]
的实现 \((D,\phi)\)：任意两个之间存在唯一一个与指定同构相容的同构。若不要求与指定同构相容，其底对象的自同构群对应 \(E\) 的等变自同构群。

现在任取 \(B\to Q\)，记
\[
H_B=H\times_Q B,\qquad q_B:H_B\to B.
\]
满射和上述核对关系都与拉回相容：
\[
H_B\times_B H_B\cong R\times_Q B,
\qquad
\underline\Gamma\times H_B\twoheadrightarrow H_B\times_B H_B.
\]
因此 \(B\) 是 \(H_B\) 的层商。完全相同的论证给出：

- \(q_B^*:\mathcal C/B\to\{\Gamma\text{-等变对象 }F\to H_B\}\) 全忠实；
- 其本质像由相应的全测试空间稳定子条件刻画；
- 实现及其态射按上述方式唯一下降。

对进一步的 \(B'\to B\)，这些构造由纤维积的结合律与拉回相容：\(H_{B'}\cong H_B\times_B B'\)，且 \(D\) 的实现拉回为 \(D\times_B B'\)。

## S4　单点上的检验

**结论：不一定可实现。**

取无限 profinite 空间 \(P=2^{\mathbb N}\)。定义 \(K\subseteq h_P\) 为有限像连续映射组成的子层：
\[
K(U)=\{f:U\to P:\operatorname{im}(f)\text{ 有限}\}.
\]
它是层，因为有限覆盖上有限像的并仍有限。

令 \(E\) 是两份 \(h_P\) 沿 \(K\) 的层推送出，并令 \(\Gamma=C_2\) 交换这两份。取 \(T=*\)，使 \(\Gamma\) 在 \(T\) 上平凡作用；于是 \(H=Q=\mathbf 1\)。

交换作用固定 \(E(*)\) 的每个元素。事实上，层推送出的任一全局截面局部来自某一份 \(h_P\)；取覆盖中一个非空测试空间及其一点，可将该全局截面表示为某个 \(p\in P\) 给出的截面。两份中的 \(p\) 都属于 \(K(*)\)，所以在推送出中被识别。

但交换作用在层上非平凡。两份中的 \(\operatorname{id}_P\in h_P(P)\) 在 \(E(P)\) 中不同：若它们在层化后相等，则在某有限覆盖上相等，因而各限制都有有限像；覆盖联合满射便迫使 \(\operatorname{id}_P\) 有有限像，与 \(P\) 无限矛盾。

因此题设单点条件成立，而 \(E\) 的作用非平凡。由于 \(H=Q=\mathbf1\)，可实现性要求作用平凡，故该 \(E\) 不可实现。

## S5　局部满射的基底检验

**结论：必可在 \(Q\) 上实现。**

由 S3，可实现性等价于作用箭头通过
\[
\underline\Gamma\times E\twoheadrightarrow
R\times_{H,\mathrm{pr}_1}E
\]
分解，也即作用箭头在这个满射的核对关系上相等。将这些箭头沿 \(B\to Q\) 拉回后，题设和 S3 表明所需等式成立。

由于 \(B\to Q\) 局部满射，它是层范畴中的满射；其任意拉回仍为满射。两个层态射若在满射上拉回后相等，则原来就相等。因此原核对关系上的等式成立，S3 给出 \(E\) 在 \(Q\) 上的实现。

## S6　非空基底与全局结论

**结论：不一定反映。** 非空可表示基底可能只看到 \(Q\) 的一部分。

取 \(\Gamma=C_2\) 平凡作用于离散有限空间 \(T=\{0,1\}\)。此时 \(Q=h_T\)。令有限 \(\Gamma\)-集合 \(X\to T\) 的纤维为：

- \(X_0\) 是一个点，作用平凡；
- \(X_1\) 是两个点，\(C_2\) 交换它们。

由 S2，\(E=h_X\to h_T\) 不可在 \(Q\) 上实现，因为 \(1\) 的稳定子在 \(X_1\) 上作用非平凡。取非空可表示层 \(B=h_*\)，以点 \(0\) 给出 \(B\to Q\)。拉回后只剩一个作用平凡的点，因此 \(E\times_Q B\) 可在 \(B\) 上实现。

由各阶段得到的检验原则是：

- 在任意情形，全体测试空间上的稳定子条件 \((*)\) 充要；仅检查 \(*\) 不充分。
- 若 \(\Gamma\) 在 \(T\) 上自由，所有等变对象都可实现；有限自由作用时，商就是可表示层 \(h_{T/\Gamma}\)。
- 沿局部满射 \(B\to Q\) 拉回后可实现，充要于原对象可实现；任意非空可表示基底不足以反映可实现性。