## S1

**商映射 \(q:Y\to Y/A\) 是同伦等价。**关键是先构造一个在整个同伦过程中都把 \(A\) 送入 \(A\) 的同伦。

取 \(A\) 的收缩同伦
\[
h:A\times I\longrightarrow A,\qquad h(a,0)=a,\quad h(a,1)=a_0
\]
其中 \(a_0\in A\)。由于子复形的包含 \(A\hookrightarrow Y\) 是余纤维化，同伦扩张性质给出
\[
H:Y\times I\longrightarrow Y
\]
使 \(H_0=\operatorname{id}_Y\)，且 \(H_t|_A=h_t\)。

\(H_1\) 在 \(A\) 上恒为 \(a_0\)，故存在连续映射
\[
g:Y/A\longrightarrow Y,\qquad gq=H_1.
\]
于是 \(gq\simeq\operatorname{id}_Y\)。

对每个 \(t\)，\(H_t(A)\subseteq A\)，所以 \(qH_t\) 在 \(A\) 上恒为商点。这使公式
\[
\overline H([y],t)=[H(y,t)]
\]
良定义。它也连续：有限 CW 复形 \(Y\) 紧 Hausdorff，\(A\) 是闭集，因此 \(q\times\operatorname{id}_I\) 是商映射，而 \(\overline H\circ(q\times\operatorname{id}_I)=q\circ H\)。因此
\[
\overline H_0=\operatorname{id}_{Y/A},\qquad
\overline H_1=qg.
\]
故 \(qg\simeq\operatorname{id}_{Y/A}\)，\(g\) 是 \(q\) 的同伦逆。

## S2

设包含 \(i:L\to D\) 零伦，并选定一个零伦
\[
F:L\times I\to D,\qquad F(-,0)=i,\quad F(-,1)=c
\]
其中 \(c\in D\)。由于 \(D\) 路径连通，也可通过把 \(F\) 与一条路径拼接，预先指定任意 \(c\in D\)。

锥底包含 \(L\hookrightarrow CL\) 是 CW 子复形包含，因而是余纤维化。附着映射的同伦不变性因此适用，给出
\[
D\cup_i CL\simeq D\cup_c CL.
\]
这里所用的标准结论是：若 \(A\hookrightarrow Z\) 是余纤维化，同伦的两个映射 \(f_0,f_1:A\to D\) 所构成的推出 \(D\cup_{f_0}Z\) 和 \(D\cup_{f_1}Z\) 同伦等价。证明可由同伦扩张性质将附着映射之间的同伦延拓到 \(Z\)，再用反向同伦构造逆映射。

在右侧，整个锥底 \(L\) 被识别为 \(c\)，因此
\[
D\cup_c CL\cong D\vee_c(CL/L)\cong D\vee_c\Sigma L.
\]
这里 \(\Sigma L\) 是**非约化悬挂**；取其一个悬挂端点为楔点，并将其与 \(c\) 识别。故
\[
\boxed{Y\simeq D\vee\Sigma L}.
\]

## S3

令 \(L\) 为题给的 \(\mathbb{RP}^2\) 的有限单纯三角剖分。取两个不属于 \(L\) 的新顶点 \(w,v\)，令
\[
K=(w*L)\cup(v*L).
\]
选 \(L\) 的任一顶点 \(u\)，令 \(B\) 是边 \(\{v,u\}\) 及其所有面组成的子复形。

删除 \(v\) 后，\(|K|\setminus\{v\}\) 变形收缩到锥 \(|w*L|\)，故非空可缩。\(|B|\) 是一条闭线段，\(|B|\setminus\{v\}\) 是非空半开线段，二者均可缩，所以其包含是同伦等价。

另一方面，\(|K|\) 是 \(|L|\) 的非约化悬挂。悬挂同调公式给出
\[
\widetilde H_n(|K|;\mathbb Q)
\cong \widetilde H_{n-1}(\mathbb{RP}^2;\mathbb Q)=0
\]
对所有 \(n\) 成立，但
\[
\widetilde H_2(|K|;\mathbb Z)
\cong H_1(\mathbb{RP}^2;\mathbb Z)
\cong\mathbb Z/2.
\]
因此 \(|K|\) 不可缩。

## S4

**所有可能的同伦类型恰为非空有限单纯复形的非约化悬挂：**
\[
\boxed{\quad X\simeq\Sigma|L|,\qquad L\text{ 为非空有限单纯复形}.\quad}
\]
下面证明必要性、实现构造和可缩性判据。

### 必要性

定义顶点删除和顶点链
\[
D=K\setminus v=\{\sigma\in K:v\notin\sigma\},\qquad
L=\operatorname{lk}_K(v)=\{\tau\in D:\tau\cup\{v\}\in K\}.
\]
于是
\[
K=D\cup(v*L),\qquad D\cap(v*L)=L.
\]

空间 \(O=|K|\setminus\{v\}\) 强变形收缩到 \(|D|\)。具体地，设 \(t_v(x)\) 为点 \(x\) 在顶点 \(v\) 处的重心坐标。对 \(x\ne v\)，删除 \(v\) 的坐标，再把其余坐标除以 \(1-t_v(x)\)，得到 \(r(x)\in|D|\)。线性同伦
\[
(1-s)x+s\,r(x)
\]
始终留在 \(O\) 中，并固定 \(|D|\)。因此 \(|D|\) 非空可缩。

还须证明 \(L\) 非空。若 \(L\) 为空，\(v\) 不属于任何正维单形，因而是 \(X\) 的孤立连通分支。由于 \(v\in B\)，它也是 \(C=|B|\) 的孤立连通分支，但 \(O\cap C\to C\) 的像不与该分支相交。这与同伦等价必须在路径分支上给出双射矛盾。

所以 \(L\) 非空。包含 \(|L|\to|D|\) 因目标可缩而零伦；对锥附着应用 S2，得到
\[
X=|D|\cup_{|L|}C|L|
\simeq |D|\vee\Sigma|L|
\simeq\Sigma|L|.
\]
最后一步使用 \(|D|\) 可缩：把 \(|D|\) 收缩到所选楔点，或应用 S1，均可得到该等价。

### 全部类型的实现

任取非空有限单纯复形 \(L\)，取两个新顶点 \(w,v\)，构造
\[
K=(w*L)\cup(v*L).
\]
选 \(u\in L\) 为一个顶点，令 \(B\) 为边 \(\{v,u\}\) 连同其所有面。

删除 \(v\) 后，\(|K|\setminus\{v\}\) 强变形收缩到锥 \(|w*L|\)，故非空可缩。\(C=|B|\) 和 \(O\cap C\) 分别是闭线段及其去掉一个端点所得的空间，均非空可缩；因此包含 \(O\cap C\to C\) 是同伦等价。同时
\[
|K|\cong\Sigma|L|.
\]
这实现了上述分类中的每一种类型。

### 只用顶点星关联数据的判据

从 \(K\) 中所有包含 \(v\) 的单形及其面，可恢复链 \(L=\operatorname{lk}_K(v)\)：一个不含 \(v\) 的单形 \(\tau\) 属于 \(L\)，当且仅当 \(\tau\cup\{v\}\in K\)。由其有限关联数据写出整数增广单纯链复形
\[
\cdots\longrightarrow C_1(L;\mathbb Z)
\longrightarrow C_0(L;\mathbb Z)
\xrightarrow{\ \varepsilon\ }\mathbb Z\longrightarrow0.
\]

在 S4 的假设下，充要条件是
\[
\boxed{\quad \widetilde H_i(L;\mathbb Z)=0
\quad\text{对所有 }i\ge 0.\quad}
\]
这些群可由上述有限整数边界矩阵计算，例如使用 Smith 标准形。

必要性由 \(X\simeq\Sigma|L|\) 和悬挂同调公式立即得到。反过来，若这些群全为零，则非空 \(L\) 满足 \(\widetilde H_0(L;\mathbb Z)=0\)，故 \(|L|\) 连通；有限单纯复形的连通分支是路径连通的。由 Seifert–van Kampen 定理，\(\Sigma|L|\) 单连通；由悬挂同调公式，它的约化整数同调全为零。单连通 CW 复形若约化整数同调全为零，则由 Hurewicz 定理和 Whitehead 定理可知它可缩。因此 \(X\) 可缩。

## S5

**不一定。**新增的唯一同伦类型是
\[
\boxed{S^0.}
\]
完整分类为 \(S^0\)，以及所有非空有限单纯复形的非约化悬挂。

使用 S4 中的删除 \(D\) 和链 \(L\)，同样有 \(|D|\) 非空可缩。

- 若 \(L\ne\varnothing\)，S2 给出
  \[
  |K|\simeq\Sigma|L|.
  \]
- 若 \(L=\varnothing\)，则 \(v\) 是孤立顶点，
  \[
  |K|=|D|\sqcup\{v\}\simeq S^0.
  \]

\(S^0\) 可由两个孤立顶点组成的复形实现：取其中一个为 \(v\)，删除后只剩一点。非空空间的非约化悬挂总是路径连通，故 \(S^0\) 不是此类悬挂。其他所有类型由 S4 的构造实现。

## S6

**不必推出。**取有限单纯复形 \(L_1,L_2\)，使
\[
|L_1|\cong T^2=S^1\times S^1,\qquad
|L_2|\cong S^1\vee S^1\vee S^2.
\]
环面及右侧楔和都可取有限单纯三角剖分。

这两个空间不同伦等价：环面的两个一次整数上同调生成元的杯积是 \(H^2(T^2;\mathbb Z)\) 的生成元；而在 \(S^1\vee S^1\vee S^2\) 中，任意两个一次上同调类的杯积都为零。同伦等价会保持上同调环，故它们不能同伦等价。

但它们的悬挂同伦等价。环面的标准 CW 结构由 \(S^1\vee S^1\) 沿交换子附着一个二维胞腔得到。悬挂后，附着映射成为
\[
S^2\longrightarrow S^2\vee S^2.
\]
它在二次同调上的两个次数都是零，因为原交换子在两条圆上的次数均为零。\(S^2\vee S^2\) 单连通，Hurewicz 定理给出
\[
\pi_2(S^2\vee S^2)\cong H_2(S^2\vee S^2;\mathbb Z),
\]
因此该悬挂附着映射零伦。于是
\[
\Sigma T^2\simeq S^2\vee S^2\vee S^3
\simeq\Sigma(S^1\vee S^1\vee S^2).
\]
这里计算使用了良基点 CW 复形的约化悬挂；对这些空间，约化悬挂与题中的非约化悬挂同伦等价。故两次悬挂同伦等价，却不能恢复原空间的同伦类型。