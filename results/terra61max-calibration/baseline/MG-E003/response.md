记
\[
R[B]=\{y\in X:\exists x\in B,\ R(x,y)\}.
\]
从 \(x\) 到 \(y\) 的长度 \(n\) 路径指 \(x=x_0,x_1,\ldots,x_n=y\)，且每步 \(R(x_k,x_{k+1})\)；长度零路径允许 \(x=y\)。定义
\[
\operatorname{cl}_R(A)=
\{y\in X:\exists a\in A,\ \exists n\in\mathbb N,\text{存在从 }a\text{ 到 }y\text{ 的长度 }n\text{ 路径}\}.
\]

**1. 最小传播封闭集。** 长度零路径说明 \(A\subseteq\operatorname{cl}_R(A)\)。若 \(x\) 已由 \(A\) 沿有限路径到达，且 \(R(x,y)\)，在路径末尾加一步就得到 \(y\in\operatorname{cl}_R(A)\)，故
\(R[\operatorname{cl}_R(A)]\subseteq\operatorname{cl}_R(A)\)。

若 \(C\subseteq X\) 包含 \(A\) 且 \(R[C]\subseteq C\)，则对路径长度归纳，路径中的每一点都属于 \(C\)，所以 \(\operatorname{cl}_R(A)\subseteq C\)。因此它恰为包含 \(A\) 的最小传播封闭集。这同时涵盖 \(A=\varnothing\) 和 \(X=\varnothing\)，此时不存在起点，闭包为空。

令 \(T_A(B)=A\cup R[B]\)。上述结果给出 \(T_A(\operatorname{cl}_R(A))\subseteq\operatorname{cl}_R(A)\)；反向包含也成立，因为任意有限路径长度为零时终点在 \(A\)，否则其倒数第二点在闭包内且最后一步来自 \(R\)。所以闭包是 \(T_A\) 的不动点；每个 \(T_A\) 的不动点都包含 \(A\) 且传播封闭，故它还是最小不动点。

**2. 随初始集合改变的规律。** 若 \(A\subseteq B\)，每条从 \(A\) 出发的路径也从 \(B\) 出发，故闭包单调。闭包自身传播封闭且包含 \(A\)，所以
\[
A\subseteq\operatorname{cl}_R(A),\qquad
\operatorname{cl}_R(\operatorname{cl}_R(A))=\operatorname{cl}_R(A).
\]
对于任意一族集合 \((A_t)_{t\in T}\)，
\[
\operatorname{cl}_R\Bigl(\bigcup_{t\in T}A_t\Bigr)
=\bigcup_{t\in T}\operatorname{cl}_R(A_t).
\]
因为任一见证路径只有一个起点，该起点属于并集当且仅当属于某个 \(A_t\)；空指标族时两边都是空集。

对于交集仅有
\[
\operatorname{cl}_R(A\cap B)\subseteq
\operatorname{cl}_R(A)\cap\operatorname{cl}_R(B),
\]
不一定相等。例如 \(X=\{a,b,c\}\)、\(R=\{(a,c),(b,c)\}\)、\(A=\{a\}\)、\(B=\{b\}\)。左侧为空，而右侧为 \(\{c\}\)。

**3. 封闭集格与可恢复的信息。** \(C\) 是传播封闭的，当且仅当 \(\operatorname{cl}_R(C)=C\)：一方向由最小性，另一方向由闭包本身传播封闭。任意一族传播封闭集的并与交仍传播封闭，因为其元素的每个后继保留相应的成员资格；这也包括空并 \(\varnothing\) 和空交 \(X\)。故这些集合在包含序下构成完备格，交为交、并为并。等价地，它们可作为某个拓扑的闭集；相应闭包正是 \(\operatorname{cl}_R\)。对每个传播封闭 \(C\)，
\[
\operatorname{cl}_R(A)\subseteq C\quad\Longleftrightarrow\quad A\subseteq C,
\]
即闭包是将任意子集送入这个封闭集格的最小扩张。

这些闭包精确记住有限可达关系 \(R^*\)：\(xR^*y\) 当且仅当 \(y\in\operatorname{cl}_R(\{x\})\)。因此所有单点闭包可恢复 \(R^*\)，但一般不能恢复原始边 \(R\)。例如在 \(X=\{0,1,2\}\) 上，\(R_1=\{(0,1),(1,2)\}\) 与 \(R_2=R_1\cup\{(0,2)\}\) 不同，却有相同的有限可达关系和相同闭包。

**4. 无限系统中的构造步数。** 令 \(A_0=A\)，\(A_{n+1}=A_n\cup R[A_n]\)。归纳可知 \(A_n\) 恰由长度至多 \(n\) 的路径到达的点组成，所以 \(\operatorname{cl}_R(A)=\bigcup_{n\ge0}A_n\)。无需无限长度路径，但不一定存在一个统一的有限停止步数：在 \(X=\mathbb N\)、\(R(n,n+1)\)、\(A=\{0\}\) 的例子中，\(A_n=\{0,1,\ldots,n\}\)，严格增长，而其并集是 \(\mathbb N\)。