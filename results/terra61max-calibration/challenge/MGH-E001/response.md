**存在唯一的最大允许关系。** 它是包含于观察等价关系 \(O\) 的最大双向匹配关系；由它得到的商在每个状态类上准确保留一步可到达的商类集合。

对任意二元关系 \(R\subseteq X\times X\)，定义 \(\Phi(R)\) 包含恰好那些满足 \(xOy\) 且同时满足下列条件的 \((x,y)\)：
\[
\begin{aligned}
&\forall x'\ (xTx'\Rightarrow\exists y'\ (yTy'\land x'Ry')),\\
&\forall y'\ (yTy'\Rightarrow\exists x'\ (xTx'\land x'Ry')).
\end{aligned}
\]
\(\Phi\) 单调：\(R\subseteq S\) 时，原来用于 \(R\) 的见证仍可用于 \(S\)。称 \(R\subseteq\Phi(R)\) 为后不动点。所有关系的集合 \(\mathcal P(X\times X)\) 是集合，故可以取全部后不动点的并，记为 \(B\)。若 \((x,y)\in B\)，它属于某个后不动点 \(R\)，所以属于 \(\Phi(R)\subseteq\Phi(B)\)。因此
\[
B\subseteq\Phi(B).
\]
由单调性，\(\Phi(B)\subseteq\Phi(\Phi(B))\)，故 \(\Phi(B)\) 自身也是后不动点，因而 \(\Phi(B)\subseteq B\)。所以 \(B=\Phi(B)\)。

接下来证明 \(B\) 是等价关系，而不仅是一个匹配关系。

- 恒等关系是后不动点：\(O\) 自反，每个转移可以用它自身匹配。故 \(B\) 自反。
- 若 \(R\) 是后不动点，则逆关系 \(R^{-1}\) 也是：\(O\) 对称，且两个方向的匹配条件互换。所以 \(B^{-1}\) 是后不动点，\(B^{-1}\subseteq B\)，即 \(B\) 对称。
- 若 \(R,S\) 是后不动点，则它们的复合 \(R\circ S=\{(x,z):\exists y,\ xRy\land ySz\}\) 也是。首先 \(xOy\) 且 \(yOz\) 推出 \(xOz\)。若 \(xTx'\)，先由 \(xRy\) 找到 \(yTy'\) 和 \(x'Ry'\)，再由 \(ySz\) 找到 \(zTz'\) 和 \(y'Sz'\)，得到 \(x'(R\circ S)z'\)；反方向同理。于是 \(B\circ B\subseteq B\)，即 \(B\) 传递。

由于 \(B\subseteq O\) 且 \(B\subseteq\Phi(B)\)，它是允许的等价关系。任何允许的等价关系都是后不动点，故都包含于 \(B\)。所以 \(B\) 是唯一的最大元；空集、空转移关系和任意分支度均包含在论证中。

**商保留的内容和普遍性质。** 设 \(q(x)=[x]_B\)，在 \(Q_B=X/B\) 上令
\[
q(x)\Rightarrow q(x')\quad\Longleftrightarrow\quad
\exists u,v\in X:\ q(u)=q(x),\ q(v)=q(x'),\ uTv.
\]
对任意 \(xBy\)，双向匹配恰好给出
\[
\{[x']_B:xTx'\}=\{[y']_B:yTy'\}.
\]
因此，从任何给定代表元 \(x\) 出发，商的一步后继集合正是 \(\{[x']_B:xTx'\}\)。观察也有良定义的商映射 \([x]_B\mapsto[x]_O\)。任何有限商路径都可从其起点类的任一给定代表元逐步提升为原空间中的有限路径；反过来原路径逐点取类自然给出商路径。商一般不保留原始后继的身份或个数：多个不同后继可能合并为同一商类。

若 \(E\) 是任何其他允许等价关系，\(E\subseteq B\) 给出唯一的满射
\[
\rho:X/E\to X/B,\qquad [x]_E\mapsto[x]_B,
\]
与原集合上的商映射交换，并保持观察和后继集合的像：
\(\rho(\operatorname{Succ}_E([x]_E))=\operatorname{Succ}_B([x]_B)\)。这表明 \(B\) 给出所有允许合并中的最粗商。

**通过超限细化构造。** 设 \(R_0=O\)，令
\[
R_{\alpha+1}=R_\alpha\cap\Phi(R_\alpha),\qquad
R_\lambda=\bigcap_{\alpha<\lambda}R_\alpha\quad(\lambda\text{ 为极限序数}).
\]
这些关系递减。它们也都是等价关系：当 \(R\) 是等价关系时，\(x\Phi(R)y\) 等价于 \(xOy\) 且
\(\{[x']_R:xTx'\}=\{[y']_R:yTy'\}\)，所以 \(\Phi(R)\) 是 \(O\) 与一个集合值函数的核关系之交；后继步及极限步均保持等价性。

细化必在某个集合序数处稳定。例如令 \(h\) 是不能注入 \(\mathcal P(X\times X)\) 的 Hartogs 序数；若每个 \(\alpha<h\) 都有 \(R_{\alpha+1}\ne R_\alpha\)，递减性使全部 \(R_\alpha\ (\alpha<h)\) 两两不同，便得到一个从 \(h\) 到 \(\mathcal P(X\times X)\) 的注入，矛盾。若 \(R_\kappa=R_{\kappa+1}\)，则 \(R_\kappa\subseteq\Phi(R_\kappa)\)，所以 \(R_\kappa\subseteq B\)。反过来，\(B\subseteq R_0\)，单调性和极限交通过超限归纳给出 \(B\subseteq R_\alpha\) 对所有阶段成立。因此稳定值恰为 \(B\)。

**有限层不一定足够。** 取互不相同的状态 \(p,q,z,h_0,h_1,\ldots\)，令 \(O\) 为全关系，转移恰为
\[
pTh_n\ (n\in\mathbb N),\quad pTz,\quad qTh_n\ (n\in\mathbb N),\quad
h_{n+1}Th_n,\quad zTz.
\]
归纳可得对有限 \(m,n\)，\(zR_mh_n\) 当且仅当 \(n\ge m\)：\(h_0\) 无后继，而其他 \(h_n\) 和 \(z\) 各有唯一后继。又对每个有限 \(m\)，有 \(pR_mq\)：在后继检验中，\(p\) 的 \(z\) 可由 \(q\) 的足够长有限链匹配，其余 \(h_n\) 互相匹配。因此 \(pR_\omega q\)。但 \(z\) 与任何 \(h_n\) 都不在 \(R_\omega\) 中，因为二者在 \(R_{n+1}\) 已不相关；所以 \(p\) 的后继 \(z\) 在 \(q\) 处无法用 \(R_\omega\) 匹配，\(p\) 与 \(q\) 在 \(R_{\omega+1}\) 被分开。这说明不能把所有有限层近似的交直接当成最终行为等价。这里证明的是一步集合及有限路径性质，未额外声称公平性或无需进一步选择原则的无限路径性质。