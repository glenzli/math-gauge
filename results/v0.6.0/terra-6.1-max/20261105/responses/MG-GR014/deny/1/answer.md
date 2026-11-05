KEEP

已逐项核查：S1、S2 的维数与计数由 \(W\subseteq W+U_A\) 的秩及纤维维数得到；S3 使用的是有限离散域的乘积紧性；S4 的整体解和纤维由线性泛函延拓得到，无限维时使用的是商空间的代数对偶；S5 的 \(x_j=1\) 确实给出所需反例。

重点断言 S6 **成立**。令 \(V=k^{(I)}\)、\(W=\operatorname{span}\{a_j\}\)。有限可解性保证
\[
\lambda\!\left(\sum_{j\in F}t_ja_j\right)=\sum_{j\in F}t_jb_j
\]
是 \(W\) 上良定义的线性泛函。对任意 \(A\subseteq I\)，原答卷的像公式为
\[
\pi_A(\mathcal S)
=\bigcap_{v\in W\cap U_A}
\left\{y\in k^A:\sum_{i\in A}v(i)y_i=\lambda(v)\right\}.
\]
必要性直接成立；充分性则因为满足右侧条件时，\(\lambda\) 与 \(y\) 在 \(W\cap U_A\) 上一致，故可拼接为 \(W+U_A\) 上的泛函，再由基延拓到 \(V\)，得到整体解。

每个 \(v\) 只有有限支撑，因此右侧各集合都是有限坐标决定的闭集，其交也闭。这一论证不依赖无限离散域的紧性。