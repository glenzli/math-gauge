固定一条轨道 \(O\)。我们先证明，沿这条轨道，每一行被反链占据的次数都相同，每一列也一样。

以第一坐标编号行。对反链 \(A\)，令 \(h_i\) 为 \(I(A)\) 在第 \(i\) 行的点数。由于 \(I(A)\) 向下封闭，这些点的第二坐标恰为 \(1,\ldots,h_i\)，且 \(h_1\ge\cdots\ge h_a\)。对 \(1\le i<a\)，有
\[
A\text{ 占据第 }i\text{ 行}
\quad\Longleftrightarrow\quad h_i>h_{i+1}
\quad\Longleftrightarrow\quad R(A)\text{ 占据第 }i+1\text{ 行}.
\]
第一个等价来自 \(A\) 恰为 \(I(A)\) 的极大元集合。第二个等价则是因为第 \(i+1\) 行中，补集的极小元只可能是 \((i+1,h_{i+1}+1)\)，而它恰在 \(h_i\ge h_{i+1}+1\) 时是极小元。交换两个坐标，列也满足同样的等价关系。

由于 \(R\) 在 \(O\) 上是双射，占据第 \(i\) 行的反链数就等于占据第 \(i+1\) 行的反链数。记每一行被占据的次数为 \(r\)，每一列被占据的次数为 \(c\)。两者由第一行的边界条件联系起来：
\[
R(A)\text{ 占据第 }1\text{ 行}
\quad\Longleftrightarrow\quad h_1<b
\quad\Longleftrightarrow\quad A\text{ 不占据第 }b\text{ 列}.
\]
沿轨道计数便得 \(r=|O|-c\)。

令 \(S=\sum_{A\in O}|A|\)。每条反链在每行、每列都至多有一个点，因此按行计数得 \(S=ar\)，按列计数得 \(S=bc\)。于是
\[
|O|=r+c=\frac Sa+\frac Sb,
\qquad\text{从而}\qquad
\boxed{\frac{1}{|O|}\sum_{A\in O}|A|=\frac{ab}{a+b}}.
\]