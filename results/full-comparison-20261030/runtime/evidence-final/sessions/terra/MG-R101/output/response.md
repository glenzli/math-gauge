令 \(D=A\cap B\)。由于 \(L=D+C\subseteq H\)，可以将 \(O\) 识别为 \(H/L\)。

对任意 \((x,y,z)\in P\)，先取
\[
s\in(x+A)\cap(y+B).
\]
这样的 \(s\) 存在：由 \(x-y\in A+B\)，可写 \(x-y=a-b\)，其中 \(a\in A\)、\(b\in B\)，于是可取 \(s=x-a=y-b\)。又因为
\[
s-z=(s-x)+(x-z)\in A+C,\qquad
s-z=(s-y)+(y-z)\in B+C,
\]
所以 \(s-z\in H\)。定义
\[
\boxed{\quad
\delta([(x,y,z)])=[s-z]_L\in O.
\quad}
\]

这个定义与选择无关。若 \(s'\) 是另一个可选元素，则 \(s'-s\in A\cap B\subseteq L\)。改变记录的代表元时，给 \(x,y,z\) 分别加上 \(A,B,C\) 中的元素，不改变前两个陪集 \(x+A,y+B\)，而 \(s-z\) 只改变一个 \(C\) 中的元素。因此 \(\delta\) 定义良好；对记录相加或作 \(R\) 的数乘时，可以相应地对所选的 \(s\) 作相同运算，故 \(\delta\) 是 \(R\)-线性映射。

对每个 \(h\in H\)，有 \((0,0,-h)\in P\)。取 \(s=0\) 即得
\[
\delta([(0,0,-h)])=[h]_L.
\]
因此 \(\delta\) 满射，并满足题目要求的规范化条件。

对角映射 \(j\) 的核由满足 \(t\in A\cap B\cap C=I\) 的元素给出，所以 \(j\) 单射。此外，
\[
j([t]_I)=[(x,y,z)]
\quad\Longleftrightarrow\quad
t-x\in A,\quad t-y\in B,\quad t-z\in C.
\]
若这样的 \(t\) 存在，取 \(s=t\) 可知 \(\delta([(x,y,z)])=0\)。

反过来，若 \(\delta([(x,y,z)])=0\)，则所选 \(s\) 满足
\[
s-z=d+c,\qquad d\in A\cap B,\quad c\in C.
\]
此时 \(t_0=s-d\) 满足
\[
t_0-x\in A,\qquad t_0-y\in B,\qquad t_0-z=c\in C,
\]
故 \(t_0\) 是原始实现。这证明了 \(\ker\delta=\operatorname{im}j\)，从而
\[
0\longrightarrow M/I\xrightarrow{j}Q\xrightarrow{\delta}O\longrightarrow0
\]
是短正合序列。

因此，**一条记录有原始实现当且仅当其在 \(\delta\) 下的像为零**。具体地，取任意 \(s\in(x+A)\cap(y+B)\)，条件就是
\[
s-z\in(A\cap B)+C.
\]
条件成立时，按上面的分解取 \(t_0=s-d\)，则它的全部原始实现恰为
\[
\boxed{\,t_0+I\,}.
\]