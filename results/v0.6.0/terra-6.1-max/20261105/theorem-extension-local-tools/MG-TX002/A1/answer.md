结论成立。关键是观察反链经过一次 \(R\) 后，哪些第一坐标和第二坐标会出现。

对反链 \(A\)，定义指示变量
\[
x_i(A)=\mathbf 1_{\{\text{\(A\) 中有元素的第一坐标为 }i\}},\qquad
y_j(A)=\mathbf 1_{\{\text{\(A\) 中有元素的第二坐标为 }j\}}.
\]
我们先证明以下关系：
\[
\begin{aligned}
x_{i+1}(R(A))&=x_i(A) &&(1\le i<a),\\
y_{j+1}(R(A))&=y_j(A) &&(1\le j<b),\\
x_1(R(A))&=1-y_b(A).
\end{aligned}
\tag{1}
\]

为此，令 \(h_i\) 为 \(I(A)\) 在第一坐标为 \(i\) 的那一行中的最大第二坐标；若该行为空，令 \(h_i=0\)。由于 \(I(A)\) 是下理想，
\[
b\ge h_1\ge h_2\ge\cdots\ge h_a\ge0.
\]
而且 \(A\) 恰好是 \(I(A)\) 的极大元素集合，所以对于 \(1\le i<a\)，
\[
x_i(A)=1\quad\Longleftrightarrow\quad h_i>h_{i+1}.
\]
另一方面，\(P\setminus I(A)\) 在第一坐标为 \(i+1\) 的那一行有极小元素，当且仅当 \(h_i>h_{i+1}\)。这证明了 (1) 的第一行；交换两个坐标便得到第二行。

最后，\(R(A)\) 在第一坐标为 \(1\) 的那一行有元素，当且仅当 \(h_1<b\)；而 \(h_1=b\) 当且仅当 \(A\) 有元素的第二坐标为 \(b\)。于是第三行也成立。

现在对轨道 \(O\) 取平均，记
\[
p_i=\frac1{|O|}\sum_{A\in O}x_i(A),\qquad
q_j=\frac1{|O|}\sum_{A\in O}y_j(A).
\]
由于 \(R\) 在 \(O\) 上置换元素，由 (1) 可知
\[
p_1=\cdots=p_a=:p,\qquad
q_1=\cdots=q_b=:q,\qquad p+q=1.
\]
反链中任意两个元素的第一坐标互不相同，第二坐标也互不相同。因此对每个 \(A\)，
\[
|A|=\sum_{i=1}^a x_i(A)=\sum_{j=1}^b y_j(A).
\]
取轨道平均得到
\[
\frac1{|O|}\sum_{A\in O}|A|=ap=bq.
\]
联立 \(p+q=1\)，得 \(p=b/(a+b)\)，从而
\[
\boxed{\frac1{|O|}\sum_{A\in O}|A|=\frac{ab}{a+b}}.
\]