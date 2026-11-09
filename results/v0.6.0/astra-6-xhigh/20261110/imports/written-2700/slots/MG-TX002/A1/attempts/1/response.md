结论成立。可以利用“每一行、每一列被反链占用的频率”来证明。

对反链 \(A\)，定义
\[
r_i(A)=\mathbf 1_{\{A\text{ 中有第一坐标为 }i\text{ 的元素}\}},\qquad
c_j(A)=\mathbf 1_{\{A\text{ 中有第二坐标为 }j\text{ 的元素}\}}.
\]
由于反链在每一行、每一列至多有一个元素，
\[
|A|=\sum_{i=1}^a r_i(A)=\sum_{j=1}^b c_j(A).
\]

**关键是以下递推关系：**
\[
\begin{aligned}
r_i(R(A))&=r_{i-1}(A) &&(2\le i\le a),\\
r_1(R(A))&=1-c_b(A),\\
c_j(R(A))&=c_{j-1}(A) &&(2\le j\le b),\\
c_1(R(A))&=1-r_a(A).
\end{aligned}
\tag{1}
\]

我们先验证关于行的两个关系。令
\[
h_i=\max\bigl(\{j:(i,j)\in I(A)\}\cup\{0\}\bigr),
\qquad h_{a+1}=0.
\]
因为 \(I(A)\) 是序理想，
\[
b\ge h_1\ge h_2\ge\cdots\ge h_a\ge0.
\]
而 \(A\) 恰为 \(I(A)\) 的极大元集合，因此
\[
r_i(A)=1\quad\Longleftrightarrow\quad h_i>h_{i+1}.
\]

对于 \(i\ge2\)，第 \(i\) 行中唯一可能成为补集极小元的点是 \((i,h_i+1)\)；它确实是补集极小元，当且仅当 \(h_{i-1}>h_i\)。所以
\[
r_i(R(A))=\mathbf 1_{\{h_{i-1}>h_i\}}=r_{i-1}(A).
\]
第一行有补集极小元，当且仅当 \(h_1<b\)，也就是 \(A\) 没有第二坐标为 \(b\) 的元素。这证明了第二个关系。交换两个坐标，就得到关于列的两个关系，故 (1) 成立。

现在对给定轨道 \(O\)，记轨道平均为
\[
\langle f\rangle=\frac1{|O|}\sum_{A\in O}f(A).
\]
由于 \(R\) 置换 \(O\)，有 \(\langle f\circ R\rangle=\langle f\rangle\)。对 (1) 取平均可知，所有行的占用频率相同，所有列的占用频率也相同。记它们分别为 \(x,y\)，则
\[
\langle r_1\rangle=\cdots=\langle r_a\rangle=x,\qquad
\langle c_1\rangle=\cdots=\langle c_b\rangle=y,
\qquad x+y=1.
\]

设反链大小的轨道平均为 \(m\)。由按行和按列计数，
\[
m=ax=by.
\]
于是
\[
\frac{m}{a}+\frac{m}{b}=x+y=1,
\]
从而
\[
\boxed{\frac1{|O|}\sum_{A\in O}|A|=\frac{ab}{a+b}}.
\]
这对任意轨道 \(O\) 都成立。