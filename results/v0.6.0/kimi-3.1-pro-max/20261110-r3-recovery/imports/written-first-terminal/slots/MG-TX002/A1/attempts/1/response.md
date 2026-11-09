下面给出一个直接的“势函数＋轨道求和”证明。

设 \(O\) 是 \(R\) 的任意一条轨道。我们将构造整数值函数 \(\Phi\)，使得对每条反链 \(A\) 都有
\[
\Phi(R(A))-\Phi(A)=(a+b)|A|-ab.
\]
沿轨道求和后左端为零，从而立即得到结论。

### 1. 写出 \(R(A)\) 的坐标公式

将 \(A\) 唯一写成
\[
A=\{(x_1,y_1),\dots,(x_k,y_k)\},\qquad
x_1<\cdots<x_k,\quad y_1>\cdots>y_k .
\]
这里坐标严格单调是因为 \(A\) 是反链。再令
\[
x_0=0,\qquad y_{k+1}=0.
\]
空反链对应 \(k=0\)。

对固定的横坐标 \(s\)，定义
\[
h(s)=\max\bigl(\{0\}\cup\{y_r:s\le x_r\}\bigr).
\]
于是
\[
I(A)=\{(s,t)\in P:t\le h(s)\}.
\]
函数 \(h(s)\) 依次在区间
\[
x_{r-1}<s\le x_r\quad(1\le r\le k)
\]
上取值 \(y_r\)，并在 \(s>x_k\) 时取值 \(0=y_{k+1}\)。

从这条阶梯边界直接读出 \(P\setminus I(A)\) 的极小元：它们恰是落在 \(P\) 内的候选点
\[
(x_{r-1}+1,\ y_r+1),\qquad 1\le r\le k+1.
\]
因此
\[
R(A)=P\cap\{(x_{r-1}+1,y_r+1):1\le r\le k+1\}.
\]
特别地，\(A=\varnothing\) 时得到 \(R(A)=\{(1,1)\}\)。

在这些候选点中，\(2\le r\le k\) 的点必定属于 \(P\)。只有两个端点可能需要删去：定义
\[
\varepsilon=\mathbf 1_{\{k>0,\ y_1=b\}},\qquad
\eta=\mathbf 1_{\{k>0,\ x_k=a\}}.
\]
第一个候选点 \((1,y_1+1)\) 在且仅在 \(\varepsilon=1\) 时落到矩形外；最后一个候选点 \((x_k+1,1)\) 在且仅在 \(\eta=1\) 时落到矩形外。故若 \(B=R(A)\)，则
\[
|B|=k+1-\varepsilon-\eta. \tag{1}
\]

### 2. 计算坐标和的变化

记
\[
X(A)=\sum_{(i,j)\in A}i,\qquad
Y(A)=\sum_{(i,j)\in A}j,
\]
空集时两者均为 \(0\)。

所有候选点的横坐标之和为
\[
\sum_{r=1}^{k+1}(x_{r-1}+1)=X(A)+k+1.
\]
删去第一个候选点时横坐标减少 \(1\)，删去最后一个时减少 \(a+1\)，所以
\[
X(B)=X(A)+k+1-\varepsilon-(a+1)\eta. \tag{2}
\]
同理，
\[
Y(B)=Y(A)+k+1-(b+1)\varepsilon-\eta. \tag{3}
\]

现在定义
\[
\boxed{\Phi(A)=bX(A)+aY(A)-(a+b+ab)|A|.}
\]
令 \(D=a+b+ab\)。由 (1)–(3)，
\[
\begin{aligned}
\Phi(B)-\Phi(A)
={}&b\bigl(k+1-\varepsilon-(a+1)\eta\bigr)\\
&+a\bigl(k+1-(b+1)\varepsilon-\eta\bigr)
-D(1-\varepsilon-\eta).
\end{aligned}
\]
注意到
\[
b+a(b+1)=D,\qquad b(a+1)+a=D,
\]
所以所有含 \(\varepsilon,\eta\) 的项恰好抵消，得到
\[
\Phi(B)-\Phi(A)
=(a+b)(k+1)-D
=(a+b)k-ab.
\]
即对任意反链 \(A\)，
\[
\boxed{\Phi(R(A))-\Phi(A)=(a+b)|A|-ab.} \tag{4}
\]

### 3. 沿轨道求和

因为 \(R\) 把轨道 \(O\) 双射到自身，
\[
\sum_{A\in O}\Phi(R(A))=\sum_{A\in O}\Phi(A).
\]
将 (4) 对所有 \(A\in O\) 求和，左端于是为零，故
\[
0=(a+b)\sum_{A\in O}|A|-ab\,|O|.
\]
最终得到
\[
\boxed{\frac1{|O|}\sum_{A\in O}|A|=\frac{ab}{a+b}.}
\]
这正好证明了所述每条轨道上的反链大小平均值都相同。