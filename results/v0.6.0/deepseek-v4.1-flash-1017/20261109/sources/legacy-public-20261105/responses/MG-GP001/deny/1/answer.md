FULL

经核查，上一版的主要数学结论可以保留，但有两处必须修正并补全：  
1. S2 中“映射锥的同伦等价”应明确陈述为同伦附着映射给出同伦等价，并说明其适用条件；  
2. S3、S4 中的 \(L*\{v,w\}\) 记号容易误解。若 \(\{v,w\}\) 是一条边，则 \(L*\{v,w\}\) 是锥，\(X\) 会可缩，不能实现一般的 \(\Sigma|L|\)。正确构造必须把 \(S^0=\{v,w\}\) 取为**两个互不相连的顶点**组成的复形。下面全部明确写出。

---

## S1 可缩子复形的商

**结论：** 若 \(Y\) 为有限 CW 复形，\(A\subset Y\) 是非空可缩子复形，则商映射
\[
q:Y\longrightarrow Y/A
\]
是同伦等价。

**证明：**

取 \(a_0\in A\) 以及同伦
\[
H:A\times I\to A,\qquad H_0=\mathrm{id}_A,\qquad H_1\equiv a_0.
\]
因为 \((Y,A)\) 是 CW 对，所以它具有同伦延拓性质。因此恒等映射
\[
Y\times\{0\}\to Y
\]
与 \(H:A\times I\to A\subset Y\) 可拼成
\[
Y\times\{0\}\cup A\times I\longrightarrow Y
\]
并延拓为
\[
\widetilde H:Y\times I\to Y,
\qquad 
\widetilde H_0=\mathrm{id}_Y,
\qquad 
\widetilde H_t|_A=H_t.
\]
令
\[
f=\widetilde H_1:Y\to Y.
\]
则 \(f\simeq \mathrm{id}_Y\)，且
\[
f(A)=H_1(A)=\{a_0\}.
\]
于是 \(f\) 通过商映射 \(q\) 分解：存在连续映射
\[
s:Y/A\to Y,
\qquad 
s([A])=a_0,\quad s([y])=f(y)\quad(y\notin A),
\]
使得
\[
f=s\circ q.
\]
所以
\[
s\circ q=f\simeq \mathrm{id}_Y.
\]

还需证明 \(q\circ s\simeq \mathrm{id}_{Y/A}\)。对每个 \(t\in I\)，由于
\[
\widetilde H_t(A)=H_t(A)\subset A,
\]
映射 \(q\circ \widetilde H_t:Y\to Y/A\) 在 \(A\) 上为常值，因此下降为连续映射
\[
\overline H_t:Y/A\to Y/A,
\qquad 
q\circ \widetilde H_t=\overline H_t\circ q.
\]
这些映射关于 \(t\) 连续：因为 \(q\times \mathrm{id}_I:Y\times I\to (Y/A)\times I\) 是商映射，而 \(q\circ\widetilde H\) 在其每个纤维上为常值。于是得到同伦
\[
\overline H:\frac YA\times I\to \frac YA.
\]
当 \(t=0\) 时，\(\overline H_0=\mathrm{id}_{Y/A}\)。当 \(t=1\) 时，
\[
\overline H_1\circ q
=q\circ f
=q\circ s\circ q
=(q\circ s)\circ q.
\]
由于 \(q\) 满射，得到
\[
\overline H_1=q\circ s.
\]
因此
\[
\mathrm{id}_{Y/A}\simeq q\circ s.
\]
故 \(q\) 与 \(s\) 互为同伦逆，\(q\) 是同伦等价。关键点是：所选取的 \(A\) 的收缩同伦始终落在 \(A\) 内，所以商映射在每个时刻都把该同伦压成常值，因而同伦可以下降到 \(Y/A\)。\(\square\)

---

## S2 非可缩底空间上的锥附着

**结论：** 若 \(D\) 为路径连通有限 CW 复形，\(L\neq\varnothing\) 为有限子复形，包含映射 \(i:L\hookrightarrow D\) 零伦，则
\[
Y=D\cup_L CL\simeq D\vee \Sigma L,
\]
其中 \(\Sigma L\) 为未约化悬挂。楔点取为零伦的常值终点 \(d_0\in D\) 与 \(\Sigma L\) 的底锥点 \([L\times\{0\}]\)。

**证明：**

先陈述一个标准事实。

**引理.** 若 \(f,g:L\to D\) 同伦，则它们的映射锥 \(C_f,C_g\) 同伦等价，且可取得在 \(D\) 上为恒等。

证明如下。记
\[
C_f=(D\sqcup L\times I)/\sim_f,
\qquad 
(l,0)\sim f(l),\quad (l,1)\sim *,
\]
并类似定义 \(C_g\)。取同伦
\[
H:L\times I\to D,\qquad H_0=f,\quad H_1=g.
\]
定义
\[
\Phi:C_f\to C_g,\qquad 
\Phi|_D=\mathrm{id}_D,
\]
并且在锥参数上
\[
\Phi(l,t)=
\begin{cases}
H(l,2t),&0\le t\le \frac12,\\[2mm]
(l,2t-1),& \frac12\le t\le 1,
\end{cases}
\]
其中第二行表示 \(C_g\) 中的锥点。由于
\[
H(l,1)=g(l)=(l,0)\quad\text{在 }C_g\text{ 中},
\]
端点相容，故 \(\Phi\) 连续。类似定义
\[
\Psi:C_g\to C_f,\qquad 
\Psi|_D=\mathrm{id}_D,
\]
\[
\Psi(l,t)=
\begin{cases}
H(l,1-2t),&0\le t\le \frac12,\\[2mm]
(l,2t-1),& \frac12\le t\le 1,
\end{cases}
\]
其中第二行表示 \(C_f\) 中的锥点。直接代入可知，在锥参数上 \(\Psi\circ\Phi\) 先沿 \(H(l,\cdot)\) 从 \(f(l)\) 走到 \(g(l)\)，再沿反向走回 \(f(l)\)，然后沿锥生成元走到锥顶。闭路
\[
H(l,\cdot)\,H(l,\cdot)^{-1}
\]
在 \(D\) 中相对端点零伦，且该零伦可关于 \(l\) 连续选取；消去该闭路后再重新参数化最后一段锥生成元，即得
\[
\Psi\circ\Phi\simeq \mathrm{id}_{C_f}\quad(\text{相对 }D).
\]
同理
\[
\Phi\circ\Psi\simeq \mathrm{id}_{C_g}\quad(\text{相对 }D).
\]
故引理成立。

现在令 \(c:L\to D\) 为常值映射 \(c(l)=d_0\)，其中 \(d_0\) 是零伦 \(i\simeq c\) 的常值终点。题中
\[
Y=D\cup_i CL
\]
正是 \(i\) 的映射锥 \(C_i\)。由引理，
\[
C_i\simeq C_c.
\]
在 \(C_c\) 中，所有 \((l,0)\) 都被粘到 \(d_0\)，所有 \((l,1)\) 都被粘到锥顶。因此锥部分为
\[
\frac{CL}{L}
=
\frac{L\times I}{L\times\{0\}\cup L\times\{1\}}
\cong \Sigma L.
\]
它与 \(D\) 只交于一点 \(d_0\)。所以
\[
C_c\cong D\vee \Sigma L.
\]
因此
\[
Y\simeq D\vee \Sigma L.
\]
楔点即
\[
d_0\in D
\quad\text{与}\quad
[L\times\{0\}]\in \Sigma L
\]
粘合所得之点。由于 \(D\) 路径连通，零伦的常值终点可以在差一个同伦的意义下任意选取。\(\square\)

---

## S3 整数扭结的实例

取 \(RP^2\) 的任一有限单纯三角剖分 \(L\)。令
\[
S^0=\{v,w\}
\]
为**两个互不相连顶点**组成的复形，即 \(\{v,w\}\notin S^0\)。令
\[
K=L*S^0.
\]
于是 \(K\) 的单形恰为
\[
\sigma,\qquad \sigma\cup\{v\},\qquad \sigma\cup\{w\},
\qquad \sigma\in L,
\]
且不含 \(\sigma\cup\{v,w\}\)。因此
\[
|K|\cong \Sigma |L|\cong \Sigma RP^2.
\]
取 \(L\) 的一个顶点 \(u\)，令
\[
B=\{v,u\}^{(\le 0)}\cup\{\{v,u\}\}
\]
即由顶点 \(v,u\) 和边 \(\{v,u\}\) 组成的子复形。下面验证全部要求。

1. \(|K|\setminus\{v\}\) 非空可缩。  
   去掉 \(v\) 后，
   \[
   |K|\setminus\{v\}\cong |L*\{w\}|\cong C|L|,
   \]
   即 \(L\) 上的锥，故非空可缩。

2. \((|B|\setminus\{v\})\to |B|\) 是同伦等价。  
   \(|B|\) 是一条闭区间；\(|B|\setminus\{v\}\) 是一条半开区间，二者均非空可缩。因此包含映射是同伦等价。

3. \(|K|\) 的约化有理同调全为零。  
   对任意非空空间 \(X\)，有悬挂同构
   \[
   \widetilde H_n(\Sigma X;\mathbb Q)
   \cong
   \widetilde H_{n-1}(X;\mathbb Q),
   \qquad n\ge 1.
   \]
   而
   \[
   H_1(RP^2;\mathbb Q)=0,
   \qquad
   H_2(RP^2;\mathbb Q)=0,
   \]
   因为 \(H_1(RP^2;\mathbb Z)=\mathbb Z/2\)，且 \(H_2(RP^2;\mathbb Z)=0\)。故
   \[
   \widetilde H_*(|K|;\mathbb Q)=0.
   \]

4. \(|K|\) 不可缩。  
   由悬挂同构，
   \[
   H_2(|K|;\mathbb Z)
   \cong
   H_1(RP^2;\mathbb Z)
   \cong \mathbb Z/2\neq 0.
   \]
   因此 \(|K|\) 不可缩。\(\square\)

---

## S4 整体对象与全部恢复目标

设
\[
X=|K|,\qquad O=X\setminus\{v\},\qquad C=|B|,
\]
且 \(O\) 非空可缩，包含映射
\[
O\cap C\longrightarrow C
\]
是同伦等价。

令
\[
L=\operatorname{link}_K(v)
=
\{\sigma\subseteq V(K)\setminus\{v\}:\sigma\cup\{v\}\in K\}.
\]
记 \(K_{\neq v}\) 为 \(K\) 中不含顶点 \(v\) 的所有单形组成的子复形，并令
\[
D=|K_{\neq v}|.
\]
令
\[
A=|v*L|.
\]
则 \(A\) 是 \(v\) 的闭星，且
\[
A\cong CL,
\qquad 
X=D\cup_L A,
\qquad 
D\cap A=L.
\]

### 4.1 \(B\) 的条件排除孤立顶点

首先证明 \(v\) 在 \(K\) 中不孤立，即 \(L\neq\varnothing\)。

若 \(v\) 孤立，则
\[
K=\{v\}\cup K',
\]
其中 \(K'\) 不含 \(v\)，且不含任何与 \(v\) 相连的单形。因 \(B\subseteq K\) 含 \(v\)，故
\[
B=\{v\}\cup B'
\]
且
\[
C=\{v\}\sqcup C',
\qquad 
C'=|B'|,
\]
并且
\[
O\cap C=C'.
\]
若 \(C'=\varnothing\)，则 \(C'=\{v\}\) 到 \(C\) 的包含映射没有同伦逆，因为空集到单点集不存在反向连续映射。若 \(C'\neq\varnothing\)，则 \(\pi_0(C)\) 比 \(\pi_0(C')\) 多出一个孤立点分量 \(\{v\}\)，故
\[
\pi_0(C')\to\pi_0(C)
\]
不可能为双射。无论如何都与 \(C'\to C\) 是同伦等价矛盾。因此 \(v\) 不孤立，从而
\[
L\neq\varnothing.
\]

### 4.2 \(O\simeq D\) 与 \(D\) 可缩

在闭星 \(A=CL\) 中，去掉锥顶 \(v\) 后，
\[
A\setminus\{v\}\cong L\times[0,1),
\]
它沿锥参数形变收缩到 \(L\)。另一方面 \(D\) 固定不动。因此
\[
O=X\setminus\{v\}
=D\cup(A\setminus\{v\})
\]
强形变收缩到 \(D\)。于是
\[
O\simeq D.
\]
由 \(O\) 可缩，得到
\[
D\text{ 可缩}.
\]
又因 \(L\neq\varnothing\)，有 \(L\subseteq D\)，故 \(D\neq\varnothing\)。

### 4.3 分类定理

由
\[
X=D\cup_L CL
\]
以及 \(D\) 可缩，包含映射 \(L\to D\) 零伦。应用 S2，得到
\[
X\simeq D\vee\Sigma L.
\]
由于 \(D\) 是非空可缩有限 CW 复形，商映射
\[
D\vee\Sigma L\longrightarrow \Sigma L
\]
由 S1 是同伦等价。因此
\[
\boxed{X\simeq \Sigma L}
\]
其中
\[
L=\operatorname{link}_K(v)
\]
为非空有限单纯复形。

反过来，任意给定非空有限单纯复形 \(P\)，令
\[
S^0=\{v,w\}
\]
为两个互不相连顶点组成的复形，并令
\[
K=P*S^0.
\]
取 \(P\) 的任一顶点 \(u\)，令
\[
B=\{\{u\},\{v\},\{u,v\}\},
\]
即边 \(vu\) 及其面组成的子复形。则：

1. \(v\) 的 link 为
   \[
   \operatorname{link}_K(v)=P.
   \]

2. 去掉 \(v\) 后，
   \[
   X\setminus\{v\}\cong |P*\{w\}|\cong C|P|,
   \]
   非空可缩。

3. \(C=|B|\cong [0,1]\)，而
   \[
   O\cap C=C\setminus\{v\}
   \]
   是半开区间，非空可缩。故包含映射
   \[
   O\cap C\longrightarrow C
   \]
   是同伦等价。

4. 此时
   \[
   X=|P*S^0|\cong \Sigma |P|.
   \]

因此所有可能的同伦类型恰为
\[
\boxed{
X\simeq \Sigma |P|,
\qquad P\text{ 为非空有限单纯复形}.
}
\]

### 4.4 \(X\) 可缩的有限判据

在题设假设下，
\[
\boxed{
X\simeq *
\iff
\operatorname{link}_K(v)\text{ 连通，且 }
\widetilde H_i\bigl(|\operatorname{link}_K(v)|;\mathbb Z\bigr)=0
\quad\text{对所有 }i.
}
\]
等价地，记 \(L=\operatorname{link}_K(v)\)，则
\[
X\simeq *
\iff
L\neq\varnothing,\quad
L\text{ 连通},\quad
\widetilde H_*(|L|;\mathbb Z)=0.
\]
在题设中 \(L\neq\varnothing\) 已自动成立。

**证明：**

由 4.3，
\[
X\simeq\Sigma L.
\]

若 \(L\) 连通且所有约化整同调为零，则 \(\Sigma L\) 单连通。事实上，悬挂由两个锥沿底 \(L\) 粘成，两个锥均可缩，且交叠部分同伦等价于连通的 \(L\)，由 van Kampen 定理得
\[
\pi_1(\Sigma L)=1.
\]
另一方面，由悬挂同构，
\[
\widetilde H_n(\Sigma L;\mathbb Z)
\cong
\widetilde H_{n-1}(L;\mathbb Z)=0,
\qquad n\ge1.
\]
因此 \(\Sigma L\) 是单连通有限 CW 复形且所有约化同调为零。由 Hurewicz 定理与 Whitehead 定理，所有同伦群为零，故 \(\Sigma L\) 可缩。于是 \(X\) 可缩。

反过来，若 \(X\simeq *\)，则 \(\Sigma L\) 可缩。由
\[
H_1(\Sigma L;\mathbb Z)
\cong
\widetilde H_0(L;\mathbb Z)
\]
得 \(\widetilde H_0(L)=0\)，故非空复形 \(L\) 连通。对 \(n\ge2\)，由
\[
0=H_n(\Sigma L;\mathbb Z)
\cong
\widetilde H_{n-1}(L;\mathbb Z)
\]
得 \(L\) 的所有正次数约化整同调为零。证毕。\(\square\)

**如何只用含 \(v\) 的单形及其面关系检验：**

含 \(v\) 的单纯数据可写成
\[
\mathcal T
=
\{\sigma\in K:\ v\in\sigma,\ \sigma\neq\{v\}\}.
\]
由它构造
\[
L_k
=
\{\sigma\setminus\{v\}:\ \sigma\in\mathcal T,\ |\sigma|=k+2\}.
\]
这里 \(L_k\) 就是 \(\operatorname{link}_K(v)\) 的 \(k\)-单形集合。其面关系为
\[
\tau\subseteq\sigma
\quad\text{在 }L\text{ 中}
\iff
\tau\cup\{v\}\subseteq\sigma\cup\{v\}
\quad\text{在 }K\text{ 中}.
\]
于是可以：

1. 由 \(L_0,L_1\) 构造图，检验 \(L\) 是否连通；
2. 用这些有限单形及面关系构造整数单纯链复形
   \[
   C_k(L;\mathbb Z)=\mathbb Z^{L_k},
   \qquad
   \partial_k:C_k(L;\mathbb Z)\to C_{k-1}(L;\mathbb Z),
   \]
   并用 Smith 标准形或秩计算检验
   \[
   H_0(L;\mathbb Z)\cong\mathbb Z,
   \qquad
   H_k(L;\mathbb Z)=0\quad(k\ge1).
   \]

这是完全由 \(K\) 中含 \(v\) 的单形及其面关系决定的有限判据。必须使用整同调；有理同调为零不够。S3 中 \(L=RP^2\) 正是反例：
\[
\widetilde H_*(RP^2;\mathbb Q)=0,
\qquad
H_1(RP^2;\mathbb Z)=\mathbb Z/2\neq0,
\]
故 \(\Sigma RP^2\) 不可缩。

---

## S5 不提供子复形 \(B\)

**结论：** \(|K|\) 不必同伦等价于非空有限复形的悬挂。若仅假设
\[
O=|K|\setminus\{v\}\text{ 非空可缩},
\]
则 \(X=|K|\) 的全部可能类型为
\[
\boxed{
\Sigma |P|,\quad P\text{ 为非空有限单纯复形},
\qquad\text{或}\qquad
S^0.
}
\]
新增类型恰为
\[
\boxed{S^0}.
\]

**证明：**

仍令
\[
L=\operatorname{link}_K(v),
\qquad 
D=|K_{\neq v}|.
\]

### 情形一：\(L\neq\varnothing\)

此时和 S4 中 4.2 一样，
\[
O\simeq D,
\]
故 \(D\) 非空可缩。并且
\[
X=D\cup_L CL.
\]
由 \(D\) 可缩，包含 \(L\to D\) 零伦。应用 S2 得
\[
X\simeq D\vee \Sigma L\simeq\Sigma L.
\]
由于 \(L\) 是非空有限单纯复形，这是一种悬挂型。

反过来，任意非空有限 \(P\) 都可由
\[
K=P*S^0
\]
实现，其中 \(S^0\) 为两个互不相连的顶点。取 \(v\) 为其中一个悬挂顶点，则
\[
|K|\setminus\{v\}\cong C|P|
\]
非空可缩，而
\[
|K|\simeq \Sigma |P|.
\]

### 情形二：\(L=\varnothing\)

此时 \(v\) 是 \(K\) 的孤立顶点，故
\[
X=\{v\}\sqcup O.
\]
由假设 \(O\) 非空可缩，于是
\[
X\simeq \{v\}\sqcup *
\cong S^0.
\]
反之，取 \(K\) 为两个孤立顶点 \(\{v,w\}\)，则
\[
O=\{w\}
\]
非空可缩，而
\[
|K|=S^0.
\]
所以 \(S^0\) 确实出现。

最后，\(S^0\) 不可能同伦等价于任何非空有限复形 \(P\) 的未约化悬挂 \(\Sigma|P|\)，因为非空 \(P\) 的未约化悬挂是路径连通的，而 \(S^0\) 不路径连通。因此新增类型恰为 \(S^0\)。\(\square\)

---

## S6 悬挂信息的逆向恢复

**结论：否。**  
存在非空有限单纯复形 \(L_1,L_2\)，使得
\[
\Sigma|L_1|\simeq \Sigma|L_2|,
\qquad
|L_1|\not\simeq |L_2|.
\]

**反例：**

取二元二十面体群
\[
2I=\langle s,t\mid (st)^2=s^3=t^5\rangle.
\]
它由 2 个生成元、2 个关系给出，且
\[
(2I)^{\mathrm{ab}}=0,
\qquad 
2I\neq 1.
\]
取该有限展示的展示 2-复形 \(M\)：它有一个 0-胞腔、两个 1-胞腔 \(s,t\)、两个 2-胞腔，分别沿
\[
(st)^2s^{-3},
\qquad 
s^3t^{-5}
\]
粘附。则
\[
\pi_1(M)\cong 2I\neq 1.
\]
在交换化后，两个关系对应的指数向量为
\[
(-1,2),\qquad (3,-5),
\]
其矩阵行列式为
\[
(-1)(-5)-2\cdot 3=5-6=-1.
\]
因此边界映射
\[
\partial_2:C_2(M;\mathbb Z)\to C_1(M;\mathbb Z)
\]
是整数可逆矩阵，故
\[
H_1(M;\mathbb Z)=0,
\qquad 
H_2(M;\mathbb Z)=0.
\]
又 \(M\) 连通，所以
\[
H_0(M;\mathbb Z)\cong\mathbb Z.
\]
更高同调为零。因此 \(M\) 是连通非循环，即
\[
\widetilde H_*(M;\mathbb Z)=0,
\]
但
\[
\pi_1(M)\neq 1,
\]
故 \(M\) 不可缩。

取 \(M\) 的一个有限单纯三角剖分，记作 \(L_2\)。令
\[
L_1=\Delta^0
\]
为单点复形。于是 \(L_1,L_2\) 都是非空有限单纯复形。

首先，
\[
\Sigma|L_1|\cong [0,1]\simeq *
\]
可缩。另一方面，\(L_2\) 连通且所有约化整同调为零，所以 \(\Sigma|L_2|\) 单连通；并且由悬挂同构，
\[
\widetilde H_n(\Sigma|L_2|;\mathbb Z)=0
\qquad(n\ge1).
\]
由 Hurewicz 定理与 Whitehead 定理，\(\Sigma|L_2|\) 可缩。因此
\[
\Sigma|L_1|\simeq *
\simeq
\Sigma|L_2|.
\]
但是
\[
|L_1|\simeq *
\not\simeq |L_2|,
\]
因为 \(|L_2|\) 的基本群为 \(2I\neq1\)。故悬挂不能逆向恢复底空间的同伦类型。\(\square\)

---

本题原题明确“无需 Lean”，且没有要求任何命名源码文件或声明对应表，因此本答卷不附额外代码文件。