下面记 \(CX\) 为未约化锥，\(\Sigma X\) 为未约化悬挂，\(\simeq\) 表示同伦等价，\(\tilde H_*\) 为约化同调。所有复形均取通常几何实现。

---

## S1 可缩子复形的商

**结论：** \(q:Y\to Y/A\) 是同伦等价。

**证明：**

因 \(A\neq\varnothing\) 且可缩，取 \(a_0\in A\) 及同伦
\[
H:A\times I\to A,\qquad H_0=\mathrm{id}_A,\qquad H_1\equiv a_0.
\]
注意这个同伦始终落在 \(A\) 内。由于 \((Y,A)\) 是 CW 对，具有同伦延拓性质，故
\[
H:A\times I\to A\subset Y
\]
与 \(Y\times\{0\}\to Y\) 的恒等映射可一起延拓为
\[
\widetilde H:Y\times I\to Y,\qquad 
\widetilde H_0=\mathrm{id}_Y,\qquad 
\widetilde H_t|_A=H_t.
\]
令 \(f=\widetilde H_1\)。则 \(f\simeq\mathrm{id}_Y\)，且
\[
f(A)=\{a_0\}.
\]
因此 \(f\) 通过商映射 \(q:Y\to Y/A\) 分解：
\[
f=s\circ q,
\qquad 
s:Y/A\to Y,\quad s([A])=a_0.
\]
于是
\[
s\circ q=f\simeq \mathrm{id}_Y.
\]

还需证明 \(q\circ s\simeq \mathrm{id}_{Y/A}\)。对每个 \(t\)，因为
\[
\widetilde H_t(A)\subset A,
\]
所以
\[
q\circ \widetilde H_t:Y\to Y/A
\]
在 \(A\) 上是常值映射，因而通过 \(q\) 分解，即存在
\[
\overline H_t:Y/A\to Y/A
\]
使得
\[
q\circ\widetilde H_t=\overline H_t\circ q.
\]
当 \(t=0\) 时，\(\overline H_0=\mathrm{id}_{Y/A}\)；当 \(t=1\) 时，
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
故 \(\overline H_t\) 给出同伦
\[
\mathrm{id}_{Y/A}\simeq q\circ s.
\]
因此 \(q\) 与 \(s\) 互为同伦逆，\(q\) 是同伦等价。\(\square\)

关键点是：所选的收缩同伦始终在 \(A\) 内进行，所以商映射在每个时刻都把它压成常值，因而该同伦能够下降到 \(Y/A\)。

---

## S2 非可缩底空间上的锥附着

**结论：**
\[
Y=D\cup_L CL\simeq D\vee \Sigma L.
\]

**证明：**

记 \(I=[0,1]\)。将 \(Y\) 看作附着映射 \(i:L\hookrightarrow D\) 的映射锥：
\[
C_i
=
(D\sqcup L\times I)\big/\sim_i,
\qquad 
(l,0)\sim i(l),\quad (l,1)\sim *.
\]
于是 \(C_i\cong Y\)。

设包含 \(i:L\to D\) 零伦，取同伦
\[
H:L\times I\to D,\qquad H_0=i,\qquad H_1\equiv d_0
\]
其中 \(d_0\in D\)。若原来的常值终点不是 \(d_0\)，因 \(D\) 道路连通，可沿一条道路改接该零伦，故可不妨设常值终点为任意预先选定的 \(d_0\)。

再令 \(c:L\to D\) 为常值映射 \(c(l)=d_0\)，其映射锥记为 \(C_c\)，即
\[
C_c
=
(D\sqcup L\times I)\big/\sim_c,
\qquad 
(l,0)\sim d_0,\quad (l,1)\sim *.
\]
下面直接构造 \(C_i\) 与 \(C_c\) 的互逆同伦等价。

定义 \(u:C_i\to C_c\)：
\[
u|_D=\mathrm{id}_D,
\]
并且
\[
u(l,t)=
\begin{cases}
H(l,2t),&0\le t\le \frac12,\\[2mm]
(l,2t-1),&\frac12\le t\le 1,
\end{cases}
\]
其中第二行看作 \(C_c\) 中的点。端点相容性来自
\[
H(l,1)=d_0=(l,0)\quad\text{在 }C_c\text{ 中}.
\]

定义 \(v:C_c\to C_i\)：
\[
v|_D=\mathrm{id}_D,
\]
并且
\[
v(l,t)=
\begin{cases}
H(l,1-2t),&0\le t\le \frac12,\\[2mm]
(l,2t-1),&\frac12\le t\le 1,
\end{cases}
\]
其中第二行看作 \(C_i\) 中的点。端点相容性来自
\[
H(l,0)=i(l)=(l,0)\quad\text{在 }C_i\text{ 中}.
\]

考察复合 \(v\circ u\)。在 \(D\) 上它是恒等。在锥参数上，前 \(3/4\) 段形如
\[
H(l,r(t)),
\]
其中 \(r(t)\) 从 \(0\) 出发，经 \(1\)，再回到 \(0\)。这正是“一条道路再接其逆道路”，故它是基于 \(f(l)=i(l)\) 的零伦闭路；后 \(1/4\) 段是锥生成元的重新参数化。因此
\[
v\circ u\simeq \mathrm{id}_{C_i}\quad(\text{相对 }D).
\]
同理，\(u\circ v\) 在锥参数前 \(3/4\) 段给出基于 \(d_0\) 的零伦闭路，后 \(1/4\) 段为锥生成元的重新参数化，故
\[
u\circ v\simeq \mathrm{id}_{C_c}.
\]
因此
\[
C_i\simeq C_c.
\]

现在识别 \(C_c\)。在 \(C_c\) 中，全部 \((l,0)\) 被粘成 \(d_0\)，全部 \((l,1)\) 被粘成锥顶，因此锥部分正是
\[
CL/L
=
\frac{L\times[0,1]}{L\times\{0\}\cup L\times\{1\}}
\cong \Sigma L.
\]
它与 \(D\) 只交于一点 \(d_0\)。所以有同胚
\[
C_c\cong D\vee \Sigma L.
\]
因此
\[
Y=C_i\simeq D\vee \Sigma L.
\]

**楔点：** 在 \(D\vee\Sigma L\) 中取
\[
d_0\in D
\quad\text{与}\quad
[L\times\{0\}]\in \Sigma L
\]
为同一点。这里 \(d_0\) 是所选取的零伦的常值终点。由于 \(D\) 道路连通，这个选择在差一个同伦的意义下无关。\(\square\)

---

## S3 整数扭结的实例

取 \(RP^2\) 的任一有限单纯三角剖分 \(L\)。令
\[
K=L*\{v,w\}
\]
为 \(L\) 与两点 \(S^0\) 的单纯 join。则
\[
|K|\cong \Sigma |L|=\Sigma RP^2.
\]
其中 \(v,w\) 是悬挂的两个锥顶。

选取 \(L\) 的任意一个顶点 \(u\)，令
\[
B=\{v,u\}
\]
为 \(K\) 中的一条边。下面验证所有条件。

1. **\(|K|\setminus\{v\}\) 非空可缩。**
   \[
   |K|\setminus\{v\}\cong |L*\{w\}|,
   \]
   即以 \(w\) 为锥顶、以 \(L\) 为底的锥，故可缩且非空。

2. **\((|B|\setminus\{v\})\to |B|\) 是同伦等价。**
   这里 \(|B|\) 是一条闭区间，而 \(|B|\setminus\{v\}\) 是半开区间，二者均非空可缩。故包含映射是同伦等价。

3. **\(|K|\) 的约化有理同调全为零。**
   对任意非空空间 \(X\)，有悬挂同构
   \[
   \tilde H_n(\Sigma X;\mathbb Q)
   \cong
   \tilde H_{n-1}(X;\mathbb Q),\qquad n\ge 1.
   \]
   而
   \[
   H_*(RP^2;\mathbb Q)
   \]
   在正次数为零：因 \(H_1(RP^2;\mathbb Z)=\mathbb Z/2\)，张量 \(\mathbb Q\) 后消失；且 \(H_2(RP^2;\mathbb Z)=0\)。因此
   \[
   \tilde H_*(|K|;\mathbb Q)=0.
   \]

4. **\(|K|\) 不可缩。**
   由悬挂同构，
   \[
   H_2(|K|;\mathbb Z)
   \cong
   H_1(RP^2;\mathbb Z)
   \cong \mathbb Z/2\neq 0.
   \]
   故 \(|K|\) 不可能是可缩空间。\(\square\)

---

## S4 整体对象与全部恢复目标

设
\[
X=|K|,\qquad O=X\setminus\{v\},\qquad C=|B|,
\]
并设 \(O\) 非空可缩，且
\[
O\cap C\longrightarrow C
\]
是同伦等价。

### 4.1 局部结构：link 分解

令
\[
L=\operatorname{link}_K(v)
=\{\sigma\subseteq V(K)\setminus\{v\}:\sigma\cup\{v\}\in K\}.
\]
令
\[
D=\bigl|\{\sigma\in K:v\notin\sigma\}\bigr|.
\]
则 \(D\) 是 \(X\) 中由不含 \(v\) 的单形组成的子复形，且闭星
\[
|v*L|\cong CL
\]
是 \(v\) 的闭星。于是有分解
\[
X=D\cup_{|L|}CL,
\qquad 
D\cap CL=|L|.
\]

去掉 \(v\) 后，
\[
CL\setminus\{v\}\cong |L|\times[0,1),
\]
它形变收缩到 \(|L|\)。因此
\[
O=X\setminus\{v\}
=D\cup_{|L|}(CL\setminus\{v\})
\]
形变收缩到 \(D\)。所以
\[
O\simeq D.
\]
由 \(O\) 可缩，得到
\[
D\text{ 可缩}.
\]
由于 \(v\) 非孤立时 \(L\neq\varnothing\)，此时 \(D\) 非空。

### 4.2 \(B\) 的条件推出 \(v\) 非孤立

若 \(v\) 在 \(K\) 中孤立，则 \(v\) 在 \(B\) 中也孤立，于是
\[
|B|=\{v\}\sqcup (|B|\setminus\{v\}).
\]
若 \(|B|\setminus\{v\}=\varnothing\)，则空集到单点集不可能是同伦等价。若其非空，则 \(\pi_0(|B|)\) 比 \(\pi_0(|B|\setminus\{v\})\) 多出一个孤立点分量；同伦等价必须诱导 \(\pi_0\) 上的双射，矛盾。因此 \(v\) 在 \(B\) 中不孤立，从而在 \(K\) 中不孤立。特别地，
\[
L\neq\varnothing.
\]

### 4.3 分类定理

由上面 \(D\) 可缩，包含映射
\[
|L|\to D
\]
零伦。对分解
\[
X=D\cup_{|L|}CL
\]
应用 S2，得
\[
X\simeq D\vee \Sigma |L|.
\]
又 \(D\) 可缩，故
\[
X\simeq \Sigma |L|.
\]
因此得到：

> **分类结论：** 在所有满足题设条件的 \((K,v,B)\) 中，\(X=|K|\) 的同伦类型必为
> \[
> \Sigma |L|,
> \]
> 其中 \(L=\operatorname{link}_K(v)\) 是某个非空有限单纯复形。反之，任意非空有限单纯复形 \(L\) 都可以实现。

**实现构造：** 给定非空有限单纯复形 \(L\)，令
\[
K=L*\{v,w\},
\]
即 \(L\) 与两点的 join。取 \(L\) 的任意顶点 \(u\)，令
\[
B=\{v,u\}.
\]
则：
\[
|K|\cong \Sigma |L|,
\]
\[
|K|\setminus\{v\}\cong |L*\{w\}|
\]
是可缩的；并且 \(|B|\) 是一条闭区间，\(|B|\setminus\{v\}\) 是半开区间，二者均可缩，故包含映射是同伦等价。因此该构造满足全部条件。

所以 \(X\) 的可能同伦类型恰好是
\[
\boxed{\ \Sigma |L|\quad (L\text{ 为非空有限单纯复形})\ }.
\]
注意 S6 表明不能进一步把 \(\Sigma|L|\) 的信息唯一还原成 \(L\) 的同伦型。

### 4.4 \(X\) 可缩的有限判据

令
\[
L=\operatorname{link}_K(v).
\]
则
\[
\boxed{
X\simeq *
\iff
L\text{ 连通，且 }
\tilde H_i(|L|;\mathbb Z)=0
\quad\text{对所有 }i.
}
\]
等价地，
\[
H_0(|L|;\mathbb Z)\cong\mathbb Z,
\qquad
H_i(|L|;\mathbb Z)=0\quad(i\ge 1).
\]

**证明：**

由 4.3，
\[
X\simeq \Sigma |L|.
\]
若 \(L\) 连通，则 \(\Sigma L\) 单连通：因为 \(\Sigma L\) 可写成两个锥沿 \(L\) 粘合，而每个锥可缩，van Kampen 定理给出 \(\pi_1(\Sigma L)=1\)。

又有悬挂同构
\[
\tilde H_n(\Sigma L;\mathbb Z)
\cong
\tilde H_{n-1}(L;\mathbb Z),
\qquad n\ge 1.
\]
若 \(L\) 连通且所有约化整同调为零，则 \(\Sigma L\) 单连通且所有约化同调为零。由 Whitehead 定理，\(\Sigma L\) 可缩。因此 \(X\) 可缩。

反过来，若 \(X\simeq *\)，则 \(\Sigma L\) 可缩，故
\[
0=H_1(\Sigma L;\mathbb Z)
\cong \tilde H_0(L;\mathbb Z).
\]
由于 \(L\) 非空，\(\tilde H_0(L)=0\) 等价于 \(L\) 连通。并且对 \(n\ge 2\)，
\[
0=H_n(\Sigma L;\mathbb Z)
\cong \tilde H_{n-1}(L;\mathbb Z),
\]
故 \(L\) 所有约化整同调为零。\(\square\)

**如何只用含 \(v\) 的单形及面关系检验：**

link 的组合描述为
\[
L_k
=
\{\sigma\subseteq V(K)\setminus\{v\}: 
|\sigma|=k+1,\ \sigma\cup\{v\}\in K\}.
\]
即 \(L\) 的每个 \(k\)-单形对应于 \(K\) 中含 \(v\) 的一个 \((k+1)\)-单形去掉 \(v\)。其面关系就是这些含 \(v\) 单形之间的面关系去掉 \(v\)。于是可以：

1. 由 \(L_0,L_1\) 构造图，检验 \(L\) 是否连通；
2. 由 \(L_k\) 上的整数单纯链复形
   \[
   C_k(L;\mathbb Z)=\mathbb Z^{L_k},
   \qquad
   \partial_k:C_k\to C_{k-1}
   \]
   计算其整同调；实践上用 Smith 标准形检查
   \[
   H_0(L;\mathbb Z)\cong\mathbb Z,
   \qquad
   H_k(L;\mathbb Z)=0\quad(k\ge1).
   \]

这是完全由 \(K\) 中含 \(v\) 的单形及其面关系决定的有限判据。注意必须用整同调；有理同调为零不够。S3 中 \(L=RP^2\) 有
\[
\tilde H_*(RP^2;\mathbb Q)=0,
\]
但
\[
H_1(RP^2;\mathbb Z)=\mathbb Z/2\neq0,
\]
所以对应的 \(X=\Sigma RP^2\) 不可缩。

---

## S5 不提供子复形 \(B\)

**结论：** \(|K|\) 不必同伦等价于非空有限复形的悬挂。新增的可能类型恰为
\[
\boxed{S^0}.
\]

**证明：**

仍令
\[
L=\operatorname{link}_K(v).
\]
分两种情况。

### 情形一：\(L\neq\varnothing\)，即 \(v\) 非孤立

此时与 S4 的 4.1–4.3 完全一样：由
\[
O=|K|\setminus\{v\}\simeq *
\]
可推出 \(D\) 可缩；再由分解
\[
|K|=D\cup_{|L|}CL
\]
和 S2，得到
\[
|K|\simeq \Sigma |L|.
\]
这是非空有限复形 \(L\) 的未约化悬挂。

### 情形二：\(L=\varnothing\)，即 \(v\) 孤立

此时
\[
|K|=\{v\}\sqcup O,
\qquad 
O=|K|\setminus\{v\}
\]
非空可缩。因此
\[
|K|\simeq \{v\}\sqcup *\cong S^0.
\]
这里 \(S^0\) 有两个点，不能同伦等价于非空复形的悬挂：任意非空 \(L\) 的未约化悬挂 \(\Sigma L\) 都是道路连通的，而 \(S^0\) 不道路连通。

反过来，两种类型都能实现：

- \(\Sigma|L|\)（\(L\neq\varnothing\)）：取 \(K=L*\{v,w\}\)，其中 \(v\) 是一个悬挂顶点。
- \(S^0\)：取 \(K\) 为两个孤立顶点，例如 \(K=\{\{v\},\{w\}\}\)；则 \(O=\{w\}\) 非空可缩，而 \(|K|=S^0\)。

因此分类为
\[
\boxed{
|K|\simeq \Sigma |L|\ (L\text{ 非空有限单纯复形})
\quad\text{或}\quad
|K|\simeq S^0.
}
\]
若约定空复形的未约化悬挂为 \(S^0\)，则可统一写成
\[
|K|\simeq \Sigma\,\operatorname{link}_K(v),
\]
其中允许 link 为空。

---

## S6 悬挂信息的逆向恢复

**结论：否。**
存在非空有限单纯复形 \(L_1,L_2\)，使得
\[
\Sigma |L_1|\simeq \Sigma |L_2|,
\qquad
|L_1|\not\simeq |L_2|.
\]

**反例：**

取一个有限、连通、整同调为一点但本身不可缩的单纯复形 \(A\)。例如，取二元二十面体群
\[
2I=\langle s,t\mid (st)^2=s^3=t^5\rangle
\]
的有限展示复形，再取它的有限单纯三角剖分。该复形满足：

- \(\pi_1\cong 2I\neq 1\)，故不可缩；
- 其 abelianization 为 \(0\)，故 \(H_1=0\)；
- 它有一个 \(0\)-胞腔、两个 \(1\)-胞腔、两个 \(2\)-胞腔，故
  \[
  \chi=1-2+2=1.
  \]
  由 \(H_0=\mathbb Z,\ H_1=0\)，Euler 示性数给出
  \[
  \operatorname{rank}H_2=0,
  \]
  所以 \(H_2=0\)。更高同调为零。

因此 \(A\) 是连通的 acyclic 复形，但不可缩。

令
\[
L_1=\Delta^0
\]
为单点复形，令
\[
L_2=A.
\]
未约化悬挂 \(\Sigma L_1\) 是闭区间，故可缩。另一方面，\(A\) 连通且所有约化整同调为零，所以 \(\Sigma A\) 单连通且所有约化同调为零；由 Whitehead 定理，\(\Sigma A\) 可缩。于是
\[
\Sigma |L_1|\simeq *
\simeq
\Sigma |L_2|.
\]
但
\[
|L_1|\simeq *
\not\simeq |L_2|,
\]
因为 \(A\) 的基本群非平凡。

若希望 \(L_1,L_2\) 都不可缩，也可取
\[
L_1'=S^1,
\qquad
L_2'=S^1\vee A.
\]
则
\[
\Sigma L_1'\simeq S^2,
\qquad
\Sigma L_2'
\simeq
\Sigma S^1\vee \Sigma A
\simeq S^2\vee *
\simeq S^2,
\]
但
\[
\pi_1(L_1')=\mathbb Z,
\qquad
\pi_1(L_2')\cong \mathbb Z * 2I,
\]
二者不同构，故 \(L_1'\not\simeq L_2'\)。

因此悬挂不能逆向恢复底空间的同伦型。\(\square\)