以下均取通常几何实现；除特别说明外，同调取整系数。记 \(st_K(v)\) 为顶点 \(v\) 的开星，\(St_K(v)\) 为闭星，
\[
lk_K(v)=\{\sigma\in K:\ v\notin\sigma,\ \sigma\cup\{v\}\in K\}.
\]
\(\Sigma\) 表示非约化悬挂。

---

## S1 可缩子复形的商

**结论：** \(q:Y\to Y/A\) 是同伦等价。

**证明：** 因 \(A\neq\varnothing\) 可缩，取 \(a_0\in A\) 及同伦
\[
h_t:A\to A,\qquad h_0=\mathrm{id}_A,\qquad h_1(A)=\{a_0\}.
\]
由于 \((Y,A)\) 是 CW 对，具有同伦延拓性质，故 \(h_t\) 可延拓为
\[
H_t:Y\to Y,\qquad H_0=\mathrm{id}_Y,\qquad H_t|_A=h_t.
\]
于是 \(H_1(A)=\{a_0\}\)，故 \(H_1\) 经过商映射 \(q\) 分解：存在
\[
g:Y/A\to Y,\qquad g\circ q=H_1.
\]
因此
\[
g\circ q=H_1\simeq H_0=\mathrm{id}_Y.
\]

另一方面，考虑
\[
K_t=q\circ H_t:Y\to Y/A.
\]
因为 \(H_t(A)\subseteq A\)，所以 \(K_t(A)=\{*\}\) 对所有 \(t\) 成立，故 \(K_t\) 经过 \(q\) 分解为
\[
\overline K_t:Y/A\to Y/A,\qquad \overline K_t\circ q=K_t.
\]
于是
\[
\overline K_0=\mathrm{id}_{Y/A},\qquad 
\overline K_1=q\circ g.
\]
故
\[
q\circ g=\overline K_1\simeq \overline K_0=\mathrm{id}_{Y/A}.
\]
综上，\(q\) 有同伦逆 \(g\)，所以 \(q\) 是同伦等价。

**同伦下降到商的理由：** 关键在于 \(H_t(A)\subseteq A\)，因此商映射后 \(q\circ H_t\) 在整个 \(A\) 上恒为基点，故可从 \(Y\) 下降为 \(Y/A\) 上的同伦；而 \(H_1(A)\) 是一个点，故 \(H_1\) 本身也经过商分解，从而给出逆映射。

---

## S2 非可缩底空间上的锥附着

**结论：** 存在同伦等价
\[
Y=D\cup_L CL\;\simeq\; D\vee \Sigma L.
\]
楔点为 \(d_0\in D\) 与 \(\Sigma L=CL/L\) 中“被 collapse 的底 \(L\)”所对应的悬挂点。

**证明：** 记 \(i:L\hookrightarrow D\) 为包含。由假设存在零伦
\[
H:L\times I\to D,\qquad H_0=i,\qquad H_1(L)=\{d_0\}.
\]
因为 \(L\) 是有限 CW 复形 \(D\) 的子复形，\(i:L\to D\) 是余纤维化；同样 \(L\to CL\) 也是余纤维化。因此 \(Y\) 是如下图的同伦推出：
\[
D\longleftarrow L\longrightarrow CL.
\]

使用标准事实：**若余纤维化 \(i:A\to B\) 零伦，则其映射锥满足**
\[
B\cup_i CA\simeq B\vee\Sigma A.
\]
这里给出计算：在同伦推出中把 \(i\) 换成与它同伦的常值映射
\[
c:L\to D,\qquad c(l)=d_0.
\]
同伦推出只依赖映射的同伦类。将 \(c\) 分解为
\[
L\to \{d_0\}\to D.
\]
于是
\[
\operatorname{hocof}(c)
\simeq
D\cup^h_{\{d_0\}}
\left(\{d_0\}\cup^h_L CL\right).
\]
内层同伦推出为
\[
\{d_0\}\cup^h_L CL\simeq CL/L\cong \Sigma L,
\]
其中 \(CL/L\) 正是把锥的底 \(L\times\{0\}\) 与锥顶 \(L\times\{1\}\) 分别 collapse 后得到的非约化悬挂。再沿 \(\{d_0\}\to D\) 粘贴，得到
\[
D\cup^h_{\{d_0\}}\Sigma L\cong D\vee\Sigma L.
\]
故
\[
Y\simeq D\vee\Sigma L.
\]

**楔点说明：** 零伦 \(H\) 的终点为 \(d_0\)。在 \(\Sigma L=CL/L\) 中，被 collapse 的底 \(L\) 成为楔点；锥顶是另一个悬挂点。若换一个零伦终点 \(d_0'\)，因 \(D\) 道路连通，\(d_0,d_0'\) 之间有道路，所得两个楔在同伦意义下相同。

---

## S3 整数扭结的实例

取 \(L\) 为 \(\mathbb RP^2\) 的任一有限单纯三角剖分。设 \(S^0=\{a,b\}\) 为两个孤立顶点组成的零维复形，即不含边 \(\{a,b\}\)。令
\[
K:=L*S^0
\]
为单纯 join。等价地，\(K\) 的顶点为 \(V(L)\cup\{a,b\}\)，单形为所有
\[
\sigma,\quad \sigma\cup\{a\},\quad \sigma\cup\{b\}\qquad(\sigma\in L),
\]
但不含同时含有 \(a,b\) 的单形。

令
\[
v:=a.
\]
取 \(L\) 的任一顶点 \(w\)，令
\[
B:=\{a,w\}
\]
为边 \(aw\) 及其面组成的子复形。

验证：

1. \(|K|\cong \Sigma|L|=\Sigma\mathbb RP^2\)。去掉一个悬挂顶点 \(v=a\) 后，剩下的空间是另一个锥 \(L*\{b\}\) 再粘上一个开锥，形变收缩到 \(L*\{b\}\)，而 \(L*\{b\}\) 是 \(L\) 上的锥，可缩且非空。因此
   \[
   |K|\setminus\{v\}\text{ 非空可缩}.
   \]

2. \(C=|B|\cong[0,1]\)，且
   \[
   C\setminus\{v\}\cong(0,1],
   \]
   它与 \(C\) 都可缩，故包含映射
   \[
   |B|\setminus\{v\}\longrightarrow |B|
   \]
   是同伦等价。

3. 同调计算：
   \[
   \widetilde H_n(\Sigma\mathbb RP^2;\mathbb Q)
   \cong
   \widetilde H_{n-1}(\mathbb RP^2;\mathbb Q)=0
   \quad\text{对所有 }n.
   \]
   但
   \[
   \widetilde H_2(\Sigma\mathbb RP^2;\mathbb Z)
   \cong
   \widetilde H_1(\mathbb RP^2;\mathbb Z)
   \cong \mathbb Z/2\neq0.
   \]
   因此 \(|K|\) 约化有理同调全为零，但不可缩。

---

## S4 整体对象与全部恢复目标

### 4.1 关键引理：穿刺-悬挂引理

**引理.** 设 \(K\) 为有限单纯复形，\(v\) 为非孤立顶点，\(X=|K|\)。若
\[
X\setminus\{v\}
\]
非空可缩，则
\[
X\simeq \Sigma\,|lk_K(v)|.
\]

**证明：** 记
\[
St(v)=St_K(v),\qquad st(v)=st_K(v),\qquad Lk(v)=|lk_K(v)|.
\]
闭星 \(St(v)\) 是 \(Lk(v)\) 上的锥：
\[
St(v)\cong v*Lk(v),
\]
故可缩。令
\[
D:=X\setminus st(v).
\]
这是 \(K\) 的一个子复形，且
\[
D\cap St(v)=Lk(v).
\]
又
\[
X\setminus\{v\}
=
(St(v)\setminus\{v\})\cup D.
\]
而 \(St(v)\setminus\{v\}\) 是 \(Lk(v)\) 上的开锥，形变收缩到 \(Lk(v)\subset D\)。因此
\[
X\setminus\{v\}\simeq D.
\]
由假设 \(X\setminus\{v\}\) 可缩，得 \(D\) 可缩。

于是
\[
X=D\cup St(v)
\]
是两个可缩子复形沿
\[
D\cap St(v)=Lk(v)
\]
的并。所有包含映射都是余纤维化，故 \(X\) 同伦等价于同伦推出
\[
*\ \cup_{Lk(v)}\ *\ \cong\ \Sigma Lk(v).
\]
即
\[
X\simeq \Sigma |lk_K(v)|.
\]
证毕。

### 4.2 可能同伦类型的分类

在 S4 的假设下，\(C=|B|\) 含 \(v\)，且
\[
A=O\cap C=C\setminus\{v\}\longrightarrow C
\]
是同伦等价。若 \(v\) 在 \(K\) 中是孤立点，则 \(B\subset\{v\}\)，从而 \(C=\{v\}\)，\(A=\varnothing\)，空集不可能同伦等价于非空单点空间。因此 \(v\) 非孤立。由穿刺-悬挂引理，
\[
X\simeq \Sigma |lk_K(v)|,
\]
且 \(lk_K(v)\) 是非空有限单纯复形。

另一方面，任取非空有限 CW 复形 \(Z\)。取有限单纯复形 \(L\) 使 \(|L|\simeq Z\)。令
\[
K=L*S^0,\qquad S^0=\{a,b\},
\]
其中 \(a,b\) 之间不加边。令
\[
v=a,
\]
并取 \(L\) 的任一顶点 \(w\)，令
\[
B=\{a,w\}
\]
为边 \(aw\)。则如前，\(K\) 有限，\(B\subset K\) 含 \(v\)，且
\[
|K|\setminus\{v\}\text{ 非空可缩},\qquad
|B|\setminus\{v\}\to|B|
\]
是同伦等价，同时
\[
X=|K|\cong \Sigma |L|\simeq \Sigma Z.
\]

因此 S4 中 \(X\) 的可能同伦类型恰好是
\[
\boxed{
X\simeq \Sigma Z
\quad\text{其中 }Z\text{ 为非空有限 CW 复形}.
}
\]
等价地，\(Z\) 可取为非空有限单纯复形。注意 \(Z\) 可以取一个点，此时 \(\Sigma Z\) 可缩，所以可缩型也包含在内。

### 4.3 \(X\) 可缩的有限组合判据

由穿刺-悬挂引理，
\[
X\simeq \Sigma |lk_K(v)|.
\]
令
\[
L:=lk_K(v).
\]
在 S4 中 \(L\) 非空有限。对非空有限 CW 复形 \(L\)，有
\[
\Sigma L\simeq *
\quad\Longleftrightarrow\quad
\widetilde H_*(L;\mathbb Z)=0.
\]
证明如下：

- 若 \(\Sigma L\) 可缩，则由悬挂同调同构
  \[
  \widetilde H_{n+1}(\Sigma L;\mathbb Z)
  \cong
  \widetilde H_n(L;\mathbb Z)
  \]
  得 \(\widetilde H_*(L;\mathbb Z)=0\)。
- 反之，若 \(\widetilde H_*(L;\mathbb Z)=0\)，则特别地 \(\widetilde H_0(L)=0\)，故 \(L\) 连通。非约化悬挂 \(\Sigma L\) 是沿连通空间 \(L\) 粘两个锥，由 van Kampen 定理知其基本群平凡；又由悬挂同调同构知 \(\Sigma L\) 的所有约化整同调为零。由 Whitehead 定理，\(\Sigma L\) 可缩。

因此
\[
\boxed{
X\text{ 可缩}
\iff
\widetilde H_*(lk_K(v);\mathbb Z)=0.
}
\]
等价地，
\[
H_0(lk_K(v);\mathbb Z)\cong\mathbb Z,
\qquad
H_i(lk_K(v);\mathbb Z)=0\quad(i>0).
\]

这个判据只需要 \(lk_K(v)\) 的有限关联数据：\(lk_K(v)\) 的 \(p\)-单形正是满足
\[
v\notin\sigma,\qquad \sigma\cup\{v\}\in K
\]
的 \((p+1)\)-单形 \(\sigma\)。因此它只用到了 \(K\) 中含 \(v\) 的单形及其面之间的关联关系。具体检验时，写出链复形
\[
0\to C_d(lk_K(v))\xrightarrow{\partial_d}\cdots
\xrightarrow{\partial_1}C_0(lk_K(v))\to0
\]
并用 Smith 标准形计算同调即可。

特别地，S3 中 \(lk_K(v)=\mathbb RP^2\)，其整同调不平凡，所以 \(X=\Sigma\mathbb RP^2\) 不可缩；但它有理同调为零。

---

## S5 不提供子复形 \(B\)

**结论：** 一般不必。若 \(v\) 非孤立，则仍必为悬挂；若 \(v\) 孤立，则恰好多出一个新类型 \(S^0\)。

由穿刺-悬挂引理，若 \(v\) 非孤立，则
\[
|K|\simeq \Sigma |lk_K(v)|,
\]
而 \(lk_K(v)\) 是非空有限单纯复形。因此此时
\[
|K|\simeq \Sigma Z
\]
对某个非空有限复形 \(Z\) 成立，故必为悬挂。

若 \(v\) 是孤立点，则
\[
|K|=O\sqcup\{v\}.
\]
由假设 \(O=|K|\setminus\{v\}\) 非空可缩，故
\[
|K|\simeq S^0.
\]
但非空有限复形的非约化悬挂总是道路连通的，而 \(S^0\) 有两个道路连通分支，故
\[
S^0
\]
不可能同伦等价于任何非空有限复形的悬挂。

所以完整的分类是：
\[
\boxed{
|K|\simeq \Sigma Z
\quad(Z\text{ 非空有限复形}),
}
\]
或者唯一的例外
\[
\boxed{
|K|\simeq S^0
\quad(v\text{ 为孤立点}).
}
\]
若题目默认 \(K\) 连通或 \(v\) 非孤立，则答案就是“必定是悬挂”，没有新增类型。

---

## S6 悬挂信息的逆向恢复

**结论：** 不一定。悬挂运算在有限复形上一般不可消去。

**反例：** 取
\[
L_1:\quad |L_1|\cong T^2=S^1\times S^1,
\]
\[
L_2:\quad |L_2|\cong S^1\vee S^1\vee S^2.
\]
二者都是非空有限单纯复形。

### 6.1 两者的悬挂同伦等价

先计算 \(L_2\)。约化悬挂与楔相容：
\[
\Sigma_{\mathrm{red}}(S^1\vee S^1\vee S^2)
\simeq
\Sigma_{\mathrm{red}}S^1
\vee
\Sigma_{\mathrm{red}}S^1
\vee
\Sigma_{\mathrm{red}}S^2
\simeq
S^2\vee S^2\vee S^3.
\]
由于 \(L_2\) 连通非空，非约化悬挂与约化悬挂同伦等价，所以
\[
\Sigma |L_2|\simeq S^2\vee S^2\vee S^3.
\]

再计算 \(T^2\)。取 \(T^2\) 的标准 CW 结构：一个 \(0\)-胞腔，两个 \(1\)-胞腔 \(a,b\)，一个 \(2\)-胞腔沿交换子
\[
aba^{-1}b^{-1}
\]
粘贴。约化悬挂后得到：

- 一个 \(0\)-胞腔；
- 两个 \(2\)-胞腔，形成二维骨架
  \[
  S^2\vee S^2;
  \]
- 一个 \(3\)-胞腔，其粘贴映射为原交换子粘贴映射的悬挂
  \[
  f:S^2\to S^2\vee S^2.
  \]

该 \(3\)-胞腔在胞腔链复形中的边界由交换子中各生成元的指数和决定。交换子 \(aba^{-1}b^{-1}\) 中 \(a\) 与 \(b\) 的指数和都为 \(0\)，故边界映射
\[
\partial_3:C_3(\Sigma T^2)\to C_2(\Sigma T^2)
\]
为零。于是 \(f\) 的 Hurewicz 像为零。又 \(S^2\vee S^2\) 单连通，且
\[
\pi_2(S^2\vee S^2)
\cong
H_2(S^2\vee S^2;\mathbb Z)
\cong
\mathbb Z^2
\]
由 Hurewicz 定理，故 \(f\) 零伦。因此
\[
\Sigma |L_1|\simeq \Sigma T^2
\simeq
S^2\vee S^2\vee S^3.
\]
于是
\[
\Sigma |L_1|\simeq \Sigma |L_2|.
\]

### 6.2 但 \(T^2\) 与 \(S^1\vee S^1\vee S^2\) 不同伦等价

计算上同调环：

- 对 \(T^2\)，
  \[
  H^1(T^2;\mathbb Z)\cong\mathbb Z^2
  \]
  有基 \(\alpha,\beta\)，且
  \[
  \alpha\cup\beta\neq0\in H^2(T^2;\mathbb Z)\cong\mathbb Z.
  \]
- 对
  \[
  Y=S^1\vee S^1\vee S^2,
  \]
  有
  \[
  H^1(Y;\mathbb Z)\cong\mathbb Z^2,\qquad
  H^2(Y;\mathbb Z)\cong\mathbb Z.
  \]
  令
  \[
  r:Y\to S^1\vee S^1
  \]
  为 collapse 掉 \(S^2\) 的和因子的收缩映射。则
  \[
  r^*:H^1(S^1\vee S^1;\mathbb Z)\to H^1(Y;\mathbb Z)
  \]
  是同构。任取 \(u,v\in H^1(Y;\mathbb Z)\)，写
  \[
  u=r^*u',\qquad v=r^*v'.
  \]
  则
  \[
  u\cup v
  =
  r^*(u'\cup v')=0,
  \]
  因为
  \[
  H^2(S^1\vee S^1;\mathbb Z)=0.
  \]
  故在 \(Y\) 中任意两个一次上同调类的 cup product 都为零。

因此 \(T^2\) 与 \(Y\) 的上同调环不同构，二者不可能同伦等价。

综上，
\[
\boxed{
\Sigma |L_1|\simeq \Sigma |L_2|
\not\Rightarrow
|L_1|\simeq |L_2|.
}
\]
这也说明 S4 的分类只能确定到“悬挂类型”，不能唯一恢复悬挂因子 \(Z\)。