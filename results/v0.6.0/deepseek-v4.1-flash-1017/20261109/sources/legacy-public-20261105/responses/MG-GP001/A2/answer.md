## S1 可缩子复形的商

设  
\[
q:Y\longrightarrow Y/A
\]
为商映射。因为 \((Y,A)\) 是 CW 对，所以具有同伦扩张性质。由于 \(A\) 可缩，取收缩
\[
H:A\times I\to A,\qquad H_0=\mathrm{id}_A,\qquad H_1\equiv a_0\in A.
\]
把 \(H\) 与 \(Y\times\{0\}\to Y\) 拼成映射
\[
A\times I\cup Y\times\{0\}\longrightarrow Y,
\]
由同伦扩张性质，它扩张为
\[
F:Y\times I\to Y,
\]
使得
\[
F_0=\mathrm{id}_Y,\qquad F_t(A)\subseteq A,\qquad F_1(A)=\{a_0\}.
\]
于是 \(F_1\) 通过 \(q\) 分解：存在唯一映射
\[
g:Y/A\to Y,\qquad g([y])=F_1(y),\qquad g(*)=a_0,
\]
其中 \(*=[A]\in Y/A\)。因此
\[
g\circ q=F_1\simeq F_0=\mathrm{id}_Y.
\]

再定义
\[
\widetilde F:Y\times I\to Y/A,\qquad \widetilde F(y,t)=q(F_t(y)).
\]
由于 \(F_t(A)\subseteq A\)，有
\[
\widetilde F(a,t)=q(F_t(a))=*,
\]
所以 \(\widetilde F\) 通过商映射 \(q\) 下降为
\[
\widetilde F':(Y/A)\times I\to Y/A.
\]
在 \(t=0\) 时，
\[
\widetilde F'_0([y])=q(F_0(y))=[y],
\]
故 \(\widetilde F'_0=\mathrm{id}_{Y/A}\)。在 \(t=1\) 时，
\[
\widetilde F'_1([y])=q(F_1(y))=q(g([y]))=(q\circ g)([y]),
\]
故
\[
\mathrm{id}_{Y/A}\simeq q\circ g.
\]
于是 \(q\) 是同伦等价，\(g\) 是同伦逆。

同伦能够下降到商的关键正是：扩张得到的同伦满足 \(F_t(A)\subseteq A\)，因此每个 \(q\circ F_t\) 在 \(A\) 上都常值于商点 \(*\)，从而通过 \(Y/A\) 分解。

---

## S2 非可缩底空间上的锥附着

设 \(f:L\hookrightarrow D\) 为包含映射。则
\[
Y=D\cup_L CL=C_f
\]
是 \(f\) 的映射锥。取零伦
\[
H:L\times I\to D,\qquad H_0=f,\qquad H_1\equiv d_0.
\]
即 \(H\) 是 \(f\) 到常值映射 \(c_{d_0}:L\to\{d_0\}\subseteq D\) 的同伦。

用标准事实：同伦的附着映射具有同伦等价的映射锥。事实上，若 \(H:f\simeq g\)，可定义 \(\Phi:C_f\to C_g\)，在 \(D\) 上取恒等，在锥坐标 \([l,t]\) 上取
\[
\Phi([l,t])=
\begin{cases}
H(l,2t),&0\le t\le \tfrac12,\\[2mm]
[l,2t-1],&\tfrac12\le t\le 1,
\end{cases}
\]
反向用逆同伦同理定义；两个复合可通过重参数化锥坐标得到与恒等同伦。因此
\[
C_f\simeq C_{c_{d_0}}.
\]

对常值映射 \(c_{d_0}\)，
\[
C_{c_{d_0}}
=
D\cup_{d_0}CL.
\]
此时整个底 \(L\times\{0\}\subseteq CL\) 都被粘到同一点 \(d_0\)，故锥的像为
\[
CL/L\cong \Sigma L,
\]
其中 \(\Sigma L\) 为非约化悬挂。于是
\[
C_{c_{d_0}}\cong D\vee \Sigma L.
\]
因此
\[
Y=C_f\simeq D\vee \Sigma L.
\]

楔点取为  
\[
p=d_0\in D
\]
与 \(\Sigma L=CL/L\) 中被塌缩的底 \(L\) 对应的下悬挂点。另一个悬挂点是锥顶。若换一个零伦终点 \(d_1\)，因为 \(D\) 道路连通，常值映射 \(c_{d_0}\) 与 \(c_{d_1}\) 同伦，故对应的映射锥同伦等价；所以楔点在道路连通分支中的选择不影响同伦型。

---

## S3 整数扭结的实例

取 \(RP^2\) 的任一有限单纯三角剖分 \(L\)。令
\[
K=L*\{v,w\},
\]
即 \(L\) 与两个离散点的 join。则
\[
|K|\cong \Sigma |L|.
\]
取 \(L\) 的任一顶点 \(a\)，令
\[
B=\{v,a\}=v*a.
\]
这是 \(K\) 的一个边，故 \(B\subseteq K\) 是含 \(v\) 的子复形。

逐条验证：

1. **商空间去掉 \(v\) 后非空可缩。**  
   \(|K|=\Sigma |L|\) 是两个锥沿 \(|L|\) 粘成。去掉上锥顶点 \(v\) 后，上锥去掉顶点形变收缩到 \(|L|\)，而 \(|L|\) 包含在下锥 \(w*|L|\) 中；下锥可缩。因此
   \[
   O=|K|\setminus\{v\}\simeq C|L|\simeq *,
   \]
   且 \(O\) 非空。

2. **\(O\cap C\to C\) 是同伦等价。**  
   这里
   \[
   C=|B|=[v,a]\cong[0,1],\qquad
   O\cap C=C\setminus\{v\}\cong(0,1],
   \]
   二者都可缩。包含映射 \((0,1]\hookrightarrow[0,1]\) 有同伦逆：常值映射到 \(a\)。故是同伦等价。

3. **约化有理同调全零。**  
   因为
   \[
   \widetilde H_n(\Sigma |L|;\mathbb Q)
   \cong
   \widetilde H_{n-1}(|L|;\mathbb Q),
   \]
   而
   \[
   H_1(RP^2;\mathbb Q)=0,\qquad H_2(RP^2;\mathbb Q)=0,
   \]
   所以
   \[
   \widetilde H_n(|K|;\mathbb Q)=0
   \qquad\text{对所有 }n.
   \]

4. **\(|K|\) 不可缩。**  
   由悬挂同调平移，
   \[
   \widetilde H_2(|K|;\mathbb Z)
   \cong
   \widetilde H_1(RP^2;\mathbb Z)
   =
   H_1(RP^2;\mathbb Z)
   \cong
   \mathbb Z/2\neq 0.
   \]
   故 \(|K|\) 不可缩。

因此该三元组满足全部要求。

---

## S4 整体对象与全部恢复目标

### 4.1 链环分解

设
\[
L=\operatorname{Lk}_K(v)
=\{\sigma\in K:\ v\notin\sigma,\ v\sigma\in K\},
\]
并令
\[
Z=\{\sigma\in K:\ v\notin\sigma\},
\]
即从 \(K\) 中去掉所有含 \(v\) 的单形后得到的子复形。则闭星
\[
\operatorname{st}_K(v)=v*L
\]
同胚于 \(CL\)，并且
\[
K=Z\cup_L (v*L).
\]
因此
\[
X=|K|=|Z|\cup_{|L|}C|L|,
\]
即 \(X\) 是包含映射
\[
|L|\hookrightarrow |Z|
\]
的映射锥。

另一方面，
\[
C|L|\setminus\{v\}\cong |L|\times[0,1)
\]
形变收缩到 \(|L|\subseteq |Z|\)。所以
\[
O=X\setminus\{v\}\simeq |Z|.
\]
若 \(O\) 可缩，则 \(|Z|\) 可缩。

于是当 \(L\neq\varnothing\) 时，由 S2（取 \(D=|Z|\)）
\[
X\simeq |Z|\vee \Sigma |L|
\simeq \Sigma |L|.
\]
最后一步因为 \(|Z|\) 是可缩子复形，商掉它得到 \(\Sigma |L|\)，由 S1 商映射为同伦等价。

---

### 4.2 分类

在 S4 的条件下，先证明
\[
L=\operatorname{Lk}_K(v)\neq\varnothing.
\]
反设 \(L=\varnothing\)。则 \(v\) 在 \(K\) 中是孤立顶点。写
\[
B=\{v\}\sqcup B_0,
\]
其中 \(B_0\) 不含 \(v\)。则
\[
C=|B|=\{v\}\sqcup |B_0|,
\qquad
C\setminus\{v\}=|B_0|.
\]
若 \(B_0=\varnothing\)，则 \(C\setminus\{v\}=\varnothing\)，不可能同伦等价于单点集 \(C\)。  
若 \(B_0\neq\varnothing\)，则 \(C\) 比 \(C\setminus\{v\}\) 多一个道路连通分支，而道路连通分支的个数在 homotopy equivalence 下不变，矛盾。

故 \(L\neq\varnothing\)。由 4.1，
\[
\boxed{X\simeq \Sigma |L|.}
\]
因此 \(X\) 的同伦型必为某个非空有限单纯复形的非约化悬挂。

反过来，任给非空有限单纯复形 \(L\)，取
\[
K=L*\{v,w\},
\qquad
B=\{v,a\},
\]
其中 \(a\) 是 \(L\) 的任一顶点。则：

- \(K\) 有限，\(v\) 是顶点，\(B\subseteq K\) 是含 \(v\) 的子复形；
- \(|K|=\Sigma |L|\)；
- 去掉 \(v\) 后，剩下的空间同伦等价于下锥 \(C|L|\)，可缩；
- \(C=|B|=[v,a]\)，且
  \[
  O\cap C=C\setminus\{v\}\cong(0,1],
  \]
  与 \(C\cong[0,1]\) 同伦等价。

于是该三元组满足全部条件，且 \(X\simeq \Sigma |L|\)。

所以完整的分类为
\[
\boxed{
\{X\text{ 的可能同伦型}\}
=
\{\Sigma |L|:\ L\text{ 为非空有限单纯复形}\}.
}
\]
等价地，\(X\) 必同伦等价于某个非空有限 CW 复形的非约化悬挂；上述构造实现了全部类型。

---

### 4.3 \(X\) 可缩的充要判据

在 S4 条件下，\(L=\operatorname{Lk}_K(v)\neq\varnothing\)，且
\[
X\simeq \Sigma |L|.
\]
我们断言
\[
\boxed{
X\text{ 可缩}
\iff
\widetilde H_i(L;\mathbb Z)=0
\quad\text{对所有 }i\ge0.
}
\]

**证明。**

若 \(X\) 可缩，则 \(\widetilde H_*(X;\mathbb Z)=0\)。由悬挂同调平移
\[
\widetilde H_{i+1}(\Sigma |L|;\mathbb Z)
\cong
\widetilde H_i(|L|;\mathbb Z),
\]
得到所有 \(\widetilde H_i(L;\mathbb Z)=0\)。

反过来，若所有 \(\widetilde H_i(L;\mathbb Z)=0\)，因为 \(L\neq\varnothing\)，特别地
\[
\widetilde H_0(L;\mathbb Z)=0,
\]
故 \(L\) 道路连通。于是 \(\Sigma |L|\) 单连通：它由两个可缩锥沿道路连通的 \(L\) 粘成，van Kampen 定理给出 \(\pi_1=0\)。同时由悬挂同调平移，
\[
\widetilde H_*(\Sigma |L|;\mathbb Z)=0.
\]
一个单连通有限 CW 复形若有平凡约化整同调，则由 Hurewicz 定理和 Whitehead 定理可缩。因此 \(X\simeq\Sigma |L|\) 可缩。

**有限关联数据检验。**  
链环 \(L=\operatorname{Lk}_K(v)\) 的单形正是那些不含 \(v\) 的 \(\tau\)，使得
\[
\tau\cup\{v\}\in K.
\]
因此它完全由 \(K\) 中含 \(v\) 的单形及其面决定。对每个 \(p\ge0\)，令
\[
C_p(L;\mathbb Z)
=
\mathbb Z\{ \tau\in L:\ |\tau|=p+1\},
\]
边界映射为通常的单纯边界
\[
\partial_p(\tau)
=
\sum_{j=0}^{p}(-1)^j(\tau\setminus\{a_j\}),
\qquad
\tau=\{a_0<\cdots<a_p\}.
\]
计算
\[
H_p(L;\mathbb Z)
=
\ker\partial_p/\operatorname{im}\partial_{p+1}.
\]
上述判据即为
\[
H_0(L;\mathbb Z)\cong\mathbb Z,
\qquad
H_p(L;\mathbb Z)=0\quad(p\ge1),
\]
等价地，所有约化整同调群为零。

注意必须使用整数系数。S3 中 \(L=RP^2\) 的所有约化有理同调为零，但
\[
H_1(RP^2;\mathbb Z)=\mathbb Z/2\neq0,
\]
所以其悬挂不可缩。这正是整系数与有理系数的差别。

---

## S5 不提供子复形 \(B\)

结论：**不必。** 新增的可能同伦型恰为
\[
S^0=\{\text{两个点}\}.
\]

设
\[
L=\operatorname{Lk}_K(v),\qquad
Z=\{\sigma\in K:\ v\notin\sigma\}.
\]
由 S4 的分解，
\[
O=X\setminus\{v\}\simeq |Z|.
\]

### 情形 1：\(L=\varnothing\)

此时 \(v\) 是 \(K\) 的孤立顶点，故
\[
X=\{v\}\sqcup |Z|,
\qquad
O=|Z|.
\]
题设 \(O\) 非空可缩，所以 \(|Z|\) 可缩且非空。于是
\[
X\simeq \{v\}\sqcup\{\text{一点}\}=S^0.
\]
这不是非空有限复形的悬挂：任何非空空间的非约化悬挂都是道路连通的，而 \(S^0\) 不连通。

### 情形 2：\(L\neq\varnothing\)

由 S4 的链环分解和 S2，
\[
X\simeq \Sigma |L|.
\]
这是非空有限复形 \(L\) 的悬挂。

因此全部可能类型为
\[
\boxed{
\{\Sigma |L|:\ L\text{ 非空有限单纯复形}\}
\;\cup\;
\{S^0\}.
}
\]
其中 \(S^0\) 确实不属于第一类。除 \(S^0\) 外没有新的类型。

---

## S6 悬挂信息的逆向恢复

结论：**不必。** 悬挂一般不满足消去律。

取 Hopf 映射
\[
\eta:S^3\to S^2
\]
为其同伦类 \(\eta\in\pi_3(S^2)\cong\mathbb Z\) 的生成元。对 \(n=1,3\)，令
\[
X_n=S^2\cup_{n\eta}e^4
\]
为附着映射 \(n\eta:S^3\to S^2\) 的映射锥。

取有限单纯模型 \(L_n\)：例如取 \(S^2,S^3\) 的有限三角剖分，用单纯逼近把 \(n\eta\) 表示为单纯映射 \(f_n:S^3\to S^2\)（必要时细分定义域），再令 \(L_n\) 为 \(f_n\) 的单纯映射锥。则 \(L_n\) 是非空有限单纯复形，且
\[
|L_n|\simeq X_n.
\]

### 6.1 两个悬挂同伦等价

约化悬挂与非约化悬挂对非空 CW 复形同伦等价，以下用约化悬挂叙述。有
\[
\Sigma X_n
\simeq
S^3\cup_{\Sigma(n\eta)}e^5.
\]
标准事实：
\[
\pi_4(S^3)\cong\mathbb Z/2,
\]
且由 \(\Sigma\eta\) 生成。因此
\[
\Sigma(3\eta)=3\Sigma\eta=\Sigma\eta.
\]
于是
\[
\Sigma X_3\simeq \Sigma X_1.
\]
从而
\[
\Sigma |L_3|\simeq \Sigma X_3\simeq \Sigma X_1\simeq \Sigma |L_1|.
\]

### 6.2 两个空间本身不同伦等价

对任意 \(f:S^3\to S^2\)，映射锥
\[
C_f=S^2\cup_f e^4
\]
的整上同调分次环为
\[
H^*(C_f;\mathbb Z)
\cong
\mathbb Z[a,b]/(a^2-H(f)b),
\]
其中
\[
\deg a=2,\qquad \deg b=4,
\]
而 \(H(f)\in\mathbb Z\) 是 \(f\) 的 Hopf 不变量。

Hopf 不变量是二次的：若 \(d_n:S^2\to S^2\) 是次数 \(n\) 的映射，则
\[
H(d_n\circ\eta)=n^2H(\eta)=n^2.
\]
又 \(d_n\circ\eta\) 代表 \(n\eta\)，故
\[
H(n\eta)=n^2.
\]
因此
\[
H^*(X_1;\mathbb Z)
\cong
\mathbb Z[a,b]/(a^2-b),
\]
而
\[
H^*(X_3;\mathbb Z)
\cong
\mathbb Z[a,b]/(a^2-9b).
\]

在 \(X_1\) 中，\(H^4\) 由 \(a^2\) 生成；在 \(X_3\) 中，所有二次元素的平方都落在
\[
9H^4\neq H^4
\]
中。因此两个分次环不同构。故
\[
X_1\not\simeq X_3,
\]
从而
\[
|L_1|\not\simeq|L_3|.
\]

但它们的悬挂同伦等价。因此
\[
\boxed{
\Sigma |L_1|\simeq \Sigma |L_2|
\;\not\Longrightarrow\;
|L_1|\simeq |L_2|.
}
\]

这个反例本质上是整系数的：若用有理系数，则 \(9\) 是可逆平方，两个上同调环会变成同构。