# 局部单形、锥附着与整体同伦型：完整最终稿

以下所有复形均为有限抽象单纯复形，并取通常的几何实现；同调除注明外均取整系数。记 $X=|K|$、$O=X\setminus\{v\}$、$C=|B|$，并记
$$
\operatorname{lk}_K(v)=\{\sigma\in K:v\notin\sigma,\ \sigma\cup\{v\}\in K\},\qquad
L=|\operatorname{lk}_K(v)|.
$$
用 $\operatorname{st}_K(v)$ 和 $\operatorname{St}_K(v)$ 分别表示顶点 $v$ 的开星和闭星。非约化悬挂记为 $\Sigma$：对非空 $Z$，固定模型
$$
\Sigma Z=CZ/Z.
$$

## S1 可缩子复形的商

结论是：商映射 $q:Y\to Y/A$ 是同伦等价。

取 $a_0\in A$ 及同伦
$$
h_t:A\to A,\qquad h_0=\mathrm{id}_A,\qquad h_1(A)=\{a_0\}.
$$
因为 $(Y,A)$ 是 CW 对，故具有同伦延拓性质；于是 $h_t$ 可以延拓为
$$
H_t:Y\to Y,\qquad H_0=\mathrm{id}_Y,\qquad H_t|_A=h_t.
$$
特别地，$H_1(A)=\{a_0\}$，所以 $H_1$ 在 $q$ 的每条纤维上为常值。由商映射的泛性质，存在连续映射
$$
g:Y/A\to Y,\qquad g\circ q=H_1.
$$
因此
$$
g\circ q=H_1\simeq \mathrm{id}_Y.
$$

另一方面，对每个 $t$，$H_t(A)\subseteq A$，所以 $K_t:=q\circ H_t:Y\to Y/A$ 在 $A$ 上恒等于商点。于是存在 $\overline K_t:Y/A\to Y/A$，使
$$
\overline K_t\circ q=q\circ H_t.
$$
映射 $(y,t)\mapsto H_t(y)$ 连续，故 $(z,t)\mapsto\overline K_t(z)$ 也连续；由此 $\overline K_0\simeq\overline K_1$。而
$$
\overline K_0=\mathrm{id}_{Y/A},\qquad
\overline K_1=q\circ g.
$$
于是 $q\circ g\simeq\mathrm{id}_{Y/A}$。映射 $q$ 的两侧都有同伦逆，故 $q$ 是同伦等价。

同伦能够下降到商的关键正是：每个 $q\circ H_t$ 都把整个 $A$ 送到同一点，故它在 $q$ 的纤维上为常值；同时 $H_1$ 也把 $A$ 压成同一点，从而给出高于商的逆映射。

## S2 非可缩底空间上的锥附着

结论是
$$
Y=D\cup_L CL\simeq D\vee\Sigma L.
$$

先说明所用标准事实及其适用条件。设 $i:A\to E$ 是 CW 对的余纤维化，且 $i\simeq *$。则 $i$ 的映射锥满足
$$
E\cup_i CA\simeq E\vee\Sigma A.\tag{1}
$$
这正是零伦余纤维化的分裂引理。证明可由同伦推出直接得到：余纤维化保证 $E\cup_i CA$ 是图中
$$
E\longleftarrow A\longrightarrow CA
$$
的同伦推出。由于 $A\xrightarrow{i}E$ 零伦，在同伦推出的计算中可把该箭头连同零伦数据替换为 $A\to *\to E$；沿 $*$ 分两次粘贴得到
$$
E\cup_i CA
\simeq E\mathbin{\vee}\left(*\mathbin{\cup}^h_A CA\right).
$$
内层的 $A\to CA$ 也零伦，且 $CA$ 可缩，因此内层同伦推出同伦等价于
$$
*\mathbin{\cup}^h_A *\cong CL/L\cong\Sigma A.
$$
这里“替换零伦箭头”必须在同伦推出中连同零伦一并替换，不能把普通严格映射锥直接换成一个落点后所得的另一个严格映射锥；CW 余纤维化条件保证上述同伦推出计算合法。

回到本题。$L\hookrightarrow D$ 和 $L\hookrightarrow CL$ 均为 CW 余纤维化，而包含 $i:L\hookrightarrow D$ 零伦。令 $d_0\in D$ 为零伦的终点。写
$$
CL=L\times[0,1]/L\times\{1\},\qquad
\Sigma L=CL/L\cong L\times[0,1]/(L\times\{0,1\}).
$$
这里 $CL$ 正是常值映射 $L\to *$ 在汇端为单点时的映射柱。若令该汇端为 $d_0\in D$，而不是一个与 $D$ 无关联的单点，得到的是映射柱与 $D$ 在汇端单点处的粘并；这正是标准事实 (1) 在空间层面的含义。再由 $i:L\hookrightarrow D$ 零伦，
$$
Y=D\cup_L CL\simeq D\vee\Sigma L.
$$

楔点取为 $d_0\in D$ 与 $\Sigma L=CL/L$ 中“被 collapse 的锥底 $L$”对应的那个悬挂极点。$CL/L$ 的两个悬挂极点在道路连通的 $\Sigma L$ 中相互同伦；即使改取另一个零伦终点 $d_0'$，$D$ 的道路连通性也保证两种楔点的选择给出同伦等价的楔空间。

## S3 整数扭结的实例

取 $L$ 为 $\mathbb RP^2$ 的任一有限单纯三角剖分，并令 $S^0=\{a,b\}$ 为由两个孤立顶点组成的零维复形，即不含边 $\{a,b\}$。定义单纯 join
$$
K=L*S^0.
$$
等价地，$K$ 的单形是没有同时含 $a,b$ 的单形，以及分别含 $a$ 或 $b$ 的 $\sigma*\{a\}$、$\sigma*\{b\}$，其中 $\sigma\in L$。置
$$
v=a.
$$
任取 $L$ 的一个顶点 $w$，并令 $B$ 为由边 $\{a,w\}$ 及其面构成的子复形。

第一，
$$
|K|\cong \Sigma|L|=\Sigma\mathbb RP^2.
$$
去掉 $a$ 后，含 $a$ 的那个锥被去掉锥顶，而形变收缩到 $|L|$；整个空间因此形变收缩到圆锥 $|L|*\{b\}$。所以
$$
|K|\setminus\{a\}\simeq |L|*\{b\},
$$
而后者非空且可缩。

第二，$|B|\cong[0,1]$，且 $|B|\setminus\{a\}\cong(0,1]$。两者都可缩，故包含映射
$$
|B|\setminus\{a\}\longrightarrow |B|
$$
是同伦等价。

第三，约化有理同调满足悬挂同构：
$$
\widetilde H_n(\Sigma\mathbb RP^2;\mathbb Q)
\cong \widetilde H_{n-1}(\mathbb RP^2;\mathbb Q)=0
$$
对所有 $n$ 都成立。然而
$$
\widetilde H_2(\Sigma\mathbb RP^2;\mathbb Z)
\cong \widetilde H_1(\mathbb RP^2;\mathbb Z)
\cong\mathbb Z/2\ne0,
$$
故 $|K|$ 不可缩。这给出了所求实例。

## S4 整体对象与全部恢复目标

### 4.1 穿刺-悬挂引理

**引理.** 设 $K$ 有限，$v$ 是非孤立顶点，$X=|K|$。若 $X\setminus\{v\}$ 非空可缩，则
$$
X\simeq \Sigma|\operatorname{lk}_K(v)|.\tag{2}
$$

证明时令 $L=|\operatorname{lk}_K(v)|$，令
$$
W=|K-v|
$$
为删除所有含 $v$ 的单形后所得的满子复形；这里 $K-v$ 表示由不含 $v$ 的单形组成的子复形，而不是集合差。有恒等式
$$
|K|\setminus\operatorname{st}_K(v)=W,\qquad
\operatorname{St}_K(v)=v*\operatorname{lk}_K(v)\cong CL,
$$
并且
$$
W\cap \operatorname{St}_K(v)=L.
$$
因为 $v$ 非孤立，$L$ 与 $W$ 都非空。若把几何实现取成各单形内部互不相交的并，则开星等于对应单形内部的并，第一式右边闭子复形的实现恰是这些内部的并。进一步，$\operatorname{St}_K(v)\setminus\{v\}=(\operatorname{st}_K(v)\setminus\{v\})\cup L$，而 $\operatorname{st}_K(v)\setminus\{v\}$ 是一个开锥，形变收缩到 $L\subset W$。因此
$$
X\setminus\{v\}
=W\cup_L\bigl(\operatorname{St}_K(v)\setminus\{v\}\bigr)
\simeq W.
$$
由假设 $X\setminus\{v\}$ 可缩，得到 $W$ 可缩。特别地，包含 $L\hookrightarrow W$ 零伦。

另一方面，
$$
X=W\cup_L \operatorname{St}_K(v)=W\cup_L CL.
$$
对 $W,L$ 应用 S2，得到
$$
X\simeq W\vee\Sigma L\simeq \Sigma L.
$$
由于 $W$ 可缩，其在楔中的因子可以缩到楔点。引理得证。

### 4.2 可能同伦类型的完整分类

先证明题设中的 $B$ 条件迫使 $v$ 非孤立。因为 $C$ 含有 $v$，
$$
O\cap C=C\setminus\{v\},
$$
并且题目要求 $C\setminus\{v\}\to C$ 是同伦等价。若 $v$ 在 $K$ 中孤立，则 $C$ 分解为
$$
C\cong (C\setminus\{v\})\sqcup\{v\}.
$$
于是无论 $C\setminus\{v\}$ 有多少个道路连通分支（包括零个），
$$
H_0(C;\mathbb Z)\cong H_0(C\setminus\{v\};\mathbb Z)\oplus\mathbb Z,
$$
左、右维数不同，故包含映射不可能诱导 $H_0$ 的同构，更不可能是同伦等价。因此 $v$ 必非孤立。

由引理，$X\simeq\Sigma|\operatorname{lk}_K(v)|$，而 $\operatorname{lk}_K(v)$ 是非空有限单纯复形。所以任何满足条件的三元组都给出
$$
X\simeq\Sigma Z,\qquad Z\text{ 为某个非空有限 CW 复形}.\tag{3}
$$

反过来，任取非空有限 CW 复形 $Z$。取一个有限单纯复形 $L$ 使 $|L|\simeq Z$，这可由有限 CW 复形的有限单纯模型或单纯逼近得到。令
$$
K=L*S^0,\qquad S^0=\{a,b\},\qquad v=a.
$$
任取 $L$ 的顶点 $w$，并令 $B$ 为边 $\{a,w\}$ 及其面组成的子复形。节点 $a,b$ 之间不加边。则
$$
|K|\setminus\{a\}\simeq |L|*\{b\},
$$
故非空可缩；同时
$$
|B|\setminus\{a\}\cong(0,1],\qquad |B|\cong[0,1],
$$
所以包含映射 $|B|\setminus\{a\}\to|B|$ 同伦等价。最后
$$
|K|\cong\Sigma|L|\simeq\Sigma Z.
$$

因此，(3) 是完整分类。等价地，$X$ 的全部可能类型的典型实现正是全部非约化悬挂
$$
\boxed{\ \Sigma|L|\quad(L\text{ 为非空有限单纯复形}).\ }
$$
其中取 $L$ 为单点时得到可缩型，故可缩型也包括在内。

### 4.3 只用 $v$ 的局部关联数据判断可缩性

令 $L=\operatorname{lk}_K(v)$。由一个 $p$ 单形 $\sigma\in L$ 对应到 $K$ 中的 $(p+1)$ 单形 $\sigma\cup\{v\}$，即可只从“包含 $v$ 的单形及其面”写出 $L$ 的全部面关联。判据为
$$
\boxed{\quad X\text{ 可缩}
\iff \widetilde H_*(L;\mathbb Z)=0
\iff
H_0(L;\mathbb Z)\cong\mathbb Z,\quad
H_i(L;\mathbb Z)=0\ (i>0).\quad}\tag{4}
$$

必要性由悬挂同调同构立即得到。反之，若 $\widetilde H_*(L)=0$，则从 $H_0$ 可知 $L$ 道路连通；又 $L$ 非空。于是 $\Sigma L$ 是道路连通空间 $L$ 上两个锥的并，由 van Kampen 定理，其基本群平凡。悬挂同调同构给出
$$
\widetilde H_*(\Sigma L;\mathbb Z)=0.
$$
具体地，$H_0(\Sigma L)\cong\mathbb Z$，且所有正次数同调为零。对有限 CW 复形 $\Sigma L$ 依次应用 Hurewicz 定理及 Whitehead 定理，可知 $\Sigma L$ 可缩。再由 (2)，$X$ 可缩。

在实际检验中，以 $L$ 的 $p$ 单形为链群基，写出有限链复形
$$
\cdots\longrightarrow C_p(L)\xrightarrow{\partial_p}C_{p-1}(L)\longrightarrow\cdots
$$
并对所有 $p$ 用 Smith 标准形检查
$$
H_p(L;\mathbb Z)=\ker\partial_p/\operatorname{im}\partial_{p+1}=0\quad(p>0),
\qquad H_0(L;\mathbb Z)=\mathbb Z.
$$
所以 (4) 只使用 $K$ 中含 $v$ 的单形及其面的有限关联数据。

## S5 不提供子复形 $B$

结论是：不提供 $B$ 时，$|K|$ 不必同伦等价于非空有限复形的悬挂；新增且唯一的类型是 $S^0$。

若 $v$ 非孤立，由穿刺-悬挂引理，$\operatorname{lk}_K(v)$ 非空，且
$$
|K|\simeq\Sigma|\operatorname{lk}_K(v)|.
$$
因此仍属于悬挂类型。

若 $v$ 是孤立点，则
$$
|K|\cong (|K|\setminus\{v\})\sqcup\{v\}.
$$
由假设，非空空间 $|K|\setminus\{v\}$ 可缩，故 $|K|\simeq S^0$。每个非空有限复形的非约化悬挂都道路连通，而 $S^0$ 有两个道路连通分支，所以它不可能同伦等价于这种悬挂。

两类都可实现：对任取的非空有限复形 $L$，$K=L*S^0$ 与顶点 $a$ 实现 $\Sigma|L|$；而 $K=S^0=\{v,w\}$ 实现 $S^0$。因此完整分类是
$$
\boxed{|K|\simeq\Sigma Z\ (Z\text{ 非空有限复形})\quad\text{或}\quad |K|\simeq S^0.}
$$

## S6 悬挂信息的逆向恢复

结论是：单次悬挂一般不可消去。

取
$$
|L_1|\cong T^2=S^1\times S^1,\qquad
|L_2|\cong S^1\vee S^1\vee S^2.
$$
两者都有非空有限单纯模型。

先算 $\Sigma|L_2|$。因 $L_2$ 道路连通，非约化悬挂与其约化悬挂同伦等价；约化悬挂保持非空 CW 复形的楔，故
$$
\Sigma|L_2|\simeq S^2\vee S^2\vee S^3.\tag{5}
$$

对 $T^2$ 取标准 CW 结构：一个 $0$ 胞腔、两个 $1$ 胞腔 $a,b$ 和一个沿交换子 $aba^{-1}b^{-1}$ 粘贴的 $2$ 胞腔。约化悬挂后，两个 $1$ 胞腔给出一个 $S^2\vee S^2$ 二骨架，沿交换子粘贴的 $2$ 胞腔给出一个 $3$ 胞腔。该 $3$ 胞腔的胞腔边界是两个悬挂 $2$ 胞腔生成元各自的“指数和”；交换子中 $a$ 和 $b$ 的总指数都是 $0$，所以
$$
\partial_3:C_3(\Sigma T^2)\longrightarrow C_2(\Sigma T^2)
$$
是零映射。

其粘贴映射因此诱导 $H_2$ 上零映射。目标 $S^2\vee S^2$ 单连通，Hurewicz 定理给出
$$
\pi_2(S^2\vee S^2)\cong H_2(S^2\vee S^2;\mathbb Z)\cong\mathbb Z^2,
$$
故粘贴映射零伦。于是
$$
\Sigma T^2\simeq S^2\vee S^2\vee S^3.\tag{6}
$$
由 (5)、(6)，
$$
\Sigma|L_1|\simeq\Sigma|L_2|.
$$

然而 $T^2$ 与 $S^1\vee S^1\vee S^2$ 不同伦等价。对 $T^2$，存在 $u,v\in H^1(T^2;\mathbb Z)$，使
$$
u\smile v\ne0\in H^2(T^2;\mathbb Z).
$$
另一方面，令 $r:S^1\vee S^1\vee S^2\to S^1\vee S^1$ 为收缩掉 $S^2$ 因子的映射。因为
$$
r^*:H^1(S^1\vee S^1)\longrightarrow H^1(S^1\vee S^1\vee S^2)
$$
是同构，而 $H^2(S^1\vee S^1)=0$，所以对任意 $x,y\in H^1(S^1\vee S^1\vee S^2)$，都可写成 $x=r^*x'$、$y=r^*y'$，从而
$$
x\smile y=r^*(x'\smile y')=0.
$$
两者的 $H^1$ 都为 $\mathbb Z^2$，但 cup product 性质不同，故它们不可能同伦等价。因此
$$
\boxed{\Sigma|L_1|\simeq\Sigma|L_2|\quad\not\Longrightarrow\quad |L_1|\simeq|L_2|.}
$$

## 本次完善说明与自评

**保留。** S1 的同伦延拓证明、S2 的零伦余纤维化分裂结论、S3 的 join 构造、S4 的悬挂分类与有限链复形判据、S5 的孤立点例外，以及 S6 的胞腔和 cup product 反例均包括在最终稿中；它们满足题设对象和范围。

**新增或修正。** 明确写出了 S2 所用分裂引理的条件和同伦推出理由；把 S4 中的 $D$ 精确改述为非空子复形 $K-v$，避免把开星补集误称为任意子复形；修正了“$v$ 孤立则 $B=\{v\}$”这一不严谨表述，改为用 $H_0$ 证明 $B$ 可含其他分支时仍不可能满足同伦等价；同时补全了悬挂可缩判据中从整同调到可缩的 Hurewicz--Whitehead 论证。

**仍未完成或不确定。** 原题 S1--S6 没有未完成项；所有六个阶段均已给出证明、构造或反例，并能独立阅读，不依赖未交付草稿。仍未完成的是额外研究增量：本轮没有添加超出 S1--S6 所要求结论的新定理，所以研究档没有达到 $R3$。

**自评。** 取 $B2$：S1--S6 的实质要求均已正确、完整交付。S4 虽然包含完整分类、全部类型的实现和局部可判定判据，S6 也包含严格反例，但这些正是原题逐项要求的结论；没有另行证明一个原题未要求、可独立陈述并解决新对象或参数族的定理。因此按题给定义，这些工作应记为原结论层面的 $R0$，而不是因篇幅或分类的规模自动升级。最终自评为 $B2/R0$：数学基线完整且可靠，但本轮没有研究增量，故不满足 SMC 所要求的 $B2$ 与 $R3$ 同时成立。
