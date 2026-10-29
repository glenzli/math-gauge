# 局部单形、锥附着与整体同伦型：逐阶段参考与判准

本组 version 0.1.0；AI 作者自查完成，human pending。未调用候选模型，未为本组生成或编译 Lean。既有母题参考只作为本组完整数学论证的来源，不继承其模型成绩或形式化覆盖。每阶段均 mandatory；分值用于诊断，整组 pass 必须全部阶段实质完成。

## S1 可缩子复形的商

判定：true。

用 CW 对的同伦延拓性质把 A 内的收缩扩张为 F:Y×I→Y，F_0=id，F_t(A)⊂A，F_1 在 A 上常值。因此 F_1 下降成 g:Y/A→Y，有 gq≃id_Y。qF_t 在 A 上恒定，下降为 id_{Y/A}≃qg。有限 CW 紧 Hausdorff，A 闭且商 Hausdorff，q×id_I 是紧到 Hausdorff 的连续满射，所以是商映射，保证所下降同伦连续。

判准：HEP 与商同伦连续；两复合。

## S2 非可缩底空间上的锥附着

判定：true。

子复形包含为 cofibration，普通锥附着是其同伦余纤维。零伦把包含变为到某 d_0∈D 的常值映射；同伦映射的映射锥同伦等价，可将给定同伦粘在圆柱 L×I 上构造相互同伦逆。常值映射的锥是把 CL 的底 L 压到 d_0，故为 D∨(CL/L)=D∨ΣL，楔在 D 的 d_0 与悬挂一个极点。非空 L 确保该描述有两个悬挂极点；D 路径连通使不同选择 d_0 给同伦等价的楔。没有假定 D 可缩。

判准：cofibration 与同伦余纤维；常值锥的具体商。

## S3 整数扭结的实例

判定：construction。

取新顶点 v,w，K=(v*L)∪(w*L)，选 L 顶点 a，B 为边 va。K−v=w*L 为锥；在去 v 的实现中把非 v 重心坐标除以 1−λ_v，再作线性同伦，得对该锥的强形变收缩。B 是闭区间，去端点仍可缩，常值到 a 作同伦逆。|K|=Σ|L|。RP² 的胞腔链为 Z --2→ Z --0→ Z，故 H̃_1=Z/2，其余约化整数同调零。悬挂 Mayer–Vietoris 给 H̃_2(|K|;Z)=Z/2，因此不可缩；张量 Q 后正维同调全零，悬挂路径连通亦使 H̃_0=0。

判准：实际 K,v,B；扭结同调与有理同调区别。

## S4 整体对象与全部恢复目标

判定：true。

主目标是成立的分类与判据。记

$$D=K-v:=\{\sigma\in K:v\notin\sigma\},\qquad
L=\operatorname{lk}_K(v):=\{\sigma\in K:v\notin\sigma,\ \sigma\cup\{v\}\in K\}.$$

结论为：$L$ 至少有一个顶点，且

$$|K|\simeq \Sigma|L|.\tag{1}$$

这里对非空空间 $Y$，$\Sigma Y$ 是非约化悬挂

$$Y\times[0,1]/\bigl(Y\times\{0\}\text{ 压为一点， }Y\times\{1\}\text{ 压为另一点}\bigr).$$

所有可能同伦类型恰为至少含一个顶点的有限单纯复形的非约化悬挂。可缩的充要条件是

$$\widetilde H_j(L;\mathbb Z)=0\quad\text{对所有整数 }j\ge0.\tag{2}$$

这里是约化整数单纯同调；通过有限边界矩阵可检验条件 (2)。它不要求 $|L|$ 可缩，亦不只检验欧拉示性数或有理同调。



## 1. 非空性与删除复形

几何实现有至少一个顶点时才称非空；只有空面的复形之实现为空。题中 $v\in B$，所以 $C$ 非空。若 $v$ 在 $B$ 中不属于任何边，则在有限复形 $|B|$ 中 $\{v\}$ 是单独的开闭分支。$C\setminus\{v\}\to C$ 的像没有遇到这个分支，因而不能在路径分支集合上满射，更不可能是同伦等价。因此 $B$ 中存在一条边 $\{v,w\}$。特别地，$w$ 是 $L$ 的顶点，所以 $|L|\ne\varnothing$，$D$ 也至少有一个顶点。这个推导排除了空 link 和孤立顶点，没有把这些情况默认为题外。

在有限顶点集对应的标准欧氏单纯形中写

$$x=\sum_{u\in V(K)}\lambda_u(x)u,\qquad
\lambda_u\ge0,\quad\sum_u\lambda_u=1.$$

对 $x\in O$，$\lambda_v(x)<1$，可定义

$$r(x)=\sum_{u\ne v}\frac{\lambda_u(x)}{1-\lambda_v(x)}u.$$

若 $x$ 的承载单形为 $\sigma$，那么 $r(x)$ 位于它不含 $v$ 的面中，所以 $r(x)\in|D|$。分母在整个 $O$ 上为正，故 $r$ 连续。线性同伦

$$H(x,t)=(1-t)x+t\,r(x)$$

始终位于同一个单形；其 $v$ 坐标为 $(1-t)\lambda_v(x)<1$，所以始终属于 $O$。若 $x\in|D|$，则 $r(x)=x$，整个同伦固定 $x$。因此 $|D|$ 是 $O$ 的强形变收缩核，题设推出 $|D|$ 可缩。

这里没有在 $v$ 处延伸这个同伦。实际上公式在 $v$ 处无定义，这个区别正是以后必须使用合法闭子复形分解的原因。



## 2. 整体的同伦模型

闭星形子复形是锥 $v*L$。按单形逐个核对，有

$$K=D\cup(v*L),\qquad D\cap(v*L)=L.\tag{3}$$

事实上，不含 $v$ 的单形属于 $D$；含 $v$ 的单形去掉 $v$ 后属于 $L$。锥中不含 $v$ 的单形恰为 $L$。

有限单纯复形与子复形构成 CW 对，故有同伦延拓性质。对本处所需的商定理给出论证：若 $A$ 是有限 CW 复形 $Y$ 的非空可缩子复形，将 $A$ 内的一个收缩延拓为 $F:Y\times I\to Y$，且 $F_0=\operatorname{id}_Y$。于是 $F_t(A)\subseteq A$，$F_1|_A$ 为常值，$F_1$ 因而下降为 $g:Y/A\to Y$。对商映射 $q:Y\to Y/A$，有 $gq=F_1\simeq\operatorname{id}_Y$。$qF_t$ 在 $A$ 上恒定，故同样下降成从 $\operatorname{id}_{Y/A}$ 到 $qg$ 的同伦。这里商与参数乘积的连续性可由 $q\times\operatorname{id}_I$ 是紧空间到 Hausdorff 空间的满射、从而是商映射得到。故 $q$ 是同伦等价。

将此用于 $Y=|K|$、$A=|D|$，得到

$$|K|\simeq|K|/|D|\cong |v*L|/|L|\cong\Sigma|L|.$$

中间同胚由 (3) 诱导：两边的点一一对应，连续双射的源紧而靶 Hausdorff。最后一个同胚把锥的顶点和被压掉的底面分别视为悬挂的两个极点。非空性已在第 1 节证明。这完成式 (1)，证明只对闭子复形 $D$ 使用了商定理。



## 3. 每种悬挂类型的实现

令 $L_0$ 是任意至少有一个顶点的有限单纯复形，取不同的新顶点 $v,w$，定义

$$K_0=(v*L_0)\cup(w*L_0).$$

两个锥沿共同的底 $L_0$ 粘合，$K_0$ 不含边 $\{v,w\}$；其几何实现就是 $\Sigma|L_0|$。选 $L_0$ 的任一顶点 $a$，令 $B_0$ 为闭边 $\{v,a\}$ 及其全部面。

删除复形 $K_0-v=w*L_0$ 是锥。第 1 节的显式收缩说明 $|K_0|\setminus\{v\}$ 形变收缩到这个锥，所以非空可缩。$|B_0|$ 是闭区间，$|B_0|\setminus\{v\}$ 是去掉一个端点的半开区间。它们都可缩，且包含映射确实是同伦等价：把整个闭区间常值映到端点 $a$ 作逆，两边的线性收缩给出所需同伦。

于是 $(K_0,v,B_0)$ 满足全部原条件。$O$ 开，是因为 $\{v\}$ 在有限多面体中闭；$C$ 闭，是因为它是有限子复形；$O\cup C=X$，因为唯一从 $O$ 删去的点属于 $C$。因此分类没有暗中增加开覆盖、变形收缩相容性或局部平坦性。

这项分类是对可能同伦类型的描述与实现，不宣称给出任意两个有限悬挂何时同伦等价的判定算法。



## 4. 可缩的精确局部判据

令 $Y=|L|\ne\varnothing$。悬挂可由删去南极和删去北极的两个开集覆盖。两个开集各自可缩，交集同胚于 $Y\times(0,1)$，与 $Y$ 同伦等价。约化 Mayer–Vietoris 正合列给出

$$\widetilde H_{j+1}(\Sigma Y;\mathbb Z)
\cong\widetilde H_j(Y;\mathbb Z)\qquad(j\ge0).\tag{4}$$

悬挂本身路径连通。因而如果 $X$ 可缩，式 (1) 和 (4) 立即推出 (2)。

反向假设 (2)。其中 $\widetilde H_0(Y;\mathbb Z)=0$，结合非空有限 CW 结构，说明 $Y$ 路径连通。对上面两个可缩开集使用 van Kampen 定理，得到 $\pi_1(\Sigma Y)=0$；这里交集路径连通的假设已由零维同调核实。式 (4) 又说明悬挂的全部正维整数同调为零。

一个单连通且整数无约化同调的 CW 复形可缩：若有非零同伦群，取最小的 $n\ge2$，Hurewicz 定理会把 $\pi_n$ 同构到 $H_n$，矛盾。因此全部同伦群均为零，再对一点到该 CW 复形的映射使用 Whitehead 定理，即为同伦等价。应用于 $\Sigma Y$，再用 (1)，得到 $X$ 可缩。

这一步没有把一般无环空间直接当作可缩空间；所需单连通性来自悬挂及 link 的路径连通性。

判据只需要题目允许的局部数据。每个含 $v$ 的单形删去 $v$ 就给出 $L$ 的单形，面关联也随之确定。给顶点选任意全序，用通常交错边界构造有限增广链复形

$$0\longrightarrow C_d(L;\mathbb Z)\longrightarrow\cdots
\longrightarrow C_0(L;\mathbb Z)\xrightarrow{\epsilon}\mathbb Z\longrightarrow0,$$

其中 $\epsilon$ 把每个顶点送到 $1$。条件 (2) 等价于它在所有位置正合。整数矩阵的 Smith 标准形能在有限步内计算各同调群，故这确是有限数据可检验的充要条件。只检查有理秩会遗漏扭结，只检查欧拉示性数会遗漏不同维度的非零同调。

判准：Describe all possible homotopy types for every allowed triple. A correct answer proves |K| is homotopy equivalent to the unreduced suspension of the nonempty finite vertex link, or gives a mathematically equivalent full description.；Realize every type in the described class by an actual finite simplicial K, distinguished vertex v, and subcomplex B satisfying both original assumptions. The two-cone suspension with B a single edge is sufficient.；Give and prove a necessary-and-sufficient, finitely checkable contractibility criterion using only the specified local incidence data. The reference criterion is vanishing of all reduced integral homology of the link; justify its sufficiency with the actual suspension and CW structure, and its necessity without adding restrictions.。

## S5 不提供子复形 B

判定：false。

不必。取 K 为两个孤立点 v,w，去 v 是一点，但 |K|为 S^0，非空空间的悬挂都路径连通，不能同伦等价。一般删除复形 D=K−v 仍由同一重心收缩可缩。如果 link L 非空，S1 及 K=D∪v*L 给 |K|≃Σ|L|；如果 L 空，v 孤立，K=D⊔{v}，故同伦型恰 S^0。两点例实现新增类型；其他类型由 S4 原实现给出。

判准：孤立顶点合法例；非空/空 link 两情况完整。

## S6 悬挂信息的逆向恢复

判定：false。

否。取有限展示 CW 复形 T，单一零胞腔，两个一胞腔 a,b，两二胞腔附着词 a³b^{−5}、(ab)²b^{−5}。边界矩阵为 ((3,2),(−5,−3))，行列式 1，故 T 连通且整数无约化同调。令 α=(1 2 3)、β=(1 4 3 2 5)，右至左复合时 αβ=(1 4)(2 5)，故两附着词映到恒等，而 α 非恒等；因此 π_1(T) 非平凡，T 不可缩。用有限 CW 的有限单纯同伦模型定理取 L_1≃T，L_2 为一点。ΣL_1 路径连通且由 van Kampen 单连通，悬挂同调全零；Hurewicz 的最小非零同伦群论证及 Whitehead 给它可缩，所以两悬挂等价，原空间因基本群不同不等价。有限单纯模型可由有限单纯逼近和映射柱逐个替换附着构成，未要求展示复形本身已是单纯复形。

判准：给出两个非空有限复形，核验其悬挂同伦等价而原复形不同伦等价；接受任何有效反例。
