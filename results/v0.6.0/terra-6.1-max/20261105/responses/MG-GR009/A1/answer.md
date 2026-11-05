以下用 \(K\) 表示测试用 profinite 空间，用 \(*\) 表示单点空间。有限联合满射族 \(\{K_i\to K\}\) 的有限不交并到 \(K\) 是从紧空间到 Hausdorff 空间的满射，因而是商映射；由此连续映射可沿覆盖唯一粘合。所以每个 \(h_T\) 确为层。空覆盖还说明任意层在 \(\varnothing\) 上恰有一个截面。

## S1　有限群的自由作用

令 \(S=T/\Gamma\)，赋予商拓扑。因为 \(T\) 紧 Hausdorff 且全不连通，它有 clopen 基。不同轨道是有限不交闭集；取包含一个轨道、避开另一个轨道的 clopen 集，再取其所有 \(\Gamma\)-平移的交，得到不变 clopen 分离集。同样，不变 clopen 集给出 \(S\) 的拓扑基。因此 \(S\) 是紧 Hausdorff 全不连通空间，即所需的 profinite 轨道空间。

事实上商映射 \(p:T\to S\) 有连续截面。对每个 \(t\in T\)，自由性和 clopen 基给出含 \(t\) 的 clopen 集 \(V\)，使 \(\{\gamma V\}_{\gamma\in\Gamma}\) 两两不交。于是
\[
p|_V:V\longrightarrow p(V)
\]
是到 clopen 集的同胚。这些 \(p(V)\) 覆盖紧空间 \(S\)，取有限子覆盖并细化成两两不交的 clopen 分割，即可将局部截面粘成连续截面 \(s:S\to T\)。空空间情形也成立。

由自由性，
\[
\Gamma\times S\longrightarrow T,\qquad (\gamma,z)\longmapsto \gamma s(z)
\]
是连续双射；其源紧、目标 Hausdorff，故是同胚。特别地，两个具有相同 \(S\)-坐标的 \(T\)-值截面，沿有限 clopen 覆盖局部相差一个群元素。因此 \(h_p:h_T\to h_S\) 是层中的 \(\Gamma\)-商：任意不变态射 \(h_T\to Y\) 唯一地经 \(h_S\) 分解。

对任意等变层 \(\pi:E\to h_T\)，令
\[
D=h_S\times_{h_T,s}E\longrightarrow h_S.
\]
利用上面的同胚，在 \(\gamma\)-分量上用 \(a_\gamma\) 得到
\[
h_T\times_{h_S}D\xrightarrow{\sim}E.
\]
若测试截面的 \(\gamma\) 坐标不是常数，就在相应有限 clopen 分割上定义并粘合。逆映射在 \(\gamma\)-分量上用 \(a_{\gamma^{-1}}\)。此同构在 \(h_T\) 上且等变，左侧作用只改变 \(h_T\) 坐标，故每个 \(E\) 都在 \(h_S\) 上实现。

## S2　有限集合上的纤维分类

把有限集合赋离散拓扑。对每个 \(T\)-轨道选代表 \(t\)，记 \(X_t\) 为 \(X\to T\) 在 \(t\) 上的纤维。则 \(X_t\) 是有限 \(\Gamma_t\)-集合，且
\[
X\cong\coprod_{[t]\in T/\Gamma}\Gamma\times_{\Gamma_t}X_t,
\qquad [g,x]\longmapsto gt.
\]
反之，任给这些有限 \(\Gamma_t\)-集合，上式构造一个有限等变 \(X\to T\)。态射也逐纤维分类：
\[
\operatorname{Hom}^{\Gamma}_{T}(X,X')
\cong
\prod_{[t]}\operatorname{Hom}_{\Gamma_t}(X_t,X'_t).
\]

**可实现性的充要条件是每个 \(\Gamma_t\) 在 \(X_t\) 上作用平凡。** 必要性来自：在只改变 \(h_T\) 坐标的作用中，固定 \(t\) 的群元素必须固定该点上的整个纤维。

反之，若稳定子作用均平凡，令 \(Y=X/\Gamma\)。自然映射
\[
X\longrightarrow T\times_{T/\Gamma}Y
\]
是双射：满射由轨道定义得到；若同一 \(X\)-轨道中的两点都位于 \(X_t\)，连接它们的群元素属于 \(\Gamma_t\)，故两点相同。因此
\[
h_X\cong h_T\times_{h_{T/\Gamma}}h_Y
\]
给出实现。

对于可实现对象，其在 \(h_T\) 上的等变自同构群，以及实现层在 \(h_{T/\Gamma}\) 上的自同构群，都是
\[
\boxed{\displaystyle\prod_{[t]\in T/\Gamma}\operatorname{Sym}(X_t)}.
\]
更一般地，不要求可实现时，前一个自同构群为
\[
\prod_{[t]}\operatorname{Aut}_{\Gamma_t}(X_t).
\]

## S3　一般层的完整下降

### 商、局部轨道关系与判据

对任意带 \(\Gamma\)-作用的层 \(F\)，令 \(F/\Gamma\) 为预层
\[
K\longmapsto F(K)/\Gamma
\]
的层化，商映射记为 \(r_F:F\to F/\Gamma\)。层化有如下局部描述：

* \(r_F\) 局部满射；
* 对 \(x,y\in F(K)\)，有 \(r_F(x)=r_F(y)\)，当且仅当存在有限覆盖 \(\{K_i\to K\}\) 和 \(\gamma_i\in\Gamma\)，使
  \[
  y|_{K_i}=a_{\gamma_i}(x|_{K_i})\quad\text{对每个 }i.
  \]

这是层化的局部代表及局部相等性质；本场址的覆盖及其复合都可取有限族，故这里确可使用有限覆盖。

取
\[
Q=H/\Gamma,\qquad q=r_H:H\to Q.
\]
按层化的泛性质，
\[
\operatorname{Hom}(Q,Y)\cong
\operatorname{Hom}(H,Y)^\Gamma
\]
对所有层 \(Y\) 自然成立。

一般不能把 \(Q\) 假定为可表示。例如 \(\mathbb Z\) 以平移作用于 \(T=\mathbb Z_3\)。整数在 \(\mathbb Z_3\) 中稠密，故从 \(T\) 到任意 Hausdorff 空间的不变连续映射都为常值；但由上述局部轨道描述及“非空 profinite 空间有点”，
\[
Q(*)\cong\mathbb Z_3/\mathbb Z
\]
不止一个元素。因此此 \(Q\) 不可表示为 profinite 空间的层。

现在令
\[
P=E/\Gamma\longrightarrow Q
\]
为由 \(\pi\) 诱导的映射，并定义规范等变映射
\[
c_E:E\longrightarrow H\times_Q P,\qquad
e\longmapsto(\pi(e),r_E(e)).
\]
它总是局部满射：给定右侧截面 \((t,z)\)，先局部将 \(z\) 提升为 \(e\)，再由 \(q(t)=q\pi(e)\) 局部选 \(\gamma\) 使 \(t=\gamma\pi(e)\)，此时 \(a_\gamma e\) 是所需提升。

以下条件等价：

1. \(E\) 在 \(Q\) 上实现；
2. \(c_E\) 是同构；
3. 对每个测试空间 \(K\)、\(e\in E(K)\) 和 \(\gamma\in\Gamma\)，
   \[
   \boxed{\quad \gamma\pi(e)=\pi(e)\ \Longrightarrow\ a_\gamma(e)=e. \quad}\tag{1}
   \]

证明如下。若 \(c_E\) 单，固定 \(\pi(e)\) 的 \(\gamma\) 使 \(e\) 与 \(a_\gamma e\) 在 \(c_E\) 下同像，故二者相等。反之，若 (1) 成立而 \(c_E(e)=c_E(e')\)，则局部有 \(e'=a_\gamma e\)，又 \(\pi(e')=\pi(e)\)，所以局部 \(e'=e\)，再由层的分离性得全局相等。故 (1) 等价于 \(c_E\) 单。局部满的层映射若又单，其局部逆在重叠处一致并可粘合，因此是同构。最后，任何只改变 \(H\) 坐标的实现都满足 (1)，而 \(c_E\) 同构本身就是一个实现。

也可把 (1) 写成固定子层上的条件。因为
\[
T^\gamma=\{t:\gamma t=t\}
\]
是 profinite 闭子空间，(1) 等价于每个 \(a_\gamma\) 在
\[
E\times_H h_{T^\gamma}
\]
上都是恒等态射。

### 所有实现及态射

写 \(\operatorname{Eq}(H)\) 表示 \(H\) 上等变层的范畴，定义
\[
\Phi_Q:\mathcal C/Q\longrightarrow\operatorname{Eq}(H),
\qquad D\longmapsto H\times_QD.
\]
对任意 \(F\in\operatorname{Eq}(H)\) 和 \(D\to Q\)，有自然双射
\[
\operatorname{Hom}_{\operatorname{Eq}(H)}(F,\Phi_Q(D))
\cong
\operatorname{Hom}_{\mathcal C/Q}(F/\Gamma,D).
\]
因为左侧态射除 \(F\to H\) 外，恰由一个在 \(Q\) 上的 \(\Gamma\)-不变映射 \(F\to D\) 决定。

并且规范映射
\[
(H\times_QD)/\Gamma\longrightarrow D
\]
是同构：它局部满射；映到同一 \(D\)-截面的两个截面，其 \(H\)-坐标局部相差群元素。故 \(\Phi_Q\) 全忠实，其本质像恰为满足 (1) 的对象，逆由 \(F\mapsto F/\Gamma\) 给出。

特别地，若 \(E\) 可实现，规范实现是 \(D=P=E/\Gamma\)。任何给定实现
\[
\theta:E\xrightarrow{\sim}H\times_QD
\]
唯一地给出 \(P\xrightarrow{\sim}D\)，且 \(\theta\) 是 \(c_E\) 经该同构得到的。两个可实现对象间的等变态射，恰由其商之间的 \(Q\)-上态射分类；固定 \(E\) 的带实现同构的实现范畴则是收缩群胚。

### 任意基底及拉回相容性

给任意 \(f:B\to Q\)，令
\[
H_B=H\times_QB.
\]
\(\Gamma\) 只作用于 \(H\) 坐标。由 \(q\) 的局部满射性及局部轨道关系，\(H_B/\Gamma\cong B\)。

于是同样的构造给出范畴等价
\[
\mathcal C/B
\;\simeq\;
\left\{\begin{array}{c}
H_B\text{ 上满足固定子条件的}\\
\Gamma\text{-等变层}
\end{array}\right\},
\qquad D\longmapsto H_B\times_BD,
\]
右侧取满子范畴，逆函子为取 \(\Gamma\)-商。

对 \(E_B=E\times_QB\)，有自然同构
\[
(E\times_QB)/\Gamma\cong (E/\Gamma)\times_QB. \tag{2}
\]
直接验证：右侧截面局部由 \(E\times_QB\) 提升；两个提升映到同一右侧截面，当且仅当它们的 \(B\) 坐标相同、\(E\) 坐标局部相差群元素。因此规范比较映射满足
\[
c_{E_B}\cong c_E\times_QB.
\]
所有实现及态射的上述分类因而与基底拉回相容；对进一步的任意 \(B'\to B\) 亦然。

具体地，\(E_B\) 在 \(B\) 上实现的充要条件是：对所有 \(K,e,b,\gamma\)，只要
\[
e\in E(K),\quad b\in B(K),\quad f(b)=q\pi(e),\quad
\gamma\pi(e)=\pi(e),
\]
就有 \(a_\gamma(e)=e\)。此时其规范实现层为 \((E/\Gamma)\times_QB\)。

## S4　单点上的检验

**结论：不一定。** 以下构造反例。

取 profinite 阿贝尔群
\[
A=\prod_{n\in\mathbb N}\mathbb F_3.
\]
令 \(\underline A\) 为以 \(A\) 的底层群为值的常值层，即
\[
\underline A(K)=\operatorname{LC}(K,A_{\mathrm{disc}}),
\]
并令 \(M=h_A/\underline A\) 为阿贝尔群层的商。它可由预层
\[
K\longmapsto
C(K,A)/\operatorname{LC}(K,A_{\mathrm{disc}})
\]
层化得到；常值层的上述描述成立，因为 profinite 空间到离散空间的连续映射像有限，且其纤维给出有限 clopen 分割。

首先 \(M(*)=0\)。任一全局截面局部有上述预层代表；覆盖 \(*\) 的有限族中有非空测试空间，取其中一点拉回，就得到该截面由
\[
C(*,A)/\operatorname{LC}(*,A_{\mathrm{disc}})=0
\]
中的元素代表。

但 \(M\) 非零。令 \(\alpha\in M(A)\) 是 \(\operatorname{id}_A:A\to A\) 的类。若 \(\alpha=0\)，则存在有限覆盖 \(\{u_i:K_i\to A\}\)，使每个 \(u_i\) 作为到 \(A_{\rm disc}\) 的映射局部常值。每个 \(K_i\) 紧，所以 \(u_i(K_i)\) 有限；有限个有限像不可能覆盖无限集 \(A\)，矛盾。故 \(\alpha\ne0\)。由于 \(3M=0\)，有 \(-\alpha\ne\alpha\)。

取 \(T=*\)，\(\Gamma=C_2\) 在 \(T\) 上平凡作用，在 \(E=M\) 上以取负作用。此时 \(Q=H=*\)，且 \(E(*)=\{0\}\)，所以题设单点条件成立；但取负并非恒等作用，故 \(E\) 不能在 \(Q\) 上实现。

## S5　局部满射的基底检验

**结论：必能实现；事实上在此假设下，拉回前后可实现性等价。**

“原来可实现 \(\Rightarrow\) 拉回后可实现”由 S3 的拉回相容性得到。反过来，假设 \(B\to Q\) 局部满射，且 \(E_B\) 在 \(B\) 上实现。

任取 \(e\in E(K)\) 和满足 \(\gamma\pi(e)=\pi(e)\) 的 \(\gamma\)。局部满射性给出有限覆盖 \(\{K_i\to K\}\) 和 \(b_i\in B(K_i)\)，使
\[
f(b_i)=q\pi(e)|_{K_i}.
\]
于是 \((e|_{K_i},b_i)\in E_B(K_i)\)，其在 \(H_B\) 中的基底截面被 \(\gamma\) 固定。由 \(E_B\) 的可实现性，\(\gamma\) 固定这些截面，因而
\[
a_\gamma(e)|_{K_i}=e|_{K_i}.
\]
层的分离性给出 \(a_\gamma(e)=e\)。这验证 S3 的条件 (1)，故 \(E\) 可实现。

注意这里不需要预选的 \(B\)-上实现层另行给出下降数据：S3 表明它必同构于规范层 \((E/\Gamma)\times_QB\)。

## S6　非空基底与全局结论

**结论：不一定。** 取 \(\Gamma=C_2=\{1,\sigma\}\)，令
\[
T=\{0,1\}
\]
带平凡作用。于是 \(Q=H=h_T\)。令
\[
X=\{a,b,c\},\qquad a\mapsto0,\quad b,c\mapsto1,
\]
其中 \(\sigma\) 固定 \(a\) 并交换 \(b,c\)。取 \(E=h_X\)。稳定子 \(\Gamma_1=\Gamma\) 非平凡地作用于 \(X_1=\{b,c\}\)，故由 S2，\(E\) 不可实现。

令非空可表示层 \(B=h_*\) 经点 \(0:*\to T\) 映到 \(Q\)。则
\[
H\times_QB\cong h_*,
\qquad E\times_QB\cong h_{\{a\}}\cong h_*,
\]
拉回后的作用平凡，故可在 \(B\) 上实现。此 \(B\to Q\) 并非局部满射：\(Q(*)\) 中的点 \(1\) 不能在覆盖 \(*\) 的非空成员上提升到 \(B\)。

由各阶段可整理出以下检验原则：

* **一般完整检验：** 对所有测试空间和所有截面检验 S3 的固定子条件 (1)；等价地，检验每个 \(a_\gamma\) 在 \(E\times_Hh_{T^\gamma}\) 上为恒等。
* **覆盖基底检验：** 对任意局部满射 \(B\to Q\)，拉回前后可实现性等价。同理，可在共同局部覆盖 \(Q\) 的一族基底上分别检验。
* **自由作用：** 若 \(\Gamma\) 在 \(T\) 上自由，则固定子条件自动成立，即使 \(\Gamma\) 无限也如此；不过无限群时商层未必可表示。有限群自由情形有 S1 中更具体的 profinite 商和截面。
* **单点何时足够：** 一般不够；但若额外知道每个 \(E(K)\to E(*)^{|K|}\) 都单射，则单点条件足够，因为可逐点应用条件后利用单射性。可表示层具有这种逐点分离性质。
* **非空不等于覆盖：** 单个非空可表示基底只可能看到商的一部分，不能代替局部满射检验。