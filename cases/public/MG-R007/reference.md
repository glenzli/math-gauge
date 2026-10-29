# 参考审核：对称提升的逐层相容实现

主目标成立。逐层分裂的存在性是本题的实际前提；困难转为如何使一整族分裂相容。证明不用除以 $|G|$，也不假设任一过渡映射满射。

## 1. 各层的全部分裂

记

$$S_n=\{s\in\operatorname{Hom}_{k[G]}(C,B_n):q_ns=I_C\},\qquad
W_n=\operatorname{Hom}_{k[G]}(C,A_n).$$

题设保证 $S_n\ne\varnothing$。任意两个元素 $s,t\in S_n$ 的差满足 $q_n(t-s)=0$，由 $\ker q_n=\operatorname{im}i_n$ 和 $i_n$ 单射，唯一写成

$$t-s=i_nu,\qquad u\in W_n.$$

其中 $u$ 线性且等变：对任意 $g\in G,c\in C$，将所需的等式经 $i_n$ 映射后，分别由 $t-s$ 的线性与等变性成立，再用 $i_n$ 单射。反之任意 $u\in W_n$ 都给出另一个分裂 $s+i_nu$。因此 $S_n$ 是以有限维空间 $W_n$ 为方向空间的非空仿射空间。

定义

$$T_n:S_{n+1}\to S_n,\quad s\longmapsto\beta_ns,\qquad
L_n:W_{n+1}\to W_n,\quad u\longmapsto\alpha_nu.$$

这些映射良定，因为 $q_n\beta_ns=q_{n+1}s=I_C$，且所有映射等变。交换关系给出

$$T_n(s+i_{n+1}u)=T_n(s)+i_nL_n(u),$$

所以 $T_n$ 为仿射映射。这里尚未声称它满射；满射性可能失败。

## 2. 有限维仿射塔的相容点

我们直接证明所需逆极限事实。设 $(S_n,T_n)$ 是可数的非空有限维仿射空间塔，过渡映射均仿射。对 $m\ge n$，记 $T_{m,n}:S_m\to S_n$ 为复合，$T_{n,n}=I$，并令

$$I_{m,n}=T_{m,n}(S_m).$$

固定 $n$ 后，这些是 $S_n$ 中的非空仿射子空间，且

$$I_{m+1,n}\subset I_{m,n}.$$

一个严格包含的非空有限维仿射子空间有严格较小的维数：将两者平移到其共同一点，便成为线性子空间的相应事实。因此这个下降链最终稳定。记其稳定值为 $I_n$；等价地，$I_n=\bigcap_{m\ge n}I_{m,n}$，且 $I_n\ne\varnothing$。

现在证明 $T_n:I_{n+1}\to I_n$ 满射。先取 $y\in I_{n+1}$。对每个 $m\ge n+1$，$y$ 在 $T_{m,n+1}$ 的像中，所以 $T_ny$ 在 $T_{m,n}$ 的像中；故 $T_ny\in I_n$。反向取 $x\in I_n$，选择足够大的 $m$，使 $I_{m,n}=I_n$ 且 $I_{m,n+1}=I_{n+1}$。存在 $z\in S_m$ 使 $T_{m,n}z=x$。令 $y=T_{m,n+1}z$，则 $y\in I_{n+1}$ 且 $T_ny=x$。

任选 $s_1\in I_1$，再逐次在 $I_{n+1}$ 中选取 $s_{n+1}$ 使 $T_ns_{n+1}=s_n$。这样得到相容点 $(s_n)\in\varprojlim S_n$。这是通常经典数学意义下的存在性构造；它不宣称有效计算统一的稳定阶段，也不产生不依赖选择的首选点。

将这一论证用于第 1 节的分裂空间，便得到题目要求的等变相容分裂。

## 3. 极限中的直和分解

由 $q_n\beta_n=q_{n+1}$，每个 $(b_n)\in B_\infty$ 的 $q_n(b_n)$ 都等于 $q_1(b_1)$，所以 $q_\infty$ 正是共同的商记录，且为等变线性映射。

对刚得到的相容分裂定义

$$s_\infty:C\to B_\infty,\qquad s_\infty(c)=(s_n(c))_n.$$

相容性保证其值在 $B_\infty$，各坐标保证它线性、等变，且 $q_\infty s_\infty=I_C$。

$i_\infty$ 单射，因为各 $i_n$ 单射。若 $b=(b_n)\in\ker q_\infty$，每个 $b_n$ 唯一写成 $i_n(a_n)$。由

$$i_n(a_n)=b_n=\beta_n b_{n+1}=i_n\alpha_n(a_{n+1})$$

及 $i_n$ 单射，得 $a_n=\alpha_n(a_{n+1})$。所以 $\ker q_\infty=\operatorname{im}i_\infty$。于是

$$\Phi:A_\infty\oplus C\longrightarrow B_\infty,\qquad
\Phi(a,c)=i_\infty(a)+s_\infty(c)$$

是等变线性同构。确切地，对 $b\in B_\infty$，先令 $c=q_\infty b$，再将 $b-s_\infty c$ 唯一写成 $i_\infty(a)$，就给出逆映射。此公式同时证明与所要求的包含及投影相容。

## 4. 全部选择及整塔同构

对两个相容分裂族 $s=(s_n)$、$t=(t_n)$，第 1 节给出唯一的 $u_n\in W_n$ 使 $t_n=s_n+i_nu_n$。相容性等价于

$$i_nu_n=i_n\alpha_nu_{n+1},\quad\text{即}\quad u_n=\alpha_nu_{n+1}.$$

反之每个这样的相容 $u$ 都产生一个相容分裂族。因此全部相容分裂是非空的仿射空间，其平移空间为

$$W_\infty=\varprojlim\operatorname{Hom}_{k[G]}(C,A_n)
\cong\operatorname{Hom}_{k[G]}(C,A_\infty).\tag{1}$$

式 (1) 的同构不借助额外的交换定理：将 $(u_n)$ 送到 $c\mapsto(u_n(c))_n$，逆向则取每个坐标，直接互逆。选定一个相容分裂后可把整个解空间与 $W_\infty$ 识别，但解空间本身并未携带首选零点。

同样，任一等变分裂 $s_\infty:C\to B_\infty$ 都由坐标给出题目要求的相容族，故这里没有遗漏极限层的分裂。任意满足题面包含、投影条件的直和同构，也唯一由它在 $(0,c)$ 上的值给出相应分裂，因而得到同一分类。

精确地，设另一塔有 $A'_n,B'_n,C'$，并有等变线性同构 $a_n:A_n\to A'_n$、$b_n:B_n\to B'_n$ 和 $d:C\to C'$，满足

$$b_ni_n=i'_na_n,\quad q'_nb_n=dq_n,\quad
a_n\alpha_n=\alpha'_na_{n+1},\quad
b_n\beta_n=\beta'_nb_{n+1}.$$

则

$$s_n\longmapsto b_ns_nd^{-1},\qquad
u_n\longmapsto a_nu_nd^{-1}$$

分别给出相容分裂族和相容平移空间的同构。代入上面的四个交换关系，逐项即得分裂、相容及平移公式；例如

$$\beta'_n(b_{n+1}s_{n+1}d^{-1})
=b_n\beta_ns_{n+1}d^{-1}=b_ns_nd^{-1}.$$

反向用 $a_n^{-1},b_n^{-1},d^{-1}$，故这些映射为双射。它们与恒等同构及同构的复合相容，证明解空间与其自由度在题目规定的意义下自然。这里自然的是整个解空间及其运输；没有声称第 2 节的任意选择给出自然首选分裂。

## 5. 说明每项结构所起的作用

以下见证用于审稿，题面不预先提示它们，也不要求候选重复。

**过渡满射不是题设，且不由其他条件推出。** 取平凡 $G$、$A_n=k$、$B_n=k\oplus k$、$C=k$，$i_n(a)=(a,0)$、$q_n(a,c)=c$，并设 $\alpha_n=0$、$\beta_n(a,c)=(0,c)$。每行等变分裂，所有交换关系成立，但 $\alpha_n,\beta_n$ 均不满射。分裂的参数 $t\in k$ 由 $s_t(c)=(tc,c)$ 表示，$T_n$ 将所有参数送到零；本题构造仍有效。

**不能用有限群平均替代已给的局部分裂假设。** 若删去每行等变分裂的前提，取 $\operatorname{char}k=p$、$G=C_p$，在 $B=k e_1\oplus k e_2$ 上令生成元满足 $\sigma e_1=e_1$、$\sigma e_2=e_2+e_1$。$A=k e_1$ 和 $C=B/A\cong k$ 均为平凡表示。因为 $N(e_2)=e_1,N(e_1)=0$ 满足 $N^2=0$，$(I+N)^p=I$，所以这确为表示。任何线性分裂把 $1$ 送到 $e_2+te_1$，其 $\sigma$ 作用之差恒为 $e_1$，故没有等变分裂。把这一行和恒等过渡重复成塔即得反例。它不满足新版题设，不能作为新版主目标的反例。

**有限维稳定具有实际内容。** 若允许无限维，取平凡 $G$、$C=k$、$A_n=k[t]$、$B_n=k[t]\oplus k$，令 $i_n(a)=(a,0)$、$q_n(a,c)=c$，并令

$$\alpha_n(a)=ta,\qquad\beta_n(a,c)=(ta+c,c).$$

每行都有分裂且图表交换。一个相容分裂族必形如 $s_n(c)=(a_n c,c)$，其中 $a_n\in k[t]$ 满足 $a_n=ta_{n+1}+1$。迭代给出

$$a_1=1+t+\cdots+t^{m-1}+t^m a_{m+1}$$

对每个 $m\ge1$ 成立。取 $m>\deg a_1+1$，比较次数为 $m-1$ 的系数，左侧为零、右侧为一，矛盾；若 $a_1=0$，常数项已矛盾。因此没有相容分裂。这个见证只表明有限维条件不能任意删除，不主张有限维是所有具体塔可解的必要条件。

**不要求自然首选。** 取上述每层 $k\oplus k$ 的平凡表示，但所有过渡取恒等。每个 $s_t(c)=(tc,c)$ 都给出一个相容族。整塔自同构 $b_v(a,c)=(a+vc,c)$、两端恒等，将 $s_t$ 送到 $s_{t+v}$。取 $v\ne0$，没有任何族被该自同构固定，所以对所有这些未指定首选分裂的塔，不存在对全部图表同构自然的首选族。这不妨碍解空间本身的自然运输，也不妨碍选择某个族来得到直和同构。

当 $C=0$ 时每个分裂唯一为零；当所有 $A_n=0$ 时每个 $q_n$ 是等变同构，分裂唯一且由交换关系相容。第 1–4 节的证明同时覆盖这些情形。

## 来源与审核范围

逆极限的稳定像背景核对于 [Stacks 02N1](https://stacks.math.columbia.edu/tag/02N1)和 [Stacks 03CA](https://stacks.math.columbia.edu/tag/03CA)。本稿直接证明了有限维仿射塔的稳定、稳定像间的满射及相容选择，没有把非空有限维空间误作有限集合或紧空间。

旧版的局部分裂障碍采用 [Stanford Math 210B 群上同调讲义](https://math.stanford.edu/~conrad/210BPage/handouts/GroupCohomology.pdf)的公开背景；新版保留等变分裂的数学语境，但不要求上同调记号或余核路线。全部题面、证明及见证为独立编排，未使用未公开 OET 材料。

本稿是新数据与新目标的参考证明。AI 独立数学审核、人工审定、模型校准和形式化证据分别以本题 review.json 及其引用记录为准；旧版单列障碍问题的审核不能直接继承为本版通过。证明完整或采用较长参考稿本身都不构成难度校准。
