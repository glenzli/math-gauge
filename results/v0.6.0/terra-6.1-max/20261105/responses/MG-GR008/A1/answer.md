以下记 \(\rho_{n,n}=1\)，并记
\[
\lambda_{n,m}=\rho_{n,m}^*:Q_n\longrightarrow Q_m\qquad(n\le m).
\]
实际记录的等价类记为 \([n,u]\)。

大小约定：若原塔的底集没有预先取在 \(U\) 中，可逐层选取同构 \(\phi_n:\mathbb Z^{r_n}\to P_n\)，并把塔换成相应的 \(U\) 内模型。记录 \([n,u]\mapsto[n,u\phi_n]\) 给出自然同构。因此下面在需要将 \(P_n\) 当作 \(\mathrm{Ab}_U\) 的对象时，可使用这些模型；保留原底集时，记录组仍是 \(V\) 中的群，且自然同构于 \(U\) 小模型。

## S1　实际记录与张量

记录相等是等价关系：传递性中，把见证两次相等的层取一个共同后继即可。加法定义为
\[
[n,u]+[m,v]=[r,u\rho_{n,r}+v\rho_{m,r}],\qquad r\ge n,m.
\]
再取共同后继可验证这与代表元和 \(r\) 的选择无关，并得到阿贝尔群。对群同态 \(g:A\to B\)，令
\[
F_P(g)[n,u]=[n,gu].
\]
这与记录相等及加法相容，并保持恒等和复合，所以 \(F_P\) 是良定义的群值函子。

对每个有限秩自由群 \(P_n\)，求值给出自然同构
\[
\alpha_{n,A}:Q_n\otimes A\xrightarrow{\sim}\operatorname{Hom}(P_n,A),
\qquad q\otimes a\longmapsto(p\mapsto q(p)a).
\]
选取有限基即可验证它是同构。这些同构与 \(\lambda_{n,m}\) 及预复合 \(\rho_{n,m}\) 相容。因此得到自然同构
\[
\Theta_A:M_P\otimes A\xrightarrow{\sim}F_P(A),\qquad
[n,q]\otimes a\longmapsto[n,p\mapsto q(p)a].
\]
这里若 \([n,q]\) 有不同的层代表元，取共同后继即可验证右边不变，故没有使用 \(Q_n\to M_P\) 的单射性。

更具体地，若 \(e_1,\ldots,e_d\) 是 \(P_n\) 的基，\(e_i^\vee\) 是对偶基，则逆映射为
\[
[n,u]\longmapsto\sum_{i=1}^d[n,e_i^\vee]\otimes u(e_i).
\]
它与换层相容，因为上述求值同构与塔过渡相容。

每个 \(Q_n\) 都是有限秩自由阿贝尔群，故至多可数；\(M_P\) 是可数多个 \(Q_n\) 的像之并，因而至多可数。它也无挠：若非零整数 \(k\) 满足 \(k[n,q]=0\)，则某个 \(m\ge n\) 上
\[
k\lambda_{n,m}(q)=0\quad\text{于 }Q_m.
\]
\(Q_m\) 无挠，故 \(\lambda_{n,m}(q)=0\)，从而 \([n,q]=0\)。

## S2　有限图表和变换

### 有限极限

\(F_P\) 保持终对象。对有限积，满射性由有限多个记录可以换到共同层得到；若两个积值记录在每个坐标上的像相等，则每个坐标各有一个见证层，取有限多个见证层的共同后继，便得到原记录相等。因此 \(F_P\) 保持有限积。

对 \(f,g:A\to B\)，设 \(E\to A\) 是等化子。若 \([n,u]\in F_P(A)\) 在 \(F_P(f),F_P(g)\) 下有相同像，则某个 \(m\ge n\) 上
\[
fu\rho_{n,m}=gu\rho_{n,m}.
\]
所以 \(u\rho_{n,m}:P_m\to A\) 经 \(E\) 唯一分解。反过来，两个 \(E\) 值记录若在 \(A\) 值记录中相等，由 \(E\to A\) 单射，它们在同一见证层作为 \(E\) 值映射也相等。故 \(F_P\) 保持等化子。有限积与等化子构成所有有限极限，因此 \(F_P\) 保持有限极限。

### 全部自然变换

由 S1，有阿贝尔群同构
\[
\boxed{\operatorname{Nat}(F_P,F_{P'})
      \cong \operatorname{Hom}_{\mathbb Z}(M_P,M_{P'}).}
\]
对应于 \(f:M_P\to M_{P'}\) 的分量是 \(f\otimes1_A\)。反之，任何自然变换在 \(\mathbb Z\) 上给出 \(f\)；对 \(a\in A\) 使用映射 \(\mathbb Z\to A,\ 1\mapsto a\)，自然性强迫
\[
m\otimes a\longmapsto f(m)\otimes a.
\]
这些纯张量生成，故没有其他变换；分量也确为群同态。

等价地，全部变换有以下实际记录描述。取各 \(n\) 的整数 \(k_n\) 和同态
\[
u_n:P'_{k_n}\longrightarrow P_n,
\]
要求对每个 \(n\le m\)，存在 \(s\ge k_n,k_m\)，使
\[
u_n\rho'_{k_n,s}
=\rho_{n,m}u_m\rho'_{k_m,s}. \tag{2.1}
\]
它定义
\[
\eta_A([n,h])=[k_n,hu_n]. \tag{2.2}
\]
条件 (2.1) 保证换层及加法良定义，自然性显然成立。

此描述没有遗漏：给定 \(\eta\)，取
\[
\eta_{P_n}([n,1_{P_n}])=[k_n,u_n].
\]
自然性给出 (2.2)，而 \([n,1_{P_n}]=[m,\rho_{n,m}]\) 给出 (2.1)。两族 \((k_n,u_n)\)、\((\ell_n,v_n)\) 给出同一变换，当且仅当对每个 \(n\)，存在 \(s\ge k_n,\ell_n\) 使
\[
u_n\rho'_{k_n,s}=v_n\rho'_{\ell_n,s}.
\]
对应的 \(M_P\to M_{P'}\) 为
\[
[n,q]\longmapsto[k_n,qu_n].
\]

恒等变换可取 \(k_n=n,\ u_n=1_{P_n}\)。若从 \(P'\) 到 \(P''\) 的变换由
\(v_j:P''_{\ell_j}\to P'_j\) 给出，则复合由
\[
P''_{\ell_{k_n}}\xrightarrow{\,v_{k_n}\,}P'_{k_n}
\xrightarrow{\,u_n\,}P_n
\]
给出。在 \(M\) 的描述中，恒等和复合就是群同态的恒等和复合。

## S3　完整表示分类

考虑只由塔的有限层映射表述的条件
\[
\boxed{\exists n\ \forall m\ge n\ \exists r\ge m:\quad
\operatorname{im}\lambda_{n,r}
=\operatorname{im}\lambda_{m,r}\subseteq Q_r.}\tag{C}
\]
对每个固定的 \(n,m,r\)，这是有限个整数矩阵的像是否相等的问题；条件本身没有引用表示对象或待分类的函子。

**结论：**以下三项等价：

1. 条件 (C) 成立；
2. \(F_P\) 由某个普通对象 \(R\in\mathrm{Ab}_U\) 表示；
3. \(F_P\) 保持所有指标范畴的对象集和箭头集均可数的小图表极限。

而且这些条件也等价于 \(M_P\) 有限生成。

### 表示性与有限生成

若 \(M_P\) 有限生成，由 S1 它无挠，所以由整数环上有限生成阿贝尔群分类，它是有限秩自由群。令
\[
R=M_P^*=\operatorname{Hom}(M_P,\mathbb Z).
\]
有限自由性保证求值映射
\[
M_P\otimes A\xrightarrow{\sim}\operatorname{Hom}(M_P^*,A),\qquad
m\otimes a\longmapsto(\ell\mapsto\ell(m)a)
\]
自然同构；选基即可验证。因此 \(R\) 表示 \(F_P\)。

反之，假设有自然同构
\[
\theta_A:\operatorname{Hom}(R,A)\xrightarrow{\sim}M_P\otimes A.
\]
写
\[
\theta_R(1_R)=\sum_{i=1}^s m_i\otimes r_i.
\]
对于任意 \(\ell:R\to\mathbb Z\)，自然性给出
\[
\theta_{\mathbb Z}(\ell)
=\sum_{i=1}^s \ell(r_i)m_i.
\]
由于 \(\theta_{\mathbb Z}\) 满射到 \(M_P\otimes\mathbb Z\cong M_P\)，这些 \(m_i\) 生成 \(M_P\)。故表示性等价于 \(M_P\) 有限生成。

### 条件 (C) 与有限生成

若 \(M_P\) 有限生成，可将有限多个生成元换到共同层，故存在 \(n\) 使 \(Q_n\to M_P\) 满射。固定 \(m\ge n\)，对 \(Q_m\) 的有限基中每个元素，选一个具有相同极限像的 \(Q_n\) 元素；把有限多个相等的见证层取共同后继 \(r\)，便得到
\(\operatorname{im}\lambda_{m,r}\subseteq\operatorname{im}\lambda_{n,r}\)。反向包含由
\(\lambda_{n,r}=\lambda_{m,r}\lambda_{n,m}\) 自动成立，故有 (C)。

反之，若 (C) 成立，任意 \(Q_m\) 的元素都可换层到 \(Q_n\) 的某个元素：当 \(m\ge n\) 时由像相等得到，当 \(m<n\) 时先换到 \(n\)。所以 \(Q_n\to M_P\) 满射，\(M_P\) 有限生成。

### 全部表示对象的构造

取满足 (C) 的 \(n\)，令
\[
K_n=\bigcup_{r\ge n}\ker\lambda_{n,r}.
\]
这些核递增。由于 \(Q_n\) 是有限生成整数模，而 \(\mathbb Z\) 是 Noether 环，该递增链在某个 \(t\ge n\) 稳定。令
\[
B=\operatorname{im}\lambda_{n,t}\subseteq Q_t.
\]
则
\[
M_P\cong Q_n/K_n\cong B.
\]
\(B\) 是有限秩自由群的子群，因此也是有限秩自由群。于是 \(B^*\) 是一个由塔构造的表示对象；若 \(r=\operatorname{rank}B\)，它同构于 \(\mathbb Z^r\)。

按协变表示函子的 Yoneda 对应，任何其他表示 \(F_P\) 的对象都与 \(B^*\) 同构；反之，任何与 \(B^*\) 同构的对象都表示 \(F_P\)。因此这给出了**全部表示对象到同构**，包括 \(r=0\) 的零对象情形。

### 可数图表极限

若 \(M_P\) 有限生成，则上面已证明 \(F_P\) 可表示。表示函子由极限的泛性质保持所有存在的小极限；当前 \(U\)-小图表的极限存在于 \(\mathrm{Ab}_U\)，故尤其保持题述可数图表极限。

反之，只需考察以 \(\mathbb N\) 为离散指标的积。典范比较为
\[
M_P\otimes\mathbb Z^{\mathbb N}\longrightarrow M_P^{\mathbb N}.
\]
其任一像序列的所有项都落在 \(M_P\) 的某个有限生成子群中：对原像的有限张量和
\(\sum_{i=1}^s m_i\otimes(a_{ij})_j\)，该子群可取 \(\langle m_1,\ldots,m_s\rangle\)。

由 S1，\(M_P\) 至多可数；取一个列出它所有元素的序列。若比较映射满射，该序列落在某个有限生成子群中，故 \(M_P\) 本身有限生成。因此可数积保持性已迫使 (C)，从而两种分类完全相同。

这也与 S2 一致：当两塔均可表示时，令 \(R=M_P^*\)、\(R'={M_{P'}}^*\)。S2 的
\(f:M_P\to M_{P'}\) 对应于对偶映射
\[
f^*:R'\longrightarrow R,
\]
所给自然变换正是 \(h:R\to A\mapsto h f'\!{}^*:R'\to A\)，即预复合 \(f^*\)。恒等与复合也相应对偶。

## S4　秩一塔

秩恒为 \(1\) **不保证**可表示：例如所有 \(a_n=2\) 时，
\[
M_P\cong\mathbb Z[1/2]
\]
不是有限生成群，所以由 S3 不可表示。

完整判据是
\[
\boxed{F_P\text{ 可表示}\iff
\bigl(a_n=0\text{ 有无穷多个}\bigr)
\ \text{或}\ 
\bigl(a_n\in\{1,-1\}\text{ 最终恒成立}\bigr).}
\]

证明如下。

* 若有无穷多个零，则每个记录在某个后继层变为零，故 \(F_P=0\)，由零群表示。
* 否则选 \(N\)，使 \(n\ge N\) 时 \(a_n\ne0\)。令
  \[
  d_N=1,\qquad d_n=\prod_{i=N}^{n-1}a_i.
  \]
  通过 \([n,k]\mapsto k/d_n\)，得到
  \[
  M_P\cong\bigcup_{n\ge N}d_n^{-1}\mathbb Z\subseteq\mathbb Q.
  \]
  若最终所有 \(a_n=\pm1\)，此并最终稳定，\(M_P\cong\mathbb Z\)，由 \(\mathbb Z\) 表示。
  若有无穷多个 \(|a_n|\ge2\)，则 \(|d_n|\) 无界。任意有限多个元素都落在某个 \(d_k^{-1}\mathbb Z\) 中，但更后面的某个 \(d_n^{-1}\) 不在该子群中；故 \(M_P\) 不有限生成，由 S3 不可表示。

## S5　稳定像中的延拓

**不是每个 \(I_n\) 都必为 \(P_n\) 的直和项。**例如取所有 \(P_n=\mathbb Z\)，令 \(\rho_0\) 乘 \(2\)，其余 \(\rho_n\) 均为恒等。取 \(n_0=0\)，则
\[
I_0=2\mathbb Z,\qquad I_n=\mathbb Z\quad(n\ge1),
\]
所有指定的限制映射都是同构，但 \(2\mathbb Z\) 不是 \(\mathbb Z\) 的直和项。

下面构造所需的后层回缩。对 \(n\ge n_0\)，由假设的逐层同构，限制映射
\[
\sigma_n=\rho_{n_0,n}|_{I_n}:I_n\xrightarrow{\sim}I_{n_0}
\]
是同构。取 \(m\ge n_0\) 使
\(\operatorname{im}\rho_{n_0,m}=I_{n_0}\)，定义
\[
r_m:P_m\xrightarrow{\rho_{n_0,m}}I_{n_0}
\xrightarrow{\sigma_m^{-1}}I_m.
\]
它在 \(I_m\) 上是恒等，故为回缩。

对 \(n\ge n_0\) 的记录，定义
\[
\Phi_A([n,u])=u|_{I_n}\,\sigma_n^{-1}:I_{n_0}\longrightarrow A.
\]
若 \(n<n_0\)，先把记录换到 \(n_0\)。逐层限制同构表明换层不改变此映射，所以 \(\Phi_A\) 良定义、加性且对 \(A\) 自然。

它是满射：对 \(f:I_{n_0}\to A\)，上面的回缩给出记录
\[
[m,f\sigma_m r_m],
\]
其像为 \(f\)。

它也是单射：若两个记录的像相同，先将它们换到共同层 \(j\ge n_0\)，记为 \([j,u]\)、\([j,v]\)。此时 \(u-v\) 在 \(I_j\) 上为零。取 \(t\ge j\) 使 \(\operatorname{im}\rho_{j,t}=I_j\)，便有
\[
u\rho_{j,t}=v\rho_{j,t},
\]
即原记录相等。因此实际记录给出自然同构
\[
\boxed{F_P\cong\operatorname{Hom}(I_{n_0},-).}
\]

## S6　具体变换与无限积

当所有 \(a_n=2\) 时，
\[
M_P=\mathbb Z[1/2],\qquad F_P(A)\cong\mathbb Z[1/2]\otimes A.
\]
由 S2，
\[
\operatorname{End}(F_P)
\cong\operatorname{End}_{\mathbb Z}(\mathbb Z[1/2])
\cong\mathbb Z[1/2].
\]
最后一个同构把自同态送到 \(1\) 的像：该像唯一决定所有 \(1/2^n\) 的像，而任意 \(r\in\mathbb Z[1/2]\) 都可作为乘法自同态。复合对应乘法。其可逆元恰为
\[
\boxed{\operatorname{Aut}(F_P)=\{\text{乘以 }\pm2^k:k\in\mathbb Z\}.}
\]

更具体地，若 \(r=p/2^k\)，其中 \(p\in\mathbb Z,\ k\ge0\)，对应变换在记录上为
\[
[n,a]\longmapsto[n+k,pa].
\]

典范比较
\[
F_P(\mathbb Z^{\mathbb N})\longrightarrow F_P(\mathbb Z)^{\mathbb N}
=\mathbb Z[1/2]^{\mathbb N}
\]
把记录 \([n,(a_j)_j]\) 送到 \((a_j/2^n)_j\)。因此其像恰是分母所需的 \(2\) 的幂有统一上界的序列。具体元素
\[
(1,1/2,1/4,1/8,\ldots)
\]
不在像中，故比较不满射。这与 S2 不矛盾：S2 只断言保持**有限**极限，而这里使用了可数无限积。