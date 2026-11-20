## S1　有限群的自由作用

令 \(S=T/\Gamma\) 为轨道集，赋予商拓扑，记商映射为 \(p:T\to S\)。这是 \(U\)-小紧空间。紧 Hausdorff 全不连通空间有开闭基，因此对两个不同的有限轨道，可以取包含第一个轨道且避开第二个轨道的开闭集。它的所有 \(\Gamma\)-平移之并仍是开闭集，且是饱和的。于是 \(S\) 中任意两点可由开闭集分开，故 \(S\) 是 profinite 空间。

自由性给出一个连续截面 \(\sigma:S\to T\)。事实上，对每个 \(t\in T\)，各点 \(\gamma t\) 互异，可为它们选取两两不交的开闭邻域 \(V_\gamma\)。令
\[
W=\bigcap_{\gamma\in\Gamma}\gamma^{-1}V_\gamma .
\]
则 \(W\) 是 \(t\) 的开闭邻域，各 \(\gamma W\) 两两不交。因为 \(p^{-1}p(W)=\bigcup_\gamma\gamma W\) 开闭，\(p(W)\) 也开闭，且 \(p|_W:W\to p(W)\) 是紧空间到 Hausdorff 空间的连续双射，因而是同胚。这些 \(p(W)\) 有有限子覆盖，将其细化为不交开闭分割，逐块取逆即得 \(\sigma\)。由此得到等变同胚
\[
\Gamma\times S\xrightarrow{\sim}T,\qquad (\gamma,s)\longmapsto\gamma\sigma(s).
\]

可表示预层确实是层。对有限联合满射覆盖 \((P_i\to P)\)，映射 \(\coprod_iP_i\to P\) 是紧空间到 Hausdorff 空间的商映射，所以相容的连续映射唯一粘合为连续映射。对任意层 \(Y\)，有限不交开闭分割上的层条件又给出各分块取值的乘积，因为 \(Y(\varnothing)\) 是单点。因此上面的同胚给出层的余积 \(H\simeq\coprod_{\gamma\in\Gamma}h_S\)。一个 \(H\to Y\) 的态射是 \(\Gamma\)-不变的，当且仅当它在这些分量上给出同一个 \(h_S\to Y\)。这证明 \(h_p:H\to h_S\) 是层商。

给定等变层 \(\pi:E\to H\)，取 \(D=h_\sigma^*E\to h_S\)。在 \(H\) 的第 \(\gamma\) 个分量上，\(a_\gamma\) 将 \(D\) 同构到 \(E\) 在该分量上的限制，逆映射由 \(a_{\gamma^{-1}}\) 给出。逐块粘合得到
\[
H\times_{h_S}D\xrightarrow{\sim}E.
\]
由 \(a_\delta a_\gamma=a_{\delta\gamma}\)，此同构等变，左侧的作用只改变 \(H\) 坐标。空空间的情形由空分割和空覆盖的层条件一并涵盖。

## S2　有限集合上的纤维分类

每个轨道选一个代表 \(t\)，记 \(X_t\) 为 \(t\) 上的纤维。取纤维给出范畴等价
\[
\{\text{有限 \(\Gamma\)-集合等变地映到 \(T\)}\}
\simeq \prod_{[t]\in T/\Gamma}\{\text{有限 \(\Gamma_t\)-集合}\}.
\]
具体地，从一族有限 \(\Gamma_t\)-集合 \(F_t\) 重建
\[
\bigsqcup_{[t]\in T/\Gamma}\Gamma\times_{\Gamma_t}F_t
   \longrightarrow T,\qquad [g,u]\longmapsto gt,
\]
其中 \((gk,u)\sim(g,ku)\)。取 \(F_t=X_t\) 时，\([g,u]\mapsto gu\) 是到 \(X\) 的等变双射。态射恰由各纤维上的 \(\Gamma_t\)-等变映射 \(f_t\) 给出，重建后的公式为 \([g,u]\mapsto[g,f_t(u)]\)。

**\(h_X\) 可在 \(Q=h_{T/\Gamma}\) 上实现，当且仅当每个 \(\Gamma_t\) 在 \(X_t\) 上作用平凡。** 必要性可在单点上检验。若 \(h_X\simeq H\times_QD\)，则对 \((t,d)\)，每个 \(k\in\Gamma_t\) 都固定两个坐标。反之，若各稳定子作用平凡，则每个 \(X\)-轨道与其像轨道中每一点的纤维恰交于一点。因此
\[
X\longrightarrow T\times_{T/\Gamma}(X/\Gamma),\qquad x\longmapsto(\pi(x),[x])
\]
是等变双射，取 \(D=h_{X/\Gamma}\) 即可。由纤维分类及 Yoneda 引理，可实现对象在 \(H\) 上的等变自同构群为
\[
\prod_{[t]\in T/\Gamma}\operatorname{Sym}(X_t).
\]

## S3　一般层的完整下降

对带 \(\Gamma\)-作用的层 \(F\)，定义其轨道层及典范映射
\[
\mathcal O(F)=\bigl(P\longmapsto F(P)/\Gamma\bigr)^\#,\qquad
\rho_F:F\longrightarrow\mathcal O(F),
\]
其中 \({}^\#\) 表示层化。由 \(U\in V\)，站点可在 \(V\) 内取小骨架，此层化可在 \(\mathrm{Set}_V\) 中进行。取 \(Q=\mathcal O(H)\)、\(q=\rho_H\)。逐截面取轨道的泛性质与层化的伴随性给出自然双射
\[
\operatorname{Hom}(Q,Y)\xrightarrow[\ \circ q\ ]{\sim}
\operatorname{Hom}(H,Y)^\Gamma .
\]

层化给出两个局部事实。第一，\(\rho_F\) 局部满射。第二，对 \(u,v\in F(P)\)，有
\[
\rho_F(u)=\rho_F(v)
\quad\Longleftrightarrow\quad
\text{存在有限覆盖 }(P_i\to P)\text{ 及 }\gamma_i\in\Gamma,\quad
v|_{P_i}=a_{\gamma_i}(u|_{P_i}).
\tag{1}
\]
这是因为层化中的截面局部来自原预层，两个原预层截面在层化中相等当且仅当它们局部相等。此处覆盖对拉回和复合封闭，所需细化仍是有限覆盖。特别地，若一个不变态射 \(F\to Z\) 局部满射，且同像截面总是局部相差群元素，则 \(\mathcal O(F)\to Z\) 是同构。它局部满射，而将轨道层的两个截面在共同覆盖上提升到 \(F\) 后，(1) 给出单射性。对层而言，单射且局部满射的态射是同构，因为局部原像唯一，故能粘合。

**可实现性判据**是对每个测试空间 \(P\)、每个 \(e\in E(P)\) 和每个 \(\gamma\in\Gamma\)，都有
\[
\gamma\pi(e)=\pi(e)\quad\Longrightarrow\quad a_\gamma(e)=e.
\tag{2}
\]
满足时，典范实现为 \(D=\mathcal O(E)\to Q\)，其结构映射由 \(q\pi\) 诱导。

下面在任意基底上证明此判据及分类。给定 \(B\to Q\)，记 \(H_B=H\times_Q B\)，令 \(q_B:H_B\to B\) 为投影。\(\Gamma\) 只作用于 \(H\) 坐标。因为 \(q\) 局部满射，\(q_B\) 也局部满射。\(H_B(P)\) 中两个有相同 \(B\) 坐标的截面，其 \(H\) 坐标在 \(Q(P)\) 中相等，由 (1) 局部相差群元素。因此 \(\mathcal O(H_B)\simeq B\)。

对 \(H_B\) 上的等变对象 \(p:F\to H_B\)，令 \(D_F=\mathcal O(F)\to B\)，考虑典范等变态射
\[
k_F:F\longrightarrow H_B\times_BD_F,\qquad e\longmapsto(p(e),\rho_F(e)).
\]
它总是局部满射。给定右侧截面 \((x,d)\)，局部提升 \(d\) 为 \(e\)。于是 \(p(e)\) 与 \(x\) 有相同的 \(B\) 坐标，再细化覆盖即可写成 \(x=\gamma p(e)\)。此时 \(a_\gamma(e)\) 提升 \((x,d)\)。

若 \(F\) 满足以 \(p\) 代替 \(\pi\) 的 (2)，则 \(k_F\) 也是单射。事实上，若 \(k_F(e)=k_F(e')\)，则 \(p(e)=p(e')\)，且由 (1)，局部有 \(e'=a_\gamma(e)\)。这个 \(\gamma\) 固定共同的底截面，故由 (2) 得 \(e'=e\) 局部成立，再由层的分离性得全局相等。因此 \(k_F\) 是同构。反过来，在任何实现 \(H_B\times_BD\) 中，固定底截面就固定整个截面，所以 (2) 必要。取 \(B=Q\) 即得原判据。

由此有范畴等价
\[
\mathbf C/B\ \simeq\
\{\,H_B\text{ 上满足 (2) 的等变对象及其全部等变态射}\,\},
\qquad
D\longmapsto q_B^*D,\quad F\longmapsto D_F .
\tag{3}
\]
具体地，对任意 \(D\to B\)，投影 \(q_B^*D\to D\) 局部满射，同像截面局部相差群元素，故 \(\mathcal O(q_B^*D)\simeq D\)。在态射上，一个 \(F\to q_B^*D\) 的底坐标已经由 \(p\) 确定，另一坐标恰是 \(B\) 上的不变态射 \(F\to D\)，因而唯一对应于 \(D_F\to D\)。这也分类了固定 \(F\) 的所有实现。若 \(F\) 可实现，指定一个实现同构 \(F\xrightarrow{\sim}q_B^*D\)，等价于指定一个 \(B\) 上的同构 \(D_F\xrightarrow{\sim}D\)。任意两个带此指定的实现之间有唯一相容同构。

最后，对任意 \(Q\) 上的态射 \(B'\to B\)，有自然同构
\[
\mathcal O(F\times_B B')\ \simeq\ \mathcal O(F)\times_B B'.
\tag{4}
\]
事实上，\(F\times_B B'\to\mathcal O(F)\times_B B'\) 是 \(\rho_F\) 的拉回，故局部满射。同像截面的 \(B'\) 坐标相等，而 \(F\) 坐标由 (1) 局部相差群元素，这就证明了 (4)。在 \(H_{B'}\simeq H_B\times_B B'\) 下，\(k_F\) 拉回为 \(k_{F\times_B B'}\)。这些映射都由投影诱导，因而也与连续两次拉回相容。

## S4　单点上的检验

**否。** 取 \(T=*\)、\(\Gamma=C_2\)，于是 \(H=Q=*\)。取无限的 \(U\)-小 profinite 空间 \(K=\{0,1\}^{\mathbb N}\)。定义预层
\[
L(P)=\bigl(\operatorname{Cont}(P,K)\times\{+,-\}\bigr)/{\sim},
\]
其中仅当 \(u(P)\) 有限时，才把 \((u,+)\) 与 \((u,-)\) 识别。预合成保持有限像条件，故限制映射良定义。交换两个符号给出 \(C_2\)-作用，令 \(E=L^\#\) 带诱导作用。

每个 \(E(*)\) 中的截面都来自 \(L(*)\)。事实上，它在某个有限覆盖上来自 \(L\)，而该覆盖中必有一个非空成员，选取其中一点拉回即得单点上的代表。每个 \(*\to K\) 的像都有限，所以 \(C_2\) 固定 \(E(*)\) 的每个元素。

但 \((\mathrm{id}_K,+)\) 和 \((\mathrm{id}_K,-)\) 在 \(E(K)\) 中不同。若它们相等，则存在有限覆盖 \((p_i:P_i\to K)\) 使二者在每个 \(L(P_i)\) 中相等。这迫使每个 \(p_i(P_i)\) 有限，与这些像覆盖无限集 \(K\) 矛盾。生成元交换这两个截面，同时固定其底截面，违反 (2)，故 \(E\) 不可实现。

## S5　局部满射的基底检验

**是。** 设 \(B\to Q\) 局部满射，且 \(E\times_Q B\) 可在 \(B\) 上实现。给定 \(e\in E(P)\) 和固定 \(x=\pi(e)\) 的 \(\gamma\)，选有限覆盖 \((P_i\to P)\)，使 \(q(x)|_{P_i}\) 提升为 \(b_i\in B(P_i)\)。在拉回对象中，\(\gamma\) 固定 \((e|_{P_i},b_i)\) 的底截面 \((x|_{P_i},b_i)\)。由 S3 判据的必要性，
\[
a_\gamma(e)|_{P_i}=e|_{P_i}.
\]
层的分离性给出 \(a_\gamma(e)=e\)。于是原对象满足 S3 的充分条件，可在 \(Q\) 上实现。

## S6　非空基底与全局结论

**否。** 取 \(\Gamma=C_2\) 平凡作用于 \(T=\{0,1\}\)，于是 \(Q=H=h_T\)。令 \(X\to T\) 在 \(0\) 上有一个元素，在 \(1\) 上有两个元素。令生成元固定前一个元素，交换后两个元素。这给出等变对象 \(E=h_X\to H\)。

取非空可表示层 \(B=h_{\{0\}}\to Q\)。此时 \(H_B=B\)，且 \(E\times_Q B\simeq B\) 带平凡作用，取 \(D=B\to B\) 即得实现。在原基底上，生成元固定 \(1\)，却交换其纤维的两个元素，故由 S2，\(E\) 不可在 \(Q\) 上实现。

可用的检验原则如下。

- 对任意层，S3 的稳定子条件在所有测试空间上给出充要判据。若每个 \(E(P)\) 的截面都由其在 \(P\) 的各点上的限制唯一确定，则单点检验已足够，因为可以逐点验证 \(a_\gamma(e)=e\)。可表示层具有这一性质，S4 说明一般层可能缺少它。
- 可实现性沿任意基底拉回保持，沿局部满射拉回也能反映。S5 的证明同样适用于一族基底，只要每个 \(Q\)-截面在某个有限覆盖的各块上都能提升到这族基底中的某个成员。
- 当 \(Q=*\) 时，非空可表示层 \(B\) 的一个点就给出 \(B\to *\) 的截面，故可用 S5。对一般 \(Q\)，非空性只保证 \(B\) 有点，不能保证各个 \(Q\)-截面局部有提升。