## 轨道层

对任意带有 \(\Gamma\) 作用的层 \(S\)，令
\[
S/\Gamma
\]
为预层
\[
U\longmapsto S(U)/\Gamma
\]
的层化，并记自然态射为 \(\rho_S:S\to S/\Gamma\)。这里每个 \(S(U)/\Gamma\) 是通常的集合轨道商。

取
\[
Q:=h_T/\Gamma,\qquad q:=\rho_{h_T}:h_T\longrightarrow Q.
\]
这个 \(q\) 不变，且对每个 \(Y\in\mathcal C\)，有关于 \(Y\) 自然的双射
\[
\operatorname{Hom}_{\mathcal C}(Q,Y)
\cong
\{b:h_T\to Y\mid b h_\gamma=b\text{ 对所有 }\gamma\in\Gamma\}.
\]

这个商的局部含义很重要。对 \(f,g\in h_T(U)=C(U,T)\)，
\[
q_U(f)=q_U(g)
\]
当且仅当存在有限覆盖 \(\{U_i\to U\}\) 和元素 \(\gamma_i\in\Gamma\)，使得
\[
g|_{U_i}=\gamma_i f|_{U_i}\quad\text{对每个 }i.
\]
等价地，存在有限集 \(F\subseteq\Gamma\)，使得
\[
U=\bigcup_{\gamma\in F}\{u\in U:g(u)=\gamma f(u)\}. \tag{1}
\]
各集合 \(\{u:g(u)=\gamma f(u)\}\) 都是 \(U\) 的闭子空间，因此属于 \(\operatorname{Prof}_{\mathcal U}\)。式 (1) 也包括 \(U=\varnothing\) 时的空覆盖。特别地，逐点属于同一轨道一般不足以保证两个 \(Q\)-截面相等。

## 主定理

设 \(B\in\mathcal C\) 带有态射 \(B\to Q\)，记
\[
X_B:=h_T\times_Q B,\qquad r_B:X_B\to B.
\]
令 \(\Gamma\) 只作用在 \(X_B\) 的 \(h_T\) 坐标上。则 \(r_B\) 是该作用的商：规范态射
\[
X_B/\Gamma\longrightarrow B
\]
是同构。

现在给定一个等变对象
\[
\pi:E\longrightarrow X_B,
\]
即层 \(E\) 带有作用 \(a_\gamma\)，且 \(\pi a_\gamma=\gamma_{X_B}\pi\)。复合 \(r_B\pi\) 是 \(\Gamma\) 不变的，故诱导
\[
\bar v_E:E/\Gamma\longrightarrow B.
\]
有规范等变态射
\[
\theta_E:E\longrightarrow X_B\times_B(E/\Gamma),\qquad
e\longmapsto\bigl(\pi(e),\rho_E(e)\bigr). \tag{2}
\]

对 \(\gamma\in\Gamma\)，令
\[
T^\gamma:=\{t\in T:\gamma t=t\}.
\]
这是一个闭的 profinite 子空间，且 \(X_B\) 的 \(\gamma\)-固定点子层为
\[
X_B^\gamma
\cong h_{T^\gamma}\times_Q B.
\]

以下条件等价：

1. 存在 \(D\to B\) 和等变同构
   \[
   E\cong X_B\times_B D,
   \]
   右侧作用只改变 \(X_B\) 坐标。

2. 对每个 \(\gamma\in\Gamma\)，\(a_\gamma\) 在
   \[
   E\times_{X_B}X_B^\gamma
   \]
   上的限制是恒等态射。

3. 式 (2) 的 \(\theta_E\) 是同构。

条件 2 可以完全用截面表述：对每个 \(U\in\operatorname{Prof}_{\mathcal U}\)、每个 \(e\in E(U)\) 和每个 \(\gamma\in\Gamma\)，只要
\[
\gamma\bigl(\operatorname{pr}_{h_T}\pi_U(e)\bigr)
=\operatorname{pr}_{h_T}\pi_U(e)
\quad\text{作为 }U\to T\text{ 的映射},
\]
就有
\[
a_{\gamma,U}(e)=e. \tag{3}
\]

因此，拉回给出范畴等价
\[
\mathcal C/B
\;\simeq\;
\left\{
\begin{array}{c}
X_B\text{ 上满足条件 \((3)\) 的}\\
\Gamma\text{-等变对象}
\end{array}
\right\},
\qquad
(D\to B)\longmapsto X_B\times_B D. \tag{4}
\]
右侧取所有等变且位于 \(X_B\) 上的映射。拟逆将 \(E\) 送到
\[
E/\Gamma\longrightarrow B,
\]
并将等变映射 \(f:E\to E'\) 送到其诱导的商映射
\[
\bar f:E/\Gamma\longrightarrow E'/\Gamma.
\]

取 \(B=Q\) 时，\(X_B\cong h_T\)。于是这正是题目中等变记录对象的分类：**记录 \(E\) 可实现，当且仅当每个 \(\gamma\) 在 \(\pi^{-1}(h_{T^\gamma})\) 上作用为恒等。** 规范实现为
\[
E\cong h_T\times_Q(E/\Gamma).
\]

更具体地，若固定满足条件的 \(E\)，则其全部实现
\[
\varphi:E\xrightarrow{\sim}X_B\times_B D
\]
由 \(B\) 上的全部同构 \(\lambda:E/\Gamma\xrightarrow{\sim}D\) 给出：
\[
\varphi=(\operatorname{id}_{X_B}\times\lambda)\theta_E.
\]
因此，任意两个带指定识别 \(\varphi\) 的实现之间，存在唯一一个与这些识别相容的 \(B\) 上同构。不同等变对象之间的映射则完全由其商在 \(B\) 上的映射描述。

## 底变换

设 \(u:B'\to B\) 是 \(Q\) 上的态射。它诱导 \(X_{B'}\to X_B\)。对等变对象 \(E\to X_B\)，其等变拉回为
\[
u^\sharp E:=X_{B'}\times_{X_B}E.
\]
因为 \(E\to B\) 是不变的，规范地有
\[
u^\sharp E\cong B'\times_B E,
\]
右侧 \(\Gamma\) 只作用在 \(E\) 坐标。并且存在自然同构
\[
(u^\sharp E)/\Gamma
\;\cong\;
B'\times_B(E/\Gamma). \tag{5}
\]
式 (5) 对任意等变 \(E\) 都成立。

因而，在等价 (4) 下，\(D\to B\) 的通常拉回 \(B'\times_BD\to B'\) 对应于 \(X_{B'}\times_{X_B}E\to X_{B'}\)。若
\[
E\cong X_B\times_BD,
\]
则拉回后的实现为
\[
u^\sharp E
\cong
X_{B'}\times_{B'}(B'\times_BD).
\]
这些同构对对象、映射和继续底变换均自然相容。特别地，从原来的 \(B=Q\) 拉回到任意 \(B\to Q\)，实现 \(D\to Q\) 对应于 \(B\times_QD\to B\)。

## 证明

首先说明所用的层化与局部性质。有限联合满射族在拉回和复合下仍是有限联合满射族。对覆盖 \(\{U_i\to U\}\)，有限不交并
\[
\coprod_i U_i\longrightarrow U
\]
是从紧空间到 Hausdorff 空间的闭满射，因而是商映射。由此，彼此在纤维积上相等的 \(U_i\to T\) 唯一地粘合为 \(U\to T\)；空覆盖也给出 \(h_T(\varnothing)=\{*\}\)。所以 \(h_T\) 是层。

该站点在 \(\mathcal V\) 中是小范畴。层化可用通常的两次加号构造：预层 \(P\) 的 \(P^+(U)\) 由有限覆盖上的匹配截面族组成，按共同覆盖上的相等取等价类；\(P^{++}\) 是层。第一次加号产生分离预层，而对分离预层再做一次加号便能粘合匹配族。所有覆盖、匹配族及所得层值都留在 \(\mathcal V\) 中。

这个构造给出两条局部性质：

- \(P(U)\) 的两个截面在层化后相等，当且仅当它们在某个有限覆盖上相等。
- 层化的每个截面都能在某个有限覆盖上由 \(P\) 的截面表示。

应用于 \(P(U)=S(U)/\Gamma\)，可得
\[
\rho_S(s)=\rho_S(s')
\iff
\text{存在有限覆盖 }U_i\to U\text{ 和 }\gamma_i\in\Gamma
\text{ 使 }s'|_{U_i}=a_{\gamma_i}(s|_{U_i}), \tag{6}
\]
而 \(S/\Gamma\) 的每个截面都局部来自 \(S\)。层化的泛性质也立即给出 \(S/\Gamma\) 对不变态射的泛性质，从而证明了 \(Q\) 的泛性质。

对 \(S=h_T\)，式 (6) 给出轨道层的局部相等条件。若有限覆盖上的关系成立，则覆盖源的像包含在相应的闭等化子中，得到式 (1)；反之，这些闭等化子的包含映射构成有限覆盖。因此式 (1) 也成立。

下面反复使用一个直接的层论事实：若层态射局部满射，且像相等的两个截面局部相等，则它是同构。事实上，层的分离性给出逐截面单射；局部提升在两两纤维积上相等，因而可唯一粘合。由此，若不变的 \(v:S\to Z\) 局部满射，而且每两个有相同 \(v\)-像的 \(S\)-截面局部处于同一 \(\Gamma\)-轨道，则诱导的 \(S/\Gamma\to Z\) 是同构。

将此应用于 \(r_B:X_B\to B\)。它局部满射，因为 \(q:h_T\to Q\) 局部满射。若 \((t_1,b_1)\) 和 \((t_2,b_2)\) 有相同的 \(B\)-像，则 \(b_1=b_2\) 且 \(q(t_1)=q(t_2)\)；由式 (6)，它们局部相差一个群元素。因此
\[
X_B/\Gamma\cong B. \tag{7}
\]

接着证明式 (2) 的判据。记 \(X=X_B\)、\(r=r_B\)。给定
\[
(x,d)\in\bigl(X\times_B(E/\Gamma)\bigr)(U),
\]
先在有限覆盖上将 \(d\) 提升为 \(e\in E\)。此时
\[
r(\pi(e))=\bar v_E(d)=r(x).
\]
由 (7) 和式 (6)，进一步局部有 \(x=\gamma\pi(e)\)。于是 \(a_\gamma(e)\) 是 \((x,d)\) 的局部原像，故 \(\theta_E\) 局部满射。

若条件 (3) 成立，而 \(\theta_E(e)=\theta_E(e')\)，则
\[
\pi(e)=\pi(e'),\qquad \rho_E(e)=\rho_E(e').
\]
由式 (6)，局部有 \(e'=a_\gamma(e)\)。等变性随即给出 \(\gamma\pi(e)=\pi(e)\)，条件 (3) 因而给出 \(e'=e\)。由层的分离性，\(\theta_E\) 是单射，故为同构。反过来，若 \(\theta_E\) 是同构且 \(\gamma\pi(e)=\pi(e)\)，则 \(\theta_E(a_\gamma e)=\theta_E(e)\)，所以 \(a_\gamma e=e\)。这证明了条件 2 与 3 的等价。

若 \(E=X\times_BD\)，群只改变 \(X\) 坐标，因此条件 2 显然成立。反之，条件 3 直接用 \(D=E/\Gamma\) 给出实现。这证明了三个条件的等价。

对任意 \(D\to B\)，投影
\[
X\times_BD\longrightarrow D
\]
局部满射；具有相同 \(D\)-像的两个截面，其 \(X\)-坐标局部相差一个群元素。因此它诱导同构
\[
(X\times_BD)/\Gamma\xrightarrow{\sim}D. \tag{8}
\]
式 (2) 与 (8) 是互为拟逆的自然同构，证明了范畴等价 (4)，也证明了所述实现与映射的唯一性。

最后证明 (5)。由 \(u^\sharp E\cong B'\times_BE\)，不变映射
\[
B'\times_BE\longrightarrow B'\times_B(E/\Gamma)
\]
局部满射：局部提升 \(E/\Gamma\) 坐标即可。若两个截面有相同的像，则它们的 \(B'\) 坐标相同，而 \(E\) 坐标由式 (6) 局部相差一个群元素。因此它的商正是右侧，得到 (5)。其余底变换陈述由纤维积的规范同构及这些商映射的泛性质给出。

## 为什么必须检查广义截面

式 (3) 不能一般地只在单点空间上的截面检查。举例，令 \(K=\mathbb Z_2\) 为 \(2\)-进整数加法群，把其底群赋予离散拓扑，以平移作用于 profinite 空间 \(K\)，并令
\[
A:=h_K/K.
\]
平移在 \(K\) 上传递，故由局部提升可知 \(A(*)\) 只有一个元素。取反 \(x\mapsto-x\) 使平移共轭为平移，因而在 \(A\) 上诱导一个二阶自同构。

这个自同构在 \(A(*)\) 上是恒等，但在 \(A\) 上不是恒等：由式 (1)，\(q_K(\operatorname{id}_K)=q_K(-\operatorname{id}_K)\) 将要求 \(\{-2x:x\in K\}\) 有限，而它是无限集。于是将 \(A\) 看作单点底空间上的 \(\mathbb Z/2\)-等变对象时，普通点上的作用全都平凡，广义截面上的作用却非平凡；该对象因此不可实现。