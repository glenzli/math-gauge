典范同态
\[
\eta_S:F(S)\longrightarrow F_{\mathrm{Zar}}(S)
\]
是同构。证明的关键是：**同伦不变的带转移预层在光滑半局部概形上的值，可以单射到其函数域上的值。**

下面会引用一个标准的 Suslin–Voevodsky 定理：对于任意域 \(k\)，同伦不变的带转移预层的 Zariski 层化仍带有函子性的转移结构，并仍是同伦不变的。具体地，若 \(P\) 是这样的预层，则 \(P_{\mathrm{Zar}}\) 可视为带转移预层，\(P\to P_{\mathrm{Zar}}\) 与转移相容，且
\[
P_{\mathrm{Zar}}(Y)\xrightarrow{\sim}
P_{\mathrm{Zar}}(Y\times\mathbb A^1)
\]
对每个 \(Y\in\mathrm{Sm}/k\) 成立。这里不需要 \(k\) 完美，也不需要更强的高阶上同调同伦不变性。

首先证明所需的半局部单射引理。

设 \(P\) 是任意同伦不变的带转移预层，\(T\) 是光滑整 \(k\)-概形 \(X\) 沿有限点集取得的半局部概形。记 \(K=k(X)\)。则
\[
\tag{1}P(T)\longrightarrow P(K)
\]
是单射，其中 \(P(K)\) 是沿 \(X\) 的非空开子集取得的滤过余极限。

确实，先设定义 \(T\) 的点 \(x_1,\ldots,x_r\) 都是 \(X\) 的闭点。若 \(a\in P(T)\) 在 \(P(K)\) 中为零，缩小到这些点的一个共同仿射开邻域后，可设 \(X\) 光滑、仿射、整，\(a\) 由 \(P(X)\) 中的一个元素表示，而且存在稠密开集 \(U\subset X\)，使得 \(a|_U=0\)。置 \(Z=X\setminus U\)。我们要证明 \(a|_T=0\)。

令 \(d=\dim X\)。\(d=0\) 时结论显然。\(d>0\) 时，可取函数 \(f_1,\ldots,f_d\in\Gamma(X,\mathcal O_X)\)，满足：

1. \(f=(f_1,\ldots,f_d):X\to\mathbb A^d_k\) 有限；
2. \(p=(f_1,\ldots,f_{d-1}):X\to B:=\mathbb A^{d-1}_k\) 在每个 \(x_i\) 处光滑；
3. \(Z\to B\) 有限。

这里的选择对有限域同样成立。为说明这一点，将 \(X\) 闭嵌入某个仿射空间，取其射影闭包。在无穷远处依次选择齐次方程，使前 \(d-1\) 个方程的共同零集避开 \(Z\) 的无穷远部分，而全部 \(d\) 个方程的共同零集避开 \(X\) 的无穷远部分。同时，在每个 \(x_i\) 的一阶邻域上规定前 \(d-1\) 个函数的微分线性无关。每一步只涉及有限个闭点及有限个一阶邻域上的插值；取足够高的次数即可由射影空间上的截面满射完成，不必假设 \(k\) 无限。所得仿射态射的有限性可由射影闭包到加权射影空间的态射看出：这些态射既是仿射的，又是适当的，因此有限。微分条件给出 \(p\) 在各 \(x_i\) 处光滑。

由于 \(X\) 正则且 \(f\) 有限，奇迹平坦性表明 \(f\) 有限平坦。我们还可将相对曲线 \(p:X\to B\) 紧化为
\[
X\subset\overline X\longrightarrow\mathbb P^1_B,
\]
使 \(\overline X\to\mathbb P^1_B\) 有限平坦，且边界
\(\overline X\setminus X\) 在 \(B\) 上有限平坦。例如，写
\(\mathbb A^d=B\times\mathbb A^1_t\)。有限平坦代数
\(\Gamma(X,\mathcal O_X)\) 是 \(k[B,t]\) 上有限自由的；选取以 \(1\) 开始的基，并在 \(u=1/t\) 的图上把其余基向量乘以充分高次的 \(u\)，便得到一个在 \(k[B,u]\) 上有限自由的代数。它与原代数在 \(t\ne0\) 处粘合，给出所需紧化。

作基变换
\[
\overline C=T\times_B\overline X,\qquad
C=T\times_B X,\qquad Z_T=T\times_B Z,
\]
并记边界为 \(D=\overline C\setminus C\)。\(D\) 和 \(Z_T\) 都在 \(T\) 上有限。对角截面
\[
\Delta:T\longrightarrow C
\]
是有效 Cartier 除子：因为 \(p\) 在所选闭点处光滑，它在整个半局部概形 \(T\) 上光滑。

取 \(\overline C\) 上充分正的可逆层 \(\mathcal L\)。由于有限于半局部概形的概形仍是半局部的，其上可逆层平凡；结合截面的延拓，能选取
\[
s'_0\in H^0\bigl(\overline C,\mathcal L(-\Delta)\bigr)
\]
使它在 \(D\cup Z_T\cup\Delta\) 上处处不为零。令 \(s_0\) 为 \(s'_0\) 与 \(\Delta\) 的典范截面的乘积，则
\[
\operatorname{div}(s_0)=\Delta+E,
\]
其中 \(E\) 避开 \(Z_T\) 和 \(D\)。再选取
\(s_1\in H^0(\overline C,\mathcal L)\)，使
\[
s_1|_D=s_0|_D,\qquad s_1|_{Z_T}\ \text{处处不为零}.
\]
这是可能的，因为 \(D\) 与 \(Z_T\) 不相交，而且 \(\mathcal L\) 可取得充分正。

考虑截面族
\[
s_t=(1-t)s_0+t s_1.
\]
它在 \(D\times\mathbb A^1\) 上处处不为零。由于
\(\overline C\to\mathbb P^1_T\) 有限平坦，每个几何纤维的每个不可约分支都遇到边界，故 \(s_t\) 在这些纤维上是非零因子。因此其零概形有限平坦于 \(T\times\mathbb A^1\)，并且位于 \(C\times\mathbb A^1\) 内。把它推到 \(X\)，得到连接有限对应
\[
\Delta+E\quad\text{与}\quad\operatorname{div}(s_1)
\]
的 \(\mathbb A^1\)-同伦。这些有限对应及同伦均可向某个包含 \(x_1,\ldots,x_r\) 的光滑开邻域下降，所以可以作用于 \(P\)。

同伦不变性于是给出
\[
\Delta^*a+E^*a=\operatorname{div}(s_1)^*a.
\]
但 \(E\) 和 \(\operatorname{div}(s_1)\) 都通过 \(X\setminus Z=U\) 给出对应，而 \(a|_U=0\)。故两项均为零，得到
\[
a|_T=\Delta^*a=0.
\]
这证明了闭点情形。

对于任意有限点集，若 \(a\in P(T)\) 在 \(P(K)\) 中为零，先在一个包含这些点的开集 \(W\) 上表示 \(a\)。由于有限型 \(k\)-概形是 Jacobson 概形，可在 \(W\) 内为每个所选点 \(x_i\) 选一个闭特化点 \(y_i\)。闭点情形表明，\(a\) 在某个包含所有 \(y_i\) 的开集上为零；该开集也包含它们的泛化 \(x_i\)。因此 \(a=0\) 于 \(P(T)\)，引理 (1) 得证。

现在应用引理。记
\[
G=F_{\mathrm{Zar}},\qquad
K_F=\ker(F\to G),\qquad C_F=\operatorname{coker}(F\to G),
\]
其中核和余核逐对象计算。由上面引用的层化定理，\(G\) 是同伦不变的带转移预层；因此 \(K_F\) 和 \(C_F\) 也都是同伦不变的带转移预层。Zariski 层化在阿贝尔群预层上正合，而 \(F\to G\) 在层化后成为同构，所以
\[
(K_F)_{\mathrm{Zar}}=0,\qquad (C_F)_{\mathrm{Zar}}=0.
\]
层化不改变茎。特别地，在任一不可约分支的泛点 \(\xi\) 处，
\[
K_F(k(\xi))=0,\qquad C_F(k(\xi))=0.
\]
对 \(K_F\) 和 \(C_F\) 分别应用半局部单射 (1)，得到它们在该分支对应的半局部概形上的值均为零。光滑概形的连通分支是整的，且带转移预层对有限不交并给出直和，因此对整个 \(S\) 有
\[
K_F(S)=0,\qquad C_F(S)=0.
\]

最后，题目中的 \(H(S)\) 正是上述半局部值：在给定仿射邻域 \(\operatorname{Spec}A\) 中，包含 \(\Sigma\) 的主开集 \(D(f)\)、\(f\in M\)，在所有包含 \(\Sigma\) 的开邻域中余终；这是有限个素理想的素理想回避引理。对逐对象正合列取这些邻域上的滤过余极限，便得到
\[
0\longrightarrow K_F(S)\longrightarrow F(S)
\xrightarrow{\eta_S}G(S)\longrightarrow C_F(S)\longrightarrow0.
\]
两端均为零，故
\[
\boxed{\,F(S)\xrightarrow{\ \sim\ }F_{\mathrm{Zar}}(S)\,}.
\]