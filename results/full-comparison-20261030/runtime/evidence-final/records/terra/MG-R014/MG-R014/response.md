整体解一定存在。全部信息由有限支撑向量空间的一个子空间 \(W\) 及其上线性泛函 \(\beta\) 决定；坐标投影和纤维则分别由 \(W\) 与相应坐标子空间的交、和决定。

令
\[
V=k^{(I)},\qquad e_i\in V\quad(i\in I)
\]
为标准基，并以
\[
\langle v,x\rangle=\sum_{i\in I}v(i)x_i
\]
配对 \(V\) 与 \(k^I\)。由此 \(k^I\) 正是 \(V\) 的代数对偶 \(V^*\)。对 \(A\subseteq I\)，记
\[
U_A=k^{(A)}=\operatorname{span}\{e_i:i\in A\}\subseteq V.
\]

首先令
\[
W=\operatorname{span}\{a_j:j\in J\}\subseteq V.
\]
对 \(w=\sum_{j\in F}c_ja_j\)，其中 \(F\subseteq J\) 有限，定义
\[
\beta(w)=\sum_{j\in F}c_jb_j.
\]
这是良定义的：若 \(\sum_{j\in F}c_ja_j=0\)，取满足 \(F\) 中方程的 \(x\)，就有
\[
\sum_{j\in F}c_jb_j
=\left\langle\sum_{j\in F}c_ja_j,x\right\rangle=0.
\]
于是 \(\beta:W\to k\) 是线性泛函，并且
\[
\mathcal S
=\{x\in V^*:x|_W=\beta\}. \tag{1}
\]

在 ZFC 中，可以取 \(W\) 的一组基并扩充为 \(V\) 的一组基，从而把 \(\beta\) 延拓到 \(V\)。因此 \(\mathcal S\ne\varnothing\)。若取定任一延拓 \(x^0\)，则
\[
\mathcal S=x^0+W^\perp,
\qquad
W^\perp\cong (V/W)^*. \tag{2}
\]
这也说明原假设等价于：每个有限线性关系
\(\sum c_ja_j=0\) 都满足 \(\sum c_jb_j=0\)。

还可以直接用**实际坐标**参数化全部解。商空间 \(V/W\) 由 \((e_i+W)_{i\in I}\) 生成；利用 ZFC 选取 \(P\subseteq I\)，使
\[
(e_p+W)_{p\in P}
\]
成为 \(V/W\) 的一组基。于是 \(V=W\oplus U_P\)。对每个 \(i\in I\)，唯一地写成
\[
e_i=w_i+\sum_{p\in P}\lambda_{ip}e_p,
\qquad w_i\in W,
\]
其中只有有限多个 \(\lambda_{ip}\) 非零。那么，对任意 \(t=(t_p)_{p\in P}\in k^P\)，
\[
\boxed{\quad
x_i=\beta(w_i)+\sum_{p\in P}\lambda_{ip}t_p
\quad(i\in I)
\quad} \tag{3}
\]
给出一个整体解，而且每个整体解唯一地以这种方式得到，其参数就是 \(t_p=x_p\)。各 \(w_i\) 都是有限多个给定 \(a_j\) 的线性组合，所以式中的常数也由有限多个给定方程算出。

这对代数数据 \((W,\beta)\) 是完整且唯一的分类数据。确实，若 \(v\notin W\)，可将 \(W\) 上为零、在 \(v\) 上为 \(1\) 的泛函延拓到 \(V\)；因此 \(\langle v,x\rangle\) 随 \(x\in\mathcal S\) 取遍 \(k\)。故
\[
W=\{v\in V:\langle v,x\rangle\text{ 在 }\mathcal S\text{ 上为常数}\},
\]
而该常数就是 \(\beta(v)\)。所以两组满足假设的方程有同一解集，当且仅当它们给出同一对 \((W,\beta)\)。反过来，任意 \(W\subseteq V\) 及 \(\beta\in W^*\) 都可通过方程
\(\langle w,x\rangle=\beta(w)\;(w\in W)\) 实现。

对于任意 \(A\subseteq I\)，将 \(y\in k^A\) 看作 \(U_A\) 上的线性泛函。其可延拓条件是
\[
\boxed{\quad
\pi_A(\mathcal S)
=\{y\in k^A:y|_{W\cap U_A}=\beta|_{W\cap U_A}\}.
\quad} \tag{4}
\]
换成原始系数，这就是说：对每个有限 \(F\subseteq J\) 和 \(c_j\in k\)，只要
\[
\left.\sum_{j\in F}c_ja_j\right|_{I\setminus A}=0,
\]
就必须有
\[
\sum_{i\in A}\left(\sum_{j\in F}c_ja_j(i)\right)y_i
=\sum_{j\in F}c_jb_j. \tag{5}
\]
式中各和都是有限和。这些条件充分：若 \(y\) 满足它们，则
\[
h_{A,y}:W+U_A\longrightarrow k,\qquad
h_{A,y}(w+u)=\beta(w)+\langle u,y\rangle \tag{6}
\]
良定义；将它延拓到 \(V\) 即得到限制为 \(y\) 的整体解。

因此，若 \(y\) 不满足 (4)，纤维为空；若满足，则其全部纤维是
\[
\boxed{\quad
\pi_A^{-1}(y)
=\{x\in V^*:x|_{W+U_A}=h_{A,y}\}
=x^y+(W+U_A)^\perp
\quad} \tag{7}
\]
其中 \(x^y\) 是任一延拓。这个纤维是 \((V/(W+U_A))^*\) 的仿射空间。

同样可把每个非空纤维用实际坐标构造出来。选择 \(P_A\subseteq I\setminus A\)，使
\[
(e_p+(W+U_A))_{p\in P_A}
\]
成为 \(V/(W+U_A)\) 的一组基。对每个 \(i\)，选择有限表示
\[
e_i=w_i+u_i+\sum_{p\in P_A}\lambda_{ip}e_p,
\qquad w_i\in W,\quad u_i\in U_A.
\]
则纤维中全部解由任意 \(t\in k^{P_A}\) 唯一给出：
\[
\boxed{\quad
x_i=\beta(w_i)+\langle u_i,y\rangle
       +\sum_{p\in P_A}\lambda_{ip}t_p.
\quad} \tag{8}
\]
这里 \(t_p=x_p\)。虽然 \(w_i+u_i\) 的拆分可能不唯一，但前两项之和由 (6) 唯一确定。

这些描述也给出像和纤维的大小。令
\[
d_A=\dim\frac{U_A}{W\cap U_A},\qquad
m_A=\dim\frac{V}{W+U_A},\qquad q=|k|.
\]
则
\[
|\pi_A(\mathcal S)|=q^{d_A},\qquad
|\pi_A^{-1}(y)|=q^{m_A}
\quad(y\in\pi_A(\mathcal S)), \tag{9}
\]
并且
\[
\dim(V/W)=d_A+m_A.
\]
这里的维数是所写商空间的维数；像的方向空间是 \((U_A/(W\cap U_A))^*\)，纤维的方向空间是 \((V/(W+U_A))^*\)。

由此得到坐标集 \(A\) 的分类：

- **任意赋值都能延拓**，即 \(\pi_A\) 满射，当且仅当
  \[
  W\cap U_A=0.
  \]
- **\(A\) 确定整个解**，即 \(\pi_A\) 单射，当且仅当
  \[
  W+U_A=V.
  \]
- **\(A\) 是一组自由且完整的坐标**，即 \(\pi_A\) 双射，当且仅当
  \[
  V=W\oplus U_A.
  \]

等价地，上面三个条件分别表示索引族 \((e_a+W)_{a\in A}\) 在 \(V/W\) 中线性无关、生成整个商空间、构成一组基。前面构造的 \(P\) 表明，至少存在一组自由且完整的坐标。

对单个坐标的恢复，可定义
\[
\operatorname{cl}(A)
=\{i\in I:e_i\in W+U_A\}. \tag{10}
\]
固定任意可延拓的 \(y\in\pi_A(\mathcal S)\)：

- 若 \(i\in\operatorname{cl}(A)\)，则存在有限 \(F\subseteq J\)、\(D\subseteq A\) 和系数 \(c_j,d_a\)，使
  \[
  e_i=\sum_{j\in F}c_ja_j+\sum_{a\in D}d_ae_a.
  \]
  所以纤维中的每个解都满足有限恢复公式
  \[
  \boxed{\quad
  x_i=\sum_{j\in F}c_jb_j+\sum_{a\in D}d_ay_a.
  \quad} \tag{11}
  \]
- 若 \(i\notin\operatorname{cl}(A)\)，则在同一纤维中，\(x_i\) 可以取遍 \(k\)。事实上，(6) 可以在
  \((W+U_A)\oplus ke_i\) 上赋予 \(e_i\) 任意指定值，再延拓到 \(V\)。

因此，只要某坐标由 \(A\) 唯一确定，它就必定能由有限多个 \(A\)-坐标和有限多个原方程恢复。由 (10) 得到的闭包是商空间 \(V/W\) 上坐标族所定义的有限型可表示拟阵闭包。

多个待恢复坐标的**联合约束**也由同一个构造给出。对任意 \(C\subseteq I\) 和可延拓的 \(y\)，有
\[
\boxed{\quad
\pi_C\bigl(\pi_A^{-1}(y)\bigr)
=\{z\in k^C:
z(v)=h_{A,y}(v)\ \text{对所有 }v\in U_C\cap(W+U_A)\}.
\quad} \tag{12}
\]
这包含了 \(A\cap C\) 上的取值一致性，也包含 \(C\) 内各坐标之间可能存在的关系。它再次来自把两个泛函在交上拼合后延拓到 \(V\)。

最后，式 (4) 表明坐标赋值也具有有限局部到整体性质：
\[
y\in\pi_A(\mathcal S)
\quad\Longleftrightarrow\quad
y|_D\in\pi_D(\mathcal S)
\ \text{对每个有限 }D\subseteq A.
\]
例如，方程 \(x_n-x_{n+1}=0\;(n\in\mathbb N)\) 的解都是常值序列；任一单坐标就是完整自由坐标，而两个坐标分别都可取遍 \(k\)，联合取值却必须相等。