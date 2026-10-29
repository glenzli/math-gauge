**主定理。** 对每个 \(X\in\mathcal V\)，相容记录自然地对应于 \(X\) 上的超滤。记超滤的集合为 \(\operatorname{Ult}(X)\)。在自然同构
\[
R(X)\cong\operatorname{Ult}(X)
\]
下，观察 \(e_{A,f}\) 取值为有限划分
\[
X=\coprod_{a\in A}f^{-1}(\{a\})
\]
中属于该超滤的唯一一块的标号。

对映射 \(h:X\to Y\)，函子 \(R\) 对应于超滤的推前：
\[
R(h)(\mathfrak p)
=h_*\mathfrak p
=\{T\subseteq Y:h^{-1}(T)\in\mathfrak p\}.
\]
单位与乘法分别对应于主超滤和超滤的聚合：
\[
\eta_X(x)=\{S\subseteq X:x\in S\},
\]
\[
\mu_X(\mathfrak Q)
=
\left\{S\subseteq X:
\{\mathfrak p\in\operatorname{Ult}(X):S\in\mathfrak p\}
\in\mathfrak Q
\right\},
\qquad
\mathfrak Q\in\operatorname{Ult}(\operatorname{Ult}(X)).
\]
这些映射构成超滤单子，并且它们由题目给出的观察公式唯一确定。

最后，\(\eta_X:X\to R(X)\) 总是单射；它是双射，亦即每个相容记录都由唯一点给出，**当且仅当 \(X\) 有限**。这里包括 \(X=\varnothing\)：此时 \(R(X)=\varnothing\)。

下面证明这些结论。为避免混淆观察的定义域，暂写
\[
e^X_{A,f}:R(X)\longrightarrow A,\qquad e^X_{A,f}(r)=r_A(f).
\]

首先，所有对象都处于所需的宇宙中。令
\[
I_X=\{(A,f):A\in\mathcal U\text{ 有限},\ f:X\to A\}.
\]
由于 \(\mathcal U\) 传递，\(I_X\) 是
\(\mathcal P(\mathcal U)\times\mathcal P(X\times\mathcal U)\)
的子集，所以 \(I_X\in\mathcal V\)。一个记录可以看作满足相容条件及
\(r(A,f)\in A\) 的函数 \(I_X\to\mathcal U\)。因此
\[
R(X)\subseteq\operatorname{Map}(I_X,\mathcal U),
\]
从而 \(R(X)\in\mathcal V\)。同样，
\(\operatorname{Ult}(X)\subseteq\mathcal P(\mathcal P(X))\)，故它也属于 \(\mathcal V\)。

现在构造分类。取 \(2=\{0,1\}\in\mathcal U\)，对 \(S\subseteq X\) 写
\(\chi_S:X\to2\) 为示性函数。对记录 \(r\)，定义
\[
\mathfrak p_r
=\{S\subseteq X:r_2(\chi_S)=1\}.
\]
它是超滤：

- 由从单点集合到 \(2\) 的两个常值映射的自然性，\(X\in\mathfrak p_r\) 且 \(\varnothing\notin\mathfrak p_r\)。
- 由交换 \(0,1\) 的映射 \(2\to2\)，对每个 \(S\subseteq X\)，恰有一个 \(S,X\setminus S\) 属于 \(\mathfrak p_r\)。
- 对 \(S,T\subseteq X\)，应用两个投影 \(2\times2\to2\) 和合取映射 \(2\times2\to2\)，得到
  \[
  r_2(\chi_{S\cap T})
  =r_2(\chi_S)\wedge r_2(\chi_T).
  \]
  因此 \(\mathfrak p_r\) 对有限交封闭。

向上封闭也随之成立：若 \(S\subseteq T\)、\(S\in\mathfrak p_r\) 而 \(T\notin\mathfrak p_r\)，则 \(X\setminus T\in\mathfrak p_r\)，导致空集属于 \(\mathfrak p_r\)，矛盾。上述性质正是超滤性质。

反过来，设 \(\mathfrak p\) 是 \(X\) 上的超滤。对有限 \(A\in\mathcal U\) 和 \(f:X\to A\)，有限划分的各块
\(f^{-1}(\{a\})\) 中恰有一块属于 \(\mathfrak p\)：若一块也没有，则各块的补集都属于 \(\mathfrak p\)，其有限交为空集；若两块都属于 \(\mathfrak p\)，它们的交为空集。因此可定义
\[
r^{\mathfrak p}_A(f)
=\text{满足 }f^{-1}(\{a\})\in\mathfrak p\text{ 的唯一 }a\in A.
\]
当 \(A=\varnothing\) 时，这个定义没有遗漏：有超滤的 \(X\) 非空，因而不存在 \(X\to\varnothing\)。

若 \(g:A\to B\)，且 \(a=r^{\mathfrak p}_A(f)\)，则
\[
f^{-1}(\{a\})\subseteq(g\circ f)^{-1}(\{g(a)\}).
\]
由超滤的向上封闭性，后一集合属于 \(\mathfrak p\)，所以
\[
r^{\mathfrak p}_B(g\circ f)=g(a).
\]
故 \(r^{\mathfrak p}\) 是相容记录。

这两个构造互逆。一方面，示性函数的定义直接给出
\(\mathfrak p_{r^{\mathfrak p}}=\mathfrak p\)。另一方面，若
\(a=r_A(f)\)，对单点 \(\{a\}\subseteq A\) 的示性函数
\(\chi_{\{a\}}:A\to2\) 使用相容性，得到
\[
r_2\bigl(\chi_{\{a\}}\circ f\bigr)
=\chi_{\{a\}}(r_A(f))=1.
\]
因此 \(f^{-1}(\{a\})\in\mathfrak p_r\)，于是
\(r^{\mathfrak p_r}_A(f)=a=r_A(f)\)。这证明了所述双射。

对任意 \(h:X\to Y\)，直接在记录上定义
\[
(R(h)(r))_A(f)=r_A(f\circ h),\qquad f:Y\to A.
\]
记录的相容性保证右侧再次定义相容记录；恒等映射和复合映射的函子律由公式立即成立。并且
\[
e^Y_{A,f}\circ R(h)=e^X_{A,f\circ h}. \tag{1}
\]
对 \(T\subseteq Y\)，因
\(\chi_T\circ h=\chi_{h^{-1}(T)}\)，上述分类把 \(R(h)\) 变成定理中的推前 \(h_*\)。所以分类对所有集合映射自然。

单位与乘法可直接在记录上定义为
\[
(\eta_X(x))_A(f)=f(x),\qquad
(\mu_X(Q))_A(f)=Q_A(e^X_{A,f}),
\quad Q\in R(R(X)). \tag{2}
\]
第一个公式显然给出相容记录。对第二个公式，记录的相容性给出
\[
e^X_{B,g\circ f}=g\circ e^X_{A,f}.
\]
因此
\[
g\bigl(Q_A(e^X_{A,f})\bigr)
=Q_B(g\circ e^X_{A,f})
=Q_B(e^X_{B,g\circ f}),
\]
故 \(\mu_X(Q)\) 也是相容记录。由定义，
\[
e^X_{A,f}\circ\eta_X=f,\qquad
e^X_{A,f}\circ\mu_X=e^{R(X)}_{A,e^X_{A,f}}. \tag{3}
\]
同一定义也给出 \(\eta_X(x)\) 对应于 \(x\) 的主超滤。对乘法，若把 \(Q\) 对应的超滤记为 \(\mathfrak Q\)，则对 \(S\subseteq X\)，
\[
\begin{aligned}
S\in\mathfrak p_{\mu_X(Q)}
&\iff Q_2(e^X_{2,\chi_S})=1\\
&\iff
\{r\in R(X):S\in\mathfrak p_r\}\in\mathfrak Q.
\end{aligned}
\]
经由 \(R(X)\cong\operatorname{Ult}(X)\) 识别，这正是定理中 \(\mu_X\) 的超滤公式。

所有 \(e^X_{A,f}\) 联合区分 \(R(X)\) 中的元素，因此可逐个观察验证自然性和单子律。对 \(h:X\to Y\) 及 \(f:Y\to A\)，由 (1) 和 (3)，
\[
e^Y_{A,f}\circ R(h)\circ\eta_X
=f\circ h
=e^Y_{A,f}\circ\eta_Y\circ h,
\]
而
\[
\begin{aligned}
e^Y_{A,f}\circ R(h)\circ\mu_X
&=e^{R(X)}_{A,e^X_{A,f\circ h}}\\
&=e^Y_{A,f}\circ\mu_Y\circ R(R(h)).
\end{aligned}
\]
故 \(\eta\) 和 \(\mu\) 自然。

两个单位律同理由
\[
\begin{aligned}
e^X_{A,f}\circ\mu_X\circ\eta_{R(X)}
&=e^{R(X)}_{A,e^X_{A,f}}\circ\eta_{R(X)}
=e^X_{A,f},\\
e^X_{A,f}\circ\mu_X\circ R(\eta_X)
&=e^X_{A,e^X_{A,f}\circ\eta_X}
=e^X_{A,f}
\end{aligned}
\]
得到。结合律则由
\[
e^X_{A,f}\circ\mu_X\circ\mu_{R(X)}
=
e^{R(R(X))}_{A,e^{R(X)}_{A,e^X_{A,f}}}
=
e^X_{A,f}\circ\mu_X\circ R(\mu_X)
\]
得到。观察联合区分元素也说明：满足题目观察公式的 \(\eta_X\) 和 \(\mu_X\) 唯一。

这个函子还有一个由观察直接给出的普遍描述。设
\(i:\mathbf{Fin}_{\mathcal U}\hookrightarrow\mathbf{Set}_{\mathcal V}\)
是有限测试集合的包含函子。对固定 \(X\)，令图的对象为所有
\(f:X\to A\)，箭头为满足 \(g\circ f=f'\) 的有限集合映射
\(g:A\to B\)。该图把 \(f:X\to A\) 送到 \(A\)，而其极限正是兼容取值的集合 \(R(X)\)。因此
\[
R=\operatorname{Ran}_i i,
\]
即 \(R\) 是 \(i\) 的余密单子。

具体地，右 Kan 延拓的余单位为
\[
\rho_A:R(A)\to A,\qquad \rho_A(r)=r_A(\operatorname{id}_A),
\]
并满足 \(e^X_{A,f}=\rho_A\circ R(f)\)。例如，若
\(\alpha:H i\Rightarrow i\)，则相应的唯一自然变换
\(\bar\alpha:H\Rightarrow R\) 由
\[
(\bar\alpha_X(t))_A(f)=\alpha_A(H(f)(t))
\]
给出；相容性由 \(\alpha\) 的自然性保证，唯一性由各观察确定。公式 (3) 也给出
\(\rho_A\eta_A=\operatorname{id}_A\) 和
\(\rho_A\mu_A=\rho_A R(\rho_A)\)，所以以上单子结构正是这个余密单子的结构。

最后证明有限性的刻画。若 \(x\ne y\)，则单点集 \(\{x\}\) 属于 \(x\) 的主超滤而不属于 \(y\) 的主超滤，故 \(\eta_X\) 总是单射。

若 \(X\) 有限且非空，任意超滤在有限划分
\(X=\coprod_{x\in X}\{x\}\) 中恰含一个单点集 \(\{x\}\)。向上封闭性及超滤的补集性质随即表明该超滤恰为 \(x\) 的主超滤。若 \(X=\varnothing\)，不存在超滤；也可直接看出，测试 \(A=\varnothing\) 和唯一映射 \(\varnothing\to\varnothing\) 无法被赋予所需的值。因此有限 \(X\) 的 \(\eta_X\) 都是双射。

若 \(X\) 无限，余有限集合构成真滤子
\[
\mathcal F_0=\{S\subseteq X:X\setminus S\text{ 有限}\}.
\]
由 Zorn 引理，它可扩张为极大真滤子 \(\mathfrak p\)，而极大真滤子是超滤：若 \(S\notin\mathfrak p\)，则加入 \(S\) 必使滤子不再为真滤子，所以某个 \(F\in\mathfrak p\) 与 \(S\) 不交，从而 \(X\setminus S\in\mathfrak p\)。这个超滤包含每个 \(X\setminus\{x\}\)，故不可能是任何 \(x\) 的主超滤。相应记录不是点值记录，证明了无限情形的非满射性。