仅由 \(R_j=0\) **不能保证所要求的有界消元算子或 \(L_j\) 的有界右逆存在**。这个条件只说明 \(\operatorname{ran}d_{j-1}\) 在 \(\ker d_j\) 中稠密；要得到稳定的精确消元，还需要像闭合。下面先给出反例，再给出必要且充分的判据、构造和范数控制。

### 反例

取 \(r=1\)，令
\[
H_0=H_1=L^2((0,1);\mathbb C),\qquad
(d_0f)(t)=t f(t).
\]
显然 \(\ker d_0=0\)。另一方面，对任意 \(g\in H_1\)，令
\[
f_n(t)=\mathbf 1_{[1/n,1]}(t)\frac{g(t)}t.
\]
则 \(f_n\in H_0\)，且 \(d_0f_n\to g\)，所以 \(\overline{\operatorname{ran}d_0}=H_1\)。因此 \(R_0=R_1=0\)。

但常数函数 \(1\) 不在 \(\operatorname{ran}d_0\) 中：它的原像只能是 \(1/t\)，而这不属于 \(L^2(0,1)\)。故不可能有 \(d_0s_1=I_{H_1}\)。甚至有界左逆也不存在，因为对
\[
u_n=\sqrt n\,\mathbf 1_{(0,1/n)}
\]
有
\[
\|u_n\|=1,\qquad \|d_0u_n\|=\frac1{\sqrt3\,n}\longrightarrow0.
\]

此例中 \(L_0=L_1\) 都是乘以 \(t^2\) 的算子。常数函数 \(1\) 也不在它们的像中，因此它们没有右逆。

### 精确稳定消元定理

在题设 \(R_j=0\) 下，以下条件等价：

1. 存在有界算子 \(s_j:H_j\to H_{j-1}\)，满足
   \[
   d_{j-1}s_j+s_{j+1}d_j=I_{H_j}\qquad(0\le j\le r).
   \]
2. 每个 \(\operatorname{ran}d_j\) 都是闭子空间。
3. 每个 \(L_j\) 都有有界右逆。
4. 存在 \(\lambda>0\)，使所有 \(j\) 和 \(x\in H_j\) 满足
   \[
   \|d_{j-1}^*x\|^2+\|d_jx\|^2\ge \lambda\|x\|^2.
   \tag{1}
   \]

这些条件成立时，可以作如下构造。令
\[
B_j=\ker d_j=\operatorname{ran}d_{j-1},\qquad
E_j=B_j^\perp.
\]
对于 \(0\le j<r\)，限制算子
\[
D_j=d_j|_{E_j}:E_j\longrightarrow B_{j+1}
\]
是有界双射。记其有界逆为 \(T_j\)，并令 \(c_j=\|T_j\|\)。若 \(E_j=0\)，取 \(c_j=0\)；另约定 \(c_{-1}=c_r=0\)。

用 \(P_{B_j}\) 表示到 \(B_j\) 的正交投影，定义
\[
s_j=T_{j-1}P_{B_j}\quad(1\le j\le r),
\qquad s_0=s_{r+1}=0.
\tag{2}
\]
再定义
\[
G_j=s_j^*s_j+s_{j+1}s_{j+1}^*.
\tag{3}
\]
则
\[
d_{j-1}s_j+s_{j+1}d_j=I_{H_j},\qquad
L_jG_j=G_jL_j=I_{H_j},
\]
并且有精确范数公式
\[
\boxed{\ \|s_{j+1}\|=c_j,\qquad
\|G_j\|=\max\{c_{j-1}^2,c_j^2\}.\ }
\tag{4}
\]
这里
\[
c_j=
\left(\inf_{\substack{x\in E_j\\ \|x\|=1}}\|d_jx\|\right)^{-1}
\]
在 \(E_j\ne0\) 时成立。构造 (2) 的每个范数都是最小的：任何满足消元恒等式的另一组有界算子 \(\sigma_j\) 都满足 \(\|\sigma_{j+1}\|\ge c_j\)。

特别地，若已知统一估计 (1)，则可以取上述构造，使
\[
\|s_j\|\le \lambda^{-1/2},\qquad
\|G_j\|\le \lambda^{-1}.
\tag{5}
\]

### 证明

先设各像闭合。题设给出正交分解 \(H_j=B_j\oplus E_j\)，而 \(D_j:E_j\to B_{j+1}\) 是有界双射，故由有界逆定理，\(T_j\) 有界。由 (2) 直接得到
\[
d_{j-1}s_j=P_{B_j},\qquad
s_{j+1}d_j=P_{E_j},
\]
两式相加即为消元恒等式。

在分解 \(H_j=B_j\oplus E_j\) 下，\(L_j\) 的分块形式为
\[
L_j=
\begin{pmatrix}
D_{j-1}D_{j-1}^*&0\\
0&D_j^*D_j
\end{pmatrix},
\]
端点处不存在的分块按零空间处理。它的逆为
\[
L_j^{-1}=
\begin{pmatrix}
T_{j-1}^*T_{j-1}&0\\
0&T_jT_j^*
\end{pmatrix},
\]
这正是 (3)。由 \(\|T^*T\|=\|TT^*\|=\|T\|^2\)，得到 (4)。

令 \(C=\max_{0\le j<r}c_j\)。若 \(C>0\)，对 \(x=b+e\in B_j\oplus E_j\)，有
\[
\begin{aligned}
\|d_{j-1}^*x\|^2+\|d_jx\|^2
&=\|D_{j-1}^*b\|^2+\|D_je\|^2\\
&\ge C^{-2}\bigl(\|b\|^2+\|e\|^2\bigr)
=C^{-2}\|x\|^2.
\end{aligned}
\]
因此得到 (1)；零空间的退化情形中任取 \(\lambda>0\) 即可。

反过来，若存在消元算子，则对 \(x\in\ker d_j\)，恒等式给出
\[
x=d_{j-1}s_jx.
\]
故 \(\operatorname{ran}d_{j-1}=\ker d_j\)，从而每个像都闭合。

若每个 \(L_j\) 有右逆，则每个 \(L_j\) 满射。对 \(x\in\ker d_j\)，取 \(u\) 使 \(L_ju=x\)。分解
\[
x=d_{j-1}d_{j-1}^*u+d_j^*d_ju
\]
的第一项属于 \(\ker d_j\)，第二项属于 \((\ker d_j)^\perp\)。由于 \(x\in\ker d_j\)，第二项必为零，于是 \(x\in\operatorname{ran}d_{j-1}\)。这再次说明各像闭合。

最后，若 (1) 成立，则
\[
\|L_jx\|\ge\lambda\|x\|.
\]
所以 \(L_j\) 的像闭合、核为零；又因为 \(L_j\) 自伴，像也稠密，故 \(L_j\) 可逆，且 \(\|L_j^{-1}\|\le1/\lambda\)。对 \(e\in E_j\) 应用 (1) 得 \(\|d_je\|\ge\sqrt\lambda\,\|e\|\)，因此 \(c_j\le\lambda^{-1/2}\)，得到 (5)。这证明了四个条件的等价性。

范数最小性也由消元恒等式直接得到：若 \(y\in B_{j+1}=\ker d_{j+1}\)，则
\[
d_j\sigma_{j+1}y=y,
\qquad
P_{E_j}\sigma_{j+1}y=T_jy.
\]
取上确界便得 \(\|\sigma_{j+1}\|\ge\|T_j\|=c_j\)。

### 仅在题设下仍可得到的正则化消元

虽然精确稳定消元可能不存在，题设总能给出一族有界的近似算子。对 \(\varepsilon>0\)，令
\[
G_{j,\varepsilon}=(L_j+\varepsilon I)^{-1},\qquad
s_{j,\varepsilon}=d_{j-1}^*G_{j,\varepsilon},
\]
并取端点 \(s_{0,\varepsilon}=s_{r+1,\varepsilon}=0\)。它们满足
\[
\|G_{j,\varepsilon}\|\le\frac1\varepsilon,\qquad
\|s_{j,\varepsilon}\|\le\frac1{2\sqrt\varepsilon},
\tag{6}
\]
以及
\[
d_{j-1}s_{j,\varepsilon}
+s_{j+1,\varepsilon}d_j
=L_jG_{j,\varepsilon}
=I-\varepsilon G_{j,\varepsilon}
\xrightarrow[\varepsilon\downarrow0]{\text{强}} I.
\tag{7}
\]

证明中，\(L_{j+1}d_j=d_jL_j\) 给出
\(G_{j+1,\varepsilon}d_j=d_jG_{j,\varepsilon}\)，从而得到 (7) 的恒等式。第一个范数估计来自 \(L_j+\varepsilon I\ge\varepsilon I\)。对于第二个，记 \(G=G_{j,\varepsilon}\)，利用
\[
d_{j-1}d_{j-1}^*\le L_j,\qquad
4\varepsilon G L_jG=I-(I-2\varepsilon G)^2\le I,
\]
即可得到 (6)。

此外，
\[
\ker L_j=\ker d_j\cap\ker d_{j-1}^*=\{0\},
\]
其中最后一步使用了题设的稠密像条件。因此自伴算子 \(L_j\) 的像稠密。算子 \(\varepsilon G_{j,\varepsilon}\) 的范数不超过 \(1\)，且对像中的向量 \(L_jy\) 有
\[
\varepsilon G_{j,\varepsilon}L_jy
=\varepsilon(I-\varepsilon G_{j,\varepsilon})y\longrightarrow0.
\]
由稠密性便得到 (7) 中的强收敛。

这种收敛一般不能提升为算子范数收敛：若某个 \(L_j\) 不满射，则对每个 \(\varepsilon>0\)，
\[
\|\varepsilon G_{j,\varepsilon}\|=1.
\]
否则 \(\|\varepsilon G_{j,\varepsilon}\|<1\) 会使
\(L_jG_{j,\varepsilon}=I-\varepsilon G_{j,\varepsilon}\) 可逆，从而给出 \(L_j\) 的有界右逆。在上述反例中，甚至
\[
\|s_{1,\varepsilon}\|=\frac1{2\sqrt\varepsilon}\qquad(0<\varepsilon\le1),
\]
所以正则化算子的范数确实会发散。