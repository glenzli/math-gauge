下面给出完整结论。为避免符号冲突，把题中的集合 \(\mathscr R,\mathscr C\) 简记为  
\[
\mathcal R_{L,M},\qquad \mathcal C_{L,M}.
\]
所有“块大小”均指题给的 \(n_1,\dots,n_r\)。记
\[
a_n=\frac{n(n-1)}2,\qquad s_n=\frac{n(n+1)}2.
\]

---

## 0. 标准引理（下文反复使用）

**引理 A（幂等元唯一提升）**  
设 \(B\) 是有限 \(\mathbb Z_2\)-代数，且 \(B/2B\simeq \mathbb F_2^r\)。则 \(B/2B\) 的每个幂等元在 \(B\) 中有唯一幂等提升。对 \(\mathbb Z/4\) 代数同样成立，因为 \((2)\) 是幂零理想。

**引理 B（奇幺模二次型）**  
设 \(G\in M_n(\mathbb Z_2)\) 对称且 \(G\equiv I_n\pmod4\)。则 \(G\) 在 \(O_L\) 上与标准型 \(I_n\) 等价，当且仅当
\[
\det G\in (O_L^\times)^2.
\]
因 \(G\equiv I\pmod4\)，故 \(\det G\equiv1\pmod4\)，于是这又等价于
\[
\det G\equiv1\pmod8.
\]
对 \(L=F,K_{-1},K_2\) 判准相同；原因是 \(5\bmod8\) 在 \(K_{\pm}\) 中仍非平方（\(K_\mu\) 是分歧二次扩域）。

**引理 C（正交群的 congruence 核）**  
对标准型，令
\[
\Gamma_n^F(M)=\ker\bigl(O_n(\mathbb Z_2)\to O_n(\mathbb Z/2^M)\bigr),
\]
\[
\Gamma_n^K(M)=\ker\bigl(O_n(O_K)\to O_n(O_K/2^M O_K)\bigr)
\]
其中 \(K=K_\mu\)，并要求元素在两边都 \(\equiv I\pmod2\)。令 \(\mathcal K_n^L(M)\) 为模 \(2^M\) 的全部该类矩阵类，\(\mathrm{Im}_n^L(M)\) 为真正可提升矩阵类的像。通过逐层展开 \(U=I+2X\)（或 \(U=I+\pi^2X\)）及
\[
X+X^{\mathsf T}+2X^{\mathsf T}X=0
\]
可得：

\[
|\mathcal K_n^F(2)|=2^{s_n},\qquad
|\mathcal K_n^F(M)|=2^{\,n^2+1+(M-3)a_n}\quad(M\ge3),
\]
\[
|\mathcal K_n^K(M)|=2^{\,(M-1)n^2+n}\qquad(M\ge2),
\]
以及
\[
|\mathrm{Im}_n^F(M)|=2^{\,n+(M-2)a_n}\qquad(M\ge2),
\]
\[
|\mathrm{Im}_n^K(M)|=2^{\,s_n+(2M-3)a_n}\qquad(M\ge2).
\]
这些公式也就是题中相应集合的基数的“单块因子”。

---

## 1. \(S_L(A)\) 的可行性、\(\mathcal R_{L,M},\mathcal C_{L,M}\) 的空集判准与基数

### 1.1 由 \(A_i\bmod4\) 计算可行性

令 \(\mathcal A_4\subset M_d(\mathbb Z/4)\) 为 \(A_i\bmod4\) 生成的 \(\mathbb Z/4\)-代数。由于 \(A_i\bmod2=E_i\)，且
\[
(\mathbb Z/4)\text{-}\mathcal A_4/2\mathcal A_4\simeq\mathbb F_2^r,
\]
由引理 A，存在唯一的相互正交对称幂等元
\[
Q_i\in \mathcal A_4,\qquad Q_i\equiv E_i\pmod2,
\]
且 \(\sum_iQ_i=I_d\)。它们可有限计算：逐层解线性方程
\[
Q_i^2=Q_i,\qquad Q_iA_j=A_jQ_i\pmod4,\qquad Q_i\equiv E_i\pmod2.
\]

把 \(Q_i\) 按 \(I_i\) 与其余坐标分块：
\[
Q_i=
\begin{pmatrix}
G_i&B_i\\
B_i^{\mathsf T}&D_i
\end{pmatrix},
\qquad
G_i\in M_{n_i}(\mathbb Z/4),
\]
则 \(B_i\equiv0\pmod2\)。写
\[
B_i=2C_i,\qquad C_i\in M_{n_i\times(d-n_i)}(\mathbb F_2).
\]
则
\[
\det G_i\equiv 1+4\,\operatorname{tr}(C_iC_i^{\mathsf T})\pmod8.
\]
因此
\[
\boxed{
S_L(A)\ne\varnothing
\iff
\operatorname{tr}(C_iC_i^{\mathsf T})=0\quad(\forall i)
\iff
\sum_{u,v}(C_i)_{uv}=0\quad(\forall i).
}
\]
等价地，对每个 \(i\)，由 \(Q_i\) 给出的子格
\[
W_i=Q_i(\mathbb Z_2^d)
\]
上的标准型 \(G_i=Q_i|_{I_i}\) 与标准型 \(I_{n_i}\) 等价，即 \(\det G_i\equiv1\pmod8\)。

这个判准只用 \(A_i\bmod4\)，因为 \(Q_i\bmod4\) 由 \(A_i\bmod4\) 唯一确定。

若 \(S_L(A)\ne\varnothing\)，则对任一 \(U_0\in S_L(A)\)，
\[
S_L(A)=U_0\,H_L,
\qquad
H_L=\prod_{j=1}^r\Gamma_{n_j}(2O_L),
\]
其中
\[
\Gamma_n(2O_L)=\{U\in O_n(O_L):U\equiv I_n\pmod{2O_L}\}.
\]
因此 \(S_L(A)\) 是一个 torsor，特别地非空时为无限紧致 \(2\)-进集合。

### 1.2 空集条件

对 \(M\ge2\)：
\[
\mathcal C_{L,2}(A)\ne\varnothing
\quad\text{对一切合法 }A\text{ 恒成立}.
\]
并且
\[
\boxed{
\mathcal C_{L,M}(A)\ne\varnothing\quad(M\ge3)
\iff S_L(A)\ne\varnothing,
}
\]
\[
\boxed{
\mathcal R_{L,M}(A)\ne\varnothing
\iff S_L(A)\ne\varnothing.
}
\]
所以若 \(S_L(A)=\varnothing\)，则所有 \(M\ge2\) 的 \(\mathcal R_{L,M}(A)\) 都为空；而 \(\mathcal C_{L,2}(A)\) 仍非空，但从 \(M=3\) 起全空。

### 1.3 基数

以下公式均按块相乘。

定义单块基数：
\[
\kappa_n^F(2)=2^{s_n},\qquad
\kappa_n^F(M)=2^{\,n^2+1+(M-3)a_n}\quad(M\ge3),
\]
\[
\kappa_n^K(M)=2^{\,(M-1)n^2+n}\quad(M\ge2),
\]
以及
\[
\rho_n^F(M)=2^{\,n+(M-2)a_n}\quad(M\ge2),
\]
\[
\rho_n^K(M)=2^{\,s_n+(2M-3)a_n}\quad(M\ge2).
\]
若相应集合非空，则
\[
\boxed{
|\mathcal C_{L,M}(A)|
=
\prod_{j=1}^r \kappa_{n_j}^L(M),
\qquad
|\mathcal R_{L,M}(A)|
=
\prod_{j=1}^r \rho_{n_j}^L(M).
}
\]
若为空，则基数为 \(0\)。

特别地，当 \(S_L(A)\ne\varnothing\) 时：
\[
|\mathcal C_{L,M}(A)|=\prod_j\kappa_{n_j}^L(M),
\qquad
|\mathcal R_{L,M}(A)|=\prod_j\rho_{n_j}^L(M),
\]
且一般
\[
|\mathcal R_{L,M}(A)|<|\mathcal C_{L,M}(A)|
\]
当且仅当某个 \(n_j\ge2\)。例如最极端 \(n_j=1\) 时，\(\rho_1^L=\kappa\) 在某些精度下相符，但一般 \(n\ge2\) 时
\[
\mathcal R_{L,M}(A)\subsetneq \mathcal C_{L,M}(A).
\]

### 1.4 给定类 \(\bar U\in\mathcal C_{L,M}(A)\) 何时属于 \(\mathcal R_{L,M}(A)\)

可用逐层可提升性核验。

**\(L=F\)**：从精度 \(M\) 到 \(M+1\)，设当前类由 \(U_k\) 表示，精度 \(2^k\)。把它提升为
\[
U_{k+1}=U_k+2^kY_k.
\]
令
\[
B_k=\frac{U_k^{\mathsf T}U_k-I}{2^k}\pmod2.
\]
存在提升当且仅当
\[
B_k\text{ 的对角线全为 }0,
\]
即 \(B_k\) 在 \(\mathbb F_2\) 上为交错矩阵。若可提升，则提升数为
\[
2^{s}=2^{n(n+1)/2}
\]
（按块取乘积）。因此
\[
\bar U\in\mathcal R_{F,M}(A)
\iff
\text{上述提升过程对所有 }k\ge M\text{ 永远可以进行}.
\]
由紧致性，这等价于：对每个 \(k\ge M\)，类在 \(\mathcal C_{F,k}\) 中都有提升。

**\(L=K_\mu\)**：类似地，在精度 \(2^kO_K\) 处添加
\[
U_{k+1}=U_k+2^kY_k,
\]
逐层核验
\[
U_{k+1}^{\mathsf T}U_{k+1}\equiv I\pmod{2^{k+1}O_K}.
\]
逐次线性化后仍得到一个有限线性方程组；若可解，则所有提升构成一个显式仿射空间。记其解数为 \(b_{n_1,\dots,n_r}(k)\)（可用下表的约化纤维公式计算）。则
\[
\bar U\in\mathcal R_{K,M}(A)
\iff
\text{该逐层方程组对所有 }k\ge M\text{ 均可解}.
\]
这就是可核验的必要充分条件。

---

## 2. \(\sigma_\mu\)-固定点、轨道数、约化像与纤维

以下均写 \(K=K_\mu\)。注意 \(K_{-1}\) 与 \(K_2\) 的基数完全相同；差别只在 \(\theta\) 在 \(\mathcal O_K\) 中是否为一致化参数，但最终的 \(|C^\sigma|,|R^\sigma|\) 公式相同。

### 2.1 \(\mathcal C_{K,M}(A)\) 的固定点

设
\[
\bar U\in\mathcal C_{K,M}(A).
\]
把 \(\bar U\) 唯一写成
\[
\bar U=A+\theta B,
\qquad
A,B\in M_d(\mathbb Z/2^M).
\]
则
\[
\sigma_\mu(\bar U)\equiv \bar U\pmod{2^M O_K}
\iff
B\equiv0\pmod{2^{M-1}}.
\]
于是
\[
\bar U=A+2^{M-1}\theta C,
\qquad
C\in M_d(\mathbb F_2).
\]
正交条件和分块条件给出：
\[
A^{\mathsf T}A=I\pmod{2^M},
\qquad
A^{\mathsf T}C+C^{\mathsf T}A=0\pmod2.
\]
因 \(A\equiv I\pmod2\)，后一式即
\[
C+C^{\mathsf T}=0\quad\text{于 }M_d(\mathbb F_2),
\]
也就是 \(C\) 对称。进一步，分块交换条件强制 \(C\) 为块对角：
\[
C=\operatorname{diag}(C_1,\dots,C_r),
\qquad
C_j=C_j^{\mathsf T}\in M_{n_j}(\mathbb F_2).
\]
因此
\[
\boxed{
\mathcal C_{K,M}(A)^{\sigma_\mu}
=
\left\{
A+2^{M-1}\theta C:
A\in\mathcal C_{F,M}(A),\
C=\bigoplus_{j=1}^r C_j,\ 
C_j=C_j^{\mathsf T}\in M_{n_j}(\mathbb F_2)
\right\}.
}
\]
所以
\[
\boxed{
|\mathcal C_{K,M}(A)^{\sigma_\mu}|
=
|\mathcal C_{F,M}(A)|\cdot
2^{\,S},
\qquad
S:=\sum_{j=1}^r s_{n_j}.
}
\]
此式在 \(\mathcal C_{F,M}(A)\ne\varnothing\) 时适用；否则左端为 \(0\)。特别地，当 \(M=2\) 时恒有
\[
|\mathcal C_{K,2}(A)^{\sigma_\mu}|
=
|\mathcal C_{K,2}(A)|,
\]
即 \(\sigma_\mu\) 在精度 \(2\) 上作用平凡。

### 2.2 \(\mathcal R_{K,M}(A)\) 的固定点

设 \(S_{K}(A)\ne\varnothing\)。用单块基数
\[
\boxed{
|\mathcal R_{K,M}(A)^{\sigma_\mu}|
=
2^{\,S+(M-1)A},
\qquad
A:=\sum_{j=1}^r a_{n_j}.
}
\]
当 \(S_K(A)=\varnothing\) 时
\[
\mathcal R_{K,M}(A)^{\sigma_\mu}=\varnothing.
\]

同样，
\[
|\mathcal R_{K,M}(A)|
=
2^{\,S+(2M-3)A}.
\]
故若 \(\mathcal R_{K,M}(A)\ne\varnothing\)，则
\[
\boxed{
|\mathcal R_{K,M}(A)/\langle\sigma_\mu\rangle|
=
\frac{
2^{\,S+(2M-3)A}
+
2^{\,S+(M-1)A}
}{2}.
}
\]

对 \(\mathcal C\)，若 \(\mathcal C_{K,M}(A)\ne\varnothing\)，则
\[
\boxed{
|\mathcal C_{K,M}(A)/\langle\sigma_\mu\rangle|
=
\frac{
|\mathcal C_{K,M}(A)|
+
|\mathcal C_{F,M}(A)|\,2^S
}{2},
}
\]
其中
\[
|\mathcal C_{K,M}(A)|
=
\prod_{j=1}^r 2^{(M-1)n_j^2+n_j}.
\]
若 \(M=2\)，则固定点数等于总点数，轨道数为总数。

### 2.3 从精度 \(M+1\) 到 \(M\) 的约化

记
\[
S=\sum_j s_{n_j},\qquad A=\sum_j a_{n_j}.
\]

#### (a) \(\mathcal R\) 的约化

对 \(L=F,K\)，只要目标层非空，
\[
\pi_{M+1\to M}:\mathcal R_{L,M+1}\twoheadrightarrow\mathcal R_{L,M}
\]
为满射。每个纤维大小均匀：
\[
\boxed{
\begin{cases}
|\pi^{-1}(\bar U)|=2^{A},&L=F,\\[2mm]
|\pi^{-1}(\bar U)|=2^{2A},&L=K.
\end{cases}
}
\]

#### (b) \(\mathcal C\) 的约化

对 \(L=F\)：若源 \(\mathcal C_{F,M+1}(A)\ne\varnothing\)，则
\[
\boxed{
\left|\pi\bigl(\mathcal C_{F,M+1}(A)\bigr)\right|
=
\frac{|\mathcal C_{F,M+1}(A)|}{2^S},
\qquad
\text{每个非空纤维大小}=2^S.
}
\]
像由上一小节 1.4 的交错条件刻画；若源为空，则像为空。

对 \(L=K\)：若源 \(\mathcal C_{K,M+1}(A)\ne\varnothing\)，则
\[
\boxed{
\left|\pi\bigl(\mathcal C_{K,M+1}(A)\bigr)\right|
=
\prod_{j=1}^r 2^{\,n_j^2(M-1)},
}
\]
且每个非空纤维大小均匀为
\[
\boxed{
2^{\sum_{j=1}^r n_j(n_j+1)}=2^{2S}.
}
\]
若源为空，则像为空。纤维的非空性同样由逐层方程
\[
U_{k+1}^{\mathsf T}U_{k+1}\equiv I\pmod{2^{k+1}O_K}
\]
的线性化可解性给出。

#### (c) 固定点集的约化

对 \(\mathcal C_K^\sigma\)：由
\[
\bar U=A+2^{M-1}\theta C
\]
可知，约化到 \(M\) 时顶层的 \(\theta C\) 项消失。因此
\[
\pi\bigl(\mathcal C_{K,M+1}^{\sigma}\bigr)
\]
恰为“缺陷项为零”的那些类，即由 \(\mathcal C_{F,M+1}\) 的像嵌入到 \(\mathcal C_{F,M}\) 所得。于是当源非空时
\[
\boxed{
\left|\pi\bigl(\mathcal C_{K,M+1}^{\sigma}\bigr)\right|
=
\frac{|\mathcal C_{F,M+1}(A)|}{2^S},
}
\]
每个非空纤维大小为
\[
\boxed{
2^{2S}.
}
\]

对 \(\mathcal R_K^\sigma\)：若 \(S_K(A)\ne\varnothing\)，则
\[
\boxed{
\left|\pi\bigl(\mathcal R_{K,M+1}^{\sigma}\bigr)\right|
=
2^{\,S+(M-2)A},
}
\]
且每个非空纤维大小为
\[
\boxed{
2^{2A}.
}
\]
当 \(S_K(A)=\varnothing\) 时，上述集合均为空。

### 2.4 哪些固定类能提升为真正的 \(\sigma\)-固定解

若 \(U\in S_K(A)\) 且 \(\sigma_\mu(U)=U\)，则 \(U\) 的系数全在 \(F=\mathbb Q_2\) 中，故
\[
S_K(A)^{\sigma_\mu}=S_F(A).
\]
因此：

- 一个 \(\mathcal C_{K,M}(A)\) 中的固定类
  \[
  \bar U=A+2^{M-1}\theta C
  \]
  能提升为真正的 \(\sigma_\mu\)-固定解
  \[
  U\in S_K(A),\qquad \sigma_\mu(U)=U
  \]
  当且仅当
  \[
  \boxed{
  C=0
  \quad\text{且}\quad
  A\in\mathcal R_{F,M}(A).
  }
  \]
  这里 \(A\) 是基域精度 \(M\) 的类；\(A\in\mathcal R_{F,M}\) 正表示它能提升为 \(S_F(A)\) 中的真正解。

- 一个固定类能作为某条逐层相容的固定矩阵类序列
  \[
  (\bar U_m\in\mathcal C_{K,m}^{\sigma})_{m\ge M}
  \]
  在精度 \(M\) 的分量，当且仅当同样有
  \[
  \boxed{
  C=0\quad\text{且}\quad A\in\mathcal R_{F,M}(A).
  }
  \]
  原因是从 \(M+1\) 到 \(M\) 的固定类约化会把顶层的非零 \(C\) 杀死；若某一层 \(C\ne0\)，它甚至不能提升到下一层的固定点集。所以无限相容的固定类序列的每一层缺陷都必须为零，其极限正是 \(S_F(A)\) 中的一个真正固定元素。

- 对 \(\mathcal R_{K,M}^{\sigma}\) 同样：一个固定类能来自真正的 \(\sigma\)-固定解，当且仅当它属于嵌入的
  \[
  \mathcal R_{F,M}(A)\subset S_K(A)^{\sigma_\mu}.
  \]

---

## 3. 从 \(K_\mu\) 向基域下降的最优精度 \(N\)

固定块大小、\(\mu\)、\(M\ge2\)。令 \(N_{\max}\) 为满足题述性质的最大整数 \(N\in\{0,\dots,M\}\)。

### 3.1 统一上界

设
\[
U\in S_K(A),\qquad \sigma_\mu(U)\equiv U\pmod{2^M O_K}.
\]
由 2.1，存在
\[
U\equiv A+2^{M-1}\theta C\pmod{2^M O_K},
\]
其中
\[
A\in\mathcal C_{F,M}(A),\qquad
C=\operatorname{diag}(C_1,\dots,C_r),\quad
C_j=C_j^{\mathsf T}\in M_{n_j}(\mathbb F_2).
\]
若 \(S_K(A)\ne\varnothing\)，由第 1 节可行性判准，\(S_F(A)\ne\varnothing\)。因为 \(\mathcal R_{F,M}(A)=\mathcal C_{F,M}(A)\) 当 \(S_F(A)\ne\varnothing\)，类 \(A\) 可提升为某个
\[
W\in S_F(A),\qquad W\equiv A\pmod{2^M}.
\]
于是
\[
U\equiv W\pmod{2^{M-1}O_K}.
\]
因此对一切情形
\[
\boxed{
N_{\max}\ge M-1.
}
\]

### 3.2 最优性：只要某个 \(n_j\ge2\)，就有 \(N_{\max}=M-1\)

设某块 \(n_j\ge2\)。取合法输入
\[
A_i=E_i\qquad(i=1,\dots,r).
\]
记
\[
J=\begin{pmatrix}0&1\\-1&0\end{pmatrix}.
\]
在 \(n_j\) 维块中取矩阵
\[
U_M^{(j)}
=
(I+2^{M-2}\theta J)(I-2^{M-2}\theta J)^{-1}
\oplus I_{n_j-2},
\]
并令其余块上为恒等矩阵，从而得到
\[
U_M\in O_d(O_K).
\]
Cayley 变换保证
\[
U_M^{\mathsf T}U_M=I_d,\qquad
U_M\equiv I_d\pmod2.
\]
展开
\[
U_M^{(j)}
=I+2^{M-1}\theta J+O(2^M).
\]
因此
\[
U_M\equiv I+2^{M-1}\theta J\pmod{2^M},
\]
且
\[
\sigma_\mu(U_M)\equiv U_M\pmod{2^M O_K},
\]
因为
\[
\sigma_\mu(U_M)-U_M
=2\cdot 2^{M-1}\theta J+O(2^M)
\equiv0\pmod{2^M O_K}.
\]
同时 \(U_M\) 是块对角的，故
\[
U_M^{\mathsf T}E_iU_M=E_i,
\]
所以 \(U_M\in S_K(A)\)。

但任何基域矩阵 \(W\in S_F(A)\subset M_d(\mathbb Z_2)\)，模 \(2^M O_K\) 后 \(\theta\)-系数为零；而 \(U_M\bmod2^M O_K\) 的 \(\theta\)-系数在 \(2^{M-1}\) 位为 \(J\ne0\)。故
\[
U_M\not\equiv W\pmod{2^M O_K}
\]
对一切 \(W\in S_F(A)\) 都成立。于是该 \(A,U\) 下不能取 \(N=M\)，从而
\[
N_{\max}\le M-1.
\]
结合 3.1：
\[
\boxed{
\text{若 }\max_j n_j\ge2,\qquad
N_{\max}=M-1.
}
\]

### 3.3 全部 \(n_j=1\) 的情形：精确下降

若
\[
n_1=\cdots=n_r=1,
\]
则
\[
H_L=\prod_{j=1}^r O_1(O_L)=\{\pm1\}^r
\]
中每个元素都来自基域，且被 \(\sigma_\mu\) 固定。若 \(S_K(A)\ne\varnothing\)，取 \(U_0\in S_F(A)\)（由同一可行性判准），则
\[
S_K(A)=U_0\{\pm1\}^r=S_F(A)\subset GL_d(\mathbb Z_2).
\]
所以每个 \(U\in S_K(A)\) 本身就在 \(S_F(A)\) 中，特别地
\[
U\equiv U\pmod{2^M O_K}.
\]
故
\[
\boxed{
\text{若 }n_1=\cdots=n_r=1,\qquad N_{\max}=M.
}
\]
若 \(S_K(A)=\varnothing\)，题设中的 \(U\) 不存在，命题空洞成立，仍可取 \(N=M\)。

### 3.4 对给定 \(A,U\)，何时可以取 \(N=M\)

对具体的合法 \(A\) 和
\[
U\in S_K(A),\qquad \sigma_\mu(U)\equiv U\pmod{2^M O_K},
\]
有
\[
\boxed{
N=M
\iff
\exists W\in S_F(A)\ \text{s.t.}\ U\equiv W\pmod{2^M O_K}.
}
\]
等价地，把 \(U\) 的固定类写成
\[
U\equiv A_0+2^{M-1}\theta C\pmod{2^M O_K},
\qquad
A_0\in\mathcal C_{F,M}(A),
\]
则
\[
\boxed{
N=M
\iff
C=0
\ \text{且}\ A_0\in\mathcal R_{F,M}(A).
}
\]
若 \(C\ne0\)，则连模 \(2^M\) 的基域逼近都不存在，因此不可能精确下降；若 \(C=0\) 但 \(A_0\notin\mathcal R_{F,M}(A)\)，则该类只是形式上的固定类，不能提升为真正的基域正交解，仍不能取 \(N=M\)。

---

## 4. 结论汇总

1. **可行性**：  
   \(S_L(A)\ne\varnothing\)（对 \(L=F,K_{-1},K_2\) 同时成立）当且仅当由 \(A_i\bmod4\) 算出的唯一提升幂等元 \(Q_i\) 满足
   \[
   \operatorname{tr}(C_iC_i^{\mathsf T})=0\quad(\forall i),
   \]
   其中 \(B_i=Q_i|_{I_i\times I_i^c}=2C_i\)。这等价于每个压缩型 \(Q_i|_{I_i}\) 的行列式在 \(\mathbb Z_2\) 中为平方（即 \(\equiv1\pmod8\)）。

2. **基数**：若相应集合非空，则
   \[
   |\mathcal C_{R,M}|=\prod_j\kappa_{n_j}^L(M),
   \qquad
   |\mathcal R_{L,M}|=\prod_j\rho_{n_j}^L(M),
   \]
   其中
   \[
   \kappa_n^F(2)=2^{s_n},\quad
   \kappa_n^F(M)=2^{n^2+1+(M-3)a_n}\ (M\ge3),
   \]
   \[
   \kappa_n^K(M)=2^{(M-1)n^2+n},
   \]
   \[
   \rho_n^F(M)=2^{n+(M-2)a_n},
   \qquad
   \rho_n^K(M)=2^{s_n+(2M-3)a_n}.
   \]
   \(\mathcal C_{L,2}\) 恒非空；\(M\ge3\) 时 \(\mathcal C_{L,M}\) 非空当且仅当 \(S_L(A)\ne\varnothing\)；\(\mathcal R_{L,M}\) 非空同样当且仅当 \(S_L(A)\ne\varnothing\)。

3. **固定点与轨道**：
   \[
   \mathcal C_{K,M}^{\sigma_\mu}
   \cong
   \mathcal C_{F,M}\times\prod_{j=1}^r \operatorname{Sym}_{n_j}(\mathbb F_2),
   \]
   \[
   |\mathcal C_{K,M}^{\sigma_\mu}|
   =
   |\mathcal C_{F,M}|\,2^{S},
   \]
   \[
   |\mathcal R_{K,M}^{\sigma_\mu}|
   =
   2^{S+(M-1)A}.
   \]
   轨道数由 Burnside 公式
   \[
   |X/\langle\sigma\rangle|
   =
   \frac{|X|+|X^\sigma|}{2}
   \]
   给出。

4. **约化**：  
   \(\mathcal R_{K,M+1}\to\mathcal R_{K,M}\) 为满射，纤维大小 \(2^{2A}\)；  
   \(\mathcal R_{F,M+1}\to\mathcal R_{F,M}\) 为满射，纤维大小 \(2^A\)。  
   \(\mathcal C\) 的约化像不再满射；其像、非空纤维大小已由第 2.3 节给出。

5. **下降精度**：
   \[
   \boxed{
   N_{\max}=
   \begin{cases}
   M,&\text{若 }n_1=\cdots=n_r=1,\\[1mm]
   M-1,&\text{若 }\max_j n_j\ge2.
   \end{cases}}
   \]
   对给定 \(A,U\)，能取 \(N=M\) 当且仅当 \(U\) 模 \(2^M O_K\) 已等于某个 \(W\in S_F(A)\)，等价地其固定类的缺陷矩阵 \(C=0\) 且基域部分 \(A_0\in\mathcal R_{F,M}(A)\)。若 \(C\ne0\)，该固定类既不能提升为真正的 \(\sigma\)-固定解，也不能出现在任何逐层相容的固定类序列中；它在精度 \(M\) 是“终止”的。