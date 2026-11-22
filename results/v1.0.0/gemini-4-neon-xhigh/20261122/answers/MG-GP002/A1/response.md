### 记号与预备引理

全文采用题设约定：$\mathbb T^2 = \mathbb R^2/\mathbb Z^2$ 配归一化 Haar 测度 $dy$（$\int_{\mathbb T^2}1\,dy=1$），记 $e_k(y)=e^{2\pi i k\cdot y}$（$k=(k_1,k_2)\in\mathbb Z^2$），$|k|=(k_1^2+k_2^2)^{1/2}$，$\langle k\rangle=(1+|k|^2)^{1/2}$。对 $u\in C^\infty(\mathbb T^2;\mathbb C)$，记
$$\widehat u(k)=\int_{\mathbb T^2}u(y)e^{-2\pi i k\cdot y}\,dy,\qquad \|u\|_{H^r}^2=\sum_{k\in\mathbb Z^2}\langle k\rangle^{2r}|\widehat u(k)|^2\quad(r\in\mathbb R).$$
记 $\mathbb N=\{1,2,\dots\}$，$\mathbb N_0=\{0,1,2,\dots\}$。先给出后续反复使用的两条基本事实，并核验其适用条件：

1. **分部积分与微分系数**：对任意 $u\in C^\infty(\mathbb T^2;\mathbb C)$ 与 $(a,b)\in\mathbb N_0^2$，由于 $u$ 及其各阶偏导数关于 $y_1,y_2$ 均为 $1$-周期函数，在 $[0,1]^2$ 上分部积分时边界项完全抵消，故
   $$\widehat{\partial_1^a\partial_2^b u}(k)=(2\pi i k_1)^a(2\pi i k_2)^b\widehat u(k)\qquad(k\in\mathbb Z^2).$$
   特别地，对 $N_\alpha=\alpha\partial_1+\partial_2$，有
   $$\widehat{N_\alpha u}(k)=2\pi i(\alpha k_1+k_2)\widehat u(k)\qquad(k\in\mathbb Z^2).$$
2. **格点可和性引理**：对任意实数 $\tau>2$，级数 $\sum_{k\in\mathbb Z^2}\langle k\rangle^{-\tau}$ 收敛。
   *证明*：对任意 $k=(k_1,k_2)\in\mathbb Z^2$，展开得
   $$\langle k\rangle^4=(1+k_1^2+k_2^2)^2=(1+k_1^2)(1+k_2^2)+k_1^2+k_2^2+k_1^4+k_1^2k_2^2+k_2^4\ge(1+k_1^2)(1+k_2^2).$$
   两边取 $-\tau/4$ 次幂得 $\langle k\rangle^{-\tau}\le(1+k_1^2)^{-\tau/4}(1+k_2^2)^{-\tau/4}$，故
   $$\sum_{k\in\mathbb Z^2}\langle k\rangle^{-\tau}\le\left(\sum_{n\in\mathbb Z}(1+n^2)^{-\tau/4}\right)^2.$$
   对 $n\ne 0$ 有 $(1+n^2)^{-\tau/4}\le |n|^{-\tau/2}$，因 $\tau/2>1$，$p$-级数 $\sum_{n=1}^\infty n^{-\tau/2}$ 收敛，故 $\sum_{k\in\mathbb Z^2}\langle k\rangle^{-\tau}<\infty$。特别地，当 $\tau=4$ 时，因对 $n\ge 2$ 有 $(1+n^2)^{-1}<\frac{1}{n(n-1)}=\frac{1}{n-1}-\frac{1}{n}$，裂项得
   $$\sum_{n\in\mathbb Z}\frac{1}{1+n^2}<1+2\left(\frac{1}{2}+\sum_{n=2}^\infty\frac{1}{n(n-1)}\right)=4,\qquad\text{从而 }\sum_{k\in\mathbb Z^2}\langle k\rangle^{-4}<16.$$

---

## S1 有限频带上的逆

设 $\alpha\in\mathbb R\setminus\mathbb Q$，$N\ge 1$（实数或正整数皆可），记频率指标集
$$I_N:=\{k\in\mathbb Z^2:0<|k|\le N\}.$$
因 $(1,0)\in I_N$，故 $I_N$ 是有限非空集合；空间 $H_N=\operatorname{span}_{\mathbb C}\{e_k:k\in I_N\}\subset C^\infty_0(\mathbb T^2)$ 有限维且非零，其中任一元素 $F\in H_N$ 唯一表为 $F(y)=\sum_{k\in I_N}\widehat F(k)e^{2\pi i k\cdot y}$，且对 $k\notin I_N$ 有 $\widehat F(k)=0$。

### 1. 逆算子的构造

对每个 $k=(k_1,k_2)\in\mathbb Z^2\setminus\{0\}$，断言 $\alpha k_1+k_2\ne 0$：
- 若 $k_1=0$，则由 $k\ne 0$ 得 $k_2\ne 0$，故 $\alpha k_1+k_2=k_2\ne 0$；
- 若 $k_1\ne 0$，若 $\alpha k_1+k_2=0$ 则 $\alpha=-k_2/k_1\in\mathbb Q$，与 $\alpha$ 无理矛盾。

直接求导得 $N_\alpha e_k=2\pi i(\alpha k_1+k_2)e_k$，故 $N_\alpha$ 映 $H_N$ 入 $H_N$：
$$N_\alpha\!\left(\sum_{k\in I_N}\widehat u(k)e_k\right)=\sum_{k\in I_N}2\pi i(\alpha k_1+k_2)\widehat u(k)e_k.$$
定义线性算子 $R_{\alpha,N}:H_N\to H_N$ 为
$$(R_{\alpha,N}F)(y):=\sum_{0<|k|\le N}\frac{\widehat F(k)}{2\pi i(\alpha k_1+k_2)}\,e^{2\pi i k\cdot y}\qquad(F\in H_N).$$
由于 $I_N$ 有限且分母处处非零，$R_{\alpha,N}$ 良定义且映 $H_N$ 入 $H_N$。对任意 $F\in H_N$ 与 $u\in H_N$，逐项计算即得
$$N_\alpha(R_{\alpha,N}F)=\sum_{k\in I_N}2\pi i(\alpha k_1+k_2)\frac{\widehat F(k)}{2\pi i(\alpha k_1+k_2)}e_k=F,$$
$$R_{\alpha,N}(N_\alpha u)=\sum_{k\in I_N}\frac{2\pi i(\alpha k_1+k_2)\widehat u(k)}{2\pi i(\alpha k_1+k_2)}e_k=u.$$
因此 $R_{\alpha,N}=(N_\alpha|_{H_N})^{-1}$ 是 $N_\alpha|_{H_N}:H_N\to H_N$ 的唯一逆算子。

### 2. $H^r\to H^r$ 逆范数的精确式

对任意 $r\in\mathbb R$，$\|\cdot\|_{H^r}$ 是 $H_N$ 上的范数（因 $\langle k\rangle^{2r}>0$）。令
$$M_{\alpha,N}:=\max_{0<|k|\le N}\frac{1}{2\pi|\alpha k_1+k_2|}=\frac{1}{2\pi\min_{0<|k|\le N}|\alpha k_1+k_2|}\in(0,\infty),$$
最大值与最小值均因 $I_N$ 有限非空且 $|\alpha k_1+k_2|>0$ 而取到。

- **上界**：对任意 $F\in H_N$，
  $$\|(N_\alpha|_{H_N})^{-1}F\|_{H^r}^2=\sum_{k\in I_N}\langle k\rangle^{2r}\frac{|\widehat F(k)|^2}{4\pi^2|\alpha k_1+k_2|^2}\le M_{\alpha,N}^2\sum_{k\in I_N}\langle k\rangle^{2r}|\widehat F(k)|^2=M_{\alpha,N}^2\|F\|_{H^r}^2,$$
  故 $\|(N_\alpha|_{H_N})^{-1}\|_{H^r\to H^r}\le M_{\alpha,N}$。
- **下界（取到等号）**：取 $k^*\in I_N$ 使 $|\alpha k_1^*+k_2^*|=\min_{k\in I_N}|\alpha k_1+k_2|$，并取非零元 $F=e_{k^*}\in H_N$。此时 $\|e_{k^*}\|_{H^r}=\langle k^*\rangle^r>0$，且
  $$\|(N_\alpha|_{H_N})^{-1}e_{k^*}\|_{H^r}=\frac{\langle k^*\rangle^r}{2\pi|\alpha k_1^*+k_2^*|}=M_{\alpha,N}\|e_{k^*}\|_{H^r}.$$

综上，对任意实数 $r\in\mathbb R$，逆算子范数与 $r$ 无关，其精确式为
$$\left\|(N_\alpha|_{H_N})^{-1}\right\|_{H^r\to H^r}=\max_{0<|k|\le N}\frac{1}{2\pi|\alpha k_1+k_2|}=\frac{1}{2\pi\min_{0<|k|\le N}|\alpha k_1+k_2|}.$$

---

## S2 有算术界的截断误差

已知对全部 $k\in\mathbb Z^2\setminus\{0\}$ 有 $|\alpha k_1+k_2|\ge c\langle k\rangle^{-s}$（$c>0,s\ge 0$）。首先说明该条件蕴含 $\alpha\in\mathbb R\setminus\mathbb Q$：若 $\alpha=p/q$（$p\in\mathbb Z,q\in\mathbb N$），则 $k=(q,-p)\ne 0$ 满足 $\alpha k_1+k_2=0<c\langle k\rangle^{-s}$，矛盾。因此 S1 适用于 $\alpha$ 与任意 $N\ge 1$。

对光滑零均值函数 $F\in C^\infty_0(\mathbb T^2)$，有 $\widehat F(0)=\int_{\mathbb T^2}F=0$，其频带截断为 $F_N(y)=\sum_{0<|k|\le N}\widehat F(k)e^{2\pi i k\cdot y}\in H_N$，S1 给出的对应解为
$$u_N(y)=\sum_{0<|k|\le N}\frac{\widehat F(k)}{2\pi i(\alpha k_1+k_2)}\,e^{2\pi i k\cdot y}.$$

### 1. 光滑零均值解 $u$ 的构造与验证

先证 $\widehat F(k)$ 的速降性：记微分算子 $L:=1-(2\pi)^{-2}(\partial_1^2+\partial_2^2)$。对任意整数 $M\ge 0$，$L^M F\in C^\infty(\mathbb T^2)$，由预备中的分部积分得
$$\widehat{L^M F}(k)=(1+k_1^2+k_2^2)^M\widehat F(k)=\langle k\rangle^{2M}\widehat F(k)\qquad(k\in\mathbb Z^2),$$
故对所有 $k\in\mathbb Z^2$ 有
$$|\widehat F(k)|\le\|L^M F\|_{L^1(\mathbb T^2)}\langle k\rangle^{-2M}\le\|L^M F\|_{C^0}\langle k\rangle^{-2M}.$$
特别地，对任意 $p\in\mathbb R$，取 $M\in\mathbb N_0$ 使 $4M-2p>2$，由格点可和性引理可知 $\|F\|_{H^p}<\infty$。

现在令
$$c_0:=0,\qquad c_k:=\frac{\widehat F(k)}{2\pi i(\alpha k_1+k_2)}\quad(k\in\mathbb Z^2\setminus\{0\}),$$
并定义
$$u(y):=\sum_{k\in\mathbb Z^2\setminus\{0\}}c_k e^{2\pi i k\cdot y}.$$
验证 $u\in C^\infty_0(\mathbb T^2)$ 且 $N_\alpha u=F$：
- **系数速降性**：由算术界 $|\alpha k_1+k_2|\ge c\langle k\rangle^{-s}$，对一切 $k\ne 0$ 有
  $$|c_k|=\frac{|\widehat F(k)|}{2\pi|\alpha k_1+k_2|}\le\frac{1}{2\pi c}\langle k\rangle^s|\widehat F(k)|.$$
  结合 $|\widehat F(k)|\le\|L^M F\|_{C^0}\langle k\rangle^{-2M}$，对任意 $p\ge 0$ 取 $2M\ge p+s$ 即得 $\sup_{k\in\mathbb Z^2}\langle k\rangle^p|c_k|<\infty$。
- **光滑性与逐项求导**：对任意 $(a,b)\in\mathbb N_0^2$，令 $m=a+b$，取 $p=m+3$ 得存在常数 $A_{a,b}<\infty$ 使
  $$\sup_{y\in\mathbb T^2}\left|\partial_1^a\partial_2^b(c_k e^{2\pi i k\cdot y})\right|=(2\pi)^{a+b}|k_1|^a|k_2|^b|c_k|\le(2\pi)^m\langle k\rangle^m|c_k|\le A_{a,b}\langle k\rangle^{-3}.$$
  由格点可和性引理（$\tau=3>2$），$\sum_{k\in\mathbb Z^2}\langle k\rangle^{-3}<\infty$。考虑部分和序列 $S_R(y)=\sum_{0<|k|\le R}c_k e^{2\pi i k\cdot y}$（$R\in\mathbb N$）：对每个 $(a,b)\in\mathbb N_0^2$，由 Weierstrass M 判别法，$\partial_1^a\partial_2^b S_R$ 在 $\mathbb T^2$ 上一致收敛。对阶数 $a+b$ 归纳并应用一致收敛函数列逐项求导定理（条件为部分和列本身及逐项偏导数列均在 $\mathbb T^2$ 上一致收敛，已验证成立），得 $u\in C^\infty(\mathbb T^2)$ 且所有偏导数可逐项求导。
- **零均值与满足方程**：由 $S_R\to u$ 一致收敛，逐项积分得 $\widehat u(k)=c_k$（$k\ne 0$）且 $\int_{\mathbb T^2}u=\widehat u(0)=0$，故 $u\in C^\infty_0(\mathbb T^2)$。进一步逐项作用 $N_\alpha$ 得
  $$N_\alpha u(y)=\sum_{k\ne 0}2\pi i(\alpha k_1+k_2)c_k e^{2\pi i k\cdot y}=\sum_{k\ne 0}\widehat F(k)e^{2\pi i k\cdot y}.$$
  由于 $F\in C^\infty_0(\mathbb T^2)$ 的 Fourier 系数同样满足 $|\widehat F(k)|\le C\langle k\rangle^{-3}$，级数 $G(y):=\sum_{k\ne 0}\widehat F(k)e^{2\pi i k\cdot y}$ 在 $\mathbb T^2$ 上一致收敛于连续函数，且逐项积分知 $\widehat G(k)=\widehat F(k)$ 对一切 $k\in\mathbb Z^2$ 成立。由 $L^2(\mathbb T^2)$ 中三角系 $\{e_k\}_{k\in\mathbb Z^2}$ 的完备性（Parseval 等式给出 $\|G-F\|_{L^2}^2=\sum_k|\widehat G(k)-\widehat F(k)|^2=0$）与 $G,F$ 的连续性，得 $G=F$ 处处成立，即 $N_\alpha u=F$。
  （且该解在 $C^\infty_0(\mathbb T^2)$ 中唯一：若 $N_\alpha\tilde u=F$ 且 $\tilde u\in C^\infty_0(\mathbb T^2)$，则 $\widehat{\tilde u}(0)=0$ 且对 $k\ne 0$ 有 $2\pi i(\alpha k_1+k_2)\widehat{\tilde u}(k)=\widehat F(k)$，故 $\widehat{\tilde u}=\widehat u$，从而 $\tilde u=u$。）

### 2. 截断误差估计

由构造，对 $|k|\le N$ 有 $\widehat{u-u_N}(k)=0$；对 $|k|>N$ 有 $\widehat{u-u_N}(k)=\frac{\widehat F(k)}{2\pi i(\alpha k_1+k_2)}$，且
$$\langle k\rangle=(1+|k|^2)^{1/2}>(1+N^2)^{1/2}.$$
由于 $q\ge 0$，函数 $t\mapsto t^{-2q}$ 在 $(0,\infty)$ 上单调非增，故对一切 $|k|>N$ 有 $\langle k\rangle^{-2q}\le(1+N^2)^{-q}$。于是对任意 $r\in\mathbb R$ 与 $q\ge 0$，利用 $|\alpha k_1+k_2|\ge c\langle k\rangle^{-s}$ 得
\begin{align*}
\|u-u_N\|_{H^r}^2
&=\sum_{|k|>N}\langle k\rangle^{2r}\frac{|\widehat F(k)|^2}{4\pi^2|\alpha k_1+k_2|^2}\\
&\le\frac{1}{4\pi^2 c^2}\sum_{|k|>N}\langle k\rangle^{2r+2s}|\widehat F(k)|^2\\
&=\frac{1}{4\pi^2 c^2}\sum_{|k|>N}\langle k\rangle^{-2q}\langle k\rangle^{2(r+s+q)}|\widehat F(k)|^2\\
&\le(2\pi c)^{-2}(1+N^2)^{-q}\sum_{|k|>N}\langle k\rangle^{2(r+s+q)}|\widehat F(k)|^2\\
&\le(2\pi c)^{-2}(1+N^2)^{-q}\sum_{k\in\mathbb Z^2}\langle k\rangle^{2(r+s+q)}|\widehat F(k)|^2\\
&=(2\pi c)^{-2}(1+N^2)^{-q}\|F\|_{H^{r+s+q}}^2,
\end{align*}
其中前已证 $\|F\|_{H^{r+s+q}}<\infty$。两边开平方即得
$$\|u-u_N\|_{H^r}\le(2\pi c)^{-1}(1+N^2)^{-q/2}\|F\|_{H^{r+s+q}}.$$

---

## S3 固定频带内改变方向

已知 $\alpha,\beta\in\mathbb R\setminus\mathbb Q$，$N\ge 1$，且对所有 $k\in I_N=\{k\in\mathbb Z^2:0<|k|\le N\}$ 均有
$$|\alpha k_1+k_2|\ge\delta>0,\qquad |\beta k_1+k_2|\ge\delta>0.$$
对任意 $F\in H_N$，由 S1（适用条件：$\alpha,\beta$ 均无理且 $N\ge 1$），对应解 $u_\alpha=(N_\alpha|_{H_N})^{-1}F\in H_N$ 与 $u_\beta=(N_\beta|_{H_N})^{-1}F\in H_N$ 满足：对 $k\notin I_N$ 有 $\widehat{u_\alpha}(k)=\widehat{u_\beta}(k)=\widehat F(k)=0$，而对 $k\in I_N$ 有
$$\widehat{u_\alpha}(k)-\widehat{u_\beta}(k)=\frac{\widehat F(k)}{2\pi i(\alpha k_1+k_2)}-\frac{\widehat F(k)}{2\pi i(\beta k_1+k_2)}=\frac{(\beta-\alpha)k_1}{2\pi i(\alpha k_1+k_2)(\beta k_1+k_2)}\widehat F(k).$$
对每个 $k\in I_N$，由 $|k_1|\le(k_1^2+k_2^2)^{1/2}=|k|\le N$ 以及小除数下界得
$$|\widehat{u_\alpha}(k)-\widehat{u_\beta}(k)|=\frac{|\alpha-\beta|\,|k_1|}{2\pi|\alpha k_1+k_2|\,|\beta k_1+k_2|}|\widehat F(k)|\le\frac{|\alpha-\beta|N}{2\pi\delta^2}|\widehat F(k)|.$$
对任意 $r\in\mathbb R$，两边平方乘以 $\langle k\rangle^{2r}$ 后对 $k\in I_N$ 求和：
$$\|u_\alpha-u_\beta\|_{H^r}^2=\sum_{k\in I_N}\langle k\rangle^{2r}|\widehat{u_\alpha}(k)-\widehat{u_\beta}(k)|^2\le\left(\frac{|\alpha-\beta|N}{2\pi\delta^2}\right)^2\sum_{k\in I_N}\langle k\rangle^{2r}|\widehat F(k)|^2=\left(\frac{|\alpha-\beta|N}{2\pi\delta^2}\right)^2\|F\|_{H^r}^2.$$
开平方即得
$$\|u_\alpha-u_\beta\|_{H^r}\le|\alpha-\beta|N(2\pi\delta^2)^{-1}\|F\|_{H^r}.$$

---

## S4 整体对象与全部恢复目标

### 结论总览

1. **可逆性刻画**：对任意无理数 $\alpha\in\mathbb R\setminus\mathbb Q$，$N_\alpha:C^\infty_0(\mathbb T^2)\to C^\infty_0(\mathbb T^2)$ 总是单射；它是双射（即对每个 $F\in C^\infty_0(\mathbb T^2)$ 存在唯一解 $u\in C^\infty_0(\mathbb T^2)$）**当且仅当** $\alpha$ 是 **Diophantine 数**，即存在 $c>0$、$s\ge 0$ 使得 $|\alpha k_1+k_2|\ge c\langle k\rangle^{-s}$ 对一切 $k\in\mathbb Z^2\setminus\{0\}$ 成立（等价于存在 $c'>0$、$s\ge 1$ 使得 $|\alpha q-p|\ge c'|q|^{-s}$ 对一切 $q\in\mathbb Z\setminus\{0\},p\in\mathbb Z$ 成立）。对非 Diophantine（即 Liouville）无理数，满射性不成立（下文给出具体反例）。
2. **全部允许损失 $s\ge 0$ 的刻画**：固定 $\alpha\in\mathbb R\setminus\mathbb Q$ 与 $s\ge 0$。对每个 $r\in\mathbb R$ 存在与 $u$ 无关的有限常数 $C_{\alpha,r,s}$ 使 $\|u\|_{H^r}\le C_{\alpha,r,s}\|N_\alpha u\|_{H^{r+s}}$（$\forall u\in C^\infty_0(\mathbb T^2)$）**当且仅当**
   $$c_{\alpha,s}:=\inf_{k\in\mathbb Z^2\setminus\{0\}}\langle k\rangle^s|\alpha k_1+k_2|>0\quad\Longleftrightarrow\quad c'_{\alpha,s}:=\inf_{q\in\mathbb Z\setminus\{0\},\,p\in\mathbb Z}|q|^s|\alpha q-p|>0.$$
   允许损失集合 $S(\alpha):=\{s\ge 0:c_{\alpha,s}>0\}$ 总包含于 $[1,\infty)$；若 $\alpha$ 为 Liouville 数则 $S(\alpha)=\emptyset$，若 $\alpha$ 为 Diophantine 数则 $S(\alpha)$ 为 $[\tau(\alpha),\infty)$ 或 $(\tau(\alpha),\infty)$（其中 $\tau(\alpha)=\inf S(\alpha)\ge 1$）。对任一 $s\in S(\alpha)$，最优常数与 $r$ 无关，为 $(2\pi c_{\alpha,s})^{-1}$。
3. **$\alpha_*=\sqrt 2-1$ 的最小允许损失**：$S(\alpha_*)=[1,\infty)$，最小允许损失为 **$s=1$**，且 **取到**。
4. **$\alpha_*=\sqrt 2-1$ 的 $C^m\to C^{m+4}$ 估计**：**成立**。对每个 $m\in\mathbb N_0$ 均存在仅依赖于 $m$ 的有限常数 $C_m$，使对全部 $F\in C^\infty_0(\mathbb T^2)$ 满足更强的不等式 $\|N_{\alpha_*}^{-1}F\|_{C^m}\le C_m\|F\|_{C^{m+3}}\le C_m\|F\|_{C^{m+4}}$。

下面依次给出完整定理与证明。

---

### 定理 1（二维与一维 Diophantine 条件的同指数等价性与 Dirichlet 下界）

设 $\alpha\in\mathbb R\setminus\mathbb Q$，$s\ge 0$。
1. 下列两条件等价（且指数 $s$ 完全相同）：
   - $(\mathrm{D}_s)$ 存在 $c>0$，使 $|\alpha k_1+k_2|\ge c\langle k\rangle^{-s}$ 对一切 $k\in\mathbb Z^2\setminus\{0\}$ 成立；
   - $(\mathrm{D}'_s)$ 存在 $c'>0$，使 $|\alpha q-p|\ge c'|q|^{-s}$ 对一切 $q\in\mathbb Z\setminus\{0\},p\in\mathbb Z$ 成立。
2. 若 $(\mathrm{D}_s)$ 成立，则必有 $s\ge 1$。

**证明**：
1. $(\mathrm{D}_s)\Rightarrow(\mathrm{D}'_s)$：任取 $q\in\mathbb Z\setminus\{0\},p\in\mathbb Z$，令 $k=(q,-p)\ne 0$。
   - 若 $|\alpha q-p|\ge 1$，因 $|q|\ge 1$ 且 $s\ge 0$，有 $|\alpha q-p|\ge 1\ge|q|^{-s}$。
   - 若 $|\alpha q-p|<1$，则 $|p|\le|\alpha||q|+1\le(|\alpha|+1)|q|$，从而
     $$\langle k\rangle=(1+q^2+p^2)^{1/2}\le\bigl(2+(|\alpha|+1)^2\bigr)^{1/2}|q|=:A_\alpha|q|.$$
     于是由 $(\mathrm{D}_s)$ 得 $|\alpha q-p|=|\alpha k_1+k_2|\ge c\langle k\rangle^{-s}\ge c A_\alpha^{-s}|q|^{-s}$。
   取 $c'=\min(1,c A_\alpha^{-s})>0$ 即得 $(\mathrm{D}'_s)$。

   $(\mathrm{D}'_s)\Rightarrow(\mathrm{D}_s)$：任取 $k=(k_1,k_2)\in\mathbb Z^2\setminus\{0\}$。
   - 若 $k_1=0$，则 $|k_2|\ge 1$，因 $\langle k\rangle\ge 1$ 及 $s\ge 0$，有 $|\alpha k_1+k_2|=|k_2|\ge 1\ge\langle k\rangle^{-s}$。
   - 若 $k_1\ne 0$，则 $1\le|k_1|<\langle k\rangle$，故由 $(\mathrm{D}'_s)$ 得 $|\alpha k_1+k_2|=|\alpha k_1-(-k_2)|\ge c'|k_1|^{-s}\ge c'\langle k\rangle^{-s}$。
   取 $c=\min(1,c')>0$ 即得 $(\mathrm{D}_s)$。

2. 用鸽巢原理证明 Dirichlet 逼近定理：对任一整数 $Q\ge 1$，考察 $[0,1)$ 中的 $Q+1$ 个小数部分 $\{m\alpha\}=m\alpha-\lfloor m\alpha\rfloor$（$m=0,1,\dots,Q$）。将 $[0,1)$ 分为 $Q$ 个半开区间 $[\frac{j-1}{Q},\frac{j}{Q})$（$j=1,\dots,Q$），必存在 $0\le m_1<m_2\le Q$ 使 $\{m_1\alpha\}$ 与 $\{m_2\alpha\}$ 落入同一区间。令 $q=m_2-m_1\in\{1,\dots,Q\}$、$p=\lfloor m_2\alpha\rfloor-\lfloor m_1\alpha\rfloor\in\mathbb Z$，则
   $$0<|\alpha q-p|=|\{m_2\alpha\}-\{m_1\alpha\}|<\frac{1}{Q}\le\frac{1}{q}$$
   （严格大于 $0$ 因为 $\alpha\notin\mathbb Q$）。由此可归纳构造序列 $(q_j,p_j)\in\mathbb N\times\mathbb Z$：取 $Q_1=1$ 得 $(q_1,p_1)$；已知 $(q_j,p_j)$ 后取整数 $Q_{j+1}>|\alpha q_j-p_j|^{-1}$ 得 $(q_{j+1},p_{j+1})$，从而 $0<|\alpha q_{j+1}-p_{j+1}|<1/Q_{j+1}<|\alpha q_j-p_j|$。对任意 $M\ge 1$，集合 $\{(q,p)\in\mathbb Z^2:1\le q\le M,\,|\alpha q-p|<1\}$ 有限（因 $|p|<|\alpha|M+1$），故其上 $|\alpha q-p|$ 有正下界；因 $|\alpha q_j-p_j|\to 0$，必有 $q_j\to\infty$。

   若 $(\mathrm{D}_s)$ 对某 $s\in[0,1)$ 成立，则由第 1 步 $(\mathrm{D}'_s)$ 成立，于是对所有 $j$ 有
   $$0<c'\le q_j^s|\alpha q_j-p_j|<q_j^{s-1}\xrightarrow{j\to\infty}0,$$
   矛盾。故必有 $s\ge 1$。$\square$

---

### 定理 2（$N_\alpha:C^\infty_0(\mathbb T^2)\to C^\infty_0(\mathbb T^2)$ 的可逆性刻画）

设 $\alpha\in\mathbb R\setminus\mathbb Q$。
1. $N_\alpha$ 映 $C^\infty_0(\mathbb T^2)$ 入 $C^\infty_0(\mathbb T^2)$ 且恒为单射。
2. $N_\alpha:C^\infty_0(\mathbb T^2)\to C^\infty_0(\mathbb T^2)$ 为双射（等价地，每个 $F\in C^\infty_0(\mathbb T^2)$ 有唯一光滑零均值解）当且仅当存在 $s\ge 0$ 使 $(\mathrm{D}_s)$ 成立（即 $\alpha$ 为 Diophantine 数）。

**证明**：
1. 若 $u\in C^\infty_0(\mathbb T^2)$，显然 $N_\alpha u\in C^\infty(\mathbb T^2)$ 且 $\int_{\mathbb T^2}N_\alpha u=\widehat{N_\alpha u}(0)=2\pi i(\alpha\cdot 0+0)\widehat u(0)=0$，故 $N_\alpha u\in C^\infty_0(\mathbb T^2)$。若 $N_\alpha u=0$，则对全部 $k\in\mathbb Z^2$ 有 $2\pi i(\alpha k_1+k_2)\widehat u(k)=0$。当 $k\ne 0$ 时由 $\alpha\notin\mathbb Q$ 知 $\alpha k_1+k_2\ne 0$，故 $\widehat u(k)=0$；当 $k=0$ 时由 $u\in C^\infty_0(\mathbb T^2)$ 知 $\widehat u(0)=0$。由 Parseval 等式 $\|u\|_{L^2}^2=\sum_k|\widehat u(k)|^2=0$ 及 $u$ 的连续性得 $u\equiv 0$，故 $N_\alpha$ 单射。
2. **充分性**：若对某 $c>0,s\ge 0$ 满足 $(\mathrm{D}_s)$，则直接援引 S2（适用条件已全部满足）：对每个 $F\in C^\infty_0(\mathbb T^2)$，级数 $u(y)=\sum_{k\ne 0}\frac{\widehat F(k)}{2\pi i(\alpha k_1+k_2)}e^{2\pi i k\cdot y}$ 给出 $C^\infty_0(\mathbb T^2)$ 中的解，再由单射性即唯一。

   **必要性（对 Liouville 方向构造显式不可解反例 $F\in C^\infty_0(\mathbb T^2)$）**：假设对一切 $c>0,s\ge 0$ 条件 $(\mathrm{D}_s)$ 均不成立。我们归纳选取频率列 $\{k^{(n)}\}_{n=1}^\infty\subset\mathbb Z^2\setminus\{0\}$：
   对 $n\ge 1$，设已选出 $k^{(1)},\dots,k^{(n-1)}$，令 $M_n:=\max\bigl(\{n\}\cup\{|k^{(j)}|:1\le j<n\}\bigr)\ge n\ge 1$。因 $I_{M_n}=\{k\in\mathbb Z^2:0<|k|\le M_n\}$ 有限非空且 $\alpha\notin\mathbb Q$，故
   $$\delta_n:=\min_{0<|k|\le M_n}|\alpha k_1+k_2|>0.$$
   置 $c_n:=\min(1,\delta_n)>0$。因 $(\mathrm{D}_n)$ 对常数 $c_n$ 不成立，存在 $k^{(n)}\in\mathbb Z^2\setminus\{0\}$ 满足
   $$|\alpha k_1^{(n)}+k_2^{(n)}|<c_n\langle k^{(n)}\rangle^{-n}.$$
   若 $|k^{(n)}|\le M_n$，因 $\langle k^{(n)}\rangle\ge 1$，必有 $|\alpha k_1^{(n)}+k_2^{(n)}|\ge\delta_n\ge c_n\ge c_n\langle k^{(n)}\rangle^{-n}$，矛盾。因此 $|k^{(n)}|>M_n\ge\max(n,|k^{(1)}|,\dots,|k^{(n-1)}|)$。由此 $\{k^{(n)}\}_{n=1}^\infty$ 的模长严格递增（从而两两互异且均非零），$\langle k^{(n)}\rangle>|k^{(n)}|>n$，且
   $$0<|\alpha k_1^{(n)}+k_2^{(n)}|<\langle k^{(n)}\rangle^{-n}\qquad(\forall n\ge 1).$$
   定义
   $$F(y):=\sum_{n=1}^\infty 2\pi|\alpha k_1^{(n)}+k_2^{(n)}|\,e^{2\pi i k^{(n)}\cdot y}.$$
   对任意 $(a,b)\in\mathbb N_0^2$，令 $m=a+b$。当 $n\ge m+2$ 时，$n-m\ge 2$ 且 $\langle k^{(n)}\rangle>n\ge 1$，故
   $$\sup_{y\in\mathbb T^2}\left|\partial_1^a\partial_2^b\bigl(2\pi|\alpha k_1^{(n)}+k_2^{(n)}|e^{2\pi i k^{(n)}\cdot y}\bigr)\right|\le(2\pi)^{m+1}\langle k^{(n)}\rangle^{m-n}\le(2\pi)^{m+1}\langle k^{(n)}\rangle^{-2}<(2\pi)^{m+1}n^{-2}.$$
   因 $\sum_{n=m+2}^\infty n^{-2}<\infty$，由 Weierstrass M 判别法与一致收敛函数列逐项求导定理，$F\in C^\infty(\mathbb T^2)$。再由一致收敛逐项积分及 $k^{(n)}$ 两两互异且非零，得 $\widehat F(0)=0$（即 $F\in C^\infty_0(\mathbb T^2)$）且 $\widehat F(k^{(n)})=2\pi|\alpha k_1^{(n)}+k_2^{(n)}|$（$\forall n\ge 1$）。

   若存在 $u\in C^\infty_0(\mathbb T^2)$ 满足 $N_\alpha u=F$，取第 $k^{(n)}$ 个 Fourier 系数得
   $$2\pi i(\alpha k_1^{(n)}+k_2^{(n)})\widehat u(k^{(n)})=2\pi|\alpha k_1^{(n)}+k_2^{(n)}|\implies|\widehat u(k^{(n)})|=1\qquad(\forall n\ge 1).$$
   因 $\{e_{k^{(n)}}\}_{n=1}^\infty$ 在 $L^2(\mathbb T^2)$ 中标准正交，由 Bessel 不等式得 $\sum_{n=1}^\infty|\widehat u(k^{(n)})|^2\le\|u\|_{L^2}^2<\infty$，与 $\sum_{n=1}^\infty 1=\infty$ 矛盾。故 $N_\alpha u=F$ 无光滑零均值解。$\square$

---

### 定理 3（全部允许 Sobolev 损失 $s\ge 0$ 的刻画）

设 $\alpha\in\mathbb R\setminus\mathbb Q$，$s\ge 0$。下列条件等价：
1. 对每个 $r\in\mathbb R$，存在与 $u$ 无关的有限常数 $C_{\alpha,r,s}$，使 $\|u\|_{H^r}\le C_{\alpha,r,s}\|N_\alpha u\|_{H^{r+s}}$ 对全部 $u\in C^\infty_0(\mathbb T^2)$ 成立；
2. 存在某个 $r\in\mathbb R$ 与有限常数 $C$，使 $\|u\|_{H^r}\le C\|N_\alpha u\|_{H^{r+s}}$ 对全部 $u\in C^\infty_0(\mathbb T^2)$ 成立；
3. $c_{\alpha,s}:=\inf_{k\in\mathbb Z^2\setminus\{0\}}\langle k\rangle^s|\alpha k_1+k_2|>0$（即 $(\mathrm{D}_s)$ 成立）；
4. $c'_{\alpha,s}:=\inf_{q\in\mathbb Z\setminus\{0\},\,p\in\mathbb Z}|q|^s|\alpha q-p|>0$（即 $(\mathrm{D}'_s)$ 成立）。

并且，当上述条件成立时，对每个 $r\in\mathbb R$，最优常数均与 $r$ 无关，为
$$C_{\alpha,r,s}^{\mathrm{opt}}=\frac{1}{2\pi c_{\alpha,s}}=\sup_{k\in\mathbb Z^2\setminus\{0\}}\frac{1}{2\pi\langle k\rangle^s|\alpha k_1+k_2|}.$$
允许损失集合 $S(\alpha):=\{s\ge 0:c_{\alpha,s}>0\}$ 满足：
- 恒有 $S(\alpha)\subseteq[1,\infty)$；
- 若 $\alpha$ 为 Liouville 数，则 $S(\alpha)=\emptyset$；
- 若 $\alpha$ 为 Diophantine 数，记 $\tau(\alpha):=\inf S(\alpha)\in[1,\infty)$，则当 $c_{\alpha,\tau(\alpha)}>0$ 时 $S(\alpha)=[\tau(\alpha),\infty)$，当 $c_{\alpha,\tau(\alpha)}=0$ 时 $S(\alpha)=(\tau(\alpha),\infty)$。

**证明**：
- $(3)\Leftrightarrow(4)$ 已由定理 1 证毕。
- $(3)\Rightarrow(1)$：设 $c_{\alpha,s}>0$，令 $C^*:=(2\pi c_{\alpha,s})^{-1}<\infty$。对任意 $r\in\mathbb R$ 与 $u\in C^\infty_0(\mathbb T^2)$，因 $\widehat u(0)=0$ 且 $\widehat{N_\alpha u}(k)=2\pi i(\alpha k_1+k_2)\widehat u(k)$，有
  $$\|u\|_{H^r}^2=\sum_{k\ne 0}\frac{1}{4\pi^2\langle k\rangle^{2s}|\alpha k_1+k_2|^2}\langle k\rangle^{2(r+s)}|\widehat{N_\alpha u}(k)|^2\le(C^*)^2\|N_\alpha u\|_{H^{r+s}}^2,$$
  即 $\|u\|_{H^r}\le C^*\|N_\alpha u\|_{H^{r+s}}$，且 $C^*$ 与 $u,r$ 均无关。
- $(1)\Rightarrow(2)$：取 $r=0$ 即可。
- $(2)\Rightarrow(3)$ 及最优常数：设对某 $r\in\mathbb R$ 与 $C<\infty$ 有 $\|u\|_{H^r}\le C\|N_\alpha u\|_{H^{r+s}}$ 对全部 $u\in C^\infty_0(\mathbb T^2)$ 成立。对任意 $k\in\mathbb Z^2\setminus\{0\}$，取单频测试函数 $u=e_k\in C^\infty_0(\mathbb T^2)$，则 $\|e_k\|_{H^r}=\langle k\rangle^r>0$ 且 $\|N_\alpha e_k\|_{H^{r+s}}=2\pi|\alpha k_1+k_2|\langle k\rangle^{r+s}>0$。代入不等式并消去 $\langle k\rangle^r$ 得
  $$1\le 2\pi C\langle k\rangle^s|\alpha k_1+k_2|\qquad(\forall k\in\mathbb Z^2\setminus\{0\}).$$
  由此 $C>0$ 且 $c_{\alpha,s}=\inf_{k\ne 0}\langle k\rangle^s|\alpha k_1+k_2|\ge(2\pi C)^{-1}>0$，同时表明任一可行常数均满足 $C\ge(2\pi c_{\alpha,s})^{-1}=C^*$，故最优常数恰为 $C^*$。
- $S(\alpha)$ 的结构：由定理 1 得 $S(\alpha)\subseteq[1,\infty)$；若 $s_0\in S(\alpha)$ 且 $s>s_0$，则由 $\langle k\rangle\ge 1$ 得 $\langle k\rangle^s|\alpha k_1+k_2|\ge\langle k\rangle^{s_0}|\alpha k_1+k_2|\ge c_{\alpha,s_0}>0$，故 $s\in S(\alpha)$，即 $S(\alpha)$ 向上封闭，由此立即得到关于 $S(\alpha)$ 形态的分类。$\square$

---

### 定理 4（$\alpha_*=\sqrt 2-1$ 的精确损失与 $C^m\to C^{m+4}$ 正则性）

令 $\alpha_*=\sqrt 2-1$。
1. $\alpha_*$ 为无理数，对一切 $k\in\mathbb Z^2\setminus\{0\}$ 有
   $$|\alpha_* k_1+k_2|>\frac{1}{\sqrt{4+2\sqrt 2}}\,\langle k\rangle^{-1}.$$
   从而 $N_{\alpha_*}:C^\infty_0(\mathbb T^2)\to C^\infty_0(\mathbb T^2)$ 为双射，$S(\alpha_*)=[1,\infty)$，最小允许损失为 $s=1$ 且取到；对全部 $r\in\mathbb R$ 与 $F\in C^\infty_0(\mathbb T^2)$ 有
   $$\|N_{\alpha_*}^{-1}F\|_{H^r}\le\frac{\sqrt{4+2\sqrt 2}}{2\pi}\,\|F\|_{H^{r+1}}.$$
2. 对每个 $m\in\mathbb N_0$，存在仅依赖于 $m$（与 $F$ 无关）的有限常数 $C_m$，使得对全部 $F\in C^\infty_0(\mathbb T^2)$ 成立
   $$\|N_{\alpha_*}^{-1}F\|_{C^m}\le C_m\|F\|_{C^{m+3}}\le C_m\|F\|_{C^{m+4}}.$$
   （特别地，题设所问 $\|N_{\alpha_*}^{-1}F\|_{C^m}\le C_m\|F\|_{C^{m+4}}$ **成立**。）

**证明**：
1. 若 $\alpha_*=\sqrt 2-1\in\mathbb Q$，则 $\sqrt 2=\alpha_*+1\in\mathbb Q$，矛盾，故 $\alpha_*\in\mathbb R\setminus\mathbb Q$。由定理 3 知 $S(\alpha_*)\subseteq[1,\infty)$。

   对任意 $k=(k_1,k_2)\in\mathbb Z^2\setminus\{0\}$，置整数 $a:=k_1,b:=k_2-k_1$，则 $(a,b)\in\mathbb Z^2\setminus\{0\}$，且 $\alpha_* k_1+k_2=b+a\sqrt 2$。考察整数 $b^2-2a^2=(b+a\sqrt 2)(b-a\sqrt 2)$：若 $b^2-2a^2=0$，由于 $(a,b)\ne(0,0)$ 必有 $a\ne 0$，从而 $\sqrt 2=|b/a|\in\mathbb Q$，矛盾。故 $b^2-2a^2$ 为非零整数，$|b^2-2a^2|\ge 1$。

   另一方面，由 Cauchy–Schwarz 不等式，
   $$|b-a\sqrt 2|=|-(1+\sqrt 2)k_1+k_2|\le\sqrt{(1+\sqrt 2)^2+1^2}\,|k|=\sqrt{4+2\sqrt 2}\,|k|<\sqrt{4+2\sqrt 2}\,\langle k\rangle.$$
   于是对一切 $k\in\mathbb Z^2\setminus\{0\}$，
   $$|\alpha_* k_1+k_2|=\frac{|b^2-2a^2|}{|b-a\sqrt 2|}>\frac{1}{\sqrt{4+2\sqrt 2}}\,\langle k\rangle^{-1}.$$
   由定理 2 与定理 3 即得 $N_{\alpha_*}:C^\infty_0(\mathbb T^2)\to C^\infty_0(\mathbb T^2)$ 双射，$1\in S(\alpha_*)$，结合 $S(\alpha_*)\subseteq[1,\infty)$ 推出 $S(\alpha_*)=[1,\infty)$，最小允许损失为 $s=1$ 且在 $s=1$ 处取到，同时对任意 $r\in\mathbb R$ 与 $F\in C^\infty_0(\mathbb T^2)$ 令 $u=N_{\alpha_*}^{-1}F$ 得 $\|u\|_{H^r}\le C_0\|F\|_{H^{r+1}}$，其中 $C_0:=\frac{\sqrt{4+2\sqrt 2}}{2\pi}$。

2. 任取 $m\in\mathbb N_0$ 与 $F\in C^\infty_0(\mathbb T^2)$，记 $u=N_{\alpha_*}^{-1}F\in C^\infty_0(\mathbb T^2)$。分两步嵌入估计：
   - **从 $H^{m+2}$ 到 $C^m$（二维 Sobolev 嵌入）**：因 $u\in C^\infty(\mathbb T^2)$，如 S2 所证其 Fourier 级数可任意阶逐项求导，故对任意 $a,b\in\mathbb N_0$ 且 $a+b\le m$ 与任意 $y\in\mathbb T^2$，
     $$\partial_1^a\partial_2^b u(y)=\sum_{k\in\mathbb Z^2}(2\pi i k_1)^a(2\pi i k_2)^b\widehat u(k)e^{2\pi i k\cdot y}.$$
     注意到 $|k_1|^a|k_2|^b\le\langle k\rangle^{a+b}\le\langle k\rangle^m$ 及 $(2\pi)^{a+b}\le(2\pi)^m$（因 $\langle k\rangle\ge 1$ 且 $2\pi>1$），由 Cauchy–Schwarz 不等式得
     $$|\partial_1^a\partial_2^b u(y)|\le(2\pi)^m\sum_{k\in\mathbb Z^2}\langle k\rangle^{-2}\cdot\langle k\rangle^{m+2}|\widehat u(k)|\le(2\pi)^m B\|u\|_{H^{m+2}},$$
     其中 $B:=\left(\sum_{k\in\mathbb Z^2}\langle k\rangle^{-4}\right)^{1/2}<4<\infty$（由预备引理中 $\tau=4>2$ 保证有限）。取 $\sup_{y\in\mathbb T^2}$ 及 $\max_{a+b\le m}$ 得
     $$\|u\|_{C^m}\le(2\pi)^m B\|u\|_{H^{m+2}}.$$
   - **从 $C^M$ 到 $H^M$（对任意整数 $M\in\mathbb N_0$）**：对任意 $F\in C^\infty(\mathbb T^2)$，按多项式定理展开 $(1+k_1^2+k_2^2)^M$，因各项非负且级数收敛，可交换有限和与无穷级数；再对每个光滑函数 $\partial_1^a\partial_2^b F\in C^\infty(\mathbb T^2)$ 应用 Parseval 等式（其第 $k$ 个 Fourier 系数为 $(2\pi i k_1)^a(2\pi i k_2)^b\widehat F(k)$）：
     \begin{align*}
     \|F\|_{H^M}^2
     &=\sum_{k\in\mathbb Z^2}(1+k_1^2+k_2^2)^M|\widehat F(k)|^2\\
     &=\sum_{\substack{j,a,b\ge 0\\j+a+b=M}}\frac{M!}{j!\,a!\,b!}(2\pi)^{-2(a+b)}\sum_{k\in\mathbb Z^2}\left|\widehat{\partial_1^a\partial_2^b F}(k)\right|^2\\
     &=\sum_{\substack{j,a,b\ge 0\\j+a+b=M}}\frac{M!}{j!\,a!\,b!}(2\pi)^{-2(a+b)}\int_{\mathbb T^2}|\partial_1^a\partial_2^b F(y)|^2\,dy\\
     &\le\sum_{\substack{j,a,b\ge 0\\j+a+b=M}}\frac{M!}{j!\,a!\,b!}(2\pi)^{-2(a+b)}\|F\|_{C^M}^2
     =\left(1+\frac{1}{2\pi^2}\right)^M\|F\|_{C^M}^2,
     \end{align*}
     其中倒数第二步利用了 $a+b=M-j\le M$ 以及归一化 Haar 测度 $\int_{\mathbb T^2}1\,dy=1$。

   结合第 1 步（取 $r=m+2$）与上面两嵌入（取 $M=m+3$），并注意到 $\|F\|_{C^{m+3}}\le\|F\|_{C^{m+4}}$（因 $\|F\|_{C^{m+4}}$ 对更大指标集 $\{a+b\le m+4\}\supseteq\{a+b\le m+3\}$ 取最大），得
   $$\|N_{\alpha_*}^{-1}F\|_{C^m}\le(2\pi)^m B\|N_{\alpha_*}^{-1}F\|_{H^{m+2}}\le(2\pi)^m B C_0\|F\|_{H^{m+3}}\le C_m\|F\|_{C^{m+3}}\le C_m\|F\|_{C^{m+4}},$$
   其中显式有限常数
   $$C_m:=(2\pi)^{m-1}\sqrt{4+2\sqrt 2}\left(\sum_{k\in\mathbb Z^2}\langle k\rangle^{-4}\right)^{1/2}\left(1+\frac{1}{2\pi^2}\right)^{(m+3)/2}<\infty$$
   仅依赖于 $m$，与 $F\in C^\infty_0(\mathbb T^2)$ 无关。$\square$

（附注：按同一论证，对任意 Diophantine 数 $\alpha$ 与任意 $s\in S(\alpha)$，记 $\lceil s\rceil$ 为不小于 $s$ 的最小整数，皆有 $\|N_\alpha^{-1}F\|_{C^m}\le C_{\alpha,m,s}\|F\|_{C^{m+\lceil s\rceil+2}}$，故 $N_\alpha^{-1}$ 在 $C^\infty_0(\mathbb T^2)$ 的 Fréchet 拓扑下连续。）

---

## S5 邻近方向的一致估计

**结论**：**不存在**满足要求的开区间 $J\ni\alpha_*$、有限数 $s\ge 0$ 与 $C<\infty$。

**证明**：用反证法。假设存在开区间 $J\ni\alpha_*$、实数 $s\ge 0$ 与常数 $C\in[0,\infty)$，使得对每个无理数 $\alpha\in J$ 及每个 $u\in C^\infty_0(\mathbb T^2)$ 都成立
$$\|u\|_{L^2}\le C\|N_\alpha u\|_{H^s}.$$
因 $J$ 是包含 $\alpha_*$ 的开区间，存在 $\eta>0$ 使 $(\alpha_*-\eta,\alpha_*+\eta)\subseteq J$。选取正整数 $q:=\lceil 2/\eta\rceil\ge 1$（从而 $1/q\le\eta/2$）与整数 $p:=\lfloor q\alpha_*\rfloor$，则有
$$q\alpha_*-1<p\le q\alpha_*\implies\alpha_*-\frac{\eta}{2}<\frac{p}{q}\le\alpha_*.$$
固定非零整频率 $k:=(q,-p)\in\mathbb Z^2\setminus\{0\}$（因 $q\ge 1$），并取单频测试函数 $u(y):=e_k(y)=e^{2\pi i(q y_1-p y_2)}$。显然 $u\in C^\infty(\mathbb T^2)$ 且 $\int_{\mathbb T^2}u=0$（因 $k\ne 0$），即 $u\in C^\infty_0(\mathbb T^2)$，且直接计算得
$$\|u\|_{L^2}=\left(\int_{\mathbb T^2}|e^{2\pi i k\cdot y}|^2\,dy\right)^{1/2}=1.$$
另一方面，对任意 $\alpha\in\mathbb R$，$N_\alpha u=2\pi i(\alpha q-p)e_k$，其唯一非零 Fourier 系数在 $k$ 处，故
$$\|N_\alpha u\|_{H^s}=2\pi|\alpha q-p|\langle k\rangle^s.$$
现在任取正整数 $n$ 满足
$$n>\frac{2\sqrt 2}{\eta}+2\pi\sqrt 2\,C q\langle k\rangle^s,$$
并定义
$$\alpha_n:=\frac{p}{q}+\frac{\sqrt 2}{n}.$$
验证 $\alpha_n$ 满足全部假设前提：
1. $\alpha_n$ 为无理数：若 $\alpha_n\in\mathbb Q$，则 $\sqrt 2=n(\alpha_n-p/q)\in\mathbb Q$，矛盾；
2. $\alpha_n\in J$：因 $n>\frac{2\sqrt 2}{\eta}$，有 $0<\frac{\sqrt 2}{n}<\frac{\eta}{2}$，从而
   $$\alpha_*-\eta<\alpha_*-\frac{\eta}{2}<\frac{p}{q}<\alpha_n\le\alpha_*+\frac{\sqrt 2}{n}<\alpha_*+\frac{\eta}{2}<\alpha_*+\eta,$$
   故 $\alpha_n\in(\alpha_*-\eta,\alpha_*+\eta)\subseteq J$。

将假设中的一致估计用于无理方向 $\alpha=\alpha_n\in J$ 与测试函数 $u=e_k\in C^\infty_0(\mathbb T^2)$，由 $|\alpha_n q-p|=\frac{q\sqrt 2}{n}$ 得
$$1=\|e_k\|_{L^2}\le C\|N_{\alpha_n}e_k\|_{H^s}=\frac{2\pi\sqrt 2\,C q\langle k\rangle^s}{n}<1$$
（最后一步因 $n>2\pi\sqrt 2\,C q\langle k\rangle^s\ge 0$），导出矛盾。

因此不存在这样的 $J,s,C$。$\square$

（附注：上述证明实际上说明，即使把无理方向 $\alpha\in J$ 进一步限制在二次无理数 $\mathbb Q(\sqrt 2)\cap J$ 上，只要 $J$ 是开区间，其内有理共振 $p/q$ 的存在就已彻底排除了任何一致常数 $C$；而结合 S6 亦知 $J$ 内还稠密地包含 Liouville 数，对它们连依赖于 $\alpha$ 的有限 $(s_\alpha,C_\alpha)$ 都不存在。）

---

## S6 一个具体方向的不可解数据

取 $\alpha=\sum_{n=1}^\infty 10^{-n!}$。由于对一切 $n\ge 1$ 有 $0<10^{-n!}\le 10^{-n}$ 且 $\sum_{n=1}^\infty 10^{-n}=1/9<\infty$，该正项级数收敛，$\alpha\in(0,1/9]$ 良定义。

### 1. $\alpha$ 的有理逼近界与无理性证明

对每个正整数 $n\ge 1$，定义正整数
$$q_n:=10^{n!},\qquad p_n:=q_n\sum_{j=1}^n 10^{-j!}=\sum_{j=1}^n 10^{n!-j!}$$
（因 $1\le j\le n$ 时 $n!-j!\ge 0$，故 $p_n\in\mathbb N$）。先估 $p_n$ 与 $\alpha q_n-p_n$：
- 因 $j!\ge j$ 对一切 $j\ge 1$ 成立，有
  $$0<\frac{p_n}{q_n}=\sum_{j=1}^n 10^{-j!}\le\sum_{j=1}^n 10^{-j}<\sum_{j=1}^\infty 10^{-j}=\frac{1}{9}<1,$$
  故 $0<p_n<q_n$。
- 计算余项：
  $$\alpha q_n-p_n=10^{n!}\sum_{j=n+1}^\infty 10^{-j!}=10^{n!-(n+1)!}\sum_{j=n+1}^\infty 10^{(n+1)!-j!}.$$
  首先，级数各项严格为正，故 $\alpha q_n-p_n>0$。其次，注意到 $(n+1)!-n!=n\cdot n!$，且对任意整数 $m\ge 1$ 有 $(m+1)!-m!=m\cdot m!\ge 1$，于是对每个 $j=n+1+\ell$（$\ell\in\mathbb N_0$），裂项相加得 $j!-(n+1)!\ge\ell$。因此
  $$0<\alpha q_n-p_n\le 10^{-n\cdot n!}\sum_{\ell=0}^\infty 10^{-\ell}=\frac{10}{9}\cdot 10^{-n\cdot n!}=\frac{10}{9}\,q_n^{-n}\qquad(\forall n\ge 1).$$

**证明 $\alpha$ 无理**：反设 $\alpha=a/b$（$a\in\mathbb Z,b\in\mathbb N$）。则对每个 $n\ge 1$，整数 $a q_n-b p_n=b(\alpha q_n-p_n)$ 严格大于 $0$，从而必为正整数，即 $a q_n-b p_n\ge 1$。代入上述上界得
$$1\le b(\alpha q_n-p_n)\le\frac{10}{9}b\cdot 10^{-n\cdot n!}\qquad(\forall n\ge 1).$$
取正整数 $n=2b$，则 $n\cdot n!\ge n=2b$，由 Bernoulli 不等式 $10^m=(1+9)^m\ge 1+9m>m$（$m\in\mathbb N$）得 $10^{n\cdot n!}\ge 10^{2b}>2b>\frac{10}{9}b$，于是 $\frac{10}{9}b\cdot 10^{-n\cdot n!}<1$，与 $1\le\frac{10}{9}b\cdot 10^{-n\cdot n!}$ 矛盾。故 $\alpha\in\mathbb R\setminus\mathbb Q$。

### 2. 构造同一个光滑零均值不可解数据 $F$

对每个整数 $n\ge 2$，注意到 $n!$ 为偶数，故 $\frac{n\cdot n!}{2}\in\mathbb N$，且 $10^{-n\cdot n!/2}=q_n^{-n/2}$。记频率
$$k^{(n)}:=(q_n,-p_n)\in\mathbb Z^2\setminus\{0\}\qquad(n\ge 2).$$
因为对一切 $n\ge 2$ 有 $(n+1)!=(n+1)n!>n!$，所以 $q_n=10^{n!}$ 关于 $n$ 严格递增，从而所有频率 $k^{(n)}$（$n\ge 2$）两两互异且均非零。

定义单个函数
$$F(y):=\sum_{n=2}^\infty 10^{-n\cdot n!/2}\,e^{2\pi i(q_n y_1-p_n y_2)}=\sum_{n=2}^\infty q_n^{-n/2}\,e^{2\pi i k^{(n)}\cdot y}.$$

**第一步：验证 $F\in C^\infty_0(\mathbb T^2)$ 并计算其 Fourier 系数。**
记第 $n$ 项为 $F_n(y)=q_n^{-n/2}e^{2\pi i(q_n y_1-p_n y_2)}$。对任意 $(a,b)\in\mathbb N_0^2$，令 $m=a+b$。利用 $0<p_n<q_n$，对一切 $y\in\mathbb T^2$ 与 $n\ge 2$ 有
$$\left|\partial_1^a\partial_2^b F_n(y)\right|=(2\pi)^m q_n^a p_n^b q_n^{-n/2}\le(2\pi)^m q_n^{m-n/2}.$$
当 $n\ge 2m+2$ 时，有 $n/2-m\ge 1$，结合 $q_n=10^{n!}\ge 10^n$ 得
$$\sup_{y\in\mathbb T^2}\left|\partial_1^a\partial_2^b F_n(y)\right|\le(2\pi)^m q_n^{-1}\le(2\pi)^m 10^{-n}.$$
因 $\sum_{n=2m+2}^\infty (2\pi)^m 10^{-n}<\infty$，由 Weierstrass M 判别法，级数 $\sum_{n=2}^\infty \partial_1^a\partial_2^b F_n$ 对任意 $(a,b)\in\mathbb N_0^2$ 在 $\mathbb T^2$ 上一致收敛。对导数阶数归纳并应用一致收敛函数列逐项求导定理，得 $F\in C^\infty(\mathbb T^2)$。

进一步，由 $\sum_{n=2}^\infty F_n$ 在 $\mathbb T^2$ 上一致收敛，可逐项积分求 Fourier 系数；利用 $k^{(n)}$ 两两互异且非零以及 $\{e_k\}_{k\in\mathbb Z^2}$ 的正交性，得
$$\widehat F(k)=\sum_{n=2}^\infty q_n^{-n/2}\int_{\mathbb T^2}e^{2\pi i(k^{(n)}-k)\cdot y}\,dy=\begin{cases} q_n^{-n/2}=10^{-n\cdot n!/2}, & k=k^{(n)}\ (n\ge 2),\\ 0, & \text{其他 }k\in\mathbb Z^2.\end{cases}$$
特别地，$\int_{\mathbb T^2}F=\widehat F(0)=0$，故 $F\in C^\infty_0(\mathbb T^2)$。

**第二步：证明 $N_\alpha u=F$ 没有光滑零均值解。**
反设存在 $u\in C^\infty_0(\mathbb T^2)$ 满足 $N_\alpha u=F$。对每个 $n\ge 2$，两边取第 $k^{(n)}$ 个 Fourier 系数（由预备中的分部积分公式），得
$$2\pi i(\alpha q_n-p_n)\widehat u(k^{(n)})=\widehat{N_\alpha u}(k^{(n)})=\widehat F(k^{(n)})=q_n^{-n/2}.$$
代入第 1 节已证不等式 $0<\alpha q_n-p_n\le\frac{10}{9}q_n^{-n}$，得对全部 $n\ge 2$：
$$|\widehat u(k^{(n)})|=\frac{q_n^{-n/2}}{2\pi(\alpha q_n-p_n)}\ge\frac{q_n^{-n/2}}{2\pi\cdot\frac{10}{9}q_n^{-n}}=\frac{9}{20\pi}\,q_n^{n/2}=\frac{9}{20\pi}\,10^{n\cdot n!/2}\xrightarrow{n\to\infty}\infty.$$
然而对任何 $u\in C^\infty_0(\mathbb T^2)$（事实上甚至对任何 $u\in L^1(\mathbb T^2)$），恒有一致上界
$$|\widehat u(k^{(n)})|=\left|\int_{\mathbb T^2}u(y)e^{-2\pi i k^{(n)}\cdot y}\,dy\right|\le\int_{\mathbb T^2}|u(y)|\,dy\le\|u\|_{C^0}<\infty\qquad(\forall n\ge 2),$$
矛盾。故对此同一个光滑零均值函数 $F\in C^\infty_0(\mathbb T^2)$，方程 $N_\alpha u=F$ 不存在任何光滑零均值解（甚至不存在 $L^1(\mathbb T^2)$ 或周期分布解，因 $\langle k^{(n)}\rangle\le 2q_n$ 而 $|\widehat u(k^{(n)})|$ 比 $\langle k^{(n)}\rangle$ 的任意次幂增长得更快）。$\square$