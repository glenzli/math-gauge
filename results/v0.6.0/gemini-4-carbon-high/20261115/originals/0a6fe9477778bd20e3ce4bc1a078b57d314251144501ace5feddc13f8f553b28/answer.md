以下在归一化二维环面 $\mathbb{T}^2 = \mathbb{R}^2/\mathbb{Z}^2$（配备归一化 Haar/Lebesgue 测度 $dy = dy_1\,dy_2$，$\operatorname{vol}(\mathbb{T}^2)=1$）上统一采用 S4 所给约定：对 $k=(k_1,k_2)\in\mathbb{Z}^2$，记 $|k|=(k_1^2+k_2^2)^{1/2}$，$\langle k\rangle=(1+|k|^2)^{1/2}$，$e_k(y)=e^{2\pi i k\cdot y}$（其中 $k\cdot y = k_1 y_1 + k_2 y_2$），Fourier 系数为
$$\widehat{u}(k)=\int_{\mathbb{T}^2}u(y)e^{-2\pi i k\cdot y}\,dy, \qquad \|u\|_{H^r}=\left(\sum_{k\in\mathbb{Z}^2}\langle k\rangle^{2r}|\widehat{u}(k)|^2\right)^{1/2},$$
且 $N_\alpha = \alpha\partial_{y_1} + \partial_{y_2}$。对每个 $k\in\mathbb{Z}^2$，直接求导得 $N_\alpha e_k = 2\pi i(\alpha k_1+k_2)e_k$；对任意 $u\in C^\infty(\mathbb{T}^2;\mathbb{C})$，利用 $u$ 与 $e^{-2\pi i k\cdot y}$ 在紧无边流形 $\mathbb{T}^2$ 上的光滑周期性作分部积分，有
$$\widehat{N_\alpha u}(k) = 2\pi i(\alpha k_1 + k_2)\widehat{u}(k) \qquad (\forall k\in\mathbb{Z}^2).$$

---

## S1 有限频带上的逆

### 1. 逆算子的构造与良定性

记有限指标集
$$\Lambda_N := \{k=(k_1,k_2)\in\mathbb{Z}^2 : 0 < |k| \le N\}.$$
因 $N\ge 1$，$(\pm 1,0),(0,\pm 1)\in\Lambda_N$，故 $\Lambda_N$ 是 $\mathbb{Z}^2\setminus\{0\}$ 的非空有限子集。空间 $H_N$ 为
$$H_N = \left\{ u(y)=\sum_{k\in\Lambda_N}\widehat{u}(k)e^{2\pi i k\cdot y} : \widehat{u}(k)\in\mathbb{C} \right\}.$$

首先验证对任意 $k=(k_1,k_2)\in\mathbb{Z}^2\setminus\{0\}$ 均有 $\alpha k_1+k_2\ne 0$：
- 若 $k_1=0$，由 $k\ne(0,0)$ 知 $k_2\ne 0$，故 $\alpha k_1+k_2=k_2\ne 0$；
- 若 $k_1\ne 0$，若 $\alpha k_1+k_2=0$ 则 $\alpha=-k_2/k_1\in\mathbb{Q}$，与 $\alpha\in\mathbb{R}\setminus\mathbb{Q}$ 矛盾。

因此对一切 $k\in\Lambda_N$，特征值 $2\pi i(\alpha k_1+k_2)\ne 0$，且 $N_\alpha(H_N)\subseteq H_N$。对任意 $F\in H_N$，定义线性算子 $T_{\alpha,N}:H_N\to H_N$ 为
$$(T_{\alpha,N}F)(y) := \sum_{k\in\Lambda_N}\frac{\widehat{F}(k)}{2\pi i(\alpha k_1+k_2)}e^{2\pi i k\cdot y}.$$
由于 $\Lambda_N$ 有限，求和为有限和，$T_{\alpha,N}F\in H_N$。由 $N_\alpha$ 的线性性：
- 对任意 $F\in H_N$，
  $$N_\alpha(T_{\alpha,N}F)(y)=\sum_{k\in\Lambda_N}\frac{\widehat{F}(k)}{2\pi i(\alpha k_1+k_2)}N_\alpha(e^{2\pi i k\cdot y})=\sum_{k\in\Lambda_N}\widehat{F}(k)e^{2\pi i k\cdot y}=F(y);$$
- 对任意 $u\in H_N$，因 $k\in\Lambda_N$ 时 $\widehat{N_\alpha u}(k)=2\pi i(\alpha k_1+k_2)\widehat{u}(k)$，故
  $$T_{\alpha,N}(N_\alpha u)(y)=\sum_{k\in\Lambda_N}\frac{2\pi i(\alpha k_1+k_2)\widehat{u}(k)}{2\pi i(\alpha k_1+k_2)}e^{2\pi i k\cdot y}=u(y).$$

故 $T_{\alpha,N}=(N_\alpha|_{H_N})^{-1}$ 即为 $N_\alpha$ 在 $H_N$ 上的唯一双侧线性逆。

### 2. 任意 $r\in\mathbb{R}$ 下 $H^r\to H^r$ 逆算子范数精确式

**结论**：对任意 $r\in\mathbb{R}$，逆算子范数与 $r$ 无关，精确式为
$$\left\|(N_\alpha|_{H_N})^{-1}\right\|_{(H_N,\|\cdot\|_{H^r})\to(H_N,\|\cdot\|_{H^r})}
= \max_{\substack{k\in\mathbb{Z}^2 \\ 0<|k|\le N}}\frac{1}{2\pi|\alpha k_1+k_2|}
= \frac{1}{2\pi\min\limits_{\substack{k\in\mathbb{Z}^2 \\ 0<|k|\le N}}|\alpha k_1+k_2|}.$$

**证明**：记 $M_{\alpha,N}:=\max_{k\in\Lambda_N}\frac{1}{2\pi|\alpha k_1+k_2|}$。因 $\Lambda_N$ 非空有限且其上 $|\alpha k_1+k_2|>0$，该最大值有限且在某个 $k^*=(k_1^*,k_2^*)\in\Lambda_N$ 处取到。

1. **上界**：对任意 $F\in H_N$，
   $$\left\|(N_\alpha|_{H_N})^{-1}F\right\|_{H^r}^2
   = \sum_{k\in\Lambda_N}\langle k\rangle^{2r}\left|\frac{\widehat{F}(k)}{2\pi i(\alpha k_1+k_2)}\right|^2
   \le M_{\alpha,N}^2\sum_{k\in\Lambda_N}\langle k\rangle^{2r}|\widehat{F}(k)|^2
   = M_{\alpha,N}^2\|F\|_{H^r}^2.$$
   开方得 $\|(N_\alpha|_{H_N})^{-1}\|_{H^r\to H^r}\le M_{\alpha,N}$。
2. **下界（取到性）**：取 $F_*(y):=e^{2\pi i k^*\cdot y}\in H_N\setminus\{0\}$。则 $\|F_*\|_{H^r}=\langle k^*\rangle^r>0$，而
   $$(N_\alpha|_{H_N})^{-1}F_*(y)=\frac{1}{2\pi i(\alpha k_1^*+k_2^*)}e^{2\pi i k^*\cdot y},$$
   从而
   $$\left\|(N_\alpha|_{H_N})^{-1}F_*\right\|_{H^r}=\frac{\langle k^*\rangle^r}{2\pi|\alpha k_1^*+k_2^*|}=M_{\alpha,N}\|F_*\|_{H^r}.$$

综上，$\|(N_\alpha|_{H_N})^{-1}\|_{H^r\to H^r}=M_{\alpha,N}$。$\blacksquare$

---

## S2 有算术界的截断误差

### 1. 预备引理与 S1 适用条件检验

- **$\alpha$ 的无理性**：若 $\alpha=p/q\in\mathbb{Q}$（$q\in\mathbb{Z}\setminus\{0\},\,p\in\mathbb{Z}$），取 $k=(q,-p)\ne(0,0)$ 得 $|\alpha k_1+k_2|=0<c\langle k\rangle^{-s}$，与假设矛盾。故 $\alpha\in\mathbb{R}\setminus\mathbb{Q}$。
- **晶格级数收敛引理**：对任意 $\tau>2$，$\sum_{k\in\mathbb{Z}^2}\langle k\rangle^{-\tau}<\infty$。
  *证明*：对任意 $k\in\mathbb{Z}^2$ 及 $y\in k+[-1/2,1/2]^2$，有 $|y|\le |k|+1/\sqrt{2}$，故 $1+|y|^2\le 1+2|k|^2+1=2\langle k\rangle^2$，即 $\langle k\rangle^{-\tau}\le 2^{\tau/2}(1+|y|^2)^{-\tau/2}$。在两两内部不交的单位方体 $k+[-1/2,1/2]^2$ 上积分并求和，化为极坐标得
  $$\sum_{k\in\mathbb{Z}^2}\langle k\rangle^{-\tau}\le 2^{\tau/2}\int_{\mathbb{R}^2}(1+|y|^2)^{-\tau/2}\,dy = 2^{\tau/2}\cdot 2\pi\int_0^\infty \rho(1+\rho^2)^{-\tau/2}\,d\rho = \frac{2^{\tau/2}\pi}{\tau/2-1}<\infty.$$
- **$F$ 的 Fourier 系数速降性**：设 $F\in C^\infty_0(\mathbb{T}^2)$，则 $\widehat{F}(0)=\int_{\mathbb{T}^2}F(y)\,dy=0$。对任意 $M\in\mathbb{N}_0$，因 $F\in C^\infty(\mathbb{T}^2)$ 光滑周期，分部积分 $2M$ 次得 $(1+4\pi^2|k|^2)^M\widehat{F}(k)=\int_{\mathbb{T}^2}(1-\Delta)^M F(y)e^{-2\pi i k\cdot y}\,dy$，由 $4\pi^2>1$ 知
  $$\langle k\rangle^{2M}|\widehat{F}(k)|\le \|(1-\Delta)^M F\|_{L^\infty(\mathbb{T}^2)}<\infty \qquad (\forall k\in\mathbb{Z}^2).$$
  特别地，对任意 $\sigma\in\mathbb{R}$，取整数 $M>(\sigma+2)/2$ 并结合晶格级数收敛引理（$\tau=4M-2\sigma>4>2$），知 $\|F\|_{H^\sigma}<\infty$。
- **截断解 $u_N$**：$F$ 在 $0<|k|\le N$ 上的频带截断为 $F_N(y)=\sum_{0<|k|\le N}\widehat{F}(k)e^{2\pi i k\cdot y}\in H_N$（注意 $\widehat{F}(0)=0$）。因 $\alpha\notin\mathbb{Q}$、$N\ge 1$、$F_N\in H_N$，满足 S1 的全部适用条件，故
  $$u_N(y)=\sum_{0<|k|\le N}\frac{\widehat{F}(k)}{2\pi i(\alpha k_1+k_2)}e^{2\pi i k\cdot y}\in H_N.$$

### 2. 光滑零均值解 $u$ 的构造与验证

定义 $c_0:=0$，对 $k\in\mathbb{Z}^2\setminus\{0\}$ 令 $c_k:=\frac{\widehat{F}(k)}{2\pi i(\alpha k_1+k_2)}$，构造级数
$$u(y):=\sum_{k\in\mathbb{Z}^2\setminus\{0\}}\frac{\widehat{F}(k)}{2\pi i(\alpha k_1+k_2)}e^{2\pi i k\cdot y}.$$

1. **光滑性（$u\in C^\infty(\mathbb{T}^2;\mathbb{C})$）与逐项求导**：对任意非负整数 $a,b\ge 0$，记 $m=a+b$。利用 $|k_1|^a|k_2|^b\le |k|^m\le \langle k\rangle^m$ 及算术下界 $|\alpha k_1+k_2|\ge c\langle k\rangle^{-s}$（$k\ne 0$），逐项求导级数的通项在 $\mathbb{T}^2$ 上满足一致估计
   $$\sup_{y\in\mathbb{T}^2}\left|c_k(2\pi i k_1)^a(2\pi i k_2)^b e^{2\pi i k\cdot y}\right|
   \le \frac{(2\pi)^m\langle k\rangle^m|\widehat{F}(k)|}{2\pi c\langle k\rangle^{-s}}
   = \frac{(2\pi)^{m-1}}{c}\langle k\rangle^{m+s}|\widehat{F}(k)|.$$
   取整数 $M\in\mathbb{N}$ 使 $2M-m-s>2$。由 $\langle k\rangle^{2M}|\widehat{F}(k)|\le \|(1-\Delta)^M F\|_{L^\infty}$ 及晶格级数收敛引理（$\tau=2M-m-s>2$），有
   $$\sum_{k\in\mathbb{Z}^2\setminus\{0\}}\frac{(2\pi)^{m-1}}{c}\langle k\rangle^{m+s}|\widehat{F}(k)|
   \le \frac{(2\pi)^{m-1}\|(1-\Delta)^M F\|_{L^\infty}}{c}\sum_{k\in\mathbb{Z}^2\setminus\{0\}}\langle k\rangle^{-(2M-m-s)}<\infty.$$
   由 **Weierstrass 优级数判别法**，对一切 $(a,b)\in\mathbb{N}_0^2$，形式偏导级数在 $\mathbb{T}^2$（等价地在 $\mathbb{R}^2$ 上作为 $\mathbb{Z}^2$-周期连续函数列）一致且绝对收敛。援引**一致收敛函数项级数的逐项求导定理**（原级数一致收敛，且一阶偏导级数在 $\mathbb{R}^2$ 上一致收敛，按阶数 $a+b$ 归纳适用），得 $u\in C^\infty(\mathbb{T}^2;\mathbb{C})$ 且任意阶偏导数均可逐项求得。
2. **零均值与 Fourier 系数**：因定义 $u$ 的级数在有限测度空间 $(\mathbb{T}^2,dy)$（$\operatorname{vol}(\mathbb{T}^2)=1<\infty$）上一致收敛，积分与无穷求和可交换次序：
   $$\int_{\mathbb{T}^2}u(y)\,dy = \sum_{k\ne 0}c_k\int_{\mathbb{T}^2}e^{2\pi i k\cdot y}\,dy = 0, \qquad \widehat{u}(k)=\sum_{l\ne 0}c_l\int_{\mathbb{T}^2}e^{2\pi i(l-k)\cdot y}\,dy = c_k \quad (\forall k\in\mathbb{Z}^2).$$
   故 $u\in C^\infty_0(\mathbb{T}^2)$。
3. **满足方程 $N_\alpha u=F$**：对一阶偏导逐项计算得
   $$N_\alpha u(y)=\sum_{k\in\mathbb{Z}^2\setminus\{0\}}c_k\cdot 2\pi i(\alpha k_1+k_2)e^{2\pi i k\cdot y}=\sum_{k\in\mathbb{Z}^2\setminus\{0\}}\widehat{F}(k)e^{2\pi i k\cdot y}=F(y),$$
   最后一个等号援引 $\mathbb{T}^2$ 上的 **Fourier 逆变换定理**（适用条件：$F\in C^\infty_0(\mathbb{T}^2)$ 连续，$\widehat{F}(0)=0$，且 $\sum_{k\in\mathbb{Z}^2}|\widehat{F}(k)|<\infty$，故 Fourier 级数一致收敛于 $F$）。

### 3. 截断误差估计的证明

设 $r\in\mathbb{R}$，$q\ge 0$。因 $u,u_N\in C^\infty_0(\mathbb{T}^2)$，有 $u-u_N\in C^\infty_0(\mathbb{T}^2)$，其 Fourier 系数满足：当 $|k|\le N$ 时 $\widehat{u-u_N}(k)=0$；当 $|k|>N$ 时 $\widehat{u-u_N}(k)=\frac{\widehat{F}(k)}{2\pi i(\alpha k_1+k_2)}$。

对每个满足 $|k|>N$ 的整点 $k\in\mathbb{Z}^2$：
- 因 $k\ne 0$，算术界给出 $|\alpha k_1+k_2|\ge c\langle k\rangle^{-s}>0$，即 $(2\pi|\alpha k_1+k_2|)^{-2}\le (2\pi c)^{-2}\langle k\rangle^{2s}$；
- 因 $|k|>N\ge 1$，有 $\langle k\rangle^2 = 1+|k|^2 > 1+N^2 > 0$；又因 $q\ge 0$（$-q\le 0$），幂函数单调性给出 $\langle k\rangle^{-2q} = (1+|k|^2)^{-q} \le (1+N^2)^{-q}$。

将两式代入 $H^r$ 范数平方得
$$\begin{aligned}
\|u-u_N\|_{H^r}^2
&= \sum_{|k|>N}\langle k\rangle^{2r}\left|\frac{\widehat{F}(k)}{2\pi i(\alpha k_1+k_2)}\right|^2 \\
&\le \frac{1}{(2\pi c)^2}\sum_{|k|>N}\langle k\rangle^{2r+2s}|\widehat{F}(k)|^2 \\
&= \frac{1}{(2\pi c)^2}\sum_{|k|>N}\langle k\rangle^{-2q}\langle k\rangle^{2(r+s+q)}|\widehat{F}(k)|^2 \\
&\le \frac{(1+N^2)^{-q}}{(2\pi c)^2}\sum_{|k|>N}\langle k\rangle^{2(r+s+q)}|\widehat{F}(k)|^2
\le \frac{(1+N^2)^{-q}}{(2\pi c)^2}\|F\|_{H^{r+s+q}}^2.
\end{aligned}$$
两边取非负平方根即得
$$\|u-u_N\|_{H^r}\le (2\pi c)^{-1}(1+N^2)^{-q/2}\|F\|_{H^{r+s+q}}.\qquad\blacksquare$$

---

## S3 固定频带内改变方向

**证明**：设 $\alpha,\beta\in\mathbb{R}\setminus\mathbb{Q}$，$N\ge 1$，且对一切 $k\in\Lambda_N=\{k\in\mathbb{Z}^2:0<|k|\le N\}$ 小除数满足
$$|\alpha k_1+k_2|\ge \delta>0, \qquad |\beta k_1+k_2|\ge \delta>0.$$
给定 $F\in H_N$，S1 对 $(N_\alpha,H_N)$ 与 $(N_\beta,H_N)$ 的适用条件（$\alpha,\beta$ 无理，$N\ge 1$，$F\in H_N$）全部满足，故对应唯一解 $u_\alpha,u_\beta\in H_N$ 为
$$u_\alpha(y)=\sum_{k\in\Lambda_N}\frac{\widehat{F}(k)}{2\pi i(\alpha k_1+k_2)}e^{2\pi i k\cdot y}, \qquad u_\beta(y)=\sum_{k\in\Lambda_N}\frac{\widehat{F}(k)}{2\pi i(\beta k_1+k_2)}e^{2\pi i k\cdot y}.$$
于是 $u_\alpha-u_\beta\in H_N$，对任意 $k\in\Lambda_N$，其 Fourier 系数为
$$\widehat{u_\alpha}(k)-\widehat{u_\beta}(k)
= \widehat{F}(k)\left(\frac{1}{2\pi i(\alpha k_1+k_2)}-\frac{1}{2\pi i(\beta k_1+k_2)}\right)
= \widehat{F}(k)\frac{(\beta-\alpha)k_1}{2\pi i(\alpha k_1+k_2)(\beta k_1+k_2)}.$$
对 $k\in\Lambda_N$，由 $|k_1|\le (k_1^2+k_2^2)^{1/2}=|k|\le N$ 以及 $|\alpha k_1+k_2|\ge\delta$、$|\beta k_1+k_2|\ge\delta$，得
$$\left|\widehat{u_\alpha}(k)-\widehat{u_\beta}(k)\right|
= \frac{|\alpha-\beta||k_1|}{2\pi|\alpha k_1+k_2||\beta k_1+k_2|}|\widehat{F}(k)|
\le \frac{|\alpha-\beta|N}{2\pi\delta^2}|\widehat{F}(k)|.$$
对任意 $r\in\mathbb{R}$，两边平方乘以 $\langle k\rangle^{2r}$ 并对 $k\in\Lambda_N$ 求和：
$$\|u_\alpha-u_\beta\|_{H^r}^2
= \sum_{k\in\Lambda_N}\langle k\rangle^{2r}|\widehat{u_\alpha}(k)-\widehat{u_\beta}(k)|^2
\le \left(\frac{|\alpha-\beta|N}{2\pi\delta^2}\right)^2\sum_{k\in\Lambda_N}\langle k\rangle^{2r}|\widehat{F}(k)|^2
= \left(\frac{|\alpha-\beta|N}{2\pi\delta^2}\right)^2\|F\|_{H^r}^2.$$
开方即得
$$\|u_\alpha-u_\beta\|_{H^r}\le |\alpha-\beta|N(2\pi\delta^2)^{-1}\|F\|_{H^r}.\qquad\blacksquare$$

---

## S4 整体对象与全部恢复目标

### 总体结论与定理陈述

仅在“$\alpha\in\mathbb{R}\setminus\mathbb{Q}$”这一前提下，$N_\alpha:C^\infty_0(\mathbb{T}^2)\to C^\infty_0(\mathbb{T}^2)$ **并非对所有无理数 $\alpha$ 都可逆**（对所有无理数均单射，但当且仅当 $\alpha$ 为非 Liouville/Diophantine 无理数时满射；Liouville 反例见下述定理证明及 S6）。完整分类、构造与特定方向 $\alpha_*=\sqrt{2}-1$ 的结论总结如下：

**定理（$N_\alpha$ 在 $C^\infty_0(\mathbb{T}^2)$ 上的可逆性与正则性分类）**：设 $\alpha\in\mathbb{R}\setminus\mathbb{Q}$。
1. **单射性（唯一性）**：对任意无理数 $\alpha$，$N_\alpha:C^\infty_0(\mathbb{T}^2)\to C^\infty_0(\mathbb{T}^2)$ 都是良定的单射；即对任意 $F\in C^\infty_0(\mathbb{T}^2)$，方程 $N_\alpha u=F$ 在 $C^\infty_0(\mathbb{T}^2)$ 中至多有一个解。
2. **可逆性刻画（Diophantine 判据）**：每个 $F\in C^\infty_0(\mathbb{T}^2)$ 都有唯一光滑零均值解 $N_\alpha u=F$（即 $N_\alpha:C^\infty_0(\mathbb{T}^2)\to C^\infty_0(\mathbb{T}^2)$ 为双射），**当且仅当** $\alpha$ 满足某阶 Diophantine 条件（即 $\alpha$ 不是 Liouville 数）：存在常数 $c>0$ 与 $s\ge 0$，使得
   $$|\alpha k_1+k_2|\ge c\langle k\rangle^{-s}\qquad(\forall k\in\mathbb{Z}^2\setminus\{0\})$$
   （等价于一维形式：存在 $c'>0,\,s\ge 0$ 使对一切整数 $q\ge 1,\,p\in\mathbb{Z}$ 有 $|q\alpha-p|\ge c'q^{-s}$）。满足此条件时，逆算子由绝对一致收敛级数给出：
   $$(N_\alpha^{-1}F)(y)=\sum_{k\in\mathbb{Z}^2\setminus\{0\}}\frac{\widehat{F}(k)}{2\pi i(\alpha k_1+k_2)}e^{2\pi i k\cdot y}.$$
   反之，若 $\alpha$ 为 Liouville 数（上述条件对一切 $c>0,\,s\ge 0$ 均不成立，例如 S6 中的 $\alpha=\sum_{n=1}^\infty 10^{-n!}$），则存在 $F\in C^\infty_0(\mathbb{T}^2)$ 使 $N_\alpha u=F$ 在 $C^\infty_0(\mathbb{T}^2)$ 中无解。
3. **允许正则性损失 $s\ge 0$ 的完全分类**：对给定 $\alpha\in\mathbb{R}\setminus\mathbb{Q}$ 与 $s\ge 0$，性质
   $$\text{“对每个 }r\in\mathbb{R}\text{ 存在有限常数 }C_{\alpha,r,s}\text{ 使 }\|u\|_{H^r}\le C_{\alpha,r,s}\|N_\alpha u\|_{H^{r+s}}\ (\forall u\in C^\infty_0(\mathbb{T}^2))\text{”}$$
   成立，**当且仅当**
   $$\inf_{k\in\mathbb{Z}^2\setminus\{0\}}\langle k\rangle^s|\alpha k_1+k_2| > 0.$$
   此外，对**任何**无理数 $\alpha$，区间 $[0,1)$ 内的数绝不可能是允许损失（必有 $s\ge 1$）。记临界指数 $s_*(\alpha):=\inf\{s\ge 0:\inf_{k\ne 0}\langle k\rangle^s|\alpha k_1+k_2|>0\}\in[1,\infty]$（约定 $\inf\emptyset=+\infty$），则全部允许损失集合为：
   - 当 $\alpha$ 为 Liouville 数（$s_*(\alpha)=+\infty$）时，允许集合为 $\emptyset$；
   - 当 $\alpha$ 为 Diophantine 数（$1\le s_*(\alpha)<\infty$）时，允许集合为上闭射线 $[s_*(\alpha),\infty)$（若 $\inf_{k\ne 0}\langle k\rangle^{s_*(\alpha)}|\alpha k_1+k_2|>0$）或 $(s_*(\alpha),\infty)$（若该下确界为 $0$）。
4. **$\alpha_*=\sqrt{2}-1$ 的精确损失与 $C^m$ 估计**：
   - $\alpha_*=\sqrt{2}-1$ 无理且满足二次型算术下界，其全部允许损失集合为 $[1,\infty)$，故**最小允许损失为 $s_{\min}=1$，且 $s=1$ 可以取到**。
   - **判断结论：成立**。对每个 $m\in\mathbb{N}_0$，确实存在与 $F$ 无关的有限常数 $C_m$，使得对所有 $F\in C^\infty_0(\mathbb{T}^2)$ 成立
     $$\|N_{\alpha_*}^{-1}F\|_{C^m}\le C_m\|F\|_{C^{m+4}}.$$

---

### 完整证明

#### 第一部分：良定性与单射性（结论 1）

对任意 $u\in C^\infty_0(\mathbb{T}^2)$，$N_\alpha u\in C^\infty(\mathbb{T}^2;\mathbb{C})$，且 $\int_{\mathbb{T}^2}N_\alpha u\,dy = \widehat{N_\alpha u}(0)=2\pi i(\alpha\cdot 0+0)\widehat{u}(0)=0$，故 $N_\alpha:C^\infty_0(\mathbb{T}^2)\to C^\infty_0(\mathbb{T}^2)$ 良定。

若 $u\in C^\infty_0(\mathbb{T}^2)$ 满足 $N_\alpha u=0$，则对一切 $k\in\mathbb{Z}^2$ 有 $2\pi i(\alpha k_1+k_2)\widehat{u}(k)=0$。如 S1 所证，$\alpha\notin\mathbb{Q}$ 蕴含 $k\ne 0$ 时 $\alpha k_1+k_2\ne 0$，从而 $\widehat{u}(k)=0$（$\forall k\ne 0$）；结合零均值 $\widehat{u}(0)=0$，由 Parseval 恒等式得 $\|u\|_{L^2}=0$，再由 $u$ 的连续性得 $u\equiv 0$。因此单射性对一切无理数 $\alpha$ 成立。（附注：若 $\alpha=p/q\in\mathbb{Q}$，$q\ge 1$，则 $u(y)=e^{2\pi i(q y_1-p y_2)}\in C^\infty_0(\mathbb{T}^2)\setminus\{0\}$ 满足 $N_\alpha u=0$，单射性与满射性均不成立。）

#### 第二部分：允许损失 $s\ge 0$ 的充要刻画与 $s\ge 1$ 下界（结论 3）

先固定 $\alpha\in\mathbb{R}\setminus\mathbb{Q}$ 与 $s\ge 0$。

- **充分性**：设 $c:=\inf_{k\ne 0}\langle k\rangle^s|\alpha k_1+k_2|>0$。对任意 $r\in\mathbb{R}$ 及任意 $u\in C^\infty_0(\mathbb{T}^2)$，因 $\widehat{u}(0)=0$ 且 $k\ne 0$ 时 $\widehat{N_\alpha u}(k)=2\pi i(\alpha k_1+k_2)\widehat{u}(k)$，有
  $$\|u\|_{H^r}^2 = \sum_{k\ne 0}\langle k\rangle^{2r}\frac{|\widehat{N_\alpha u}(k)|^2}{(2\pi|\alpha k_1+k_2|)^2}
  \le \frac{1}{(2\pi c)^2}\sum_{k\ne 0}\langle k\rangle^{2(r+s)}|\widehat{N_\alpha u}(k)|^2
  = \frac{1}{(2\pi c)^2}\|N_\alpha u\|_{H^{r+s}}^2.$$
  故取 $C_{\alpha,r,s}=(2\pi c)^{-1}<\infty$（甚至与 $r$ 无关）即满足估计。
- **必要性**：反之，设哪怕仅对**某一个** $r\in\mathbb{R}$ 存在有限常数 $C_{\alpha,r,s}>0$，使一切 $u\in C^\infty_0(\mathbb{T}^2)$ 满足 $\|u\|_{H^r}\le C_{\alpha,r,s}\|N_\alpha u\|_{H^{r+s}}$。对任意 $k\in\mathbb{Z}^2\setminus\{0\}$，检验单一模式 $u_k(y):=e^{2\pi i k\cdot y}$。显然 $u_k\in C^\infty(\mathbb{T}^2;\mathbb{C})$ 且 $\int_{\mathbb{T}^2}u_k\,dy=0$，即 $u_k\in C^\infty_0(\mathbb{T}^2)$。因 $\|u_k\|_{H^r}=\langle k\rangle^r$，$\|N_\alpha u_k\|_{H^{r+s}}=2\pi|\alpha k_1+k_2|\langle k\rangle^{r+s}$，代入不等式得
  $$\langle k\rangle^r \le 2\pi C_{\alpha,r,s}|\alpha k_1+k_2|\langle k\rangle^{r+s}
  \iff \langle k\rangle^s|\alpha k_1+k_2|\ge \frac{1}{2\pi C_{\alpha,r,s}}>0.$$
  对 $k\in\mathbb{Z}^2\setminus\{0\}$ 取下确界即得 $\inf_{k\ne 0}\langle k\rangle^s|\alpha k_1+k_2|\ge (2\pi C_{\alpha,r,s})^{-1}>0$。

又因 $k\ne 0$ 时 $\langle k\rangle>1$，若 $s_0$ 满足 $\inf_{k\ne 0}\langle k\rangle^{s_0}|\alpha k_1+k_2|>0$，则对一切 $s\ge s_0$ 有 $\langle k\rangle^s\ge\langle k\rangle^{s_0}$，从而 $[s_0,\infty)$ 内所有 $s$ 均允许，故允许集合必为上闭射线（或空集）。

下面证明对任何无理数 $\alpha$，**任何 $s\in[0,1)$ 均不允许**（Dirichlet 逼近论证）：
对任意正整数 $Q\ge 1$，考察 $Q+1$ 个小数部分 $\{j\alpha\}:=j\alpha-\lfloor j\alpha\rfloor\in[0,1)$（$0\le j\le Q$）。将 $[0,1)$ 剖分为 $Q$ 个半开区间 $[l/Q,(l+1)/Q)$（$0\le l\le Q-1$），由抽屉原理必存在 $0\le a<b\le Q$ 落入同一小区间。令 $q=b-a\in\{1,\dots,Q\}$，则存在整数 $p\in\mathbb{Z}$ 使 $0<|q\alpha-p|<1/Q\le 1/q$（因 $\alpha\notin\mathbb{Q}$，左端严格大于 $0$）。令 $Q\to\infty$，便得到无穷多对 $(q_j,p_j)\in\mathbb{N}_{\ge 1}\times\mathbb{Z}$ 满足 $q_j\to\infty$ 且 $|q_j\alpha-p_j|<1/q_j\le 1$。
对 $k^{(j)}:=(q_j,-p_j)\in\mathbb{Z}^2\setminus\{0\}$，由 $|p_j|\le q_j|\alpha|+1\le (|\alpha|+1)q_j$ 知 $\langle k^{(j)}\rangle = (1+q_j^2+p_j^2)^{1/2}\le \sqrt{2+(|\alpha|+1)^2}\,q_j$。故当 $0\le s<1$ 时，
$$\langle k^{(j)}\rangle^s|\alpha k_1^{(j)}+k_2^{(j)}|
\le \left(2+(|\alpha|+1)^2\right)^{s/2} q_j^s\cdot \frac{1}{q_j}
= \left(2+(|\alpha|+1)^2\right)^{s/2} q_j^{s-1}\xrightarrow{j\to\infty}0.$$
因此 $\inf_{k\ne 0}\langle k\rangle^s|\alpha k_1+k_2|=0$，即 $s\in[0,1)$ 绝不允许。（顺带验证一维与二维算术条件等价：若 $|q\alpha-p|\ge c'q^{-s}$，则 $k_1=0\ne k_2$ 时 $|\alpha k_1+k_2|=|k_2|\ge 1\ge \langle k\rangle^{-s}$，$k_1\ne 0$ 时 $|\alpha k_1+k_2|\ge c'|k_1|^{-s}\ge c'\langle k\rangle^{-s}$；反之若 $|\alpha k_1+k_2|\ge c\langle k\rangle^{-s}$，则 $|q\alpha-p|<1$ 时 $|q\alpha-p|\ge c(2+(|\alpha|+1)^2)^{-s/2}q^{-s}$，$|q\alpha-p|\ge 1$ 时 $|q\alpha-p|\ge q^{-s}$。）

#### 第三部分：可逆性充要条件与反例构造（结论 2）

- **充分性与构造**：若存在 $c>0,\,s\ge 0$ 使 $|\alpha k_1+k_2|\ge c\langle k\rangle^{-s}$（$\forall k\ne 0$），则对任意 $F\in C^\infty_0(\mathbb{T}^2)$，直接满足 S2 的全部前提条件，S2 所构造的 $u=N_\alpha^{-1}F\in C^\infty_0(\mathbb{T}^2)$ 满足 $N_\alpha u=F$；结合第一部分的唯一性，$N_\alpha$ 在 $C^\infty_0(\mathbb{T}^2)$ 上可逆。
- **必要性（对一般 Liouville 数的不可解数据构造）**：假设 $\alpha\in\mathbb{R}\setminus\mathbb{Q}$ 不满足任何 Diophantine 界，即对每个 $n\in\mathbb{N}$ 均有 $\inf_{k\ne 0}\langle k\rangle^{n^2}|\alpha k_1+k_2|=0$。归纳选取点列 $\{k^{(n)}\}_{n=1}^\infty\subset\mathbb{Z}^2\setminus\{0\}$：
  - 取 $k^{(1)}\ne 0$ 使 $\langle k^{(1)}\rangle|\alpha k_1^{(1)}+k_2^{(1)}|<1$；
  - 已取定 $k^{(1)},\dots,k^{(n-1)}$ 后，在有限集 $\{k\in\mathbb{Z}^2:0<|k|\le |k^{(n-1)}|+n\}$ 上 $\langle k\rangle^{n^2}|\alpha k_1+k_2|$ 有正最小值（因 $\alpha\notin\mathbb{Q}$），故由下确界为 $0$ 可取 $k^{(n)}\in\mathbb{Z}^2\setminus\{0\}$ 满足 $|k^{(n)}|>|k^{(n-1)}|+n$（从而 $k^{(n)}$ 两两互异）且
    $$|\alpha k_1^{(n)}+k_2^{(n)}|<\langle k^{(n)}\rangle^{-n^2}.$$
  定义级数
  $$F(y):=\sum_{n=1}^\infty \langle k^{(n)}\rangle^{-n} e^{2\pi i k^{(n)}\cdot y}.$$
  对任意 $(a,b)\in\mathbb{N}_0^2$（记 $m=a+b$），当 $n\ge m+3$ 时通项上界为 $(2\pi)^m\langle k^{(n)}\rangle^{m-n}\le (2\pi)^m\langle k^{(n)}\rangle^{-3}$。因 $k^{(n)}$ 互异，结合 S2 中的晶格级数收敛引理（$\tau=3>2$），$\sum_{n\ge m+3}\langle k^{(n)}\rangle^{-3}\le \sum_{k\in\mathbb{Z}^2}\langle k\rangle^{-3}<\infty$。同 S2 由 Weierstrass 判别法及逐项求导/积分定理，知 $F\in C^\infty_0(\mathbb{T}^2)$ 且 $\widehat{F}(k^{(n)})=\langle k^{(n)}\rangle^{-n}$。
  若存在 $u\in C^\infty_0(\mathbb{T}^2)$ 使 $N_\alpha u=F$，则对每个 $n\ge 2$ 有 $2\pi i(\alpha k_1^{(n)}+k_2^{(n)})\widehat{u}(k^{(n)})=\langle k^{(n)}\rangle^{-n}$，故
  $$\left|\widehat{u}(k^{(n)})\right|=\frac{\langle k^{(n)}\rangle^{-n}}{2\pi|\alpha k_1^{(n)}+k_2^{(n)}|}
  > \frac{1}{2\pi}\langle k^{(n)}\rangle^{n^2-n}\ge \frac{1}{2\pi}(1+n^2)^{(n^2-n)/2}\xrightarrow{n\to\infty}+\infty,$$
  这与 $|\widehat{u}(k)|\le \|u\|_{L^\infty(\mathbb{T}^2)}<\infty$ 矛盾！（具体方向的显式反例同时见 S6。）

#### 第四部分：$\alpha_*=\sqrt{2}-1$ 的最小损失与 $C^m$ 正则性估计（结论 4）

1. **$\alpha_*=\sqrt{2}-1$ 的无理性与 $s_{\min}=1$ 的取到性**：
   若 $\alpha_*=\sqrt{2}-1\in\mathbb{Q}$，则 $\sqrt{2}\in\mathbb{Q}$；写既约分数 $\sqrt{2}=a/b$ 得 $a^2=2b^2$，推出 $2\mid a$ 进而 $2\mid b$，矛盾，故 $\alpha_*\in\mathbb{R}\setminus\mathbb{Q}$。

   下面对一切 $k=(k_1,k_2)\in\mathbb{Z}^2\setminus\{0\}$ 建立 $s=1$ 的精确型下界：
   - 若 $k_1\ne 0$，考察共轭积
     $$((\sqrt{2}-1)k_1+k_2)((-\sqrt{2}-1)k_1+k_2)=(k_2-k_1)^2-2k_1^2\in\mathbb{Z}.$$
     因 $k_1\ne 0$ 且 $\sqrt{2}\notin\mathbb{Q}$，该整数非零，故其绝对值至少为 $1$：
     $$\left|(\alpha_* k_1+k_2)((-\sqrt{2}-1)k_1+k_2)\right|\ge 1.$$
     对第二因子应用 $\mathbb{R}^2$ 上的 Cauchy-Schwarz 不等式：
     $$|(-\sqrt{2}-1)k_1+k_2|\le \sqrt{(\sqrt{2}+1)^2+1^2}\,\sqrt{k_1^2+k_2^2}=\sqrt{4+2\sqrt{2}}\,|k|<\sqrt{4+2\sqrt{2}}\,\langle k\rangle.$$
     相除得 $|\alpha_* k_1+k_2|\ge (4+2\sqrt{2})^{-1/2}\langle k\rangle^{-1}$。
   - 若 $k_1=0$，由 $k\ne 0$ 知 $|k_2|\ge 1$；又 $\sqrt{4+2\sqrt{2}}>2>1$ 且 $\langle k\rangle>1$，仍有 $|\alpha_* k_1+k_2|=|k_2|\ge 1>(4+2\sqrt{2})^{-1/2}\langle k\rangle^{-1}$。

   因此，令 $c_*:=(4+2\sqrt{2})^{-1/2}>0$，对所有 $k\in\mathbb{Z}^2\setminus\{0\}$ 恒有
   $$|\alpha_* k_1+k_2|\ge c_*\langle k\rangle^{-1}.$$
   由结论 3 知 $[1,\infty)$ 内所有 $s$ 均为允许损失，且任何 $s\in[0,1)$ 均不允许（亦可直接由递推 $(\sqrt{2}-1)^n=a_n\alpha_*+b_n$ 验证：$\langle(a_n,b_n)\rangle\le 2\alpha_*^{-n}$ 而 $|\alpha_* a_n+b_n|=\alpha_*^n$，当 $s<1$ 时 $\langle(a_n,b_n)\rangle^s|\alpha_* a_n+b_n|\le 2^s\alpha_*^{(1-s)n}\to 0$）。故**最小允许损失为 $s_{\min}=1$，且在 $s=1$ 处取到**。

2. **估计 $\|N_{\alpha_*}^{-1}F\|_{C^m}\le C_m\|F\|_{C^{m+4}}$ 的证明**：
   固定任意 $m\in\mathbb{N}_0$ 及任意 $F\in C^\infty_0(\mathbb{T}^2)$，令 $u=N_{\alpha_*}^{-1}F\in C^\infty_0(\mathbb{T}^2)$。
   - 首先对任意 $k=(k_1,k_2)\in\mathbb{Z}^2\setminus\{0\}$，取下标 $j\in\{1,2\}$ 使 $|k_j|=\max(|k_1|,|k_2|)$。因 $k\in\mathbb{Z}^2\setminus\{0\}$，必有 $|k_j|\ge 1$，从而
     $$\langle k\rangle^2 = 1+k_1^2+k_2^2 \le k_j^2+k_j^2+k_j^2 = 3k_j^2 \implies |k_j|\ge \frac{1}{\sqrt{3}}\langle k\rangle.$$
     对 $\widehat{F}(k)$ 关于变量 $y_j$ 分部积分 $m+4$ 次（由 $F\in C^\infty(\mathbb{T}^2)$ 的光滑周期性适用）：
     $$(2\pi i k_j)^{m+4}\widehat{F}(k)=\int_{\mathbb{T}^2}(\partial_{y_j}^{m+4}F)(y)e^{-2\pi i k\cdot y}\,dy.$$
     利用 $\operatorname{vol}(\mathbb{T}^2)=1$ 及 $\sup_{y\in\mathbb{T}^2}|\partial_{y_j}^{m+4}F(y)|\le \|F\|_{C^{m+4}}$，得
     $$|\widehat{F}(k)|\le \frac{\|F\|_{C^{m+4}}}{(2\pi|k_j|)^{m+4}}\le \left(\frac{\sqrt{3}}{2\pi}\right)^{m+4}\langle k\rangle^{-(m+4)}\|F\|_{C^{m+4}}.$$
   - 其次，对任意满足 $a,b\ge 0,\,a+b\le m$ 的偏导指标，由 S2 所证的逐项求导公式、$(2\pi)^{a+b}\le (2\pi)^m$（因 $2\pi>1$）、$|k_1|^a|k_2|^b\le \langle k\rangle^{a+b}\le \langle k\rangle^m$（因 $\langle k\rangle\ge 1$）以及 $|\alpha_* k_1+k_2|\ge c_*\langle k\rangle^{-1}$，对任意 $y\in\mathbb{T}^2$ 有
     $$\begin{aligned}
     \left|\partial_{y_1}^a\partial_{y_2}^b u(y)\right|
     &\le \sum_{k\in\mathbb{Z}^2\setminus\{0\}}\frac{(2\pi)^{a+b}|k_1|^a|k_2|^b}{2\pi|\alpha_* k_1+k_2|}|\widehat{F}(k)| \\
     &\le \frac{(2\pi)^m}{2\pi c_*}\sum_{k\in\mathbb{Z}^2\setminus\{0\}}\langle k\rangle^{m+1}|\widehat{F}(k)| \\
     &\le \frac{3^{(m+4)/2}}{(2\pi)^5 c_*}\left(\sum_{k\in\mathbb{Z}^2\setminus\{0\}}\langle k\rangle^{-3}\right)\|F\|_{C^{m+4}}.
     \end{aligned}$$
   由 S2 的晶格级数收敛引理（取 $\tau=3>2$），$S_3:=\sum_{k\in\mathbb{Z}^2\setminus\{0\}}\langle k\rangle^{-3}<\infty$。对 $y\in\mathbb{T}^2$ 取上确界并对 $a+b\le m$ 取最大值，令有限常数
   $$C_m:=\frac{3^{(m+4)/2}\sqrt{4+2\sqrt{2}}}{(2\pi)^5}\sum_{k\in\mathbb{Z}^2\setminus\{0\}}\langle k\rangle^{-3}<\infty$$
   （仅依赖于 $m$，与 $F$ 无关），即证得 $\|N_{\alpha_*}^{-1}F\|_{C^m}\le C_m\|F\|_{C^{m+4}}$。$\blacksquare$

---

## S5 邻近方向的一致估计

**结论**：**不成立**（不存在满足条件的开区间 $J\ni\alpha_*$、有限 $s\ge 0$ 与常数 $C<\infty$）。

**反例构造与证明**：任给包含 $\alpha_*=\sqrt{2}-1$ 的开区间 $J$、有限实数 $s\ge 0$ 及有限常数 $C<\infty$，我们显式构造一个无理数 $\alpha\in J$ 与一个光滑零均值函数 $u\in C^\infty_0(\mathbb{T}^2)$，使其违反 $\|u\|_{L^2}\le C\|N_\alpha u\|_{H^s}$：

1. **在 $J$ 中选取有理基点**：因 $J$ 是非空开区间，存在 $a<b$ 使 $(a,b)\subseteq J$。取正整数 $q>\frac{2}{b-a}$ 并令 $p:=\left\lfloor q\frac{a+b}{2}\right\rfloor\in\mathbb{Z}$，则 $\left|\frac{p}{q}-\frac{a+b}{2}\right|\le\frac{1}{q}<\frac{b-a}{2}$，故有理数 $\frac{p}{q}\in(a,b)\subseteq J$。记 $\delta_0:=\min\left(\frac{p}{q}-a,\,b-\frac{p}{q}\right)>0$，则开邻域 $\left(\frac{p}{q}-\delta_0,\frac{p}{q}+\delta_0\right)\subseteq J$。
2. **构造 $u\in C^\infty_0(\mathbb{T}^2)$ 与无理方向 $\alpha\in J$**：固定非零整频 $k=(q,-p)\in\mathbb{Z}^2\setminus\{0\}$（因 $q\ge 1$），定义
   $$u(y):=e^{2\pi i(q y_1-p y_2)}.$$
   显然 $u\in C^\infty(\mathbb{T}^2;\mathbb{C})$，且因 $q\ge 1$，$\int_{\mathbb{T}^2}u(y)\,dy=\left(\int_0^1 e^{2\pi i q y_1}\,dy_1\right)\left(\int_0^1 e^{-2\pi i p y_2}\,dy_2\right)=0$，故 $u\in C^\infty_0(\mathbb{T}^2)$，且 $\|u\|_{L^2}=1$。
   再取正整数
   $$n > \max\left\{\frac{\sqrt{2}}{\delta_0},\ 2\sqrt{2}\pi(\max(C,0)+1)\,q(1+q^2+p^2)^{s/2}\right\},$$
   令
   $$\alpha := \frac{p}{q} + \frac{\sqrt{2}}{n}.$$
   - 由 $|\alpha-p/q|=\sqrt{2}/n<\delta_0$ 知 $\alpha\in J$；
   - 若 $\alpha\in\mathbb{Q}$，则 $\sqrt{2}=n(\alpha-p/q)\in\mathbb{Q}$，与 $\sqrt{2}$ 无理（见 S4 证明）矛盾，故 $\alpha\in J\setminus\mathbb{Q}$ 为无理数。
3. **验证估计失效**：因 $N_\alpha u(y)=2\pi i(\alpha q-p)u(y)=2\pi i\frac{\sqrt{2}\,q}{n}u(y)$，故
   $$\|N_\alpha u\|_{H^s}=\frac{2\sqrt{2}\pi q}{n}(1+q^2+p^2)^{s/2}.$$
   由 $n$ 的选取（无论 $C\le 0$ 还是 $C>0$），均有
   $$C\|N_\alpha u\|_{H^s}\le \max(C,0)\cdot\frac{2\sqrt{2}\pi q}{n}(1+q^2+p^2)^{s/2} < \frac{\max(C,0)}{\max(C,0)+1} < 1 = \|u\|_{L^2}.$$

这表明对任意候选 $(J,s,C)$，一致估计 $\|u\|_{L^2}\le C\|N_\alpha u\|_{H^s}$ 均被上述无理 $\alpha\in J$ 与 $u\in C^\infty_0(\mathbb{T}^2)$ 推翻。（注：甚至若取足够大的正整数 $M$，令 $\tilde{\alpha}=\frac{p}{q}+10^{-M}\sum_{j=1}^\infty 10^{-j!}\in J\setminus\mathbb{Q}$，则 $\tilde{\alpha}$ 本身为 $J$ 内的 Liouville 数，由 S4 知连依赖方向的常数都不存在。）$\blacksquare$

---

## S6 一个具体方向的不可解数据

设 $\alpha=\sum_{n=1}^\infty 10^{-n!}$（因 $n!\ge n$，$0<10^{-n!}\le 10^{-n}$，级数绝对收敛于实数 $\alpha\in(0,1/9)$）。

### 1. 通用余项估计与 $\alpha$ 无理性的证明

对任意正整数 $m\ge 1$，记正整数
$$q_m:=10^{m!}, \qquad p_m:=\sum_{n=1}^m 10^{m!-n!}\in\mathbb{N}.$$
考察差值 $q_m\alpha-p_m = \sum_{n=m+1}^\infty 10^{m!-n!}$：
- 每一项严格为正，故 $q_m\alpha-p_m>0$；
- 对任意整数 $n\ge m+1$，记 $j:=n-(m+1)\ge 0$。当 $j=0$ 时 $n!-(m+1)!=0$；当 $j\ge 1$ 时 $n!-(m+1)!=\sum_{l=m+1}^{n-1}l\cdot l!\ge \sum_{l=m+1}^{n-1}1 = j$。故对一切 $m\ge 1$ 及 $n\ge m+1$，恒有
  $$n!-m! = \big((m+1)!-m!\big)+\big(n!-(m+1)!\big) \ge m\cdot m! + j.$$
  因此
  $$0 < q_m\alpha-p_m \le \sum_{j=0}^\infty 10^{-m\cdot m!-j} = \frac{10}{9}\cdot 10^{-m\cdot m!} = \frac{10}{9}q_m^{-m} < 2q_m^{-m}.\tag{$\ast$}$$

**证明 $\alpha\notin\mathbb{Q}$**：反设 $\alpha=a/b\in\mathbb{Q}$，其中 $a\in\mathbb{Z}$，$b\in\mathbb{N}_{\ge 1}$。取 $m=b+1\ge 2$，考虑 $N:=b(q_m\alpha-p_m)=a q_m - b p_m$。
- 一方面，$a,b,q_m,p_m\in\mathbb{Z}$，故 $N\in\mathbb{Z}$ 是整数；
- 另一方面，由 $(\ast)$ 及 $(b+1)(b+1)!\ge 2(b+1)=2b+2$、$10^{2b+2}=100\cdot 10^{2b}>100b$，有
  $$0 < N = b(q_m\alpha-p_m) \le \frac{10}{9}b\cdot 10^{-(b+1)(b+1)!} \le \frac{10}{9}b\cdot 10^{-(2b+2)} < \frac{10}{9}b\cdot\frac{1}{100b}=\frac{1}{90}<1.$$
区间 $(0,1)$ 内不存在整数，矛盾！故 $\alpha$ 无理。

### 2. 同一个不可解光滑零均值数据 $F$ 的构造与证明

定义单个函数 $F:\mathbb{T}^2\to\mathbb{C}$ 为
$$F(y):=\sum_{m=1}^\infty q_m^{-m/2} e^{2\pi i(q_m y_1-p_m y_2)}, \qquad \text{其中 } q_m=10^{m!},\ p_m=\sum_{n=1}^m 10^{m!-n!}.$$

1. **验证 $F\in C^\infty_0(\mathbb{T}^2)$**：
   注意 $0<p_m=q_m\sum_{n=1}^m 10^{-n!}<q_m\sum_{l=1}^\infty 10^{-l}=\frac{1}{9}q_m<q_m$。对任意非负整数 $a,b\ge 0$（记 $M=a+b$），逐项偏导级数的第 $m$ 项在 $\mathbb{T}^2$ 上满足一致上界
   $$\sup_{y\in\mathbb{T}^2}\left|q_m^{-m/2}(2\pi i q_m)^a(-2\pi i p_m)^b e^{2\pi i(q_m y_1-p_m y_2)}\right|
   \le (2\pi)^M q_m^{M-m/2}.$$
   当 $m\ge 2M+2$ 时，$M-m/2\le -1$，故 $q_m^{M-m/2}\le q_m^{-1}=10^{-m!}\le 10^{-m}$。因几何级数 $\sum_{m=2M+2}^\infty 10^{-m}<\infty$，优级数 $\sum_{m=1}^\infty(2\pi)^M q_m^{M-m/2}$ 收敛。由 **Weierstrass 优级数判别法**及**一致收敛级数的逐项求导定理**（在 $\mathbb{R}^2$ 上对周期连续函数列按导数阶数归纳适用），得 $F\in C^\infty(\mathbb{T}^2;\mathbb{C})$。
   又因原级数在有限测度空间 $(\mathbb{T}^2,dy)$ 上一致收敛，逐项积分得
   $$\int_{\mathbb{T}^2}F(y)\,dy=\sum_{m=1}^\infty q_m^{-m/2}\int_{\mathbb{T}^2}e^{2\pi i(q_m y_1-p_m y_2)}\,dy=0$$
   （因对每个 $m\ge 1$，$k^{(m)}:=(q_m,-p_m)$ 满足 $q_m\ge 10\ne 0$）。故 $F\in C^\infty_0(\mathbb{T}^2)$。

2. **计算 $F$ 在频率 $k^{(m)}$ 处的 Fourier 系数**：
   因 $1!<2!<3!<\cdots$ 严格递增，故 $q_1<q_2<q_3<\cdots$，从而向量列 $\{k^{(m)}=(q_m,-p_m)\}_{m=1}^\infty\subset\mathbb{Z}^2\setminus\{0\}$ 两两互异。利用级数的一致收敛性逐项积分并应用三角指数系的正交性 $\int_{\mathbb{T}^2}e^{2\pi i(k^{(l)}-k^{(m)})\cdot y}\,dy=\delta_{l,m}$，得
   $$\widehat{F}(k^{(m)})=\int_{\mathbb{T}^2}F(y)e^{-2\pi i k^{(m)}\cdot y}\,dy = \sum_{l=1}^\infty q_l^{-l/2}\delta_{l,m} = q_m^{-m/2} \qquad (\forall m\ge 1).$$

3. **证明 $N_\alpha u=F$ 无光滑零均值解**：
   反设存在某个 $u\in C^\infty_0(\mathbb{T}^2)$ 满足 $N_\alpha u=F$。
   - 一方面，$u$ 在紧空间 $\mathbb{T}^2$ 上连续，故 $\|u\|_{L^\infty(\mathbb{T}^2)}<\infty$，从而对一切 $k\in\mathbb{Z}^2$ 有
     $$|\widehat{u}(k)|=\left|\int_{\mathbb{T}^2}u(y)e^{-2\pi i k\cdot y}\,dy\right|\le \|u\|_{L^\infty(\mathbb{T}^2)}<\infty;$$
   - 另一方面，在频率 $k^{(m)}=(q_m,-p_m)$ 处比较 $N_\alpha u=F$ 的 Fourier 系数，得
     $$2\pi i(q_m\alpha-p_m)\widehat{u}(k^{(m)})=\widehat{F}(k^{(m)})=q_m^{-m/2}.$$
     结合余项估计 $(\ast)$（$0<q_m\alpha-p_m<2q_m^{-m}$），对每个 $m\ge 1$ 均有
     $$\left|\widehat{u}(k^{(m)})\right|=\frac{q_m^{-m/2}}{2\pi(q_m\alpha-p_m)}>\frac{q_m^{-m/2}}{4\pi q_m^{-m}}=\frac{1}{4\pi}q_m^{m/2}=\frac{1}{4\pi}10^{\frac{1}{2}m\cdot m!}\xrightarrow{m\to\infty}+\infty.$$

   两相矛盾！因此，对于这同一个 $F\in C^\infty_0(\mathbb{T}^2)$，方程 $N_\alpha u=F$ 不存在任何光滑零均值解。$\blacksquare$
