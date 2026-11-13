下面按 **S1–S6** 逐项给出完整解答与证明。

### 记号与预备事实

在 $\mathbb T^2=\mathbb R^2/\mathbb Z^2$ 上配备归一化 Haar 测度（总测度为 $1$）。对 $k=(k_1,k_2)\in\mathbb Z^2$，$|k|=(k_1^2+k_2^2)^{1/2}$ 为 Euclidean 范数，$\langle k\rangle=(1+|k|^2)^{1/2}$。对 $u\in C^\infty(\mathbb T^2;\mathbb C)$，Fourier 系数定义为
$$\widehat u(k)=\int_{\mathbb T^2}u(y)e^{-2\pi i k\cdot y}\,dy.$$
利用 $1$-周期性作分部积分，对任意多指标 $(a,b)\in\mathbb N_0^2$ 有 $\widehat{\partial_1^a\partial_2^b u}(k)=(2\pi i k_1)^a(2\pi i k_2)^b\widehat u(k)$；特别地，对任意整数 $m\ge 0$，
$$\langle k\rangle^{2m}|\widehat u(k)|=\left|\widehat{(1-(2\pi)^{-2}\Delta)^m u}(k)\right|\le \|(1-(2\pi)^{-2}\Delta)^m u\|_{L^\infty(\mathbb T^2)},$$
故 $\widehat u(k)$ 快速衰减。结合 $\{e^{2\pi i k\cdot y}\}_{k\in\mathbb Z^2}$ 在 $L^2(\mathbb T^2)$ 中的完备性（标准 Fourier 级数理论），对所有 $u\in C^\infty(\mathbb T^2;\mathbb C)$，Fourier 级数 $\sum_{k\in\mathbb Z^2}\widehat u(k)e^{2\pi i k\cdot y}$ 及逐项任意阶偏导数均绝对一致收敛于 $u$ 及其相应导数，且 Parseval 等式 $\|u\|_{L^2(\mathbb T^2)}^2=\sum_{k\in\mathbb Z^2}|\widehat u(k)|^2=\|u\|_{H^0}^2$ 成立，并且
$$\widehat{N_\alpha u}(k)=2\pi i(\alpha k_1+k_2)\widehat u(k)\qquad(\forall k\in\mathbb Z^2).$$

此外顺便证明一个后面反复用到的级数收敛性：对任意 $k=(k_1,k_2)\in\mathbb Z^2$，
$$(1+k_1^2+k_2^2)^2-(1+k_1^2)(1+k_2^2)=k_1^2+k_2^2+k_1^4+k_1^2k_2^2+k_2^4\ge 0,$$
从而
$$\sum_{k\in\mathbb Z^2}\langle k\rangle^{-4}\le \sum_{k_1\in\mathbb Z}\sum_{k_2\in\mathbb Z}\frac{1}{(1+k_1^2)(1+k_2^2)}=\left(\sum_{n\in\mathbb Z}\frac{1}{1+n^2}\right)^2<\infty.$$

---

## S1 有限频带上的逆

设 $N\ge 1$，记有限频带指标集 $\Lambda_N=\{k\in\mathbb Z^2:0<|k|\le N\}$。因 $N\ge 1$，$\Lambda_N$ 非空（例如 $(\pm1,0),(0,\pm1)\in\Lambda_N$）且有限，故 $H_N=\operatorname{span}_{\mathbb C}\{e^{2\pi i k\cdot y}:k\in\Lambda_N\}$ 有限维且非零。

1. **可逆性与逆算子的构造**  
   对任意 $u(y)=\sum_{k\in\Lambda_N}\widehat u(k)e^{2\pi i k\cdot y}\in H_N$，逐项求导得
   $$N_\alpha u(y)=\sum_{k\in\Lambda_N}2\pi i(\alpha k_1+k_2)\widehat u(k)e^{2\pi i k\cdot y}\in H_N.$$
   因为 $\alpha\in\mathbb R\setminus\mathbb Q$ 无理，对所有 $k=(k_1,k_2)\in\mathbb Z^2\setminus\{0\}$ 都有 $\alpha k_1+k_2\neq 0$（若 $k_1=0$ 则 $k_2\neq 0$；若 $k_1\neq 0$ 且 $\alpha k_1+k_2=0$，则 $\alpha=-k_2/k_1\in\mathbb Q$，矛盾）。因此 $N_\alpha$ 在 $H_N$ 上的每个特征值 $2\pi i(\alpha k_1+k_2)$ 均非零，$N_\alpha:H_N\to H_N$ 双射。其逆 $N_\alpha^{-1}:H_N\to H_N$ 为
   $$(N_\alpha^{-1}F)(y)=\sum_{0<|k|\le N}\frac{\widehat F(k)}{2\pi i(\alpha k_1+k_2)}e^{2\pi i k\cdot y}\qquad\left(F(y)=\sum_{0<|k|\le N}\widehat F(k)e^{2\pi i k\cdot y}\in H_N\right).$$
   直接代入即得 $N_\alpha(N_\alpha^{-1}F)=F$ 且 $N_\alpha^{-1}(N_\alpha u)=u$。

2. **$H^r\to H^r$ 逆范数精确式**  
   对任意 $r\in\mathbb R$ 与 $F\in H_N$，
   $$\|N_\alpha^{-1}F\|_{H^r}^2=\sum_{k\in\Lambda_N}\langle k\rangle^{2r}\left|\frac{\widehat F(k)}{2\pi i(\alpha k_1+k_2)}\right|^2=\sum_{k\in\Lambda_N}\frac{1}{4\pi^2|\alpha k_1+k_2|^2}\langle k\rangle^{2r}|\widehat F(k)|^2.$$
   由于 $\Lambda_N$ 有限非空且 $|\alpha k_1+k_2|>0$，最小值 $\delta_N(\alpha):=\min_{0<|k|\le N}|\alpha k_1+k_2|>0$ 在某个 $k^*\in\Lambda_N$ 处取到。于是
   $$\|N_\alpha^{-1}F\|_{H^r}^2\le \frac{1}{4\pi^2\delta_N(\alpha)^2}\sum_{k\in\Lambda_N}\langle k\rangle^{2r}|\widehat F(k)|^2=\frac{1}{4\pi^2\delta_N(\alpha)^2}\|F\|_{H^r}^2.$$
   另一方面，取 $F^*(y)=e^{2\pi i k^*\cdot y}\in H_N$，则 $\|F^*\|_{H^r}=\langle k^*\rangle^r>0$ 且
   $$\|N_\alpha^{-1}F^*\|_{H^r}=\frac{\langle k^*\rangle^r}{2\pi|\alpha k_1^*+k_2^*|}=\frac{1}{2\pi\delta_N(\alpha)}\|F^*\|_{H^r}.$$
   故对任意 $r\in\mathbb R$，$N_\alpha^{-1}:(H_N,\|\cdot\|_{H^r})\to(H_N,\|\cdot\|_{H^r})$ 的算子范数与 $r$ 无关，精确式为
   $$\|N_\alpha^{-1}\|_{H^r(H_N)\to H^r(H_N)}=\max_{0<|k|\le N}\frac{1}{2\pi|\alpha k_1+k_2|}=\frac{1}{2\pi\min_{0<|k|\le N}|\alpha k_1+k_2|}.$$

---

## S2 有算术界的截断误差

1. **条件检验与光滑解的构造**  
   由假设 $|\alpha k_1+k_2|\ge c\langle k\rangle^{-s}>0$ 对全部 $k\neq 0$ 成立，可知 $\alpha$ 必为无理数（若 $\alpha=p/q\in\mathbb Q$，$q\ge 1$，取 $k=(q,-p)\neq 0$ 得 $\alpha k_1+k_2=0$，矛盾）。

   设 $F\in C^\infty_0(\mathbb T^2)$，则 $\widehat F(0)=0$ 且 $\widehat F(k)$ 快速衰减。构造形式解
   $$u(y)=\sum_{k\in\mathbb Z^2\setminus\{0\}}\frac{\widehat F(k)}{2\pi i(\alpha k_1+k_2)}e^{2\pi i k\cdot y}.$$
   对任意 $a,b\in\mathbb N_0$，利用算术下界 $|\alpha k_1+k_2|^{-1}\le c^{-1}\langle k\rangle^s$ 与 $|k_1|,|k_2|\le\langle k\rangle$，并取整数 $m\ge \frac{a+b+s+4}{2}$ 利用 $|\widehat F(k)|\le C_m\langle k\rangle^{-2m}$，有
   $$\sum_{k\neq 0}(2\pi |k_1|)^a(2\pi |k_2|)^b\frac{|\widehat F(k)|}{2\pi|\alpha k_1+k_2|}\le \frac{(2\pi)^{a+b-1}}{c}\sum_{k\neq 0}\langle k\rangle^{a+b+s}|\widehat F(k)|\le \frac{(2\pi)^{a+b-1}C_m}{c}\sum_{k\neq 0}\langle k\rangle^{-4}<\infty.$$
   由 Weierstrass M-判别法，$u$ 的定义级数以及逐项求任意阶偏导数得到的级数均在 $\mathbb T^2$ 上绝对一致收敛。因此 $u\in C^\infty(\mathbb T^2;\mathbb C)$，其零频系数为 $0$（故 $\int_{\mathbb T^2}u=0$，即 $u\in C^\infty_0(\mathbb T^2)$），且逐项作用 $N_\alpha$ 得
   $$N_\alpha u(y)=\sum_{k\neq 0}2\pi i(\alpha k_1+k_2)\frac{\widehat F(k)}{2\pi i(\alpha k_1+k_2)}e^{2\pi i k\cdot y}=\sum_{k\neq 0}\widehat F(k)e^{2\pi i k\cdot y}=F(y).$$
   （由 $\alpha\notin\mathbb Q$ 亦知此光滑零均值解唯一。）

2. **截断误差估计**  
   对截断 $F_N(y)=\sum_{0<|k|\le N}\widehat F(k)e^{2\pi i k\cdot y}\in H_N$（$N\ge 1$；实际对 $0\le N<1$ 有 $F_N=0,u_N=0$ 亦成立），由于 $\alpha$ 无理且 $F_N\in H_N$，S1 的构造适用，给出
   $$u_N(y)=(N_\alpha^{-1}F_N)(y)=\sum_{0<|k|\le N}\frac{\widehat F(k)}{2\pi i(\alpha k_1+k_2)}e^{2\pi i k\cdot y}.$$
   于是 $u-u_N\in C^\infty_0(\mathbb T^2)$ 仅含 $|k|>N$ 的频率：
   $$(u-u_N)(y)=\sum_{|k|>N}\frac{\widehat F(k)}{2\pi i(\alpha k_1+k_2)}e^{2\pi i k\cdot y}.$$
   对任意 $r\in\mathbb R$ 与 $q\ge 0$，当 $|k|>N$ 时有 $\langle k\rangle^2=1+|k|^2>1+N^2$，因 $-2q\le 0$ 故 $\langle k\rangle^{-2q}\le (1+N^2)^{-q}$；再结合 $|\alpha k_1+k_2|^{-2}\le c^{-2}\langle k\rangle^{2s}$，得到
   $$\begin{aligned}
   \|u-u_N\|_{H^r}^2
   &=\sum_{|k|>N}\langle k\rangle^{2r}\frac{|\widehat F(k)|^2}{4\pi^2|\alpha k_1+k_2|^2}\\
   &\le \frac{1}{4\pi^2 c^2}\sum_{|k|>N}\langle k\rangle^{2r+2s}|\widehat F(k)|^2\\
   &=\frac{1}{4\pi^2 c^2}\sum_{|k|>N}\langle k\rangle^{-2q}\langle k\rangle^{2(r+s+q)}|\widehat F(k)|^2\\
   &\le \frac{(1+N^2)^{-q}}{4\pi^2 c^2}\sum_{|k|>N}\langle k\rangle^{2(r+s+q)}|\widehat F(k)|^2
   \le (2\pi c)^{-2}(1+N^2)^{-q}\|F\|_{H^{r+s+q}}^2.
   \end{aligned}$$
   （因 $F$ 光滑，右端 $\|F\|_{H^{r+s+q}}<\infty$。）两边开平方即证
   $$\|u-u_N\|_{H^r}\le (2\pi c)^{-1}(1+N^2)^{-q/2}\|F\|_{H^{r+s+q}}.$$

---

## S3 固定频带内改变方向

因 $\alpha,\beta$ 无理、$N\ge 1$（承接 S1 的空间设定）且 $F\in H_N$，S1 适用于 $\alpha$ 与 $\beta$，对应解 $u_\alpha=N_\alpha^{-1}F\in H_N$ 和 $u_\beta=N_\beta^{-1}F\in H_N$ 的 Fourier 系数在 $0<|k|\le N$ 上满足
$$\widehat{u_\alpha-u_\beta}(k)=\frac{\widehat F(k)}{2\pi i}\left(\frac{1}{\alpha k_1+k_2}-\frac{1}{\beta k_1+k_2}\right)=\frac{(\beta-\alpha)k_1}{2\pi i(\alpha k_1+k_2)(\beta k_1+k_2)}\widehat F(k),$$
而在其余频率上均为 $0$。

对全部满足 $0<|k|\le N$ 的 $k=(k_1,k_2)\in\mathbb Z^2$，由题设小除数下界有 $|\alpha k_1+k_2|\ge\delta>0$ 与 $|\beta k_1+k_2|\ge\delta>0$，且 $|k_1|\le |k|\le N$，从而
$$|\widehat{u_\alpha-u_\beta}(k)|\le \frac{|\alpha-\beta|N}{2\pi\delta^2}|\widehat F(k)|.$$
因此对任意 $r\in\mathbb R$，
$$\|u_\alpha-u_\beta\|_{H^r}^2=\sum_{0<|k|\le N}\langle k\rangle^{2r}|\widehat{u_\alpha-u_\beta}(k)|^2\le \left(\frac{|\alpha-\beta|N}{2\pi\delta^2}\right)^2\sum_{0<|k|\le N}\langle k\rangle^{2r}|\widehat F(k)|^2=\left(\frac{|\alpha-\beta|N}{2\pi\delta^2}\right)^2\|F\|_{H^r}^2.$$
两边开平方即得
$$\|u_\alpha-u_\beta\|_{H^r}\le |\alpha-\beta|N(2\pi\delta^2)^{-1}\|F\|_{H^r}.$$
（注：亦可写成预解式恒等式 $u_\alpha-u_\beta=(\beta-\alpha)N_\alpha^{-1}\partial_1 N_\beta^{-1}F$ 并两次援引 S1 的界 $\|N_\alpha^{-1}\|_{H^r\to H^r},\|N_\beta^{-1}\|_{H^r\to H^r}\le (2\pi\delta)^{-1}$ 与 $\|\partial_1\|_{H^r(H_N)\to H^r(H_N)}\le 2\pi N$，所得常数相同。）

---

## S4 整体对象与全部恢复目标

先验证 $N_\alpha(C^\infty_0(\mathbb T^2))\subset C^\infty_0(\mathbb T^2)$：对 $u\in C^\infty_0(\mathbb T^2)$，显然 $N_\alpha u\in C^\infty(\mathbb T^2;\mathbb C)$，且 $\int_{\mathbb T^2}N_\alpha u=\widehat{N_\alpha u}(0)=2\pi i(\alpha\cdot 0+0)\widehat u(0)=0$。

### 1. 可逆性的完全刻画

**定理 4.1（可逆性刻画）**  
设 $\alpha\in\mathbb R\setminus\mathbb Q$。
1. **唯一性总成立**：对每个 $\alpha\in\mathbb R\setminus\mathbb Q$，$N_\alpha:C^\infty_0(\mathbb T^2)\to C^\infty_0(\mathbb T^2)$ 是单射（若存在解，必唯一）。
2. **双射（可逆）充要条件**：每个 $F\in C^\infty_0(\mathbb T^2)$ 都存在唯一的光滑零均值解 $N_\alpha u=F$，**当且仅当 $\alpha$ 是 Diophantine 数**（即非 Liouville 数），也就是：存在常数 $c>0$ 和 $s\ge 0$ 使得
   $$|\alpha k_1+k_2|\ge c\langle k\rangle^{-s}\qquad\text{对所有 }k=(k_1,k_2)\in\mathbb Z^2\setminus\{0\}. \tag{D}$$
   这等价于存在 $c'>0$ 与 $\tau\ge 2$，使 $|\alpha-p/q|\ge c'q^{-\tau}$ 对所有 $q\in\mathbb Z_{\ge 1},\,p\in\mathbb Z$ 成立。

（注：若考虑有理数 $\alpha=p/q$（$q\ge 1$），则 $e^{2\pi i(qy_1-py_2)}\in C^\infty_0(\mathbb T^2)\setminus\{0\}$ 满足 $N_\alpha u=0$，既不单射也不满射。）

**证明：**  
- **单射性**：若 $u\in C^\infty_0(\mathbb T^2)$ 且 $N_\alpha u=0$，则对所有 $k\in\mathbb Z^2$ 有 $2\pi i(\alpha k_1+k_2)\widehat u(k)=0$。因 $\alpha\notin\mathbb Q$，对 $k\neq 0$ 有 $\alpha k_1+k_2\neq 0$，故 $\widehat u(k)=0$；又 $\widehat u(0)=\int_{\mathbb T^2}u=0$。由光滑函数等于其 Fourier 级数，得 $u\equiv 0$。
- **两种 Diophantine 条件及非 Liouville 的等价性**：  
  - 若 $(D)$ 成立，对 $q\in\mathbb Z_{\ge 1},\,p\in\mathbb Z$ 令 $k=(q,-p)\neq 0$。若 $|p|>(|\alpha|+1)q$，则 $|\alpha q-p|\ge |p|-|\alpha|q>q\ge q^{-s}$；若 $|p|\le(|\alpha|+1)q$，则 $\langle k\rangle\le (2+(|\alpha|+1)^2)^{1/2}q$，故 $|\alpha q-p|\ge c(2+(|\alpha|+1)^2)^{-s/2}q^{-s}$。无论何种情况均有 $|\alpha-p/q|\ge c'q^{-(s+1)}$。  
  - 反之若 $|\alpha-p/q|\ge c'q^{-\tau}$ 对所有 $q\ge 1,p\in\mathbb Z$（取 $s=\max(\tau-1,0)\ge 0$），则 $k_1=0,k_2\neq 0$ 时 $|\alpha k_1+k_2|=|k_2|\ge 1\ge\langle k\rangle^{-s}$；$k_1\neq 0$ 时记 $q=|k_1|\ge 1,\,p=-\operatorname{sgn}(k_1)k_2$，有 $|\alpha k_1+k_2|=q|\alpha-p/q|\ge c'q^{1-\tau}\ge c'|k_1|^{-s}\ge c'\langle k\rangle^{-s}$。  
  - 此外，非 Liouville（即存在 $n\in\mathbb N$ 使对所有 $q\ge 2,p\in\mathbb Z$ 有 $|\alpha-p/q|\ge q^{-n}$）与上述条件显然等价（$q=1$ 时 $\inf_p|\alpha-p|=\operatorname{dist}(\alpha,\mathbb Z)>0$）。
- **充分性（Diophantine $\implies$ 可逆）**：  
  若 $(D)$ 成立，则 S2 的全部条件（$|\alpha k_1+k_2|\ge c\langle k\rangle^{-s}$ 对所有 $k\neq 0$，$c>0,\,s\ge 0$）满足。由 S2 知对每个 $F\in C^\infty_0(\mathbb T^2)$ 均存在 $u\in C^\infty_0(\mathbb T^2)$ 满足 $N_\alpha u=F$；结合已证单射性，解唯一。
- **必要性（可逆 $\implies$ Diophantine）**：  
  假设 $(D)$ 对任何 $c>0,s\ge 0$ 均不成立。对每个正整数 $n\ge 1$，集合 $\{k\in\mathbb Z^2\setminus\{0\}:|\alpha k_1+k_2|<\langle k\rangle^{-n}\}$ 必无限（否则若它全落在某个闭球 $|k|\le R$ 内，因 $\alpha\notin\mathbb Q$ 可取 $\delta=\min_{0<|k|\le R}|\alpha k_1+k_2|>0$，则对全部 $k\neq 0$ 都有 $|\alpha k_1+k_2|\ge\min(1,\delta)\langle k\rangle^{-n}$，与假设矛盾）。
  于是可归纳选取频率序列 $\{k^{(n)}\}_{n=1}^\infty\subset\mathbb Z^2\setminus\{0\}$，满足对每个 $n\ge 1$：
  $$|k^{(n)}|>\max\bigl(n,|k^{(n-1)}|\bigr)\quad(\text{记 }|k^{(0)}|:=0),\qquad |\alpha k_1^{(n)}+k_2^{(n)}|<\langle k^{(n)}\rangle^{-n}.$$
  显然所有 $k^{(n)}$ 两两互异且均非零。定义
  $$F(y)=\sum_{n=1}^\infty \langle k^{(n)}\rangle^{-n/2}e^{2\pi i k^{(n)}\cdot y}.$$
  对任意 $a,b\in\mathbb N_0$，记 $M=a+b$。当 $n\ge 2M+4$ 时，
  $$(2\pi|k_1^{(n)}|)^a(2\pi|k_2^{(n)}|)^b\langle k^{(n)}\rangle^{-n/2}\le (2\pi)^M\langle k^{(n)}\rangle^{M-n/2}\le (2\pi)^M\langle k^{(n)}\rangle^{-2}\le (2\pi)^M n^{-2},$$
  故 $F$ 的级数及逐项任意阶偏导数均在 $\mathbb T^2$ 上绝对一致收敛。因此 $F\in C^\infty(\mathbb T^2;\mathbb C)$，且 $\int_{\mathbb T^2}F=0$，即 $F\in C^\infty_0(\mathbb T^2)$，同时 $\widehat F(k^{(n)})=\langle k^{(n)}\rangle^{-n/2}$。  
  若存在 $u\in C^\infty_0(\mathbb T^2)$ 满足 $N_\alpha u=F$，两边取第 $k^{(n)}$ 个 Fourier 系数得
  $$2\pi i(\alpha k_1^{(n)}+k_2^{(n)})\widehat u(k^{(n)})=\widehat F(k^{(n)})=\langle k^{(n)}\rangle^{-n/2},$$
  于是
  $$|\widehat u(k^{(n)})|=\frac{\langle k^{(n)}\rangle^{-n/2}}{2\pi|\alpha k_1^{(n)}+k_2^{(n)}|}>\frac{\langle k^{(n)}\rangle^{n/2}}{2\pi}>\frac{n^{n/2}}{2\pi}\xrightarrow{n\to\infty}+\infty.$$
  但对 $u\in C^\infty_0(\mathbb T^2)$ 必有 $|\widehat u(k)|\le\|u\|_{L^\infty(\mathbb T^2)}<\infty$，矛盾！故此时 $N_\alpha$ 不满射。$\blacksquare$

---

### 2. 全部允许的正则性损失 $s\ge 0$

**定理 4.2（Sobolev 损失分类）**  
设 $\alpha\in\mathbb R\setminus\mathbb Q$，记 $\mathcal S(\alpha)$ 为所有使得“对每个 $r\in\mathbb R$ 存在与 $u$ 无关的有限常数 $C_{\alpha,r,s}$ 满足 $\|u\|_{H^r}\le C_{\alpha,r,s}\|N_\alpha u\|_{H^{r+s}}$（$\forall u\in C^\infty_0(\mathbb T^2)$）”的 $s\ge 0$ 之集合。则：
1. **精确刻画**：
   $$\mathcal S(\alpha)=\left\{s\ge 0:\inf_{k\in\mathbb Z^2\setminus\{0\}}\langle k\rangle^s|\alpha k_1+k_2|>0\right\}=\left\{s\ge 0:\inf_{q\in\mathbb Z_{\ge 1},\,p\in\mathbb Z}q^s|\alpha q-p|>0\right\}.$$
2. **结构与区间形式**：恒有 $\mathcal S(\alpha)\subseteq [1,\infty)$。具体分为两类：
   - 若 $\alpha$ 是 Liouville 数，则 $\mathcal S(\alpha)=\emptyset$；
   - 若 $\alpha$ 是 Diophantine 数，记 $s_0(\alpha):=\inf\mathcal S(\alpha)\in[1,\infty)$（即 $\mu(\alpha)-1$，其中 $\mu(\alpha)=\sup\{\tau\ge 2:0<|\alpha-p/q|<q^{-\tau}\text{ 有无穷多解}\}$ 为无理数指数），则 $\mathcal S(\alpha)$ 为向上半直线：
     $$\mathcal S(\alpha)=\begin{cases} [s_0(\alpha),\infty), & \text{若 }\inf_{k\neq 0}\langle k\rangle^{s_0(\alpha)}|\alpha k_1+k_2|>0,\\ (s_0(\alpha),\infty), & \text{若 }\inf_{k\neq 0}\langle k\rangle^{s_0(\alpha)}|\alpha k_1+k_2|=0. \end{cases}$$

**证明：**  
- **必要与充分条件**：  
  若 $s\in\mathcal S(\alpha)$，取定 $r=0$ 并以 $u_k(y)=e^{2\pi i k\cdot y}\in C^\infty_0(\mathbb T^2)$（$k\in\mathbb Z^2\setminus\{0\}$）代入，得
  $$\langle k\rangle^0=1\le C_{\alpha,0,s}\cdot 2\pi\langle k\rangle^s|\alpha k_1+k_2|\implies \inf_{k\neq 0}\langle k\rangle^s|\alpha k_1+k_2|\ge\frac{1}{2\pi C_{\alpha,0,s}}>0.$$
  反之，若 $c_s:=\inf_{k\neq 0}\langle k\rangle^s|\alpha k_1+k_2|>0$，则对**所有** $r\in\mathbb R$ 及 $u\in C^\infty_0(\mathbb T^2)$，
  $$\|u\|_{H^r}^2=\sum_{k\neq 0}\frac{\langle k\rangle^{-2s}}{4\pi^2|\alpha k_1+k_2|^2}\langle k\rangle^{2(r+s)}|\widehat{N_\alpha u}(k)|^2\le \frac{1}{4\pi^2c_s^2}\|N_\alpha u\|_{H^{r+s}}^2,$$
  即 $s\in\mathcal S(\alpha)$（且常数可取 $(2\pi c_s)^{-1}$，与 $r$ 无关）。与 $q^s|\alpha q-p|$ 下确界的等价性由定理 4.1 证明中对固定 $s\ge 0$ 的双边比较直接给出。
- **$\mathcal S(\alpha)\subseteq [1,\infty)$（Dirichlet 逼近定理）**：  
  对任意整数 $Q\ge 1$，考虑 $Q+1$ 个小数部分 $\{j\alpha\}\in[0,1)$（$j=0,1,\dots,Q$）。将 $[0,1)$ 等分为 $Q$ 个子区间 $[(\ell-1)/Q,\ell/Q)$，由抽屉原理存在 $0\le j_1<j_2\le Q$ 使 $\{j_1\alpha\},\{j_2\alpha\}$ 落入同一子区间。令 $q=j_2-j_1\in\{1,\dots,Q\}$、$p=\lfloor j_2\alpha\rfloor-\lfloor j_1\alpha\rfloor\in\mathbb Z$，因 $\alpha\notin\mathbb Q$ 有
  $$0<|q\alpha-p|=|\{j_2\alpha\}-\{j_1\alpha\}|<\frac{1}{Q}\le\frac{1}{q}.$$
  由于对任一有限组 $(q_i,p_i)$ 都有 $\min_i|q_i\alpha-p_i|>0$，令 $Q\to\infty$ 可得无穷多对整数 $(q,p)$（$q\ge 1$）满足 $0<|q\alpha-p|<1/q$；又每个 $q$ 至多对应两个满足 $|q\alpha-p|<1$ 的 $p$，故必有子列使 $q\to\infty$。当 $0\le s<1$ 时，沿着该子列 $q^s|q\alpha-p|<q^{s-1}\to 0$，故 $s\notin\mathcal S(\alpha)$。
- **区间结构**：  
  因 $k\neq 0\implies\langle k\rangle>1$，若 $s\in\mathcal S(\alpha)$ 且 $s'>s$，则 $\langle k\rangle^{s'}|\alpha k_1+k_2|\ge\langle k\rangle^s|\alpha k_1+k_2|$，故 $s'\in\mathcal S(\alpha)$（向上封闭）。结合定理 4.1 知 $\mathcal S(\alpha)\neq\emptyset\iff\alpha$ 非 Liouville；若非空，则必为 $[s_0(\alpha),\infty)$ 或 $(s_0(\alpha),\infty)$，取决于下确界在 $s_0(\alpha)$ 处是否严格大于 $0$。$\blacksquare$

---

### 3. $\alpha_*=\sqrt{2}-1$ 时的最小允许损失与是否取到

**结论**：当 $\alpha_*=\sqrt{2}-1$ 时，$\mathcal S(\alpha_*)=[1,\infty)$，**最小允许损失为 $s=1$，且该最小值可以取到**。

**证明：**  
由定理 4.2 已证 $\mathcal S(\alpha_*)\subseteq [1,\infty)$，故只需证 $1\in\mathcal S(\alpha_*)$，即存在 $c>0$ 使 $|\alpha_*k_1+k_2|\ge c\langle k\rangle^{-1}$ 对所有 $k\in\mathbb Z^2\setminus\{0\}$ 成立：
- 若 $k_1=0$，则 $|k_2|\ge 1$，有 $|\alpha_* k_1+k_2|=|k_2|\ge 1>\langle k\rangle^{-1}$。
- 若 $k_1\neq 0$，注意 $\alpha_*=\sqrt{2}-1$ 的代数共轭为 $\overline\alpha_*=-\sqrt{2}-1$，满足 $\alpha_*+\overline\alpha_*=-2$，$\alpha_*\overline\alpha_*=-1$。考虑整数值二次型
  $$P(k_1,k_2):=(\alpha_* k_1+k_2)(\overline\alpha_* k_1+k_2)=-k_1^2-2k_1k_2+k_2^2=(k_2-k_1)^2-2k_1^2\in\mathbb Z.$$
  因 $k_1\neq 0$ 且 $\sqrt{2}\notin\mathbb Q$，不可能有 $(k_2-k_1)^2=2k_1^2$，故 $P(k_1,k_2)\in\mathbb Z\setminus\{0\}$，从而 $|P(k_1,k_2)|\ge 1$。再由 Cauchy–Schwarz 不等式，
  $$|\overline\alpha_* k_1+k_2|\le\sqrt{\overline\alpha_*^2+1}\,|k|=\sqrt{(-\sqrt{2}-1)^2+1}\,|k|=\sqrt{4+2\sqrt{2}}\,|k|<\sqrt{4+2\sqrt{2}}\,\langle k\rangle.$$
  因此
  $$|\alpha_* k_1+k_2|=\frac{|P(k_1,k_2)|}{|\overline\alpha_* k_1+k_2|}\ge\frac{1}{\sqrt{4+2\sqrt{2}}}\langle k\rangle^{-1}.$$
综合两类情形，对一切 $k\in\mathbb Z^2\setminus\{0\}$ 都有
$$|\alpha_* k_1+k_2|\ge c_*\langle k\rangle^{-1},\qquad c_*:=(4+2\sqrt{2})^{-1/2}>0.$$
由定理 4.2 知 $1\in\mathcal S(\alpha_*)$（且对任意 $r\in\mathbb R$ 可取 $C_{\alpha_*,r,1}=(2\pi c_*)^{-1}=\frac{\sqrt{4+2\sqrt{2}}}{2\pi}$）。故最小允许损失为 $s=1$，并且取到。$\blacksquare$

---

### 4. $C^m$ 范数估计 $\|N_{\alpha_*}^{-1}F\|_{C^m}\le C_m\|F\|_{C^{m+4}}$ 的判定

**结论：成立。** 对每个 $m\in\mathbb N_0$，存在与 $F$ 无关的有限常数 $C_m$，使得对所有 $F\in C^\infty_0(\mathbb T^2)$，唯一零均值解 $u=N_{\alpha_*}^{-1}F$ 满足
$$\|N_{\alpha_*}^{-1}F\|_{C^m}\le C_m\|F\|_{C^{m+4}}$$
（事实上甚至对 $\|F\|_{C^{m+3}}$ 也成立）。

**证明：**  
由前两项知 $N_{\alpha_*}:C^\infty_0(\mathbb T^2)\to C^\infty_0(\mathbb T^2)$ 可逆，对任意 $F\in C^\infty_0(\mathbb T^2)$，设 $u=N_{\alpha_*}^{-1}F\in C^\infty_0(\mathbb T^2)$。

1. **Sobolev 嵌入 $H^{m+2}\hookrightarrow C^m$**：  
   对任意 $a,b\in\mathbb N_0$ 且 $a+b\le m$，以及任意 $y\in\mathbb T^2$，因 $u$ 光滑，Fourier 级数可逐项求导并一致收敛，故
   $$|\partial_{y_1}^a\partial_{y_2}^b u(y)|\le\sum_{k\neq 0}(2\pi)^{a+b}|k_1|^a|k_2|^b|\widehat u(k)|\le (2\pi)^m\sum_{k\neq 0}\langle k\rangle^m|\widehat u(k)|.$$
   由 Cauchy–Schwarz 不等式，
   $$\sum_{k\neq 0}\langle k\rangle^m|\widehat u(k)|=\sum_{k\neq 0}\langle k\rangle^{-2}\cdot\langle k\rangle^{m+2}|\widehat u(k)|\le K\|u\|_{H^{m+2}},\qquad K:=\left(\sum_{k\neq 0}\langle k\rangle^{-4}\right)^{1/2}<\infty$$
   （$K<\infty$ 已在预备事实中证明）。对 $a+b\le m$ 和 $y\in\mathbb T^2$ 取上确界即得
   $$\|u\|_{C^m}\le (2\pi)^m K\|u\|_{H^{m+2}}.$$
2. **使用 $s=1$ 的正则性估计**：  
   由第 3 项结果（对 $r=m+2,\,s=1$ 适用），
   $$\|u\|_{H^{m+2}}\le \frac{\sqrt{4+2\sqrt{2}}}{2\pi}\|N_{\alpha_*}u\|_{H^{m+3}}=\frac{\sqrt{4+2\sqrt{2}}}{2\pi}\|F\|_{H^{m+3}}.$$
3. **用 $\|F\|_{C^{m+3}}$（进而 $\|F\|_{C^{m+4}}$）控制 $\|F\|_{H^{m+3}}$**：  
   由多项式定理展开 $\langle k\rangle^{2(m+3)}=(1+k_1^2+k_2^2)^{m+3}$，并应用 Parseval 等式与 Haar 测度归一化（$\|g\|_{L^2(\mathbb T^2)}\le \|g\|_{L^\infty(\mathbb T^2)}$）：
   $$\begin{aligned}
   \|F\|_{H^{m+3}}^2
   &=\sum_{\substack{j_0,j_1,j_2\ge 0\\ j_0+j_1+j_2=m+3}}\frac{(m+3)!}{j_0!j_1!j_2!}\sum_{k\in\mathbb Z^2}k_1^{2j_1}k_2^{2j_2}|\widehat F(k)|^2\\
   &=\sum_{j_0+j_1+j_2=m+3}\frac{(m+3)!}{j_0!j_1!j_2!}(2\pi)^{-2(j_1+j_2)}\|\partial_{y_1}^{j_1}\partial_{y_2}^{j_2}F\|_{L^2(\mathbb T^2)}^2\\
   &\le \left(\sum_{j_0+j_1+j_2=m+3}\frac{(m+3)!}{j_0!j_1!j_2!}(2\pi)^{-2(j_1+j_2)}\right)\|F\|_{C^{m+3}}^2
   =\left(1+\frac{2}{4\pi^2}\right)^{m+3}\|F\|_{C^{m+3}}^2.
   \end{aligned}$$
   又显然 $\|F\|_{C^{m+3}}\le \|F\|_{C^{m+4}}$。

将三步合并，令
$$C_m:=(2\pi)^{m-1}K\sqrt{4+2\sqrt{2}}\left(1+\frac{1}{2\pi^2}\right)^{(m+3)/2}<\infty,$$
即得 $\|N_{\alpha_*}^{-1}F\|_{C^m}\le C_m\|F\|_{C^{m+4}}$ 对一切 $F\in C^\infty_0(\mathbb T^2)$ 成立。$\blacksquare$

---

## S5 邻近方向的一致估计

**结论：不存在**这样的开区间 $J\ni\alpha_*$、有限 $s\ge 0$ 与 $C<\infty$。

**证明（反证法）：**  
假设存在包含 $\alpha_*$ 的开区间 $J$、有限 $s\ge 0$ 与常数 $C<\infty$，使得对所有无理数 $\alpha\in J\setminus\mathbb Q$ 和所有 $u\in C^\infty_0(\mathbb T^2)$ 都有
$$\|u\|_{L^2}\le C\|N_\alpha u\|_{H^s}.$$
因 $J$ 是非空开区间且 $\mathbb Q$ 在 $\mathbb R$ 中稠密，可选取有理数 $p/q\in J$（其中 $p\in\mathbb Z,\,q\in\mathbb Z_{\ge 1}$）。取频率 $k=(q,-p)\in\mathbb Z^2\setminus\{0\}$ 及光滑零均值函数
$$u(y)=e^{2\pi i(qy_1-py_2)}\in C^\infty_0(\mathbb T^2).$$
则 $\|u\|_{L^2}=\left(\int_{\mathbb T^2}1\,dy\right)^{1/2}=1$，且 $N_\alpha u(y)=2\pi i(\alpha q-p)e^{2\pi i k\cdot y}$，故
$$\|N_\alpha u\|_{H^s}=2\pi\langle k\rangle^s|\alpha q-p|=2\pi q\langle k\rangle^s\left|\alpha-\frac{p}{q}\right|.$$
现在选取足够大的正整数 $m$，同时满足
$$\alpha:=\frac{p}{q}+\frac{\sqrt{2}}{m}\in J\qquad\text{且}\qquad \frac{2\pi\sqrt{2}\,C q\langle k\rangle^s}{m}<1$$
（这可实现，因 $p/q$ 是开区间 $J$ 的内点，且 $s,C,q,\langle k\rangle$ 均与 $m$ 无关）。由 $\sqrt{2}\notin\mathbb Q$ 与 $p/q\in\mathbb Q$，知 $\alpha\in J\setminus\mathbb Q$ 无理。但对此 $\alpha$ 与上述 $u$，
$$C\|N_\alpha u\|_{H^s}=2\pi C q\langle k\rangle^s\cdot\frac{\sqrt{2}}{m}<1=\|u\|_{L^2},$$
与假设矛盾！故满足条件的 $(J,s,C)$ 不存在。$\blacksquare$

---

## S6 一个具体方向的不可解数据

令 $\alpha=\sum_{n=1}^\infty 10^{-n!}$（因 $n!\ge n$，级数绝对收敛，$0<\alpha<1$）。对每个正整数 $m\ge 1$，记
$$q_m:=10^{m!}\in\mathbb Z_{\ge 1},\qquad p_m:=q_m\sum_{n=1}^m 10^{-n!}=\sum_{n=1}^m 10^{m!-n!}\in\mathbb Z_{\ge 1}.$$
首先估计误差 $\alpha-p_m/q_m$。对所有 $j\ge 0$，$(m+1+j)!-(m+1)!\ge j$（当 $j=0$ 时等号成立；当 $j\ge 1$ 时 $(m+1+j)!\ge 2^j(m+1)!\ge (m+1)!+j$），故
$$0<\alpha-\frac{p_m}{q_m}=\sum_{n=m+1}^\infty 10^{-n!}\le 10^{-(m+1)!}\sum_{j=0}^\infty 10^{-j}=\frac{10}{9}\cdot 10^{-(m+1)!}<2\cdot 10^{-(m+1)!}.$$
乘以 $q_m=10^{m!}$ 得
$$0<\alpha q_m-p_m<2\cdot 10^{m!-(m+1)!}=2\cdot 10^{-m\cdot m!}. \tag{$*$}$$

### 1. 证明 $\alpha$ 无理

反设 $\alpha=a/b\in\mathbb Q$，其中 $a\in\mathbb Z,\,b\in\mathbb Z_{\ge 1}$。对每个 $m\ge 1$，
$$b(\alpha q_m-p_m)=a\cdot 10^{m!}-bp_m\in\mathbb Z.$$
由 $(*)$ 左端知该整数严格大于 $0$，因此必有 $b(\alpha q_m-p_m)\ge 1$。但由 $(*)$ 右端，
$$b(\alpha q_m-p_m)<2b\cdot 10^{-m\cdot m!}.$$
取足够大的 $m$ 使 $10^{m\cdot m!}>2b$，即得 $1\le b(\alpha q_m-p_m)<1$，矛盾。因此 $\alpha\in\mathbb R\setminus\mathbb Q$ 无理。

### 2. 构造同一个光滑零均值 $F$ 使 $N_\alpha u=F$ 无光滑零均值解

记 $k^{(m)}:=(q_m,-p_m)\in\mathbb Z^2\setminus\{0\}$（$m\ge 1$）。因 $q_m=10^{m!}$ 严格递增（$q_1<q_2<\dots$）且 $q_m\ge 10$，故 $\{k^{(m)}\}_{m=1}^\infty$ 两两互异且均非 $(0,0)$。同时由 $p_m=q_m\sum_{n=1}^m 10^{-n!}<\frac{1}{9}q_m<q_m$，有 $|k^{(m)}|<\sqrt{2}\,q_m=\sqrt{2}\cdot 10^{m!}$。

构造单一函数 $F:\mathbb T^2\to\mathbb C$：
$$F(y):=\sum_{m=1}^\infty 10^{-\frac{1}{2}m\cdot m!}e^{2\pi i k^{(m)}\cdot y}=\sum_{m=1}^\infty 10^{-\frac{1}{2}m\cdot m!}e^{2\pi i(q_my_1-p_my_2)}.$$

- **验证 $F\in C^\infty_0(\mathbb T^2)$**：  
  对任意 $a,b\in\mathbb N_0$，记 $M=a+b$。由 $|q_m|,|p_m|\le 10^{m!}$，第 $m$ 项逐项求 $\partial_{y_1}^a\partial_{y_2}^b$ 后的绝对值上界为
  $$(2\pi q_m)^a(2\pi p_m)^b 10^{-\frac{1}{2}m\cdot m!}\le (2\pi)^M 10^{(M-\frac{m}{2})m!}.$$
  当 $m\ge 2M+2$ 时，有 $M-\frac{m}{2}\le -1$，故上式不超过 $(2\pi)^M 10^{-m!}$。因 $\sum_{m=1}^\infty 10^{-m!}<\infty$，$F$ 的级数及全部逐项偏导数级数都在 $\mathbb T^2$ 上绝对一致收敛。因此 $F\in C^\infty(\mathbb T^2;\mathbb C)$。又每个 $k^{(m)}\neq 0$，一致收敛允许积分与求和交换，得
  $$\int_{\mathbb T^2}F(y)\,dy=\sum_{m=1}^\infty 10^{-\frac{1}{2}m\cdot m!}\int_{\mathbb T^2}e^{2\pi i k^{(m)}\cdot y}\,dy=0,$$
  故 $F\in C^\infty_0(\mathbb T^2)$，且因 $\{k^{(m)}\}$ 两两互异，有 $\widehat F(k^{(m)})=10^{-\frac{1}{2}m\cdot m!}$。

- **证明 $N_\alpha u=F$ 没有光滑零均值解**：  
  假设存在 $u\in C^\infty_0(\mathbb T^2)$ 满足 $N_\alpha u=F$。两边取第 $k^{(m)}$ 个 Fourier 系数，得
  $$2\pi i(\alpha q_m-p_m)\widehat u(k^{(m)})=\widehat{N_\alpha u}(k^{(m)})=\widehat F(k^{(m)})=10^{-\frac{1}{2}m\cdot m!}.$$
  结合 $(*)$ 中的上界 $0<|\alpha q_m-p_m|<2\cdot 10^{-m\cdot m!}$，推出对所有 $m\ge 1$ 有
  $$|\widehat u(k^{(m)})|=\frac{10^{-\frac{1}{2}m\cdot m!}}{2\pi|\alpha q_m-p_m|}>\frac{10^{-\frac{1}{2}m\cdot m!}}{4\pi\cdot 10^{-m\cdot m!}}=\frac{10^{\frac{1}{2}m\cdot m!}}{4\pi}\xrightarrow{m\to\infty}+\infty.$$
  然而任何光滑函数（乃至 $L^1$ 函数）的 Fourier 系数均有界：$|\widehat u(k)|\le\|u\|_{L^\infty(\mathbb T^2)}<\infty$，矛盾！  
  因此，对这同一个 $F\in C^\infty_0(\mathbb T^2)$，方程 $N_\alpha u=F$ 不存在光滑零均值解。$\blacksquare$
