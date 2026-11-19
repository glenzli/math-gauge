以下统一采用题目在 S4 中给出的环面与 Fourier 分析记号：$\mathbb{T}^2 = \mathbb{R}^2/\mathbb{Z}^2$ 配备归一化 Haar 测度 $dy$（$\int_{\mathbb{T}^2} 1\,dy = 1$），频率 $k=(k_1,k_2)\in\mathbb{Z}^2$ 的欧氏范数为 $|k|=(k_1^2+k_2^2)^{1/2}$，日本括号为 $\langle k\rangle=(1+|k|^2)^{1/2}$，Fourier 系数为 $\widehat{u}(k)=\int_{\mathbb{T}^2}u(y)e^{-2\pi i k\cdot y}\,dy$，$H^r$ 范数为 $\|u\|_{H^r}=\bigl(\sum_{k\in\mathbb{Z}^2}\langle k\rangle^{2r}|\widehat{u}(k)|^2\bigr)^{1/2}$，方向导数算子为 $N_\alpha=\alpha\partial_{y_1}+\partial_{y_2}$。

---

## S1 有限频带上的逆

### 1. 逆算子的构造
记基函数 $e_k(y) := e^{2\pi i(k_1 y_1 + k_2 y_2)}$（$k\in\mathbb{Z}^2$）。因为 $N\ge 1$，指标集
$$\Lambda_N := \{k\in\mathbb{Z}^2 : 0 < |k| \le N\}$$
有限且非空（例如 $(1,0)\in\Lambda_N$），空间 $H_N = \operatorname{span}_{\mathbb{C}}\{e_k : k\in\Lambda_N\}$。每个 $F\in H_N$ 唯一表为
$$F(y) = \sum_{k\in\Lambda_N} \widehat{F}(k) e^{2\pi i k\cdot y}.$$
直接求导得 $N_\alpha e_k = 2\pi i(\alpha k_1 + k_2)e_k$，故 $N_\alpha(H_N)\subset H_N$。

由于 $\alpha\in\mathbb{R}\setminus\mathbb{Q}$，对任意 $k=(k_1,k_2)\in\mathbb{Z}^2\setminus\{0\}$：
- 若 $k_1=0$，则 $k\neq 0 \implies k_2\neq 0$，从而 $\alpha k_1+k_2 = k_2 \neq 0$；
- 若 $k_1\neq 0$，假设 $\alpha k_1+k_2=0$，则 $\alpha = -k_2/k_1\in\mathbb{Q}$，与 $\alpha$ 无理矛盾。

因此对所有 $k\in\Lambda_N$ 均有 $2\pi i(\alpha k_1+k_2)\neq 0$。定义线性算子 $T_{\alpha,N}:H_N\to H_N$ 为
$$T_{\alpha,N}F(y) := \sum_{0<|k|\le N} \frac{\widehat{F}(k)}{2\pi i(\alpha k_1 + k_2)} e^{2\pi i k\cdot y} \qquad (F\in H_N).$$
对任意 $F\in H_N$，逐项求导得
$$N_\alpha(T_{\alpha,N}F)(y) = \sum_{0<|k|\le N} 2\pi i(\alpha k_1+k_2)\frac{\widehat{F}(k)}{2\pi i(\alpha k_1+k_2)}e^{2\pi i k\cdot y} = F(y),$$
且对任意 $u\in H_N$ 有 $\widehat{N_\alpha u}(k)=2\pi i(\alpha k_1+k_2)\widehat{u}(k)$，故 $T_{\alpha,N}(N_\alpha u)=u$。因此 $T_{\alpha,N} = (N_\alpha|_{H_N})^{-1}$ 即为 $N_\alpha$ 在 $H_N$ 上的唯一双边逆。

### 2. $H^r \to H^r$ 逆范数精确式
对任意 $r\in\mathbb{R}$，逆算子的精确算子范数为（与 $r$ 无关）：
$$\left\|(N_\alpha|_{H_N})^{-1}\right\|_{H^r\to H^r} = \max_{\substack{k\in\mathbb{Z}^2\\ 0<|k|\le N}} \frac{1}{2\pi|\alpha k_1 + k_2|} = \left(2\pi \min_{\substack{k\in\mathbb{Z}^2\\ 0<|k|\le N}} |\alpha k_1 + k_2|\right)^{-1}.$$

**证明**：因为 $\Lambda_N$ 有限非空且 $|\alpha k_1+k_2|>0$（$k\in\Lambda_N$），最小值 $\delta_N := \min_{k\in\Lambda_N}|\alpha k_1+k_2| > 0$ 在某个 $k_*\in\Lambda_N$ 处取到。
- **上界**：对任意 $F\in H_N$，由 $\{e_k\}_{k\in\mathbb{Z}^2}$ 在 $L^2(\mathbb{T}^2)$ 中的正交归一性，$(N_\alpha|_{H_N})^{-1}F$ 的非零 Fourier 系数仅在 $\Lambda_N$ 上，故
  $$\left\|(N_\alpha|_{H_N})^{-1}F\right\|_{H^r}^2 = \sum_{k\in\Lambda_N}\langle k\rangle^{2r}\frac{|\widehat{F}(k)|^2}{4\pi^2|\alpha k_1+k_2|^2} \le \frac{1}{4\pi^2\delta_N^2}\sum_{k\in\Lambda_N}\langle k\rangle^{2r}|\widehat{F}(k)|^2 = \left(\frac{1}{2\pi\delta_N}\|F\|_{H^r}\right)^2.$$
- **可达性（下界）**：取 $F_*(y) := e^{2\pi i k_*\cdot y}\in H_N$。由于 $\langle k_*\rangle^r > 0$，$\|F_*\|_{H^r} = \langle k_*\rangle^r \neq 0$，而
  $$\left\|(N_\alpha|_{H_N})^{-1}F_*\right\|_{H^r} = \frac{\langle k_*\rangle^r}{2\pi|\alpha k_{*,1}+k_{*,2}|} = \frac{1}{2\pi\delta_N}\|F_*\|_{H^r}.$$
结合上下界即得精确范数公式。$\blacksquare$

---

## S2 有算术界的截断误差

### 1. 前提核验与光滑零均值解 $u$ 的构造
首先验证 $\alpha$ 无理：若 $\alpha = p/q\in\mathbb{Q}$（$p\in\mathbb{Z}, q\in\mathbb{N}$），取 $k=(q,-p)\neq 0$ 得 $|\alpha k_1+k_2|=0 < c\langle k\rangle^{-s}$，与算术界矛盾。故 $\alpha\in\mathbb{R}\setminus\mathbb{Q}$，S1 的结论对频带截断
$$F_N(y) := \sum_{0<|k|\le N}\widehat{F}(k)e^{2\pi i k\cdot y}\in H_N$$
完全适用，给出 $u_N(y) = \sum_{0<|k|\le N}\frac{\widehat{F}(k)}{2\pi i(\alpha k_1+k_2)}e^{2\pi i k\cdot y}\in H_N$。

对光滑零均值函数 $F\in C^\infty_0(\mathbb{T}^2)$（满足 $\widehat{F}(0)=\int_{\mathbb{T}^2}F=0$），定义级数
$$u(y) := \sum_{k\in\mathbb{Z}^2\setminus\{0\}} c_k e^{2\pi i k\cdot y}, \qquad c_k := \frac{\widehat{F}(k)}{2\pi i(\alpha k_1+k_2)} \quad (k\neq 0).$$

**证明 $u\in C^\infty_0(\mathbb{T}^2)$ 且 $N_\alpha u = F$**：
1. **$F$ 的任意阶 $H^M$ 范数有限**：对任意整数 $K\ge 0$，由多项式展开
   $$\langle k\rangle^{2K} = (1+k_1^2+k_2^2)^K = \sum_{\substack{j_0,j_1,j_2\ge 0\\ j_0+j_1+j_2=K}}\frac{K!}{j_0!j_1!j_2!}k_1^{2j_1}k_2^{2j_2}.$$
   因为 $F\in C^\infty(\mathbb{T}^2)$ 且 $\mathbb{T}^2$ 紧致，分部积分给出 $\widehat{\partial_{y_1}^{j_1}\partial_{y_2}^{j_2}F}(k)=(2\pi i k_1)^{j_1}(2\pi i k_2)^{j_2}\widehat{F}(k)$；对连续（从而平方可积）函数 $\partial_{y_1}^{j_1}\partial_{y_2}^{j_2}F\in L^2(\mathbb{T}^2)$ 应用正交归一系 $\{e_k\}_{k\in\mathbb{Z}^2}$ 的 Bessel 不等式得
   $$\sum_{k\in\mathbb{Z}^2}k_1^{2j_1}k_2^{2j_2}|\widehat{F}(k)|^2 \le (2\pi)^{-2(j_1+j_2)}\|\partial_{y_1}^{j_1}\partial_{y_2}^{j_2}F\|_{L^2}^2 < \infty.$$
   故对任意 $K\in\mathbb{N}_0$ 有 $\|F\|_{H^K}<\infty$；对一般实数 $M\in\mathbb{R}$，取整数 $K\ge \max(0,M)$，由 $\langle k\rangle^{2M}\le\langle k\rangle^{2K}$ 得 $\|F\|_{H^M}\le\|F\|_{H^K}<\infty$。
2. **级数及其各阶偏导的一致收敛性**：注意到对所有 $(k_1,k_2)\in\mathbb{Z}^2$ 有 $(1+k_1^2+k_2^2)^2 \ge (1+k_1^2)(1+k_2^2)$，故
   $$S_4 := \sum_{k\in\mathbb{Z}^2\setminus\{0\}}\langle k\rangle^{-4} \le \left(\sum_{n\in\mathbb{Z}}\frac{1}{1+n^2}\right)^2 < \infty.$$
   对任意多重指标 $\beta=(a,b)\in\mathbb{N}_0^2$（记 $m=a+b$），利用 $|k_1|^a|k_2|^b\le\langle k\rangle^m$、算术界 $|\alpha k_1+k_2|\ge c\langle k\rangle^{-s}$ 以及 Cauchy–Schwarz 不等式：
   $$\begin{aligned}
   \sum_{k\neq 0}\left|(2\pi i k_1)^a(2\pi i k_2)^b c_k e^{2\pi i k\cdot y}\right|
   &\le \frac{(2\pi)^m}{2\pi c}\sum_{k\neq 0}\langle k\rangle^{-2}\cdot\langle k\rangle^{m+s+2}|\widehat{F}(k)| \\
   &\le \frac{(2\pi)^{m-1}}{c}S_4^{1/2}\|F\|_{H^{m+s+2}} < \infty.
   \end{aligned}$$
   由 Weierstrass $M$ 判别法，$u$ 的定义级数及任意阶形式偏导级数在 $\mathbb{T}^2$ 上绝对且一致收敛。根据一致收敛函数项级数的逐项求导与逐项积分定理，$u\in C^\infty(\mathbb{T}^2)$，其 Fourier 系数满足 $\widehat{u}(0)=0$（即 $\int_{\mathbb{T}^2}u=0$，故 $u\in C^\infty_0(\mathbb{T}^2)$）及 $\widehat{u}(k)=c_k$（$k\neq 0$），且可逐项求导得
   $$N_\alpha u(y) = \sum_{k\neq 0}2\pi i(\alpha k_1+k_2)c_k e^{2\pi i k\cdot y} = \sum_{k\neq 0}\widehat{F}(k)e^{2\pi i k\cdot y}.$$
   记右端函数为 $G\in C^\infty(\mathbb{T}^2)$，则对全部 $k\in\mathbb{Z}^2$ 有 $\widehat{G}(k)=\widehat{F}(k)$（含 $k=0$ 处 $\widehat{G}(0)=0=\widehat{F}(0)$）。由三角函数系 $\{e_k\}_{k\in\mathbb{Z}^2}$ 在 $L^2(\mathbb{T}^2)$ 中的完备性（Parseval 恒等式）得 $\|F-G\|_{L^2}=0$；再由 $F-G$ 在 $\mathbb{T}^2$ 上连续，得 $N_\alpha u(y)=G(y)=F(y)$ 处处成立。

### 2. 截断误差估计的证明
对任意 $r\in\mathbb{R}$ 及 $q\ge 0$，$u-u_N$ 的 Fourier 系数在 $|k|\le N$ 时为 $0$，在 $|k|>N$ 时为 $c_k = \frac{\widehat{F}(k)}{2\pi i(\alpha k_1+k_2)}$。当 $|k|>N$ 时，$1+|k|^2 > 1+N^2$；因 $q\ge 0$，单调性给出
$$\langle k\rangle^{-2q} = (1+|k|^2)^{-q} \le (1+N^2)^{-q}.$$
结合算术界 $|\alpha k_1+k_2|\ge c\langle k\rangle^{-s}$ 得
$$\begin{aligned}
\|u-u_N\|_{H^r}^2
&= \sum_{|k|>N}\langle k\rangle^{2r}\frac{|\widehat{F}(k)|^2}{4\pi^2|\alpha k_1+k_2|^2} \\
&\le \frac{1}{4\pi^2 c^2}\sum_{|k|>N}\langle k\rangle^{2(r+s)}|\widehat{F}(k)|^2 \\
&= \frac{1}{4\pi^2 c^2}\sum_{|k|>N}\langle k\rangle^{-2q}\langle k\rangle^{2(r+s+q)}|\widehat{F}(k)|^2 \\
&\le \frac{(1+N^2)^{-q}}{4\pi^2 c^2}\sum_{|k|>N}\langle k\rangle^{2(r+s+q)}|\widehat{F}(k)|^2 \\
&\le \frac{(1+N^2)^{-q}}{4\pi^2 c^2}\|F\|_{H^{r+s+q}}^2.
\end{aligned}$$
两边开平方即得
$$\|u-u_N\|_{H^r} \le (2\pi c)^{-1}(1+N^2)^{-q/2}\|F\|_{H^{r+s+q}}.\qquad\blacksquare$$

---

## S3 固定频带内改变方向

**证明**：因为 $\alpha,\beta$ 均为无理数且 $F\in H_N$，S1 的适用条件对两个方向均成立，对应解 $u_\alpha,u_\beta\in H_N$ 的非零 Fourier 系数仅落在 $0<|k|\le N$ 上，且对每个 $0<|k|\le N$：
$$\widehat{u_\alpha}(k)-\widehat{u_\beta}(k) = \frac{\widehat{F}(k)}{2\pi i}\left(\frac{1}{\alpha k_1+k_2}-\frac{1}{\beta k_1+k_2}\right) = \frac{(\beta-\alpha)k_1}{2\pi i(\alpha k_1+k_2)(\beta k_1+k_2)}\widehat{F}(k).$$
对满足 $0<|k|\le N$ 的整频率 $k=(k_1,k_2)$，有 $|k_1|\le (k_1^2+k_2^2)^{1/2}=|k|\le N$，且由题设小除数下界 $|\alpha k_1+k_2|\ge\delta$、$|\beta k_1+k_2|\ge\delta$（$\delta>0$），得
$$|\widehat{u_\alpha}(k)-\widehat{u_\beta}(k)| \le \frac{|\alpha-\beta|\cdot |k_1|}{2\pi|\alpha k_1+k_2|\cdot|\beta k_1+k_2|}|\widehat{F}(k)| \le \frac{|\alpha-\beta|N}{2\pi\delta^2}|\widehat{F}(k)|.$$
因此对任意 $r\in\mathbb{R}$，
$$\|u_\alpha-u_\beta\|_{H^r}^2 = \sum_{0<|k|\le N}\langle k\rangle^{2r}|\widehat{u_\alpha}(k)-\widehat{u_\beta}(k)|^2 \le \left(\frac{|\alpha-\beta|N}{2\pi\delta^2}\right)^2\sum_{0<|k|\le N}\langle k\rangle^{2r}|\widehat{F}(k)|^2 = \left(\frac{|\alpha-\beta|N}{2\pi\delta^2}\|F\|_{H^r}\right)^2.$$
开平方即得
$$\|u_\alpha-u_\beta\|_{H^r} \le |\alpha-\beta|N(2\pi\delta^2)^{-1}\|F\|_{H^r}.\qquad\blacksquare$$

---

## S4 整体对象与全部恢复目标

### 结论总览
1. **整体可逆性分类**：对任意 $\alpha\in\mathbb{R}\setminus\mathbb{Q}$，$N_\alpha:C^\infty_0(\mathbb{T}^2)\to C^\infty_0(\mathbb{T}^2)$ 良定义且**恒为单射**（解若存在必唯一）；但**并非对所有无理 $\alpha$ 都是满射**（对 Liouville 无理数不成立，见下方定理 4.1 必要性构造及 S6 的具体反例）。每个 $F\in C^\infty_0(\mathbb{T}^2)$ 都有唯一光滑零均值解 $N_\alpha u=F$ **当且仅当** $\alpha$ 是 **Diophantine 数（非 Liouville 数）**，即存在 $c>0$ 与 $s\ge 0$ 使 $|\alpha k_1+k_2|\ge c\langle k\rangle^{-s}$ 对所有 $k\in\mathbb{Z}^2\setminus\{0\}$ 成立。
2. **正则性损失 $s\ge 0$ 的完全分类**：对给定 $\alpha\in\mathbb{R}\setminus\mathbb{Q}$ 与 $s\ge 0$，“对每个 $r\in\mathbb{R}$ 存在 $C_{\alpha,r,s}<\infty$ 使 $\|u\|_{H^r}\le C_{\alpha,r,s}\|N_\alpha u\|_{H^{r+s}}$（$\forall u\in C^\infty_0(\mathbb{T}^2)$）”成立 **当且仅当**
   $$\inf_{k\in\mathbb{Z}^2\setminus\{0\}}\langle k\rangle^s|\alpha k_1+k_2| > 0 \quad\Longleftrightarrow\quad \inf_{q\in\mathbb{Z}\setminus\{0\},\,p\in\mathbb{Z}}|q|^s|\alpha q+p| > 0.$$
   特别地，$[0,1)$ 中的任何 $s$ 对任何无理 $\alpha$ 均不成立；记临界指数 $s_*(\alpha):=\inf\{s\ge 0:\inf_{k\neq 0}\langle k\rangle^s|\alpha k_1+k_2|>0\}\in[1,+\infty]$，允许的 $s$ 集合在 $s_*(\alpha)=+\infty$ 时为空集，在 $s_*(\alpha)<\infty$ 时为射线 $[s_*(\alpha),+\infty)$ 或 $(s_*(\alpha),+\infty)$（取决于 $s=s_*(\alpha)$ 处下确界是否大于 $0$）。
3. **$\alpha_*=\sqrt{2}-1$ 的精确边界与 $C^m$ 估计**：
   - $\alpha_*=\sqrt{2}-1$ 无理，其允许的损失集合为 $[1,+\infty)$，**最小允许损失为 $s_{\min}=1$，且该下界可以取到**；
   - $C^m$ 恢复目标**成立**：对每个 $m\in\mathbb{N}_0$，确实存在与 $F$ 无关的有限常数 $C_m$，使得对所有 $F\in C^\infty_0(\mathbb{T}^2)$ 有 $\|N_{\alpha_*}^{-1}F\|_{C^m}\le C_m\|F\|_{C^{m+4}}$。

---

### 定理与完整证明

#### 引理 4.0（双变量小除数界与单变量 Diophantine 界的等价性，以及 $s\ge 1$ 的必然性）
设 $\alpha\in\mathbb{R}\setminus\mathbb{Q}$，$s\ge 0$。则
$$\inf_{k\in\mathbb{Z}^2\setminus\{0\}}\langle k\rangle^s|\alpha k_1+k_2|>0 \quad\Longleftrightarrow\quad \inf_{q\in\mathbb{Z}\setminus\{0\},\,p\in\mathbb{Z}}|q|^s|\alpha q+p|>0.$$
并且若上述条件成立，则必有 $s\ge 1$。

**证明**：
- ($\Rightarrow$) 设 $|\alpha k_1+k_2|\ge c\langle k\rangle^{-s}$（$\forall k\neq 0$，$c>0$）。任取 $q\in\mathbb{Z}\setminus\{0\},p\in\mathbb{Z}$：若 $|p|>|\alpha||q|+1$，则 $|\alpha q+p|\ge |p|-|\alpha||q|>1\ge |q|^{-s}$；若 $|p|\le |\alpha||q|+1$，因 $|q|\ge 1$，有 $1+q^2+p^2\le \bigl(2+(|\alpha|+1)^2\bigr)q^2=:A_\alpha q^2$，故 $|\alpha q+p|\ge c A_\alpha^{-s/2}|q|^{-s}$。取 $c_1=\min(1,cA_\alpha^{-s/2})>0$ 即得右端。
- ($\Leftarrow$) 设 $|\alpha q+p|\ge c_1|q|^{-s}$（$\forall q\neq 0,p\in\mathbb{Z}$，$c_1>0$）。任取 $k=(k_1,k_2)\in\mathbb{Z}^2\setminus\{0\}$：若 $k_1=0$，则 $|k_2|\ge 1$，$|\alpha k_1+k_2|=|k_2|\ge 1\ge\langle k\rangle^{-s}$；若 $k_1\neq 0$，因 $|k_1|\le\langle k\rangle$ 且 $s\ge 0$，有 $|\alpha k_1+k_2|\ge c_1|k_1|^{-s}\ge c_1\langle k\rangle^{-s}$。取 $c=\min(1,c_1)>0$ 即得左端。
- ($s\ge 1$ 的必然性，Dirichlet 抽屉原理)：对任意整数 $Q\ge 1$，考察 $Q+1$ 个实数 $\{j\alpha-\lfloor j\alpha\rfloor:0\le j\le Q\}\subset[0,1)$。将 $[0,1)$ 等分为 $Q$ 个左闭右开子区间 $[\ell/Q,(\ell+1)/Q)$（$0\le\ell<Q$），由抽屉原理存在 $0\le j_1<j_2\le Q$ 落在同一子区间。令 $q=j_2-j_1\in\{1,\dots,Q\}$，$p=\lfloor j_1\alpha\rfloor-\lfloor j_2\alpha\rfloor\in\mathbb{Z}$，则 $0<|\alpha q+p|<1/Q\le 1/q$（因 $\alpha\notin\mathbb{Q}$，左端严格大于 $0$）。不断取更大的整数 $Q'>|\alpha q+p|^{-1}$ 即可得到无穷多个互异的正整数 $q\to\infty$ 及对应 $p\in\mathbb{Z}$，满足 $|\alpha q+p|<q^{-1}$。若 $0\le s<1$，则对这无穷多组 $(q,p)$ 有 $|q|^s|\alpha q+p|<q^{s-1}\to 0$（$q\to\infty$），下确界必为 $0$。故任何满足条件的 $s$ 必满足 $s\ge 1$。$\blacksquare$

---

#### 定理 4.1（$H^r$ 先验估计中损失指数 $s$ 的刻画）
设 $\alpha\in\mathbb{R}\setminus\mathbb{Q}$，$s\ge 0$。下列三条等价：
1. 对每个 $r\in\mathbb{R}$，存在有限常数 $C_{\alpha,r,s}>0$，使对所有 $u\in C^\infty_0(\mathbb{T}^2)$ 有 $\|u\|_{H^r}\le C_{\alpha,r,s}\|N_\alpha u\|_{H^{r+s}}$；
2. 存在某个 $r_0\in\mathbb{R}$ 和有限常数 $C>0$，使对所有 $u\in C^\infty_0(\mathbb{T}^2)$ 有 $\|u\|_{H^{r_0}}\le C\|N_\alpha u\|_{H^{r_0+s}}$；
3. 存在 $c>0$，使对所有 $k\in\mathbb{Z}^2\setminus\{0\}$ 有 $|\alpha k_1+k_2|\ge c\langle k\rangle^{-s}$。

**证明**：
- $(1)\Rightarrow(2)$：取 $r_0=0$ 即可。
- $(2)\Rightarrow(3)$：对任意 $k\in\mathbb{Z}^2\setminus\{0\}$，取测试函数 $u_k(y):=e^{2\pi i k\cdot y}\in C^\infty_0(\mathbb{T}^2)$。直接计算得 $\|u_k\|_{H^{r_0}}=\langle k\rangle^{r_0}$，$\|N_\alpha u_k\|_{H^{r_0+s}}=2\pi|\alpha k_1+k_2|\langle k\rangle^{r_0+s}$。代入 $(2)$（注意到 $\|u_k\|_{H^{r_0}}>0$ 故必有 $C>0$）得
  $$\langle k\rangle^{r_0} \le 2\pi C|\alpha k_1+k_2|\langle k\rangle^{r_0+s} \implies |\alpha k_1+k_2| \ge \frac{1}{2\pi C}\langle k\rangle^{-s}.$$
- $(3)\Rightarrow(1)$：对任意 $u\in C^\infty_0(\mathbb{T}^2)$，有 $\widehat{u}(0)=0$，且对 $k\neq 0$ 分部积分得 $\widehat{N_\alpha u}(k)=2\pi i(\alpha k_1+k_2)\widehat{u}(k)$。利用 $(3)$：
  $$\|u\|_{H^r}^2 = \sum_{k\neq 0}\langle k\rangle^{2r}\frac{|\widehat{N_\alpha u}(k)|^2}{4\pi^2|\alpha k_1+k_2|^2} \le \frac{1}{4\pi^2 c^2}\sum_{k\neq 0}\langle k\rangle^{2(r+s)}|\widehat{N_\alpha u}(k)|^2 = \left(\frac{1}{2\pi c}\|N_\alpha u\|_{H^{r+s}}\right)^2.$$
  取 $C_{\alpha,r,s}=(2\pi c)^{-1}$ 即得 $(1)$。$\blacksquare$

> **注（射线的开闭性）**：若 $s_1$ 满足定理 4.1(3) 且 $s_2>s_1$，因 $\langle k\rangle\ge 1$，有 $\langle k\rangle^{-s_2}\le\langle k\rangle^{-s_1}$，故 $s_2$ 亦满足。因此允许的 $s$ 集合恰为 $\{s\ge 1:\inf_{k\neq 0}\langle k\rangle^s|\alpha k_1+k_2|>0\}$。

---

#### 定理 4.2（$N_\alpha:C^\infty_0(\mathbb{T}^2)\to C^\infty_0(\mathbb{T}^2)$ 可逆性的充要条件）
设 $\alpha\in\mathbb{R}\setminus\mathbb{Q}$。
1. $N_\alpha$ 将 $C^\infty_0(\mathbb{T}^2)$ 映入 $C^\infty_0(\mathbb{T}^2)$ 且恒为单射。
2. $N_\alpha:C^\infty_0(\mathbb{T}^2)\to C^\infty_0(\mathbb{T}^2)$ 为双射（即每个 $F\in C^\infty_0(\mathbb{T}^2)$ 都有唯一光滑零均值解 $N_\alpha u=F$）**当且仅当** $\alpha$ 满足 Diophantine 条件：存在 $c>0$ 和 $s\ge 0$ 使得 $|\alpha k_1+k_2|\ge c\langle k\rangle^{-s}$ 对所有 $k\in\mathbb{Z}^2\setminus\{0\}$ 成立。此时唯一逆算子由
   $$N_\alpha^{-1}F(y) = \sum_{k\in\mathbb{Z}^2\setminus\{0\}}\frac{\widehat{F}(k)}{2\pi i(\alpha k_1+k_2)}e^{2\pi i k\cdot y}$$
   给出。

**证明**：
1. **良定义与单射性**：若 $u\in C^\infty_0(\mathbb{T}^2)$，则 $N_\alpha u\in C^\infty(\mathbb{T}^2)$，且由环面周期性 $\int_{\mathbb{T}^2}\partial_{y_j}u\,dy=0$（$j=1,2$），故 $N_\alpha u\in C^\infty_0(\mathbb{T}^2)$。若 $N_\alpha u=0$，则对所有 $k\in\mathbb{Z}^2$ 有 $2\pi i(\alpha k_1+k_2)\widehat{u}(k)=0$。因 $\alpha\notin\mathbb{Q}$，对 $k\neq 0$ 有 $\alpha k_1+k_2\neq 0$，从而 $\widehat{u}(k)=0$；又 $\widehat{u}(0)=\int_{\mathbb{T}^2}u=0$。由 $\{e_k\}_{k\in\mathbb{Z}^2}$ 在 $L^2(\mathbb{T}^2)$ 中的 Parseval 恒等式得 $\|u\|_{L^2}^2=\sum_k|\widehat{u}(k)|^2=0$，结合 $u$ 连续知 $u\equiv 0$。
2. **充分性**：设存在 $c>0,s\ge 0$ 使 $|\alpha k_1+k_2|\ge c\langle k\rangle^{-s}$（$\forall k\neq 0$）。S2 的全部前提均满足，故对每个 $F\in C^\infty_0(\mathbb{T}^2)$，S2 构造的级数给出了光滑零均值解 $u\in C^\infty_0(\mathbb{T}^2)$；由第 1 步单射性知该解唯一。
3. **必要性（非 Diophantine 时的不可解构造）**：设 Diophantine 条件不成立，即对每个整数 $n\ge 1$ 都有 $\inf_{k\neq 0}\langle k\rangle^{n}|\alpha k_1+k_2|=0$。因对任意有限半径 $R>0$，有限集 $\{0<|k|\le R\}$ 上 $\min|\alpha k_1+k_2|>0$（$\alpha\notin\mathbb{Q}$），我们可归纳选取点列 $\{k^{(n)}\}_{n=1}^\infty\subset\mathbb{Z}^2\setminus\{0\}$，使得 $|k^{(1)}|<|k^{(2)}|<\cdots$（从而 $k^{(n)}$ 两两互异且 $\langle k^{(n)}\rangle > 1$），并且
   $$0 < |\alpha k_1^{(n)}+k_2^{(n)}| < 2^{-n}\langle k^{(n)}\rangle^{-n} \qquad (\forall n\ge 1).$$
   定义级数
   $$F(y) := \sum_{n=1}^\infty 2\pi i(\alpha k_1^{(n)}+k_2^{(n)})e^{2\pi i k^{(n)}\cdot y}.$$
   对任意多重指标 $(a,b)\in\mathbb{N}_0^2$（记 $m=a+b$），当 $n\ge m$ 时，通项偏导的绝对值上界满足
   $$(2\pi)^m|k_1^{(n)}|^a|k_2^{(n)}|^b\cdot 2\pi|\alpha k_1^{(n)}+k_2^{(n)}| \le (2\pi)^{m+1}\langle k^{(n)}\rangle^m\cdot 2^{-n}\langle k^{(n)}\rangle^{-n} \le (2\pi)^{m+1}2^{-n}.$$
   由 Weierstrass $M$ 判别法，$F\in C^\infty(\mathbb{T}^2)$；又每个 $k^{(n)}\neq 0$ 且两两互异，逐项积分给出 $\widehat{F}(0)=0$（即 $F\in C^\infty_0(\mathbb{T}^2)$）以及 $\widehat{F}(k^{(n)})=2\pi i(\alpha k_1^{(n)}+k_2^{(n)})$（$\forall n\ge 1$）。若存在 $u\in C^\infty_0(\mathbb{T}^2)$ 使 $N_\alpha u=F$，比较 $k=k^{(n)}$ 处的 Fourier 系数并约去非零因子 $2\pi i(\alpha k_1^{(n)}+k_2^{(n)})$，得 $\widehat{u}(k^{(n)})=1$（$\forall n\ge 1$）。但对 $u\in C^\infty_0(\mathbb{T}^2)\subset L^2(\mathbb{T}^2)$ 应用 Bessel 不等式得
   $$\infty > \|u\|_{L^2}^2 \ge \sum_{n=1}^\infty|\widehat{u}(k^{(n)})|^2 = \sum_{n=1}^\infty 1 = \infty,$$
   矛盾！故 $N_\alpha u=F$ 在 $C^\infty_0(\mathbb{T}^2)$ 中无解。$\blacksquare$

---

#### 定理 4.3（$\alpha_*=\sqrt{2}-1$ 的精确损失指数与 $C^m$ 正则性恢复）
令 $\alpha_*=\sqrt{2}-1$。
1. $\alpha_*\in\mathbb{R}\setminus\mathbb{Q}$，且对所有 $k\in\mathbb{Z}^2\setminus\{0\}$ 成立精确阶下界
   $$|\alpha_* k_1+k_2| \ge \frac{1}{\sqrt{4+2\sqrt{2}}}\langle k\rangle^{-1}.$$
   从而 $\alpha_*$ 允许的损失集合恰为 $[1,+\infty)$，**最小允许损失为 $s_{\min}=1$，且 $s=1$ 可以取到**。
2. 对每个 $m\in\mathbb{N}_0$，存在仅依赖 $m$ 的有限常数 $C_m>0$，使得对所有 $F\in C^\infty_0(\mathbb{T}^2)$ 有
   $$\|N_{\alpha_*}^{-1}F\|_{C^m} \le C_m\|F\|_{C^{m+4}}.$$

**证明**：
1. **无理性、$s=1$ 的可达性与最优性**：
   - 若 $\alpha_*\in\mathbb{Q}$，则 $\sqrt{2}=\alpha_*+1\in\mathbb{Q}$，与 $\sqrt{2}$ 无理矛盾，故 $\alpha_*\in\mathbb{R}\setminus\mathbb{Q}$。
   - 任取 $k=(k_1,k_2)\in\mathbb{Z}^2\setminus\{0\}$。
     - 若 $k_1=0$，则 $|k_2|\ge 1$，$|\alpha_* k_1+k_2|=|k_2|\ge 1 > (4+2\sqrt{2})^{-1/2}\langle k\rangle^{-1}$。
     - 若 $k_1\neq 0$，考察二次代数整数及其共轭之积：
       $$(\alpha_* k_1+k_2)\bigl(-(\sqrt{2}+1)k_1+k_2\bigr) = \bigl((k_2-k_1)+k_1\sqrt{2}\bigr)\bigl((k_2-k_1)-k_1\sqrt{2}\bigr) = (k_2-k_1)^2-2k_1^2\in\mathbb{Z}.$$
       因 $k_1\neq 0$ 且 $\sqrt{2}\notin\mathbb{Q}$，必有 $(k_2-k_1)^2-2k_1^2\neq 0$，作为非零整数其绝对值至少为 $1$：
       $$|\alpha_* k_1+k_2|\cdot|-(\sqrt{2}+1)k_1+k_2| \ge 1.$$
       由 Cauchy–Schwarz 不等式，
       $$|-(\sqrt{2}+1)k_1+k_2| \le (\sqrt{2}+1)|k_1|+|k_2| \le \sqrt{(\sqrt{2}+1)^2+1^2}\sqrt{k_1^2+k_2^2} = \sqrt{4+2\sqrt{2}}\,|k| < \sqrt{4+2\sqrt{2}}\,\langle k\rangle.$$
       相除即得 $|\alpha_* k_1+k_2|\ge (4+2\sqrt{2})^{-1/2}\langle k\rangle^{-1}$。
   - 由定理 4.1 知 $s=1$（以及所有 $s\ge 1$）均为允许损失；再由引理 4.0 知任何 $s\in[0,1)$ 均不允许（亦可直接取 Pell 数列 $P_0=0,P_1=1,P_{n+1}=2P_n+P_{n-1}$，因 $\alpha_*^2+2\alpha_*-1=0$，归纳得 $\alpha_* P_n - P_{n-1}=(-1)^{n-1}\alpha_*^n\asymp P_n^{-1}$，故对 $s<1$ 有 $\langle(P_n,-P_{n-1})\rangle^s|\alpha_* P_n-P_{n-1}|\to 0$）。故最小允许损失为 $s_{\min}=1$ 且可取到。

2. **$C^m$ 范数估计 $\|N_{\alpha_*}^{-1}F\|_{C^m}\le C_m\|F\|_{C^{m+4}}$ 的证明**：
   由定理 4.2 及第 1 步，$u:=N_{\alpha_*}^{-1}F\in C^\infty_0(\mathbb{T}^2)$ 良定义，其非零 Fourier 系数为 $\widehat{u}(k)=\frac{\widehat{F}(k)}{2\pi i(\alpha_* k_1+k_2)}$（$k\neq 0$）。
   对每个 $k=(k_1,k_2)\in\mathbb{Z}^2\setminus\{0\}$，取 $j\in\{1,2\}$ 使 $|k_j|=\max(|k_1|,|k_2|)$。因为 $|k|\ge 1$，有
   $$\langle k\rangle^2 = 1+k_1^2+k_2^2 \le 2|k|^2 \le 4k_j^2 \implies |k_j| \ge \frac{1}{2}\langle k\rangle.$$
   对 $F\in C^\infty_0(\mathbb{T}^2)$ 关于变量 $y_j$ 分部积分 $m+4$ 次（由 $\mathbb{T}^2$ 的周期性无边界项）：
   $$(2\pi i k_j)^{m+4}\widehat{F}(k) = \int_{\mathbb{T}^2}\bigl(\partial_{y_j}^{m+4}F(y)\bigr)e^{-2\pi i k\cdot y}\,dy.$$
   由于归一化 Haar 测度总质量为 $1$ 且 $\sup_{y\in\mathbb{T}^2}|\partial_{y_j}^{m+4}F(y)|\le\|F\|_{C^{m+4}}$，得
   $$|\widehat{F}(k)| \le (2\pi|k_j|)^{-(m+4)}\|F\|_{C^{m+4}} \le \pi^{-(m+4)}\langle k\rangle^{-(m+4)}\|F\|_{C^{m+4}} \qquad (\forall k\in\mathbb{Z}^2\setminus\{0\}).$$
   现任取 $a,b\ge 0$ 满足 $a+b\le m$，由 S2 中已证的一致收敛性可对 $u$ 逐项求导；对任意 $y\in\mathbb{T}^2$，结合 $|k_1|^a|k_2|^b\le\langle k\rangle^m$ 及第 1 步的小除数界 $|\alpha_* k_1+k_2|^{-1}\le\sqrt{4+2\sqrt{2}}\langle k\rangle$，有
   $$\begin{aligned}
   \left|\partial_{y_1}^a\partial_{y_2}^b u(y)\right|
   &\le \sum_{k\neq 0}(2\pi)^{a+b}|k_1|^a|k_2|^b\frac{|\widehat{F}(k)|}{2\pi|\alpha_* k_1+k_2|} \\
   &\le \frac{(2\pi)^m\sqrt{4+2\sqrt{2}}}{2\pi}\sum_{k\neq 0}\langle k\rangle^{m+1}\cdot\pi^{-(m+4)}\langle k\rangle^{-(m+4)}\|F\|_{C^{m+4}} \\
   &= \frac{2^{m-1}\sqrt{4+2\sqrt{2}}}{\pi^5}\left(\sum_{k\in\mathbb{Z}^2\setminus\{0\}}\langle k\rangle^{-3}\right)\|F\|_{C^{m+4}}.
   \end{aligned}$$
   验证级数 $S_3:=\sum_{k\in\mathbb{Z}^2\setminus\{0\}}\langle k\rangle^{-3}$ 有限：按无穷范数分层 $R=\max(|k_1|,|k_2|)\ge 1$，每层恰有 $(2R+1)^2-(2R-1)^2=8R$ 个整点，且每点满足 $\langle k\rangle = (1+k_1^2+k_2^2)^{1/2} > R$，故
   $$S_3 = \sum_{R=1}^\infty\sum_{\max(|k_1|,|k_2|)=R}\langle k\rangle^{-3} \le \sum_{R=1}^\infty 8R\cdot R^{-3} = 8\sum_{R=1}^\infty\frac{1}{R^2} < \infty.$$
   令 $C_m := \frac{2^{m-1}\sqrt{4+2\sqrt{2}}}{\pi^5}S_3 < \infty$（与 $F$ 无关），对 $y\in\mathbb{T}^2$ 取上确界并对 $a+b\le m$ 取最大值即得 $\|N_{\alpha_*}^{-1}F\|_{C^m}\le C_m\|F\|_{C^{m+4}}$。$\blacksquare$

---

## S5 邻近方向的一致估计

### 结论
**不成立**（不存在满足条件的开区间 $J\ni\alpha_*$、有限 $s\ge 0$ 与常数 $C<\infty$）。

### 完整证明（对任意给定参数的显式反例）
任给包含 $\alpha_*=\sqrt{2}-1$ 的开区间 $J$、有限实数 $s\ge 0$ 以及常数 $C\in[0,\infty)$，我们构造无理数 $\alpha\in J\setminus\mathbb{Q}$ 及光滑零均值函数 $u_0\in C^\infty_0(\mathbb{T}^2)$，使 $\|u_0\|_{L^2} > C\|N_\alpha u_0\|_{H^s}$：

1. 因为 $J$ 是 $\mathbb{R}$ 中的非空开区间，有理数集 $\mathbb{Q}$ 在 $\mathbb{R}$ 中稠密，故存在有理数 $\frac{p}{q}\in J$，其中 $p\in\mathbb{Z},q\in\mathbb{N}$（$q\ge 1$）。
2. 固定非零整频率 $k_0:=(q,-p)\in\mathbb{Z}^2\setminus\{0\}$，定义
   $$u_0(y) := e^{2\pi i(q y_1 - p y_2)}.$$
   显然 $u_0\in C^\infty(\mathbb{T}^2)$，$\int_{\mathbb{T}^2}u_0(y)\,dy = 0$，即 $u_0\in C^\infty_0(\mathbb{T}^2)$，且 $\|u_0\|_{L^2}=1$。
3. 因为 $J$ 开且 $\frac{p}{q}\in J$，存在 $\varepsilon>0$ 使 $(\frac{p}{q}-\varepsilon,\frac{p}{q}+\varepsilon)\subset J$。取正整数 $n$ 充分大，同时满足
   $$\frac{\sqrt{2}}{n} < \varepsilon \qquad\text{以及}\qquad 2\pi C q\frac{\sqrt{2}}{n}(1+q^2+p^2)^{s/2} < \frac{1}{2},$$
   并令
   $$\alpha := \frac{p}{q} + \frac{\sqrt{2}}{n}.$$
   则 $\alpha\in J$，且因 $\frac{p}{q}\in\mathbb{Q},n\in\mathbb{N},\sqrt{2}\notin\mathbb{Q}$，必有 $\alpha\in\mathbb{R}\setminus\mathbb{Q}$（否则 $\sqrt{2}=n(\alpha-p/q)\in\mathbb{Q}$，矛盾）。
4. 对该无理方向 $\alpha\in J$ 与 $u_0\in C^\infty_0(\mathbb{T}^2)$，计算得
   $$N_\alpha u_0(y) = 2\pi i(\alpha q - p)e^{2\pi i(q y_1 - p y_2)} = 2\pi i q\frac{\sqrt{2}}{n}e^{2\pi i(q y_1 - p y_2)},$$
   从而
   $$C\|N_\alpha u_0\|_{H^s} = 2\pi C q\frac{\sqrt{2}}{n}\langle k_0\rangle^s = 2\pi C q\frac{\sqrt{2}}{n}(1+q^2+p^2)^{s/2} < \frac{1}{2} < 1 = \|u_0\|_{L^2}.$$

这违反了 $\|u_0\|_{L^2}\le C\|N_\alpha u_0\|_{H^s}$。由于 $J,s,C$ 任意，满足题设的一致估计不存在。$\blacksquare$

> *注*：事实上，开区间 $J$ 中不仅有无限逼近有理数的 Diophantine 方向破坏一致常数 $C$，甚至还稠密地包含形如 $\frac{p}{q}+\sum_{n=M}^\infty 10^{-n!}\in J\setminus\mathbb{Q}$ 的 Liouville 数，对单个这样的方向连非一致常数 $C_{\alpha,s}<\infty$ 都不存在。

---

## S6 一个具体方向的不可解数据

设 $\alpha = \sum_{n=1}^\infty 10^{-n!}$。对每个整数 $N\ge 1$，记
$$q_N := 10^{N!}\in\mathbb{N}, \qquad p_N := \sum_{n=1}^N 10^{N!-n!}\in\mathbb{N}.$$

### 1. 证明 $\alpha$ 无理
对任意整数 $N\ge 1$，将级数拆分为前 $N$ 项与余项：
$$\alpha - \frac{p_N}{q_N} = \sum_{n=N+1}^\infty 10^{-n!}.$$
因为当 $n\ge N+1$ 时不同指标对应的阶乘 $n!$ 严格递增且不小于 $(N+1)!$，故可用公比为 $1/10$ 的几何级数控制余项：
$$0 < \alpha - \frac{p_N}{q_N} \le \sum_{j=(N+1)!}^\infty 10^{-j} = \frac{10^{-(N+1)!}}{1-\frac{1}{10}} = \frac{10}{9}\cdot 10^{-(N+1)!}.$$
两边同乘 $q_N=10^{N!}$，利用 $(N+1)!-N! = N\cdot N!$，得关键小除数估计
$$0 < \alpha q_N - p_N \le \frac{10}{9}\cdot 10^{-N\cdot N!} \qquad (\forall N\ge 1). \tag{$\ast$}$$

假设 $\alpha\in\mathbb{Q}$，写成 $\alpha = \frac{a}{b}$（$a\in\mathbb{Z},b\in\mathbb{N},b\ge 1$）。则对任意 $N\ge 1$，
$$\alpha q_N - p_N = \frac{a q_N - b p_N}{b}.$$
由 $(\ast)$ 左端知 $a q_N - b p_N > 0$；又 $a q_N - b p_N\in\mathbb{Z}$，故 $a q_N - b p_N \ge 1$，从而 $\alpha q_N - p_N \ge \frac{1}{b}$ 对一切 $N\ge 1$ 成立。但由 $(\ast)$ 右端，当 $N\to\infty$ 时 $\frac{10}{9}\cdot 10^{-N\cdot N!}\to 0$，取正整数 $N$ 使 $10^{N\cdot N!} > \frac{10}{9}b$ 即得 $\frac{1}{b} \le \alpha q_N - p_N < \frac{1}{b}$，矛盾！因此 $\alpha$ 是无理数。

---

### 2. 单一不可解光滑零均值数据 $F$ 的构造与证明
记整频率序列 $k^{(N)} := (q_N,-p_N)\in\mathbb{Z}^2$（$N\ge 1$），并定义**同一个**函数 $F:\mathbb{T}^2\to\mathbb{C}$ 为
$$F(y) := \sum_{N=1}^\infty 10^{-N\cdot N!} e^{2\pi i(q_N y_1 - p_N y_2)}.$$

#### 第一步：证明 $F\in C^\infty_0(\mathbb{T}^2)$
- **光滑性**：注意到 $0 < \alpha = \sum_{n=1}^\infty 10^{-n!} < \sum_{j=1}^\infty 10^{-j} = \frac{1}{9} < 1$，故 $0 < p_N < \alpha q_N < q_N = 10^{N!}$。对任意偏导阶数 $a,b\ge 0$（记 $m=a+b$），考察形式逐项求导级数
  $$\sum_{N=1}^\infty 10^{-N\cdot N!}(2\pi i q_N)^a(-2\pi i p_N)^b e^{2\pi i(q_N y_1 - p_N y_2)}.$$
  其第 $N$ 项在 $\mathbb{T}^2$ 上的一致绝对值上界满足
  $$\left|10^{-N\cdot N!}(2\pi i q_N)^a(-2\pi i p_N)^b e^{2\pi i(q_N y_1 - p_N y_2)}\right| \le (2\pi)^m q_N^{a+b} 10^{-N\cdot N!} = (2\pi)^m 10^{(m-N)N!}.$$
  当 $N\ge m+1$ 时，$(m-N)N!\le -N!\le -N$，故尾和受几何级数 $(2\pi)^m\sum_{N=m+1}^\infty 10^{-N}<\infty$ 控制。由 Weierstrass $M$ 判别法及一致收敛级数逐项求导定理，$F\in C^\infty(\mathbb{T}^2)$。
- **零均值与 Fourier 系数**：因级数一致收敛，可逐项积分。对每个 $N\ge 1$，$q_N=10^{N!}\ge 10\neq 0$，故 $k^{(N)}=(q_N,-p_N)\neq (0,0)$，从而
  $$\int_{\mathbb{T}^2}F(y)\,dy = \sum_{N=1}^\infty 10^{-N\cdot N!}\int_{\mathbb{T}^2}e^{2\pi i k^{(N)}\cdot y}\,dy = 0,$$
  即 $F\in C^\infty_0(\mathbb{T}^2)$。同时，因 $q_1<q_2<\cdots<q_N<\cdots$ 严格递增，整频率 $\{k^{(N)}\}_{N=1}^\infty$ 两两互异，故由 $\{e_k\}_{k\in\mathbb{Z}^2}$ 的正交归一性得
  $$\widehat{F}(k^{(N)}) = 10^{-N\cdot N!} \qquad (\forall N\ge 1).$$

#### 第二步：证明 $N_\alpha u = F$ 没有光滑零均值解
反证法：假设存在光滑零均值函数 $u\in C^\infty_0(\mathbb{T}^2)$ 满足 $N_\alpha u = F$。对每个 $N\ge 1$，在频率 $k^{(N)}=(q_N,-p_N)$ 处分部积分取 Fourier 系数：
$$2\pi i(\alpha q_N - p_N)\widehat{u}(k^{(N)}) = \widehat{N_\alpha u}(k^{(N)}) = \widehat{F}(k^{(N)}) = 10^{-N\cdot N!}.$$
结合 $(\ast)$ 式 $0 < \alpha q_N - p_N \le \frac{10}{9}\cdot 10^{-N\cdot N!}$，对每个 $N\ge 1$ 都有
$$|\widehat{u}(k^{(N)})| = \frac{10^{-N\cdot N!}}{2\pi(\alpha q_N - p_N)} \ge \frac{10^{-N\cdot N!}}{2\pi\cdot\frac{10}{9}\cdot 10^{-N\cdot N!}} = \frac{9}{20\pi} > 0.$$
由于序列 $\{k^{(N)}\}_{N=1}^\infty$ 在 $\mathbb{Z}^2$ 中两两互异，且 $u\in C^\infty_0(\mathbb{T}^2)\subset C(\mathbb{T}^2)\subset L^2(\mathbb{T}^2)$，对正交归一系 $\{e_k\}_{k\in\mathbb{Z}^2}$ 应用 Bessel 不等式得
$$\|u\|_{C^0}^2 \ge \|u\|_{L^2(\mathbb{T}^2)}^2 \ge \sum_{N=1}^\infty |\widehat{u}(k^{(N)})|^2 \ge \sum_{N=1}^\infty \left(\frac{9}{20\pi}\right)^2 = +\infty,$$
与紧流形 $\mathbb{T}^2$ 上连续函数 $u$ 的有界性 $\|u\|_{C^0}<\infty$ 矛盾！因此 $N_\alpha u=F$ 没有光滑零均值解。$\blacksquare$
