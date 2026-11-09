# 总览

以下在 $\mathbb T^2=\mathbb R^2/\mathbb Z^2$（归一化 Haar 测度）上工作。记 $e_k(y)=e^{2\pi ik\cdot y}$，小除数
$$\sigma_\alpha(k):=\alpha k_1+k_2,\qquad \langle k\rangle=(1+|k|^2)^{1/2}\ (|k|\ \text{Euclid 范数}).$$

各题结论一览：

- **S1**：$\alpha$ 无理时 $N_\alpha$ 在 $H_N$ 上可逆，逆为显式 Fourier 乘子；对**一切** $r\in\mathbb R$，$\|N_\alpha^{-1}\|_{H^r\to H^r}=\big(2\pi\min_{0<|k|\le N}|\alpha k_1+k_2|\big)^{-1}$（与 $r$ 无关，且取到）。
- **S2**：光滑解 $u$ 显式构造、唯一；截断误差界成立（证明见下）。
- **S3**：$\|u_\alpha-u_\beta\|_{H^r}\le|\alpha-\beta|N(2\pi\delta^2)^{-1}\|F\|_{H^r}$（证明见下）。
- **S4**：$N_\alpha:C^\infty_0\to C^\infty_0$ 双射 $\iff$ $\alpha$ 为 Diophantine 数（$\exists c,s:\ |\alpha k_1+k_2|\ge c\langle k\rangle^{-s}\ \forall k\ne0$）；有理或 Liouville 时给出满足全部条件的反例。允许损失集 $\mathcal S_\alpha=\{s:\inf_{k\ne0}\langle k\rangle^s|\sigma_\alpha(k)|>0\}$，最优常数 $(2\pi\delta_s)^{-1}$ 与 $r$ 无关。对 $\alpha_*=\sqrt2-1$：$\mathcal S_{\alpha_*}=[1,\infty)$，最小损失 $s=1$ **被取到**；$C^m$ 估计（损失 $4$）**成立**。
- **S5**：**不存在**这样的 $(J,s,C)$。
- **S6**：$\alpha=\sum 10^{-n!}$ 无理；给出**单个**显式 $F\in C^\infty_0$ 使 $N_\alpha u=F$ 无光滑（甚至无 $L^1$）解。

---

# 0 记号与预备事实

**(P1) Fourier 公式与唯一性。** 对 $u\in C^1(\mathbb T^2)$（对分布亦然），环面上分部积分给出 $\widehat{\partial_{y_j}u}(k)=2\pi ik_j\widehat u(k)$，故
$$\widehat{N_\alpha u}(k)=2\pi i\,\sigma_\alpha(k)\,\widehat u(k),\qquad k\in\mathbb Z^2. \tag{P1}$$
特别 $\widehat{N_\alpha u}(0)=0$，即 $N_\alpha(C^\infty_0)\subseteq C^\infty_0$。$\{e_k\}$ 为 $L^2$ 正交基，$\|e_k\|_{L^2}=1,\ \|e_k\|_{H^r}=\langle k\rangle^r$；$|\hat f(k)|\le\|f\|_{L^1}\le\|f\|_{L^\infty}$（测度 $=1$）；Fourier 系数在 $L^1$ 上单射（标准唯一性定理，由 Fejér 逼近可得）：$L^1$ 中两函数系数全同则几乎处处相等，连续时恒等。这些是标准环面 Fourier 理论。

**(P2) 共振。** $\sigma_\alpha(k)\ne0\ \forall k\ne0\iff\alpha\notin\mathbb Q$。事实上若 $\sigma_\alpha(k)=0,\ k\ne0$，则 $k_1\ne0$（否则 $k_2=0$），$\alpha=-k_2/k_1\in\mathbb Q$；反之 $\alpha=p/q$（$q\ge1$）时 $\sigma_\alpha(q,-p)=0$。

**(P3) 格点和。** $t>2$ 时 $S_t:=\sum_{k\in\mathbb Z^2}\langle k\rangle^{-t}\le 1+24\sum_{n\ge1}n^{1-t}<\infty$：环壳 $\{n\le|k|<n+1\}$ 至多含 $(2n+3)^2-(2n-1)^2=16n+8\le24n$ 个点，其上 $\langle k\rangle^{-t}\le n^{-t}$。

**(P4) 光滑性的系数刻画。**
(i) 若 $f\in C^D$，则对 $k\ne0$，取 $i^*$ 使 $|k_{i^*}|=\max(|k_1|,|k_2|)\ge|k|/\sqrt2$；由 $|k|\ge1\Rightarrow\langle k\rangle\le\sqrt2|k|$ 得 $|k_{i^*}|\ge\langle k\rangle/2$，于是
$$|\hat f(k)|=\frac{|\widehat{\partial_{y_{i^*}}^Df}(k)|}{(2\pi|k_{i^*}|)^D}\le\frac{2^{D}\|f\|_{C^D}}{\langle k\rangle^{D}}. \tag{P4}$$
(ii) 若数列 $(c_k)$ 满足 $\sum_k\langle k\rangle^{2m}|c_k|^2<\infty$ 对一切 $m\in\mathbb N_0$，则由 Cauchy–Schwarz（配合 $\sum\langle k\rangle^{-4}=S_4<\infty$），$\sum_k(2\pi)^j\langle k\rangle^{j}|c_k|<\infty$ 对一切 $j$；由 M-判别法 $f:=\sum_kc_ke_k\in C^\infty$，可逐项求导，$\hat f=c$（一致收敛可逐项积分），且
$$\|f\|_{C^j}\le(2\pi)^j\sum_k\langle k\rangle^{j}|c_k|,\qquad \Big(\sum_k\langle k\rangle^{2j+4}|c_k|^2\Big)^{1/2}S_4^{1/2}<\infty. \tag{P4'}$$
(iii) $f\in C^\infty\Rightarrow\|f\|_{H^m}<\infty\ \forall m$（在 (P4) 中取 $D=m+2$ 并用 $S_4<\infty$）。

**(P5) Dirichlet 逼近。** $\alpha$ 无理时存在无穷多对 $(p,q),\ q\ge1,\ q\to\infty$，使 $|q\alpha-p|<1/q$。证明：对每个 $Q\ge1$，$Q+1$ 个点 $0,\{\alpha\},\dots,\{Q\alpha\}\subset[0,1)$ 中有两点距离 $<1/Q$，其差给出 $1\le q\le Q,\ \|q\alpha\|<1/Q\le1/q$。若这样的对只有有限多，诸 $|q\alpha-p|$ 有正下界 $\mu$（无理性），取 $Q>1/\mu$ 得更小的一对，矛盾；同理分母无界。

**(P6) 小除数函数。** 对 $s\ge0$ 令 $\delta_s(\alpha):=\inf_{k\ne0}\langle k\rangle^{s}|\sigma_\alpha(k)|\in[0,\infty)$（关于 $s$ 不减，因 $\langle k\rangle\ge1$）。称 $\alpha\in\mathcal D$（Diophantine），若 $\exists s\ge0:\delta_s(\alpha)>0$。由 (P2)，$\alpha\in\mathcal D\Rightarrow\alpha$ 无理。

(a) **对一切 $\alpha\in\mathbb R$ 与一切 $s<1$：$\delta_s(\alpha)=0$。** 有理 $\alpha=p/q$：在 $k=(q,-p)$ 处 $\sigma_\alpha=0$。无理 $\alpha$：取 (P5) 的 $(p,q)$，$k=(q,-p)$；由 $|p|\le q|\alpha|+1$ 得 $\langle k\rangle\le C_\alpha q$（例如 $C_\alpha=\sqrt{3+2\alpha^2+3}$），故 $\langle k\rangle^{s}|\sigma_\alpha(k)|\le C_\alpha^{s}q^{s-1}\to0$（$s<1$）。

(b) 对照（非必需）：$\delta_s(\alpha)>0\iff\exists c>0:\|n\alpha\|\ge cn^{-s}\ \forall n\ge1$。$\Leftarrow$：$k_1=0$ 时 $|\sigma_\alpha(k)|=|k_2|\ge1$；$k_1\ne0$ 时 $|\sigma_\alpha(k)|\ge\|k_1\alpha\|\ge c|k_1|^{-s}\ge c\langle k\rangle^{-s}$。$\Rightarrow$：取 $k_2$ 为 $-n\alpha$ 的最近整数，$\|n\alpha\|=|\sigma_\alpha(n,k_2)|\ge\delta_s\langle(n,k_2)\rangle^{-s}\ge\delta_s(C_\alpha n)^{-s}$。

---

# S1 有限频带上的逆

**定理 S1.** 设 $\alpha$ 无理，$N\ge1$，$H_N=\mathrm{span}\{e_k:0<|k|\le N\}$（有限维，且 $\supset\{e_{(1,0)}\}\neq\{0\}$）。则

1. $N_\alpha(H_N)\subseteq H_N$ 且 $N_\alpha$ 为 $H_N\to H_N$ 的线性同构，其逆为
$$(N_\alpha^{-1}F)(y)=\sum_{0<|k|\le N}\frac{\hat F(k)}{2\pi i\,\sigma_\alpha(k)}\,e_k(y),\qquad F\in H_N .$$
2. 记 $\delta_N:=\min_{0<|k|\le N}|\sigma_\alpha(k)|$。由 (P2) 与有限性 $\delta_N>0$，且对**每个** $r\in\mathbb R$
$$\|N_\alpha^{-1}\|_{H^r\to H^r}=\frac{1}{2\pi\,\delta_N}\quad(\text{与 }r\text{ 无义}),$$
该值在极值频率处达到：若 $|\sigma_\alpha(k_0)|=\delta_N$，则 $\|N_\alpha^{-1}e_{k_0}\|_{H^r}=\dfrac{\langle k_0\rangle^{r}}{2\pi\delta_N}=\dfrac{\|e_{k_0}\|_{H^r}}{2\pi\delta_N}$。

**证明.** (1) 由 (P1)，$N_\alpha u$ 的系数为 $2\pi i\sigma_\alpha(k)\hat u(k)$：支于同一频带且 $k=0$ 处为 $0$，故 $N_\alpha(H_N)\subseteq H_N$。由 (P2)，频带内 $\sigma_\alpha(k)\ne0$，故可定义线性算子 $TF:=\sum_{0<|k|\le N}\frac{\hat F(k)}{2\pi i\sigma_\alpha(k)}e_k\in H_N$，且逐系数地 $N_\alpha(TF)=F,\ T(N_\alpha u)=u$。故 $N_\alpha$ 可逆且逆为 $T$。

(2) 对 $F\in H_N$，
$$\|N_\alpha^{-1}F\|_{H^r}^2=\sum_{0<|k|\le N}\langle k\rangle^{2r}\frac{|\hat F(k)|^2}{4\pi^2\sigma_\alpha(k)^2}\le\frac{1}{4\pi^2\delta_N^2}\sum_{0<|k|\le N}\langle k\rangle^{2r}|\hat F(k)|^2=\frac{\|F\|_{H^r}^2}{4\pi^2\delta_N^2}.$$
反之取 $F=e_{k_0}$ 即等号。故算子范数恰为 $(2\pi\delta_N)^{-1}$；权重 $\langle k\rangle^{2r}$ 在比值中消去，故与 $r$ 无关，且范数取到。$\blacksquare$

---

# S2 有算术界的截断误差

**定理 S2.** 设 $c>0,\ s\ge0$ 使 $|\sigma_\alpha(k)|\ge c\langle k\rangle^{-s}$ 对一切 $k\ne0$（由 (P2) 这蕴涵 $\alpha$ 无理，故 S1 适用）。设 $F\in C^\infty_0$，$F_N:=\sum_{0<|k|\le N}\hat F(k)e_k\in H_N$，$u_N:=N_\alpha^{-1}F_N$。令
$$u:=\sum_{k\ne0}\frac{\hat F(k)}{2\pi i\,\sigma_\alpha(k)}\,e_k .$$
则 $u\in C^\infty_0$ 是 $N_\alpha u=F$ 的**唯一**光滑零均值解，且对一切 $r\in\mathbb R,\ q\ge0,\ N\ge1$：
$$\|u-u_N\|_{H^r}\le(2\pi c)^{-1}(1+N^2)^{-q/2}\,\|F\|_{H^{r+s+q}} .$$
特别地（取 $q>0$，$F$ 光滑故右边诸范数有限），$u_N\to u$ 于每个 $H^r$。

**证明.** (i) **$u$ 合法且解方程.** 对每个 $m\in\mathbb N_0$，
$$\sum_{k\ne0}\langle k\rangle^{2m}\Big|\frac{\hat F(k)}{2\pi i\sigma_\alpha(k)}\Big|^{2}\le\frac{1}{4\pi^{2}c^{2}}\sum_{k\ne0}\langle k\rangle^{2(m+s)}|\hat F(k)|^{2}=\frac{\|F\|_{H^{m+s}}^{2}}{4\pi^{2}c^{2}}<\infty$$
（(P4)(iii)）。由 (P4)(ii)，$u\in C^\infty$，系数如所示，且 $\hat u(0)=0$（级数不含 $k=0$），即 $u\in C^\infty_0$。由 (P1) 逐系数验证 $\widehat{N_\alpha u}(k)=\hat F(k)$ 对一切 $k$（$k=0$ 处 $0=\hat F(0)$），再由 (P1) 的单射性得 $N_\alpha u=F$。

(ii) **唯一性.** 若 $u'\in C^\infty_0$ 亦解，则 $w:=u-u'\in C^\infty_0$ 满足 $2\pi i\sigma_\alpha(k)\hat w(k)=0\ \forall k$；$k\ne0$ 时 $\sigma_\alpha(k)\neq0$（假设），故 $\hat w(k)=0$；$k=0$ 时 $\hat w(0)=0$（零均值）。故 $w=0$。

(iii) **误差估计.** 由 S1，$\hat u_N(k)=\frac{\hat F(k)}{2\pi i\sigma_\alpha(k)}\mathbf 1_{\{0<|k|\le N\}}$，故 $\widehat{u-u_N}$ 支于 $\{|k|>N\}$ 且在该处等于 $\frac{\hat F(k)}{2\pi i\sigma_\alpha(k)}$。于是
$$\|u-u_N\|_{H^r}^2=\sum_{|k|>N}\langle k\rangle^{2r}\frac{|\hat F(k)|^2}{4\pi^2\sigma_\alpha(k)^2}\le\frac{1}{4\pi^2c^2}\sum_{|k|>N}\langle k\rangle^{2(r+s)}|\hat F(k)|^2 .$$
若 $|k|>N$（整数），则 $|k|\ge N+1$，故 $\langle k\rangle^2=1+|k|^2\ge1+(N+1)^2>1+N^2$，从而（$q\ge0$，两端为正数）
$$\langle k\rangle^{-2q}\le(1+N^2)^{-q},\qquad 
\langle k\rangle^{2(r+s)}|\hat F(k)|^2\le(1+N^2)^{-q}\,\langle k\rangle^{2(r+s+q)}|\hat F(k)|^2 .$$
对 $|k|>N$ 求和并放大为全和：
$$\|u-u_N\|_{H^r}^2\le\frac{(1+N^2)^{-q}}{4\pi^2c^2}\,\|F\|_{H^{r+s+q}}^2 .$$
开方即得。$\blacksquare$

---

# S3 固定频带内改变方向

**定理 S3.** 设 $\alpha,\beta$ 无理，$N\ge1$，且 $\min_{0<|k|\le N}|\sigma_\alpha(k)|\ge\delta>0$、$\min_{0<|k|\le N}|\sigma_\beta(k)|\ge\delta>0$。对 $F\in H_N$，令 $u_\alpha:=N_\alpha^{-1}F,\ u_\beta:=N_\beta^{-1}F$（定理 S1）。则对一切 $r\in\mathbb R$：
$$\|u_\alpha-u_\beta\|_{H^r}\le\frac{|\alpha-\beta|\,N}{2\pi\,\delta^{2}}\,\|F\|_{H^r}.$$

**证明.** 对 $0<|k|\le N$（此时 $|\sigma_\alpha(k)|,|\sigma_\beta(k)|\ge\delta>0$，除法合法）：
$$\widehat{u_\alpha-u_\beta}(k)=\frac{\hat F(k)}{2\pi i}\Big(\frac{1}{\sigma_\alpha(k)}-\frac{1}{\sigma_\beta(k)}\Big)=\frac{(\beta-\alpha)\,k_1}{2\pi i\,\sigma_\alpha(k)\,\sigma_\beta(k)}\,\hat F(k),$$
故由 $|k_1|\le|k|\le N$：
$$|\widehat{u_\alpha-u_\beta}(k)|\le\frac{|\alpha-\beta|\,|k_1|}{2\pi\delta^{2}}|\hat F(k)|\le\frac{|\alpha-\beta|\,N}{2\pi\delta^{2}}|\hat F(k)| .$$
加权求和（$u_\alpha-u_\beta,\ F\in H_N$）：
$$\|u_\alpha-u_\beta\|_{H^r}^2=\sum_{0<|k|\le N}\langle k\rangle^{2r}|\widehat{u_\alpha-u_\beta}(k)|^{2}\le\frac{|\alpha-\beta|^{2}N^{2}}{4\pi^{2}\delta^{4}}\|F\|_{H^r}^{2}. \qquad\blacksquare$$

---

# S4 整体对象与全部恢复目标

**判断摘要.** (A) “对每个无理 $\alpha$，每个 $F$ 可解”不成立；正确分类：可解且唯一 $\iff\alpha\in\mathcal D$，反例对有理与 Liouville 方向分别给出。(B) “对一切 $s$ 估计成立”不成立；正确集合 $\mathcal S_\alpha=\{s:\delta_s(\alpha)>0\}$（非 Diophantine 方向为空集）。（C）$\alpha_*=\sqrt2-1$：最小允许损失 $s=1$，被取到。（D）$C^m$ 估计（损失 $4$）：成立。

## 定理 S4.1（可逆性分类）

对 $\alpha\in\mathbb R$，下列等价：

(i) 每个 $F\in C^\infty_0$ 都有唯一的光滑零均值解 $u$（$N_\alpha u=F$）；
(ii) $N_\alpha:C^\infty_0\to C^\infty_0$ 是线性双射；
(iii) $\alpha\in\mathcal D$（即 $\exists c>0,s\ge0:\ |\sigma_\alpha(k)|\ge c\langle k\rangle^{-s}\ \forall k\ne0$）。

并且：**(a)** $\alpha=p/q\in\mathbb Q$（$q\ge1,\gcd(p,q)=1$）时，$u_0:=e_{(q,-p)}\in C^\infty_0$ 非零而 $N_\alpha u_0=0$（不单），且 $F_0:=e_{(q,-p)}\in C^\infty_0$ **没有任何解**（不满）。**(b)** $\alpha$ 无理而 $\alpha\notin\mathcal D$ 时，$N_\alpha$ 在 $C^\infty_0$ 上单射但不 满（显式 $F$ 构造见证明）。**(c)** $\alpha\in\mathcal D$ 时逆为
$$N_\alpha^{-1}F=\sum_{k\ne0}\frac{\hat F(k)}{2\pi i\,\sigma_\alpha(k)}\,e_k,\qquad F\in C^\infty_0, \tag{4.1}$$
且对无理 $\alpha$，齐次方程 $N_\alpha u=0$ 的光滑解恰为常数，故可解时一般解 $=$ 零均值解 $+$ 常数。

**证明.**

**(iii)$\Rightarrow$(i),(ii),(c).** 设 $\delta_s(\alpha)=c>0$。对 $F\in C^\infty_0$ 令 $u$ 如 (4.1)。与定理 S2 证明 (i) 完全相同（把 $c$ 换成 $\delta_s$）：
$$\sum_{k\ne0}\langle k\rangle^{2m}\Big|\frac{\hat F(k)}{2\pi i\sigma_\alpha(k)}\Big|^2\le(2\pi c)^{-2}\|F\|_{H^{m+s}}^2<\infty\quad\forall m,$$
故由 (P4)(ii) $u\in C^\infty_0$、$N_\alpha u=F$（系数验证 + 单射性）。这给出满射。单射：若 $u\in C^\infty_0,\ N_\alpha u=0$，则 (P1) 给 $2\pi i\sigma_\alpha(k)\hat u(k)=0\ \forall k$；$\alpha\in\mathcal D\Rightarrow\alpha$ 无理（P6），由 (P2) $\sigma_\alpha(k)\ne0\ (k\ne0)$，故 $\hat u(k)=0\ (k\ne0)$，连同 $\hat u(0)=0$ 得 $u=0$。故 (ii)。

**(ii)$\Rightarrow$(i).** 显然：双射给出存在与唯一（原像属于 $C^\infty_0$；任何光滑零均值解也在 $C^\infty_0$ 中故等于原像）。

**(i)$\Rightarrow$(iii).** 设 $\alpha\notin\mathcal D$，分两种情形证明 (i) 失败。

**情形 1：$\alpha=p/q\in\mathbb Q$.** 取 $F_0:=e_{(q,-p)}\in C^\infty_0$。若有 $u\in C^1$ 使 $N_\alpha u=F_0$，则由 (P1) 在 $k=(q,-p)$ 处比较系数：左边 $=2\pi i\cdot0\cdot\hat u(k)=0$，右边 $=1$，矛盾。故 $F_0$ 无解（此处未用零均值，排除得更彻底）。又 $N_\alpha e_{(q,-p)}=2\pi i\,\sigma_\alpha(q,-p)\,e_{(q,-p)}=0$：不单。

**情形 2：$\alpha$ 无理且 $\alpha\notin\mathcal D$**（即 $\forall c>0,\forall s\ge0\ \exists k\ne0:\ |\sigma_\alpha(k)|<c\langle k\rangle^{-s}$）。

*选择引理.* 存在序列 $k^{(j)}\in\mathbb Z^2\setminus\{0\}$（$j\ge1$）使 $|k^{(j)}|\ge j$（从而 $\langle k^{(j)}\rangle\ge j$，且可取 $|k^{(j)}|$ 严格增、两两不同）且
$$|\sigma_\alpha(k^{(j)})|<\langle k^{(j)}\rangle^{-3j}.$$

*引理证明.* 对 $j\ge1$ 归纳（约定 $|k^{(0)}|:=0$）。设已有 $k^{(j-1)}$，令 $L:=\max(j,\ |k^{(j-1)}|+1)$。若 $K_L:=\{k:0<|k|<L\}$ 非空，由 (P2) 与 $\alpha$ 无理，$\mu_L:=\min_{K_L}|\sigma_\alpha|>0$；因 $K_L$ 有限且每个 $\langle k\rangle\ge\sqrt2>1$，可取 $s^*\ge3j$ 充分大使 $\langle k\rangle^{-s^*}<\mu_L\ \forall k\in K_L$。由 $\alpha\notin\mathcal D$（取 $c=1$），存在 $k\ne0$ 使 $|\sigma_\alpha(k)|<\langle k\rangle^{-s^*}$。此 $k\notin K_L$（否则 $\mu_L\le|\sigma_\alpha(k)|<\langle k\rangle^{-s^*}<\mu_L$），故 $|k|\ge L\ge j$ 且 $|k|>|k^{(j-1)}|$；又 $s^*\ge3j,\ \langle k\rangle\ge1$ 给 $|\sigma_\alpha(k)|<\langle k\rangle^{-3j}$。置 $k^{(j)}:=k$。$\square$

*构造.* 令 $a_j:=\langle k^{(j)}\rangle^{-j}$，$F:=\sum_{j\ge1}a_je_{k^{(j)}}$。对每个 $m\in\mathbb N_0$：
$$\sum_{j\ge1}a_j\,(2\pi)^m\langle k^{(j)}\rangle^{m}=(2\pi)^m\sum_{j\ge1}\langle k^{(j)}\rangle^{m-j},$$
其中 $j\ge m+2$ 的项 $\le\langle k^{(j)}\rangle^{-2}\le j^{-2}$（用 $\langle k^{(j)}\rangle\ge j$），$j<m+2$ 只有有限项。由 M-判别法（(P4)(ii) 型论证），$F\in C^\infty$，频率两两不同故 $\hat F(k^{(j)})=a_j$、其余 $\hat F=0$；特别 $\hat F(0)=0$，$F\in C^\infty_0$。

*无解.* 反设 $u\in L^1$（特别地，$u\in C^\infty$）按分布意义满足 $N_\alpha u=F$（此时 (P1) 的系数等式对分布成立）。对每个 $j$，在 $k^{(j)}$ 处：
$$2\pi|\sigma_\alpha(k^{(j)})|\,|\hat u(k^{(j)})|=a_j
\ \Longrightarrow\
|\hat u(k^{(j)})|=\frac{a_j}{2\pi|\sigma_\alpha(k^{(j)})|}>\frac{\langle k^{(j)}\rangle^{-j}}{2\pi\langle k^{(j)}\rangle^{-3j}}=\frac{\langle k^{(j)}\rangle^{2j}}{2\pi}\ge\frac{j^{2j}}{2\pi}\to\infty,$$
与 $|\hat u(k)|\le\|u\|_{L^1}<\infty$（(P1)）矛盾。故 $F$ 无任何 $L^1$ 解，更无光滑零均值解，$N_\alpha$ 不满。$\blacksquare$

## 定理 S4.2（损失指数的完全分类）

设 $\alpha\in\mathbb R,\ s\ge0$。下列等价：

(1) 对每个 $r\in\mathbb R$ 存在 $C<\infty$ 使 $\|u\|_{H^r}\le C\|N_\alpha u\|_{H^{r+s}}$ 对一切 $u\in C^\infty_0$；
(2) 存在某个 $r$ 与 $C$ 使上式成立；
(3) $\delta_s(\alpha)>0$。

当 (3) 成立时，可取与 $r$ 无关的最优常数 $C_{\alpha,r,s}=(2\pi\delta_s(\alpha))^{-1}$（对一切 $r$ 同一常数，任何可行常数 $\ge$ 它）。因此
$$\mathcal S_\alpha:=\{s\ge0:\text{(1) 成立}\}=\{s\ge0:\delta_s(\alpha)>0\}$$
为上行集合，且由 (P6)(a)，$\mathcal S_\alpha\subseteq[1,\infty)$；$\mathcal S_\alpha\ne\emptyset\iff\alpha\in\mathcal D$，此时 $\mathcal S_\alpha=[s_\alpha,\infty)$ 或 $(s_\alpha,\infty)$，$s_\alpha:=\inf\mathcal S_\alpha\in[1,\infty)$。若 $\alpha\notin\mathcal D$（含一切有理数与 Liouville 无理数），则 $\mathcal S_\alpha=\emptyset$：任何损失都不行。

**证明.** (3)$\Rightarrow$(1)：设 $\delta:=\delta_s(\alpha)>0$。对 $u\in C^\infty_0$（$\hat u(0)=0$，$\widehat{N_\alpha u}(0)=0$），由 (P1)（对任意实 $r$ 权重为正，恒等式逐项成立）：
$$\|N_\alpha u\|_{H^{r+s}}^2=\sum_{k\ne0}\langle k\rangle^{2(r+s)}\,4\pi^2\sigma_\alpha(k)^2\,|\hat u(k)|^2\ge4\pi^2\delta^2\sum_{k\ne0}\langle k\rangle^{2r}|\hat u(k)|^2=(2\pi\delta)^2\|u\|_{H^r}^2 .$$
故 $\|u\|_{H^r}\le(2\pi\delta)^{-1}\|N_\alpha u\|_{H^{r+s}}$，常数与 $r$ 无关。

(2)$\Rightarrow$(3)：设某 $r,C$ 使估计成立。对每个 $k\ne0$ 取 $u:=e_k\in C^\infty_0$（零均值）：$\|e_k\|_{H^r}=\langle k\rangle^r$，$\|N_\alpha e_k\|_{H^{r+s}}=2\pi|\sigma_\alpha(k)|\langle k\rangle^{r+s}$（单一频率）。代入得
$$\langle k\rangle^{s}|\sigma_\alpha(k)|\ge(2\pi C)^{-1}\qquad\forall k\ne0,$$
即 $\delta_s(\alpha)\ge(2\pi C)^{-1}>0$。(1)$\Rightarrow$(2) 平凡。最优常数由 (2)$\Rightarrow$(3) 的论证（任何可行 $C$ 满足 $C\ge(2\pi\delta_s)^{-1}$）与 (3)$\Rightarrow$(1) 得。结构断言：上行性由 $\delta_s$ 关于 $s$ 单调（$\langle k\rangle\ge1$）；$\mathcal S_\alpha\subseteq[1,\infty)$ 由 (P6)(a)；上行集合若非空，则恰为其下确界处含或不含下确界的两种区间形式。$\blacksquare$

> 注：当 $\delta_s(\alpha)=0$ 时，对**每个** $r$ 与每个 $C$，估计都被某个单频 $u=e_k$ 破坏（取 $\langle k\rangle^s|\sigma_\alpha(k)|<(2\pi C)^{-1}$ 即可，因下确界为 $0$）。失败方式一致。

## 定理 S4.3（$\alpha_*=\sqrt2-1$：最小损失为 $s=1$，被取到）

$$\delta_1(\alpha_*)\ge\tfrac14>0,\qquad \delta_s(\alpha_*)=0\quad(s<1),\qquad\text{故}\quad\mathcal S_{\alpha_*}=[1,\infty).$$
即：最小允许损失为 $s=1$，且**被取到**（$s=1$ 可行，最优常数 $(2\pi\delta_1(\alpha_*))^{-1}\le2/\pi$，与 $r$ 无关；任何 $s<1$ 对任何 $r$、任何常数都失败）。

**证明.** 记 $\alpha:=\alpha_*=\sqrt2-1$，其共轭 $\alpha':=-\sqrt2-1$：$\alpha\alpha'=-1,\ \alpha+\alpha'=-2$。对 $k\in\mathbb Z^2$：
$$\sigma_\alpha(k)\sigma_{\alpha'}(k)=(\alpha k_1+k_2)(\alpha'k_1+k_2)=\alpha\alpha'k_1^2+(\alpha+\alpha')k_1k_2+k_2^2=k_2^2-2k_1k_2-k_1^2\in\mathbb Z .$$
若其为 $0$，视作 $k_2$ 的二次方程得 $k_2=k_1\pm\sqrt2\,k_1$；整数解仅可能 $k_1=0$（否则 $\sqrt2\in\mathbb Q$），进而 $k_2=0$。故 $k\ne0$ 时 $|\sigma_\alpha(k)\sigma_{\alpha'}(k)|\ge1$。又 $|\alpha'|=\sqrt2+1<\tfrac52$，故
$$|\sigma_{\alpha'}(k)|\le\tfrac52|k_1|+|k_2|\le\tfrac52(|k_1|+|k_2|)\le\tfrac{5\sqrt2}{2}|k|\le4\langle k\rangle$$
（用 $|k_1|+|k_2|\le\sqrt2|k|$，$|k|\le\langle k\rangle$，$\tfrac{5\sqrt2}2<4$）。于是
$$|\sigma_\alpha(k)|\ge\frac{1}{4\langle k\rangle}\qquad(k\ne0),\qquad\text{即 }\delta_1(\alpha_*)\ge\tfrac14 .$$

反之取 Pell 序列：$p_n+q_n\sqrt2=(1+\sqrt2)^n$（$n\ge1$）。归纳（乘 $1+\sqrt2$ 把 $a+b\sqrt2$ 映为 $(a+2b)+(a+b)\sqrt2$）知 $p_n,q_n\in\mathbb Z_{>0}$；范数可乘给 $p_n^2-2q_n^2=(-1)^n$；$q_{n+1}=p_n+q_n\ge q_n+1\Rightarrow q_n\to\infty$；$p_n^2=2q_n^2\mp1\le4q_n^2\Rightarrow p_n\le2q_n$。令 $k^{(n)}:=(q_n,\ q_n-p_n)$，则
$$\sigma_{\alpha_*}(k^{(n)})=(\sqrt2-1)q_n+q_n-p_n=\sqrt2q_n-p_n,\qquad |\sqrt2q_n-p_n|=\frac{|2q_n^2-p_n^2|}{\sqrt2q_n+p_n}=\frac{1}{\sqrt2q_n+p_n}\le\frac{1}{\sqrt2\,q_n},$$
且 $|k^{(n)}|\le q_n+|q_n-p_n|\le2q_n+p_n\le4q_n$。故对 $s<1$：
$$\langle k^{(n)}\rangle^{s}|\sigma_{\alpha_*}(k^{(n)})|\le(4q_n)^{s}\cdot\frac{1}{\sqrt2q_n}=\frac{4^{s}}{\sqrt2}\,q_n^{s-1}\xrightarrow[n\to\infty]{}0 ,$$
即 $\delta_s(\alpha_*)=0$（$s<1$）。结合单调性（$s\ge1\Rightarrow\delta_s\ge\delta_1\ge\tfrac14>0$）得 $\mathcal S_{\alpha_*}=[1,\infty)$。$\blacksquare$

## 定理 S4.4（$C^m$ 估计，损失 $4$：**成立**）

是。对每个 $m\in\mathbb N_0$，常数
$$C_m:=(2\pi)^m\,\frac{2^{m+4}S_3}{2\pi\,\delta_1(\alpha_*)}\ \le\ (2\pi)^m\,\frac{2^{m+5}}{\pi}\,S_3\ <\ \infty\qquad\Big(S_3=\sum_{k\ne0}\langle k\rangle^{-3}<\infty,\ \delta_1(\alpha_*)\ge\tfrac14\Big)$$
满足
$$\|N_{\alpha_*}^{-1}F\|_{C^m}\le C_m\,\|F\|_{C^{m+4}}\qquad\forall F\in C^\infty_0 .$$
（$N_{\alpha_*}^{-1}F$ 良定义：由 S4.1、S4.3，$\alpha_*\in\mathcal D$，$N_{\alpha_*}^{-1}F$ 即 $F$ 的唯一光滑零均值解 (4.1)。）

**证明.** 简记 $\alpha:=\alpha_*,\ \delta_1:=\delta_1(\alpha_*)\ge\tfrac14$。由 (4.1) 与 $|\sigma_\alpha(k)|\ge\delta_1\langle k\rangle^{-1}$：
$$\hat u(k)=\frac{\hat F(k)}{2\pi i\,\sigma_\alpha(k)}\ (k\ne0),\qquad \hat u(0)=0,\qquad |\hat u(k)|\le\frac{\langle k\rangle}{2\pi\delta_1}|\hat F(k)|,\qquad u:=N_{\alpha_*}^{-1}F. \tag{4.2}$$
序列 $\hat u$ 满足 (P4)(ii) 的假设：对每个 $m$，$\sum_k\langle k\rangle^{2m}|\hat u(k)|^2\le(2\pi\delta_1)^{-2}\|F\|_{H^{m+1}}^2<\infty$（(P4)(iii)）。故由 (P4')（$j=m$）：
$$\|u\|_{C^m}\le(2\pi)^m\sum_{k\ne0}\langle k\rangle^{m}|\hat u(k)|\le\frac{(2\pi)^m}{2\pi\delta_1}\sum_{k\ne0}\langle k\rangle^{m+1}|\hat F(k)| .$$
由 (P4)（取 $D=m+4$）：$|\hat F(k)|\le2^{m+4}\|F\|_{C^{m+4}}\langle k\rangle^{-(m+4)}$（$k\ne0$）。故
$$\sum_{k\ne0}\langle k\rangle^{m+1}|\hat F(k)|\le2^{m+4}\|F\|_{C^{m+4}}\sum_{k\ne0}\langle k\rangle^{-3}=2^{m+4}S_3\,\|F\|_{C^{m+4}},$$
其中 $S_3<\infty$（(P3)，$3>2=$ 维数）。代入即得结论。$\blacksquare$

> **注（正则性理论综述）.** 同法对一般 $\alpha\in\mathcal D$（$\delta_s(\alpha)>0$）给 $\|N_\alpha^{-1}F\|_{C^m}\le(2\pi)^m2^{D}S_3(2\pi\delta_s)^{-1}\|F\|_{C^{D}}$，$D=m+\lceil s\rceil+3$。对 $\alpha_*$：$s=1,\ D=m+4$，损失 $4=1$（算术损失，由 S4.3 不可再降）$+3$（二维格点余量：需 $\sum\langle k\rangle^{-t}<\infty$ 即 $t>2$，此处 $t=3$；若尝试 $D=m+3$ 则相应和为 $\sum\langle k\rangle^{-2}$，发散——该方法在 $m+3$ 处失效，但本题只须判定损失 $4$，结论为成立）。Sobolev 层面：$\|N_\alpha^{-1}F\|_{H^r}\le(2\pi\delta_s)^{-1}\|F\|_{H^{r+s}}$，最小损失即 $\alpha$ 的 Diophantine 型 $s_\alpha\ge1$（(P6)(a)），对 $\alpha_*$ 恰为 $1$ 且取到。两类区间 $[s_\alpha,\infty)$（如一切二次无理数）与 $(s_\alpha,\infty)$（如 Lebesgue-a.e. $\alpha$，标准度量丢番图逼近结果，此处不证）都出现。$N_\alpha$ 是常向量场 $(\alpha,1)$ 方向导数，上述即线性流上小除数上闭方程的经典理论。

---

# S5 邻近方向的一致估计

**定理 S5.** **不存在。** 即：不存在开区间 $J\ni\alpha_*=\sqrt2-1$、有限 $s\ge0$ 与 $C<\infty$，使对每个无理 $\alpha\in J$ 与每个 $u\in C^\infty_0$ 都有 $\|u\|_{L^2}\le C\|N_\alpha u\|_{H^s}$。事实上，对**任意**非空开区间 $J\subset\mathbb R$、任意 $s\ge0$、任意 $C<\infty$ 都失败；且反例中的 $\alpha$ 还可取为二次无理数（badly approximable，$\delta_1(\alpha)>0$）。

**证明.** 反设 $(J,s,C)$ 满足要求。取有理数 $\frac pq\in J$（$q\ge1$；$\mathbb Q$ 稠密）。记 $k^0:=(q,-p)\ne0$，$K:=\langle k^0\rangle\ge\sqrt2\ge1$。$J$ 开，故有 $d>0$ 使 $(p/q-d,\ p/q+d)\subset J$。取无理数 $\eta$ 使
$$0<|\eta|<\min\Big(d,\ \frac{1}{2\pi CqK^{s}}\Big)$$
（例如 $\eta=\sqrt2\,\varepsilon$，$\varepsilon\in\mathbb Q_{>0}$ 充分小：非零有理数乘 $\sqrt2$ 为无理数）。令
$$\alpha:=\frac pq+\eta\in J .$$
则 $\alpha$ 无理（有理 $+$ 无理 $=$ 无理）；若取 $\eta=\sqrt2\varepsilon$，则 $\alpha\in\mathbb Q(\sqrt2)\setminus\mathbb Q$ 是二次无理数。取 $u:=e_{k^0}\in C^\infty_0$（$k^0\ne0$ 故零均值），则 $\|u\|_{L^2}=1$，且由 (P1)（单一频率）：
$$\|N_\alpha u\|_{H^s}=2\pi|\sigma_\alpha(k^0)|\,\langle k^0\rangle^{s}=2\pi|q\alpha-p|\,K^{s}=2\pi q|\eta|\,K^{s}<2\pi q\cdot\frac{1}{2\pi CqK^{s}}\cdot K^{s}=\frac1C .$$
于是 $C\|N_\alpha u\|_{H^s}<1=\|u\|_{L^2}$，与假设矛盾。$\blacksquare$

> 注：失效机理是每个有理方向 $p/q$ 在频率 $(q,-p)$ 处**精确共振**，而有理数稠密，故任何开区间内都有任意接近共振的无理方向；即使限于 badly approximable 方向（$\eta=\sqrt2\varepsilon$ 型反例仍是二次无理数），一致常数也必然随方向退化。

---

# S6 一个具体方向的不可解数据

**定理 S6.** 令 $\alpha:=\sum_{n=1}^{\infty}10^{-n!}$。则：

**(1) $\alpha$ 无理.**

**(2)** 令 $Q_N:=10^{N!},\ P_N:=\sum_{n=1}^{N}10^{N!-n!}\in\mathbb Z,\ k^{(N)}:=(Q_N,-P_N)$，并定义
$$F(y):=\sum_{N=1}^{\infty}\langle k^{(N)}\rangle^{-N/2}\,e^{2\pi i\,(Q_Ny_1-P_Ny_2)} .$$
则 $F\in C^\infty_0(\mathbb T^2)$，且 $N_\alpha u=F$ **没有任何 $L^1$ 解**（特别没有光滑零均值解）。这是同一个显式给出的 $F$，它同时否定一切正则性层面的可解性，无需对各个估计分别选取频率。

**证明.**

**(1)** 对 $N\ge1$：$P_N/Q_N=\sum_{n=1}^N10^{-n!}$，且（尾项指数 $n!\ (n\ge N+1)$ 两两至少差 $1$，首项为 $(N+1)!$，故不超过几何级数）
$$0<\alpha-\frac{P_N}{Q_N}=\sum_{n\ge N+1}10^{-n!}\le10^{-(N+1)!}\sum_{j\ge0}10^{-j}=\frac{10}{9}\,10^{-(N+1)!}=\frac{10}{9}\,Q_N^{-(N+1)}, \tag{6.1}$$
其中用了 $10^{(N+1)!}=(10^{N!})^{N+1}=Q_N^{N+1}$。若 $\alpha=\frac ab\in\mathbb Q$（$b\ge1$），则对每个 $N$ 有 $\frac ab\ne\frac{P_N}{Q_N}$（差为正），故 $aQ_N-bP_N\in\mathbb Z\setminus\{0\}$ 给
$$\frac{1}{bQ_N}\le\Big|\frac ab-\frac{P_N}{Q_N}\Big|\le\frac{10}{9}Q_N^{-(N+1)}\quad\Longrightarrow\quad Q_N^{N}\le\frac{10b}{9}\quad\forall N,$$
即 $10^{N\cdot N!}\le\frac{10b}9$ 对一切 $N$，荒谬（左端 $\to\infty$）。故 $\alpha$ 无理。同时由 (6.1) 乘 $Q_N$ 得关键逼近式
$$0<\sigma_\alpha(k^{(N)})=Q_N\alpha-P_N\le\frac{10}{9}\,Q_N^{-N}\qquad(N\ge1). \tag{6.2}$$

**(2)** 尺寸估计：$P_N=\sum_{n=1}^N10^{N!-n!}\le N\cdot10^{N!-1}=\frac N{10}Q_N$，故（$1+\frac N{10}\le2N$ 对 $N\ge1$；$\sqrt{1+4N^2Q_N^2}\le\sqrt8\,NQ_N\le3NQ_N$，用 $1\le4N^2Q_N^2$）
$$Q_N\le|k^{(N)}|\le Q_N+P_N\le2NQ_N,\qquad \langle k^{(N)}\rangle\le3NQ_N,\qquad \langle k^{(N)}\rangle\ge Q_N=10^{N!}\ge10^{N}. \tag{6.3}$$
$Q_N$ 严格增，故频率 $k^{(N)}$ 两两不同且均非零。

**$F\in C^\infty_0$：** 对每个 $m\in\mathbb N_0$，
$$\sum_{N\ge1}\langle k^{(N)}\rangle^{-N/2}\,(2\pi)^m\langle k^{(N)}\rangle^{m}=(2\pi)^m\sum_{N\ge1}\langle k^{(N)}\rangle^{m-N/2},$$
其中 $N\ge2m+4$ 的项 $\le\langle k^{(N)}\rangle^{-2}\le10^{-2N!}\le10^{-2N}$（可和），其余有限项。由 M-判别法，级数连同各阶导数绝对一致收敛，故 $F\in C^\infty$；逐项积分给 $\hat F(k^{(N)})=\langle k^{(N)}\rangle^{-N/2}$，其余 $\hat F=0$；特别 $\hat F(0)=0$，即 $F\in C^\infty_0$。

**无解：** 反设 $u\in L^1(\mathbb T^2)$ 按分布意义满足 $N_\alpha u=F$（$u\in C^\infty$ 时由 (P1) 古典成立；系数等式对分布成立）。在每个 $k^{(N)}$ 处比较系数，并用 (6.2)（其中 $\sigma_\alpha(k^{(N)})>0$，可除）：
$$|\hat u(k^{(N)})|=\frac{\langle k^{(N)}\rangle^{-N/2}}{2\pi\,\sigma_\alpha(k^{(N)})}\ \ge\ \frac{\langle k^{(N)}\rangle^{-N/2}}{2\pi\cdot\frac{10}{9}Q_N^{-N}}=\frac{9}{20\pi}\,Q_N^{N}\,\langle k^{(N)}\rangle^{-N/2} .$$
由 (6.3)，$\langle k^{(N)}\rangle^{N/2}\le(3NQ_N)^{N/2}$，故
$$|\hat u(k^{(N)})|\ \ge\ \frac{9}{20\pi}\Big(\frac{Q_N}{3N}\Big)^{N/2}.$$
而 $Q_N=10^{N!}\ge10^{N}$，故 $N\ge2$ 时 $\frac{Q_N}{3N}\ge\frac{100}{6}>16$，从而
$$|\hat u(k^{(N)})|\ \ge\ \frac{9}{20\pi}\,4^{N}\ \xrightarrow[N\to\infty]{}\ \infty ,$$
与 $|\hat u(k)|\le\|u\|_{L^1}<\infty$（(P1)，测度为 $1$）矛盾。故不存在 $L^1$ 解，更不存在光滑零均值解。$\blacksquare$

> 注：(6.1) 同时表明 $\alpha$ 是 Liouville 数：对每个 $s\ge0$，$\delta_s(\alpha)=0$（沿 $k^{(N)}$：$\langle k^{(N)}\rangle^{s}\sigma_\alpha(k^{(N)})\le(3NQ_N)^{s}\cdot\frac{10}{9}Q_N^{-N}\to0$）。这与 S4.1/S4.2 的分类吻合：正因 $\alpha\notin\mathcal D$，才存在此类不可解数据；而上述构造中 $|\hat u(k^{(N)})|\to\infty$，故这同一个 $F$ 使方程在 $L^1$ 层面即不可解，从而同时破坏一切 $H^r$、$C^m$ 层面的可解性与先验估计。