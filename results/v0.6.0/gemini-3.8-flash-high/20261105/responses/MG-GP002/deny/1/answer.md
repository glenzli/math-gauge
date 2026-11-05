KEEP

### 本轮核查依据说明

维持上一版全套解答（S1–S6），结论与论证均无需修改。针对本轮重点断言（S5），核查结论及确定数学主张如下：

1. **确定数学主张（S5 结论：不存在一致先验估计）**
   本轮所给重点断言“*存在含指定方向的邻域和一个有限阶数及有限常数，使邻域内所有无理方向共同满足题定 Sobolev 逆估计*”**确实不成立**，这与上一版答卷中 S5 的结论（**不存在** 满足要求的开区间 $J\ni\alpha_*$、有限 $s\ge0$ 及常数 $C<\infty$）完全一致。

2. **核心核查依据**
   - **单模测试与必要条件**：若存在开区间 $J\ni\alpha_*$、有限 $s\ge0$ 及 $C<\infty$ 使得 $\|u\|_{L^2}\le C\|N_\alpha u\|_{H^s}$ 对所有无理数 $\alpha\in J$ 与 $u\in C_0^\infty(\mathbb T^2)$ 成立，取单频测试函数 $u_k(y)=e^{2\pi i k\cdot y}$（$k\in\mathbb Z^2\setminus\{0\}$），立得必要条件：
     $$|\alpha k_1 + k_2| \ge \frac{1}{2\pi C}\langle k\rangle^{-s} \qquad (\forall \alpha\in J\setminus\mathbb Q,\ \forall k\in\mathbb Z^2\setminus\{0\}).$$
   - **有理逼近与微扰反例**：由于 $\mathbb Q$ 在开区间 $J$ 中稠密，可在 $J$ 内取有理点 $p/q\in J$（$q\in\mathbb N, p\in\mathbb Z$），并固定频点 $k^*=(q,-p)\ne0$。构造无理方向列 $\alpha_\varepsilon = p/q + \varepsilon/\sqrt{2}$。对充分小的 $\varepsilon>0$，$\alpha_\varepsilon\in J\setminus\mathbb Q$，其对应的小除数为：
     $$|\alpha_\varepsilon k_1^* + k_2^*| = \frac{q\varepsilon}{\sqrt{2}}.$$
     当 $\varepsilon \to 0^+$ 时该小除数趋于 0，必严格小于固定的正下界 $\frac{1}{2\pi C}\langle k^*\rangle^{-s}$，产生矛盾。此外，$J$ 内包含不可数个 Liouville 数，在任意 Liouville 方向上有限损失 Sobolev 估计均不成立。

3. **其余各阶段（S1–S4、S6）复核确认**
   - **S1**：$N_\alpha$ 在 $H_N$ 上的逆算子及 $H^r\to H^r$ 逆范数精确式 $(2\pi \min_{0<|k|\le N}|\alpha k_1+k_2|)^{-1}$ 严格成立且与 $r$ 无关；
   - **S2**：基于频带截断的高频尾项估计与二项权展开，截断误差界 $(2\pi c)^{-1}(1+N^2)^{-q/2}\|F\|_{H^{r+s+q}}$ 严格无误；
   - **S3**：利用代数差式变形与频率模长控制，方向微扰估计 $|\alpha-\beta|N(2\pi\delta^2)^{-1}\|F\|_{H^r}$ 严格无误；
   - **S4**：可逆性充要于 Diophantine 性；正则性损失参数集与坏逼近数性质刻画完全正确；$\alpha_*=\sqrt{2}-1$ 的最小损失指标 $s_{\min}=1$ 且可取到；$C^m\to C^{m+4}$ 控制通过二维环面上模长和的收敛性严格成立；
   - **S6**：Liouville 常数 $\alpha=\sum_{n=1}^\infty 10^{-n!}$ 的无理性证明完整，单一光滑零均值数据 $F$ 的构造与 Fourier 系数发散性论证完备。
