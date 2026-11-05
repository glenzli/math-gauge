KEEP

### 本轮核查依据与数学主张

经对上一版答卷（S1 至 S6）进行逐项严格数学核查，上一版答卷全部结论、构造与论证完全正确无误。本轮重点断言（**“存在含指定方向的邻域和一个有限阶数及有限常数，使邻域内所有无理方向共同满足题定 Sobolev 逆估计”**）在数学上**不成立**。维持上一版答卷的结论（即**不存在**满足要求的开区间 $J$、有限阶数 $s \ge 0$ 及常数 $C < \infty$）。具体核查依据如下：

#### 1. 重点断言（S5）的严格核查
- **频率测试与必要条件**（明确引用上一版答卷 S5 步骤 1）：
  若存在开区间 $J \ni \alpha_*$、有限 $s \ge 0$ 及常数 $C < \infty$ 使得 $\|u\|_{L^2} \le C \|N_\alpha u\|_{H^s}$ 对所有无理数 $\alpha \in J$ 及所有 $u \in C_0^\infty(\mathbb T^2)$ 成立，则对任意固定非零频率 $k = (k_1, k_2) \in \mathbb Z^2 \setminus \{0\}$，代入单模测试函数 $u_k(y) = e^{2\pi i k \cdot y} \in C_0^\infty(\mathbb T^2)$（满足 $\|u_k\|_{L^2} = 1$ 且 $\|N_\alpha u_k\|_{H^s} = 2\pi |\alpha k_1 + k_2| \langle k \rangle^s$），必然导出小除数必须满足下界：
  $$|\alpha k_1 + k_2| \ge \frac{1}{2\pi C} \langle k \rangle^{-s} \qquad (\forall \alpha \in J \setminus \mathbb Q,\ \forall k \in \mathbb Z^2 \setminus \{0\}).$$
- **有理逼近直接击穿一致界**（明确引用上一版答卷 S5 步骤 2）：
  由于实数开区间 $J \subset \mathbb R$ 必含有理数，任取有理点 $p/q \in J$（$q \in \mathbb N, p \in \mathbb Z$），取固定整频率 $k^* = (q, -p) \ne (0,0)$。考虑无理数序列 $\alpha_n = \frac{p}{q} + \frac{1}{n\sqrt{2}}$：当 $n$ 充分大时 $\alpha_n \in J \setminus \mathbb Q$。但在该固定频率 $k^*$ 处，其小除数绝对值为：
  $$|\alpha_n k_1^* + k_2^*| = \left| \alpha_n q - p \right| = \frac{q}{n\sqrt{2}} \xrightarrow{n \to \infty} 0.$$
  由于频率 $k^*$ 固定，右端 $\frac{1}{2\pi C} \langle k^* \rangle^{-s} > 0$ 为固定的严格正数。只要取 $n > \sqrt{2} \pi C q \langle k^* \rangle^s$，小除数即可小于该正数，直接导致上述必要条件破除。
- **区间内 Liouville 数的存在性**：
  任意开区间 $J$ 内均包含不可数个 Liouville 数。对于任意单个 Liouville 数 $\alpha \in J \setminus \mathbb Q$，由定义不存在任何有限的 $(C, s)$ 使该算术下界成立，因而在单个方向上即不存在这样的 Sobolev 逆估计，更不可能在整个无理子集 $J \setminus \mathbb Q$ 上一致成立。
- 因此，重点断言不成立，原答卷 S5 结论“不存在”与证明完全严密正确。

#### 2. 原答卷其余各阶段（S1–S4、S6）核查
- **S1**：有限频带 $H_N$ 上特征值 $2\pi i(\alpha k_1 + k_2) \ne 0$ 的非奇异性成立，显式逆算子与 $H^r \to H^r$ 逆范数精确式 $\frac{1}{2\pi \min_{0 < |k| \le N} |\alpha k_1 + k_2|}$ 推导准确。
- **S2**：在算术下界 $|\alpha k_1 + k_2| \ge c\langle k \rangle^{-s}$ 下，光滑解构造、快速衰减性及截断误差上界 $(2\pi c)^{-1} (1+N^2)^{-q/2} \|F\|_{H^{r+s+q}}$ 严密无误。
- **S3**：方向扰动差项代数分解 $\frac{1}{\alpha k_1 + k_2} - \frac{1}{\beta k_1 + k_2} = \frac{(\beta - \alpha) k_1}{(\alpha k_1 + k_2)(\beta k_1 + k_2)}$ 与范数估计 $| \alpha - \beta | N (2\pi \delta^2)^{-1} \|F\|_{H^r}$ 论证确凿。
- **S4**：可逆性充要条件完全刻画为 Diophantine 数；允许的损失指标集精确等价于算术下界指数；坏逼近数 $\alpha_* = \sqrt{2}-1$ 的最小损失确为 $s_{\min} = 1$ 且可取到；基于分部积分与 $\sum \langle k \rangle^{-3} < \infty$ 的连续可微模估计 $\|N_{\alpha_*}^{-1} F\|_{C^m} \le C_m \|F\|_{C^{m+4}}$ 构造完整。
- **S6**：Liouville 数 $\alpha = \sum_{n=1}^\infty 10^{-n!}$ 的无理性证明完整；单一检验函数 $F(y) = \sum_{m=2}^\infty 10^{-\frac{1}{2}m \cdot m!} e^{2\pi i(q_m y_1 - p_m y_2)}$ 满足光滑零均值，且形式解 Fourier 模长趋于无穷，确证无连续/光滑解。

综上，维持原答卷的全部结论与证明。
