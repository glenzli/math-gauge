KEEP

### 本轮核查依据说明

经严格核查，本轮重点断言（“存在含指定方向 $\alpha_* = \sqrt{2}-1$ 的邻域和一个有限阶数及有限常数，使邻域内所有无理方向共同满足题定 Sobolev 逆估计”）**不成立**。维持原答卷的判定与论证，核查核心依据如下：

1. **单模测试导出的必要条件**：
   若存在开区间 $J \ni \alpha_*$、有限 $s \ge 0$ 及常数 $C < \infty$，使得对每个无理数 $\alpha \in J$ 及每个 $u \in C_0^\infty(\mathbb T^2)$ 均有 $\|u\|_{L^2} \le C \|N_\alpha u\|_{H^s}$，则对任意非零整频率 $k = (k_1, k_2) \in \mathbb Z^2 \setminus \{0\}$，选取单模测试函数 $u_k(y) = e^{2\pi i k \cdot y} \in C_0^\infty(\mathbb T^2)$。
   计算得 $\|u_k\|_{L^2} = 1$ 且 $\|N_\alpha u_k\|_{H^s} = 2\pi |\alpha k_1 + k_2| \langle k \rangle^s$。由此必须对每个无理数 $\alpha \in J$ 及每个 $k \ne 0$ 一致成立算术下界：
   $$|\alpha k_1 + k_2| \ge \frac{1}{2\pi C} \langle k \rangle^{-s}.$$

2. **邻近有理点的显式破坏构造（明确引用前版 S5 论据）**：
   对任意包含 $\alpha_*$ 的开区间 $J$，由有理数稠密性，必存在有理数 $p/q \in J$（$q \in \mathbb N, p \in \mathbb Z$）。固定非零频率 $k^* = (q, -p)$，此时 $\langle k^* \rangle$ 为确定的有限常数。
   对于参数 $\varepsilon > 0$，定义方向 $\alpha_\varepsilon = \frac{p}{q} + \frac{\varepsilon}{\sqrt{2}}$。由于 $\sqrt{2} \notin \mathbb Q$，$\alpha_\varepsilon$ 必为无理数。
   只要选取充分小的 $\varepsilon > 0$，使得 $\alpha_\varepsilon \in J$ 且
   $$0 < \varepsilon < \frac{\sqrt{2}}{4\pi C q \langle k^* \rangle^s},$$
   则在该无理方向 $\alpha_\varepsilon$ 下，对应的小除数为：
   $$|\alpha_\varepsilon k_1^* + k_2^*| = \frac{q\varepsilon}{\sqrt{2}} < \frac{1}{4\pi C} \langle k^* \rangle^{-s} < \frac{1}{2\pi C} \langle k^* \rangle^{-s},$$
   直接违背了一致 Sobolev 逆估计导出的必要条件。

3. **Liouville 数的拓扑稠密性阻碍**：
   任何非空开区间 $J \subset \mathbb R$ 内均包含稠密的 Liouville 数集（无理性测度为无穷的无理数）。对任意给定的 Liouville 数 $\alpha \in J$ 及任意有限 $s \ge 0$，均有
   $$\inf_{k \in \mathbb Z^2 \setminus \{0\}} |\alpha k_1 + k_2| \langle k \rangle^s = 0.$$
   因此不存在任何有限常数 $C$ 能使单个 Liouville 数方向满足该估计，更不可能在含开区间的所有无理方向上一致成立。

综上，S5 的正确结论为**不存在**满足要求的一致开邻域与指标；原答卷 S1 至 S6 各阶段证明、分类与构造均完全正确且论证严密，故维持上一版完整答卷。
