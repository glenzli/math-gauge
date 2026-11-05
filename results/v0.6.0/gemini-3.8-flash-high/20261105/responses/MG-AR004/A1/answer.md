本审阅意见基于原题 [original-task.md](file:///private/tmp/math-gauge-answer-review-exam-20261103/gemini/sessions/MG-AR004-A1/1/work/original-task.md) 与待审答卷 [original-answer.md](file:///private/tmp/math-gauge-answer-review-exam-20261103/gemini/sessions/MG-AR004-A1/1/work/original-answer.md) 的对照核查。

---

## 总体审阅结论

待审答卷在 **S2、S3、S4、S6** 的作答结论正确、论证详实、反例构造符合全部前提；但在 **S1** 与 **S5** 存在严重的**数学断言错误、概念混淆与证明断层**。
因此，答卷在原题条件下**不完全正确，且证明不完整**。

---

## 分项逐题审阅意见

### S1 层的半局部拼接
- **等化子证明**：**正确、完整**。
  - 构造了指标有向族 $\mathcal{I} = \prod_{i=1}^n \mathcal{I}_{x_i}$，说明了 $\mathbf{U} \mapsto \bigcup U_i$ 在 $\Sigma$ 开邻域系统中的余终性。
  - 利用了阿贝尔群范畴 $\mathrm{Ab}$ 中滤过余极限与有限极限（有限积与等化子）可交换的正合性，推导严谨。
- **说明 $S_i$ 不必是开子概形**：**存在局部断言错误**。
  - **答卷断言**：在“拓扑层面”声称当 $\dim\mathcal{O}_{X, x_i} \ge 1$ 且 $n \ge 2$ 时 $S_i$ 绝不是开子集；在“概形层面”断言“当 $\dim\mathcal{O}_{X, x_i} \ge 1$ 时，局部环 $\mathcal{O}_{X, x_i}$ 作为 $\mathcal{O}_{X, \Sigma}$-代数不是有限生成的，故不是有限型的，因而不是开子概形”。
  - **可核查依据**：当相对维数 $\dim X = 1$（如光滑代数曲线）且 $n \ge 2$ 时，半局部环 $\mathcal{O}_{X, \Sigma}$ 是主理想整环（PID）。设其极大理想为 $\mathfrak{m}_1, \dots, \mathfrak{m}_n$。取元素 $f \in \left(\bigcap_{j \neq i} \mathfrak{m}_j\right) \setminus \mathfrak{m}_i$，则主开子集 $D(f) \subset S$ 仅包含通用点 $(0)$ 与闭点 $x_i$，拓扑上恰好是 $S_i$；且代数局部化 $(\mathcal{O}_{X, \Sigma})_f \cong \mathcal{O}_{X, x_i}$ 是单元素有限生成的有限型代数。因此在一维情形，$S_i \to S$ **恰好是主开浸入，构成了 $S$ 的开子概形**。
  - **影响**：原题要求说明“$S_i$ **不必**是开子概形”（即一般高维情形不是开子概形），答卷将其绝对化为“$\dim \ge 1$ 即非开子概形”，混淆了充要维度条件（需 $\dim \ge 2$）。

---

### S2 分离预层的比较图
- **审阅判定**：**正确、完整**。
  - 将 S1 的 2 点等化子条件化归为核正合列 $0 \to G(S) \to G(S_1) \oplus G(S_2) \to G(S_1 \times_S S_2)$ 步骤清晰。
  - 对可缩邻域的 Mayer-Vietoris 序列取滤过余极限保持正合性无误。
  - 四引理图追逐（利用中坚直同构、右坚直单射以及底行与顶行在核处的正合性）分别验证 $\eta_S$ 单射性与满射性逻辑闭环。

---

### S3 含指定点的开集
- **审阅判定**：**正确、完整**。
  - 余终性证明中，对任一 $V \in \mathcal{I}$ 取 $U = V \cap W \in \mathcal{I}_W$ 验证了支配性与有向相容性。
  - 构造包含诱导映射 $\phi$ 与限制诱导族 $\psi_V$ 的余极限态射 $\psi$，严格验证了 $\phi \circ \psi = \mathrm{id}$ 与 $\psi \circ \phi = \mathrm{id}$，给出了典范同构。

---

### S4 稠密开与邻域系统
- **审阅判定**：**正确、完整**。
  - **结论判定**：“不成立（否定）”，正确。
  - **反例构造**：取 $k$ 为任意域，$X = \mathbb{A}^1_k = \operatorname{Spec} k[t]$（光滑积分仿射），$\Sigma = \{0\}$（对应 $(t)$），$W = X \setminus \{0\} = D(t)$（稠密开子集）。
  - **论证**：包含 $\Sigma$ 且包含于 $W$ 的开集族必然要求 $0 \in U \subset X \setminus \{0\}$，该族为空集；空集在非空有向族中绝不余终。完全符合题设全部前提。

---

### S5 整体对象与全部恢复目标
- **审阅判定**：**不正确、不完整（存在重大核心错误与证明断层）**。
- **具体问题剖析**：
  1. **核心断言错误：稠密开浸入单射性对预层不成立**
     - **答卷断言**：答卷第 3 小节列出“定理（稠密开浸入单射性）：设 $Y \in \mathrm{Sm}/k$ 是连通光滑整概形，$W \subset Y$ 是稠密开子集。则限制映射 $F(Y) \to F(W)$ 是单射”。
     - **可核查反例**：该断言严重错误。取 $F = \mathrm{CH}^1 = \operatorname{Pic}$（Picard 群 / 第一 Chow 群函子），它是标准的同伦不变带转移预层。令 $Y = \mathbb{P}^1_k$，$W = \mathbb{A}^1_k \subset \mathbb{P}^1_k$ 为标准仿射直线稠密开子集。此时：
       $$F(Y) = \operatorname{Pic}(\mathbb{P}^1_k) \cong \mathbb{Z} \cdot [\mathcal{O}(1)], \qquad F(W) = \operatorname{Pic}(\mathbb{A}^1_k) = 0.$$
       限制同态为 $\mathbb{Z} \to 0$，其核为 $\mathbb{Z} \neq 0$，**绝非单射**！
  2. **错误推论：预层 $F$ 并非分离预层**
     - **答卷推论**：答卷由上述假定理推得“$F$ 是 Zariski 分离预层”以及“典范态射 $F(U) \to F_{\mathrm{Zar}}(U)$ 对任一开集 $U$ 均是单射”。
     - **可核查反例**：在上述反例中，$\mathbb{P}^1_k$ 上的非零丛 $\mathcal{O}(1)$ 在标准二开覆盖 $\{U_0, U_1\}$ 上局部平凡（限制均为 0），因此 $F = \operatorname{Pic}$ **不是分离预层**；且其 Zariski 层化 $\operatorname{Pic}_{\mathrm{Zar}} = 0$，态射 $\operatorname{Pic}(\mathbb{P}^1) \to \operatorname{Pic}_{\mathrm{Zar}}(\mathbb{P}^1)$ 即 $\mathbb{Z} \to 0$，不是单射。答卷混淆了预层 $F$ 与其层化 $F_{\mathrm{Zar}}$（在 Voevodsky 理论中，单射性 $F_{\mathrm{Zar}}(Y) \hookrightarrow F_{\mathrm{Zar}}(W)$ 仅对**层化后**的层成立）。
  3. **前置条件断裂：S2 适用条件失效**
     - 答卷在应用 S2 时，依赖“$F$ 为分离预层”以及“$\eta_{S_1 \times_S S_2}: F(S_1 \times_S S_2) \to F_{\mathrm{Zar}}(S_1 \times_S S_2)$ 为单射”。由于前述分离性证明彻底错误，此处单射性未经证明，导致 S2 的四引理图追逐无法合法启动。
  4. **违反题设规则：未说明标准定理的关键适用条件（完备域）**
     - 原题总则明确要求“援引前项或标准定理时说明实际适用条件”。
     - 原题仅设“$k$ 为域”，答卷援引的 Voevodsky 经典定理（*Cohomological Theory of Presheaves with Transfers*, Theorem 3.1.11 及 MVW Theorem 4.18/5.7）**明确要求基域 $k$ 必须是完备域（perfect field）**，以确保 Artin 初等纤维化中的曲线光滑紧化与移动引理成立。答卷完全未对 $k$ 是否完备这一适用边界进行说明或讨论。
  5. **归纳步骤的证明脱节**
     - 答卷在 $n \ge 3$ 的归纳中，直接将 $\Sigma$ 拆为 $S'$（$n-1$ 点半局部概形）与 $S_n$（单点局部概形），声称“顶行由同伦转移 MV 给出，底行由 S1 给出”。
     - 然而 S2 仅建立了 2 个单点的情形，并未证明涉及多点半局部概形 $S'$ 的邻域收缩正合性；且 S1 仅为 $n$ 个单点局部化的等化子，并非任意两块半局部概形拼接的短正合列。此处存在明显的逻辑跳步。

---

### S6 极限正合与阶段正合
- **审阅判定**：**正确、完整**。
  - **第一问判定与反例**：
    - 判定“不成立（否定）”正确。
    - 构造 $\mathbb{N}$ 上的二项复形滤过系统 $C_1^{(i)} = \mathbb{Z} \xrightarrow{\times 2} C_0^{(i)} = \mathbb{Z}$，链映射各分量均为乘以 2。
    - 各阶段复形同调均为 $H_0(C_\bullet^{(i)}) = \mathbb{Z}/2\mathbb{Z} \neq 0$（处处不正合）；余极限微分算子为 $\mathbb{Z}[1/2] \xrightarrow{\times 2} \mathbb{Z}[1/2]$ 是同构，余极限复形严格正合。充分证明了极限正合不能蕴含充分后阶段正合。
  - **第二问证明**：
    - 提供了基于同调函子与滤过余极限交换性 $H_n(\varinjlim C_\bullet^{(i)}) \cong \varinjlim H_n(C_\bullet^{(i)})$ 的证明，以及直接追踪循环元到边界元的元素追逐证明，论证完整严谨。

---

## 审阅结论汇总表

| 题目编号 | 结论判定 | 完整性与数学正确性 | 主要问题与可核查依据 |
| :--- | :--- | :--- | :--- |
| **S1** | 部分有误 | 不完整 | 等化子证明正确；但断言“$\dim \ge 1$ 即非开子概形”错误，一维半局部 PID 上 $S_i$ 是主开子概形 $D(f)$。 |
| **S2** | 正确 | 完整正确 | Mayer-Vietoris 序列极限化与四引理图追逐规范严谨。 |
| **S3** | 正确 | 完整正确 | 邻域支配性、相容性及互逆同态构造完备。 |
| **S4** | 正确 | 完整正确 | 判定否定正确，反例 $X = \mathbb{A}^1, W = X \setminus \{0\}, \Sigma = \{0\}$ 满足全部前提。 |
| **S5** | 错误 | 不正确且不完整 | 1. 虚构“$F(Y) \to F(W)$ 稠密单射”定理（反例：$F = \operatorname{Pic}, Y = \mathbb{P}^1, W = \mathbb{A}^1$）；<br>2. 错误断言 $F$ 分离，致使 S2 前提失效；<br>3. 漏述 Voevodsky 定理要求 $k$ 完备的适用条件；<br>4. $n \ge 3$ 归纳步存在跳步与证明脱节。 |
| **S6** | 正确 | 完整正确 | 乘 2 复形滤过系统反例严密有效；同调消亡蕴含极限正合证明详尽。 |
