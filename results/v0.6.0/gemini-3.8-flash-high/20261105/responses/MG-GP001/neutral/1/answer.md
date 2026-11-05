KEEP

### 本轮核查依据

经对上一版答卷中所有阶段（S1～S6）的全面核验，原答卷的所有数学结论、证明、反例构造、类型分类及充要判据均完全严密正确，故维持上一版的全部答案。

#### 一、重点断言（S4）核查

1. **同伦类型刻画定理成立**：
   - **底空间可缩性**：在几何实现中，$O = |K| \setminus \{v\}$ 沿单形重心坐标向底投影强形变收缩到有限 CW 子复形 $|K \setminus v|$。假定 $O$ 非空可缩，故 $|K \setminus v| \simeq *$ 为非空可缩有限 CW 复形。
   - **非空链环排除孤立顶点**：$O \cap C = |B| \setminus \{v\}$ 同理形变收缩到 $|B \setminus v|$。若链环 $L_K = \mathrm{lk}_K(v) = \emptyset$，则 $v$ 是 $K$ 的孤立顶点，亦必为子复形 $B$ 的孤立顶点，从而 $|B| = |B \setminus v| \sqcup \{v\}$。此时包含映射 $(|B| \setminus \{v\}) \hookrightarrow |B|$ 在连通分支集 $\pi_0$ 上的诱导映射非满（遗漏分支 $\{v\}$），不可能为同伦等价。故必有 $L_K \ne \emptyset$。
   - **附着空间识别**：几何实现即胞腔附着空间 $X = |K| = |K \setminus v| \cup_{L_K} C(L_K)$。因为底空间 $|K \setminus v| \simeq *$ 可缩，包含映射 $i: |L_K| \hookrightarrow |K \setminus v|$ 自动零伦。由 S2 结论，附着映射锥同伦等价于 $X \simeq |K \setminus v| \vee \Sigma |L_K| \simeq * \vee \Sigma |L_K| \cong \Sigma |L_K|$。
   - 故合法三元组的可能同伦类型恰为全部非空有限单纯复形的非约化悬挂类型：
     $$\{ [X] \mid X = |K| \} = \{ [\Sigma |L|] \mid L \text{ 为非空有限抽象单纯复形} \}.$$

2. **全类型实现构造完备**：
   - 对任一非空有限单纯复形 $L$，取单纯悬挂 $K = (w * L) \cup_L (v * L) = \Sigma_{\mathrm{simp}}(L)$。其除去 $v$ 后为锥 $K \setminus v = w * L$，故 $O \simeq *$ 非空可缩。
   - 因 $L \ne \emptyset$，任取顶点 $u \in L^{(0)}$，由边 $\{v, u\}$ 及其面生成的子复形 $B = \{\emptyset, \{v\}, \{u\}, \{v, u\}\}$ 满足 $C = |B| = [v, u] \simeq *$ 与 $O \cap C = (v, u] \simeq *$，包含映射为两可缩空间间的映射，必为同伦等价。且显然 $|K| \cong \Sigma |L|$。

3. **局部有限关联数据判据充要性确立**：
   - 包含 $v$ 的单形集合 $\mathrm{Star}_K(v) = \{\sigma \in K \mid v \in \sigma\}$ 及其面包含关系完全确定了单纯形链环 $L_K = \mathrm{lk}_K(v)$ 的有限代数链复形与整系数边缘矩阵 $\partial_k$。
   - **判据**：$X$ 可缩当且仅当 $L_K$ 是整数无环复形（$\tilde{H}_*(L_K; \mathbb{Z}) = 0$）。
     - **必要性**：$X \simeq \Sigma |L_K| \simeq * \implies \tilde{H}_{k+1}(X; \mathbb{Z}) = 0 \implies \tilde{H}_k(L_K; \mathbb{Z}) = 0$（由非约化悬挂同构）。
     - **充分性**：$\tilde{H}_0(L_K; \mathbb{Z}) = 0$ 且 $L_K \ne \emptyset$ 保证 $|L_K|$ 路径连通，由 Seifert-van Kampen 定理 $\Sigma |L_K|$ 单连通；同调全平凡结合 Hurewicz 定理与 Whitehead 定理严格推出 $\Sigma |L_K| \simeq *$。
     - **算法可检性**：仅需对有限边缘矩阵计算 Smith 标准型，验证零度连通性及各度数上 $\ker \partial_k = \mathrm{im}\,\partial_{k+1}$ 即可在有限步内判定。

---

#### 二、其余阶段（S1～S3, S5, S6）核查

- **S1（可缩子复形的商）**：CW 对 $(Y, A)$ 的 Borsuk 同伦延拓性质使收缩同伦延拓至全空间 $H_t$；由于 $A \times I$ 恒映入 $A$，且区间 $[0, 1]$ 紧致 Hausdorff，积映射 $q \times \mathrm{id}_I: Y \times I \to (Y/A) \times I$ 为拓扑商映射，同伦严格下降为商空间间的同伦。
- **S2（非可缩底空间上的锥附着）**：零伦延拓给出标准映射锥变换 $C(i) \simeq C(c_{d_0})$，常值粘合空间同胚于楔和 $D \vee \Sigma L$；因 $D$ 路径连通且点退化平凡，同伦类型严格独立于楔点在 $D$ 中的选取。
- **S3（实射影平面悬挂实例）**：$K = \Sigma_{\mathrm{simp}}(\mathbb{R}P^2)$，$B$ 取悬挂边，几何实现为 $\Sigma \mathbb{R}P^2$。有理同调全零，但 $\tilde{H}_2(|K|; \mathbb{Z}) \cong \mathbb{Z}/2\mathbb{Z} \ne 0$，严格满足不可缩要求。
- **S5（不提供子复形 B）**：移去 $B$ 后，允许 $L_K = \emptyset$（即 $v$ 为孤立顶点），产生 $K = K_0 \sqcup \{v\} \simeq * \sqcup * = S^0$；分类证明排除了其他情况，新增同伦类型恰好且仅为 $S^0$。
- **S6（悬挂逆向恢复反例）**：取庞加莱同调 3-球面挖去开 3-球的三角剖分 $L_1$ 与单点复形 $L_2$。$|L_1|$ 连通整无环但 $\pi_1(|L_1|) \cong I^* \ne 0$，故 $|L_1| \not\simeq |L_2|$，但 $\Sigma |L_1| \simeq * \simeq \Sigma |L_2|$，证伪逆向恢复。
