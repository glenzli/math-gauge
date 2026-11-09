# 审阅意见

## 总体判断

**结论层面：S1–S6 的结论全部正确。** S4 目标成立，S5 否定，S6 肯定。所引定理的适用条件均满足，我没有发现会改变任何结论的错误。

**完整性：基本完整，有一处缺口。** S4 §5（`original-answer.md:193–201`）的分类表只有断言，没有证明，也没有显式恢复公式，而题面要求“完成全部……分类……的证明”。另有几处表述和引用瑕疵，见“问题清单”。

**对 `current-check.md`：** 保留（KEEP）的决定可以接受。它的三条数学论据本身正确，但措辞夸大，并有一处名称误用。

## 逐项核验

**S1**
- 解集是 $\mathcal S=x_0+W^\perp$，$\dim\mathcal S=|I|-\dim W$。
- 这里用到标准点积在任意域上非退化（虽不正定），所以 $\dim W^\perp=|I|-\dim W$ 且 $W^{\perp\perp}=W$。答卷没有点明这一点，但它成立。
- 非空纤维的方向空间是 $W^\perp\cap U_A^\perp=(W+U_A)^\perp$。维数为 $|I|-\dim(W+U_A)=|I|-|A|-\dim W+\dim(W\cap U_A)$，与 $y$ 无关。
- 延拓判据是：对一切 $w\in W\cap U_A$，$\sum_{i\in A}w_iy_i=\beta(w)$，其中 $\beta(\sum c_ja_j)=\sum c_jb_j$。
- 必要性一行即得。充分性取 $T:W^\perp\to k^A$，$T^*u=\iota_A(u)+W$，则 $\ker T^*\cong W\cap U_A$，且 $\operatorname{Im}T=(\ker T^*)^\perp$（有限维、非退化配对）。推导无误。

**S2**
- $|\mathcal S|=q^{|I|-\dim W}$。
- 每个可实现坐标的完成数是 $q^{|I|-\dim(W+U_A)}$。
- 可实现的 $A$ 坐标数是 $q^{\dim(W+U_A)-\dim W}$，也等于 $q^{|A|-\dim(W\cap U_A)}$。
- 端点自检：$A=\emptyset$ 得 $1$ 与 $|\mathcal S|$；$A=I$ 得 $|\mathcal S|$ 与 $1$。

**S3**
- $k^I$ 由 Tychonoff 定理紧且 Hausdorff。
- $f_j$ 连续，因为 $a_j$ 有限支撑且 $k$ 离散。
- 闭集族 $\{\mathcal S_j\}$ 有有限交性质，故 $\mathcal S\ne\emptyset$，且 $\mathcal S$ 紧。
- 全不连通性由“全不连通空间的积与子空间仍全不连通”得到。
- $\pi_A(\mathcal S)$ 是紧集在 Hausdorff 空间中的像，所以闭。
- 有限可实现性的刻画，是对闭集族 $\{\mathcal S_j\}_{j\in J}\cup\{K_i\}_{i\in A}$ 用有限交性质得到的，正确。
- 适用条件：紧性依赖 $k$ 有限。答卷没有把这条论证外推到无限域，处理正确。

**S4**
- $\beta$ 良定义：有限关系 $\sum c_ja_j=0$ 与该有限子系统的一个解配对，得 $\sum c_jb_j=0$。这正是假设的用处。
- 整体解：基扩充（Zorn 引理）得 $\tilde\beta$，取 $x^*_i=\tilde\beta(e_i)$，故 $\mathcal S=x^*+W^\circ=\{x:\langle w,x\rangle=\beta(w)\ \forall w\in W\}$。
- 像：$\supseteq$ 方向中，$\psi(w+u)=\beta(w)+\gamma_y(u)$ 良定，因为不一致性只可能出现在 $W\cap U_A$ 上，而那里恰是假设条件。再延拓到全空间（选择公理）。
- 纤维为 $x+(W+U_A)^\circ$，正确。

**S5**
- 反例：$x_1=1$，$x_{j-1}-x_j=0$（$j\ge2$）。
- 有限子系统 $F$ 取 $M=\max F$，则 $\mathbf 1_{[1,M]}\in k^{(\mathbb N)}$ 是它的解。
- 全系统在 $k^{\mathbb N}$ 中的唯一解是全 1 序列，不属于 $k^{(\mathbb N)}$。对每个域 $k$ 都成立，且与 S4 相容（S4 保证 $k^{\mathbb N}$ 中有解）。

**S6**
- $\pi_A(\mathcal S)=\bigcap_{w\in W\cap U_A}C_w$，每个 $C_w$ 只依赖有限集 $\operatorname{supp}w$ 上的坐标，因此是 clopen 柱集，任意交仍闭。
- 论证不依赖紧性。$k$ 无限时 $k^I$ 不紧，答卷也没有误用 S3 的紧性论证。

## 问题清单

1. **S4 §5 缺证明与恢复公式（完整性缺口，中等偏轻）**
   - 三条分类结论本身正确，但未证。
   - 题面“对应构造”所需的显式恢复公式也没有给出。
   - 不影响 S4 主定理，也不影响其余阶段，补证后即可闭合。补证见下节。

2. **S4 首句（`original-answer.md:129`，表述）**
   - “对任意域 $k$ 与任意集合 $I,J$，全系统的整体解必存在”漏写了“有限子系统可解”的假设。
   - 如此写出的命题是假的，例如 $x_1=0$ 与 $x_1=1$ 两行。
   - §1 的证明正确使用了该假设，所以只是文字问题。

3. **`current-check.md:16`，“Hahn-Banach/基扩充公理”（名称误用）**
   - 分析型 Hahn–Banach 需要实（或复）向量空间与次线性泛函，不适用于任意域 $k$。
   - 这里真正用的是代数事实：子空间上的线性泛函可延拓到全空间，其证明是基扩充加 Zorn 引理。
   - 论证本身不受影响。

4. **`current-check.md:27`，线性紧性论据（引用）**
   - Bourbaki 的章节号我无法离线核对。
   - “$k^I$ 线性紧”只被引用，没有证明。其余两个事实正确，可当场验证：
     - 连续仿射像保持线性紧。
     - Hausdorff 线性拓扑中，线性紧子空间 $L$ 闭。证明：设 $x\in\overline L$，则 $\{(x+V)\cap L\}_V$（$V$ 取开子空间）是 $L$ 中有有限交性质的闭陪集族，故有公共点 $z$，且 $z-x\in\bigcap V=0$。
   - 这条论据与第一条重复，不构成独立必要依据。

5. **`current-check.md:5`（措辞）**
   - “独立且严密的核查”“无任何漏洞”“无可辩驳”不是数学依据。
   - 它与问题 1 的缺口不符。
   - 第一条论据（扩充方程组加 S4）不是循环论证，因为 S4 的整体可解性不依赖闭性，这点正确。

6. **极轻微**
   - `original-answer.md:247` 的“互不冗余”未证，但成立：若 $w_{\lambda_0}$ 不在其余 $w_\lambda$ 的张成中，可构造只违反第 $\lambda_0$ 个方程的 $y$。
   - S5 只处理了非空 $F$，$F=\emptyset$ 平凡。

## 问题 1 的补证（我已核对，结论正确）

- **单射 $\iff W+U_A=k^{(I)}$**
  - $\Leftarrow$：纤维为 $x+(W+U_A)^\circ=\{x\}$。
  - $\Rightarrow$：若 $W+U_A\subsetneq k^{(I)}$，把它的基扩充为 $k^{(I)}$ 的基（选择公理），在新增基向量上取 $f=1$、其余取 0，令 $v_i=f(e_i)$。则 $0\ne v\in(W+U_A)^\circ$，$x$ 与 $x+v$ 同属 $\mathcal S$ 且 $A$ 坐标相同。
  - 恢复公式：对 $i\notin A$ 写 $e_i=w^{(i)}+u^{(i)}$（$w^{(i)}\in W$，$u^{(i)}\in U_A$），则 $x_i=\beta(w^{(i)})+\sum_{l\in A}u^{(i)}_ly_l$。

- **满射 $\iff W\cap U_A=0$**
  - $\Leftarrow$：S4 §3 定理中的约束只剩 $w=0$，即 $0=\beta(0)$，平凡成立。
  - $\Rightarrow$：若 $0\ne w\in W\cap U_A$，取 $w_i\ne0$。对任一 $y\in\pi_A(\mathcal S)$（非空），$y+e_i$ 违反 $\sum w_ly_l=\beta(w)$，故不满射。

- **双射**是以上两者之合，即 $W\oplus U_A=k^{(I)}$。

## 核验手段与局限

- 我在 $\mathbb F_2,\mathbb F_3,\mathbb F_5$ 上对约 920 个随机系统做了穷举，共 0 处不符。核对内容为：
  - $|\mathcal S|$、像大小和纤维大小的公式。
  - S1 延拓判据（对所有表示 $w=\sum c_ja_j$ 检验）。
  - 单射和满射判据的有限维类比。
- 无限维部分（S3–S6）无法穷举，靠逐步核对证明及其适用条件完成。
- 未联网，没有核对任何外部文献。