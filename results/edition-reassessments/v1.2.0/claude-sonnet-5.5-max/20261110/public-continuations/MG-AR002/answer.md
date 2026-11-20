# 审阅意见（修订稿）

## 一、总判断

- **结论层面：S1–S6 的结论全部正确。** S1/S2 的公式正确，S3 三项成立，S4 目标成立，S5 答“不必”且反例有效，S6 答“闭”且描述正确。逐步核对没有发现错误断言或错误推导，也没有越过适用条件的定理引用。
- **完整性：基本完整，有一处实质性缺口。**
  - S1–S3、S5、S6 完整。S4 §1–§4（整体解、$\mathcal S$、$\pi_A(\mathcal S)$、非空纤维）完整正确。
  - 缺口是 S4 §5 的分类表：只有断言，没有证明，也没有显式恢复公式，而题面要求“完成全部构造、分类与性质的证明”。
  - 三条断言都为真（第四节补证）。缺口是局部的：S6 只引用 §3，所以 §1–§4、S1–S3、S5、S6 都不受影响。
- **表述层面：** S4 首句漏写前提；答卷没有陈述解集与数据 $(W,\beta)$ 的一一对应（问题 3）。
- **对 `current-check.md`：** 保留（KEEP）的决定可以接受，其三条具体论据在数学上成立。但“无任何漏洞、无可辩驳”是没有依据的整体验证断言，与 §5 缺口不符。另有一处名称误用、一处无法核对的引用。

## 二、逐项核验（含适用条件与依赖）

**S1**
- 标准点积在任意域上对有限维 $k^I$ 非退化。它不要求正定，答卷也没有用 $k^I=W\oplus W^\perp$（该分解在有限域上可能为假）。
- 因此 $\dim W^\perp=|I|-\dim W$，$W^{\perp\perp}=W$，$(W^\perp)^*\cong k^I/W$。
- $\mathcal S=x_0+W^\perp$，仿射维数 $|I|-\dim W$。
- 非空纤维的方向空间是 $W^\perp\cap U_A^\perp=(W+U_A)^\perp$，维数 $|I|-\dim(W+U_A)=|I|-|A|-\dim W+\dim(W\cap U_A)$，与 $y$ 无关。
- 延拓判据：对一切 $w\in W\cap U_A$，$\sum_{i\in A}w_iy_i=\beta(w)$，其中 $\beta(\sum c_ja_j)=\sum c_jb_j$（由相容性，与表示无关）。
- 必要性一行即得。充分性用 $T:W^\perp\to k^A$，$T^*u=\iota_A(u)+W$，$\ker T^*\cong W\cap U_A$，$\operatorname{Im}T=(\ker T^*)^\perp$（有限维、非退化配对）。推导无误。

**S2**
- $|\mathcal S|=q^{|I|-\dim W}$。
- 每个可实现坐标的完成数是 $q^{|I|-\dim(W+U_A)}$。
- 可实现的 $A$ 坐标数是 $q^{\dim(W+U_A)-\dim W}=q^{|A|-\dim(W\cap U_A)}$（纤维等大，取商）。
- $A=\emptyset$ 与 $A=I$ 两个端点自检吻合。

**S3**
- Tychonoff 定理：$k$ 有限离散，故 $k^I$ 紧 Hausdorff。
- $f_j$ 连续，因为 $a_j$ 有限支撑且 $k$ 离散。$\mathcal S_j=f_j^{-1}(b_j)$ 闭且有有限交性质，故 $\mathcal S\ne\emptyset$ 且紧。
- 全不连通：全不连通空间的积与子空间仍全不连通。
- $\pi_A(\mathcal S)$ 是紧集在 Hausdorff 空间 $k^A$ 中的像，故闭。
- 刻画：对 $\{\mathcal S_j\}_{j\in J}\cup\{K_i\}_{i\in A}$（$K_i=\{x_i=y_i\}$）用有限交性质，正确。
- 适用条件：紧性依赖 $k$ 有限。$k$ 无限时 $k^I$ 不紧（$I\neq\emptyset$ 时，开覆盖 $\{x_{i_0}=c\}_{c\in k}$ 无有限子覆盖）。答卷没有外推，处理正确。

**S4**
- $\beta$ 良定义：有限关系 $\sum_{j\in F}c_ja_j=0$ 与子系统 $F$ 的一个解配对，得 $\sum c_jb_j=0$。这正是用到“有限子系统可解”的地方。
- 整体解：基扩充（Zorn 引理）得 $\tilde\beta\in(k^{(I)})^*$，取 $x^*_i=\tilde\beta(e_i)$，则 $\langle a_j,x^*\rangle=b_j$。$k^I\cong(k^{(I)})^*$ 的配对对有限支撑向量是有限和，合法。该“构造”本质依赖选择公理，与“采用 ZFC”一致。
- $\mathcal S=x^*+W^\circ=\{x:\langle w,x\rangle=\beta(w)\ \forall w\in W\}$。两种写法等价，因为行的线性组合给出等价性。
- 像定理：
  - $\subseteq$ 直接。
  - $\supseteq$ 中 $\psi(w+u)=\beta(w)+\gamma_y(u)$ 的良定义，恰好只依赖 $W\cap U_A$ 上 $\gamma_y=\beta$；再延拓到 $k^{(I)}$（选择公理）。
- 纤维是 $x+(W+U_A)^\circ$，正确。
- §5 分类表：三条断言为真，但无证明（问题 1）。

**S5**
- 反例 $x_1=1$，$x_{j-1}=x_j$（$j\ge2$）满足全部前提。
- 有限子系统 $F$ 取 $M=\max F$，$\mathbf 1_{[1,M]}\in k^{(\mathbb N)}$ 是其解。
- 全系统在 $k^{\mathbb N}$ 中的唯一解是全 1 序列，不在 $k^{(\mathbb N)}$ 中。对每个域 $k$ 成立。
- 在 S4 的语言里，这里 $W=k^{(\mathbb N)}$，$\beta(w)=\sum w_i$，唯一解 $x^*_i=\beta(e_i)=1$。这与 S4（$k^{\mathbb N}$ 中有解）相容。

**S6**
- $\pi_A(\mathcal S)=\bigcap_{w\in W\cap U_A}C_w$。每个 $C_w$ 只依赖有限集 $\operatorname{supp}w\subseteq A$ 上的坐标，是 clopen 柱集，任意交仍闭。
- 论证只用 S4 §3（对任意域成立），不用紧性，对无限域有效。
- 答卷末尾“互不冗余”的基方程组说法成立（问题 5）。

**依赖关系：** S2←S1；S3 独立（紧性）；S4 §1→§2→§3→§4→§5；S6←S4 §3；S5 独立。无循环依赖，各处条件满足。

## 三、问题清单（位置、性质、影响范围）

1. **S4 §5 分类表无证明、无恢复公式（实质性缺口，局部）**
   - 单射 ⟺ $W+U_A=k^{(I)}$，满射 ⟺ $W\cap U_A=0$，双射 ⟺ $W\oplus U_A=k^{(I)}$，三条为真但未证。
   - 影响范围：仅“分类”这一子要求。§1–§4、S1–S3、S5、S6 不受影响。补证见第四节定理 C。
2. **S4 开头判定段（表述）**
   - “对任意域 $k$ 与任意集合 $I,J$，全系统的整体解必存在”漏写“每个有限子系统可解”。
   - 字面命题为假：取 $I=\{1\}$，$J=\{1,2\}$，$a_1=a_2=e_1$，$b_1=0$，$b_2=1$，各单行可解而全系统无解。
   - §1 的证明正确用了该假设，故只是文字问题，无数学影响。
3. **未陈述 $(W,\beta)\leftrightarrow\mathcal S$ 的一一对应（可选读法下的缺项，不是错误）**
   - 答卷用 $(W,\beta)$ 描述了 $\mathcal S$，但没有说明数据可由 $\mathcal S$ 唯一还原，也没有说明有限支撑后承恰是方程的有限线性组合。
   - 是否算缺项取决于对“分类”的读法。补证见定理 D。
4. **`current-check.md`**
   - (a) 整体断言“第二轮独立且严密的核查……无任何漏洞”“无可辩驳”没有给出任何可检内容，且与问题 1 不符。它只影响这句评语的可信度，不影响下列具体论据。
   - (b) 论据 1（扩充方程组加 S4 §1）正确，且不循环：S4 §1 的整体可解性不依赖闭性。它是 S3 §3 有限交论证的代数版本，对任意域成立。
   - (c) 论据 2 正确，即原答 S6。
   - (d) 论据 3 的三件事实本身成立，但存在两个问题：
     - 离散域上 $k^I$ 线性紧是已知定理，文中只引用未证；“Bourbaki, Algèbre, Chap. II, §7”的章节号我无法离线核对。
     - 论据 3 与论据 1 重复，不构成独立必要依据。
     - 其余两件事我当场验证：连续仿射像保持线性紧；Hausdorff 线性拓扑中线性紧子空间闭。后者的证明是：设 $x\in\overline L$，开子空间 $V$ 给出 $L$ 中有有限交性质的闭陪集族 $\{(x+V)\cap L\}$，取公共点 $z$，则 $z-x\in\bigcap V=0$。
   - (e) “Hahn-Banach/基扩充公理”名称不准确。分析型 Hahn–Banach 需要实/复向量空间与次线性泛函，对无序、无赋值结构的任意域 $k$ 不适用。这里用的是纯代数事实“子空间上的线性泛函可延拓”，由基扩充（Zorn 引理）证明，且基扩充是定理而非公理。论证本身不受影响。
5. **极轻微**
   - S6 的“互不冗余”未证，但成立：若 $w_{\lambda_0}\notin\operatorname{span}\{w_\lambda\}_{\lambda\ne\lambda_0}$，把基 $\{w_\lambda\}$ 扩充为 $k^{(A)}$ 的基，取对偶泛函 $\delta\in k^A$，使其在 $w_\lambda$（$\lambda\ne\lambda_0$）上为 0、在 $w_{\lambda_0}$ 上为 1。取 $y_0\in\pi_A(\mathcal S)$，则 $y_0+\delta$ 只违反第 $\lambda_0$ 个方程。
   - S5 只处理了非空 $F$，$F=\emptyset$ 平凡。

## 四、补证（我的补充，不属于被审文本）

记 $V=k^{(I)}$，$\langle w,x\rangle=\sum w_ix_i$，$M^\circ=\{x\in k^I:\langle m,x\rangle=0\ \forall m\in M\}$。$(W,\beta)$ 为 S4 的数据，$\mathcal S\ne\emptyset$ 已由 S4 §1 得到。

**引理 F（选择公理）。** 若 $M\le V$，$w\in V\setminus M$，则存在 $v\in M^\circ$ 使 $\langle w,v\rangle\neq0$。
- 证明：取 $M$ 的基，添入 $w$ 后仍线性无关，扩充为 $V$ 的基（Zorn）。令线性泛函 $\varphi$ 在 $w$ 上取 1、在其余基向量上取 0，并令 $v_i=\varphi(e_i)$。
- 对 $u\in V$ 有 $\langle u,v\rangle=\varphi(u)$（有限和），所以 $v\in M^\circ$ 且 $\langle w,v\rangle=1$。∎

**命题 R（可恢复的量）。** 对 $w\in V$，下列两条等价：(i) $\langle w,\cdot\rangle$ 在 $\pi_A|_{\mathcal S}$ 的每个纤维上取常值；(ii) $w\in W+U_A$。此时若 $w=w_1+u$（$w_1\in W$，$u\in U_A$），则对 $x\in\mathcal S$，$\langle w,x\rangle=\beta(w_1)+\sum_{l\in A}u_lx_l$。
- (ii)⟹(i) 及公式：$\langle w,x\rangle=\langle w_1,x\rangle+\langle u,x\rangle=\beta(w_1)+\sum_{l\in A}u_ly_l$，只依赖 $y=x|_A$。
- (i)⟹(ii)：若 $w\notin W+U_A$，由引理 F 得 $v\in(W+U_A)^\circ$ 且 $\langle w,v\rangle\ne0$。取 $x\in\mathcal S$，则 $x+v\in\mathcal S$（$v\in W^\circ$）与 $x$ 有相同 $A$ 坐标（$v\in U_A^\circ$），但 $\langle w,\cdot\rangle$ 的值不同。∎

**定理 C（§5 分类表）。**
- (a) $\pi_A|_{\mathcal S}$ 单射 ⟺ $W+U_A=V$。此时对 $i\notin A$，写 $e_i=w^{(i)}+u^{(i)}$（$w^{(i)}\in W$，$u^{(i)}\in U_A$），则
  $$x_i=\beta(w^{(i)})+\sum_{l\in A}u^{(i)}_ly_l.$$
  - 证明：单射 ⟺ 每个纤维是单点 ⟺ 每个坐标函数 $x_i=\langle e_i,\cdot\rangle$ 在纤维上为常值 ⟺（命题 R）$e_i\in W+U_A$ 对所有 $i$ 成立 ⟺ $W+U_A=V$（$e_i$ 生成 $V$）。
  - 更细地，坐标 $i$ 可由 $x|_A$ 唯一恢复 ⟺ $e_i\in W+U_A$。
- (b) 满射 ⟺ $W\cap U_A=0$。
  - 若 $W\cap U_A=0$，S4 §3 的约束只剩 $0=\beta(0)$，故 $\pi_A(\mathcal S)=k^A$。
  - 若 $0\neq w\in W\cap U_A$，取 $w_i\ne0$ 与 $y_0\in\pi_A(\mathcal S)$。则 $y_0+e_i$ 使 $\sum w_ly_l$ 改变 $w_i\neq0$，违反该方程，故不满射。
- (c) 双射 ⟺ $V=W\oplus U_A$。此时 $\pi_A|_{\mathcal S}:\mathcal S\to k^A$ 是仿射双射，因而是仿射同构，逆由 (a) 的公式给出。

**定理 D（解集与数据的对应）。**
1. 任给 $W\le V$ 与 $\beta\in W^*$，取 $J=W$，$a_w=w$，$b_w=\beta(w)$。把 $\beta$ 延拓到 $V$（选择公理），其解为该系统的整体解，故每个有限子系统可解。该系统的数据正是 $(W,\beta)$。
2. 对满足题设的系统，$\mathcal S$ 唯一确定其数据：$W=\{w\in V:\langle w,\cdot\rangle$ 在 $\mathcal S$ 上为常数$\}$，$\beta(w)$ 为该常数。等价地：有限支撑关系 $\langle w,x\rangle=c$ 对一切 $x\in\mathcal S$ 成立，当且仅当 $w\in W$ 且 $c=\beta(w)$。
   - 证明：“$\Leftarrow$”显然。“$\Rightarrow$”：$\mathcal S=x^*+W^\circ$，常值意味着 $\langle w,v\rangle=0$ 对 $v\in W^\circ$ 成立。若 $w\notin W$，引理 F 给出矛盾。故 $w\in W$，$c=\langle w,x^*\rangle=\beta(w)$。∎
3. 因此 $(W,\beta)\mapsto\mathcal S(W,\beta)$ 是数据集合到“满足题设的系统的解集”的双射。
4. 补充：这些解集恰是 $k^I$（$k$ 离散、乘积拓扑）中的非空闭仿射子空间。
   - $\mathcal S(W,\beta)$ 是 clopen 超平面的交，故闭；非空见 S4 §1。
   - 反向：设 $S'=x_0+L$ 闭，$M=\{w\in V:\langle w,L\rangle=0\}$。若 $v\notin L$，闭性给出有限 $F$ 使 $v|_F\notin\pi_F(L)$。有限维对偶给出 $u\in k^F$，$u\perp\pi_F(L)$ 且 $\langle u,v|_F\rangle\ne0$。把 $u$ 以 0 延拓为 $w\in V$，则 $w\in M$ 而 $\langle w,v\rangle\ne0$，故 $v\notin M^\circ$。于是 $L=M^\circ$，$S'=\mathcal S(M,\langle\cdot,x_0\rangle|_M)$。这一步不用选择公理。

**命题 L（S6 的局部形式）。** $\pi_A(\mathcal S)=\bigcap_{B\subseteq A\ \text{有限}}\pi_B^{-1}(\pi_B(\mathcal S))$。
- 每个 $\pi_B(\mathcal S)=\{z\in k^B:\langle w,z\rangle=\beta(w),\ w\in W\cap U_B\}$ 是有限维 $k^B$ 的仿射子空间。$W\cap U_B$ 有限维，所以只涉及有限个方程。
- 证明：$\subseteq$ 显然。$\supseteq$：设 $y$ 在右边。对 $w\in W\cap U_A$ 取 $B=\operatorname{supp}w$，有 $x\in\mathcal S$ 使 $x|_B=y|_B$，故 $\sum w_iy_i=\langle w,x\rangle=\beta(w)$。由 S4 §3，$y\in\pi_A(\mathcal S)$。每个 $\pi_B^{-1}(\cdot)$ 是 clopen 柱集，所以右边闭。∎

## 五、核验手段与局限

- 我在本地对 $\mathbb F_2,\mathbb F_3,\mathbb F_5$ 上的随机有限系统做了穷举核对。
  - 系统规模：$|I|\le5$（$\mathbb F_5$ 上 $\le4$），$|J|\le4$，行部分强制线性相关，$b=Ax_0$ 保证相容，$A\subseteq I$ 随机（含 $\emptyset$ 与 $I$）。
  - 两轮共 6000 个系统（3600 + 2400），0 处不符。
  - 核对内容：
    - $|\mathcal S|$、$|\pi_A(\mathcal S)|$、纤维大小公式；
    - $\beta$ 的良定义；
    - S1 延拓判据（对每个 $y\in k^A$ 的充要性）；
    - 单射/满射判据及单射时的恢复公式；
    - “$w\cdot x$ 在 $\mathcal S$ 上为常数 ⟺ $w\in W$，且常数为 $\beta(w)$”。
  - 另做了 5948 个“坐标 $i$ 在纤维上唯一确定 ⟺ $e_i\in W+U_A$”的检查，0 处不符。
  - 同分布的 9000 个结构抽样中，单射约占 56%，满射约占 62%，双射约占 26%，$W\cap U_A\ne0$ 约占 38%，各类情形都大量出现。
- 这些只是有限维类比。无限维部分（S3–S6、定理 C/D、命题 L）靠逐步审读证明及其适用条件完成。
- 脚本为本地辅助，未作为交付物。未联网，没有核对任何外部文献。

## 六、保留 / 新增与修正 / 未完成与自评

- **保留**
  - 全部裁决：S1–S6 结论正确；S4 §5 缺证明；S4 首句漏前提；`current-check` 夸大且有引用问题。
  - 问题清单的实质内容。
- **新增与修正**
  - 删除了原稿中的行号引用（当前工作区没有材料文件，无法核对行号），改用小节标题。
  - 重写补证：把“单射”判据提升为更细的命题 R（坐标可恢复 ⟺ $e_i\in W+U_A$）。
  - 新增定理 D（解集与数据的一一对应、有限支撑后承完备性、闭仿射子空间刻画）和命题 L。
  - 放缓 Hahn–Banach 一条的措辞。
  - 重做了数值核对，并扩大了核对范围。
- **未完成与不确定**
  - Bourbaki 章节号无法核实。
  - “分类”一词的出题意图只能推断，定理 C、D 是对两种读法的对冲。
  - 无限维结论没有机器验证。
- **自评**
  - 判断依据全部可核查。
  - 被审材料的结论层面正确。
  - 我只认定一处实质缺口（S4 §5 无证明），并已给出闭合它的证明。
  - 按审阅任务要求，我已判断正误、给出依据、说明影响范围并检查依赖合法性，没有重做整套习题。
  - 我没有发现需要撤回的断言。