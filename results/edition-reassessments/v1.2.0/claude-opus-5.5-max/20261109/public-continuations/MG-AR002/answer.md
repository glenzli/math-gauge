# 审阅报告：《线性关系、坐标纤维与无限赋值》答卷

审阅对象是 `original-answer.md`（继承的正文）和 `current-check.md`（本轮核查里实际作出的数学断言），两者合起来算作待审答卷。

## 〇、总体结论

1. **正确性：答卷在原题条件下是正确的。**
   - S1–S6 的判定全部正确：S4 成立，S5 否，S6 是。
   - 所有公式和主干证明都成立。
   - 我没有找到会改变任何结论的数学错误。
2. **完整性：基本完整，但按"完整论证"的标准并不完全完整。**
   - 主要缺口在 S4 §5 的分类表：表中只写了条件，"仅当"方向没有证明（下文 G1）。而题目对 S4 明确要求"给出分类……和完整论证"。
   - 其余是小问题：一句措辞在行线性相关时字面上不成立（G2）；两处直接验证没写出来（G3）；一个附带断言没有证明（G4）；漏了一个平凡情形（G5）。
   - 每一处都能用几行补齐，补法见第二节。
3. **对 current-check 的判断：**
   - 三条论据在数学上都成立。论据 3 依赖它所引用的线性紧性定理。
   - 但它的总括断言"S1 至 S6 的所有构造、分类与定理证明……均无任何漏洞"不成立，原因见 G1 和 G4。
   - 它引用的 Bourbaki 章节我无法离线核实；另有几处术语不准确。

---

## 一、逐项核查依据

### S1：正确

- **解集维数。** 齐次解空间是 $\mathcal S_0=W^\perp$。标准点积在 $k^I$ 上非退化，所以对任意域都有 $\dim W^\perp=|I|-\dim W$，包括 $\mathbb F_2$ 这种存在迷向向量的情形。这只是秩–零度定理，不需要 $W\cap W^\perp=0$。系统相容，所以 $\mathcal S\neq\varnothing$，从而 $\dim\mathcal S=|I|-\dim W$。
- **纤维维数。** 非空纤维是 $\mathcal F_y=x+V_0$，其中 $V_0=W^\perp\cap U_A^\perp=(W+U_A)^\perp$，维数为 $|I|-\dim(W+U_A)$。附注里的另一种写法与此相等，因为 $\dim(W+U_A)=\dim W+|A|-\dim(W\cap U_A)$。
- **延拓判据。**
  - 必要性是直接计算。
  - 充分性：限制映射 $T:W^\perp\to k^A$ 的伴随是 $T^*(u)=\iota_A(u)+W\in k^I/W\cong(W^\perp)^*$，所以 $\ker T^*\cong W\cap U_A$。
  - 再用 $\operatorname{Im}T=(\ker T^*)^\perp$：包含关系显然；两边维数相等，因为 $\operatorname{rank}T=\operatorname{rank}T^*=|A|-\dim\ker T^*$。
  - 答卷还说明了 $\beta(w)=w\cdot x_0$，与 $w$ 的表示方式无关。
  - 这一部分没有问题。

### S2：正确

- 三个计数是：解数 $q^{|I|-\dim W}$，可实现坐标数 $q^{\dim(W+U_A)-\dim W}$，每个可实现坐标的完成数 $q^{|I|-\dim(W+U_A)}$。
- 所有非空纤维大小相同，所以用除法求可实现坐标数是合法的。
- 公式只用了题目允许的量。

### S3：正确

- **非空与紧。** $k^I$ 由 Tychonoff 定理紧且 Hausdorff。每个 $f_j$ 只依赖 $\operatorname{supp}a_j$ 上有限个坐标，所以连续，单方程解集 $\mathcal S_j$ 闭。这族闭集有有限交性质，所以 $\mathcal S\neq\varnothing$；$\mathcal S$ 是紧空间的闭子集，所以紧。
- **全不连通。** 答卷引用了"全不连通空间的乘积及其子空间仍全不连通"，这是正确的。也可以直接论证：两个不同的解在某个坐标 $i$ 上取值不同，柱集 $\{x_i=t\}$ 既开又闭，把它们分开。
- **像闭。** $\pi_A(\mathcal S)$ 是紧集在 Hausdorff 空间中的像，所以闭。
- **元素刻画。** 闭集族 $\{\mathcal S_j\}_{j\in J}\cup\{K_i\}_{i\in A}$ 的有限交性质恰好就是题设条件。$F$ 或 $B$ 为空的情形也包含在"任意有限子集"之内。由紧性，全交非空。

### S4：判定"成立"正确，核心构造正确

- **对偶。** $k^I\cong(k^{(I)})^*$，对应为 $x\mapsto\langle\cdot,x\rangle$，因为线性泛函由它在基 $e_i$ 上的取值自由决定。
- **$\beta$ 良定。** 同一个 $w$ 的两种表示之差是某个有限集 $F$ 上的线性关系。$F$ 上的有限子系统有解，所以对应常数的组合为 $0$。
- **整体解。** 用 Zorn 引理把 $W$ 的基扩充为 $k^{(I)}$ 的基，令 $\tilde\beta$ 在新增基向量上取 $0$，再令 $x^*_i=\tilde\beta(e_i)$。于是 $\langle a_j,x^*\rangle=\tilde\beta(a_j)=b_j$。在 ZFC 中合法。
- **解集。** $\mathcal S=x^*+W^\circ=\{x:\langle w,x\rangle=\beta(w)\ \forall w\in W\}$，正确（验证见 G3）。
- **像定理。** 在 $W+U_A$ 上把 $\beta$ 与 $\gamma_y$ 粘合。良定性恰好用到"两者在 $W\cap U_A$ 上一致"这一条件，然后延拓到全空间。正确。
- **纤维。** 纤维为 $x+(W+U_A)^\circ$，其中 $(W+U_A)^\circ=W^\circ\cap U_A^\circ$，$U_A^\circ=\{v:v|_A=0\}$。正确。
- **分类表。** 三行的条件全部正确，但证明有缺口，见 G1。

### S5：判定"否"正确

- 反例为 $x_1=1$，$x_{j-1}-x_j=0$（$j\ge2$）。
- 对非空有限的 $F$，取 $\mathbf 1_{[1,\max F]}\in k^{(\mathbb N)}$，它满足 $F$ 中的每一行。$F=\varnothing$ 时取 $0$ 即可（G5）。
- 全系统在 $k^{\mathbb N}$ 中的唯一解是全 1 序列，它不在 $k^{(\mathbb N)}$ 中。
- 这个反例对任意域都成立。

### S6：判定"闭"正确

- 由 S4 的像定理，$\pi_A(\mathcal S)=\bigcap_{w\in W\cap U_A}C_w$。
- 每个 $w$ 的支撑有限且含于 $A$，所以每个 $C_w$ 只是有限个坐标上的条件，是既开又闭的柱集；任意多个闭集的交仍是闭集。
- 这里没有用到紧性。当 $k$ 无限且 $I\neq\varnothing$ 时，$k^I$ 不紧：开覆盖 $\{x:x_{i_0}=t\}_{t\in k}$ 没有有限子覆盖。$\mathcal S$ 也可以不紧，例如 $J=\varnothing$。所以 S3 的方法搬不过来，但结论仍然成立。
- 给出的方程描述确实只涉及有限个坐标，并且由 $(a_j,b_j)$ 决定。

---

## 二、问题清单与补法

| 编号 | 位置 | 性质 | 影响 |
|---|---|---|---|
| G1 | S4 §5 表，单射行与满射行 | 只写了条件，"仅当"方向没有证明 | S4"分类……完整论证"没有完全交付；结论正确 |
| G2 | S4 §5 表，满射行的"意义"栏 | 行线性相关时字面上为假 | 只影响解释性文字 |
| G3 | S4 §2、§4 | 等式只写了结论，没写验证 | 极轻微，都是直接推论 |
| G4 | S6 §1"互不冗余" | 断言为真，但没有证明 | 闭性证明不依赖它 |
| G5 | S5 | 漏了 $F=\varnothing$ | 平凡 |

**G1 的补法。**

单射 $\iff W+U_A=k^{(I)}$：
- ($\Leftarrow$) 记 $M=W+U_A$。若 $M=k^{(I)}$，则对任意 $z\in M^\circ$ 有 $z_i=\langle e_i,z\rangle=0$，所以 $M^\circ=0$。由 §4，每个纤维都是单点。
- ($\Rightarrow$) 若 $M\neq k^{(I)}$：
  1. 取 $v_0\notin M$，把 $M$ 的一组基添上 $v_0$，再扩充为 $k^{(I)}$ 的基。
  2. 令线性泛函 $\varphi$ 在 $v_0$ 上取 $1$，在其余基向量上取 $0$；令 $z_i=\varphi(e_i)$。
  3. 则 $z\in M^\circ=W^\circ\cap U_A^\circ$，且 $\langle v_0,z\rangle=1$，所以 $z\neq0$。
  4. 任取 $x\in\mathcal S$（S4 §1 已证 $\mathcal S\neq\varnothing$），则 $x+z\in\mathcal S$ 且 $(x+z)|_A=x|_A$，所以 $\pi_A$ 不是单射。

满射 $\iff W\cap U_A=0$：
- ($\Leftarrow$) 由像定理，条件只剩 $w=0$ 一条，自动成立。
- ($\Rightarrow$) 若有 $0\neq w\in W\cap U_A$：
  1. 取 $i_0\in A$ 使 $w_{i_0}\neq0$。
  2. 令 $y=t\,\delta_{i_0}$，其中 $t=(\beta(w)+1)/w_{i_0}$。
  3. 则 $\sum_{i\in A}w_iy_i=\beta(w)+1\neq\beta(w)$，由像定理 $y\notin\pi_A(\mathcal S)$。

双射一行就是前两行的合取。

**G2：措辞问题。** 满射行的"意义"栏写的是"方程系中不存在支撑全在 $A$ 内的非平凡线性组合"。如果"非平凡"指系数不全为零，那么行线性相关时这句话是错的。
- 反例：$I=\{1,2\}$，$a_1=a_2=e_1$，$b_1=b_2=1$，$A=\{2\}$。
- 此时 $a_1-a_2=0$ 是非平凡组合，支撑为空集，当然含于 $A$。
- 但 $W\cap U_A=\operatorname{span}(e_1)\cap\operatorname{span}(e_2)=0$，而且 $\pi_A$ 确实是满射：$x_1=1$，$x_2$ 任意。本轮机检也确认了这一点。
- 应改为"$W$ 中不存在支撑含于 $A$ 的非零向量"。
- 中间栏的形式条件 $W\cap U_A=\{0\}$ 本身是对的。

**G3：两处直接验证。**
- §2 的 $\mathcal S=\{x:\langle w,x\rangle=\beta(w)\ \forall w\in W\}=x^*+W^\circ$：
  - "⊇"：取 $w=a_j$；
  - "⊆"：对有限组合 $w=\sum c_ja_j$ 用线性；
  - 第二个等号：两边同时减去 $x^*$。
- §4 的纤维：对 $x,x'\in\mathcal S$，二者 $A$-限制相同 $\iff x'-x\in W^\circ\cap U_A^\circ$。又因为和的零化子等于零化子的交，$W^\circ\cap U_A^\circ=(W+U_A)^\circ$。

**G4：互不冗余。** 断言为真，证明如下：
1. $\{w_\lambda\}$ 在 $k^{(A)}$ 中线性无关，把它扩充为 $k^{(A)}$ 的基，取第 $\mu$ 个对偶泛函，得到 $z\in k^A$，满足 $\langle w_\lambda,z\rangle=\delta_{\lambda\mu}$。
2. 取 $y_0\in\pi_A(\mathcal S)$（非空）。
3. 则 $y_0+z$ 满足除第 $\mu$ 个以外的全部方程，但不满足第 $\mu$ 个。所以没有哪个基方程能由其余方程推出。

**可选补强（不算错误）。**

(a) 方向空间：
- $\mathcal S$ 的方向空间是 $W^\circ\cong(k^{(I)}/W)^*$。
- 像的方向空间是 $\pi_A(W^\circ)=(W\cap U_A)^\perp\cong(k^{(A)}/(W\cap U_A))^*$。这是把像定理用于齐次系统得到的。
- 纤维的方向空间是 $(W+U_A)^\circ\cong(k^{(I)}/(W+U_A))^*$。
- 三者构成正合列 $0\to(W+U_A)^\circ\to W^\circ\xrightarrow{\pi_A}(W\cap U_A)^\perp\to0$。有限情形下，它给出的正是 S1/S2 的维数。

(b) 数据的忠实性：
- 结论：$W=\{v\in k^{(I)}:\langle v,\cdot\rangle$ 在 $\mathcal S$ 上取常值$\}$，并且 $\beta(v)$ 就是这个常值。
- 证明：对 $v\notin W$，用 G1 的构造（取 $M=W$）得到 $z\in W^\circ$，使 $\langle v,z\rangle=1$。于是 $\langle v,x+z\rangle\neq\langle v,x\rangle$，$v$ 在 $\mathcal S$ 上不是常值。
- 推论：非空解集与数据对 $(W,\beta\in W^*)$ 一一对应，而且每一对都能实现（取 $W$ 的一组基作为行）。
- 如果把题目里的"分类"读作"解集按代数数据分类"，就应补上这一条。答卷采用的读法是"$\pi_A$ 的单射/满射分类"，也是合理的。

---

## 三、对 current-check 的核查

**论据 1（扩充系统）：正确。**
- $k$ 离散时，$k^A$ 的基本开邻域就是有限坐标柱集 $[B,y^*|_B]$。所以 $y^*$ 在闭包中，当且仅当对每个有限 $B\subseteq A$ 都存在 $x\in\mathcal S$ 使 $x|_B=y^*|_B$。
- 扩充系统的行指标集是 $J\sqcup A$，所有行都有限支撑，而且每个有限子系统都可解，所以 S4 给出整体解。
- 附带的推论：同样的论证说明，S3 的"有限可实现性"刻画对任意域都成立，不必假设 $k$ 有限。

**论据 2：正确**，与 S6 的论证相同。

**论据 3（线性紧性）：在所引定理成立的前提下正确。** 它用到三条事实：
- (i) $k$ 离散时 $k^I$ 线性紧。这是线性紧空间的乘积定理，Lefschetz 引入线性紧概念时给出的标准结果；具体章节号我没有核对。
- (ii) 线性紧空间中的闭线性簇是线性紧的；线性紧集在连续仿射映射下的像仍是线性紧的。
- (iii) 在 Hausdorff 的线性拓扑空间里，线性紧的线性簇是闭的。

(iii) 可以直接证明：
1. 设 $v\in\overline L$。对每个开子空间 $U$，$(v+U)\cap L$ 是 $L$ 的非空闭线性簇；这里用到开子空间同时也是闭的。
2. 开子空间的有限交仍是开子空间，所以这族集合有有限交性质。
3. 由线性紧性，存在 $\ell$ 属于所有 $(v+U)\cap L$，于是 $\ell-v\in\bigcap U=\overline{\{0\}}=\{0\}$，即 $v=\ell\in L$。

另外要说明，论据 3 并不是独立于 S4 的新证据，因为 $k^I$ 的线性紧性与 S4 的存在定理本质上等价：
- $k^I$ 的闭子空间 $C$ 恰好等于 $(C_\perp)^\circ$，其中 $C_\perp=\{v\in k^{(I)}:\langle v,C\rangle=0\}$。理由：若 $x\notin C$，由闭性存在有限 $B$ 使 $x|_B\notin\pi_B(C)$；在有限维空间 $k^B$ 中取 $v$ 零化 $\pi_B(C)$ 且 $v\cdot x|_B\neq0$，再把 $v$ 零延拓到 $k^{(I)}$ 即可。
- 因此，一族具有有限交性质的闭线性簇，就是一个每个有限子系统都可解的有限支撑方程组，S4 给出它们的公共点。

**存在的问题：**
- "S1–S6 无任何漏洞""无可辩驳的数学确定性"这一总括断言不成立，见 G1、G4。
- Bourbaki《Algèbre》Ch. II §7 这一出处无法离线核实；三条论据都不依赖它。
- "Hahn–Banach"这个叫法不严格。这里只需要代数上的线性泛函延拓（基扩充，在 ZFC 中由 Zorn 引理得到），不涉及半范数控制，而一般域上本来也没有序结构。"基扩充公理"应称为基扩充定理。
- "闭仿射子空间为线性紧子空间"应改称"线性簇"。
- "拓扑拓扑"是笔误。
- 维持 `KEEP` 的决定就结论而言是对的，但应同时补上 G1。

---

## 四、计算核验（本轮实际运行）

脚本见附录，没有沿用上一轮的任何数据。

**生成方式：**
- 在 $\mathbb F_2,\mathbb F_3,\mathbb F_5$ 上随机生成相容系统，规模分别为 $|I|\le6,5,4$，$|J|\le6,5,3$。
- 有至少两行时，以 0.3 的概率令前两行相同，以覆盖行线性相关的情形。
- 一半样本的右端随机生成，只保留相容的系统。
- $A$ 随机选取。

**穷举检验的内容：**
- $\beta$ 良定；
- S2 的三个计数，以及维数恒等式；
- 对每个 $y\in k^A$ 检验 S1/S4 的像判据；
- S4 分类表的单射判据和满射判据；
- S6 中基方程的互不冗余性；
- $\pi_A(W^\perp)=(W\cap U_A)^\perp$。

**结果：**
- 共 5500 个系统（3000 / 2000 / 500），**0 个失败**。
- 其中单射情形 1615 / 1204 / 312 例，满射情形 1604 / 1148 / 318 例。
- 变异检验：把像计数的指数改成 $+1$，或者把满射判据取反，5500 例全部失败。这说明各项检验确实在起作用。
- G2 的反例：程序确认 $\pi_A$ 是满射。
- S5：$N=10$ 时，行 $1..N$ 的全部 1024 个子集 $F$ 都能由 $\mathbf 1_{[1,\max F]}$ 解出。

这些检验只覆盖有限维情形，支持的是 S1、S2 以及 S4/S6 判据的有限版本。无限情形的依据是第一、二节的证明。

---

## 五、本轮修订说明与自评

**保留的内容：**
- 上一版的全部判定：答卷正确；S4 成立，S5 否，S6 是。
- 问题 G1–G5 及其补法。
- 对 current-check 三条论据的评价。

**新增和修正：**
- 计算核验在本轮重新运行，并扩大了范围：加入 $\mathbb F_5$，加大规模，强制相关行，随机右端，并做了变异检验。上一版报告的"800 例"不再引用。
- 新增问题表（位置、性质、影响），并对 G2 给出具体反例且做了机检。
- 新增可选补强 (b)：数据 $(W,\beta)$ 由 $\mathcal S$ 唯一决定，附证明。
- 新增两点有证明的观察：论据 1 说明 S3 的刻画对任意域成立；论据 3 与 S4 本质等价。
- 术语评价改得更准确："Hahn–Banach"只是叫法不严格，不算数学错误。

**仍不确定的部分：**
- current-check 引用的 Bourbaki 出处和 Lefschetz 的具体章节号都没有离线核实。本报告的所有判断都不依赖这些引用。
- 把 G1 定为"完整性缺口而非错误"属于判断。如果题中"分类"另有所指，答卷的覆盖面评价也会随之变化，见可选补强 (b)。

**自评：** 本报告中每一个"正确"或"不正确"的判断都附有可核查的证明或反例，计算结果都是本轮实际运行的输出，没有把未经证明的断言当作结论。结论是"答卷正确；S4 的分类论证有可补的缺口；current-check 的'无漏洞'断言不成立"，我认为这个结论有充分依据。

---

## 附录：本轮运行的脚本（`verify_compact.py` 全文，`python3 -I` 运行）

```python
import itertools as it, random

def rank(rows, p):
    M, r = [list(x) for x in rows], 0
    for c in range(len(M[0]) if M else 0):
        piv = next((i for i in range(r, len(M)) if M[i][c] % p), None)
        if piv is None: continue
        M[r], M[piv] = M[piv], M[r]
        inv = pow(M[r][c], p - 2, p); M[r] = [v * inv % p for v in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c] % p:
                f = M[i][c]; M[i] = [(a - f * b) % p for a, b in zip(M[i], M[r])]
        r += 1
    return r

def check(p, n, rows, b, A):
    dot = lambda u, v: sum(x * y for x, y in zip(u, v)) % p
    pts = list(it.product(range(p), repeat=n))
    S = [x for x in pts if all(dot(r, x) == c for r, c in zip(rows, b))]
    if not S: return None
    dW = rank(rows, p); dWU = rank(rows + [[int(k == i) for k in range(n)] for i in A], p)
    beta, ok = {}, True                      # beta(sum c_j a_j) = sum c_j b_j; well-definedness checked
    for c in it.product(range(p), repeat=len(rows)):
        w = tuple(sum(cj * r[i] for cj, r in zip(c, rows)) % p for i in range(n))
        v = sum(cj * bj for cj, bj in zip(c, b)) % p
        ok &= beta.setdefault(w, v) == v
    WU = [w for w in beta if all(w[i] == 0 for i in range(n) if i not in A)]   # W ∩ U_A
    dWcU = rank([list(w) for w in WU], p)
    img = {}
    for x in S: img.setdefault(tuple(x[i] for i in A), []).append(x)
    ys = list(it.product(range(p), repeat=len(A)))
    ev = lambda w, y: sum(w[i] * t for i, t in zip(A, y)) % p
    ok &= len(S) == p ** (n - dW) and len(img) == p ** (dWU - dW)               # S2
    ok &= all(len(f) == p ** (n - dWU) for f in img.values()) and dWU == dW + len(A) - dWcU
    ok &= all((y in img) == all(ev(w, y) == beta[w] for w in WU) for y in ys)  # S1 / S4 image
    inj, surj = all(len(f) == 1 for f in img.values()), len(img) == p ** len(A)
    ok &= inj == (dWU == n) and surj == (dWcU == 0)                             # S4 table
    basis = []
    for w in WU:
        if rank([list(u) for u in basis + [w]], p) > len(basis): basis.append(w)
    for mu in range(len(basis)):                                                # S6 non-redundancy
        ok &= any(ev(basis[mu], y) != beta[basis[mu]] and
                  all(ev(w, y) == beta[w] for l, w in enumerate(basis) if l != mu) for y in ys)
    img0 = {tuple(x[i] for i in A) for x in pts if all(dot(r, x) == 0 for r in rows)}
    ok &= img0 == {y for y in ys if all(ev(w, y) == 0 for w in WU)}             # pi_A(W^perp) = (W∩U_A)^perp
    return ok, inj, surj

def run(p, trials, maxI, maxJ, seed):
    rng, st = random.Random(seed), dict(tests=0, fails=0, inj=0, surj=0)
    while st['tests'] < trials:
        n, m = rng.randint(1, maxI), rng.randint(0, maxJ)
        rows = [[rng.randrange(p) for _ in range(n)] for _ in range(m)]
        if m >= 2 and rng.random() < 0.3: rows[1] = list(rows[0])               # force dependent rows
        x0 = [rng.randrange(p) for _ in range(n)]
        b = [sum(a * x for a, x in zip(r, x0)) % p for r in rows]
        if rng.random() < 0.5: b = [rng.randrange(p) for _ in rows]             # random rhs, kept if consistent
        res = check(p, n, rows, b, [i for i in range(n) if rng.random() < 0.5])
        if res is None: continue
        st['tests'] += 1; st['fails'] += not res[0]; st['inj'] += res[1]; st['surj'] += res[2]
    return st

for p, trials, mI, mJ in [(2, 3000, 6, 6), (3, 2000, 5, 5), (5, 500, 4, 3)]:
    print('F_%d' % p, run(p, trials, mI, mJ, seed=p))
print('a1=a2=e1, b=(1,1), A={2}: surjective =', check(2, 2, [[1, 0], [1, 0]], [1, 1], [1])[2])
N = 10                                        # S5: rows x1=1, x_{j-1}-x_j=0 restricted to 1..N
rowsS5 = [[int(i == 0) for i in range(N)]] + [[int(i == j - 2) - int(i == j - 1) for i in range(N)] for j in range(2, N + 1)]
bS5 = [1] + [0] * (N - 1)
print('S5 finite subsystems solved by 1_[1,max F]:', all(
    all(sum(a * x for a, x in zip(rowsS5[j - 1], [int(i < max(F, default=0)) for i in range(N)])) == bS5[j - 1] for j in F)
    for m in range(N + 1) for F in it.combinations(range(1, N + 1), m)))
```

实际输出：
```
F_2 {'tests': 3000, 'fails': 0, 'inj': 1615, 'surj': 1604}
F_3 {'tests': 2000, 'fails': 0, 'inj': 1204, 'surj': 1148}
F_5 {'tests': 500, 'fails': 0, 'inj': 312, 'surj': 318}
a1=a2=e1, b=(1,1), A={2}: surjective = True
S5 finite subsystems solved by 1_[1,max F]: True
```