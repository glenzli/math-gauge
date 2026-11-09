复核与数值验证均已完成，现在给出审阅结论。

---

# 答卷审阅报告

## 0. 总结论

**待审答卷（`original-answer.md` 的 S1–S6 正文 + `current-check.md` 的核查论证）在原题条件下正确，且（除两处“论证从简/文献存疑”级别的小瑕疵外）完整。** 六个部分的判定——S1–S4、S6 各目标成立，S5 目标不成立——经逐条独立复核全部成立；关键公式、判据、构造、拓扑论证与反例均无数学错误。我对有限维/有限域情形另做了穷举数值验证（GF(2)、GF(3)、GF(5)，共 1760 组随机系统 + 定向截断检验，全部通过，见 §7）。

发现的问题清单见 §8：仅 (a) S4 分类表的两处等价条件未写出完整证明（条件本身正确，本报告补证）；(b) `current-check.md` 论据 3 的 Bourbaki 引文无法离线核实、归属存疑（该论据数学内容正确且冗余）；(c) 若干极微措辞问题。**因此 `current-check.md` 维持 KEEP 的决定是正确的**，但其“均无任何漏洞”“无可辩驳”等绝对化措辞相对上述小瑕疵略有夸张。

## 1. S1（有限系统的坐标纤维）——**正确**

**断言 1**：$\dim\mathcal{S}=|I|-\dim W$。核实：相容性给出特解 $x_0$，$\mathcal{S}=x_0+W^\perp$，$W^\perp=\{x:a_j\cdot x=0\ \forall j\}$；$I$ 有限时点积配对非退化，$\dim W^\perp=|I|-\dim W$。✓

**断言 2**：非空纤维方向 $=W^\perp\cap U_A^\perp=(W+U_A)^\perp$，维数 $|I|-\dim(W+U_A)$。核实两条关键换算：$x|_A=0\iff x_i=0(\forall i\in A)\iff x\in U_A^\perp$（因 $e_i\in U_A$）；零化子将子空间和变为交。✓ 括号中的等价式 $|I|-\dim W-|A|+\dim(W\cap U_A)$ 由 $\dim(W+U_A)=\dim W+|A|-\dim(W\cap U_A)$ 立得。✓

**断言 3**（延拓判据）：$y$ 可延拓 $\iff\forall w\in W\cap U_A$，$\sum_{i\in A}w_iy_i=\beta(w):=\sum_jc_jb_j$（$w=\sum_jc_ja_j$）。逐环节核实：

- **良定性**：若 $\sum c_ja_j=\sum c'_ja'_j$，差是有限关系，与相容特解 $x_0$ 配对得 $\sum(c_j-c'_j)b_j=0$。✓（答卷的括号说明正确，这正是唯一用到“相容”假设之处。）
- **必要性**：$\sum_{i\in A}w_iy_i=\langle w,x\rangle=\sum_jc_j\langle a_j,x\rangle=\sum_jc_jb_j$。✓
- **充分性**：取 $T:W^\perp\to k^A,\ v\mapsto v|_A$，需 $z=y-x_0|_A\in\operatorname{Im}T$。答卷的伴随论证可独立重推：直接验证 $\ker T^*=\operatorname{Im}(T)^\perp$（$u\in\ker T^*\iff u\cdot T(v)=0\ \forall v\in W^\perp$），故 $\operatorname{Im}T=(\operatorname{Im}T)^{\perp\perp}=(\ker T^\perp)^\perp$（有限维双零化定理，适用条件 $I$ 有限在此成立）；又 $u\in\ker T^*\iff\iota_A(u)\in(W^\perp)^\perp=W\iff \iota_A(u)\in W\cap U_A$，且 $u\mapsto\iota_A(u)$ 是 $\ker T^*\to W\cap U_A$ 的双射。于是 $z\in\operatorname{Im}T\iff\sum_{i\in A}w_iy_i=\beta(w)$。∎

值得肯定：答卷**只在有限维处**使用 $(W^\perp)^\perp=W$ 与 Fredholm 型对偶，并在 S4 起改用代数对偶 $k^I\cong(k^{(I)})^*$，没有把有限维事实非法外推到无限维——这正是本题最大的陷阱，答卷规避正确。

## 2. S2（有限域计数）——**正确**

三条公式逐一核实：$|\mathcal{S}|=q^{|I|-\dim W}$（仿射空间计数）；纤维 $|\mathcal{F}_y|=q^{|I|-\dim(W+U_A)}$；由 $\pi_A|_\mathcal{S}$ 把 $\mathcal{S}$ 划分为等大小纤维得 $|\pi_A(\mathcal{S})|=q^{|I|-\dim W}/q^{|I|-\dim(W+U_A)}=q^{\dim(W+U_A)-\dim W}$（亦 $=q^{|A|-\dim(W\cap U_A)}$，即像的仿射维数）。所有公式只含 $|I|,\dim W,\dim(W+U_A)$（及给定的 $q$），满足原题限制。数值穷举验证通过（§7）。

## 3. S3（有限域的无限坐标拓扑）——**正确**

- **非空紧**：每行 $a_j$ 有限支撑 $\Rightarrow f_j$ 是有限个坐标投影的组合，连续；$k$ 离散 $\Rightarrow\{b_j\}$ 闭 $\Rightarrow\mathcal{S}_j=f_j^{-1}(b_j)$ 闭；有限交性质由“每个有限子系统可解”逐字给出；Tychonoff（ZFC 下成立，答卷说明了适用前提）+ FIP $\Rightarrow\mathcal{S}\neq\emptyset$；闭子集继承紧。✓
- **全不连通**：所用事实“全不连通空间的任意积全不连通、子空间遗传”为标准结论（两行证明：连通子集 $C\subseteq\prod X_i$ 的每个投影连通；若 $C$ 含相异两点则某投影含两点，与 $X_i$ 全不连通矛盾）。✓
- **像闭**：$\pi_A$ 连续、$\mathcal{S}$ 紧、$k^A$ Hausdorff，紧像必闭。✓（注意：此证明用到 $k$ 有限（紧性），在 S6 被正确地替换为不依赖紧性的方法，两处无循环。）
- **刻画**：充分性方向的 FIP 论证正确，且关键点把握准确——假设只要求“有限行 + 有限坐标”同时可解（不要求全解存在），紧性恰好把它桥接到全解。✓

## 4. S4（整体对象与恢复理论）——**正确；分类表论证从简（唯一实质性的完整性小瑕疵）**

逐条核实：

- $k^I\cong(k^{(I)})^*$，$x\mapsto\varphi_x$（因每个 $v\in k^{(I)}$ 支撑有限）✓。
- **$\beta$ 良定**：对有限关系 $\sum_{j\in F}c_ja_j=0$，用**指标恰为 $F$ 的那个有限子系统的解** $x^{(F)}$ 配对得 $\sum c_jb_j=0$——对假设的引用准确。✓
- **整体解**：$\mathcal{B}_W$ 扩基（Zorn，ZFC 允许）定义 $\tilde\beta$，$x_i^*=\tilde\beta(e_i)$；验算 $\sum_ia_j(i)x_i^*=\tilde\beta(a_j)=\beta(a_j)=b_j$（$a_j=\sum_ia_j(i)e_i$ 为有限和）。✓
- $\mathcal{S}=x^*+W^\circ=\{x:\langle w,x\rangle=\beta(w)\ \forall w\in W\}$：两个包含都是一行验算。✓ 数据 $(W,\beta)$ 仅由给定 $(a_j),(b_j)$ 确定，满足原题“仅由给定系数和常数确定的代数数据”的要求（构造用了选择，但描述不依赖选择）。✓
- **像定理** $\pi_A(\mathcal{S})=\{y:\sum_{i\in A}w_iy_i=\beta(w)\ \forall w\in W\cap U_A\}$：$\subseteq$ 一行；$\supseteq$ 中 $\psi(w+u)=\beta(w)+\gamma_y(u)$ 的良定性验算（$w-w‘=u’-u\in W\cap U_A\Rightarrow\beta(w-w')=\gamma_y(u'-u)$）正确，扩基成 $\Phi$ 后两端（$w\in W$、$e_i,i\in A$）核对无误。✓
- **纤维** $\pi_A^{-1}(y)\cap\mathcal{S}=x+(W+U_A)^\circ$，双向验算正确。✓

**分类表（§5）**：三行的充要条件**均正确**，但按原题“完整论证”的标准，两步推理未写出，需补：

1. **单射行**所用等价 $(W+U_A)^\circ=\{0\}\iff W+U_A=k^{(I)}$："$\Leftarrow$"平凡；"$\Rightarrow$"在无限维需零化子引理：取 $v_0\notin W+U_A$，将 $W+U_A$ 的基连同 $v_0$ 扩成 $V$ 的基（Zorn），定义 $\Phi(v_0)=1$、$\Phi=0$ 于其余基元，则 $x:=(\Phi(e_i))_i\in k^I$ 非零且 $\langle w+u,x\rangle=\Phi(w+u)=0$，故 $(W+U_A)^\circ\neq\{0\}$。∎
2. **满射行**的反方向：若 $0\neq w\in W\cap U_A$，取 $i_0\in A$ 使 $w_{i_0}\neq0$，令 $y$ 仅在 $i_0$ 处取 $t\neq\beta(w)/w_{i_0}$，则 $y\notin\pi_A(\mathcal{S})$，故不满。∎

补上这两行后表格完全成立（单射 ⟺ 纤维方向为零 ⟺ 条件 1；满射 ⟺ 判据为空 ⟺ 条件 2；双射 ⟺ 直和）。这是**完整性上的小缺口，不影响任何结论**。

## 5. S5（赋值空间的支持）——**正确，反例有效**

反例（$x_1=1$；$x_{j-1}-x_j=0,\ j\ge2$）逐条验证：

- 行支撑有限 ✓；
- 任意非空有限 $F$：取 $M=\max F$，$x=\mathbf 1_{[1,M]}$ 有限支撑；$1\in F$ 时 $x_1=1$；$j\in F,j\geq2$ 时 $j-1<j\le M$ 故 $x_{j-1}=x_j=1$，方程成立（对 $F$ 不含 $1$、含间断、单点等情形均验过）✓（$F=\emptyset$ 取 $x=0$ 即可，答卷未提，属极微省略）；
- 全系统解被归纳逼成全 $1$ 序列，支撑 $=\mathbb N$ 无限 $\Rightarrow$ 不在 $k^{(\mathbb N)}$ 中 ✓；且全系统在 $k^{\mathbb N}$ 中可解，与 S4 不矛盾（一致性正确）。任何域（$1\neq0$）均适用。**判定“不成立”正确。** ✓

## 6. S6（无限域的坐标像）——**正确**

- **判定“闭”成立**：$g_w=L_w\circ p_{F_w}$，其中 $F_w=\operatorname{supp}(w)\subseteq A$ 有限；$k^{F_w}$ 是有限个离散空间之积、本身离散，故 $L_w$ 自动连续，$p_{F_w}$ 连续；$\{\beta(w)\}$ 在离散 $k$ 中 clopen $\Rightarrow C_w=g_w^{-1}(\{\beta(w)\})$ clopen；**任意交闭**。论证完全未用 $k$ 的有限性，故对无限离散域成立。✓
- **基归约**：由 $\sum w_iy_i$ 与 $\beta(w)$ 对 $w$ 的线性性，约束在基上成立即在全空间 $W\cap U_A$ 上成立。（顺带核实：“互不冗余”也真：由上面的零化子引理，对每个基元 $w_{\lambda_0}$ 存在 $y$ 满足其余全部方程而独独违反第 $\lambda_0$ 条，配合像非空取 $y‘=y^*+y$ 即得。）
- 方程“只涉及有限坐标”成立：$W\cap U_A\subseteq k^{(A)}$ 中每个 $w$ 支撑有限。注意方程族一般必须无穷多条（例：$I=\{0\}\cup\mathbb N_{\ge1}$，行 $e_0-e_n$，$A=\mathbb N_{\ge1}$ 时 $\pi_A(\mathcal{S})=\{$常值序列$\}$ 是闭而非开的对角线，不可能由有限条此类方程表出——答卷的解读是唯一可行的）。
- 另外我核对了一个手算例（常值序列系统，见 §7 的定向检验）：像 $=$ 常值元组，与判据 $\sum v_ny_n=0\ (\forall v,\ \sum v_n=0)$ 完全一致，与 S4/S6 理论吻合。

## 7. 数值验证（可复现）

脚本 `verify_answer.py`（全文附于文末）穷举验证了：S1/S2 全部公式、延拓判据逐点等价、$\beta$ 按表示定义的良定性（并与特解配对对照）、S4 像公式与纤维描述逐点一致、S5 反例的截断行为、以及“常值序列”无穷系统的截断像。参数：$k=\mathrm{GF}(2),\mathrm{GF}(3)$（$|I|\le4$）、$\mathrm{GF}(5)$（$|I|\le3$），$|J|\le3$，随机 $A\subseteq I$（含 $A=\varnothing,A=I$、行退化等情形），共 1760 组随机系统 + 全部定向检验。

```text
$ python3 -I verify_answer.py
ALL CHECKS PASSED; random finite-system trials = 1760
```

## 8. 对 `current-check.md` 三条论据的核查

**论据 1（闭包 + 增广系统 + S4）——正确。** 逐步核实：$y^*\in\overline{\pi_A(\mathcal S)}$ $\Rightarrow$ 每个基本开柱 $\{y:y|_B=y^*|_B\}$（$B\subseteq A$ 有限）与像相交 $\Rightarrow$ 存在**全解** $x\in\mathcal S$ 使 $x|_B=y^*|_B$；增广系统的行（原行 + 单点支撑的 $e_i$）均有限支撑；其任意有限子系统相容；S4 定理的适用条件（任意域、行有限支撑、有限子系统皆可解）被正确核对，故增广系统有整体解 $x^*$，$x^*\in\mathcal S$ 且 $x^*|_A=y^*$。这本质上是 S3(c) 的紧性论证在任意域上的代数化移植，正确且不循环。

**论据 2（S4 公式 + clopen + 任意交闭）——正确**，与 `original-answer.md` 的 S6 相同。

**论据 3（线性紧性）——数学内容正确，引文存疑、且冗余。** 内容可直接验证：(i) 离散域 $k$ 对自身线性紧（一维空间的线性子空间陪集只有单点与全空间，FIP 族之交非空）；(ii) 本特例中 $k^I$ 的线性紧性**恰可由 S4 定理直接推出**：$k^I$ 的闭线性子空间 $V$ 是有限支撑泛函核之交（若 $x\notin V$，某基本开陪集 $x+N_B$ 与 $V$ 不交，在有限维 $k^B$ 中以线性泛函分离），故闭陪集的 FIP 族 = 有限支撑线性方程组的有限可解系统，S4 给出公共解；(iii) 闭仿射子集（把自身并入族）与连续线性像（商空间论证）保持线性紧；(iv) Hausdorff 中线性紧 $\Rightarrow$ 闭：对 $C=c_1+C_0$ 与 $y\in\overline C$，族 $\{(y+N_B)\cap C\}_B$ 是 $C_0\cap N_B$（在 $C$ 中闭）的非空陪集且 FIP，其公共点 $z$ 满足 $z-y\in\bigcap_BN_B=\{0\}$，故 $y=z\in C$。∎ 但其中引用 “Bourbaki (*Algèbre*, Chap. II, §7)” 无法在本离线环境核实，且按通行文献归属，线性紧空间理论出自 Lefschetz (1942) 及其后 Dieudonné 一系（Bourbaki 若有涉及，载体也更可能是《拓扑向量空间》而非《代数》）。**即便确系误引，也只影响文献层面**——内容已如上直接验证，且在论据 1、2 已充分的情况下该论据是冗余的。

**措辞**：“均无任何漏洞”“无可辩驳的数学确定性”属夸张修辞：数学断言本身经核查无误，但鉴于 §4 末与上述引文两处小瑕疵，这一全称断言略强于实情；不影响 KEEP 的结论。

## 9. 问题清单及影响

| # | 位置 | 问题 | 影响 |
|---|------|------|------|
| 1 | `original-answer.md` S4 §5 分类表 | 单射/满射两行的充要条件未附完整证明（无限维零化子引理、非平凡约束确能排除点这两步被省略） | 仅完整性从简；**条件本身正确**（本报告 §4 补证），不影响判定 |
| 2 | `current-check.md` 论据 3 | Bourbaki 引文位置无法离线核实、归属存疑 | 仅文献精度；数学内容正确且可独立验证；该论据冗余，不影响 KEEP |
| 3 | S5 验证、check 论据 1 | 未提 $F=\emptyset$（取 $x=0$ 即可）；“Hahn-Banach/基扩充”措辞宽松（实际只用基扩充） | 无实质影响 |

其余全部断言（S1 维数与判据、S2 三公式、S3 的四项结论、S4 的构造与三个刻画、S5 反例、S6 判定与描述、check 的论据 1、2）经独立复核与穷举验证**均正确**。

## 10. 最终判定

- **正确性**：通过。六个部分的判定、公式、构造、反例全部正确。
- **完整性**：除问题 1、2 两处小瑕疵外满足原题要求（含“援引标准定理时说明适用条件”：Tychonoff 于 ZFC、有限维对偶定理于 $I$ 有限、Zorn 于 ZFC、S4 定理的适用前提在 check 中被逐一核对）。
- **KEEP 的决定：成立。** 本轮核查所作的全部数学断言经检验无误，维持原答卷是正确的处置。

### 附：验证脚本（`verify_answer.py`，已运行通过）

```python
#!/usr/bin/env python3
# Independent brute-force verification of the finite-case claims of the
# reviewed answer (S1 dimension/counting formulas, extendability criterion,
# S4 image & fiber descriptions, S5 counterexample on truncations),
# plus one truncated infinite example (constant-sequence system) for S4/S6.
import itertools, random

def inv_mod(a, p): return pow(a % p, -1, p)

def rref(mat, p):
    A = [row[:] for row in mat]
    m = len(A); n = len(A[0]) if A else 0
    piv = []; r = 0
    for c in range(n):
        pr = None
        for i in range(r, m):
            if A[i][c] % p: pr = i; break
        if pr is None: continue
        A[r], A[pr] = A[pr], A[r]
        iv = inv_mod(A[r][c], p)
        A[r] = [(x*iv) % p for x in A[r]]
        for i in range(m):
            if i != r and A[i][c] % p:
                f = A[i][c]
                A[i] = [(u - f*v) % p for u, v in zip(A[i], A[r])]
        piv.append(c); r += 1
    A = [row for row in A if any(row)]
    return A, piv

def dim_span(rows, p):
    if not rows: return 0
    R, _ = rref([list(r) for r in rows], p)
    return len(R)

def solve_cols(cols, target, p):
    """one solution c of sum_j c_j*cols[j] = target, or None"""
    m = len(cols)
    if m == 0:
        return [] if all(t % p == 0 for t in target) else None
    n = len(target)
    aug = [[cols[j][i] for j in range(m)] + [target[i] % p] for i in range(n)]
    R, piv = rref(aug, p)
    for row in R:
        if all(x % p == 0 for x in row[:m]) and row[m] % p:
            return None
    c = [0]*m
    for idx, pc in enumerate(piv):
        if pc < m: c[pc] = R[idx][m] % p
    return c

def dotp(u, v, p): return sum(a*b for a, b in zip(u, v)) % p

def brute_S(rows, b, p, n):
    return [x for x in itertools.product(range(p), repeat=n)
            if all(dotp(r, x, p) == b[j] for j, r in enumerate(rows))]

def check_random(p, n, m):
    rows = [tuple(random.randrange(p) for _ in range(n)) for _ in range(m)]
    x0 = tuple(random.randrange(p) for _ in range(n))
    b = [dotp(r, x0, p) for r in rows]          # consistent, x0 in S
    A = [i for i in range(n) if random.randrange(2)]
    eA = [tuple(1 if i == t else 0 for i in range(n)) for t in A]
    dimW = dim_span(rows, p); dimWUA = dim_span(list(rows) + eA, p)
    S = brute_S(rows, b, p, n)
    assert len(S) == p**(n - dimW), "S2(1) solution count"          # S2 (1)
    img = {}
    for x in S: img.setdefault(tuple(x[i] for i in A), []).append(x)
    assert len(img) == p**(dimWUA - dimW), "S2(3) image size"       # S2 (3)
    for y, f in img.items():
        assert len(f) == p**(n - dimWUA), "S2(2) fiber size"        # S2 (2)
    # beta on W cap U_A defined from representations (tests well-definedness)
    if rows:
        Wset = set()
        for cs in itertools.product(range(p), repeat=len(rows)):
            v = [0]*n
            for c, rw in zip(cs, rows):
                for i in range(n): v[i] = (v[i] + c*rw[i]) % p
            Wset.add(tuple(v))
    else:
        Wset = {(0,)*n}
    WUA = [w for w in Wset if all(w[i] == 0 for i in range(n) if i not in A)]
    beta = {}
    for w in WUA:
        c = solve_cols(rows, list(w), p)
        assert c is not None
        beta[w] = sum(ci*bj for ci, bj in zip(c, b)) % p
        assert beta[w] == dotp(w, x0, p), "beta well-defined"       # consistency
    for y in itertools.product(range(p), repeat=len(A)):
        ext = any(tuple(x[i] for i in A) == y for x in S)
        crit = all(dotp(tuple(w[i] for i in A), y, p) == beta[w] for w in WUA)
        assert ext == crit, "S1 criterion / S4 image formula"
    # S4 fiber description: fiber = x + {v : rows.v=0, v|A=0}
    D = [v for v in itertools.product(range(p), repeat=n)
         if all(dotp(r, v, p) == 0 for r in rows) and all(v[i] == 0 for i in A)]
    y0 = next(iter(img)); xf = img[y0][0]
    assert {tuple((xf[i]+v[i]) % p for i in range(n)) for v in D} == set(img[y0]), "fiber desc"
    return True

def check_s5_truncation(p, N):
    # rows: eq1 x_1=1; eq j>=2 x_{j-1}-x_j=0, truncated to coords 1..N
    rows = [[1] + [0]*(N-1)]; b = [1]
    for e in range(1, N):
        r = [0]*N; r[e-1] = 1; r[e] = (p-1) % p
        rows.append(r); b.append(0)
    sols = brute_S(rows, b, p, N)
    assert sols == [tuple(1 % p for _ in range(N))], "truncated full system = all-ones"
    for k in range(1, N+1):
        for F in itertools.combinations(range(N), k):
            M = max(F) + 1
            x = tuple(1 if i < M else 0 for i in range(N))  # finitely supported
            assert all(dotp(rows[j], x, p) == b[j] for j in F), "finite subsystem"
    return True

def check_constseq_truncation(p, T):
    # infinite example: rows e_0 - e_n (n>=1), b=0 ; A = {1..T}
    n = T + 1
    rows = []
    for j in range(1, T+1):
        r = [0]*n; r[0] = 1; r[j] = (p-1) % p
        rows.append(r)
    b = [0]*T
    S = brute_S(rows, b, p, n)
    A = list(range(1, T+1))
    img = {tuple(x[i] for i in A) for x in S}
    consts = {tuple(c % p for _ in range(T)) for c in range(p)}
    assert img == consts, "image = constant tuples"
    # criterion via W cap U_A (beta = 0)
    Wset = set()
    for cs in itertools.product(range(p), repeat=T):
        v = [0]*n
        for c, rw in zip(cs, rows):
            for i in range(n): v[i] = (v[i] + c*rw[i]) % p
        Wset.add(tuple(v))
    WUA = [w for w in Wset if w[0] == 0]
    for y in itertools.product(range(p), repeat=T):
        crit = all(dotp(tuple(w[i] for i in A), y, p) == 0 for w in WUA)
        assert crit == (y in consts), "S4/S6 image formula on infinite-type system"
    return True

random.seed(20260911)
cnt = 0
for p in (2, 3, 5):
    maxn = 4 if p < 5 else 3
    for n in range(1, maxn+1):
        for m in range(0, 4):
            for _ in range(40):
                check_random(p, n, m); cnt += 1
for p in (2, 3, 5):
    for N in range(1, 6): check_s5_truncation(p, N)
    for T in range(1, 5): check_constseq_truncation(p, T)
print("ALL CHECKS PASSED; random finite-system trials =", cnt)
```