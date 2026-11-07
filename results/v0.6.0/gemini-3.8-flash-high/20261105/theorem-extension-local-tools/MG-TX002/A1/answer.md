这个结论是成立的，它属于代数组合学中关于偏序集上 **Rowmotion（行运动）** 的 **Homomesy（均值同态 / 轨道同均）** 定理（由 Jim Propp 与 Tom Roby 于 2015 年证明）。

下面给出一个完全初等、严密且自洽的证明。

---

### 一、 概念与符号设定

设偏序集 $P = \{1, \dots, a\} \times \{1, \dots, b\}$，其上的偏序为坐标序：
$$(i, j) \le (i', j') \iff i \le i' \text{ 且 } j \le j'$$

1. **反链与阶理想的对应**：
   - 对于反链 $A$，其生成的阶理想（下闭子集）为：
     $$I(A) = \{u \in P : \exists v \in A, u \le v\}$$
   - 反过来，对于任意阶理想 $I \subseteq P$，其极大元素构成的集合 $\max(I)$ 是一条反链，且满足 $I(\max(I)) = I$ 以及 $\max(I(A)) = A$。因此反链与阶理想之间存在双射。

2. **Rowmotion 映射 $R$**：
   - $P \setminus I(A)$ 是一个滤子（上闭子集）。
   - $R(A) = \min(P \setminus I(A))$ 为该滤子的全部极小元素组成的反链。
   - $R$ 是 $P$ 的全体反链集合 $\mathcal{A}(P)$ 上的一个置换。设 $O$ 为 $R$ 的任意一条轨道，其长度为 $|O|$。

3. **行与列的示性统计量**：
   对于任意反链 $A$，因为 $A$ 中任意两不同元素不可比，所以在同一行 $\{i\} \times \{1, \dots, b\}$ 中至多只能有一个元素，在同一列 $\{1, \dots, a\} \times \{j\}$ 中也至多只能有一个元素。
   
   因此，我们可以定义行指示变量 $r_i(A)$ 和列指示变量 $c_j(A)$：
   $$r_i(A) = |A \cap (\{i\} \times \{1, \dots, b\})| = \begin{cases} 1, & A \text{ 在第 } i \text{ 行有元素}, \\ 0, & A \text{ 在第 } i \text{ 行无元素}, \end{cases} \quad (1 \le i \le a)$$
   $$c_j(A) = |A \cap (\{1, \dots, a\} \times \{j\})| = \begin{cases} 1, & A \text{ 在第 } j \text{ 列有元素}, \\ 0, & A \text{ 在第 } j \text{ 列无元素}, \end{cases} \quad (1 \le j \le b)$$

   显然，反链的大小 $|A|$ 分别等于各行、各列指示变量之和：
   $$|A| = \sum_{i=1}^a r_i(A) = \sum_{j=1}^b c_j(A)$$

4. **阶理想的行宽表示（Young 图）**：
   对阶理想 $I = I(A)$，记第 $i$ 行在 $I$ 中的元素个数为：
   $$\lambda_i = |\{j \in \{1, \dots, b\} : (i, j) \in I\}|$$
   因为 $I$ 是下闭集，若 $(i, j) \in I$，则 $(i, 1), \dots, (i, j) \in I$；且若 $(i+1, j) \in I$，必有 $(i, j) \in I$。故有递减关系：
   $$b \ge \lambda_1 \ge \lambda_2 \ge \dots \ge \lambda_a \ge 0$$
   特别约定边界值：$\lambda_0 = b$，$\lambda_{a+1} = 0$。
   此时，$(i, j) \in I \iff 1 \le j \le \lambda_i$。

---

### 二、 核心引理

#### 引理 1（行指示变量在 $R$ 下的平移）：
对任意 $1 \le i \le a - 1$ 及任意反链 $A \in \mathcal{A}(P)$，均有：
$$r_{i+1}(R(A)) = r_i(A)$$

**证明**：
1. **分析 $r_i(A)$**：
   元素 $(i, j) \in I$ 是极大元（即属于 $A$），当且仅当它不能再向上或向右扩展，即 $(i, j+1) \notin I$ 且 $(i+1, j) \notin I$。
   - $(i, j) \in I$ 且 $(i, j+1) \notin I \iff j = \lambda_i \ge 1$；
   - $(i+1, j) \notin I \iff \lambda_{i+1} < j$。
   将 $j = \lambda_i$ 代入，可知第 $i$ 行存在极大元当且仅当：
   $$\lambda_i > \lambda_{i+1}$$
   且该元素唯一，即 $(i, \lambda_i)$。因此：
   $$r_i(A) = 1 \iff \lambda_i > \lambda_{i+1}$$

2. **分析 $r_{i+1}(R(A))$**：
   $R(A) = \min(P \setminus I)$。元素 $(k, j) \in P \setminus I$ 是极小元，当且仅当其在 $P$ 中的下紧邻均属于 $I$。
   - 在同行中的下紧邻为 $(k, j-1)$（若 $j > 1$）；
   - 在同列中的下紧邻为 $(k-1, j)$（若 $k > 1$）。
   
   因此，$(k, j) \in R(A)$ 当且仅当：
   - $(k, j) \notin I \iff j > \lambda_k$；
   - 若 $j > 1$，则 $(k, j-1) \in I \iff j - 1 \le \lambda_k$。两式联立给出 $j = \lambda_k + 1 \le b$（特别地，当 $j=1$ 时即 $\lambda_k = 0$，结论同样为 $j = \lambda_k + 1$）；
   - 若 $k > 1$，同列下紧邻 $(k-1, j) \in I \iff j \le \lambda_{k-1}$。代入 $j = \lambda_k + 1$，得到 $\lambda_k + 1 \le \lambda_{k-1}$，即 $\lambda_{k-1} > \lambda_k$。

   现在取第 $k = i + 1$ 行（由于 $1 \le i \le a-1$，故 $k \ge 2$）：
   第 $i+1$ 行存在极小元当且仅当：
   $$\lambda_i > \lambda_{i+1} \quad \text{且} \quad \lambda_{i+1} + 1 \le b$$
   注意到，当 $\lambda_i > \lambda_{i+1}$ 成立时，由 $\lambda_i \le b$ 立得 $\lambda_{i+1} < b$，即 $\lambda_{i+1} + 1 \le b$ 自然满足！
   
   因此，第 $i+1$ 行存在极小元当且仅当 $\lambda_i > \lambda_{i+1}$。这正是 $r_i(A) = 1$ 的充要条件。
   
   从而对任意反链 $A$，恒有：
   $$r_{i+1}(R(A)) = r_i(A) \quad (1 \le i \le a-1)$$
$\blacksquare$

---

#### 引理 2（列指示变量在 $R$ 下的平移）：
对任意 $1 \le j \le b - 1$ 及任意反链 $A \in \mathcal{A}(P)$，均有：
$$c_{j+1}(R(A)) = c_j(A)$$

**证明**：
考虑映射 $\tau(i, j) = (j, i)$，它是偏序集 $[a] \times [b]$ 到 $[b] \times [a]$ 的序同构，它将行与列互换，并将反链映射为共轭 Young 图对应的反链。由于行运动映射 $R$ 的定义完全由偏序结构决定，它与序同构 $\tau$ 可交换。将引理 1 应用于转置偏序集，立得列指示变量的平移性质：
$$c_{j+1}(R(A)) = c_j(A) \quad (1 \le j \le b-1)$$
$\blacksquare$

---

#### 引理 3（边界处的行列互补关联）：
对任意反链 $A \in \mathcal{A}(P)$，恒有：
$$r_a(A) + c_1(R(A)) = 1$$

**证明**：
根据前述分析：
1. **关于 $r_a(A)$**：
   第 $a$ 行是最后一行（$\lambda_{a+1} = 0$），由引理 1 的推导可知：
   $$r_a(A) = 1 \iff \lambda_a > \lambda_{a+1} \iff \lambda_a > 0$$
   即反链 $A$ 在最后一行有元素，当且仅当阶理想 $I$ 包含元素 $(a, 1)$。

2. **关于 $c_1(R(A))$**：
   考虑第 1 列 $\{1, \dots, a\} \times \{1\}$。因为阶理想 $I$ 向下封闭，第 1 列中属于 $I$ 的元素必为前若干个，形如 $(1, 1), (2, 1), \dots, (\mu_1, 1)$，其中 $\mu_1 \in \{0, 1, \dots, a\}$。
   
   若一个元素 $(k, 1) \in R(A) = \min(P \setminus I)$，由于它没有同行左侧的紧邻，它成为极小元只需满足：
   $$(k, 1) \notin I \quad \text{且（若 } k > 1 \text{ 则 } (k-1, 1) \in I\text{）}$$
   这说明 $(k, 1)$ 必须是第 1 列中**第一个不属于 $I$ 的元素**，即 $k = \mu_1 + 1$。
   - **情况 1**：若 $(a, 1) \in I$，则 $\mu_1 = a$，第 1 列的全部 $a$ 个元素都属于 $I$。
     此时第 1 列在 $P \setminus I$ 中没有任何元素，故 $R(A)$ 在第 1 列中**没有元素**，即 $c_1(R(A)) = 0$。
     同时，由 $(a, 1) \in I$ 知 $\lambda_a \ge 1 > 0$，故 $r_a(A) = 1$。
     因此 $r_a(A) + c_1(R(A)) = 1 + 0 = 1$。
   - **情况 2**：若 $(a, 1) \notin I$，则 $\mu_1 < a$。
     此时元素 $(\mu_1 + 1, 1)$ 存在且必然是 $P \setminus I$ 的极小元，故 $R(A)$ 在第 1 列**恰有这一个元素**，即 $c_1(R(A)) = 1$。
     同时，由 $(a, 1) \notin I$ 知第 $a$ 行在 $I$ 中没有任何元素（因若有则必含 $(a, 1)$），故 $\lambda_a = 0$，从而 $r_a(A) = 0$。
     因此 $r_a(A) + c_1(R(A)) = 0 + 1 = 1$。

综上两种情况，恒有：
$$r_a(A) + c_1(R(A)) = 1$$
$\blacksquare$

---

### 三、 轨道的平均值计算与最终证明

记轨道 $O$ 上任意统计量 $f: \mathcal{A}(P) \to \mathbb{R}$ 的平均值为：
$$\overline{f} = \frac{1}{|O|} \sum_{A \in O} f(A)$$

因为 $R$ 是轨道 $O$ 上的置换，对轨道求和遍历所有元素与遍历所有 $R(A)$ 结果完全相同，故：
$$\frac{1}{|O|} \sum_{A \in O} f(R(A)) = \frac{1}{|O|} \sum_{A \in O} f(A) = \overline{f}$$

1. **各行平均值相等**：
   由引理 1，对任意 $1 \le i \le a-1$，在轨道 $O$ 上取平均：
   $$\overline{r}_{i+1} = \frac{1}{|O|} \sum_{A \in O} r_{i+1}(A) = \frac{1}{|O|} \sum_{A \in O} r_{i+1}(R(A)) = \frac{1}{|O|} \sum_{A \in O} r_i(A) = \overline{r}_i$$
   这表明轨道 $O$ 上每一行的反链元素平均个数都相等，记此常数为 $\overline{r}$：
   $$\overline{r}_1 = \overline{r}_2 = \dots = \overline{r}_a = \overline{r}$$

2. **各列平均值相等**：
   同理，由引理 2，对任意 $1 \le j \le b-1$，在轨道 $O$ 上取平均：
   $$\overline{c}_{j+1} = \frac{1}{|O|} \sum_{A \in O} c_{j+1}(R(A)) = \frac{1}{|O|} \sum_{A \in O} c_j(A) = \overline{c}_j$$
   这表明轨道 $O$ 上每一列的反链元素平均个数都相等，记此常数为 $\overline{c}$：
   $$\overline{c}_1 = \overline{c}_2 = \dots = \overline{c}_b = \overline{c}$$

3. **反链大小与 $\overline{r}, \overline{c}$ 的关系**：
   因为 $|A| = \sum_{i=1}^a r_i(A) = \sum_{j=1}^b c_j(A)$，取轨道平均得：
   $$\frac{1}{|O|} \sum_{A \in O} |A| = \sum_{i=1}^a \overline{r}_i = a \overline{r}$$
   $$\frac{1}{|O|} \sum_{A \in O} |A| = \sum_{j=1}^b \overline{c}_j = b \overline{c}$$
   从而有关系式：
   $$a \overline{r} = b \overline{c}$$

4. **利用互补性建立方程**：
   由引理 3，在轨道 $O$ 上对 $r_a(A) + c_1(R(A)) = 1$ 取平均：
   $$\overline{r}_a + \overline{c_1 \circ R} = 1 \implies \overline{r}_a + \overline{c}_1 = 1$$
   即：
   $$\overline{r} + \overline{c} = 1$$

5. **联立求解**：
   将 $\overline{c} = 1 - \overline{r}$ 代入 $a \overline{r} = b \overline{c}$：
   $$a \overline{r} = b(1 - \overline{r}) = b - b \overline{r}$$
   $$(a + b) \overline{r} = b \implies \overline{r} = \frac{b}{a + b}$$

   将 $\overline{r} = \frac{b}{a + b}$ 代入反链平均大小的表达式：
   $$\frac{1}{|O|} \sum_{A \in O} |A| = a \overline{r} = a \cdot \frac{b}{a + b} = \frac{ab}{a + b}$$

此结果对任意轨道 $O$ 均成立。

证明完毕。
