{}
这个结论是成立的。下面给出完整的初等证明。

---

### 一、为每条反链定义 $0$-$1$ 特征序列

对 $P=\{1,\dots,a\}\times\{1,\dots,b\}$ 中的任意反链 $A$，构造一个长度为 $a+b$ 的 $0$-$1$ 序列
$$w(A) = \bigl(w_1(A),\, w_2(A),\, \dots,\, w_{a+b}(A)\bigr) \in \{0,1\}^{a+b},$$
定义如下：
- 对 $1 \le i \le a$（对应第 $i$ 行）：
  $$w_i(A) = \begin{cases} 1, & \text{若存在 } j \in \{1,\dots,b\} \text{ 使得 } (i,j) \in A, \\ 0, & \text{否则}; \end{cases}$$
- 对 $1 \le j \le b$（对应第 $j$ 列）：
  $$w_{a+j}(A) = \begin{cases} 0, & \text{若存在 } i \in \{1,\dots,a\} \text{ 使得 } (i,j) \in A, \\ 1, & \text{否则}. \end{cases}$$

我们先计算 $w(A)$ 的分量之和：
1. 在同一行 $\{i\}\times\{1,\dots,b\}$ 中，任意两个元素 $(i,j)$ 与 $(i,j')$ 都可比较（因 $j\le j'$ 或 $j'\le j$）。由于 $A$ 是反链，每一行至多含有 $A$ 的一个元素，从而
   $$w_i(A) = \bigl|A \cap (\{i\}\times\{1,\dots,b\})\bigr|.$$
   对 $i=1,\dots,a$ 求和得
   $$\sum_{i=1}^a w_i(A) = |A|. \tag{1}$$
2. 同理，在同一列 $\{1,\dots,a\}\times\{j\}$ 中，任意两个元素都可比较，故每一列至多含有 $A$ 的一个元素，从而
   $$1 - w_{a+j}(A) = \bigl|A \cap (\{1,\dots,a\}\times\{j\})\bigr|.$$
   对 $j=1,\dots,b$ 求和得 $\sum_{j=1}^b (1 - w_{a+j}(A)) = |A|$，即
   $$\sum_{j=1}^b w_{a+j}(A) = b - |A|. \tag{2}$$
3. 将 $(1)$ 与 $(2)$ 相加，对**任意**反链 $A$ 恒有
   $$\sum_{t=1}^{a+b} w_t(A) = |A| + (b - |A|) = b. \tag{3}$$

---

### 二、用行轮廓刻画 $I(A)$、$A$ 与 $R(A)$

对任意子集 $S \subseteq P$，记
$$\max(S) = \{u \in S : \text{不存在 } u' \in S \text{ 使 } u' \ne u \text{ 且 } u \le u'\},$$
$$\min(S) = \{u \in S : \text{不存在 } u' \in S \text{ 使 } u' \ne u \text{ 且 } u' \le u\}$$
分别为 $S$ 的极大元集合与极小元集合。依题意 $R(A) = \min(P \setminus I(A))$。我们先验证 $A = \max(I(A))$：
- 若 $v \in A$，则由 $v \le v$ 知 $v \in I(A)$。设 $u' \in I(A)$ 满足 $v \le u'$，则依 $I(A)$ 定义存在 $w \in A$ 使 $u' \le w$。由偏序传递性得 $v \le w$；因 $A$ 是反链，必有 $v = w$，再由 $v \le u' \le v$ 及反对称性得 $u' = v$。故 $v \in \max(I(A))$。
- 反之，若 $u \in \max(I(A))$，则存在 $v \in A \subseteq I(A)$ 使 $u \le v$；由 $u$ 在 $I(A)$ 中的极大性知 $u = v \in A$。

因此 $A = \max(I(A))$。

接下来固定反链 $A$，简记 $I = I(A)$。注意到 $I$ 向下封闭：若 $u' \le u$ 且 $u \in I$，则由传递性知 $u' \in I$。对每个 $i \in \{1,\dots,a\}$，令
$$c_i = \max\bigl(\{0\} \cup \{j \in \{1,\dots,b\} : (i,j) \in I\}\bigr) \in \{0,1,\dots,b\}.$$
- 由 $I$ 向下封闭知：若 $c_i \ge 1$，则对一切 $1 \le j \le c_i$ 有 $(i,j) \le (i,c_i) \in I$，故 $(i,j) \in I$；再结合 $c_i$ 的最大性，对任意 $(i,j) \in P$ 都有
  $$(i,j) \in I \iff j \le c_i, \qquad (i,j) \in P \setminus I \iff j \ge c_i + 1. \tag{4}$$
- 对任意 $1 \le i \le a-1$，若 $c_{i+1} \ge 1$，则 $(i, c_{i+1}) \le (i+1, c_{i+1}) \in I$，故 $(i, c_{i+1}) \in I$，即 $c_i \ge c_{i+1}$（当 $c_{i+1}=0$ 时亦显然成立）。补充记号 $c_0 = b$，$c_{a+1} = 0$，则有
  $$b = c_0 \ge c_1 \ge c_2 \ge \dots \ge c_a \ge c_{a+1} = 0. \tag{5}$$

由此可直接写出 $A$ 与 $R(A)$ 的显式表达式：

**断言 1：** $A = \{(i, c_i) : 1 \le i \le a,\ c_i > c_{i+1}\}$。

*证明：* 固定 $i \in \{1,\dots,a\}$，考察第 $i$ 行中属于 $\max(I)$ 的元素：
- 若 $c_i = c_{i+1}$：当 $c_i = 0$ 时第 $i$ 行无 $I$ 中元素；当 $c_i \ge 1$ 时，因 $c_{a+1}=0$ 必有 $i \le a-1$，此时 $(i+1, c_i) = (i+1, c_{i+1}) \in I$，对第 $i$ 行中任意 $(i,j) \in I$（即 $j \le c_i$）都有 $(i,j) \le (i+1, c_i)$ 且二者不等，故 $(i,j) \notin \max(I)$。
- 若 $c_i > c_{i+1}$：因 $c_{i+1} \ge 0$ 知 $c_i \ge 1$，故 $(i, c_i) \in I$。对 $1 \le j < c_i$ 有 $(i,j) \le (i,c_i)$ 且不等，故 $(i,j) \notin \max(I)$。另一方面，若 $(i',j') \in I$ 满足 $(i,c_i) \le (i',j')$，则 $i \le i'$ 且 $c_i \le j' \le c_{i'}$；倘若 $i' \ge i+1$，由 $(5)$ 得 $c_{i'} \le c_{i+1} < c_i$，矛盾。故必有 $i' = i$ 且 $j' = c_i$，即 $(i, c_i) \in \max(I) = A$。

遍历 $1 \le i \le a$ 即得断言 1。 $\blacksquare$

**断言 2：** $R(A) = \{(i, c_i + 1) : 1 \le i \le a,\ c_{i-1} > c_i\}$。

*证明：* 固定 $i \in \{1,\dots,a\}$，考察第 $i$ 行中属于 $\min(P \setminus I)$ 的元素：
- 若 $c_{i-1} = c_i$：当 $c_i = b$ 时，由 $(4)$ 知第 $i$ 行无 $P \setminus I$ 中元素；当 $c_i < b$ 时，因 $c_0 = b$ 必有 $i \ge 2$，此时 $1 \le c_{i-1}+1 = c_i+1 \le b$，故 $(i-1, c_i+1) \in P \setminus I$，对第 $i$ 行中任意 $(i,j) \in P \setminus I$（即 $j \ge c_i+1$）都有 $(i-1, c_i+1) \le (i,j)$ 且二者不等，故 $(i,j) \notin \min(P \setminus I)$。
- 若 $c_{i-1} > c_i$：因 $c_{i-1} \le b$ 知 $c_i \le b-1$，故 $1 \le c_i+1 \le b$，即 $(i, c_i+1) \in P \setminus I$。对 $c_i+1 < j \le b$ 有 $(i, c_i+1) \le (i,j)$ 且不等，故 $(i,j) \notin \min(P \setminus I)$。另一方面，若 $(i',j') \in P \setminus I$ 满足 $(i',j') \le (i, c_i+1)$，则 $1 \le i' \le i$ 且 $c_{i'}+1 \le j' \le c_i+1$，即 $c_{i'} \le c_i$；倘若 $i' \le i-1$，由 $(5)$ 得 $c_{i'} \ge c_{i-1} > c_i$，矛盾。故必有 $i' = i$ 且 $j' = c_i+1$，即 $(i, c_i+1) \in \min(P \setminus I) = R(A)$。

遍历 $1 \le i \le a$ 即得断言 2。 $\blacksquare$

---

### 三、证明 $w(R(A))$ 是 $w(A)$ 的循环右移

先根据断言 1 和断言 2 刻画 $w(A)$ 与 $w(R(A))$ 的各个分量：

1. **行分量（$1 \le i \le a$）：** 由断言 1 和断言 2 直接得
   $$w_i(A) = 1 \iff c_i > c_{i+1}, \qquad w_i(R(A)) = 1 \iff c_{i-1} > c_i. \tag{6}$$

2. **$A$ 的列分量（$1 \le j \le b$）：** 我们证明第 $j$ 列含有 $A$ 的元素当且仅当 $j \in \{c_1,\dots,c_a\}$：
   - 若第 $j$ 列含有 $A$ 的元素，由断言 1 知存在 $i \in \{1,\dots,a\}$ 使 $c_i = j$，故 $j \in \{c_1,\dots,c_a\}$。
   - 反之，若 $j \in \{c_1,\dots,c_a\}$，取最大的下标 $i \in \{1,\dots,a\}$ 使 $c_i = j$。当 $i = a$ 时 $c_{i+1} = c_{a+1} = 0 < 1 \le j = c_i$；当 $i < a$ 时，由 $i$ 的最大性知 $c_{i+1} \ne j$，结合 $c_{i+1} \le c_i = j$ 得 $c_{i+1} < c_i$。于是由断言 1 知 $(i,j) = (i,c_i) \in A$。

   因此，对任意 $1 \le j \le b$，
   $$w_{a+j}(A) = 1 \iff j \notin \{c_1,\dots,c_a\}. \tag{7}$$

3. **$R(A)$ 的列分量（$1 \le j \le b$）：** 我们证明第 $j$ 列含有 $R(A)$ 的元素当且仅当 $j - 1 \in \{c_1,\dots,c_a\}$：
   - 若第 $j$ 列含有 $R(A)$ 的元素，由断言 2 知存在 $i \in \{1,\dots,a\}$ 使 $c_i + 1 = j$，故 $j - 1 = c_i \in \{c_1,\dots,c_a\}$。
   - 反之，若 $j - 1 \in \{c_1,\dots,c_a\}$（注意 $0 \le j - 1 \le b - 1$），取最小的下标 $i \in \{1,\dots,a\}$ 使 $c_i = j - 1$。当 $i = 1$ 时 $c_{i-1} = c_0 = b > b - 1 \ge j - 1 = c_1$；当 $i \ge 2$ 时，由 $i$ 的最小性知 $c_{i-1} \ne j - 1$，结合 $c_{i-1} \ge c_i = j - 1$ 得 $c_{i-1} > c_i$。于是由断言 2 知 $(i,j) = (i, c_i+1) \in R(A)$。

   因此，对任意 $1 \le j \le b$，
   $$w_{a+j}(R(A)) = 1 \iff j - 1 \notin \{c_1,\dots,c_a\}. \tag{8}$$

现在逐一核对 $w(R(A))$ 的全部 $a+b$ 个位置：
- **当 $t = 1$ 时：** 由 $(6)$ 知 $w_1(R(A)) = 1 \iff c_0 > c_1 \iff b > c_1$；由 $(5)$ 与 $(7)$ 知 $w_{a+b}(A) = 1 \iff b \notin \{c_1,\dots,c_a\} \iff c_1 < b$。故
  $$w_1(R(A)) = w_{a+b}(A).$$
- **当 $2 \le t \le a$ 时：** 记 $i = t$，由 $(6)$ 知 $w_i(R(A)) = 1 \iff c_{i-1} > c_i \iff w_{i-1}(A) = 1$，故
  $$w_t(R(A)) = w_{t-1}(A).$$
- **当 $t = a + 1$ 时：** 在 $(8)$ 中取 $j = 1$，结合 $(5)$ 得 $w_{a+1}(R(A)) = 1 \iff 0 \notin \{c_1,\dots,c_a\} \iff c_a > 0 = c_{a+1}$；再由 $(6)$（取 $i=a$）知这等价于 $w_a(A) = 1$，故
  $$w_{a+1}(R(A)) = w_a(A).$$
- **当 $a + 2 \le t \le a + b$ 时：** 记 $j = t - a \in \{2,\dots,b\}$，由 $(8)$ 及 $(7)$（对 $j-1 \in \{1,\dots,b-1\}$ 应用）知
  $$w_{a+j}(R(A)) = 1 \iff j - 1 \notin \{c_1,\dots,c_a\} \iff w_{a+j-1}(A) = 1,$$
  即 $w_t(R(A)) = w_{t-1}(A)$。

综上，对任意反链 $A$，$w(R(A))$ 恰好是 $w(A)$ 向右循环移位一格所得的序列：
$$w_1(R(A)) = w_{a+b}(A), \qquad w_t(R(A)) = w_{t-1}(A) \quad (2 \le t \le a+b). \tag{9}$$

---

### 四、轨道上的双重计数

因为 $P$ 是有限集，$P$ 的全部反链构成的集合也是有限集。已知 $R$ 是其上的一个置换，故任意轨道 $O$ 都是非空有限集（$|O| \ge 1$），且映射 $A \mapsto R(A)$ 是 $O$ 到自身的双射。

对每个 $t \in \{1,2,\dots,a+b\}$，记
$$S_t = \sum_{A \in O} w_t(A).$$
由于当 $A$ 取遍 $O$ 时 $R(A)$ 也恰好取遍 $O$，结合 $(9)$ 对任意 $2 \le t \le a+b$ 有
$$S_t = \sum_{A \in O} w_t(R(A)) = \sum_{A \in O} w_{t-1}(A) = S_{t-1}$$
（同时 $S_1 = \sum_{A \in O} w_1(R(A)) = S_{a+b}$）。因此 $S_1 = S_2 = \dots = S_{a+b}$，记这一公共值为 $S$。

一方面，对所有 $1 \le t \le a+b$ 求和并交换求和次序，利用 $(3)$ 可得
$$(a + b)S = \sum_{t=1}^{a+b} S_t = \sum_{t=1}^{a+b} \sum_{A \in O} w_t(A) = \sum_{A \in O} \sum_{t=1}^{a+b} w_t(A) = \sum_{A \in O} b = b|O|,$$
从而
$$S = \frac{b|O|}{a + b}.$$

另一方面，利用 $(1)$ 对 $A \in O$ 求和得
$$\sum_{A \in O} |A| = \sum_{A \in O} \sum_{i=1}^a w_i(A) = \sum_{i=1}^a \sum_{A \in O} w_i(A) = \sum_{i=1}^a S_i = aS = \frac{ab}{a + b}|O|.$$

两边同除以 $|O|$，即得
$$\frac{1}{|O|} \sum_{A \in O} |A| = \frac{ab}{a + b}.$$
证毕。
