下面给出该结论的完整证明。

### 证明思路

将 $P = \{1,\dots,a\}\times\{1,\dots,b\}$ 中的每个反链 $A$ 编码为一个长度为 $a+b$、恰含 $b$ 个 $1$ 的 $0$-$1$ 序列 $w(A)$，使得：
1. 映射 $A \mapsto w(A)$ 是一个双射，且反链大小 $|A|$ 恰好等于 $w(A)$ 前 $a$ 项之和；
2. 映射 $R$ 在此编码下恰好对应 $0$-$1$ 序列的循环右移一位。

由此可推出 $R^{a+b} = \mathrm{id}$，且沿着长度为 $a+b$ 的一次完整循环求和时，序列的每个位置在前 $a$ 位中恰好各出现 $a$ 次，立即得出任意轨道上的平均值恒为 $\dfrac{ab}{a+b}$。

---

### 第一步：反链的 $0$-$1$ 序列编码

记 $\mathcal{A}$ 为 $P$ 的全部反链构成的集合（包括空集 $\emptyset$）。对任意 $A \in \mathcal{A}$，定义其第一、第二坐标的投影集合：
$$
X(A) = \{i \in \{1,\dots,a\} : \exists j \in \{1,\dots,b\}\text{ 使 }(i,j) \in A\},
$$
$$
Y(A) = \{j \in \{1,\dots,b\} : \exists i \in \{1,\dots,a\}\text{ 使 }(i,j) \in A\}.
$$

由于 $A$ 是反链，同一行中任意两个不同元素 $(i,j)$ 与 $(i,j')$ 必可比较，因此每个 $i \in \{1,\dots,a\}$ 至多对应一个 $(i,j) \in A$；同理，每个 $j \in \{1,\dots,b\}$ 至多对应一个 $(i,j) \in A$。于是
$$
|X(A)| = |Y(A)| = |A|.
$$

进一步，设 $W$ 为所有长度为 $a+b$ 且恰有 $b$ 个 $1$（从而恰有 $a$ 个 $0$）的 $0$-$1$ 序列集合：
$$
W = \left\{(x_1,\dots,x_{a+b}) \in \{0,1\}^{a+b} : \sum_{k=1}^{a+b} x_k = b\right\}.
$$
对每个 $A \in \mathcal{A}$，定义序列 $w(A) = \bigl(w_1(A),\dots,w_{a+b}(A)\bigr) \in \{0,1\}^{a+b}$ 为
$$
w_i(A) = \begin{cases} 1, & i \in X(A), \\ 0, & i \notin X(A), \end{cases} \quad (1 \le i \le a),
$$
$$
w_{a+j}(A) = \begin{cases} 0, & j \in Y(A), \\ 1, & j \notin Y(A), \end{cases} \quad (1 \le j \le b).
$$

**性质 1**：对任意 $A \in \mathcal{A}$，有
$$
\sum_{i=1}^{a} w_i(A) = |X(A)| = |A|, \qquad
\sum_{k=1}^{a+b} w_k(A) = |X(A)| + \bigl(b - |Y(A)|\bigr) = |A| + b - |A| = b,
$$
因此 $w(A) \in W$。

**性质 2**：映射 $w : \mathcal{A} \to W$ 是双射。

*证明*：
- **单射性**：若已知 $w(A)$，则可唯一确定 $X(A)$ 和 $Y(A)$。记 $k = |A| = |X(A)| = |Y(A)|$。当 $k = 0$ 时，$A = \emptyset$ 唯一确定。当 $k \ge 1$ 时，将 $X(A)$ 和 $Y(A)$ 的元素分别严格递增排列为
  $$
  i_1 < i_2 < \dots < i_k, \qquad j_1 < j_2 < \dots < j_k.
  $$
  对每个 $r \in \{1,\dots,k\}$，存在唯一的 $y_r \in Y(A)$ 使 $(i_r, y_r) \in A$，且 $\{y_1,\dots,y_k\} = \{j_1,\dots,j_k\}$。对任意 $1 \le r < s \le k$，有 $i_r < i_s$；因为 $(i_r, y_r)$ 与 $(i_s, y_s)$ 不可比较，故不能有 $y_r \le y_s$，从而必有 $y_r > y_s$。因此 $y_1 > y_2 > \dots > y_k$，于是必有 $y_r = j_{k+1-r}$，即
  $$
  A = \bigl\{(i_1, j_k), (i_2, j_{k-1}), \dots, (i_k, j_1)\bigr\}.
  $$
  这说明 $A$ 由 $w(A)$ 唯一确定，故 $w$ 是单射。
- **满射性**：任取 $x = (x_1,\dots,x_{a+b}) \in W$，令 $X = \{i \in \{1,\dots,a\} : x_i = 1\}$，$Y = \{j \in \{1,\dots,b\} : x_{a+j} = 0\}$。由 $\sum_{k=1}^{a+b} x_k = b$ 得 $|X| + (b - |Y|) = b$，即 $|X| = |Y| = k$。若 $k = 0$，取 $A = \emptyset$；若 $k \ge 1$，将 $X, Y$ 分别严格递增排为 $i_1 < \dots < i_k$ 与 $j_1 < \dots < j_k$，令 $A = \{(i_1,j_k),\dots,(i_k,j_1)\}$。对任意 $1 \le r < s \le k$，有 $i_r < i_s$ 且 $j_{k+1-r} > j_{k+1-s}$，故 $A \in \mathcal{A}$，且显然 $w(A) = x$。

由此 $w : \mathcal{A} \to W$ 为双射。$\square$

---

### 第二步：用 $I(A)$ 的行长与列长刻画 $X(A), Y(A)$ 及 $X(R(A)), Y(R(A))$

任取 $A \in \mathcal{A}$，简记 $I = I(A)$。由定义，$I$ 向下封闭：若 $u \in I$ 且 $u' \le u$，则存在 $v \in A$ 使 $u \le v$，由传递性有 $u' \le v$，故 $u' \in I$。

首先验证 **$A$ 恰好是 $I$ 的全部极大元组成的集合**：
- 若 $v \in A$，则 $v \in I$；若存在 $u \in I$ 使 $v < u$，则存在 $v' \in A$ 使 $u \le v'$，于是 $v < v'$，与 $A$ 为反链矛盾，故 $v$ 是 $I$ 的极大元。
- 反之，若 $u$ 是 $I$ 的极大元，由 $I$ 的定义存在 $v \in A \subseteq I$ 使 $u \le v$，由极大性必有 $u = v \in A$。

（当 $A = \emptyset$ 时 $I = \emptyset$，上述结论同样成立。）

对每个 $i \in \{1,\dots,a\}$，定义第 $i$ 行的长度
$$
m_i = \bigl|\{j \in \{1,\dots,b\} : (i,j) \in I\}\bigr|,
$$
并补充约定边界值 $m_0 = b$，$m_{a+1} = 0$。

因为 $I$ 向下封闭：
1. 对固定的 $i \in \{1,\dots,a\}$，若 $(i,j) \in I$ 且 $1 \le j' \le j$，则 $(i,j') \in I$。因此 $\{j \in \{1,\dots,b\} : (i,j) \in I\} = \{1,\dots,m_i\}$（$m_i = 0$ 时为空集），即对所有 $1 \le i \le a$ 和 $1 \le j \le b$ 有
   $$
   (i,j) \in I \iff j \le m_i, \qquad (i,j) \in P \setminus I \iff j \ge m_i + 1.
   $$
2. 对任意 $1 \le i \le a-1$，由 $(i,j) \le (i+1,j)$ 知 $\{j : (i+1,j) \in I\} \subseteq \{j : (i,j) \in I\}$，故 $m_i \ge m_{i+1}$。结合 $0 \le m_i \le b$，有单调链
   $$
   b = m_0 \ge m_1 \ge m_2 \ge \dots \ge m_a \ge m_{a+1} = 0.
   $$

下面证明关于行的两个等价刻画：

**引理**：对任意 $i \in \{1,\dots,a\}$，
1. $i \in X(A) \iff m_i > m_{i+1}$；
2. $i \in X(R(A)) \iff m_{i-1} > m_i$。

*证明*：

**(1) 证明 $i \in X(A) \iff m_i > m_{i+1}$**：
- $(\Rightarrow)$ 设 $i \in X(A)$，则存在 $j \in \{1,\dots,b\}$ 使 $(i,j) \in A$。因为 $A$ 是 $I$ 的极大元集合，故 $(i,j) \in I$，从而 $1 \le j \le m_i$。若 $j < m_i$，则 $(i, m_i) \in I$ 且 $(i,j) < (i, m_i)$，与 $(i,j)$ 在 $I$ 中极大矛盾，故 $j = m_i \ge 1$。
  - 若 $i = a$，则 $m_a = j \ge 1 > 0 = m_{a+1}$。
  - 若 $i < a$，由于 $(i, m_i) < (i+1, m_i) \in P$ 且 $(i, m_i)$ 在 $I$ 中极大，必有 $(i+1, m_i) \notin I$，因此 $m_i > m_{i+1}$。
- $(\Leftarrow)$ 设 $m_i > m_{i+1}$。由 $m_{i+1} \ge 0$ 得 $m_i \ge 1$，从而 $(i, m_i) \in I$。断言 $(i, m_i)$ 是 $I$ 的极大元（从而属于 $A$，得 $i \in X(A)$）。反设存在 $(i', j') \in I$ 使 $(i, m_i) < (i', j')$，则 $i \le i'$、$m_i \le j'$ 且至少一处严格：
  - 若 $i' = i$，则 $j' > m_i$，与 $(i, j') \in I \iff j' \le m_i$ 矛盾；
  - 若 $i' > i$，则 $i + 1 \le i' \le a$（特别地 $i < a$）且 $(i+1, m_i) \le (i', j')$；由 $I$ 向下封闭得 $(i+1, m_i) \in I$，从而 $m_i \le m_{i+1}$，矛盾。

  故 $(i, m_i) \in A$，即 $i \in X(A)$。

**(2) 证明 $i \in X(R(A)) \iff m_{i-1} > m_i$**：
- $(\Rightarrow)$ 设 $i \in X(R(A))$，则存在 $j \in \{1,\dots,b\}$ 使 $(i,j) \in R(A)$，即 $(i,j)$ 是 $P \setminus I$ 的极小元。于是 $m_i + 1 \le j \le b$，特别地 $m_i < b$。若 $j > m_i + 1$，则 $(i, m_i + 1) \in P \setminus I$ 且 $(i, m_i + 1) < (i,j)$，与 $(i,j)$ 在 $P \setminus I$ 中极小矛盾，故 $j = m_i + 1$。
  - 若 $i = 1$，则 $m_0 = b > m_1$。
  - 若 $i \ge 2$，由于 $(i-1, m_i + 1) \in P$ 且 $(i-1, m_i + 1) < (i, m_i + 1)$，由 $(i, m_i + 1)$ 在 $P \setminus I$ 中的极小性知 $(i-1, m_i + 1) \in I$，从而 $m_i + 1 \le m_{i-1}$，即 $m_{i-1} > m_i$。
- $(\Leftarrow)$ 设 $m_{i-1} > m_i$。由 $m_{i-1} \le b$ 得 $1 \le m_i + 1 \le m_{i-1} \le b$，从而 $(i, m_i + 1) \in P \setminus I$。断言 $(i, m_i + 1)$ 是 $P \setminus I$ 的极小元（从而属于 $R(A)$，得 $i \in X(R(A))$）。反设存在 $(i', j') \in P \setminus I$ 使 $(i', j') < (i, m_i + 1)$，则 $i' \le i$、$j' \le m_i + 1$ 且至少一处严格：
  - 若 $i' = i$，则 $j' < m_i + 1$，即 $j' \le m_i$，从而 $(i, j') \in I$，矛盾；
  - 若 $i' < i$，则 $1 \le i' \le i - 1$（特别地 $i \ge 2$）。因 $m_i + 1 \le m_{i-1}$，有 $(i-1, m_i + 1) \in I$；又 $(i', j') \le (i-1, m_i + 1)$，由 $I$ 向下封闭得 $(i', j') \in I$，矛盾。

  故 $(i, m_i + 1) \in R(A)$，即 $i \in X(R(A))$。$\square$

---

**对称的列刻画**：

对每个 $j \in \{1,\dots,b\}$，定义第 $j$ 列的长度
$$
n_j = \bigl|\{i \in \{1,\dots,a\} : (i,j) \in I\}\bigr|,
$$
并约定 $n_0 = a$，$n_{b+1} = 0$。

坐标交换映射 $\tau : \{1,\dots,a\}\times\{1,\dots,b\} \to \{1,\dots,b\}\times\{1,\dots,a\}$，$\tau(i,j) = (j,i)$ 是偏序同构，它保持反链、序理想 $I$、补集及极小元，同时交换 $X(\cdot)$ 与 $Y(\cdot)$、交换行长 $(m_i)$ 与列长 $(n_j)$。将上述结果应用于 $\tau(A)$，立即得到：
- $a = n_0 \ge n_1 \ge \dots \ge n_b \ge n_{b+1} = 0$，且对所有 $1 \le i \le a, 1 \le j \le b$ 有 $(i,j) \in I \iff i \le n_j$；
- 对所有 $j \in \{1,\dots,b\}$，有
  $$
  j \in Y(A) \iff n_j > n_{j+1}, \qquad j \in Y(R(A)) \iff n_{j-1} > n_j.
  $$

---

### 第三步：证明 $R$ 对应编码序列的循环右移

定义 $W$ 上的循环右移映射 $\sigma : W \to W$ 为
$$
\sigma(x_1, x_2, \dots, x_{a+b}) = (x_{a+b}, x_1, \dots, x_{a+b-1}).
$$
下面证明对任意 $A \in \mathcal{A}$，均有
$$
w(R(A)) = \sigma\bigl(w(A)\bigr).
$$

逐位验证如下：

1. **第 $1$ 位**：由引理 (2) 及 $(1,b) \in I(A) \iff b \le m_1 \iff m_1 = b$，得
   $$
   1 \in X(R(A)) \iff m_0 > m_1 \iff m_1 < b \iff (1,b) \notin I(A).
   $$
   另一方面，对任意 $(i,j) \in P$，条件 $(1,b) \le (i,j)$（即 $1 \le i$ 且 $b \le j$）等价于 $j = b$，因此
   $$
   (1,b) \in I(A) \iff \exists (i,j) \in A \text{ 使 } (1,b) \le (i,j) \iff \exists i \in \{1,\dots,a\} \text{ 使 } (i,b) \in A \iff b \in Y(A).
   $$
   故 $1 \in X(R(A)) \iff b \notin Y(A)$，即
   $$
   w_1(R(A)) = w_{a+b}(A).
   $$

2. **第 $2$ 至第 $a$ 位**：对任意 $2 \le i \le a$，由引理 (2) 与 (1) 直接得
   $$
   i \in X(R(A)) \iff m_{i-1} > m_i \iff i-1 \in X(A),
   $$
   即
   $$
   w_i(R(A)) = w_{i-1}(A).
   $$

3. **第 $a+1$ 位**：由列的刻画及 $(a,1) \in I(A) \iff a \le n_1 \iff n_1 = a$，得
   $$
   1 \notin Y(R(A)) \iff \neg(n_0 > n_1) \iff n_1 = a \iff (a,1) \in I(A).
   $$
   又对任意 $(i,j) \in P$，条件 $(a,1) \le (i,j)$（即 $a \le i$ 且 $1 \le j$）等价于 $i = a$，因此
   $$
   (a,1) \in I(A) \iff \exists j \in \{1,\dots,b\} \text{ 使 } (a,j) \in A \iff a \in X(A).
   $$
   故 $1 \notin Y(R(A)) \iff a \in X(A)$，即
   $$
   w_{a+1}(R(A)) = w_a(A).
   $$

4. **第 $a+2$ 至第 $a+b$ 位**：对任意 $2 \le j \le b$，由列的刻画直接得
   $$
   j \in Y(R(A)) \iff n_{j-1} > n_j \iff j-1 \in Y(A),
   $$
   取否定即 $j \notin Y(R(A)) \iff j-1 \notin Y(A)$，从而
   $$
   w_{a+j}(R(A)) = w_{a+j-1}(A).
   $$

综合以上四点，即证 $w(R(A)) = \sigma(w(A))$。

---

### 第四步：计算任意轨道上的反链大小平均值

由 $w(R(A)) = \sigma(w(A))$ 及归纳法，对任意非负整数 $t$ 和任意 $A \in \mathcal{A}$，有
$$
w\bigl(R^t(A)\bigr) = \sigma^t\bigl(w(A)\bigr).
$$
特别地，因 $\sigma^{a+b} = \mathrm{id}_W$，有 $w(R^{a+b}(A)) = w(A)$。又因 $w$ 是单射，故对所有 $A \in \mathcal{A}$ 均有
$$
R^{a+b}(A) = A.
$$

现任取 $R$ 的一条轨道 $\mathcal{O}$，记 $d = |\mathcal{O}|$，并任取 $A_0 \in \mathcal{O}$。则
$$
\mathcal{O} = \bigl\{A_0, R(A_0), \dots, R^{d-1}(A_0)\bigr\},
$$
其中这 $d$ 个反链两两不同，且 $R^d(A_0) = A_0$。做带余除法 $a + b = qd + r$（$q \in \mathbb{Z}_{\ge 0}$，$0 \le r < d$），则
$$
A_0 = R^{a+b}(A_0) = R^{qd+r}(A_0) = R^r(A_0).
$$
若 $0 < r < d$，将与 $A_0, R(A_0), \dots, R^{d-1}(A_0)$ 两两不同矛盾，故 $r = 0$，即 $d \mid (a+b)$ 且 $q = \dfrac{a+b}{d} \in \mathbb{Z}_{>0}$。

因此，当 $t$ 遍取 $0, 1, \dots, a+b-1$ 时，$R^t(A_0)$ 将轨道 $\mathcal{O}$ 中的每个元素恰好遍历 $q$ 次，于是
$$
\sum_{t=0}^{a+b-1} \bigl|R^t(A_0)\bigr| = q \sum_{A \in \mathcal{O}} |A| = \frac{a+b}{|\mathcal{O}|} \sum_{A \in \mathcal{O}} |A|.
$$

另一方面，记 $w(A_0) = (x_1, x_2, \dots, x_{a+b}) \in W$，并按周期 $a+b$ 将下标延拓至全体整数，即对任意 $k \in \mathbb{Z}$ 令 $x_{k+a+b} = x_k$。易对 $t \ge 0$ 归纳验证，对所有 $k \in \{1,\dots,a+b\}$ 有
$$
w_k\bigl(R^t(A_0)\bigr) = \bigl(\sigma^t(w(A_0))\bigr)_k = x_{k-t}.
$$
（$t = 0$ 显然；若对 $t$ 成立，则对 $t+1$，当 $k = 1$ 时 $w_1(R^{t+1}(A_0)) = w_{a+b}(R^t(A_0)) = x_{a+b-t} = x_{1-(t+1)}$，当 $2 \le k \le a+b$ 时 $w_k(R^{t+1}(A_0)) = w_{k-1}(R^t(A_0)) = x_{k-1-t} = x_{k-(t+1)}$。）

结合第一步的性质 1，对每个 $t \in \{0,1,\dots,a+b-1\}$ 有
$$
\bigl|R^t(A_0)\bigr| = \sum_{i=1}^{a} w_i\bigl(R^t(A_0)\bigr) = \sum_{i=1}^{a} x_{i-t}.
$$
对 $t = 0,1,\dots,a+b-1$ 求和并交换求和次序：
$$
\sum_{t=0}^{a+b-1} \bigl|R^t(A_0)\bigr| = \sum_{t=0}^{a+b-1} \sum_{i=1}^{a} x_{i-t} = \sum_{i=1}^{a} \sum_{t=0}^{a+b-1} x_{i-t}.
$$
对每个固定的 $i \in \{1,\dots,a\}$，当 $t$ 遍取 $0,1,\dots,a+b-1$ 时，$i - t$ 构成模 $a+b$ 的一个完全剩余系；由 $x_k$ 的周期性及 $w(A_0) \in W$，得
$$
\sum_{t=0}^{a+b-1} x_{i-t} = \sum_{k=1}^{a+b} x_k = b.
$$
因此
$$
\sum_{t=0}^{a+b-1} \bigl|R^t(A_0)\bigr| = \sum_{i=1}^{a} b = ab.
$$

联立两式，即得
$$
\frac{a+b}{|\mathcal{O}|} \sum_{A \in \mathcal{O}} |A| = ab \implies \frac{1}{|\mathcal{O}|} \sum_{A \in \mathcal{O}} |A| = \frac{ab}{a+b}.
$$
证毕。$\blacksquare$