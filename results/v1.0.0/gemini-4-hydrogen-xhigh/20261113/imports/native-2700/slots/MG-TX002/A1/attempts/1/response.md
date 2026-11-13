{}
结论成立。下面给出一个完整的证明（核心思路是将反链的行、列占据情况编码为一个长度为 $a+b$ 的 $0$-$1$ 序列，并证明映射 $R$ 在该编码下表现为循环移位）。

---

### 证明

对任意命题 $\mathcal{E}$，记示性函数 $\mathbf{1}[\mathcal{E}]$ 在 $\mathcal{E}$ 为真时取值为 $1$，否则为 $0$。

#### 第一步：下集、极大元与行列指示函数

设 $A \subseteq P = \{1,\dots,a\} \times \{1,\dots,b\}$ 是任意一条反链（允许为空集），令 $I = I(A) = \{u \in P : \exists v \in A \text{ 使 } u \le v\}$。

1. **下集与上集性质**：显然 $I$ 是下集（若 $u' \le u$ 且 $u \in I$，则 $u' \in I$），而 $P \setminus I$ 是上集（若 $u \in P \setminus I$ 且 $u \le u'$，则 $u' \in P \setminus I$，否则 $u' \in I \implies u \in I$）。
2. **$A$ 是 $I$ 的全体极大元之集**：
   - 若 $v \in A$，则 $v \in I$；若另有 $u \in I$ 满足 $v \le u$，则存在 $v' \in A$ 使 $u \le v'$，从而 $v \le u \le v'$。因 $A$ 是反链，只能有 $v = v'$，进而 $u = v$，故 $v$ 是 $I$ 的极大元。
   - 反之，若 $u$ 是 $I$ 的极大元，由 $u \in I$ 知存在 $v \in A \subseteq I$ 使 $u \le v$，由极大性必有 $u = v \in A$。

对任意反链 $A$、任意行标 $i \in \{1,\dots,a\}$ 及列标 $j \in \{1,\dots,b\}$，定义行、列指示函数：
$$r_i(A) = \mathbf{1}\bigl[A \cap (\{i\} \times \{1,\dots,b\}) \neq \emptyset\bigr], \qquad c_j(A) = \mathbf{1}\bigl[A \cap (\{1,\dots,a\} \times \{j\}) \neq \emptyset\bigr].$$
因为每一行 $\{i\} \times \{1,\dots,b\}$ 与每一列 $\{1,\dots,a\} \times \{j\}$ 在偏序 $\le$ 下都是全序链，所以反链 $A$ 与每行、每列至多交于一个元素。于是
$$|A| = \sum_{i=1}^a r_i(A) = \sum_{j=1}^b c_j(A). \tag{1}$$

---

#### 第二步：用行长与列高刻画 $A$ 与 $R(A)$

仍记 $I = I(A)$。对每个 $i \in \{1,\dots,a\}$，定义行长
$$\lambda_i = \max\bigl(\{0\} \cup \{j \in \{1,\dots,b\} : (i,j) \in I\}\bigr),$$
并约定边界值 $\lambda_0 = b$，$\lambda_{a+1} = 0$。因 $I$ 是下集，立得：
- 对任意 $(i,j) \in P$，$(i,j) \in I \iff j \le \lambda_i$；
- 单调性：$b = \lambda_0 \ge \lambda_1 \ge \lambda_2 \ge \dots \ge \lambda_a \ge \lambda_{a+1} = 0$（对 $1 \le i \le a-1$，若 $\lambda_{i+1} \ge 1$，则 $(i, \lambda_{i+1}) \le (i+1, \lambda_{i+1}) \in I$，故 $(i, \lambda_{i+1}) \in I$，即 $\lambda_i \ge \lambda_{i+1}$）。

下面固定 $i \in \{1,\dots,a\}$，考察第 $i$ 行中的元素与 $A$ 以及 $R(A)$ 的交：

1. **刻画 $r_i(A)$**：
   - 若 $\lambda_i = 0$，则第 $i$ 行无元素属于 $I$，故无元素属于 $A$；此时也有 $\lambda_i = 0 = \lambda_{i+1}$。
   - 若 $\lambda_i \ge 1$，则第 $i$ 行中属于 $I$ 的元素为 $(i,1), \dots, (i,\lambda_i)$，其中 $(i,1),\dots,(i,\lambda_i-1)$ 均严格小于 $(i,\lambda_i) \in I$，不可能是 $I$ 的极大元；而 $(i,\lambda_i)$ 是 $I$ 的极大元当且仅当不存在 $(i',j') \in I$ 满足 $(i',j') > (i,\lambda_i)$。当 $i = a$ 时，任意 $(a, j') > (a, \lambda_a)$ 满足 $j' > \lambda_a$，从而 $(a, j') \notin I$，故 $(a, \lambda_a) \in A$（此时确实有 $\lambda_a \ge 1 > 0 = \lambda_{a+1}$）；当 $i < a$ 时，因为任意 $i' > i, j' \ge \lambda_i$ 都满足 $(i+1, \lambda_i) \le (i', j')$ 且 $I$ 是下集，所以 $(i,\lambda_i)$ 为 $I$ 的极大元当且仅当 $(i+1, \lambda_i) \notin I$，即 $\lambda_i > \lambda_{i+1}$。

   综上，对所有 $i \in \{1,\dots,a\}$：
   $$r_i(A) = \mathbf{1}[\lambda_i > \lambda_{i+1}]. \tag{2}$$

2. **刻画 $r_i(R(A))$**：
   第 $i$ 行中属于 $P \setminus I$ 的元素满足 $j > \lambda_i$。
   - 若 $\lambda_i = b$，则第 $i$ 行无元素属于 $P \setminus I$，故无元素属于 $R(A)$；此时由 $\lambda_{i-1} \le b$ 亦有 $\lambda_{i-1} = \lambda_i$。
   - 若 $\lambda_i < b$，则第 $i$ 行中属于 $P \setminus I$ 的元素为 $(i, \lambda_i+1), \dots, (i, b)$，其中 $(i, \lambda_i+2), \dots, (i, b)$ 均严格大于 $(i, \lambda_i+1) \in P \setminus I$，不可能是 $P \setminus I$ 的极小元。而 $(i, \lambda_i+1)$ 是 $P \setminus I$ 的极小元当且仅当不存在 $(i', j') \in P \setminus I$ 满足 $(i', j') < (i, \lambda_i+1)$：
     - 当 $i = 1$ 时，任意 $(1, j') < (1, \lambda_1+1)$ 满足 $j' \le \lambda_1$，从而 $(1, j') \in I$，故 $(1, \lambda_1+1) \in R(A)$（此时确实有 $\lambda_0 = b > \lambda_1$）。
     - 当 $i > 1$ 时，任意满足 $(i', j') < (i, \lambda_i+1)$ 的元素 $(i', j') \in P$，要么 $i'=i, j' \le \lambda_i$（已在 $I$ 中），要么 $i' \le i-1, j' \le \lambda_i+1$，从而 $(i', j') \le (i-1, \lambda_i+1)$。因 $P \setminus I$ 是上集，不存在这样的 $(i',j') \in P \setminus I$ 当且仅当 $(i-1, \lambda_i+1) \in I$，即 $\lambda_i+1 \le \lambda_{i-1}$，也即 $\lambda_{i-1} > \lambda_i$。

   综上，对所有 $i \in \{1,\dots,a\}$：
   $$r_i(R(A)) = \mathbf{1}[\lambda_{i-1} > \lambda_i]. \tag{3}$$

对称地，对每个 $j \in \{1,\dots,b\}$ 定义列高
$$\mu_j = \max\bigl(\{0\} \cup \{i \in \{1,\dots,a\} : (i,j) \in I\}\bigr),$$
并约定 $\mu_0 = a$，$\mu_{b+1} = 0$。交换两个坐标的角色（即通过序同构 $(i,j) \mapsto (j,i)$），完全同理有 $(i,j) \in I \iff i \le \mu_j$，$a = \mu_0 \ge \mu_1 \ge \dots \ge \mu_b \ge \mu_{b+1} = 0$，以及对所有 $j \in \{1,\dots,b\}$：
$$c_j(A) = \mathbf{1}[\mu_j > \mu_{j+1}], \qquad c_j(R(A)) = \mathbf{1}[\mu_{j-1} > \mu_j]. \tag{4}$$

---

#### 第三步：行、列指示函数之间的移位关系

由 $(2)$、$(3)$、$(4)$ 可立即得到如下四条关系：

1. 对 $2 \le i \le a$：$r_i(R(A)) = \mathbf{1}[\lambda_{i-1} > \lambda_i] = r_{i-1}(A)$。
2. 当 $i = 1$ 时：$r_1(R(A)) = \mathbf{1}[b > \lambda_1] = 1 - \mathbf{1}[\lambda_1 = b]$。注意到
   $$\lambda_1 = b \iff (1, b) \in I \iff 1 \le \mu_b \iff \mu_b > 0 = \mu_{b+1},$$
   因此 $\mathbf{1}[\lambda_1 = b] = c_b(A)$，从而 $r_1(R(A)) = 1 - c_b(A)$。
3. 对 $2 \le j \le b$：$c_j(R(A)) = \mathbf{1}[\mu_{j-1} > \mu_j] = c_{j-1}(A)$，从而 $1 - c_j(R(A)) = 1 - c_{j-1}(A)$。
4. 当 $j = 1$ 时：$1 - c_1(R(A)) = 1 - \mathbf{1}[a > \mu_1] = \mathbf{1}[\mu_1 = a]$。注意到
   $$\mu_1 = a \iff (a, 1) \in I \iff 1 \le \lambda_a \iff \lambda_a > 0 = \lambda_{a+1},$$
   因此 $\mathbf{1}[\mu_1 = a] = r_a(A)$，从而 $1 - c_1(R(A)) = r_a(A)$。

---

#### 第四步：利用循环编码计算轨道平均值

记 $n = a + b$。对 $P$ 的每条反链 $A$，构造长为 $n$ 的序列 $w(A) = (w_0(A), w_1(A), \dots, w_{n-1}(A)) \in \{0,1\}^n$：
$$w_k(A) = \begin{cases}
r_{k+1}(A), & 0 \le k \le a-1, \\
1 - c_{k-a+1}(A), & a \le k \le a+b-1.
\end{cases}$$

1. **序列元素总和恒为 $b$**：由 $(1)$，对任意反链 $A$，
   $$\sum_{k=0}^{n-1} w_k(A) = \sum_{i=1}^a r_i(A) + \sum_{j=1}^b \bigl(1 - c_j(A)\bigr) = |A| + (b - |A|) = b. \tag{5}$$

2. **$R$ 诱导循环右移**：将第三步的四条关系代入 $w(R(A))$ 的定义：
   - $w_0(R(A)) = r_1(R(A)) = 1 - c_b(A) = w_{n-1}(A)$；
   - 对 $1 \le k \le a-1$，$w_k(R(A)) = r_{k+1}(R(A)) = r_k(A) = w_{k-1}(A)$；
   - $w_a(R(A)) = 1 - c_1(R(A)) = r_a(A) = w_{a-1}(A)$；
   - 对 $a+1 \le k \le n-1$，$w_k(R(A)) = 1 - c_{k-a+1}(R(A)) = 1 - c_{k-a}(A) = w_{k-1}(A)$。

   合并写作，对一切 $k \in \{0,1,\dots,n-1\}$ 都有
   $$w_k(R(A)) = w_{(k-1) \bmod n}(A), \tag{6}$$
   其中 $(k-1)\bmod n$ 表示 $\{0,1,\dots,n-1\}$ 中与 $k-1$ 模 $n$ 同余的唯一整数。

现在设 $O$ 是置换 $R$ 的任意一条轨道。由于 $P$ 有限，全部反链的集合有限且非空，所以 $1 \le |O| < \infty$，且 $A \mapsto R(A)$ 是 $O$ 到自身的双射。对每个 $k \in \{0,1,\dots,n-1\}$，记
$$S_k = \sum_{A \in O} w_k(A).$$
因为 $R$ 在 $O$ 上是双射，利用 $(6)$ 对求和重新指标化得
$$S_k = \sum_{A \in O} w_k(R(A)) = \sum_{A \in O} w_{(k-1) \bmod n}(A) = S_{(k-1)\bmod n}.$$
由此可知 $S_0 = S_1 = \dots = S_{n-1}$，记此公共值为 $S$。

对 $k = 0,1,\dots,n-1$ 求和并交换求和次序，结合 $(5)$ 得
$$n S = \sum_{k=0}^{n-1} S_k = \sum_{k=0}^{n-1} \sum_{A \in O} w_k(A) = \sum_{A \in O} \sum_{k=0}^{n-1} w_k(A) = \sum_{A \in O} b = b|O|,$$
故
$$S = \frac{b}{n}|O| = \frac{b}{a+b}|O|.$$

最后，再由 $(1)$ 得 $|A| = \sum_{i=1}^a r_i(A) = \sum_{k=0}^{a-1} w_k(A)$，从而
$$\sum_{A \in O} |A| = \sum_{A \in O} \sum_{k=0}^{a-1} w_k(A) = \sum_{k=0}^{a-1} \sum_{A \in O} w_k(A) = \sum_{k=0}^{a-1} S_k = a S = \frac{ab}{a+b}|O|.$$
两边同除以 $|O|$ 即得
$$\frac{1}{|O|} \sum_{A \in O} |A| = \frac{ab}{a+b}.$$
$\blacksquare$
