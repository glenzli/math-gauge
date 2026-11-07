本题旨在研究有界实数列空间上的伪度量商空间 \(X\) 以及由严格递增函数 \(f: \mathbb N \to \mathbb N\) 诱导的取样算子 \(T_f\) 的动力系统与泛函分析性质。以下给出详尽、严格的完整论证。

---

### 一、预备知识与记号规范

记 \(E = \ell^\infty(\mathbb N, \mathbb R)\) 为所有有界实数列构成的实向量空间，配备半范数（seminorm）
\[
\|x\| = \limsup_{N\to\infty}\frac1N\sum_{j=1}^{N}|x_j|.
\]
易验证：
1. 对任意 \(x\in E\)，\(\|x\|\ge 0\)；
2. 对任意 \(\lambda\in\mathbb R, x\in E\)，\(\|\lambda x\| = |\lambda|\|x\|\)；
3. 对任意 \(x,y\in E\)，由 \(\limsup\) 的次可加性，\(\|x+y\| \le \|x\| + \|y\|\)。

在 \(E\) 上的伪距离即为 \(d(x,y)=\|x-y\|\)。记其零化子空间（核）为
\[
\mathcal N = \{x\in E : \|x\|=0\} = \{x\in E : \lim_{N\to\infty}\frac1N\sum_{j=1}^{N}|x_j|=0\}.
\]
等价关系 \(x\sim y \iff x-y\in\mathcal N\)。商空间 \(X = E/\!\sim = E/\mathcal N\) 是一个以 \(\|[x]\| = \|x\|\) 为范数的实赋范向量空间，\(\bar d([x],[y]) = \|[x-y]\|\) 即为其诱导的度量。

对严格递增函数 \(f:\mathbb N\to\mathbb N\)，定义算子 \(P_f: E\to E\)，\((P_f x)_j = x_{f(j)}\)。显然 \(P_f\) 是 \(E\) 上的实线性算子。

---

### 二、第 1 问的解答与证明

#### 1. 映射 \(T_f\) 良定的充要条件

线性映射 \(P_f\) 能诱导商空间 \(X\) 上的良定映射 \(T_f([x]) = [P_f x]\)，当且仅当 \(P_f(\mathcal N)\subseteq \mathcal N\)，即：
\[
\forall x\in E,\quad \|x\|=0 \implies \|P_f x\|=0.
\]

**定理 1**：\(P_f\) 诱导 \(X\) 上的映射 \(T_f\) 当且仅当
\[
\limsup_{n\to\infty}\frac{f(n)}{n} < \infty.
\]

**证明**：

**（充分性）**
设 \(C = \limsup_{n\to\infty}\frac{f(n)}{n} < \infty\)。注意对任意严格递增函数 \(f:\mathbb N\to\mathbb N\)，必有 \(f(n)\ge n\)，故 \(C\ge 1\)。
对任意 \(x\in E\)，由 \(|x_m|\ge 0\) 以及 \(f\) 是单射知：
\[
\sum_{j=1}^N |(P_f x)_j| = \sum_{j=1}^N |x_{f(j)}| \le \sum_{m=1}^{f(N)} |x_m|.
\]
两边除以 \(N\)：
\[
\frac1N \sum_{j=1}^N |x_{f(j)}| \le \frac{f(N)}{N} \cdot \frac{1}{f(N)}\sum_{m=1}^{f(N)} |x_m|.
\]
两边取 \(N\to\infty\) 的上极限：
\[
\|P_f x\| = \limsup_{N\to\infty}\frac1N \sum_{j=1}^N |x_{f(j)}| \le \left(\limsup_{N\to\infty}\frac{f(N)}{N}\right) \cdot \left(\limsup_{N\to\infty} \frac{1}{f(N)}\sum_{m=1}^{f(N)} |x_m|\right).
\]
因为 \(\{f(N)\}_{N=1}^\infty\) 是正整数序列的一个严格递增子序列，子序列的上极限不超过整个序列的上极限：
\[
\limsup_{N\to\infty} \frac{1}{f(N)}\sum_{m=1}^{f(N)} |x_m| \le \limsup_{M\to\infty}\frac1M\sum_{m=1}^M |x_m| = \|x\|.
\]
从而得到核心不等式：
\[
\|P_f x\| \le C \|x\|. \tag{1}
\]
若 \(\|x\|=0\)，则 \(\|P_f x\| \le C \cdot 0 = 0\)，即 \(P_f x\in\mathcal N\)。因此 \(T_f\) 良定。

**（必要性）**
反设 \(\limsup_{n\to\infty}\frac{f(n)}{n} = \infty\)。我们将构造一个有界实数列 \(x\in E\)，满足 \(\|x\|=0\)，但 \(\|P_f x\|\ge \frac12 > 0\)。

因为 \(\limsup_{n\to\infty}\frac{f(n)}{n} = \infty\)，我们可以归纳选取严格递增正整数列 \(\{n_k\}_{k=1}^\infty\) 满足：
1. \(n_1 \ge 1\)；
2. \(\frac{f(n_k)}{n_k} \ge 2^{2k}\) 对一切 \(k\ge 1\) 成立；
3. \(n_{k+1} \ge 4 n_k\) 对一切 \(k\ge 1\) 成立。

构造数列 \(y = (y_j)_{j=1}^\infty\) 为：
\[
y_j = \begin{cases}
1, & j\in [n_k, 2n_k] \text{ 对某个 } k\ge 1,\\
0, & \text{其它}.
\end{cases}
\]
定义 \(x\in E\) 为：
\[
x_m = \begin{cases}
y_j, & \text{若存在 } j\in\mathbb N \text{ 使得 } m=f(j),\\
0, & \text{若 } m\notin f(\mathbb N).
\end{cases}
\]
因为 \(y_j\in\{0,1\}\)，故 \(x_m\in\{0,1\}\)，从而 \(x\in E\)。由定义，\((P_f x)_j = x_{f(j)} = y_j\)。

先计算 \(\|P_f x\|\)：
对每个 \(k\ge 1\)，考虑前 \(2n_k\) 项：
\[
\frac{1}{2n_k}\sum_{j=1}^{2n_k} |(P_f x)_j| = \frac{1}{2n_k}\sum_{j=1}^{2n_k} y_j \ge \frac{1}{2n_k}\sum_{j=n_k}^{2n_k} 1 = \frac{n_k+1}{2n_k} > \frac12.
\]
因此：
\[
\|P_f x\| = \limsup_{N\to\infty}\frac1N\sum_{j=1}^N |(P_f x)_j| \ge \frac12 > 0.
\]

再计算 \(\|x\|\)：
由于 \(x\) 仅在 \(f(\mathbb N)\) 上非零，对任意 \(M\ge f(n_1)\)，存在唯一的整数 \(n\ge n_1\) 使得 \(f(n)\le M < f(n+1)\)。则：
\[
\sum_{m=1}^M |x_m| = \sum_{j=1}^n |x_{f(j)}| = \sum_{j=1}^n y_j.
\]
因此：
\[
\frac1M\sum_{m=1}^M |x_m| \le \frac{1}{f(n)}\sum_{j=1}^n y_j.
\]
对于 \(n\ge n_1\)，设 \(n\in [n_k, n_{k+1}-1]\)。由 \(y\) 的构造，在区间 \([1, n]\) 内 \(y_j=1\) 的项数不超过：
\[
\sum_{j=1}^n y_j \le \sum_{i=1}^k (n_i + 1) = k + \sum_{i=1}^k n_i.
\]
由于 \(n_i \ge 4 n_{i-1}\)，有 \(\sum_{i=1}^k n_i < \frac{4}{3}n_k\)，故当 \(n_k\ge 3\) 时，\(\sum_{j=1}^n y_j \le 2 n_k\)。
另一方面，因 \(f\) 严格递增且 \(n\ge n_k\)，有 \(f(n)\ge f(n_k) \ge 2^{2k} n_k\)。从而：
\[
\frac{1}{f(n)}\sum_{j=1}^n y_j \le \frac{2n_k}{2^{2k} n_k} = \frac{2}{2^{2k}}.
\]
当 \(M\to\infty\) 时，必有 \(n\to\infty\)，从而对应的 \(k\to\infty\)，因此：
\[
\lim_{M\to\infty}\frac1M\sum_{m=1}^M |x_m| = 0.
\]
这表明 \(\|x\|=0\)，即 \(x\in\mathcal N\)。然而 \(\|P_f x\|\ge \frac12 > 0\)，即 \(P_f x\notin\mathcal N\)。矛盾！
因此必有 \(\limsup_{n\to\infty}\frac{f(n)}{n} < \infty\)。\(\blacksquare\)

---

#### 2. \(T_f\) 的连续性与最小 Lipschitz 常数

设 \(C = \limsup_{n\to\infty}\frac{f(n)}{n} < \infty\)。

**（连续性与 Lipschitz 上界）**
由不等式 (1)，对任意 \([x],[y]\in X\)：
\[
\bar d(T_f([x]), T_f([y])) = \|T_f([x-y])\| = \|P_f(x-y)\| \le C \|x-y\| = C \bar d([x],[y]).
\]
这说明 \(T_f\) 是 Lipschitz 连续的（Lipschitz 常数不超过 \(C\)），因而必然是连续的。

**（最小 Lipschitz 常数恰为 \(C\)）**
因为 \(T_f\) 是线性映射，其最小 Lipschitz 常数即为其算子范数：
\[
L_1 = \sup_{[x]\ne [0]} \frac{\|T_f([x])\|}{\|[x]\|}.
\]
我们已证 \(L_1 \le C\)。下面证明 \(L_1 \ge C\)。

任取 \(\varepsilon \in (0, 1)\) 及任意正数 \(\eta > 0\)（若 \(C>1\)，选取充分小的 \(\eta\) 使得 \(C-\eta > 1\)；若 \(C=1\)，因 \(C\ge 1\)，显然 \(L_1=1\)）。
根据上极限定义，存在严格递增子序列 \(\{N_k\}_{k=1}^\infty\)，满足 \(\frac{f(N_k)}{N_k} \ge C - \eta\)。通过充分稀疏地选取子序列，可令 \(N_{k+1} \ge 2 f(N_k + \lfloor\varepsilon N_k\rfloor)\)。

对每个 \(k\)，置区间 \(I_k = [N_k, N_k + \lfloor\varepsilon N_k\rfloor]\)。定义 \(y\in\ell^\infty(\mathbb N)\) 为：
\[
y = \sum_{k=1}^\infty \mathbf{1}_{I_k}.
\]
并定义 \(x\in E\) 为：\(x_m = y_j\)（若 \(m=f(j)\)），其余处为 \(0\)。
此时 \(P_f x = y\)。
在子序列点 \(M_k = N_k + \lfloor\varepsilon N_k\rfloor\) 处计算：
\[
\frac{1}{M_k}\sum_{j=1}^{M_k} y_j \ge \frac{\lfloor\varepsilon N_k\rfloor + 1}{N_k + \lfloor\varepsilon N_k\rfloor} \ge \frac{\varepsilon N_k}{(1+\varepsilon)N_k} = \frac{\varepsilon}{1+\varepsilon}.
\]
从而：
\[
\|P_f x\| = \limsup_{N\to\infty}\frac1N\sum_{j=1}^N y_j \ge \frac{\varepsilon}{1+\varepsilon}.
\]
再计算 \(\|x\|\)：对于 \(n\in I_k\)，由 \(f\) 严格递增，对 \(n\ge N_k\) 有 \(f(n) \ge f(N_k) + n - N_k \ge (C-\eta)N_k + n - N_k\)。由于之前的区间贡献满足 \(\sum_{j < N_k} y_j = o(N_k)\)，故对 \(n\in I_k\)：
\[
\frac{\sum_{j=1}^n y_j}{f(n)} \le \frac{n - N_k + o(N_k)}{(C-\eta)N_k + n - N_k} \le \frac{\lfloor\varepsilon N_k\rfloor + o(N_k)}{(C-\eta+\varepsilon)N_k} = \frac{\varepsilon}{C-\eta+\varepsilon} + o(1).
\]
对于 \(n\) 位于 \(I_k\) 之后、\(I_{k+1}\) 之前的范围，分子保持在 \(\lfloor\varepsilon N_k\rfloor + o(N_k)\) 不变，而分母随 \(n\) 增大而增大，比值单调减小。
因此：
\[
\|x\| = \limsup_{n\to\infty}\frac{1}{f(n)}\sum_{j=1}^n y_j \le \frac{\varepsilon}{C-\eta+\varepsilon}.
\]
由此得到：
\[
\frac{\|T_f([x])\|}{\|[x]\|} = \frac{\|P_f x\|}{\|x\|} \ge \frac{\frac{\varepsilon}{1+\varepsilon}}{\frac{\varepsilon}{C-\eta+\varepsilon}} = \frac{C-\eta+\varepsilon}{1+\varepsilon}.
\]
令 \(\varepsilon \to 0\) 且 \(\eta \to 0\)，可知：
\[
L_1 \ge C.
\]
结合上界，得 \(T_f\) 的最小 Lipschitz 常数为：
\[
L_1 = \limsup_{n\to\infty}\frac{f(n)}{n}.
\]

---

#### 3. \(T_f\) 的满射性

**结论**：对每个允许的 \(f\)，\(T_f\) 恒为**满射**。

**证明**：
任取 \([y]\in X\)，设其代表元为 \(y=(y_j)_{j=1}^\infty \in E\)。
定义序列 \(x = (x_m)_{m=1}^\infty\) 为：
\[
x_m = \begin{cases}
y_j, & \text{若存在 } j\in\mathbb N \text{ 使得 } m=f(j),\\
0, & \text{若 } m\notin f(\mathbb N).
\end{cases}
\]
由于 \(f\) 严格递增，\(f\) 是单射，故对每个 \(m\in f(\mathbb N)\)，原像 \(j\) 是唯一确定的，上述定义良定。
又因为 \(|x_m| \le \sup_{j}|y_j| = \|y\|_\infty < \infty\)，故 \(x\in E\)。
直接计算 \(P_f x\)：对每一个 \(j\in\mathbb N\)，
\[
(P_f x)_j = x_{f(j)} = y_j.
\]
这意味着 \(P_f x = y\) 在 \(E\) 中恒等成立！
因此 \(T_f([x]) = [P_f x] = [y]\)。这证明了 \(T_f\) 恒为满射。\(\blacksquare\)

---

#### 4. \(T_f\) 的单射性

**结论**：\(T_f\) 是单射当且仅当 \(\lim_{n\to\infty}\frac{f(n)}{n} = 1\)（等价于 \(L_1 = 1\)）。

**证明**：
由于 \(T_f\) 是线性映射，\(T_f\) 是单射等价于其核为平凡子空间，即：
\[
\|P_f x\|=0 \implies \|x\|=0.
\]

**情形一：若 \(\limsup_{n\to\infty}\frac{f(n)}{n} > 1\)**。
令集合 \(A = \mathbb N \setminus f(\mathbb N)\)。
取 \(x = \mathbf{1}_A\in E\)。
对任意 \(j\in\mathbb N\)，由于 \(f(j)\in f(\mathbb N)\)，必有 \(f(j)\notin A\)，从而：
\[
(P_f x)_j = (\mathbf{1}_A)_{f(j)} = 0.
\]
因此 \(P_f x = 0\)，特别地 \(\|P_f x\| = 0\)，即 \(T_f([x]) = [0]\)。

然而，计算 \(x = \mathbf{1}_A\) 在点 \(M = f(N)\) 处的截断平均：
\[
\frac{1}{f(N)}\sum_{m=1}^{f(N)} |x_m| = \frac{|A \cap [1, f(N)]|}{f(N)} = \frac{f(N) - |f(\mathbb N)\cap [1, f(N)]|}{f(N)} = \frac{f(N) - N}{f(N)} = 1 - \frac{N}{f(N)}.
\]
由于 \(\limsup_{N\to\infty}\frac{f(N)}{N} > 1\)，必有：
\[
\liminf_{N\to\infty}\frac{N}{f(N)} = \frac{1}{\limsup_{N\to\infty}\frac{f(N)}{N}} < 1.
\]
从而：
\[
\|x\| = \limsup_{M\to\infty}\frac1M\sum_{m=1}^M |x_m| \ge \limsup_{N\to\infty}\left(1 - \frac{N}{f(N)}\right) = 1 - \frac{1}{\limsup_{N\to\infty}\frac{f(N)}{N}} > 0.
\]
这表明 \([x] \ne [0]\)。
因此 \(T_f\) 不是单射。

**情形二：若 \(\limsup_{n\to\infty}\frac{f(n)}{n} = 1\)**。
因 \(f(n)\ge n\)，总有 \(\frac{f(n)}{n} \ge 1\)，故此时 \(\lim_{n\to\infty}\frac{f(n)}{n} = 1\)。
对任意 \(x\in E\)，利用 \(|x_m| \le \|x\|_\infty\)：
\[
\sum_{m=1}^{f(N)} |x_m| = \sum_{j=1}^N |x_{f(j)}| + \sum_{\substack{m\le f(N)\\ m\notin f(\mathbb N)}} |x_m|.
\]
第二项非负且被 \(\|x\|_\infty (f(N) - N)\) 控制。两端除以 \(f(N)\)：
\[
\left|\frac{1}{f(N)}\sum_{m=1}^{f(N)} |x_m| - \frac{1}{f(N)}\sum_{j=1}^N |x_{f(j)}|\right| \le \|x\|_\infty \left(1 - \frac{N}{f(N)}\right) \to 0 \quad (N\to\infty).
\]
又因为 \(\frac{f(N)}{N}\to 1\)，有：
\[
\lim_{N\to\infty} \left(\frac{1}{f(N)}\sum_{j=1}^N |x_{f(j)}| - \frac1N \sum_{j=1}^N |x_{f(j)}|\right) = 0.
\]
对任意 \(M\)，设 \(f(N)\le M < f(N+1)\)，由 \(\frac{f(N+1)}{f(N)} = \frac{f(N+1)}{N+1}\frac{N+1}{N}\frac{N}{f(N)} \to 1\)，可知在全序列上取上极限时，两者的上极限完全相等：
\[
\|x\| = \limsup_{M\to\infty}\frac1M\sum_{m=1}^M |x_m| = \limsup_{N\to\infty}\frac1N\sum_{j=1}^N |x_{f(j)}| = \|P_f x\|.
\]
即对一切 \([x]\in X\)，均有：
\[
\|T_f([x])\| = \|[x]\|.
\]
这说明当 \(\lim_{n\to\infty}\frac{f(n)}{n}=1\) 时，\(T_f\) 是 \(X\) 上的**等距同构（isometry）**！
既然是等距映射，自然若 \(T_f([x])=[0]\)，则 \(\|[x]\| = \|T_f([x])\|=0\)，即 \([x]=[0]\)。
因此 \(T_f\) 是单射。\(\blacksquare\)

---

### 三、第 2 问的解答与证明

#### 1. 证明极限 \(\lim_{k\to\infty} L_k^{1/k}\) 存在

对于 \(k\ge 1\)，\(T_f^k\) 是由算子 \(P_f^k\) 诱导的映射。
注意对任意 \(x\in E\) 及 \(j\in\mathbb N\)：
\[
(P_f^k x)_j = x_{f^k(j)},
\]
其中 \(f^k = f\circ f\circ \cdots \circ f\) 是 \(f\) 的 \(k\) 次复合迭代。
因为严格递增函数的复合仍为严格递增函数，且 \(f(n)\le C n \implies f^k(n)\le C^k n\)，故 \(f^k\) 仍满足第 1 问的允许条件。
由第 1 问的结论，\(T_f^k = T_{f^k}\) 的最小 Lipschitz 常数（即算子范数）为：
\[
L_k = \limsup_{n\to\infty}\frac{f^k(n)}{n}.
\]
因为 \(T_f^{j+k} = T_f^j \circ T_f^k\)，由赋范空间上线​​性算子范数的次乘性（submultiplicativity）：
\[
\|T_f^{j+k}([x])\| = \|T_f^j(T_f^k([x]))\| \le L_j \|T_f^k([x])\| \le L_j L_k \|[x]\|,
\]
取上确界即得：
\[
L_{j+k} \le L_j L_k, \quad \forall j,k\ge 1.
\]
又因 \(f(n)\ge n \implies f^k(n)\ge n\)，总有 \(L_k \ge 1\)。
因此取对数后，数列 \(a_k = \log L_k\) 是非负次可加数列：
\[
a_{j+k} \le a_j + a_k, \quad \forall j,k\ge 1.
\]
由经典的 **Fekete 次可加引理（Fekete's Subadditive Lemma）**，极限
\[
\lim_{k\to\infty}\frac{a_k}{k} \text{ 存在，且等于 } \inf_{k\ge 1}\frac{a_k}{k}.
\]
两边取指数，即得：
\[
\lim_{k\to\infty} L_k^{1/k} \text{ 存在，且等于 } \inf_{k\ge 1} L_k^{1/k}.
\]
记此极限为 \(R_f\)。\(\blacksquare\)

---

#### 2. 全部可能的有序对 \((L_1, R_f)\)

**定理 2**：有序对 \((L_1, R_f)\) 的全部可能取值集合为：
\[
\mathcal S = \{(a, b)\in\mathbb R^2 : 1 \le b \le a < \infty\}.
\]

**证明**：

##### （一）必要性
对于任意允许的 \(f\)：
1. 由第 1 问知 \(L_1 = \limsup_{n\to\infty}\frac{f(n)}{n} < \infty\)。
2. 因为 \(f(n)\ge n\)，有 \(L_1 \ge 1\)。
3. 对所有 \(k\ge 1\)，因 \(f^k(n)\ge n\)，有 \(L_k \ge 1\)，故 \(R_f = \lim_{k\to\infty} L_k^{1/k} \ge 1\)。
4. 由 Fekete 引理，\(R_f = \inf_{k\ge 1} L_k^{1/k} \le L_1^{1/1} = L_1\)。

综上，必然有 \(1 \le b \le a < \infty\)。

---

##### （二）充分性（对任意给定满足 \(1\le b \le a < \infty\) 的有序对 \((a, b)\) 进行构造）

我们构造严格递增函数 \(f:\mathbb N\to\mathbb N\) 使得 \(L_1 = a\) 且 \(R_f = b\)。分以下情况：

---

**情形 1：\(a = b = 1\)**
取 \(f(n) = n\)。
则对一切 \(k\ge 1\)，\(f^k(n) = n\)，故 \(L_k = \limsup_{n\to\infty}\frac{n}{n} = 1\)。
于是 \(L_1 = 1\)，\(R_f = \lim_{k\to\infty} 1^{1/k} = 1 = b\)。

---

**情形 2：\(a = b > 1\)**
取 \(f(n) = \lfloor a n \rfloor\)。
由于 \(a > 1\)，对任意 \(n\ge 1\)：
\[
a(n+1) - an = a > 1 \implies \lfloor a(n+1) \rfloor \ge \lfloor an \rfloor + 1,
\]
故 \(f\) 是严格递增的。
对任意固定的 \(k\ge 1\)，由数学归纳法容易证明：
\[
a^k n - \sum_{j=0}^{k-1} a^j \le f^k(n) \le a^k n.
\]
两边除以 \(n\) 并令 \(n\to\infty\)，得到：
\[
\lim_{n\to\infty}\frac{f^k(n)}{n} = a^k.
\]
因此 \(L_k = a^k\)。
特别地，\(L_1 = a\)，且：
\[
R_f = \lim_{k\to\infty} (L_k)^{1/k} = \lim_{k\to\infty} (a^k)^{1/k} = a = b.
\]

---

**情形 3：\(1 \le b < a < \infty\)**
此情形的核心思想是：以底增长率 \(b\) 为主体，在极为稀疏的点处植入增长率为 \(a\) 的跳跃。

选取充分迅速递增的正整数序列 \(\{N_m\}_{m=1}^\infty\)，满足：
1. \(N_1 \ge 1\)；
2. 对任意 \(m\ge 1\)，\(N_{m+1} > (a + 2)^{m+1} N_m\)。

定义 \(f:\mathbb N\to\mathbb N\) 如下：
- 当 \(1 \le n < N_1\) 时，定义 \(f(n) = \lfloor b n \rfloor\)（若 \(b=1\) 则直接取 \(f(n)=n\)）；
- 当 \(n \ge N_1\) 时，设 \(m\ge 1\) 为满足 \(N_m \le n < N_{m+1}\) 的唯一正整数，定义：
\[
f(n) = \lfloor a N_m \rfloor + \lfloor b (n - N_m) \rfloor.
\]

我们逐项验证该函数符合全部要求：

**1. 验证 \(f\) 严格递增**
- 在每个半开区间 \([N_m, N_{m+1}-1]\) 内部：
  任取该区间内的 \(n\)，
  \[
  f(n+1) - f(n) = \lfloor b(n+1-N_m) \rfloor - \lfloor b(n-N_m) \rfloor.
  \]
  因为 \(b\ge 1\)，两实数之差为 \(b(n+1-N_m) - b(n-N_m) = b \ge 1\)，根据向下取整函数的性质，其底函数值之差至少为 \(1\)：
  \[
  f(n+1) - f(n) \ge 1.
  \]
- 在相邻区间的拼接边界 \(n = N_{m+1}-1\) 与 \(n = N_{m+1}\) 处：
  由定义：
  \[
  f(N_{m+1}-1) = \lfloor a N_m \rfloor + \lfloor b(N_{m+1} - 1 - N_m) \rfloor \le a N_m + b N_{m+1}.
  \]
  而
  \[
  f(N_{m+1}) = \lfloor a N_{m+1} \rfloor \ge a N_{m+1} - 1.
  \]
  两者之差：
  \[
  f(N_{m+1}) - f(N_{m+1}-1) \ge (a - b) N_{m+1} - a N_m - 1.
  \]
  因为 \(a > b\) 且 \(N_{m+1} > (a+2) N_m\)，有 \((a-b)N_{m+1} - a N_m - 1 > 0\)。
  因此对一切 \(n\in\mathbb N\)，均有 \(f(n+1) > f(n)\)，即 \(f\) 严格递增。

**2. 计算 \(L_1\)**
对任意 \(n\in [N_m, N_{m+1}-1]\)：
\[
\frac{f(n)}{n} = \frac{\lfloor a N_m \rfloor + \lfloor b(n - N_m) \rfloor}{n} \le \frac{a N_m + b(n - N_m)}{n} = b + (a - b)\frac{N_m}{n}.
\]
因为 \(a > b\)，函数 \(g(n) = b + (a - b)\frac{N_m}{n}\) 在 \(n \ge N_m\) 上关于 \(n\) 严格单调递减。
在左端点 \(n = N_m\) 处：
\[
\frac{f(N_m)}{N_m} = \frac{\lfloor a N_m \rfloor}{N_m} \to a \quad (m\to\infty).
\]
对该区间内的任意 \(n\)，都有 \(\frac{f(n)}{n} \le \frac{f(N_m)}{N_m} \le a\)。
因此：
\[
L_1 = \limsup_{n\to\infty}\frac{f(n)}{n} = a.
\]

**3. 计算 \(L_k\)（对任意固定正整数 \(k\ge 1\)）**
考虑固定的 \(k\ge 1\)。
设 \(m > k\)。由于选取了 \(N_{m+1} > (a + 2)^{m+1} N_m\)，在 \(N_m\) 附近的点，其前 \(k\) 次迭代均不会超过 \(N_{m+1}\)。
记常数 \(D_m = \lfloor a N_m \rfloor - N_m = (a - 1) N_m + O(1)\)。
在区间 \([N_m, N_{m+1}-1]\) 内，只要 \(x\) 与其前 \(k-1\) 次迭代均落在该区间内，就有：
\[
f(x) - N_m = D_m + \lfloor b(x - N_m) \rfloor.
\]
对 \(u = n - N_m \ge 0\)，迭代 \(k\) 次得：
\[
f^k(n) - N_m = D_m \left(\sum_{j=0}^{k-1} b^j\right) + b^k u + O_k(1),
\]
其中 \(O_k(1)\) 是仅依赖于 \(k\) 的有界量。
记常数：
\[
C_k = \begin{cases}
1 + (a - 1)\frac{b^k - 1}{b - 1}, & b > 1,\\
1 + k(a - 1), & b = 1.
\end{cases}
\]
则对于 \(n\in [N_m, N_{m+1}-1]\) 使得 \(f^k(n) < N_{m+1}\) 的情形：
\[
f^k(n) = C_k N_m + b^k(n - N_m) + O_k(1).
\]
两边除以 \(n\)：
\[
\frac{f^k(n)}{n} = \frac{C_k N_m + b^k(n - N_m) + O_k(1)}{n} = b^k + (C_k - b^k)\frac{N_m}{n} + o(1) \quad (m\to\infty).
\]
注意到：
- 若 \(b > 1\)：\(C_k - b^k = 1 + (a - 1)\frac{b^k - 1}{b - 1} - b^k = (a - b)\frac{b^k - 1}{b - 1} > 0\)（因 \(a > b\) 且 \(b > 1\)）；
- 若 \(b = 1\)：\(C_k - b^k = 1 + k(a - 1) - 1 = k(a - 1) > 0\)（因 \(a > 1\)）。

因此，在两种情况下都有 \(C_k - b^k > 0\)。
这意味着函数 \(n \mapsto b^k + (C_k - b^k)\frac{N_m}{n}\) 在 \(n \ge N_m\) 上是**严格单调递减**的！
其最大值在左端点 \(n = N_m\) 处取得：
\[
\frac{f^k(N_m)}{N_m} = C_k + o(1) \quad (m\to\infty).
\]
若 \(n\) 充分靠近右端点 \(N_{m+1}\) 使得在 \(k\) 步之内轨道跃入下一个区间 \([N_{m+1}, N_{m+2}-1]\)，则由于 \(N_{m+1} \gg N_m\)，此时 \(n = N_{m+1}(1 - o(1))\)，在下一个区间内至多还能进行不到 \(k\) 步迭代，所产生的比值 \(\frac{f^k(n)}{n}\) 被 \(\max_{0\le j < k} C_j + o(1)\) 控制。因为序列 \(\{C_k\}\) 严格递增，此值严格小于 \(C_k\)。
综上分析，精确得上极限：
\[
L_k = \limsup_{n\to\infty}\frac{f^k(n)}{n} = C_k.
\]

**4. 计算 \(R_f\)**
- 若 \(b = 1\)：
  \[
  L_k = 1 + k(a - 1).
  \]
  因此：
  \[
  R_f = \lim_{k\to\infty} L_k^{1/k} = \lim_{k\to\infty} (1 + k(a - 1))^{1/k} = 1 = b.
  \]
- 若 \(b > 1\)：
  \[
  L_k = 1 + (a - 1)\frac{b^k - 1}{b - 1} = \frac{a - 1}{b - 1} b^k + \frac{b - a}{b - 1}.
  \]
  由于 \(\frac{a - 1}{b - 1} > 0\)，有：
  \[
  R_f = \lim_{k\to\infty} L_k^{1/k} = \lim_{k\to\infty} \left(\frac{a - 1}{b - 1} b^k\right)^{1/k} = b.
  \]

无论 \(b=1\) 还是 \(b>1\)，均有 \(L_1 = a\) 且 \(R_f = b\)。
充分性得证。\(\blacksquare\)

---

### 四、结论汇总

1. **第 1 问**：
   - 允许的严格递增函数 \(f\) 为且仅为满足
     \[
     \limsup_{n\to\infty}\frac{f(n)}{n} < \infty
     \]
     的函数。
   - 对每一个允许的 \(f\)：
     - **连续性**：\(T_f\) 恒**连续**（实际上是 Lipschitz 连续的）；
     - **最小 Lipschitz 常数**：为有限值
       \[
       L_1 = \limsup_{n\to\infty}\frac{f(n)}{n}；
       \]
     - **单射性**：\(T_f\) 为单射当且仅当 \(\lim_{n\to\infty}\frac{f(n)}{n} = 1\)（等价于 \(L_1 = 1\)），此时 \(T_f\) 为等距同构；
     - **满射性**：\(T_f\) 恒为**满射**。

2. **第 2 问**：
   - 极限 \(R_f = \lim_{k\to\infty} L_k^{1/k}\) 恒存在，且 \(R_f = \inf_{k\ge 1} L_k^{1/k}\)。
   - 全部可能的有序对 \((L_1, R_f)\) 的集合为：
     \[
     \{(a, b)\in\mathbb R^2 : 1 \le b \le a < \infty\}.
     \]
   - 构造：
     - 当 \(a = b = 1\) 时，取 \(f(n) = n\)；
     - 当 \(a = b > 1\) 时，取 \(f(n) = \lfloor a n \rfloor\)；
     - 当 \(1 \le b < a < \infty\) 时，选取增长极为迅速的整数列 \(N_{m+1} > (a + 2)^{m+1} N_m\)，并在区间 \([N_m, N_{m+1}-1]\) 上定义
       \[
       f(n) = \lfloor a N_m \rfloor + \lfloor b (n - N_m) \rfloor,
       \]
       即得 \(L_1 = a\) 且 \(R_f = b\)。
