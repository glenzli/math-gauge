在 ZFC 集合论框架下，设 $R$ 为任意含幺环，$M$ 为左 $R$-模，$A, B, C \le M$ 为子模。

先明确基本包含关系：
由于 $A \cap B \subseteq A \subseteq A + C$ 且 $A \cap B \subseteq B \subseteq B + C$，故 $A \cap B \subseteq (A+C)\cap(B+C) = H$；又 $C \subseteq A+C$ 且 $C \subseteq B+C$，故 $C \subseteq H$。从而
\[
L = (A \cap B) + C \subseteq H = (A + C) \cap (B + C) \subseteq M.
\]
因此，$O = \{[h]_L : h \in H\} = H/L$ 作为商模 $M/L$ 的子模是良定义的左 $R$-模。

---

### 一、映射 $\delta: Q \to O$ 的构造

对任意记录类 $[(x,y,z)] \in Q = P/E$，其代表元 $(x,y,z) \in P$ 满足 $x - y \in A + B$。
1. 选取分解：存在 $a \in A$ 与 $b \in B$，使得
   \[
   x - y = a + b.
   \]
2. 构造同步元：令
   \[
   w = x - a = y + b \in M.
   \]
3. 考察差元 $w - z$：
   - 由 $(x,y,z) \in P$ 知 $x - z \in A + C$，从而
     \[
     w - z = (x - a) - z = (x - z) - a \in (A + C) + A = A + C.
     \]
   - 由 $(x,y,z) \in P$ 知 $y - z \in B + C$，从而
     \[
     w - z = (y + b) - z = (y - z) + b \in (B + C) + B = B + C.
     \]
   因此，
   \[
   w - z \in (A + C) \cap (B + C) = H.
   \]
4. **定义映射 $\delta$**：
   \[
   \delta([(x,y,z)]) := [w - z]_L \in O = H/L.
   \]

---

### 二、$\delta$ 的良定性、线性与给定性质验证

#### 1. 良定性（Well-definedness）
- **与分解 $x - y = a + b$ 的选择无关**：
  若还有另一组分解 $x - y = a' + b'$（$a' \in A, b' \in B$），对应 $w' = x - a' = y + b'$。
  则
  \[
  w - w' = (x - a) - (x - a') = a' - a \in A,
  \]
  且
  \[
  w - w' = (y + b) - (y + b') = b - b' \in B.
  \]
  于是 $w - w' \in A \cap B \subseteq (A \cap B) + C = L$。
  从而
  \[
  (w - z) - (w' - z) = w - w' \in L \implies [w - z]_L = [w' - z]_L.
  \]
- **与代表元 $(x,y,z) \in P$ 在类 $[(x,y,z)] \in P/E$ 中的选取无关**：
  设 $(x', y', z') \in P$ 且 $(x', y', z') - (x,y,z) \in E = A \times B \times C$，即存在 $a_0 \in A, b_0 \in B, c_0 \in C$ 使得
  \[
  x' = x + a_0,\qquad y' = y + b_0,\qquad z' = z + c_0.
  \]
  此时 $x' - y' = (x - y) + a_0 - b_0 = (a + a_0) + (b - b_0)$。
  选取 $a' = a + a_0 \in A, b' = b - b_0 \in B$，则
  \[
  w' = x' - a' = (x + a_0) - (a + a_0) = x - a = w.
  \]
  于是
  \[
  (w' - z') - (w - z) = - (z' - z) = -c_0 \in C \subseteq L,
  \]
  从而 $[w' - z']_L = [w - z]_L$。

因此，$\delta: Q \to O$ 良定。

#### 2. $R$-线性
设 $[(x_1, y_1, z_1)], [(x_2, y_2, z_2)] \in Q$，$r \in R$。
分别取分解 $x_1 - y_1 = a_1 + b_1$ 与 $x_2 - y_2 = a_2 + b_2$（$a_i \in A, b_i \in B$），对应 $w_1 = x_1 - a_1, w_2 = x_2 - a_2$。
对于组合 $(x_1 + r x_2) - (y_1 + r y_2) = (a_1 + r a_2) + (b_1 + r b_2)$，取 $a = a_1 + r a_2 \in A$，对应的同步元为
\[
w = (x_1 + r x_2) - a = (x_1 - a_1) + r(x_2 - a_2) = w_1 + r w_2.
\]
从而
\[
w - (z_1 + r z_2) = (w_1 - z_1) + r(w_2 - z_2).
\]
投影至 $M/L$ 中即得：
\[
\delta([(x_1, y_1, z_1)] + r[(x_2, y_2, z_2)]) = \delta([(x_1, y_1, z_1)]) + r\,\delta([(x_2, y_2, z_2)]).
\]
故 $\delta$ 为左 $R$-模同态。

#### 3. 满足 $\delta([(0,0,-h)]) = [h]_L$
对任意 $h \in H = (A+C)\cap(B+C)$，三元组 $(0,0,-h)$ 满足：
$0 - 0 = 0 \in A+B$，$0 - (-h) = h \in A+C$，$0 - (-h) = h \in B+C$，故 $(0,0,-h) \in P$。
按定义计算：对 $0 - 0 = 0 + 0$，取 $a = 0, b = 0$，则 $w = 0 - 0 = 0$。
于是 $w - z = 0 - (-h) = h$，从而
\[
\delta([(0,0,-h)]) = [h]_L.
\]

---

### 三、短正合序列的证明

我们需要证明
\[
0\longrightarrow M/I\xrightarrow{j}Q\xrightarrow{\delta}O\longrightarrow0
\]
正合。

1. **$j$ 为单射**：
   $j$ 显然是良定的 $R$-线性映射。
   若 $j([t]_I) = 0 \in Q$，则 $(t,t,t) \in E = A \times B \times C$。
   从而 $t \in A, t \in B, t \in C$，即 $t \in A \cap B \cap C = I$。
   因此 $[t]_I = 0 \in M/I$。故 $\ker(j) = \{0\}$，$j$ 为单同态。

2. **$\delta$ 为满射**：
   对任意 $[h]_L \in O$（其中 $h \in H$），由上述验证可知 $[(0,0,-h)] \in Q$ 且 $\delta([(0,0,-h)]) = [h]_L$。故 $\delta$ 为满同态。

3. **正合性 $\operatorname{Im}(j) = \ker(\delta)$**：
   - **$\operatorname{Im}(j) \subseteq \ker(\delta)$**：
     对任意 $[t]_I \in M/I$，$j([t]_I) = [(t,t,t)]$。
     此时 $t - t = 0 + 0$，取 $a = 0$，得 $w = t$。则 $w - z = t - t = 0$，故 $\delta([(t,t,t)]) = [0]_L = 0$。
   - **$\ker(\delta) \subseteq \operatorname{Im}(j)$**：
     设 $[(x,y,z)] \in \ker(\delta)$。
     由 $\delta([(x,y,z)]) = [w - z]_L = 0 \in O = H/L$，得
     \[
     w - z \in L = (A \cap B) + C.
     \]
     因此存在 $u \in A \cap B$ 与 $c \in C$，使得
     \[
     w - z = u + c.
     \]
     令
     \[
     t := w - u \in M.
     \]
     检验 $t$ 与各分量的差：
     - $t - x = (w - u) - x = (w - x) - u = -a - u$。因 $a \in A$ 且 $u \in A \cap B \subseteq A$，故 $t - x \in A$；
     - $t - y = (w - u) - y = (w - y) - u = b - u$。因 $b \in B$ 且 $u \in A \cap B \subseteq B$，故 $t - y \in B$；
     - $t - z = (w - u) - z = (w - z) - u = (u + c) - u = c \in C$。
     
     这说明 $(t - x, t - y, t - z) \in A \times B \times C = E$，即在 $Q$ 中有
     \[
     [(x,y,z)] = [(t,t,t)] = j([t]_I) \in \operatorname{Im}(j).
     \]
   
综上，$\operatorname{Im}(j) = \ker(\delta)$，该序列构成短正合序列。

*(注：在 $Q$ 中，恒有恒等式 $[(x,y,z)] = j([w]_I) + [(0,0,-(w-z))]$，结合正合性与条件 $\delta([(0,0,-h)])=[h]_L$，说明满足题设要求的同态 $\delta$ 是唯一确定的。)*

---

### 四、原始实现的存在性判定与全部原始实现描述

由原始实现的定义，$t \in M$ 是记录 $[(x,y,z)] \in Q$ 的原始实现，当且仅当
\[
t - x \in A,\qquad t - y \in B,\qquad t - z \in C \iff [(x,y,z)] = [(t,t,t)] = j([t]_I).
\]
因此，原始实现的存在性等价于 $[(x,y,z)] \in \operatorname{Im}(j)$。

借助短正合序列的性质：

#### 1. 存在性判定准则
记录 $[(x,y,z)] \in Q$ 存在原始实现，当且仅当
\[
\delta([(x,y,z)]) = 0 \in O = H/L.
\]
即：任取满足 $x - y = a + b$（$a \in A, b \in B$）的分解，并令 $w = x - a = y + b$，原始实现存在的充要条件是
\[
w - z \in L = (A \cap B) + C.
\]

#### 2. 全部原始实现的描述
当上述存在性条件满足时，将差元 $w - z \in L$ 分解为
\[
w - z = u + c \qquad (u \in A \cap B,\ c \in C).
\]
- **特解**：
  元素
  \[
  t_0 = w - u = z + c \in M
  \]
  是一个原始实现（由正合性证明知 $j([t_0]_I) = [(x,y,z)]$）。
- **通解（全部原始实现）**：
  任意 $t \in M$ 是原始实现，当且仅当
  \[
  j([t]_I) = j([t_0]_I) \iff [t]_I = [t_0]_I \iff t - t_0 \in I = A \cap B \cap C.
  \]
  因此，该记录的全部原始实现的集合为模 $M$ 中的陪集：
  \[
  t_0 + I = t_0 + (A \cap B \cap C) = \{t_0 + i : i \in A \cap B \cap C\}.
  \]
  （亦即三模同余子集的交：$(x + A) \cap (y + B) \cap (z + C) = t_0 + (A \cap B \cap C)$）。
