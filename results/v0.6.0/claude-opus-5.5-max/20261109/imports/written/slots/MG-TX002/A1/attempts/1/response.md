这个结论成立，下面给出完整证明。它是 Propp–Roby 关于 $[a]\times[b]$ 上 rowmotion 的 homomesy 定理。证明的思路是：给每个反链配一个长度为 $a+b$ 的 0/1 词（Stanley–Thomas 词），$R$ 作用后这个词恰好循环右移一位，而 $|A|$ 等于词的前 $a$ 位之和。证明对一切 $a,b\ge 1$ 都成立。

我另外用 Python 对 $1\le a,b\le 6$ 做了穷举检验：$R$ 是置换、引理 1 的显式公式、词的循环移位关系、每条轨道的平均值等于 $ab/(a+b)$，全部通过。这只是辅助核对，证明本身不依赖它。

## 记号

记 $n=a+b$，$[k]=\{1,\dots,k\}$。对 $x\in[a]$，称 $\{x\}\times[b]$ 为第 $x$ 行；对 $y\in[b]$，称 $[a]\times\{y\}$ 为第 $y$ 列。

同一行（或同一列）中的两个元素总可比较，所以反链与每行、每列至多有一个公共元素。每个元素又恰好属于一行和一列，因此对任意反链 $A$：
$$|A|=\#\{x\in[a]:A\text{ 与第 }x\text{ 行相交}\}=\#\{y\in[b]:A\text{ 与第 }y\text{ 列相交}\}.\tag{1}$$

## 1. 基本事实

固定反链 $A$，记 $I=I(A)$，$F=P\setminus I$，$B=R(A)$（即 $F$ 的极小元之集）。

**(a) $I$ 是下集，$F$ 是上集。** 若 $u\le u'\in I$，取 $v\in A$ 使 $u'\le v$，则 $u\le v$，故 $u\in I$。若 $u\in F$、$u\le u'$ 而 $u'\in I$，则 $u\in I$，矛盾，所以 $F$ 是上集。

**(b) $A$ 恰是 $I$ 的极大元之集。** 设 $v\in A$ 且 $v\le u\in I$。取 $v'\in A$ 使 $u\le v'$，则 $v\le v'$，由反链性得 $v=v'$，于是 $u=v$，即 $v$ 在 $I$ 中极大。反之，设 $u$ 在 $I$ 中极大，取 $v\in A$ 使 $u\le v$。因为 $v\in I$，由极大性得 $u=v\in A$。

（附注：题目已给出 $R$ 是置换，这里补一句理由。有限上集 $F$ 中每个元素都在某个极小元之上，所以 $F$ 等于 $B$ 的上闭包，于是 $B$ 决定 $F$，进而决定 $I$，再由 (b) 决定 $A$。因此 $R$ 是有限集上的单射，从而是置换。）

## 2. 轮廓

对 $x\in[a]$，令 $\lambda_x=\#\{y:(x,y)\in I\}$。

- 因为 $I$ 是下集，$\{y:(x,y)\in I\}$ 是链 $[b]$ 的下集，所以它等于 $\{1,\dots,\lambda_x\}$。
- 又由 $(x+1,y)\in I\Rightarrow(x,y)\in I$ 得 $\lambda_{x+1}\le\lambda_x$。

约定 $\lambda_0=b$，$\lambda_{a+1}=0$，则
$$b=\lambda_0\ge\lambda_1\ge\cdots\ge\lambda_a\ge\lambda_{a+1}=0,$$
并且对 $(x,y)\in P$ 有 $(x,y)\in I\iff y\le\lambda_x$，$(x,y)\in F\iff y>\lambda_x$。

## 3. 引理 1（$A$ 与 $B$ 的显式形式）

(i) $A=\{(x,\lambda_x): x\in[a],\ \lambda_x>\lambda_{x+1}\}$；
(ii) $B=\{(x,\lambda_x+1): x\in[a],\ \lambda_{x-1}>\lambda_x\}$。

**证明。** 下文中不属于 $P$ 的点一律视为既不在 $I$ 中也不在 $F$ 中。设 $u=(x,y)$。

- 若 $u<u'=(x',y')$，则 $x'>x$ 或 $y'>y$，相应地 $(x+1,y)\le u'$ 或 $(x,y+1)\le u'$。因 $I$ 是下集，得：$u\in I$ 不是 $I$ 的极大元 $\iff$ $(x+1,y)\in I$ 或 $(x,y+1)\in I$。
- 同理，若 $u'<u$，则 $u'\le(x-1,y)$ 或 $u'\le(x,y-1)$。因 $F$ 是上集，得：$u\in F$ 不是 $F$ 的极小元 $\iff$ $(x-1,y)\in F$ 或 $(x,y-1)\in F$。

**(i)** 
- "$(x,y)\in I$ 且 $(x,y+1)\notin I$" 等价于 $y\le\lambda_x<y+1$，即 $y=\lambda_x$（需 $\lambda_x\ge1$）。$y=b$ 时这也成立，因为 $\lambda_x\le b$。
- "$(x+1,y)\notin I$" 等价于 "$x=a$ 或 $y>\lambda_{x+1}$"。由于 $y\ge1>0=\lambda_{a+1}$，它就是 $y>\lambda_{x+1}$。
- 所以 $(x,y)$ 是 $I$ 的极大元当且仅当 $y=\lambda_x$ 且 $\lambda_x>\lambda_{x+1}$；条件 $\lambda_x\ge1$ 由 $\lambda_{x+1}\ge0$ 自动满足。再结合 1(b) 即得 (i)。

**(ii)**
- "$(x,y)\in F$ 且 $(x,y-1)\notin F$" 等价于 $\lambda_x<y\le\lambda_x+1$（$y=1$ 时 $y-1=0\le\lambda_x$ 自动成立），即 $y=\lambda_x+1$；此外还需 $\lambda_x+1\le b$。
- "$(x-1,y)\notin F$" 等价于 "$x=1$ 或 $\lambda_x+1\le\lambda_{x-1}$"。
- $x=1$ 时，条件合起来是 $\lambda_1<b=\lambda_0$；$x\ge2$ 时是 $\lambda_x<\lambda_{x-1}$，它已蕴含 $\lambda_x<b$。两种情形都等价于 "$y=\lambda_x+1$ 且 $\lambda_{x-1}>\lambda_x$"。∎

## 4. 引理 2（行与列）

令 $\Lambda=\{\lambda_1,\dots,\lambda_a\}$（取值集合）。

- **(R)** 对 $x\in[a]$：$A$ 与第 $x$ 行相交 $\iff\lambda_x>\lambda_{x+1}$；$B$ 与第 $x$ 行相交 $\iff\lambda_{x-1}>\lambda_x$。
- **(C)** 对 $y\in[b]$：$A$ 与第 $y$ 列相交 $\iff y\in\Lambda$；$B$ 与第 $y$ 列相交 $\iff y-1\in\Lambda$。

**证明。** (R) 直接由引理 1 读出。

(C) 的前半：由引理 1(i)，$A$ 与第 $y$ 列相交当且仅当存在 $x$ 使 $\lambda_x=y>\lambda_{x+1}$，这显然蕴含 $y\in\Lambda$。反之，若 $y\in\Lambda$，取最大的 $x$ 使 $\lambda_x=y$。
- 若 $x<a$，由单调性 $\lambda_{x+1}\le y$，由 $x$ 的最大性 $\lambda_{x+1}\ne y$；
- 若 $x=a$，则 $\lambda_{a+1}=0<y$。

两种情形都有 $\lambda_x>\lambda_{x+1}$。

(C) 的后半：由引理 1(ii)，$B$ 与第 $y$ 列相交当且仅当存在 $x$ 使 $\lambda_x=y-1<\lambda_{x-1}$，这蕴含 $y-1\in\Lambda$。反之，若 $y-1\in\Lambda$，取最小的 $x$ 使 $\lambda_x=y-1$。
- 若 $x>1$，由单调性和最小性得 $\lambda_{x-1}>y-1$；
- 若 $x=1$，则 $\lambda_0=b>y-1$。∎

## 5. 词与循环移位

对反链 $A$ 定义 $w(A)\in\{0,1\}^n$：
- 对 $x\in[a]$：$A$ 与第 $x$ 行相交时 $w_x(A)=1$，否则为 $0$；
- 对 $y\in[b]$：$A$ 与第 $y$ 列**不**相交时 $w_{a+y}(A)=1$，否则为 $0$。

令 $\sigma(w_1,\dots,w_n)=(w_n,w_1,\dots,w_{n-1})$，即循环右移一位。

**引理 3.** 对每个反链 $A$，有 $w(R(A))=\sigma(w(A))$。

**证明。** 用引理 2（$\lambda$ 是 $A$ 的轮廓，引理 2 同时描述 $A$ 和 $B$），分四段验证：

- **$k=1$：** $w_1(B)=1\iff\lambda_1<b\iff b\notin\Lambda$（因为 $\max\Lambda=\lambda_1\le b$）$\iff A$ 与第 $b$ 列不相交 $\iff w_n(A)=1$。
- **$2\le k\le a$：** $w_k(B)=1\iff\lambda_{k-1}>\lambda_k\iff A$ 与第 $k-1$ 行相交 $\iff w_{k-1}(A)=1$。
- **$k=a+1$：** $w_{a+1}(B)=1\iff 0\notin\Lambda\iff\lambda_a>0=\lambda_{a+1}$（因为 $\min\Lambda=\lambda_a\ge 0$）$\iff A$ 与第 $a$ 行相交 $\iff w_a(A)=1$。
- **$k=a+y$，$2\le y\le b$：** $w_{a+y}(B)=1\iff y-1\notin\Lambda\iff A$ 与第 $y-1$ 列不相交 $\iff w_{a+y-1}(A)=1$。∎

**引理 4.** $|A|=\sum_{k=1}^{a}w_k(A)$，且 $\sum_{k=1}^{n}w_k(A)=b$。

**证明。** 由 (1)，前 $a$ 位之和等于与 $A$ 相交的行数，即 $|A|$；后 $b$ 位之和等于与 $A$ 不相交的列数，即 $b-|A|$。两者相加得 $b$。∎

## 6. 轨道平均

设 $A_0\in O$，$m=|O|$。由于 $R$ 是有限集上的置换，$A_0,R(A_0),\dots,R^{m-1}(A_0)$ 两两不同、恰好组成 $O$，并且 $R^m(A_0)=A_0$。

令 $w=w(A_0)$，下标按模 $n$ 理解，则 $\sigma^t(w)_k=w_{k-t}$。由引理 3 归纳得 $w(R^tA_0)=\sigma^t(w)$。再由引理 4，
$$f(t):=|R^t(A_0)|=\sum_{k=1}^{a}w_{k-t}\qquad(t\ge 0).$$

由 $R^{t+m}(A_0)=R^t(A_0)$ 得 $f(t+m)=f(t)$；由下标模 $n$ 得 $f(t+n)=f(t)$。把 $0,\dots,mn-1$ 分别分成 $n$ 段长为 $m$ 的区间和 $m$ 段长为 $n$ 的区间，得
$$n\sum_{A\in O}|A|=n\sum_{t=0}^{m-1}f(t)=\sum_{t=0}^{mn-1}f(t)=m\sum_{t=0}^{n-1}f(t).$$

对固定的 $k$，当 $t$ 取遍 $0,\dots,n-1$ 时，$k-t$ 恰好取遍模 $n$ 的每个剩余类一次。结合引理 4 的 $\sum_j w_j=b$，得
$$\sum_{t=0}^{n-1}f(t)=\sum_{k=1}^{a}\sum_{j=1}^{n}w_j=ab.$$

所以 $n\sum_{A\in O}|A|=m\,ab$，即
$$\frac{1}{|O|}\sum_{A\in O}|A|=\frac{ab}{a+b}.\qquad\blacksquare$$

证明中没有用到 $w$ 是双射，只用了引理 3 的循环移位关系和引理 4 的计数。